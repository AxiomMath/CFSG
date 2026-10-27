module

public import CFSG.Quasithin.Recognition.F112J2Ctx

public section

namespace CFSG.Quasithin.SzVB

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G}

theorem S_le_normalizer_conjClosure (hRO : RankOneListedFacts.{0}) (h : R1SettingLegacyBare K1 L2 S Zs) :
    S ≤ Subgroup.normalizer (conjClosure Zs L2 : Set G) :=
  (le_sup_right : S ≤ L2 ⊔ S).trans (F112J2.amalgamHypV_of_setting hRO h).normalizes

theorem borelOf_le_normalizer_conjClosure (h : R1SettingLegacyBare K1 L2 S Zs) :
    borelOf K1 S ≤ Subgroup.normalizer (conjClosure Zs L2 : Set G) := by
  refine F7.le_normalizer_closure {x | ∃ l ∈ L2, ∃ z ∈ Zs, l * z * l⁻¹ = x} ?_
  rintro g hg _ ⟨l, hl, z, hz, rfl⟩
  have hgL : g * l * g⁻¹ ∈ L2 :=
    (Subgroup.mem_normalizer_iff.mp (h.hyp.h2.borel_le hg) l).mp hl
  have hgz : z * g = g * z :=
    Subgroup.mem_centralizer_iff.mp (h.K1_cent_Z (F1.borelOf_le K1 S hg)) z hz
  have hz' : g⁻¹ * z * g = z := by
    calc g⁻¹ * z * g = g⁻¹ * (z * g) := by group
      _ = g⁻¹ * (g * z) := by rw [hgz]
      _ = z := by group
  refine ⟨g * l * g⁻¹, hgL, z, hz, ?_⟩
  calc g * l * g⁻¹ * z * (g * l * g⁻¹)⁻¹ = g * l * (g⁻¹ * z * g) * l⁻¹ * g⁻¹ := by group
    _ = g * l * z * l⁻¹ * g⁻¹ := by rw [hz']
    _ = g * (l * z * l⁻¹) * g⁻¹ := by group

omit [Finite G] in
theorem mem_normalizer_iff_conjSub_eq {g : G} {H : Subgroup G} :
    g ∈ Subgroup.normalizer (H : Set G) ↔ conjSub g H = H := by
  refine ⟨F1.conjSub_eq_of_mem_normalizer, fun e => F7.mem_normalizer_of_conj_le e.le ?_⟩
  have e' := conjSub_conjSub_inv g H
  rw [e] at e'
  exact e'.le

theorem inf_normalizer_eq_borelOf (hRO : RankOneListedFacts.{0}) (h : R1SettingLegacyBare K1 L2 S Zs) :
    K1 ⊓ Subgroup.normalizer (conjClosure Zs L2 : Set G) = borelOf K1 S := by
  have hR : Hyp111R K1 L2 S := F112J2.hyp111R_of_setting hRO h
  have hamal := F112J2.amalgamHypV_of_setting hRO h
  have hSN : S ≤ Subgroup.normalizer (conjClosure Zs L2 : Set G) :=
    S_le_normalizer_conjClosure hRO h
  refine le_antisymm ?_ (le_inf (F1.borelOf_le K1 S) (borelOf_le_normalizer_conjClosure h))
  refine (F1.isUniqueMax_borelOf hR.r1).2.2 _ (le_inf inf_le_right (inf_le_left.trans hSN))
    (lt_of_le_of_ne inf_le_left fun heq => ?_)
  have hK1N : K1 ≤ Subgroup.normalizer (conjClosure Zs L2 : Set G) := inf_eq_left.mp heq
  have hG0N : K1 ⊔ L2 ⊔ S ≤ Subgroup.normalizer (conjClosure Zs L2 : Set G) :=
    sup_le (sup_le hK1N ((le_sup_left : L2 ≤ L2 ⊔ S).trans hamal.normalizes)) hSN
  have hKS : K1 ⊔ S ≤ K1 ⊔ L2 ⊔ S := sup_le (le_sup_left.trans le_sup_left) le_sup_right
  have hVle : conjClosure Zs L2 ≤ K1 ⊔ L2 ⊔ S :=
    h.V_le.trans ((CFSG.LieType.BorelTits.pCoreOf_le 2 (K1 ⊔ S)).trans hKS)
  have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVle hG0N hamal.isPGroup
  rw [h.hyp.o2] at hle
  exact F112J2.V_ne_bot h (le_bot_iff.mp hle)

theorem conjSub_eq_iff_mem_borelOf (hRO : RankOneListedFacts.{0}) (h : R1SettingLegacyBare K1 L2 S Zs)
    {k k' : G} (hk : k ∈ K1) (hk' : k' ∈ K1) :
    conjSub k (conjClosure Zs L2) = conjSub k' (conjClosure Zs L2) ↔ k⁻¹ * k' ∈ borelOf K1 S := by
  rw [← inf_normalizer_eq_borelOf hRO h, Subgroup.mem_inf]
  constructor
  · intro e
    refine ⟨K1.mul_mem (K1.inv_mem hk) hk', mem_normalizer_iff_conjSub_eq.mpr ?_⟩
    rw [conjSub_mul, ← e, conjSub_conjSub_inv]
  · rintro ⟨-, hN⟩
    rw [← mul_inv_cancel_left k k', conjSub_mul, mem_normalizer_iff_conjSub_eq.mp hN]

theorem exists_mem_K1_conjSub (h : R1SettingLegacyBare K1 L2 S Zs) (hRO : RankOneListedFacts.{0}) {x : G}
    (hx : x ∈ K1 ⊔ S) :
    ∃ k ∈ K1, conjSub x (conjClosure Zs L2) = conjSub k (conjClosure Zs L2) := by
  obtain ⟨k, hk, s, hs, rfl⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes h.hyp.h1.normalizes).mp hx
  refine ⟨k, hk, ?_⟩
  rw [conjSub_mul, F1.conjSub_eq_of_mem_normalizer (S_le_normalizer_conjClosure hRO h hs)]

end CFSG.Quasithin.SzVB

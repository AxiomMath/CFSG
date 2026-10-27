module

public import CFSG.Quasithin.Vol2.Ch11SecHKB

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecH

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.InternalSec

variable {G : Type} [Group G]

theorem conjAct_mem_normalizer_autOn {W X : Subgroup G} {x : G}
    (hxW : x ∈ Subgroup.normalizer (W : Set G)) (hxX : x ∈ Subgroup.normalizer (X : Set G)) :
    conjAct W ⟨x, hxW⟩ ∈ Subgroup.normalizer (autOn X W : Set (MulAut ↥W)) :=
  CFSG.Quasithin.AutOn.conjAct_mem_normalizer_autOn _ hxX

theorem mem_autOn_conjSubgroup {X W : Subgroup G} {h : G} (hW : h ∈ Subgroup.normalizer (W : Set G))
    (σ : MulAut ↥W) : σ ∈ autOn (conjSubgroup X h) W ↔
      conjAct W ⟨h, hW⟩ * σ * (conjAct W ⟨h, hW⟩)⁻¹ ∈ autOn X W := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨⟨h, hW⟩ * z * ⟨h, hW⟩⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp⟩
    exact mem_conjSubgroup_iff.mp (Subgroup.mem_subgroupOf.mp hz)
  · rintro ⟨z, hz, hze⟩
    refine ⟨⟨h, hW⟩⁻¹ * z * ⟨h, hW⟩, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · rw [mem_conjSubgroup_iff]
      simpa [mul_assoc] using Subgroup.mem_subgroupOf.mp hz
    · rw [map_mul, map_mul, hze, map_inv]
      group

theorem autOn_mono {H₁ H₂ W : Subgroup G} (h : H₁ ≤ H₂) : autOn H₁ W ≤ autOn H₂ W :=
  Subgroup.map_mono fun _ hx => h hx

theorem mem_of_pow_two_pow_mem [Finite G] {S : Subgroup G} {x : G} {e : ℕ}
    (hx : x ^ 2 ^ e ∈ S) (hodd : Odd (orderOf x)) : x ∈ S := by
  rcases Nat.lt_or_ge 1 (orderOf x) with h1 | h1
  · have hcop : Nat.Coprime (2 ^ e) (orderOf x) :=
      Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hodd)
    obtain ⟨c, hc⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h1
    have : x = (x ^ 2 ^ e) ^ c := by
      rw [← pow_mul, ← pow_mod_orderOf, hc.2, pow_one]
    rw [this]
    exact S.pow_mem hx c
  · have : orderOf x = 1 := le_antisymm h1 (orderOf_pos x)
    rw [orderOf_eq_one_iff] at this
    rw [this]
    exact S.one_mem

theorem not_isPGroup_SL2 {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 2 ≤ n)
    (hF : Nat.card F = 2 ^ n) : ¬ IsPGroup 2 (Matrix.SpecialLinearGroup (Fin 2) F) := by
  intro h
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF] at hk
  have hodd : Odd ((2 ^ n) ^ 2 - 1) := by
    rw [← pow_mul]
    exact Nat.Even.sub_odd Nat.one_le_two_pow ((Nat.even_pow' (by omega)).mpr even_two) odd_one
  have hdvd : (2 ^ n) ^ 2 - 1 ∣ 2 ^ k := ⟨2 ^ n, by rw [← hk, mul_comm]⟩
  have h1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd))
    hdvd
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have : 16 ≤ (2 ^ n) ^ 2 := by nlinarith
  omega

theorem mem_normalizer_sup {A B : Subgroup G} {x : G} (hA : x ∈ Subgroup.normalizer (A : Set G))
    (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [← conjSubgroup_eq_iff_mem_normalizer]
  have hsup : conjSubgroup (A ⊔ B) x = conjSubgroup A x ⊔ conjSubgroup B x :=
    Subgroup.map_sup A B _
  rw [hsup, conjSubgroup_eq_iff_mem_normalizer.mpr hA, conjSubgroup_eq_iff_mem_normalizer.mpr hB]

variable [Finite G]

namespace Data

variable {T L I : Subgroup G} {n : ℕ} {V₁ H : Subgroup G} {g h y : G}
  (d : Data T L I n V₁ H g h y)
include d

theorem pCoreOf_le_T : pCoreOf 2 H ≤ T := F7.isSylowTwoOf_pCoreOf_le d.c.s.sylow

theorem pCoreOf_le_normalizer_V : pCoreOf 2 H ≤ Subgroup.normalizer (fsuV T I : Set G) :=
  d.pCoreOf_le_T.trans (SecA.T_le_normalizer_fsuV T I)

theorem pCoreOf_le_normalizer_Vh :
    pCoreOf 2 H ≤ Subgroup.normalizer (conjSubgroup (fsuV T I) h : Set G) := by
  intro x hx
  have hx' : h * x * h⁻¹ ∈ pCoreOf 2 H :=
    (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H d.c.hH)
      x).mp hx
  have hN := SecA.T_le_normalizer_fsuV T I (d.pCoreOf_le_T hx')
  rw [Subgroup.mem_normalizer_iff]
  intro z
  rw [mem_conjSubgroup_iff, mem_conjSubgroup_iff]
  have : h * (x * z * x⁻¹) * h⁻¹ = (h * x * h⁻¹) * (h * z * h⁻¹) * (h * x * h⁻¹)⁻¹ := by group
  rw [this]
  exact Subgroup.mem_normalizer_iff.mp hN _

theorem pCoreOf_le_normalizer_I : pCoreOf 2 H ≤
    Subgroup.normalizer ((fsuV T I ⊔ conjSubgroup (fsuV T I) h : Subgroup G) : Set G) :=
  fun _ hx => mem_normalizer_sup (d.pCoreOf_le_normalizer_V hx) (d.pCoreOf_le_normalizer_Vh hx)

theorem Vh_le_H : conjSubgroup (fsuV T I) h ≤ H := by
  intro x hx
  have h1 := d.c.V_le_H (mem_conjSubgroup_iff.mp hx)
  have : x = h⁻¹ * (h * x * h⁻¹) * h := by group
  rw [this]
  exact H.mul_mem (H.mul_mem (H.inv_mem d.c.hH) h1) d.c.hH

theorem not_le_centralizer : ¬ fsuV T I ≤ Subgroup.centralizer (VZ T H : Set G) := by
  have := d.c.s.hAC
  rwa [← d.Vg] at this

theorem vhStar_ne : autOn (conjSubgroup (fsuV T I) h) (VZ T H) ≠ autOn (fsuV T I) (VZ T H) := by
  intro heq
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := d.kStar
  have hHN := SecC.le_normalizer_VZ T H
  let Nst : Subgroup G := ((Subgroup.normalizer (autOn (fsuV T I) (VZ T H) :
    Set (MulAut ↥(VZ T H)))).comap (conjAct (VZ T H))).map
      (Subgroup.normalizer (VZ T H : Set G)).subtype
  have hmemN : ∀ x (hx : x ∈ Subgroup.normalizer (VZ T H : Set G)),
      conjAct (VZ T H) ⟨x, hx⟩ ∈ Subgroup.normalizer (autOn (fsuV T I) (VZ T H) :
        Set (MulAut ↥(VZ T H))) → x ∈ Nst := fun x hx hN => ⟨⟨x, hx⟩, hN, rfl⟩
  have hTY : T ≤ H ⊓ Nst := fun t ht => ⟨d.c.s.T_le ht, hmemN t _
    (conjAct_mem_normalizer_autOn (hHN (d.c.s.T_le ht)) (SecA.T_le_normalizer_fsuV T I ht))⟩
  have hhY : h ∈ H ⊓ Nst := by
    refine ⟨d.c.hH, hmemN h (hHN d.c.hH) ?_⟩
    rw [Subgroup.mem_normalizer_iff]
    intro σ
    rw [← mem_autOn_conjSubgroup (hHN d.c.hH), heq]
  have hInH : InH T (H ⊓ Nst) := by
    refine ⟨hTY, fun hbot => d.c.s.h31.hstar.1.2 ?_⟩
    have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (d.pCoreOf_le_T.trans hTY)
      (inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
    rw [hbot] at hle
    exact le_bot_iff.mp hle
  have hYM : H ⊓ Nst ≤ Subgroup.normalizer (L : Set G) := by
    by_contra hYM
    have hYH := d.c.s.h31.hstar.2.2 _ hInH inf_le_left hYM
    have hK : ∀ z : ↥(Subgroup.normalizer (VZ T H : Set G)), (z : G) ∈ oTwoUpper H →
        conjAct (VZ T H) z ∈ Subgroup.normalizer (autOn (fsuV T I) (VZ T H) :
          Set (MulAut ↥(VZ T H))) := by
      intro z hz
      have hzY : (z : G) ∈ H ⊓ Nst := by
        rw [hYH]
        exact oTwoUpper_le H hz
      obtain ⟨z', hz', hzz⟩ := hzY.2
      have : z' = z := Subtype.ext hzz
      exact this ▸ hz'
    have hnorm : ((autOn (fsuV T I) (VZ T H)).subgroupOf (autOn (oTwoUpper H) (VZ T H))).Normal :=
      by
      refine ⟨fun a ha b => ?_⟩
      obtain ⟨z, hz, hzb⟩ := b.2
      rw [Subgroup.mem_subgroupOf] at ha ⊢
      have := (Subgroup.mem_normalizer_iff.mp (hK z (Subgroup.mem_subgroupOf.mp hz)) a).mp ha
      rw [hzb] at this
      simpa using this
    have : IsSimpleGroup ↥(autOn (oTwoUpper H) (VZ T H)) := by
      have := SecC.isSimpleGroup_SL2 d.c.two_le hF
      exact e.isSimpleGroup
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((autOn (fsuV T I) (VZ T H)).subgroupOf (autOn (oTwoUpper H) (VZ T H))) with hb | ht
    · apply d.not_le_centralizer
      intro v hv
      have hvs : conjAct (VZ T H) ⟨v, hHN (d.c.V_le_H hv)⟩ ∈ autOn (fsuV T I) (VZ T H) :=
        ⟨_, Subgroup.mem_subgroupOf.mpr hv, rfl⟩
      have hdisj := Subgroup.subgroupOf_eq_bot.mp hb
      exact (conjAct_eq_one_iff _ _).mp (Subgroup.disjoint_def.mp hdisj hvs (d.sylow.1 hvs))
    · apply not_isPGroup_SL2 d.c.two_le hF
      have h2 : IsPGroup 2 ↥(autOn (oTwoUpper H) (VZ T H)) := by
        intro σ
        have hσ : (σ : MulAut ↥(VZ T H)) ∈ autOn (fsuV T I) (VZ T H) := by
          have : σ ∈ (autOn (fsuV T I) (VZ T H)).subgroupOf (autOn (oTwoUpper H) (VZ T H)) :=
            ht ▸ Subgroup.mem_top σ
          exact Subgroup.mem_subgroupOf.mp this
        obtain ⟨k, hk⟩ := d.sylow.2.1 ⟨σ, hσ⟩
        exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
      exact h2.of_equiv e
  exact d.c.hM (hYM hhY)

theorem vhStar_sylow : QuasithinUnique.IsSylowTwoOf (autOn (conjSubgroup (fsuV T I) h) (VZ T H))
    (autOn (oTwoUpper H) (VZ T H)) := by
  have hHN := SecC.le_normalizer_VZ T H
  have heq : autOn (conjSubgroup (fsuV T I) h) (VZ T H) =
      conjSubgroup (autOn (fsuV T I) (VZ T H)) (conjAct (VZ T H) ⟨h, hHN d.c.hH⟩) := by
    ext σ
    rw [mem_autOn_conjSubgroup (hHN d.c.hH), mem_conjSubgroup_iff]
  have hψK : conjAct (VZ T H) ⟨h, hHN d.c.hH⟩ ∈
      Subgroup.normalizer (autOn (oTwoUpper H) (VZ T H) : Set (MulAut ↥(VZ T H))) :=
    SecC.Set37.hStar_le_normalizer_kStar T H ⟨⟨h, _⟩, Subgroup.mem_subgroupOf.mpr d.c.hH, rfl⟩
  have hKs := conjSubgroup_eq_iff_mem_normalizer.mpr hψK
  rw [heq]
  refine ⟨?_, d.sylow.2.1.map _, ?_⟩
  · rw [← hKs]
    exact E3.conjSubgroup_mono_left _ d.sylow.1
  · have h1 := d.sylow.2.2
    change ¬ 2 ∣ (conjSubgroup (autOn (fsuV T I) (VZ T H)) _).relIndex _
    rw [← hKs]
    change ¬ 2 ∣ ((autOn (fsuV T I) (VZ T H)).map _).relIndex ((autOn (oTwoUpper H) (VZ T H)).map _)
    rw [Subgroup.relIndex_map_map_of_injective _ _ (MulEquiv.injective _)]
    exact h1

theorem K_le_I (i : Inp32) : oTwoUpper H ≤ fsuV T I ⊔ conjSubgroup (fsuV T I) h := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := d.kStar
  have hHN := SecC.le_normalizer_VZ T H
  have hsup := sup_eq_of_sylow i.hKF5 d.c.two_le hF e d.sylow d.vhStar_sylow
    (Ne.symm d.vhStar_ne)
  have hKs : autOn (oTwoUpper H) (VZ T H) ≤
      autOn (fsuV T I ⊔ conjSubgroup (fsuV T I) h) (VZ T H) := by
    rw [← hsup]
    exact sup_le (autOn_mono le_sup_left) (autOn_mono le_sup_right)
  have hIH : fsuV T I ⊔ conjSubgroup (fsuV T I) h ≤ H := sup_le d.c.V_le_H d.Vh_le_H
  have hKIO : ∀ k ∈ oTwoUpper H,
      k ∈ (fsuV T I ⊔ conjSubgroup (fsuV T I) h) ⊔ pCoreOf 2 H := by
    intro k hk
    have hkN := hHN (oTwoUpper_le H hk)
    obtain ⟨z, hz, hze⟩ := hKs ⟨⟨k, hkN⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
    have h1 : conjAct (VZ T H) (z⁻¹ * ⟨k, hkN⟩) = 1 := by
      rw [map_mul, map_inv, hze, inv_mul_cancel]
    have hc := (conjAct_eq_one_iff _ _).mp h1
    have hzI := Subgroup.mem_subgroupOf.mp hz
    have ho : (z : G)⁻¹ * k ∈ pCoreOf 2 H :=
      d.c.centralizer_VZ_le i.h1135 i.h1136 ⟨H.mul_mem (H.inv_mem (hIH hzI)) (oTwoUpper_le H hk),
        by simpa using hc⟩
    have : k = (z : G) * ((z : G)⁻¹ * k) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hzI) (Subgroup.mem_sup_right ho)
  have hpow := two_of_sup (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
    d.pCoreOf_le_normalizer_I
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨hxH, hodd⟩
  obtain ⟨e', he'⟩ := hpow x (hKIO x (mem_oTwoUpper_of_odd hxH hodd))
  exact mem_of_pow_two_pow_mem he' hodd

end Data

end CFSG.Quasithin.Vol2.Ch11.SecH

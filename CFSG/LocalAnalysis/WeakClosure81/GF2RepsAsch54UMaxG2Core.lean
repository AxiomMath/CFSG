module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54UMaxG2Frame
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512WrAbs
import CFSG.GroupTheory.CoprimeActionSupport.NormalPSubgroupMeetsCenter
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205GRow
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch80G2

open Subgroup
open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique
open CFSG.Blueprint (LieModel)

open CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab (z₀ orderOf_z₀ z₀_ne_one)
open CFSG.LocalAnalysis.WeakClosure81.Asch80Wr (normalizer_ne_top_of_le le_normalizer_inf_of_normal
  exists_map_conj_eq)


variable {Y : Type} [Group Y]

private theorem g2Core_exists_inv {E : Subgroup Y} {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hE : LieModel ↥E .G2 0 r 1) : ∃ x ∈ E, x * x = 1 ∧ x ≠ 1 := by
  obtain ⟨F, _, _, hcard, ⟨φ⟩⟩ := CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.exists_equiv_of_lieModel hE
  have hchar : ringChar F ≠ 2 := CFSG.RankThree.PartOne.ringChar_ne_two_of_odd_card
    (CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.odd_card_of_model hr hr2 hcard)
  have ho := orderOf_z₀ hchar
  have h1 : z₀ F * z₀ F = 1 := by
    rw [← pow_two, ← ho, pow_orderOf_eq_one]
  refine ⟨(φ.symm (z₀ F) : Y), (φ.symm (z₀ F)).2, ?_, ?_⟩
  · rw [← Subgroup.coe_mul, ← map_mul, h1, map_one, Subgroup.coe_one]
  · intro h
    apply z₀_ne_one hchar
    apply φ.symm.injective
    rw [map_one]
    exact Subtype.ext h

private theorem g2Core_inf_ne_bot [Finite Y] {E : Subgroup Y} (hEn : E.Normal) (S : Sylow 2 Y)
    {x : Y} (hxE : x ∈ E) (hx2 : x * x = 1) (hx1 : x ≠ 1) : (S : Subgroup Y) ⊓ E ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (zpowers x) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := exists_map_conj_eq Q S
  intro hbot
  have hmem : g * x * g⁻¹ ∈ (S : Subgroup Y) ⊓ E := by
    refine mem_inf.2 ⟨?_, hEn.conj_mem x hxE g⟩
    have h := mem_map_of_mem (MulAut.conj g).toMonoidHom (hQ (mem_zpowers x))
    rw [hg] at h
    simpa using h
  rw [hbot, mem_bot, conj_eq_one_iff] at hmem
  exact hx1 hmem

private theorem g2Core_exists_central_inv [Finite Y] {T E : Subgroup Y} [E.Normal]
    (hT : IsPGroup 2 T) (hTE : T ⊓ E ≠ ⊥) :
    ∃ z ∈ E, z * z = 1 ∧ z ≠ 1 ∧ T ≤ centralizer ({z} : Set Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : E.subgroupOf T ≠ ⊥ := by
    intro h
    apply hTE
    rw [eq_bot_iff]
    intro y hy
    have : (⟨y, (mem_inf.1 hy).1⟩ : ↥T) ∈ E.subgroupOf T := mem_subgroupOf.2 (mem_inf.1 hy).2
    rw [h, mem_bot] at this
    exact mem_bot.2 (congrArg Subtype.val this)
  obtain ⟨⟨k, hk⟩, hk1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
    (CFSG.GroupTheory.CoprimeActionSupport.NormalPSubgroupMeetsCenter.inf_center_ne_bot hT _ hN)
  obtain ⟨hkN, hkZ⟩ := mem_inf.1 hk
  have hkE : (k : Y) ∈ E := mem_subgroupOf.1 hkN
  have hkc : ∀ t ∈ T, t * (k : Y) = (k : Y) * t := fun t ht =>
    congrArg Subtype.val (mem_center_iff.1 hkZ ⟨t, ht⟩)
  have hk1' : (k : Y) ≠ 1 := fun h => hk1 (Subtype.ext (Subtype.ext h))
  obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.mp hT k
  rw [← Subgroup.orderOf_coe] at hm
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hm
    exact hk1' hm
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  refine ⟨(k : Y) ^ 2 ^ n, pow_mem hkE _, ?_, ?_, ?_⟩
  · rw [← pow_add, show 2 ^ n + 2 ^ n = orderOf (k : Y) by rw [hm, pow_succ]; ring,
      pow_orderOf_eq_one]
  · refine pow_ne_one_of_lt_orderOf (by positivity) ?_
    rw [hm]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  · intro t ht
    rw [mem_centralizer_singleton_iff]
    exact (Commute.pow_right (hkc t ht : Commute t (k : Y)) (2 ^ n)).eq

private theorem g2Core_mem_normalizer {V : Subgroup Y} {c : Y}
    (hmap : V.map (MulAut.conj c).toMonoidHom = V) : c ∈ normalizer (V : Set Y) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← hmap]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← hmap] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by simpa [MulAut.conj_apply] using hyx
    rwa [← this]

theorem eq_top_of_gen
    [Finite Y] {E T : Subgroup Y} {r : ℕ}
    (hEn : E.Normal) (hr : r.Prime) (hr2 : r ≠ 2) (hE : LieModel ↥E .G2 0 r 1)
    (hC : centralizer (E : Set Y) = ⊥) (hT : IsSylowIn 2 T ⊤)
    (hgen : ∀ z z' : ↥E, z * z = 1 → z' * z' = 1 → z ≠ 1 → z' ≠ 1 → z ≠ z' →
      z * z' = z' * z → (∀ w : ↥E, (∀ x : ↥E, x * z = z * x → w * x = x * w) → w = 1 ∨ w = z) →
      centralizer ({z} : Set ↥E) ⊔ centralizer {z'} = ⊤) {M : Subgroup Y}
    (hCzM : ∀ z ∈ E, z * z = 1 → z ≠ 1 → T ≤ centralizer ({z} : Set Y) →
      centralizer ({z} : Set Y) < ⊤ → centralizer ({z} : Set Y) ≤ M)
    (hNVM : ∀ z ∈ E, z * z = 1 → z ≠ 1 → T ≤ centralizer ({z} : Set Y) → ∀ u ∈ sqCent E z,
      u * u = 1 → u ∉ zpowers z → T ≤ normalizer ((zpowers z ⊔ zpowers u : Subgroup Y) : Set Y) →
      normalizer ((zpowers z ⊔ zpowers u : Subgroup Y) : Set Y) < ⊤ →
      normalizer ((zpowers z ⊔ zpowers u : Subgroup Y) : Set Y) ≤ M)
    (hNTM : normalizer ((T ⊓ E : Subgroup Y) : Set Y) < ⊤ →
      normalizer ((T ⊓ E : Subgroup Y) : Set Y) ≤ M) :
    M = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hEn
  have hTi : ¬ 2 ∣ T.index := by
    have h := hT.2.2
    rwa [relIndex_top_right] at h
  let S : Sylow 2 Y := hT.2.1.toSylow hTi
  have hST : (S : Subgroup Y) = T := rfl
  have hT2 : IsPGroup 2 T := hT.2.1
  have hEs : IsSimpleGroup ↥E :=
    CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.isSimpleGroup_of_lieModel_g2 hr2 hE
  have hEab : ∀ e ∈ E, (∀ x ∈ E, e * x = x * e) → e = 1 := fun e _ h => by
    have : e ∈ centralizer (E : Set Y) := mem_centralizer_iff.2 fun x hx => (h x hx).symm
    rw [hC, mem_bot] at this
    exact this
  obtain ⟨x, hxE, hx2, hx1⟩ := g2Core_exists_inv hr hr2 hE
  have hT₀1 : (S : Subgroup Y) ⊓ E ≠ ⊥ := g2Core_inf_ne_bot hEn S hxE hx2 hx1
  obtain ⟨z, hzE, hz2, hz1, hTz⟩ := g2Core_exists_central_inv hT2 (hST ▸ hT₀1)
  have hE2 : ¬ IsPGroup 2 ↥E := by
    intro h2
    have : Nontrivial ↥E := ⟨⟨⟨z, hzE⟩, 1, fun h => hz1 (congrArg Subtype.val h)⟩⟩
    have hZ := h2.center_nontrivial
    rcases hEs.eq_bot_or_eq_top_of_normal (center ↥E) with h | h
    · exact ((Subgroup.nontrivial_iff_ne_bot _).mp hZ) h
    · apply hz1
      refine hEab z hzE fun y hy => ?_
      have hzc : (⟨z, hzE⟩ : ↥E) ∈ center ↥E := by
        rw [h]
        trivial
      exact (congrArg Subtype.val (mem_center_iff.mp hzc ⟨y, hy⟩)).symm
  have hTE : T ≤ normalizer (E : Set Y) := by
    rw [normalizer_eq_top_iff.mpr hEn]
    exact le_top
  obtain ⟨J₁, J₂, hJ⟩ := exists_sl2Pair hr hr2 hE hzE hz2 hz1
  obtain ⟨u, hu, hu2, huz, hTV⟩ := hJ.exists_le_normalizer hT2 hTE hTz
  have huE : u ∈ E := sqCent_le E z hu
  have hu1 : u ≠ 1 := fun h => huz (by rw [h]; exact one_mem _)
  have hzu : z * u = u * z :=
    (mem_centralizer_singleton_iff.1 (sqCent_le_centralizer E z hu)).symm
  have hsqV : ∀ g ∈ zpowers z ⊔ zpowers u, g * g = 1 := by
    intro g hg
    rcases mem_sup_zpowers hz2 hu2 hzu hg with h | h | h | h <;> rw [h]
    · exact one_mul 1
    · exact hz2
    · exact hu2
    · calc z * u * (z * u) = z * (u * z) * u := by group
        _ = z * (z * u) * u := by rw [hzu]
        _ = z * z * (u * u) := by group
        _ = 1 := by rw [hz2, hu2, one_mul]
  have hV2 : IsPGroup 2 ↥(zpowers z ⊔ zpowers u : Subgroup Y) := fun g => ⟨1, Subtype.ext (by
    rw [pow_one, pow_two, Subgroup.coe_mul, Subgroup.coe_one]
    exact hsqV g g.2)⟩
  have hVE : zpowers z ⊔ zpowers u ≤ E := sup_le (zpowers_le.2 hzE) (zpowers_le.2 huE)
  have hV1 : zpowers z ⊔ zpowers u ≠ ⊥ := fun h => hz1 (by
    have : z ∈ zpowers z ⊔ zpowers u := mem_sup_left (mem_zpowers z)
    rwa [h, mem_bot] at this)
  have hNV : normalizer ((zpowers z ⊔ zpowers u : Subgroup Y) : Set Y) ≤ M :=
    hNVM z hzE hz2 hz1 hTz u hu hu2 huz hTV
      (lt_top_iff_ne_top.mpr (normalizer_ne_top_of_le hEs hE2 hVE hV2 hV1))
  have hCz : centralizer ({z} : Set Y) ≤ M := by
    refine hCzM z hzE hz2 hz1 hTz (lt_top_iff_ne_top.mpr fun htop => hz1 ?_)
    refine hEab z hzE fun y _ => ?_
    have : y ∈ centralizer ({z} : Set Y) := by
      rw [htop]
      trivial
    exact (mem_centralizer_singleton_iff.1 this).symm
  obtain ⟨K₁, K₂, hK⟩ := exists_sl2Pair hr hr2 hE huE hu2 hu1
  obtain ⟨c, -, hcu, hcz⟩ := hK.exists_swap (hJ.mem_sqCent_of_mem hu hu2 huz) hz2
    (hJ.not_mem_zpowers hu2 huz)
  have hcu' : c * u * c⁻¹ = u := by rw [hcu]; group
  have hcV : c ∈ normalizer ((zpowers z ⊔ zpowers u : Subgroup Y) : Set Y) := by
    refine g2Core_mem_normalizer ?_
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.conj_apply, hcz, hcu']
    apply le_antisymm
    · exact sup_le (zpowers_le.2 (mul_mem (mem_sup_left (mem_zpowers z))
        (mem_sup_right (mem_zpowers u)))) le_sup_right
    · refine sup_le (zpowers_le.2 ?_) le_sup_right
      have h1 : z * u * u ∈ zpowers (z * u) ⊔ zpowers u :=
        mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_zpowers u))
      rwa [mul_assoc, hu2, mul_one] at h1
  have hcM : c ∈ M := hNV hcV
  have hzu' : c⁻¹ * (z * u) * c = z := by rw [← hcz]; group
  have hCzu : ∀ y : Y, y * (z * u) = z * u * y → y ∈ M := by
    intro y hy
    have h1 : c⁻¹ * y * c ∈ centralizer ({z} : Set Y) := by
      rw [mem_centralizer_singleton_iff]
      calc c⁻¹ * y * c * z = c⁻¹ * y * c * (c⁻¹ * (z * u) * c) := by rw [hzu']
        _ = c⁻¹ * (y * (z * u)) * c := by group
        _ = c⁻¹ * (z * u * y) * c := by rw [hy]
        _ = c⁻¹ * (z * u) * c * (c⁻¹ * y * c) := by group
        _ = z * (c⁻¹ * y * c) := by rw [hzu']
    have h2 : y = c * (c⁻¹ * y * c) * c⁻¹ := by group
    rw [h2]
    exact mul_mem (mul_mem hcM (hCz h1)) (inv_mem hcM)
  have hzu2 : z * u * (z * u) = 1 :=
    hsqV _ (mul_mem (mem_sup_left (mem_zpowers z)) (mem_sup_right (mem_zpowers u)))
  have hzu1 : z * u ≠ 1 := by
    intro h
    apply huz
    rw [show u = z⁻¹ by rw [eq_inv_iff_mul_eq_one, ← hzu, h], inv_eq_of_mul_eq_one_right hz2]
    exact mem_zpowers z
  have hgen' := hgen ⟨z, hzE⟩ ⟨z * u, mul_mem hzE huE⟩ (Subtype.ext hz2) (Subtype.ext hzu2)
    (fun h => hz1 (congrArg Subtype.val h)) (fun h => hzu1 (congrArg Subtype.val h))
    (fun h => hu1 (by
      have h' : z = z * u := congrArg Subtype.val h
      calc u = z⁻¹ * (z * u) := by group
        _ = 1 := by rw [← h', inv_mul_cancel]))
    (Subtype.ext (by
      show z * (z * u) = z * u * z
      rw [mul_assoc, hzu, ← mul_assoc]))
    (fun w hw => by
      have hwz : (w : Y) * z = z * w := congrArg Subtype.val (hw ⟨z, hzE⟩ rfl)
      have hw' := hJ.cent w w.2 hwz fun y hy => congrArg Subtype.val (hw ⟨y, sqCent_le E z hy⟩
        (Subtype.ext (mem_centralizer_singleton_iff.1 (sqCent_le_centralizer E z hy))))
      rcases hJ.mem_zpowers_iff.1 hw' with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h))
  have hEM : E ≤ M := by
    intro y hy
    have hy' : (⟨y, hy⟩ : ↥E) ∈ centralizer ({(⟨z, hzE⟩ : ↥E)} : Set ↥E) ⊔
        centralizer {(⟨z * u, mul_mem hzE huE⟩ : ↥E)} := by
      rw [hgen']
      trivial
    have hle : centralizer ({(⟨z, hzE⟩ : ↥E)} : Set ↥E) ⊔
        centralizer {(⟨z * u, mul_mem hzE huE⟩ : ↥E)} ≤ M.comap E.subtype := by
      refine sup_le (fun a ha => ?_) (fun a ha => ?_)
      · exact hCz (mem_centralizer_singleton_iff.2
          (congrArg Subtype.val (mem_centralizer_singleton_iff.1 ha)))
      · exact hCzu a (congrArg Subtype.val (mem_centralizer_singleton_iff.1 ha))
    exact hle hy'
  set T₀ := (S : Subgroup Y) ⊓ E with hT₀
  have hST₀ : (S : Subgroup Y) ≤ normalizer (T₀ : Set Y) := le_normalizer_inf_of_normal
  have hT₀2 : IsPGroup 2 T₀ := S.isPGroup'.to_inf_left
  have hNT₀M : normalizer (T₀ : Set Y) ≤ M :=
    hNTM (lt_top_iff_ne_top.mpr (normalizer_ne_top_of_le hEs hE2 inf_le_right hT₀2 hT₀1))
  obtain ⟨P, hP⟩ := CFSG.HardMathSupport.Foote.E27.exists_sylow_subgroupOf_eq E S
  have hPmap : (P : Subgroup E).map E.subtype = T₀ := by
    rw [hP, subgroupOf_map_subtype]
  have hfr := Sylow.normalizer_sup_eq_top P
  rw [hPmap] at hfr
  exact top_le_iff.mp (hfr ▸ sup_le hNT₀M hEM)

theorem not_hasUniqueMaxOver_of_gen
    [Finite Y] {E T : Subgroup Y} {r : ℕ}
    (hEn : E.Normal) (hr : r.Prime) (hr2 : r ≠ 2) (hE : LieModel ↥E .G2 0 r 1)
    (hC : centralizer (E : Set Y) = ⊥) (hT : IsSylowIn 2 T ⊤)
    (hgen : ∀ z z' : ↥E, z * z = 1 → z' * z' = 1 → z ≠ 1 → z' ≠ 1 → z ≠ z' →
      z * z' = z' * z → (∀ w : ↥E, (∀ x : ↥E, x * z = z * x → w * x = x * w) → w = 1 ∨ w = z) →
      centralizer ({z} : Set ↥E) ⊔ centralizer {z'} = ⊤) :
    ¬ HasUniqueMaxOver T := by
  rintro ⟨M, hMt, hM⟩
  have hTE : T ≤ normalizer ((T ⊓ E : Subgroup Y) : Set Y) := by
    have := hEn
    exact le_normalizer_inf_of_normal
  exact hMt.ne (eq_top_of_gen hEn hr hr2 hE hC hT hgen
    (fun _ _ _ _ hTz hlt => hM _ hTz hlt) (fun _ _ _ _ _ _ _ _ _ hTV hlt => hM _ hTV hlt)
    (fun hlt => hM _ hTE hlt))

end CFSG.LocalAnalysis.WeakClosure81.Asch80G2

end

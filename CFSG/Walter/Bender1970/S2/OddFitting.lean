module

import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Walter.Bender1970.S2.Layer
public import CFSG.Walter.Bender1970.S2.PGroup

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter
open scoped Pointwise commutatorElement

@[expose] def oStar (X : Type*) [Group X] : Subgroup X :=
  (generalizedFittingSubgroupOf (⊤ : Subgroup (X ⧸ pPrimeCore 2 X))).comap
    (QuotientGroup.mk' (pPrimeCore 2 X))

section OStar

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem oStar_normal : (oStar X).Normal := by
  have : (generalizedFittingSubgroupOf (⊤ : Subgroup (X ⧸ pPrimeCore 2 X))).Normal :=
    normal_of_isNormalIn_top' (generalizedFittingSubgroupOf_isNormalIn ⊤)
  exact Subgroup.Normal.comap inferInstance _

omit [Finite X] in
theorem pPrimeCore_le_oStar : pPrimeCore 2 X ≤ oStar X := by
  intro x hx
  show QuotientGroup.mk' (pPrimeCore 2 X) x ∈
    generalizedFittingSubgroupOf (⊤ : Subgroup (X ⧸ pPrimeCore 2 X))
  rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
  exact one_mem _

omit [Finite X] in
theorem le_oStar_of_isPGroup (hX : IsAStar X) {P : Subgroup X} (hP : IsPGroup 2 P) :
    P ≤ oStar X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set q := QuotientGroup.mk' (pPrimeCore 2 X)
  set F := generalizedFittingSubgroupOf (⊤ : Subgroup (X ⧸ pPrimeCore 2 X))
  have hFn : F.Normal := normal_of_isNormalIn_top' (generalizedFittingSubgroupOf_isNormalIn ⊤)
  intro x hx
  show q x ∈ F
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  have h1 : (QuotientGroup.mk' F (q x)) ^ (2 ^ k) = 1 := by
    rw [← map_pow, ← map_pow]
    have : x ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    rw [this, map_one, map_one]
  have h2 : orderOf (QuotientGroup.mk' F (q x)) ∣ F.index := by
    rw [Subgroup.index_eq_card]
    exact orderOf_dvd_natCard _
  have h3 : orderOf (QuotientGroup.mk' F (q x)) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2
      (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hX.2.1))) (orderOf_dvd_of_pow_eq_one h1)
  rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
  exact h3

theorem oStar_le_normalizer (hX : IsAStar X) {E : Subgroup X} (hE : IsComponentOf E ⊤) :
    oStar X ≤ Subgroup.normalizer (E : Set X) := by
  classical
  set q := QuotientGroup.mk' (pPrimeCore 2 X) with hq
  obtain ⟨hEb, -, -⟩ := hX.component_image hE
  set Eb := E.map q with hEbdef
  intro x hx
  have h1 : q x ∈ Subgroup.normalizer (Eb : Set (X ⧸ pPrimeCore 2 X)) :=
    (generalizedFittingSubgroupOf_le_actingAs hEb hx).1
  set E' := E.map (MulAut.conj x).toMonoidHom with hE'def
  have hE' : IsComponentOf E' ⊤ := isComponentOf_map_conj hE (by
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact Subgroup.mem_top x)
  rcases isComponentOf_eq_or_commutator_eq_bot hE hE' with h | h
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [h]
      exact ⟨y, hy, rfl⟩
    · intro hy
      rw [h] at hy
      obtain ⟨e, he, hey⟩ := hy
      have : e = y := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hey
        exact mul_left_cancel (mul_right_cancel hey)
      rwa [← this]
  · exfalso
    have hEbE' : Eb ≤ E'.map q := by
      rintro _ ⟨e, he, rfl⟩
      have h2 : (q x)⁻¹ * q e * q x ∈ Eb := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ h1) (q e)).mp ⟨e, he, rfl⟩
        simpa using this
      obtain ⟨e', he', he'eq⟩ := h2
      refine ⟨x * e' * x⁻¹, ⟨e', he', rfl⟩, ?_⟩
      rw [map_mul, map_mul, map_inv, he'eq]
      group
    have h3 : ⁅Eb, Eb⁆ = ⊥ := by
      rw [← le_bot_iff]
      calc ⁅Eb, Eb⁆ ≤ ⁅E.map q, E'.map q⁆ := Subgroup.commutator_mono le_rfl hEbE'
        _ = (⁅E, E'⁆).map q := (Subgroup.map_commutator _ _ _).symm
        _ = ⊥ := by rw [h, Subgroup.map_bot]
    obtain ⟨a, b, hab⟩ := exists_mul_ne_mul_of_isQuasisimple hEb.2.2
    apply hab
    have h4 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3 a.2
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp h4 b b.2).symm

end OStar

theorem centralizer_sylow_le_normalizer {X : Type*} [Group X] [Finite X]
    (hY : HasAbelianSylowTwo X) (T : Sylow 2 X) {E : Subgroup X} (hE : IsComponentOf E ⊤) :
    Subgroup.centralizer ((T : Subgroup X) : Set X) ≤ Subgroup.normalizer (E : Set X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd := odd_card_center_of_isQuasisimple hE.2.2 (hY.subgroup E)
  obtain ⟨⟨x, hxT, hxE⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (sylow_inf_ne_bot_of_isSubnormal T (isSubnormal_of_isComponentOf hE)
      (IsQuasisimple.two_dvd_card hE.2.2))
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  intro c hc
  set E' := E.map (MulAut.conj c).toMonoidHom with hE'def
  have hE' : IsComponentOf E' ⊤ := isComponentOf_map_conj hE (by
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact Subgroup.mem_top c)
  rcases isComponentOf_eq_or_commutator_eq_bot hE hE' with h | h
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [h]
      exact ⟨y, hy, rfl⟩
    · intro hy
      rw [h] at hy
      obtain ⟨e, he, hey⟩ := hy
      have : e = y := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hey
        exact mul_left_cancel (mul_right_cancel hey)
      rwa [← this]
  · exfalso
    have hcx : c * x * c⁻¹ = x := by
      rw [(Subgroup.mem_centralizer_iff.mp hc x hxT).symm, mul_inv_cancel_right]
    have hxE' : x ∈ E' := ⟨x, hxE, by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hcx]⟩
    have hxZ : (⟨x, hxE⟩ : E) ∈ Subgroup.center E := by
      rw [Subgroup.mem_center_iff]
      intro k
      apply Subtype.ext
      have hkC := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h k.2
      exact ((Subgroup.mem_centralizer_iff.mp hkC) x hxE').symm
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp T.isPGroup') ⟨x, hxT⟩
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hj
      exact hx1' (congrArg Subtype.val hj)
    have h2 : 2 ∣ orderOf (⟨⟨x, hxE⟩, hxZ⟩ : Subgroup.center E) := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
      rw [Subgroup.orderOf_mk] at hj
      rw [hj]
      exact dvd_pow_self 2 hj0
    exact (Nat.not_even_iff_odd.mpr hodd)
      (even_iff_two_dvd.mpr (h2.trans (orderOf_dvd_natCard _)))

theorem le_sup_commutator_of_coprime {G : Type*} [Group G] [Finite G] {U T : Subgroup G}
    (hTU : T ≤ Subgroup.normalizer (U : Set G)) (hU : Group.IsSolvable U)
    (hcop : Nat.Coprime (Nat.card T) (Nat.card U)) :
    U ≤ (U ⊓ Subgroup.centralizer (T : Set G)) ⊔ ⁅U, T⁆ := by
  have : Subgroup.Normalizes T U := ⟨hTU⟩
  have h := CFSG.fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime (G := U)
    (A := T) hU hcop
  have h2 := congrArg (Subgroup.map U.subtype) h
  rw [Subgroup.map_sup, CFSG.commutatorAction_subgroup_conj_map_eq_commutator U T hTU,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
  have hfix : (CFSG.fixedPointSubgroup T U).map U.subtype ≤
      U ⊓ Subgroup.centralizer (T : Set G) := by
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨u.2, ?_⟩
    show (u : G) ∈ Subgroup.centralizer (T : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h3 : (⟨s, hs⟩ : T) • u = u := hu ⟨s, hs⟩
    have h4 := congrArg Subtype.val h3
    rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] at h4
    calc s * (u : G) = (s * u * s⁻¹) * s := by group
      _ = u * s := by rw [h4]
  intro x hx
  rw [← h2] at hx
  exact sup_le_sup hfix le_rfl hx

section OddFitting

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem normalizer_le_normalizer_map_of_characteristic {A : Subgroup X} (D : Subgroup A)
    [D.Characteristic] : Subgroup.normalizer (A : Set X) ≤
      Subgroup.normalizer ((D.map A.subtype : Subgroup X) : Set X) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_mem_map_of_characteristic hg hx, fun hx => ?_⟩
  have h1 := conj_mem_map_of_characteristic (Subgroup.inv_mem _ hg) hx
  simpa [mul_assoc] using h1

theorem odd_card_oddCoreOf (A : Subgroup X) : Odd (Nat.card (oddCoreOf A)) := by
  rw [oddCoreOf, Subgroup.card_map_of_injective A.subtype_injective]
  exact Nat.coprime_two_left.mp pPrimeCore_coprime_card

theorem oddFitting_le_sup_commutator (hX : IsAStar X) {t : X} (T : Sylow 2 X)
    (htT : t ∈ (T : Subgroup X)) :
    let U := oddCoreOf (CFSG.fittingSubgroupOf (Subgroup.centralizer ({t} : Set X)))
    (T : Subgroup X) ≤ Subgroup.normalizer (U : Set X) ∧
      U ≤ (U ⊓ Subgroup.centralizer ((T : Subgroup X) : Set X)) ⊔ ⁅U, (T : Subgroup X)⁆ ∧
      ⁅U, (T : Subgroup X)⁆ ≤ oStar X := by
  intro U
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTab := hX.1 T
  set C := Subgroup.centralizer ({t} : Set X) with hC
  set FC := CFSG.fittingSubgroupOf C with hFC
  have hTC : (T : Subgroup X) ≤ C := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mpr (setLike_mul_comm hs htT)
  have hTU : (T : Subgroup X) ≤ Subgroup.normalizer (U : Set X) :=
    (hTC.trans (le_normalizer_of_isNormalIn (fittingSubgroupOf_isNormalIn C))).trans
      (normalizer_le_normalizer_map_of_characteristic (pPrimeCore 2 FC))
  have hUodd : Odd (Nat.card U) := odd_card_oddCoreOf FC
  have hUsolv : Group.IsSolvable U := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hUodd
  have hcop : Nat.Coprime (Nat.card (T : Subgroup X)) (Nat.card U) := by
    obtain ⟨k, hk⟩ := T.isPGroup'.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hUodd)
  refine ⟨hTU, le_sup_commutator_of_coprime hTU hUsolv hcop, ?_⟩
  have hTO : (T : Subgroup X) ≤ oStar X := le_oStar_of_isPGroup hX T.isPGroup'
  have : (oStar X).Normal := oStar_normal
  calc ⁅U, (T : Subgroup X)⁆ ≤ ⁅⊤, oStar X⁆ := Subgroup.commutator_mono le_top hTO
    _ ≤ oStar X := Subgroup.commutator_le_right _ _

theorem bender1970_2_5_i (hX : IsAStar X) {t : X} (T : Sylow 2 X) (htT : t ∈ (T : Subgroup X))
    {E : Subgroup X} (hE : IsComponentOf E ⊤) :
    oddCoreOf (CFSG.fittingSubgroupOf (Subgroup.centralizer ({t} : Set X))) ≤
      Subgroup.normalizer (E : Set X) := by
  obtain ⟨-, hdec, hcomm⟩ := oddFitting_le_sup_commutator hX T htT
  refine hdec.trans (sup_le ?_ ?_)
  · exact inf_le_right.trans (centralizer_sylow_le_normalizer hX.1 T hE)
  · exact hcomm.trans (oStar_le_normalizer hX hE)

theorem le_oStar_of_inf_centralizer_le (hX : IsAStar X) {t : X} (T : Sylow 2 X)
    (htT : t ∈ (T : Subgroup X))
    (hCU : oddCoreOf (CFSG.fittingSubgroupOf (Subgroup.centralizer ({t} : Set X))) ⊓
      Subgroup.centralizer ((T : Subgroup X) : Set X) ≤ pPrimeCore 2 X) :
    oddCoreOf (CFSG.fittingSubgroupOf (Subgroup.centralizer ({t} : Set X))) ≤ oStar X := by
  obtain ⟨-, hdec, hcomm⟩ := oddFitting_le_sup_commutator hX T htT
  exact hdec.trans (sup_le (hCU.trans pPrimeCore_le_oStar) hcomm)

end OddFitting

end CFSG.Walter

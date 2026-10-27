module

public import CFSG.Sporadic.SuzOddCore.SmallAut
public import CFSG.Sporadic.SuzOddCore.OddCore
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Components

public noncomputable section

namespace CFSG.Sporadic.SuzOddCore

open CFSG CFSG.Certificates CFSG.Monster.B.Co2

section Conj

variable {X : Type*} [Group X] [Finite X]

instance genFitting_normal : (generalizedFitting X).Normal :=
  (CFSG.LocalCores.generalized_fitting_characteristic (G := X)).2

theorem conjNormal_injective (hs : IsSimpleGroup (generalizedFitting X))
    (hnc : ∃ a b : generalizedFitting X, a * b ≠ b * a) :
    Function.Injective (MulAut.conjNormal : X →* MulAut (generalizedFitting X)) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hc : x ∈ Subgroup.centralizer (generalizedFitting X : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have := congrArg (fun α : MulAut (generalizedFitting X) => ((α ⟨f, hf⟩ : _) : X)) hx
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
    calc f * x = x * f * x⁻¹ * x := by rw [this]
      _ = x * f := by group
  have hxF := centralizer_generalizedFitting_le X hc
  have hcen := center_eq_bot_of_simple hnc
  have hz : (⟨x, hxF⟩ : generalizedFitting X) ∈ Subgroup.center (generalizedFitting X) :=
    Subgroup.mem_center_iff.2 fun g => Subtype.ext
      ((Subgroup.mem_centralizer_iff.1 hc) g g.2)
  rw [hcen, Subgroup.mem_bot] at hz
  exact congrArg Subtype.val hz

omit [Finite X] in
theorem conjNormal_coe (f : generalizedFitting X) :
    (MulAut.conjNormal (f : X) : MulAut (generalizedFitting X)) = MulAut.conj f :=
  MulAut.conjNormal_val

end Conj

theorem mulAut_congr_conj {G H : Type*} [Group G] [Group H] (φ : G ≃* H) (g : G) :
    MulAut.congr φ (MulAut.conj g) = MulAut.conj (φ g) := by
  ext x
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem eq_or_top_of_index_two {G : Type*} [Group G] {H K : Subgroup G} (hHK : H ≤ K)
    (hH : H.index = 2) : K = H ∨ K = ⊤ := by
  have h := Subgroup.relIndex_mul_index hHK
  rw [hH] at h
  have hK : K.index = 1 ∨ K.index = 2 := by
    have hdvd : K.index ∣ 2 := ⟨_, by rw [← h, mul_comm]⟩
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h1 <;> simp [h1]
  rcases hK with h1 | h1
  · right
    exact Subgroup.index_eq_one.1 h1
  · left
    rw [h1] at h
    have hr : H.relIndex K = 1 := by omega
    exact le_antisymm (Subgroup.relIndex_eq_one.1 hr) hHK

theorem CTUC_Suz_simple_generalized_fitting_extension_model
    {X : Type*} [Group X] [Finite X]
    (hs : IsSimpleGroup (generalizedFitting X))
    (hnc : ∃ a b : generalizedFitting X, a * b ≠ b * a)
    (e : generalizedFitting X ≃* Blueprint.NativeSporadic.Suz) :
    ∃ j : X →* suzR, Function.Injective j ∧
      (generalizedFitting X).map j = suzP.subgroupOf suzR ∧
      (j.range = suzP.subgroupOf suzR ∨ j.range = ⊤) ∧
      ((generalizedFitting X).index = 1 ∨ (generalizedFitting X).index = 2) := by
  set φ : generalizedFitting X ≃* suzP := e.trans suzEquivP
  set ψ : suzR ≃* MulAut suzP := MulEquiv.ofBijective suzConjR suzConjR_bijective
  set j : X →* suzR := ψ.symm.toMonoidHom.comp ((MulAut.congr φ).toMonoidHom.comp
    MulAut.conjNormal)
  have hj : Function.Injective j :=
    ψ.symm.injective.comp ((MulAut.congr φ).injective.comp (conjNormal_injective hs hnc))
  have hjF : ∀ f : generalizedFitting X, j f = ⟨φ f, suzP_le_suzR (φ f).2⟩ := by
    intro f
    apply ψ.injective
    simp only [j, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
      conjNormal_coe, mulAut_congr_conj]
    ext q
    simp [ψ, suzConjR_apply, MulAut.conj_apply]
  have hmap : (generalizedFitting X).map j = suzP.subgroupOf suzR := by
    ext r
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Subgroup.mem_subgroupOf, show x = ((⟨x, hx⟩ : generalizedFitting X) : X) from rfl, hjF]
      exact (φ ⟨x, hx⟩).2
    · intro hr
      rw [Subgroup.mem_subgroupOf] at hr
      refine ⟨φ.symm ⟨r, hr⟩, (φ.symm ⟨r, hr⟩).2, ?_⟩
      rw [hjF, MulEquiv.apply_symm_apply]
  have hrange := eq_or_top_of_index_two (show suzP.subgroupOf suzR ≤ j.range by
    rw [← hmap]; exact Subgroup.map_le_range _ _) suzP_index_R
  refine ⟨j, hj, hmap, hrange, ?_⟩
  have hcardF : Nat.card (generalizedFitting X) = 448345497600 := by
    rw [Nat.card_congr φ.toEquiv, suzP_card]
  have hX : Nat.card X = Nat.card j.range := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hj, Subgroup.card_top]
  have hidx := (generalizedFitting X).card_mul_index
  rw [hcardF] at hidx
  rcases hrange with h | h
  · left
    rw [hX, h, Nat.card_congr (Subgroup.subgroupOfEquivOfLe suzP_le_suzR).toEquiv,
      suzP_card] at hidx
    omega
  · right
    rw [hX, h, Subgroup.card_top, suzR_card] at hidx
    omega

theorem map_centralizer {X : Type*} [Group X] (j : X →* suzT) (hj : Function.Injective j)
    (a : X) (K : Subgroup (Equiv.Perm (Fin 1782))) (hK : K ≤ suzT)
    (hrange : j.range = K.subgroupOf suzT) :
    (Subgroup.centralizer ({a} : Set X)).map (suzT.subtype.comp j) =
      K ⊓ Subgroup.centralizer {((j a : suzT) : Equiv.Perm (Fin 1782))} := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    MonoidHom.comp_apply, Subgroup.coe_subtype]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxr : j x ∈ j.range := ⟨x, rfl⟩
    rw [hrange, Subgroup.mem_subgroupOf] at hxr
    refine ⟨hxr, ?_⟩
    have := congrArg (fun w => ((j w : suzT) : Equiv.Perm (Fin 1782))) hx
    simpa using this
  · rintro ⟨hyK, hyc⟩
    have hyr : (⟨y, hK hyK⟩ : suzT) ∈ j.range := by
      rw [hrange, Subgroup.mem_subgroupOf]
      exact hyK
    obtain ⟨x, hx⟩ := hyr
    refine ⟨x, ?_, by rw [hx]⟩
    apply hj
    apply Subtype.ext
    simp only [map_mul, Subgroup.coe_mul, hx]
    exact hyc

theorem oddCore_centralizer_of_map {X : Type*} [Group X] (j : X →* suzT)
    (hj : Function.Injective j) (a : X) {K : Subgroup (Equiv.Perm (Fin 1782))} (hK : K ≤ suzT)
    (hrange : j.range = K.subgroupOf suzT)
    (hO : CFSG.oddCore ↥(K ⊓ Subgroup.centralizer {((j a : suzT) : Equiv.Perm (Fin 1782))}) = ⊥) :
    CFSG.oddCore ↥(Subgroup.centralizer ({a} : Set X)) = ⊥ := by
  have hinj : Function.Injective (suzT.subtype.comp j) := suzT.subtype_injective.comp hj
  have e := Subgroup.equivMapOfInjective (Subgroup.centralizer ({a} : Set X)) _ hinj
  rw [map_centralizer j hj a K hK hrange] at e
  exact oddCore_eq_bot_of_mulEquiv' e.symm hO

theorem CTUC_Suz_model_simple_generalized_fitting_centralizer_exclusion
    {X : Type*} [Group X]
    [Finite X] (hs : IsSimpleGroup (generalizedFitting X))
    (hnc : ∃ a b : generalizedFitting X, a * b ≠ b * a)
    (e : generalizedFitting X ≃* Blueprint.NativeSporadic.Suz) :
    ((generalizedFitting X).index = 1 ∨ (generalizedFitting X).index = 2) ∧
    ∀ a : X, orderOf a = 2 → CFSG.oddCore ↥(Subgroup.centralizer ({a} : Set X)) = ⊥ := by
  set φ : generalizedFitting X ≃* suzM := e.trans suzEquivM
  set ψ : suzT ≃* MulAut suzM := MulEquiv.ofBijective suzConjT suzConjT_bijective
  set j : X →* suzT := ψ.symm.toMonoidHom.comp ((MulAut.congr φ).toMonoidHom.comp
    MulAut.conjNormal)
  have hj : Function.Injective j :=
    ψ.symm.injective.comp ((MulAut.congr φ).injective.comp (conjNormal_injective hs hnc))
  have hjF : ∀ f : generalizedFitting X, j f = ⟨φ f, suzM_le_suzT (φ f).2⟩ := by
    intro f
    apply ψ.injective
    simp only [j, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
      conjNormal_coe, mulAut_congr_conj]
    ext q
    simp [ψ, suzConjT_apply, MulAut.conj_apply]
  have hmap : (generalizedFitting X).map j = suzM.subgroupOf suzT := by
    ext r
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Subgroup.mem_subgroupOf, show x = ((⟨x, hx⟩ : generalizedFitting X) : X) from rfl, hjF]
      exact (φ ⟨x, hx⟩).2
    · intro hr
      rw [Subgroup.mem_subgroupOf] at hr
      refine ⟨φ.symm ⟨r, hr⟩, (φ.symm ⟨r, hr⟩).2, ?_⟩
      rw [hjF, MulEquiv.apply_symm_apply]
  have hrange := eq_or_top_of_index_two (show suzM.subgroupOf suzT ≤ j.range by
    rw [← hmap]; exact Subgroup.map_le_range _ _) suzM_index_T
  have hcardF : Nat.card (generalizedFitting X) = 448345497600 := by
    rw [Nat.card_congr φ.toEquiv, suzM_card_chain]
  have hX : Nat.card X = Nat.card j.range := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hj, Subgroup.card_top]
  refine ⟨?_, fun a ha => ?_⟩
  · have hidx := (generalizedFitting X).card_mul_index
    rw [hcardF] at hidx
    rcases hrange with h | h
    · left
      rw [hX, h, Nat.card_congr (Subgroup.subgroupOfEquivOfLe suzM_le_suzT).toEquiv,
        suzM_card_chain] at hidx
      omega
    · right
      rw [hX, h, Subgroup.card_top, suzT_card] at hidx
      omega
  · have hja : orderOf ((j a : suzT) : Equiv.Perm (Fin 1782)) = 2 := by
      rw [Subgroup.orderOf_coe, orderOf_injective j hj, ha]
    obtain ⟨hM, hT⟩ := CTUC_Suz_all_involution_centralizers_odd_core_free _ (j a).2 hja
    rcases hrange with h | h
    · exact oddCore_centralizer_of_map j hj a suzM_le_suzT h hM
    · have h' : j.range = suzT.subgroupOf suzT := by rw [h, Subgroup.subgroupOf_self]
      exact oddCore_centralizer_of_map j hj a le_rfl h' hT

end CFSG.Sporadic.SuzOddCore

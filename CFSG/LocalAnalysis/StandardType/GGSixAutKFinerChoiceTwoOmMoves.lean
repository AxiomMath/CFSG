module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoOmCoord

public section

namespace CFSG.StandardType

namespace ChoiceTwoOm

open Module Multiplicative QuadraticMap ChoiceTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Mono

variable {K : Type} [Field K] [CharP K 2] {s : ℕ}

@[expose] def sgnC (K : Type) [Field K] [CharP K 2] (b : Bool) : (K × K) ≃ₗ[K] (K × K) :=
  if b then σL K else LinearEquiv.refl K (K × K)

theorem sgnC_false (c : K × K) : sgnC K false c = c := rfl

theorem sgnC_true (c : K × K) : sgnC K true c = σL K c := rfl

theorem sgnC_sgnC (b : Bool) (c : K × K) : sgnC K b (sgnC K b c) = c := by
  cases b
  · rfl
  · exact σL_σL c

theorem nrm_sgnC (b : Bool) (c : K × K) : nrm (sgnC K b c) = nrm c := by
  cases b
  · rfl
  · exact nrm_σL c

theorem sgnC_zpow (b : Bool) (a : ZMod 3) (c : K × K) :
    sgnC K b (zpow a c) = zpow (sgnZ b a) (sgnC K b c) := by
  cases b
  · rfl
  · exact σL_zpow a c

@[expose] def monoC (π : Equiv.Perm (Fin s)) (η : Fin s → Bool) :
    (Fin s → K × K) ≃ₗ[K] (Fin s → K × K) where
  toFun d i := sgnC K (η i) (d (π i))
  invFun d j := sgnC K (η (π.symm j)) (d (π.symm j))
  map_add' d d' := funext fun _ => map_add _ _ _
  map_smul' c d := funext fun i => by
    simp only [Pi.smul_apply, RingHom.id_apply]
    exact map_smul _ _ _
  left_inv d := funext fun j => by simp [sgnC_sgnC]
  right_inv d := funext fun i => by simp [sgnC_sgnC]

theorem monoC_apply (π : Equiv.Perm (Fin s)) (η : Fin s → Bool) (d : Fin s → K × K)
    (i : Fin s) : monoC π η d i = sgnC K (η i) (d (π i)) := rfl

theorem monoC_torC (π : Equiv.Perm (Fin s)) (η : Fin s → Bool) (f : Fin s → ZMod 3)
    (d : Fin s → K × K) : monoC π η (torC f d) = torC (moveExp π η f) (monoC π η d) :=
  funext fun i => sgnC_zpow (η i) (f (π i)) (d (π i))

theorem nrm_monoC (π : Equiv.Perm (Fin s)) (η : Fin s → Bool) (d : Fin s → K × K) :
    ∑ i, nrm (monoC π η d i) = ∑ i, nrm (d i) := by
  simp only [monoC_apply, nrm_sgnC]
  exact Equiv.sum_comp π (fun i => nrm (d i))

theorem moveExp_swap {i j : Fin s} (b : Bool) {f : Fin s → ZMod 3} (hf : f i = sgnZ b (f j)) :
    moveExp (Equiv.swap i j) (swapSgn i j b) f = f := by
  funext l
  rw [moveExp_apply]
  by_cases hli : l = i
  · subst hli
    simp [swapSgn, hf]
  · by_cases hlj : l = j
    · subst hlj
      simp only [swapSgn, or_true, ite_true, Equiv.swap_apply_right]
      rw [hf, sgnZ_sgnZ]
    · simp [swapSgn, hli, hlj, Equiv.swap_apply_of_ne_of_ne hli hlj, sgnZ_false]

theorem monoC_mul_false (π π' : Equiv.Perm (Fin s)) :
    (monoC (π' * π) (fun _ => false) : (Fin s → K × K) ≃ₗ[K] (Fin s → K × K)) =
      monoC π (fun _ => false) * monoC π' (fun _ => false) :=
  LinearEquiv.ext fun _ => funext fun _ => rfl

theorem monoC_one_false :
    (monoC 1 (fun _ => false) : (Fin s → K × K) ≃ₗ[K] (Fin s → K × K)) = 1 :=
  LinearEquiv.ext fun _ => funext fun _ => rfl

theorem monoC_eq_mul (π : Equiv.Perm (Fin s)) (η : Fin s → Bool) :
    (monoC π η : (Fin s → K × K) ≃ₗ[K] (Fin s → K × K)) =
      monoC 1 η * monoC π (fun _ => false) :=
  LinearEquiv.ext fun _ => funext fun _ => rfl

omit [CharP K 2] in
theorem neg_two [CharP K 2] (x : K × K) : -x = x :=
  neg_eq_of_add_eq_zero_left (Prod.ext (add_self_K x.1) (add_self_K x.2))

theorem sub_comm_two (x y : K × K) : x - y = y - x := by
  rw [sub_eq_add_neg, sub_eq_add_neg, neg_two, neg_two, add_comm]

omit [CharP K 2] in
theorem finrank_K_K : finrank K (K × K) = 2 := by
  rw [Module.finrank_prod, Module.finrank_self]

@[expose] def twoPlanes (i j : Fin s) : (K × K) →ₗ[K] (Fin s → K × K) :=
  LinearMap.single K (fun _ => K × K) i + LinearMap.single K (fun _ => K × K) j

omit [CharP K 2] in
theorem twoPlanes_apply (i j : Fin s) (c : K × K) :
    twoPlanes i j c = Pi.single i c + Pi.single j c := rfl

omit [CharP K 2] in
theorem twoPlanes_injective {i j : Fin s} (hij : i ≠ j) :
    Function.Injective (twoPlanes (K := K) i j) := by
  intro c c' h
  have := congrFun h i
  simpa [twoPlanes_apply, Pi.single_eq_of_ne' hij, Pi.single_eq_of_ne hij] using this

theorem range_swap_sub {i j : Fin s} (hij : i ≠ j) :
    LinearMap.range ((monoC (Equiv.swap i j) (fun _ => false) :
      (Fin s → K × K) ≃ₗ[K] (Fin s → K × K)).toLinearMap - LinearMap.id) =
      LinearMap.range (twoPlanes (K := K) i j) := by
  apply le_antisymm
  · rintro _ ⟨d, rfl⟩
    refine ⟨d j - d i, funext fun l => ?_⟩
    simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, Pi.sub_apply,
      monoC_apply, sgnC_false, twoPlanes_apply, Pi.add_apply]
    by_cases hli : l = i
    · subst hli
      simp [Pi.single_eq_of_ne hij]
    · by_cases hlj : l = j
      · subst hlj
        simp [Pi.single_eq_of_ne' hij, sub_comm_two]
      · simp [Pi.single_eq_of_ne hli, Pi.single_eq_of_ne hlj,
          Equiv.swap_apply_of_ne_of_ne hli hlj]
  · rintro _ ⟨c, rfl⟩
    refine ⟨Pi.single i c, funext fun l => ?_⟩
    simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, Pi.sub_apply,
      monoC_apply, sgnC_false, twoPlanes_apply, Pi.add_apply]
    by_cases hli : l = i
    · subst hli
      simp [Pi.single_eq_of_ne hij, Pi.single_eq_of_ne' hij, neg_two]
    · by_cases hlj : l = j
      · subst hlj
        simp [Pi.single_eq_of_ne' hij]
      · simp [Pi.single_eq_of_ne hli, Pi.single_eq_of_ne hlj,
          Equiv.swap_apply_of_ne_of_ne hli hlj]

@[expose] def twoLines (i j : Fin s) : (K × K) →ₗ[K] (Fin s → K × K) :=
  (LinearMap.single K (fun _ => K × K) i ∘ₗ LinearMap.inl K K K ∘ₗ LinearMap.fst K K K) +
    (LinearMap.single K (fun _ => K × K) j ∘ₗ LinearMap.inl K K K ∘ₗ LinearMap.snd K K K)

omit [CharP K 2] in
theorem twoLines_apply (i j : Fin s) (c : K × K) :
    twoLines i j c = Pi.single i (c.1, 0) + Pi.single j (c.2, 0) := rfl

omit [CharP K 2] in
theorem twoLines_injective {i j : Fin s} (hij : i ≠ j) :
    Function.Injective (twoLines (K := K) i j) := by
  intro c c' h
  have h1 := congrArg Prod.fst (congrFun h i)
  have h2 := congrArg Prod.fst (congrFun h j)
  simp [twoLines_apply, Pi.single_eq_of_ne' hij, Pi.single_eq_of_ne hij] at h1 h2
  exact Prod.ext h1 h2

theorem range_twist_sub {i j : Fin s} (hij : i ≠ j) :
    LinearMap.range ((monoC 1 (swapSgn i j true) :
      (Fin s → K × K) ≃ₗ[K] (Fin s → K × K)).toLinearMap - LinearMap.id) =
      LinearMap.range (twoLines (K := K) i j) := by
  apply le_antisymm
  · rintro _ ⟨d, rfl⟩
    refine ⟨((d i).2, (d j).2), funext fun l => ?_⟩
    simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, Pi.sub_apply,
      monoC_apply, twoLines_apply, Pi.add_apply, Equiv.Perm.coe_one, id]
    by_cases hli : l = i
    · subst hli
      simp only [swapSgn, true_or, ite_true, sgnC_true, Pi.single_eq_same,
        Pi.single_eq_of_ne hij, add_zero]
      ext <;> simp [σL_apply]
    · by_cases hlj : l = j
      · subst hlj
        simp only [swapSgn, or_true, ite_true, sgnC_true, Pi.single_eq_same,
          Pi.single_eq_of_ne' hij, zero_add]
        ext <;> simp [σL_apply]
      · simp [swapSgn, hli, hlj, sgnC_false]
  · rintro _ ⟨c, rfl⟩
    refine ⟨Pi.single i (0, c.1) + Pi.single j (0, c.2), funext fun l => ?_⟩
    simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, Pi.sub_apply,
      monoC_apply, twoLines_apply, Pi.add_apply, Equiv.Perm.coe_one, id]
    by_cases hli : l = i
    · subst hli
      simp only [swapSgn, true_or, ite_true, sgnC_true, Pi.single_eq_same,
        Pi.single_eq_of_ne hij, add_zero]
      ext <;> simp [σL_apply]
    · by_cases hlj : l = j
      · subst hlj
        simp only [swapSgn, or_true, ite_true, sgnC_true, Pi.single_eq_same,
          Pi.single_eq_of_ne' hij, zero_add]
        ext <;> simp [σL_apply]
      · simp [swapSgn, hli, hlj, sgnC_false]

end Mono

namespace OmCoord

section Lift

variable {K : Type} [Field K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {A : Subgroup (V ≃ₗ[K] V)} (C : OmCoord K Q A)

@[expose] noncomputable def lift (m : (Fin C.s → K × K) ≃ₗ[K] (Fin C.s → K × K)) : V ≃ₗ[K] V :=
  C.Φ.symm.trans ((m.prodCongr (LinearEquiv.refl K C.W0)).trans C.Φ)

theorem lift_apply (m : (Fin C.s → K × K) ≃ₗ[K] (Fin C.s → K × K)) (d : Fin C.s → K × K)
    (x : C.W0) : C.lift m (C.Φ (d, x)) = C.Φ (m d, x) := by
  simp [lift]

theorem ext_Φ {g g' : V ≃ₗ[K] V} (h : ∀ d x, g (C.Φ (d, x)) = g' (C.Φ (d, x))) : g = g' :=
  LinearEquiv.ext fun v => by
    obtain ⟨⟨d, x⟩, rfl⟩ := C.Φ.surjective v
    exact h d x

theorem lift_mul (m m' : (Fin C.s → K × K) ≃ₗ[K] (Fin C.s → K × K)) :
    C.lift (m * m') = C.lift m * C.lift m' :=
  C.ext_Φ fun d x => by rw [LinearEquiv.mul_apply, lift_apply, lift_apply, lift_apply]; rfl

theorem lift_one : C.lift 1 = 1 := C.ext_Φ fun d x => by rw [lift_apply]; rfl

theorem lift_isom {m : (Fin C.s → K × K) ≃ₗ[K] (Fin C.s → K × K)}
    (hm : ∀ d, ∑ i, nrm (m d i) = ∑ i, nrm (d i)) :
    C.lift m ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_
  obtain ⟨⟨d, x⟩, rfl⟩ := C.Φ.surjective v
  rw [lift_apply, C.form, C.form, hm]

theorem finrank_commSpace_lift [FiniteDimensional K V]
    (m : (Fin C.s → K × K) ≃ₗ[K] (Fin C.s → K × K)) :
    finrank K (CFSG.RankThree.OrthogonalInvolutions.commSpace (C.lift m)) =
      finrank K (LinearMap.range (m.toLinearMap - LinearMap.id)) := by
  set ι₁ : (Fin C.s → K × K) →ₗ[K] V := C.Φ.toLinearMap ∘ₗ LinearMap.inl K _ C.W0 with hι₁
  have hinj : Function.Injective ι₁ := fun a b h => by
    have := C.Φ.injective h
    exact congrArg Prod.fst this
  have heq : CFSG.RankThree.OrthogonalInvolutions.commSpace (C.lift m) =
      (LinearMap.range (m.toLinearMap - LinearMap.id)).map ι₁ := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      obtain ⟨⟨d, x⟩, rfl⟩ := C.Φ.surjective v
      refine ⟨m d - d, ⟨d, rfl⟩, ?_⟩
      simp only [hι₁, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        LinearMap.inl_apply, LinearMap.sub_apply]
      rw [lift_apply, Module.End.one_apply, ← map_sub, Prod.mk_sub_mk, sub_self]
    · rintro _ ⟨_, ⟨d, rfl⟩, rfl⟩
      refine ⟨C.Φ (d, 0), ?_⟩
      simp only [hι₁, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        LinearMap.inl_apply, LinearMap.sub_apply]
      rw [lift_apply, Module.End.one_apply, ← map_sub, Prod.mk_sub_mk, sub_self]
      rfl
  rw [heq]
  exact (Submodule.equivMapOfInjective ι₁ hinj _).finrank_eq.symm

@[expose] noncomputable def move (π : Equiv.Perm (Fin C.s)) (η : Fin C.s → Bool) : V ≃ₗ[K] V :=
  C.lift (monoC π η)

theorem move_apply (π : Equiv.Perm (Fin C.s)) (η : Fin C.s → Bool) (d : Fin C.s → K × K)
    (x : C.W0) : C.move π η (C.Φ (d, x)) = C.Φ (monoC π η d, x) := C.lift_apply _ d x

theorem move_mem_O (π : Equiv.Perm (Fin C.s)) (η : Fin C.s → Bool) :
    C.move π η ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  C.lift_isom (nrm_monoC π η)

theorem move_conj (π : Equiv.Perm (Fin C.s)) (η : Fin C.s → Bool) (f : Fin C.s → ZMod 3) :
    C.move π η * C.tor f = C.tor (moveExp π η f) * C.move π η :=
  C.ext_Φ fun d x => by
    simp only [LinearEquiv.mul_apply, move_apply, C.tor_acts, monoC_torC]

theorem tor_add (f f' : Fin C.s → ZMod 3) : C.tor (f + f') = C.tor f * C.tor f' :=
  C.ext_Φ fun d x => by simp only [LinearEquiv.mul_apply, C.tor_acts, torC_add]

theorem tor_zero : C.tor 0 = 1 :=
  C.ext_Φ fun d x => by rw [C.tor_acts, torC_zero]; rfl

theorem zpow_inj {a b : ZMod 3} (h : zpow a ((1, 0) : K × K) = zpow b (1, 0)) : a = b := by
  have h1 : zpow (a - b) ((1, 0) : K × K) = (1, 0) := by
    have := congrArg (zpow (-b)) h
    rw [← zpow_apply_add, ← zpow_apply_add, neg_add_cancel, zpow_zero] at this
    rw [show a - b = -b + a by ring]
    exact this
  by_contra hab
  have := eq_zero_of_zpow_eq (a - b) (sub_ne_zero.mpr hab) _ h1
  exact one_ne_zero (congrArg Prod.fst this)

theorem tor_injective {f f' : Fin C.s → ZMod 3} (h : C.tor f = C.tor f') : f = f' := by
  have h1 := congrArg (fun g : V ≃ₗ[K] V => g (C.Φ (fun _ => ((1 : K), (0 : K)), 0))) h
  simp only [C.tor_acts] at h1
  have h2 := congrArg Prod.fst (C.Φ.injective h1)
  funext i
  exact zpow_inj (congrFun h2 i)

theorem swapSgn_false (i j : Fin C.s) : swapSgn i j false = fun _ => false := by
  funext l
  simp [swapSgn]

theorem swap_mul_self {i j : Fin C.s} (hij : i ≠ j) (b : Bool) :
    C.move (Equiv.swap i j) (swapSgn i j b) * C.move (Equiv.swap i j) (swapSgn i j b) = 1 := by
  have hd : ∀ d : Fin C.s → K × K, monoC (Equiv.swap i j) (swapSgn i j b)
      (monoC (Equiv.swap i j) (swapSgn i j b) d) = d := by
    intro d
    funext l
    simp only [monoC_apply]
    by_cases hli : l = i
    · subst hli
      simp [swapSgn, sgnC_sgnC]
    · by_cases hlj : l = j
      · subst hlj
        simp [swapSgn, sgnC_sgnC]
      · simp [swapSgn, hli, hlj, Equiv.swap_apply_of_ne_of_ne hli hlj, sgnC_false]
  exact C.ext_Φ fun d x => by
    rw [LinearEquiv.mul_apply, move_apply, move_apply, hd]
    rfl

theorem swap_commute_tor {i j : Fin C.s} (b : Bool) {f : Fin C.s → ZMod 3}
    (hf : f i = sgnZ b (f j)) :
    C.move (Equiv.swap i j) (swapSgn i j b) * C.tor f =
      C.tor f * C.move (Equiv.swap i j) (swapSgn i j b) := by
  rw [move_conj, moveExp_swap b hf]

theorem swap_not_commute {i₁ i₂ i₃ : Fin C.s} (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h23 : i₂ ≠ i₃)
    (b b' : Bool) :
    C.move (Equiv.swap i₁ i₂) (swapSgn i₁ i₂ b) * C.move (Equiv.swap i₁ i₃) (swapSgn i₁ i₃ b') ≠
      C.move (Equiv.swap i₁ i₃) (swapSgn i₁ i₃ b') *
        C.move (Equiv.swap i₁ i₂) (swapSgn i₁ i₂ b) := by
  intro h
  have h1 := congrArg (fun g : V ≃ₗ[K] V => g (C.Φ (Pi.single i₃ ((1 : K), (0 : K)), 0))) h
  simp only [LinearEquiv.mul_apply, move_apply] at h1
  have h2 := congrFun (congrArg Prod.fst (C.Φ.injective h1)) i₂
  have e1 : swapSgn i₁ i₂ b i₂ = b := by simp [swapSgn]
  have e2 : swapSgn i₁ i₃ b' i₁ = b' := by simp [swapSgn]
  have e3 : swapSgn i₁ i₃ b' i₂ = false := by simp [swapSgn, h12.symm, h23]
  simp only [monoC_apply, e1, e2, e3, Equiv.swap_apply_right, Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne h12.symm h23, Pi.single_eq_same, Pi.single_eq_of_ne h13,
    map_zero] at h2
  have h3 := congrArg (sgnC K b') (congrArg (sgnC K b) h2)
  simp only [sgnC_sgnC, map_zero] at h3
  exact one_ne_zero (congrArg Prod.fst h3)

theorem swap_not_commute_tor {i j : Fin C.s} (hij : i ≠ j) (b : Bool) :
    C.move (Equiv.swap i j) (swapSgn i j b) * C.tor (Pi.single i 1) ≠
      C.tor (Pi.single i 1) * C.move (Equiv.swap i j) (swapSgn i j b) := by
  intro h
  rw [move_conj] at h
  have h1 := C.tor_injective (mul_right_cancel h)
  have h2 := congrFun h1 i
  rw [moveExp_apply, Equiv.swap_apply_left, Pi.single_eq_same, Pi.single_eq_of_ne hij.symm,
    sgnZ_zero] at h2
  exact zero_ne_one h2

end Lift

section Omega

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {A : Subgroup (V ≃ₗ[K] V)} (C : OmCoord K Q A)
  (hQ : (polarBilin Q).Nondegenerate)
  (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
include hQ hT

theorem lift_mem_omega {m : (Fin C.s → K × K) ≃ₗ[K] (Fin C.s → K × K)}
    (hm : ∀ d, ∑ i, nrm (m d i) = ∑ i, nrm (d i))
    (h2 : finrank K (LinearMap.range (m.toLinearMap - LinearMap.id)) = 2) :
    C.lift m ∈ CFSG.RankThree.Classical2.orthDerived Q :=
  CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hQ hT
    (CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup.mpr
      ⟨C.lift_isom hm, by rw [C.finrank_commSpace_lift, h2]; exact even_two⟩)


theorem move_swap_mem {i j : Fin C.s} (hij : i ≠ j) :
    C.move (Equiv.swap i j) (fun _ => false) ∈ CFSG.RankThree.Classical2.orthDerived Q :=
  C.lift_mem_omega hQ hT (nrm_monoC _ _) (by
    rw [range_swap_sub hij, LinearMap.finrank_range_of_inj (twoPlanes_injective (K := K) hij)]
    exact finrank_K_K (K := K))

theorem move_twist_mem {i j : Fin C.s} (hij : i ≠ j) :
    C.move 1 (swapSgn i j true) ∈ CFSG.RankThree.Classical2.orthDerived Q :=
  C.lift_mem_omega hQ hT (nrm_monoC _ _) (by
    rw [range_twist_sub hij, LinearMap.finrank_range_of_inj (twoLines_injective (K := K) hij)]
    exact finrank_K_K (K := K))

theorem move_perm_mem (π : Equiv.Perm (Fin C.s)) :
    C.move π (fun _ => false) ∈ CFSG.RankThree.Classical2.orthDerived Q := by
  induction π using Equiv.Perm.swap_induction_on with
  | one =>
    rw [move, monoC_one_false, C.lift_one]
    exact one_mem _
  | swap_mul f x y hxy ih =>
    rw [move, monoC_mul_false, C.lift_mul]
    exact mul_mem ih (C.move_swap_mem hQ hT hxy)

theorem move_mem (π : Equiv.Perm (Fin C.s)) {η : Fin C.s → Bool}
    (hη : η = (fun _ => false) ∨ ∃ i j, i ≠ j ∧ η = swapSgn i j true) :
    C.move π η ∈ CFSG.RankThree.Classical2.orthDerived Q := by
  rcases hη with rfl | ⟨i, j, hij, rfl⟩
  · exact C.move_perm_mem hQ hT π
  · rw [move, monoC_eq_mul, C.lift_mul]
    exact mul_mem (C.move_twist_mem hQ hT hij) (C.move_perm_mem hQ hT π)

theorem swap_mem {i j : Fin C.s} (hij : i ≠ j) (b : Bool) :
    C.move (Equiv.swap i j) (swapSgn i j b) ∈ CFSG.RankThree.Classical2.orthDerived Q := by
  cases b
  · rw [C.swapSgn_false]
    exact C.move_perm_mem hQ hT _
  · exact C.move_mem hQ hT _ (Or.inr ⟨i, j, hij, rfl⟩)

end Omega

end OmCoord

end ChoiceTwoOm

end CFSG.StandardType

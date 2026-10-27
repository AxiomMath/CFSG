module

public import CFSG.RankThree.PartTwo.Census.Classical.EvenWitness

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS21LocalRank

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (localRank)
open scoped commutatorElement

abbrev Om := Fin 3 ⊕ Fin 3 ⊕ Fin 2

variable {K : Type} [Field K]

theorem quadMinus_apply (b c : K) (v : Om → K) :
    StatedQuadMinus 4 K b c v = v (.inl 0) * v (.inr (.inl 0)) + v (.inl 1) * v (.inr (.inl 1)) +
      v (.inl 2) * v (.inr (.inl 2)) + v (.inr (.inr 0)) ^ 2 +
        b * v (.inr (.inr 0)) * v (.inr (.inr 1)) + c * v (.inr (.inr 1)) ^ 2 := by
  change (∑ i : Fin 3, v (.inl i) * v (.inr (.inl i))) + v (.inr (.inr 0)) ^ 2 +
    b * v (.inr (.inr 0)) * v (.inr (.inr 1)) + c * v (.inr (.inr 1)) ^ 2 = _
  rw [Fin.sum_univ_three]

@[expose] noncomputable def diagOm : (Om → Kˣ) →* GL Om K :=
  (Units.map (Matrix.diagonalRingHom Om K).toMonoidHom).comp
    (MulEquiv.piUnits (M := fun _ : Om => K)).symm.toMonoidHom

theorem coe_diagOm (d : Om → Kˣ) :
    ((diagOm d : GL Om K) : Matrix Om Om K) = diagonal fun i => (d i : K) :=
  rfl

@[expose] def torusEnt : (Fin 3 → Kˣ) →* (Om → Kˣ) where
  toFun t := Sum.elim t (Sum.elim (fun i => (t i)⁻¹) fun _ => 1)
  map_one' := by
    funext j
    rcases j with j | j | j <;> simp
  map_mul' s t := by
    funext j
    rcases j with j | j | j <;> simp [mul_comm]

@[expose] noncomputable def torusOm : (Fin 3 → Kˣ) →* GL Om K := diagOm.comp torusEnt

theorem torusEnt_inl (t : Fin 3 → Kˣ) (i : Fin 3) : torusEnt t (.inl i) = t i := rfl

theorem torusEnt_inr_inl (t : Fin 3 → Kˣ) (i : Fin 3) :
    torusEnt t (.inr (.inl i)) = (t i)⁻¹ := rfl

theorem torusEnt_inr_inr (t : Fin 3 → Kˣ) (i : Fin 2) : torusEnt t (.inr (.inr i)) = 1 := rfl

theorem mulVec_torusOm (t : Fin 3 → Kˣ) (v : Om → K) (j : Om) :
    (((torusOm t : GL Om K) : Matrix Om Om K) *ᵥ v) j = (torusEnt t j : K) * v j := by
  rw [torusOm, MonoidHom.comp_apply, coe_diagOm, mulVec_diagonal]

theorem quadMinus_torusOm (b c : K) (t : Fin 3 → Kˣ) (v : Om → K) :
    StatedQuadMinus 4 K b c (((torusOm t : GL Om K) : Matrix Om Om K) *ᵥ v) =
      StatedQuadMinus 4 K b c v := by
  rw [show (((torusOm t : GL Om K) : Matrix Om Om K) *ᵥ v) = fun j => (torusEnt t j : K) * v j
    from funext (mulVec_torusOm t v), quadMinus_apply, quadMinus_apply]
  simp only [torusEnt_inl, torusEnt_inr_inl, torusEnt_inr_inr, Units.val_one, one_mul]
  have e : ∀ x : Kˣ, (x : K) * ((x⁻¹ : Kˣ) : K) = 1 := fun x => x.mul_inv
  linear_combination (v (.inl 0) * v (.inr (.inl 0))) * e (t 0) +
    (v (.inl 1) * v (.inr (.inl 1))) * e (t 1) + (v (.inl 2) * v (.inr (.inl 2))) * e (t 2)

@[expose] def swapFun : Om → Om
  | .inl i => .inr (.inl i)
  | .inr (.inl i) => .inl i
  | .inr (.inr k) => .inr (.inr k)

theorem swapFun_swapFun (j : Om) : swapFun (swapFun j) = j := by
  rcases j with j | j | j <;> rfl

@[expose] def swapPerm : Equiv.Perm Om :=
  ⟨swapFun, swapFun, swapFun_swapFun, swapFun_swapFun⟩

theorem permMatrix_swap_mul_self :
    swapPerm.permMatrix K * swapPerm.permMatrix K = (1 : Matrix Om Om K) := by
  refine Matrix.ext_of_mulVec_single fun i => ?_
  rw [← mulVec_mulVec, permMatrix_mulVec, permMatrix_mulVec, one_mulVec]
  funext j
  exact congrArg (Pi.single i (1 : K)) (swapFun_swapFun j)

@[expose] noncomputable def swapOm : GL Om K :=
  ⟨swapPerm.permMatrix K, swapPerm.permMatrix K, permMatrix_swap_mul_self,
    permMatrix_swap_mul_self⟩

theorem swapOm_inv : (swapOm : GL Om K)⁻¹ = swapOm :=
  inv_eq_of_mul_eq_one_right (Units.ext permMatrix_swap_mul_self)

theorem mulVec_swapOm (v : Om → K) :
    ((swapOm : GL Om K) : Matrix Om Om K) *ᵥ v = v ∘ swapFun :=
  permMatrix_mulVec swapPerm

theorem quadMinus_swapOm (b c : K) (v : Om → K) :
    StatedQuadMinus 4 K b c (((swapOm : GL Om K) : Matrix Om Om K) *ᵥ v) =
      StatedQuadMinus 4 K b c v := by
  rw [mulVec_swapOm, quadMinus_apply, quadMinus_apply]
  simp only [Function.comp, swapFun]
  ring

theorem commutator_torusOm_swapOm (a : Fin 3 → Kˣ) :
    ⁅(torusOm a : GL Om K), swapOm⁆ = torusOm (a ^ 2) := by
  rw [commutatorElement_def, swapOm_inv, ← map_inv]
  apply Units.ext
  refine Matrix.ext_of_mulVec_single fun i => ?_
  simp only [Units.val_mul, ← mulVec_mulVec]
  funext j
  rw [mulVec_torusOm, mulVec_swapOm, Function.comp_apply, mulVec_torusOm, mulVec_swapOm,
    Function.comp_apply, mulVec_torusOm, swapFun_swapFun]
  rcases j with j | j | j <;>
    simp [swapFun, torusEnt_inl, torusEnt_inr_inl, torusEnt_inr_inr, pow_two, mul_assoc]

@[expose] def rootN : Matrix Om Om K :=
  single (.inl 0) (.inl 1) 1 + single (.inr (.inl 1)) (.inr (.inl 0)) 1

theorem rootN_mul_rootN : (rootN : Matrix Om Om K) * rootN = 0 := by
  simp only [rootN, add_mul, mul_add]
  rw [single_mul_single_of_ne _ _ _ _ (by decide), single_mul_single_of_ne _ _ _ _ (by decide),
    single_mul_single_of_ne _ _ _ _ (by decide), single_mul_single_of_ne _ _ _ _ (by decide)]
  simp

theorem rootN_mulVec (v : Om → K) (j : Om) :
    (rootN *ᵥ v) j = (if j = .inl 0 then v (.inl 1) else 0) +
      (if j = .inr (.inl 1) then v (.inr (.inl 0)) else 0) := by
  rw [rootN, add_mulVec, Pi.add_apply, single_mulVec, single_mulVec, Function.update_apply,
    Function.update_apply]
  simp

variable [CharP K 2]

omit [CharP K 2] in
theorem one_add_smul_rootN_mul (a a' : K) :
    (1 + a • rootN : Matrix Om Om K) * (1 + a' • rootN) = 1 + (a + a') • rootN := by
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, rootN_mul_rootN, smul_zero,
    add_zero, add_smul]
  abel

theorem one_add_smul_rootN_mul_self (a : K) :
    (1 + a • rootN : Matrix Om Om K) * (1 + a • rootN) = 1 := by
  rw [one_add_smul_rootN_mul, CharTwo.add_self_eq_zero, zero_smul, add_zero]

@[expose] noncomputable def rootOm : Multiplicative K →* GL Om K where
  toFun a := ⟨1 + a.toAdd • rootN, 1 + a.toAdd • rootN, one_add_smul_rootN_mul_self _,
    one_add_smul_rootN_mul_self _⟩
  map_one' := Units.ext (by simp)
  map_mul' a a' := Units.ext (by
    change (1 + (a.toAdd + a'.toAdd) • rootN : Matrix Om Om K) = _
    rw [← one_add_smul_rootN_mul]
    rfl)

theorem coe_rootOm (a : Multiplicative K) :
    ((rootOm a : GL Om K) : Matrix Om Om K) = 1 + a.toAdd • rootN := rfl

theorem mulVec_rootOm (a : Multiplicative K) (v : Om → K) (j : Om) :
    (((rootOm a : GL Om K) : Matrix Om Om K) *ᵥ v) j = v j + a.toAdd *
      ((if j = .inl 0 then v (.inl 1) else 0) +
        (if j = .inr (.inl 1) then v (.inr (.inl 0)) else 0)) := by
  rw [coe_rootOm, add_mulVec, one_mulVec, smul_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    rootN_mulVec]

theorem quadMinus_rootOm (b c : K) (a : Multiplicative K) (v : Om → K) :
    StatedQuadMinus 4 K b c (((rootOm a : GL Om K) : Matrix Om Om K) *ᵥ v) =
      StatedQuadMinus 4 K b c v := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [show (((rootOm a : GL Om K) : Matrix Om Om K) *ᵥ v) = fun j => v j + a.toAdd *
      ((if j = .inl 0 then v (.inl 1) else 0) +
        (if j = .inr (.inl 1) then v (.inr (.inl 0)) else 0)) from funext (mulVec_rootOm a v),
    quadMinus_apply, quadMinus_apply]
  simp
  linear_combination (a.toAdd * v (.inl 1) * v (.inr (.inl 0))) * h2

theorem torusOm_mul_rootOm (t : Fin 3 → Kˣ) (a : Multiplicative K) :
    (torusOm t : GL Om K) * rootOm a =
      rootOm (Multiplicative.ofAdd ((t 0 : K) * ((t 1)⁻¹ : Kˣ) * a.toAdd)) * torusOm t := by
  apply Units.ext
  refine Matrix.ext_of_mulVec_single fun i => ?_
  simp only [Units.val_mul, ← mulVec_mulVec]
  funext j
  rw [mulVec_torusOm, mulVec_rootOm, mulVec_rootOm, mulVec_torusOm, mulVec_torusOm,
    mulVec_torusOm, toAdd_ofAdd]
  have h0 : (t 0 : K) ≠ 0 := (t 0).ne_zero
  have h1 : (t 1 : K) ≠ 0 := (t 1).ne_zero
  rcases j with j | j | j <;> fin_cases j <;>
    simp [torusEnt_inl, torusEnt_inr_inl, torusEnt_inr_inr]
  all_goals field_simp


omit [CharP K 2] in
theorem torusOm_injective : Function.Injective (torusOm : (Fin 3 → Kˣ) →* GL Om K) := by
  intro s t hst
  funext i
  have h := congrArg (fun A : GL Om K => (A : Matrix Om Om K) (.inl i) (.inl i)) hst
  simp only [torusOm, MonoidHom.comp_apply, coe_diagOm, diagonal_apply_eq, torusEnt_inl] at h
  exact Units.ext h

theorem le_localRank_statedOmegaMinus_torus [Finite K] {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hK : r ∣ Nat.card Kˣ) (b c : K) :
    3 ≤ localRank r (StatedProj (StatedOmega (StatedQuadMinus 4 K b c))) := by
  have hμ := CFSG.RankThree.PartTwo.Census.card_rootsOfUnity_of_dvd hr hK
  set μ := rootsOfUnity r K
  set incl := μ.subtype
  set Ω : Subgroup (GL Om K) := StatedOmega (StatedQuadMinus 4 K b c) with hΩ
  set O : Subgroup (GL Om K) := Subgroup.closure
    {A : GL Om K | ∀ v, StatedQuadMinus 4 K b c ((A : Matrix Om Om K) *ᵥ v) =
      StatedQuadMinus 4 K b c v} with hO
  have hΩO : Ω = ⁅O, O⁆ := rfl
  have hT : ∀ t, (torusOm t : GL Om K) ∈ O := fun t => Subgroup.subset_closure
    (quadMinus_torusOm b c t)
  have hS : (swapOm : GL Om K) ∈ O := Subgroup.subset_closure (quadMinus_swapOm b c)
  have hR : ∀ a, (rootOm a : GL Om K) ∈ O := fun a => Subgroup.subset_closure
    (quadMinus_rootOm b c a)
  have hTΩ : ∀ t : Fin 3 → Kˣ, t ^ r = 1 → (torusOm t : GL Om K) ∈ Ω := by
    intro t ht
    obtain ⟨k, hk⟩ := hr.odd_of_ne_two hr2
    have ha : (t ^ (k + 1)) ^ 2 = t := by
      rw [← pow_mul, show (k + 1) * 2 = r + 1 by omega, pow_succ, ht, one_mul]
    rw [← ha, ← commutator_torusOm_swapOm, hΩO]
    exact Subgroup.commutator_mem_commutator (hT _) hS
  have hnt : Nontrivial μ := by
    rw [← Finite.one_lt_card_iff_nontrivial, hμ]
    exact hr.one_lt
  obtain ⟨ζ, hζ⟩ := exists_ne (1 : μ)
  have hζK : ((ζ : Kˣ) : K) ≠ 1 := fun h => hζ (Subtype.ext (Units.ext h))
  set t₀ : Fin 3 → Kˣ := Function.update 1 0 (ζ : Kˣ) with ht₀
  have ht₀r : t₀ ^ r = 1 := by
    funext i
    rw [Pi.pow_apply, ht₀]
    rcases eq_or_ne i 0 with rfl | hi
    · rw [Function.update_self, ← Subgroup.coe_pow,
        CFSG.RankThree.PartTwo.Census.rootsOfUnity_pow_eq_one, OneMemClass.coe_one]
      rfl
    · rw [Function.update_of_ne hi, Pi.one_apply, one_pow]
  have hRΩ : ∀ x : Multiplicative K, (rootOm x : GL Om K) ∈ Ω := by
    intro x
    set a' : K := x.toAdd / (((ζ : Kˣ) : K) - 1)
    have hD := torusOm_mul_rootOm t₀ (Multiplicative.ofAdd a')
    have hlam : ((t₀ 0 : Kˣ) : K) * ((t₀ 1)⁻¹ : Kˣ) = ((ζ : Kˣ) : K) := by
      rw [ht₀, Function.update_self, Function.update_of_ne (by decide), Pi.one_apply, inv_one,
        Units.val_one, mul_one]
    have hx : rootOm x = ⁅(torusOm t₀ : GL Om K), rootOm (Multiplicative.ofAdd a')⁆ := by
      rw [commutatorElement_def, hD, mul_inv_cancel_right, ← map_inv, ← map_mul]
      congr 1
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_inv, toAdd_ofAdd, toAdd_ofAdd, hlam]
      have hne : ((ζ : Kˣ) : K) - 1 ≠ 0 := sub_ne_zero.mpr hζK
      have ha' : a' * (((ζ : Kˣ) : K) - 1) = x.toAdd := div_mul_cancel₀ _ hne
      linear_combination (-1 : K) * ha'
    rw [hx, hΩO]
    exact Subgroup.commutator_mem_commutator (hT _) (hR _)
  let τ : (Fin 3 → μ) →* Ω := (torusOm.comp (incl.compLeft (Fin 3))).codRestrict Ω fun s =>
    hTΩ _ (funext fun i => by
      rw [Pi.pow_apply, MonoidHom.compLeft_apply, Function.comp_apply, ← map_pow,
        CFSG.RankThree.PartTwo.Census.rootsOfUnity_pow_eq_one, map_one, Pi.one_apply])
  let ρ : Multiplicative K →* Ω := rootOm.codRestrict Ω hRΩ
  have hτ : Function.Injective τ := by
    intro s s' h
    have h1 := congrArg Subtype.val h
    have h2 := torusOm_injective h1
    funext i
    exact Subtype.ext (congrFun h2 i)
  refine CFSG.RankThree.PartTwo.Census.le_localRank_quotient_of_le_normalizer _ hr
    (E := τ.range) (P := ρ.range)
    (CFSG.RankThree.PartTwo.Census.isElemAbelian_range
      (fun s => funext fun j => CFSG.RankThree.PartTwo.Census.rootsOfUnity_pow_eq_one (s j)) τ)
    ?_ ?_ ?_ ?_ ?_
  · rw [← Nat.card_congr (MonoidHom.ofInjective hτ).toEquiv]
    exact CFSG.RankThree.PartTwo.Census.card_fun_rootsOfUnity hμ
  · rw [eq_bot_iff]
    rintro x ⟨⟨s, rfl⟩, hxN⟩
    obtain ⟨z, hz⟩ := Subgroup.mem_subgroupOf.mp hxN
    have hz' : Matrix.GeneralLinearGroup.scalar Om z = torusOm (incl.compLeft (Fin 3) s) := hz
    have h1 := congrArg (fun A : GL Om K => (A : Matrix Om Om K) (.inr (.inr 0)) (.inr (.inr 0)))
      hz'
    simp only [Matrix.GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq, torusOm,
      MonoidHom.comp_apply, coe_diagOm, torusEnt_inr_inr, Units.val_one] at h1
    have hz1 : z = 1 := Units.ext h1
    rw [hz1, map_one] at hz'
    have hs : s = 1 := hτ (Subtype.ext (by
      change torusOm (incl.compLeft (Fin 3) s) = torusOm (incl.compLeft (Fin 3) 1)
      rw [← hz', map_one, map_one]))
    rw [Subgroup.mem_bot, hs, map_one]
  · intro y
    obtain ⟨x, hx⟩ := y.2
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    rw [pow_one, pow_two]
    change ((y : Ω) : GL Om K) * (y : Ω) = 1
    rw [← hx]
    change rootOm x * rootOm x = 1
    rw [← map_mul]
    have : x * x = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_one, CharTwo.add_self_eq_zero]
    rw [this, map_one]
  · intro hP
    have h1 : ρ (Multiplicative.ofAdd 1) ∈ ρ.range := ⟨_, rfl⟩
    obtain ⟨z, hz⟩ := Subgroup.mem_subgroupOf.mp (hP h1)
    have hz' : Matrix.GeneralLinearGroup.scalar Om z = rootOm (Multiplicative.ofAdd (1 : K)) := hz
    have h2 := congrArg (fun A : GL Om K => (A : Matrix Om Om K) (.inl 0) (.inl 1)) hz'
    simp [Matrix.GeneralLinearGroup.coe_scalar, coe_rootOm, rootN] at h2
  · refine CFSG.RankThree.PartTwo.Census.le_normalizer_of_conj_mem ?_
    rintro _ ⟨s, rfl⟩ _ ⟨x, rfl⟩
    refine ⟨Multiplicative.ofAdd (((incl.compLeft (Fin 3) s 0 : Kˣ) : K) *
      ((incl.compLeft (Fin 3) s 1)⁻¹ : Kˣ) * x.toAdd), Subtype.ext ?_⟩
    change rootOm _ = torusOm (incl.compLeft (Fin 3) s) * rootOm x *
      (torusOm (incl.compLeft (Fin 3) s))⁻¹
    rw [torusOm_mul_rootOm, mul_inv_cancel_right]

end CFSG.RankThree.PartTwo.KFacts.KS21LocalRank

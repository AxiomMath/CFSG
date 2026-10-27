module

public import CFSG.LocalAnalysis.StandardType.GGPresentation
public import CFSG.LieType.Universal.SpecialLinearExtras
public import CFSG.LieType.Universal.SpecialLinearRoots.SignedPerm

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits CoxeterSystem

section Braid

variable {B : Type*} {G : Type*} [Group G] (f : B → G)

theorem prod_map_alternatingWord (i i' : B) (m : ℕ) :
    ((alternatingWord i i' m).map f).prod =
      if Even m then (f i * f i') ^ (m / 2) else (f i' * f i) ^ (m / 2) * f i' := by
  induction m generalizing i i' with
  | zero => simp [alternatingWord]
  | succ m ih =>
    rw [alternatingWord_succ, List.concat_eq_append, List.map_append, List.prod_append, ih i' i]
    rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · have h1 : ¬ Even (k + k + 1) := Nat.not_even_iff_odd.mpr ⟨k, by ring⟩
      have h2 : (k + k) / 2 = k := by omega
      have h3 : (k + k + 1) / 2 = k := by omega
      simp [h1, h2, h3]
    · have h1 : ¬ Even (2 * k + 1) := Nat.not_even_iff_odd.mpr ⟨k, rfl⟩
      have h2 : Even (2 * k + 1 + 1) := ⟨k + 1, by ring⟩
      have h3 : (2 * k + 1) / 2 = k := by omega
      have h4 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
      simp [h1, h2, h3, h4, pow_succ, mul_assoc]

theorem isLiftable_of_braid {M : CoxeterMatrix B} (hsq : ∀ i, f i * f i = 1)
    (hbraid : ∀ i i', ((braidWord M i i').map f).prod = ((braidWord M i' i).map f).prod) :
    M.IsLiftable f := by
  intro i i'
  by_cases hii : i = i'
  · subst hii
    rw [M.diagonal, pow_one, hsq]
  have h := hbraid i i'
  rw [braidWord, braidWord, M.symmetric i' i, prod_map_alternatingWord,
    prod_map_alternatingWord] at h
  set a := f i
  set b := f i'
  have ha : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq i)
  have hb : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq i')
  have hba : b * a = (a * b)⁻¹ := by rw [mul_inv_rev, ha, hb]
  rcases Nat.even_or_odd (M i i') with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hev : Even (M i i') := ⟨k, hk⟩
    simp only [hev, ite_true] at h
    rw [hba, inv_pow, hk, show (k + k) / 2 = k by omega] at h
    rw [hk, pow_add]
    exact mul_eq_one_iff_eq_inv.mpr h
  · have hev : ¬ Even (M i i') := Nat.not_even_iff_odd.mpr ⟨k, hk⟩
    simp only [hev, ite_false] at h
    rw [hba, inv_pow, hk, show (2 * k + 1) / 2 = k by omega] at h
    have h' : b = (a * b) ^ k * ((a * b) ^ k * a) := inv_mul_eq_iff_eq_mul.mp h
    have e : (a * b) ^ M i i' = ((a * b) ^ k * ((a * b) ^ k * a)) * b := by
      rw [hk, pow_succ, two_mul, pow_add]
      simp only [mul_assoc]
    rw [e, ← h']
    exact hsq i'

end Braid

@[expose] def GGStandardCopy {U : Type*} [Group U] (D : UniversalRootDatum U)
    (ν : GGWeyl D →* U) : Prop :=
  GGWeylLift D ν ∧ ∀ (w : GGWeyl D), ∀ α ∈ D.roots, weylAction D.isFiniteType w α = α →
    ∀ z ∈ D.rootGroup α, ν w * z * (ν w)⁻¹ = z

section Lift

variable {U : Type*} [Group U] {D : UniversalRootDatum U} {n : Fin D.rank → U}
  {H : Fin D.rank → Subgroup U}

@[expose] noncomputable def ggWeylLiftOf
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hsq : ∀ i, n i * n i = 1) : GGWeyl D →* U :=
  (coxeterMatrix D.isFiniteType).toCoxeterSystem.lift ⟨n, isLiftable_of_braid n hsq hct.braid⟩

theorem ggWeylLiftOf_simple
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hsq : ∀ i, n i * n i = 1) (i : Fin D.rank) :
    ggWeylLiftOf hct hsq ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i) = n i :=
  (coxeterMatrix D.isFiniteType).toCoxeterSystem.lift_apply_simple _ i

theorem ggWeylLiftOf_spec
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hsq : ∀ i, n i * n i = 1) : GGWeylLift D (ggWeylLiftOf hct hsq) where
  conj_mem w := by
    induction w using (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple_induction_left with
    | one =>
      intro γ _ x hx
      simpa using hx
    | mul_simple_left w i ih =>
      intro γ hγ x hx
      have h1 := ih γ hγ x hx
      have h2 := hct.conj_mem i _ ((ggIsCTRootSystem D).smul_mem w γ hγ) _ h1
      rw [map_mul (ggWeylLiftOf hct hsq), ggWeylLiftOf_simple, weylAction_mul_apply]
      simpa only [mul_inv_rev, mul_assoc] using h2
  simple_mem i := by
    rw [ggWeylLiftOf_simple]
    exact hct.n_mem i
  le_rankOne := hct.le_rankOne

end Lift

section SpecialLinear

open Matrix SpecialLinear SpecialLinearGroup

variable (m : ℕ) {F : Type} [Field F]

theorem eq_one_of_mul_self_of_two (h2 : (2 : F) = 0) {e : F} (he : e * e = 1) : e = 1 := by
  have h : (e - 1) * (e - 1) = 0 := by linear_combination he + (1 - e) * h2
  exact sub_eq_zero.mp (mul_self_eq_zero.mp h)

theorem coe_weylRep_of_two (h2 : (2 : F) = 0) (k : Fin m) :
    ((weylRep m F k : SpecialLinearGroup (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      signedPerm (Equiv.swap k.castSucc k.succ) 1 := by
  rw [weylRep, coe_transvection_mul_transvection_mul_transvection, weylMatrix]
  congr 1
  funext r
  exact eq_one_of_mul_self_of_two h2 (weylSign_mul_self _ r)

theorem weylRep_mul_self (h2 : (2 : F) = 0) (k : Fin m) : weylRep m F k * weylRep m F k = 1 := by
  apply coeMonoidHom_injective
  rw [map_mul, map_one, coeMonoidHom_apply, coe_weylRep_of_two m h2, signedPerm_mul_signedPerm,
    Equiv.swap_mul_self, signedPerm_one]
  simp

@[expose] noncomputable def slWeylLift (h2 : (2 : F) = 0) :
    (coxeterMatrix (isFiniteType_A m)).Group →* SpecialLinearGroup (Fin (m + 1)) F :=
  (coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.lift
    ⟨weylRep m F, isLiftable_of_braid _ (weylRep_mul_self m h2) (isCTGroupDatum m F).braid⟩

theorem slWeylLift_simple (h2 : (2 : F) = 0) (k : Fin m) :
    slWeylLift m h2 ((coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.simple k) =
      weylRep m F k :=
  (coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.lift_apply_simple _ k

theorem slWeylLift_spec (h2 : (2 : F) = 0) : GGWeylLift (rootDatum m F) (slWeylLift m h2) :=
  ggWeylLiftOf_spec (D := rootDatum m F) (isCTGroupDatum m F) (weylRep_mul_self m h2)

theorem slWeylLift_signedPerm (h2 : (2 : F) = 0) (w : (coxeterMatrix (isFiniteType_A m)).Group) :
    ∃ π : Equiv.Perm (Fin (m + 1)),
      coeMonoidHom (slWeylLift m h2 w) = signedPerm π 1 ∧
      ∀ γ, toStd m (weylAction (isFiniteType_A m) w γ) = fun a => toStd m γ (π.symm a) := by
  induction w using (coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.simple_induction_left with
  | one =>
    refine ⟨1, ?_, fun γ => ?_⟩
    · rw [map_one, map_one, signedPerm_one]
      exact Matrix.diagonal_one.symm
    · rw [map_one, Module.End.one_apply]
      rfl
  | mul_simple_left w k ih =>
    obtain ⟨π, hπ, hact⟩ := ih
    refine ⟨Equiv.swap k.castSucc k.succ * π, ?_, fun γ => ?_⟩
    · rw [map_mul, map_mul, slWeylLift_simple, coeMonoidHom_apply (weylRep m F k),
        coe_weylRep_of_two m h2, hπ, signedPerm_mul_signedPerm]
      congr 1
      funext r
      simp
    · rw [weylAction_mul_apply, weylAction_simple, toStd_reflection, hact]
      funext a
      simp [Equiv.Perm.mul_def]

theorem slWeylLift_fix (h2 : (2 : F) = 0) (w : (coxeterMatrix (isFiniteType_A m)).Group)
    {α : Fin m → ℤ} (hα : α ∈ roots (isFiniteType_A m) ∅)
    (hfix : weylAction (isFiniteType_A m) w α = α)
    {z : SpecialLinearGroup (Fin (m + 1)) F} (hz : z ∈ rootGroup m F α) :
    slWeylLift m h2 w * z * (slWeylLift m h2 w)⁻¹ = z := by
  rw [roots_eq] at hα
  obtain ⟨i, j, hij, hαij⟩ := hα
  have hz' : z ∈ rootSubgroup m F hij := by
    rw [← rootGroup_eq m F hij hαij]
    exact hz
  obtain ⟨c, rfl⟩ := (mem_rootSubgroup hij z).mp hz'
  obtain ⟨π, hπ, hact⟩ := slWeylLift_signedPerm m h2 w
  have key := hact α
  rw [hfix, hαij] at key
  have hval : ∀ a, (Pi.single i 1 - Pi.single j 1 : Fin (m + 1) → ℤ) (π a) =
      (Pi.single i 1 - Pi.single j 1 : Fin (m + 1) → ℤ) a := by
    intro a
    have := congrFun key (π a)
    simpa using this
  have hπi : π i = i := by
    by_contra h
    have := hval i
    simp only [Pi.sub_apply, Pi.single_apply, h, hij] at this
    split_ifs at this <;> omega
  have hπj : π j = j := by
    by_contra h
    have := hval j
    simp only [Pi.sub_apply, Pi.single_apply, h, Ne.symm hij] at this
    split_ifs at this <;> omega
  rw [conj_transvection_of_coe_eq_signedPerm hπ (fun _ => by simp) hij c]
  apply coeMonoidHom_injective
  simp only [coeMonoidHom_apply, transvection_coe, Pi.one_apply, one_mul, hπi, hπj]

theorem slWeylLift_standardCopy (h2 : (2 : F) = 0) :
    GGStandardCopy (rootDatum m F) (slWeylLift m h2) :=
  ⟨slWeylLift_spec m h2, fun w _ hα hfix _ hz => slWeylLift_fix m h2 w hα hfix hz⟩

end SpecialLinear

end CFSG.StandardType

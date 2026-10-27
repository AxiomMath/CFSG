module

public import CFSG.Monster.B.Classical.E6AdjointTable
import CFSG.Monster.B.Classical.E6AdjointJacobi
import CFSG.Monster.B.Classical.E6AdjointChecks
import CFSG.LieType.Steinberg.Adjoint.Pairs

public noncomputable section

namespace CFSG.Monster.B.Classical.E6Adjoint

open CFSG.Blueprint.Chevalley

variable {R : Type*} [CommRing R]

theorem ext_single {M : Type*} [AddCommMonoid M] [Module R M]
    {f g : RootModule Tag.E6 R →ₗ[R] M}
    (h : ∀ x : Label Tag.E6, f (Finsupp.single x 1) = g (Finsupp.single x 1)) : f = g :=
  Finsupp.lhom_ext' fun x => LinearMap.ext_ring (h x)

theorem ext_single₂ {M : Type*} [AddCommMonoid M] [Module R M]
    {f g : RootModule Tag.E6 R →ₗ[R] RootModule Tag.E6 R →ₗ[R] M}
    (h : ∀ x y : Label Tag.E6,
      f (Finsupp.single x 1) (Finsupp.single y 1) = g (Finsupp.single x 1) (Finsupp.single y 1)) :
    f = g :=
  Finsupp.lhom_ext' fun x => LinearMap.ext_ring <|
    Finsupp.lhom_ext' fun y => LinearMap.ext_ring <| h x y

theorem ext_lab {M : Type*} [AddCommMonoid M] [Module R M]
    {f g : RootModule Tag.E6 R →ₗ[R] M}
    (h : ∀ a : Fin 78, f (Finsupp.single (lab a) 1) = g (Finsupp.single (lab a) 1)) : f = g :=
  ext_single fun x => by
    obtain ⟨a, rfl⟩ := lab_surjective x
    exact h a

theorem ext_lab₂ {M : Type*} [AddCommMonoid M] [Module R M]
    {f g : RootModule Tag.E6 R →ₗ[R] RootModule Tag.E6 R →ₗ[R] M}
    (h : ∀ a b : Fin 78, f (Finsupp.single (lab a) 1) (Finsupp.single (lab b) 1) =
      g (Finsupp.single (lab a) 1) (Finsupp.single (lab b) 1)) : f = g :=
  ext_single₂ fun x y => by
    obtain ⟨a, rfl⟩ := lab_surjective x
    obtain ⟨b, rfl⟩ := lab_surjective y
    exact h a b

theorem cartan_comm
    (i j : Fin Tag.E6.rank) : Tag.E6.cartan i j = Tag.E6.cartan j i := by
  have h := CFSG.LieType.Steinberg.Adjoint.symmetrizedCartan_symm Tag.E6 i j
  simpa [Tag.symmetrizedCartan, Tag.symmetrizer] using h

private def cartanInvBits : ℕ := 0x4a0081a46

private def cartanInv (j k : Fin Tag.E6.rank) : ℤ :=
  if cartanInvBits.testBit (6 * j + k) then 1 else 0

private theorem cartan_mul_cartanInv_mod : ∀ i k : Fin Tag.E6.rank,
    (∑ j : Fin Tag.E6.rank, Tag.E6.cartan i j * cartanInv j k) % 2 = if i = k then 1 else 0 := by
  decide +kernel

private theorem code_self : ∀ a < 78, code a a = 0 := by
  decide +kernel

theorem formLabel_comm
    (x y : Label Tag.E6) : formLabel R x y = formLabel R y x := by
  rcases x with i | α <;> rcases y with j | β
  · simp only [formLabel, cartan_comm i j]
  · rfl
  · rfl
  · simp only [formLabel]
    by_cases h : β.1 = -α.1
    · rw [ite_eq_left h, ite_eq_left (by rw [h, neg_neg])]
    · rw [ite_eq_right h, ite_eq_right fun h' => h (by rw [h', neg_neg])]

theorem form_comm
    (u v : RootModule Tag.E6 R) : form R u v = form R v u := by
  have h : form R = LinearMap.flip (form R) := ext_single₂ fun x y => by
    rw [LinearMap.flip_apply, form_single, form_single, formLabel_comm]
  exact (LinearMap.congr_fun₂ h u v).trans (LinearMap.flip_apply _ _ _)

section CharTwo

variable [CharP R 2]

private theorem sum_cartan_mul_cartanInv (i k : Fin Tag.E6.rank) :
    ∑ j, (Tag.E6.cartan i j : R) * (cartanInv j k : R) = if i = k then 1 else 0 := by
  have h := cartan_mul_cartanInv_mod i k
  have hc : ((∑ j, Tag.E6.cartan i j * cartanInv j k : ℤ) : R) = if i = k then 1 else 0 := by
    rw [intCast_eq_ite_emod, h]
    by_cases hik : i = k
    · simp [hik]
    · simp [hik]
  push_cast at hc
  exact hc

theorem bracketLabel_comm (x y : Label Tag.E6) : bracketLabel R x y = bracketLabel R y x := by
  rcases x with i | α <;> rcases y with j | β
  · rfl
  · rfl
  · rfl
  · simp only [bracketLabel]
    by_cases h : β.1 = -α.1
    · have h' : α.1 = -β.1 := by rw [h, neg_neg]
      rw [ite_eq_left h, ite_eq_left h']
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [h, Pi.neg_apply, Int.cast_neg, CharTwo.neg_eq]
    · have h' : ¬α.1 = -β.1 := fun h' => h (by rw [h', neg_neg])
      rw [ite_eq_right h, ite_eq_right h', add_comm]

theorem bracket_comm (u v : RootModule Tag.E6 R) : bracket R u v = bracket R v u := by
  have h : bracket R = (bracket R).flip := ext_single₂ fun x y => by
    rw [LinearMap.flip_apply, bracket_single, bracket_single, bracketLabel_comm]
  exact (LinearMap.congr_fun₂ h u v).trans (LinearMap.flip_apply _ _ _)

theorem bracketLabel_self
    (x : Label Tag.E6) : bracketLabel R x x = 0 := by
  obtain ⟨a, rfl⟩ := lab_surjective x
  rw [← bracket_single, bracket_lab, brMask, code_self a a.2]
  simp [maskOf, toVec_zero]

theorem bracket_self
    (u : RootModule Tag.E6 R) : bracket R u u = 0 := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv =>
    simp only [map_add, LinearMap.add_apply, hu, hv, zero_add, add_zero]
    rw [bracket_comm v u, ← two_smul R, CharTwo.two_eq_zero, zero_smul]
  | single x r =>
    rw [← Finsupp.smul_single_one]
    simp only [map_smul, LinearMap.smul_apply, bracket_single, bracketLabel_self, smul_zero]

private theorem jacobi_lab_left
    (b c : Fin 78) (u : RootModule Tag.E6 R) :
    bracket R u (bracket R (Finsupp.single (lab b) 1) (Finsupp.single (lab c) 1)) +
        bracket R (Finsupp.single (lab b) 1) (bracket R (Finsupp.single (lab c) 1) u) +
      bracket R (Finsupp.single (lab c) 1) (bracket R u (Finsupp.single (lab b) 1)) = 0 := by
  have h : (bracket R).flip (bracket R (Finsupp.single (lab b) 1) (Finsupp.single (lab c) 1)) +
      (bracket R (Finsupp.single (lab b) 1)).comp (bracket R (Finsupp.single (lab c) 1)) +
      (bracket R (Finsupp.single (lab c) 1)).comp
        ((bracket R).flip (Finsupp.single (lab b) 1)) = 0 :=
    ext_lab fun a => by
      simp only [LinearMap.add_apply, LinearMap.flip_apply, LinearMap.comp_apply,
        LinearMap.zero_apply]
      exact jacobi_lab (jacOK_all a b c)
  simpa using LinearMap.congr_fun h u

theorem bracket_jacobi
    (u v w : RootModule Tag.E6 R) :
    bracket R u (bracket R v w) + bracket R v (bracket R w u) + bracket R w (bracket R u v) =
      0 := by
  have h : (bracket R).compr₂ (bracket R u) + (bracket R).compl₂ ((bracket R).flip u) +
      ((bracket R).compl₂ (bracket R u)).flip = 0 :=
    ext_lab₂ fun b c => by
      simp only [LinearMap.add_apply, LinearMap.compr₂_apply, LinearMap.compl₂_apply,
        LinearMap.flip_apply, LinearMap.zero_apply]
      exact jacobi_lab_left b c u
  simpa using LinearMap.congr_fun₂ h v w

theorem formLabel_self (x : Label Tag.E6) : formLabel R x x = 0 := by
  rcases x with i | ⟨α, hα⟩
  · simp only [formLabel, Tag.cartan_self]
    push_cast
    exact CharTwo.two_eq_zero
  · simp only [formLabel]
    refine ite_eq_right fun h => hα.ne_zero (funext fun j => ?_)
    have := congrFun h j
    simp only [Pi.neg_apply] at this
    simp only [Pi.zero_apply]
    omega

theorem form_self
    (u : RootModule Tag.E6 R) : form R u u = 0 := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv =>
    simp only [map_add, LinearMap.add_apply, hu, hv, zero_add, add_zero]
    rw [form_comm v u, CharTwo.add_self_eq_zero]
  | single x r =>
    rw [← Finsupp.smul_single_one]
    simp only [map_smul, LinearMap.smul_apply, form_single, formLabel_self, smul_zero]

theorem form_bracket
    (u v w : RootModule Tag.E6 R) :
    form R (bracket R u v) w = form R u (bracket R v w) := by
  have h₁ : ∀ a b : Fin 78,
      form R (bracket R (Finsupp.single (lab a) 1) (Finsupp.single (lab b) 1)) =
        (form R (Finsupp.single (lab a) 1)).comp (bracket R (Finsupp.single (lab b) 1)) :=
    fun a b => ext_lab fun c => by
      rw [LinearMap.comp_apply]
      exact invariant_lab (invOK_all a b c)
  have h₂ : (bracket R).compr₂ (LinearMap.flip (form R) w) =
      (form R).compl₂ ((bracket R).flip w) :=
    ext_lab₂ fun a b => by
      simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.flip_apply]
      exact LinearMap.congr_fun (h₁ a b) w
  simpa using LinearMap.congr_fun₂ h₂ u v

private theorem exists_dual
    (x : Label Tag.E6) :
    ∃ n : RootModule Tag.E6 R, ∀ y : Label Tag.E6,
      form R (Finsupp.single y 1) n = if y = x then 1 else 0 := by
  rcases x with k | ⟨α, hα⟩
  · refine ⟨∑ j, (cartanInv j k : R) • hVec Tag.E6 R j, fun y => ?_⟩
    simp only [map_sum, map_smul, smul_eq_mul, hVec, form_single]
    rcases y with i | β
    · simp only [formLabel, Sum.inl.injEq]
      rw [← sum_cartan_mul_cartanInv i k]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    · simp [formLabel]
  · refine ⟨Finsupp.single (Sum.inr ⟨-α, CFSG.LieType.Steinberg.TagRoots.isRoot_neg hα⟩) 1,
      fun y => ?_⟩
    rw [form_single]
    rcases y with i | ⟨β, hβ⟩
    · simp [formLabel]
    · simp only [formLabel, neg_inj, Sum.inr.injEq, Subtype.mk.injEq]
      by_cases h : α = β
      · rw [ite_eq_left h, ite_eq_left h.symm]
      · rw [ite_eq_right h, ite_eq_right fun h' => h h'.symm]

theorem form_separatingLeft :
    (form R).SeparatingLeft := by
  intro m hm
  ext x
  obtain ⟨n, hn⟩ := exists_dual (R := R) x
  have h : LinearMap.flip (form R) n = Finsupp.lapply x := ext_single fun y => by
    rw [LinearMap.flip_apply, hn y, Finsupp.lapply_apply, Finsupp.single_apply]
  have h' := LinearMap.congr_fun h m
  rw [LinearMap.flip_apply, Finsupp.lapply_apply, hm n] at h'
  rw [← h', Finsupp.zero_apply]

theorem form_nondegenerate :
    (form R).Nondegenerate :=
  ⟨form_separatingLeft, fun n hn => form_separatingLeft n fun m => by rw [form_comm]; exact hn m⟩

end CharTwo

end CFSG.Monster.B.Classical.E6Adjoint

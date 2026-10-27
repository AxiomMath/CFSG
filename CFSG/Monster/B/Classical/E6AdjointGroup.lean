module

public import CFSG.Monster.B.Classical.E6AdjointLie
public import CFSG.Blueprint.ChevalleyRootGroups
public import CFSG.Fischer.F4
import CFSG.Monster.B.Classical.E6AdjointChecks
import CFSG.Blueprint.ChevalleyPinnedBridge
import CFSG.LieType.Steinberg.Adjoint.Pairs

public noncomputable section

namespace CFSG.Monster.B.Classical.E6Adjoint

open CFSG.Blueprint.Chevalley

variable {R : Type*} [CommRing R]

theorem rootOp_apply (a : RootModule Tag.E6 R) (c : R) (u : RootModule Tag.E6 R) :
    (1 + c • ad R a + c ^ 2 • formTensor R a : Module.End R (RootModule Tag.E6 R)) u =
      u + c • bracket R a u + c ^ 2 • (form R a u • a) := by
  simp [ad_apply, formTensor_apply]

section CharTwo

variable [CharP R 2]

theorem bracket_bracket_left
    (a u v : RootModule Tag.E6 R) :
    bracket R a (bracket R u v) = bracket R (bracket R a u) v + bracket R u (bracket R a v) := by
  have h := bracket_jacobi a u v
  rw [bracket_comm v a, bracket_comm v (bracket R a u)] at h
  linear_combination (norm := module) h -
    (CharTwo.two_eq_zero (R := R)) • (bracket R u (bracket R a v) + bracket R (bracket R a u) v)

theorem rootOp_bracket
    {a : RootModule Tag.E6 R}
    (hsq : ∀ u, bracket R a (bracket R a u) = 0)
    (hQ : ∀ u v, form R a (bracket R u v) • a = form R a u • bracket R a v +
      bracket R (bracket R a u) (bracket R a v) + form R a v • bracket R u a)
    (c : R) (u v : RootModule Tag.E6 R) :
    (1 + c • ad R a + c ^ 2 • formTensor R a : Module.End R (RootModule Tag.E6 R))
        (bracket R u v) =
      bracket R ((1 + c • ad R a + c ^ 2 • formTensor R a : Module.End R (RootModule Tag.E6 R)) u)
        ((1 + c • ad R a + c ^ 2 • formTensor R a : Module.End R (RootModule Tag.E6 R)) v) := by
  have hsq' : ∀ w, bracket R (bracket R a w) a = 0 := fun w => by rw [bracket_comm, hsq]
  have hder := bracket_bracket_left a u v
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, ad_apply,
    formTensor_apply, map_add, map_smul, bracket_self a, hsq, hsq', smul_zero, add_zero]
  linear_combination (norm := module) c • hder + c ^ 2 • hQ u v

theorem rootOp_form
    {a : RootModule Tag.E6 R} (hsq : ∀ u, bracket R a (bracket R a u) = 0)
    (c : R) (u v : RootModule Tag.E6 R) :
    form R ((1 + c • ad R a + c ^ 2 • formTensor R a : Module.End R (RootModule Tag.E6 R)) u)
        ((1 + c • ad R a + c ^ 2 • formTensor R a : Module.End R (RootModule Tag.E6 R)) v) =
      form R u v := by
  have h₁ : ∀ w x, form R (bracket R a w) x = form R w (bracket R a x) := fun w x => by
    rw [bracket_comm, form_bracket]
  have h₂ : ∀ x, form R a (bracket R a x) = 0 := fun x => by
    rw [← form_bracket, bracket_self, map_zero, LinearMap.zero_apply]
  have h₃ : form R u a = form R a u := form_comm u a
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, ad_apply,
    formTensor_apply, map_add, map_smul, smul_eq_mul, h₁, h₂, hsq, bracket_self a, form_self a,
    map_zero, h₃]
  linear_combination (c * form R u (bracket R a v) + c ^ 2 * form R a u * form R a v) *
    (CharTwo.two_eq_zero (R := R))

omit [CharP R 2] in
theorem conj_rootOp {g : (Module.End R (RootModule Tag.E6 R))ˣ}
    (hb : ∀ u v, g.val (bracket R u v) = bracket R (g.val u) (g.val v))
    (hf : ∀ u v, form R (g.val u) (g.val v) = form R u v)
    (a : RootModule Tag.E6 R) (c : R) :
    g.val * (1 + c • ad R a + c ^ 2 • formTensor R a) * g⁻¹.val =
      1 + c • ad R (g.val a) + c ^ 2 • formTensor R (g.val a) := by
  have hgi : ∀ w, g.val (g⁻¹.val w) = w :=
    fun w => by rw [← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply]
  refine LinearMap.ext fun u => ?_
  have hf' : form R a (g⁻¹.val u) = form R (g.val a) u := by
    rw [← hf a, hgi]
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply, ad_apply, formTensor_apply, map_add, map_smul, hb, hgi, hf']

end CharTwo

private theorem natAbs_cast [CharP R 2] (n : ℤ) : ((n.natAbs : ℕ) : R) = (n : R) := by
  rw [← Int.cast_natCast, Int.natCast_natAbs]
  rcases abs_choice n with h | h <;> rw [h]
  simp [CharTwo.neg_eq]

private theorem cartanPair_single (j i : Fin Tag.E6.rank) :
    cartanPair j (Pi.single i 1) = Tag.E6.cartan j i := by
  simp [cartanPair, Pi.single_apply]

private theorem sum_single_smul_hVec (i : Fin Tag.E6.rank) :
    ∑ k, (((Pi.single i 1 : Fin Tag.E6.rank → ℤ) k : ℤ) : R) • hVec Tag.E6 R k =
      hVec Tag.E6 R i := by
  simp [Pi.single_apply]

private theorem xOp_hVec (i j : Fin Tag.E6.rank) (c : R) :
    xOp Tag.E6 R i c (hVec Tag.E6 R j) =
      hVec Tag.E6 R j +
        (((Tag.E6.cartan j i).natAbs : R) * c) • rootVec Tag.E6 R (Pi.single i 1) := by
  change xOp Tag.E6 R i c (Finsupp.single (Sum.inl j) 1) = _
  rw [xOp, Finsupp.linearCombination_single, one_smul]

private theorem yOp_hVec (i j : Fin Tag.E6.rank) (c : R) :
    yOp Tag.E6 R i c (hVec Tag.E6 R j) =
      hVec Tag.E6 R j +
        (((Tag.E6.cartan j i).natAbs : R) * c) • rootVec Tag.E6 R (-Pi.single i 1) := by
  change yOp Tag.E6 R i c (Finsupp.single (Sum.inl j) 1) = _
  rw [yOp, Finsupp.linearCombination_single, one_smul]

private theorem xOp_rootVec_single (i : Fin Tag.E6.rank) (c : R) :
    xOp Tag.E6 R i c (rootVec Tag.E6 R (Pi.single i 1)) = rootVec Tag.E6 R (Pi.single i 1) := by
  rw [rootVec_eq_single (isRoot_single _ i), xOp, Finsupp.linearCombination_single, one_smul]
  exact ite_eq_left rfl

private theorem xOp_rootVec_neg_single (i : Fin Tag.E6.rank) (c : R) :
    xOp Tag.E6 R i c (rootVec Tag.E6 R (-Pi.single i 1)) =
      rootVec Tag.E6 R (-Pi.single i 1) + c • hVec Tag.E6 R i +
        c ^ 2 • rootVec Tag.E6 R (Pi.single i 1) := by
  rw [rootVec_eq_single (isRoot_neg_single _ i), xOp, Finsupp.linearCombination_single,
    one_smul]
  exact (ite_eq_right (single_ne_neg_single i).symm).trans (ite_eq_left rfl)

private theorem yOp_rootVec_neg_single (i : Fin Tag.E6.rank) (c : R) :
    yOp Tag.E6 R i c (rootVec Tag.E6 R (-Pi.single i 1)) = rootVec Tag.E6 R (-Pi.single i 1) := by
  rw [rootVec_eq_single (isRoot_neg_single _ i), yOp, Finsupp.linearCombination_single,
    one_smul]
  exact ite_eq_left rfl

private theorem yOp_rootVec_single (i : Fin Tag.E6.rank) (c : R) :
    yOp Tag.E6 R i c (rootVec Tag.E6 R (Pi.single i 1)) =
      rootVec Tag.E6 R (Pi.single i 1) + c • hVec Tag.E6 R i +
        c ^ 2 • rootVec Tag.E6 R (-Pi.single i 1) := by
  rw [rootVec_eq_single (isRoot_single _ i), yOp, Finsupp.linearCombination_single, one_smul]
  exact (ite_eq_right (single_ne_neg_single i)).trans (ite_eq_left rfl)

open CFSG.LieType.Steinberg.Adjoint in
private theorem string_le_one
    {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α)
    {i : Fin Tag.E6.rank} (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) :
    stringUp Tag.E6 i α + stringDown Tag.E6 i α ≤ 1 := by
  obtain ⟨-, hs⟩ := isRoot_add_smul_single_iff hα i h₁ h₂
  have hn : ∀ m : ℤ, IsRoot Tag.E6 (α + m • Pi.single i 1) →
      2 * m * iform α (Pi.single i 1) + 2 * m ^ 2 = 0 := by
    intro m hm
    obtain ⟨j, hj⟩ := iform_self_of_isRoot hm
    obtain ⟨j', hj'⟩ := iform_self_of_isRoot hα
    have hexp : iform (α + m • Pi.single i 1) (α + m • Pi.single i 1) =
        iform α α + 2 * m * iform α (Pi.single i 1) +
          m ^ 2 * iform (Pi.single i 1 : Fin Tag.E6.rank → ℤ) (Pi.single i 1) := by
      simp only [iform_add_left, iform_add_right, iform_smul_left, iform_smul_right]
      rw [iform_comm (Pi.single i 1) α]
      ring
    rw [iform_single_single] at hexp
    simp only [Tag.symmetrizer, Matrix.one_apply_eq] at hj hj' hexp
    rw [hj, hj'] at hexp
    linear_combination -hexp
  have hu : ∀ m : ℤ, 0 ≤ m → m ≤ stringUp Tag.E6 i α →
      2 * m * iform α (Pi.single i 1) + 2 * m ^ 2 = 0 :=
    fun m h0 hm => hn m ((hs m).2 ⟨by omega, hm⟩)
  have hd : ∀ m : ℤ, m ≤ 0 → -(stringDown Tag.E6 i α : ℤ) ≤ m →
      2 * m * iform α (Pi.single i 1) + 2 * m ^ 2 = 0 :=
    fun m h0 hm => hn m ((hs m).2 ⟨hm, by omega⟩)
  by_contra hcon
  rcases Nat.lt_or_ge (stringUp Tag.E6 i α) 2 with hp | hp
  · rcases Nat.lt_or_ge (stringDown Tag.E6 i α) 2 with hq | hq
    · have h1 := hu 1 (by norm_num) (by omega)
      have h2 := hd (-1) (by norm_num) (by omega)
      nlinarith
    · have h1 := hd (-1) (by norm_num) (by omega)
      have h2 := hd (-2) (by norm_num) (by omega)
      nlinarith
  · have h1 := hu 1 (by norm_num) (by omega)
    have h2 := hu 2 (by norm_num) (by omega)
    nlinarith

private theorem xOp_rootVec_of_ne
    (i : Fin Tag.E6.rank) (c : R) {α : Fin Tag.E6.rank → ℤ}
    (hα : IsRoot Tag.E6 α) (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) :
    xOp Tag.E6 R i c (rootVec Tag.E6 R α) =
      rootVec Tag.E6 R α + c • rootVec Tag.E6 R (α + Pi.single i 1) := by
  have hpq := string_le_one hα h₁ h₂
  obtain ⟨-, hs⟩ := isRoot_add_smul_single_iff hα i h₁ h₂
  rw [rootVec_eq_single hα, xOp, Finsupp.linearCombination_single, one_smul]
  simp only [ite_eq_right h₁, ite_eq_right h₂]
  rw [← rootVec_eq_single hα]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (show stringUp Tag.E6 i α ≤ 1 by omega) with h0 | h1
  · rw [h0, Finset.sum_range_one]
    have hnot : ¬IsRoot Tag.E6 (α + Pi.single i 1) := by
      intro h
      have := (hs 1).mp (by rwa [one_smul])
      omega
    simp [rootVec_eq_zero hnot]
  · have hq : stringDown Tag.E6 i α = 0 := by omega
    rw [h1, Finset.sum_range_succ, Finset.sum_range_one, hq]
    simp

private theorem yOp_rootVec_of_ne
    (i : Fin Tag.E6.rank) (c : R) {α : Fin Tag.E6.rank → ℤ}
    (hα : IsRoot Tag.E6 α) (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) :
    yOp Tag.E6 R i c (rootVec Tag.E6 R α) =
      rootVec Tag.E6 R α + c • rootVec Tag.E6 R (α - Pi.single i 1) := by
  have hpq := string_le_one hα h₁ h₂
  obtain ⟨-, hs⟩ := isRoot_add_smul_single_iff hα i h₁ h₂
  rw [rootVec_eq_single hα, yOp, Finsupp.linearCombination_single, one_smul]
  simp only [ite_eq_right h₁, ite_eq_right h₂]
  rw [← rootVec_eq_single hα]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (show stringDown Tag.E6 i α ≤ 1 by omega) with
    h0 | h1
  · rw [h0, Finset.sum_range_one]
    have hnot : ¬IsRoot Tag.E6 (α - Pi.single i 1) := by
      intro h
      have := (hs (-1)).mp (by rwa [neg_smul, one_smul, ← sub_eq_add_neg])
      omega
    simp [rootVec_eq_zero hnot]
  · have hp : stringUp Tag.E6 i α = 0 := by omega
    rw [h1, Finset.sum_range_succ, Finset.sum_range_one, hp]
    simp

section CharTwo

variable [CharP R 2]

theorem xOp_eq
    (i : Fin Tag.E6.rank) (c : R) :
    xOp Tag.E6 R i c = 1 + c • ad R (rootVec Tag.E6 R (Pi.single i 1)) +
      c ^ 2 • formTensor R (rootVec Tag.E6 R (Pi.single i 1)) := by
  have hi := isRoot_single Tag.E6 i
  refine ext_single fun x => ?_
  rw [rootOp_apply]
  rcases x with j | ⟨α, hα⟩
  · rw [show (Finsupp.single (Sum.inl j) 1 : RootModule Tag.E6 R) = hVec Tag.E6 R j from rfl,
      xOp_hVec, bracket_rootVec_hVec hi, form_rootVec_hVec, zero_smul, smul_zero, add_zero,
      smul_smul, cartanPair_single, natAbs_cast, mul_comm]
  · rw [← rootVec_eq_single hα]
    by_cases h₁ : α = Pi.single i 1
    · subst h₁
      rw [xOp_rootVec_single, bracket_self, form_self, zero_smul, smul_zero, smul_zero, add_zero,
        add_zero]
    by_cases h₂ : α = -Pi.single i 1
    · subst h₂
      rw [xOp_rootVec_neg_single, bracket_rootVec_neg hi (isRoot_neg_single _ i),
        form_rootVec_neg hi (isRoot_neg_single _ i), one_smul, sum_single_smul_hVec]
    · rw [xOp_rootVec_of_ne i c hα h₁ h₂, bracket_rootVec_rootVec hi hα h₂,
        form_rootVec_rootVec h₂, zero_smul, smul_zero, add_zero, add_comm (Pi.single i 1) α]

theorem yOp_eq
    (i : Fin Tag.E6.rank) (c : R) :
    yOp Tag.E6 R i c = 1 + c • ad R (rootVec Tag.E6 R (-Pi.single i 1)) +
      c ^ 2 • formTensor R (rootVec Tag.E6 R (-Pi.single i 1)) := by
  have hi := isRoot_neg_single Tag.E6 i
  have hi' : IsRoot Tag.E6 (-(-Pi.single i 1)) := by rw [neg_neg]; exact isRoot_single _ i
  refine ext_single fun x => ?_
  rw [rootOp_apply]
  rcases x with j | ⟨α, hα⟩
  · have hc : (cartanPair j (-Pi.single i 1) : R) = (Tag.E6.cartan j i : R) := by
      simp [cartanPair, Pi.single_apply, CharTwo.neg_eq]
    rw [show (Finsupp.single (Sum.inl j) 1 : RootModule Tag.E6 R) = hVec Tag.E6 R j from rfl,
      yOp_hVec, bracket_rootVec_hVec hi, form_rootVec_hVec, zero_smul, smul_zero, add_zero,
      smul_smul, hc, natAbs_cast, mul_comm]
  · rw [← rootVec_eq_single hα]
    by_cases h₂ : α = -Pi.single i 1
    · subst h₂
      rw [yOp_rootVec_neg_single, bracket_self, form_self, zero_smul, smul_zero, smul_zero,
        add_zero, add_zero]
    by_cases h₁ : α = Pi.single i 1
    · subst h₁
      have hb := bracket_rootVec_neg (R := R) hi hi'
      have hf := form_rootVec_neg (R := R) hi hi'
      rw [neg_neg] at hb hf
      have hsum : ∑ k, (((-Pi.single i 1 : Fin Tag.E6.rank → ℤ) k : ℤ) : R) • hVec Tag.E6 R k =
          hVec Tag.E6 R i := by
        simp [Pi.single_apply, CharTwo.neg_eq]
      rw [yOp_rootVec_single, hb, hf, one_smul, hsum]
    · have hne : α ≠ -(-Pi.single i 1) := by rwa [neg_neg]
      rw [yOp_rootVec_of_ne i c hα h₁ h₂, bracket_rootVec_rootVec hi hα hne,
        form_rootVec_rootVec hne, zero_smul, smul_zero, add_zero, neg_add_eq_sub]

end CharTwo

private theorem certRoot_simple : (List.finRange Tag.E6.rank).all (fun i =>
    List.ofFn (e6Certificate.root i) ==
      List.ofFn (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) = true := by
  decide +kernel

private theorem certRoot_negSimple : (List.finRange Tag.E6.rank).all (fun i =>
    List.ofFn (e6Certificate.root (6 + 2 * i)) ==
      List.ofFn (-Pi.single i 1 : Fin Tag.E6.rank → ℤ)) = true := by
  decide +kernel

private theorem lt_six (i : Fin Tag.E6.rank) : (i : ℕ) < 6 := by
  have h := i.2
  simp only [Tag.rank] at h
  exact h

private theorem lab_simple (i : Fin Tag.E6.rank) :
    Finsupp.single (lab ⟨6 + i, by have := lt_six i; omega⟩) (1 : R) =
      rootVec Tag.E6 R (Pi.single i 1) := by
  have h := List.all_eq_true.1 certRoot_simple i (List.mem_finRange i)
  have hl : lab ⟨6 + i, by have := lt_six i; omega⟩ =
      Sum.inr ⟨Pi.single i 1, isRoot_single _ i⟩ := by
    rw [lab_of_ge (by simp only [not_lt]; omega)]
    simp only [Sum.inr.injEq, Subtype.mk.injEq]
    rw [show 6 + (i : ℕ) - 6 = i by omega]
    exact RootCertificate.eq_of_ofFn_beq h
  rw [hl, rootVec_eq_single (isRoot_single _ i)]

private theorem lab_negSimple (i : Fin Tag.E6.rank) :
    Finsupp.single (lab ⟨12 + 2 * i, by have := lt_six i; omega⟩) (1 : R) =
      rootVec Tag.E6 R (-Pi.single i 1) := by
  have h := List.all_eq_true.1 certRoot_negSimple i (List.mem_finRange i)
  have hl : lab ⟨12 + 2 * i, by have := lt_six i; omega⟩ =
      Sum.inr ⟨-Pi.single i 1, isRoot_neg_single _ i⟩ := by
    rw [lab_of_ge (by simp only [not_lt]; omega)]
    simp only [Sum.inr.injEq, Subtype.mk.injEq]
    rw [show 12 + 2 * (i : ℕ) - 6 = 6 + 2 * i by omega]
    exact RootCertificate.eq_of_ofFn_beq h
  rw [hl, rootVec_eq_single (isRoot_neg_single _ i)]

section CharTwo

variable [CharP R 2]

private theorem simple_sq
    {A : ℕ} (hA : A ∈ simpleIdx) (hA' : A < 78) (u : RootModule Tag.E6 R) :
    bracket R (Finsupp.single (lab ⟨A, hA'⟩) 1)
      (bracket R (Finsupp.single (lab ⟨A, hA'⟩) 1) u) = 0 := by
  have h : (bracket R (Finsupp.single (lab ⟨A, hA'⟩) 1)).comp
      (bracket R (Finsupp.single (lab ⟨A, hA'⟩) 1)) = 0 :=
    ext_lab fun x => by
      rw [LinearMap.comp_apply, LinearMap.zero_apply]
      exact adSq_lab (A := ⟨A, hA'⟩) (adSqOK_all hA x)
  simpa using LinearMap.congr_fun h u

private theorem simple_Q
    {A : ℕ} (hA : A ∈ simpleIdx) (hA' : A < 78)
    (u v : RootModule Tag.E6 R) :
    form R (Finsupp.single (lab ⟨A, hA'⟩) 1) (bracket R u v) • Finsupp.single (lab ⟨A, hA'⟩) 1 =
      form R (Finsupp.single (lab ⟨A, hA'⟩) 1) u •
          bracket R (Finsupp.single (lab ⟨A, hA'⟩) 1) v +
        bracket R (bracket R (Finsupp.single (lab ⟨A, hA'⟩) 1) u)
          (bracket R (Finsupp.single (lab ⟨A, hA'⟩) 1) v) +
        form R (Finsupp.single (lab ⟨A, hA'⟩) 1) v •
          bracket R u (Finsupp.single (lab ⟨A, hA'⟩) 1) := by
  set a := Finsupp.single (lab ⟨A, hA'⟩) (1 : R) with ha
  have h : (bracket R).compr₂ (formTensor R a) =
      (form R a).smulRight (bracket R a) +
        ((bracket R).comp (bracket R a)).compl₂ (bracket R a) +
        LinearMap.flip ((form R a).smulRight ((bracket R).flip a)) :=
    ext_lab₂ fun x y => by
      simp only [LinearMap.compr₂_apply, formTensor_apply, LinearMap.add_apply,
        LinearMap.smulRight_apply, LinearMap.smul_apply, LinearMap.compl₂_apply,
        LinearMap.comp_apply, LinearMap.flip_apply]
      exact gen_lab (A := ⟨A, hA'⟩) (genOK_all hA x y)
  have h' := LinearMap.congr_fun₂ h u v
  simp only [LinearMap.compr₂_apply, formTensor_apply, LinearMap.add_apply,
    LinearMap.smulRight_apply, LinearMap.smul_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
    LinearMap.flip_apply] at h'
  exact h'

private theorem simple_props
    (i : Fin Tag.E6.rank) :
    (∀ u, bracket R (rootVec Tag.E6 R (Pi.single i 1))
        (bracket R (rootVec Tag.E6 R (Pi.single i 1)) u) = 0) ∧
      (∀ u v, form R (rootVec Tag.E6 R (Pi.single i 1)) (bracket R u v) •
          rootVec Tag.E6 R (Pi.single i 1) =
        form R (rootVec Tag.E6 R (Pi.single i 1)) u •
            bracket R (rootVec Tag.E6 R (Pi.single i 1)) v +
          bracket R (bracket R (rootVec Tag.E6 R (Pi.single i 1)) u)
            (bracket R (rootVec Tag.E6 R (Pi.single i 1)) v) +
          form R (rootVec Tag.E6 R (Pi.single i 1)) v •
            bracket R u (rootVec Tag.E6 R (Pi.single i 1))) := by
  have hA : 6 + (i : ℕ) ∈ simpleIdx := by
    have := lt_six i
    simp only [simpleIdx, List.mem_cons, List.not_mem_nil, or_false]
    omega
  rw [← lab_simple i]
  exact ⟨simple_sq hA _, simple_Q hA _⟩

private theorem negSimple_props
    (i : Fin Tag.E6.rank) :
    (∀ u, bracket R (rootVec Tag.E6 R (-Pi.single i 1))
        (bracket R (rootVec Tag.E6 R (-Pi.single i 1)) u) = 0) ∧
      (∀ u v, form R (rootVec Tag.E6 R (-Pi.single i 1)) (bracket R u v) •
          rootVec Tag.E6 R (-Pi.single i 1) =
        form R (rootVec Tag.E6 R (-Pi.single i 1)) u •
            bracket R (rootVec Tag.E6 R (-Pi.single i 1)) v +
          bracket R (bracket R (rootVec Tag.E6 R (-Pi.single i 1)) u)
            (bracket R (rootVec Tag.E6 R (-Pi.single i 1)) v) +
          form R (rootVec Tag.E6 R (-Pi.single i 1)) v •
            bracket R u (rootVec Tag.E6 R (-Pi.single i 1))) := by
  have hA : 12 + 2 * (i : ℕ) ∈ simpleIdx := by
    have := lt_six i
    simp only [simpleIdx, List.mem_cons, List.not_mem_nil, or_false]
    omega
  rw [← lab_negSimple i]
  exact ⟨simple_sq hA _, simple_Q hA _⟩

end CharTwo

section Field

variable {K : Type*} [Field K]

private def autGroup (K : Type*) [Field K] : Subgroup (ModGL Tag.E6 K) where
  carrier := {g | ∀ u v, g.val (bracket K u v) = bracket K (g.val u) (g.val v) ∧
    form K (g.val u) (g.val v) = form K u v}
  one_mem' := fun u v => by simp
  mul_mem' := by
    intro g h hg hh u v
    simp only [Units.val_mul, Module.End.mul_apply]
    exact ⟨by rw [(hh u v).1, (hg _ _).1], by rw [(hg _ _).2, (hh u v).2]⟩
  inv_mem' := by
    intro g hg u v
    have hgi : ∀ w, g.val (g⁻¹.val w) = w := fun w => by
      rw [← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply]
    have hig : ∀ w, g⁻¹.val (g.val w) = w := fun w => by
      rw [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply]
    have h₁ := hg (g⁻¹.val u) (g⁻¹.val v)
    rw [hgi, hgi] at h₁
    refine ⟨?_, h₁.2.symm⟩
    rw [← h₁.1, hig]

variable [CharP K 2]

private theorem adjointGroup_le_autGroup :
    adjointGroup Tag.E6 K ≤ autGroup K := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨i, c, hg | hg⟩
  · obtain ⟨hsq, hQ⟩ := simple_props (R := K) i
    exact fun u v => by
      rw [hg, xOp_eq]
      exact ⟨rootOp_bracket hsq hQ c u v, rootOp_form hsq c u v⟩
  · obtain ⟨hsq, hQ⟩ := negSimple_props (R := K) i
    exact fun u v => by
      rw [hg, yOp_eq]
      exact ⟨rootOp_bracket hsq hQ c u v, rootOp_form hsq c u v⟩

theorem adjointGroup_bracket
    {g : ModGL Tag.E6 K} (hg : g ∈ adjointGroup Tag.E6 K)
    (u v : RootModule Tag.E6 K) :
    g.val (bracket K u v) = bracket K (g.val u) (g.val v) :=
  (adjointGroup_le_autGroup hg u v).1

theorem adjointGroup_form
    {g : ModGL Tag.E6 K} (hg : g ∈ adjointGroup Tag.E6 K)
    (u v : RootModule Tag.E6 K) :
    form K (g.val u) (g.val v) = form K u v :=
  (adjointGroup_le_autGroup hg u v).2

private theorem pinnedX_eq_conj
    (α : Fin Tag.E6.rank → ℤ) (c : K) :
    pinnedX Tag.E6 K α c =
      pinnedWeyl Tag.E6 K α * xUnit Tag.E6 K (pinnedData Tag.E6 α).1 c *
        (pinnedWeyl Tag.E6 K α)⁻¹ := by
  rw [pinnedX]
  rcases pinnedSign_eq Tag.E6 α with h | h <;> rw [h]
  · rw [one_smul]
  · rw [neg_smul, one_smul, CharTwo.neg_eq]

private theorem weylElt_one_rootVec
    (j : Fin Tag.E6.rank) {β : Fin Tag.E6.rank → ℤ}
    (hβ : IsRoot Tag.E6 β) :
    (weylElt Tag.E6 K j 1 : Module.End K (RootModule Tag.E6 K)) (rootVec Tag.E6 K β) =
      rootVec Tag.E6 K (reflect Tag.E6 j β) := by
  rw [weylElt_rootVec j 1 hβ, one_zpow, Units.val_one, mul_one, CharTwo.neg_eq, one_pow,
    one_smul]

private theorem prod_weylElt_rootVec :
    ∀ (w : List ℕ) {β : Fin Tag.E6.rank → ℤ},
    IsRoot Tag.E6 β →
      ((((w.map fun i => weylElt Tag.E6 K (Tag.E6.idx i) 1).reverse).prod :
          (Module.End K (RootModule Tag.E6 K))ˣ) : Module.End K (RootModule Tag.E6 K))
          (rootVec Tag.E6 K β) =
        rootVec Tag.E6 K (w.foldl (fun v i => reflect Tag.E6 (Tag.E6.idx i) v) β)
  | [], _, _ => by simp
  | i :: w, β, hβ => by
    rw [List.map_cons, List.reverse_cons, List.prod_append, List.prod_singleton, Units.val_mul,
      Module.End.mul_apply, weylElt_one_rootVec _ hβ, List.foldl_cons]
    exact prod_weylElt_rootVec w (IsRoot.reflect _ hβ)

private theorem pinnedWeyl_rootVec
    {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) :
    (pinnedWeyl Tag.E6 K α : Module.End K (RootModule Tag.E6 K))
        (rootVec Tag.E6 K (Pi.single (pinnedData Tag.E6 α).1 1)) = rootVec Tag.E6 K α := by
  rw [pinnedWeyl, prod_weylElt_rootVec _ (isRoot_single _ _), foldl_reflect_pinnedData hα]

theorem pinnedX_eq
    {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) (c : K) :
    (pinnedX Tag.E6 K α c : Module.End K (RootModule Tag.E6 K)) =
      1 + c • ad K (rootVec Tag.E6 K α) + c ^ 2 • formTensor K (rootVec Tag.E6 K α) := by
  have hW := adjointGroup_le_autGroup (pinnedWeyl_mem_adjointGroup (K := K) α)
  rw [pinnedX_eq_conj, Units.val_mul, Units.val_mul, coe_xUnit, xOp_eq,
    conj_rootOp (fun u v => (hW u v).1) (fun u v => (hW u v).2), pinnedWeyl_rootVec hα]

private def ρE6 : Equiv.Perm (Fin Tag.E6.rank) :=
  TwistTag.E6.perm

private theorem cartan_rho (i j : Fin Tag.E6.rank) :
    Tag.E6.cartan (ρE6 i) (ρE6 j) = Tag.E6.cartan i j :=
  TwistTag.cartan_perm TwistTag.E6 i j

private def Pd (K : Type*) [Field K] : Module.End K (RootModule Tag.E6 K) :=
  (diagramMap TwistTag.E6 K : Module.End K (RootModule TwistTag.E6.tag K))

omit [CharP K 2] in
private theorem P_hVec (i : Fin Tag.E6.rank) : Pd K (hVec Tag.E6 K i) = hVec Tag.E6 K (ρE6 i) :=
  diagramMap_hVec TwistTag.E6 K i

private theorem permLattice_symm (γ : Fin Tag.E6.rank → ℤ) :
    permLattice ρE6.symm (permLattice ρE6 γ) = γ := by
  funext k
  simp [permLattice]

omit [CharP K 2] in
private theorem P_rootVec (γ : Fin Tag.E6.rank → ℤ) :
    Pd K (rootVec Tag.E6 K γ) = rootVec Tag.E6 K (permLattice ρE6 γ) := by
  by_cases hγ : IsRoot Tag.E6 γ
  · exact diagramMap_rootVec TwistTag.E6 K γ hγ
  · have hγ' : ¬IsRoot Tag.E6 (permLattice ρE6 γ) := fun h => hγ (by
      have := h.permLattice (cartan_perm_symm cartan_rho)
      rwa [permLattice_symm] at this)
    rw [rootVec_eq_zero hγ, rootVec_eq_zero hγ', map_zero]

private theorem permLattice_inj {v w : Fin Tag.E6.rank → ℤ}
    (h : permLattice ρE6 v = permLattice ρE6 w) : v = w := by
  rw [← permLattice_symm v, h, permLattice_symm]

private theorem cartanPair_rho (i : Fin Tag.E6.rank) (α : Fin Tag.E6.rank → ℤ) :
    cartanPair (ρE6 i) (permLattice ρE6 α) = cartanPair i α := by
  simp only [cartanPair, permLattice, Function.comp_apply]
  rw [← Equiv.sum_comp ρE6]
  simp [cartan_rho]

omit [CharP K 2] in
private theorem P_sum (α : Fin Tag.E6.rank → ℤ) :
    Pd K (∑ i, (α i : K) • hVec Tag.E6 K i) =
      ∑ i, ((permLattice ρE6 α i : ℤ) : K) • hVec Tag.E6 K i := by
  rw [map_sum]
  simp only [map_smul, P_hVec]
  rw [← Equiv.sum_comp ρE6 (fun i => ((permLattice ρE6 α i : ℤ) : K) • hVec Tag.E6 K i)]
  simp [permLattice]

omit [CharP K 2] in
private theorem Pd_bracket (u v : RootModule Tag.E6 K) :
    Pd K (bracket K u v) = bracket K (Pd K u) (Pd K v) := by
  have h : (bracket K).compr₂ (Pd K) = ((bracket K).comp (Pd K)).compl₂ (Pd K) :=
    ext_single₂ fun x y => by
      simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply]
      rcases x with i | ⟨α, hα⟩ <;> rcases y with j | ⟨β, hβ⟩
      · rw [show (Finsupp.single (Sum.inl i) 1 : RootModule Tag.E6 K) = hVec Tag.E6 K i from rfl,
          show (Finsupp.single (Sum.inl j) 1 : RootModule Tag.E6 K) = hVec Tag.E6 K j from rfl,
          bracket_hVec_hVec, map_zero, P_hVec, P_hVec, bracket_hVec_hVec]
      · rw [show (Finsupp.single (Sum.inl i) 1 : RootModule Tag.E6 K) = hVec Tag.E6 K i from rfl,
          ← rootVec_eq_single hβ, bracket_hVec_rootVec i hβ, map_smul, P_hVec, P_rootVec,
          bracket_hVec_rootVec _ (hβ.permLattice cartan_rho), cartanPair_rho]
      · rw [show (Finsupp.single (Sum.inl j) 1 : RootModule Tag.E6 K) = hVec Tag.E6 K j from rfl,
          ← rootVec_eq_single hα, bracket_rootVec_hVec hα j, map_smul, P_hVec, P_rootVec,
          bracket_rootVec_hVec (hα.permLattice cartan_rho), cartanPair_rho]
      · rw [← rootVec_eq_single hα, ← rootVec_eq_single hβ, P_rootVec, P_rootVec]
        have hα' := hα.permLattice cartan_rho
        have hβ' := hβ.permLattice cartan_rho
        by_cases h : β = -α
        · subst h
          have hn : permLattice ρE6 (-α) = -permLattice ρE6 α := rfl
          rw [bracket_rootVec_neg hα hβ, P_sum, hn, bracket_rootVec_neg hα' (hn ▸ hβ')]
        · have hne : permLattice ρE6 β ≠ -permLattice ρE6 α :=
            fun h' => h (permLattice_inj h')
          rw [bracket_rootVec_rootVec hα hβ h, P_rootVec, bracket_rootVec_rootVec hα' hβ' hne]
          rfl
  simpa using LinearMap.congr_fun₂ h u v

omit [CharP K 2] in
private theorem Pd_form (u v : RootModule Tag.E6 K) :
    form K (Pd K u) (Pd K v) = form K u v := by
  have h : (form K).comp (Pd K) (Pd K) = form K := ext_single₂ fun x y => by
    simp only [LinearMap.BilinForm.comp_apply]
    rcases x with i | ⟨α, hα⟩ <;> rcases y with j | ⟨β, hβ⟩
    · rw [show (Finsupp.single (Sum.inl i) 1 : RootModule Tag.E6 K) = hVec Tag.E6 K i from rfl,
        show (Finsupp.single (Sum.inl j) 1 : RootModule Tag.E6 K) = hVec Tag.E6 K j from rfl,
        P_hVec, P_hVec, form_hVec_hVec, form_hVec_hVec, cartan_rho]
    · rw [show (Finsupp.single (Sum.inl i) 1 : RootModule Tag.E6 K) = hVec Tag.E6 K i from rfl,
        ← rootVec_eq_single hβ, P_hVec, P_rootVec, form_hVec_rootVec, form_hVec_rootVec]
    · rw [show (Finsupp.single (Sum.inl j) 1 : RootModule Tag.E6 K) = hVec Tag.E6 K j from rfl,
        ← rootVec_eq_single hα, P_hVec, P_rootVec, form_rootVec_hVec, form_rootVec_hVec]
    · rw [← rootVec_eq_single hα, ← rootVec_eq_single hβ, P_rootVec, P_rootVec]
      have hα' := hα.permLattice cartan_rho
      have hβ' := hβ.permLattice cartan_rho
      by_cases h : β = -α
      · subst h
        have hn : permLattice ρE6 (-α) = -permLattice ρE6 α := rfl
        rw [hn, form_rootVec_neg hα' (hn ▸ hβ'), form_rootVec_neg hα hβ]
      · have hne : permLattice ρE6 β ≠ -permLattice ρE6 α :=
          fun h' => h (permLattice_inj h')
        rw [form_rootVec_rootVec hne, form_rootVec_rootVec h]
  simpa using LinearMap.BilinForm.congr_fun h u v

omit [CharP K 2] in
theorem diagramMap_bracket (u v : RootModule Tag.E6 K) :
    (diagramMap TwistTag.E6 K : Module.End K (RootModule TwistTag.E6.tag K)) (bracket K u v) =
      bracket K ((diagramMap TwistTag.E6 K : Module.End K (RootModule TwistTag.E6.tag K)) u)
        ((diagramMap TwistTag.E6 K : Module.End K (RootModule TwistTag.E6.tag K)) v) :=
  Pd_bracket u v

omit [CharP K 2] in
theorem diagramMap_form (u v : RootModule Tag.E6 K) :
    form K ((diagramMap TwistTag.E6 K : Module.End K (RootModule TwistTag.E6.tag K)) u)
        ((diagramMap TwistTag.E6 K : Module.End K (RootModule TwistTag.E6.tag K)) v) =
      form K u v :=
  Pd_form u v

end Field

private theorem mapRange_smul' (f : R →+* R) (r : R) (v : RootModule Tag.E6 R) :
    Finsupp.mapRange f (map_zero f) (r • v) = f r • Finsupp.mapRange f (map_zero f) v := by
  ext l
  simp

private theorem mapRange_rootVec (f : R →+* R) (γ : Fin Tag.E6.rank → ℤ) :
    Finsupp.mapRange f (map_zero f) (rootVec Tag.E6 R γ) = rootVec Tag.E6 R γ := by
  by_cases hγ : IsRoot Tag.E6 γ
  · rw [rootVec_eq_single hγ, Finsupp.mapRange_single, map_one]
  · rw [rootVec_eq_zero hγ, Finsupp.mapRange_zero]

private theorem mapRange_hVec (f : R →+* R) (i : Fin Tag.E6.rank) :
    Finsupp.mapRange f (map_zero f) (hVec Tag.E6 R i) = hVec Tag.E6 R i := by
  rw [hVec, Finsupp.mapRange_single, map_one]

private theorem mapRange_bracketLabel (f : R →+* R) (x y : Label Tag.E6) :
    Finsupp.mapRange f (map_zero f) (bracketLabel R x y) = bracketLabel R x y := by
  rcases x with i | α <;> rcases y with j | β <;> simp only [bracketLabel]
  · exact Finsupp.mapRange_zero
  · rw [mapRange_smul', map_intCast, mapRange_rootVec]
  · rw [mapRange_smul', map_intCast, mapRange_rootVec]
  · split_ifs
    · rw [Finsupp.mapRange_finsetSum]
      simp only [mapRange_smul', map_intCast, mapRange_hVec]
    · exact mapRange_rootVec f _

private theorem formLabel_ringHom (f : R →+* R) (x y : Label Tag.E6) :
    f (formLabel R x y) = formLabel R x y := by
  rcases x with i | α <;> rcases y with j | β <;> simp only [formLabel]
  · exact map_intCast f _
  · exact map_zero f
  · exact map_zero f
  · split_ifs
    · exact map_one f
    · exact map_zero f

theorem mapRange_bracket (f : R →+* R) (u v : RootModule Tag.E6 R) :
    Finsupp.mapRange f (map_zero f) (bracket R u v) =
      bracket R (Finsupp.mapRange f (map_zero f) u) (Finsupp.mapRange f (map_zero f) v) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u₁ u₂ h₁ h₂ =>
    rw [map_add, LinearMap.add_apply, Finsupp.mapRange_add (map_add f), h₁, h₂,
      Finsupp.mapRange_add (map_add f), map_add, LinearMap.add_apply]
  | single x r =>
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v₁ v₂ h₁ h₂ =>
      rw [map_add, Finsupp.mapRange_add (map_add f), h₁, h₂, Finsupp.mapRange_add (map_add f),
        map_add]
    | single y s =>
      rw [Finsupp.mapRange_single, Finsupp.mapRange_single, ← Finsupp.smul_single_one x r,
        ← Finsupp.smul_single_one y s, ← Finsupp.smul_single_one x (f r),
        ← Finsupp.smul_single_one y (f s)]
      simp only [map_smul, LinearMap.smul_apply, bracket_single, mapRange_smul',
        mapRange_bracketLabel]

theorem form_mapRange (f : R →+* R) (u v : RootModule Tag.E6 R) :
    form R (Finsupp.mapRange f (map_zero f) u) (Finsupp.mapRange f (map_zero f) v) =
      f (form R u v) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u₁ u₂ h₁ h₂ =>
    rw [Finsupp.mapRange_add (map_add f), map_add, LinearMap.add_apply, h₁, h₂, map_add,
      LinearMap.add_apply, map_add]
  | single x r =>
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v₁ v₂ h₁ h₂ =>
      rw [Finsupp.mapRange_add (map_add f), map_add, h₁, h₂, map_add, map_add]
    | single y s =>
      rw [Finsupp.mapRange_single, Finsupp.mapRange_single, ← Finsupp.smul_single_one x r,
        ← Finsupp.smul_single_one y s, ← Finsupp.smul_single_one x (f r),
        ← Finsupp.smul_single_one y (f s)]
      simp only [map_smul, LinearMap.smul_apply, form_single, smul_eq_mul, map_mul,
        formLabel_ringHom]

private def sqHom (K : Type*) [CommRing K] [CharP K 2] : K →+* K where
  toFun x := x ^ 2
  map_one' := one_pow 2
  map_mul' x y := mul_pow x y 2
  map_zero' := zero_pow two_ne_zero
  map_add' x y := CharTwo.add_sq x y

theorem sq_bracket [CharP R 2] (u v : RootModule Tag.E6 R) :
    Finsupp.mapRange (fun x : R => x ^ 2) (zero_pow two_ne_zero) (bracket R u v) =
      bracket R (Finsupp.mapRange (fun x : R => x ^ 2) (zero_pow two_ne_zero) u)
        (Finsupp.mapRange (fun x : R => x ^ 2) (zero_pow two_ne_zero) v) :=
  mapRange_bracket (sqHom R) u v

theorem sq_form [CharP R 2] (u v : RootModule Tag.E6 R) :
    form R (Finsupp.mapRange (fun x : R => x ^ 2) (zero_pow two_ne_zero) u)
        (Finsupp.mapRange (fun x : R => x ^ 2) (zero_pow two_ne_zero) v) = form R u v ^ 2 :=
  form_mapRange (sqHom R) u v

theorem lie_form_and_root_operators
    (K : Type*) [Field K] [CharP K 2] :
    (∀ u : RootModule Tag.E6 K, bracket K u u = 0) ∧
    (∀ u v w : RootModule Tag.E6 K,
      bracket K u (bracket K v w) + bracket K v (bracket K w u) + bracket K w (bracket K u v) =
        0) ∧
    (∀ u : RootModule Tag.E6 K, form K u u = 0) ∧
    (form K).Nondegenerate ∧
    (∀ u v w : RootModule Tag.E6 K, form K (bracket K u v) w = form K u (bracket K v w)) ∧
    (∀ g ∈ adjointGroup Tag.E6 K, ∀ u v : RootModule Tag.E6 K,
      g.val (bracket K u v) = bracket K (g.val u) (g.val v) ∧
        form K (g.val u) (g.val v) = form K u v) ∧
    (∀ α : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α → ∀ c : K,
      (pinnedX Tag.E6 K α c : Module.End K (RootModule Tag.E6 K)) =
        1 + c • ad K (rootVec Tag.E6 K α) + c ^ 2 • formTensor K (rootVec Tag.E6 K α)) ∧
    (∀ u v : RootModule Tag.E6 K,
      (diagramMap TwistTag.E6 K : Module.End K (RootModule TwistTag.E6.tag K))
          (bracket K u v) =
        bracket K
          ((diagramMap TwistTag.E6 K : Module.End K (RootModule TwistTag.E6.tag K)) u)
          ((diagramMap TwistTag.E6 K : Module.End K (RootModule TwistTag.E6.tag K))
            v) ∧
      form K
          ((diagramMap TwistTag.E6 K : Module.End K (RootModule TwistTag.E6.tag K)) u)
          ((diagramMap TwistTag.E6 K : Module.End K (RootModule TwistTag.E6.tag K))
            v) = form K u v) ∧
    (∀ u v : RootModule Tag.E6 K,
      Finsupp.mapRange (fun x : K => x ^ 2) (zero_pow two_ne_zero) (bracket K u v) =
          bracket K (Finsupp.mapRange (fun x : K => x ^ 2) (zero_pow two_ne_zero) u)
            (Finsupp.mapRange (fun x : K => x ^ 2) (zero_pow two_ne_zero) v) ∧
        form K (Finsupp.mapRange (fun x : K => x ^ 2) (zero_pow two_ne_zero) u)
          (Finsupp.mapRange (fun x : K => x ^ 2) (zero_pow two_ne_zero) v) = form K u v ^ 2) :=
  ⟨bracket_self, bracket_jacobi, form_self, form_nondegenerate, form_bracket,
    fun _ hg u v => ⟨adjointGroup_bracket hg u v, adjointGroup_form hg u v⟩,
    fun _ hα c => pinnedX_eq hα c, fun u v => ⟨diagramMap_bracket u v, diagramMap_form u v⟩,
    fun u v => ⟨sq_bracket u v, sq_form u v⟩⟩

theorem e6_binary_adjoint_lie_form_and_root_operators :
    (∀ u : RootModule Tag.E6 CFSG.Fischer.F4, bracket CFSG.Fischer.F4 u u = 0) ∧
    (∀ u v w : RootModule Tag.E6 CFSG.Fischer.F4,
      bracket CFSG.Fischer.F4 u (bracket CFSG.Fischer.F4 v w) +
          bracket CFSG.Fischer.F4 v (bracket CFSG.Fischer.F4 w u) +
        bracket CFSG.Fischer.F4 w (bracket CFSG.Fischer.F4 u v) = 0) ∧
    (∀ u : RootModule Tag.E6 CFSG.Fischer.F4, form CFSG.Fischer.F4 u u = 0) ∧
    (form CFSG.Fischer.F4).Nondegenerate ∧
    (∀ u v w : RootModule Tag.E6 CFSG.Fischer.F4,
      form CFSG.Fischer.F4 (bracket CFSG.Fischer.F4 u v) w =
        form CFSG.Fischer.F4 u (bracket CFSG.Fischer.F4 v w)) ∧
    (∀ g ∈ adjointGroup Tag.E6 CFSG.Fischer.F4, ∀ u v : RootModule Tag.E6 CFSG.Fischer.F4,
      g.val (bracket CFSG.Fischer.F4 u v) = bracket CFSG.Fischer.F4 (g.val u) (g.val v) ∧
        form CFSG.Fischer.F4 (g.val u) (g.val v) = form CFSG.Fischer.F4 u v) ∧
    (∀ α : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α → ∀ c : CFSG.Fischer.F4,
      (pinnedX Tag.E6 CFSG.Fischer.F4 α c :
          Module.End CFSG.Fischer.F4 (RootModule Tag.E6 CFSG.Fischer.F4)) =
        1 + c • ad CFSG.Fischer.F4 (rootVec Tag.E6 CFSG.Fischer.F4 α) +
          c ^ 2 • formTensor CFSG.Fischer.F4 (rootVec Tag.E6 CFSG.Fischer.F4 α)) ∧
    (∀ u v : RootModule Tag.E6 CFSG.Fischer.F4,
      (diagramMap TwistTag.E6 CFSG.Fischer.F4 :
          Module.End CFSG.Fischer.F4 (RootModule TwistTag.E6.tag CFSG.Fischer.F4))
          (bracket CFSG.Fischer.F4 u v) =
        bracket CFSG.Fischer.F4
          ((diagramMap TwistTag.E6 CFSG.Fischer.F4 :
            Module.End CFSG.Fischer.F4 (RootModule TwistTag.E6.tag CFSG.Fischer.F4)) u)
          ((diagramMap TwistTag.E6 CFSG.Fischer.F4 :
            Module.End CFSG.Fischer.F4 (RootModule TwistTag.E6.tag CFSG.Fischer.F4)) v) ∧
      form CFSG.Fischer.F4
          ((diagramMap TwistTag.E6 CFSG.Fischer.F4 :
            Module.End CFSG.Fischer.F4 (RootModule TwistTag.E6.tag CFSG.Fischer.F4)) u)
          ((diagramMap TwistTag.E6 CFSG.Fischer.F4 :
            Module.End CFSG.Fischer.F4 (RootModule TwistTag.E6.tag CFSG.Fischer.F4)) v) =
        form CFSG.Fischer.F4 u v) ∧
    (∀ u v : RootModule Tag.E6 CFSG.Fischer.F4,
      Finsupp.mapRange (fun x : CFSG.Fischer.F4 => x ^ 2) (zero_pow two_ne_zero)
          (bracket CFSG.Fischer.F4 u v) =
        bracket CFSG.Fischer.F4
          (Finsupp.mapRange (fun x : CFSG.Fischer.F4 => x ^ 2) (zero_pow two_ne_zero) u)
          (Finsupp.mapRange (fun x : CFSG.Fischer.F4 => x ^ 2) (zero_pow two_ne_zero) v) ∧
      form CFSG.Fischer.F4
          (Finsupp.mapRange (fun x : CFSG.Fischer.F4 => x ^ 2) (zero_pow two_ne_zero) u)
          (Finsupp.mapRange (fun x : CFSG.Fischer.F4 => x ^ 2) (zero_pow two_ne_zero) v) =
        form CFSG.Fischer.F4 u v ^ 2) :=
  lie_form_and_root_operators CFSG.Fischer.F4

end CFSG.Monster.B.Classical.E6Adjoint

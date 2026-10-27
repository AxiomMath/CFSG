module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcPositiveRootDecomposition
public import CFSG.LieType.Chevalley.ParabolicRootFactorData
public import CFSG.LieType.Chevalley.SignKernelPositiveRepresentatives

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.SimplyLacedCover
  CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag}

theorem eq_parabolicRoots_of_orthogonal_complement
    (hτ : ∀ i, τ.symmetrizer i i = 1) {S : Set (Fin τ.rank)}
    {Ψ : Set (Fin τ.rank → ℤ)} (hsub : Ψ ⊆ parabolicRoots τ S)
    (hneg : ∀ α ∈ Ψ, -α ∈ Ψ)
    (hadd : ∀ α ∈ Ψ, ∀ β ∈ Ψ, IsRoot τ (α + β) → α + β ∈ Ψ)
    (horth : ∀ α ∈ Ψ, ∀ β ∈ parabolicRoots τ S, β ∉ Ψ → iform α β = 0) :
    Ψ = parabolicRoots τ {j | (Pi.single j 1 : Fin τ.rank → ℤ) ∈ Ψ} := by
  classical
  have hpos : ∀ n : ℕ, ∀ α : Fin τ.rank → ℤ, IsRoot τ α → height α = n →
      0 < height α → α ∈ parabolicRoots τ S →
      (α ∈ Ψ ↔ ∀ j, (Pi.single j 1 : Fin τ.rank → ℤ) ∉ Ψ → α j = 0) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro α hα hn hp hS
      rcases CFSG.StandardType.isRoot_eq_single_or_exists_add hτ hα hp with
        ⟨j, rfl⟩ | ⟨a, b, ha, hb, hpa, hpb, hab⟩
      · constructor
        · intro hj k hk
          by_cases hkj : k = j
          · subst k
            exact (hk hj).elim
          · simp [Pi.single_eq_of_ne hkj]
        · intro h
          by_contra hj
          have := h j hj
          simp at this
      · have hsupport : ∀ j, α j = 0 → a j = 0 ∧ b j = 0 := by
          intro j hj
          have ha0 := (IsRoot.height_pos_iff ha).1 hpa j
          have hb0 := (IsRoot.height_pos_iff hb).1 hpb j
          have he := congrFun hab j
          simp only [Pi.add_apply] at he
          omega
        have hSa : a ∈ parabolicRoots τ S :=
          ⟨ha, fun j hj => (hsupport j (hS.2 j hj)).1⟩
        have hSb : b ∈ parabolicRoots τ S :=
          ⟨hb, fun j hj => (hsupport j (hS.2 j hj)).2⟩
        have hna : height a = ((height a).toNat : ℕ) :=
          (Int.toNat_of_nonneg (le_of_lt hpa)).symm
        have hnb : height b = ((height b).toNat : ℕ) :=
          (Int.toNat_of_nonneg (le_of_lt hpb)).symm
        have hheight : height α = height a + height b := by rw [hab, height_add]
        have hla : (height a).toNat < n := by omega
        have hlb : (height b).toNat < n := by omega
        have hia := ih (height a).toNat hla a ha hna hpa hSa
        have hib := ih (height b).toNat hlb b hb hnb hpb hSb
        have haa : iform a a = 2 := iform_self_eq_two hτ ha
        have hbb : iform b b = 2 := iform_self_eq_two hτ hb
        have hαα : iform α α = 2 := iform_self_eq_two hτ hα
        have habf : iform a b = -1 := by
          rw [hab, iform_add_left, iform_add_right, iform_add_right,
            iform_comm b a, haa, hbb] at hαα
          omega
        have hαa : iform α a = 1 := by
          rw [hab, iform_add_left, haa, iform_comm b a, habf]
          norm_num
        have hαb : iform α b = 1 := by
          rw [hab, iform_add_left, habf, hbb]
          norm_num
        constructor
        · intro hmem
          have haΨ : a ∈ Ψ := by
            by_contra h
            have := horth α hmem a hSa h
            rw [hαa] at this
            norm_num at this
          have hbΨ : b ∈ Ψ := by
            by_contra h
            have := horth α hmem b hSb h
            rw [hαb] at this
            norm_num at this
          intro j hj
          rw [hab, Pi.add_apply, hia.1 haΨ j hj, hib.1 hbΨ j hj, add_zero]
        · intro h
          have haΨ : a ∈ Ψ := hia.2 fun j hj => (hsupport j (h j hj)).1
          have hbΨ : b ∈ Ψ := hib.2 fun j hj => (hsupport j (h j hj)).2
          rw [hab]
          exact hadd a haΨ b hbΨ (hab ▸ hα)
  have hiff : ∀ α ∈ parabolicRoots τ S,
      α ∈ Ψ ↔ ∀ j, (Pi.single j 1 : Fin τ.rank → ℤ) ∉ Ψ → α j = 0 := by
    intro α hα
    rcases IsRoot.height_pos_or_neg hα.1 with hp | hn
    · exact hpos (height α).toNat α hα.1
        (Int.toNat_of_nonneg (le_of_lt hp)).symm hp hα
    · have hp : 0 < height (-α) := by rw [height_neg]; omega
      have hαn : -α ∈ parabolicRoots τ S :=
        ⟨IsRoot.neg hα.1, fun j hj => by simp [hα.2 j hj]⟩
      have hi := hpos (height (-α)).toNat (-α) hαn.1
        (Int.toNat_of_nonneg (le_of_lt hp)).symm hp hαn
      constructor
      · intro h j hj
        have := hi.1 (hneg α h) j hj
        simpa only [Pi.neg_apply, neg_eq_zero] using this
      · intro h
        have hmem : -α ∈ Ψ := hi.2 fun j hj => by simp [h j hj]
        simpa using hneg (-α) hmem
  have hCS : {j | (Pi.single j 1 : Fin τ.rank → ℤ) ∈ Ψ} ⊆ S := by
    intro j hj
    by_contra h
    have := (hsub hj).2 j h
    simp at this
  ext α
  constructor
  · intro h
    exact ⟨(hsub h).1, (hiff α (hsub h)).1 h⟩
  · intro h
    have hS : α ∈ parabolicRoots τ S :=
      ⟨h.1, fun j hj => h.2 j (fun hC => hj (hCS hC))⟩
    exact (hiff α hS).2 h.2

theorem componentRoots_eq_smul_parabolicRoots_of_kernel
    (hτ : ∀ j, τ.symmetrizer j j = 1) {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (i : KernelComponent χ)
    (u : WeylGroup τ) {S : Set (Fin τ.rank)}
    (hkernel : (u • ·) '' kernelRoots χ = parabolicRoots τ S) :
    ∃ C ⊆ S, componentRoots χ i = (u⁻¹ • ·) '' parabolicRoots τ C := by
  classical
  let Ψ : Set (Fin τ.rank → ℤ) := (u • ·) '' componentRoots χ i
  have hcomp := isRootComponent_componentRoots i
  have hsub : Ψ ⊆ parabolicRoots τ S := by
    rintro α ⟨β, hβ, rfl⟩
    rw [← hkernel]
    obtain ⟨hβker, -⟩ := hβ
    exact ⟨β, hβker, rfl⟩
  have hneg : ∀ α ∈ Ψ, -α ∈ Ψ := by
    rintro α ⟨β, hβ, rfl⟩
    exact ⟨-β, hcomp.neg_mem β hβ, smul_neg u β⟩
  have hadd : ∀ α ∈ Ψ, ∀ β ∈ Ψ, IsRoot τ (α + β) → α + β ∈ Ψ := by
    rintro α ⟨a, ha, rfl⟩ β ⟨b, hb, rfl⟩ hab
    have hroot : IsRoot τ (a + b) := by
      simpa only [smul_add, inv_smul_smul] using IsRoot.smul hab u⁻¹
    exact ⟨a + b, hcomp.add_mem a ha b hb hroot, smul_add u a b⟩
  have horth : ∀ α ∈ Ψ, ∀ β ∈ parabolicRoots τ S, β ∉ Ψ → iform α β = 0 := by
    rintro α ⟨a, ha, rfl⟩ β hβ hnot
    have hβker : u⁻¹ • β ∈ kernelRoots χ := by
      rw [← hkernel] at hβ
      obtain ⟨b, hb, rfl⟩ := hβ
      simpa only [inv_smul_smul] using hb
    let j : KernelComponent χ := ⟦⟨u⁻¹ • β, hβker⟩⟧
    have hj : u⁻¹ • β ∈ componentRoots χ j := ⟨hβker, rfl⟩
    have hij : i ≠ j := by
      intro he
      apply hnot
      exact ⟨u⁻¹ • β, he.symm ▸ hj, smul_inv_smul u β⟩
    have h0 := iform_eq_zero_of_ne_class hij ha hj
    have h := iform_smul u a (u⁻¹ • β)
    rw [smul_inv_smul, h0] at h
    exact h
  have heq := eq_parabolicRoots_of_orthogonal_complement hτ hsub hneg hadd horth
  have hCS : {j | (Pi.single j 1 : Fin τ.rank → ℤ) ∈ Ψ} ⊆ S := by
    intro j hj
    by_contra h
    have := (hsub hj).2 j h
    simp at this
  refine ⟨_, hCS, ?_⟩
  ext α
  constructor
  · intro hα
    refine ⟨u • α, ?_, inv_smul_smul u α⟩
    rw [← heq]
    exact ⟨α, hα, rfl⟩
  · rintro ⟨β, hβ, rfl⟩
    rw [← heq] at hβ
    obtain ⟨α, hα, rfl⟩ := hβ
    simpa only [inv_smul_smul] using hα

end CFSG.LieType.Chevalley

end

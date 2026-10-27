module

public import CFSG.RankThree.PartOne.KC.OrthogonalNonbinaryNonsplit

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module QuadraticMap CFSG.Assembly CFSG.RankThree.Classical CFSG.RankThree.Classical2
  CFSG.ClassicalGroups.Orthogonal

open _root_.Classical in
theorem exists_active_element_eight {K V : Type} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (Q : QuadraticForm K V)
    (hQ : (polarBilin Q).Nondegenerate) (hV : finrank K V = 8) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpl : p ≠ ringChar K) (hpq : ¬ p ∣ Nat.card K ^ 2 - 1)
    (A : Subgroup (ProjOrthDerived Q)) (hA : IsElemAbelian p A) (hAc : Nat.card A = p ^ 2) :
    ∃ a : orthDerived Q, a ^ p = 1 ∧
      QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) a ∈ A ∧
      QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) a ≠ 1 ∧
      finrank K (LinearMap.ker (((a : orthDerived Q) : V ≃ₗ[K] V).toLinearMap -
        LinearMap.id)) = 4 ∧
      ¬ ∃ S : Submodule K (LinearMap.ker (((a : orthDerived Q) : V ≃ₗ[K] V).toLinearMap -
          LinearMap.id)), finrank K S = 2 ∧
        ∀ s ∈ S, (Q.comp (LinearMap.ker (((a : orthDerived Q) : V ≃ₗ[K] V).toLinearMap -
          LinearMap.id)).subtype) s = 0 := by
  have hp2 : p ≠ 2 := by omega
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hℓ : (ringChar K).Prime := CharP.char_is_prime K _
  have : CharP K (ringChar K) := ringChar.charP K
  obtain ⟨Ã, hle, hsyl, e', he', -, -, -, -, hline, -⟩ :=
    orthogonal_inner_plane_kernel_line_quadratic_decomposition hℓ hp hp2 hpl Q hQ A hA hAc
  obtain ⟨hDat, hDims⟩ := kernelLineDims Q hQ hp hp2 hpl A hA hAc Ã ⟨hle, hsyl⟩
  obtain ⟨M₁, M₂, hM₁, hM₂, hM₁₂, hM₁a, hM₂a⟩ := hDat.two_active
  have hdim4 : ∀ M : Subgroup Ã, Nat.card M = p → lineSpace M ≠ ⊥ →
      4 ≤ finrank K (lineSpace M) := fun M hM hMa => by
    obtain ⟨hpos, hdvd⟩ := hDims.dvd M hM hMa
    have hlcm0 : Nat.lcm (orderOf (Nat.card K : ZMod p)) 2 ≠ 0 := fun h => by
      rw [h] at hdvd
      exact hpos.ne' (zero_dvd_iff.mp hdvd)
    exact (four_le_lcm_of_not_dvd (Nat.card K) hpq hlcm0).trans (Nat.le_of_dvd hpos hdvd)
  have hdisj : Disjoint (lineFixSpace M₁) (lineSpace M₂) := by
    have hi := hDat.internal.submodule_iSupIndep (some ⟨M₂, hM₂⟩)
    refine Disjoint.symm (Disjoint.mono_right ?_ hi)
    rw [hDims.line_fix M₁ hM₁]
    refine sup_le ?_ ?_
    · exact le_iSup₂_of_le (f := fun (j : Option {M : Subgroup Ã // Nat.card M = p})
        (_ : j ≠ some ⟨M₂, hM₂⟩) => innerSummand p Ã j) none (by simp) le_rfl
    · exact le_iSup₂_of_le (f := fun (j : Option {M : Subgroup Ã // Nat.card M = p})
        (_ : j ≠ some ⟨M₂, hM₂⟩) => innerSummand p Ã j) (some ⟨M₁, hM₁⟩)
        (fun h => hM₁₂ (congrArg Subtype.val (Option.some.inj h))) le_rfl
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (lineFixSpace M₁) (lineSpace M₂)
  rw [disjoint_iff.mp hdisj, finrank_bot] at hsum
  have hle8 : finrank K ↥(lineFixSpace M₁ ⊔ lineSpace M₂) ≤ 8 :=
    hV ▸ Submodule.finrank_le _
  have hle1 : lineSpace M₁ ≤ lineFixSpace M₁ := by
    rw [hDims.line_fix M₁ hM₁]
    exact le_sup_right
  have hW4 : finrank K (lineFixSpace M₁) = 4 := by
    have h1 := Submodule.finrank_mono hle1
    have h2 := hdim4 M₁ hM₁ hM₁a
    have h3 := hdim4 M₂ hM₂ hM₂a
    omega
  have hM1 : 1 < Nat.card M₁ := by
    rw [hM₁]
    exact hp.one_lt
  have : Finite M₁ := Nat.finite_of_card_ne_zero (by omega)
  have : Nontrivial M₁ := Finite.one_lt_card_iff_nontrivial.mp hM1
  obtain ⟨⟨a, haM⟩, ha1⟩ := exists_ne (1 : M₁)
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hker := (hline M₁ hM₁ a haM ha1').1
  refine ⟨(a : orthDerived Q), ?_, ?_, ?_, ?_, ?_⟩
  · have := congrArg Subtype.val (hDat.exp a)
    simpa using this
  · exact Subgroup.mem_comap.mp (hle a.2)
  · intro h
    have h1 : e' a = 1 := Subtype.ext ((he' a).trans h)
    exact ha1' (e'.injective (h1.trans (map_one e').symm))
  · rw [hker]
    exact hW4
  · rw [hker]
    exact not_split_four_of_active hp hp3 hpl hpq hDat hDims hM₁ hM₁a hW4

end CFSG.RankThree.PartOne.KCOrthogonal

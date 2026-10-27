module

public import CFSG.Open.StatedDefs
public import CFSG.GroupTheory.PCore.Construction
import CFSG.LocalAnalysis.RankThreeUC.Section5.PCoreEqBotOfFaithfulIrreducible
import TauCeti.RepresentationTheory.Irreducible

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KOrdNat

open CFSG.Open

open scoped Matrix

private noncomputable def naturalRep (K : Type) [Field K] (d : ℕ) :
    Representation K ↥(StatedSL d K) (Fin d → K) :=
  (Units.coeHom (Module.End K (Fin d → K))).comp
    ((Matrix.GeneralLinearGroup.toLin (n := Fin d) (R := K)).toMonoidHom.comp
      (StatedSL d K).subtype)

private lemma naturalRep_apply {K : Type} [Field K] (d : ℕ) (g : ↥(StatedSL d K))
    (v : Fin d → K) :
    naturalRep K d g v = ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ v := by
  simp [naturalRep, Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply]

private lemma naturalRep_injective {K : Type} [Field K] (d : ℕ) :
    Function.Injective (naturalRep K d) := by
  intro g h hgh
  have h₁ : (Matrix.GeneralLinearGroup.toLin (n := Fin d) (R := K)) (g : GL (Fin d) K) =
      (Matrix.GeneralLinearGroup.toLin (n := Fin d) (R := K)) (h : GL (Fin d) K) :=
    Units.ext (by simpa [naturalRep] using hgh)
  exact Subtype.ext ((Matrix.GeneralLinearGroup.toLin (n := Fin d) (R := K)).injective h₁)

private noncomputable def slTransvection {K : Type} [Field K] {d : ℕ} (i j : Fin d) (hij : i ≠ j)
    (c : K) : ↥(StatedSL d K) :=
  ⟨Matrix.GeneralLinearGroup.mk'' (Matrix.transvection i j c)
      (by rw [Matrix.det_transvection_of_ne i j hij]; exact isUnit_one),
    Subgroup.subset_closure (by simpa using Matrix.det_transvection_of_ne i j hij c)⟩

private lemma slTransvection_mulVec {K : Type} [Field K] {d : ℕ} (i j : Fin d) (hij : i ≠ j)
    (c : K) (v : Fin d → K) :
    (((slTransvection i j hij c : ↥(StatedSL d K)) : Matrix.GeneralLinearGroup (Fin d) K) :
        Matrix (Fin d) (Fin d) K).mulVec v = v + Pi.single i (c * v j) := by
  have hcoe : (((slTransvection i j hij c : ↥(StatedSL d K)) :
      Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      Matrix.transvection i j c := rfl
  rw [hcoe, Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec]
  congr 1
  ext k
  simp only [Matrix.mulVec, dotProduct, Matrix.single_apply, Pi.single_apply]
  by_cases hk : i = k
  · subst hk; simp
  · simp [hk, Ne.symm hk]

private lemma single_mem_of_ne_of_statedSL_invariant {K : Type} [Field K] {d : ℕ}
    {W : Submodule K (Fin d → K)}
    (hW : ∀ g : GL (Fin d) K, g ∈ StatedSL d K →
      ∀ v : Fin d → K, v ∈ W → (g : Matrix (Fin d) (Fin d) K) *ᵥ v ∈ W)
    {w : Fin d → K} (hwW : w ∈ W) {j : Fin d} (hj : w j ≠ 0) :
    ∀ i, i ≠ j → ∀ a : K, Pi.single i a ∈ W := by
  intro i hij a
  have h1 := hW _ (slTransvection i j hij (a / w j)).2 w hwW
  have h2 : (((slTransvection i j hij (a / w j) : ↥(StatedSL d K)) :
      Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ w =
      w + Pi.single i ((a / w j) * w j) :=
    slTransvection_mulVec i j hij (a / w j) w
  rw [h2] at h1
  have h3 : Pi.single i ((a / w j) * w j) ∈ W := by
    simpa using W.sub_mem h1 hwW
  have h4 : (a / w j) * w j = a := div_mul_cancel₀ a hj
  rwa [h4] at h3

private lemma single_mem_at_of_statedSL_invariant {K : Type} [Field K] {d : ℕ}
    {W : Submodule K (Fin d → K)}
    (hW : ∀ g : GL (Fin d) K, g ∈ StatedSL d K →
      ∀ v : Fin d → K, v ∈ W → (g : Matrix (Fin d) (Fin d) K) *ᵥ v ∈ W)
    {j : Fin d} (hne : ∀ i, i ≠ j → ∀ a : K, Pi.single i a ∈ W) (i₀ : Fin d)
    (hi₀ : i₀ ≠ j) : ∀ a : K, Pi.single j a ∈ W := by
  intro a
  have hx0 : Pi.single i₀ (1 : K) ∈ W := hne i₀ hi₀ 1
  have h1 := hW _ (slTransvection j i₀ hi₀.symm a).2 _ hx0
  have h2 : (((slTransvection j i₀ hi₀.symm a : ↥(StatedSL d K)) :
      Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ
      Pi.single i₀ (1 : K) =
      Pi.single i₀ (1 : K) + Pi.single j (a * 1) := by
    simpa using slTransvection_mulVec j i₀ hi₀.symm a (Pi.single i₀ (1 : K))
  rw [h2] at h1
  have h3 : Pi.single j (a * 1) ∈ W := by
    simpa using W.sub_mem h1 hx0
  simpa using h3

private lemma submodule_eq_bot_or_top_of_statedSL_invariant {K : Type} [Field K] {d : ℕ}
    (hd : 2 ≤ d) (W : Submodule K (Fin d → K))
    (hW : ∀ g : GL (Fin d) K, g ∈ StatedSL d K →
      ∀ v : Fin d → K, v ∈ W → (g : Matrix (Fin d) (Fin d) K) *ᵥ v ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hw0 (funext hcon)
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin d, i₀ ≠ j := by
    by_cases hj0 : j = ⟨0, by omega⟩
    · exact ⟨⟨1, by omega⟩, by rw [hj0]; simp [Fin.ext_iff]⟩
    · exact ⟨⟨0, by omega⟩, fun h => hj0 h.symm⟩
  have hsingle := single_mem_of_ne_of_statedSL_invariant hW hwW hj
  have hsingle_j := single_mem_at_of_statedSL_invariant hW hsingle i₀ hi₀
  rw [Submodule.eq_top_iff']
  intro v
  rw [← Finset.univ_sum_single v]
  exact W.sum_mem fun i _ => by
    by_cases hij : i = j
    · subst hij; exact hsingle_j (v i)
    · exact hsingle i hij (v i)

private lemma naturalRep_isIrreducible {K : Type} [Field K] (d : ℕ) (hd : 2 ≤ d) :
    (naturalRep K d).IsIrreducible := by
  haveI : Nontrivial (Subrepresentation (naturalRep K d)) := by
    have hne : (⊥ : Submodule K (Fin d → K)) ≠ ⊤ := by
      intro htop
      have hmem : Pi.single ⟨0, by omega⟩ (1 : K) ∈ (⊥ : Submodule K (Fin d → K)) := by
        rw [htop]; trivial
      rw [Submodule.mem_bot] at hmem
      have h10 : (1 : K) = 0 := by simpa using congrFun hmem ⟨0, by omega⟩
      exact one_ne_zero h10
    exact ⟨⊥, ⊤, fun h => hne (by
      have := congrArg Subrepresentation.toSubmodule h
      rwa [Subrepresentation.toSubmodule_bot, Subrepresentation.toSubmodule_top] at this)⟩
  refine IsSimpleOrder.of_forall_eq_top (fun R hR => ?_)
  rcases submodule_eq_bot_or_top_of_statedSL_invariant hd R.toSubmodule (fun g hg v hv => by
      have h1 := R.apply_mem_toSubmodule (⟨g, hg⟩ : ↥(StatedSL d K)) hv
      rwa [naturalRep_apply] at h1) with h | h
  · exact absurd (Subrepresentation.toSubmodule_injective
      (h.trans Subrepresentation.toSubmodule_bot.symm)) hR
  · exact Subrepresentation.toSubmodule_injective (h.trans Subrepresentation.toSubmodule_top.symm)

theorem pCore_statedSL_eq_bot {K : Type} [Field K] [Finite K] (p : ℕ) [Fact p.Prime]
    [CharP K p] (d : ℕ) : CFSG.pCore p ↥(StatedSL d K) = ⊥ := by
  rcases Nat.lt_or_ge d 2 with hd | hd
  · have hle : d ≤ 1 := by omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with rfl | rfl
    · haveI : Subsingleton ↥(StatedSL 0 K) :=
        ⟨fun a b => Subtype.ext (Units.ext (funext fun i => Fin.elim0 i))⟩
      rw [Subgroup.eq_bot_iff_forall]
      intro x _
      exact Subsingleton.elim x 1
    · refine CFSG.LocalAnalysis.RankThreeUC.Section5.pCore_eq_bot_of_faithful_irreducible
        p (naturalRep K 1) (naturalRep_injective 1) ?_
      exact Representation.isIrreducible_of_finrank_eq_one (naturalRep K 1)
        (Module.finrank_fin_fun (R := K))
  · exact CFSG.LocalAnalysis.RankThreeUC.Section5.pCore_eq_bot_of_faithful_irreducible
      p (naturalRep K d) (naturalRep_injective d) (naturalRep_isIrreducible d hd)

end CFSG.LocalAnalysis.UniquenessCase.UC22.KOrdNat

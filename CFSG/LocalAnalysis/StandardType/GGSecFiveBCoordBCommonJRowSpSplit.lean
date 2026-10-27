module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJNativeConj
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRowSpSplitAux1
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRowSpSplitAux2
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRowSpSplitAux3
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRowSpSplitAux4
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRowSpSplitAux5
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRowSpSplitAux6
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflSp
import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.Open (StatedSp)

private lemma ggSpSplit_sparse {r p : ℕ} (f : Fin r → Multiplicative (ZMod p)) (hr : 1 ≤ r)
    (h : Nat.card {i : Fin r // f i = 1} = r - 1) : GGCoordSparse f := by
  classical
  let S : Finset (Fin r) := Finset.univ.filter (fun i => f i = 1)
  have hScard : S.card = r - 1 := by
    change (Finset.univ.filter (fun i => f i = 1)).card = r - 1
    rw [← h, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hcompl : (Finset.univ \ S).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hScard]
    omega
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcompl
  refine ⟨i, fun j hj => ?_⟩
  have hmem : j ∈ S := by
    by_contra hjs
    have hj' : j ∈ Finset.univ \ S := Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hjs⟩
    rw [hi] at hj'
    exact hj (by simpa using hj')
  exact (Finset.mem_filter.mp hmem).2

private lemma ggSpSplit_dense {r p : ℕ} {f : Fin r → Multiplicative (ZMod p)}
    {lam : Multiplicative (ZMod p)} (hlam : lam ≠ 1)
    (h : Nat.card {i : Fin r // f i = lam ∨ f i = lam⁻¹} = r) : GGCoordDense f := by
  classical
  have hfilter :
      (Finset.univ.filter (fun j : Fin r => f j = lam ∨ f j = lam⁻¹)).card = r := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, h]
  have hnot :
      (Finset.univ.filter (fun j : Fin r => ¬ (f j = lam ∨ f j = lam⁻¹))).card = 0 := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin r))) (fun j => f j = lam ∨ f j = lam⁻¹)
    rw [hfilter, Finset.card_univ, Fintype.card_fin] at hsplit
    omega
  have hall : ∀ i, f i = lam ∨ f i = lam⁻¹ := by
    intro i
    by_contra hi
    have hmem : i ∈ Finset.univ.filter (fun j : Fin r => ¬ (f j = lam ∨ f j = lam⁻¹)) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hi
    have hpos : 0 <
        (Finset.univ.filter (fun j : Fin r => ¬ (f j = lam ∨ f j = lam⁻¹))).card :=
      Finset.card_pos.mpr ⟨i, hmem⟩
    omega
  refine fun i => ⟨?_, ?_⟩
  · rcases hall i with hi | hi
    · rw [hi]; exact hlam
    · rw [hi]
      intro h1
      exact hlam (inv_eq_one.mp h1)
  · intro j
    rcases hall i with hi | hi <;> rcases hall j with hj | hj
    · rw [hi, hj]; exact Or.inl rfl
    · rw [hi, hj]; exact Or.inr rfl
    · rw [hi, hj]; exact Or.inr (by rw [inv_inv])
    · rw [hi, hj]; exact Or.inl rfl

theorem ggSecFiveBNativeRow_spSplit {K : Type} [Field K] [Finite K] {f p r : ℕ}
    (hK : Nat.card K = 2 ^ f) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f - 1) (hr : 3 ≤ r) :
    GGSecFiveBNativeRow (LargeEvenProj (LargeEvenSpGroup K r)) p r
      (fun lab => lab = ⟨.A, r - 1, f⟩) (fun lab => lab = ⟨.C, r - 1, f⟩) := by
  classical
  have hf2 : 2 ≤ f := by
    by_contra h
    have hf : f ≤ 1 := by omega
    interval_cases f
    · have h1 : 1 < Nat.card K := Finite.one_lt_card
      rw [hK] at h1
      simpa using h1
    · have h1 : p ∣ 1 := by simpa using hpq
      exact hp.ne_one (Nat.dvd_one.mp h1)
  haveI : CharP K 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hK
  have hpq' : p ∣ Nat.card K - 1 := by rw [hK]; exact hpq
  have hpK : (p : K) ≠ 0 := TableBSymp.natCast_ne_zero_of_charTwo hp hp2
  obtain ⟨ζ, hζo⟩ := ReflSp.exists_orderOf_eq (K := K) hp hpq'
  have hζ : ζ ^ p = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero r := ⟨by omega⟩
  let τ : (Fin r → Multiplicative (ZMod p)) →* StatedSp r K :=
    TableBSymp.spTorusSp (m := r) hζ
  have hτ : Function.Injective τ := TableBSymp.spTorusSp_injective (m := r) hζ hζo
  have hsign : ∀ g : StatedSp r K, (∀ s ∈ τ.range, g * s * g⁻¹ ∈ τ.range) →
      ∃ u : (Fin r → Multiplicative (ZMod p)) → (Fin r → Multiplicative (ZMod p)),
        SpCoord.IsSignedPerm u ∧ ∀ x, g * τ x * g⁻¹ = τ (u x) := by
    intro g hg
    exact ggCommonJSpSplit_signed hp hζ hζo g hg
  have hcomp : ∀ (x : Fin r → Multiplicative (ZMod p)) (J : Subgroup (StatedSp r K)),
      CFSG.Assembly.IsComponentOf J (Subgroup.centralizer ({τ x} : Set (StatedSp r K))) →
      Nat.card ↥(τ.range ⊓ Subgroup.centralizer (J : Set (StatedSp r K))) = p →
        (GGCoordDense x ∧ ∃ lab, lab = ⟨.A, r - 1, f⟩ ∧ LargeEvenInLambda2 lab ∧
            GGHasLabel lab (↥J ⧸ Subgroup.center ↥J) ∧
            (lab = ⟨.twA, 3, 1⟩ → Subgroup.center ↥J = ⊥)) ∨
          (GGCoordSparse x ∧ ∃ lab, lab = ⟨.C, r - 1, f⟩ ∧ LargeEvenInLambda2 lab ∧
            GGHasLabel lab (↥J ⧸ Subgroup.center ↥J)) := by
    intro x J hJ hcard
    obtain ⟨lam, hiso, hfix⟩ :=
      ggCommonJSpSplit_component_block hK hp hp2 hpq hr hζo hζ x hJ
    have hm : lam ≠ 1 → 1 ≤ Nat.card {i : Fin r // x i = lam ∨ x i = lam⁻¹} := by
      intro hne
      rcases hiso with ⟨h1, -⟩ | ⟨-, hge, -⟩
      · exact absurd h1 hne
      · exact hge
    have hcount := ggCommonJSpSplit_count hp hp2 hζ hζo x hfix hm
    rw [hcard] at hcount
    by_cases hlam : lam = 1
    ·
      have hm1 : Nat.card {i : Fin r // x i = 1} = r - 1 := by
        rw [if_pos hlam] at hcount
        have h1 : p ^ (r - Nat.card {i : Fin r // x i = 1}) = p ^ 1 := by
          simpa using hcount.symm
        have h2 : r - Nat.card {i : Fin r // x i = 1} = 1 :=
          Nat.pow_right_injective hp.two_le h1
        have h3 : Nat.card {i : Fin r // x i = 1} ≤ r := by
          simpa using Finite.card_subtype_le (fun i : Fin r => x i = 1)
        omega
      have hisoSp : Nonempty (↥J ≃* StatedSp (r - 1) K) := by
        rcases hiso with ⟨-, h⟩ | ⟨hne, -⟩
        · rwa [hm1] at h
        · exact absurd hlam hne
      have hsparse : GGCoordSparse x := ggSpSplit_sparse x (by omega) hm1
      have hlab := ggCommonJSpSplit_label_sp hK hr hisoSp
      have hLam : LargeEvenInLambda2 ⟨.C, r - 1, f⟩ := by
        simp only [LargeEvenInLambda2]
        omega
      exact Or.inr ⟨hsparse, ⟨⟨.C, r - 1, f⟩, rfl, hLam, hlab⟩⟩
    ·
      have hm2 : Nat.card {i : Fin r // x i = lam ∨ x i = lam⁻¹} = r := by
        rw [if_neg hlam] at hcount
        have h1 : p ^ (r - Nat.card {i : Fin r // x i = lam ∨ x i = lam⁻¹} + 1) = p ^ 1 := by
          simpa using hcount.symm
        have h2 : r - Nat.card {i : Fin r // x i = lam ∨ x i = lam⁻¹} + 1 = 1 :=
          Nat.pow_right_injective hp.two_le h1
        have h3 : Nat.card {i : Fin r // x i = lam ∨ x i = lam⁻¹} ≤ r := by
          simpa using Finite.card_subtype_le (fun i : Fin r => x i = lam ∨ x i = lam⁻¹)
        omega
      have hisoSL : Nonempty (↥J ≃* Matrix.SpecialLinearGroup (Fin r) K) := by
        rcases hiso with ⟨h1, -⟩ | ⟨-, -, h⟩
        · exact absurd h1 hlam
        · rwa [hm2] at h
      have hdense : GGCoordDense x := ggSpSplit_dense hlam hm2
      have hlab := ggCommonJSpSplit_label_lin hK hr hisoSL
      have hLam : LargeEvenInLambda2 ⟨.A, r - 1, f⟩ := by
        simp only [LargeEvenInLambda2]
        omega
      have htwA : (⟨.A, r - 1, f⟩ : LargeEvenLabel) = ⟨.twA, 3, 1⟩ →
          Subgroup.center ↥J = ⊥ := by
        intro h
        exact absurd (congrArg LargeEvenLabel.tag h) (fun htag => by cases htag)
      exact Or.inl ⟨hdense, ⟨⟨.A, r - 1, f⟩, rfl, hLam, hlab, htwA⟩⟩
  have hconj : ∀ T : Subgroup (StatedSp r K), IsElemAbelian p T → Nat.card T = p ^ r →
      ∃ α : StatedSp r K ≃* StatedSp r K, T = τ.range.map α.toMonoidHom := by
    intro T hT hTcard
    obtain ⟨P, hP⟩ := ggCommonJSpSplit_conj (r := r) hp hp2 hpK hζo hζ T hT hTcard
    exact ⟨MulAut.conj P, hP⟩
  have hAt : GGSecFiveBNativeAt (StatedSp r K) p r
      (fun lab => lab = ⟨.A, r - 1, f⟩) (fun lab => lab = ⟨.C, r - 1, f⟩) τ.range :=
    GGSecFiveBNativeAt.of_torus (SD := fun lab => lab = ⟨.A, r - 1, f⟩)
      (SS := fun lab => lab = ⟨.C, r - 1, f⟩) τ hτ hsign hcomp
  have hRow : GGSecFiveBNativeRow (StatedSp r K) p r
      (fun lab => lab = ⟨.A, r - 1, f⟩) (fun lab => lab = ⟨.C, r - 1, f⟩) :=
    GGSecFiveBNativeRow.of_std (SD := fun lab => lab = ⟨.A, r - 1, f⟩)
      (SS := fun lab => lab = ⟨.C, r - 1, f⟩) (T₀ := τ.range) hAt hconj
  exact GGSecFiveBNativeRow.of_mulEquiv (SD := fun lab => lab = ⟨.A, r - 1, f⟩)
    (SS := fun lab => lab = ⟨.C, r - 1, f⟩)
    (TableBSymp.spProjEquivSp (K := K) (m := r)).symm hRow

end CFSG.StandardType

end

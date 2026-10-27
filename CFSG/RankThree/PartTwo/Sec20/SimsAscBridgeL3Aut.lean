module

public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411Skeleton
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411Outer
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411L3
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411L3Group
import CFSG.RankThree.PartTwo.Sec20.Item20Res7ProofL3Aut

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Subgroup
open scoped MatrixGroups

section Model

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {n : ℕ}

theorem mul_inner_of_not_inner_projectiveSL3 (hn : Odd n)
    {β γ : MulAut (projectiveSL 3 (GaloisField 2 n))} (hβ : β * β = 1) (hγ : γ * γ = 1)
    (hβi : ∀ g, β ≠ MulAut.conj g) (hγi : ∀ g, γ ≠ MulAut.conj g) :
    ∃ g, β * γ = MulAut.conj g := by
  set F := GaloisField 2 n
  have htrans := standard_automorphism_transport (K := F) (n := 3)
  obtain ⟨A, rfl⟩ := exists_conjAut_mul_dualAut hn β hβ hβi
  obtain ⟨B, rfl⟩ := exists_conjAut_mul_dualAut hn γ hγ hγi
  have h : conjAut 3 F A * dualAut 3 F * (conjAut 3 F B * dualAut 3 F) =
      conjAut 3 F (A * GeneralLinearGroup.inverseTranspose B) := by
    rw [← htrans.1, ← htrans.2.2.2.2.1]
    group
  rw [h]
  exact Res7.exists_conj_eq_conjAut_of_cube _ (Res7.exists_cube_galoisField hn)

end Model

theorem mul_inner_of_not_inner_L3 {H : Type*} [Group H] {n : ℕ} (hn : Odd n)
    (e : H ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 n)) {β γ : MulAut H}
    (hβ : β * β = 1) (hγ : γ * γ = 1) (hβi : ∀ g, β ≠ MulAut.conj g)
    (hγi : ∀ g, γ ≠ MulAut.conj g) : ∃ g, β * γ = MulAut.conj g := by
  set f := e.trans (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 n)) with hf
  have hinner : ∀ δ : MulAut H, (∀ g, δ ≠ MulAut.conj g) →
      ∀ g, MulAut.congr f δ ≠ MulAut.conj g := by
    intro δ hδ g hg
    refine hδ (f.symm g) (MulEquiv.ext fun x => f.injective ?_)
    have := congrArg (fun α => α (f x)) hg
    simpa [MulAut.congr_apply] using this
  obtain ⟨g, hg⟩ := mul_inner_of_not_inner_projectiveSL3 hn
    (by rw [← map_mul, hβ, map_one]) (by rw [← map_mul, hγ, map_one]) (hinner β hβi)
    (hinner γ hγi)
  refine ⟨f.symm g, MulEquiv.ext fun x => f.injective ?_⟩
  have := congrArg (fun α => α (f x)) hg
  simpa [MulAut.congr_apply] using this

variable {X : Type} [Group X] [Finite X] {L S : Subgroup X}

theorem relIndex_pCore_le_two_of_L3 (h : Hyp1411 X L S) {n : ℕ} (hn : Odd n)
    (hL : Nonempty (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ≃*
        CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 n)))
    (hSL : S.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ⊓
      L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) = ⊥) :
    ∀ A : Subgroup X, A ≤ S → Sec3.IsElemTwo A → (CFSG.pCore 2 X).relIndex A ≤ 2 := by
  intro A hAS hA
  obtain ⟨e⟩ := hL
  set K := CFSG.pPrimeCore 3 X with hKdef
  set π := QuotientGroup.mk' K with hπ
  have : (L.map π).Normal := h.2.1.map π (QuotientGroup.mk'_surjective _)
  have hinv : ∀ t ∈ A, MulAut.conjNormal (π t) * MulAut.conjNormal (π t) =
      (1 : MulAut ↥(L.map π)) := by
    intro t ht
    rw [← map_mul, ← map_mul, hA.2 t ht, map_one, map_one]
  have hni : ∀ t ∈ A, t ∉ CFSG.pCore 2 X →
      ∀ g, (MulAut.conjNormal (π t) : MulAut ↥(L.map π)) ≠ MulAut.conj g := by
    intro t ht htQ g hg
    obtain ⟨y, hyL, hy⟩ := not_inner_of_inf_eq_bot_of_hyp1411 h hSL (hAS ht) htQ
      (g : X ⧸ K) g.2
    apply hy
    have := congrArg Subtype.val (DFunLike.congr_fun hg ⟨y, hyL⟩)
    simpa [hπ, MulAut.conjNormal_apply] using this
  have hprod : ∀ s ∈ A, ∀ t ∈ A, s ∉ CFSG.pCore 2 X → t ∉ CFSG.pCore 2 X →
      s * t ∈ CFSG.pCore 2 X := by
    intro s hs t ht hsQ htQ
    by_contra hstQ
    obtain ⟨g, hg⟩ := mul_inner_of_not_inner_L3 hn e (hinv s hs) (hinv t ht) (hni s hs hsQ)
      (hni t ht htQ)
    rw [← map_mul, ← map_mul] at hg
    exact hni (s * t) (A.mul_mem hs ht) hstQ g hg
  by_cases hsome : ∃ s ∈ A, s ∉ CFSG.pCore 2 X
  · obtain ⟨s, hsA, hsQ⟩ := hsome
    refine (Subgroup.relIndex_eq_two_iff_exists_notMem_and'.mpr
      ⟨s, hsA, hsQ, fun b hb => ?_⟩).le
    by_cases hbQ : b ∈ CFSG.pCore 2 X
    · exact Or.inr hbQ
    · exact Or.inl (hprod s hsA b hb hsQ hbQ)
  · push Not at hsome
    rw [Subgroup.relIndex_eq_one.mpr hsome]
    norm_num

theorem asc82Item1411_L3odd (X : Type) [Group X] [Finite X] (L S : Subgroup X)
    (h : Hyp1411 X L S) {n : ℕ} (hn : Odd n)
    (hL : Nonempty (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ≃*
        Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n)) ∨
      Nonempty (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ≃*
        CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 n)))
    (hSL : S.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ⊓
      L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) = ⊥) :
    ∃ i₁ i₂ : Fin 4, i₁ ≠ i₂ ∧ i₁ ≠ 3 ∧ i₂ ≠ 3 ∧ (Sec18.fourChar S i₁).Normal ∧
      (Sec18.fourChar S i₂).Normal := by
  have hL' : Nonempty (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ≃*
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 n)) := by
    rcases hL with he | he
    · obtain ⟨e⟩ := he
      exact ⟨e.trans (slThreeEquivProjSL hn)⟩
    · exact he
  exact asc82Item1411_of_noSmall h (relIndex_pCore_le_two_of_L3 h hn hL' hSL)
    (noSmall1411_of_L3graph h hn hL' hSL)

end CFSG.RankThree.PartTwo.Sec20

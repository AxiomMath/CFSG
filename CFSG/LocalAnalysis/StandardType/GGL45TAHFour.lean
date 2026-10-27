module

public import CFSG.LocalAnalysis.StandardType.GGL45NtAssembly
public import CFSG.LocalAnalysis.StandardType.GGL45NtAutAsm
public import CFSG.LocalAnalysis.StandardType.GGL45FamCover
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldCyclicLabels
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldLinear
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneOutdiagLinear
public import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOtherUnitary
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GLinMat
public import CFSG.ClassicalGroups.Unitary.Simple

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggL45NtAut_of_inputs {p : ℕ} (hp : p.Prime) {R : Type} [Group R] {I F : Set (MulAut R)}
    (hIF : GGRawInnField p R I F)
    (hID : LargeEvenSimpleGuard (fun R _ I _ => GGInndiagNormal R I) R I F)
    (hCyc : GGRawPCyclic p R I F) : GGL45NtAut p R I F := by
  intro hs hna
  obtain ⟨-, -, hinn, hFnotI⟩ := hIF hs hna
  obtain ⟨J, S, hJcoe, -, hJnorm, hgen, hpS⟩ := hCyc hs hna
  have hJ : J.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hle : ggInndiag R I ≤ J := by
      refine sup_le ?_ ((Subgroup.closure_le J).mpr fun x hx => ?_)
      · rintro _ ⟨r, rfl⟩
        change MulAut.conj r ∈ (J : Set (MulAut R))
        rw [hJcoe]
        exact hinn r
      · change x ∈ (J : Set (MulAut R))
        rwa [hJcoe]
    have hnI : n ∈ I := by rw [← hJcoe]; exact hn
    exact hle (hID hs hna g n hnI)
  refine ⟨⟨J, hJ, hJcoe⟩, fun α hαP hαI hαp f hfF hford => ?_⟩
  haveI : (J.subgroupOf S).Normal := hJnorm
  haveI : IsCyclic (S ⧸ J.subgroupOf S) := ggL45NtAutAsm_isCyclic_quotient hJnorm hgen
  have hmk : ∀ x : S, (QuotientGroup.mk x : S ⧸ J.subgroupOf S) = 1 ↔ (x : MulAut R) ∈ I := by
    intro x
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, ← hJcoe]
    rfl
  have hfp : f ^ p = 1 := by rw [← hford]; exact pow_orderOf_eq_one f
  have hαS : α ∈ S := hpS α hαP
  have hfS : f ∈ S := hpS f ⟨1, by simpa using hfp⟩
  obtain ⟨j, hj, hjeq⟩ := ggL45NtAutAsm_exists_pow_of_cyclic hp
    (a := (QuotientGroup.mk ⟨α, hαS⟩ : S ⧸ J.subgroupOf S))
    (b := (QuotientGroup.mk ⟨f, hfS⟩ : S ⧸ J.subgroupOf S))
    (by rw [← QuotientGroup.mk_pow, hmk]; simpa using hαp)
    (by
      rw [← QuotientGroup.mk_pow, hmk]
      have h1 : (1 : MulAut R) ∈ I := by rw [← hJcoe]; exact J.one_mem
      simpa [hfp] using h1)
    (by rw [Ne, hmk]; exact hαI)
    (by rw [Ne, hmk]; exact hFnotI f hfF hford)
  refine ⟨j, hj, ?_⟩
  have h := (hmk (⟨α, hαS⟩ * (⟨f, hfS⟩ ^ j)⁻¹)).1 (by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow, hjeq, mul_inv_cancel])
  simpa using h

theorem ggL45FamTypeA_three_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (h : GGL45FamTypeA p lab) : 3 ≤ lab.rank + 1 := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  exact hp3.trans (Nat.le_of_dvd (Nat.succ_pos _) h.2)

theorem ggL45NtSimpOn_famTypeA : GGL45NtSimpOn GGL45FamTypeA := by
  rintro p hp hp2 ⟨tag, rank, n⟩ hlab - hS Q hQ
  have hd : 3 ≤ rank + 1 := ggL45FamTypeA_three_le hp hp2 hS
  rcases hS.1 with ht | ht <;> dsimp only at ht hd <;> subst ht <;>
    dsimp only [LargeEvenRawDatum] at hQ ⊢
  · exact NbrGraphLinear.recipeLinear_all (fun K _ _ _ _ =>
      CFSG.LocalAnalysis.GLTheoremA.T156.Lin.isSimpleGroup_proj' (d := rank + 1) (by omega) K
        (Or.inl hd)) hQ
  · obtain ⟨-, -, hl2n⟩ := hlab
    dsimp only at hl2n
    have hdq : (rank + 1, 2 ^ n) ≠ (3, 2) := by
      intro h
      obtain ⟨h1, h2⟩ := Prod.mk.inj h
      have hn : 2 ≤ n := hl2n (by omega)
      have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      omega
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact recipeUnitary_and (fun K _ _ hK _ =>
      CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 n hK (rank + 1) hd hdq) hQ

theorem ggL45NtAutOn_famTypeA : GGL45NtAutOn GGL45FamTypeA := by
  intro p hp hp2 lab hlab _ hS
  have hIF : LargeEvenLabelAll lab (GGRawInnField p) :=
    hS.1.elim (fun h => ggRawInnFieldOn_linear p hp hp2 lab hlab (Or.inl h))
      (fun h => ggRawInnFieldOn_unitary p hp hp2 lab hlab (Or.inl h))
  have hID : LargeEvenLabelAll lab
      (LargeEvenSimpleGuard fun R _ I _ => GGInndiagNormal R I) :=
    hS.1.elim (fun h => largeEvenLabelAll_inndiag_proved hlab (Or.inr (Or.inl h)))
      (fun h => largeEvenLabelAll_inndiag_unitary hlab (Or.inl h))
  have hCyc : LargeEvenLabelAll lab (GGRawPCyclic p) :=
    hS.1.elim (fun h => ggRawPCyclicOn_linear p hp hp2 lab hlab (Or.inl h))
      (fun h => ggRawPCyclicOn_unitary p hp hp2 lab hlab (Or.inl h))
  exact (largeEvenLabelAll_and hIF (largeEvenLabelAll_and hID hCyc)).mono
    fun _ _ _ _ h => ggL45NtAut_of_inputs hp h.1 h.2.1 h.2.2

theorem ggL45NtH4On_famTypeA : GGL45NtH4On GGL45FamTypeA :=
  ggL45NtH4On_of_aut ggL45NtSimpOn_famTypeA ggL45NtAutOn_famTypeA

end CFSG.StandardType

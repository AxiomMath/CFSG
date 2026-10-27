module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1Holds
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2OffRows
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2Rows
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2Toral
import CFSG.LocalAnalysis.StandardType.GGPGLTorality
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
import CFSG.LocalAnalysis.StandardType.GGTableBExcTorus
import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Three
import CFSG.LocalAnalysis.StandardType.GGResLeaf
import CFSG.LocalAnalysis.StandardType.GGTableBRank

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private theorem q2li_comap_comm_of_diag {d : ℕ} {K : Type} [Field K]
    {E : Subgroup (MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K)))}
    {A₀ : GL (Fin d) K}
    (hA₀ : ∀ A : GL (Fin d) K,
      conjAut d K A ∈ E.map (MulAut.congr (TypeA.recipeEquiv d K)).toMonoidHom →
      ∀ i j, i ≠ j →
        ((A₀ : Matrix (Fin d) (Fin d) K) * (A : Matrix (Fin d) (Fin d) K) *
          ((A₀⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) i j = 0) :
    IsMulCommutative (E.comap (TableB.linConjAut (Fin d) K)) := by
  refine ⟨⟨fun a b => ?_⟩⟩
  apply Subtype.ext
  have hmem : ∀ c : E.comap (TableB.linConjAut (Fin d) K),
      conjAut d K (c : GL (Fin d) K) ∈
        E.map (MulAut.congr (TypeA.recipeEquiv d K)).toMonoidHom := by
    intro c
    rw [← q1CentLin_congr_linConjAut (c : GL (Fin d) K)]
    exact Subgroup.mem_map_of_mem _ c.2
  set D : GL (Fin d) K := A₀ * (a : GL (Fin d) K) * A₀⁻¹ with hD
  set D' : GL (Fin d) K := A₀ * (b : GL (Fin d) K) * A₀⁻¹ with hD'
  have hDdiag : (D : Matrix (Fin d) (Fin d) K) =
      Matrix.diagonal (fun i => (D : Matrix (Fin d) (Fin d) K) i i) :=
    CFSG.RankThree.CALinearPlane.eq_diagonal_of_offDiag (fun i j hij => by
      rw [hD, Units.val_mul, Units.val_mul]
      exact hA₀ _ (hmem a) i j hij)
  have hD'diag : (D' : Matrix (Fin d) (Fin d) K) =
      Matrix.diagonal (fun i => (D' : Matrix (Fin d) (Fin d) K) i i) :=
    CFSG.RankThree.CALinearPlane.eq_diagonal_of_offDiag (fun i j hij => by
      rw [hD', Units.val_mul, Units.val_mul]
      exact hA₀ _ (hmem b) i j hij)
  have hcomm : D * D' = D' * D := by
    apply Units.ext
    change (D : Matrix (Fin d) (Fin d) K) * (D' : Matrix (Fin d) (Fin d) K) =
      (D' : Matrix (Fin d) (Fin d) K) * (D : Matrix (Fin d) (Fin d) K)
    rw [hDdiag, hD'diag, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  calc (a : GL (Fin d) K) * (b : GL (Fin d) K)
      = A₀⁻¹ * (A₀ * (a : GL (Fin d) K) * A₀⁻¹ *
          (A₀ * (b : GL (Fin d) K) * A₀⁻¹)) * A₀ := by group
    _ = A₀⁻¹ * (A₀ * (b : GL (Fin d) K) * A₀⁻¹ *
          (A₀ * (a : GL (Fin d) K) * A₀⁻¹)) * A₀ := by
        rw [← hD, ← hD']
        exact congrArg (fun x => A₀⁻¹ * x * A₀) hcomm
    _ = (b : GL (Fin d) K) * (a : GL (Fin d) K) := by group

private theorem q2li_two_le_n {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (hpq : p ∣ 2 ^ n - 1) :
    2 ≤ n := by
  by_contra h
  have hn1 : n = 1 := by omega
  subst hn1
  exact hp.not_dvd_one (by simpa using hpq)

section Rows


theorem q2_comm_of_large_gamma {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hInner : GGInnerDiagOn Bs L)
    (hN : Bs ≤ Subgroup.normalizer (J : Set G)) {d : ℕ} (hd : 3 ≤ d)
    {K : Type} [Field K] [Finite K]
    (θ : ↥J ⧸ Subgroup.center ↥J ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) K))
    (hp2 : p ≠ 2) {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) (hpK : p ∣ Nat.card K - 1)
    (hcard : p ^ (d - 2) ≤ Nat.card (ggGamma J hN).range)
    (hcard3 : p ^ 3 ≤ Nat.card (ggGamma J hN).range) :
    IsMulCommutative
      ((((ggBsAut hN).range).map (kgInducedAut θ)).comap (TableB.linConjAut (Fin d) K)) := by
  classical
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hBs : IsElemAbelian p Bs := hcfg.2.1.2.1
  have hQ1 : GGInnerDiagOn Bs J := ggBstarInnerDiagJInput_holds G p B Bs x L D J hcfg hInner
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  have hΛ : LargeEvenInLambda2 ⟨.A, d', n⟩ :=
    ⟨show 1 ≤ n by omega, show 1 ≤ d' by omega, fun _ => show 2 ≤ n by omega⟩
  have hhas : GGHasLabel ⟨.A, d', n⟩ (↥J ⧸ Subgroup.center ↥J) := by
    unfold GGHasLabel
    dsimp only [CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeLinear]
    exact ⟨K, inferInstance, inferInstance, hK, ⟨θ⟩⟩
  obtain ⟨hJperf, lab', -, hraw⟩ := ggInnerDiagOn_relabel ggLabelRigidInput_holds hQ1 hΛ hhas
  obtain ⟨_, _, _, _, _, _, _, hlab', _⟩ := largeEvenRawDatum_exists hraw
  subst hlab'
  obtain ⟨F, _, _, hF, -, -, θJ, -, -, hact⟩ := hraw
  have hpF : p ∣ Nat.card F - 1 := by
    rw [show Nat.card F = Nat.card K from hF.trans hK.symm]
    exact hpK
  set E : Subgroup (MulAut (LargeEvenProj (LargeEvenSLGroup (Fin (d' + 1)) F))) :=
    (ggGamma J hN).range.map (ggInducedAut θJ) with hEdef
  have hE : IsElemAbelian p E := by
    rw [hEdef]
    exact (ggBsAut_range_isElemAbelian hBs hN).map (ggInducedAut θJ)
  have hcardE : Nat.card E = Nat.card (ggGamma J hN).range := by
    rw [hEdef]
    exact Subgroup.card_map_of_injective (ggInducedAut_injective_of_perfect hJperf θJ)
  have hIE : ∀ b : Bs, ggInducedAut θJ (ggGamma J hN b) ∈
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin (d' + 1)) F)) Set.univ := by
    intro b
    have h := ggLAut_mem_of_induces (L := J) (θ := θJ) hN hact b.2
    have h2 : ggInducedAut θJ (ggGamma J hN b) = ggLAut J θJ ⟨b, hN b.2⟩ := by
      rw [ggLAut_eq_ggInducedAut, ggGamma]
      congr 1
    rw [h2]
    exact h
  set X : Subgroup (MulAut (projectiveSL (d' + 1) F)) :=
    E.map (MulAut.congr (TypeA.recipeEquiv (d' + 1) F)).toMonoidHom with hXdef
  have hXelem : IsElemAbelian p X := by
    rw [hXdef]
    exact hE.map (MulAut.congr (TypeA.recipeEquiv (d' + 1) F)).toMonoidHom
  have hXsub : (X : Set (MulAut (projectiveSL (d' + 1) F))) ⊆
      Set.range (conjAut (d' + 1) F) := by
    rintro _ ⟨ψ, hψE, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hψE
    obtain ⟨b, rfl⟩ := hy
    exact TypeA.congr_recipeEquiv_mem (hIE b)
  have hcardX : Nat.card X = Nat.card E := by
    rw [hXdef]
    exact Subgroup.card_map_of_injective (MulAut.congr (TypeA.recipeEquiv (d' + 1) F)).injective
  obtain ⟨A₀, hA₀⟩ := TypeA.ggPGLTorality_holds (d := d' + 1) hp hp2 hpF X hXelem hXsub
    (by rw [hcardX, hcardE]; exact hcard) (by rw [hcardX, hcardE]; exact hcard3)
  have hcommE : IsMulCommutative (E.comap (TableB.linConjAut (Fin (d' + 1)) F)) :=
    q2li_comap_comm_of_diag hA₀
  have hLift : Q2LinearLift ((ggBsAut hN).range.map (centerQuotAut ↥J)) := by
    refine ⟨d' + 1, F, inferInstance, inferInstance, θJ,
      E.comap (TableB.linConjAut (Fin (d' + 1)) F), hcommE, ?_⟩
    rintro α ⟨a, ⟨b, rfl⟩, rfl⟩
    obtain ⟨A, hA⟩ := TableB.exists_eq_linConjAut (hIE b)
    refine ⟨A, ?_, hA⟩
    show TableB.linConjAut (Fin (d' + 1)) F A ∈ E
    rw [← hA, hEdef]
    exact Subgroup.mem_map_of_mem _ (MonoidHom.mem_range.mpr ⟨b, rfl⟩)
  have hcomm := q2_commutative_of_linearLift hLift (d := d' + 1) hd hn hK θ
  have hMeq : ((ggBsAut hN).range.map (centerQuotAut ↥J)).map (MulAut.congr θ).toMonoidHom =
      (ggBsAut hN).range.map (kgInducedAut θ) := by
    rw [Subgroup.map_map]
    rfl
  rwa [hMeq] at hcomm

theorem q2RowSolver_e7Seven_holds : Q2RowSolverInput .e7Seven := by
  intro G _ _ p B Bs x L D J hcfg hInner hN d K _ _ θ hpd hpq hlab
  obtain ⟨hLperf, ⟨tag, rank, n⟩, hΛ, hraw⟩ := hlab
  obtain ⟨_, _, _, _, _, _, _, hfits, _⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨hp, hp2, -, -, htag, rfl, rfl, hQ⟩ := hfits
  have htag' : tag = .E7 := htag
  subst htag'
  have hQ' : Nat.card K = 2 ^ n := hQ
  have hn : 2 ≤ n := q2li_two_le_n (n := n) hp hΛ.1 (by rw [← hQ']; exact hpq)
  obtain ⟨KL, _, _, hKL, -, -, θL, -⟩ := hraw
  haveI : CharP KL 2 := charP_two_of_card hKL
  have hpKL : 7 ∣ Nat.card KL - 1 := by
    rw [show Nat.card KL = Nat.card K from hKL.trans hQ'.symm]
    exact hpq
  have hS : LargeEvenSStar 7 B x L := hcfg.1.2.2.2.2.2.2.1
  have hm := succ_le_twoLocalRank_of_torusLift hp hS.2.2.2.1.1 (hS.1.1.2 x hS.2.1) hS.2.2.1
    hLperf θL (TableBExc.ggTorusLift_E7 (K := KL) hp hp2 hpKL)
  have hc := hcfg.pow_le_card_gamma_J hN
  exact q2_comm_of_large_gamma hcfg hInner hN (by norm_num) θ hp2 hn hQ' hpq
    ((Nat.pow_le_pow_right hp.pos (by omega)).trans hc)
    ((Nat.pow_le_pow_right hp.pos (by omega)).trans hc)

theorem q2RowSolver_e8Three_holds : Q2RowSolverInput .e8Three := by
  intro G _ _ p B Bs x L D J hcfg hInner hN d K _ _ θ hpd hpq hlab
  obtain ⟨hLperf, ⟨tag, rank, n⟩, hΛ, hraw⟩ := hlab
  obtain ⟨_, _, _, _, _, _, _, hfits, _⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨hp, hp2, -, -, htag, rfl, rfl, hQ⟩ := hfits
  have htag' : tag = .E8 := htag
  subst htag'
  have hQ' : Nat.card K = 2 ^ n := hQ
  have hn : 2 ≤ n := q2li_two_le_n (n := n) hp hΛ.1 (by rw [← hQ']; exact hpq)
  obtain ⟨KL, _, _, hKL, -, -, θL, -⟩ := hraw
  haveI : CharP KL 2 := charP_two_of_card hKL
  have hpKL : 3 ∣ Nat.card KL - 1 := by
    rw [show Nat.card KL = Nat.card K from hKL.trans hQ'.symm]
    exact hpq
  have hS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hm := succ_le_twoLocalRank_of_torusLift hp hS.2.2.2.1.1 (hS.1.1.2 x hS.2.1) hS.2.2.1
    hLperf θL (TableBExc.ggTorusLift_E8 (K := KL) hp hp2 hpKL)
  have hc := hcfg.pow_le_card_gamma_J hN
  exact q2_comm_of_large_gamma hcfg hInner hN (by norm_num) θ hp2 hn hQ' hpq
    ((Nat.pow_le_pow_right hp.pos (by omega)).trans hc)
    ((Nat.pow_le_pow_right hp.pos (by omega)).trans hc)

theorem q2RowSolver_e6Three_holds : Q2RowSolverInput .e6Three := by
  intro G _ _ p B Bs x L D J hcfg hInner hN d K _ _ θ hpd hpq hlab
  obtain ⟨hLperf, ⟨tag, rank, n⟩, hΛ, hraw⟩ := hlab
  obtain ⟨_, _, _, _, _, _, _, hfits, _⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨hp, hp2, -, -, htag, rfl, rfl, hQ⟩ := hfits
  have htag' : tag = .E6 := htag
  subst htag'
  have hQ' : Nat.card K = 2 ^ n := hQ
  have hn : 2 ≤ n := q2li_two_le_n (n := n) hp hΛ.1 (by rw [← hQ']; exact hpq)
  obtain ⟨KL, _, _, hKL, -, -, θL, -⟩ := hraw
  haveI : CharP KL 2 := charP_two_of_card hKL
  have hpKL : 3 ∣ Nat.card KL - 1 := by
    rw [show Nat.card KL = Nat.card K from hKL.trans hQ'.symm]
    exact hpq
  have hS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hm := succ_le_twoLocalRank_of_torusLift hp hS.2.2.2.1.1 (hS.1.1.2 x hS.2.1) hS.2.2.1
    hLperf θL (TableBExc.ggTorusLift_E6_three (K := KL) hpKL)
  have hc := hcfg.pow_le_card_gamma_J hN
  exact q2_comm_of_large_gamma hcfg hInner hN (by norm_num) θ hp2 hn hQ' hpq
    ((Nat.pow_le_pow_right hp.pos (by omega)).trans hc)
    ((Nat.pow_le_pow_right hp.pos (by omega)).trans hc)

theorem ggBstarAbelianPreimageJLinResOffRowsInput_of_offExc
    (h : GGBstarAbelianPreimageJLinResOffRowsInput fun kind =>
      kind = .orthogonalPlus ∨ kind = .linear ∨ kind = .fieldTwo ∨
        kind = .e6Three ∨ kind = .e7Seven ∨ kind = .e8Three) :
    GGBstarAbelianPreimageJLinResOffRowsInput fun kind =>
      kind = .orthogonalPlus ∨ kind = .linear ∨ kind = .fieldTwo := by
  refine ggBstarAbelianPreimageJLinResOffRowsInput_of_rows (fun kind hT hS => ?_) h
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd (Or.inl rfl) hS
  · exact absurd (Or.inr (Or.inl rfl)) hS
  · exact absurd (Or.inr (Or.inr rfl)) hS
  · exact q2RowSolver_e6Three_holds
  · exact q2RowSolver_e7Seven_holds
  · exact q2RowSolver_e8Three_holds

end Rows

end CFSG.StandardType

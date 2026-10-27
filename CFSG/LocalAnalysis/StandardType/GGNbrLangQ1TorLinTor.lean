module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1RLevel
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TorLinDefs
public import CFSG.LocalAnalysis.StandardType.GGPGLTorality
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATorus
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeACover
public import CFSG.LocalAnalysis.StandardType.GGTableBRank
import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.S2MathAs51642Interfaces
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private theorem l02qt6_congr_recipeEquiv_linConjAut {N : ℕ} {K : Type} [Field K]
    (A : GL (Fin N) K) :
    MulAut.congr (TypeA.recipeEquiv N K) (TableB.linConjAut (Fin N) K A) =
      conjAut N K A := by
  ext x
  obtain ⟨g, rfl⟩ := proj_surjective N K x
  set h : ↥(LargeEvenSLGroup (Fin N) K) := (TypeA.slKerEquiv N K).symm g with hh
  have h1 : (TypeA.slKerEquiv N K) h = g := by
    rw [hh, MulEquiv.apply_symm_apply]
  have hx : TypeA.recipeEquiv N K (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) h) =
      proj N K g := by
    rw [TypeA.recipeEquiv_mk, h1]
  have hsymm : (TypeA.recipeEquiv N K).symm (proj N K g) =
      LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) h := by
    rw [MulEquiv.symm_apply_eq]
    exact hx.symm
  have hlin : (TableB.linConjAut (Fin N) K A)
      (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) h) =
      LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) (MulAut.conjNormal A h) := by
    change (TableB.linConjAut (Fin N) K A)
        (h : LargeEvenProj (LargeEvenSLGroup (Fin N) K)) =
      (MulAut.conjNormal A h : LargeEvenProj (LargeEvenSLGroup (Fin N) K))
    exact TableB.linConjAut_mk A h
  rw [MulAut.congr_apply, MulEquiv.trans_apply, hsymm, MulEquiv.trans_apply, hlin,
    TypeA.recipeEquiv_mk, conjAut_proj]
  apply congrArg (proj N K)
  apply Matrix.SpecialLinearGroup.toGL_injective
  have htoGL : Matrix.SpecialLinearGroup.toGL
      ((TypeA.slKerEquiv N K) (MulAut.conjNormal A h)) =
      (MulAut.conjNormal A h : GL (Fin N) K) := by
    apply Units.ext
    exact TypeA.coe_slKerEquiv (MulAut.conjNormal A h)
  have hg : Matrix.SpecialLinearGroup.toGL g = (h : GL (Fin N) K) := by
    rw [← h1]
    rfl
  rw [htoGL, CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation,
    hg, MulAut.conjNormal_apply]

private theorem l02qt6_ggBeta_eq_ggInducedAut_gamma {G : Type} [Group G] {L B Bs : Subgroup G}
    {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
    (hBBs : B ≤ Bs) (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (b : B) :
    ggBeta L θ hBN b = ggInducedAut θ (ggGamma L hN ⟨b, hBBs b.2⟩) := by
  rw [ggBeta_eq, ggLAut_eq_ggInducedAut]
  congr 1

private theorem l02qt6_comap_comm_of_diag {d : ℕ} {K : Type} [Field K]
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
  have hda : conjAut d K (a : GL (Fin d) K) ∈
      E.map (MulAut.congr (TypeA.recipeEquiv d K)).toMonoidHom := by
    rw [← l02qt6_congr_recipeEquiv_linConjAut (a : GL (Fin d) K)]
    exact Subgroup.mem_map_of_mem _ a.2
  have hdb : conjAut d K (b : GL (Fin d) K) ∈
      E.map (MulAut.congr (TypeA.recipeEquiv d K)).toMonoidHom := by
    rw [← l02qt6_congr_recipeEquiv_linConjAut (b : GL (Fin d) K)]
    exact Subgroup.mem_map_of_mem _ b.2
  set D : GL (Fin d) K := A₀ * (a : GL (Fin d) K) * A₀⁻¹ with hD
  set D' : GL (Fin d) K := A₀ * (b : GL (Fin d) K) * A₀⁻¹ with hD'
  have hDdiag : (D : Matrix (Fin d) (Fin d) K) =
      Matrix.diagonal (fun i => (D : Matrix (Fin d) (Fin d) K) i i) :=
    CFSG.RankThree.CALinearPlane.eq_diagonal_of_offDiag (fun i j hij => by
      rw [hD, Units.val_mul, Units.val_mul]
      exact hA₀ _ hda i j hij)
  have hD'diag : (D' : Matrix (Fin d) (Fin d) K) =
      Matrix.diagonal (fun i => (D' : Matrix (Fin d) (Fin d) K) i i) :=
    CFSG.RankThree.CALinearPlane.eq_diagonal_of_offDiag (fun i j hij => by
      rw [hD', Units.val_mul, Units.val_mul]
      exact hA₀ _ hdb i j hij)
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

theorem q1TorLin_config :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
      GGConfig p B Bs x L D J →
      GGMarkingAll (K := ↥L) (fun lab R _ I _ θ =>
        LinearTorsion p lab → ∀ hN : Bs ≤ Subgroup.normalizer (L : Set G),
          (∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) →
          ToralLin R ((ggGamma L hN).range.map (ggInducedAut θ))) := by
  intro G _ _ p B Bs x L D J hcfg
  unfold GGMarkingAll
  intro P hP
  obtain ⟨hperf, lab, hlab, hraw⟩ := hP
  refine ⟨hperf, lab, hlab, ?_⟩
  obtain ⟨tag, rank, n⟩ := lab
  by_cases hTor : LinearTorsion p ⟨tag, rank, n⟩
  · obtain ⟨htagA, hpdvd0⟩ := hTor
    subst htagA
    unfold LargeEvenRawDatumLegacy LargeEvenRecipeLinear at hraw
    obtain ⟨K, _, _, hKcard, hs, hna, θ, hPθ⟩ := hraw
    unfold LargeEvenRawDatumLegacy LargeEvenRecipeLinear
    refine ⟨K, inferInstance, inferInstance, hKcard, hs, hna, θ, hPθ, ?_⟩
    intro _ hN hact
    have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
    have hBs : IsElemAbelian p Bs := hcfg.2.1.2.1
    have hBBs : B ≤ Bs := hcfg.2.1.1
    have hSstar : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
    have hbeta : p ∈ LargeEvenBeta 4 G := hcfg.1.2.2.2.2.2.1
    have hBmax : LargeEvenIsBmax p B := hSstar.1
    have h4rank : 4 ≤ LargeEvenTwoLocalRank p G := hbeta.2.2.2
    have hBN : B ≤ Subgroup.normalizer (L : Set G) := hBBs.trans hN
    have hn : 1 ≤ n := hlab.1
    have hpdvd2 : p ∣ 2 ^ n - 1 := hpdvd0.trans (Nat.gcd_dvd_right _ _)
    have hp2 : p ≠ 2 := by
      rintro rfl
      have hodd : Odd (2 ^ n - 1) :=
        Nat.Even.sub_odd Nat.one_le_two_pow
          (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hpdvd2)
    have hpK : p ∣ Nat.card K - 1 := by rw [hKcard]; exact hpdvd2
    set E : Subgroup (MulAut (LargeEvenProj (LargeEvenSLGroup (Fin (rank + 1)) K))) :=
      (ggGamma L hN).range.map (ggInducedAut θ) with hEdef
    have hrange_le : (ggBeta L θ hBN).range ≤ E := by
      rintro _ ⟨b, rfl⟩
      rw [l02qt6_ggBeta_eq_ggInducedAut_gamma (θ := θ) hBBs hBN hN b, hEdef]
      exact Subgroup.mem_map.mpr ⟨ggGamma L hN ⟨b, hBBs b.2⟩,
        MonoidHom.mem_range.mpr ⟨⟨b, hBBs b.2⟩, rfl⟩, rfl⟩
    have hcard3 : p ^ 3 ≤ Nat.card E := by
      have hc := card_range_ggBeta_mul (L := L) (θ := θ) hp hSstar hperf hBN
      have h4 := pow_four_le_card_of_bmax hp hBmax h4rank
      have hrange3 : p ^ 3 ≤ Nat.card (ggBeta L θ hBN).range := by
        have h : p ^ 3 * p ≤ Nat.card (ggBeta L θ hBN).range * p := by
          rw [hc]
          calc p ^ 3 * p = p ^ 4 := by ring
            _ ≤ Nat.card B := h4
        exact Nat.le_of_mul_le_mul_right h hp.pos
      exact hrange3.trans (Nat.card_le_card_of_injective
        (Subgroup.inclusion hrange_le) (Subgroup.inclusion_injective hrange_le))
    have hcard1 : p ^ (rank + 1 - 2) ≤ Nat.card E := by
      by_cases hd5 : rank + 1 ≤ 5
      · exact (Nat.pow_le_pow_right hp.pos (by omega : rank + 1 - 2 ≤ 3)).trans hcard3
      · have hd5' : 5 ≤ rank + 1 := by omega
        haveI : CharP K 2 :=
          CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
            Nat.prime_two hn hKcard
        have hlift : GGTorusLift p (rank + 1 - 2)
            (LargeEvenProj (LargeEvenSLGroup (Fin (rank + 1)) K)) :=
          TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv (rank + 1) K)
            (TypeA.ggTorusLift_sub_two (d := rank + 1) hp hpK (by omega)
              (TypeA.slHasSections_of_five_le hd5'))
        exact (pow_le_card_range_ggBeta (r := rank + 1 - 2) hp hSstar hperf θ hBN hlift).trans
          (Nat.card_le_card_of_injective
            (Subgroup.inclusion hrange_le) (Subgroup.inclusion_injective hrange_le))
    have htop : IsElemAbelian p (⊤ : Subgroup ↥Bs) := by
      refine ⟨?_, ?_⟩
      · refine ⟨⟨fun a b => ?_⟩⟩
        haveI : IsMulCommutative ↥Bs := hBs.1
        exact Subtype.ext (mul_comm' a.1 b.1)
      · intro y _
        exact Subtype.ext (hBs.2 y.1 y.2)
    have hElemGamma : IsElemAbelian p (ggGamma L hN).range := by
      simpa only [MonoidHom.range_eq_map] using htop.map (ggGamma L hN)
    have hE : IsElemAbelian p E := by
      rw [hEdef]
      exact hElemGamma.map (ggInducedAut θ)
    set X : Subgroup (MulAut (projectiveSL (rank + 1) K)) :=
      E.map (MulAut.congr (TypeA.recipeEquiv (rank + 1) K)).toMonoidHom with hXdef
    have hXelem : IsElemAbelian p X := by
      rw [hXdef]
      exact hE.map (MulAut.congr (TypeA.recipeEquiv (rank + 1) K)).toMonoidHom
    have hXsub : (X : Set (MulAut (projectiveSL (rank + 1) K))) ⊆
        Set.range (conjAut (rank + 1) K) := by
      rintro _ ⟨ψ, hψE, rfl⟩
      obtain ⟨y, hy, rfl⟩ := hψE
      obtain ⟨b, rfl⟩ := hy
      refine TypeA.congr_recipeEquiv_mem ?_
      have h := ggLAut_mem_of_induces (L := L) (θ := θ) hN hact b.2
      have h2 : ggInducedAut θ (ggGamma L hN b) = ggLAut L θ ⟨b, hN b.2⟩ := by
        rw [ggLAut_eq_ggInducedAut, ggGamma]
        congr 1
      simpa only [h2] using h
    have hcardX : Nat.card X = Nat.card E := by
      rw [hXdef]
      exact Subgroup.card_map_of_injective (MulAut.congr (TypeA.recipeEquiv (rank + 1) K)).injective
    obtain ⟨A₀, hA₀⟩ := TypeA.ggPGLTorality_holds (d := rank + 1) hp hp2 hpK X hXelem hXsub
      (by rw [hcardX]; exact hcard1) (by rw [hcardX]; exact hcard3)
    refine ⟨rank + 1, K, inferInstance, inferInstance,
      MulEquiv.refl (LargeEvenProj (LargeEvenSLGroup (Fin (rank + 1)) K)), ?_⟩
    have hcongr : MulAut.congr
        (MulEquiv.refl (LargeEvenProj (LargeEvenSLGroup (Fin (rank + 1)) K))) =
        MulEquiv.refl (MulAut (LargeEvenProj (LargeEvenSLGroup (Fin (rank + 1)) K))) := by
      ext φ x
      simp [MulAut.congr_apply]
    have hmap : E.map (MulAut.congr
        (MulEquiv.refl (LargeEvenProj (LargeEvenSLGroup (Fin (rank + 1)) K)))).toMonoidHom = E := by
      rw [hcongr]
      simp
    rw [hmap]
    exact l02qt6_comap_comm_of_diag (d := rank + 1) hA₀
  · refine largeEvenRawDatum_mono (fun R _ I F hh => ?_) hraw
    obtain ⟨hs, hna, θ, hPθ⟩ := hh
    exact ⟨hs, hna, θ, hPθ, fun h => absurd h hTor⟩

end CFSG.StandardType

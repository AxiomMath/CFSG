module

public import CFSG.RankThree.PartOne.KC.OrthogonalPairCrossing
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBDenseDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpPlaneFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrow
public import CFSG.LocalAnalysis.StandardType.GGForkA8NotRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBJoinDefs
import CFSG.LocalAnalysis.StandardType.GGTBJOrthLeft
import CFSG.LocalAnalysis.StandardType.GGTBJOrthNbr
import CFSG.LocalAnalysis.StandardType.GGSecFiveBNbrAxis
import CFSG.LocalAnalysis.StandardType.GGTBJOrthLeftGlue
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSparseEndpoint
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermOmKCrossing

public section

namespace CFSG.StandardType

open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2

theorem exists_range_coherent_split_charts_of_marked_deletion
    {G F : Type} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
    {p : ℕ} {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {Bs L : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod p))) (ell : Equiv.Perm (Fin 4))
    (hJoin : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull 4 p)
    (a0 : chartSubgroup (n := 5) (F := F) (b := b) (c := c) (deletionPlanes 3) →* G)
    (ha0 : Function.Injective a0) (haL : a0.range = L)
    (hmarkL : ∀ S : Finset (Fin 4), S.Nonempty → S.card ≤ 2 → S ⊆ deletionPlanes 3 →
      ((chartSubgroup (n := 5) (F := F) (b := b) (c := c) S).subgroupOf
        (chartSubgroup (n := 5) (F := F) (b := b) (c := c) (deletionPlanes 3))).map a0 =
          ggBlockComm Bs eta (ell '' (S : Set (Fin 4)))) :
    ∃ a : ∀ i : Fin 4,
        chartSubgroup (n := 5) (F := F) (b := b) (c := c) (Finset.univ.erase i) →* G,
      (∀ i, Function.Injective (a i)) ∧
      ∀ (i : Fin 4) (S : Finset (Fin 4)), S.Nonempty → S.card ≤ 2 → S ⊆ Finset.univ.erase i →
        ((chartSubgroup (n := 5) (F := F) (b := b) (c := c) S).subgroupOf
          (chartSubgroup (n := 5) (F := F) (b := b) (c := c) (Finset.univ.erase i))).map
            (a i) = ggBlockComm Bs eta (ell '' (S : Set (Fin 4))) := by
  classical
  have hver (u : Fin 4) :
      ∃ k : chartSubgroup (n := 5) (F := F) (b := b) (c := c) (Finset.univ.erase u) →* G,
        Function.Injective k ∧
        ∀ S : Finset (Fin 4), S.Nonempty → S.card ≤ 2 → S ⊆ Finset.univ.erase u →
          ((chartSubgroup (n := 5) (F := F) (b := b) (c := c) S).subgroupOf
            (chartSubgroup (n := 5) (F := F) (b := b) (c := c) (Finset.univ.erase u))).map k =
              ggBlockComm Bs eta (ell '' (S : Set (Fin 4))) := by
    obtain ⟨w, hw, _, hact⟩ := exists_normalizer_conjAut_eq_permAut_of_join hJoin
      (ell * Equiv.swap 0 u * ell⁻¹)
    obtain ⟨P, k, _, _, hk, _, hmarks⟩ :=
      ggTBJOrthNbr_exists_markedDeletionChart_of_conj_of_three_le (r := 3) (by decide) hirr
        Bs L (L.map (MulAut.conj w).toMonoidHom) eta ell u w hw hact rfl a0 ha0 haL hmarkL
    exact ⟨k, hk, hmarks⟩
  choose a ha hmarks using hver
  exact ⟨a, ha, hmarks⟩

theorem ggBlockComm_pairResidual_commute_of_marked_deletion
    {G F : Type} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
    {p : ℕ} {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hcard : 4 ≤ Nat.card F) {Bs L : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod p))) (ell : Equiv.Perm (Fin 4))
    (hJoin : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull 4 p)
    (a0 : chartSubgroup (n := 5) (F := F) (b := b) (c := c) (deletionPlanes 3) →* G)
    (ha0 : Function.Injective a0) (haL : a0.range = L)
    (hmarkL : ∀ S : Finset (Fin 4), S.Nonempty → S.card ≤ 2 → S ⊆ deletionPlanes 3 →
      ((chartSubgroup (n := 5) (F := F) (b := b) (c := c) S).subgroupOf
        (chartSubgroup (n := 5) (F := F) (b := b) (c := c) (deletionPlanes 3))).map a0 =
          ggBlockComm Bs eta (ell '' (S : Set (Fin 4))))
    (i0 i1 j0 j1 : Fin 4) (hij : i0 ≠ i1) (hjj : j0 ≠ j1)
    (hdisj : Disjoint ({i0, i1} : Finset (Fin 4)) {j0, j1}) :
    let R := fun S : Finset (Fin 4) => ggBlockComm Bs eta (ell '' (S : Set (Fin 4)))
    ∀ g ∈ inSubgroup perfectResidual
        (R {i0, i1} ⊓ Subgroup.centralizer ((R {i0} ⊓ R {i1} : Subgroup G) : Set G)),
      ∀ h ∈ R {j0, j1}, Commute g h := by
  obtain ⟨a, ha, hmarks⟩ := exists_range_coherent_split_charts_of_marked_deletion
    hirr eta ell hJoin a0 ha0 haL hmarkL
  exact pairResidual_commute_of_range_coherent_split_charts hirr hcard a ha
    (fun S => ggBlockComm Bs eta (ell '' (S : Set (Fin 4)))) hmarks
    i0 i1 j0 j1 hij hjj hdisj

open CFSG.Assembly CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal

theorem GGSecFiveRouteCfg.ggBlockComm_pairResidual_commute_of_sparse_twD_four_split
    {G : Type} [Group G] [Finite G] {p n : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput) (hFC : GGResNbrFixCentralizesInput)
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (i0 : Fin n)
    (h𝒦 : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (hL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    (hLab : GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab ∧
      (n = 4 ∧ lab.n ≠ 1 ∧ lab.tag = .twD ∧ p ∣ 2 ^ lab.n - 1)) p Bs L)
    (hB : B = Bs)
    (hRM : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (hDense : ¬ ∃ K : Subgroup G, GGSecFiveBCoordBDenseNbr p Bs 𝒦 n eta K) :
    ∀ i j i' j' : Fin n,
      i ≠ j → i' ≠ j' → i ≠ i' → i ≠ j' → j ≠ i' → j ≠ j' →
      ∀ z ∈ inSubgroup perfectResidual
          (ggBlockComm Bs eta {i, j} ⊓ Subgroup.centralizer
            ((ggBlockComm Bs eta {i} ⊓ ggBlockComm Bs eta {j} : Subgroup G) : Set G)),
        ∀ w ∈ ggBlockComm Bs eta {i', j'}, Commute z w := by
  classical
  obtain ⟨hperf, lab, hlab, hrawLabel⟩ := hLab
  obtain ⟨R0, _, I0, F0, _, _, θ0, ⟨hBL, hn4, hf1, htag, hpd⟩, _, _⟩ :=
    largeEvenRawDatum_exists hrawLabel
  subst n
  let f := lab.n
  have hf : 2 ≤ f := by
    have hpos : 1 ≤ lab.n := hlab.1
    dsimp only [f]
    omega
  have hBn : lab.rank = 4 ∧
      (p ∣ 2 ^ lab.n - 1 ∨ Even 4 ∧ p ∣ 2 ^ lab.n + 1) := by
    simpa [GGSecFiveBCoordBLabel, htag] using hBL
  have heq : lab = ⟨.twD, 4, f⟩ := by
    rcases lab with ⟨t, r, f0⟩
    dsimp [f] at htag hBn ⊢
    subst t
    have hr : r = 4 := hBn.1
    subst r
    rfl
  have hrow : GGTBRowR5O1 p lab := by
    refine ⟨htag, ?_, ?_⟩
    · rw [hBn.1]
    · rw [hBn.1]
      exact Or.inl hpd
  have hLexact : GGInnerDiagOnLabel
      (fun p lab => lab = ⟨.twD, 4, f⟩ ∧ GGTBRowR5O1 p lab) p Bs L := by
    refine ⟨hperf, lab, hlab, ?_⟩
    refine largeEvenRawDatum_mono ?_ hrawLabel
    rintro R _ I F ⟨hs, hna, θ, _, hBsN, hind⟩
    exact ⟨hs, hna, θ, ⟨heq, hrow⟩, hBsN, hind⟩
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  have : Fact p.Prime := ⟨hp⟩
  have hcfg : GGConfig p B Bs x L D J := hR.1.1
  obtain ⟨K, hKmem, hKL⟩ :=
    exists_mem_not_le_ggAutomizer_of_bSignedFull hp hp2 eta h𝒦 hL
  obtain ⟨y, hnb⟩ := hR.2.2.2.1.2 K hKmem
  have hy : y ∈ Bs := hB ▸ hnb.1.2.1
  rcases hR.nbr_axis_or_dense hX hTCJ hRig hTPn hA8 hraw hiso hFC hB (by decide)
    eta h𝒦 hL hnb (hRM y K hnb) hKL hy with
    ⟨jAxis, hj, hblk, haxis⟩ | ⟨⟨δ, hδ, hKδ⟩, _⟩
  swap
  · exact (hDense ⟨K, hKmem, δ, hδ, hKδ⟩).elim
  have hyj : eta ⟨y, hcfg.2.1.1 hnb.1.2.1⟩ jAxis ≠ 1 := by
    intro h1
    have hfun : eta ⟨y, hcfg.2.1.1 hnb.1.2.1⟩ = 1 := by
      funext k
      by_cases hk : k = jAxis
      · subst hk
        exact h1
      · exact haxis k hk
    have hy1 : (⟨y, hcfg.2.1.1 hnb.1.2.1⟩ : ↥Bs) = 1 := by
      apply eta.injective
      rw [hfun, map_one]
    exact hnb.1.2.2.1 (by simpa using congrArg Subtype.val hy1)
  obtain ⟨F, fieldF, finiteF, charF, b, c, hFcard, hirr, θ, hBsN, E, Δ, hE, σ, ΘA, Θ,
    hψσ, hΘA, hΘ, hcoord, hAut, hW, hrest⟩ :=
    ggTBJOrthLeft_nativeModel_of_twD (n := 4) (f := f) hcfg hB.symm
      (by decide) hf hL hLexact
  obtain ⟨⟨hminus, hdim, hrowF⟩, hZL, hfin⟩ := hrest
  obtain ⟨χ, κ, hχraw, hχτ, hκτ, hκinj, hκrange, hHmap, hJmap⟩ := hfin
  let : Field F := fieldF
  let : Finite F := finiteF
  have : CharP F 2 := charF
  have hQ : (QuadraticMap.polarBilin (TableBOrth.qMinusForm F 3 b c)).Nondegenerate :=
    TableBOrth.nondegenerate_qMinusForm 3 hirr
  have hsplit : p ∣ Nat.card F - 1 := by
    rw [hFcard]
    exact hpd
  have hcard : 4 ≤ Nat.card F := by
    rw [hFcard]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hf
  obtain ⟨eL, a, ell, hainj, harange, hfac, hell0, hdict, hmarkL, hJchart⟩ :=
    OrthTorus.ggTBJOrthLeft_exists_markedDeletionChart_of_sparse
      (r := 3) (R := OrthRest.RMinus F 3 b c) (eR := OrthTorus.rMinusEquiv F 3 b c)
      (hcfg := hcfg) (hnb := hnb) (hBsB := hB.symm) (hr := by decide)
      (Δ := Δ) (hQ := hQ) (hE := hE) (hdim := hdim) (hminus := hminus)
      (hsplit := hsplit) (hirr := hirr) (θ := θ) (hBsN := hBsN)
      (σ := σ) (ΘA := ΘA) (hψσ := hψσ) (hΘA := hΘA) (Θ := Θ) (hΘ := hΘ)
      (hW := hW) (κ := κ) (hκτ := hκτ) (hκinj := hκinj) (hκrange := hκrange)
      (hJmap := hJmap) (eta := eta) (i0 := i0) (j := jAxis) (hcoord := hcoord)
      (hj := hj) (hyj := hyj) (hyoff := fun k _ hkj => haxis k hkj)
  intro i j i' j' hij hij' hii' hij'' hji' hjj'
  have hdisj : Disjoint ({ell.symm i, ell.symm j} : Finset (Fin 4))
      {ell.symm i', ell.symm j'} := by
    apply Finset.disjoint_left.mpr
    intro k hk hk'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk hk'
    rcases hk with hk | hk <;> rcases hk' with hk' | hk'
    · exact hii' (ell.symm.injective (hk.symm.trans hk'))
    · exact hij'' (ell.symm.injective (hk.symm.trans hk'))
    · exact hji' (ell.symm.injective (hk.symm.trans hk'))
    · exact hjj' (ell.symm.injective (hk.symm.trans hk'))
  have hCross := ggBlockComm_pairResidual_commute_of_marked_deletion hirr hcard eta ell h𝒦
    a hainj harange hmarkL (ell.symm i) (ell.symm j) (ell.symm i') (ell.symm j')
    (fun h => hij (ell.symm.injective h)) (fun h => hij' (ell.symm.injective h)) hdisj
  simpa only [Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq,
    Set.image_singleton, Equiv.apply_symm_apply, Subgroup.coe_inf] using hCross


end CFSG.StandardType

end

module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSparseTwDFiveSplitDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBDenseDefs
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrow
public import CFSG.LocalAnalysis.StandardType.GGForkA8NotRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBJoinDefs

import CFSG.LocalAnalysis.StandardType.GGTBJOrthLeft
import CFSG.LocalAnalysis.StandardType.GGTBJOrthNbr
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSparseOrthCharts
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSparseSp
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSparseEndpoint
import CFSG.LocalAnalysis.StandardType.GGSecFiveBNbrAxis
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBDenseRows
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSpSp
import CFSG.LocalAnalysis.StandardType.GGQuadMinusSpinCover
import CFSG.ClassicalGroups.Orthogonal.IsometryConj
import CFSG.RankThree.PartOne.KC.OrthogonalSplitCompletion

public section

namespace CFSG.StandardType

section Inputs

open CFSG.Assembly
open CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.LieType.Universal.Spin
open CFSG.ClassicalGroups.Orthogonal

private theorem eta_apply_ne_one_of_forall_eq_one
    {G : Type} [Group G] {Bs : Subgroup G} {m p : ℕ}
    {eta : ↥Bs ≃* (Fin m → Multiplicative (ZMod p))} {b : ↥Bs} {j : Fin m}
    (hb : (b : G) ≠ 1) (h : ∀ k, k ≠ j → eta b k = 1) : eta b j ≠ 1 := by
  intro h1
  have hfun : eta b = 1 := by
    funext k
    by_cases hk : k = j
    · subst hk
      exact h1
    · exact h k hk
  have hb1 : b = 1 := by
    apply eta.injective
    rw [hfun, map_one]
  exact hb (by simpa using congrArg Subtype.val hb1)

private theorem exists_deleted_coordinate_and_conj_action
    {G : Type} [Group G] {Bs : Subgroup G} {p r : ℕ}
    {eta : ↥Bs ≃* (Fin (r + 1) → Multiplicative (ZMod p))}
    {w : G} {hw : w ∈ Subgroup.normalizer (Bs : Set G)}
    {i0 j : Fin (r + 1)} {ell : Equiv.Perm (Fin (r + 1))}
    (hact0 : MulAut.congr eta (ggConjAut Bs hw) =
      SpCoord.permAut (p := p) (Equiv.swap i0 j))
    (hell0 : ell 0 = i0) (hj : j ≠ i0) :
    ∃ u : Fin (r + 1), (0 : Fin (r + 1)) ≠ u ∧
      MulAut.congr eta (ggConjAut Bs hw) =
        SpCoord.permAut (p := p) (ell * Equiv.swap 0 u * ell⁻¹) := by
  let u : Fin (r + 1) := ell.symm j
  have hellu : ell u = j := by simp [u]
  have h0u : (0 : Fin (r + 1)) ≠ u := by
    intro h
    have h1 : ell (0 : Fin (r + 1)) = ell u := congrArg ell h
    rw [hell0, hellu] at h1
    exact hj h1.symm
  refine ⟨u, h0u, ?_⟩
  rw [hact0, ← Equiv.swap_apply_apply, hell0, hellu]

private theorem two_lt_card_of_card_eq_two_pow {F : Type} {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (hf : 2 ≤ f) : 2 < Nat.card F := by
  rw [hF]
  calc (2 : ℕ) = 2 ^ 1 := rfl
    _ < 2 ^ f := Nat.pow_lt_pow_right (by norm_num) (by omega)

private theorem exists_two_further_coordinates {r : ℕ} {u : Fin (r + 1)}
    (h0u : (0 : Fin (r + 1)) ≠ u) (hr : 3 ≤ r) :
    ∃ v cc : Fin (r + 1), v ≠ 0 ∧ v ≠ u ∧ cc ≠ 0 ∧ cc ≠ u ∧ v ≠ cc := by
  let T : Finset (Fin (r + 1)) := (Finset.univ.erase u).erase 0
  have hTcard : 1 < T.card := by
    dsimp only [T]
    rw [Finset.card_erase_of_mem (show (0 : Fin (r + 1)) ∈ Finset.univ.erase u from by
          simp only [Finset.mem_erase, Finset.mem_univ, and_true]
          exact h0u),
      Finset.card_erase_of_mem (Finset.mem_univ u)]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨v, hvT, cc, hccT, hvc⟩ := Finset.one_lt_card.mp hTcard
  have hvT' : v ≠ 0 ∧ v ≠ u := by
    simpa only [T, Finset.mem_erase, Finset.mem_univ, and_true] using hvT
  have hccT' : cc ≠ 0 ∧ cc ≠ u := by
    simpa only [T, Finset.mem_erase, Finset.mem_univ, and_true] using hccT
  exact ⟨v, cc, hvT'.1, hvT'.2, hccT'.1, hccT'.2, hvc⟩

private theorem exists_sparse_neighbour_setup
    {G : Type} [Group G] [Finite G] {p n : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hFC : GGResNbrFixCentralizesInput) (hBJ : BMaxJoinInput)
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hB : B = Bs) (hn : 4 ≤ n)
    (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (i0 : Fin n)
    (h𝒦 : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (hL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    (hRM : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (hDense : ¬ ∃ K : Subgroup G, GGSecFiveBCoordBDenseNbr p Bs 𝒦 n eta K) :
    ∃ (_hp : p.Prime) (K : Subgroup G) (y : G) (_hnb : GGNbr p B x D J y K) (hy : y ∈ Bs)
      (j : Fin n) (w : G) (hw : w ∈ Subgroup.normalizer (Bs : Set G)),
      K ∈ 𝒦 ∧ j ≠ i0 ∧ (∀ k, k ≠ j → eta ⟨y, hy⟩ k = 1) ∧
      MulAut.congr eta (ggConjAut Bs hw) = SpCoord.permAut (p := p) (Equiv.swap i0 j) ∧
      K = L.map (MulAut.conj w).toMonoidHom ∧
      ggG0 p B x L D J = L ⊔ K ∧ eta ⟨y, hy⟩ j ≠ 1 := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  obtain ⟨K, hKmem, hKL⟩ :=
    exists_mem_not_le_ggAutomizer_of_bSignedFull hp hp2 eta h𝒦 hL
  obtain ⟨y, hnb⟩ := hR.2.2.2.1.2 K hKmem
  have hy : y ∈ Bs := hB ▸ hnb.1.2.1
  rcases hR.nbr_axis_or_dense hX hTCJ hRig hTPn hA8 hraw hiso hFC hB (by omega)
      eta h𝒦 hL hnb (hRM y K hnb) hKL hy with ⟨j, hj, hblk, haxis⟩ | ⟨⟨δ, hδ, hKδ⟩, -⟩
  swap
  · exact (hDense ⟨K, hKmem, δ, hδ, hKδ⟩).elim
  obtain ⟨w, hw, hact0, hKeq, hAK⟩ :=
    hR.exists_eq_map_conj_swap_of_sparse hB (by omega) eta i0 h𝒦 hL hy hnb hj haxis hblk
  have hLK : ggG0 p B x L D J = L ⊔ K :=
    ggG0_eq_sup_of_bCoordinateBlocks hBJ hR e hP (by omega) h𝒦 hL hRM hKmem hj hAK
  have hyj : eta ⟨y, hy⟩ j ≠ 1 :=
    eta_apply_ne_one_of_forall_eq_one (by simpa using hnb.1.2.2.1) haxis
  exact ⟨hp, K, y, hnb, hy, j, w, hw, hKmem, hj, haxis, hact0, hKeq, hLK, hyj⟩

private theorem exists_native_marked_L_chart
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {r f : ℕ} (hr : 4 ≤ r) (hf : 2 ≤ f)
    (hcfg : GGConfig p B Bs x L D J) (hBsB : Bs = B)
    {eta : ↥Bs ≃* (Fin (r + 1) → Multiplicative (ZMod p))} {i0 : Fin (r + 1)}
    (hL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom =
      bCoordinateBlock (r + 1) p i0)
    (hLexact : GGInnerDiagOnLabel
      (fun p lab => lab = ⟨.twD, r + 1, f⟩ ∧ GGTBRowR5O1 p lab) p Bs L)
    (hpd : p ∣ 2 ^ f - 1)
    {y : G} {K : Subgroup G} {j : Fin (r + 1)}
    (hnb : GGNbr p B x D J y K) (hj : j ≠ i0)
    (hyj : eta ⟨y, hcfg.2.1.1 hnb.1.2.1⟩ j ≠ 1)
    (hyoff : ∀ k, k ≠ i0 → k ≠ j → eta ⟨y, hcfg.2.1.1 hnb.1.2.1⟩ k = 1) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (b c : F),
      Nat.card F = 2 ^ f ∧ (∀ s : F, s ^ 2 + b * s + c ≠ 0) ∧
      ∃ (a : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
          (deletionPlanes r) →* G)
        (ell : Equiv.Perm (Fin (r + 1))),
        Function.Injective a ∧ a.range = L ∧ ell 0 = i0 ∧
        (∀ S : Finset (Fin (r + 1)), S.Nonempty → S.card ≤ 2 → S ⊆ deletionPlanes r →
          ((chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) S).subgroupOf
            (chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
              (deletionPlanes r))).map a =
            ggBlockComm Bs eta (ell '' (S : Set (Fin (r + 1))))) := by
  obtain ⟨F, fieldF, finiteF, charF, b, c, hFcard, hirr, θ, hBsN, E, Δ, hE, σ, ΘA, Θ,
    hψσ, hΘA, hΘ, hcoord, hAut, hW, hrest⟩ :=
    ggTBJOrthLeft_nativeModel_of_twD (n := r + 1) (f := f) hcfg hBsB
      (by omega) hf hL hLexact
  obtain ⟨⟨hminus, hdim, hrow⟩, hZL, hfin⟩ := hrest
  obtain ⟨χ, κ, hχraw, hχτ, hκτ, hκinj, hκrange, hHmap, hJmap⟩ := hfin
  let fieldF' : Field F := fieldF
  let finiteF' : Finite F := finiteF
  let charF' : CharP F 2 := charF
  have hQ : (QuadraticMap.polarBilin (TableBOrth.qMinusForm F r b c)).Nondegenerate :=
    TableBOrth.nondegenerate_qMinusForm r hirr
  have hsplit : p ∣ Nat.card F - 1 := by
    rw [hFcard]
    exact hpd
  obtain ⟨eL, a, ell, hainj, harange, hfac, hell0, hdict, hmarkL, hJchart⟩ :=
    OrthTorus.ggTBJOrthLeft_exists_markedDeletionChart_of_sparse (r := r)
      (R := OrthRest.RMinus F r b c) (eR := OrthTorus.rMinusEquiv F r b c)
      (hcfg := hcfg) (hnb := hnb) (hBsB := hBsB) (hr := by omega) (Δ := Δ)
      (hQ := hQ) (hE := hE) (hdim := hdim) (hminus := hminus) (hsplit := hsplit)
      (hirr := hirr) (θ := θ) (hBsN := hBsN) (σ := σ) (ΘA := ΘA)
      (hψσ := hψσ) (hΘA := hΘA) (Θ := Θ) (hΘ := hΘ) (hW := hW)
      (κ := κ) (hκτ := hκτ) (hκinj := hκinj) (hκrange := hκrange)
      (hJmap := hJmap) (eta := eta) (i0 := i0) (j := j) (hcoord := hcoord)
      (hj := hj) (hyj := hyj) (hyoff := hyoff)
  exact ⟨F, fieldF, finiteF, charF, b, c, hFcard, hirr, a, ell, hainj, harange,
    hell0, hmarkL⟩

private theorem exists_calibrated_marked_K_chart
    {G F : Type} [Group G] [Field F] [Finite F] [CharP F 2]
    {r p : ℕ} {b c : F}
    (hr : 4 ≤ r) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hcard : 2 < Nat.card F)
    (Bs L K : Subgroup G) (eta : ↥Bs ≃* (Fin (r + 1) → Multiplicative (ZMod p)))
    (ell : Equiv.Perm (Fin (r + 1))) (u : Fin (r + 1))
    (h0u : (0 : Fin (r + 1)) ≠ u)
    (w : G) (hw : w ∈ Subgroup.normalizer (Bs : Set G))
    (hact : MulAut.congr eta (ggConjAut Bs hw) =
      SpCoord.permAut (p := p) (ell * Equiv.swap 0 u * ell⁻¹))
    (hK : L.map (MulAut.conj w).toMonoidHom = K)
    (a : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) (deletionPlanes r) →* G)
    (ha : Function.Injective a) (haL : a.range = L)
    (hmarkL : ∀ S : Finset (Fin (r + 1)), S.Nonempty → S.card ≤ 2 →
      S ⊆ deletionPlanes r →
      ((chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) S).subgroupOf
        (chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
          (deletionPlanes r))).map a =
        ggBlockComm Bs eta (ell '' (S : Set (Fin (r + 1))))) :
    ∃ k' : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
        (Finset.univ.erase u) →* G,
      Function.Injective k' ∧ k'.range = K ∧
      (∀ x : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
          (deletionPlanes r ∩ Finset.univ.erase u),
        a (Subgroup.inclusion (chartSubgroup_mono hirr Finset.inter_subset_left) x) =
        k' (Subgroup.inclusion (chartSubgroup_mono hirr Finset.inter_subset_right) x)) ∧
      (∀ S : Finset (Fin (r + 1)), S.Nonempty → S.card ≤ 2 →
        S ⊆ Finset.univ.erase u →
        ((chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) S).subgroupOf
          (chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
            (Finset.univ.erase u))).map k' =
        ggBlockComm Bs eta (ell '' (S : Set (Fin (r + 1))))) := by
  classical
  obtain ⟨-, k, -, -, hkinj, hkrange, hmarkK⟩ :=
    ggTBJOrthNbr_exists_markedDeletionChart_of_conj (r := r) (F := F) (p := p)
      (b := b) (c := c) (hr := hr) (hirr := hirr)
      (Bs := Bs) (L := L) (K := K) (eta := eta) (ell := ell) (u := u) (h0u := h0u)
      (w := w) (hw := hw) (hact := hact) (hK := hK)
      (a := a) (ha := ha) (haL := haL) (hmarkL := hmarkL)
  let D0 : Finset (Fin (r + 1)) := Finset.univ.erase (0 : Fin (r + 1))
  let Du : Finset (Fin (r + 1)) := Finset.univ.erase u
  let O : Finset (Fin (r + 1)) := D0 ∩ Du
  have hmark : ∀ S : Finset (Fin (r + 1)), S.Nonempty → S.card ≤ 2 → S ⊆ O →
      ((chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) S).subgroupOf
        (chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) D0)).map a =
      ((chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) S).subgroupOf
        (chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) Du)).map k := by
    intro S hSne hScard hSub
    dsimp only [D0, Du, O] at hSub ⊢
    rw [hmarkL S hSne hScard (fun x hx => (Finset.mem_inter.mp (hSub hx)).1),
      hmarkK S hSne hScard (fun x hx => (Finset.mem_inter.mp (hSub hx)).2)]
  obtain ⟨beta, hcoh', hk'inj, hk'range, hbetaSupp⟩ :=
    exists_calibrated_deletion_chart_of_marked_supports
      (F := F) (b := b) (c := c) (r := r) (G := G) (u := u)
      hr hirr hcard h0u a k ha hkinj hmark
  let k' : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
      (Finset.univ.erase u) →* G := k.comp beta.toMonoidHom
  refine ⟨k', hk'inj, hk'range.trans hkrange, ?_, ?_⟩
  · intro x
    exact (DFunLike.congr_fun hcoh' x).symm
  · intro S hSne hScard hSub
    rw [show k' = k.comp beta.toMonoidHom from rfl, ← Subgroup.map_map,
      hbetaSupp S hSub, hmarkK S hSne hScard hSub]

private theorem exists_injective_split_completion
    {G F : Type} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
    {r p : ℕ} {b c : F} {Bs L K : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hr : 4 ≤ r) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hcard : 2 < Nat.card F)
    (eta : ↥Bs ≃* (Fin (r + 1) → Multiplicative (ZMod p)))
    (ell : Equiv.Perm (Fin (r + 1))) (u : Fin (r + 1))
    (a : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) (deletionPlanes r) →* G)
    (k : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
      (Finset.univ.erase u) →* G)
    (ha : Function.Injective a) (hk : Function.Injective k)
    (haL : a.range = L) (hkK : k.range = K)
    (hmarkL : ∀ S : Finset (Fin (r + 1)), S.Nonempty → S.card ≤ 2 →
      S ⊆ deletionPlanes r →
      ((chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) S).subgroupOf
        (chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
          (deletionPlanes r))).map a =
        ggBlockComm Bs eta (ell '' (S : Set (Fin (r + 1)))))
    (hmarkK : ∀ S : Finset (Fin (r + 1)), S.Nonempty → S.card ≤ 2 →
      S ⊆ Finset.univ.erase u →
      ((chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) S).subgroupOf
        (chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
          (Finset.univ.erase u))).map k =
        ggBlockComm Bs eta (ell '' (S : Set (Fin (r + 1)))))
    (hcoh : ∀ x : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
        (deletionPlanes r ∩ Finset.univ.erase u),
      a (Subgroup.inclusion (chartSubgroup_mono hirr Finset.inter_subset_left) x) =
      k (Subgroup.inclusion (chartSubgroup_mono hirr Finset.inter_subset_right) x))
    (hSigma : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom =
      bSignedFull (r + 1) p)
    {v cc : Fin (r + 1)}
    (huv : u ≠ v) (hcu : cc ≠ u) (hcv : cc ≠ v)
    (h0u : (0 : Fin (r + 1)) ≠ u) (h0v : (0 : Fin (r + 1)) ≠ v)
    (hcc0 : cc ≠ 0) :
    ∃ Phi : orthDerived (quadMinus (r + 2) F b c) →* G,
      Function.Injective Phi ∧ Phi.range = L ⊔ K := by
  classical
  obtain ⟨t, hRestrL, hRestrK, hcross, hrangeGH⟩ :=
    exists_permHom_of_coherent_marked_sparse_split_charts (r := r) (F := F) (p := p)
      (b := b) (c := c) (hr := hr) (hirr := hirr) (hcard := hcard)
      (Bs := Bs) (L := L) (K := K) (𝒦 := 𝒦) (eta := eta) (ell := ell)
      (hSigma := hSigma) (huv := huv) (hcu := hcu) (hcv := hcv)
      (h0u := h0u) (h0v := h0v) (hcc0 := hcc0) (a := a) (k := k)
      (ha := ha) (hk := hk) (haL := haL) (hkK := hkK)
      (hmarkL := hmarkL) (hmarkK := hmarkK) (hcoh := hcoh)
  obtain ⟨Phi, ⟨haPhi, htPhi⟩, -⟩ :=
    existsUnique_extends_deletion_and_permutation (r := r) (F := F) (b := b) (c := c)
      (hr := hr) (hirr := hirr) (hcard := hcard) (a := a) (t := t)
      (huv := huv) (hcu := hcu) (hcv := hcv) (h0u := h0u)
      (h0v := h0v) (hcc0 := hcc0) (hcommon := hRestrL) (hcross := hcross)
  obtain ⟨hPhiInj, hPhiRangeSup⟩ :=
    injective_range_of_injective_a (r := r) (F := F) (b := b) (c := c)
      (hr := hr) (hirr := hirr) (hcard := hcard) (a := a) (t := t)
      (huv := huv) (hcu := hcu) (hcv := hcv) (h0u := h0u)
      (h0v := h0v) (hcc0 := hcc0) (hcommon := hRestrL) (hcross := hcross)
      (hinj_a := ha) (haΦ := haPhi) (htΦ := htPhi)
  exact ⟨Phi, hPhiInj, hPhiRangeSup.trans hrangeGH⟩

private theorem exists_exact_twD_label_of_split
    {G : Type} [Group G] {n p : ℕ} {Bs L : Subgroup G}
    (hLab : GGInnerDiagOnLabel
      (fun p lab => GGSecFiveBCoordBLabel n p lab ∧
        (5 ≤ n ∧ lab.n ≠ 1 ∧ lab.tag = .twD ∧ p ∣ 2 ^ lab.n - 1)) p Bs L) :
    ∃ f : ℕ, 5 ≤ n ∧ 2 ≤ f ∧ p ∣ 2 ^ f - 1 ∧
      GGInnerDiagOnLabel
        (fun p lab => lab = ⟨.twD, n, f⟩ ∧ GGTBRowR5O1 p lab) p Bs L := by
  obtain ⟨lab, hΛ, hPred, hHas, hKeep⟩ := GGInnerDiagOnLabel.exists_label_eq hLab
  have hBL : GGSecFiveBCoordBLabel n p lab := hPred.1
  have h5 : 5 ≤ n := hPred.2.1
  have hf1 : lab.n ≠ 1 := hPred.2.2.1
  have htag : lab.tag = .twD := hPred.2.2.2.1
  have hpd : p ∣ 2 ^ lab.n - 1 := hPred.2.2.2.2
  rcases lab with ⟨tag, rank, f⟩
  simp only [GGSecFiveBCoordBLabel] at hBL
  rcases hBL with ⟨hBC, -, -⟩ | ⟨hTw, hrank, -⟩ | ⟨hD, -, -⟩ | ⟨hA, -, -⟩
  · rcases hBC with h | h
    · rw [h] at htag
      cases htag
    · rw [h] at htag
      cases htag
  · have hf1' : 1 ≤ f := by simpa using hΛ.1
    have hf : 2 ≤ f := Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hf1' (Ne.symm hf1))
    have hlab_eq : (⟨tag, rank, f⟩ : LargeEvenLabel) = ⟨.twD, n, f⟩ := by rw [hTw, hrank]
    rw [hlab_eq] at hKeep
    refine ⟨f, h5, hf, hpd, ?_⟩
    refine largeEvenMarking_mono (fun lab' R _ I F θ hP => ?_) hKeep
    exact ⟨⟨hP.1.2, by
      rw [hP.1.2]
      exact ⟨rfl, by change 4 ≤ n; omega, Or.inl hpd⟩⟩, hP.2⟩
  · rw [hD] at htag
    cases htag
  · rw [hA] at htag
    cases htag

theorem ggSecFiveBCoordBSparseTwDFiveSplitInput_holds :
    GGSecFiveBCoordBSparseTwDFiveSplitInput := by
  intro hX hTCJ hRig hTPn hA8 hraw hiso hFC hBJ
    G _ _ p B Bs x L D J 𝒦 hR hT1 n e hP hn
    eta i0 h𝒦 hL hLab hB hRM hG0 hSpC hSpSpC hOmC hDense
  obtain ⟨r, hn_eq⟩ : ∃ r, n = r + 1 := ⟨n - 1, by omega⟩
  subst n
  obtain ⟨f, h5, hf, hpd, hLexact⟩ := exists_exact_twD_label_of_split hLab
  have hr : 4 ≤ r := by omega
  obtain ⟨hp, K, y, hnb, hy, j, w, hw, hKmem, hj, haxis, hact0, hKeq, hLK, hyj⟩ :=
    exists_sparse_neighbour_setup hX hTCJ hRig hTPn hA8 hraw hiso hFC hBJ hR hB
      (by omega) e hP eta i0 h𝒦 hL hRM hDense
  let fact : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, fieldF, finiteF, charF, b, c, hFcard, hirr, a, ell, hainj, harange,
    hell0, hmarkL⟩ :=
    exists_native_marked_L_chart (r := r) (f := f) hr hf hR.1.1 hB.symm hL hLexact hpd
      hnb hj hyj (fun k _ hkj => haxis k hkj)
  let fieldF' : Field F := fieldF
  let finiteF' : Finite F := finiteF
  let charF' : CharP F 2 := charF
  obtain ⟨u, h0u, hact⟩ :=
    exists_deleted_coordinate_and_conj_action (r := r) hact0 hell0 hj
  obtain ⟨k', hk'inj, hk'range, hcoh, hmarkK'⟩ :=
    exists_calibrated_marked_K_chart (r := r) (F := F) (p := p) (b := b) (c := c)
      hr hirr (two_lt_card_of_card_eq_two_pow hFcard hf) Bs L K eta ell u h0u
      w hw hact hKeq.symm a hainj harange hmarkL
  obtain ⟨v, cc, hv0, hvu, hcc0, hccu, hvc⟩ :=
    exists_two_further_coordinates (r := r) (u := u) h0u (by omega)
  obtain ⟨Phi, hPhiInj, hPhiRange⟩ :=
    exists_injective_split_completion (r := r) (F := F) (p := p) (b := b) (c := c)
      (Bs := Bs) (L := L) (K := K) (𝒦 := 𝒦)
      hr hirr (two_lt_card_of_card_eq_two_pow hFcard hf) eta ell u a k'
      hainj hk'inj harange hk'range hmarkL hmarkK' hcoh h𝒦
      hvu.symm hccu hvc.symm h0u hv0.symm hcc0
  exact ggSecFiveData_of_injective_quadMinus (F := F) (b := b) (c := c)
    (m := r + 2) (f := f) hirr (by omega) (by omega) hFcard hPhiInj
    (hPhiRange.trans hLK.symm)
end Inputs

end CFSG.StandardType

end

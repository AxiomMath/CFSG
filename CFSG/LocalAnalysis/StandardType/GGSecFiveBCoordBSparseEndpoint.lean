module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSparseSpDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJDefs
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrow
public import CFSG.LocalAnalysis.StandardType.GGForkA8NotRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBJoinDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJLink
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJCore
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBDenseCoords
import CFSG.LocalAnalysis.StandardType.GGSecFiveBFixLine
import CFSG.LocalAnalysis.StandardType.GGFrameRouteJoin
import CFSG.LocalAnalysis.StandardType.GGSecFiveBNbrAxis
import CFSG.LocalAnalysis.StandardType.GGSecFiveBNbrType
import CFSG.LocalAnalysis.StandardType.GGSignedCoordFix
import CFSG.LocalAnalysis.StandardType.GGTBRowSignedFrameAux
import CFSG.LocalAnalysis.StandardType.GGTypeANbrGate
import CFSG.LocalAnalysis.StandardType.GGSharedInvolution
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred
import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr
import CFSG.LocalAnalysis.StandardType.GGPropFiveTwentyOneDefs
import CFSG.Mathlib.GroupTheory.SymmetricNormalizer

public section

namespace CFSG.StandardType

open CFSG.Assembly Multiplicative

theorem exists_mem_not_le_ggAutomizer_of_bSignedFull
    {G : Type} [Group G] {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Bs L : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {i0 : Fin n}
    (hEta : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (hL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0) :
    ∃ K ∈ 𝒦, ¬ ggAutomizer K Bs ≤ ggAutomizer L Bs := by
  by_contra h
  push Not at h
  have hjoin : ggAutomizerJoin L Bs 𝒦 ≤ ggAutomizer L Bs := by
    rw [ggAutomizerJoin]
    exact sup_le le_rfl (iSup₂_le fun K hK => h K hK)
  have hle : bSignedFull n p ≤ bCoordinateBlock n p i0 := by
    have hmap := Subgroup.map_mono (f := (MulAut.congr eta).toMonoidHom) hjoin
    rwa [hEta, hL] at hmap
  exact sgnAut_not_mem_bCoordinateBlock hp hp2 i0
    (hle (Subgroup.subset_closure (Or.inl ⟨i0, rfl⟩)))

private theorem mem_zpowers_of_axis {G : Type} [Group G] {Bs : Subgroup G} {n p : ℕ}
    [Fact p.Prime] (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {j : Fin n} {a b : ↥Bs}
    (ha : ∀ k, k ≠ j → eta a k = 1) (hb : ∀ k, k ≠ j → eta b k = 1) (ha1 : eta a j ≠ 1) :
    (b : G) ∈ Subgroup.zpowers (a : G) := by
  have hp : p.Prime := Fact.out
  have ha0 : toAdd (eta a j) ≠ 0 := fun h => ha1 (by rw [← ofAdd_toAdd (eta a j), h]; rfl)
  obtain ⟨m, hm⟩ := SpCoord.exists_natCast_mul_eq hp ha0 (toAdd (eta b j))
  have hab : a ^ m = b := by
    apply eta.injective
    funext k
    rw [map_pow, Pi.pow_apply]
    by_cases hk : k = j
    · subst hk
      apply toAdd.injective
      rw [toAdd_pow, ← hm, nsmul_eq_mul]
    · rw [ha k hk, hb k hk, one_pow]
  exact ⟨m, by rw [← hab]; simp⟩

theorem GGSecFiveRouteCfg.eq_map_conj_of_sparse_of_swap
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hB : B = Bs)
    {n : ℕ} (hn : 4 ≤ n) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (i0 : Fin n)
    (hLB : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    {y : G} (hy : y ∈ Bs) {K : Subgroup G} {j : Fin n} (hnb : GGNbr p B x D J y K)
    (hj : j ≠ i0) (hyj : ∀ k, k ≠ j → eta ⟨y, hy⟩ k = 1)
    (hAK : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p j ∨
      (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = dCoordinateBlock n p j)
    (w : G) (hw : w ∈ Subgroup.normalizer (Bs : Set G))
    (hact : MulAut.congr eta (ggConjAut Bs hw) =
      SpCoord.permAut (p := p) (Equiv.swap i0 j)) :
    K = L.map (MulAut.conj w).toMonoidHom ∧
      (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p j := by
  classical
  have hcfg : GGConfig p B Bs x L D J := hR.1.1
  obtain ⟨hp, hEl, hxBs, -, -⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have : Fact p.Prime := ⟨hp⟩
  have hx1 : x ≠ 1 := hcfg.1.2.2.2.2.2.2.1.2.2.1
  have hy1 : y ≠ 1 := hnb.1.2.2.1
  have hLc : IsComponentOf L (Subgroup.centralizer ({x} : Set G)) :=
    hcfg.1.2.2.2.2.2.2.1.2.2.2.1
  obtain ⟨hKc, hBK⟩ := isComponentOf_of_isNeighborOf hcfg.1.2.2.2.2.2.2.2
    (isNeighborOf_of_ggNbr hcfg.2.2 hnb)
  let σ : Equiv.Perm (Fin n) := Equiv.swap i0 j
  have hσ : MulAut.congr eta (ggConjAut Bs hw) = SpCoord.permAut (p := p) σ := hact
  have hcoord : ∀ (φ : MulAut ↥Bs) (b : ↥Bs), eta (φ b) = MulAut.congr eta φ (eta b) := by
    intro φ b
    simp [MulAut.congr_apply]
  have hx0 : ∀ k, k ≠ i0 → eta ⟨x, hxBs⟩ k = 1 := fun k hk =>
    CommonJ.eta_x_eq_one hcfg hB eta i0 hLB ⟨x, hxBs⟩ rfl hk
  have hwx : w * x * w⁻¹ ∈ Bs := (Subgroup.mem_normalizer_iff.mp hw x).mp hxBs
  have hτx : ggConjAut Bs hw ⟨x, hxBs⟩ = ⟨w * x * w⁻¹, hwx⟩ :=
    Subtype.ext (ggConjAut_apply Bs hw _)
  have hwxj : ∀ k, k ≠ j → eta ⟨w * x * w⁻¹, hwx⟩ k = 1 := by
    intro k hk
    rw [← hτx, hcoord, hσ, SpCoord.permAut_apply]
    apply hx0
    intro h
    apply hk
    have h' : σ⁻¹ k = i0 := h
    rw [Equiv.swap_inv, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at h'
    exact h'
  have hyj1 : eta ⟨y, hy⟩ j ≠ 1 := by
    intro h
    apply hy1
    have h1 : eta ⟨y, hy⟩ = 1 := by
      funext k
      by_cases hk : k = j
      · subst hk
        exact h
      · exact hyj k hk
    exact congrArg Subtype.val (eta.injective (h1.trans (map_one eta).symm))
  have hwxj1 : eta ⟨w * x * w⁻¹, hwx⟩ j ≠ 1 := by
    intro h
    apply hx1
    have h1 : eta ⟨w * x * w⁻¹, hwx⟩ = 1 := by
      funext k
      by_cases hk : k = j
      · subst hk
        exact h
      · exact hwxj k hk
    have h2 : w * x * w⁻¹ = 1 := congrArg Subtype.val (eta.injective (h1.trans (map_one eta).symm))
    have h3 : x = w⁻¹ * (w * x * w⁻¹) * w := by group
    rw [h3, h2]
    group
  have hy_mem := mem_zpowers_of_axis (G := G) eta hwxj hyj hwxj1
  have hwx_mem := mem_zpowers_of_axis (G := G) eta hyj hwxj hyj1
  have hcent : Subgroup.centralizer ({w * x * w⁻¹} : Set G) =
      Subgroup.centralizer ({y} : Set G) := by
    ext g
    simp only [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hg
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hy_mem
      have hm' : (w * x * w⁻¹) ^ m = y := hm
      rw [← hm']
      exact (Commute.zpow_right (show Commute g _ from hg) m).eq
    · intro hg
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hwx_mem
      have hm' : y ^ m = w * x * w⁻¹ := hm
      rw [← hm']
      exact (Commute.zpow_right (show Commute g _ from hg) m).eq
  have hLwc : IsComponentOf (L.map (MulAut.conj w).toMonoidHom)
      (Subgroup.centralizer ({y} : Set G)) := by
    rw [← hcent]
    exact isComponentOf_centralizer_map_conj hLc w
  have hLwmap : (ggAutomizer (L.map (MulAut.conj w).toMonoidHom) Bs).map
      (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p j := by
    rw [map_congr_ggAutomizer_map_conj eta hw L, hLB, hσ,
      map_conj_permAut_bCoordinateBlock, Equiv.swap_apply_left]
  obtain ⟨k, hk, l, hl, hkl⟩ : ∃ k ∈ (Finset.univ.erase i0).erase j,
      ∃ l ∈ (Finset.univ.erase i0).erase j, k ≠ l := by
    apply Finset.one_lt_card.mp
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  rw [Finset.mem_erase, Finset.mem_erase] at hk hl
  let ρ : MulAut (Fin n → Multiplicative (ZMod p)) := SpCoord.permAut (Equiv.swap k l)
  let r : MulAut ↥Bs := (MulAut.congr eta).symm ρ
  have hr_map : MulAut.congr eta r = ρ := MulEquiv.apply_symm_apply _ _
  have hmem : ∀ A : Subgroup (MulAut ↥Bs), ρ ∈ A.map (MulAut.congr eta).toMonoidHom → r ∈ A := by
    intro A hA
    obtain ⟨r', hr', hr'eq⟩ := Subgroup.mem_map.mp hA
    have hrr : r' = r := (MulAut.congr eta).injective (hr'eq.trans hr_map.symm)
    rwa [← hrr]
  have hρB : ρ ∈ bCoordinateBlock n p j :=
    Subgroup.subset_closure (Or.inr ⟨k, l, hkl, hk.1, hl.1, rfl⟩)
  have hrK : r ∈ ggAutomizer K Bs := by
    apply hmem
    rcases hAK with h | h
    · rw [h]
      exact hρB
    · rw [h]
      exact Subgroup.subset_closure (Or.inl ⟨k, l, hkl, hk.1, hl.1, rfl⟩)
  have hrLw : r ∈ ggAutomizer (L.map (MulAut.conj w).toMonoidHom) Bs := by
    apply hmem
    rw [hLwmap]
    exact hρB
  have hBs2 : ∀ b ∈ Bs, b * b = 1 → b = 1 := fun b hb h =>
    eq_one_of_mul_self_eq_one_of_isElemAbelian (hp.odd_of_ne_two hp2) hEl hb h
  have hr2 : r ^ 2 = 1 := by
    apply (MulAut.congr eta).injective
    rw [map_pow, hr_map, map_one]
    exact SpCoord.permAut_swap_sq k l
  have hr1 : r ≠ 1 := by
    intro h
    have hρ1 : ρ = 1 := by rw [← hr_map, h, map_one]
    have h' := congrArg (fun φ : MulAut (Fin n → Multiplicative (ZMod p)) =>
      φ (Pi.mulSingle k (ofAdd (1 : ZMod p))) l) hρ1
    simp only [ρ, SpCoord.permAut_apply, Function.comp_apply, Equiv.swap_inv,
      Equiv.swap_apply_right, Pi.mulSingle_eq_same, MulAut.one_apply,
      Pi.mulSingle_eq_of_ne' hkl] at h'
    exact SpCoord.coord_zero_ne_one hp (congrArg toAdd h').symm
  have hKeq : K = L.map (MulAut.conj w).toMonoidHom :=
    eq_of_isComponentOf_of_mem_ggAutomizer hKc hLwc hBs2 (hB ▸ hBK) hrK hrLw hr2 hr1
  exact ⟨hKeq, hKeq ▸ hLwmap⟩

theorem GGSecFiveRouteCfg.exists_ggG0_eq_map_conj_swap_of_sparse
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hB : B = Bs)
    {n : ℕ} (hn : 4 ≤ n) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (i0 : Fin n)
    (hEta : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (hLB : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    {y : G} (hy : y ∈ Bs) {K : Subgroup G} {j : Fin n} (hnb : GGNbr p B x D J y K)
    (hj : j ≠ i0) (hyj : ∀ k, k ≠ j → eta ⟨y, hy⟩ k = 1)
    (hAK : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p j ∨
      (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = dCoordinateBlock n p j) :
    ∃ (w : G) (hw : w ∈ Subgroup.normalizer (Bs : Set G)),
      w ∈ ggG0 p B x L D J ∧
      MulAut.congr eta (ggConjAut Bs hw) = SpCoord.permAut (p := p) (Equiv.swap i0 j) ∧
      K = L.map (MulAut.conj w).toMonoidHom ∧
      (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p j := by
  let σ : Equiv.Perm (Fin n) := Equiv.swap i0 j
  have hP : SpCoord.permAut (p := p) σ ∈ bSignedFull n p :=
    Subgroup.subset_closure (Or.inr ⟨i0, j, hj.symm, rfl⟩)
  rw [← hEta] at hP
  obtain ⟨τ, hτ𝒦, hτP⟩ := Subgroup.mem_map.mp hP
  obtain ⟨w, hwG0, hw, hτw⟩ :=
    mem_ggAutomizer_iff.mp (FrameRoute.ggAutomizerJoin_le_ggG0 hR.2.2.2.1 hτ𝒦)
  have hτeq : ggConjAut Bs hw = τ :=
    MulEquiv.ext fun b => Subtype.ext ((ggConjAut_apply Bs hw b).trans (hτw b).symm)
  have hact : MulAut.congr eta (ggConjAut Bs hw) =
      SpCoord.permAut (p := p) (Equiv.swap i0 j) := by
    rw [hτeq]
    simpa [σ] using hτP
  obtain ⟨hKw, hAKB⟩ :=
    hR.eq_map_conj_of_sparse_of_swap hB hn eta i0 hLB hy hnb hj hyj hAK w hw hact
  exact ⟨w, hw, hwG0, hact, hKw, hAKB⟩

theorem GGSecFiveRouteCfg.exists_eq_map_conj_swap_of_sparse
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hB : B = Bs)
    {n : ℕ} (hn : 4 ≤ n) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (i0 : Fin n)
    (hEta : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (hLB : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    {y : G} (hy : y ∈ Bs) {K : Subgroup G} {j : Fin n} (hnb : GGNbr p B x D J y K)
    (hj : j ≠ i0) (hyj : ∀ k, k ≠ j → eta ⟨y, hy⟩ k = 1)
    (hAK : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p j ∨
      (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = dCoordinateBlock n p j) :
    ∃ (w : G) (hw : w ∈ Subgroup.normalizer (Bs : Set G)),
      MulAut.congr eta (ggConjAut Bs hw) = SpCoord.permAut (p := p) (Equiv.swap i0 j) ∧
      K = L.map (MulAut.conj w).toMonoidHom ∧
      (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p j := by
  obtain ⟨w, hw, -, hσ, hKw, hAKB⟩ :=
    hR.exists_ggG0_eq_map_conj_swap_of_sparse hB hn eta i0 hEta hLB hy hnb hj hyj hAK
  exact ⟨w, hw, hσ, hKw, hAKB⟩

theorem GGSecFiveRouteCfg.exists_eq_map_conj_of_sparse
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hB : B = Bs)
    {n : ℕ} (hn : 4 ≤ n) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (i0 : Fin n)
    (hEta : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (hLB : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    {y : G} (hy : y ∈ Bs) {K : Subgroup G} {j : Fin n} (hnb : GGNbr p B x D J y K)
    (hj : j ≠ i0) (hyj : ∀ k, k ≠ j → eta ⟨y, hy⟩ k = 1)
    (hAK : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p j ∨
      (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = dCoordinateBlock n p j) :
    ∃ w : G, w ∈ Subgroup.normalizer (Bs : Set G) ∧ K = L.map (MulAut.conj w).toMonoidHom ∧
      (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p j := by
  obtain ⟨w, hw, -, hKw, hAKB⟩ :=
    hR.exists_eq_map_conj_swap_of_sparse hB hn eta i0 hEta hLB hy hnb hj hyj hAK
  exact ⟨w, hw, hKw, hAKB⟩

private theorem nonempty_quotCenter_mulEquiv_map_conj {G : Type} [Group G] (L : Subgroup G)
    (w : G) : Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃*
      (↥(L.map (MulAut.conj w).toMonoidHom) ⧸
        Subgroup.center ↥(L.map (MulAut.conj w).toMonoidHom))) :=
  ⟨QuotientGroup.congr _ _ (L.equivMapOfInjective _ (MulAut.conj w).injective)
    (Subgroup.map_center_eq _)⟩

theorem ggSecFiveBCoordBSparseEndpointOn_holds (S : ℕ → ℕ → LargeEvenLabel → Prop) :
    GGSecFiveBCoordBSparseEndpointOn S := by
  intro G _ _ p B Bs x L D J 𝒦 hR n _ _ hn eta i0 hEta hLB _ hB _ y hy K j _ hnb hj hyj hAK
  obtain ⟨w, -, hKw, hAKB⟩ :=
    hR.exists_eq_map_conj_of_sparse hB (by omega) eta i0 hEta hLB hy hnb hj hyj hAK
  refine ⟨hAKB, ?_⟩
  subst hKw
  exact nonempty_quotCenter_mulEquiv_map_conj L w

theorem ggSecFiveBCoordBSparseEndpointFourOn_holds (S : ℕ → ℕ → LargeEvenLabel → Prop) :
    GGSecFiveBCoordBSparseEndpointFourOn S := by
  intro G _ _ p B Bs x L D J 𝒦 hR n _ _ hn eta i0 hEta hLB _ hB _ y hy K j _ hnb hj hyj hAK
  obtain ⟨w, -, hKw, hAKB⟩ :=
    hR.exists_eq_map_conj_of_sparse hB (by omega) eta i0 hEta hLB hy hnb hj hyj hAK
  refine ⟨hAKB, ?_⟩
  subst hKw
  exact nonempty_quotCenter_mulEquiv_map_conj L w

theorem GGSecFiveRouteCfg.nbr_axis_of_bCoordSparse
    {G : Type} [Group G] [Finite G] {p n : ℕ}
    {B Bs : Subgroup G} {x y : G} {L D J K : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hFC : GGResNbrFixCentralizesInput)
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hB : B = Bs) (hn : 4 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (i0 : Fin n)
    (hEta : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (hLB : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    (hSparse : GGSecFiveBCoordSparse eta i0 D)
    (hy : y ∈ Bs) (hnb : GGNbr p B x D J y K)
    (hKle : ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) :
    ∃ j : Fin n, j ≠ i0 ∧ (∀ k, k ≠ j → eta ⟨y, hy⟩ k = 1) ∧
      ((ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p j ∨
        (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = dCoordinateBlock n p j) := by
  classical
  have hcfg : GGConfig p B Bs x L D J := hR.1.1
  obtain ⟨hp, -, hxBs, -, -⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hxD : x ∈ D := hcfg.2.2.1.2.2.2.1
  obtain ⟨-, hyK, hyD, hyx, hx1⟩ := ggNbr_facts hcfg hnb
  have hx0 : ∀ k, k ≠ i0 → eta ⟨x, hxBs⟩ k = 1 := fun k hk =>
    CommonJ.eta_x_eq_one hcfg hB eta i0 hLB ⟨x, hxBs⟩ rfl hk
  have hx_i0 : eta ⟨x, hxBs⟩ i0 ≠ 1 := by
    intro h
    apply hx1
    have h1 : eta ⟨x, hxBs⟩ = 1 := by
      funext k
      by_cases hk : k = i0
      · subst hk
        exact h
      · exact hx0 k hk
    exact congrArg Subtype.val (eta.injective (h1.trans (map_one eta).symm))
  have hx0add : toAdd (eta ⟨x, hxBs⟩ i0) ≠ 0 := fun h =>
    hx_i0 (by rw [← ofAdd_toAdd (eta ⟨x, hxBs⟩ i0), h]; rfl)
  obtain ⟨m, hm⟩ := SpCoord.exists_natCast_mul_eq hp hx0add (toAdd (eta ⟨y, hy⟩ i0))
  have hxm : (eta ⟨x, hxBs⟩ i0) ^ m = eta ⟨y, hy⟩ i0 := by
    apply toAdd.injective
    rw [toAdd_pow, ← hm, nsmul_eq_mul]
  let z : ↥Bs := ⟨y * (x ^ m)⁻¹, Bs.mul_mem hy (Bs.inv_mem (Subgroup.pow_mem Bs hxBs m))⟩
  have hz_eq : z = ⟨y, hy⟩ * (⟨x, hxBs⟩ ^ m)⁻¹ := Subtype.ext (by simp [z])
  have hzmap : eta z = eta ⟨y, hy⟩ * ((eta ⟨x, hxBs⟩) ^ m)⁻¹ := by
    rw [hz_eq, map_mul, map_inv, map_pow]
  have hzi0 : eta z i0 = 1 := by
    rw [hzmap]
    simp [hxm]
  have hzy : ∀ k, k ≠ i0 → eta z k = eta ⟨y, hy⟩ k := by
    intro k hk
    rw [hzmap]
    simp [hx0 k hk]
  have hz1 : z ≠ 1 := by
    intro hz
    apply hyx
    have hval : y * (x ^ m)⁻¹ = 1 := by
      simpa [z] using congrArg Subtype.val hz
    have hy_eq : y = x ^ m := by
      calc y = y * (x ^ m)⁻¹ * (x ^ m) := by group
        _ = 1 * (x ^ m) := by rw [hval]
        _ = x ^ m := by group
    exact Subgroup.mem_zpowers_iff.mpr ⟨(m : ℤ), by rw [zpow_natCast]; exact hy_eq.symm⟩
  have hzD : (z : G) ∈ D := by
    simpa [z] using D.mul_mem hyD (D.inv_mem (Subgroup.pow_mem D hxD m))
  obtain ⟨i, hi0, hiz⟩ := hSparse z hzD hz1 hzi0
  have hk : ∃ k : Fin n, k ≠ i0 ∧ k ≠ i := by
    by_contra h
    have hsub : (Finset.univ : Finset (Fin n)) ⊆ {i0, i} := by
      intro k _
      by_cases hk : k = i0
      · simp [hk]
      · have hki : k = i := by
          by_contra hki
          exact h ⟨k, hk, hki⟩
        simp [hki]
    have hle := Finset.card_le_card hsub
    rw [Finset.card_univ, Fintype.card_fin] at hle
    have h2 : ({i0, i} : Finset (Fin n)).card ≤ 2 := by
      simpa using Finset.card_insert_le i0 ({i} : Finset (Fin n))
    omega
  obtain ⟨k, hk0, hki⟩ := hk
  have hyk : eta ⟨y, hy⟩ k = 1 := by
    rw [← hzy k hk0]
    exact hiz k hk0 hki
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := by
    intro κ hκ
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hyK κ hκ)
  have hfix : ∀ w ∈ (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom,
      w (eta ⟨y, hy⟩) = eta ⟨y, hy⟩ :=
    (forall_map_congr_fix_iff eta (ggAutomizer K Bs) ⟨y, hy⟩).2
      (ggRC_automizer_fixes_y hy hKy)
  rcases hR.nbr_coordType hX hTCJ hRig hTPn hA8 hraw hiso hFC hB eta hEta hnb hKle with
    ⟨j, hj⟩ | ⟨δ, hδ, hS⟩
  · have hfix_axis : ∀ k, k ≠ j → eta ⟨y, hy⟩ k = 1 := by
      rcases hj with h | h
      · rw [h] at hfix
        exact (forall_bCoordinateBlock_fix_iff hp hp2 j _).1 hfix
      · rw [h] at hfix
        exact (forall_dCoordinateBlock_fix_iff hp hp2 (by omega) j _).1 hfix
    have hjne : j ≠ i0 := by
      rintro rfl
      have hmem := mem_zpowers_of_axis (G := G) eta hx0 hfix_axis hx_i0
      exact hyx (by simpa using hmem)
    exact ⟨j, hjne, hfix_axis, hj⟩
  ·
    rw [hS] at hfix
    obtain ⟨c, hc⟩ := exists_const_of_forall_map_conj_aPermutationFull_fix δ hfix
    obtain ⟨ε, hε, hconst⟩ := exists_signs_apply_const hδ
    have hεc : ε k * c = 0 := by
      rw [← hconst c k, ← hc, hyk, toAdd_one]
    have hc0 : c = 0 :=
      (mul_eq_zero.mp hεc).resolve_left
        (SpCoord.coord_sign_ne_zero hp (hε k))
    have h1 : eta ⟨y, hy⟩ = 1 := by
      rw [hc, hc0]
      exact map_one δ
    exfalso
    exact hnb.1.2.2.1 (congrArg Subtype.val ((MulEquiv.map_eq_one_iff eta).1 h1))

theorem GGSecFiveRouteCfg.exists_ggG0_eq_map_conj_swap_of_bCoordSparse
    {G : Type} [Group G] [Finite G] {p n : ℕ}
    {B Bs : Subgroup G} {x y : G} {L D J K : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hFC : GGResNbrFixCentralizesInput)
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hB : B = Bs) (hn : 4 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (i0 : Fin n)
    (hEta : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (hLB : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    (hSparse : GGSecFiveBCoordSparse eta i0 D)
    (hy : y ∈ Bs) (hnb : GGNbr p B x D J y K)
    (hKle : ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) :
    ∃ (j : Fin n) (_hj : j ≠ i0),
      (∀ k, k ≠ j → eta ⟨y, hy⟩ k = 1) ∧
      ∃ (w : G) (hw : w ∈ Subgroup.normalizer (Bs : Set G)),
        w ∈ ggG0 p B x L D J ∧
        MulAut.congr eta (ggConjAut Bs hw) = SpCoord.permAut (p := p) (Equiv.swap i0 j) ∧
        K = L.map (MulAut.conj w).toMonoidHom ∧
        (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p j := by
  obtain ⟨j, hj, hyj, hAK⟩ :=
    GGSecFiveRouteCfg.nbr_axis_of_bCoordSparse hX hTCJ hRig hTPn hA8 hraw hiso hFC hR hB hn
      eta i0 hEta hLB hSparse hy hnb hKle
  obtain ⟨w, hw, hwG0, hσ, hKw, hAKB⟩ :=
    hR.exists_ggG0_eq_map_conj_swap_of_sparse hB hn eta i0 hEta hLB hy hnb hj hyj hAK
  exact ⟨j, hj, hyj, w, hw, hwG0, hσ, hKw, hAKB⟩

theorem GGSecFiveRouteCfg.ggG0_le_of_bCoordSparse_of_swap_lifts
    {G : Type} [Group G] [Finite G] {p n : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hFC : GGResNbrFixCentralizesInput)
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hB : B = Bs) (hn : 4 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (i0 : Fin n)
    (hEta : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (hLB : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    (hSparse : GGSecFiveBCoordSparse eta i0 D)
    (hRM : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (H : Subgroup G) (hLH : L ≤ H)
    (hLift : ∀ j : Fin n, j ≠ i0 → ∃ (w : G), w ∈ H ∧
      ∃ (hw : w ∈ Subgroup.normalizer (Bs : Set G)),
        MulAut.congr eta (ggConjAut Bs hw) = SpCoord.permAut (p := p) (Equiv.swap i0 j)) :
    ggG0 p B x L D J ≤ H := by
  refine ggG0_le_of hLH ?_
  intro y K hnb
  have hy : y ∈ Bs := hB ▸ hnb.1.2.1
  obtain ⟨j, hj, hyj, hAK⟩ :=
    GGSecFiveRouteCfg.nbr_axis_of_bCoordSparse hX hTCJ hRig hTPn hA8 hraw hiso hFC hR hB hn
      eta i0 hEta hLB hSparse hy hnb (hRM y K hnb)
  obtain ⟨w, hwH, hw, hact⟩ := hLift j hj
  obtain ⟨hKw, -⟩ :=
    hR.eq_map_conj_of_sparse_of_swap hB hn eta i0 hLB hy hnb hj hyj hAK w hw hact
  rw [hKw]
  rintro z ⟨a, haL, rfl⟩
  change w * a * w⁻¹ ∈ H
  exact H.mul_mem (H.mul_mem hwH (hLH haL)) (H.inv_mem hwH)

theorem GGSecFiveRouteCfg.ggG0_eq_sup_range_of_permHom
    {G : Type} [Group G] [Finite G] {p k : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)}
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown)
    (hRig : GGLabelRigidInput) (hTPn : GGNbrTablePNbrInputNarrow)
    (hA8 : GGForkA8NotReflInput) (hraw : GGRawInnFieldInput)
    (hiso : GGRawInndiagIsoInput) (hFC : GGResNbrFixCentralizesInput)
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hB : B = Bs)
    (eta : ↥Bs ≃* (Fin (k + 4) → Multiplicative (ZMod p)))
    (i0 : Fin (k + 4))
    (hSigned : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom =
      bSignedFull (k + 4) p)
    (hAL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom =
      bCoordinateBlock (k + 4) p i0)
    (hSparse : GGSecFiveBCoordSparse eta i0 D)
    (hRM : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (w : G) (hwG0 : w ∈ ggG0 p B x L D J)
    (π : Fin (k + 4) ≃ Fin (k + 4))
    (f g : Equiv.Perm (Fin (k + 3)) →* G)
    (t : Equiv.Perm (Fin (k + 4)) →* G)
    (htf : t.comp (Equiv.Perm.viaEmbeddingHom
      (Fin.castSuccEmb : Fin (k + 3) ↪ Fin (k + 4))) = f)
    (htg : t.comp (Equiv.Perm.viaEmbeddingHom (Fin.succEmb (k + 3))) = g)
    (hfL : f.range ≤ L)
    (hgLw : g.range ≤ L.map (MulAut.conj w).toMonoidHom)
    (hfN : ∀ σ, f σ ∈ Subgroup.normalizer (Bs : Set G))
    (hgN : ∀ σ, g σ ∈ Subgroup.normalizer (Bs : Set G))
    (hfAct : ∀ σ, MulAut.congr eta (ggConjAut Bs (hfN σ)) =
      SpCoord.permAut (p := p) (π.permCongr (Equiv.Perm.viaEmbeddingHom
        (Fin.castSuccEmb : Fin (k + 3) ↪ Fin (k + 4)) σ)))
    (hgAct : ∀ σ, MulAut.congr eta (ggConjAut Bs (hgN σ)) =
      SpCoord.permAut (p := p) (π.permCongr
        (Equiv.Perm.viaEmbeddingHom (Fin.succEmb (k + 3)) σ))) :
    ggG0 p B x L D J = L ⊔ t.range := by
  let ρ : Equiv.Perm (Fin (k + 4)) →* MulAut ↥Bs :=
    ((MulAut.congr eta).symm.toMonoidHom.comp (ggSpSigned_permAutHom p (k + 4))).comp
      π.permCongrHom.toMonoidHom
  have hρ : ∀ σ : Equiv.Perm (Fin (k + 4)),
      ρ σ = (MulAut.congr eta).symm (SpCoord.permAut (p := p) (π.permCongr σ)) := by
    intro σ
    rfl
  have hconv : ∀ (z : G) (hz : z ∈ Subgroup.normalizer (Bs : Set G)),
      Bs.normalizerMonoidHom ⟨z, hz⟩ = ggConjAut Bs hz := by
    intro z hz
    ext b
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, ggConjAut_apply]
  have hfρ : ∀ σ, Bs.normalizerMonoidHom ⟨f σ, hfN σ⟩ =
      ρ (Equiv.Perm.viaEmbeddingHom
        (Fin.castSuccEmb : Fin (k + 3) ↪ Fin (k + 4)) σ) := by
    intro σ
    rw [hconv (f σ) (hfN σ)]
    apply (MulAut.congr eta).injective
    rw [hfAct σ, hρ]
    exact (MulEquiv.apply_symm_apply _ _).symm
  have hgρ : ∀ σ, Bs.normalizerMonoidHom ⟨g σ, hgN σ⟩ =
      ρ (Equiv.Perm.viaEmbeddingHom (Fin.succEmb (k + 3)) σ) := by
    intro σ
    rw [hconv (g σ) (hgN σ)]
    apply (MulAut.congr eta).injective
    rw [hgAct σ, hρ]
    exact (MulEquiv.apply_symm_apply _ _).symm
  obtain ⟨ht, htρ⟩ :=
    CFSG.Permutation.SymmetricCoxeter.normalizer_action_of_restrictions Bs f g t
      htf htg ρ hfN hgN hfρ hgρ
  have htAct : ∀ σ, MulAut.congr eta (ggConjAut Bs (ht σ)) =
      SpCoord.permAut (p := p) (π.permCongr σ) := by
    intro σ
    rw [← hconv (t σ) (ht σ), htρ σ, hρ]
    exact MulEquiv.apply_symm_apply _ _
  have hconjL : L.map (MulAut.conj w).toMonoidHom ≤ ggG0 p B x L D J := by
    rintro z ⟨a, haL, rfl⟩
    change w * a * w⁻¹ ∈ ggG0 p B x L D J
    exact (ggG0 p B x L D J).mul_mem
      ((ggG0 p B x L D J).mul_mem hwG0 (le_ggG0_left p B x L D J haL))
      ((ggG0 p B x L D J).inv_mem hwG0)
  have hHle : L ⊔ t.range ≤ ggG0 p B x L D J := by
    rw [CFSG.Permutation.SymmetricCoxeter.range_eq_sup htf htg]
    exact sup_le (le_ggG0_left p B x L D J)
      (sup_le (hfL.trans (le_ggG0_left p B x L D J)) (hgLw.trans hconjL))
  refine le_antisymm ?_ hHle
  refine GGSecFiveRouteCfg.ggG0_le_of_bCoordSparse_of_swap_lifts hX hTCJ hRig hTPn hA8 hraw
    hiso hFC hR hB (by omega) eta i0 hSigned hAL hSparse hRM (L ⊔ t.range) le_sup_left ?_
  intro j hj
  let σ : Equiv.Perm (Fin (k + 4)) := π.permCongr.symm (Equiv.swap i0 j)
  have hσ : π.permCongr σ = Equiv.swap i0 j := π.permCongr.apply_symm_apply _
  exact ⟨t σ, Subgroup.mem_sup_right ⟨σ, rfl⟩, ht σ, by rw [htAct σ, hσ]⟩

theorem GGSecFiveRouteCfg.bCoordSparse_of_no_denseNbr
    {G : Type} [Group G] [Finite G] {p n : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hFC : GGResNbrFixCentralizesInput)
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hB : B = Bs) (hn : 4 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (i0 : Fin n)
    (hSigned : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom =
      bSignedFull n p)
    (hAL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom =
      bCoordinateBlock n p i0)
    (hLab : GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab) p Bs L)
    (hNoDense : ¬ ∃ K : Subgroup G, GGSecFiveBCoordBDenseNbr p Bs 𝒦 n eta K) :
    GGSecFiveBCoordSparse eta i0 D := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  obtain ⟨K, hKmem, hKL⟩ :=
    exists_mem_not_le_ggAutomizer_of_bSignedFull hp hp2 eta hSigned hAL
  obtain ⟨y, hnb⟩ := hR.2.2.2.1.2 K hKmem
  have hy : y ∈ Bs := (ggNbr_facts hR.1.1 hnb).1
  have hyD : y ∈ D := (ggNbr_facts hR.1.1 hnb).2.2.1
  have hy1 : y ≠ 1 := hnb.1.2.2.1
  have hKle : ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦 :=
    ggAutomizer_le_ggAutomizerJoin (Or.inr hKmem)
  rcases hR.nbr_axis_or_dense hX hTCJ hRig hTPn hA8 hraw hiso hFC hB (by omega) eta
      hSigned hAL hnb hKle hKL hy with
    ⟨j, hj, -, hax⟩ | ⟨hDelta, -⟩
  · obtain ⟨lab, hLambda, hHas, _, _, _, _, _, hPred⟩ :=
      largeEvenMarking_exists_hasLabel
        (ggSecFiveBCoordBCommonJCoreInput_holds G p B Bs x L D J hR.1.1 hB n hn eta i0
          hAL hLab)
    rcases hPred.1.2 with ⟨hDense, -⟩ | ⟨hSparse, -⟩
    · obtain ⟨k, hk0, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i0 j (by omega)
      have hz1 : (⟨y, hy⟩ : ↥Bs) ≠ 1 := fun hz => hy1 (congrArg Subtype.val hz)
      have hi0 : eta ⟨y, hy⟩ i0 = 1 := hax i0 (Ne.symm hj)
      exact ((hDense ⟨y, hy⟩ hyD hz1 hi0 k hk0).1 (hax k hkj)).elim
    · exact hSparse
  · exact (hNoDense ⟨K, hKmem, hDelta⟩).elim

end CFSG.StandardType

end

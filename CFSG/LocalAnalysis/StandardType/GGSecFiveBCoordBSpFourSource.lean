module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpPlaneBlocks
import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitzExcComp
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizeSwap
import CFSG.LocalAnalysis.StandardType.GGSpJoinBstarSplit
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpKFrame
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniBlocks
import CFSG.LocalAnalysis.StandardType.GGSecFiveBSpCoordFrameFacts
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneConjSplit
import CFSG.LocalAnalysis.StandardType.GGTPNDefs
import CFSG.LocalAnalysis.StandardType.GGTypeAFarPComp
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeModel
import CFSG.LocalAnalysis.SteinbergSFSingleCommRootStandardClosure
import CFSG.LocalAnalysis.ComponentInitial.EscapingNotAlternating

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open scoped MatrixGroups
open CFSG.SeitzReduction.SymplecticPilot (diagSp)

private theorem original_J_eq_range_of_coordD
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : 4 ≤ Nat.card F)
    {B Bs L D J : Subgroup G} {x : G} (hcfg : GGConfig p B Bs x L D J)
    {eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod p))} {π : Fin 4 ≃ Fin 4}
    {κ : StatedSp 3 F →* G} {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hframe : GGSecFiveBPermSpPlaneFrame Bs L eta π κ ζ)
    (σ : Fin 2 → Fin 3) (hσ : Function.Injective σ)
    (hD : D = ggBsCoordZeroOn Bs eta (Set.range fun l => π (σ l).succ)) :
    J = (κ.comp (spEmbed (K := F) σ hσ)).range := by
  let C : Subgroup G := L ⊓ Subgroup.centralizer (D : Set G)
  have hJC : CFSG.Assembly.IsComponentOf J C := hcfg.2.2.1.2.2.2.2.2.1
  have hder : ⁅C, C⁆ = (κ.comp (spEmbed (K := F) σ hσ)).range := by
    simpa only [C, hD] using
      hframe.commutator_inf_centralizer_eq_range hp2 (Or.inl hF) σ hσ
  have : IsSimpleGroup (StatedSp 2 F) :=
    CFSG.SeitzReduction.SymplecticPilot.isSimpleGroup_statedSp_of_four_le hF (by decide)
  have hκσ : Function.Injective (κ.comp (spEmbed (K := F) σ hσ)) := by
    intro a b h
    apply spEmbed_injective hσ
    exact hframe.1 h
  let e : StatedSp 2 F ≃* (κ.comp (spEmbed (K := F) σ hσ)).range :=
    MonoidHom.ofInjective hκσ
  have hRsimple : IsSimpleGroup (κ.comp (spEmbed (K := F) σ hσ)).range :=
    e.symm.isSimpleGroup
  have hCsimple : IsSimpleGroup ↥(⁅C, C⁆ : Subgroup G) := by
    rw [hder]
    exact hRsimple
  exact (ggComponent_eq_commutator hJC hCsimple).trans hder


private theorem range_plane_complement (π : Fin 4 ≃ Fin 4) (i : Fin 3) :
    Set.range (fun l : Fin 2 => π (i.succAbove l).succ) =
      ({π 0, π i.succ} : Set (Fin 4))ᶜ := by
  ext x
  constructor
  · rintro ⟨l, rfl⟩
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · intro h
      have hv := congrArg Fin.val (π.injective h)
      simp only [Fin.val_succ, Fin.val_zero] at hv
      omega
    · intro h
      have heq : i.succAbove l = i := by simpa using π.injective h
      exact (Fin.succAbove_ne i l) heq
  · intro hx
    have hx0 : x ≠ π 0 := by intro h; subst x; exact hx (by simp)
    have hxi : x ≠ π i.succ := by intro h; subst x; exact hx (by simp)
    have hnonzero : π.symm x ≠ 0 := by
      intro h
      apply hx0
      rw [← π.apply_symm_apply x, h]
    have hr : π.symm x ∈ Set.range (Fin.succ : Fin 3 → Fin 4) := by
      rw [Fin.range_succ]
      exact hnonzero
    obtain ⟨u, hu⟩ := hr
    have hui : u ≠ i := by
      intro h
      apply hxi
      rw [← π.apply_symm_apply x, ← hu, h]
    have hru : u ∈ Set.range i.succAbove := by
      rw [Fin.range_succAbove]
      exact hui
    obtain ⟨l, hl⟩ := hru
    exact ⟨l, by
      change π (i.succAbove l).succ = x
      rw [hl, hu, π.apply_symm_apply]⟩

private theorem coord_ne_one_of_axis {G : Type} [Group G] {p n : ℕ} {Bs : Subgroup G}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (b : ↥Bs) (hb : b ≠ 1)
    (i : Fin n) (hoff : ∀ k, k ≠ i → eta b k = 1) : eta b i ≠ 1 := by
  intro hi
  apply hb
  apply (MulEquiv.map_eq_one_iff eta).mp
  funext k
  by_cases hki : k = i
  · subst k
    exact hi
  · exact hoff k hki

private theorem exists_fin3_succ_eq_of_apply_zero_eq {π : Fin 4 ≃ Fin 4} {i0 j : Fin 4}
    (hπ0 : π 0 = i0) (hj0 : j ≠ i0) : ∃ i : Fin 3, π i.succ = j := by
  have hjnonzero : π.symm j ≠ 0 := by
    intro h
    apply hj0
    rw [← π.apply_symm_apply j, h, hπ0]
  have hjrange : π.symm j ∈ Set.range (Fin.succ : Fin 3 → Fin 4) := by
    rw [Fin.range_succ]
    exact hjnonzero
  obtain ⟨i, hi⟩ := hjrange
  exact ⟨i, by rw [hi, π.apply_symm_apply]⟩

theorem GGConfig.J_eq_blockComm_and_exists_range_spEmbed
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : 4 ≤ Nat.card F)
    {B Bs L D J : Subgroup G} {x y : G} {K : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hnb : GGNbr p B x D J y K)
    (eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod p))) {i0 j : Fin 4} (hj0 : j ≠ i0)
    (hAL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock 4 p i0)
    (hAK : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock 4 p j)
    {π : Fin 4 ≃ Fin 4} {κ : StatedSp 3 F →* G}
    {ζ : Multiplicative (ZMod p) →* SL(2, F)} (hπ0 : π 0 = i0)
    (hframe : GGSecFiveBPermSpPlaneFrame Bs L eta π κ ζ) :
    J = ggBlockComm Bs eta ({i0, j} : Set (Fin 4))ᶜ ∧
      ∃ i : Fin 3, π i.succ = j ∧
        J = (κ.comp (spEmbed (K := F) i.succAbove Fin.succAbove_right_injective)).range := by
  obtain ⟨hp, hp2, -⟩ := (hcfg.1.2.2.2.2.2.1 : p ∈ LargeEvenBeta 4 G)
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hBsEA, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have hx1 : x ≠ 1 := hcfg.1.2.2.2.2.2.2.1.2.2.1
  have hyBs : y ∈ Bs := hcfg.2.1.1 hnb.1.2.1
  have hy1 : y ≠ 1 := hnb.1.2.2.1
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := hnb.1.2.2.2.1
  have hxoff : ∀ k, k ≠ i0 → eta ⟨x, hxBs⟩ k = 1 :=
    ggBs_coord_eq_one_of_mem_bCoordinateBlock hp hp2 hxBs hLx eta i0 hAL
  have hyoff : ∀ k, k ≠ j → eta ⟨y, hyBs⟩ k = 1 :=
    ggBs_coord_eq_one_of_mem_bCoordinateBlock hp hp2 hyBs hKy eta j hAK
  have hxaxis : eta ⟨x, hxBs⟩ i0 ≠ 1 :=
    coord_ne_one_of_axis eta ⟨x, hxBs⟩ (fun h => hx1 (congrArg Subtype.val h)) i0 hxoff
  have hyaxis : eta ⟨y, hyBs⟩ j ≠ 1 :=
    coord_ne_one_of_axis eta ⟨y, hyBs⟩ (fun h => hy1 (congrArg Subtype.val h)) j hyoff
  have hpair : Subgroup.closure ({x, y} : Set G) = Subgroup.zpowers x ⊔ Subgroup.zpowers y :=
    closure_pair_eq_sup x y
  have hD : D = ggBsCoordZeroOn Bs eta ({i0, j} : Set (Fin 4))ᶜ :=
    hnb.2.1.trans (hpair.trans
      (ggBsCoordZeroOn_pair_compl_eq_sup_zpowers eta hxBs hyBs hj0.symm
        hxaxis hyaxis hxoff hyoff).symm)
  obtain ⟨i, hπi⟩ := exists_fin3_succ_eq_of_apply_zero_eq hπ0 hj0
  have hS : Set.range (fun l : Fin 2 => π (i.succAbove l).succ) =
      ({i0, j} : Set (Fin 4))ᶜ := by
    rw [range_plane_complement, hπ0, hπi]
  have hD' : D = ggBsCoordZeroOn Bs eta (Set.range fun l : Fin 2 => π (i.succAbove l).succ) := by
    rw [hS]
    exact hD
  have hJrange := original_J_eq_range_of_coordD hp2 hF hcfg hframe
    i.succAbove Fin.succAbove_right_injective hD'
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hcfg.2.1.2.2.2
  have hLcomp : CFSG.Open.IsComponentOf L (Subgroup.centralizer ({x} : Set G)) :=
    CFSG.Assembly.isComponentOf_iff_open.mp hcfg.1.2.2.2.2.2.2.1.2.2.2.1
  have hσs : ¬ Function.Surjective i.succAbove := by
    intro h
    obtain ⟨a, ha⟩ := h i
    exact (Fin.succAbove_ne i a) ha
  have hblock := ggSecFiveBPermZeta_commutator_centralizer_eq hp2 hF hSC hxBs hLcomp hframe
    i.succAbove Fin.succAbove_right_injective hσs
  rw [hS] at hblock
  exact ⟨hJrange.trans hblock.symm, i, hπi, hJrange⟩


private theorem native_longRoot_component
    {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : 4 ≤ Nat.card F) (t : Fin n → Fˣ) (k : Fin n)
    (hk : t k = 1) (ht : ∀ i, i ≠ k → t i ≠ 1) :
    IsComponentOf (longRootSp2 F n k) (Subgroup.centralizer {diagSp F n t}) := by
  have hQC := CFSG.SeitzReduction.SymplecticPilot.longRootSp2_le_centralizer_diagSp t k hk
  have hQN := CFSG.SeitzReduction.SymplecticPilot.longRootSp2_normal_subgroupOf_centralizer_diagSp
    t k hk ht
  refine ⟨hQC, IsSubnormal.step hQC hQN (IsSubnormal.refl _), ?_⟩
  exact CFSG.LocalAnalysis.SymplecticFourStandard.RootStandard.isQuasisimple_of_sl2 hF
    (MonoidHom.ofInjective (longBlock_injective k))

private theorem component_longRoot_image_of_component_range
    {G : Type} [Group G] {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : 4 ≤ Nat.card F) (κ : StatedSp n F →* G) (hκ : Function.Injective κ)
    {e d : G} (hM : IsComponentOf κ.range (Subgroup.centralizer {e}))
    (t : Fin n → Fˣ) (k : Fin n) (hk : t k = 1)
    (ht : ∀ i, i ≠ k → t i ≠ 1) (hd : κ (diagSp F n t) = d) :
    IsComponentOf ((longRootSp2 F n k).map κ)
      (Subgroup.centralizer {d} ⊓ Subgroup.centralizer {e}) := by
  have hQ := isComponentOf_map_of_injective κ hκ (native_longRoot_component hF t k hk ht)
  rw [CFSG.LocalAnalysis.ComponentInitial.map_centralizer_singleton_of_injective hκ, hd] at hQ
  have hs := hM.2.1.inf (Subgroup.centralizer {d})
  rw [inf_comm (Subgroup.centralizer {e})] at hs
  exact ⟨fun z hz => ⟨(hQ.1 hz).2, hM.1 (hQ.1 hz).1⟩, hQ.2.1.trans hs, hQ.2.2⟩

private theorem component_longRoot_image_of_original
    {G : Type} [Group G] {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : 4 ≤ Nat.card F) (κ : StatedSp n F →* G) (hκ : Function.Injective κ)
    {L : Subgroup G} {x d : G} (hκL : κ.range = L)
    (hL : IsComponentOf L (Subgroup.centralizer {x})) (g : G)
    (t : Fin n → Fˣ) (k : Fin n) (hk : t k = 1)
    (ht : ∀ i, i ≠ k → t i ≠ 1) (hd : g * κ (diagSp F n t) * g⁻¹ = d) :
    IsComponentOf (((longRootSp2 F n k).map κ).map (MulAut.conj g).toMonoidHom)
      (Subgroup.centralizer {d} ⊓ Subgroup.centralizer {g * x * g⁻¹}) := by
  let κ₁ := (MulAut.conj g).toMonoidHom.comp κ
  have hM := isComponentOf_map_of_injective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective hL
  rw [CFSG.LocalAnalysis.ComponentInitial.map_centralizer_singleton_of_injective
    (MulAut.conj g).injective] at hM
  have htop : (MulAut.conj g).toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top.mpr (MulAut.conj g).surjective
  simp only [htop, top_inf_eq] at hM
  have hM' : IsComponentOf κ₁.range (Subgroup.centralizer {g * x * g⁻¹}) := by
    simpa only [κ₁, MonoidHom.range_comp, hκL, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hM
  have h := component_longRoot_image_of_component_range hF κ₁
    ((MulAut.conj g).injective.comp hκ) hM' t k hk ht hd
  simpa only [κ₁, Subgroup.map_map] using h

private theorem eta_conjAut_symm_apply {G : Type} [Group G] {p n : ℕ} {Bs : Subgroup G}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {g : G}
    (hg : g ∈ Subgroup.normalizer (Bs : Set G)) {τ : Equiv.Perm (Fin n)}
    (hτ : MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut τ) :
    ∀ b : ↥Bs, ∀ i, eta ((ggConjAut Bs hg).symm b) i = eta b (τ i) := by
  intro b i
  have h := eta_ggConjAut_apply_of_permAut hg hτ ((ggConjAut Bs hg).symm b) i
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

private theorem conj_diagSp_of_two_support
    {G : Type} [Group G] [Finite G] {p f : ℕ}
    {B Bs L D J : Subgroup G} {x : G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod p)))
    {π : Fin 4 ≃ Fin 4} {κ : StatedSp 3 (GaloisField 2 f) →* G}
    {χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}
    {i0 j u : Fin 4} (hju : j ≠ u) (hu0 : u ≠ i0)
    (hF : 4 ≤ Nat.card (GaloisField 2 f)) (hπ0 : π 0 = i0)
    (hAL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock 4 p i0)
    (hFL : GGSecFiveBPermSpKFrame Bs L eta π κ χ)
    {g : G} (hg : g ∈ Subgroup.normalizer (Bs : Set G))
    (hτ : MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut (Equiv.swap i0 u))
    (d : ↥Bs) (hdoff : ∀ k, k ≠ i0 → k ≠ j → eta d k = 1) :
    g * κ (diagSp (GaloisField 2 f) 3
        (fun i => χ (eta ((ggConjAut Bs hg).symm d) (π i.succ)))) * g⁻¹ = (d : G) := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  let : Fact p.Prime := ⟨hp⟩
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hBs, hxBs, hLx, -⟩ := hR.1.1.tableB_facts
  have hx1 : x ≠ 1 := hR.1.1.1.2.2.2.2.2.2.1.2.2.1
  have hSC : ∀ a ∈ Subgroup.centralizer (Bs : Set G), a ^ p = 1 → a ∈ Bs :=
    hR.1.1.2.1.2.2.2
  let φ : MulAut ↥Bs := ggConjAut Bs hg
  let a : ↥Bs := φ.symm d
  let w : Fin 3 → Multiplicative (ZMod p) := fun i => eta a (π i.succ)
  have hact : ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = g * b * g⁻¹ := by intro b; rfl
  have ha0 : eta a (π 0) = 1 := by
    rw [hπ0, eta_conjAut_symm_apply eta hg hτ, Equiv.swap_apply_left]
    exact hdoff u hu0 hju.symm
  have hη : ((Fin.cases 1 w) ∘ π.symm) = eta a := by
    funext k
    obtain ⟨i, rfl⟩ := π.surjective k
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
    exact Fin.cases ha0.symm (fun _ => rfl) i
  have hT := hFL.toPlaneFrame.spPlaneTorus_eq_coordinate hp2 hF hBs hSC hxBs hx1 hLx
    (ggInnerDiagOn_le_normalizer hR.1.2.2.1.1) (by rw [hπ0]; exact hAL) w
  rw [SpJoin.spPlaneTorus_sl2Diag_comp_apply, hη, eta.symm_apply_apply] at hT
  change g * κ (diagSp (GaloisField 2 f) 3 (fun i => χ (w i))) * g⁻¹ = (d : G)
  rw [hT, ← hact a, φ.apply_symm_apply]

private theorem chi_eta_succ_eq_one_iff
    {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G}
    (eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod p)))
    {M : Type} [Monoid M] {χ : Multiplicative (ZMod p) →* M}
    {g : G} (hg : g ∈ Subgroup.normalizer (Bs : Set G))
    {i0 j u v : Fin 4} (hj0 : j ≠ i0) (hju : j ≠ u) (hjv : j ≠ v)
    (huv : u ≠ v) (hu0 : u ≠ i0) (hv0 : v ≠ i0)
    {π : Fin 4 ≃ Fin 4} {iv : Fin 3} (hπ0 : π 0 = i0) (hiv' : π iv.succ = v)
    (hτ : MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut (Equiv.swap i0 u))
    (hχ : Function.Injective χ)
    (d : ↥Bs) (hd0 : eta d i0 ≠ 1) (hdj : eta d j ≠ 1)
    (hdoff : ∀ k, k ≠ i0 → k ≠ j → eta d k = 1) :
    ∀ i : Fin 3, χ (eta ((ggConjAut Bs hg).symm d) (π i.succ)) = 1 ↔ i = iv := by
  intro i
  constructor
  · intro hi
    by_contra hni
    have hw : eta ((ggConjAut Bs hg).symm d) (π i.succ) = 1 :=
      hχ (hi.trans (map_one χ).symm)
    rw [eta_conjAut_symm_apply eta hg hτ] at hw
    have h0 : π i.succ ≠ i0 := by
      intro h
      have hh := π.injective (h.trans hπ0.symm)
      have hv := congrArg Fin.val hh
      simp at hv
    have hnv : π i.succ ≠ v := by
      intro h
      apply hni
      simpa using π.injective (h.trans hiv'.symm)
    have hτu : Equiv.swap i0 u (π i.succ) ≠ u := by
      intro h
      apply h0
      exact (Equiv.swap i0 u).injective
        (h.trans (Equiv.swap_apply_left i0 u).symm)
    have hτv : Equiv.swap i0 u (π i.succ) ≠ v := by
      intro h
      apply hnv
      exact (Equiv.swap i0 u).injective
        (h.trans (Equiv.swap_apply_of_ne_of_ne hv0 huv.symm).symm)
    have hfour : ∀ k : Fin 4, k = i0 ∨ k = j ∨ k = u ∨ k = v := by
      intro k
      omega
    rcases hfour (Equiv.swap i0 u (π i.succ)) with h | h | h | h
    · rw [h] at hw; exact hd0 hw
    · rw [h] at hw; exact hdj hw
    · exact hτu h
    · exact hτv h
  · intro hi
    subst hi
    rw [hiv', eta_conjAut_symm_apply eta hg hτ,
      Equiv.swap_apply_of_ne_of_ne hv0 huv.symm, hdoff v hv0 hjv.symm, map_one]

theorem GGSecFiveRouteCfg.isComponentOf_singleton_of_two_support
    {G : Type} [Group G] [Finite G] {p f : ℕ} (hf : 2 ≤ f)
    {B Bs L D J : Subgroup G} {x : G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod p)))
    {π : Fin 4 ≃ Fin 4} {κ : StatedSp 3 (GaloisField 2 f) →* G}
    {χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}
    {i0 j u v : Fin 4} (hj0 : j ≠ i0) (hju : j ≠ u) (hjv : j ≠ v)
    (huv : u ≠ v) (hu0 : u ≠ i0) (hv0 : v ≠ i0)
    (hπ0 : π 0 = i0)
    (hAL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock 4 p i0)
    (hFL : GGSecFiveBPermSpKFrame Bs L eta π κ χ)
    {g : G} (hg : g ∈ Subgroup.normalizer (Bs : Set G))
    (hτ : MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut (Equiv.swap i0 u))
    (d : ↥Bs) (hd0 : eta d i0 ≠ 1) (hdj : eta d j ≠ 1)
    (hdoff : ∀ k, k ≠ i0 → k ≠ j → eta d k = 1) :
    IsComponentOf ⁅Subgroup.centralizer (ggBsCoordZero Bs eta v : Set G), Bs⁆
      (Subgroup.centralizer {(d : G)} ⊓ Subgroup.centralizer {g * x * g⁻¹}) := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  let : Fact p.Prime := ⟨hp⟩
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : 4 ≤ Nat.card (GaloisField 2 f) := ggSecFiveBFour_le_card_galois hf
  obtain ⟨-, hBs, hxBs, hLx, -⟩ := hR.1.1.tableB_facts
  have hx1 : x ≠ 1 := hR.1.1.1.2.2.2.2.2.2.1.2.2.1
  have hLcomp : IsComponentOf L (Subgroup.centralizer {x}) :=
    hR.1.1.1.2.2.2.2.2.2.1.2.2.2.1
  have hSC : ∀ a ∈ Subgroup.centralizer (Bs : Set G), a ^ p = 1 → a ∈ Bs :=
    hR.1.1.2.1.2.2.2
  let τ : Equiv.Perm (Fin 4) := Equiv.swap i0 u
  let φ : MulAut ↥Bs := ggConjAut Bs hg
  have hact : ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = g * b * g⁻¹ := by intro b; rfl
  have he1 : g * x * g⁻¹ ∈ Bs := by rw [← hact ⟨x, hxBs⟩]; exact (φ ⟨x, hxBs⟩).2
  let κ₁ : StatedSp 3 (GaloisField 2 f) →* G := (MulAut.conj g).toMonoidHom.comp κ
  let M : Subgroup G := L.map (MulAut.conj g).toMonoidHom
  have hFM : GGSecFiveBPermSpKFrame Bs M eta (π.trans τ) κ₁ χ :=
    hFL.conj_transporter φ g τ hact
      (fun b i => eta_ggConjAut_apply_of_permAut hg hτ b i)
  have hPL : LargeEvenPComponent p (Subgroup.centralizer {x}) L :=
    hR.largeEvenPComponent_L (GGSecFiveBPermSpKFrame.prime_dvd_card hp hFL)
  have hPM : LargeEvenPComponent p (Subgroup.centralizer {g * x * g⁻¹}) M :=
    largeEvenPComponent_conj_centralizer_singleton hPL g
  obtain ⟨iv, hiv'⟩ := exists_fin3_succ_eq_of_apply_zero_eq hπ0 hv0
  let t : Fin 3 → (GaloisField 2 f)ˣ :=
    fun i => χ (eta ((ggConjAut Bs hg).symm d) (π i.succ))
  have hTd : g * κ (diagSp (GaloisField 2 f) 3 t) * g⁻¹ = (d : G) :=
    conj_diagSp_of_two_support hR eta hju hu0 hF hπ0 hAL hFL hg hτ d hdoff
  have hiff := chi_eta_succ_eq_one_iff eta hg hj0 hju hjv huv hu0 hv0 hπ0 hiv' hτ
    hFL.2.2.1 d hd0 hdj hdoff
  have htv : t iv = 1 := (hiff iv).2 rfl
  have htne : ∀ i, i ≠ iv → t i ≠ 1 := fun i hni hti => hni ((hiff i).1 hti)
  have hQ := component_longRoot_image_of_original hF κ hFL.1 hFL.2.1 hLcomp g t iv htv htne hTd
  have hBc : ∀ b ∈ Bs, ∀ c ∈ Bs, b * c = c * b :=
    fun b hb c hc => CFSG.Open.IsElemAbelian.comm hBs hb hc
  have hQrange := ggSecFiveBPermSp_singletonComm_K (r := 2) hp2 hf le_rfl hBc hSC he1 hPM hFM iv
  have hπMv : (π.trans τ) iv.succ = v := by
    rw [Equiv.trans_apply, hiv', Equiv.swap_apply_of_ne_of_ne hv0 huv.symm]
  rw [hπMv] at hQrange
  rw [hQrange, MonoidHom.range_comp]
  dsimp only [κ₁]
  rw [← Subgroup.map_map]
  exact hQ


end CFSG.StandardType

end

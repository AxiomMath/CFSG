module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBRestLeafDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSpFourSource
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSpFourCommonChartRouteHolds
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSpFour
import CFSG.LocalAnalysis.StandardType.GGSecFiveBSpCoordFrame
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpPlaneAxis
import CFSG.LocalAnalysis.StandardType.GGSecFiveBSplitFourRadical
import CFSG.LocalAnalysis.StandardType.GGPumpupBalance
import CFSG.LocalAnalysis.StandardType.GGStdTypeOddConj
import CFSG.LocalAnalysis.StandardType.GGTPNDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSpSpSplit
import CFSG.LocalAnalysis.StandardType.GGSecFiveBNbrAxis
import CFSG.LocalAnalysis.StandardType.GGSpJoinBstarSplit
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniBlocks

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.Models.SymplecticPairs

private theorem compl_pair_eq_pair_of_four {i0 j u v : Fin 4}
    (hj0 : j ≠ i0) (hju : j ≠ u) (hjv : j ≠ v) (huv : u ≠ v)
    (hu0 : u ≠ i0) (hv0 : v ≠ i0) :
    ({i0, j} : Set (Fin 4))ᶜ = ({u, v} : Set (Fin 4)) := by
  have hfour : ∀ k : Fin 4, k = i0 ∨ k = j ∨ k = u ∨ k = v := by intro k; omega
  ext k
  constructor
  · intro hk
    rcases hfour k with rfl | rfl | rfl | rfl
    · exact False.elim (hk (by simp))
    · exact False.elim (hk (by simp))
    · simp
    · simp
  · rintro (rfl | rfl)
    · simp [hu0, hju.symm]
    · simp [hv0, hjv.symm]

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

private theorem exists_two_support_coord {G : Type} [Group G] {p n : ℕ} {Bs : Subgroup G}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (a : Multiplicative (ZMod p))
    {i0 j : Fin n} (ha : a ≠ 1) :
    ∃ d : ↥Bs, eta d i0 = a ∧ eta d j = a ∧
      (∀ k, k ≠ i0 → k ≠ j → eta d k = 1) ∧
      eta d i0 ≠ 1 ∧ eta d j ≠ 1 ∧ (d : G) ≠ 1 := by
  let d : ↥Bs := eta.symm (fun k => if k = i0 ∨ k = j then a else 1)
  have hd0 : eta d i0 = a := by simp [d]
  have hdj : eta d j = a := by simp [d]
  have hdoff : ∀ k, k ≠ i0 → k ≠ j → eta d k = 1 := by
    intro k hk0 hkj; simp [d, hk0, hkj]
  have hd0ne : eta d i0 ≠ 1 := by rw [hd0]; exact ha
  have hdjne : eta d j ≠ 1 := by rw [hdj]; exact ha
  have hd1 : (d : G) ≠ 1 := by
    intro h
    have hb : d = 1 := Subtype.ext h
    exact hd0ne (by simp [hb])
  exact ⟨d, hd0, hdj, hdoff, hd0ne, hdjne, hd1⟩

private theorem mem_ggBsCoordZeroOn_of_coord_two_support {G : Type} [Group G] {p n : ℕ}
    {Bs : Subgroup G} (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    {d : ↥Bs} {i0 j u v : Fin n} (hu0 : u ≠ i0) (hju : j ≠ u)
    (hv0 : v ≠ i0) (hjv : j ≠ v)
    (hdoff : ∀ k, k ≠ i0 → k ≠ j → eta d k = 1) :
    (d : G) ∈ ggBsCoordZeroOn Bs eta ({u, v} : Set (Fin n)) := by
  apply mem_ggBsCoordZeroOn.mpr
  refine ⟨d.2, ?_⟩
  intro k hk
  rcases hk with hk | hk
  · subst k; exact hdoff u hu0 hju.symm
  · change k = v at hk
    subst k; exact hdoff v hv0 hjv.symm

private theorem mem_centralizer_ggBlockComm_of_mem_coordZeroOn {G : Type} [Group G] {p n : ℕ}
    {Bs : Subgroup G} (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    {d : ↥Bs} {S : Set (Fin n)}
    (hd : (d : G) ∈ ggBsCoordZeroOn Bs eta S) :
    (d : G) ∈ Subgroup.centralizer (ggBlockComm Bs eta S : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact (Subgroup.mem_centralizer_iff.mp
    (ggBlockComm_le_centralizer Bs eta S hz) (d : G) hd).symm

private theorem mem_D_of_mem_centralizer {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs L D J : Subgroup G} {x : G} (hcfg : GGConfig p B Bs x L D J) (hBB : B = Bs)
    {d : ↥Bs} (hdJ : (d : G) ∈ Subgroup.centralizer (J : Set G)) : (d : G) ∈ D := by
  rw [hcfg.2.2.1.2.2.2.2.2.2]
  exact ⟨by rw [hBB]; exact d.2, hdJ⟩

private theorem notMem_zpowers_of_coord_ne_one {G : Type} [Group G] {p n : ℕ}
    {Bs : Subgroup G} {x : G} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {d : ↥Bs} {j : Fin n} (hxBs : x ∈ Bs) (hxoff : eta ⟨x, hxBs⟩ j = 1)
    (hdjne : eta d j ≠ 1) : (d : G) ∉ Subgroup.zpowers x := by
  intro hd
  have hxZ : x ∈ ggBsCoordZero Bs eta j := coe_mem_ggBsCoordZero.mpr hxoff
  exact hdjne (coe_mem_ggBsCoordZero.mp ((Subgroup.zpowers_le.mpr hxZ) hd))

private theorem isComponentOf_inf_centralizer_of_closure_pair {G : Type} [Group G]
    {x d : G} {L D J : Subgroup G}
    (hD : D = Subgroup.closure ({x, d} : Set G))
    (hJL : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)))
    (hLcomp : IsComponentOf L (Subgroup.centralizer ({x} : Set G))) :
    IsComponentOf J (Subgroup.centralizer ({d} : Set G) ⊓
      Subgroup.centralizer ({x} : Set G)) := by
  let H : Subgroup G := Subgroup.centralizer ({d} : Set G)
  have hCD : Subgroup.centralizer (D : Set G) =
      Subgroup.centralizer ({x} : Set G) ⊓ H := by
    rw [hD, Subgroup.centralizer_closure]
    ext z
    simp [H, Subgroup.mem_centralizer_iff]
  have hJL' : IsComponentOf J (L ⊓ H) := by
    have h : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) := hJL
    rwa [hCD, ← inf_assoc, inf_eq_left.mpr hLcomp.1] at h
  have hs := hLcomp.2.1.inf H
  rw [inf_comm (Subgroup.centralizer ({x} : Set G))] at hs
  exact ⟨fun z hz => ⟨(hJL'.1 hz).2, hLcomp.1 (hJL'.1 hz).1⟩,
    hJL'.2.1.trans hs, hJL'.2.2⟩

private theorem odd_card_commutator_pPrimeCoreOf_of_mem_D {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs L D J : Subgroup G} {x : G} (hcfg : GGConfig p B Bs x L D J)
    {d : G} (hdD : d ∈ D) (hd1 : d ≠ 1) :
    Odd (Nat.card ↥⁅J, LargeEvenPPrimeCoreOf p (Subgroup.centralizer ({d} : Set G))⁆) := by
  have hid : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    rw [map_one]
    rfl
  have h := hcfg.odd_commutator_pPrimeCoreOf_map_conj (1 : G) (d := d)
    (by simpa only [hid, Subgroup.map_id] using hdD) hd1
  rw [hid, Subgroup.map_id] at h
  exact h

private theorem ggConjAut_ne_one_and_coord_off {G : Type} [Group G] {p n : ℕ}
    {Bs : Subgroup G} {x : G} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {i0 u : Fin n} {g : G} (hg : g ∈ Subgroup.normalizer (Bs : Set G))
    (hgτ : MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut (Equiv.swap i0 u))
    (hxBs : x ∈ Bs) (hx1 : x ≠ 1) (hxoff : ∀ k, k ≠ i0 → eta ⟨x, hxBs⟩ k = 1) :
    ggConjAut Bs hg ⟨x, hxBs⟩ ≠ 1 ∧
      ∀ k, k ≠ u → eta (ggConjAut Bs hg ⟨x, hxBs⟩) k = 1 := by
  have hbe1 : ggConjAut Bs hg ⟨x, hxBs⟩ ≠ 1 := by
    intro h
    apply hx1
    exact congrArg Subtype.val ((MulEquiv.map_eq_one_iff (ggConjAut Bs hg)).mp h)
  have hbeoff : ∀ k, k ≠ u → eta (ggConjAut Bs hg ⟨x, hxBs⟩) k = 1 := by
    intro k hk
    have hτ0 : Equiv.swap i0 u k ≠ i0 := by
      intro h
      apply hk
      exact (Equiv.swap i0 u).injective (h.trans (Equiv.swap_apply_right i0 u).symm)
    have h := eta_ggConjAut_apply_of_permAut hg hgτ ⟨x, hxBs⟩ (Equiv.swap i0 u k)
    simpa only [Equiv.swap_apply_self, hxoff _ hτ0] using h
  exact ⟨hbe1, hbeoff⟩

private theorem comp_spEmbed_longBlock_eq {G : Type} [Group G] {F : Type} [Field F]
    (κ : StatedSp 3 F →* G) (σ : Fin 2 → Fin 3) (hσ : Function.Injective σ)
    (lam : Fˣ) (e : G)
    (heq : κ (longBlock F 3 (σ 0)
      (CFSG.LocalAnalysis.ComponentInitial.sl2Diag F lam)) = e) :
    (κ.comp (spEmbed σ hσ)) (longBlock F 2 0
      (CFSG.LocalAnalysis.ComponentInitial.sl2Diag F lam)) = e := by
  change κ (spEmbed σ hσ (longBlock F 2 0
    (CFSG.LocalAnalysis.ComponentInitial.sl2Diag F lam))) = e
  rw [spEmbed_longBlock]
  exact heq

private theorem exists_frame_and_block_eq
    {G : Type} [Group G] [Finite G] {p f : ℕ} {B Bs L D J : Subgroup G} {x : G}
    {𝒦 : Finset (Subgroup G)}
    {eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod p))} {i0 : Fin 4}
    {K : Subgroup G} {j u v : Fin 4}
    (hfr : GGSecFiveBSpCoordFrameInput)
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hcell : GGSecFiveBCoordBSpFourCell p Bs L 𝒦 4 eta f K i0)
    (hLeta : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom =
      bCoordinateBlock 4 p i0)
    (hLab : GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel 4 p lab) p Bs L)
    (hRig : GGLabelRigidInput)
    (hKeta : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom =
      bCoordinateBlock 4 p j)
    (hj0 : j ≠ i0) (hju : j ≠ u) (hjv : j ≠ v) (huv : u ≠ v)
    (hu0 : u ≠ i0) (hv0 : v ≠ i0) :
    ∃ (π : Fin 4 ≃ Fin 4) (κ : StatedSp 3 (GaloisField 2 f) →* G)
      (χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ),
      p.Prime ∧ p ≠ 2 ∧ 2 ≤ f ∧ 4 ≤ Nat.card (GaloisField 2 f) ∧
        π 0 = i0 ∧ GGSecFiveBPermSpKFrame Bs L eta π κ χ ∧
          J = ggBlockComm Bs eta ({u, v} : Set (Fin 4)) := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  have hdvd : p ∣ 2 ^ f - 1 := hcell.dvd_two_pow_sub_one hLab hRig
  obtain ⟨hf, -, hK, ⟨eL⟩, -⟩ := hcell
  have hF := ggSecFiveBFour_le_card_galois hf
  obtain ⟨π, κ, χ, hπ0, hFL⟩ := hfr G p hp hp2 2 f le_rfl hf hdvd B Bs L
    hR.1.1.2.1 hR.1.2.2.1.1 ⟨eL⟩ eta i0 hLeta
  obtain ⟨y, hnb⟩ := hR.2.2.2.1.2 K hK
  obtain ⟨hJblock, -⟩ := hR.1.1.J_eq_blockComm_and_exists_range_spEmbed hF hnb eta hj0
    hLeta hKeta hπ0 hFL.toPlaneFrame
  have hS := compl_pair_eq_pair_of_four hj0 hju hjv huv hu0 hv0
  rw [hS] at hJblock
  exact ⟨π, κ, χ, hp, hp2, hf, hF, hπ0, hFL, hJblock⟩

private theorem coord_axis_facts {G : Type} [Group G] [Finite G] {p n : ℕ}
    {B Bs L D J : Subgroup G} {x : G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {i0 : Fin n}
    (hcfg : GGConfig p B Bs x L D J) (hp2 : p ≠ 2)
    (hLeta : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom =
      bCoordinateBlock n p i0) :
    ∃ (hxBs : x ∈ Bs), L ≤ Subgroup.centralizer ({x} : Set G) ∧ x ≠ 1 ∧
      (∀ k, k ≠ i0 → eta ⟨x, hxBs⟩ k = 1) ∧ eta ⟨x, hxBs⟩ i0 ≠ 1 := by
  obtain ⟨hp, -, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have hx1 : x ≠ 1 := hcfg.1.2.2.2.2.2.2.1.2.2.1
  have hxoff : ∀ k, k ≠ i0 → eta ⟨x, hxBs⟩ k = 1 :=
    ggBs_coord_eq_one_of_mem_bCoordinateBlock hp hp2 hxBs hLx eta i0 hLeta
  have hxa : eta ⟨x, hxBs⟩ i0 ≠ 1 :=
    coord_ne_one_of_axis eta ⟨x, hxBs⟩ (fun h => hx1 (congrArg Subtype.val h)) i0 hxoff
  exact ⟨hxBs, hLx, hx1, hxoff, hxa⟩

private theorem pumpup_odd_data
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs L D J : Subgroup G} {x : G}
    {𝒦 : Finset (Subgroup G)} {n : ℕ}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {i0 j u : Fin n} {d : ↥Bs}
    (hLB : GGLBalanceInput) (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hFC : GGResNbrFixCentralizesInput) (hBB : B = Bs) (hn : 3 ≤ n)
    (hBfull : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom =
      bSignedFull n p)
    (hnbr : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (hj0 : j ≠ i0) (hju : j ≠ u) (hu0 : u ≠ i0)
    (hd0ne : eta d i0 ≠ 1) (hdjne : eta d j ≠ 1)
    (hdoff : ∀ k, k ≠ i0 → k ≠ j → eta d k = 1)
    (hdD : (d : G) ∈ D) (hd1 : (d : G) ≠ 1)
    (hD : D = Subgroup.closure ({x, (d : G)} : Set G)) (hpJ : p ∣ Nat.card J) :
    LargeEvenPComponent p (Subgroup.centralizer ({(d : G)} : Set G))
        (ggLayerClosure p (Subgroup.centralizer ({(d : G)} : Set G)) J) ∧
      J ≤ ggLayerClosure p (Subgroup.centralizer ({(d : G)} : Set G)) J ∧
      x ∈ Subgroup.normalizer
        (ggLayerClosure p (Subgroup.centralizer ({(d : G)} : Set G)) J : Set G) ∧
      (⁅ggLayerClosure p (Subgroup.centralizer ({(d : G)} : Set G)) J,
          Subgroup.zpowers x⁆ ≤
        LargeEvenPPrimeCoreOf p
          (ggLayerClosure p (Subgroup.centralizer ({(d : G)} : Set G)) J)) ∧
      x ^ p = 1 ∧
      Odd (Nat.card ↥⁅J, LargeEvenPPrimeCoreOf p
        (Subgroup.centralizer ({(d : G)} : Set G))⁆) := by
  obtain ⟨hA, hJA, hxA, hOr⟩ := pumpup_of_stdSub (ggPumpupInput_of_lBalance hLB)
    hR.1.1.1 hR.1.1.2.2 hpJ hD
  have hNo := hR.not_nbr_of_two_ne_one_of_eq_one hX hTCJ hRig hTPn hA8 hraw hiso hFC hBB
    hn eta hBfull hnbr (y := (d : G)) d.2 hj0 hdjne hd0ne (hdoff u hu0 hju.symm)
  have hxc := hOr.resolve_left (hNo _)
  have hSstar : LargeEvenSStar p B x L := hR.1.1.1.2.2.2.2.2.2.1
  have hxp : x ^ p = 1 := hSstar.1.1.2 x hSstar.2.1
  have hodd := odd_card_commutator_pPrimeCoreOf_of_mem_D hR.1.1 hdD hd1
  exact ⟨hA, hJA, hxA, hxc, hxp, hodd⟩

private theorem opposite_singleton_diagonal_data
    {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {B Bs L D J : Subgroup G} {x : G}
    {𝒦 : Finset (Subgroup G)}
    {eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod p))}
    {i0 j u v : Fin 4} {d : ↥Bs} {g : G}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hcfg : GGConfig p B Bs x L D J)
    (hf : 2 ≤ f) (hp2 : p ≠ 2) (hF : 4 ≤ Nat.card (GaloisField 2 f))
    {π : Fin 4 ≃ Fin 4} {κ : StatedSp 3 (GaloisField 2 f) →* G}
    {χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}
    (hπ0 : π 0 = i0) (hFL : GGSecFiveBPermSpKFrame Bs L eta π κ χ)
    (hLeta : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom =
      bCoordinateBlock 4 p i0)
    (hj0 : j ≠ i0) (hju : j ≠ u) (hjv : j ≠ v) (huv : u ≠ v)
    (hu0 : u ≠ i0) (hv0 : v ≠ i0)
    {ψ : StatedSp 2 (GaloisField 2 f) →* G}
    (hQ₂R : (ψ.comp (longBlock (GaloisField 2 f) 2 1)).range =
      ⁅Subgroup.centralizer (ggBsCoordZero Bs eta v : Set G), Bs⁆)
    (hg : g ∈ Subgroup.normalizer (Bs : Set G))
    (hgτ : MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut (Equiv.swap i0 u))
    (hxBs : x ∈ Bs) (hx1 : x ≠ 1)
    (hxoff : ∀ k, k ≠ i0 → eta ⟨x, hxBs⟩ k = 1)
    (hd0ne : eta d i0 ≠ 1) (hdjne : eta d j ≠ 1)
    (hdoff : ∀ k, k ≠ i0 → k ≠ j → eta d k = 1)
    {iu : Fin 3} (hπu : π iu.succ = u) :
    IsComponentOf (ψ.comp (longBlock (GaloisField 2 f) 2 1)).range
        (Subgroup.centralizer ({(d : G)} : Set G) ⊓
          Subgroup.centralizer ({g * x * g⁻¹} : Set G)) ∧
      ∃ lam : (GaloisField 2 f)ˣ, orderOf lam = p ∧
        κ (longBlock (GaloisField 2 f) 3 iu
          (CFSG.LocalAnalysis.ComponentInitial.sl2Diag (GaloisField 2 f) lam)) =
          g * x * g⁻¹ := by
  have hQ₂ := hR.isComponentOf_singleton_of_two_support hf eta hj0 hju hjv huv hu0 hv0 hπ0
    hLeta hFL hg hgτ d hd0ne hdjne hdoff
  rw [← hQ₂R] at hQ₂
  let be : ↥Bs := ggConjAut Bs hg ⟨x, hxBs⟩
  obtain ⟨hbe1, hbeoff⟩ := ggConjAut_ne_one_and_coord_off hg hgτ hxBs hx1 hxoff
  obtain ⟨hlam, heq⟩ := hFL.toPlaneFrame.sl2Diag_eq_coordinate_of_axis hp2 hF hcfg
    (ggInnerDiagOn_le_normalizer hR.1.2.2.1.1) (by rw [hπ0]; exact hLeta)
    iu be hbe1 (by rw [hπu]; exact hbeoff)
  let lam : (GaloisField 2 f)ˣ := χ (eta be (π iu.succ))
  refine ⟨hQ₂, lam, hlam, ?_⟩
  exact heq


theorem ggSecFiveBCoordBSpFourCommonCompRouteInput_holds :
    GGSecFiveBCoordBSpFourCommonCompRouteInput := by
  intro hMp hLB hP hX hTCJ hRig hTPn hA8 hraw hiso hFC _
  have hfr := ggSecFiveBSpCoordFrameInput_of_mp hMp
  intro G _ _ p B Bs x L D J 𝒦 hR hT1 n e hpres h4 eta i0 hBfull hLeta hLab hBB hnbr hG0 f K
    hcell j hj0 hKeta u v hju hjv huv hu0 hv0
  have hn4 : n = 4 := hcell.2.1
  subst hn4
  obtain ⟨π, κ, χ, hp, hp2, hf, hF, hπ0, hFL, hJblock⟩ :=
    exists_frame_and_block_eq hfr hR hcell hLeta hLab hRig hKeta hj0 hju hjv huv hu0 hv0
  obtain ⟨iu, iv, hiuv, hπu, hπv, hψ, hψR, hQ₁R, hQ₂R⟩ :=
    (letI : Fact p.Prime := ⟨hp⟩;
      hFL.exists_ordered_commonChart hp2 hf hR (by rw [hπ0]; exact hu0)
        (by rw [hπ0]; exact hv0) huv)
  let σ : Fin 2 → Fin 3 := pairMap iu iv
  let ψ : StatedSp 2 (GaloisField 2 f) →* G := κ.comp (spEmbed σ (pairMap_injective hiuv))
  have hψJ : ψ.range = J := hψR.trans hJblock.symm
  obtain ⟨hxBs, hLx, hx1, hxoff, hxa⟩ := coord_axis_facts hR.1.1 hp2 hLeta
  let a : Multiplicative (ZMod p) := eta ⟨x, hxBs⟩ i0
  obtain ⟨d, hd0, hdj, hdoff, hd0ne, hdjne, hd1⟩ :=
    exists_two_support_coord eta a hxa
  have hdHS := mem_ggBsCoordZeroOn_of_coord_two_support eta hu0 hju hv0 hjv hdoff
  have hdCJ : (d : G) ∈ Subgroup.centralizer (J : Set G) := by
    rw [hJblock]
    exact mem_centralizer_ggBlockComm_of_mem_coordZeroOn eta hdHS
  have hdD := mem_D_of_mem_centralizer hR.1.1 hBB hdCJ
  have hdx := notMem_zpowers_of_coord_ne_one hxBs (hxoff j hj0) hdjne
  have hD := eq_closure_pair_of_mem hR.1.1.1 hR.1.1.2.2 hdD hdx
  have hpJ := hP G p B x L D J hR.1.1.1 hR.1.1.2.2
  have hJ : IsComponentOf J (Subgroup.centralizer ({(d : G)} : Set G) ⊓
      Subgroup.centralizer ({x} : Set G)) :=
    isComponentOf_inf_centralizer_of_closure_pair hD hR.1.1.2.2.1.2.2.2.2.2.1
      hR.1.1.1.2.2.2.2.2.2.1.2.2.2.1
  obtain ⟨hA, hJA, hxA, hxc, hxp, hodd⟩ :=
    pumpup_odd_data hLB hR hX hTCJ hRig hTPn hA8 hraw hiso hFC hBB (by norm_num)
      hBfull hnbr hj0 hju hu0 hd0ne hdjne hdoff hdD hd1 hD hpJ
  obtain ⟨g, hgK, hg, hgτ⟩ :=
    exists_normalizing_swap_of_bCoordinateBlock hKeta hu0.symm hj0.symm hju.symm
  obtain ⟨hQ₂, lam, hlam, heq⟩ :=
    (letI : Fact p.Prime := ⟨hp⟩;
      opposite_singleton_diagonal_data hR hR.1.1 hf hp2 hF hπ0 hFL hLeta hj0 hju hjv huv hu0
        hv0 hQ₂R hg hgτ hxBs hx1 hxoff hd0ne hdjne hdoff hπu)
  have he₁ : ψ (longBlock (GaloisField 2 f) 2 0
      (CFSG.LocalAnalysis.ComponentInitial.sl2Diag (GaloisField 2 f) lam)) = g * x * g⁻¹ := by
    dsimp only [ψ]
    exact comp_spEmbed_longBlock_eq κ σ (pairMap_injective hiuv) lam (g * x * g⁻¹) heq
  have hJH := (letI : Fact p.Prime := ⟨hp⟩; letI : Fintype (GaloisField 2 f) := Fintype.ofFinite _;
    (ggPComponent_eq_of_oddRadical_of_Sp4 ψ hψ hψJ lam hlam he₁ hA hJA hJ hpJ
      hxA hxp hxc hodd hQ₂).2)
  refine ⟨(d : G), coe_mem_ggBsCoordEq.mpr (hdj.trans hd0.symm), ?_⟩
  rw [← hJblock]
  exact hJH

end CFSG.StandardType

end

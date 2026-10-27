module

public import CFSG.Quasithin.Vol2.Ch11SecAViLevi
public import CFSG.Quasithin.Background.InternalSecB56
public import CFSG.Quasithin.Background.B2Factorization
public import CFSG.Quasithin.Background.InternalSecB51

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecC

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.InternalSec CFSG.QuasithinUnique CFSG.Quasithin.H13
open scoped IsMulCommutative commutatorElement

namespace B51

theorem commutator_eq_or_eq_bot {Ω : Type*} [Group Ω] {K A : Subgroup Ω}
    (hK : CFSG.IsQuasisimple ↥K) (hA : A ≤ Subgroup.normalizer (K : Set Ω)) :
    ⁅K, A⁆ = K ∨ ⁅K, A⁆ = ⊥ := by
  have hle : ⁅K, A⁆ ≤ K := Subgroup.le_normalizer_iff_commutator_le_left.mp hA
  have hN : ((⁅K, A⁆ : Subgroup Ω).subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr
      (Subgroup.normalizer_commutator_ge_left K A)
  have hKo := B1Red.isQuasisimple_to_open hK
  have hKK : ⁅K, K⁆ = K := by
    have h2 := Subgroup.map_commutator (⊤ : Subgroup ↥K) ⊤ K.subtype
    rw [← commutator_def, hKo.1, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
    exact h2.symm
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hKo
      ((⁅K, A⁆ : Subgroup Ω).subgroupOf K) with h | h
  · right
    have hc : ⁅⁅K, A⁆, K⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hx' : (⟨x, hle hx⟩ : ↥K) ∈ (⁅K, A⁆ : Subgroup Ω).subgroupOf K := hx
      have := Subgroup.mem_center_iff.mp (h hx') ⟨k, hk⟩
      exact congrArg Subtype.val this
    have hc' : ⁅⁅A, K⁆, K⁆ = ⊥ := by rw [Subgroup.commutator_comm A K]; exact hc
    have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate hc hc'
    rwa [hKK] at h3
  · left
    refine le_antisymm hle fun k hk => ?_
    have : (⟨k, hk⟩ : ↥K) ∈ (⁅K, A⁆ : Subgroup Ω).subgroupOf K := by rw [h]; trivial
    exact this

theorem pCoreOf_ne_bot_of_faithful {G : Type} [Group G] {T L : Subgroup G}
    (h : quasithinIsFaithfulLocal T L) : pCoreOf 2 L ≠ ⊥ := by
  intro h2
  apply h.2.2.2
  rw [quasithinV2, h2]
  have hb : Subgroup.closure {z : G | z ∈ (⊥ : Subgroup G) ⊓
      Subgroup.centralizer ((⊥ : Subgroup G) : Set G) ∧ z ^ 2 = 1} = ⊥ :=
    le_bot_iff.mp ((Subgroup.closure_le _).mpr fun _ hz => hz.1.1)
  rw [hb, Subgroup.commutator_bot_left]

variable {G : Type} [Group G] [Finite G]

structure BridgeHyp (T L I : Subgroup G) (n : ℕ) (Y W : Subgroup G) : Prop where
  hyp : Hyp11 G T L I n
  le : L ⊔ T ≤ Y
  normL : Y ≤ Subgroup.normalizer (L : Set G)
  red : IsTwoReducedIn Y W
  fsuV_le : fsuV T I ≤ W
  comm_ne : ⁅W, L⁆ ≠ ⊥

namespace BridgeHyp

variable {T L I : Subgroup G} {n : ℕ} {Y W : Subgroup G} (h : BridgeHyp T L I n Y W)
include h

theorem isElemAbelian : IsElemAbelian 2 W := h.red.2.2.1

theorem normW : Y ≤ Subgroup.normalizer (W : Set G) := h.red.2.1

theorem le_Y : L ≤ Y := le_sup_left.trans h.le

theorem T_le : T ≤ Y := le_sup_right.trans h.le

theorem le_normW : L ≤ Subgroup.normalizer (W : Set G) := h.le_Y.trans h.normW

theorem not_le_centralizer : ¬ L ≤ Subgroup.centralizer (W : Set G) := by
  intro hc
  apply h.comm_ne
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact hc

theorem pCoreOf_autOn_Y : pCoreOf 2 (autOn Y W) = ⊥ := Setup.pCoreOf_autOn_eq_bot h.red

theorem autOn_le : autOn L W ≤ autOn Y W := autOn_le_autOn_of_le h.le_Y

theorem pCoreOf_autOn_L : pCoreOf 2 (autOn L W) = ⊥ := by
  have hn : ((autOn L W).subgroupOf (autOn Y W)).Normal := by
    refine ⟨fun k hk x => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    exact autOn_normal_of h.normL _ x.2 _ hk
  have := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 _ _
    h.autOn_le hn
  rw [h.pCoreOf_autOn_Y] at this
  exact le_bot_iff.1 this

theorem isQuasisimple : CFSG.IsQuasisimple ↥(autOn L W) :=
  isQuasisimple_autOn h.le_normW h.hyp.fsu.quasisimple h.pCoreOf_autOn_L h.not_le_centralizer

theorem pCoreOf_le_centralizer : pCoreOf 2 L ≤ Subgroup.centralizer (W : Set G) := by
  have hle := pCore_le_ker_autOnHom h.le_normW h.pCoreOf_autOn_L
  rintro _ ⟨y, hy, rfl⟩
  exact (mem_ker_autOnHom h.le_normW y).1 (hle hy)

theorem inf_centralizer_eq (h1102 : Stmt11_0_2) :
    L ⊓ Subgroup.centralizer (W : Set G) = L ⊓ Subgroup.centralizer (fsuV T I : Set G) := by
  apply le_antisymm
  · exact inf_le_inf_left _ (Subgroup.centralizer_le h.fsuV_le)
  · rw [SecA.centralizer_eq_pCoreOf h1102 h.hyp]
    exact le_inf (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le 2 L)
      h.pCoreOf_le_centralizer

theorem sqtkGroup (h1102 : Stmt11_0_2) : SQTKGroup ↥(autOn L W) := by
  have := h.hyp.fsu.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat h.hyp.fsu.nonabelian h.hyp.fsu.qtke).1
  have hS : SQTKGroup ↥L := sqtkGroup_of_localSQTK hloc
    (pCoreOf_ne_bot_of_faithful h.hyp.fsu.faithful)
  refine sqtkGroup_autOn h.le_normW hS ?_
  rw [h.inf_centralizer_eq h1102, SecA.centralizer_eq_pCoreOf h1102 h.hyp]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [pCoreOf]
  exact (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).map L.subtype

theorem nonempty_autOnEquiv (h1102 : Stmt11_0_2) :
    Nonempty (↥(autOn L W) ≃* ↥(autOn L (fsuV T I))) := by
  have hLV : L ≤ Subgroup.normalizer (fsuV T I : Set G) := SecA.L_le_normalizer_fsuV h.hyp
  have hker : (autOnHom h.le_normW).ker = (autOnHom hLV).ker := by
    ext l
    rw [mem_ker_autOnHom, mem_ker_autOnHom]
    constructor
    · intro hl
      have h2 : (l : G) ∈ L ⊓ Subgroup.centralizer (W : Set G) := ⟨l.2, hl⟩
      rw [h.inf_centralizer_eq h1102] at h2
      exact h2.2
    · intro hl
      have h2 : (l : G) ∈ L ⊓ Subgroup.centralizer (fsuV T I : Set G) := ⟨l.2, hl⟩
      rw [← h.inf_centralizer_eq h1102] at h2
      exact h2.2
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective _
      (autOnHom_surjective h.le_normW)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (autOnHom_surjective hLV)))⟩

theorem exists_offender [IsMulCommutative ↥W] (hJ : L = ⁅L, thompsonJ T⁆) :
    ∃ A : Subgroup G, IsMaxElemAbelian T A ∧
      IsFFStarOffender (autOn Y W) (autOn A W) ∧ ⁅autOn L W, autOn A W⁆ = autOn L W := by
  have hWe := h.isElemAbelian
  have hTsyl : IsSylowTwoOf T Y := isSylowTwoOf_of_quasithinIsSylowTwo h.hyp.fsu.sylow h.T_le
  have hTN : T ≤ Subgroup.normalizer (L : Set G) := h.T_le.trans h.normL
  have hTW : T ≤ Subgroup.normalizer (W : Set G) := h.T_le.trans h.normW
  have hq := h.isQuasisimple
  have hnorm : ∀ A : Subgroup G, A ≤ T →
      autOn A W ≤ Subgroup.normalizer (autOn L W : Set (MulAut ↥W)) := by
    intro A hAT x hx
    have hc := autOn_normal_of (U := W) (hAT.trans hTN)
    rw [Subgroup.mem_normalizer_iff]
    intro k
    refine ⟨fun hk => hc x hx k hk, fun hk => ?_⟩
    have := hc x⁻¹ ((autOn A W).inv_mem hx) _ hk
    simpa [mul_assoc] using this
  by_cases hex : ∃ A : Subgroup G, IsMaxElemAbelian T A ∧ ⁅autOn L W, autOn A W⁆ = autOn L W
  · obtain ⟨A, hA, hLA⟩ := hex
    have hAC : ¬ A ≤ Subgroup.centralizer (W : Set G) := by
      intro hAC
      have h0 : autOn A W = ⊥ := autI_eq_bot_of_le_centralizer hWe hAC
      rw [h0, Subgroup.commutator_bot_right] at hLA
      refine not_commute_of_isQuasisimple hq fun a ha b hb => ?_
      rw [← hLA, Subgroup.mem_bot] at ha hb
      rw [ha, hb]
    have hoff : IsFFOffender Y W A := ⟨isMaxElemAbelian_of_isSylowTwoOf hTsyl hA, hAC⟩
    exact ⟨A, hA, offenderImages_isFFStarOffender hWe h.red.1 h.normW ⟨A, hoff, rfl⟩, hLA⟩
  · exfalso
    push Not at hex
    have hbot : ∀ A : Subgroup G, IsMaxElemAbelian T A →
        autOn A W ≤ Subgroup.centralizer (autOn L W : Set (MulAut ↥W)) := by
      intro A hA
      rcases commutator_eq_or_eq_bot hq (hnorm A hA.1) with h1 | h1
      · exact absurd h1 (hex A hA)
      · rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h1
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        exact (Subgroup.mem_centralizer_iff.mp (h1 hk) x hx).symm
    set S : Subgroup G :=
      ((Subgroup.centralizer (autOn L W : Set (MulAut ↥W))).comap (conjAct W)).map
        (Subgroup.normalizer (W : Set G)).subtype with hS
    have hJS : thompsonJ T ≤ S := by
      refine iSup₂_le fun A hA => ?_
      intro a ha
      have haN : a ∈ Subgroup.normalizer (W : Set G) := hTW (hA.1 ha)
      exact ⟨⟨a, haN⟩, hbot A hA (Setup.mem_autOn_iff.2 ⟨⟨a, haN⟩, ha, rfl⟩), rfl⟩
    apply h.not_le_centralizer
    rw [hJ, Subgroup.commutator_le]
    intro l hl j hj
    obtain ⟨g, hg, rfl⟩ := hJS hj
    set lN : ↥(Subgroup.normalizer (W : Set G)) := ⟨l, h.le_normW hl⟩
    have hlK : conjAct W lN ∈ autOn L W := conjAct_mem_autOn h.le_normW hl
    have hcomm : conjAct W ⁅lN, g⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.mp hg _ hlK)
    exact (convI_eq_one_iff hWe ⁅lN, g⁆).1 hcomm

theorem b51Hyp_of_two [IsMulCommutative ↥W] (h1102 : Stmt11_0_2) (hJ : L = ⁅L, thompsonJ T⁆)
    (hY2 : ∀ y ∈ Y, ∃ e : ℕ, y ^ 2 ^ e ∈ L ⊔ Subgroup.centralizer (W : Set G)) :
    B51Hyp (ffJ (autOn Y W)) (autOn L W) := by
  obtain ⟨A, -, hA, hLA⟩ := h.exists_offender hJ
  exact (b51Hyp_ffJ_autOn h.normW h.le_Y h.normL hY2 h.pCoreOf_autOn_Y h.isQuasisimple
    (h.sqtkGroup h1102) hA hLA).1

end BridgeHyp

end B51

end CFSG.Quasithin.Vol2.Ch11.SecC

module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtC134ResComm

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.FLc

open Matrix CFSG.Quasithin CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LieType.BorelTits CFSG.Open CFSG.Quasithin.C134Res

variable {G : Type} [Group G]

namespace P0Setup

variable {L S UL : Subgroup G} {n : ℕ} {W : ℕ → Subgroup G} (D : P0Setup L S UL n W)

include D

theorem exists_sylow_pCoreOf_eq [Finite G] (hn : n = 4 ∨ n = 5) (hUL : UL ≤ L ⊔ S) {T : Subgroup G}
    (hT : IsPGroup 2 T) (hST : S ≤ T) (hTQ : T ≤ Subgroup.normalizer (qNode L S n W : Set G))
    (hTY : T ≤ Subgroup.normalizer (yNode L S n W 2 : Set G))
    (hZ : ∀ x ∈ T, (∀ t ∈ T, t * x = x * t) → x ^ 2 = 1 →
      ∀ y ∈ yNode L S n W 2, y * x = x * y) :
    ∃ S' : Subgroup G, IsSylowTwoOf S' (gNode L S n W) ∧ qNode L S n W ≤ S' ∧
      qNode L S n W =
        pCoreOf 2 (gNode L S n W ⊓ Subgroup.centralizer (omegaOneCenterOf S' : Set G)) := by
  have h1n : 1 < n := by omega
  have hcomm := D.yNode_commute_elemCenter hn hT hST hTQ hTY hZ
  obtain ⟨l₂, hl⟩ := D.exists_hasL2 hn
  have hl₂P : (l₂ : G) ∈ parab (L ⊔ S) n W 2 := D.mem_parab_of_alpha l₂ hl.mem
  have hl₂Y : (l₂ : G) ∈ yNode L S n W 2 := mem_oTwoUpper_of_odd hl₂P hl.odd
  have hSyl : IsSylowTwoOf S (gNode L S n W ⊔ S) :=
    A4.isSylowTwoOf_mono D.syl le_sup_right (sup_le D.gNode_le_sup le_sup_right)
  have hS0 : IsSylowTwoOf (S ⊓ gNode L S n W) (gNode L S n W) :=
    A4.isSylowTwoOf_inf_normal hSyl le_sup_left
      (sup_le Subgroup.le_normalizer D.S_le_normalizer_gNode)
  have hQS' : qNode L S n W ≤ S ⊓ gNode L S n W := le_inf D.qNode_le_S qNode_le_gNode
  refine ⟨S ⊓ gNode L S n W, hS0, hQS', ?_⟩
  set S' : Subgroup G := S ⊓ gNode L S n W with hS'def
  set Z' : Subgroup G := omegaOneCenterOf S' with hZ'def
  have hgen : ∀ x, x ∈ S' ⊓ Subgroup.centralizer (S' : Set G) → x ^ 2 = 1 → x ∈ Z' :=
    fun x hx hx2 => Subgroup.subset_closure ⟨hx, hx2⟩
  have hgenE : ∀ x, x ∈ S' ⊓ Subgroup.centralizer (S' : Set G) → x ^ 2 = 1 →
      x ∈ elemCenter (qNode L S n W) := by
    intro x hx hx2
    have hULQ : UL ≤ qNode L S n W := D.UL_le_qNode hUL
    have hxUL : x ∈ Subgroup.centralizer (UL : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact Subgroup.mem_centralizer_iff.1 hx.2 u (hQS' (hULQ hu))
    have hxP : x ∈ parab (L ⊔ S) n W 2 := D.S_le_parab 2 hx.1.1
    refine ⟨D.inf_centralizer_UL_le_qNode hn hxP hxUL, ?_, hx2⟩
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact Subgroup.mem_centralizer_iff.1 hx.2 q (hQS' hq)
  have hZ'S : Z' ≤ Subgroup.centralizer (S' : Set G) :=
    (Subgroup.closure_le _).2 fun x hx => hx.1.2
  have hZ'Y : ∀ y ∈ yNode L S n W 2, y ∈ Subgroup.centralizer (Z' : Set G) := by
    intro y hy
    have : Z' ≤ Subgroup.centralizer ({y} : Set G) := by
      refine (Subgroup.closure_le _).2 fun x hx => ?_
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.1 hh]
      exact hcomm y hy x (hgenE x hx.1 hx.2)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.1 (this hz) y rfl).symm
  have hW1 : Nat.card ↥(W 1) = 2 := by
    have := D.W_card 1 le_rfl h1n
    simpa using this
  have hW1Z : W 1 ≤ Z' := by
    intro w hw
    have hwQ : w ∈ qNode L S n W := D.UL_le_qNode hUL (D.W_le 1 le_rfl h1n hw)
    have hwS' : w ∈ S' := hQS' hwQ
    have hwc : w ∈ Subgroup.centralizer (S' : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      exact card_two_centralized hW1 (D.W_norm 1 le_rfl h1n) hs.1 hw
    have hw2 : w ^ 2 = 1 := by
      have := pow_card_eq_one' (G := ↥(W 1)) (x := ⟨w, hw⟩)
      rw [hW1] at this
      exact congrArg Subtype.val this
    exact hgen w ⟨hwS', hwc⟩ hw2
  set C : Subgroup G := gNode L S n W ⊓ Subgroup.centralizer (Z' : Set G) with hCdef
  have hCH : C ≤ gNode L S n W ⊓ Subgroup.normalizer (W 1 : Set G) := by
    intro x hx
    obtain ⟨hxg, hxc⟩ := Subgroup.mem_inf.1 hx
    refine Subgroup.mem_inf.2 ⟨hxg, Subgroup.centralizer_le_normalizer _ ?_⟩
    exact Subgroup.centralizer_le (s := (W 1 : Set G)) (t := (Z' : Set G)) hW1Z hxc
  have hQC : qNode L S n W ≤ C := by
    intro q hq
    refine Subgroup.mem_inf.2 ⟨qNode_le_gNode hq, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.1 (hZ'S hz) q (hQS' hq)).symm
  have hlC : (l₂ : G) ∈ C :=
    Subgroup.mem_inf.2 ⟨Subgroup.mem_sup_left (Subgroup.mem_sup_right hl₂Y), hZ'Y _ hl₂Y⟩
  refine le_antisymm ?_ (D.pCoreOf_le_qNode_of_mem hn hCH hl hlC)
  exact le_pCoreOf_of_le_normalizer 2 hQC
    ((hCH.trans D.inf_le_parab).trans (le_normalizer_pCoreOf 2 _)) qNode_isPGroup

end P0Setup

end CFSG.Quasithin.FLc

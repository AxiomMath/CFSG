module

public import CFSG.RankThree.GF2n.Stroth80.Sec10RootKernel
public import CFSG.RankThree.GF2n.Stroth80.Sec101Tt
public import CFSG.RankThree.GF2n.Stroth80.Sec103Inv

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Good101.exists_root_group_ne (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t) :
    ∃ μ ∈ M, conjSubgroup μ B ≤ QB Y ∧ conjSubgroup μ B ≠ B := by
  set A₀ := Q ⊓ QB Y ⊓ Vt M (LB M Q B) B Z t
  obtain ⟨m, hm2, hm⟩ := SLlike.exists_SLMNat (H.slLike ht)
  have hcardB : Nat.card ↥B = Nat.card Z := by
    obtain ⟨g, hg⟩ := hc.conj
    rw [hg, card_conjSubgroup]
  have hnotle : ¬ A₀ ≤ B := by
    intro hle
    have hcardle : Nat.card ↥A₀ ≤ Nat.card ↥B :=
      Nat.card_le_card_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective _)
    rw [show Nat.card ↥A₀ = Nat.card Z ^ m from ht.card_inf_QB_inf_Vt h34 hspread H hs hm,
      hcardB] at hcardle
    have hq : 1 < Nat.card Z := by have := hc.hyp.q4; omega
    have hm1 : 1 < m := by omega
    have hlt : Nat.card Z ^ 1 < Nat.card Z ^ m := Nat.pow_lt_pow_right hq hm1
    rw [pow_one] at hlt
    omega
  obtain ⟨x, hxA, hxB⟩ := Set.not_subset.mp hnotle
  have hx1 : x ≠ 1 := fun h => hxB (h ▸ B.one_mem)
  have hxZ : x ∉ Z := by
    intro hxZ
    have h' : x ∈ Z ⊓ QB Y := ⟨hxZ, hxA.1.2⟩
    rw [Z_inf_QB_eq_bot hs (smith_1_12 hs), Subgroup.mem_bot] at h'
    exact hx1 h'
  obtain ⟨C, hC, hxC, hCY, -⟩ :=
    Sit.exists_root_group hs ⟨hxA.1.1, hxA.1.2⟩ hx1 (ht.isRoot_of_mem_Vt H hxA.2 hxZ)
  obtain ⟨μ, hμM, hμB⟩ := H.rootTrans h34 hspread C hC
  have hCB : C ≠ B := fun h => hxB (h ▸ hxC)
  exact ⟨μ, hμM, by rw [hμB]; exact hCY, fun h => hCB (hμB.symm.trans h)⟩

theorem Good101.Q1_eq_of_mem_root (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t) {s : G}
    (hsY : s ∈ Y) (hs1 : s ≠ 1) : Q1 hc s = Q1 hc t := by
  obtain ⟨μ, hμM, hμC, hne⟩ := ht.exists_root_group_ne h34 hspread H hs
  have hBY : B ≤ QB Y :=
    hc.hyp.le_QB_of_mem_QB hc.conj hs.conj hs.mem hs.ne_one ht.2.2.2.1
  have hBμ : conjSubgroup (1 : G) B ≤ QB Y := by rw [conjSubgroup_one]; exact hBY
  have hne' : conjSubgroup (1 : G) B ≠ conjSubgroup μ B := by
    rw [conjSubgroup_one]; exact hne.symm
  have hsy := Sit.of_mem_root hs hsY hs1
  ext h
  constructor
  · intro hh
    rw [hc.mem_Q1_iff hsy.memM] at hh
    rw [hc.mem_Q1_iff hs.memM]
    exact ⟨hh.1, H.comm_mem_Z_of_mem_root h34 hsy M.one_mem hμM hBμ hμC hne' hs.mem hh.1 hh.2⟩
  · intro hh
    rw [hc.mem_Q1_iff hs.memM] at hh
    rw [hc.mem_Q1_iff hsy.memM]
    exact ⟨hh.1, H.comm_mem_Z_of_mem_root h34 hs M.one_mem hμM hBμ hμC hne' hsY hh.1 hh.2⟩

theorem Good101.Ut_eq_of_mem_root (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t) {s : G}
    (hsY : s ∈ Y) (hs1 : s ≠ 1) : Ut Q Z s = Ut Q Z t := by
  have hsg : Good101 M Q Z B s := ht.of_mem_root_good101 h34 hspread H hs hsY hs1
  calc Ut Q Z s = (Subgroup.center ↥(Q1 hc s)).map (Q1 hc s).subtype :=
        hc.Ut_eq_center_Q1 hsg.mem_LB
    _ = (Subgroup.center ↥(Q1 hc t)).map (Q1 hc t).subtype := by
        rw [ht.Q1_eq_of_mem_root h34 hspread H hs hsY hs1]
    _ = Ut Q Z t := (hc.Ut_eq_center_Q1 ht.mem_LB).symm

end CFSG.RankThree.GF2n.Stroth80

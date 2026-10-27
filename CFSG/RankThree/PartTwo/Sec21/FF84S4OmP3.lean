module

public import CFSG.RankThree.PartTwo.Sec21.FF84Defs
public import CFSG.RankThree.PartTwo.Sec21.FF84S4OmP1
public import CFSG.ClassicalGroups.Orthogonal.RootGroupCard

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Sec2Omega
  CFSG.ClassicalGroups.Orthogonal MulAction

@[expose] noncomputable def Eτ : Subgroup OmG :=
  CFSG.RankThree.PartTwo.Sec21.FF79.Op 2 (MulAction.stabilizer OmG tau0)

theorem le_Op_of_normalized {G : Type} [Group G] (p : ℕ) {H N : Subgroup G} (hNH : N ≤ H)
    (hnorm : ∀ n ∈ N, ∀ h ∈ H, h * n * h⁻¹ ∈ N) (hp : ∀ n ∈ N, ∃ k : ℕ, n ^ (p ^ k) = 1) :
    N ≤ CFSG.RankThree.PartTwo.Sec21.FF79.Op p H := by
  have hn : (N.subgroupOf H).Normal := by
    constructor
    intro n hn h
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hnorm _ hn h h.2
  have hpg : IsPGroup p ↥(N.subgroupOf H) := by
    intro x
    obtain ⟨k, hk⟩ := hp x.1.1 x.2
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using hk))⟩
  have hle : N.subgroupOf H ≤ CFSG.pCore p ↥H := le_sSup ⟨hn, hpg⟩
  intro n hnN
  refine Subgroup.mem_map.mpr ⟨⟨n, hNH hnN⟩, hle ?_, rfl⟩
  rw [Subgroup.mem_subgroupOf]
  exact hnN

theorem conj_mem_Op {G : Type} [Group G] (p : ℕ) {H : Subgroup G} {g h : G}
    (hg : g ∈ CFSG.RankThree.PartTwo.Sec21.FF79.Op p H) (hh : h ∈ H) :
    h * g * h⁻¹ ∈ CFSG.RankThree.PartTwo.Sec21.FF79.Op p H := by
  obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.mp hg
  have hn : (CFSG.pCore p ↥H).Normal := CFSG.pCore_normal
  refine Subgroup.mem_map.mpr ⟨⟨h, hh⟩ * g' * ⟨h, hh⟩⁻¹, hn.conj_mem _ hg' _, ?_⟩
  simp

theorem eich_conj_P2 {g h : OmG} (hg : g ∈ Eτ) (hh : h ∈ P2) : h * g * h⁻¹ ∈ Eτ :=
  conj_mem_Op 2 hg hh.2

theorem polar_qMinusForm_eq (u v : F6) : QuadraticMap.polar qMinusForm u v = polarMinus u v :=
  polar_qMinusForm u v

theorem qMinusForm_tau0 : qMinusForm tau0 = 0 := by rw [qMinusForm_apply]; exact qMinus_tau0

@[expose] noncomputable def eichOm (w : F6) : OmG :=
  ⟨eichler qMinusForm tau0 w, eichler_mem_timmesfeldOmega tau0 w⟩

theorem eichOm_smul {w : F6} (hw : polarMinus w tau0 = 0) (x : F6) :
    eichOm w • x = x + polarMinus x tau0 • w +
      (polarMinus x w + qMinus w * polarMinus x tau0) • tau0 := by
  show eichler qMinusForm tau0 w x = _
  rw [eichler_apply_qMinus qMinus_tau0 (by rw [polarMinus_comm]; exact hw)]

theorem eichOm_smul_tau0 (w : F6) : eichOm w • tau0 = tau0 :=
  eichler_apply_self tau0 w

@[expose] noncomputable def rootGroupOm : Subgroup OmG :=
  (rootGroup qMinusForm tau0).subgroupOf (CFSG.Open.timmesfeldOmega qMinus)

theorem rootGroup_le_Omega : rootGroup qMinusForm tau0 ≤ CFSG.Open.timmesfeldOmega qMinus :=
  (rootGroup_le_elementaryGroup qMinusForm tau0).trans elementaryGroup_le_timmesfeldOmega

theorem mem_rootGroupOm {g : OmG} :
    g ∈ rootGroupOm ↔ ∃ w, polarMinus w tau0 = 0 ∧
      (g : F6 ≃ₗ[ZMod 2] F6) = eichler qMinusForm tau0 w := by
  rw [rootGroupOm, Subgroup.mem_subgroupOf, mem_rootGroup]
  constructor
  · rintro ⟨w, hw, h⟩
    exact ⟨w, by rw [polar_qMinusForm_eq] at hw; rw [polarMinus_comm]; exact hw, h.symm⟩
  · rintro ⟨w, hw, h⟩
    exact ⟨w, by rw [polar_qMinusForm_eq, polarMinus_comm]; exact hw, h.symm⟩

theorem eichOm_mem_rootGroupOm {w : F6} (hw : polarMinus w tau0 = 0) : eichOm w ∈ rootGroupOm :=
  mem_rootGroupOm.mpr ⟨w, hw, rfl⟩

theorem card_rootGroupOm : Nat.card rootGroupOm = 16 := by
  have h1 : Nat.card rootGroupOm = Nat.card (rootGroup qMinusForm tau0) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe rootGroup_le_Omega).toEquiv
  rw [h1, card_rootGroup qMinusForm_nondegenerate qMinusForm_tau0 tau0_ne_zero, finrank_fin_six,
    Nat.card_zmod]
  norm_num

theorem mul_self_of_mem_rootGroupOm {g : OmG} (hg : g ∈ rootGroupOm) : g * g = 1 :=
  Subtype.ext (sq_eq_one_of_mem_rootGroup (by decide) (Subgroup.mem_subgroupOf.mp hg))

theorem rootGroupOm_le_Eτ : rootGroupOm ≤ Eτ := by
  refine le_Op_of_normalized 2 ?_ ?_ ?_
  · intro g hg
    obtain ⟨w, hw, h⟩ := mem_rootGroupOm.mp hg
    rw [MulAction.mem_stabilizer_iff]
    show (g : F6 ≃ₗ[ZMod 2] F6) tau0 = tau0
    rw [h]
    exact eichler_apply_self tau0 w
  · intro n hn h hh
    have hh' : (h : F6 ≃ₗ[ZMod 2] F6) tau0 = tau0 := MulAction.mem_stabilizer_iff.mp hh
    have hmem := conj_mem_rootGroup_of_apply_eq_smul
      (timmesfeldOmega_le_orthogonalGroup h.2) (c := 1) (u := tau0)
      (by rw [hh', one_smul]) (x := (n : F6 ≃ₗ[ZMod 2] F6)) (Subgroup.mem_subgroupOf.mp hn)
    rw [rootGroupOm, Subgroup.mem_subgroupOf]
    exact hmem
  · intro n hn
    exact ⟨1, by rw [pow_one, pow_two]; exact mul_self_of_mem_rootGroupOm hn⟩

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end

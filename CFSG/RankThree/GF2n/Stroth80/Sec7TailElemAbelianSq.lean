module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.CGT.Timmesfeld75.SLTransvection
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

@[expose] def elemAbSqSub {Y : Type} [Group Y] (L : Subgroup Y)
    (hLcomm : ∀ a ∈ L, ∀ b ∈ L, a * b = b * a) : Subgroup Y where
  carrier := {x | x ∈ L ∧ x * x = 1}
  mul_mem' := by
    rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
    refine ⟨L.mul_mem ha hb, ?_⟩
    calc a * b * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
      _ = a * (a * b) * b := by rw [hLcomm b hb a ha]
      _ = a * a * (b * b) := by simp only [mul_assoc]
      _ = 1 := by rw [ha2, hb2, one_mul]
  one_mem' := ⟨L.one_mem, one_mul 1⟩
  inv_mem' := by
    rintro x ⟨hx, hx2⟩
    refine ⟨L.inv_mem hx, ?_⟩
    rw [← mul_inv_rev, hx2, inv_one]

theorem mem_elemAbSqSub {Y : Type} [Group Y] {L : Subgroup Y}
    {hLcomm : ∀ a ∈ L, ∀ b ∈ L, a * b = b * a} {x : Y} :
    x ∈ elemAbSqSub L hLcomm ↔ x ∈ L ∧ x * x = 1 :=
  Iff.rfl

theorem elemAbSq_mul {Y : Type} [Group Y] (L : Subgroup Y)
    (hLcomm : ∀ a ∈ L, ∀ b ∈ L, a * b = b * a) (a b : L) :
    ((a * b : L) : Y) * ((a * b : L) : Y) = ((a : Y) * (a : Y)) * ((b : Y) * (b : Y)) := by
  have hba : (b : Y) * (a : Y) = (a : Y) * (b : Y) := hLcomm (b : Y) b.2 (a : Y) a.2
  calc ((a * b : L) : Y) * ((a * b : L) : Y)
      = (a : Y) * ((b : Y) * (a : Y)) * (b : Y) := by simp only [Subgroup.coe_mul, mul_assoc]
    _ = (a : Y) * ((a : Y) * (b : Y)) * (b : Y) := by rw [hba]
    _ = ((a : Y) * (a : Y)) * ((b : Y) * (b : Y)) := by simp only [mul_assoc]

@[expose] def elemAbSqHom {Y : Type} [Group Y] (L : Subgroup Y)
    (hLcomm : ∀ a ∈ L, ∀ b ∈ L, a * b = b * a) : L →* Y :=
  MonoidHom.mk' (fun x : L => (x : Y) * (x : Y)) (fun a b => elemAbSq_mul L hLcomm a b)

theorem exists_elemAbelian_of_sq_le {Y : Type} [Group Y] [Finite Y] (V L : Subgroup Y) (q : ℕ)
    (hq4 : 4 ≤ q) (hVL : V ≤ L) (hVcard : Nat.card V = q) (hLcard : Nat.card L = q ^ 5)
    (hLcomm : ∀ a ∈ L, ∀ b ∈ L, a * b = b * a) (hLsq : ∀ x ∈ L, x * x ∈ V)
    (hVsq : ∀ a ∈ V, a * a = 1) :
    ∃ D : Subgroup Y, V ≤ D ∧ D ≤ L ∧ IsElemAbelian 2 D ∧ 2 ^ 6 < Nat.card D ∧
      ∀ k ∈ Subgroup.normalizer (L : Set Y), k ∈ Subgroup.normalizer (D : Set Y) := by
  have hDL : elemAbSqSub L hLcomm ≤ L := fun x hx => (mem_elemAbSqSub.1 hx).1
  refine ⟨elemAbSqSub L hLcomm, ?_, hDL, ?_, ?_, ?_⟩
  · intro a ha
    exact mem_elemAbSqSub.2 ⟨hVL ha, hVsq a ha⟩
  · refine ⟨isMulCommutative_iff.2 fun a b => Subtype.ext ?_, fun x hx => ?_⟩
    · exact hLcomm (a : Y) (mem_elemAbSqSub.1 a.2).1 (b : Y) (mem_elemAbSqSub.1 b.2).1
    · rw [sq]
      exact (mem_elemAbSqSub.1 hx).2
  · have hker : (elemAbSqHom L hLcomm).ker = (elemAbSqSub L hLcomm).subgroupOf L := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact ⟨fun h => mem_elemAbSqSub.2 ⟨x.2, h⟩, fun h => (mem_elemAbSqSub.1 h).2⟩
    have hrange : (elemAbSqHom L hLcomm).range ≤ V := by
      intro y hy
      obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
      exact hLsq (x : Y) x.2
    have hcard := Subgroup.card_ker_mul_card_range (elemAbSqHom L hLcomm)
    rw [hLcard] at hcard
    have hR : Nat.card (elemAbSqHom L hLcomm).range ≤ q := by
      have hle := Subgroup.card_le_of_le hrange
      rwa [hVcard] at hle
    have h1 : q ^ 5 ≤ Nat.card (elemAbSqHom L hLcomm).ker * q := by
      rw [← hcard]
      exact Nat.mul_le_mul_left _ hR
    have h2 : q ^ 4 * q ≤ Nat.card (elemAbSqHom L hLcomm).ker * q := by
      calc q ^ 4 * q = q ^ 5 := (pow_succ q 4).symm
        _ ≤ Nat.card (elemAbSqHom L hLcomm).ker * q := h1
    have h3 : q ^ 4 ≤ Nat.card (elemAbSqHom L hLcomm).ker :=
      Nat.le_of_mul_le_mul_right h2 (by omega)
    have hD : Nat.card (elemAbSqSub L hLcomm) = Nat.card (elemAbSqHom L hLcomm).ker := by
      rw [hker]
      exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDL).toEquiv).symm
    rw [hD]
    calc 2 ^ 6 < 4 ^ 4 := by norm_num
      _ ≤ q ^ 4 := Nat.pow_le_pow_left hq4 4
      _ ≤ Nat.card (elemAbSqHom L hLcomm).ker := h3
  · intro k hk
    rw [Subgroup.mem_normalizer_iff] at hk ⊢
    intro h
    constructor
    · intro hh
      obtain ⟨hhL, hhh⟩ := mem_elemAbSqSub.1 hh
      refine mem_elemAbSqSub.2 ⟨(hk h).1 hhL, ?_⟩
      calc k * h * k⁻¹ * (k * h * k⁻¹) = k * (h * h) * k⁻¹ := by simp [mul_assoc]
        _ = 1 := by rw [hhh]; simp
    · intro hc
      obtain ⟨hcL, hcc⟩ := mem_elemAbSqSub.1 hc
      refine mem_elemAbSqSub.2 ⟨(hk h).2 hcL, ?_⟩
      have key : k * (h * h) * k⁻¹ = 1 := by
        calc k * (h * h) * k⁻¹ = k * h * k⁻¹ * (k * h * k⁻¹) := by simp [mul_assoc]
          _ = 1 := hcc
      calc h * h = k⁻¹ * (k * (h * h) * k⁻¹) * k := by simp [mul_assoc]
        _ = k⁻¹ * 1 * k := by rw [key]
        _ = 1 := by simp

end CFSG.RankThree.GF2n.Stroth80

module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma14Base

import CFSG.CharacterTheory.Wreathed.FullDefectCanonicalStructure
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec21.FF84S4PreAct

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B K : Subgroup G}

theorem conj_cenS {g c : G} (hg : g ∈ Nor L) (hc : c ∈ CenS L) : g * c * g⁻¹ ∈ CenS L := by
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hl' : g⁻¹ * l * g ∈ L := by
    have := (Subgroup.mem_normalizer_iff.1 hg (g⁻¹ * l * g)).2
    rw [show g * (g⁻¹ * l * g) * g⁻¹ = l by group] at this
    exact this hl
  have hc' : (g⁻¹ * l * g) * c = c * (g⁻¹ * l * g) := Subgroup.mem_centralizer_iff.1 hc _ hl'
  have e1 : l * (g * c * g⁻¹) = g * ((g⁻¹ * l * g) * c) * g⁻¹ := by group
  have e2 : (g * c * g⁻¹) * l = g * (c * (g⁻¹ * l * g)) * g⁻¹ := by group
  rw [e1, e2, hc']

theorem L_inf_cenS (hZ : Subgroup.center L = ⊥) : ∀ z ∈ L, z ∈ CenS L → z = 1 := by
  intro z hz hzc
  have : (⟨z, hz⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hzc g g.2)
  rw [hZ, Subgroup.mem_bot] at this
  exact congrArg Subtype.val this

theorem b_mem_cenS (h : FF84Sec4 b L B K b₁ b₂) : b ∈ CenS L := by
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  exact Subgroup.mem_centralizer_singleton_iff.1 (h.hyp.hLC hl)

theorem B_inf_Q (h : FF84Sec4 b L B K b₁ b₂) (hZ : Subgroup.center L = ⊥) :
    B ⊓ (Cen b ⊓ CenS L) = Subgroup.zpowers b := by
  apply le_antisymm
  · rintro x ⟨hxB, -, hxc⟩
    obtain ⟨a, c, d, rfl⟩ := coord_of_mem_B h hxB
    have hb₁L : b₁ ∈ L := (Subgroup.mem_inf.1 h.hb₁).2
    have hb₂L : b₂ ∈ L := (Subgroup.mem_inf.1 h.hb₂).2
    have hbz : b ^ a ∈ CenS L := Subgroup.zpow_mem _ (b_mem_cenS h) a
    have hy : b₁ ^ c * b₂ ^ d ∈ CenS L := by
      have := mul_mem (inv_mem hbz) hxc
      rwa [show (b ^ a)⁻¹ * (b ^ a * b₁ ^ c * b₂ ^ d) = b₁ ^ c * b₂ ^ d by group] at this
    have hyL : b₁ ^ c * b₂ ^ d ∈ L :=
      mul_mem (Subgroup.zpow_mem _ hb₁L c) (Subgroup.zpow_mem _ hb₂L d)
    have := L_inf_cenS hZ _ hyL hy
    rw [mul_assoc, this, mul_one]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) a
  · refine Subgroup.zpowers_le.2 ⟨mem_b h, Subgroup.mem_centralizer_singleton_iff.2 rfl,
      b_mem_cenS h⟩

theorem Q_norm (h : FF84Sec4 b L B K b₁ b₂) : ∀ g ∈ Cen b, ∀ c ∈ Cen b ⊓ CenS L,
    g * c * g⁻¹ ∈ Cen b ⊓ CenS L := by
  intro g hg c hc
  obtain ⟨hcb, hcL⟩ := Subgroup.mem_inf.1 hc
  refine Subgroup.mem_inf.2 ⟨?_, conj_cenS (h.hyp.hLN hg) hcL⟩
  have e1 := Subgroup.mem_centralizer_singleton_iff.1 hg
  have e2 := Subgroup.mem_centralizer_singleton_iff.1 hcb
  refine Subgroup.mem_centralizer_singleton_iff.2 ?_
  calc g * c * g⁻¹ * b = g * c * (g⁻¹ * b) := by rw [mul_assoc]
    _ = g * c * (b * g⁻¹) := by
        congr 1
        calc g⁻¹ * b = g⁻¹ * (b * g) * g⁻¹ := by group
          _ = g⁻¹ * (g * b) * g⁻¹ := by rw [e1]
          _ = b * g⁻¹ := by group
    _ = g * (c * b) * g⁻¹ := by group
    _ = g * (b * c) * g⁻¹ := by rw [e2]
    _ = b * (g * c * g⁻¹) := by
        calc g * (b * c) * g⁻¹ = (g * b) * c * g⁻¹ := by group
          _ = (b * g) * c * g⁻¹ := by rw [e1]
          _ = b * (g * c * g⁻¹) := by group

theorem Q_decomp (h : FF84Sec4 b L B K b₁ b₂) (hZ : Subgroup.center L = ⊥) :
    ∀ c ∈ Cen b ⊓ CenS L, ∃ i : ℤ, ∃ x ∈ Opp 3 (Cen b), c = b ^ i * x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C₀ := Cen b ⊓ CenS L with hC₀
  have hBsyl : IsSylowOf 3 (B ⊓ C₀) C₀ :=
    FF79.L14.isSylowOf_inf_normal h.sylB inf_le_left (Q_norm h)
  rw [B_inf_Q h hZ] at hBsyl
  have hP0p : IsPGroup 3 ((Subgroup.zpowers b).subgroupOf C₀) := hBsyl.2.1.comap_subtype
  have hidx : ¬ 3 ∣ ((Subgroup.zpowers b).subgroupOf C₀).index :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hBsyl.2.2
  let P : Sylow 3 ↥C₀ := hP0p.toSylow hidx
  have hPc : (P : Subgroup ↥C₀) ≤ Subgroup.center ↥C₀ := by
    intro p hp
    rw [Subgroup.mem_center_iff]
    intro q
    have hp' : (p : G) ∈ Subgroup.zpowers b := Subgroup.mem_subgroupOf.mp hp
    have hbq : (q : G) * b = b * q := Subgroup.mem_centralizer_singleton_iff.1 q.2.1
    have hpq : (q : G) * (p : G) = (p : G) * q := by
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hp'
      rw [← hi]
      exact ((Commute.zpow_right (show Commute (q : G) b from hbq) i)).eq
    exact Subtype.ext hpq
  have hcomp := CFSG.FullDefectCanonical.pPrimeCore_isComplement_of_central P hPc
  intro c hc
  obtain ⟨⟨⟨m, hm⟩, ⟨p, hp⟩⟩, hx, -⟩ := hcomp.existsUnique (⟨c, hc⟩ : ↥C₀)
  have hmX : (m : G) ∈ Opp 3 (Cen b) :=
    FF79.L14.Opp_le_Opp_of_normalized inf_le_left (Q_norm h)
      (Subgroup.mem_map.mpr ⟨m, hm, rfl⟩)
  have hpZ : (p : G) ∈ Subgroup.zpowers b := Subgroup.mem_subgroupOf.mp hp
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hpZ
  refine ⟨i, m, hmX, ?_⟩
  have hc' : c = m * p := (congrArg Subtype.val hx).symm
  rw [hc', ← hi]
  have hmc : (m : G) ∈ Cen b := FF79.L14.Opp_le 3 _ hmX
  have : (m : G) * b = b * m := Subgroup.mem_centralizer_singleton_iff.1 hmc
  exact (((show Commute (m : G) b from this).zpow_right i)).eq

theorem Q_eq (h : FF84Sec4 b L B K b₁ b₂) (hZ : Subgroup.center L = ⊥)
    (hX : Opp 3 (Cen b) = ⊥) : ∀ c ∈ Cen b ⊓ CenS L, c ∈ Subgroup.zpowers b := by
  intro c hc
  obtain ⟨i, x, hx, rfl⟩ := Q_decomp h hZ c hc
  rw [hX, Subgroup.mem_bot] at hx
  rw [hx, mul_one]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) i

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

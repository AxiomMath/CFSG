module

public import CFSG.Sporadic.MI301Five.HNShape
public import CFSG.Sporadic.MI301Five.RowK
public import CFSG.Sporadic.MI301.RowMax
public import CFSG.Sporadic.MI301.LeechLayer
public import CFSG.Monster.GMS.ExistenceBridge

public section

namespace CFSG.Sporadic.MI301Five

open CFSG.Blueprint CFSG.Open CFSG.Monster.Existence CFSG.Monster.GMS
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.Yardstones.Md0ec50421ce4
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S8
  CFSG.LocalAnalysis.GLTheoremA.H301 Subgroup

variable {G : Type} [Group G]

private theorem card_cent_of_isTwoACentralizer {α : G} (hα : orderOf α = 2)
    (h : IsTwoACentralizer α) (hB : Nat.card NativeSporadic.B = monsterBabyOrder) :
    Nat.card ↥(cent α) = 2 * monsterBabyOrder := by
  obtain ⟨-, hz, ⟨e⟩⟩ := h
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥(cent α))
  have hc : Nat.card ↥(Subgroup.center ↥(cent α)) = 2 := by
    rw [← Subgroup.card_map_of_injective (cent α).subtype_injective, hz, Nat.card_zpowers, hα]
  rw [Nat.card_congr e.toEquiv, hB, hc] at h1
  omega

theorem exists_invertedByTwoA_five (hE : MonsterExistenceStatement G)
    (hB : Nat.card NativeSporadic.B = monsterBabyOrder) :
    ∃ d : G, orderOf d = 5 ∧ InvertedByTwoA d := by
  obtain ⟨-, a, z, ha, -, -, -, hA, -, hgraph⟩ := hE
  obtain ⟨-, c, -, -, -, -, hord, -, hex, -⟩ := hgraph
  obtain ⟨α, β, hα, hβ, hc⟩ := hex 7
  have hα2 : orderOf α = 2 := (orderOf_eq_of_isConj' hα).symm.trans ha
  have hβ2 : orderOf β = 2 := (orderOf_eq_of_isConj' hβ).symm.trans ha
  have hαα : α * α = 1 := by rw [← pow_two, ← hα2, pow_orderOf_eq_one]
  have hββ : β * β = 1 := by rw [← pow_two, ← hβ2, pow_orderOf_eq_one]
  have hαi : α⁻¹ = α := inv_eq_of_mul_eq_one_right hαα
  have hβi : β⁻¹ = β := inv_eq_of_mul_eq_one_right hββ
  refine ⟨α * β, ?_, α, hα2, card_cent_of_isTwoACentralizer hα2 (hA α hα) hB, ?_⟩
  · rw [orderOf_eq_of_isConj' hc, hord 7]
    rfl
  · rw [hαi, mul_inv_rev, hαi, hβi, ← mul_assoc, hαα, one_mul]

variable [Finite G] {α d z : G}


theorem FiveFrame.i301ARowCfg (F : FiveFrame α d z)
    (hOut : ∀ σ : MulAut G, ∃ g : G, σ = MulAut.conj g)
    (hrk : GLATwoLocalRank 5 NativeSporadic.Co1 < 3) {B₁ : Subgroup G}
    (hB : IsElemAbelian 5 B₁ ∧ Nat.card B₁ = 5 ^ 3) (hdB : d ∈ B₁)
    (hBX : B₁ ≤ zpowers d ⊔ (cent2 α d ⊓ cent z))
    (hR0 : Nat.card (rowR0Of d (leechQ z)) = 2 ^ 9) (hR0t : IsExtraSpec2 (rowR0Of d (leechQ z)))
    (hc : centerOf (rowR0Of d (leechQ z)) = zpowers z) :
    I301ARowCfg .m5 (leechQ z) B₁ d := by
  have hL : GMSLeechCentralizer z := GMSLeechCentralizer.of_isTwoBCentralizer F.orderOf_z F.twoB
  have hdz : d ∈ cent z :=
    mem_centralizer_singleton_iff.2 (mem_centralizer_singleton_iff.1 F.mem_z.2).symm
  have hBz : B₁ ≤ cent z := hBX.trans (sup_le (zpowers_le.2 hdz) inf_le_right)
  have hd1 : d ≠ 1 := by
    intro h
    have h1 := F.orderOf_d
    rw [h, orderOf_one] at h1
    exact absurd h1 (by norm_num)
  have hpC : 5 ∣ Nat.card NativeSporadic.Co1 := by
    rw [CFSG.Sporadic.Co1.card_Co1]
    norm_num
  exact
    { hR := CFSG.Sporadic.MI301.leech_hR hL
      hB := hB
      hBN := by rw [CFSG.Sporadic.MI301.normalizer_leechQ hL]; exact hBz
      hd := ⟨hdB, hd1⟩
      hI := F.hI
      hK := F.hK hL F.shape
      hR0 := hR0
      hR0t := Or.inl hR0t
      hK6 := Or.inr (F.hK6 hL hc)
      hNL := fun _ => CFSG.Sporadic.MI301.leech_hNL hL Nat.prime_five (by norm_num) hpC
      hMax := CFSG.Sporadic.MI301.hMax_leech hL Nat.prime_five (by norm_num) hrk hOut hB.1 hB.2
        hBz }

end CFSG.Sporadic.MI301Five

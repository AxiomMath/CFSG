module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec9Defs
import CFSG.RankThree.GF2n.Stroth80.Sec8BridgeModel

public section

namespace CFSG.RankThree.GF2n.Stroth80.HS9

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
  {M Q Z B Y : Subgroup G}

theorem exists_comm_conj_of_cover (hc : Ctx M Q Z B) (hYM : Y ≤ M)
    (hcard : Nat.card ↥(Uline Z B Y) = Nat.card Z ^ 3)
    (hcover : ∀ u ∈ Uline Z B Y, u ∉ Z → ∃ y ∈ Y, u ∈ (conjSubgroup y B ⊔ Z : Subgroup G))
    {m : G} (hm : m ∈ M) :
    ∃ y ∈ Y, ∀ b ∈ conjSubgroup y B, ∀ f ∈ conjSubgroup m B, b * f = f * b := by
  classical
  obtain ⟨K, _, _, -, γ, M₀, hD⟩ := stroth_globalModelData hc.hyp
  have hcF : Ctx M Q Z (conjSubgroup m B) := hc.conj_of_mem hm
  obtain ⟨e, -, -, he, -, -⟩ := hcF.dictB hD
  have hUQ : Uline Z B Y ≤ Q := by
    refine sup_le hc.hyp.Z_normal.1 (iSup₂_le fun y hy => ?_)
    exact (hc.conj_of_mem (hYM hy)).le
  let φ : ↥(Uline Z B Y) →* Multiplicative K :=
    { toFun := fun x => Multiplicative.ofAdd (M₀.B (M₀.π (x : G)) e)
      map_one' := by simp [Tim79.QuadModel.pi_one M₀]
      map_mul' := fun x y => by
        simp only [Subgroup.coe_mul]
        rw [M₀.π_mul (x : G) (hUQ x.2) (y : G) (hUQ y.2), map_add, LinearMap.add_apply]
        rfl }
  have hφcard : Nat.card φ.range ≤ Nat.card K := by
    calc
      Nat.card φ.range ≤ Nat.card (Multiplicative K) := Subgroup.card_le_card_group φ.range
      _ = Nat.card K := Nat.card_congr Multiplicative.toAdd
  have hker_ge : Nat.card Z ^ 2 ≤ Nat.card φ.ker := by
    have h1 := Subgroup.card_ker_mul_card_range φ
    have h2 : Nat.card Z ^ 2 * Nat.card Z ≤ Nat.card φ.ker * Nat.card Z := by
      calc
        Nat.card Z ^ 2 * Nat.card Z = Nat.card Z ^ 3 := by ring
        _ = Nat.card ↥(Uline Z B Y) := hcard.symm
        _ = Nat.card φ.ker * Nat.card φ.range := h1.symm
        _ ≤ Nat.card φ.ker * Nat.card K := Nat.mul_le_mul_left _ hφcard
        _ = Nat.card φ.ker * Nat.card Z := by rw [hD.card]
    exact Nat.le_of_mul_le_mul_right h2 Nat.card_pos
  have hZU : Z ≤ Uline Z B Y := le_sup_left
  have hnotle : ¬ φ.ker ≤ Z.subgroupOf (Uline Z B Y) := by
    intro hle
    have hker_le : Nat.card φ.ker ≤ Nat.card Z := by
      calc
        Nat.card φ.ker ≤ Nat.card ↥(Z.subgroupOf (Uline Z B Y)) := Subgroup.card_le_of_le hle
        _ = Nat.card Z := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv
    have hq2 : Nat.card Z ^ 2 ≤ Nat.card Z := hker_ge.trans hker_le
    have hq1 : Nat.card Z ≤ 1 := by
      have hqpos : 0 < Nat.card Z := Nat.card_pos
      exact Nat.le_of_mul_le_mul_left (by simpa [pow_two, mul_one] using hq2) hqpos
    have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
    omega
  obtain ⟨u, huk, huZ⟩ := Set.not_subset.mp hnotle
  have huU : (u : G) ∈ Uline Z B Y := u.2
  have hune : (u : G) ∉ Z := fun h => huZ (Subgroup.mem_subgroupOf.mpr h)
  have huk' : M₀.B (M₀.π (u : G)) e = 0 :=
    ofAdd_eq_one.mp (MonoidHom.mem_ker.mp huk)
  obtain ⟨y, hy, huy⟩ := hcover (u : G) huU hune
  have hcY : Ctx M Q Z (conjSubgroup y B) := hc.conj_of_mem (hYM hy)
  obtain ⟨ey, -, -, hey, -, -⟩ := hcY.dictB hD
  have huZ' : (u : G) ∈ Z ⊔ conjSubgroup y B := by simpa [sup_comm] using huy
  have hpi : M₀.π (u : G) ∈ M₀.img (conjSubgroup y B) :=
    sec8_img_sup_le M₀ hcY (Tim79.QuadModel.pi_mem_img M₀ huZ' (hUQ u.2))
  obtain ⟨s, hs⟩ := (hey (M₀.π (u : G))).mp hpi
  have hpi0 : M₀.π (u : G) ≠ 0 := fun h0 =>
    hune ((M₀.π_ker (u : G) (hUQ u.2)).mp h0)
  have hsu : s ≠ 0 := by
    intro hs0
    exact hpi0 (by rw [hs, hs0, zero_smul])
  have hBey : M₀.B ey e = 0 := by
    have h0 := huk'
    rw [hs, map_smul, LinearMap.smul_apply, smul_eq_mul] at h0
    exact (mul_eq_zero.mp h0).resolve_left hsu
  refine ⟨y, hy, ?_⟩
  exact (Tim79.QuadModel.commute_iff M₀ hD.reg hcY.le hcF.le).mpr fun e' he' f' hf' => by
    obtain ⟨r, rfl⟩ := (hey e').mp he'
    obtain ⟨t, rfl⟩ := (he f').mp hf'
    simp [hBey]

end CFSG.RankThree.GF2n.Stroth80.HS9

module

public import CFSG.Sporadic.Schreier.LyDoubleCover
public import CFSG.Sporadic.Schreier.LySevenProof
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.LyAbstract
public import CFSG.RankThree.PartOne.KS.LyFiveGeneric

public noncomputable section

namespace CFSG.Sporadic.LySchreier

open CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier.Native CFSG.Sporadic.Ly.Omega MulAction

theorem card_centralizer_conj_eq {G : Type*} [Group G] (v x : G) :
    Nat.card (Subgroup.centralizer ({v * x * v⁻¹} : Set G)) =
      Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  refine Nat.card_congr
    { toFun := fun y => ⟨v⁻¹ * y * v, ?_⟩
      invFun := fun y => ⟨v * y * v⁻¹, ?_⟩
      left_inv := fun y => Subtype.ext (by group)
      right_inv := fun y => Subtype.ext (by group) }
  · have hy := Subgroup.mem_centralizer_singleton_iff.1 y.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc v⁻¹ * y * v * x = v⁻¹ * (y * (v * x * v⁻¹)) * v := by group
      _ = v⁻¹ * ((v * x * v⁻¹) * y) * v := by rw [hy]
      _ = x * (v⁻¹ * y * v) := by group
  · have hy := Subgroup.mem_centralizer_singleton_iff.1 y.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc v * y * v⁻¹ * (v * x * v⁻¹) = v * (y * x) * v⁻¹ := by group
      _ = v * (x * y) * v⁻¹ := by rw [hy]
      _ = v * x * v⁻¹ * (v * y * v⁻¹) := by group

theorem full_involution_centralizer :
    lyC = Subgroup.centralizer {lyz} ∧
      Nat.card (Subgroup.centralizer ({lyz} : Set J)) = 39916800 := by
  classical
  obtain ⟨-, hzv, hzc, -, -, -, -, hcard, -⟩ := centralizer_double_cover
  obtain ⟨-, -, -, -, ht, -, htcard⟩ := seven_space_centralizer_bound
  have hC : lyC ≤ Subgroup.centralizer {lyz} := by
    intro c hc
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := congrArg Subtype.val (Subgroup.mem_center_iff.1 hzc ⟨c, hc⟩)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hzv] at this
    exact this
  have hz : lyt • omegaE = omegaE := Subtype.ext ly_certificate.2.2.2.2.2.2.1
  let F : Finset (orbit J opE) := (Set.toFinite {y : orbit J opE | lyt • y = y}).toFinset
  have hF : ∀ y : orbit J opE, lyt • y = y → y ∈ F := fun y hy => by
    rw [Set.Finite.mem_toFinset]
    exact hy
  have hFc : F.card ≤ 2772 := by
    have e := Set.ncard_eq_toFinset_card {y : orbit J opE | lyt • y = y} (Set.toFinite _)
    rw [← e, ← Nat.card_coe_set_eq]
    exact ly_certificate.2.2.2.2.2.2.2.1
  have h1 := CFSG.ClassicalInvolution.card_centralizer_le_of_fixed lyt omegaE hz F hF
  rw [stabilizer_omegaE, CFSG.RankThree.PartOne.card_centralizer_inf_eq lyH lyt ht] at h1
  have hzt : Nat.card (Subgroup.centralizer ({lyz} : Set J)) =
      Nat.card (Subgroup.centralizer ({lyt} : Set J)) := by
    have e : lyz = lyv * lyt * lyv⁻¹ := by
      change lyz = lyv * (lyv⁻¹ * lyz * lyv) * lyv⁻¹
      group
    rw [e]
    exact card_centralizer_conj_eq lyv lyt
  have hle : Nat.card (Subgroup.centralizer ({lyz} : Set J)) ≤ Nat.card lyC := by
    rw [hcard, hzt]
    exact h1.trans ((Nat.mul_le_mul hFc htcard).trans (by norm_num))
  have heq := Subgroup.eq_of_le_of_card_ge hC hle
  exact ⟨heq, by rw [← heq, hcard]⟩

end CFSG.Sporadic.LySchreier

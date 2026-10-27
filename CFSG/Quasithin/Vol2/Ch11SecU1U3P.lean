module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.U3

open scoped MatrixGroups

theorem eq_one_or_neg_one_of_mul_self {K : Type} [Field K] (h2 : (2 : K) ≠ 0)
    {S : Matrix (Fin 2) (Fin 2) K} (hS : S * S = 1) (hdet : S.det = 1) : S = 1 ∨ S = -1 := by
  have e00 := congrFun (congrFun hS 0) 0
  have e01 := congrFun (congrFun hS 0) 1
  have e10 := congrFun (congrFun hS 1) 0
  have e11 := congrFun (congrFun hS 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  rw [Matrix.det_fin_two] at hdet
  by_cases had : S 0 0 + S 1 1 = 0
  · exfalso
    apply h2
    linear_combination S 0 0 * had - e00 - hdet
  · have hb : S 0 1 = 0 := by
      have : S 0 1 * (S 0 0 + S 1 1) = 0 := by linear_combination e01
      exact (mul_eq_zero.mp this).resolve_right had
    have hc : S 1 0 = 0 := by
      have : S 1 0 * (S 0 0 + S 1 1) = 0 := by linear_combination e10
      exact (mul_eq_zero.mp this).resolve_right had
    have hda : S 1 1 = S 0 0 := by
      linear_combination S 0 0 * hdet - S 1 1 * e00 + S 0 0 * S 1 0 * hb + S 1 1 * S 1 0 * hb
    have ha : (S 0 0 - 1) * (S 0 0 + 1) = 0 := by
      linear_combination e00 - S 1 0 * hb
    have hS1 : S = Matrix.scalar (Fin 2) (S 0 0) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hb, hc, hda, Matrix.scalar_apply]
    rcases mul_eq_zero.mp ha with h | h
    · left
      rw [hS1, show S 0 0 = 1 by linear_combination h, map_one]
    · right
      rw [hS1, show S 0 0 = -1 by linear_combination h, map_neg, map_one]

theorem sl2_eq_one_or_neg_one {K : Type} [Field K] (h2 : (2 : K) ≠ 0) {g : SL(2, K)}
    (hg : g * g = 1) : g = 1 ∨ g = -1 := by
  have hS : (g : Matrix (Fin 2) (Fin 2) K) * g = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hg, Matrix.SpecialLinearGroup.coe_one]
  rcases eq_one_or_neg_one_of_mul_self h2 hS g.2 with h | h
  · exact Or.inl (Subtype.ext (by rw [h, Matrix.SpecialLinearGroup.coe_one]))
  · exact Or.inr (Subtype.ext (by
      rw [h, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]))

variable {G : Type} [Group G]

theorem mul_mem_centralizer_of_pair {L Y : Subgroup G} {y : G} (hYL : Y ≤ L)
    (hyC : y ∈ Subgroup.centralizer (Y : Set G)) (hy1 : y ≠ 1) (hy2 : y * y = 1)
    (hY2 : ∀ s ∈ Y, s * s = 1 → s = 1 ∨ s = y)
    (hLC : ∀ g ∈ L, g ∈ Subgroup.centralizer (Y : Set G) → g = 1 ∨ g = y)
    (hout : ∀ t₁ t₂ : G, t₁ ∉ L → t₂ ∉ L → orderOf t₁ = 2 → orderOf t₂ = 2 →
      t₁ * t₂ = t₂ * t₁ → t₁ * t₂ ∈ L)
    {a₁ a₂ s₁ s₂ : G} (hs₁ : s₁ ∈ Y) (hs₂ : s₂ ∈ Y)
    (hn₁ : a₁ * s₁⁻¹ ∈ Subgroup.centralizer (Y : Set G))
    (hn₂ : a₂ * s₂⁻¹ ∈ Subgroup.centralizer (Y : Set G))
    (hn₁y : a₁ * s₁⁻¹ * y = y * (a₁ * s₁⁻¹))
    (hs₁C : s₁ ∉ Subgroup.centralizer (Y : Set G)) (hs₂C : s₂ ∉ Subgroup.centralizer (Y : Set G))
    (ha₁ : a₁ * a₁ = 1) (ha₂ : a₂ * a₂ = 1) (ha : a₁ * a₂ = a₂ * a₁) :
    s₁ * s₂ ∈ Subgroup.centralizer (Y : Set G) := by
  set n₁ := a₁ * s₁⁻¹ with hn₁def
  set n₂ := a₂ * s₂⁻¹ with hn₂def
  have hcY : ∀ {n s : G}, n ∈ Subgroup.centralizer (Y : Set G) → s ∈ Y → s * n = n * s :=
    fun hn hs => Subgroup.mem_centralizer_iff.mp hn _ hs
  have ha₁e : a₁ = n₁ * s₁ := by rw [hn₁def, inv_mul_cancel_right]
  have ha₂e : a₂ = n₂ * s₂ := by rw [hn₂def, inv_mul_cancel_right]
  have h1C : (1 : G) ∈ Subgroup.centralizer (Y : Set G) := Subgroup.one_mem _
  have hsq : ∀ {n s a : G}, n ∈ Subgroup.centralizer (Y : Set G) → s ∈ Y →
      s ∉ Subgroup.centralizer (Y : Set G) → a = n * s → a * a = 1 → s * s = y ∧ n * n = y := by
    intro n s a hn hs hsC hae haa
    have hns : s * n = n * s := hcY hn hs
    have h1 : n * n * (s * s) = 1 := by
      rw [← haa, hae]
      calc n * n * (s * s) = n * (n * s) * s := by group
        _ = n * (s * n) * s := by rw [hns]
        _ = n * s * (n * s) := by group
    have hss : s * s = (n * n)⁻¹ := eq_inv_of_mul_eq_one_right h1
    have hssC : s * s ∈ Subgroup.centralizer (Y : Set G) := by
      rw [hss]
      exact Subgroup.inv_mem _ (Subgroup.mul_mem _ hn hn)
    have hssy : s * s = y := by
      rcases hLC _ (L.mul_mem (hYL hs) (hYL hs)) hssC with h | h
      · rcases hY2 s hs h with h' | h' <;> rw [h'] at hsC
        · exact absurd h1C hsC
        · exact absurd hyC hsC
      · exact h
    refine ⟨hssy, ?_⟩
    have : n * n = (s * s)⁻¹ := by rw [hss, inv_inv]
    rw [this, hssy]
    exact inv_eq_of_mul_eq_one_right hy2
  obtain ⟨hs₁s, hn₁s⟩ := hsq hn₁ hs₁ hs₁C ha₁e ha₁
  obtain ⟨hs₂s, hn₂s⟩ := hsq hn₂ hs₂ hs₂C ha₂e ha₂
  have hnL : ∀ {n : G}, n ∈ Subgroup.centralizer (Y : Set G) → n * n = y → n ∉ L := by
    intro n hn hnn hnL
    rcases hLC n hnL hn with h | h <;> rw [h] at hnn
    · exact hy1 (by rw [← hnn, one_mul])
    · exact hy1 (by rw [← hnn, hy2])
  have haL : ∀ {n s a : G}, n ∈ Subgroup.centralizer (Y : Set G) → n * n = y → s ∈ Y →
      a = n * s → a ∉ L := by
    intro n s a hn hnn hs hae haL
    apply hnL hn hnn
    have : n = a * s⁻¹ := by rw [hae, mul_inv_cancel_right]
    rw [this]
    exact L.mul_mem haL (L.inv_mem (hYL hs))
  have ha₁L := haL hn₁ hn₁s hs₁ ha₁e
  have ha₂L := haL hn₂ hn₂s hs₂ ha₂e
  have hord : ∀ {a : G}, a ∉ L → a * a = 1 → orderOf a = 2 := fun haL haa =>
    orderOf_eq_prime (by rw [sq]; exact haa) fun h => haL (h ▸ L.one_mem)
  have h12 := hout a₁ a₂ ha₁L ha₂L (hord ha₁L ha₁) (hord ha₂L ha₂) ha
  have hprod : a₁ * a₂ = n₁ * n₂ * (s₁ * s₂) := by
    rw [ha₁e, ha₂e]
    calc n₁ * s₁ * (n₂ * s₂) = n₁ * (s₁ * n₂) * s₂ := by group
      _ = n₁ * (n₂ * s₁) * s₂ := by rw [hcY hn₂ hs₁]
      _ = n₁ * n₂ * (s₁ * s₂) := by group
  have hnnL : n₁ * n₂ ∈ L := by
    have : n₁ * n₂ = a₁ * a₂ * (s₁ * s₂)⁻¹ := by rw [hprod, mul_inv_cancel_right]
    rw [this]
    exact L.mul_mem h12 (L.inv_mem (L.mul_mem (hYL hs₁) (hYL hs₂)))
  have hnn : n₁ * n₂ = n₂ * n₁ := by
    rcases hLC _ hnnL (Subgroup.mul_mem _ hn₁ hn₂) with h | h
    · have : n₂ = n₁⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [this, mul_inv_cancel, inv_mul_cancel]
    · have : n₂ = n₁⁻¹ * y := by rw [← h, inv_mul_cancel_left]
      rw [this, mul_inv_cancel_left]
      calc y = n₁⁻¹ * (n₁ * y) := by group
        _ = n₁⁻¹ * (y * n₁) := by rw [hn₁y]
        _ = n₁⁻¹ * y * n₁ := by group
  have hss : s₁ * s₂ = s₂ * s₁ := by
    have hprod' : a₂ * a₁ = n₂ * n₁ * (s₂ * s₁) := by
      rw [ha₁e, ha₂e]
      calc n₂ * s₂ * (n₁ * s₁) = n₂ * (s₂ * n₁) * s₁ := by group
        _ = n₂ * (n₁ * s₂) * s₁ := by rw [hcY hn₁ hs₂]
        _ = n₂ * n₁ * (s₂ * s₁) := by group
    have := ha
    rw [hprod, hprod', hnn] at this
    exact mul_left_cancel this
  have hsq12 : s₁ * s₂ * (s₁ * s₂) = 1 := by
    calc s₁ * s₂ * (s₁ * s₂) = s₁ * (s₂ * s₁) * s₂ := by group
      _ = s₁ * (s₁ * s₂) * s₂ := by rw [hss]
      _ = s₁ * s₁ * (s₂ * s₂) := by group
      _ = 1 := by rw [hs₁s, hs₂s, hy2]
  rcases hY2 _ (Y.mul_mem hs₁ hs₂) hsq12 with h | h <;> rw [h]
  · exact h1C
  · exact hyC

end CFSG.Quasithin.Vol2.Ch11.SecU1.U3

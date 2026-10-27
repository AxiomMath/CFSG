module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.SmithD321Ext
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Lemma19

public section

namespace CFSG.Quasithin.H13.T326

open CFSG.Quasithin CFSG.Quasithin.SmithD321 CFSG.Quasithin.SmithD39Two CFSG.Quasithin.Z391
  CFSG.Quasithin.SmithD391 CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Open
open scoped Pointwise

variable {W : Type} [CommGroup W] [Finite W]

theorem prime_of_side {M Mp X : Subgroup (MulAut W)} {V : Subgroup W}
    (hW : ∀ w : W, w ^ 2 = 1) {hMp : M ≤ Subgroup.normalizer (Mp : Set (MulAut W))}
    (hS : SideHyp hMp X V) {y : MulAut W} (hy : y ∈ M) (hyX : ∀ l ∈ X, y * l = l * y)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hyp : letI := qAct hMp; ∀ q ∈ tilde Mp ⊤ (commV X), (⟨y, hy⟩ : ↥M) ^ p • q = q)
    (hmove : letI := qAct hMp; ∃ q ∈ tilde Mp ⊤ (commV X), (⟨y, hy⟩ : ↥M) • q ≠ q) :
    letI := qAct hMp
    p = 3 ∨ p = 7 ∨
      (p = 5 ∧ ∀ q ∈ tilde Mp ⊤ (commV X), (⟨y, hy⟩ : ↥M) • q = q → q = 1) := by
  let _i := qAct hMp
  set Λ := X.subgroupOf M with hΛ
  set Y := tilde Mp ⊤ (commV X) with hYdef
  set y₀ : ↥M := ⟨y, hy⟩ with hy₀
  have hQ : ∀ q : W ⧸ modFix Mp (⊤ : Subgroup W), q ^ 2 = 1 := quot_sq_of hW _
  have hI := hS.irr
  have hY := hS.homog
  obtain ⟨K, hKf, hKfin, π, hK, hR⟩ := hS.nat
  have hE := card_end_eq_two_of_nat hMp hS.le hK hR hI
  have hyΛ : ∀ l ∈ Λ, l * y₀ = y₀ * l := fun l hl =>
    Subtype.ext (hyX _ (Subgroup.mem_subgroupOf.1 hl)).symm
  have hyN : y ∈ Subgroup.normalizer (X : Set (MulAut W)) := by
    refine Subgroup.mem_normalizer_iff.2 fun l => ⟨fun hl => ?_, fun hl => ?_⟩
    · rw [hyX l hl, mul_inv_cancel_right]
      exact hl
    · have h1 := hyX _ hl
      have h2 : y * l * y⁻¹ = l := mul_left_cancel (h1.trans (by group))
      rw [h2] at hl
      exact hl
  have hyY : ∀ q ∈ Y, y₀ • q ∈ Y := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨_, B15P4.map_commV_mem hyN u hu, rfl⟩
  set F := Y ⊓ XMod.fixed ↥(Subgroup.zpowers y₀) ⊤ with hFdef
  have hFinv : XMod.IsInv ↥Λ F := by
    rintro ⟨l, hl⟩ q ⟨hqY, hqF⟩
    refine ⟨hY.1 ⟨l, hl⟩ q hqY, (mem_fixed_zpowers_iff (b := y₀)).2 ?_⟩
    have h1 := (mem_fixed_zpowers_iff (b := y₀)).1 hqF
    show y₀ • (l • q) = l • q
    rw [smul_smul, ← hyΛ l hl, mul_smul, h1]
  obtain ⟨c', hc'⟩ := IsotypicOfLength.exists_of_le hQ hI hY hFinv inf_le_left
  have hlt : c' < 4 := by
    obtain ⟨q, hq, hqy⟩ := hmove
    have hFY : F < Y := lt_of_le_of_ne inf_le_left fun hFY => by
      have hqF : q ∈ F := hFY ▸ hq
      exact hqy ((mem_fixed_zpowers_iff (b := y₀)).1 hqF.2)
    have h1 := Subgroup.card_lt_of_lt hFY
    rw [card_eq_two_pow hQ F, card_eq_two_pow hQ Y] at h1
    have h2 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 h1
    rw [hc'.2.2, hY.2.2] at h2
    exact Nat.lt_of_mul_lt_mul_right h2
  have : Fact p.Prime := ⟨hp⟩
  have hmod := card_end_pow_modEq hQ hI hY hyΛ hyY hyp hc'
  rw [hE] at hmod
  rcases prime_of_two_pow_modEq hp hp2 le_rfl hlt hmod with h3 | h7 | ⟨h5, -, hc0⟩
  · exact Or.inl h3
  · exact Or.inr (Or.inl h7)
  · refine Or.inr (Or.inr ⟨h5, fun q hq hfix => ?_⟩)
    have hF0 : F = ⊥ := (rk_eq_zero_iff hQ).1 (by rw [hc'.2.2, hc0, zero_mul])
    have hqF : q ∈ F := ⟨hq, (mem_fixed_zpowers_iff (b := y₀)).2 hfix⟩
    rw [hF0] at hqF
    exact hqF

end CFSG.Quasithin.H13.T326

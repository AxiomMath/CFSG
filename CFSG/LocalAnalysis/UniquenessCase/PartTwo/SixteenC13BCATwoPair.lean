module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCAPairConj
public import CFSG.Quasithin.Background.RealizesFaithful

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

theorem s16c13bcA_transfer_pair {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {J : Subgroup W} (D : FFModel) (hR : D.Realizes H J ⊥) (hD : D.Faithful)
    (hγ : ∀ m ∈ D.sec, m ∉ D.ker → ∃ γ₁ γ₂ : D.Gam, orderOf γ₁ = 3 ∧ orderOf γ₂ = 3 ∧
      γ₁ * γ₂ = γ₂ * γ₁ ∧ γ₂ ∉ Subgroup.zpowers γ₁ ∧ D.act γ₁ m = m ∧ D.act γ₂ m = m) :
    s16c13bcA_PairFix H J := by
  intro w hw hw1
  obtain ⟨π, hπ⟩ := hR
  have hinj : Function.Injective π := FFModel.RealizesVia.injective_of_faithful_on hD hπ
  obtain ⟨-, -, -, hUinv, -, hsecinv, -, β, hβs, hβk, hβeq⟩ := hπ
  let u : ↥J := ⟨w, hw⟩
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
  have hmk : (m : D.Amb) ∉ D.ker := by
    intro hmk
    have h1 : β u = 1 := by
      rw [← hm, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hmk
    have h2 : (u : W) ∈ (⊥ : Subgroup W) := (hβk u).mp h1
    exact hw1 (Subgroup.mem_bot.mp h2)
  obtain ⟨γ₁, γ₂, h₁, h₂, hc, hn, hγ₁m, hγ₂m⟩ := hγ m m.2 hmk
  have hfix : ∀ γ : D.Gam, D.act γ (m : D.Amb) = m →
      ((π γ : ↥H) : MulAut W) w = w := by
    intro γ hγm
    have hwv : ((π γ : ↥H) : MulAut W) (u : W) ∈ J := hUinv (π γ) u u.2
    have hact : D.act γ (m : D.Amb) ∈ D.sec := hsecinv γ m m.2
    have h := hβeq γ u m hwv hact hm.symm
    have e : (⟨D.act γ (m : D.Amb), hact⟩ : ↥D.sec) = m := Subtype.ext hγm
    rw [e, hm] at h
    have h3 : β (⟨_, hwv⟩ * u⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
    have h4 := (hβk _).mp h3
    rw [Subgroup.mem_bot] at h4
    exact mul_inv_eq_one.mp h4
  refine ⟨((π γ₁ : ↥H) : MulAut W), (π γ₁).2, ((π γ₂ : ↥H) : MulAut W), (π γ₂).2, ?_, ?_, ?_, ?_,
    hfix γ₁ hγ₁m, hfix γ₂ hγ₂m⟩
  · rw [Subgroup.orderOf_coe, orderOf_injective π hinj γ₁]
    exact h₁
  · rw [Subgroup.orderOf_coe, orderOf_injective π hinj γ₂]
    exact h₂
  · have h := congrArg π hc
    rw [map_mul, map_mul] at h
    exact congrArg Subtype.val h
  · intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    apply hn
    refine Subgroup.mem_zpowers_iff.2 ⟨k, hinj (Subtype.ext ?_)⟩
    rw [map_zpow, Subgroup.coe_zpow]
    exact hk

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

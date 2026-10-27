module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.ModGRed2

public section

namespace CFSG.Quasithin.ModH

open CFSG.ComponentClassification.OuterAutomorphisms

theorem odd_mem_of_sup {G : Type} [Group G] {Y P : Subgroup G} (hP : IsPGroup 2 ↥P)
    (hN : P ≤ Subgroup.normalizer (Y : Set G)) {z : G} (hz : z ∈ Y ⊔ P)
    (hodd : Odd (orderOf z)) : z ∈ Y := by
  obtain ⟨a, ha, b, hb, hzab⟩ := ModG.Red.exists_mul_of_mem_sup' hN hz
  have hYZ : Y ≤ Y ⊔ P := le_sup_left
  have hZN : Y ⊔ P ≤ Subgroup.normalizer (Y : Set G) := sup_le Subgroup.le_normalizer hN
  have hnorm : (Y.subgroupOf (Y ⊔ P)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYZ).2 hZN
  let ψ : ↥(Y ⊔ P) →* ↥(Y ⊔ P) ⧸ Y.subgroupOf (Y ⊔ P) := QuotientGroup.mk' (Y.subgroupOf (Y ⊔ P))
  let zz : ↥(Y ⊔ P) := ⟨z, hz⟩
  have haZ : a ∈ Y ⊔ P := hYZ ha
  have hbZ : b ∈ Y ⊔ P := (le_sup_right : P ≤ Y ⊔ P) hb
  have hψa : ψ ⟨a, haZ⟩ = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.2 ha
  have hzz : zz = ⟨a, haZ⟩ * ⟨b, hbZ⟩ := Subtype.ext hzab
  have hψz : ψ zz = ψ ⟨b, hbZ⟩ := by rw [hzz, map_mul, hψa, one_mul]
  obtain ⟨k, hk⟩ := hP ⟨b, hb⟩
  have hbk : (⟨b, hbZ⟩ : ↥(Y ⊔ P)) ^ (2 ^ k) = 1 := by
    have := congrArg (fun w : ↥P => ((w : ↥P) : G)) hk
    exact Subtype.ext (by simpa using this)
  have h1 : ψ zz ^ (2 ^ k) = 1 := by rw [hψz, ← map_pow, hbk, map_one]
  have h2 : ψ zz ^ (orderOf z) = 1 := by
    have : zz ^ (orderOf z) = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact pow_orderOf_eq_one z
    rw [← map_pow, this, map_one]
  have h3 : ψ zz ^ (Nat.gcd (2 ^ k) (orderOf z)) = 1 := pow_gcd_eq_one.2 ⟨h1, h2⟩
  have hcop : Nat.Coprime (2 ^ k) (orderOf z) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)
  rw [hcop] at h3
  rw [pow_one] at h3
  have h4 : zz ∈ Y.subgroupOf (Y ⊔ P) := (QuotientGroup.eq_one_iff zz).1 h3
  exact Subgroup.mem_subgroupOf.1 h4

theorem inner_of_equiv_of_inner {Q Γ : Type} [Group Q] [Group Γ] (e : Q ≃* Γ)
    (hinn : ∀ α : MulAut Γ, ∃ g : Γ, MulAut.conj g = α) (hcen : Subgroup.center Γ = ⊥) :
    (∀ α : MulAut Q, ∃ q : Q, MulAut.conj q = α) ∧ Subgroup.center Q = ⊥ := by
  refine ⟨fun α => ?_, ?_⟩
  · obtain ⟨g, hg⟩ := hinn ((e.symm.trans α).trans e)
    refine ⟨e.symm g, ?_⟩
    ext x
    have h1 := congrArg (fun φ : MulAut Γ => φ (e x)) hg
    simp only [MulAut.conj_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1 ⊢
    apply e.injective
    simpa using h1
  · rw [eq_bot_iff]
    intro q hq
    have : e q ∈ Subgroup.center Γ := by
      rw [← Subgroup.map_center_eq e]
      exact ⟨q, hq, rfl⟩
    rw [hcen, Subgroup.mem_bot] at this
    have : q = 1 := e.injective (by simpa using this)
    simp [this]

end CFSG.Quasithin.ModH

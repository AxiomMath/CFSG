module

public import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Hering129KEa

theorem nonempty_range_mulEquiv {M₁ M₂ B₁ B₂ : Type*} [Group M₁] [Group M₂] [Group B₁]
    [Group B₂] (f₁ : M₁ →* B₁) (f₂ : M₂ →* B₂) (α : M₁ →* M₂) (hα : Function.Surjective α)
    (hker : (f₂.comp α).ker = f₁.ker) : Nonempty (f₁.range ≃* f₂.range) := by
  have hrange : (f₂.comp α).range = f₂.range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective α hα, MonoidHom.range_eq_map]
  exact ⟨(QuotientGroup.quotientKerEquivRange f₁).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      ((QuotientGroup.quotientKerEquivRange (f₂.comp α)).trans
        (MulEquiv.subgroupCongr hrange)))⟩

theorem isPGroup_sup_of_le_normalizer {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
    {F B : Subgroup P} (hF : IsPGroup p F) (hB : IsPGroup p B)
    (hBF : B ≤ Subgroup.normalizer (F : Set P)) : IsPGroup p ↥(F ⊔ B) :=
  hF.to_sup_of_normal_left' hB hBF

theorem theta_le_of_sup_eq_top {H : Type*} [Group H] [Finite H] {Y A : Subgroup H} [Y.Normal]
    (hA : IsPGroup 3 A) (hYA : Y ⊔ A = ⊤) : aschbacherSolvableCore 3 H ≤ Y := by
  intro t ht
  have hcls : ∀ h : H, ∃ a ∈ A, ((h : H ⧸ Y) = (a : H ⧸ Y)) := by
    intro h
    have hh : h ∈ Y ⊔ A := by
      rw [hYA]
      exact Subgroup.mem_top h
    obtain ⟨y, hy, a, ha, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hh
    refine ⟨a, ha, ?_⟩
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff y).mpr hy, one_mul]
  obtain ⟨a, ha, hta⟩ := hcls t
  obtain ⟨k, hk⟩ := hA.exists_orderOf_dvd_pow ⟨a, ha⟩
  rw [Subgroup.orderOf_mk] at hk
  have hd1 : orderOf (t : H ⧸ Y) ∣ 3 ^ k := by
    rw [hta]
    exact (orderOf_map_dvd (QuotientGroup.mk' Y) a).trans hk
  have hd2 : orderOf (t : H ⧸ Y) ∣ Nat.card (aschbacherSolvableCore 3 H) :=
    (orderOf_map_dvd (QuotientGroup.mk' Y) t).trans (Subgroup.orderOf_dvd_natCard _ ht)
  have hcop : Nat.Coprime (3 ^ k) (Nat.card (aschbacherSolvableCore 3 H)) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2
      (three_not_dvd_card_aschbacherSolvableCore (G := H)))
  have hone : orderOf (t : H ⧸ Y) = 1 := Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
  exact (QuotientGroup.eq_one_iff t).mp (orderOf_eq_one_iff.mp hone)

end Hering129KEa

end CFSG.RankThree.PartTwo.Sec12

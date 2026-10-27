module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_1_b

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter1section1

/-!
# Peterfalvi, Part II, Chapter I, Section 1, Proposition 1(d)
-/

private theorem rightConjugate_eq_self_of_mem_normalizer
    {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    rightConjugate H g = H := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨y, hy, rfl⟩
    have hg_inv : g⁻¹ ∈ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normalizer (H : Set G)).inv_mem hg
    exact (Subgroup.mem_normalizer_iff.mp hg_inv y).1 hy
  · intro hx
    refine ⟨g * x * g⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hg x).1 hx
    · calc
        (MulAut.conj g⁻¹) (g * x * g⁻¹) =
            g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ := rfl
        _ = x := by group

public theorem proposition_1_d
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) :
    Subgroup.normalizer (Q : Set G) = H ∧
      Subgroup.normalizer (H : Set G) = H := by
  classical
  have hQne : Q ≠ ⊥ := by
    intro hQ
    have hcard : Nat.card Q = 1 := by
      rw [hQ]
      simp
    have hEven_one : Even 1 := by
      simpa [hcard] using hA1.Q_even
    norm_num at hEven_one
  have hNQ_le_H : Subgroup.normalizer (Q : Set G) ≤ H :=
    proposition_1_b H D Q t hA1 Q hQne le_rfl
  have hH_le_NQ : H ≤ Subgroup.normalizer (Q : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      have hqH : q ∈ H := hA1.Q_le_H hq
      have hqSub : (⟨q, hqH⟩ : H) ∈ Q.subgroupOf H := hq
      exact hA1.Q_normal_in_H.conj_mem (⟨q, hqH⟩ : H) hqSub ⟨h, hh⟩
    · intro hq
      have hyH : h * q * h⁻¹ ∈ H := hA1.Q_le_H hq
      have hySub :
          (⟨h * q * h⁻¹, hyH⟩ : H) ∈ Q.subgroupOf H := hq
      have hmem :=
        hA1.Q_normal_in_H.conj_mem
          (⟨h * q * h⁻¹, hyH⟩ : H) hySub ⟨h⁻¹, H.inv_mem hh⟩
      change ((h⁻¹ * (h * q * h⁻¹) * (h⁻¹)⁻¹ : G) ∈ Q) at hmem
      simpa [mul_assoc] using hmem
  have hNH_le_H : Subgroup.normalizer (H : Set G) ≤ H := by
    intro g hgNorm
    by_contra hgH
    obtain ⟨_h, _hHD, hodd⟩ := proposition_1_a H D Q t hA1 g hgH
    have hright : rightConjugate H g = H :=
      rightConjugate_eq_self_of_mem_normalizer hgNorm
    have hcard :
        Nat.card (↥(rightConjugate H g ⊓ H)) = Nat.card H := by
      simp [hright]
    have hOddH : Odd (Nat.card H) := hcard ▸ hodd
    have hEvenH : Even (Nat.card H) :=
      hA1.Q_even.trans_dvd (Subgroup.card_dvd_of_le hA1.Q_le_H)
    exact (Nat.not_even_iff_odd.mpr hOddH) hEvenH
  exact ⟨le_antisymm hNQ_le_H hH_le_NQ,
    le_antisymm hNH_le_H Subgroup.le_normalizer⟩

end PFchapter1section1
end CFSG.BenderSuzuki

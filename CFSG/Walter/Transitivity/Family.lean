module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection7.Defs

public section

namespace CFSG.Walter.Transitivity

open CFSG

variable {G : Type*} [Group G]

theorem le_normalizer_inf {A H K : Subgroup G} (hH : A ≤ Subgroup.normalizer (H : Set G))
    (hK : A ≤ Subgroup.normalizer (K : Set G)) :
    A ≤ Subgroup.normalizer ((H ⊓ K : Subgroup G) : Set G) :=
  (le_inf hH hK).trans Subgroup.inf_normalizer_le_normalizer_inf

theorem le_normalizer_sup {A H K : Subgroup G} (hH : A ≤ Subgroup.normalizer (H : Set G))
    (hK : A ≤ Subgroup.normalizer (K : Set G)) :
    A ≤ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) :=
  (le_inf hH hK).trans (Subgroup.inf_normalizer_le_normalizer_sup H K)

theorem section7HFamily_mono {X Y A Q : Subgroup G} {π : Set Nat.Primes} (hXY : X ≤ Y)
    (hQ : Q ∈ section7HFamily X A π) : Q ∈ section7HFamily Y A π :=
  ⟨hQ.1.trans hXY, hQ.2.1, hQ.2.2⟩

theorem conjBy_mono {Q R : Subgroup G} (c : G) (h : Q ≤ R) : Q.conjBy c ≤ R.conjBy c :=
  Subgroup.map_mono h

theorem conjBy_le {Q X : Subgroup G} {c : G} (hQX : Q ≤ X) (hcX : c ∈ X) : Q.conjBy c ≤ X := by
  rintro _ ⟨y, hy, rfl⟩
  exact X.mul_mem (X.mul_mem hcX (hQX hy)) (X.inv_mem hcX)

theorem le_normalizer_conjBy {A Q : Subgroup G} {c : G}
    (hc : c ∈ Subgroup.centralizer (A : Set G)) (hAQ : A ≤ Subgroup.normalizer (Q : Set G)) :
    A ≤ Subgroup.normalizer ((Q.conjBy c : Subgroup G) : Set G) := by
  refine subgroup_le_normalizer_of_conj_mem (Q.conjBy c) A ?_
  rintro a _ ⟨y, hy, rfl⟩
  have hy' : (a : G) * y * (a : G)⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hAQ a.property) y).1 hy
  have hcomm : (a : G) * c = c * (a : G) := Subgroup.mem_centralizer_iff.mp hc _ a.property
  refine ⟨(a : G) * y * (a : G)⁻¹, hy', ?_⟩
  change c * ((a : G) * y * (a : G)⁻¹) * c⁻¹ = (a : G) * (c * y * c⁻¹) * (a : G)⁻¹
  have hcomm' : c⁻¹ * (a : G)⁻¹ = (a : G)⁻¹ * c⁻¹ := by
    rw [← mul_inv_rev, ← mul_inv_rev, hcomm]
  calc c * ((a : G) * y * (a : G)⁻¹) * c⁻¹
      = (c * (a : G)) * y * ((a : G)⁻¹ * c⁻¹) := by group
    _ = ((a : G) * c) * y * (c⁻¹ * (a : G)⁻¹) := by rw [hcomm, hcomm']
    _ = (a : G) * (c * y * c⁻¹) * (a : G)⁻¹ := by group

theorem conjBy_mem_section7HFamily {X A Q : Subgroup G} {π : Set Nat.Primes} {c : G}
    (hcX : c ∈ X) (hcA : c ∈ Subgroup.centralizer (A : Set G))
    (hQ : Q ∈ section7HFamily X A π) : Q.conjBy c ∈ section7HFamily X A π :=
  ⟨conjBy_le hQ.1 hcX, hQ.2.1.map (MulAut.conj c).toMonoidHom, le_normalizer_conjBy hcA hQ.2.2⟩

theorem conjBy_mem_section7HStarFamily {X A Q : Subgroup G} {π : Set Nat.Primes} {c : G}
    (hcX : c ∈ X) (hcA : c ∈ Subgroup.centralizer (A : Set G))
    (hQ : Q ∈ section7HStarFamily X A π) : Q.conjBy c ∈ section7HStarFamily X A π := by
  refine ⟨conjBy_mem_section7HFamily hcX hcA hQ.1, fun R hQR hR => ?_⟩
  have hR' : R.conjBy c⁻¹ ∈ section7HFamily X A π :=
    conjBy_mem_section7HFamily (X.inv_mem hcX) ((Subgroup.centralizer _).inv_mem hcA) hR
  have hle : Q ≤ R.conjBy c⁻¹ :=
    (Subgroup.conjBy_inv Q c).symm.le.trans (conjBy_mono c⁻¹ hQR)
  calc R = (R.conjBy c⁻¹).conjBy c := (Subgroup.conjBy_inv' R c).symm
    _ = Q.conjBy c := by rw [hQ.2 _ hle hR']

theorem exists_conjBy_trans {K Q₁ Q₂ Q₃ : Subgroup G}
    (h₁ : ∃ k : K, Q₂ = Q₁.conjBy (k : G)) (h₂ : ∃ k : K, Q₃ = Q₂.conjBy (k : G)) :
    ∃ k : K, Q₃ = Q₁.conjBy (k : G) := by
  obtain ⟨a, rfl⟩ := h₁
  obtain ⟨b, rfl⟩ := h₂
  exact ⟨b * a, by rw [Subgroup.conjBy_conjBy]; rfl⟩

end CFSG.Walter.Transitivity

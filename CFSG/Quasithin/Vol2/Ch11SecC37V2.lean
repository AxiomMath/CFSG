module

public import CFSG.Quasithin.Vol2.Ch11SecC37B2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecC

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.InternalSec
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem fix_autOn_iff {V P : Subgroup G} (hPV : P ≤ Subgroup.normalizer (V : Set G))
    (x : ↥V) : (∀ σ ∈ autOn P V, σ x = x) ↔ (x : G) ∈ Subgroup.centralizer (P : Set G) := by
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have h1 := h (conjAct V ⟨p, hPV hp⟩) ⟨⟨p, hPV hp⟩, hp, rfl⟩
    have h2 := congrArg Subtype.val h1
    rw [conjAct_apply_coe] at h2
    calc p * x = (p * x * p⁻¹) * p := by group
      _ = x * p := by rw [show p * (x : G) * p⁻¹ = x from h2]
  · rintro hx σ ⟨z, hz, rfl⟩
    apply Subtype.ext
    rw [conjAct_apply_coe, Subgroup.mem_centralizer_iff.mp hx z hz, mul_inv_cancel_right]

omit [Finite G] in
theorem conj_conj (g u x : G) :
    g * u * g⁻¹ * x * (g * u * g⁻¹)⁻¹ = g * (u * (g⁻¹ * x * g) * u⁻¹) * g⁻¹ := by group

omit [Finite G] in
theorem conj_mem_normalizer {V : Subgroup G} {g u : G}
    (hu : u ∈ Subgroup.normalizer (conjSubgroup V g : Set G)) :
    g * u * g⁻¹ ∈ Subgroup.normalizer (V : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro v
  have h1 := Subgroup.mem_normalizer_iff.mp hu (g⁻¹ * v * g)
  rw [mem_conjSubgroup_iff, mem_conjSubgroup_iff] at h1
  rw [conj_conj, ← h1]
  have e1 : g * (g⁻¹ * v * g) * g⁻¹ = v := by group
  rw [e1]

namespace Set37

variable {T L I : Subgroup G} {n : ℕ} {V₁ H : Subgroup G} {g : G} (s : Set37 T L I n V₁ H g)
include s

theorem relIndex_CA (hAS : FactAStarSylow) (hF : SecA.NatFacts) (h1102 : Stmt11_0_2)
    (hG2 : SecA.FactG2DerivedOrder) (h1122 : Stmt11_2_2) (h1134 : Stmt11_3_4)
    (h1135 : Stmt11_3_5) (h1136 : Stmt11_3_6) :
    (conjSubgroup (fsuV T I) g ⊓ Subgroup.centralizer (VZ T H : Set G)).relIndex
      (conjSubgroup (fsuV T I) g) = 2 ^ n := by
  have : IsMulCommutative ↥(VZ T H) := s.isElemAbelian_VZ.1
  rw [← card_autOn_eq_relIndex (s.hAT.trans (s.T_le.trans (le_normalizer_VZ T H)))]
  exact s.card_aStar hAS hF h1102 hG2 h1122 h1134 h1135 h1136

theorem card_le_fix (hAS : FactAStarSylow) (hF : SecA.NatFacts) (h1102 : Stmt11_0_2)
    (hG2 : SecA.FactG2DerivedOrder) (h1122 : Stmt11_2_2) (h1134 : Stmt11_3_4)
    (h1135 : Stmt11_3_5) (h1136 : Stmt11_3_6) {u : G} (hu : u ∈ VZ T H)
    (hN : g * u * g⁻¹ ∈ Subgroup.normalizer (fsuV T I : Set G)) :
    Nat.card ↥(fsuV T I) ≤
      2 ^ n * Nat.card {w : ↥(fsuV T I) // conjAct (fsuV T I) ⟨_, hN⟩ w = w} := by
  have h1 : Nat.card ↥(fsuV T I) = Nat.card ↥(conjSubgroup (fsuV T I) g) :=
    (Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective).symm
  have h2 := Subgroup.relIndex_mul_card
    (conjSubgroup (fsuV T I) g ⊓ Subgroup.centralizer (VZ T H : Set G))
    (conjSubgroup (fsuV T I) g)
  rw [inf_eq_left.mpr inf_le_left, s.relIndex_CA hAS hF h1102 hG2 h1122 h1134 h1135 h1136] at h2
  rw [h1, ← h2]
  refine Nat.mul_le_mul_left _ (Nat.card_le_card_of_injective
    (fun c => ⟨⟨g * c * g⁻¹, mem_conjSubgroup_iff.mp c.2.1⟩, ?_⟩) ?_)
  · apply Subtype.ext
    rw [conjAct_apply_coe]
    show g * u * g⁻¹ * (g * c * g⁻¹) * (g * u * g⁻¹)⁻¹ = g * c * g⁻¹
    have hcu : u * c = c * u := Subgroup.mem_centralizer_iff.mp c.2.2 u hu
    calc g * u * g⁻¹ * (g * c * g⁻¹) * (g * u * g⁻¹)⁻¹ = g * (u * c * u⁻¹) * g⁻¹ := by group
      _ = g * c * g⁻¹ := by rw [hcu, mul_inv_cancel_right]
  · intro a b hab
    have h3 : g * (a : G) * g⁻¹ = g * b * g⁻¹ := congrArg (fun w => ((w.1 : ↥(fsuV T I)) : G)) hab
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h3))

end Set37

end CFSG.Quasithin.Vol2.Ch11.SecC

module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.GoldschmidtF431Loc442Free
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsLie

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin.Loc442

universe u v

section Defs

variable {Mb : Type u} [Group Mb]

@[expose] def PairLink (T M1 M2 : Subgroup Mb) (p p' : Mb × Mb) : Prop :=
  p.1 ∈ T ∧ p.2 ∈ T ∧ p'.1 ∈ T ∧ p'.2 ∈ T ∧
    ∃ c : Mb, (c ∈ M1 ∨ c ∈ M2) ∧ p'.1 = c * p.1 * c⁻¹ ∧ p'.2 = c * p.2 * c⁻¹

structure Loc442Datum (M1 M2 T : Subgroup Mb) (z t : Mb) (Vb : Subgroup Mb) (q : Mb) : Prop where
  lie : F431LieI T M1 M2 z t
  V_le : Vb ≤ Subgroup.centralizer ({t} : Set Mb)
  V_card : Nat.card Vb = 4
  V_comm : ∀ a ∈ Vb, ∀ b ∈ Vb, a * b = b * a
  V_sq : ∀ a ∈ Vb, a ^ 2 = 1
  V_norm : ∀ x ∈ Subgroup.centralizer ({t} : Set Mb), ∀ v ∈ Vb, x * v * x⁻¹ ∈ Vb
  V_conj : ∀ v ∈ Vb, v ≠ 1 → ∃ x ∈ Subgroup.centralizer ({t} : Set Mb), v = x * z * x⁻¹
  q_mem : q ∈ Subgroup.centralizer ({t} : Set Mb)
  q_comm : ∀ v ∈ Vb, q * v = v * q
  q_sq : q ^ 2 ∈ Vb
  q_sq_ne : q ^ 2 ≠ 1
  M2_card : Nat.card M2 ∣ 12288
  fusion : ∀ u ∈ Subgroup.centralizer ({t} : Set Mb), IsConj z u → u ∈ Vb ∨
    ∃ n ∈ M2, ∃ a ∈ T, ∃ b ∈ T, u = n * a * n⁻¹ ∧ t = n * b * n⁻¹ ∧
      ∃ b' ∈ T, Relation.ReflTransGen (PairLink T M1 M2) (a, b) (z, b') ∧
        ∀ h ∈ M1, h * t * h⁻¹ ≠ b'

end Defs

section Psi

variable {Mb : Type u} [Group Mb] {M : Type v} [Group M] {M1 M2 : Subgroup Mb}
  {b1 : M1 →* M} {b2 : M2 →* M}

theorem psi_conj₁ {c x : Mb} (hc : c ∈ M1) (hx : x ∈ M1) :
    amalgamMap b1 b2 (c * x * c⁻¹) =
      amalgamMap b1 b2 c * amalgamMap b1 b2 x * (amalgamMap b1 b2 c)⁻¹ := by
  rw [amalgamMap_of_mem₁ b1 b2 (M1.mul_mem (M1.mul_mem hc hx) (M1.inv_mem hc)),
    amalgamMap_of_mem₁ b1 b2 hc, amalgamMap_of_mem₁ b1 b2 hx]
  have : (⟨c * x * c⁻¹, M1.mul_mem (M1.mul_mem hc hx) (M1.inv_mem hc)⟩ : M1) =
      ⟨c, hc⟩ * ⟨x, hx⟩ * ⟨c, hc⟩⁻¹ := rfl
  rw [this, map_mul, map_mul, map_inv]

theorem psi_conj₂ (C : F431Comp M1 M2 b1 b2) {c x : Mb} (hc : c ∈ M2) (hx : x ∈ M2) :
    amalgamMap b1 b2 (c * x * c⁻¹) =
      amalgamMap b1 b2 c * amalgamMap b1 b2 x * (amalgamMap b1 b2 c)⁻¹ := by
  rw [amalgamMap_of_mem₂ b1 b2 C.agree (M2.mul_mem (M2.mul_mem hc hx) (M2.inv_mem hc)),
    amalgamMap_of_mem₂ b1 b2 C.agree hc, amalgamMap_of_mem₂ b1 b2 C.agree hx]
  have : (⟨c * x * c⁻¹, M2.mul_mem (M2.mul_mem hc hx) (M2.inv_mem hc)⟩ : M2) =
      ⟨c, hc⟩ * ⟨x, hx⟩ * ⟨c, hc⟩⁻¹ := rfl
  rw [this, map_mul, map_mul, map_inv]

theorem chain_conj {T : Subgroup Mb} (hT1 : T ≤ M1) (hT2 : T ≤ M2) (C : F431Comp M1 M2 b1 b2)
    {p p' : Mb × Mb} (h : Relation.ReflTransGen (PairLink T M1 M2) p p') :
    ∃ Y : M, amalgamMap b1 b2 p'.1 = Y * amalgamMap b1 b2 p.1 * Y⁻¹ ∧
      amalgamMap b1 b2 p'.2 = Y * amalgamMap b1 b2 p.2 * Y⁻¹ := by
  induction h with
  | refl => exact ⟨1, by simp, by simp⟩
  | tail _ hs ih =>
    obtain ⟨Y, h1, h2⟩ := ih
    obtain ⟨hx, hy, hx', hy', c, hc, e1, e2⟩ := hs
    refine ⟨amalgamMap b1 b2 c * Y, ?_, ?_⟩
    · rw [e1]
      rcases hc with hc | hc
      · rw [psi_conj₁ hc (hT1 hx), h1, mul_inv_rev]
        group
      · rw [psi_conj₂ C hc (hT2 hx), h1, mul_inv_rev]
        group
    · rw [e2]
      rcases hc with hc | hc
      · rw [psi_conj₁ hc (hT1 hy), h2, mul_inv_rev]
        group
      · rw [psi_conj₂ C hc (hT2 hy), h2, mul_inv_rev]
        group

end Psi

end CFSG.Quasithin

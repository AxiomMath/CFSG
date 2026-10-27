module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3Hyp

public section

namespace CFSG.Quasithin

open CFSG.Quasithin CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

theorem le_of_card_four {X Y Z : Subgroup D} (hX : Nat.card X = 4) (hZ : Nat.card Z = 2)
    (hZX : Z ≤ X) (hZY : Z ≤ Y) {c : D} (hcX : c ∈ X) (hcY : c ∈ Y) (hcZ : c ∉ Z) : X ≤ Y := by
  have hK : Z ≤ X ⊓ Y := le_inf hZX hZY
  have h1 : Nat.card Z ∣ Nat.card (X ⊓ Y : Subgroup D) := Subgroup.card_dvd_of_le hK
  have h2 : Nat.card (X ⊓ Y : Subgroup D) ∣ Nat.card X :=
    Subgroup.card_dvd_of_le inf_le_left
  rw [hZ] at h1
  rw [hX] at h2
  have hne : (X ⊓ Y : Subgroup D) ≠ Z := fun e => hcZ (by
    have : c ∈ (X ⊓ Y : Subgroup D) := ⟨hcX, hcY⟩
    rwa [e] at this)
  have hlt : Nat.card Z < Nat.card (X ⊓ Y : Subgroup D) := by
    have hle := Subgroup.card_le_of_le hK
    rcases hle.lt_or_eq with hlt | heq
    · exact hlt
    · exact absurd (Subgroup.eq_of_le_of_card_ge hK heq.symm.le).symm hne
  rw [hZ] at hlt
  have hc4 : Nat.card (X ⊓ Y : Subgroup D) = 4 := by
    have hpos : 0 < Nat.card (X ⊓ Y : Subgroup D) := Nat.card_pos
    have hle : Nat.card (X ⊓ Y : Subgroup D) ≤ 4 := Nat.le_of_dvd (by norm_num) h2
    interval_cases k : Nat.card (X ⊓ Y : Subgroup D) <;> omega
  have heq : X ⊓ Y = X := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hc4, hX])
  rw [← heq]
  exact inf_le_right

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

omit [Finite D] in
theorem ballStab_one_le_centralizer_Vv {u : CosetGeom (A ⊔ B) A B} (hu : vtype u = false)
    {x : D} (hx : x ∈ ballStab 1 u) {w : D} (hw : w ∈ Vv V u) : x * w * x⁻¹ = w := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₀ hu
  rw [ballStab_smul, mem_conjSub] at hx
  rw [Vv_smul_γ₀ h.natural.reduced.2.1, mem_conjSub] at hw
  have h0 := (ballStab_one_γ₀ (G₀ := A ⊔ B) (G₁ := A) (G₂ := B) rfl).1
  rw [h0] at hx
  have hQ : (g : D)⁻¹ * x * g ∈ pCoreOf 2 A :=
    le_pCoreOf_of_le_normalizer 2 ((coreIn_le_right _ _).trans inf_le_left)
      (le_normalizer_coreIn _ _)
      ((h.gold.isSylowTwoOf_left.2.1).to_le (coreIn_le_right _ _)) hx
  rw [← h.natural.centralizer_eq] at hQ
  have hc := Subgroup.mem_centralizer_iff.mp hQ.2 _ hw
  have e : x * w * x⁻¹ = (g : D) * (((g : D)⁻¹ * x * g) * ((g : D)⁻¹ * w * g) *
      ((g : D)⁻¹ * x * g)⁻¹) * (g : D)⁻¹ := by group
  rw [e, ← hc]
  group

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin

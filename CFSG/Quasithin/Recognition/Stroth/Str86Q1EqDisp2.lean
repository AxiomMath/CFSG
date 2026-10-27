module

public import CFSG.Quasithin.Recognition.Stroth.Str86Q1EqDisp
public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoChain

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem str86_q2_displacement_le {L1 L2 S : Subgroup G} {k : ℕ} (hF : F112Hyp L1 L2 S)
    (hY : Nat.card ↥(Z2 L1 L2 S ⊓ Q1 L1 L2 S) = (2 ^ k) ^ 3)
    (hI4 : Nat.card (u3X1 L1 L2 S) = (2 ^ k) ^ 7)
    (hX1Q2 : u3X1 L1 L2 S ⊔ Q2 L1 L2 S = S)
    (hSQ2 : (Q2 L1 L2 S).relIndex S = (2 ^ k) ^ 2) :
    ∀ x ∈ u3X1 L1 L2 S,
      (centralizerMod (Z2 L1 L2 S) (Q2 L1 L2 S) (Subgroup.zpowers x)).relIndex (Q2 L1 L2 S) ≤
        (2 ^ k) ^ 2 := by
  classical
  intro x hxX
  have hI4' : Nat.card ↥(u3X1 L1 L2 S) = (2 ^ k) ^ 7 := hI4
  have hsupX : u3X1 L1 L2 S ≤ u3X1 L1 L2 S ⊔ Q2 L1 L2 S := le_sup_left
  have hsupQ : Q2 L1 L2 S ≤ u3X1 L1 L2 S ⊔ Q2 L1 L2 S := le_sup_right
  have hX1leS : u3X1 L1 L2 S ≤ S := hsupX.trans (le_of_eq hX1Q2)
  have hQ2leS : Q2 L1 L2 S ≤ S := hsupQ.trans (le_of_eq hX1Q2)
  have hxS : x ∈ S := hX1leS hxX
  have hSleP2 : S ≤ P2 L1 L2 S :=
    (le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right
  have hSNQ2 : S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    hSleP2.trans (le_normalizer_pCoreOf 2 (P2 L1 L2 S))
  have hSNX1 : S ≤ Subgroup.normalizer (u3X1 L1 L2 S : Set G) := le_normalizer_u3X1_sylow hF
  have hQ2X1rel : (Q2 L1 L2 S).relIndex (u3X1 L1 L2 S) = (2 ^ k) ^ 2 := by
    calc (Q2 L1 L2 S).relIndex (u3X1 L1 L2 S)
        = (Q2 L1 L2 S).relIndex (u3X1 L1 L2 S ⊔ Q2 L1 L2 S) :=
          (F1.relIndex_sup_eq_of_le_normalizer (D := Q2 L1 L2 S) (T := u3X1 L1 L2 S)
            (hX1leS.trans hSNQ2)).symm
      _ = (Q2 L1 L2 S).relIndex S := by rw [hX1Q2]
      _ = (2 ^ k) ^ 2 := hSQ2
  have hcardQ2X1 : Nat.card ↥(Q2 L1 L2 S ⊓ u3X1 L1 L2 S) = (2 ^ k) ^ 5 := by
    have hmul := Subgroup.relIndex_mul_card (Q2 L1 L2 S ⊓ u3X1 L1 L2 S) (u3X1 L1 L2 S)
    have h7 : (2 ^ k) ^ 7 = (2 ^ k) ^ 2 * (2 ^ k) ^ 5 := by ring
    rw [inf_eq_left.mpr (inf_le_right : Q2 L1 L2 S ⊓ u3X1 L1 L2 S ≤ u3X1 L1 L2 S),
      Subgroup.inf_relIndex_right, hQ2X1rel, hI4', h7] at hmul
    exact Nat.eq_of_mul_eq_mul_left (by positivity) hmul
  have hZX : Z2 L1 L2 S ⊓ u3X1 L1 L2 S = Z2 L1 L2 S ⊓ Q1 L1 L2 S :=
    le_antisymm (inf_le_inf_left _ u3X1_le_q1) (le_inf inf_le_left u3Y_le_u3X1)
  have hZQX : Z2 L1 L2 S ⊓ (Q2 L1 L2 S ⊓ u3X1 L1 L2 S) = Z2 L1 L2 S ⊓ Q1 L1 L2 S := by
    rw [← inf_assoc, inf_eq_left.mpr (omegaOneCenterOf_le (Q2 L1 L2 S)), hZX]
  have hcardZ2 : Nat.card ↥(Z2 L1 L2 S ⊓ (Q2 L1 L2 S ⊓ u3X1 L1 L2 S)) = (2 ^ k) ^ 3 := by
    rw [hZQX]
    exact hY
  have hZ2rel : (Z2 L1 L2 S).relIndex (Q2 L1 L2 S ⊓ u3X1 L1 L2 S) = (2 ^ k) ^ 2 := by
    have hmul := Subgroup.relIndex_mul_card (Z2 L1 L2 S) (Q2 L1 L2 S ⊓ u3X1 L1 L2 S)
    have h5 : (2 ^ k) ^ 5 = (2 ^ k) ^ 2 * (2 ^ k) ^ 3 := by ring
    rw [hcardZ2, hcardQ2X1, h5] at hmul
    exact Nat.eq_of_mul_eq_mul_right (by positivity) hmul
  have hD : ∀ v ∈ Q2 L1 L2 S, v * x * v⁻¹ * x⁻¹ ∈ Q2 L1 L2 S ⊓ u3X1 L1 L2 S := by
    intro v hv
    have hvS : v ∈ S := hQ2leS hv
    refine ⟨?_, ?_⟩
    · have h1 : x * v⁻¹ * x⁻¹ ∈ Q2 L1 L2 S :=
        (Subgroup.mem_normalizer_iff.mp (hSNQ2 hxS) v⁻¹).mp ((Q2 L1 L2 S).inv_mem hv)
      have e : v * x * v⁻¹ * x⁻¹ = v * (x * v⁻¹ * x⁻¹) := by group
      rw [e]
      exact (Q2 L1 L2 S).mul_mem hv h1
    · have h1 : v * x * v⁻¹ ∈ u3X1 L1 L2 S :=
        (Subgroup.mem_normalizer_iff.mp (hSNX1 hvS) x).mp hxX
      have e : v * x * v⁻¹ * x⁻¹ = (v * x * v⁻¹) * x⁻¹ := by group
      rw [e]
      exact (u3X1 L1 L2 S).mul_mem h1 ((u3X1 L1 L2 S).inv_mem hxX)
  have hQ2Z : Q2 L1 L2 S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    (Subgroup.le_normalizer (H := Q2 L1 L2 S)).trans
      (normalizer_le_normalizer_omegaOneCenterOf (Q2 L1 L2 S))
  have hxZ : x ∈ Subgroup.normalizer (Z2 L1 L2 S : Set G) := le_normalizer_z2_of_sylow hxS
  have hG1 : (centralizerMod (Z2 L1 L2 S) (Q2 L1 L2 S) (Subgroup.zpowers x)).relIndex
      (Q2 L1 L2 S) ≤ (Z2 L1 L2 S).relIndex (Q2 L1 L2 S ⊓ u3X1 L1 L2 S) :=
    relIndex_centralizerMod_zpowers_le_of_commutator_mem hQ2Z hxZ hD
  rw [hZ2rel] at hG1
  exact hG1

end CFSG.Quasithin.Stroth

module

public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoBound

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem str86_q1_inf_q2_le_centralizerMod {L1 L2 S : Subgroup G}
    (hX1Q2 : u3X1 L1 L2 S ⊔ Q2 L1 L2 S = S)
    (hX1Q1 : ⁅u3X1 L1 L2 S, Q1 L1 L2 S⁆ ≤ Z1 L1 L2 S) (hZ1Z2 : Z1 L1 L2 S ≤ Z2 L1 L2 S)
    (hab : ∀ x ∈ Q2 L1 L2 S, ∀ y ∈ Q2 L1 L2 S, x * y * x⁻¹ * y⁻¹ ∈ Z2 L1 L2 S) :
    Q1 L1 L2 S ⊓ Q2 L1 L2 S ≤ centralizerMod (Z2 L1 L2 S) (Q2 L1 L2 S) S := by
  have hQZ : Q2 L1 L2 S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    Subgroup.le_normalizer.trans (A4.normalizer_le_normalizer_omegaOneCenterOf (Q2 L1 L2 S))
  have hSZ : S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    le_normalizer_z2_of_sylow (L1 := L1) (L2 := L2) (S := S)
  set X₁ : Subgroup G := u3X1 L1 L2 S with hX₁
  set Q₁ : Subgroup G := Q1 L1 L2 S with hQ₁
  set Q₂ : Subgroup G := Q2 L1 L2 S with hQ₂
  set Z₁ : Subgroup G := Z1 L1 L2 S with hZ₁
  set Z₂ : Subgroup G := Z2 L1 L2 S with hZ₂
  clear_value X₁ Q₁ Q₂ Z₁ Z₂
  intro y hy
  obtain ⟨hyQ₁, hyQ₂⟩ := Subgroup.mem_inf.mp hy
  have hXZ : X₁ ≤ Subgroup.normalizer (Z₂ : Set G) :=
    (hX1Q2 ▸ le_sup_left).trans hSZ
  have hyZ : y ∈ Subgroup.normalizer (Z₂ : Set G) := hQZ hyQ₂
  refine mem_centralizerMod.mpr ⟨hyQ₂, hyZ, ?_⟩
  have hX₁E : X₁ ≤ centralizerMod Z₂ (Subgroup.normalizer (Z₂ : Set G))
      (Subgroup.zpowers y) := by
    intro x hx
    have hxZ : x ∈ Subgroup.normalizer (Z₂ : Set G) := hXZ hx
    have hxZ₁ : x * y * x⁻¹ * y⁻¹ ∈ Z₁ :=
      hX1Q1 (Subgroup.commutator_mem_commutator hx hyQ₁)
    exact (mem_centralizerMod_zpowers_iff_of_normalizer le_rfl hyZ hxZ).mpr (hZ1Z2 hxZ₁)
  have hQ₂E : Q₂ ≤ centralizerMod Z₂ (Subgroup.normalizer (Z₂ : Set G))
      (Subgroup.zpowers y) := by
    intro q hq
    have hqy : q * y * q⁻¹ * y⁻¹ ∈ Z₂ := by
      have h := Z₂.inv_mem (hab y hyQ₂ q hq)
      convert h using 1
      group
    exact (mem_centralizerMod_zpowers_iff_of_normalizer le_rfl hyZ (hQZ hq)).mpr hqy
  have hSE : S ≤ centralizerMod Z₂ (Subgroup.normalizer (Z₂ : Set G))
      (Subgroup.zpowers y) := by
    rw [← hX1Q2]
    exact sup_le hX₁E hQ₂E
  intro s hs
  have hsy : y * s * y⁻¹ * s⁻¹ ∈ Z₂ := by
    have h := Z₂.inv_mem ((mem_centralizerMod.mp (hSE hs)).2.2 y (Subgroup.mem_zpowers y))
    convert h using 1
    group
  exact hsy

theorem str86_q1_eq_of_card {L1 L2 S : Subgroup G} {k : ℕ}
    (hF : F112Hyp L1 L2 S) (hX1Q2 : u3X1 L1 L2 S ⊔ Q2 L1 L2 S = S)
    (hSQ2 : (Q2 L1 L2 S).relIndex S = (2 ^ k) ^ 2)
    (hY : Nat.card ↥(Z2 L1 L2 S ⊓ Q1 L1 L2 S) = (2 ^ k) ^ 3)
    (hI4 : Nat.card (u3X1 L1 L2 S) = (2 ^ k) ^ 7)
    (hQQ : Q1 L1 L2 S ⊓ Q2 L1 L2 S ≤ centralizerMod (Z2 L1 L2 S) (Q2 L1 L2 S) S)
    (hC : (Z2 L1 L2 S).relIndex (centralizerMod (Z2 L1 L2 S) (Q2 L1 L2 S) S) ≤ (2 ^ k) ^ 2) :
    Q1 L1 L2 S = u3X1 L1 L2 S := by
  have hQ₁S : Q1 L1 L2 S ≤ S :=
    F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hQ₂S : Q2 L1 L2 S ≤ S :=
    F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW)
  have hX₁Q₁ : u3X1 L1 L2 S ≤ Q1 L1 L2 S := u3X1_le_q1
  have hQ₁N : Q1 L1 L2 S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    hQ₁S.trans (le_normalizer_q2_of_sylow (L1 := L1) (L2 := L2) (S := S))
  have hZQ : Z2 L1 L2 S ≤ Q2 L1 L2 S := omegaOneCenterOf_le (Q2 L1 L2 S)
  set X₁ : Subgroup G := u3X1 L1 L2 S with hX₁
  set Q₁ : Subgroup G := Q1 L1 L2 S with hQ₁
  set Q₂ : Subgroup G := Q2 L1 L2 S with hQ₂
  set Z₂ : Subgroup G := Z2 L1 L2 S with hZ₂
  clear_value X₁ Q₁ Q₂ Z₂
  have hsup : Q₁ ⊔ Q₂ = S := by
    refine le_antisymm (sup_le hQ₁S hQ₂S) ?_
    rw [← hX1Q2]
    exact sup_le (hX₁Q₁.trans le_sup_left) le_sup_right
  have hrel : Q₂.relIndex Q₁ = Q₂.relIndex (Q₁ ⊔ Q₂) := by
    have h2 := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
      (H := Q₁) (K := Q₂) hQ₁N).2
    rw [h2, Subgroup.inf_relIndex_left]
  set A : Subgroup G := Q₁ ⊓ Q₂ with hA
  have hArel : A.relIndex Q₁ = (2 ^ k) ^ 2 := by
    rw [hA, Subgroup.inf_relIndex_left, hrel, hsup, hSQ2]
  have hZA : Z₂ ⊓ A = Z₂ ⊓ Q₁ := by
    ext z
    rw [hA]
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hzZ, hzQ₁, -⟩
      exact ⟨hzZ, hzQ₁⟩
    · rintro ⟨hzZ, hzQ₁⟩
      exact ⟨hzZ, hzQ₁, hZQ hzZ⟩
  have hZrel : Z₂.relIndex A ≤ (2 ^ k) ^ 2 :=
    (Subgroup.relIndex_le_of_le_right (H := Z₂) (K := A)
      (L := centralizerMod Z₂ Q₂ S) hQQ (D15Proof.relIndex_ne_zero _ _)).trans hC
  have hcardA : Nat.card ↥A ≤ (2 ^ k) ^ 5 := by
    calc Nat.card ↥A = Z₂.relIndex A * Nat.card ↥(Z₂ ⊓ A) :=
          (Subgroup.relIndex_mul_card Z₂ A).symm
      _ ≤ (2 ^ k) ^ 2 * (2 ^ k) ^ 3 := by
          refine Nat.mul_le_mul hZrel ?_
          rw [hZA, hY]
      _ = (2 ^ k) ^ 5 := by rw [← pow_add]
  have hcardQ₁ : Nat.card ↥Q₁ ≤ (2 ^ k) ^ 7 := by
    have hmul := Subgroup.relIndex_mul_card A Q₁
    rw [show A ⊓ Q₁ = A from inf_eq_left.mpr (by rw [hA]; exact inf_le_left)] at hmul
    calc Nat.card ↥Q₁ = A.relIndex Q₁ * Nat.card ↥A := hmul.symm
      _ ≤ (2 ^ k) ^ 2 * (2 ^ k) ^ 5 := Nat.mul_le_mul (le_of_eq hArel) hcardA
      _ = (2 ^ k) ^ 7 := by rw [← pow_add]
  have hle : Nat.card ↥Q₁ ≤ Nat.card ↥X₁ := by
    rw [hI4]
    exact hcardQ₁
  exact (Subgroup.eq_of_le_of_card_ge hX₁Q₁ hle).symm

end CFSG.Quasithin.Stroth

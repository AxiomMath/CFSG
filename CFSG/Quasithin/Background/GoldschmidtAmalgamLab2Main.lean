module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab2Card
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLarge

public section

universe u

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmLarge

namespace F6

namespace GoldAmLab2

variable {D : Type*} [Group D]

theorem T_le_normalizer_R (A B : Subgroup D) :
    A ⊓ B ≤ Subgroup.normalizer ((pCoreOf 2 A ⊓ pCoreOf 2 B : Subgroup D) : Set D) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro r
  have hA := le_normalizer_pCoreOf 2 A ht.1
  have hB := le_normalizer_pCoreOf 2 B ht.2
  constructor
  · intro hr
    exact ⟨(Subgroup.mem_normalizer_iff.mp hA r).mp hr.1,
      (Subgroup.mem_normalizer_iff.mp hB r).mp hr.2⟩
  · intro hr
    exact ⟨(Subgroup.mem_normalizer_iff.mp hA r).mpr hr.1,
      (Subgroup.mem_normalizer_iff.mp hB r).mpr hr.2⟩

theorem card_T_ge_of_moves [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}
    (h : GoldHyp A B) (h32 : 32 ≤ Nat.card ↥(A ⊓ B)) (hn : IsNaturalAt A (A ⊓ B) z V)
    (hVQ : V ≤ pCoreOf 2 B) (hU : IsElemAbelian 2 (conjClosure V B))
    (hmove : ∃ y ∈ B, y * z * y⁻¹ ≠ z) : 256 ≤ Nat.card ↥(A ⊓ B) := by
  classical
  have h1 : OneSide A B z V := ⟨h, hn, hVQ, hU⟩
  obtain ⟨x, z', V', hxB, hx3, hxz, hz', hn', -⟩ :=
    exists_natural_data h.vertex_right hn.z_mem hn.z_sq hmove
  obtain ⟨a, ha1, haz, hVset⟩ := hn.basis
  have haV : a ∈ V := by
    have : a ∈ (V : Set D) := by rw [hVset]; simp
    exact this
  have hxT : x ∉ A ⊓ B := fun hxT => hxz (by
    have := Subgroup.mem_centralizer_iff.mp hn.z_mem.2 x hxT
    calc x * z * x⁻¹ = z * x * x⁻¹ := by rw [this]
      _ = z := by group)
  by_cases hcase : x ∉ Subgroup.normalizer ((pCoreOf 2 A ⊓ pCoreOf 2 B : Subgroup D) : Set D) ∨
      z * (x * z * x⁻¹) * (x * x * z * (x * x)⁻¹) ≠ 1
  · exact h1.card_T_ge hxB hx3 hxz haV ha1 haz hcase
  ·
    obtain ⟨hxN, hε⟩ := not_or.mp hcase
    have hxN : x ∈ Subgroup.normalizer ((pCoreOf 2 A ⊓ pCoreOf 2 B : Subgroup D) : Set D) :=
      not_not.mp hxN
    have hε : z * (x * z * x⁻¹) * (x * x * z * (x * x)⁻¹) = 1 := not_not.mp hε
    have hzz : z' = z := by
      have h2 : z * z' = 1 := by rw [hz', ← mul_assoc]; exact hε
      have h3 : z * z = 1 := by rw [← pow_two]; exact hn.z_sq
      exact (inv_eq_of_mul_eq_one_right h2).symm.trans (inv_eq_of_mul_eq_one_right h3)
    subst hzz
    have h32' : 32 ≤ Nat.card ↥(B ⊓ A) := by rwa [inf_comm]
    have hn₂ : IsNaturalAt B (B ⊓ A) z' V' := by rw [inf_comm]; exact hn'
    have hV'A : V' ≤ pCoreOf 2 A := hn₂.le_pCoreOf_of_large h.symm h32'
    have hAmove : ∃ g ∈ A, g * z' * g⁻¹ ≠ z' := by
      by_contra hcon
      push Not at hcon
      apply hn.not_normalizes
      refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      intro g hg
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      have hcm : Commute g z' := mul_eq_of_conj_eq (hcon g hg)
      exact (hcm.zpow_right k).symm.eq
    rcases critDist_dichotomy h.symm hn₂ hV'A with hb₂ | ⟨-, hU₂⟩
    · exfalso
      obtain ⟨g, hgA, hg⟩ := hAmove
      exact hg (centralizes_of_critDist_two h.symm hn₂ hb₂ g hgA)
    · have h2 : OneSide B A z' V' := ⟨h.symm, hn₂, hV'A, hU₂⟩
      obtain ⟨y, z'', V'', hyA, hy3, hyz, -, -, -⟩ :=
        exists_natural_data h.vertex_left hn.z_mem hn.z_sq hAmove
      obtain ⟨a₂, ha₂1, ha₂z, hV'set⟩ := hn₂.basis
      have ha₂V : a₂ ∈ V' := by
        have : a₂ ∈ (V' : Set D) := by rw [hV'set]; simp
        exact this
      have hyT : y ∉ B ⊓ A := fun hyT => hyz (by
        have := Subgroup.mem_centralizer_iff.mp
          (show z' ∈ Subgroup.centralizer ((B ⊓ A : Subgroup D) : Set D) by
            rw [inf_comm]; exact hn.z_mem.2) y hyT
        calc y * z' * y⁻¹ = z' * y * y⁻¹ := by rw [this]
          _ = z' := by group)
      by_cases hyN : y ∈ Subgroup.normalizer
          ((pCoreOf 2 B ⊓ pCoreOf 2 A : Subgroup D) : Set D)
      ·
        exfalso
        have hyN' : y ∈ Subgroup.normalizer
            ((pCoreOf 2 A ⊓ pCoreOf 2 B : Subgroup D) : Set D) := by
          rwa [inf_comm] at hyN
        have hTN := T_le_normalizer_R A B
        have hBN : B ≤ Subgroup.normalizer ((pCoreOf 2 A ⊓ pCoreOf 2 B : Subgroup D) : Set D) := by
          have := h.vertex_right.le_of_not_mem (C := B ⊓ Subgroup.normalizer
            ((pCoreOf 2 A ⊓ pCoreOf 2 B : Subgroup D) : Set D))
            (le_inf inf_le_right hTN) inf_le_left ⟨hxB, hxN⟩ hxT
          exact fun g hg => (this hg).2
        have hAN : A ≤ Subgroup.normalizer ((pCoreOf 2 A ⊓ pCoreOf 2 B : Subgroup D) : Set D) := by
          have := h.vertex_left.le_of_not_mem (C := A ⊓ Subgroup.normalizer
            ((pCoreOf 2 A ⊓ pCoreOf 2 B : Subgroup D) : Set D))
            (le_inf inf_le_left hTN) inf_le_left ⟨hyA, hyN'⟩ (by rwa [inf_comm] at hyT)
          exact fun g hg => (this hg).2
        have hRle : pCoreOf 2 A ⊓ pCoreOf 2 B ≤ A ⊓ B :=
          inf_le_left.trans h.pCoreOf_left_le
        have hbot := h.eq_bot_of_normalizes hAN hBN hRle
        have h4 := h1.card_T_eq
        rw [hbot, Subgroup.card_bot] at h4
        omega
      · have := h2.card_T_ge hyA hy3 hyz ha₂V ha₂1 ha₂z (Or.inl hyN)
        rwa [inf_comm] at this

theorem exists_move_of_natural {H T : Subgroup D} {z : D} {V : Subgroup D}
    (hn : IsNaturalAt H T z V) : ∃ g ∈ H, g * z * g⁻¹ ≠ z := by
  by_contra hcon
  push Not at hcon
  apply hn.not_normalizes
  refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  have hcm : Commute g z := mul_eq_of_conj_eq (hcon g hg)
  exact (hcm.zpow_right k).symm.eq

@[expose] def B3MovedCardBound : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (A B : Subgroup D) (z : D) (V : Subgroup D),
    GoldHyp A B → 32 ≤ Nat.card ↥(A ⊓ B) → IsNaturalAt A (A ⊓ B) z V → V ≤ pCoreOf 2 B →
      3 ≤ critDist (A ⊔ B) A B V → IsElemAbelian 2 (conjClosure V B) →
      (∃ y ∈ B, y * z * y⁻¹ ≠ z) → Nat.card ↥(A ⊓ B) ≤ 128

theorem b3LabelInput_of_movedCardBound (hc : B3MovedCardBound.{u}) : B3LabelInput.{u} := by
  intro D _ _ A B z V h h32 hn hVQ hb hU y hy
  by_contra hyz
  have h1 := hc D A B z V h h32 hn hVQ hb hU ⟨y, hy, hyz⟩
  have h2 := card_T_ge_of_moves h h32 hn hVQ hU ⟨y, hy, hyz⟩
  omega

end GoldAmLab2

end F6

end CFSG.Quasithin

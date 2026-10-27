module

public import CFSG.Quasithin.Background.C126NatDSL2
public import CFSG.Quasithin.Background.C126NatSL2

public section

namespace CFSG.Quasithin.C126.Nat

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped MatrixGroups commutatorElement

section Field

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem center_sl2_eq_bot [CharP F 2] : Subgroup.center SL(2, F) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hA'⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  have hr2 : r ^ 2 = 1 := by simpa using hr
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have h0 : (r - 1) ^ 2 = 0 := by linear_combination hr2 + (1 - r) * h2
  have hr1 : r = 1 := sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h0)
  rw [hr1] at hA'
  have : (A : Matrix (Fin 2) (Fin 2) F) = 1 := by rw [← hA']; simp
  exact (Subgroup.mem_bot).2 (Subtype.ext (by simpa using this))

theorem isSimpleGroup_sl2 [CharP F 2] (h : 4 ≤ Nat.card F) : IsSimpleGroup SL(2, F) := by
  have hq := (isQuasisimple_sl2 h).2.1
  have e : SL(2, F) ≃* (SL(2, F) ⧸ Subgroup.center SL(2, F)) :=
    ((QuotientGroup.quotientMulEquivOfEq (center_sl2_eq_bot (F := F))).trans
      QuotientGroup.quotientBot).symm
  exact e.isSimpleGroup

end Field

section Commutator

variable {Γ : Type*} [Group Γ]

theorem conj_mem_commutator_of_mem_left {S A : Subgroup Γ} {s : Γ} (hs : s ∈ S) {y : Γ}
    (hy : y ∈ (⁅S, A⁆ : Subgroup Γ)) : s * y * s⁻¹ ∈ (⁅S, A⁆ : Subgroup Γ) := by
  induction hy using Subgroup.closure_induction with
  | mem z hz =>
    obtain ⟨u, hu, a, ha, rfl⟩ := hz
    have e : s * ⁅u, a⁆ * s⁻¹ = ⁅s * u, a⁆ * ⁅s, a⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (Subgroup.commutator_mem_commutator (mul_mem hs hu) ha)
      (inv_mem (Subgroup.commutator_mem_commutator hs ha))
  | one => simp
  | mul y z _ _ hy hz =>
    have : s * (y * z) * s⁻¹ = (s * y * s⁻¹) * (s * z * s⁻¹) := by group
    rw [this]
    exact mul_mem hy hz
  | inv y _ hy =>
    have : s * y⁻¹ * s⁻¹ = (s * y * s⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem hy

theorem le_normalizer_commutator_left (S A : Subgroup Γ) :
    S ≤ Subgroup.normalizer ((⁅S, A⁆ : Subgroup Γ) : Set Γ) := fun s hs =>
  Subgroup.mem_normalizer_iff.2 fun y => ⟨fun hy => conj_mem_commutator_of_mem_left hs hy,
    fun hy => by
      have := conj_mem_commutator_of_mem_left (inv_mem hs) hy
      simpa [mul_assoc] using this⟩

theorem commutator_le_left_of_le_normalizer {S A : Subgroup Γ}
    (hA : A ≤ Subgroup.normalizer (S : Set Γ)) : ⁅S, A⁆ ≤ S :=
  Subgroup.commutator_le.2 fun g hg a ha => by
    rw [commutatorElement_def]
    have h1 : a * g⁻¹ * a⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 (hA ha) g⁻¹).1 (S.inv_mem hg)
    have h2 : g * (a * g⁻¹ * a⁻¹) ∈ S := S.mul_mem hg h1
    have h3 : g * (a * g⁻¹ * a⁻¹) = g * a * g⁻¹ * a⁻¹ := by group
    rwa [h3] at h2

end Commutator

section Perfectness

variable {F : Type} [Field F] [Finite F]

theorem commutator_eq_of_ne_bot [CharP F 2] (h : 4 ≤ Nat.card F) {Γ : Type*} [Group Γ]
    {L A : Subgroup Γ} (e : ↥L ≃* SL(2, F)) (hAL : A ≤ L) (hA : A ≠ ⊥) : ⁅L, A⁆ = L := by
  have hsimple := isSimpleGroup_sl2 (F := F) h
  have hML : ⁅L, A⁆ ≤ L := commutator_le_left_of_le_normalizer (hAL.trans Subgroup.le_normalizer)
  have hnorm : (⁅L, A⁆.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hML).2 (le_normalizer_commutator_left L A)
  have hN' : ((⁅L, A⁆.subgroupOf L).map e.toMonoidHom).Normal := hnorm.map _ e.surjective
  have := hN'
  rcases hsimple.eq_bot_or_eq_top_of_normal ((⁅L, A⁆.subgroupOf L).map e.toMonoidHom) with h0 | h1
  · exfalso
    refine hA (eq_bot_iff.2 fun a ha => ?_)
    have hcomm : ∀ l : ↥L, (l : Γ) * a = a * l := fun l => by
      have hmem : (⟨⁅(l : Γ), a⁆, hML (Subgroup.commutator_mem_commutator l.2 ha)⟩ : ↥L) ∈
          ⁅L, A⁆.subgroupOf L := Subgroup.commutator_mem_commutator l.2 ha
      have h1 : e ⟨⁅(l : Γ), a⁆, _⟩ ∈ (⁅L, A⁆.subgroupOf L).map e.toMonoidHom := ⟨_, hmem, rfl⟩
      rw [h0, Subgroup.mem_bot] at h1
      have h2 : (⟨⁅(l : Γ), a⁆, hML (Subgroup.commutator_mem_commutator l.2 ha)⟩ : ↥L) = 1 :=
        e.injective (h1.trans (map_one e).symm)
      exact commutatorElement_eq_one_iff_mul_comm.1 (congrArg Subtype.val h2)
    have hz : e ⟨a, hAL ha⟩ ∈ Subgroup.center SL(2, F) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨l, rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul]
      exact congrArg e (Subtype.ext (hcomm l))
    rw [center_sl2_eq_bot, Subgroup.mem_bot] at hz
    have : (⟨a, hAL ha⟩ : ↥L) = 1 := e.injective (hz.trans (map_one e).symm)
    exact congrArg Subtype.val this
  · refine le_antisymm hML fun l hl => ?_
    have hmem : e ⟨l, hl⟩ ∈ (⁅L, A⁆.subgroupOf L).map e.toMonoidHom := h1 ▸ Subgroup.mem_top _
    obtain ⟨m, hm, hme⟩ := hmem
    have hmeq : m = ⟨l, hl⟩ := e.injective hme
    rw [hmeq] at hm
    exact hm

end Perfectness

section Sylow

variable {F : Type} [Field F] [Finite F]

theorem card_sylow_of_equiv_sl2 {Γ : Type*} [Group Γ] [Finite Γ] {L S : Subgroup Γ} {n : ℕ}
    (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n) (e : ↥L ≃* SL(2, F)) (hS : IsSylowTwoOf S L) :
    Nat.card S = 2 ^ n := by
  rw [hS.card_eq]
  unfold twoPart
  rw [Nat.card_congr e.toEquiv, factorization_card_sl2 hn hF]

end Sylow

end CFSG.Quasithin.C126.Nat

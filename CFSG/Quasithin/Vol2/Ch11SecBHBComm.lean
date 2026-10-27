module

public import CFSG.Quasithin.Vol2.Ch11SecBHBGen

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G]

theorem map_conj_eq_self_of_mem_normalizer {B : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (B : Set G)) : B.map (MulAut.conj g).toMonoidHom = B := by
  apply le_antisymm
  · rintro _ ⟨b, hb, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg b).mp hb
  · intro b hb
    refine ⟨g⁻¹ * b * g, ?_, by simp [mul_assoc]⟩
    exact (Subgroup.mem_normalizer_iff.mp hg _).mpr (by simpa [mul_assoc] using hb)

theorem normalizer_le_normalizer_commutator (A : Subgroup G) :
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer ((⁅A, A⁆ : Subgroup G) : Set G) := by
  intro g hg
  refine mem_normalizer_of_map_conj_eq ?_
  rw [Subgroup.map_commutator, map_conj_eq_self_of_mem_normalizer hg]

theorem commutatorElement_mul_left' (a b c : G) : ⁅a * b, c⁆ = a * ⁅b, c⁆ * a⁻¹ * ⁅a, c⁆ := by
  simp only [commutatorElement_def]
  group

theorem commutatorElement_inv_left' (a c : G) : ⁅a⁻¹, c⁆ = a⁻¹ * ⁅a, c⁆⁻¹ * a := by
  simp only [commutatorElement_def]
  group

theorem commutatorElement_mul_right' (a b c : G) : ⁅a, b * c⁆ = ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) := by
  simp only [commutatorElement_def]
  group

theorem commutatorElement_inv_right' (a c : G) : ⁅a, c⁻¹⁆ = c⁻¹ * ⁅a, c⁆⁻¹ * c := by
  simp only [commutatorElement_def]
  group

theorem commutator_sSup_le {𝒜 : Set (Subgroup G)} {R : Subgroup G}
    (hR : sSup 𝒜 ≤ Subgroup.normalizer (R : Set G))
    (hgen : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, ∀ a ∈ A, ∀ b ∈ B, ⁅a, b⁆ ∈ R) : ⁅sSup 𝒜, sSup 𝒜⁆ ≤ R := by
  set Y := sSup 𝒜 with hYdef
  have hconj : ∀ y ∈ Y, ∀ r ∈ R, y * r * y⁻¹ ∈ R := fun y hy r hr =>
    (Subgroup.mem_normalizer_iff.mp (hR hy) r).mp hr
  have hright : ∀ A ∈ 𝒜, ∀ a ∈ A, ∀ z ∈ Y, ⁅a, z⁆ ∈ R := by
    intro A hA a ha
    let W : Subgroup G :=
      { carrier := {z | z ∈ Y ∧ ⁅a, z⁆ ∈ R}
        one_mem' := ⟨Y.one_mem, by simp [commutatorElement_def]⟩
        mul_mem' := fun {x y} hx hy => ⟨Y.mul_mem hx.1 hy.1, by
          rw [commutatorElement_mul_right']
          exact R.mul_mem hx.2 (hconj x hx.1 _ hy.2)⟩
        inv_mem' := fun {x} hx => ⟨Y.inv_mem hx.1, by
          rw [commutatorElement_inv_right']
          have := hconj x⁻¹ (Y.inv_mem hx.1) _ (R.inv_mem hx.2)
          simpa using this⟩ }
    have hYW : Y ≤ W := sSup_le fun B hB b hb =>
      ⟨(le_sSup hB : B ≤ Y) hb, hgen A hA B hB a ha b hb⟩
    exact fun z hz => (hYW hz).2
  let Z : Subgroup G :=
    { carrier := {y | y ∈ Y ∧ ∀ z ∈ Y, ⁅y, z⁆ ∈ R}
      one_mem' := ⟨Y.one_mem, fun z _ => by simp [commutatorElement_def]⟩
      mul_mem' := fun {x y} hx hy => ⟨Y.mul_mem hx.1 hy.1, fun z hz => by
        rw [commutatorElement_mul_left']
        exact R.mul_mem (hconj x hx.1 _ (hy.2 z hz)) (hx.2 z hz)⟩
      inv_mem' := fun {x} hx => ⟨Y.inv_mem hx.1, fun z hz => by
        rw [commutatorElement_inv_left']
        have := hconj x⁻¹ (Y.inv_mem hx.1) _ (R.inv_mem (hx.2 z hz))
        simpa using this⟩ }
  have hYZ : Y ≤ Z := sSup_le fun A hA a ha =>
    ⟨(le_sSup hA : A ≤ Y) ha, hright A hA a ha⟩
  exact Subgroup.commutator_le.mpr fun y hy z hz => (hYZ hy).2 z hz

theorem commutator_sSup_le_pCoreOf {𝒜 : Set (Subgroup G)}
    (hcomm : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A = B ∨ ⁅A, B⁆ = ⊥)
    (h2 : ∀ A ∈ 𝒜, IsPGroup 2 ↥⁅A, A⁆) :
    ⁅sSup 𝒜, sSup 𝒜⁆ ≤ pCoreOf 2 (sSup 𝒜) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := sSup 𝒜 with hYdef
  have hnorm : ∀ A ∈ 𝒜, Y ≤ Subgroup.normalizer (A : Set G) := by
    intro A hA
    refine sSup_le fun B hB b hb => ?_
    rcases hcomm A hA B hB with rfl | h
    · exact Subgroup.le_normalizer hb
    · rw [Subgroup.mem_normalizer_iff]
      intro a
      have hab : ∀ a ∈ A, b * a * b⁻¹ = a := by
        intro a ha
        have h1 : ⁅a, b⁆ = 1 := by
          have := Subgroup.commutator_mem_commutator ha hb
          rwa [h, Subgroup.mem_bot] at this
        rw [commutatorElement_eq_one_iff_mul_comm] at h1
        rw [← h1]
        group
      constructor
      · intro ha
        rw [hab a ha]
        exact ha
      · intro ha
        have h1 := hab _ ha
        have h2 : a = b * a * b⁻¹ := by
          have := congrArg (fun z => b⁻¹ * z * b) h1
          simp only [mul_assoc, inv_mul_cancel_left] at this
          simpa [mul_assoc] using this.symm
        rw [h2]
        exact ha
  have hAO : ∀ A ∈ 𝒜, ⁅A, A⁆ ≤ pCoreOf 2 Y := fun A hA =>
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((commutator_le_self A).trans (le_sSup hA))
      ((hnorm A hA).trans (normalizer_le_normalizer_commutator A)) (h2 A hA)
  refine commutator_sSup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
    fun A hA B hB a ha b hb => ?_
  rcases hcomm A hA B hB with rfl | h
  · exact hAO A hA (Subgroup.commutator_mem_commutator ha hb)
  · have := Subgroup.commutator_mem_commutator ha hb
    rw [h, Subgroup.mem_bot] at this
    rw [this]
    exact Subgroup.one_mem _

end CFSG.Quasithin.Vol2.Ch11.SecB

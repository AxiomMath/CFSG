module

public import CFSG.Timmesfeld.Bridge.RootStructTwoLocalSetting
public import CFSG.Timmesfeld.Exceptional.Counting

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

theorem mul_eq_one_iff_of_mem_pair {G : Type*} [Group G] {a c₁ c₂ : G} (ha1 : a ≠ 1)
    (haa : a * a = 1) (h₁ : c₁ = 1 ∨ c₁ = a) (h₂ : c₂ = 1 ∨ c₂ = a) :
    c₁ * c₂ = 1 ↔ (c₁ = 1 ↔ c₂ = 1) := by
  rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl <;> simp [ha1, haa]

namespace TwoLocalSetting

variable {G : Type*} [Group G] {D : Set G} (S : TwoLocalSetting G D)
include S

theorem nCore_eq {a : G} (ha : a ∈ D) :
    nCore D a = Subgroup.closure {x | x ∈ D ∧ Commute x a} := by
  have := S.hyp.finite
  unfold nCore
  congr 1
  ext x
  exact ⟨fun ⟨hx, hxQ⟩ => ⟨hx, Moufang.commute_of_mem_twoCore hxQ⟩,
    fun ⟨hx, hxa⟩ => ⟨hx, S.noLevi.mem_twoCore S.hyp.isClass S.root ha hx hxa⟩⟩

theorem mem_nCore {a x : G} (ha : a ∈ D) (hx : x ∈ D) (hxa : Commute x a) : x ∈ nCore D a := by
  rw [S.nCore_eq ha]
  exact Subgroup.subset_closure ⟨hx, hxa⟩

theorem collinearSet_eq {a : G} (ha : a ∈ D) :
    Moufang.collinearSet D a = {x | x ∈ D ∧ Commute a x ∧ x ≠ a} := by
  ext x
  constructor
  · rintro ⟨hx, hax, haxD⟩
    refine ⟨hx, hax, fun h => ?_⟩
    rw [h, S.root.mul_self_eq_one ha] at haxD
    exact S.root.ne_one haxD rfl
  · rintro ⟨hx, hax, hxa⟩
    exact ⟨hx, hax, S.mul_mem_of_commute ha hx hax (Ne.symm hxa)⟩

theorem mem_nCore_of_mem_collinearSet {a x : G} (ha : a ∈ D)
    (hx : x ∈ Moufang.collinearSet D a) : x ∈ nCore D a :=
  S.mem_nCore ha hx.1 hx.2.1.symm

theorem self_mem {a : G} (ha : a ∈ D) : a ∈ nCore D a :=
  S.mem_nCore ha ha (Commute.refl a)

theorem commutator_eq {a x y : G} (ha : a ∈ D) (hx : x ∈ nCore D a) (hy : y ∈ nCore D a) :
    x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = a := by
  have hle := S.noLevi.commutator_le_zpowers S.root (fun g _ h => S.conj_mem g h) S.noPolar
    S.noPlane ha
  rw [← S.nCore_eq ha] at hle
  exact (mem_zpowers_iff_of_mul_self (S.root.mul_self_eq_one ha)).1
    (hle (Subgroup.commutator_mem_commutator hx hy))

theorem commute_mul_right_iff {a x y z : G} (ha : a ∈ D) (hx : x ∈ nCore D a)
    (hy : y ∈ nCore D a) (hz : z ∈ nCore D a) :
    Commute x (y * z) ↔ (Commute x y ↔ Commute x z) := by
  have hD := S.root
  have hya : Commute y a := commute_of_mem_nCore hy
  have key : x * (y * z) * x⁻¹ * (y * z)⁻¹ =
      (x * y * x⁻¹ * y⁻¹) * (x * z * x⁻¹ * z⁻¹) := by
    have e : x * (y * z) * x⁻¹ * (y * z)⁻¹ =
        (x * y * x⁻¹ * y⁻¹) * (y * (x * z * x⁻¹ * z⁻¹) * y⁻¹) := by group
    rw [e]
    congr 1
    rcases S.commutator_eq ha hx hz with h | h <;> rw [h]
    · rw [mul_one, mul_inv_cancel]
    · rw [hya.eq, mul_inv_cancel_right]
  have hcomm : ∀ w, Commute x w ↔ x * w * x⁻¹ * w⁻¹ = 1 :=
    fun _ => commutatorElement_eq_one_iff_commute.symm
  rw [hcomm, hcomm, hcomm, key]
  exact mul_eq_one_iff_of_mem_pair (hD.ne_one ha) (hD.mul_self_eq_one ha)
    (S.commutator_eq ha hx hy) (S.commutator_eq ha hx hz)

theorem commute_mul_left_iff {a x y z : G} (ha : a ∈ D) (hx : x ∈ nCore D a)
    (hy : y ∈ nCore D a) (hz : z ∈ nCore D a) :
    Commute (x * y) z ↔ (Commute x z ↔ Commute y z) := by
  rw [Commute.symm_iff, S.commute_mul_right_iff ha hz hx hy, Commute.symm_iff (a := z),
    Commute.symm_iff (a := z)]

theorem forall_commute_nCore_iff {a x : G} (ha : a ∈ D) :
    (∀ m ∈ nCore D a, Commute x m) ↔ ∀ e ∈ D, Commute e a → Commute x e := by
  refine ⟨fun h e he hea => h e (S.mem_nCore ha he hea), fun h m hm => ?_⟩
  rw [S.nCore_eq ha] at hm
  induction hm using Subgroup.closure_induction with
  | mem e he => exact h e he.1 he.2
  | one => exact Commute.one_right x
  | mul _ _ _ _ ih₁ ih₂ => exact ih₁.mul_right ih₂
  | inv _ _ ih => exact ih.inv_right

theorem commute_iff_eq_or_eq_mul {a x y : G} (ha : a ∈ D) (hx : x ∈ D) (hy : y ∈ D)
    (hax : Commute a x) (hay : Commute a y) (hxa : x ≠ a) (hya : y ≠ a) :
    Commute x y ↔ y = x ∨ y = a * x := by
  have hD := S.root
  constructor
  · intro hxy
    rcases S.cases ha hx hy hax hay hxa hya with h | h | ⟨-, hsq⟩
    · exact Or.inl h
    · exact Or.inr h
    · refine absurd ?_ (hD.ne_one ha)
      rw [← hsq, sq, hxy.symm.mul_mul_mul_comm, hD.mul_self_eq_one hx, hD.mul_self_eq_one hy,
        one_mul]
  · rintro (h | h)
    · rw [h]
    · rw [h]
      exact hax.symm.mul_right (Commute.refl x)

theorem conj_eq_mul_of_not_commute {a x y : G} (ha : a ∈ D) (hx : x ∈ D) (hy : y ∈ D)
    (hax : Commute a x) (hay : Commute a y) (hxa : x ≠ a) (hya : y ≠ a) (hxy : ¬ Commute x y) :
    x * y * x⁻¹ = a * y := by
  have hD := S.root
  rcases S.cases ha hx hy hax hay hxa hya with h | h | ⟨-, hsq⟩
  · exact absurd (by rw [h]) hxy
  · exact absurd (by rw [h]; exact hax.symm.mul_right (Commute.refl x)) hxy
  · rw [← hsq, hD.inv_eq hx, sq]
    calc x * y * x = x * y * x * (y * y) := by rw [hD.mul_self_eq_one hy, mul_one]
      _ = x * y * (x * y) * y := by group

theorem forall_commute_or_forall_commute_mul {a e g : G} (ha : a ∈ D) (he : e ∈ nCore D a)
    (hg : g ∈ nCore D a) (h : ∀ m ∈ nCore D a, Commute m e → Commute g m) :
    (∀ m ∈ nCore D a, Commute g m) ∨ (∀ m ∈ nCore D a, Commute (g * e) m) := by
  by_cases hcen : ∀ m ∈ nCore D a, Commute g m
  · exact Or.inl hcen
  right
  push Not at hcen
  obtain ⟨m₀, hm₀, hgm₀⟩ := hcen
  have hm₀e : ¬ Commute m₀ e := fun h' => hgm₀ (h m₀ hm₀ h')
  intro m hm
  rw [S.commute_mul_left_iff ha hg he hm]
  by_cases hme : Commute m e
  · exact iff_of_true (h m hm hme) hme.symm
  ·
    have hmm₀ : Commute (m * m₀) e := by
      rw [S.commute_mul_left_iff ha hm hm₀ (he)]
      exact iff_of_false hme hm₀e
    have hg' := h (m * m₀) ((nCore D a).mul_mem hm hm₀) hmm₀
    rw [S.commute_mul_right_iff ha hg hm hm₀] at hg'
    refine iff_of_false (fun hgm => hgm₀ (hg'.1 hgm)) fun hem => hme hem.symm

theorem commute_or_commute_mul {a e y m : G} (ha : a ∈ D) (he : e ∈ nCore D a)
    (hy : y ∈ nCore D a) (hm : m ∈ nCore D a) (hye : ¬ Commute y e) :
    Commute m e ∨ Commute (m * y) e := by
  rw [S.commute_mul_left_iff ha hm hy he]
  tauto

theorem commute_of_commute_of_commute_mul {a e y c : G} (ha : a ∈ D) (he : e ∈ nCore D a)
    (hy : y ∈ nCore D a) (hye : ¬ Commute y e)
    (hc : ∀ m ∈ nCore D a, Commute m e → Commute c m) (hcy : Commute c y) :
    ∀ m ∈ nCore D a, Commute c m := by
  intro m hm
  rcases S.commute_or_commute_mul ha he hy hm hye with h | h
  · exact hc m hm h
  · have h1 := hc (m * y) ((nCore D a).mul_mem hm hy) h
    have e : m = m * y * y⁻¹ := by group
    rw [e]
    exact h1.mul_right hcy.inv_right

end TwoLocalSetting

end CFSG.Timmesfeld.Bridge

module

public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin

namespace HSRuLoc

namespace Excl

open CFSG.Open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G]

theorem le_normalizer_of_conj_mem {A D : Subgroup G} (h : ∀ g ∈ A, ∀ d ∈ D, g * d * g⁻¹ ∈ D) :
    A ≤ Subgroup.normalizer (D : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro d
  refine ⟨fun hd => h g hg d hd, fun hd => ?_⟩
  simpa [mul_assoc] using h g⁻¹ (A.inv_mem hg) _ hd

theorem sup_le_normalizer {K S : Subgroup G} (hS : S ≤ Subgroup.normalizer (K : Set G)) :
    K ⊔ S ≤ Subgroup.normalizer (K : Set G) :=
  sup_le Subgroup.le_normalizer hS

theorem pCoreOf_le_pCoreOf_sup [Finite G] {K S : Subgroup G}
    (hS : S ≤ Subgroup.normalizer (K : Set G)) : pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ S) :=
  le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans le_sup_left)
    ((sup_le_normalizer hS).trans (normalizer_le_normalizer_pCoreOf 2 K)) (pCoreOf_isPGroup 2 K)

theorem commutator_pCoreOf_sup_le [Finite G] {K S : Subgroup G}
    (hS : S ≤ Subgroup.normalizer (K : Set G)) : ⁅pCoreOf 2 (K ⊔ S), K⁆ ≤ pCoreOf 2 K := by
  rw [Subgroup.commutator_le]
  intro x hx k hk
  have hxX : x ∈ K ⊔ S := pCoreOf_le 2 _ hx
  have hkX : k ∈ K ⊔ S := (le_sup_left : K ≤ K ⊔ S) hk
  have hD : K ⊓ pCoreOf 2 (K ⊔ S) ≤ pCoreOf 2 K := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_left (le_normalizer_of_conj_mem ?_)
      ((pCoreOf_isPGroup 2 (K ⊔ S)).to_le inf_le_right)
    intro g hg d hd
    exact ⟨K.mul_mem (K.mul_mem hg hd.1) (K.inv_mem hg),
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ ((le_sup_left : K ≤ K ⊔ S) hg)) d).mp hd.2⟩
  refine hD ⟨?_, ?_⟩
  · rw [commutatorElement_def]
    exact K.mul_mem ((Subgroup.mem_normalizer_iff.mp (sup_le_normalizer hS hxX) k).mp hk)
      (K.inv_mem hk)
  · have e : ⁅x, k⁆ = x * (k * x⁻¹ * k⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [e]
    exact (pCoreOf 2 (K ⊔ S)).mul_mem hx
      ((Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hkX) x⁻¹).mp
        ((pCoreOf 2 (K ⊔ S)).inv_mem hx))

theorem exists_card_ker {L Q : Subgroup G} (hQL : Q ≤ L) {H : Type} [Group H] (π : ↥L →* H)
    (B : Subgroup H) (hB : ∀ y, y ∈ B ↔ ∃ q : G, ∃ hq : q ∈ Q, π ⟨q, hQL hq⟩ = y) :
    ∃ T : Subgroup G, T ≤ Q ∧ (∀ t ∈ T, ∃ l : ↥L, (l : G) = t ∧ π l = 1) ∧
      Nat.card ↥Q = Nat.card ↥B * Nat.card ↥T := by
  let φ : ↥Q →* H := π.comp (Subgroup.inclusion hQL)
  refine ⟨φ.ker.map Q.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · intro t ht
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp ht
    exact ⟨Subgroup.inclusion hQL q, rfl, hq⟩
  · have hrange : φ.range = B := by
      ext y
      rw [hB y, MonoidHom.mem_range]
      constructor
      · rintro ⟨q, rfl⟩
        exact ⟨q, q.2, rfl⟩
      · rintro ⟨q, hq, rfl⟩
        exact ⟨⟨q, hq⟩, rfl⟩
    rw [Subgroup.card_map_of_injective Q.subtype_injective, ← Subgroup.card_ker_mul_card_range φ,
      hrange, mul_comm]

theorem commute_of_exists_ker {L : Subgroup G} {H : Type} [Group H] {π : ↥L →* H}
    (hz : π.ker ≤ Subgroup.center ↥L) {t : G} (ht : ∃ l : ↥L, (l : G) = t ∧ π l = 1) {y : G}
    (hy : y ∈ L) : y * t = t * y := by
  obtain ⟨l, rfl, hl⟩ := ht
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp (hz hl) ⟨y, hy⟩)

end Excl

end HSRuLoc

end CFSG.Quasithin

module

public import CFSG.Quasithin.Vol2.Ch11SecU1Crit
public import CFSG.Quasithin.Vol2.Ch11SecU1Defs

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.Quasithin.A1b
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem tauOf_le_centralizer (hO2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥) {T A : Subgroup G} {a : G}
    (ha : a ∈ A) : tauOf ⊤ T A ≤ Subgroup.centralizer {a} := by
  intro t ht
  have h1 := (mem_tauOf.mp ht).2.2 a ha
  rw [hO2, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact Subgroup.mem_centralizer_singleton_iff.mpr h1

omit [Finite G] in
theorem exists_mem_ne_ne {A : Subgroup G} [Finite A] (hA : 3 ≤ Nat.card A) (a b : G) :
    ∃ x ∈ A, x ≠ a ∧ x ≠ b := by
  by_contra hcon
  push Not at hcon
  have hsub : (A : Set G) ⊆ {a, b} := fun x hx => by
    by_cases hxa : x = a
    · exact Or.inl hxa
    · exact Or.inr (hcon x hx hxa)
  have h1 : Nat.card A = (A : Set G).ncard := Nat.card_coe_set_eq (A : Set G)
  have h2 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h3 : ({a, b} : Set G).ncard ≤ 2 := by
    calc ({a, b} : Set G).ncard ≤ ({b} : Set G).ncard + 1 := Set.ncard_insert_le a {b}
      _ = 2 := by rw [Set.ncard_singleton]
  omega

theorem member_of_oddTorus (hTor : TorusMember) {L : Subgroup G}
    (hO2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥) {T A : Subgroup G} (hT : IsSylowIn 2 T ⊤)
    (hAT : A ≤ T) (hA : IsElemAbelian 2 A) {z b : G} (hzA : z ∈ A) (hzL : z ∈ L)
    (hz2 : orderOf z = 2) (hbA : b ∈ A) (hzb : z ≠ b) (hb : OddTorus L b) :
    ∃ K : Subgroup G, IsE 1 ⊤ T A K ∧ ¬ K ≤ Subgroup.centralizer {z} := by
  obtain ⟨P, -, hPp, hP2, hPn, hPc⟩ := hb
  have hzc : z ∈ L ⊓ Subgroup.centralizer {b} :=
    ⟨hzL, le_centralizer_of_isElemAbelian hA hbA hzA⟩
  have hPz := hPc z hzc hz2 hzb
  exact ⟨P ⊔ tauOf ⊤ T A, hTor G T A P hT hAT hA hPp hP2
    ((tauOf_le_centralizer hO2 hbA).trans hPn) ⟨z, hzA, hPz⟩,
    fun hle => hPz (le_sup_left.trans hle)⟩

theorem member_of_sigma (hComp : ComponentMember) {L : Subgroup G} (h : Setting L)
    (hO2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥) {T A : Subgroup G} (hT : IsSylowIn 2 T ⊤)
    (hAT : A ≤ T) (hA : IsElemAbelian 2 A) {v b z : G} (hvA : v ∈ A) (hvL : v ∈ L) (hv1 : v ≠ 1)
    (hbA : b ∈ A) (hA4 : ∀ x ∈ A, x = 1 ∨ x = v ∨ x = b ∨ x = v * b)
    (hSyl : IsSylowIn 2 (T ⊓ Subgroup.centralizer {b}) (Subgroup.centralizer {b}))
    (hb : SigmaFacts L b) (hzL : z ∈ L) (hz2 : orderOf z = 2) :
    ∃ K : Subgroup G, IsE 1 ⊤ T A K ∧ ¬ K ≤ Subgroup.centralizer {z} := by
  obtain ⟨L₀, hle, hs, hnab, hnorm, hcent⟩ := hb
  set C := Subgroup.centralizer ({b} : Set G) with hC
  have hL₀C : L₀ ≤ C := hle.trans inf_le_right
  have hSyl₀ : IsSylowIn 2 (T ⊓ L₀) L₀ := by
    have h1 := B6.isSylowTwoOf_inf_normal hSyl hL₀C hnorm
    rwa [inf_assoc, inf_eq_right.mpr hL₀C] at h1
  have hbc : b ∈ Subgroup.centralizer (L₀ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hL₀C hl)
  have hvc : v ∉ Subgroup.centralizer (L₀ : Set G) := fun hv => hv1 (by
    have h1 : v ∈ L ⊓ Subgroup.centralizer (L₀ : Set G) := ⟨hvL, hv⟩
    rw [hcent] at h1
    exact Subgroup.mem_bot.mp h1)
  have hcomm : v * b = b * v := le_centralizer_of_isElemAbelian hA hbA hvA |>
    Subgroup.mem_centralizer_singleton_iff.mp
  have hvv : v * v = 1 := by rw [← sq]; exact hA.2 v hvA
  have hrel : (A ⊓ Subgroup.centralizer (L₀ : Set G)).relIndex A = 2 := by
    refine Subgroup.relIndex_eq_two_iff_exists_notMem_and.mpr
      ⟨v, hvA, fun hv => hvc hv.2, fun x hx => ?_⟩
    rcases hA4 x hx with rfl | rfl | rfl | rfl
    · exact Or.inr ⟨A.one_mem, Subgroup.one_mem _⟩
    · exact Or.inl ⟨A.mul_mem hvA hvA, by rw [hvv]; exact Subgroup.one_mem _⟩
    · exact Or.inr ⟨hbA, hbc⟩
    · refine Or.inl ⟨A.mul_mem (A.mul_mem hvA hbA) hvA, ?_⟩
      rw [mul_assoc, ← hcomm, ← mul_assoc, hvv, one_mul]
      exact hbc
  have hτ : tauOf ⊤ T A ≤ Subgroup.normalizer (L₀ : Set G) :=
    (tauOf_le_centralizer hO2 hbA).trans hnorm
  refine ⟨L₀ ⊔ tauOf ⊤ T A, hComp G T A L₀ hT hAT hA hs hnab hτ hSyl₀ hrel, fun hK => ?_⟩
  have hL₀z : L₀ ≤ L ⊓ Subgroup.centralizer {z} :=
    le_inf (hle.trans inf_le_left) (le_sup_left.trans hK)
  have := h.inner_solvable z hzL hz2
  have : Group.IsSolvable ↥L₀ :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hL₀z)
  exact not_isSolvable_of_simple hnab this

end CFSG.Quasithin.Vol2.Ch11.SecU1

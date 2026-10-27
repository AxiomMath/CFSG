module

public import CFSG.Quasithin.EmptyFaithful.S146P19
public import CFSG.Quasithin.EmptyFaithful.S146P4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

namespace SBc13

section Basic

variable {G : Type} [Group G] {T M H : Subgroup G} {H₁ H₂ K₁ K₂ : Subgroup G} {s : G}

theorem conjSub_mul' (a b : G) (X : Subgroup G) :
    conjSub (a * b) X = conjSub a (conjSub b X) := by
  ext x
  simp only [mem_conjSub]
  have e : (a * b)⁻¹ * x * (a * b) = b⁻¹ * (a⁻¹ * x * a) * b := by group
  rw [e]

theorem card_conjSub' (g : G) (X : Subgroup G) : Nat.card (conjSub g X) = Nat.card X :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem K₁_ne_K₂ (hset : Setup14615 T M H H₁ H₂ K₁ K₂ s) : K₁ ≠ K₂ := by
  intro h
  apply hset.s_not
  have : conjSub s K₁ = K₁ := by rw [← hset.conj]; exact h.symm
  exact CosetGeom.mem_normalizer_of_conjSub_eq this

theorem K₁_eq_conjSub (hset : Setup14615 T M H H₁ H₂ K₁ K₂ s) : K₁ = conjSub s⁻¹ K₂ := by
  rw [hset.conj, conjSub_conjSub_inv]

theorem card_K₁ (hset : Setup14615 T M H H₁ H₂ K₁ K₂ s) : Nat.card K₁ = Nat.card K₂ := by
  rw [K₁_eq_conjSub hset, card_conjSub']

theorem oTwoUpper_K₁ [Finite G] (hset : Setup14615 T M H H₁ H₂ K₁ K₂ s) : oTwoUpper K₁ = K₁ := by
  have h2 : conjSub s (oTwoUpper K₁) = conjSub s K₁ := by
    rw [← oTwoUpper_conjSub_P, ← hset.conj]; exact hset.perf₂
  have := congrArg (conjSub s⁻¹) h2
  rwa [conjSub_conjSub_inv, conjSub_conjSub_inv] at this

end Basic

section Pair

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ K₁ K₂ : Subgroup G}
  {t s : G}

theorem conjSub_K₁_eq_of_conjSub_K₂_eq (S : Setting146 G T M)
    (hset : Setup14615 T M H H₁ H₂ K₁ K₂ s) (hgap : Gap3Pair T K₁ K₂) {x : G} (hx : x ∈ mcOf T)
    (h2 : conjSub x K₂ = K₂) : conjSub x K₁ = K₁ := by
  have hsG : s ∈ mcOf T := S.isHTM_mcOf.1.1 hset.s_mem
  have h1 : conjSub x K₁ = conjSub (x * s⁻¹) K₂ := by
    rw [K₁_eq_conjSub hset, conjSub_mul']
  rcases hgap (x * s⁻¹) ((mcOf T).mul_mem hx ((mcOf T).inv_mem hsG)) with h | h
  · exfalso
    have h3 : conjSub x K₁ = conjSub x K₂ := by rw [h1, h, h2]
    have h4 := congrArg (conjSub x⁻¹) h3
    rw [conjSub_conjSub_inv, conjSub_conjSub_inv] at h4
    exact K₁_ne_K₂ hset h4
  · rw [h1, h]

theorem kz_le_mcOf (S : Setting146 G T M) {PQ : Subgroup G} (hred : IsRedCE T M H PQ p) :
    conjClosure (oTwoUpper H) (mcOf T) ≤ mcOf T := by
  have hH : H ≤ mcOf T := S.le_mcOf hred.isHTM
  exact conjClosure_le fun g hg v hv =>
    (mcOf T).mul_mem ((mcOf T).mul_mem hg (hH (oTwoUpper_le H hv))) ((mcOf T).inv_mem hg)

theorem normalizer_eq_mcOf_of_char (S : Setting146 G T M) {C : Subgroup G}
    (hCQ : C ≤ pCoreOf 2 (mcOf T)) (hC : C ≠ ⊥)
    (hchar : (C.subgroupOf (pCoreOf 2 (mcOf T))).Characteristic) :
    Subgroup.normalizer (C : Set G) = mcOf T := by
  have hle : mcOf T ≤ Subgroup.normalizer (C : Set G) :=
    (le_normalizer_pCoreOf 2 (mcOf T)).trans
      (normalizer_le_normalizer_of_characteristic_subgroupOf hCQ hchar)
  have hL : IsTwoLocal (Subgroup.normalizer (C : Set G)) :=
    ⟨C, hC, (pCoreOf_isPGroup 2 _).to_le hCQ, rfl⟩
  exact S.hyp.mc_max.2 _ hL hle

end Pair

end SBc13

end CFSG.Quasithin

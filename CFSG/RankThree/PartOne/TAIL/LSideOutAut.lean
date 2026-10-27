module

public import CFSG.RankThree.PartOne.TAIL.KSideOutLin

public section

namespace CFSG.RankThree.PartOne.TAIL

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open CFSG.ComponentClassification.CatalogueBHigherLinearField (slFieldAut)
open CFSG.ComponentClassification.CatalogueBGraphForm (slGraphAut)

theorem aut_sl_zmod_two {n : ℕ} (hn : 3 ≤ n)
    (β : MulAut (SpecialLinearGroup (Fin n) (ZMod 2))) :
    ∃ (g : SpecialLinearGroup (Fin n) (ZMod 2)) (ε : ℕ), ε ≤ 1 ∧
      β = MulAut.conj g * slGraphAut n (ZMod 2) ^ ε := by
  obtain ⟨A, σ, ε, hε, hβ⟩ := CFSG.RankThree.PartOne.AUTSL.exists_eq_std_of_mulAut_sl hn β
  have hg : Nat.gcd n (Nat.card (ZMod 2) - 1) = 1 := by
    rw [Nat.card_zmod]
    simp
  obtain ⟨g, hgA⟩ := slConjugation_mem_inn hg A
  have hσ : σ = RingEquiv.refl (ZMod 2) := by
    apply RingEquiv.ext
    intro x
    exact congrArg (fun f : ZMod 2 →+* ZMod 2 => f x) (RingHom.ext_zmod σ.toRingHom (RingHom.id _))
  refine ⟨g, ε, hε, ?_⟩
  rw [hβ, hσ, ← hgA]
  have h1 : slFieldAut (Fin n) (ZMod 2) (RingEquiv.refl (ZMod 2)) = 1 := by
    have := map_one (slFieldAut (Fin n) (ZMod 2))
    exact this
  rw [h1, mul_one]

theorem mem_innK_congr {K X : Type*} [Group K] [Group X] (e : K ≃* X) (a : MulAut K) :
    a ∈ innK K ↔ MulAut.congr e a ∈ innK X := by
  have hinn : ∀ k : K, MulAut.congr e (MulAut.conj k) = MulAut.conj (e k) := by
    intro k
    ext x
    simp [MulAut.congr_apply, MulAut.conj_apply]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨e k, (hinn k).symm⟩
  · rintro ⟨x, hx⟩
    refine ⟨e.symm x, ?_⟩
    apply (MulAut.congr e).injective
    rw [hinn, MulEquiv.apply_symm_apply, hx]

theorem sup_centralizer_of_pow_seven {G : Type} [Group G] {L : Subgroup G} {n : ℕ} (hn : 3 ≤ n)
    (e : ↥L ≃* SpecialLinearGroup (Fin n) (ZMod 2)) {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) (k : ℕ) (hk : orderOf x = 7 ^ k) :
    x ∈ L ⊔ Subgroup.centralizer (L : Set G) := by
  rw [mem_sup_centralizer_iff hx, mem_innK_congr e]
  set ρ : MulAut ↥L := L.normalizerMonoidHom ⟨x, hx⟩ with hρ
  set α : MulAut (SpecialLinearGroup (Fin n) (ZMod 2)) := MulAut.congr e ρ with hα
  have hρk : ρ ^ (7 ^ k) = 1 := by
    rw [← hk, hρ, ← map_pow]
    have : (⟨x, hx⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ orderOf x = 1 := by
      apply Subtype.ext
      simp
    rw [this, map_one]
  have hαk : α ^ (7 ^ k) = 1 := by
    rw [hα, ← map_pow, hρk, map_one]
  obtain ⟨g, ε, hε, hαg⟩ := aut_sl_zmod_two hn α
  set δ : MulAut (SpecialLinearGroup (Fin n) (ZMod 2)) := slGraphAut n (ZMod 2) with hδ
  have hδ2 : δ * δ = 1 := slGraph_mul_slGraph
  let q : MulAut (SpecialLinearGroup (Fin n) (ZMod 2)) →*
      MulAut (SpecialLinearGroup (Fin n) (ZMod 2)) ⧸ innK (SpecialLinearGroup (Fin n) (ZMod 2)) :=
    QuotientGroup.mk' _
  have hqg : q (MulAut.conj g) = 1 := (QuotientGroup.eq_one_iff _).2 ⟨g, rfl⟩
  have hq2 : q δ ^ 2 = 1 := by
    rw [← map_pow, pow_two, hδ2, map_one]
  have hqα : q α = q δ ^ ε := by
    rw [hαg, map_mul, hqg, one_mul, map_pow]
  have hqk : q α ^ (7 ^ k) = 1 := by rw [← map_pow, hαk, map_one]
  have hodd : Odd (7 ^ k) := Odd.pow (by decide)
  obtain ⟨j, hj⟩ := hodd
  have hq1 : q α = 1 := by
    interval_cases ε
    · rw [hqα, pow_zero]
    · rw [hqα, pow_one] at hqk ⊢
      rw [hj, pow_succ, pow_mul, hq2, one_pow, one_mul] at hqk
      exact hqk
  exact (QuotientGroup.eq_one_iff _).1 hq1

end CFSG.RankThree.PartOne.TAIL

module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellNatContract

public section

namespace CFSG.Quasithin

open Subgroup CFSG CFSG.QuasithinUnique.Setup.Campbell
open scoped commutatorElement

section AlgTwo

variable {F : Type*} [Field F] [Fintype F]

theorem eq_zero_or_one_of_card_eq_two (h : Fintype.card F = 2) (c : F) : c = 0 ∨ c = 1 := by
  classical
  by_contra hc
  push Not at hc
  have hcard : ({0, 1, c} : Finset F).card = 3 := by
    rw [Finset.card_eq_three]
    exact ⟨0, 1, c, zero_ne_one, hc.1.symm, hc.2.symm, rfl⟩
  have := Finset.card_le_univ ({0, 1, c} : Finset F)
  omega

theorem exists_sl2_action {Γ W : Type*} [Group Γ] [Group W] (act : Γ →* MulAut W)
    (β : W →* Multiplicative (Fin 2 → F)) (hβ : Function.Surjective β)
    (hF : Fintype.card F = 2)
    (hker : ∀ g u v, β u = β v → β (act g u) = β (act g v)) :
    ∃ ρ : Γ →* Matrix.SpecialLinearGroup (Fin 2) F,
      ∀ g u, Multiplicative.toAdd (β (act g u)) =
        (ρ g : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u)) := by
  classical
  let P : Γ → (Fin 2 → F) → (Fin 2 → F) := fun g x =>
    Multiplicative.toAdd (β (act g (Function.surjInv hβ (Multiplicative.ofAdd x))))
  have hP : ∀ g u, P g (Multiplicative.toAdd (β u)) = Multiplicative.toAdd (β (act g u)) := by
    intro g u
    have h2 : β (Function.surjInv hβ (Multiplicative.ofAdd (Multiplicative.toAdd (β u)))) =
        β u := Function.surjInv_eq hβ _
    show Multiplicative.toAdd (β (act g (Function.surjInv hβ
      (Multiplicative.ofAdd (Multiplicative.toAdd (β u)))))) = _
    rw [hker g _ u h2]
  have hex : ∀ x : Fin 2 → F, ∃ u, Multiplicative.toAdd (β u) = x := fun x => by
    obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd x)
    exact ⟨u, by rw [hu]; rfl⟩
  have hPadd : ∀ g x y, P g (x + y) = P g x + P g y := by
    intro g x y
    obtain ⟨u, rfl⟩ := hex x
    obtain ⟨v, rfl⟩ := hex y
    have e3 : Multiplicative.toAdd (β u) + Multiplicative.toAdd (β v) =
        Multiplicative.toAdd (β (u * v)) := by rw [map_mul, toAdd_mul]
    rw [e3, hP, hP, hP, map_mul, map_mul, toAdd_mul]
  have hP0 : ∀ g, P g 0 = 0 := by
    intro g
    have := hPadd g 0 0
    simpa using this
  have hPsmul : ∀ g (c : F) x, P g (c • x) = c • P g x := by
    intro g c x
    rcases eq_zero_or_one_of_card_eq_two hF c with rfl | rfl
    · simp [hP0]
    · simp
  have hPmul : ∀ g h x, P (g * h) x = P g (P h x) := by
    intro g h x
    obtain ⟨u, rfl⟩ := hex x
    rw [hP h u, hP g (act h u), hP (g * h) u, map_mul]
    rfl
  have hP1 : ∀ x, P 1 x = x := by
    intro x
    obtain ⟨u, rfl⟩ := hex x
    rw [hP, map_one]
    rfl
  let Pl : Γ → (Fin 2 → F) →ₗ[F] (Fin 2 → F) := fun g =>
    { toFun := P g
      map_add' := hPadd g
      map_smul' := fun c x => hPsmul g c x }
  let M : Γ → Matrix (Fin 2) (Fin 2) F := fun g => LinearMap.toMatrix' (Pl g)
  have hMv : ∀ g x, (M g).mulVec x = P g x := fun g x => LinearMap.toMatrix'_mulVec (Pl g) x
  have hMmul : ∀ g h, M (g * h) = M g * M h := by
    intro g h
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix',
      Matrix.toLin'_toMatrix']
    exact LinearMap.ext fun x => hPmul g h x
  have hM1 : M 1 = 1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_toMatrix', Matrix.toLin'_one]
    exact LinearMap.ext fun x => hP1 x
  have hdet : ∀ g, (M g).det = 1 := by
    intro g
    have h1 : (M g).det * (M g⁻¹).det = 1 := by
      rw [← Matrix.det_mul, ← hMmul, mul_inv_cancel, hM1, Matrix.det_one]
    rcases eq_zero_or_one_of_card_eq_two hF (M g).det with h0 | h0
    · rw [h0, zero_mul] at h1
      exact absurd h1 zero_ne_one
    · exact h0
  refine ⟨{ toFun := fun g => ⟨M g, hdet g⟩
            map_one' := Subtype.ext hM1
            map_mul' := fun g h => Subtype.ext (hMmul g h) }, ?_⟩
  intro g u
  show _ = (M g).mulVec _
  rw [hMv, hP]

end AlgTwo

section CommutatorSL

variable {F : Type*} [Field F] [Fintype F]

theorem exists_commutator_eq_zpowers (hF : Fintype.card F = 2) :
    ∃ t : Matrix.SpecialLinearGroup (Fin 2) F,
      orderOf t = 3 ∧ commutator (Matrix.SpecialLinearGroup (Fin 2) F) = Subgroup.zpowers t := by
  classical
  have : Finite F := Finite.of_fintype F
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = 6 := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, Nat.card_eq_fintype_card, hF]
    norm_num
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 3
    (show 3 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) by rw [hSL]; norm_num)
  have hz3 : Nat.card (Subgroup.zpowers t) = 3 := by rw [Nat.card_zpowers, ht]
  have hidx : (Subgroup.zpowers t).index = 2 := by
    have := Subgroup.card_mul_index (Subgroup.zpowers t)
    rw [hz3, hSL] at this
    omega
  have hnormal : (Subgroup.zpowers t).Normal := Subgroup.normal_of_index_eq_two hidx
  have hle : commutator (Matrix.SpecialLinearGroup (Fin 2) F) ≤ Subgroup.zpowers t := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : IsCyclic (Matrix.SpecialLinearGroup (Fin 2) F ⧸ Subgroup.zpowers t) :=
      isCyclic_of_prime_card hidx
    have hc : QuotientGroup.mk' (Subgroup.zpowers t) x * QuotientGroup.mk' (Subgroup.zpowers t) y =
        QuotientGroup.mk' (Subgroup.zpowers t) y * QuotientGroup.mk' (Subgroup.zpowers t) x :=
      (IsCyclic.commGroup (α := Matrix.SpecialLinearGroup (Fin 2) F ⧸ Subgroup.zpowers t)).mul_comm
        _ _
    have h1 : QuotientGroup.mk' (Subgroup.zpowers t) ⁅x, y⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hc
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hne : commutator (Matrix.SpecialLinearGroup (Fin 2) F) ≠ ⊥ := by
    intro hbot
    have hcomm : ∀ a b : Matrix.SpecialLinearGroup (Fin 2) F, a * b = b * a := by
      intro a b
      have h1 : ⁅a, b⁆ ∈ commutator (Matrix.SpecialLinearGroup (Fin 2) F) :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [hbot, Subgroup.mem_bot] at h1
      exact (commutatorElement_eq_one_iff_mul_comm.mp h1)
    exact not_commutative_sl2 hcomm
  have hdvd : Nat.card (commutator (Matrix.SpecialLinearGroup (Fin 2) F)) ∣ 3 :=
    hz3 ▸ Subgroup.card_dvd_of_le hle
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact absurd (Subgroup.eq_bot_of_card_eq _ h1) hne
  · exact ⟨t, ht, (Subgroup.eq_of_le_of_card_ge hle (by rw [h3, hz3])).symm.symm⟩

end CommutatorSL

end CFSG.Quasithin

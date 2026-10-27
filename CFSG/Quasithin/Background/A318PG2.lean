module

public import CFSG.Quasithin.Background.A318PCRank
public import CFSG.Quasithin.Background.A318PRW
public import CFSG.Quasithin.Background.A318PInn
public import CFSG.RankThree.PartTwo.KFacts.AutG2

public section

namespace CFSG.Quasithin

namespace A318P

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open CFSG.SectionRank
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.PartTwo.KFacts

section G2Witness

variable {K : Type} [Field K]

theorem rankOneZ_facts_g2
    [CharP K 2] (i : Fin (Tag.rank .G2)) :
    rankOneZ (τ := .G2) (K := K) i ^ 3 = 1 ∧
      ¬ Commute (rankOneZ (K := K) i) ((rootOperatorFamily .G2).eltElement (simpleRoot .G2 i) 1) ∧
      ¬ Commute (rankOneZ (K := K) i ^ 2)
        ((rootOperatorFamily .G2).eltElement (simpleRoot .G2 i) 1) := by
  have h2 : (1 : K) + 1 = 0 := by rw [one_add_one_eq_two]; exact CharP.cast_eq_zero K 2
  obtain ⟨φ, hφ, hu, hl⟩ := g2_exists_sl2_hom (K := K) i
  have hz : rankOneZ (τ := .G2) (K := K) i = φ (sl2Upper 1 * sl2Lower 1) := by
    rw [map_mul, hu, hl]
    rfl
  rw [hz, ← hu]
  refine ⟨by rw [← map_pow, sl2_ul_pow_three h2, map_one], fun h => ?_, fun h => ?_⟩
  · exact sl2_ul_not_commute h2 (by
      have := h.eq
      rw [← map_mul, ← map_mul] at this
      exact hφ this)
  · exact sl2_ul_sq_not_commute h2 (by
      have := h.eq
      rw [← map_pow, ← map_mul, ← map_mul] at this
      exact hφ this)

end G2Witness



@[expose] def witnessG2 : RootWitness .G2 2 where
  word := ![([] : List (Fin 2)), ([1, 0] : List (Fin 2))]
  simple := ![(0 : Fin 2), (1 : Fin 2)]

theorem witnessG2_check : witnessG2.check = true := by decide +kernel

theorem witnessG2_orthoCheck : witnessG2.orthoCheck = true := by decide +kernel

section G2Nine

variable {K : Type} [Field K]

theorem g2FieldHom_elemZ
    (σ : K ≃+* K) {n : ℕ} (W : RootWitness .G2 n) (i : Fin n) :
    g2FieldHom K σ (W.elemZ K i) = W.elemZ K i := by
  apply Subtype.ext
  rw [coe_g2FieldHom]
  have hN : Units.map (entrywiseHom σ.toRingHom)
      ((nrep .G2 K ((coxeterSystem .G2).wordProd (W.word i)) : adjointGroup .G2 K) :
        ModGL .G2 K) =
      ((nrep .G2 K ((coxeterSystem .G2).wordProd (W.word i)) : adjointGroup .G2 K) :
        ModGL .G2 K) :=
    entrywise_canonicalRep σ _
  have hX : Units.map (entrywiseHom σ.toRingHom)
      (((rootOperatorFamily .G2).eltElement (simpleRoot .G2 (W.simple i)) 1 :
        adjointGroup .G2 K) : ModGL .G2 K) =
      (((rootOperatorFamily .G2).eltElement (simpleRoot .G2 (W.simple i)) 1 :
        adjointGroup .G2 K) : ModGL .G2 K) := by
    rw [eltElement_simpleRoot]
    exact (units_map_entrywiseHom_xUnit σ.toRingHom (W.simple i) 1).trans (by rw [map_one]; rfl)
  have hY : Units.map (entrywiseHom σ.toRingHom)
      (((rootOperatorFamily .G2).eltElement (-simpleRoot .G2 (W.simple i)) 1 :
        adjointGroup .G2 K) : ModGL .G2 K) =
      (((rootOperatorFamily .G2).eltElement (-simpleRoot .G2 (W.simple i)) 1 :
        adjointGroup .G2 K) : ModGL .G2 K) := by
    have : (rootOperatorFamily .G2).eltElement (-simpleRoot .G2 (W.simple i)) (1 : K) =
        yElement (W.simple i) 1 := Subtype.ext ((rootOperatorFamily .G2).eltUnit_neg_simple _ _)
    rw [this]
    exact (units_map_entrywiseHom_yUnit σ.toRingHom (W.simple i) 1).trans (by rw [map_one]; rfl)
  simp only [RootWitness.elemZ, rankOneZ, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv,
    hN, hX, hY]

theorem exists_nine_g2
    [CharP K 2] (σ : K ≃+* K) :
    ∃ E : Subgroup (adjointGroup .G2 K), Nat.card E = 9 ∧ IsElemAbelian 3 E ∧
      ∀ y ∈ E, g2FieldHom K σ y = y := by
  obtain ⟨hZ, hZA, hZZ, -⟩ := charTwo_facts_of_rankOne witnessG2 witnessG2_check
    witnessG2_orthoCheck (K := K) (fun i => rankOneZ_facts_g2 (witnessG2.simple i))
  obtain ⟨E, hEH, hEel, hEcard⟩ := exists_elemAbelian_three (n := 2)
    (fun i => witnessG2.elemZ K i) (fun i => witnessG2.elemA K i) (fun i => (hZ i).1)
    (fun i => (hZ i).2.1) (fun i => (hZ i).2.2) hZA hZZ
    (H := ((g2FieldHom K σ).toMonoidHom.eqLocus (MonoidHom.id _)))
    (fun i => g2FieldHom_elemZ σ witnessG2 i)
  exact ⟨E, by rw [hEcard]; norm_num, hEel, fun y hy => hEH hy⟩

end G2Nine

section G2Frame

open CFSG.ComponentClassification.OuterAutomorphisms (inner)

@[expose] noncomputable def innFrameG2
    (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK4 : 4 ≤ Nat.card K) : InnFrame ↥(adjointGroup .G2 K) (K ≃+* K) where
  fld := g2FieldHom K
  fld_inter := fun c hc =>
    (g2_automorphism_normal_form (by rw [ringChar.eq K 2]; norm_num) hK4).2 c hc
  three_mem := fun α _ _ => by
    obtain ⟨g, σ, h⟩ := (g2_automorphism_normal_form (by rw [ringChar.eq K 2]; norm_num) hK4).1 α
    exact ⟨MulAut.conj g, ⟨g, rfl⟩, σ, h⟩
  nine := fun c _ => exists_nine_g2 c

end G2Frame

section G2Core

variable {X : Type} [Group X] [Finite X] {S : Subgroup X} [S.Normal]

theorem g2_threeElements
    (hC : ∀ c : X, (∀ s ∈ S, c * s = s * c) → c = 1) {f : ℕ} (hf : 2 ≤ f)
    (hS : ChevalleyExceptionalModel ↥S .G2 2 f)
    (hX : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2) :
    ∀ x : X, (∃ k : ℕ, orderOf x = 3 ^ k) → x ∈ S := by
  classical
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hS
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K 2 := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card]; exact hKcard)
  have hK4 : 4 ≤ Nat.card K := by
    rw [hKcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  let ψ : ↥S ≃* ↥(adjointGroup .G2 K) :=
    e.trans ((QuotientGroup.quotientMulEquivOfEq
      (center_adjointGroup_eq_bot (τ := .G2) (K := K))).trans QuotientGroup.quotientBot)
  exact innFrame_core hC ((innFrameG2 K hK4).ofMulEquiv ψ) hX

end G2Core

end A318P

end CFSG.Quasithin

module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitF4Three
public import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicFourNonregular
public import CFSG.RankThree.Chevalley.SteinbergCAF4CyclotomicFourActors
public import CFSG.RankThree.Chevalley.SteinbergCAF4NonregularSp4

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.Chevalley.F4Weyl CFSG.RankThree.E6

namespace F4Nonsplit

theorem pow_four_sub_one_eq (q : ℕ) (hq : 1 ≤ q) : q ^ 4 - 1 = (q ^ 2 + 1) * (q ^ 2 - 1) := by
  zify [Nat.one_le_pow 2 q hq, Nat.one_le_pow 4 q hq]
  ring

theorem card_eq_of_alternating {M : Type*} [Group M] {R P : Subgroup M} (hle : R ≤ P)
    (e : P ≃* Equiv.Perm (Fin 6)) (he : ∀ z : P, (z : M) ∈ R ↔ e z ∈ alternatingGroup (Fin 6)) :
    Nat.card R = 360 := by
  have hcard : Nat.card R = Nat.card (alternatingGroup (Fin 6)) := Nat.card_congr
    { toFun := fun r => ⟨e ⟨r, hle r.2⟩, (he ⟨r, hle r.2⟩).1 r.2⟩
      invFun := fun s => ⟨(e.symm s : M), (he (e.symm s)).2 (by
        rw [e.apply_symm_apply]
        exact s.2)⟩
      left_inv := fun r => Subtype.ext (by
        change ((e.symm (e ⟨r, hle r.2⟩) : P) : M) = r
        rw [e.symm_apply_apply])
      right_inv := fun s => Subtype.ext (by
        change e ⟨(e.symm s : M), _⟩ = s
        rw [Subtype.coe_eta, e.apply_symm_apply]) }
  rw [hcard, nat_card_alternatingGroup, Nat.card_fin]
  decide


theorem dvd_card_of_isComponentOf_phiFour {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpd : p ∣ Nat.card K ^ 2 + 1)
    {x₁ : adjointGroup .F4 K} (hx₁p : orderOf x₁ = p) {X : Subgroup (adjointGroup .F4 K)}
    (hX : IsComponentOf X (Subgroup.centralizer {x₁})) : p ∣ Nat.card X := by
  classical
  obtain ⟨f, hf, hK⟩ := exists_card_eq_two_pow K
  obtain ⟨F, hF⟩ := exists_frobenius_pow K
  set Ω := AlgebraicClosure K with hΩ
  obtain ⟨g, hg, hgn, x, hx, hxp, hx₁⟩ := exists_lang_coordinate K Ω F hF hp hp3 hpd hx₁p
  obtain ⟨-, hCA⟩ := F4_cyclotomic_four_torus_and_regular_prime_centralizers K Ω F hF _ rfl
  obtain ⟨-, -, -, hprime, -⟩ := hCA g hg hgn _ _ _ rfl rfl rfl
  obtain ⟨-, -, -, hdich⟩ := hprime p hp hp3 hpd
  obtain ⟨hcases, -, hreg⟩ := hdich x hx hxp _ rfl
  by_cases hne : {α | IsRoot .F4 α ∧ torusRootChar x α = 1}.Nonempty
  swap
  ·
    have hT := hreg (Set.not_nonempty_iff_eq_empty.1 hne)
    refine absurd hX (not_isComponentOf_of_commute
      (mul_comm_of_conj_mem_torusGroup K Ω g _ fun y hy => ?_))
    have h1 := conj_inv_baseChange_mem K Ω hx₁ hy
    rw [hT] at h1
    exact h1.1
  obtain ⟨u, ε, hε, hu, huw⟩ := hcases.resolve_left hne.ne_empty
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K₄, hK₄⟩ := EvenF4Actors.exists_intermediateField_finrank K Ω 4
  obtain ⟨-, Z₀, P, -, -, ⟨a, -, hPmem, -⟩, -, -, h4, h2, -, -, -, x₀, hx₀, hCx, -⟩ :=
    even_F4_cyclotomic_four_nonregular_derived_centralizer hf K hK Ω F hF hp hp3 K₄ hK₄ _ g rfl
      hg hgn _ _ rfl rfl x hx hxp u ε hε hu huw _ _ rfl rfl _ _ _ rfl rfl rfl
  have hx₀₁ : x₀ = x₁ := Subtype.ext (baseChangeGL_injective (τ := .F4)
    (algebraMap K Ω) (hx₀.trans hx₁.symm))
  subst hx₀₁
  have hι : Function.Injective ((baseChangeGL (algebraMap K Ω)).comp
      (adjointGroup .F4 K).subtype) :=
    (baseChangeGL_injective (τ := .F4) (algebraMap K Ω)).comp Subtype.val_injective
  rcases (show f = 1 ∨ 2 ≤ f by omega) with rfl | hf2
  ·
    have hq : Nat.card K = 2 := by rw [hK, pow_one]
    obtain ⟨hRP, ⟨e, he⟩, hsimp, hperf, hnc⟩ := h2 hq
    have hp5 : p = 5 := by
      rw [hq] at hpd
      exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 hpd
    refine dvd_card_of_isComponentOf_of_map_eq hι (MulAut.conj _).injective hCx
      (isQuasisimple_of_isSimpleGroup hsimp hperf hnc) ?_ hX
    rw [card_eq_of_alternating (hRP ▸ F4Nonsplit.commutator_le_self P) e he, hp5]
    decide
  ·
    have hq4 : 4 ≤ Nat.card K := by
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
    obtain ⟨hRP, -, hsimp, hperf, hnc⟩ := h4 hq4
    refine dvd_card_of_isComponentOf_of_map_eq hι (MulAut.conj _).injective hCx
      (isQuasisimple_of_isSimpleGroup hsimp hperf hnc) ?_ hX
    have hPeq : P = ((subsystemGroup .F4 K {1, 2}).map (baseChangeGL (algebraMap K Ω))).map
        (MulAut.conj (baseChangeGL (algebraMap K₄ Ω) a)).toMonoidHom := by
      ext z
      rw [hPmem z]
      constructor
      · rintro ⟨y', hy', rfl⟩
        exact ⟨_, ⟨y', hy', rfl⟩, rfl⟩
      · rintro ⟨_, ⟨y', hy', rfl⟩, rfl⟩
        exact ⟨y', hy', rfl⟩
    obtain ⟨-, -, hbij, -⟩ := F4_native_B2_faithful_Sp4_all_characteristics K
    rw [hRP, hPeq, Subgroup.card_map_of_injective (MulAut.conj _).injective,
      Subgroup.card_map_of_injective (baseChangeGL_injective (τ := .F4) _),
      Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_congr (f4SpEquiv K).toEquiv,
      CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp (K := K) 2]
    have h1 : 1 ≤ Nat.card K := by omega
    have hmem : 2 ∈ Finset.Icc 1 2 := by decide
    refine Dvd.dvd.mul_left (Dvd.dvd.trans ?_
      (Finset.dvd_prod_of_mem (fun j => Nat.card K ^ (2 * j) - 1) hmem)) _
    change p ∣ Nat.card K ^ 4 - 1
    rw [pow_four_sub_one_eq _ h1]
    exact Dvd.dvd.mul_right hpd _

end F4Nonsplit

end CFSG.StandardType

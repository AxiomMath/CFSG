module

public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxDefs
public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxL3Pairs
import CFSG.LieType.SteinbergBROddLinearThreeParabolic
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityAB
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityTorusLayerAux
public import CFSG.RankThree.PartTwo.Sec21.Item219LieProofD4U
public import Certificates.Data.ExceptionalSL3

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartTwo.Sec19 CFSG.RankThree.PartTwo.Sec11
open scoped commutatorElement
open CFSG.RankThree.PartTwo.Sec21.Item219LieProof (d4_threeA_model d4_threeA_model_unitary)

namespace CFSG.RankThree.PartTwo.Sec4.E27

section Conj

variable {G : Type*} [Group G]

theorem layer_mem_conj_inv (h x u : G)
    (hu : u ∈ ⁅Subgroup.centralizer ({h * x * h⁻¹} : Set G),
      Subgroup.centralizer ({h * x * h⁻¹} : Set G)⁆) :
    h⁻¹ * u * h ∈ ⁅Subgroup.centralizer ({x} : Set G), Subgroup.centralizer ({x} : Set G)⁆ := by
  have := TorusLayerAux.conj_mem_commutator h⁻¹ (h * x * h⁻¹) u hu
  have e : h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x := by group
  rw [e, inv_inv] at this
  exact this

theorem heisIn_of_conj (h x : G)
    (H : HeisIn ⁅Subgroup.centralizer ({h * x * h⁻¹} : Set G),
      Subgroup.centralizer ({h * x * h⁻¹} : Set G)⁆) :
    HeisIn ⁅Subgroup.centralizer ({x} : Set G), Subgroup.centralizer ({x} : Set G)⁆ := by
  obtain ⟨y, hy, p, hp, u, hu, hu1, hu3, huc, hup⟩ := H
  refine ⟨h⁻¹ * y * h, layer_mem_conj_inv h x y hy, h⁻¹ * p * h, layer_mem_conj_inv h x p hp,
    h⁻¹ * u * h, layer_mem_conj_inv h x u hu, ?_, ?_, ?_, ?_⟩
  · intro h1
    apply hu1
    have : u = h * (h⁻¹ * u * h) * h⁻¹ := by group
    rw [this, h1]
    group
  · have := TorusLayerAux.pow_conj_eq h⁻¹ u 3
    rw [inv_inv] at this
    rw [this, hu3]
    group
  · intro d hd
    have hd' := TorusLayerAux.conj_mem_commutator h x d hd
    have key := huc _ hd'
    calc h⁻¹ * u * h * d = h⁻¹ * (u * (h * d * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * d * h⁻¹) * u) * h := by rw [key]
      _ = d * (h⁻¹ * u * h) := by group
  · calc h⁻¹ * p * h * (h⁻¹ * y * h) * (h⁻¹ * p * h)⁻¹ * (h⁻¹ * y * h)⁻¹
        = h⁻¹ * (p * y * p⁻¹ * y⁻¹) * h := by group
      _ = h⁻¹ * u * h := by rw [hup]

theorem cubeCenter_of_conj (h x : G)
    (H : CubeCenter ⁅Subgroup.centralizer ({h * x * h⁻¹} : Set G),
      Subgroup.centralizer ({h * x * h⁻¹} : Set G)⁆) :
    CubeCenter ⁅Subgroup.centralizer ({x} : Set G), Subgroup.centralizer ({x} : Set G)⁆ := by
  intro t ht htc
  have ht' := TorusLayerAux.conj_mem_commutator h x t ht
  have hc : ∀ d ∈ ⁅Subgroup.centralizer ({h * x * h⁻¹} : Set G),
      Subgroup.centralizer ({h * x * h⁻¹} : Set G)⁆, (h * t * h⁻¹) * d = d * (h * t * h⁻¹) := by
    intro d hd
    have hd' := layer_mem_conj_inv h x d hd
    have key := htc _ hd'
    calc h * t * h⁻¹ * d = h * (t * (h⁻¹ * d * h)) * h⁻¹ := by group
      _ = h * ((h⁻¹ * d * h) * t) * h⁻¹ := by rw [key]
      _ = d * (h * t * h⁻¹) := by group
  have h3 := H _ ht' hc
  rw [TorusLayerAux.pow_conj_eq] at h3
  have : h * t ^ 3 * h⁻¹ = 1 := h3
  calc t ^ 3 = h⁻¹ * (h * t ^ 3 * h⁻¹) * h := by group
    _ = 1 := by rw [this]; group

theorem card_layer_conj (h x : G) :
    Nat.card ↥⁅Subgroup.centralizer ({h * x * h⁻¹} : Set G),
      Subgroup.centralizer ({h * x * h⁻¹} : Set G)⁆ =
      Nat.card ↥⁅Subgroup.centralizer ({x} : Set G), Subgroup.centralizer ({x} : Set G)⁆ := by
  symm
  refine Nat.card_congr ⟨fun u => ⟨h * u * h⁻¹, TorusLayerAux.conj_mem_commutator h x u u.2⟩,
    fun v => ⟨h⁻¹ * v * h, layer_mem_conj_inv h x v v.2⟩, ?_, ?_⟩
  · intro u
    apply Subtype.ext
    show h⁻¹ * (h * u * h⁻¹) * h = u
    group
  · intro v
    apply Subtype.ext
    show h * (h⁻¹ * v * h) * h⁻¹ = v
    group

end Conj

section Model


variable {n : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}

theorem layer_facts_even (P : D4Par n X σ) (hn : 2 ≤ n) (hev : Even n) {x : C0 σ}
    (hx : IsClassX σ x) : HeisIn (layerSub σ x) ∧ CubeCenter (layerSub σ x) := by
  unfold IsClassX at hx
  obtain ⟨hx3, hx1, g, hg⟩ := hx
  have hy3 : (g * x * g⁻¹) ^ 3 = 1 := TorusLayerAux.conj_pow_eq_one hx3
  have hy1 : g * x * g⁻¹ ≠ 1 := TorusLayerAux.conj_ne_one hx1
  have hf : 1 ≤ n := by omega
  have hK : Nat.card X = (2 ^ n) ^ 3 := P.card
  have hσ : ∀ c : X, σ c = c ^ (2 ^ n) := P.frob
  obtain ⟨m, hm⟩ := hev
  have hq1 : 2 ^ n % 3 = 1 := by
    rw [hm, ← two_mul]
    exact TorusLayerAux.two_pow_mod_three_even m
  obtain ⟨c, R, hcR, hRc, hcomm, hq, F, hFi, hFf, hFcard, ⟨e⟩⟩ :=
    d4_threeA_model Nat.prime_two hf (by norm_num) hq1 hK hσ hg hy3 hy1
  have hD : layerSub σ (c * (g * x * g⁻¹) * c⁻¹) = R :=
    TorusLayerAux.commutator_centralizer_eq _ R hq.1 hRc hcomm
  let e' : layerSub σ (c * (g * x * g⁻¹) * c⁻¹) ≃* Matrix.SpecialLinearGroup (Fin 3) F :=
    (MulEquiv.subgroupCongr hD).trans e
  have h3F : 3 ∣ Nat.card Fˣ := by
    rw [Nat.card_units, hFcard]
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 h3F
  have hω3 : (ω : F) ^ 3 = 1 := by
    have := pow_orderOf_eq_one ω
    rw [hω] at this
    exact congrArg Units.val this
  have hω1 : (ω : F) ≠ 1 := by
    intro h1
    have : ω = 1 := Units.ext h1
    rw [this, orderOf_one] at hω
    omega
  have hH : HeisIn (layerSub σ (c * (g * x * g⁻¹) * c⁻¹)) :=
    heisIn_of_mulEquiv _ e' (heisPair_SL3 hω3 hω1)
  have hC : CubeCenter (layerSub σ (c * (g * x * g⁻¹) * c⁻¹)) := by
    intro t ht htc
    have hmem : e' ⟨t, ht⟩ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) := by
      rw [Subgroup.mem_center_iff]
      intro s
      obtain ⟨s', rfl⟩ := e'.surjective s
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (htc _ s'.2).symm
    obtain ⟨r, hr3, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hmem
    have h3 : (e' ⟨t, ht⟩) ^ 3 = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_pow, ← hr, Matrix.SpecialLinearGroup.coe_one,
        ← map_pow]
      rw [Fintype.card_fin] at hr3
      rw [hr3, map_one]
    have : (⟨t, ht⟩ : layerSub σ (c * (g * x * g⁻¹) * c⁻¹)) ^ 3 = 1 := by
      apply e'.injective
      rw [map_pow, h3, map_one]
    exact congrArg Subtype.val this
  have hwh : c * (g * x * g⁻¹) * c⁻¹ = (c * g) * x * (c * g)⁻¹ := by group
  rw [hwh] at hH hC
  exact ⟨heisIn_of_conj _ _ hH, cubeCenter_of_conj _ _ hC⟩

theorem layer_facts_odd (P : D4Par n X σ) (hn : 2 ≤ n) (hodd : Odd n) {x : C0 σ}
    (hx : IsClassX σ x) : HeisIn (layerSub σ x) ∧ CubeCenter (layerSub σ x) := by
  unfold IsClassX at hx
  obtain ⟨hx3, hx1, g, hg⟩ := hx
  have hy3 : (g * x * g⁻¹) ^ 3 = 1 := TorusLayerAux.conj_pow_eq_one hx3
  have hy1 : g * x * g⁻¹ ≠ 1 := TorusLayerAux.conj_ne_one hx1
  have hf : 1 ≤ n := by omega
  have hK : Nat.card X = (2 ^ n) ^ 3 := P.card
  have hσ : ∀ c : X, σ c = c ^ (2 ^ n) := P.frob
  obtain ⟨m, hm⟩ := hodd
  have hq1 : 2 ^ n % 3 = 2 := by
    rw [hm]
    exact TorusLayerAux.two_pow_mod_three_odd m
  have h2n : 2 < 2 ^ n := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)
  obtain ⟨c, R, hcR, hRc, hcomm, hq, U, hU, e, hcen⟩ :=
    d4_threeA_model_unitary Nat.prime_two hf (by norm_num) hq1 h2n hK hσ hg hy3 hy1
  have hD : layerSub σ (c * (g * x * g⁻¹) * c⁻¹) = R :=
    TorusLayerAux.commutator_centralizer_eq _ R hq.1 hRc hcomm
  let e' : layerSub σ (c * (g * x * g⁻¹) * c⁻¹) ≃* U := (MulEquiv.subgroupCongr hD).trans e
  have hcharX : CharP X 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (k := n * 3) (by omega) (by rw [hK, pow_mul])
  have hcharL : CharP (AlgebraicClosure X) 2 :=
    charP_of_injective_algebraMap (algebraMap X (AlgebraicClosure X)).injective 2
  have h3L : (3 : AlgebraicClosure X) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : AlgebraicClosure X) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (AlgebraicClosure X) 2] at h'
    omega
  obtain ⟨ζ, hζ⟩ := CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof.exists_units_orderOf_three
    (AlgebraicClosure X) h3L
  have hζ3 : (ζ : AlgebraicClosure X) ^ 3 = 1 := by
    have := pow_orderOf_eq_one ζ
    rw [hζ] at this
    exact congrArg Units.val this
  have hζ1 : (ζ : AlgebraicClosure X) ≠ 1 := by
    intro h1
    have : ζ = 1 := Units.ext h1
    rw [this, orderOf_one] at hζ
    omega
  have hζq : (ζ : AlgebraicClosure X) ^ (2 ^ n + 1) = 1 := by
    have h3dvd : 3 ∣ 2 ^ n + 1 := by omega
    obtain ⟨k, hk⟩ := h3dvd
    rw [hk, pow_mul, hζ3, one_pow]
  have hH : HeisIn (layerSub σ (c * (g * x * g⁻¹) * c⁻¹)) :=
    heisIn_of_mulEquiv _ e' (heisPair_unitary (q := 2 ^ n) Nat.one_le_two_pow hζ3 hζ1 hζq U hU)
  have hC : CubeCenter (layerSub σ (c * (g * x * g⁻¹) * c⁻¹)) := by
    intro t ht htc
    have htR : t ∈ R := hD ▸ ht
    set t' : R := ⟨t, htR⟩ with ht'
    have hcent : t' ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro d
      exact Subtype.ext (htc (d : C0 σ) (hD ▸ d.2)).symm
    obtain ⟨μ, hμ⟩ := (hcen t').1 hcent
    have hmem : ((e t' : U) : GL (Fin 3) (AlgebraicClosure X)) ∈
        CFSG.RankThree.Classical2.unitarySet (2 ^ n) 3 := by
      rw [← hU]
      exact (e t').2
    have hdet : (((e t' : U) : GL (Fin 3) (AlgebraicClosure X)) :
        Matrix (Fin 3) (Fin 3) (AlgebraicClosure X)).det = 1 := hmem.2.1
    have hμ3 : μ ^ 3 = 1 := by
      rw [hμ, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin] at hdet
      exact hdet
    have h3 : (e t') ^ 3 = 1 := by
      apply Subtype.ext
      apply Units.ext
      rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hμ, ← map_pow, hμ3, map_one]
      rfl
    have : t' ^ 3 = 1 := by
      apply e.injective
      rw [map_pow, h3, map_one]
    exact congrArg Subtype.val this
  have hwh : c * (g * x * g⁻¹) * c⁻¹ = (c * g) * x * (c * g)⁻¹ := by group
  rw [hwh] at hH hC
  exact ⟨heisIn_of_conj _ _ hH, cubeCenter_of_conj _ _ hC⟩

theorem layer_facts (P : D4Par n X σ) (hn : 2 ≤ n) {x : C0 σ} (hx : IsClassX σ x) :
    HeisIn (layerSub σ x) ∧ CubeCenter (layerSub σ x) := by
  rcases Nat.even_or_odd n with hev | hodd
  · exact layer_facts_even P hn hev hx
  · exact layer_facts_odd P hn hodd hx

theorem layer_card_even (P : D4Par n X σ) (hn : 2 ≤ n) (hev : Even n) {x : C0 σ}
    (hx : IsClassX σ x) :
    Nat.card (layerSub σ x) = (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) := by
  unfold IsClassX at hx
  obtain ⟨hx3, hx1, g, hg⟩ := hx
  have hy3 : (g * x * g⁻¹) ^ 3 = 1 := TorusLayerAux.conj_pow_eq_one hx3
  have hy1 : g * x * g⁻¹ ≠ 1 := TorusLayerAux.conj_ne_one hx1
  have hf : 1 ≤ n := by omega
  have hK : Nat.card X = (2 ^ n) ^ 3 := P.card
  have hσ : ∀ c : X, σ c = c ^ (2 ^ n) := P.frob
  obtain ⟨m, hm⟩ := hev
  have hq1 : 2 ^ n % 3 = 1 := by
    rw [hm, ← two_mul]
    exact TorusLayerAux.two_pow_mod_three_even m
  obtain ⟨c, R, hcR, hRc, hcomm, hq, F, hFi, hFf, hFcard, ⟨e⟩⟩ :=
    d4_threeA_model Nat.prime_two hf (by norm_num) hq1 hK hσ hg hy3 hy1
  have hD : layerSub σ (c * (g * x * g⁻¹) * c⁻¹) = R :=
    TorusLayerAux.commutator_centralizer_eq _ R hq.1 hRc hcomm
  let e' : layerSub σ (c * (g * x * g⁻¹) * c⁻¹) ≃* Matrix.SpecialLinearGroup (Fin 3) F :=
    (MulEquiv.subgroupCongr hD).trans e
  have hwh : c * (g * x * g⁻¹) * c⁻¹ = (c * g) * x * (c * g)⁻¹ := by group
  have h1 : Nat.card (layerSub σ ((c * g) * x * (c * g)⁻¹)) = Nat.card (layerSub σ x) :=
    card_layer_conj (c * g) x
  rw [hwh] at e'
  rw [← h1, Nat.card_congr e'.toEquiv, CFSG.LieType.SteinbergBR.BlockPar.card_SL_three', hFcard]

theorem layer_model_odd (P : D4Par n X σ) (hn : 2 ≤ n) (hodd : Odd n) {x : C0 σ}
    (hx : IsClassX σ x) :
    ∃ (h : C0 σ) (U : Subgroup (GL (Fin 3) (AlgebraicClosure X))),
      (U : Set (GL (Fin 3) (AlgebraicClosure X))) =
        CFSG.RankThree.Classical2.unitarySet (2 ^ n) 3 ∧
      Nonempty (layerSub σ (h * x * h⁻¹) ≃* U) := by
  unfold IsClassX at hx
  obtain ⟨hx3, hx1, g, hg⟩ := hx
  have hy3 : (g * x * g⁻¹) ^ 3 = 1 := TorusLayerAux.conj_pow_eq_one hx3
  have hy1 : g * x * g⁻¹ ≠ 1 := TorusLayerAux.conj_ne_one hx1
  have hf : 1 ≤ n := by omega
  have hK : Nat.card X = (2 ^ n) ^ 3 := P.card
  have hσ : ∀ c : X, σ c = c ^ (2 ^ n) := P.frob
  obtain ⟨m, hm⟩ := hodd
  have hq1 : 2 ^ n % 3 = 2 := by
    rw [hm]
    exact TorusLayerAux.two_pow_mod_three_odd m
  have h2n : 2 < 2 ^ n := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)
  obtain ⟨c, R, hcR, hRc, hcomm, hq, U, hU, e, hcen⟩ :=
    d4_threeA_model_unitary Nat.prime_two hf (by norm_num) hq1 h2n hK hσ hg hy3 hy1
  have hD : layerSub σ (c * (g * x * g⁻¹) * c⁻¹) = R :=
    TorusLayerAux.commutator_centralizer_eq _ R hq.1 hRc hcomm
  have hwh : c * (g * x * g⁻¹) * c⁻¹ = (c * g) * x * (c * g)⁻¹ := by group
  refine ⟨c * g, U, hU, ⟨?_⟩⟩
  rw [← hwh]
  exact (MulEquiv.subgroupCongr hD).trans e

end Model

end CFSG.RankThree.PartTwo.Sec4.E27

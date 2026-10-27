module

public import CFSG.LinearAlgebra.SL2MinimalFaithful
public import CFSG.Quasithin.Vol2.Ch11SecAKM1

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA.C10KH

open CFSG.Open CFSG.Blueprint CFSG.SL2MinimalFaithful

section Restrict

variable {J V : Type*} [Group J] [Group V]

theorem apply_mem_of_map_eq {U : Subgroup V} {e : MulAut V} (he : U.map (e : V →* V) = U)
    {v : V} (hv : v ∈ U) : e v ∈ U :=
  he ▸ Subgroup.mem_map_of_mem (e : V →* V) hv

@[expose] def restrictAction (ρ : J →* MulAut V) (U : Subgroup V)
    (hU : ∀ j, U.map (ρ j : V →* V) = U) : J →* MulAut U where
  toFun j :=
    { toFun := fun u => ⟨ρ j (u : V), apply_mem_of_map_eq (hU j) u.2⟩
      invFun := fun u => ⟨ρ j⁻¹ (u : V), apply_mem_of_map_eq (hU j⁻¹) u.2⟩
      left_inv := fun u => Subtype.ext (by
        change ρ j⁻¹ (ρ j (u : V)) = u
        rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply])
      right_inv := fun u => Subtype.ext (by
        change ρ j (ρ j⁻¹ (u : V)) = u
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply])
      map_mul' := fun u v => Subtype.ext (map_mul (ρ j) (u : V) (v : V)) }
  map_one' := MulEquiv.ext fun u => Subtype.ext (by
    change ρ 1 (u : V) = u
    rw [map_one, MulAut.one_apply])
  map_mul' j k := MulEquiv.ext fun u => Subtype.ext (by
    change ρ (j * k) (u : V) = ρ j (ρ k (u : V))
    rw [map_mul, MulAut.mul_apply])

theorem restrictAction_apply (ρ : J →* MulAut V) (U : Subgroup V)
    (hU : ∀ j, U.map (ρ j : V →* V) = U) (j : J) (u : U) :
    ((restrictAction ρ U hU j u : U) : V) = ρ j (u : V) :=
  rfl

theorem map_fixedPoints_eq (ρ : J →* MulAut V) {O : Subgroup J} (hO : O.Normal) (j : J) :
    (fixedPoints ρ O).map (ρ j : V →* V) = fixedPoints ρ O := by
  have key : ∀ (g : J) (v : V), v ∈ fixedPoints ρ O → ρ g v ∈ fixedPoints ρ O := by
    intro g v hv u hu
    have h1 : g⁻¹ * u * g ∈ O := by
      have := hO.conj_mem u hu g⁻¹
      rwa [inv_inv] at this
    have h2 := hv _ h1
    calc ρ u (ρ g v) = ρ g (ρ (g⁻¹ * u * g) v) := by
          rw [← MulAut.mul_apply, ← map_mul, ← MulAut.mul_apply, ← map_mul]
          congr 2
          group
      _ = ρ g v := by rw [h2]
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact key j v hv
  · intro hw
    refine ⟨ρ j⁻¹ w, key j⁻¹ w hw, ?_⟩
    change ρ j (ρ j⁻¹ w) = w
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

end Restrict

theorem two_le_card_fixedPoints {J W : Type*} [Group J] [Group W] [Finite W]
    (hW : IsPGroup 2 W) [Nontrivial W] (ρ : J →* MulAut W) {O : Subgroup J}
    (hO : IsPGroup 2 O) : 2 ≤ Nat.card (fixedPoints ρ O) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (O.map ρ) := hO.map ρ
  have hmod := hp.card_modEq_card_fixedPoints W
  have hset : (MulAction.fixedPoints (O.map ρ) W) = (fixedPoints ρ O : Set W) := by
    ext w
    constructor
    · intro hw u hu
      exact hw ⟨ρ u, Subgroup.mem_map_of_mem ρ hu⟩
    · rintro hw ⟨_, ⟨u, hu, rfl⟩⟩
      exact hw u hu
  have hc : Nat.card (MulAction.fixedPoints (O.map ρ) W) = Nat.card (fixedPoints ρ O) := by
    rw [hset]
    rfl
  rw [hc] at hmod
  obtain ⟨d, hd⟩ := hW.exists_card_eq
  have hd1 : d ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hd
    exact (Finite.one_lt_card (α := W)).ne' hd
  rw [hd] at hmod
  have h0 : 2 ^ d % 2 = 0 := by
    obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd1
    rw [pow_succ, Nat.mul_mod_left]
  have h1 : 1 ≤ Nat.card (fixedPoints ρ O) := Nat.card_pos
  have h2 := hmod
  unfold Nat.ModEq at h2
  omega

theorem exists_section {K₀ : Type*} [Group K₀] [Finite K₀] {y : K₀} (hy : Odd (orderOf y)) :
    ∀ (k : ℕ) (W : Type) [CommGroup W] [Finite W], Nat.card W ≤ k → (∀ w : W, w ^ 2 = 1) →
      ∀ ρ : K₀ →* MulAut W, ρ y ≠ 1 →
        ∃ (V : Type) (_ : CommGroup V) (_ : Finite V), (∀ v : V, v ^ 2 = 1) ∧
          Nat.card V ≤ k ∧ ∃ σ : K₀ →* MulAut V, σ y ≠ 1 ∧ ∀ x ∈ CFSG.pCore 2 K₀, σ x = 1 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro W _ _ hWk hW ρ hρ
  have hUinv := map_fixedPoints_eq ρ (CFSG.pCore_normal (p := 2) (G := K₀))
  by_cases hA : ∃ u ∈ fixedPoints ρ (CFSG.pCore 2 K₀), ρ y u ≠ u
  · obtain ⟨u, hu, hyu⟩ := hA
    refine ⟨fixedPoints ρ (CFSG.pCore 2 K₀), inferInstance, inferInstance,
      fun v => Subtype.ext (hW v), (Subgroup.card_le_card_group _).trans hWk,
      restrictAction ρ _ hUinv, fun h => hyu ?_, fun x hx => ?_⟩
    · have := congrArg (fun f : MulAut (fixedPoints ρ (CFSG.pCore 2 K₀)) =>
        ((f ⟨u, hu⟩ : fixedPoints ρ (CFSG.pCore 2 K₀)) : W)) h
      simpa [restrictAction_apply] using this
    · exact MulEquiv.ext fun v => Subtype.ext (v.2 x hx)
  · push Not at hA
    have hWnt : Nontrivial W := by
      by_contra hnt
      rw [not_nontrivial_iff_subsingleton] at hnt
      exact hρ (MulEquiv.ext fun w => Subsingleton.elim _ _)
    have hWp : IsPGroup 2 W := fun w => ⟨1, by rw [pow_one]; exact hW w⟩
    have hU2 := two_le_card_fixedPoints hWp ρ (CFSG.pCore_isPGroup (p := 2) (G := K₀))
    have hUn : (fixedPoints ρ (CFSG.pCore 2 K₀)).Normal :=
      ⟨fun n hn g => by rw [mul_comm g n, mul_inv_cancel_right]; exact hn⟩
    by_cases hB : quotientAction ρ _ hUinv y = 1
    · exfalso
      have h2 : ρ y ^ 2 = 1 := by
        ext w
        have hq := congrArg (fun f : MulAut (W ⧸ fixedPoints ρ (CFSG.pCore 2 K₀)) =>
          f (w : W ⧸ fixedPoints ρ (CFSG.pCore 2 K₀))) hB
        simp only [quotientAction_mk, MulAut.one_apply] at hq
        obtain ⟨c, hcdef⟩ : ∃ c, c = w⁻¹ * ρ y w := ⟨_, rfl⟩
        have hc : c ∈ fixedPoints ρ (CFSG.pCore 2 K₀) := by
          rw [hcdef]
          exact QuotientGroup.eq.mp hq.symm
        have hcw : ρ y w = w * c := by rw [hcdef]; group
        have hc2 := hW c
        rw [MulAut.one_apply, sq, MulAut.mul_apply, hcw, map_mul, hcw, hA c hc, mul_assoc, ← sq,
          hc2, mul_one]
      have h3 : orderOf (ρ y) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
      have h4 : Odd (orderOf (ρ y)) := Odd.of_dvd_nat hy (orderOf_map_dvd ρ y)
      have h5 : orderOf (ρ y) = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp h3 with h | h
        · exact h
        · rw [h] at h4
          exact absurd h4 (by decide)
      exact hρ (orderOf_eq_one_iff.mp h5)
    · have hcard : Nat.card (W ⧸ fixedPoints ρ (CFSG.pCore 2 K₀)) < k := by
        have h1 := (fixedPoints ρ (CFSG.pCore 2 K₀)).card_eq_card_quotient_mul_card_subgroup
        have h2 : 1 ≤ Nat.card (W ⧸ fixedPoints ρ (CFSG.pCore 2 K₀)) := Nat.card_pos
        nlinarith
      obtain ⟨V, i1, i2, hV, hVk, σ, hσ⟩ := ih _ hcard (W ⧸ fixedPoints ρ (CFSG.pCore 2 K₀))
        le_rfl (fun x => by
          induction x using QuotientGroup.induction_on with
          | H w => rw [← QuotientGroup.mk_pow, hW w, QuotientGroup.mk_one])
        (quotientAction ρ _ hUinv) hB
      exact ⟨V, i1, i2, hV, hVk.trans hcard.le, σ, hσ⟩

theorem concl_b_hat (hA7 : FactHatA7Module) {K₀ W : Type} [Group K₀] [Finite K₀] [CommGroup W]
    [Finite W] (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W ≤ 2 ^ 6) (ρ : K₀ →* MulAut W)
    (hX : IsHat (K₀ ⧸ CFSG.pCore 2 K₀) (alternatingGroup (Fin 7))) (y : K₀)
    (hyZ : (QuotientGroup.mk y : K₀ ⧸ CFSG.pCore 2 K₀) ∈
      Subgroup.center (K₀ ⧸ CFSG.pCore 2 K₀)) (hodd : Odd (orderOf y)) : ρ y = 1 := by
  by_contra hne
  obtain ⟨V, _, _, hV, hVk, σ, hσy, hσO⟩ := exists_section hodd (Nat.card W) W le_rfl hW ρ hne
  let σb : (K₀ ⧸ CFSG.pCore 2 K₀) →* MulAut V :=
    QuotientGroup.lift (CFSG.pCore 2 K₀) σ fun x hx => (MonoidHom.mem_ker).mpr (hσO x hx)
  have hσb : σb (y : K₀ ⧸ CFSG.pCore 2 K₀) = σ y := rfl
  have hinj : Function.Injective σb := by
    rw [← MonoidHom.ker_eq_bot_iff]
    obtain ⟨hq, hZ3, -⟩ := hX
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq σb.normal_ker with h | h
    · exfalso
      have hmem : (y : K₀ ⧸ CFSG.pCore 2 K₀) ∈ σb.ker := h ▸ Subgroup.mem_top _
      rw [MonoidHom.mem_ker, hσb] at hmem
      exact hσy hmem
    · have hdvd : Nat.card σb.ker ∣ 3 := hZ3 ▸ Subgroup.card_dvd_of_le h
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact Subgroup.eq_bot_of_card_eq _ h1
      · exfalso
        have heq : σb.ker = Subgroup.center (K₀ ⧸ CFSG.pCore 2 K₀) :=
          Subgroup.eq_of_le_of_card_ge h (by rw [hZ3, h3])
        have hmem : (y : K₀ ⧸ CFSG.pCore 2 K₀) ∈ σb.ker := heq ▸ hyZ
        rw [MonoidHom.mem_ker, hσb] at hmem
        exact hσy hmem
  exact hA7 _ hX V hV (hVk.trans hcard) σb hinj

end CFSG.Quasithin.Vol2.Ch11.SecA.C10KH

module

public import CFSG.Quasithin.Vol2.Ch11SecAKM4
public import CFSG.Quasithin.Vol2.Ch11SecAKE14
public import CFSG.Quasithin.Vol2.Ch11SecAKM2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA.AKN

open Matrix CFSG.SL2MinimalFaithful
open CFSG.Assembly.LowTwoRank (specialLinearGroupEquivStatedSL
  specialLinearGroupEquivStatedSL_coe)

theorem exists_odd_ne_one {K₀ V : Type*} [Group K₀] [Finite K₀] [Group V] [Finite V]
    (hperf : ⁅(⊤ : Subgroup K₀), (⊤ : Subgroup K₀)⁆ = ⊤) {ρ : K₀ →* MulAut V} (hρ : ρ ≠ 1) :
    ∃ y : K₀, Odd (orderOf y) ∧ ρ y ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut V) := Finite.of_injective (fun a : MulAut V => a.toEquiv)
    (fun a b h => MulEquiv.ext fun x => congrArg (fun e : V ≃ V => e x) h)
  by_contra hall
  push Not at hall
  apply hρ
  have hp : IsPGroup 2 ρ.range := by
    rintro ⟨_, x, rfl⟩
    obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    have hodd : Odd (orderOf (x ^ 2 ^ k)) := by
      rw [orderOf_pow' x (by positivity), hkm, Nat.gcd_mul_right_left, Nat.mul_div_cancel_left _
        (by positivity)]
      exact hm
    refine ⟨k, Subtype.ext ?_⟩
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    rw [← map_pow]
    exact hall _ hodd
  have hperf' : ⁅ρ.range, ρ.range⁆ = ρ.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, hperf]
  have h1 := C10KH.eq_bot_of_perfect_of_isPGroup hperf' hp
  exact MonoidHom.range_eq_bot_iff.mp h1

theorem exists_section_of_ne {K₀ : Type*} [Group K₀] [Finite K₀] {y : K₀}
    (hy : Odd (orderOf y)) :
    ∀ (k : ℕ) (W : Type) [CommGroup W] [Finite W], Nat.card W ≤ k → (∀ w : W, w ^ 2 = 1) →
      ∀ ρ : K₀ →* MulAut W, ρ y ≠ 1 →
        ∃ (V : Type) (_ : CommGroup V) (_ : Finite V), (∀ v : V, v ^ 2 = 1) ∧
          Nat.card V ≤ k ∧ ∃ σ : K₀ →* MulAut V, σ y ≠ 1 ∧
            (∀ x ∈ CFSG.pCore 2 K₀, σ x = 1) ∧ ∀ x, ρ x = 1 → σ x = 1 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro W _ _ hWk hW ρ hρ
  have hUinv := C10KH.map_fixedPoints_eq ρ (CFSG.pCore_normal (p := 2) (G := K₀))
  by_cases hA : ∃ u ∈ fixedPoints ρ (CFSG.pCore 2 K₀), ρ y u ≠ u
  · obtain ⟨u, hu, hyu⟩ := hA
    refine ⟨fixedPoints ρ (CFSG.pCore 2 K₀), inferInstance, inferInstance,
      fun v => Subtype.ext (hW v), (Subgroup.card_le_card_group _).trans hWk,
      C10KH.restrictAction ρ _ hUinv, fun h => hyu ?_, fun x hx => ?_, fun x hx => ?_⟩
    · have := congrArg (fun f : MulAut (fixedPoints ρ (CFSG.pCore 2 K₀)) =>
        ((f ⟨u, hu⟩ : fixedPoints ρ (CFSG.pCore 2 K₀)) : W)) h
      simpa [C10KH.restrictAction_apply] using this
    · exact MulEquiv.ext fun v => Subtype.ext (v.2 x hx)
    · exact MulEquiv.ext fun v => Subtype.ext (by
        rw [C10KH.restrictAction_apply, hx, MulAut.one_apply, MulAut.one_apply])
  · push Not at hA
    have hWnt : Nontrivial W := by
      by_contra hnt
      rw [not_nontrivial_iff_subsingleton] at hnt
      exact hρ (MulEquiv.ext fun w => Subsingleton.elim _ _)
    have hWp : IsPGroup 2 W := fun w => ⟨1, by rw [pow_one]; exact hW w⟩
    have hU2 := C10KH.two_le_card_fixedPoints hWp ρ (CFSG.pCore_isPGroup (p := 2) (G := K₀))
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
      obtain ⟨V, i1, i2, hV, hVk, σ, hσ, hσO, hσρ⟩ := ih _ hcard
        (W ⧸ fixedPoints ρ (CFSG.pCore 2 K₀)) le_rfl (fun x => by
          induction x using QuotientGroup.induction_on with
          | H w => rw [← QuotientGroup.mk_pow, hW w, QuotientGroup.mk_one])
        (quotientAction ρ _ hUinv) hB
      refine ⟨V, i1, i2, hV, hVk.trans hcard.le, σ, hσ, hσO, fun x hx => hσρ x ?_⟩
      ext w
      induction w using QuotientGroup.induction_on with
      | H w => rw [quotientAction_mk, hx, MulAut.one_apply, MulAut.one_apply]

theorem exists_theta {X : Type} [Group X] {n : ℕ}
    (hX : IsSL3 (2 ^ n) X ∨ IsPSL 3 2 n X) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      ∃ θ : SpecialLinearGroup (Fin 3) K →* X, Function.Surjective θ ∧
        θ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin 3) K) := by
  rcases hX with ⟨K, _, _, hK, ⟨e⟩⟩ | ⟨-, K, _, _, hK, ⟨e⟩⟩
  · refine ⟨K, inferInstance, inferInstance, hK,
      e.symm.toMonoidHom.comp (specialLinearGroupEquivStatedSL 3 K).toMonoidHom,
      e.symm.surjective.comp (specialLinearGroupEquivStatedSL 3 K).surjective, fun x hx => ?_⟩
    have h1 : x = 1 := by
      have h := MonoidHom.mem_ker.mp hx
      rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff] at h
      exact h
    rw [h1]
    exact Subgroup.one_mem _
  · refine ⟨K, inferInstance, inferInstance, hK, e.symm.toMonoidHom.comp
      ((QuotientGroup.mk' _).comp (specialLinearGroupEquivStatedSL 3 K).toMonoidHom),
      e.symm.surjective.comp ((QuotientGroup.mk'_surjective _).comp
        (specialLinearGroupEquivStatedSL 3 K).surjective), fun x hx => ?_⟩
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hx
    obtain ⟨c, hc⟩ := hx
    have hxm : (x : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) (c : K) := by
      have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hc
      simp only [Matrix.GeneralLinearGroup.coe_scalar] at this
      rw [MulEquiv.coe_toMonoidHom, specialLinearGroupEquivStatedSL_coe] at this
      exact this.symm
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hxm]
    exact (Matrix.scalar_commute (c : K) (fun r' => Commute.all _ r')
      (g : Matrix (Fin 3) (Fin 3) K)).eq.symm

theorem eq_one_of_ker {K : Type} [Field K] [Finite K] {X : Type*} [Group X]
    {θ : SpecialLinearGroup (Fin 3) K →* X} (hθ : Function.Surjective θ) {N : Subgroup X}
    (hN : N.Normal) (hNt : N ≠ ⊤) {x : X} (hx : x ∈ N) {k : ℕ} (hxk : x ^ 2 ^ k = 1) : x = 1 := by
  have hq := CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 K le_rfl
  obtain ⟨xh, rfl⟩ := hθ x
  have hN' : (N.comap θ).Normal := hN.comap θ
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hN' with h | h
  · exfalso
    apply hNt
    rw [eq_top_iff]
    intro z _
    obtain ⟨zh, rfl⟩ := hθ z
    exact (h ▸ Subgroup.mem_top zh : zh ∈ N.comap θ)
  · have hc : xh ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K) := h hx
    have h3 : xh ^ 3 = 1 := by
      have h1 := C10KH.card_center_sl3_dvd K
      have h2 := pow_card_eq_one' (G := Subgroup.center (SpecialLinearGroup (Fin 3) K))
        (x := ⟨xh, hc⟩)
      obtain ⟨m, hm⟩ := h1
      have := congrArg Subtype.val h2
      rw [Subgroup.coe_pow, Subgroup.coe_one] at this
      calc xh ^ 3 = xh ^ (Nat.card (Subgroup.center (SpecialLinearGroup (Fin 3) K)) * m) := by
            rw [← hm]
        _ = 1 := by rw [pow_mul, this, one_pow]
    have h4 : θ xh ^ 3 = 1 := by rw [← map_pow, h3, map_one]
    have h5 : orderOf (θ xh) ∣ Nat.gcd (2 ^ k) 3 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hxk) (orderOf_dvd_of_pow_eq_one h4)
    have h6 : Nat.gcd (2 ^ k) 3 = 1 :=
      Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)
    rw [h6, Nat.dvd_one, orderOf_eq_one_iff] at h5
    exact h5

theorem card_sup_mul_card_inf {X : Type*} [Group X] {H K : Subgroup X}
    (hHK : H ≤ Subgroup.normalizer (K : Set X)) :
    Nat.card (H ⊔ K : Subgroup X) * Nat.card (H ⊓ K : Subgroup X) = Nat.card H * Nat.card K := by
  set N := Subgroup.normalizer (K : Set X)
  have hKN : K ≤ N := Subgroup.le_normalizer
  have : (K.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have h1 := Subgroup.relIndex_mul_card (H := K.subgroupOf N) (K := H.subgroupOf N ⊔ K.subgroupOf N)
  have h2 := Subgroup.relIndex_mul_card (H := K.subgroupOf N) (K := H.subgroupOf N)
  rw [Subgroup.relIndex_sup_right, inf_of_le_left (le_sup_right :
    K.subgroupOf N ≤ H.subgroupOf N ⊔ K.subgroupOf N)] at h1
  rw [inf_comm] at h2
  have hc : ∀ Y : Subgroup X, Y ≤ N → Nat.card (Y.subgroupOf N) = Nat.card Y := fun Y hY =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY).toEquiv
  have hsup : H.subgroupOf N ⊔ K.subgroupOf N = (H ⊔ K).subgroupOf N :=
    (Subgroup.subgroupOf_sup hHK hKN).symm
  have hinf : H.subgroupOf N ⊓ K.subgroupOf N = (H ⊓ K).subgroupOf N :=
    Subgroup.ext fun _ => Iff.rfl
  rw [hsup, hc _ (sup_le hHK hKN), hc K hKN] at h1
  rw [hinf, hc _ (inf_le_left.trans hHK), hc H hHK] at h2
  rw [← h1, ← h2]
  ring

end CFSG.Quasithin.Vol2.Ch11.SecA.AKN

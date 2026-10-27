module

public import CFSG.RankThree.GF2n.Basic
public import CFSG.CGT.PushingUpLit.SolKNA.SzModelFacts
public import CFSG.Open.BenderStronglyEmbedded

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open CFSG.RankThree.GF2n.SzExplicit CFSG.CGT.PushingUpLit.SolKNA

theorem normalizer_le_of_fusionStronglyEmbedded {Y : Type} [Group Y] {H E : Subgroup Y}
    (hH : fusionStronglyEmbedded H) (hEH : E ≤ H) (hE : Even (Nat.card E)) :
    Subgroup.normalizer (E : Set Y) ≤ H := by
  intro n hn
  by_contra hnH
  have hodd := hH.2.2 n hnH
  have hsub : E ≤ H ⊓ H.map (MulAut.conj n⁻¹).toMonoidHom := by
    intro e he
    refine ⟨hEH he, ?_⟩
    have h1 : n * e * n⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hn e).mp he
    refine ⟨n * e * n⁻¹, hEH h1, ?_⟩
    show MulAut.conj n⁻¹ (n * e * n⁻¹) = e
    rw [MulAut.conj_apply]
    group
  have hdvd := Subgroup.card_dvd_of_le hsub
  have h2 : 2 ∣ Nat.card ↥(H ⊓ H.map (MulAut.conj n⁻¹).toMonoidHom) :=
    (even_iff_two_dvd.mp hE).trans hdvd
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

theorem sz_many_conjugates {a : ℕ} (ha : 1 ≤ a)
    (E : Subgroup ↥(Sz a)) (hE : E ≠ ⊥) (hE2 : IsPGroup 2 E) :
    ∃ y : Fin (2 ^ (2 * (2 * a + 1)) + 1) → ↥(Sz a),
      Function.Injective fun i => conjSubgroup (y i) E := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hEQ⟩ := hE2.exists_le_sylow
  obtain ⟨hse, -, -, -, hQcard⟩ := CFSG.Open.Open.bender_suzuki_borel a ha Q
  set Hn := Subgroup.normalizer ((Q : Subgroup ↥(Sz a)) : Set ↥(Sz a)) with hHn
  have hEH : E ≤ Hn := hEQ.trans Subgroup.le_normalizer
  have hEeven : Even (Nat.card E) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hE2
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hE (Subgroup.eq_bot_of_card_eq E (by rw [hk, pow_zero]))
    rw [hk]
    exact (Nat.even_pow.mpr ⟨even_two, hk0⟩)
  have hN : Subgroup.normalizer (E : Set ↥(Sz a)) ≤ Hn :=
    normalizer_le_of_fusionStronglyEmbedded hse hEH hEeven
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : ↥(Sz a), y₀ ∉ Hn := by
    by_contra h
    exact hse.1 (eq_top_iff.mpr fun y _ => by_contra fun hy => h ⟨y, hy⟩)
  have key : ∀ u v : ↥(Sz a), conjSubgroup u E = conjSubgroup v E → u⁻¹ * v ∈ Hn := by
    intro u v h
    apply hN
    rw [← conjSubgroup_eq_self_iff, conjSubgroup_mul, ← h, ← conjSubgroup_mul, inv_mul_cancel,
      conjSubgroup_one]
  let y' : Option ↥Q → ↥(Sz a) := fun o => match o with
    | none => 1
    | some s => (s : ↥(Sz a)) * y₀
  have hinj : Function.Injective fun o : Option ↥Q => conjSubgroup (y' o) E := by
    intro o o' h
    have h1 := key _ _ h
    have hQH : ∀ s : ↥Q, (s : ↥(Sz a)) ∈ Hn := fun s => Subgroup.le_normalizer s.2
    rcases o with _ | s <;> rcases o' with _ | s'
    · rfl
    · exfalso
      apply hy₀
      have h2 : (s' : ↥(Sz a)) * y₀ ∈ Hn := by simpa [y'] using h1
      have := Hn.mul_mem (Hn.inv_mem (hQH s')) h2
      simpa using this
    · exfalso
      apply hy₀
      have h2 : ((s : ↥(Sz a)) * y₀)⁻¹ ∈ Hn := by simpa [y'] using h1
      have h3 := Hn.inv_mem h2
      rw [inv_inv] at h3
      have := Hn.mul_mem (Hn.inv_mem (hQH s)) h3
      simpa using this
    · have hu : (s : ↥(Sz a))⁻¹ * s' ∈ (Q : Subgroup ↥(Sz a)) :=
        Q.mul_mem (Q.inv_mem s.2) s'.2
      have hn : y₀⁻¹ * ((s : ↥(Sz a))⁻¹ * s') * y₀ ∈ Hn := by
        have h2 : ((s : ↥(Sz a)) * y₀)⁻¹ * ((s' : ↥(Sz a)) * y₀) ∈ Hn := h1
        rwa [show ((s : ↥(Sz a)) * y₀)⁻¹ * ((s' : ↥(Sz a)) * y₀) =
          y₀⁻¹ * ((s : ↥(Sz a))⁻¹ * s') * y₀ by group] at h2
      have hy₀' : y₀⁻¹ ∉ Hn := fun h => hy₀ (by simpa using Hn.inv_mem h)
      have hodd := hse.2.2 y₀⁻¹ hy₀'
      have hmem : (s : ↥(Sz a))⁻¹ * s' ∈ Hn ⊓ Hn.map (MulAut.conj (y₀⁻¹)⁻¹).toMonoidHom := by
        refine ⟨Subgroup.le_normalizer hu, y₀⁻¹ * ((s : ↥(Sz a))⁻¹ * s') * y₀, hn, ?_⟩
        show MulAut.conj (y₀⁻¹)⁻¹ (y₀⁻¹ * ((s : ↥(Sz a))⁻¹ * s') * y₀) = _
        rw [MulAut.conj_apply]
        group
      have hdvd : orderOf ((s : ↥(Sz a))⁻¹ * s') ∣
          Nat.card ↥(Hn ⊓ Hn.map (MulAut.conj (y₀⁻¹)⁻¹).toMonoidHom) := by
        have := orderOf_dvd_natCard
          (⟨_, hmem⟩ : ↥(Hn ⊓ Hn.map (MulAut.conj (y₀⁻¹)⁻¹).toMonoidHom))
        rwa [Subgroup.orderOf_mk _ hmem] at this
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf (p := 2)).mp Q.isPGroup' ⟨_, hu⟩
      have hk' : orderOf ((s : ↥(Sz a))⁻¹ * s') = 2 ^ k := by
        rw [← hk]
        exact (Subgroup.orderOf_mk _ hu).symm
      have hk0 : k = 0 := by
        by_contra hk0
        have h2 : 2 ∣ Nat.card ↥(Hn ⊓ Hn.map (MulAut.conj (y₀⁻¹)⁻¹).toMonoidHom) :=
          (dvd_pow_self 2 hk0).trans (hk' ▸ hdvd)
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
      rw [hk0, pow_zero, orderOf_eq_one_iff] at hk'
      have : s = s' := Subtype.ext (inv_mul_eq_one.mp hk')
      rw [this]
  haveI : Fintype ↥Q := Fintype.ofFinite _
  have hcardO : Fintype.card (Option ↥Q) = 2 ^ (2 * (2 * a + 1)) + 1 := by
    rw [Fintype.card_option, ← Nat.card_eq_fintype_card,
      show Nat.card ↥Q = (2 ^ (2 * a + 1)) ^ 2 from hQcard, ← pow_mul, mul_comm]
  let eqv : Option ↥Q ≃ Fin (2 ^ (2 * (2 * a + 1)) + 1) := Fintype.equivFinOfCardEq hcardO
  exact ⟨fun i => y' (eqv.symm i), fun i j h => eqv.symm.injective (hinj h)⟩

theorem szTorus_coprime (a : ℕ) : Nat.Coprime (2 ^ (a + 1) + 1) (2 ^ (2 * a + 1) - 1) := by
  have hX : 1 ≤ 2 ^ (a + 1) := Nat.one_le_two_pow
  have hY : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
  have key : (2 ^ (a + 1) + 1) * (2 ^ (a + 1) - 1) = 2 * (2 ^ (2 * a + 1) - 1) + 1 := by
    have h3 : (2 : ℤ) ^ (a + 1) * 2 ^ (a + 1) = 2 * 2 ^ (2 * a + 1) := by
      rw [← pow_add, ← pow_succ']
      congr 1
      ring
    zify [hX, hY]
    linear_combination h3
  show Nat.gcd _ _ = 1
  have hg1 := Nat.gcd_dvd_left (2 ^ (a + 1) + 1) (2 ^ (2 * a + 1) - 1)
  have hg2 := Nat.gcd_dvd_right (2 ^ (a + 1) + 1) (2 ^ (2 * a + 1) - 1)
  have h4 : Nat.gcd (2 ^ (a + 1) + 1) (2 ^ (2 * a + 1) - 1) ∣ 2 * (2 ^ (2 * a + 1) - 1) + 1 :=
    key ▸ dvd_mul_of_dvd_left hg1 _
  exact Nat.dvd_one.mp ((Nat.dvd_add_right (dvd_mul_of_dvd_right hg2 2)).mp h4)

private theorem coe_torusSz' (a : ℕ) (x : (F a)ˣ) :
    (((torusSz a x : ↥(Sz a)) : GL (Fin 4) (F a)) : Matrix (Fin 4) (Fin 4) (F a)) =
      torusMat a x := rfl

theorem szTorus_one (a : ℕ) : torusSz a 1 = 1 := by
  refine Subtype.ext (Units.ext ?_)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_torusSz', torusMat]

theorem szTorus_mul (a : ℕ) (x y : (F a)ˣ) : torusSz a (x * y) = torusSz a x * torusSz a y := by
  refine Subtype.ext (Units.ext ?_)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_torusSz', torusMat, Matrix.mul_apply, Fin.sum_univ_four, mul_pow, mul_inv] <;> ring

noncomputable def szTorusHom (a : ℕ) : (F a)ˣ →* ↥(Sz a) where
  toFun := torusSz a
  map_one' := szTorus_one a
  map_mul' := szTorus_mul a

theorem szTorusHom_injective (a : ℕ) : Function.Injective (szTorusHom a) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hx' : torusSz a x = 1 := hx
  have h00 := congrArg (fun y : ↥(Sz a) =>
    ((y : GL (Fin 4) (F a)) : Matrix (Fin 4) (Fin 4) (F a)) 0 0) hx'
  have h11 := congrArg (fun y : ↥(Sz a) =>
    ((y : GL (Fin 4) (F a)) : Matrix (Fin 4) (Fin 4) (F a)) 1 1) hx'
  simp [coe_torusSz', torusMat] at h00 h11
  apply Units.ext
  calc (x : F a) = x * (x : F a) ^ 2 ^ a := by rw [h11, mul_one]
    _ = (x : F a) ^ (1 + 2 ^ a) := by rw [pow_add, pow_one]
    _ = 1 := h00

theorem sz_torus {a : ℕ} (ha : 1 ≤ a) (E : Subgroup ↥(Sz a))
    (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hsq : ∀ x ∈ E, x * x = 1)
    (hcard : Nat.card ↥E = 2 ^ (2 * a + 1)) :
    ∃ C : Subgroup ↥(Sz a), IsCyclic C ∧ Nat.card C = 2 ^ (2 * a + 1) - 1 ∧
      C ≤ Subgroup.normalizer (E : Set ↥(Sz a)) ∧
      ∀ c ∈ C, c ≠ 1 → ∀ e ∈ E, c * e * c⁻¹ = e → e = 1 := by
  classical
  obtain ⟨g₀, hg₀⟩ := exists_conj_eq_Z ha E hc hsq hcard
  let τ : (F a)ˣ →* ↥(Sz a) := (MulAut.conj g₀).toMonoidHom.comp (szTorusHom a)
  have hτ : ∀ x : (F a)ˣ, τ x = g₀ * torusSz a x * g₀⁻¹ := fun x => rfl
  have hτinj : Function.Injective τ := (MulAut.conj g₀).injective.comp (szTorusHom_injective a)
  have hconj : ∀ (x : (F a)ˣ) (b : F a), τ x * (g₀ * rootSz a 0 b * g₀⁻¹) * (τ x)⁻¹ =
      g₀ * rootSz a 0 ((x : F a) ^ (1 + 2 ^ (a + 1)) * b) * g₀⁻¹ := by
    intro x b
    rw [hτ, ← torus_conj_root_zero]
    group
  have hFcard : Nat.card (F a)ˣ = 2 ^ (2 * a + 1) - 1 := by
    rw [Nat.card_units, GaloisField.card 2 (2 * a + 1) (by omega)]
  refine ⟨τ.range, ?_, ?_, ?_, ?_⟩
  · exact isCyclic_of_surjective τ.rangeRestrict τ.rangeRestrict_surjective
  · rw [Nat.card_congr (MonoidHom.ofInjective hτinj).toEquiv.symm, hFcard]
  · intro c hc'
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hc'
    refine Subgroup.mem_normalizer_fintype fun e he => ?_
    obtain ⟨b, rfl⟩ := (hg₀ e).mp he
    rw [hconj]
    exact (hg₀ _).mpr ⟨_, rfl⟩
  · intro c hc' hc1 e he hce
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hc'
    obtain ⟨b, rfl⟩ := (hg₀ e).mp he
    rw [hconj] at hce
    have h1 : rootSz a 0 ((x : F a) ^ (1 + 2 ^ (a + 1)) * b) = rootSz a 0 b :=
      mul_left_cancel (mul_right_cancel hce)
    have h2 : (x : F a) ^ (1 + 2 ^ (a + 1)) * b = b := rootSz_zero_injective a h1
    by_cases hb : b = 0
    · rw [hb, rootSz_zero_zero]
      group
    · exfalso
      have h3 : (x : F a) ^ (1 + 2 ^ (a + 1)) = 1 :=
        mul_right_cancel₀ hb (by rw [one_mul]; exact h2)
      have hxu : x ^ (1 + 2 ^ (a + 1)) = 1 := Units.ext (by simpa using h3)
      have d1 : orderOf x ∣ 2 ^ (a + 1) + 1 := by
        have e : 1 + 2 ^ (a + 1) = 2 ^ (a + 1) + 1 := Nat.add_comm _ _
        exact e ▸ orderOf_dvd_of_pow_eq_one hxu
      have d2 : orderOf x ∣ 2 ^ (2 * a + 1) - 1 := hFcard ▸ orderOf_dvd_natCard x
      have h4 := Nat.Coprime.coprime_dvd_left d1
        (Nat.Coprime.coprime_dvd_right d2 (szTorus_coprime a))
      have hx1 : x = 1 := orderOf_eq_one_iff.mp (Nat.coprime_self _ |>.mp h4)
      exact hc1 (by rw [hx1, map_one])

end CFSG.RankThree.GF2n.Tim78

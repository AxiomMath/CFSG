module

public import CFSG.GroupTheory.WeirSylow.OrthogonalTypes

public section

namespace CFSG.RankThree.PartOne.S15K

open Module QuadraticMap CFSG.GroupTheory.WeirSylow
open CFSG.LieType.Universal.Spin (quadPlus quadMinus)

section Fixed

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

@[expose] def fixedSubmodule (S : Subgroup (V ≃ₗ[K] V)) : Submodule K V where
  carrier := {v | ∀ s ∈ S, s v = v}
  add_mem' := fun {a b} ha hb s hs => by rw [map_add, ha s hs, hb s hs]
  zero_mem' := fun s _ => map_zero s
  smul_mem' := fun c v hv s hs => by rw [map_smul, hv s hs]

theorem exists_fixed_vector {S : Subgroup (V ≃ₗ[K] V)} (hS : IsPGroup 2 S) {U : Submodule K V}
    (hU : ∀ s ∈ S, ∀ u ∈ U, s u ∈ U) (hne : U ≠ ⊥) :
    ∃ u ∈ U, u ≠ 0 ∧ ∀ s ∈ S, s u = u := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite V := Module.finite_of_finite K
  have : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hne
  let : MulAction S U :=
    { smul := fun s u => ⟨(s : V ≃ₗ[K] V) u, hU s s.2 u u.2⟩
      one_smul := fun u => Subtype.ext rfl
      mul_smul := fun s t u => Subtype.ext rfl }
  have h0 : (0 : U) ∈ MulAction.fixedPoints S U := fun s => Subtype.ext (map_zero (s : V ≃ₗ[K] V))
  have h2K : 2 ∣ Nat.card K := by
    have := Fintype.ofFinite K
    obtain ⟨n, -, hcard⟩ := FiniteField.card K 2
    rw [Nat.card_eq_fintype_card, hcard]
    exact dvd_pow_self 2 n.ne_zero
  have hdvd : 2 ∣ Nat.card U := by
    rw [Module.natCard_eq_pow_finrank (K := K)]
    exact dvd_pow h2K Module.finrank_pos.ne'
  obtain ⟨b, hb, hb0⟩ := hS.exists_fixed_point_of_prime_dvd_card_of_fixed_point U hdvd h0
  refine ⟨b, b.2, fun h => hb0 (Subtype.ext h.symm), fun s hs => ?_⟩
  exact congrArg Subtype.val (hb ⟨s, hs⟩)

theorem exists_rad_fixed {B : LinearMap.BilinForm K V} (hB : B.Nondegenerate)
    {S : Subgroup (V ≃ₗ[K] V)} (hS : IsPGroup 2 S) (hiso : ∀ s ∈ S, ∀ u w, B (s u) (s w) = B u w)
    (hne : ∃ s ∈ S, s ≠ 1) :
    ∃ r ∈ fixedSubmodule S, r ≠ 0 ∧ ∀ u ∈ fixedSubmodule S, B u r = 0 := by
  classical
  by_contra hcon
  push Not at hcon
  have hperp : B.orthogonal (fixedSubmodule S) = ⊥ := by
    by_contra hnb
    obtain ⟨u, hu, hu0, hufix⟩ := exists_fixed_vector hS (U := B.orthogonal (fixedSubmodule S))
      (fun s hs w hw => by
        rw [LinearMap.BilinForm.mem_orthogonal_iff] at hw ⊢
        intro f hf
        have h1 := hiso s hs f w
        rw [hf s hs] at h1
        rw [h1]
        exact hw f hf) hnb
    obtain ⟨f, hf, hfu⟩ := hcon u (fun s hs => hufix s hs) hu0
    exact hfu ((LinearMap.BilinForm.mem_orthogonal_iff.mp hu) f hf)
  have h1 := LinearMap.BilinForm.finrank_orthogonal hB (fixedSubmodule S)
  rw [hperp, finrank_bot] at h1
  have h2 : finrank K (fixedSubmodule S) = finrank K V :=
    le_antisymm (Submodule.finrank_le _) (by omega)
  have htop := Submodule.eq_top_of_finrank_eq h2
  obtain ⟨s, hs, hs1⟩ := hne
  apply hs1
  refine LinearEquiv.ext fun v => ?_
  have hv : v ∈ fixedSubmodule S := by rw [htop]; trivial
  exact hv s hs

end Fixed

section Aniso

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem map_hyperbolic_pair {w w₂ : V} (hw : Q w = 0) (hw₂ : Q w₂ = 0)
    (hww₂ : QuadraticMap.polar Q w w₂ = 1) (a b : K) : Q (a • w + b • w₂) = a * b := by
  rw [QuadraticMap.map_add (⇑Q), QuadraticMap.map_smul, QuadraticMap.map_smul, hw, hw₂,
    QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hww₂]
  simp

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem pow_apply_of_apply_eq (y : V ≃ₗ[K] V) {w : V} {l : K} (h : y w = l • w) (n : ℕ) :
    (y ^ n) w = l ^ n • w := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ' y n, LinearEquiv.mul_apply, ih, map_smul, h, smul_smul, ← pow_succ]

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem exists_smul_of_hyperbolic_pair {w w₂ : V} (hw : Q w = 0) (hw₂ : Q w₂ = 0)
    (hww₂ : QuadraticMap.polar Q w w₂ = 1) {P : Submodule K V} (hwP : w ∈ P) (hw₂P : w₂ ∈ P)
    (hPspan : ∀ v ∈ P, ∃ a b : K, v = a • w + b • w₂) {y : V ≃ₗ[K] V}
    (hy : ∀ v, Q (y v) = Q v) (hyP : ∀ v ∈ P, y v ∈ P) {p : ℕ} (hp : Odd p) (hyp : y ^ p = 1) :
    ∃ l : K, y w = l • w := by
  have hpolar : ∀ u v, QuadraticMap.polar Q (y u) (y v) = QuadraticMap.polar Q u v := by
    intro u v
    unfold QuadraticMap.polar
    rw [← map_add, hy, hy, hy]
  have hpol22 : QuadraticMap.polar Q w₂ w₂ = 0 := by
    rw [QuadraticMap.polar_self, hw₂]
    simp
  have hpol21 : QuadraticMap.polar Q w₂ w = 1 := by rw [QuadraticMap.polar_comm, hww₂]
  obtain ⟨a, b, hab⟩ := hPspan (y w) (hyP w hwP)
  have hQy : a * b = 0 := by
    rw [← map_hyperbolic_pair hw hw₂ hww₂, ← hab, hy, hw]
  by_cases hb : b = 0
  · exact ⟨a, by rw [hab, hb, zero_smul, add_zero]⟩
  · have ha : a = 0 := by
      rcases mul_eq_zero.mp hQy with h | h
      · exact h
      · exact absurd h hb
    obtain ⟨a', b', hab'⟩ := hPspan (y w₂) (hyP w₂ hw₂P)
    have hQy' : a' * b' = 0 := by
      rw [← map_hyperbolic_pair hw hw₂ hww₂, ← hab', hy, hw₂]
    have h1 : QuadraticMap.polar Q (y w) (y w₂) = 1 := by rw [hpolar, hww₂]
    rw [hab, hab', ha, zero_smul, zero_add, QuadraticMap.polar_smul_left,
      QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right, QuadraticMap.polar_smul_right,
      hpol21, hpol22] at h1
    simp only [smul_eq_mul, mul_one, mul_zero, add_zero] at h1
    have hb'0 : b' = 0 := by
      rcases mul_eq_zero.mp hQy' with h | h
      · rw [h, mul_zero] at h1
        exact absurd h1 zero_ne_one
      · exact h
    have hyw : y w = b • w₂ := by rw [hab, ha, zero_smul, zero_add]
    have hyw₂ : y w₂ = a' • w := by rw [hab', hb'0, zero_smul, add_zero]
    have hyy : y (y w) = w := by
      rw [hyw, map_smul, hyw₂, smul_smul, h1, one_smul]
    obtain ⟨k, rfl⟩ := hp
    have hy2 : ∀ n : ℕ, (y ^ (2 * n)) w = w := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Nat.mul_succ, pow_add, LinearEquiv.mul_apply, pow_two, LinearEquiv.mul_apply, hyy, ih]
    have hy1 : y w = w := by
      have e1 : y ^ (2 * (k + 1)) = y := by
        rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, hyp, one_mul]
      have := hy2 (k + 1)
      rwa [e1] at this
    exact ⟨1, by rw [hy1, one_smul]⟩

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem eq_zero_of_singular_of_isometry [Finite K] [CharP K 2] [FiniteDimensional K V]
    {P : Submodule K V} (hP : finrank K P = 2)
    (hPn : ∀ v ∈ P, (∀ u ∈ P, QuadraticMap.polar Q v u = 0) → v = 0) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card K - 1) {y : V ≃ₗ[K] V} (hy : ∀ v, Q (y v) = Q v)
    (hyP : ∀ v ∈ P, y v ∈ P) (hyp : y ^ p = 1) (hy1 : ∃ v ∈ P, y v ≠ v) :
    ∀ v ∈ P, Q v = 0 → v = 0 := by
  classical
  intro w hwP hQw
  by_contra hw0
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨w', hw'P, hw'⟩ : ∃ w' ∈ P, QuadraticMap.polar Q w w' ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hw0 (hPn w hwP hcon)
  obtain ⟨w₁, hw₁P, hww₁⟩ : ∃ w₁ ∈ P, QuadraticMap.polar Q w w₁ = 1 :=
    ⟨(QuadraticMap.polar Q w w')⁻¹ • w', P.smul_mem _ hw'P, by
      rw [QuadraticMap.polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hw']⟩
  have hpww : QuadraticMap.polar Q w w = 0 := by
    rw [QuadraticMap.polar_self, hQw]
    simp
  obtain ⟨w₂, hw₂P, hww₂, hQw₂⟩ : ∃ w₂ ∈ P, QuadraticMap.polar Q w w₂ = 1 ∧ Q w₂ = 0 := by
    refine ⟨w₁ + Q w₁ • w, P.add_mem hw₁P (P.smul_mem _ hwP), ?_, ?_⟩
    · rw [QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right, hww₁, hpww]
      simp
    · have h2 : Q w₁ + Q w₁ = 0 := CharTwo.add_self_eq_zero _
      rw [QuadraticMap.map_add (⇑Q), QuadraticMap.map_smul, hQw, QuadraticMap.polar_smul_right,
        QuadraticMap.polar_comm, hww₁]
      simpa using h2
  have hspan : ∀ v ∈ P, ∃ a b : K, v = a • w + b • w₂ := by
    let φ : (K × K) →ₗ[K] V := LinearMap.coprod (LinearMap.toSpanSingleton K V w)
      (LinearMap.toSpanSingleton K V w₂)
    have hφ : ∀ a b, φ (a, b) = a • w + b • w₂ := fun a b => by simp [φ]
    have hinj : Function.Injective φ := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      rintro ⟨a, b⟩ hab
      rw [hφ] at hab
      have h1 : QuadraticMap.polar Q w (a • w + b • w₂) = 0 := by rw [hab]; simp
      rw [QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right, QuadraticMap.polar_smul_right,
        hpww, hww₂] at h1
      simp only [smul_eq_mul, mul_zero, mul_one, zero_add] at h1
      subst h1
      rw [zero_smul, add_zero] at hab
      have ha : a = 0 := by
        rcases smul_eq_zero.mp hab with h | h
        · exact h
        · exact absurd h hw0
      rw [ha]
      rfl
    have hrange : LinearMap.range φ ≤ P := by
      rintro _ ⟨⟨a, b⟩, rfl⟩
      rw [hφ]
      exact P.add_mem (P.smul_mem _ hwP) (P.smul_mem _ hw₂P)
    have hfr : finrank K (LinearMap.range φ) = finrank K P := by
      rw [LinearMap.finrank_range_of_inj hinj, hP]
      simp
    have heq : LinearMap.range φ = P := Submodule.eq_of_le_of_finrank_eq hrange hfr
    intro v hv
    rw [← heq] at hv
    obtain ⟨⟨a, b⟩, rfl⟩ := hv
    exact ⟨a, b, (hφ a b).symm⟩
  obtain ⟨l, hl⟩ := exists_smul_of_hyperbolic_pair hQw hQw₂ hww₂ hwP hw₂P hspan hy hyP hpodd hyp
  have hww₂' : QuadraticMap.polar Q w₂ w = 1 := by rw [QuadraticMap.polar_comm, hww₂]
  obtain ⟨l', hl'⟩ := exists_smul_of_hyperbolic_pair hQw₂ hQw hww₂' hw₂P hwP
    (fun v hv => by
      obtain ⟨a, b, hab⟩ := hspan v hv
      exact ⟨b, a, by rw [hab, add_comm]⟩) hy hyP hpodd hyp
  have hpolar : QuadraticMap.polar Q (y w) (y w₂) = QuadraticMap.polar Q w w₂ := by
    unfold QuadraticMap.polar
    rw [← map_add, hy, hy, hy]
  rw [hl, hl', QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hww₂] at hpolar
  simp only [smul_eq_mul, mul_one] at hpolar
  have hlp : l ^ p = 1 := by
    have h1 := pow_apply_of_apply_eq y hl p
    rw [hyp] at h1
    have h2 : (1 : V ≃ₗ[K] V) w = w := rfl
    rw [h2] at h1
    have h3 : (l ^ p - 1) • w = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
    rcases smul_eq_zero.mp h3 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hw0
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hpolar
    exact zero_ne_one hpolar
  have hl1 : l = 1 := by
    have h1 : l ^ (Nat.card K - 1) = 1 := by
      have := Fintype.ofFinite K
      rw [Nat.card_eq_fintype_card]
      exact FiniteField.pow_card_sub_one_eq_one l hl0
    have hcop : Nat.Coprime p (Nat.card K - 1) := (Nat.Prime.coprime_iff_not_dvd hp).2 hpq
    have := pow_gcd_eq_one.2 ⟨hlp, h1⟩
    rwa [hcop.gcd_eq_one, pow_one] at this
  have hl'1 : l' = 1 := by
    rw [hl1, one_mul] at hpolar
    exact hpolar
  obtain ⟨v, hvP, hv⟩ := hy1
  obtain ⟨a, b, hab⟩ := hspan v hvP
  apply hv
  rw [hab, map_add, map_smul, map_smul, hl, hl', hl1, hl'1, one_smul, one_smul]

end Aniso

section Plus

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

omit [Finite K] [FiniteDimensional K V] in
theorem polarBilin_comp_subtype_nondegenerate {P : Submodule K V}
    (hPn : ∀ v ∈ P, (∀ u ∈ P, QuadraticMap.polar Q v u = 0) → v = 0) :
    (polarBilin (Q.comp P.subtype)).Nondegenerate := by
  have hsep : ∀ x : P, (∀ y : P, QuadraticMap.polar (Q.comp P.subtype) x y = 0) → x = 0 := by
    intro x hx
    exact Subtype.ext (hPn x x.2 fun u hu => hx ⟨u, hu⟩)
  exact ⟨hsep, fun y hy => hsep y fun x => by rw [QuadraticMap.polar_comm]; exact hy x⟩

omit [Finite K] [FiniteDimensional K V] in
theorem not_isPlusType_of_aniso_plane {P : Submodule K V} (hP : finrank K P = 2)
    (hPa : ∀ v ∈ P, Q v = 0 → v = 0) : ¬ IsPlusType (Q.comp P.subtype) := by
  rintro ⟨W, hW, hWs⟩
  rw [hP] at hW
  have hW1 : finrank K W = 1 := by omega
  have hne : W ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hW1
    omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact hx0 (Subtype.ext (hPa x x.2 (hWs x hx)))

theorem exists_totSing_of_two_aniso {P P' : Submodule K V} (hP : finrank K P = 2)
    (hP' : finrank K P' = 2)
    (hPn : ∀ v ∈ P, (∀ u ∈ P, QuadraticMap.polar Q v u = 0) → v = 0)
    (hP'n : ∀ v ∈ P', (∀ u ∈ P', QuadraticMap.polar Q v u = 0) → v = 0)
    (hPa : ∀ v ∈ P, Q v = 0 → v = 0) (hP'a : ∀ v ∈ P', Q v = 0 → v = 0)
    (horth : ∀ u ∈ P, ∀ w ∈ P', QuadraticMap.polar Q u w = 0) :
    ∃ T : Submodule K V, T ≤ P ⊔ P' ∧ finrank K T = 2 ∧ ∀ t ∈ T, Q t = 0 := by
  classical
  have hQP := polarBilin_comp_subtype_nondegenerate hPn
  have hQP' := polarBilin_comp_subtype_nondegenerate hP'n
  have hnp := not_isPlusType_of_aniso_plane hP hPa
  have hnp' := not_isPlusType_of_aniso_plane hP' hP'a
  rcases exists_isometry_quadPlus_or_quadMinus (Q.comp P.subtype) hQP (n := 1) le_rfl (by omega) with
    ⟨⟨e⟩⟩ | ⟨b, c, hirr, -⟩
  · exact absurd ((isPlusType_congr e).2 (isPlusType_quadPlus K 1)) hnp
  obtain ⟨e'⟩ := nonempty_isometry_of_not_isPlusType hQP' (n := 1) le_rfl (by omega) hnp' hirr
  have hplus : IsPlusType ((Q.comp P.subtype).prod (quadMinus 1 K b c)) :=
    isPlusType_prod_quadMinus hQP (d := 1) le_rfl (by omega) hnp 1 hirr
  have hplus' : IsPlusType ((Q.comp P.subtype).prod (Q.comp P'.subtype)) :=
    (isPlusType_congr ((QuadraticMap.IsometryEquiv.refl _).prod e')).2 hplus
  obtain ⟨W, hW, hWs⟩ := hplus'
  let ι : (P × P') →ₗ[K] V := P.subtype.coprod P'.subtype
  have hι : ∀ (u : P) (u' : P'), ι (u, u') = (u : V) + (u' : V) := fun u u' => by simp [ι]
  have hinj : Function.Injective ι := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨u, u'⟩ h
    rw [hι] at h
    have h1 : (u : V) = -(u' : V) := eq_neg_of_add_eq_zero_left h
    have hu : (u : V) = 0 := by
      refine hPn u u.2 fun z hz => ?_
      rw [h1, QuadraticMap.polar_neg_left, QuadraticMap.polar_comm, horth z hz u' u'.2, neg_zero]
    have hu' : (u' : V) = 0 := by rw [h1] at hu; exact neg_eq_zero.mp hu
    exact Prod.ext (Subtype.ext hu) (Subtype.ext hu')
  refine ⟨W.map ι, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    rw [show x = (x.1, x.2) from rfl, hι]
    exact Submodule.add_mem_sup x.1.2 x.2.2
  · have h1 : finrank K (W.map ι) = finrank K W := (Submodule.equivMapOfInjective ι hinj W).finrank_eq.symm
    rw [h1]
    have h2 : finrank K (P × P') = 4 := by rw [Module.finrank_prod, hP, hP']
    omega
  · rintro _ ⟨x, hx, rfl⟩
    have h1 := hWs x hx
    rw [show x = (x.1, x.2) from rfl, hι]
    change Q x.1 + Q x.2 = 0 at h1
    rw [QuadraticMap.map_add (⇑Q), horth x.1 x.1.2 x.2 x.2.2, add_zero]
    exact h1

theorem isPlusType_of_four_aniso_planes (hdim : finrank K V = 8) {P₀ P₁ P₂ P₃ : Submodule K V}
    (hP₀ : finrank K P₀ = 2) (hP₁ : finrank K P₁ = 2) (hP₂ : finrank K P₂ = 2)
    (hP₃ : finrank K P₃ = 2)
    (hn₀ : ∀ v ∈ P₀, (∀ u ∈ P₀, QuadraticMap.polar Q v u = 0) → v = 0)
    (hn₁ : ∀ v ∈ P₁, (∀ u ∈ P₁, QuadraticMap.polar Q v u = 0) → v = 0)
    (hn₂ : ∀ v ∈ P₂, (∀ u ∈ P₂, QuadraticMap.polar Q v u = 0) → v = 0)
    (hn₃ : ∀ v ∈ P₃, (∀ u ∈ P₃, QuadraticMap.polar Q v u = 0) → v = 0)
    (ha₀ : ∀ v ∈ P₀, Q v = 0 → v = 0) (ha₁ : ∀ v ∈ P₁, Q v = 0 → v = 0)
    (ha₂ : ∀ v ∈ P₂, Q v = 0 → v = 0) (ha₃ : ∀ v ∈ P₃, Q v = 0 → v = 0)
    (h01 : ∀ u ∈ P₀, ∀ w ∈ P₁, QuadraticMap.polar Q u w = 0)
    (h02 : ∀ u ∈ P₀, ∀ w ∈ P₂, QuadraticMap.polar Q u w = 0)
    (h03 : ∀ u ∈ P₀, ∀ w ∈ P₃, QuadraticMap.polar Q u w = 0)
    (h12 : ∀ u ∈ P₁, ∀ w ∈ P₂, QuadraticMap.polar Q u w = 0)
    (h13 : ∀ u ∈ P₁, ∀ w ∈ P₃, QuadraticMap.polar Q u w = 0)
    (h23 : ∀ u ∈ P₂, ∀ w ∈ P₃, QuadraticMap.polar Q u w = 0) : IsPlusType Q := by
  classical
  have h10 : ∀ u ∈ P₁, ∀ w ∈ P₀, QuadraticMap.polar Q u w = 0 := fun u hu w hw => by
    rw [QuadraticMap.polar_comm]; exact h01 w hw u hu
  have h20 : ∀ u ∈ P₂, ∀ w ∈ P₀, QuadraticMap.polar Q u w = 0 := fun u hu w hw => by
    rw [QuadraticMap.polar_comm]; exact h02 w hw u hu
  have h30 : ∀ u ∈ P₃, ∀ w ∈ P₀, QuadraticMap.polar Q u w = 0 := fun u hu w hw => by
    rw [QuadraticMap.polar_comm]; exact h03 w hw u hu
  have h21 : ∀ u ∈ P₂, ∀ w ∈ P₁, QuadraticMap.polar Q u w = 0 := fun u hu w hw => by
    rw [QuadraticMap.polar_comm]; exact h12 w hw u hu
  have h31 : ∀ u ∈ P₃, ∀ w ∈ P₁, QuadraticMap.polar Q u w = 0 := fun u hu w hw => by
    rw [QuadraticMap.polar_comm]; exact h13 w hw u hu
  obtain ⟨T₁, hT₁, hT₁d, hT₁s⟩ := exists_totSing_of_two_aniso hP₀ hP₁ hn₀ hn₁ ha₀ ha₁ h01
  obtain ⟨T₂, hT₂, hT₂d, hT₂s⟩ := exists_totSing_of_two_aniso hP₂ hP₃ hn₂ hn₃ ha₂ ha₃ h23
  have hperp : ∀ s ∈ P₀ ⊔ P₁, ∀ t ∈ P₂ ⊔ P₃, QuadraticMap.polar Q s t = 0 := by
    intro s hs t ht
    obtain ⟨s₀, hs₀, s₁, hs₁, rfl⟩ := Submodule.mem_sup.mp hs
    obtain ⟨t₂, ht₂, t₃, ht₃, rfl⟩ := Submodule.mem_sup.mp ht
    rw [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right, QuadraticMap.polar_add_right,
      h02 s₀ hs₀ t₂ ht₂, h03 s₀ hs₀ t₃ ht₃, h12 s₁ hs₁ t₂ ht₂, h13 s₁ hs₁ t₃ ht₃]
    simp
  have hdisj : T₁ ⊓ T₂ = ⊥ := by
    rw [eq_bot_iff]
    intro t ht
    obtain ⟨ht1, ht2⟩ := Submodule.mem_inf.mp ht
    obtain ⟨u₀, hu₀, u₁, hu₁, hu⟩ := Submodule.mem_sup.mp (hT₁ ht1)
    obtain ⟨u₂, hu₂, u₃, hu₃, hu'⟩ := Submodule.mem_sup.mp (hT₂ ht2)
    have h0 : u₀ = 0 := by
      refine hn₀ u₀ hu₀ fun z hz => ?_
      have h1 : QuadraticMap.polar Q t z = 0 := by
        rw [← hu', QuadraticMap.polar_add_left, h20 u₂ hu₂ z hz, h30 u₃ hu₃ z hz, add_zero]
      rw [← hu, QuadraticMap.polar_add_left, h10 u₁ hu₁ z hz, add_zero] at h1
      exact h1
    have h1 : u₁ = 0 := by
      refine hn₁ u₁ hu₁ fun z hz => ?_
      have h1 : QuadraticMap.polar Q t z = 0 := by
        rw [← hu', QuadraticMap.polar_add_left, h21 u₂ hu₂ z hz, h31 u₃ hu₃ z hz, add_zero]
      rw [← hu, QuadraticMap.polar_add_left, h01 u₀ hu₀ z hz, zero_add] at h1
      exact h1
    rw [← hu, h0, h1, add_zero]
    exact Submodule.zero_mem _
  have hT : ∀ t ∈ T₁ ⊔ T₂, Q t = 0 := by
    intro t ht
    obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ := Submodule.mem_sup.mp ht
    rw [QuadraticMap.map_add (⇑Q), hT₁s t₁ ht₁, hT₂s t₂ ht₂, hperp t₁ (hT₁ ht₁) t₂ (hT₂ ht₂)]
    simp
  refine ⟨T₁ ⊔ T₂, ?_, hT⟩
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq T₁ T₂
  rw [hdisj, finrank_bot] at h1
  omega

end Plus

end CFSG.RankThree.PartOne.S15K

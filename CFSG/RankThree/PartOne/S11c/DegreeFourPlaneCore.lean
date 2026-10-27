module

public import CFSG.RankThree.PartOne.S11c.DegreeSixPrimesCore
public import CFSG.CharacterTheory.Semidihedral.ElementaryActionTransport

public section

namespace CFSG.RankThree.PartOne.DegreeFourInduction

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne.DegreeSixInduction
open scoped IsMulCommutative

universe u v

theorem exists_ne_one_smul_eq_of_card_frattini_quotient {E R : Type*} [Group E] [Group R]
    [Finite E] [Finite R] [MulDistribMulAction E R] (hR : IsPGroup 2 R)
    (hEexp : ∀ x : E, x ^ 5 = 1) (hEcard : Nat.card E = 5 ^ 2)
    (hVel : IsElementaryAbelian 2 (R ⧸ frattini R))
    (hcard : Nat.card (R ⧸ frattini R) = 2 ^ 4) :
    ∃ x : E, x ≠ 1 ∧ ∀ r : R, x • r = r := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulDistribMulAction E (R ⧸ frattini R) := SteinbergBY.frattiniQuotientAction E R
  have : IsElementaryAbelian 2 (R ⧸ frattini R) := hVel
  set ρ := Semidihedral.ElementaryActionTransport.primeFieldAction (p := 2)
    (MulDistribMulAction.toMulAut E (R ⧸ frattini R)) with hρ
  set D : Subgroup E := (MulDistribMulAction.toMulAut E (R ⧸ frattini R)).ker with hD
  have hDmem : ∀ e : E, e ∈ D ↔ ∀ v : R ⧸ frattini R, e • v = v := by
    intro e
    rw [hD, MonoidHom.mem_ker]
    constructor
    · intro h v
      exact congrArg (fun σ : MulAut (R ⧸ frattini R) => σ v) h
    · intro h
      ext v
      exact h v
  have hker : ρ.ker = D := Semidihedral.ElementaryActionTransport.primeFieldAction_kernel _
  have hfin : Module.finrank (ZMod 2) (Additive (R ⧸ frattini R)) = 4 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (R ⧸ frattini R))
    rw [Nat.card_zmod] at h
    have h' : Nat.card (Additive (R ⧸ frattini R)) = Nat.card (R ⧸ frattini R) := rfl
    rw [h', hcard] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  let b := Module.finBasisOfFinrankEq (ZMod 2) (Additive (R ⧸ frattini R)) hfin
  have hGL : Nat.card (LinearMap.GeneralLinearGroup (ZMod 2) (Additive (R ⧸ frattini R))) =
      20160 := by
    have h1 : Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) =
        Nat.card (LinearMap.GeneralLinearGroup (ZMod 2) (Additive (R ⧸ frattini R))) :=
      Nat.card_congr (Matrix.GeneralLinearGroup.toLin' b).toEquiv
    rw [← h1, Matrix.card_GL_field, ZMod.card]
    decide
  have hdvd : Nat.card ρ.range ∣ 20160 := hGL ▸ Subgroup.card_subgroup_dvd_card ρ.range
  have hmul := Subgroup.card_ker_mul_card_range ρ
  have hker1 : Nat.card ρ.ker ≠ 1 := by
    intro h1
    rw [h1, one_mul, hEcard] at hmul
    rw [hmul] at hdvd
    norm_num at hdvd
  obtain ⟨⟨x, hxD⟩, hx1⟩ : ∃ x : D, x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hker1
    rw [hker]
    exact Subgroup.card_eq_one.mpr (Subgroup.eq_bot_iff_forall _ |>.mpr fun y hy =>
      congrArg Subtype.val (hcon ⟨y, hy⟩))
  refine ⟨x, fun h => hx1 (Subtype.ext h), fun r => ?_⟩
  obtain ⟨hquot, hker2⟩ := GroupTheory.frattini_automorphism_kernel hR
  set σ := MulDistribMulAction.toMulAut E R x with hσ
  have hσker : σ ∈ (OrderReductions.FrattiniAutomorphisms.quotientAutomorphism
      (frattini R)).ker := by
    rw [MonoidHom.mem_ker]
    ext v
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective v
    rw [hquot, MulAut.one_apply]
    exact (hDmem x).mp hxD q
  have hσp : σ ^ 5 = 1 := by rw [hσ, ← map_pow, hEexp, map_one]
  obtain ⟨i, hi⟩ := hker2 ⟨σ, hσker⟩
  have hσi : σ ^ 2 ^ i = 1 := congrArg Subtype.val hi
  have hcop : Nat.Coprime (2 ^ i) 5 := Nat.Coprime.pow_left i (by norm_num)
  have hord : orderOf σ = 1 := Nat.eq_one_of_dvd_coprimes hcop
    (orderOf_dvd_of_pow_eq_one hσi) (orderOf_dvd_of_pow_eq_one hσp)
  exact congrArg (fun τ : MulAut R => (τ r : R)) (orderOf_eq_one_iff.mp hord)

theorem extraspecial_pow_le_finrank {k : Type u} [Field k] (h2 : (2 : k) ≠ 0) {V : Type v}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
    {R : Subgroup (Module.End k V)ˣ} [Finite R] (hext : IsExtraspecialPGroup 2 R) {z : R}
    (hz : Subgroup.center R = Subgroup.zpowers z)
    (hzV : ((z : (Module.End k V)ˣ) : Module.End k V) = -1) :
    ∃ n : ℕ, 1 ≤ n ∧ 2 ^ n ≤ Module.finrank k V ∧ Nat.card R = 2 ^ (1 + 2 * n) := by
  obtain ⟨n, hn1, hcard⟩ := PartOne.Quotient36.exists_card_eq_pow_extraspecial hext
  refine ⟨n, hn1, ?_, hcard⟩
  let ρ : Representation k R V := (Units.coeHom (Module.End k V)).comp R.subtype
  have h := SteinbergBM.pow_le_finrank_of_invariant hext hcard hz h2 ρ ⊤ top_ne_bot
    (fun _ _ _ => Submodule.mem_top) (fun w _ => by
      change ((z : (Module.End k V)ˣ) : Module.End k V) w = -w
      rw [hzV]
      rfl)
  rwa [finrank_top] at h

theorem exists_scalar_of_commute_extraspecial {k : Type u} [Field k] (h2 : (2 : k) ≠ 0)
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {R : Subgroup (Module.End k V)ˣ} [Finite R] (hext : IsExtraspecialPGroup 2 R) {n : ℕ}
    (hcard : Nat.card R = 2 ^ (1 + 2 * n)) {z : R} (hz : Subgroup.center R = Subgroup.zpowers z)
    (hdim : Module.finrank k V = 2 ^ n) {x : (Module.End k V)ˣ}
    (hx : ∀ r ∈ R, x * r = r * x) :
    ∃ c : kˣ, (x : Module.End k V) = algebraMap k (Module.End k V) (c : k) := by
  have hK : ringChar k ≠ 2 := by
    intro h
    apply h2
    have h0 : ((2 : ℕ) : k) = 0 := (ringChar.spec k 2).mpr (by rw [h])
    simpa using h0
  let ρ : Representation k R V := (Units.coeHom (Module.End k V)).comp R.subtype
  have hρinj : Function.Injective ρ := fun a b h => Subtype.ext (Units.ext h)
  have hcen := (SteinbergBM.minimal_extraspecial_module_scalar_centralizer.{_, _, _, 0} hext hcard
    hz hK hdim ρ hρinj).2.2.1
  have hxmem : x ∈ Subgroup.centralizer (Set.range ρ.asGroupHom) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨s, rfl⟩
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Representation.asGroupHom_apply]
    have h' := congrArg Units.val (hx s s.2)
    rw [Units.val_mul, Units.val_mul] at h'
    exact h'.symm
  rw [hcen] at hxmem
  obtain ⟨c, hc⟩ := hxmem
  exact ⟨c, by rw [← hc]; rfl⟩

theorem step_five {k : Type u} [Field k] (h2 : (2 : k) ≠ 0) {V : Type v} [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (hV : Module.finrank k V ≤ 4)
    {Q A : Subgroup (Module.End k V)ˣ} [Finite Q] (hQ : IsPGroup 2 Q) [Finite A]
    (hA : IsPGroup 5 A) (hAQ : A ≤ Subgroup.normalizer (Q : Set (Module.End k V)ˣ))
    (hplane : Module.finrank k V = 4 → Nat.card A = 5 ^ 2 ∧ (∀ x ∈ A, x ^ 5 = 1) ∧
      ∀ x ∈ A, LinearMap.det ((x : (Module.End k V)ˣ) : Module.End k V) = 1)
    (ih : ∀ W : Submodule k V, Module.finrank k W < Module.finrank k V →
      CommuteStmt k 5 W) :
    ∀ a ∈ A, ∀ q ∈ Q, a * q = q * a := by
  classical
  intro a₁ ha₁ q₁ hq₁
  by_contra hcon
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA2 : ¬ 2 ∣ Nat.card A := by
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hA
    rw [hj]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two (by norm_num : Nat.Prime 5)).mp
      (Nat.prime_two.dvd_of_dvd_pow h)
    omega
  let Good : Subgroup (Module.End k V)ˣ → Prop := fun R =>
    R ≤ Q ∧ (∀ a ∈ A, ∀ r ∈ R, a * r * a⁻¹ ∈ R) ∧ ∃ a ∈ A, ∃ r ∈ R, a * r * a⁻¹ ≠ r
  have hgood : Good Q := by
    refine ⟨le_rfl, fun a ha r hr => ?_, a₁, ha₁, q₁, hq₁, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hAQ ha) r).mp hr
    · intro h
      apply hcon
      calc a₁ * q₁ = a₁ * q₁ * a₁⁻¹ * a₁ := by group
        _ = q₁ * a₁ := by rw [h]
  have hex : ∃ n : ℕ, ∃ R : Subgroup (Module.End k V)ˣ, Good R ∧ Nat.card R = n :=
    ⟨_, Q, hgood, rfl⟩
  obtain ⟨R, ⟨hRQ, hRinv, a₀, ha₀, r₀, hr₀, hmove₀⟩, hRn⟩ := Nat.find_spec hex
  have hRmin : ∀ S : Subgroup (Module.End k V)ˣ, Good S → Nat.card R ≤ Nat.card S :=
    fun S hS => hRn ▸ Nat.find_min' hex ⟨S, hS, rfl⟩
  have hAR : A ≤ Subgroup.normalizer (R : Set (Module.End k V)ˣ) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro r
    refine ⟨fun hr => hRinv a ha r hr, fun h => ?_⟩
    have := hRinv a⁻¹ (A.inv_mem ha) _ h
    simpa [mul_assoc] using this
  have : Finite R :=
    Finite.of_injective (Subgroup.inclusion hRQ) (Subgroup.inclusion_injective hRQ)
  have hR2 : IsPGroup 2 R := hQ.to_le hRQ
  have : Fact (A ≤ Subgroup.normalizer (R : Set (Module.End k V)ˣ)) := ⟨hAR⟩
  have hnt : ∃ (a : A) (q : R), a • q ≠ q := by
    refine ⟨⟨a₀, ha₀⟩, ⟨r₀, hr₀⟩, fun h => hmove₀ ?_⟩
    have := congrArg Subtype.val h
    simpa using this
  have hmin : ∀ S : Subgroup R, S ≠ ⊤ → (∀ (a : A), ∀ s ∈ S, a • s ∈ S) →
      ∀ (a : A), ∀ s ∈ S, a • s = s := by
    intro S hS hSinv
    by_contra hcon
    push Not at hcon
    obtain ⟨a, s, hs, hes⟩ := hcon
    have hgoodS : Good (S.map R.subtype) := by
      refine ⟨(Subgroup.map_subtype_le S).trans hRQ, ?_, a, a.2, s,
        Subgroup.mem_map_of_mem _ hs, ?_⟩
      · rintro b hb _ ⟨t, ht, rfl⟩
        refine ⟨(⟨b, hb⟩ : A) • t, hSinv ⟨b, hb⟩ t ht, ?_⟩
        simp
      · intro h
        apply hes
        apply Subtype.ext
        simpa using h
    have hle := hRmin _ hgoodS
    rw [Subgroup.card_map_of_injective R.subtype_injective] at hle
    exact hS ((Subgroup.card_eq_iff_eq_top S).mp (le_antisymm (Subgroup.card_le_card_group S) hle))
  obtain ⟨htop, hΦ, ⟨hVnt, hVel, hVmove, hVirr⟩, hab, hnab⟩ :=
    SteinbergBY.minimal_coprime_action_elementary_or_special (A := A) (P := R) (l := 2) hR2 hA2
      hnt hmin
  by_cases hRab : IsMulCommutative R
  ·
    obtain ⟨-, hel⟩ := hab hRab
    have : IsElementaryAbelian 2 R := hel
    have hc := commute_of_isElementaryAbelian_of_normalizes h2 (by norm_num : Nat.Prime 5) hA
      (by omega) hAR a₀ ha₀ r₀ hr₀
    apply hmove₀
    rw [hc, mul_inv_cancel_right]
  · obtain ⟨hcf, hfc, hcne, hcel, hcen⟩ := hnab hRab
    have : IsElementaryAbelian 2 (commutator R) := hcel
    have hsqR : ∀ z : R, z ∈ Subgroup.center R → z * z = 1 := by
      intro z hz
      have hzc : z ∈ commutator R := by rw [hcf, hfc]; exact hz
      have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (commutator R)) ⟨z, hzc⟩
      have h' : z ^ 2 = 1 := congrArg Subtype.val h
      rwa [pow_two] at h'
    have hsq : ∀ z : R, z ∈ Subgroup.center R →
        ((z : (Module.End k V)ˣ) : Module.End k V) * ((z : (Module.End k V)ˣ) : Module.End k V) =
          1 := by
      intro z hz
      rw [← Units.val_mul, ← Subgroup.coe_mul, hsqR z hz]
      simp
    have hcomm : ∀ z : R, z ∈ Subgroup.center R → ∀ r ∈ R,
        r * (z : (Module.End k V)ˣ) = (z : (Module.End k V)ˣ) * r := by
      intro z hz r hr
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨r, hr⟩)
    have hAfix : ∀ z : R, z ∈ Subgroup.center R → ∀ a ∈ A,
        a * (z : (Module.End k V)ˣ) * a⁻¹ = z := by
      intro z hz a ha
      have := congrArg Subtype.val (hcen ⟨a, ha⟩ z hz)
      simpa using this
    have h1ne : (1 : k) ≠ -1 := fun h => h2 (by linear_combination h)
    by_cases htwo : ∃ z : R, z ∈ Subgroup.center R ∧
        Module.End.eigenspace ((z : (Module.End k V)ˣ) : Module.End k V) 1 ≠ ⊥ ∧
        Module.End.eigenspace ((z : (Module.End k V)ˣ) : Module.End k V) (-1) ≠ ⊥
    ·
      obtain ⟨z, hzc, hE1, hE2⟩ := htwo
      let C : Subgroup (Module.End k V)ˣ := Subgroup.centralizer {(z : (Module.End k V)ˣ)}
      have hCinv : ∀ ε : k, ∀ g ∈ C, ∀ w ∈ Module.End.eigenspace
          ((z : (Module.End k V)ˣ) : Module.End k V) ε,
          ((g : (Module.End k V)ˣ) : Module.End k V) w ∈ Module.End.eigenspace
            ((z : (Module.End k V)ˣ) : Module.End k V) ε := by
        intro ε g hg w hw
        have hgz := Subgroup.mem_centralizer_singleton_iff.mp hg
        rw [Module.End.mem_eigenspace_iff] at hw ⊢
        rw [← Module.End.mul_apply, ← Units.val_mul, ← hgz, Units.val_mul, Module.End.mul_apply, hw,
          map_smul]
      have hRC : R ≤ C := fun r hr =>
        Subgroup.mem_centralizer_singleton_iff.mpr (hcomm z hzc r hr)
      have hne1 := eigenspace_ne_top_of_ne (z := ((z : (Module.End k V)ˣ) : Module.End k V))
        h1ne hE2
      have hne2 := eigenspace_ne_top_of_ne (z := ((z : (Module.End k V)ˣ) : Module.End k V))
        h1ne.symm hE1
      have hcu : ∀ u ∈ A, ∀ r ∈ R, u * r = r * u := by
        intro u hu r hr
        obtain ⟨m, hm⟩ := hA ⟨u, hu⟩
        have hum : u ^ 5 ^ m = 1 := congrArg Subtype.val hm
        have huC : u ∈ C := by
          rw [Subgroup.mem_centralizer_singleton_iff]
          have := hAfix z hzc u hu
          calc u * z = u * z * u⁻¹ * u := by group
            _ = z * u := by rw [this]
        have hu_norm : u ∈ Subgroup.normalizer (R : Set (Module.End k V)ˣ) := hAR hu
        have hc₁ := commute_on_invariant_subspace (hCinv 1) (ih _ (Submodule.finrank_lt hne1))
          hR2 hRC huC hu_norm hum
        have hc₂ := commute_on_invariant_subspace (hCinv (-1))
          (ih _ (Submodule.finrank_lt hne2)) hR2 hRC huC hu_norm hum
        apply Units.ext
        rw [Units.val_mul, Units.val_mul]
        exact eq_of_eq_on_eigenspaces h2 (hsq z hzc) (fun w hw => hc₁ r hr w hw)
          (fun w hw => hc₂ r hr w hw)
      apply hmove₀
      rw [hcu a₀ ha₀ r₀ hr₀, mul_inv_cancel_right]
    ·
      have hB : ∀ z : R, z ∈ Subgroup.center R →
          Module.End.eigenspace ((z : (Module.End k V)ˣ) : Module.End k V) 1 = ⊥ ∨
          Module.End.eigenspace ((z : (Module.End k V)ˣ) : Module.End k V) (-1) = ⊥ := by
        intro z hz
        by_contra hcon
        push Not at hcon
        exact htwo ⟨z, hz, hcon.1, hcon.2⟩
      have hdich : ∀ z : R, z ∈ Subgroup.center R →
          ((z : (Module.End k V)ˣ) : Module.End k V) = 1 ∨
            ((z : (Module.End k V)ˣ) : Module.End k V) = -1 := fun z hz =>
        eq_one_or_eq_neg_one_of_eigenspace_eq_bot (hsq z hz) (hB z hz)
      have hcenter_ne : Subgroup.center R ≠ ⊥ := by
        rw [← hfc, ← hcf]
        exact hcne
      obtain ⟨⟨z₀, hz₀c⟩, hz₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hcenter_ne
      have hz₀ne : z₀ ≠ 1 := fun h => hz₀1 (Subtype.ext h)
      have : Nontrivial V := by
        by_contra hnt'
        rw [not_nontrivial_iff_subsingleton] at hnt'
        apply hz₀ne
        apply Subtype.ext
        apply Units.ext
        apply LinearMap.ext
        intro v
        exact Subsingleton.elim _ _
      have hz₀neg : ((z₀ : (Module.End k V)ˣ) : Module.End k V) = -1 := by
        rcases hdich z₀ hz₀c with h | h
        · exfalso
          apply hz₀ne
          apply Subtype.ext
          apply Units.ext
          simpa using h
        · exact h
      have hz : Subgroup.center R = Subgroup.zpowers z₀ := by
        apply le_antisymm
        · intro z hz
          rcases hdich z hz with h | h
          · have : z = 1 := by
              apply Subtype.ext
              apply Units.ext
              simpa using h
            rw [this]
            exact one_mem _
          · have : z = z₀ := by
              apply Subtype.ext
              apply Units.ext
              rw [h, hz₀neg]
            rw [this]
            exact Subgroup.mem_zpowers z₀
        · rw [Subgroup.zpowers_le]
          exact hz₀c
      have hcard2 : Nat.card (Subgroup.center R) = 2 := by
        rw [hz, Nat.card_zpowers]
        refine orderOf_eq_prime ?_ hz₀ne
        rw [pow_two]
        exact hsqR z₀ hz₀c
      have hext : IsExtraspecialPGroup 2 R := ⟨hR2, hcf.trans hfc, hfc, hcard2⟩
      obtain ⟨n, hn1, hn2, hcardR⟩ := extraspecial_pow_le_finrank h2 hext hz hz₀neg
      have hn : n = 1 ∨ n = 2 := by
        by_contra hcon'
        push Not at hcon'
        have hn3 : 3 ≤ n := by omega
        have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
        omega
      have hΦcard : Nat.card (frattini R) = 2 := by
        rw [hfc]
        exact hcard2
      have hquot : Nat.card (R ⧸ frattini R) = 2 ^ (2 * n) := by
        have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini R)
        rw [hcardR, hΦcard, pow_add, pow_one] at h
        omega
      let _ := SteinbergBY.frattiniQuotientAction A R
      have hmod := card_modEq_one_of_irreducible (A := A) (X := R ⧸ frattini R) (p := 5) hA
        hVirr hVmove
      rw [hquot] at hmod
      rcases hn with rfl | rfl
      · exact absurd hmod (by decide)
      ·
        have hfin4 : Module.finrank k V = 4 := by omega
        obtain ⟨hAcard, hAexp, hAdet⟩ := hplane hfin4
        obtain ⟨x, hx1, hxfix⟩ := exists_ne_one_smul_eq_of_card_frattini_quotient (E := A)
          (R := R) hR2 (fun x => Subtype.ext (by simpa using hAexp x x.2)) hAcard hVel
          (by simpa using hquot)
        have hcommR : ∀ r ∈ R, (x : (Module.End k V)ˣ) * r = r * (x : (Module.End k V)ˣ) := by
          intro r hr
          have h := congrArg Subtype.val (hxfix ⟨r, hr⟩)
          have h' : (x : (Module.End k V)ˣ) * r * (x : (Module.End k V)ˣ)⁻¹ = r := by
            simpa using h
          calc (x : (Module.End k V)ˣ) * r =
              (x : (Module.End k V)ˣ) * r * (x : (Module.End k V)ˣ)⁻¹ * x := by group
            _ = r * x := by rw [h']
        obtain ⟨c, hc⟩ := exists_scalar_of_commute_extraspecial h2 hext hcardR hz
          (hfin4.trans (by norm_num)) hcommR
        have hdetx := hAdet x x.2
        rw [hc, Algebra.algebraMap_eq_smul_one, LinearMap.det_smul, hfin4, map_one,
          mul_one] at hdetx
        have hx5 : ((x : (Module.End k V)ˣ) : Module.End k V) ^ 5 = 1 := by
          rw [← Units.val_pow_eq_pow_val, hAexp x x.2, Units.val_one]
        rw [hc, ← map_pow] at hx5
        have hc5 : (c : k) ^ 5 = 1 :=
          (algebraMap k (Module.End k V)).injective (by rw [hx5, map_one])
        have hc1 : (c : k) = 1 := by
          have h45 : (c : k) ^ 5 = (c : k) ^ 4 * c := by ring
          rw [h45, hdetx, one_mul] at hc5
          exact hc5
        apply hx1
        apply Subtype.ext
        apply Units.ext
        rw [hc, hc1, map_one]
        rfl

theorem commuteStmt_five_of_finrank_le_three {k : Type u} [Field k] (h2 : (2 : k) ≠ 0) :
    ∀ (n : ℕ) (V : Type v) [AddCommGroup V] [Module k V] [FiniteDimensional k V],
      Module.finrank k V = n → n ≤ 3 → CommuteStmt k 5 V := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V _ _ _ hn hn3 Q hQfin hQ u hu m hum q hq
    have hfin : Finite (Subgroup.zpowers u) :=
      finite_zpowers.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨5 ^ m, pow_pos (by norm_num) m, hum⟩)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).mp
      (orderOf_dvd_of_pow_eq_one hum)
    have hAp : IsPGroup 5 (Subgroup.zpowers u) :=
      IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers]; exact hj)
    exact step_five h2 (by omega) hQ hAp (Subgroup.zpowers_le.mpr hu)
      (fun h => absurd h (by omega))
      (fun W hW => ih (Module.finrank k W) (by omega) W rfl (by omega)) u
      (Subgroup.mem_zpowers u) q hq

theorem plane_five {k : Type u} [Field k] (h2 : (2 : k) ≠ 0) {V : Type v} [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (hV : Module.finrank k V ≤ 4)
    {Q E : Subgroup (Module.End k V)ˣ} [Finite Q] (hQ : IsPGroup 2 Q) [IsElementaryAbelian 5 E]
    (hEcard : Nat.card E = 5 ^ 2)
    (hdet : ∀ x ∈ E, LinearMap.det ((x : (Module.End k V)ˣ) : Module.End k V) = 1)
    (hEQ : E ≤ Subgroup.normalizer (Q : Set (Module.End k V)ˣ)) :
    ∀ a ∈ E, ∀ q ∈ Q, a * q = q * a := by
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hEcard]; norm_num)
  exact step_five h2 hV hQ (IsElementaryAbelian.isPGroup 5 E) hEQ
    (fun _ => ⟨hEcard, fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx, hdet⟩)
    (fun W hW => commuteStmt_five_of_finrank_le_three h2 _ W rfl (by omega))

end CFSG.RankThree.PartOne.DegreeFourInduction

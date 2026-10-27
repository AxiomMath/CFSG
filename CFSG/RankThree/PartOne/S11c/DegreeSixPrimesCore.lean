module

public import CFSG.RankThree.PartOne.S11c.DegreeSixPrimesWeights
public import CFSG.RankThree.GroupTheory.SteinbergBMMinimalExtraspecialModule
public import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientShape

public section

namespace CFSG.RankThree.PartOne.DegreeSixInduction

open CFSG CFSG.RankThree.GroupTheory

universe u v

@[expose] def CommuteStmt (k : Type u) [Field k] (p : ℕ) (V : Type v) [AddCommGroup V]
    [Module k V] : Prop :=
  ∀ (Q : Subgroup (Module.End k V)ˣ) [Finite Q], IsPGroup 2 Q →
    ∀ u ∈ Subgroup.normalizer (Q : Set (Module.End k V)ˣ), ∀ m : ℕ, u ^ p ^ m = 1 →
      ∀ q ∈ Q, u * q = q * u

theorem commute_on_invariant_subspace {k : Type u} [Field k] {p : ℕ}
    {V : Type v} [AddCommGroup V] [Module k V] {W : Submodule k V}
    {C : Subgroup (Module.End k V)ˣ}
    (hC : ∀ g ∈ C, ∀ w ∈ W, ((g : (Module.End k V)ˣ) : Module.End k V) w ∈ W)
    (hW : CommuteStmt k p W) {R : Subgroup (Module.End k V)ˣ} [Finite R] (hR : IsPGroup 2 R)
    (hRC : R ≤ C) {u : (Module.End k V)ˣ} (huC : u ∈ C)
    (hu : u ∈ Subgroup.normalizer (R : Set (Module.End k V)ˣ)) {m : ℕ} (hum : u ^ p ^ m = 1) :
    ∀ r ∈ R, ∀ w ∈ W, (u : Module.End k V) ((r : Module.End k V) w) =
      (r : Module.End k V) ((u : Module.End k V) w) := by
  classical
  let τ₀ : C →* Module.End k W :=
    { toFun := fun g => ((g : (Module.End k V)ˣ) : Module.End k V).restrict (hC g g.2)
      map_one' := by
        ext w
        rfl
      map_mul' := fun g h => by
        ext w
        rfl }
  let τ : C →* (Module.End k W)ˣ := τ₀.toHomUnits
  let R₀ : Subgroup C := R.comap C.subtype
  have : Finite R₀ := Finite.of_injective (fun x : R₀ => (⟨x.1.1, x.2⟩ : R)) (by
    intro x y h
    have h' : (⟨x.1.1, x.2⟩ : R) = ⟨y.1.1, y.2⟩ := h
    exact Subtype.ext (Subtype.ext (Subtype.mk.inj h')))
  have : Finite (R₀.map τ) := Finite.of_surjective
    (fun x : R₀ => (⟨τ x.1, Subgroup.mem_map_of_mem τ x.2⟩ : R₀.map τ)) (by
      rintro ⟨_, x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩)
  have hR₀ : IsPGroup 2 R₀ := hR.comap_subtype
  have hnorm : (⟨u, huC⟩ : C) ∈ Subgroup.normalizer (R₀ : Set C) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact Subgroup.mem_normalizer_iff.mp hu (x : (Module.End k V)ˣ)
  have hord : (τ ⟨u, huC⟩) ^ p ^ m = 1 := by
    rw [← map_pow]
    have : (⟨u, huC⟩ : C) ^ p ^ m = 1 := Subtype.ext hum
    rw [this, map_one]
  have h := hW (R₀.map τ) (hR₀.map τ) (τ ⟨u, huC⟩)
    (Subgroup.le_normalizer_map τ (Subgroup.mem_map_of_mem τ hnorm)) m hord
  intro r hr w hw
  have hrC := hRC hr
  have h' := h (τ ⟨r, hrC⟩) (Subgroup.mem_map_of_mem τ (show (⟨r, hrC⟩ : C) ∈ R₀ from hr))
  have h'' := congrArg (fun x : (Module.End k W)ˣ => ((x : Module.End k W) ⟨w, hw⟩ : W)) h'
  exact congrArg Subtype.val h''

theorem card_modEq_one_of_irreducible {A X : Type*} [Group A] [Group X] [Finite X]
    [MulDistribMulAction A X] {p : ℕ} [Fact p.Prime] (hA : IsPGroup p A)
    (hirr : ∀ S : Subgroup X, (∀ a : A, ∀ s ∈ S, a • s ∈ S) → S = ⊥ ∨ S = ⊤)
    (hmove : ∃ (a : A) (v : X), a • v ≠ v) : Nat.card X ≡ 1 [MOD p] := by
  have h1 := hA.card_modEq_card_fixedPoints X
  have hS : FixedPoints.subgroup A X = ⊥ := by
    rcases hirr (FixedPoints.subgroup A X) (fun a s hs => by
      rw [(FixedPoints.mem_subgroup A X s).mp hs a]; exact hs) with h | h
    · exact h
    · exfalso
      obtain ⟨a, v, hv⟩ := hmove
      apply hv
      have : v ∈ FixedPoints.subgroup A X := by rw [h]; exact Subgroup.mem_top v
      exact (FixedPoints.mem_subgroup A X v).mp this a
  have hfix : MulAction.fixedPoints A X = {1} := by
    ext x
    rw [Set.mem_singleton_iff]
    constructor
    · intro hx
      have : x ∈ FixedPoints.subgroup A X := (FixedPoints.mem_subgroup A X x).mpr hx
      rw [hS, Subgroup.mem_bot] at this
      exact this
    · rintro rfl a
      exact smul_one a
  rw [hfix] at h1
  simpa using h1

section Eigen

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

theorem add_apply_mem_eigenspace_one {z : Module.End k V} (hz : z * z = 1) (v : V) :
    v + z v ∈ Module.End.eigenspace z 1 := by
  rw [Module.End.mem_eigenspace_iff, one_smul, map_add, ← Module.End.mul_apply, hz,
    Module.End.one_apply, add_comm]

theorem sub_apply_mem_eigenspace_neg_one {z : Module.End k V} (hz : z * z = 1) (v : V) :
    v - z v ∈ Module.End.eigenspace z (-1) := by
  rw [Module.End.mem_eigenspace_iff, neg_one_smul, map_sub, ← Module.End.mul_apply, hz,
    Module.End.one_apply, neg_sub]

theorem eigenspace_ne_top_of_ne {z : Module.End k V} {ε μ : k} (hεμ : ε ≠ μ)
    (h : Module.End.eigenspace z μ ≠ ⊥) : Module.End.eigenspace z ε ≠ ⊤ := by
  intro htop
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  have hw' : w ∈ Module.End.eigenspace z ε := by rw [htop]; exact Submodule.mem_top
  rw [Module.End.mem_eigenspace_iff] at hw hw'
  have h0 : (ε - μ) • w = 0 := by rw [sub_smul, ← hw', hw, sub_self]
  exact hw0 ((smul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hεμ))

theorem eq_of_eq_on_eigenspaces (h2 : (2 : k) ≠ 0) {z f g : Module.End k V} (hz : z * z = 1)
    (h₁ : ∀ w ∈ Module.End.eigenspace z 1, f w = g w)
    (h₂ : ∀ w ∈ Module.End.eigenspace z (-1), f w = g w) : f = g := by
  apply LinearMap.ext
  intro v
  have h3 : (2 : k) • v = (v + z v) + (v - z v) := by rw [two_smul]; abel
  have h4 : (2 : k) • f v = (2 : k) • g v := by
    rw [← map_smul, ← map_smul, h3, map_add f (v + z v) (v - z v),
      map_add g (v + z v) (v - z v), h₁ _ (add_apply_mem_eigenspace_one hz v),
      h₂ _ (sub_apply_mem_eigenspace_neg_one hz v)]
  exact smul_right_injective V h2 h4

theorem eq_one_or_eq_neg_one_of_eigenspace_eq_bot {z : Module.End k V} (hz : z * z = 1)
    (h : Module.End.eigenspace z 1 = ⊥ ∨ Module.End.eigenspace z (-1) = ⊥) :
    z = 1 ∨ z = -1 := by
  rcases h with h | h
  · right
    apply LinearMap.ext
    intro v
    have hv := add_apply_mem_eigenspace_one hz v
    rw [h, Submodule.mem_bot] at hv
    rw [LinearMap.neg_apply, Module.End.one_apply]
    exact eq_neg_of_add_eq_zero_right hv
  · left
    apply LinearMap.ext
    intro v
    have hv := sub_apply_mem_eigenspace_neg_one hz v
    rw [h, Submodule.mem_bot] at hv
    rw [Module.End.one_apply]
    exact (sub_eq_zero.mp hv).symm

end Eigen

theorem extraspecial_card_le {k : Type u} [Field k] (h2 : (2 : k) ≠ 0) {V : Type v}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
    {R : Subgroup (Module.End k V)ˣ} [Finite R] (hext : IsExtraspecialPGroup 2 R) {z : R}
    (hz : Subgroup.center R = Subgroup.zpowers z)
    (hzV : ((z : (Module.End k V)ˣ) : Module.End k V) = -1)
    (hV : Module.finrank k V ≤ 6) :
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ 2 ∧ Nat.card R = 2 ^ (1 + 2 * n) := by
  obtain ⟨n, hn1, hcard⟩ := PartOne.Quotient36.exists_card_eq_pow_extraspecial hext
  refine ⟨n, hn1, ?_, hcard⟩
  let ρ : Representation k R V := (Units.coeHom (Module.End k V)).comp R.subtype
  have h := SteinbergBM.pow_le_finrank_of_invariant hext hcard hz h2 ρ ⊤ top_ne_bot
    (fun _ _ _ => Submodule.mem_top) (fun w _ => by
      change ((z : (Module.End k V)ˣ) : Module.End k V) w = -w
      rw [hzV]
      rfl)
  rw [finrank_top] at h
  by_contra hn
  push Not at hn
  have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  omega

theorem commuteStmt_of_lt {k : Type u} [Field k] (h2 : (2 : k) ≠ 0) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 < p) {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (hV : Module.finrank k V ≤ 6)
    (ih : ∀ W : Submodule k V, Module.finrank k W < Module.finrank k V → CommuteStmt k p W) :
    CommuteStmt k p V := by
  classical
  intro Q hQfin hQ u hu m hum
  by_contra hcon
  push Not at hcon
  obtain ⟨q₀, hq₀, hq₀ne⟩ := hcon
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp6 : 6 < p := by
    rcases Nat.lt_or_ge 6 p with h | h
    · exact h
    · have : p = 6 := by omega
      rw [this] at hp
      exact absurd hp (by norm_num)
  let A : Subgroup (Module.End k V)ˣ := Subgroup.zpowers u
  have hAfin : Finite A :=
    finite_zpowers.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨p ^ m, pow_pos hp.pos m, hum⟩)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hum)
  have hAcard : Nat.card A = p ^ j := by rw [Nat.card_zpowers]; exact hj
  have hAp : IsPGroup p A := IsPGroup.of_card hAcard
  have hA2 : ¬ 2 ∣ Nat.card A := by
    rw [hAcard]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (Nat.prime_two.dvd_of_dvd_pow h)
    omega
  have hAQ : A ≤ Subgroup.normalizer (Q : Set (Module.End k V)ˣ) := Subgroup.zpowers_le.mpr hu
  let Good : Subgroup (Module.End k V)ˣ → Prop := fun R =>
    R ≤ Q ∧ (∀ a ∈ A, ∀ r ∈ R, a * r * a⁻¹ ∈ R) ∧ ∃ a ∈ A, ∃ r ∈ R, a * r * a⁻¹ ≠ r
  have hgood : Good Q := by
    refine ⟨le_rfl, fun a ha r hr => ?_, u, Subgroup.mem_zpowers u, q₀, hq₀, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hAQ ha) r).mp hr
    · intro h
      apply hq₀ne
      calc u * q₀ = u * q₀ * u⁻¹ * u := by group
        _ = q₀ * u := by rw [h]
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
    have hc := commute_of_isElementaryAbelian_of_normalizes h2 hp hAp (by omega) hAR a₀ ha₀ r₀
      hr₀
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
    by_cases hA : ∃ z : R, z ∈ Subgroup.center R ∧
        Module.End.eigenspace ((z : (Module.End k V)ˣ) : Module.End k V) 1 ≠ ⊥ ∧
        Module.End.eigenspace ((z : (Module.End k V)ˣ) : Module.End k V) (-1) ≠ ⊥
    ·
      obtain ⟨z, hzc, hE1, hE2⟩ := hA
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
      have huC : u ∈ C := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have := hAfix z hzc u (Subgroup.mem_zpowers u)
        calc u * z = u * z * u⁻¹ * u := by group
          _ = z * u := by rw [this]
      have hu_norm : u ∈ Subgroup.normalizer (R : Set (Module.End k V)ˣ) :=
        hAR (Subgroup.mem_zpowers u)
      have hne1 := eigenspace_ne_top_of_ne (z := ((z : (Module.End k V)ˣ) : Module.End k V))
        h1ne hE2
      have hne2 := eigenspace_ne_top_of_ne (z := ((z : (Module.End k V)ˣ) : Module.End k V))
        h1ne.symm hE1
      have hc₁ := commute_on_invariant_subspace (hCinv 1) (ih _ (Submodule.finrank_lt hne1)) hR2
        hRC huC hu_norm hum
      have hc₂ := commute_on_invariant_subspace (hCinv (-1)) (ih _ (Submodule.finrank_lt hne2))
        hR2 hRC huC hu_norm hum
      have hcu : ∀ r ∈ R, u * r = r * u := by
        intro r hr
        apply Units.ext
        rw [Units.val_mul, Units.val_mul]
        exact eq_of_eq_on_eigenspaces h2 (hsq z hzc) (fun w hw => hc₁ r hr w hw)
          (fun w hw => hc₂ r hr w hw)
      apply hmove₀
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha₀
      have := (Commute.zpow_left (show Commute u r₀ from hcu r₀ hr₀) i).eq
      rw [this, mul_inv_cancel_right]
    ·
      have hB : ∀ z : R, z ∈ Subgroup.center R →
          Module.End.eigenspace ((z : (Module.End k V)ˣ) : Module.End k V) 1 = ⊥ ∨
          Module.End.eigenspace ((z : (Module.End k V)ˣ) : Module.End k V) (-1) = ⊥ := by
        intro z hz
        by_contra hcon
        push Not at hcon
        exact hA ⟨z, hz, hcon.1, hcon.2⟩
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
      obtain ⟨n, hn1, hn2, hcardR⟩ := extraspecial_card_le h2 hext hz hz₀neg hV
      have hΦcard : Nat.card (frattini R) = 2 := by
        rw [hfc]
        exact hcard2
      have hquot : Nat.card (R ⧸ frattini R) = 2 ^ (2 * n) := by
        have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini R)
        rw [hcardR, hΦcard, pow_add, pow_one] at h
        omega
      let _ := SteinbergBY.frattiniQuotientAction A R
      have hmod := card_modEq_one_of_irreducible (A := A) (X := R ⧸ frattini R) (p := p) hAp
        hVirr hVmove
      rw [hquot] at hmod
      have hdvd : p ∣ 2 ^ (2 * n) - 1 := (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp hmod.symm
      interval_cases n
      · have h3 : p ∣ 3 := by simpa using hdvd
        have := Nat.le_of_dvd (by norm_num) h3
        omega
      · have h15 : p ∣ 3 * 5 := by simpa using hdvd
        rcases (Nat.Prime.dvd_mul hp).mp h15 with h3 | h5
        · have := Nat.le_of_dvd (by norm_num) h3
          omega
        · have := Nat.le_of_dvd (by norm_num) h5
          omega

theorem commuteStmt_of_finrank_le_six {k : Type u} [Field k] (h2 : (2 : k) ≠ 0) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 < p) :
    ∀ (n : ℕ) (V : Type v) [AddCommGroup V] [Module k V] [FiniteDimensional k V],
      Module.finrank k V = n → n ≤ 6 → CommuteStmt k p V := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V _ _ _ hn hn6
    refine commuteStmt_of_lt h2 hp hp5 (by omega) fun W hW => ?_
    exact ih (Module.finrank k W) (hn ▸ hW) W rfl (by omega)

end CFSG.RankThree.PartOne.DegreeSixInduction

module

public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockSpTwoPart

public section

namespace CFSG.StandardType

open CFSG.StandardType.ClassicalBlocks Matrix

private lemma pslGraphArith_pow_eq_of_sub_one_eq {q x : ℕ} (hq : 1 < q) (hx : 1 ≤ x)
    (h : q ^ x - 1 = q - 1) : x = 1 := by
  by_contra hx1
  have hx2 : 2 ≤ x := by omega
  have hlt : q ^ 1 < q ^ x := Nat.pow_lt_pow_right hq hx2
  rw [pow_one] at hlt
  have hqx : q ^ x = q := by omega
  omega

private lemma pslGraphArith_factor_ge_one {ι : Type} (q : ℕ) (kind d : ι → ℕ) (r : ι)
    (hq : 2 ≤ q) (hd : 1 ≤ d r)
    (hII : kind r = 1 → Even (d r)) :
    1 ≤ (if kind r = 1 then q ^ (d r / 2) - 1 else q ^ d r - 1) := by
  by_cases h : kind r = 1
  · rw [if_pos h]
    have hdr : 1 ≤ d r := hd
    obtain ⟨k, hk⟩ := hII h
    have hkpos : k ≠ 0 := by omega
    have hd2 : d r = 2 * k := by omega
    have hdiv : d r / 2 = k := by
      rw [hd2, Nat.mul_div_right k (by norm_num : 0 < 2)]
    have hpow : 2 ≤ q ^ (d r / 2) := by
      rw [hdiv]
      calc 2 ≤ q := hq
        _ ≤ q ^ k := Nat.le_self_pow hkpos q
    omega
  · rw [if_neg h]
    have hdr : 1 ≤ d r := hd
    have hpow : 2 ≤ q ^ d r := by
      calc 2 ≤ q := hq
        _ ≤ q ^ d r := Nat.le_self_pow (by omega : d r ≠ 0) q
    omega

private lemma pslGraphArith_factor_ge_q_sub_one {ι : Type} (q : ℕ) (kind d : ι → ℕ) (r : ι)
    (hq : 2 ≤ q) (hd : 1 ≤ d r)
    (hII : kind r = 1 → Even (d r)) :
    q - 1 ≤ (if kind r = 1 then q ^ (d r / 2) - 1 else q ^ d r - 1) := by
  by_cases h : kind r = 1
  · rw [if_pos h]
    have hdr : 1 ≤ d r := hd
    obtain ⟨k, hk⟩ := hII h
    have hkpos : k ≠ 0 := by omega
    have hd2 : d r = 2 * k := by omega
    have hdiv : d r / 2 = k := by
      rw [hd2, Nat.mul_div_right k (by norm_num : 0 < 2)]
    have hpow : q ≤ q ^ (d r / 2) := by
      rw [hdiv]
      exact Nat.le_self_pow hkpos q
    omega
  · rw [if_neg h]
    have hdr : 1 ≤ d r := hd
    have hpow : q ≤ q ^ d r := Nat.le_self_pow (by omega : d r ≠ 0) q
    omega

theorem pslGraph_arith {ι : Type} (q n f : ℕ) (hq : q = 2 ^ f) (hf : 1 ≤ f)
    (R : Finset ι) (kind d rk : ι → ℕ)
    (hkind : ∀ r ∈ R, kind r ≤ 2) (hd : ∀ r ∈ R, 1 ≤ d r)
    (hII : ∀ r ∈ R, kind r = 1 → Even (d r))
    (hn : n = ∑ r ∈ R, (if kind r = 2 then 2 else 1) * rk r)
    (hbound : ∏ r ∈ R, (if kind r = 1 then q ^ (d r / 2) - 1 else q ^ d r - 1) ≤
      (q - 1) * Nat.gcd n (q - 1))
    (hI : ∃ r ∈ R, kind r = 0 ∧ rk r = 2 * d r ∧ 4 ≤ q ^ d r)
    (hne : ∃ r ∈ R, kind r ≠ 0)
    (hno : ∀ r ∈ R, kind r ≠ 0 → 4 ≤ q ^ d r → rk r = d r) : False := by
  classical
  have hfne : f ≠ 0 := by omega
  have hqeven : Even q := by
    rw [hq]
    exact (Nat.even_pow).2 ⟨even_two, hfne⟩
  have hq2 : 2 ≤ q := by
    rw [hq]
    exact Nat.le_self_pow hfne 2
  let ρ : ι → ℕ := fun r =>
    if kind r = 1 then q ^ (d r / 2) - 1 else q ^ d r - 1
  have hρ_one : ∀ r ∈ R, 1 ≤ ρ r := by
    intro r hr
    exact pslGraphArith_factor_ge_one q kind d r hq2 (hd r hr) (hII r hr)
  have hρ_ge : ∀ r ∈ R, q - 1 ≤ ρ r := by
    intro r hr
    exact pslGraphArith_factor_ge_q_sub_one q kind d r hq2 (hd r hr) (hII r hr)
  obtain ⟨r0, hr0R, hk0, hrk0, hq0⟩ := hI
  obtain ⟨r1, hr1R, hk1ne⟩ := hne
  have hr10 : r1 ≠ r0 := by
    intro h
    apply hk1ne
    rw [h]
    exact hk0
  have hr01 : r0 ≠ r1 := fun h => hr10 h.symm
  by_cases hqeq : q = 2
  · have hρr0 : 3 ≤ ρ r0 := by
      dsimp [ρ]
      rw [if_neg (by omega : kind r0 ≠ 1)]
      omega
    have hle : ρ r0 ≤ ∏ r ∈ R, ρ r := Finset.single_le_prod hρ_one hr0R
    have hrhs : (q - 1) * Nat.gcd n (q - 1) = 1 := by
      rw [hqeq]
      simp
    have hboundρ : (∏ r ∈ R, ρ r) ≤ (q - 1) * Nat.gcd n (q - 1) := hbound
    omega
  · have hq4 : 4 ≤ q := by
      have hq3 : 3 ≤ q := by omega
      obtain ⟨m, hm⟩ := hqeven
      have hm2 : 2 ≤ m := by omega
      omega
    have hρr0 : ρ r0 = q ^ d r0 - 1 := by
      dsimp [ρ]
      rw [if_neg (by omega : kind r0 ≠ 1)]
    have hρr0_ge : q - 1 ≤ ρ r0 := hρ_ge r0 hr0R
    have hρr1_ge : q - 1 ≤ ρ r1 := hρ_ge r1 hr1R
    have hsplit0 : (∏ r ∈ R.erase r0, ρ r) * ρ r0 = ∏ r ∈ R, ρ r :=
      Finset.prod_erase_mul R ρ hr0R
    have hr1erase : r1 ∈ R.erase r0 := by
      rw [Finset.mem_erase]
      exact ⟨hr10, hr1R⟩
    have hrest : ρ r1 ≤ ∏ r ∈ R.erase r0, ρ r :=
      Finset.single_le_prod
        (fun r hr => hρ_one r (Finset.mem_of_mem_erase hr)) hr1erase
    have hpair_le_P : ρ r0 * ρ r1 ≤ ∏ r ∈ R, ρ r := by
      calc ρ r0 * ρ r1 = ρ r1 * ρ r0 := by rw [mul_comm]
        _ ≤ (∏ r ∈ R.erase r0, ρ r) * ρ r0 := Nat.mul_le_mul_right (ρ r0) hrest
        _ = ∏ r ∈ R, ρ r := hsplit0
    have hpair_lower : (q - 1) * (q - 1) ≤ ρ r0 * ρ r1 :=
      Nat.mul_le_mul hρr0_ge hρr1_ge
    have hgcdle : Nat.gcd n (q - 1) ≤ q - 1 :=
      Nat.gcd_le_right n (by omega : 0 < q - 1)
    have hboundρ : (∏ r ∈ R, ρ r) ≤ (q - 1) * Nat.gcd n (q - 1) := hbound
    have hP_upper : (∏ r ∈ R, ρ r) ≤ (q - 1) * (q - 1) :=
      hboundρ.trans (Nat.mul_le_mul_left (q - 1) hgcdle)
    have hP_eq : (∏ r ∈ R, ρ r) = (q - 1) * (q - 1) :=
      le_antisymm hP_upper (le_trans hpair_lower hpair_le_P)
    have hpair_upper : ρ r0 * ρ r1 ≤ (q - 1) * (q - 1) :=
      le_trans hpair_le_P (le_of_eq hP_eq)
    have hpair_eq : ρ r0 * ρ r1 = (q - 1) * (q - 1) :=
      le_antisymm hpair_upper hpair_lower
    have hapos : 0 < q - 1 := by omega
    have hρr1_eq : ρ r1 = q - 1 := by
      have h1 : (q - 1) * ρ r1 ≤ (q - 1) * (q - 1) := by
        calc (q - 1) * ρ r1 ≤ ρ r0 * ρ r1 := Nat.mul_le_mul_right (ρ r1) hρr0_ge
          _ = (q - 1) * (q - 1) := hpair_eq
      exact le_antisymm (Nat.le_of_mul_le_mul_left h1 hapos) hρr1_ge
    have hρr0_eq : ρ r0 = q - 1 := by
      have h1 : ρ r0 * (q - 1) = (q - 1) * (q - 1) := by
        simpa [hρr1_eq] using hpair_eq
      exact Nat.mul_right_cancel hapos h1
    have hd0 : d r0 = 1 := by
      have h : q ^ d r0 - 1 = q - 1 := by
        rw [← hρr0]
        exact hρr0_eq
      exact pslGraphArith_pow_eq_of_sub_one_eq (by omega : 1 < q) (hd r0 hr0R) h
    have hrest_eq_one : (∏ r ∈ (R.erase r0).erase r1, ρ r) = 1 := by
      have hsplit1 : (∏ r ∈ (R.erase r0).erase r1, ρ r) * ρ r1 =
          ∏ r ∈ R.erase r0, ρ r :=
        Finset.prod_erase_mul (R.erase r0) ρ hr1erase
      have hPsplit : (∏ r ∈ (R.erase r0).erase r1, ρ r) * (ρ r1 * ρ r0) =
          (q - 1) * (q - 1) := by
        rw [← mul_assoc, hsplit1, hsplit0, hP_eq]
      rw [hρr1_eq, hρr0_eq] at hPsplit
      have h1 : (∏ r ∈ (R.erase r0).erase r1, ρ r) * ((q - 1) * (q - 1)) =
          1 * ((q - 1) * (q - 1)) := by
        simpa using hPsplit
      exact Nat.mul_right_cancel (Nat.mul_pos hapos hapos) h1
    have hRsub : R ⊆ ({r0, r1} : Finset ι) := by
      intro r hr
      by_contra hnot
      have hrne0 : r ≠ r0 := by
        intro h
        apply hnot
        rw [h]
        simp
      have hrne1 : r ≠ r1 := by
        intro h
        apply hnot
        rw [h]
        simp
      have hrmem : r ∈ (R.erase r0).erase r1 := by
        simp [Finset.mem_erase, hr, hrne0, hrne1]
      have hle : ρ r ≤ ∏ x ∈ (R.erase r0).erase r1, ρ x :=
        Finset.single_le_prod
          (fun x hx => hρ_one x (Finset.mem_of_mem_erase
            (Finset.mem_of_mem_erase hx))) hrmem
      rw [hrest_eq_one] at hle
      have hge : q - 1 ≤ ρ r := hρ_ge r hr
      omega
    have hR : R = ({r0, r1} : Finset ι) := by
      refine Finset.Subset.antisymm hRsub ?_
      intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact hr0R
      · exact hr1R
    have hqpow1 : 4 ≤ q ^ d r1 := by
      have hdr1 : 1 ≤ d r1 := hd r1 hr1R
      have hle : q ≤ q ^ d r1 :=
        Nat.le_self_pow (by omega : d r1 ≠ 0) q
      omega
    have hrk1 : rk r1 = d r1 := hno r1 hr1R hk1ne hqpow1
    have hk1cases : kind r1 = 1 ∨ kind r1 = 2 := by
      have hle := hkind r1 hr1R
      omega
    have hsum4 : n = 4 := by
      rcases hk1cases with hk1 | hk1
      · have hfac : q ^ (d r1 / 2) - 1 = q - 1 := by
          have h := hρr1_eq
          dsimp [ρ] at h
          rw [if_pos hk1] at h
          exact h
        have hx1 : 1 ≤ d r1 / 2 := by
          obtain ⟨k, hk⟩ := hII r1 hr1R hk1
          have hdr : 1 ≤ d r1 := hd r1 hr1R
          have hkpos : 1 ≤ k := by omega
          have hd2 : d r1 = 2 * k := by omega
          rw [hd2, Nat.mul_div_right k (by norm_num : 0 < 2)]
          exact hkpos
        have hhalf : d r1 / 2 = 1 :=
          pslGraphArith_pow_eq_of_sub_one_eq (by omega : 1 < q) hx1 hfac
        have hd1 : d r1 = 2 := by
          obtain ⟨k, hk⟩ := hII r1 hr1R hk1
          have hd2 : d r1 = 2 * k := by omega
          have hk1eq : k = 1 := by
            rw [hd2, Nat.mul_div_right k (by norm_num : 0 < 2)] at hhalf
            exact hhalf
          rw [hd2, hk1eq]
        rw [hn, hR]
        simp [hr01, hk0, hk1, hrk0, hd0, hd1, hrk1]
      · have hfac : q ^ d r1 - 1 = q - 1 := by
          have h := hρr1_eq
          dsimp [ρ] at h
          rw [if_neg (by omega : kind r1 ≠ 1)] at h
          exact h
        have hd1 : d r1 = 1 :=
          pslGraphArith_pow_eq_of_sub_one_eq (by omega : 1 < q) (hd r1 hr1R) hfac
        rw [hn, hR]
        simp [hr01, hk0, hk1, hrk0, hd0, hd1, hrk1]
    have hgcd_eq : Nat.gcd n (q - 1) = q - 1 := by
      have hle1 : (q - 1) * (q - 1) ≤ (q - 1) * Nat.gcd n (q - 1) := by
        rw [← hP_eq]
        exact hboundρ
      have hle2 : q - 1 ≤ Nat.gcd n (q - 1) :=
        Nat.le_of_mul_le_mul_left hle1 hapos
      exact le_antisymm hgcdle hle2
    have hdiv : q - 1 ∣ n := (Nat.gcd_eq_right_iff_dvd).1 hgcd_eq
    have hdiv4 : q - 1 ∣ 4 := by
      rw [hsum4] at hdiv
      exact hdiv
    have hodd : Odd (q - 1) := by
      refine ⟨2 ^ (f - 1) - 1, ?_⟩
      have hf' : f - 1 + 1 = f := Nat.sub_add_cancel hf
      have hq' : q = 2 * 2 ^ (f - 1) := by
        calc q = 2 ^ f := hq
          _ = 2 ^ (f - 1 + 1) := by rw [hf']
          _ = 2 ^ (f - 1) * 2 := by rw [pow_succ]
          _ = 2 * 2 ^ (f - 1) := by rw [Nat.mul_comm]
      have ht : 1 ≤ 2 ^ (f - 1) := Nat.one_le_pow _ _ (by norm_num : 1 ≤ 2)
      rw [hq']
      omega
    have ha3 : 3 ≤ q - 1 := by omega
    have hle4 : q - 1 ≤ 4 := Nat.le_of_dvd (by norm_num) hdiv4
    have hcases : q - 1 = 3 ∨ q - 1 = 4 := by omega
    rcases hcases with h3 | h4
    · rw [h3] at hdiv4
      norm_num at hdiv4
    · obtain ⟨k, hk⟩ := hodd
      omega

private lemma pslGraphNormII_theta_order {F : Type} [Field F] (θ : F ≃+* F)
    (hθ2 : θ * θ = 1) (hθ1 : θ ≠ 1) : orderOf θ = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by simpa [pow_two] using hθ2) hθ1

private lemma pslGraphNormII_card_range_pow {G : Type} [CommGroup G] [Finite G] [IsCyclic G]
    {d : ℕ} (hd : d ∣ Nat.card G) :
    Nat.card (Set.range (fun x : G => x ^ d)) = Nat.card G / d := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := G)
  have htop : Subgroup.zpowers g = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hg]
  have hrange : (powMonoidHom d : G →* G).range = Subgroup.zpowers (g ^ d) := by
    rw [MonoidHom.range_eq_map, show (⊤ : Subgroup G) = Subgroup.zpowers g from htop.symm,
      MonoidHom.map_zpowers, powMonoidHom_apply]
  have hset : Set.range (fun x : G => x ^ d) = (Subgroup.zpowers (g ^ d) : Set G) := by
    rw [← hrange]
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact MonoidHom.mem_range.mpr ⟨x, by rw [powMonoidHom_apply]⟩
    · intro hy
      change y ∈ (powMonoidHom d).range at hy
      rw [MonoidHom.mem_range] at hy
      obtain ⟨x, hx⟩ := hy
      exact Set.mem_range.mpr ⟨x, by rwa [powMonoidHom_apply] at hx⟩
  rw [hset]
  change Nat.card ↥(Subgroup.zpowers (g ^ d)) = Nat.card G / d
  rw [Nat.card_zpowers, orderOf_pow, hg, Nat.gcd_eq_right hd]

private lemma pslGraphNormII_card_norm_range {F : Type} [Field F] (θ : F ≃+* F) (Q : ℕ)
    (hpow : ∀ x : F, θ x = x ^ Q) :
    Nat.card (Set.range (fun t : Fˣ => θ (t : F) * (t : F))) =
      Nat.card (Set.range (fun t : Fˣ => t ^ (Q + 1))) := by
  have hfun : (fun t : Fˣ => θ (t : F) * (t : F)) =
      fun t : Fˣ => ((t ^ (Q + 1) : Fˣ) : F) := by
    funext t
    rw [hpow (t : F), Units.val_pow_eq_pow_val, pow_succ]
  rw [hfun]
  have hcomp : (fun t : Fˣ => ((t ^ (Q + 1) : Fˣ) : F)) =
      (fun u : Fˣ => (u : F)) ∘ (fun t : Fˣ => t ^ (Q + 1)) := rfl
  rw [hcomp, Set.range_comp]
  exact Nat.card_image_of_injective (f := (fun u : Fˣ => (u : F)))
    (fun _ _ h => Units.ext h) _

theorem pslGraph_norm_card_II {F : Type} [Field F] [Finite F] (θ : F ≃+* F) (hθ2 : θ * θ = 1)
    (hθ1 : θ ≠ 1) :
    ∃ Q : ℕ, Nat.card F = Q * Q ∧
      Nat.card (Set.range (fun t : Fˣ => θ (t : F) * (t : F))) = Q - 1 := by
  classical
  let K : Subfield F := FixedPoints.subfield (Subgroup.zpowers θ) F
  let Q : ℕ := Nat.card K
  have horder : orderOf θ = 2 := pslGraphNormII_theta_order θ hθ2 hθ1
  have hcard : Nat.card F = Q * Q := by
    have h := CFSG.GorensteinWalter.nat_card_eq_fixedSubfield_card_pow_orderOf F θ
    rw [h, horder]
    dsimp only [Q, K]
    ring
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Module.Finite K F := Module.Finite.of_finite
  haveI : Algebra.IsAlgebraic K F := Algebra.IsAlgebraic.of_finite K F
  let θA : F ≃ₐ[K] F :=
    AlgEquiv.ofRingEquiv (f := θ) (fun x => by
      have hx : (⟨θ, Subgroup.mem_zpowers θ⟩ : Subgroup.zpowers θ) • (x : F) = (x : F) :=
        x.2 ⟨θ, Subgroup.mem_zpowers θ⟩
      change θ (x : F) = (x : F)
      simpa [RingHom.smul_def] using hx)
  let φA : F ≃ₐ[K] F := FiniteField.frobeniusAlgEquivOfAlgebraic K F
  have hφx : ∀ x : F, φA x = x ^ Q := by
    intro x
    rw [FiniteField.frobeniusAlgEquivOfAlgebraic_apply]
    dsimp only [Q]
    rw [Nat.card_eq_fintype_card]
  have hθA2 : θA * θA = 1 := by
    ext x
    rw [AlgEquiv.mul_apply, AlgEquiv.one_apply]
    change θ (θ x) = x
    simpa [Equiv.trans_apply] using congrFun (congrArg DFunLike.coe hθ2) x
  have hφA2 : φA * φA = 1 := by
    ext x
    rw [AlgEquiv.mul_apply, AlgEquiv.one_apply, hφx, hφx, ← pow_mul]
    have hF : Fintype.card F = Q * Q := by
      rw [← Nat.card_eq_fintype_card, hcard]
    rw [← hF, FiniteField.pow_card]
  have hθA1 : θA ≠ 1 := by
    intro h
    apply hθ1
    ext x
    exact congrArg (fun e : F ≃ₐ[K] F => e x) h
  have hφA1 : φA ≠ 1 := by
    intro hφ1
    haveI : IsCyclic Fˣ := inferInstance
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
    have hgQ : g ^ Q = g := by
      apply Units.ext
      have h := congrArg (fun e : F ≃ₐ[K] F => e (g : F)) hφ1
      simp only [AlgEquiv.one_apply] at h
      rw [hφx] at h
      exact h
    have hQ2 : 1 < Q := by
      have : Nontrivial K := inferInstance
      exact Finite.one_lt_card
    have hg1 : g ^ (Q - 1) = 1 := by
      have hQ1 : Q - 1 + 1 = Q := by omega
      have h2 : g ^ (Q - 1) * g = 1 * g := by
        rw [← pow_succ, hQ1, hgQ, one_mul]
      exact mul_right_cancel h2
    have hdvd : orderOf g ∣ Q - 1 := orderOf_dvd_of_pow_eq_one hg1
    rw [hg, Nat.card_units, hcard] at hdvd
    have hle := Nat.le_of_dvd (by omega : 0 < Q - 1) hdvd
    have hQQ : Q * Q - 1 = (Q - 1) * (Q + 1) := by
      have h := Nat.pow_two_sub_pow_two Q 1
      simpa [pow_two, one_pow, mul_comm] using h
    rw [hQQ] at hle
    have hge : 2 * (Q - 1) ≤ (Q - 1) * (Q + 1) := by
      rw [mul_comm (Q - 1) (Q + 1)]
      exact Nat.mul_le_mul_right _ (by omega : 2 ≤ Q + 1)
    omega
  have hθφ : θA = φA := by
    haveI : IsCyclic (F ≃ₐ[K] F) := inferInstance
    haveI : Finite (F ≃ₐ[K] F) :=
      Finite.of_injective (fun e : F ≃ₐ[K] F => (e : F → F)) DFunLike.coe_injective
    haveI : Fintype (F ≃ₐ[K] F) := Fintype.ofFinite _
    by_contra hne
    have hle := IsCyclic.card_pow_eq_one_le (α := F ≃ₐ[K] F) (n := 2) (by norm_num)
    have hsub : ({1, θA, φA} : Finset (F ≃ₐ[K] F)) ⊆
        Finset.univ.filter (fun a : F ≃ₐ[K] F => a ^ 2 = 1) := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases ha with rfl | rfl | rfl
      · exact one_pow 2
      · rw [sq, hθA2]
      · rw [sq, hφA2]
    have hcard3 : ({1, θA, φA} : Finset (F ≃ₐ[K] F)).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair (a := θA) (b := φA) hne]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hθA1, Ne.symm hφA1⟩
    have := Finset.card_le_card hsub
    omega
  have hθpow : ∀ x : F, θ x = x ^ Q := by
    intro x
    have hx : θ x = φA x := congrArg (fun e : F ≃ₐ[K] F => e x) hθφ
    rw [hx, hφx]
  refine ⟨Q, hcard, ?_⟩
  rw [pslGraphNormII_card_norm_range θ Q hθpow]
  haveI : IsCyclic Fˣ := inferInstance
  have hQQ : Q * Q - 1 = (Q - 1) * (Q + 1) := by
    have h := Nat.pow_two_sub_pow_two Q 1
    simpa [pow_two, one_pow, mul_comm] using h
  have hdvd : Q + 1 ∣ Nat.card Fˣ := by
    rw [Nat.card_units, hcard, hQQ]
    exact dvd_mul_left (Q + 1) (Q - 1)
  rw [pslGraphNormII_card_range_pow hdvd]
  rw [Nat.card_units, hcard, hQQ]
  rw [Nat.mul_div_left _ (by omega : 0 < Q + 1)]

end CFSG.StandardType

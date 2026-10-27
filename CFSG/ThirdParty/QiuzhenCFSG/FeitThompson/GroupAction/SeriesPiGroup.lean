module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.Defs

namespace CFSG
end CFSG
open CFSG

lemma CFSG.not_dvd_card_of_isPiGroup_of_prime_notMem (π : Set Nat.Primes) (G : Type*) [Group G] [Finite G]
    (hpi : IsPiGroup π G) (p : Nat.Primes) (hp : p ∉ π) : ¬ p.val ∣ Nat.card G := by
  rw [IsPiGroup_iff] at hpi
  exact fun hdiv => hp (hpi p hdiv)


/-- If `H` is invariant under the action of `A`, then it is also invariant under any subgroup of `A`. -/
instance CFSG.IsInvariant.subgroup {A G : Type*} [Group A] [Group G] [SMul A G] (H : Subgroup G) [IsInvariant A G H]
    (B : Subgroup A) : IsInvariant B G H where
  invariant a g := IsInvariant.invariant (A := A) (G := G) (H := H) a g

lemma CFSG.actsTriviallyOn_subgroup_of_smul_div_mem_and_coprime {G A : Type _} [Group G] [Finite G] [Group A] [Finite A] [MulDistribMulAction A G]
    (p : ℕ) (hp : Nat.Prime p) (H K : Subgroup G)
    [IsInvariant A G H] [IsInvariant A G K]
    (hP : IsPGroup p A) (hcoprime : Nat.Coprime p (Nat.card H))
    (htriv_factor : ∀ a : A, ∀ g : G, g ∈ K → (a • g) * g⁻¹ ∈ H)
    (htriv_H : ∀ a : A, ∀ g : G, g ∈ H → a • g = g) :
    ∀ a : A, ∀ g : G, g ∈ K → a • g = g := by
  have hp_fact : Fact (Nat.Prime p) := ⟨hp⟩
  intro a g hgK
  -- define x = (a • g) * g⁻¹, which lies in H
  set x := (a • g) * g⁻¹ with hx_def
  have hxH : x ∈ H := htriv_factor a g hgK
  -- a fixes x because x ∈ H and A acts trivially on H
  have hax : a • x = x := htriv_H a x hxH
  -- powers of x also belong to H
  have hx_pow_mem : ∀ n : ℕ, x ^ n ∈ H := fun n => pow_mem hxH n
  -- a fixes each power of x
  have hax_pow : ∀ n : ℕ, a • (x ^ n) = x ^ n := fun n => htriv_H a (x ^ n) (hx_pow_mem n)
  -- formula: a ^ n • g = x ^ n * g
  have formula : ∀ n : ℕ, a ^ n • g = x ^ n * g := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          a ^ (n + 1) • g = a • (a ^ n • g) := by rw [pow_succ', smul_smul]
          _ = a • (x ^ n * g) := by rw [ih]
          _ = (a • (x ^ n)) * (a • g) := by rw [MulDistribMulAction.smul_mul]
          _ = (x ^ n) * (a • g) := by rw [hax_pow n]
          _ = (x ^ n) * ((a • g) * 1) := by simp
          _ = (x ^ n) * ((a • g) * (g⁻¹ * g)) := by group
          _ = (x ^ n) * (((a • g) * g⁻¹) * g) := by group
          _ = (x ^ n) * (x * g) := by rw [hx_def]
          _ = (x ^ n * x) * g := by rw [← mul_assoc]
          _ = (x ^ (n + 1)) * g := by rw [← pow_succ x n]
  -- Since A is a p-group, the order of a is a power of p
  have h_order_a : ∃ k : ℕ, orderOf a = p ^ k := by
    have h := (IsPGroup.iff_orderOf (p := p)).mp hP
    exact h a
  rcases h_order_a with ⟨k, hk⟩
  have ha_order : a ^ orderOf a = 1 := pow_orderOf_eq_one a
  have h_smul_eq : a ^ orderOf a • g = g := by
    rw [ha_order, one_smul]
  -- apply formula at orderOf a
  have h_formula_order := formula (orderOf a)
  rw [h_smul_eq] at h_formula_order
  -- we have g = x^(orderOf a) * g, hence x^(orderOf a) = 1
  have hx_pow_eq_one : x ^ orderOf a = 1 := by
    have := congrArg (fun t : G => t * g⁻¹) h_formula_order
    simp [mul_assoc] at this
    exact this.symm
  -- The order of x divides orderOf a
  have h_order_x_dvd : orderOf x ∣ orderOf a := by
    apply orderOf_dvd_of_pow_eq_one hx_pow_eq_one
  -- The order of x divides Nat.card H (since x ∈ H)
  have h_order_x_dvd_card : orderOf x ∣ Nat.card H := by
    exact Subgroup.orderOf_dvd_natCard H hxH
  -- Since p is coprime to Nat.card H, p is coprime to orderOf x
  have h_coprime' : Nat.Coprime p (orderOf x) := by
    apply Nat.Coprime.coprime_dvd_right h_order_x_dvd_card hcoprime
  -- orderOf a is a power of p
  have h_order_a_pow : orderOf a = p ^ k := hk
  -- orderOf x divides p ^ k
  have h_order_x_dvd_pow : orderOf x ∣ p ^ k := by
    rw [← h_order_a_pow]
    exact h_order_x_dvd
  -- Since orderOf x divides a prime power, it is itself a power of p
  rcases (Nat.dvd_prime_pow hp).mp h_order_x_dvd_pow with ⟨l, hl, h_order_x_eq⟩
  -- h_order_x_eq: orderOf x = p ^ l
  -- But p is coprime to orderOf x, so p does not divide orderOf x
  have h_coprime_pow : Nat.Coprime p (p ^ l) := by rwa [h_order_x_eq] at h_coprime'
  -- Since p is prime, Coprime p (p ^ l) forces l = 0
  have hl0 : l = 0 := by
    by_cases hl0' : l = 0
    · exact hl0'
    · have hpos : 0 < l := Nat.pos_of_ne_zero hl0'
      have h_dvd : p ∣ p ^ l := dvd_pow_self p hpos.ne'
      have h_not_dvd : ¬ p ∣ p ^ l := hp.coprime_iff_not_dvd.mp h_coprime_pow
      exfalso
      exact h_not_dvd h_dvd
  -- Therefore orderOf x = p ^ 0 = 1
  have h_order_x_eq_one : orderOf x = 1 := by
    rw [h_order_x_eq, hl0, pow_zero]
  -- Therefore x = 1
  have hx_eq_one : x = 1 := by
    rw [← pow_one x, ← h_order_x_eq_one, pow_orderOf_eq_one]
  -- Now compute a • g = x * g = 1 * g = g
  calc
    a • g = x * g := by
      rw [hx_def]; group
    _ = 1 * g := by rw [hx_eq_one]
    _ = g := by simp


/-
**Kind**: Theorem
**Note**: Lemma 1.9
**Stmt**:
Let $\pi$ be a set of primes.
Let $G$ be a finite solvable $\pi$-group.
Let $A$ be an operator group on $G$ that stablizes a normal series of $G$.
Then $A/C_A(G)$ is a $\pi$-group.
-/

-- TODO(tianjiao): how to handle the normal assumption
public theorem CFSG.isPiGroup_quotient_fixingSubgroup_of_stabilizesNormalSeries {G A : Type*} [Group G] [Finite G] [Group A] [Finite A] [MulDistribMulAction A G]
    (π : Set Nat.Primes) (hsolv : Group.IsSolvable G) (hpi : IsPiGroup (π := π) G)
    (hstab : ∃ (ι : Type*) (Gi : ι → Subgroup G) (next : ι → ι),
      StabilizesNormalSeries (G := G) (A := A) Gi next)
    (hker : (fixingSubgroupOf A G (Set.univ : Set G)).Normal) :
    IsPiGroup (π := π) (A ⧸ fixingSubgroupOf A G (Set.univ : Set G)) := by
  let _ := hsolv
  let K := fixingSubgroupOf A G Set.univ
  have hK_normal : K.Normal := hker
  have hK_triv : ∀ a ∈ K, ∀ g : G, a • g = g := by
    intro a ha g
    exact (mem_fixingSubgroup_iff (M := A) (s := Set.univ)).mp ha g (Set.mem_univ g)
  let Q := A ⧸ K
  have hQ_finite : Finite Q := by infer_instance
  let φ : A →* MulAut G := MulDistribMulAction.toMulAut (G := A) (M := G)
  have hφ_ker : φ.ker = K := by
    ext a
    constructor
    · intro ha
      have ha' : φ a = 1 := ha
      have h : ∀ g, φ a g = g := fun g => by
        rw [ha', MulAut.one_apply]
      have h' : ∀ g, a • g = g := fun g => by
        change φ a g = g
        exact h g
      exact (mem_fixingSubgroup_iff (M := A) (s := Set.univ)).mpr (fun g _ => h' g)
    · intro ha
      have h : ∀ g, a • g = g := hK_triv a ha
      have ha' : φ a = 1 := by
        ext g
        exact h g
      exact ha'
  have hφ_lift : K ≤ φ.ker := by rw [hφ_ker]
  let hK_normal_inst : K.Normal := hK_normal
  have hφker_normal : φ.ker.Normal := MonoidHom.normal_ker φ
  let ψ' : A ⧸ φ.ker →* MulAut G := QuotientGroup.kerLift φ
  have ψ'_inj : Function.Injective ψ' := QuotientGroup.kerLift_injective φ
  let e : Q ≃* A ⧸ φ.ker := (QuotientGroup.quotientMulEquivOfEq hφ_ker).symm
  let ψ : Q →* MulAut G := ψ'.comp e.toMonoidHom
  have ψ_inj : Function.Injective ψ := ψ'_inj.comp e.injective
  let instMD : MulDistribMulAction Q G := MulDistribMulAction.compHom G ψ
  have smul_def : ∀ a : Q, ∀ g : G, a • g = (ψ a) • g := by
    intro a g
    exact MulAction.compHom_smul_def ψ a g
  have faithful : ∀ aQ : Q, (∀ g : G, aQ • g = g) → aQ = 1 := by
    intro aQ h
    apply ψ_inj
    ext g
    have h_smul : aQ • g = (ψ aQ) g := by
      rw [smul_def aQ g, MulAut.smul_def]
    simpa [h_smul] using h g
  rcases hstab with ⟨ι, Gi, next, hstab⟩
  rcases hstab with ⟨⟨top, bottom, htop, hbottom, ⟨n, hn⟩⟩, hdesc, hnormal, hinv, hfactor⟩
  have smul_eq : ∀ (a : A) (g : G), ((a : Q) • g) = a • g := by
    intro a g
    calc
      ((a : Q) • g) = (ψ (a : Q)) • g := smul_def (a : Q) g
      _ = (ψ (a : Q)) g := by simp [MulAut.smul_def]
      _ = (φ a) g := by
        calc
          (ψ (a : Q)) g = (ψ' (e (a : Q))) g := rfl
          _ = (ψ' (QuotientGroup.mk a)) g := by
            have H : e (a : Q) = QuotientGroup.mk a := by
              simp [e, QuotientGroup.quotientMulEquivOfEq, Subgroup.quotientEquivOfEq]
            simp [H]
          _ = (φ a) g := by simp only [ψ', QuotientGroup.kerLift_mk]
      _ = a • g := rfl
  have hinvQ : ∀ i, IsInvariant Q G (Gi i) := by
    intro i
    constructor
    intro aQ g
    refine QuotientGroup.induction_on aQ (fun a => ?_)
    constructor
    · intro hg
      have hg' := (IsInvariant.invariant (A := A) (G := G) (H := Gi i) a g).1 hg
      simpa [smul_eq] using hg'
    · intro hg
      have hg' : a • g ∈ Gi i := by simpa [smul_eq] using hg
      exact (IsInvariant.invariant (A := A) (G := G) (H := Gi i) a g).2 hg'
  have hfactorQ : ∀ i (aQ : Q) (g : G), g ∈ Gi i → (aQ • g) * g⁻¹ ∈ Gi (next i) := by
    intro i aQ g hg
    refine QuotientGroup.induction_on aQ (fun a => ?_)
    simpa [smul_eq] using hfactor i a g hg
  have hstabQ : StabilizesNormalSeries (G := G) (A := Q) Gi next :=
    ⟨⟨top, bottom, htop, hbottom, ⟨n, hn⟩⟩, hdesc, hnormal, hinvQ, hfactorQ⟩
  rw [IsPiGroup_iff]
  intro p hp
  by_cases h : p.val ∣ Nat.card Q
  · by_cases h_not : p ∉ π
    · have h_coprime_G' : ¬ p.val ∣ Nat.card G := not_dvd_card_of_isPiGroup_of_prime_notMem π G hpi p h_not
      have hp_prime : Nat.Prime p.val := p.2
      have h_coprime_G : Nat.Coprime p.val (Nat.card G) :=
        (hp_prime.coprime_iff_not_dvd).mpr h_coprime_G'
      have hp_prime_fact : Fact (Nat.Prime p.val) := ⟨hp_prime⟩
      rcases Sylow.nonempty (p := p.val) (G := Q) with ⟨P⟩
      have hP_pgroup : IsPGroup p.val P := P.isPGroup'
      let P' : Subgroup Q := P
      have hinvP : ∀ i, IsInvariant P' G (Gi i) := fun i => IsInvariant.subgroup (Gi i) P'
      have hfactorP : ∀ i (a : P') (g : G), g ∈ Gi i → (a • g) * g⁻¹ ∈ Gi (next i) := by
        intro i a g hg
        exact hfactorQ i a g hg
      have h_triv_bottom : ∀ a : P', ∀ g : G, g ∈ Gi bottom → a • g = g := by
        intro a g hg
        rw [hbottom, Subgroup.mem_bot] at hg
        subst hg
        simp [smul_one]
      have h_triv_chain : ∀ k, k ≤ n → ∀ a : P', ∀ g : G, g ∈ Gi (Nat.iterate next k top) → a • g = g := by
        have base : ∀ a : P', ∀ g : G, g ∈ Gi (Nat.iterate next n top) → a • g = g := by
          rw [hn] at *
          exact h_triv_bottom
        have step : ∀ k, k < n → (∀ a : P', ∀ g : G, g ∈ Gi (Nat.iterate next (k + 1) top) → a • g = g) →
            ∀ a : P', ∀ g : G, g ∈ Gi (Nat.iterate next k top) → a • g = g := by
          intro k hk IH a g hg
          have h_desc : Gi (Nat.iterate next (k + 1) top) ≤ Gi (Nat.iterate next k top) := by
            calc
              Gi (Nat.iterate next (k + 1) top) = Gi (next (Nat.iterate next k top)) := by
                rw [Function.iterate_succ_apply']
              _ ≤ Gi (Nat.iterate next k top) := hdesc (Nat.iterate next k top)
          have h_normal_H : (Gi (Nat.iterate next (k + 1) top)).Normal := hnormal _
          have h_normal_K : (Gi (Nat.iterate next k top)).Normal := hnormal _
          have h_inv_next : IsInvariant P' G (Gi (Nat.iterate next (k + 1) top)) := hinvP _
          have h_inv_current : IsInvariant P' G (Gi (Nat.iterate next k top)) := hinvP _
          have h_factor : ∀ a : P', ∀ g : G, g ∈ Gi (Nat.iterate next k top) → (a • g) * g⁻¹ ∈ Gi (Nat.iterate next (k + 1) top) := by
            intro a' g' hg'
            have h := hfactorQ (Nat.iterate next k top) a' g' hg'
            have h_iter_eq : next (Nat.iterate next k top) = Nat.iterate next (k + 1) top := by
              simpa using (Function.iterate_succ_apply' next k top).symm
            rw [h_iter_eq] at h
            exact h
          have h_coprime : Nat.Coprime p.val (Nat.card (Gi (Nat.iterate next (k + 1) top))) := by
            refine Nat.Coprime.coprime_dvd_right (Subgroup.card_subgroup_dvd_card _) h_coprime_G
          have hP_pgroup' : IsPGroup p.val P' := hP_pgroup
          exact actsTriviallyOn_subgroup_of_smul_div_mem_and_coprime (A := P') p.val hp_prime
            (Gi (Nat.iterate next (k + 1) top)) (Gi (Nat.iterate next k top))
            hP_pgroup' h_coprime h_factor IH a g hg
        intro k hk
        exact Nat.decreasingInduction step base hk
      have h_triv_all : ∀ a : P', ∀ g : G, a • g = g := by
        intro a g
        have : g ∈ Gi top := by rw [htop]; trivial
        exact h_triv_chain 0 (by omega) a g this
      have h_subsingleton : Subsingleton P' := ⟨fun a b => by
        apply Subtype.ext
        have ha : (a : Q) = 1 := faithful a (h_triv_all a)
        have hb : (b : Q) = 1 := faithful b (h_triv_all b)
        rw [ha, hb]⟩
      have hP_subsingleton : Subsingleton P' := h_subsingleton
      have hP_trivial : P' = ⊥ := Subgroup.eq_bot_of_subsingleton (H := P')
      have h_card : p.val ∣ Nat.card P' := by
        exact P.dvd_card_of_dvd_card h
      have h_card' : Nat.card P' = 1 := by
        calc
          Nat.card P' = Nat.card (⊥ : Subgroup Q) := congr_arg (fun H : Subgroup Q => Nat.card H) hP_trivial
          _ = 1 := Subgroup.card_bot
      rw [h_card'] at h_card
      have h_dvd_one : p.val ∣ 1 := h_card
      have h_val_eq_one : p.val = 1 := Nat.dvd_one.mp h_dvd_one
      have : p.val > 1 := hp_prime.one_lt
      linarith
    · exact not_not.mp h_not
  · exfalso
    exact h hp

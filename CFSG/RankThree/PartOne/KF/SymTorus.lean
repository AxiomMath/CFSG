module

public import CFSG.RankThree.PartOne.KF.U4Perm
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.RankThree.PartOne.KFU

variable {n p : ℕ} {K : Type} [Field K]

@[expose] def torusEltHom (i j : Fin n) : Kˣ →* (Fin n → Kˣ) where
  toFun := torusElt i j
  map_one' := by
    funext k
    simp [torusElt]
  map_mul' u v := by
    funext k
    simp only [torusElt, Pi.mul_apply, Pi.mulSingle_apply, mul_inv_rev]
    split_ifs <;> simp [mul_comm]
    rw [← mul_inv, mul_inv_cancel]

theorem torusEltHom_apply (i j : Fin n) (u : Kˣ) : torusEltHom i j u = torusElt i j u := rfl

theorem torusElt_swap (i j : Fin n) (u : Kˣ) : torusElt j i u = torusElt i j u⁻¹ := by
  simp [torusElt, mul_comm]

@[expose] def torusEltV (p : ℕ) {i j : Fin n} (hij : i ≠ j) :
    rootsOfUnity p K →* torusVec p n K where
  toFun u := ⟨torusElt i j (u : Kˣ), torusElt_mem hij ((mem_rootsOfUnity p _).mp u.2)⟩
  map_one' := Subtype.ext (map_one (torusEltHom i j))
  map_mul' u v := Subtype.ext (map_mul (torusEltHom i j) (u : Kˣ) (v : Kˣ))

theorem coe_torusEltV {i j : Fin n} (hij : i ≠ j) (u : rootsOfUnity p K) :
    ((torusEltV p hij u : torusVec p n K) : Fin n → Kˣ) = torusElt i j (u : Kˣ) := rfl

theorem torusEltV_injective {i j : Fin n} (hij : i ≠ j) :
    Function.Injective (torusEltV (p := p) (K := K) hij) := by
  intro u v h
  have h1 := congrFun (congrArg Subtype.val h) i
  rw [coe_torusEltV, coe_torusEltV, torusElt_apply_left hij, torusElt_apply_left hij] at h1
  exact Subtype.ext h1

@[expose] def symAct (p : ℕ) (K : Type) [Field K] (σ : Equiv.Perm (Fin n)) :
    torusVec p n K →* torusVec p n K where
  toFun d := ⟨(d : Fin n → Kˣ) ∘ σ.symm, torusVec_comp σ.symm d.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem coe_symAct (σ : Equiv.Perm (Fin n)) (d : torusVec p n K) (i : Fin n) :
    ((symAct p K σ d : torusVec p n K) : Fin n → Kˣ) i = (d : Fin n → Kˣ) (σ.symm i) := rfl

theorem symAct_one (d : torusVec p n K) : symAct p K 1 d = d := rfl

theorem symAct_mul (σ τ : Equiv.Perm (Fin n)) (d : torusVec p n K) :
    symAct p K (σ * τ) d = symAct p K σ (symAct p K τ d) := rfl

@[expose] def symAut (p : ℕ) (K : Type) [Field K] :
    Equiv.Perm (Fin n) →* MulAut (torusVec p n K) where
  toFun σ :=
    { toFun := symAct p K σ
      invFun := symAct p K σ⁻¹
      left_inv := fun d => by rw [← symAct_mul, inv_mul_cancel, symAct_one]
      right_inv := fun d => by rw [← symAct_mul, mul_inv_cancel, symAct_one]
      map_mul' := map_mul _ }
  map_one' := MulEquiv.ext fun d => symAct_one d
  map_mul' σ τ := MulEquiv.ext fun d => symAct_mul σ τ d

theorem symAut_apply (σ : Equiv.Perm (Fin n)) (d : torusVec p n K) :
    symAut p K σ d = symAct p K σ d := rfl

theorem symAct_torusEltV (σ : Equiv.Perm (Fin n)) {i j : Fin n} (hij : i ≠ j)
    (u : rootsOfUnity p K) :
    symAct p K σ (torusEltV p hij u) = torusEltV p (σ.injective.ne hij) u := by
  apply Subtype.ext
  funext k
  rw [coe_symAct, coe_torusEltV, coe_torusEltV]
  by_cases hk : σ.symm k = i
  · have hk' : k = σ i := by rw [← hk]; simp
    rw [hk, hk', torusElt_apply_left hij, torusElt_apply_left (σ.injective.ne hij)]
  · by_cases hk2 : σ.symm k = j
    · have hk' : k = σ j := by rw [← hk2]; simp
      rw [hk2, hk', torusElt_apply_right hij, torusElt_apply_right (σ.injective.ne hij)]
    · have h1 : k ≠ σ i := fun h => hk (by rw [h]; simp)
      have h2 : k ≠ σ j := fun h => hk2 (by rw [h]; simp)
      rw [torusElt_apply_other hk hk2, torusElt_apply_other h1 h2]

theorem symAut_injective (hp : p.Prime) (hp2 : p ≠ 2) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    Function.Injective (symAut (n := n) p K) := by
  obtain ⟨ζ, hζ⟩ := hζ
  have hζ2 : ζ ^ 2 ≠ 1 := by
    intro h
    have := hζ.dvd_of_pow_eq_one 2 h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  rw [injective_iff_map_eq_one]
  intro σ hσ
  refine Equiv.ext fun k => ?_
  by_contra hne
  have hij : σ k ≠ k := hne
  have h1 := congrArg (fun m : MulAut (torusVec p n K) =>
    ((m (torusEltV p hij ⟨ζ, (mem_rootsOfUnity p _).mpr hζ.pow_eq_one⟩) : torusVec p n K) :
      Fin n → Kˣ) (σ k)) hσ
  simp only [symAut_apply, MulAut.one_apply] at h1
  rw [coe_symAct, Equiv.symm_apply_apply, coe_torusEltV, torusElt_apply_right hij,
    torusElt_apply_left hij] at h1
  apply hζ2
  calc ζ ^ 2 = ζ * ζ := sq ζ
    _ = ζ * ζ⁻¹ := by rw [h1]
    _ = 1 := mul_inv_cancel ζ

theorem card_torusVec_eq [Finite K] (hp : 0 < p) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) (m : ℕ) :
    Nat.card (torusVec p (m + 1) K) = p ^ m := by
  classical
  have : NeZero p := ⟨hp.ne'⟩
  refine le_antisymm (card_torusVec_le hp m) ?_
  obtain ⟨ζ, hζ⟩ := hζ
  have hcard : Nat.card (rootsOfUnity p K) = p :=
    IsPrimitiveRoot.card_rootsOfUnity (IsPrimitiveRoot.coe_units_iff.mpr hζ)
  let ι : (Fin m → rootsOfUnity p K) → torusVec p (m + 1) K := fun w =>
    ⟨Fin.snoc (α := fun _ => Kˣ) (fun j => (w j : Kˣ)) (∏ j, (w j : Kˣ))⁻¹, fun i => by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Fin.snoc_last, inv_pow, ← Finset.prod_pow]
        simp [(mem_rootsOfUnity p _).mp (w _).2]
      · rw [Fin.snoc_castSucc]
        exact (mem_rootsOfUnity p _).mp (w j).2, by
      rw [Fin.prod_univ_castSucc]
      simp⟩
  have hι : Function.Injective ι := by
    intro w w' h
    funext j
    have := congrFun (congrArg Subtype.val h) (Fin.castSucc j)
    simp only [ι, Fin.snoc_castSucc] at this
    exact Subtype.ext this
  have h1 := Nat.card_le_card_of_injective ι hι
  have h2 : Nat.card (Fin m → rootsOfUnity p K) = p ^ m := by
    rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hcard]
  rw [h2] at h1
  exact h1

@[expose] def torusSpan (p n : ℕ) (K : Type) [Field K] : Subgroup (torusVec p n K) :=
  Subgroup.closure {d | ∃ (i j : Fin n) (hij : i ≠ j) (u : rootsOfUnity p K),
    d = torusEltV p hij u}

theorem torusEltV_mem_torusSpan {i j : Fin n} (hij : i ≠ j) (u : rootsOfUnity p K) :
    torusEltV p hij u ∈ torusSpan p n K :=
  Subgroup.subset_closure ⟨i, j, hij, u, rfl⟩

theorem torusSpan_eq_top : torusSpan p n K = ⊤ := by
  classical
  rw [eq_top_iff]
  rintro ⟨d, hd⟩ -
  suffices H : ∀ m : ℕ, ∀ d : Fin n → Kˣ, ∀ hd : d ∈ torusVec p n K,
      (Finset.univ.filter fun i => d i ≠ 1).card = m →
        (⟨d, hd⟩ : torusVec p n K) ∈ torusSpan p n K from H _ d hd rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro d hd hm
    by_cases h0 : ∀ i, d i = 1
    · have : d = 1 := funext h0
      subst this
      exact Subgroup.one_mem _
    · push Not at h0
      obtain ⟨i, hi⟩ := h0
      obtain ⟨j, hji, hj⟩ : ∃ j, j ≠ i ∧ d j ≠ 1 := by
        by_contra hcon
        push Not at hcon
        apply hi
        have h1 := hd.2
        rwa [Finset.prod_eq_single i (fun k _ hk => hcon k hk) (by simp)] at h1
      have hij : i ≠ j := hji.symm
      have hu : (d i)⁻¹ ^ p = 1 := by rw [inv_pow, hd.1 i, inv_one]
      have hmem : torusElt i j (d i)⁻¹ ∈ torusVec p n K := torusElt_mem hij hu
      have hd' : d * torusElt i j (d i)⁻¹ ∈ torusVec p n K := Subgroup.mul_mem _ hd hmem
      have hcard : (Finset.univ.filter fun k => (d * torusElt i j (d i)⁻¹) k ≠ 1).card < m := by
        rw [← hm]
        have hsub : (Finset.univ.filter fun k => (d * torusElt i j (d i)⁻¹) k ≠ 1) ⊆
            (Finset.univ.filter fun k => d k ≠ 1).erase i := by
          intro k hk
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hk ⊢
          by_cases hki : k = i
          · subst hki
            exfalso
            apply hk
            rw [Pi.mul_apply, torusElt_apply_left hij, mul_inv_cancel]
          · refine ⟨hki, fun h1 => hk ?_⟩
            by_cases hkj : k = j
            · subst hkj
              exact absurd h1 hj
            · rw [Pi.mul_apply, torusElt_apply_other hki hkj, h1, mul_one]
        have hi' : i ∈ Finset.univ.filter fun k => d k ≠ 1 := by simp [hi]
        calc _ ≤ ((Finset.univ.filter fun k => d k ≠ 1).erase i).card := Finset.card_le_card hsub
          _ < _ := Finset.card_erase_lt_of_mem hi'
      have hIH := ih _ hcard _ hd' rfl
      have hmul : (⟨d, hd⟩ : torusVec p n K) =
          ⟨d * torusElt i j (d i)⁻¹, hd'⟩ *
            torusEltV p hij ⟨d i, (mem_rootsOfUnity p _).mpr (hd.1 i)⟩ := by
        apply Subtype.ext
        change d = d * torusElt i j (d i)⁻¹ * torusElt i j (d i)
        rw [mul_assoc, ← torusEltHom_apply, ← torusEltHom_apply, ← map_mul, inv_mul_cancel,
          map_one, mul_one]
      rw [hmul]
      exact Subgroup.mul_mem _ hIH (torusEltV_mem_torusSpan hij _)

@[expose] def movedSub (p : ℕ) (K : Type) [Field K] (σ : Equiv.Perm (Fin n)) :
    Subgroup (torusVec p n K) :=
  Subgroup.closure (Set.range fun d : torusVec p n K => symAct p K σ d * d⁻¹)

theorem symAct_swap_mul_inv {a b : Fin n} (hab : a ≠ b) (d : torusVec p n K) :
    symAct p K (Equiv.swap a b) d * d⁻¹ =
      torusEltV p hab ⟨(d : Fin n → Kˣ) b * ((d : Fin n → Kˣ) a)⁻¹,
        (mem_rootsOfUnity p _).mpr (by rw [mul_pow, inv_pow, d.2.1 b, d.2.1 a]; simp)⟩ := by
  apply Subtype.ext
  funext k
  rw [coe_torusEltV]
  show (d.1 ((Equiv.swap a b).symm k)) * (d.1 k)⁻¹ = torusElt a b _ k
  rw [Equiv.symm_swap]
  by_cases hka : k = a
  · subst hka
    rw [Equiv.swap_apply_left, torusElt_apply_left hab]
  · by_cases hkb : k = b
    · subst hkb
      rw [Equiv.swap_apply_right, torusElt_apply_right hab, mul_inv_rev, inv_inv, mul_comm]
    · rw [Equiv.swap_apply_of_ne_of_ne hka hkb, torusElt_apply_other hka hkb, mul_inv_cancel]

theorem movedSub_swap (hp : p.Prime) (hp2 : p ≠ 2) {a b : Fin n} (hab : a ≠ b) :
    movedSub p K (Equiv.swap a b) = (torusEltV p hab).range := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨d, rfl⟩
    show symAct p K (Equiv.swap a b) d * d⁻¹ ∈ _
    rw [symAct_swap_mul_inv hab]
    exact ⟨_, rfl⟩
  · rintro _ ⟨u, rfl⟩
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
    have hu : (u : Kˣ) ^ p = 1 := (mem_rootsOfUnity p _).mp u.2
    have hw : ((u : Kˣ) ^ (k + 1))⁻¹ ^ p = 1 := by rw [inv_pow, ← pow_mul, mul_comm, pow_mul, hu,
      one_pow, inv_one]
    apply Subgroup.subset_closure
    refine ⟨torusEltV p hab ⟨((u : Kˣ) ^ (k + 1))⁻¹, (mem_rootsOfUnity p _).mpr hw⟩, ?_⟩
    show symAct p K (Equiv.swap a b) _ * _⁻¹ = _
    rw [symAct_swap_mul_inv hab]
    congr 1
    apply Subtype.ext
    simp only [coe_torusEltV, torusElt_apply_left hab, torusElt_apply_right hab, inv_inv]
    rw [← pow_add, show k + 1 + (k + 1) = p + 1 by omega, pow_succ, hu, one_mul]

theorem card_movedSub_swap [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) {a b : Fin n} (hab : a ≠ b) :
    Nat.card (movedSub p K (Equiv.swap a b)) = p := by
  obtain ⟨ζ, hζ⟩ := hζ
  have : NeZero p := ⟨hp.ne_zero⟩
  rw [movedSub_swap hp hp2 hab,
    Nat.card_congr (MonoidHom.ofInjective (torusEltV_injective hab)).toEquiv.symm]
  exact IsPrimitiveRoot.card_rootsOfUnity (IsPrimitiveRoot.coe_units_iff.mpr hζ)

theorem exists_perm_pair {i j k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l) :
    ∃ τ : Equiv.Perm (Fin n), τ i = k ∧ τ j = l := by
  have hj' : Equiv.swap i k j ≠ k := by
    intro h
    apply hij
    have : Equiv.swap i k j = Equiv.swap i k i := by rw [h, Equiv.swap_apply_left]
    exact (Equiv.swap i k).injective this |>.symm
  refine ⟨Equiv.swap (Equiv.swap i k j) l * Equiv.swap i k, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hj'.symm hkl]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]

theorem eq_top_of_symInvariant_of_nonconst [Finite K] (hp : p.Prime)
    (B : Subgroup (torusVec p n K))
    (hB : ∀ σ : Equiv.Perm (Fin n), ∀ d ∈ B, symAct p K σ d ∈ B) {d : torusVec p n K}
    (hdB : d ∈ B) {i j : Fin n} (hij : d.1 i ≠ d.1 j) : B = ⊤ := by
  have hij' : i ≠ j := fun h => hij (by rw [h])
  have hu : (d.1 j * (d.1 i)⁻¹) ^ p = 1 := by rw [mul_pow, inv_pow, d.2.1 j, d.2.1 i]; simp
  have hu1 : d.1 j * (d.1 i)⁻¹ ≠ 1 := fun h => hij (mul_inv_eq_one.mp h).symm
  have heB : torusEltV p hij' ⟨d.1 j * (d.1 i)⁻¹, (mem_rootsOfUnity p _).mpr hu⟩ ∈ B := by
    have := B.mul_mem (hB (Equiv.swap i j) d hdB) (B.inv_mem hdB)
    rwa [symAct_swap_mul_inv hij'] at this
  have hprim : IsPrimitiveRoot (d.1 j * (d.1 i)⁻¹) p := by
    have : Fact p.Prime := ⟨hp⟩
    have h := IsPrimitiveRoot.orderOf (d.1 j * (d.1 i)⁻¹)
    rwa [orderOf_eq_prime hu hu1] at h
  have : NeZero p := ⟨hp.ne_zero⟩
  have hall : ∀ (k l : Fin n) (hkl : k ≠ l) (v : rootsOfUnity p K), torusEltV p hkl v ∈ B := by
    intro k l hkl v
    obtain ⟨τ, rfl, rfl⟩ := exists_perm_pair hij' hkl
    have h1 := hB τ _ heB
    rw [symAct_torusEltV τ hij'] at h1
    obtain ⟨m, -, hm⟩ := (IsPrimitiveRoot.coe_units_iff.mpr hprim).eq_pow_of_pow_eq_one
      (ξ := ((v : Kˣ) : K)) (by
        have := (mem_rootsOfUnity p _).mp v.2
        rw [← Units.val_pow_eq_pow_val, this, Units.val_one])
    have hvm : v = ⟨d.1 j * (d.1 i)⁻¹, (mem_rootsOfUnity p _).mpr hu⟩ ^ m := by
      apply Subtype.ext
      apply Units.ext
      rw [← hm]
      simp
    rw [hvm, map_pow]
    exact B.pow_mem h1 m
  rw [eq_top_iff, ← torusSpan_eq_top]
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨k, l, hkl, v, rfl⟩
  exact hall k l hkl v


theorem eq_bot_or_eq_top_of_symInvariant [Finite K] (hp : p.Prime) (hn : 2 ≤ n)
    (hpn : ¬ p ∣ n) (B : Subgroup (torusVec p n K))
    (hB : ∀ σ : Equiv.Perm (Fin n), ∀ d ∈ B, symAct p K σ d ∈ B) : B = ⊥ ∨ B = ⊤ := by
  by_cases hB1 : B = ⊥
  · exact Or.inl hB1
  right
  obtain ⟨d, hdB, hd1⟩ : ∃ d ∈ B, d ≠ 1 := by
    by_contra h
    push Not at h
    exact hB1 ((Subgroup.eq_bot_iff_forall B).mpr h)
  obtain ⟨i, j, hij⟩ : ∃ i j : Fin n, d.1 i ≠ d.1 j := by
    by_contra h
    push Not at h
    apply hd1
    have hc : ∀ i, d.1 i = d.1 ⟨0, by omega⟩ := fun i => h i _
    have h1 : (d.1 ⟨0, by omega⟩) ^ n = 1 := by
      have := d.2.2
      simpa [hc, Finset.prod_const, Finset.card_univ] using this
    have h2 : (d.1 ⟨0, by omega⟩) ^ p = 1 := d.2.1 _
    have hcop : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpn
    have h3 := pow_gcd_eq_one.mpr ⟨h2, h1⟩
    rw [hcop, pow_one] at h3
    exact Subtype.ext (funext fun k => by rw [hc k, h3]; rfl)
  exact eq_top_of_symInvariant_of_nonconst hp B hB hdB hij

@[expose] def scalarSub (p n : ℕ) (K : Type) [Field K] : Subgroup (torusVec p n K) where
  carrier := {d | ∀ i j, (d : Fin n → Kˣ) i = (d : Fin n → Kˣ) j}
  mul_mem' := fun {a b} ha hb i j => by
    show (a : Fin n → Kˣ) i * (b : Fin n → Kˣ) i = (a : Fin n → Kˣ) j * (b : Fin n → Kˣ) j
    rw [ha i j, hb i j]
  one_mem' := fun i j => rfl
  inv_mem' := fun {a} ha i j => by
    show ((a : Fin n → Kˣ) i)⁻¹ = ((a : Fin n → Kˣ) j)⁻¹
    rw [ha i j]

theorem le_scalarSub_or_eq_top [Finite K] (hp : p.Prime) (B : Subgroup (torusVec p n K))
    (hB : ∀ σ : Equiv.Perm (Fin n), ∀ d ∈ B, symAct p K σ d ∈ B) :
    B ≤ scalarSub p n K ∨ B = ⊤ := by
  by_cases h : B ≤ scalarSub p n K
  · exact Or.inl h
  right
  obtain ⟨d, hdB, hd⟩ := Set.not_subset.mp h
  have hd' : ¬ ∀ i j, (d : Fin n → Kˣ) i = (d : Fin n → Kˣ) j := hd
  push Not at hd'
  obtain ⟨i, j, hij⟩ := hd'
  exact eq_top_of_symInvariant_of_nonconst hp B hB hdB hij

theorem card_scalarSub [Finite K] (hp : p.Prime) (hn : 1 ≤ n) (hpn : p ∣ n)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) : Nat.card (scalarSub p n K) = p := by
  obtain ⟨ζ, hζ⟩ := hζ
  have : NeZero p := ⟨hp.ne_zero⟩
  have hcard : Nat.card (rootsOfUnity p K) = p :=
    IsPrimitiveRoot.card_rootsOfUnity (IsPrimitiveRoot.coe_units_iff.mpr hζ)
  let i₀ : Fin n := ⟨0, hn⟩
  have hbij : Function.Bijective (fun d : scalarSub p n K =>
      (⟨(d.1 : Fin n → Kˣ) i₀, (mem_rootsOfUnity p _).mpr (d.1.2.1 i₀)⟩ : rootsOfUnity p K)) := by
    constructor
    · intro d e h
      have h1 : ((d : torusVec p n K) : Fin n → Kˣ) i₀ =
          ((e : torusVec p n K) : Fin n → Kˣ) i₀ := congrArg Subtype.val h
      apply Subtype.ext
      apply Subtype.ext
      funext k
      rw [d.2 k i₀, e.2 k i₀, h1]
    · intro v
      refine ⟨⟨⟨fun _ => (v : Kˣ), fun _ => (mem_rootsOfUnity p _).mp v.2, ?_⟩,
        fun _ _ => rfl⟩, rfl⟩
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      obtain ⟨m, hm⟩ := hpn
      rw [hm, pow_mul, (mem_rootsOfUnity p _).mp v.2, one_pow]
  exact (Nat.card_congr (Equiv.ofBijective _ hbij)).trans hcard

theorem moved_coord (σ : Equiv.Perm (Fin n)) {i j : Fin n} (hij : i ≠ j) (u : rootsOfUnity p K)
    (k : Fin n) :
    ((symAct p K σ (torusEltV p hij u) * (torusEltV p hij u)⁻¹ : torusVec p n K) :
      Fin n → Kˣ) k = torusElt i j (u : Kˣ) (σ.symm k) * (torusElt i j (u : Kˣ) k)⁻¹ := rfl

theorem card_movedSub_ne_prime_of_cycle (hp : p.Prime) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p)
    (σ : Equiv.Perm (Fin n)) {a : Fin n} (h1 : σ a ≠ a) (h2 : σ (σ a) ≠ a)
    (h3 : σ (σ (σ a)) ≠ a) : Nat.card (movedSub p K σ) ≠ p := by
  obtain ⟨ζ, hζ⟩ := hζ
  have hζ1 : ζ ≠ 1 := hζ.ne_one hp.one_lt
  obtain ⟨b, hb⟩ : ∃ b, σ a = b := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, σ b = c := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e, σ c = e := ⟨_, rfl⟩
  rw [hb] at h1 h2 h3
  rw [hc] at h2 h3
  rw [he] at h3
  have hab : a ≠ b := h1.symm
  have hbc : b ≠ c := fun h => h1 (σ.injective ((hc.trans h.symm).trans hb.symm))
  have hac : a ≠ c := h2.symm
  have hae : a ≠ e := h3.symm
  have hbe : b ≠ e := fun h => h2 (σ.injective ((he.trans h.symm).trans hb.symm))
  have hce : c ≠ e := fun h => hbc (σ.injective ((he.trans h.symm).trans hc.symm)).symm
  have hs1 : σ.symm a ≠ a := fun h => h1 (by
    have := congrArg σ h
    rw [Equiv.apply_symm_apply] at this
    rw [← hb, ← this])
  have hs2 : σ.symm a ≠ b := fun h => h2 (by
    have := congrArg σ h
    rw [Equiv.apply_symm_apply, hc] at this
    exact this.symm)
  have hse : σ.symm e = c := by rw [← he]; simp
  let z : rootsOfUnity p K := ⟨ζ, (mem_rootsOfUnity p _).mpr hζ.pow_eq_one⟩
  have hx : symAct p K σ (torusEltV p hab z) * (torusEltV p hab z)⁻¹ ∈ movedSub p K σ :=
    Subgroup.subset_closure ⟨_, rfl⟩
  have hy : symAct p K σ (torusEltV p hbc z) * (torusEltV p hbc z)⁻¹ ∈ movedSub p K σ :=
    Subgroup.subset_closure ⟨_, rfl⟩
  have hxe := moved_coord σ hab z e
  have hye := moved_coord σ hbc z e
  have hxa := moved_coord σ hab z a
  rw [hse, torusElt_apply_other hac.symm hbc.symm, torusElt_apply_other hae.symm hbe.symm] at hxe
  rw [hse, torusElt_apply_right hbc, torusElt_apply_other hbe.symm hce.symm] at hye
  rw [torusElt_apply_other hs1 hs2, torusElt_apply_left hab] at hxa
  intro hcard
  have hx1 : symAct p K σ (torusEltV p hab z) * (torusEltV p hab z)⁻¹ ≠ 1 := by
    intro h
    have := congrFun (congrArg Subtype.val h) a
    rw [hxa] at this
    simp only [one_mul] at this
    exact hζ1 (inv_eq_one.mp this)
  have hy' : symAct p K σ (torusEltV p hbc z) * (torusEltV p hbc z)⁻¹ ∉
      Subgroup.zpowers (symAct p K σ (torusEltV p hab z) * (torusEltV p hab z)⁻¹) := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have h4 := congrFun (congrArg Subtype.val hk) e
    have h5 : ((symAct p K σ (torusEltV p hab z) * (torusEltV p hab z)⁻¹ : torusVec p n K) :
        Fin n → Kˣ) e = 1 := by rw [hxe]; simp
    have h6 : (((symAct p K σ (torusEltV p hab z) * (torusEltV p hab z)⁻¹) ^ k :
        torusVec p n K) : Fin n → Kˣ) e = 1 := by
      rw [Subgroup.coe_zpow]
      have := map_zpow (Pi.evalMonoidHom (fun _ : Fin n => Kˣ) e)
        ((symAct p K σ (torusEltV p hab z) * (torusEltV p hab z)⁻¹ : torusVec p n K) :
          Fin n → Kˣ) k
      simp only [Pi.evalMonoidHom_apply] at this
      rw [this, h5, one_zpow]
    rw [h6, hye] at h4
    simp only [inv_one, mul_one] at h4
    exact hζ1 (inv_eq_one.mp h4.symm)
  exact card_ne_prime_of_two_independent hp (movedSub p K σ) hx hy hx1 hy' hcard

theorem involution_cases (σ : Equiv.Perm (Fin n)) (hσ : σ * σ = 1) (h1 : σ ≠ 1) :
    (∃ a b : Fin n, a ≠ b ∧ σ = Equiv.swap a b) ∨
      ∃ a b c d : Fin n, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
        σ a = b ∧ σ b = a ∧ σ c = d ∧ σ d = c := by
  have hinv : ∀ x, σ (σ x) = x := fun x => by
    have := congrArg (fun τ : Equiv.Perm (Fin n) => τ x) hσ
    simpa using this
  obtain ⟨a, ha⟩ : ∃ a, σ a ≠ a := by
    by_contra h
    push Not at h
    exact h1 (Equiv.ext h)
  by_cases hall : ∀ c, c ≠ a → c ≠ σ a → σ c = c
  · left
    refine ⟨a, σ a, fun h => ha h.symm, Equiv.ext fun x => ?_⟩
    by_cases hxa : x = a
    · subst hxa
      rw [Equiv.swap_apply_left]
    · by_cases hxb : x = σ a
      · subst hxb
        rw [Equiv.swap_apply_right, hinv]
      · rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]
        exact hall x hxa hxb
  · right
    push Not at hall
    obtain ⟨c, hca, hcb, hc⟩ := hall
    refine ⟨a, σ a, c, σ c, fun h => ha h.symm, fun h => hca h.symm, ?_, ?_, ?_, ?_, rfl, hinv a,
      rfl, hinv c⟩
    · intro h
      apply hcb
      have := congrArg σ h
      rw [hinv] at this
      exact this.symm
    · exact fun h => hcb h.symm
    · exact fun h => hca (σ.injective h).symm
    · exact fun h => hc h.symm

theorem card_movedSub_ne_prime_of_double_swap (hp : p.Prime) (hp2 : p ≠ 2)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) (σ : Equiv.Perm (Fin n)) {a b c d : Fin n}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hcd : c ≠ d)
    (h1 : σ a = b) (h2 : σ b = a) (h3 : σ c = d) (h4 : σ d = c) :
    Nat.card (movedSub p K σ) ≠ p := by
  obtain ⟨ζ, hζ⟩ := hζ
  have hζ1 : ζ ≠ 1 := hζ.ne_one hp.one_lt
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
  have hz : ∀ (z : Kˣ), z ^ p = 1 → ∃ w : Kˣ, w ^ p = 1 ∧ w⁻¹ * w⁻¹ = z := by
    intro z hz
    refine ⟨(z ^ (k + 1))⁻¹, by rw [inv_pow, ← pow_mul, mul_comm, pow_mul, hz, one_pow, inv_one],
      ?_⟩
    rw [inv_inv, ← pow_add, show k + 1 + (k + 1) = p + 1 by omega, pow_succ, hz, one_mul]
  have hroot : ∀ {i j : Fin n} (hij : i ≠ j), σ i = j → σ j = i → ∀ u : rootsOfUnity p K,
      torusEltV p hij u ∈ movedSub p K σ := by
    intro i j hij hσij hσji u
    obtain ⟨w, hw, hww⟩ := hz (u : Kˣ) ((mem_rootsOfUnity p _).mp u.2)
    apply Subgroup.subset_closure
    refine ⟨torusEltV p hij ⟨w, (mem_rootsOfUnity p _).mpr hw⟩, ?_⟩
    apply Subtype.ext
    funext m
    rw [moved_coord σ hij]
    show torusElt i j w (σ.symm m) * (torusElt i j w m)⁻¹ = torusElt i j (u : Kˣ) m
    by_cases hmi : m = i
    · subst hmi
      have h5 : σ.symm m = j := by rw [Equiv.symm_apply_eq]; exact hσji.symm
      rw [h5, torusElt_apply_right hij, torusElt_apply_left hij, torusElt_apply_left hij, ← hww]
    · by_cases hmj : m = j
      · subst hmj
        have h5 : σ.symm m = i := by rw [Equiv.symm_apply_eq]; exact hσij.symm
        rw [h5, torusElt_apply_left hij, torusElt_apply_right hij, torusElt_apply_right hij,
          ← hww]
        simp
      · have h6 : σ.symm m ≠ i := fun h => hmj (by
          have := congrArg σ h
          rw [Equiv.apply_symm_apply] at this
          rw [this, hσij])
        have h7 : σ.symm m ≠ j := fun h => hmi (by
          have := congrArg σ h
          rw [Equiv.apply_symm_apply] at this
          rw [this, hσji])
        rw [torusElt_apply_other h6 h7, torusElt_apply_other hmi hmj, torusElt_apply_other hmi hmj]
        simp
  let z : rootsOfUnity p K := ⟨ζ, (mem_rootsOfUnity p _).mpr hζ.pow_eq_one⟩
  have hx := hroot hab h1 h2 z
  have hy := hroot hcd h3 h4 z
  have hx1 : torusEltV p hab z ≠ 1 := by
    intro h
    have := congrFun (congrArg Subtype.val h) a
    rw [coe_torusEltV, torusElt_apply_left hab] at this
    exact hζ1 this
  have hy' : torusEltV p hcd z ∉ Subgroup.zpowers (torusEltV p hab z) := by
    intro hmem
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have h5 := congrFun (congrArg Subtype.val hm) c
    have h6 : (((torusEltV p hab z) ^ m : torusVec p n K) : Fin n → Kˣ) c = 1 := by
      rw [Subgroup.coe_zpow]
      have := map_zpow (Pi.evalMonoidHom (fun _ : Fin n => Kˣ) c)
        ((torusEltV p hab z : torusVec p n K) : Fin n → Kˣ) m
      simp only [Pi.evalMonoidHom_apply] at this
      rw [this, coe_torusEltV, torusElt_apply_other hac.symm hbc.symm, one_zpow]
    rw [h6, coe_torusEltV, torusElt_apply_left hcd] at h5
    exact hζ1 h5.symm
  intro hcard
  exact card_ne_prime_of_two_independent hp (movedSub p K σ) hx hy hx1 hy' hcard

end CFSG.RankThree.PartOne.KFU

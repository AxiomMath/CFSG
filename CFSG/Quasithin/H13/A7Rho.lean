module

public import CFSG.Quasithin.H13.A7DSub

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.SteinbergCB
open scoped Pointwise commutatorElement

@[expose] def stab016 : Subgroup (Perm (Fin 7)) :=
  MulAction.stabilizer (Perm (Fin 7)) ({0, 1, 6} : Finset (Fin 7))

@[expose] def iota3 : Fin 3 → Fin 7 := ![0, 1, 6]

@[expose] def idx3 : Fin 7 → Fin 3 := ![0, 1, 0, 0, 0, 0, 2]

theorem idx3_iota3 : ∀ i, idx3 (iota3 i) = i := by
  decide

theorem iota3_mem : ∀ i, iota3 i ∈ ({0, 1, 6} : Finset (Fin 7)) := by
  decide

theorem iota3_idx3 : ∀ y ∈ ({0, 1, 6} : Finset (Fin 7)), iota3 (idx3 y) = y := by
  decide

theorem mem_016_of_mem_stab016 {σ : Perm (Fin 7)} (hσ : σ ∈ stab016) {y : Fin 7}
    (hy : y ∈ ({0, 1, 6} : Finset (Fin 7))) : σ y ∈ ({0, 1, 6} : Finset (Fin 7)) := by
  have h1 : σ • ({0, 1, 6} : Finset (Fin 7)) = {0, 1, 6} := hσ
  rw [← h1]
  exact Finset.smul_mem_smul_finset hy

@[expose] def r3fun (σ : Perm (Fin 7)) (i : Fin 3) : Fin 3 := idx3 (σ (iota3 i))

theorem iota3_r3fun {σ : Perm (Fin 7)} (hσ : σ ∈ stab016) (i : Fin 3) :
    iota3 (r3fun σ i) = σ (iota3 i) :=
  iota3_idx3 _ (mem_016_of_mem_stab016 hσ (iota3_mem i))

@[expose] def res3 : stab016 →* Perm (Fin 3) where
  toFun σ :=
    { toFun := r3fun σ
      invFun := r3fun (σ⁻¹ : stab016)
      left_inv := fun i => by
        simp only [r3fun]
        rw [show iota3 (idx3 ((σ : Perm (Fin 7)) (iota3 i))) = (σ : Perm (Fin 7)) (iota3 i) from
          iota3_r3fun σ.2 i]
        simp [idx3_iota3]
      right_inv := fun i => by
        simp only [r3fun]
        rw [show iota3 (idx3 (((σ⁻¹ : stab016) : Perm (Fin 7)) (iota3 i))) =
          ((σ⁻¹ : stab016) : Perm (Fin 7)) (iota3 i) from iota3_r3fun (σ⁻¹ : stab016).2 i]
        simp [idx3_iota3] }
  map_one' := by
    ext i
    simp [r3fun, idx3_iota3]
  map_mul' σ τ := by
    ext i
    simp only [Equiv.coe_fn_mk, Perm.coe_mul, Function.comp_apply, Subgroup.coe_mul, r3fun]
    rw [← iota3_r3fun τ.2 i, idx3_iota3]

theorem res3_apply (σ : stab016) (i : Fin 3) : res3 σ i = r3fun σ i := rfl

@[expose] def q48 : Subgroup (Perm (Fin 7)) :=
  stab016 ⊓ MulAction.stabilizer (Perm (Fin 7))
    ({{2, 3}, {4, 5}} : Finset (Finset (Fin 7)))

@[expose] def Q48Cond (σ : Perm (Fin 7)) : Prop :=
  σ • ({0, 1, 6} : Finset (Fin 7)) = {0, 1, 6} ∧
    σ • ({{2, 3}, {4, 5}} : Finset (Finset (Fin 7))) = {{2, 3}, {4, 5}}

instance : DecidablePred Q48Cond := fun σ => by
  unfold Q48Cond
  infer_instance

theorem mem_q48_iff {σ : Perm (Fin 7)} : σ ∈ q48 ↔ Q48Cond σ := by
  rw [q48, Subgroup.mem_inf]
  exact Iff.rfl

@[expose] def fam48 (i : Fin 3) (u : Bool × Bool × Bool × Bool) : Perm (Fin 7) :=
  cyc016 ^ (i : ℕ) * sevenWord u

theorem card_filter_q48 : (Finset.univ.filter Q48Cond).card = 48 := by
  decide +kernel

theorem q48Cond_fam48 : ∀ i u, Q48Cond (fam48 i u) := by
  decide +kernel

theorem fam48_injective : ∀ i u i' u', fam48 i u = fam48 i' u' → i = i' ∧ u = u' := by
  decide +kernel

theorem exists_fam48 {σ : Perm (Fin 7)} (h : σ ∈ q48) : ∃ i u, σ = fam48 i u := by
  classical
  have hinj : Function.Injective fun q : Fin 3 × (Bool × Bool × Bool × Bool) => fam48 q.1 q.2 := by
    rintro ⟨i, u⟩ ⟨i', u'⟩ hq
    obtain ⟨rfl, rfl⟩ := fam48_injective i u i' u' hq
    rfl
  have himage : Finset.univ.image (fun q : Fin 3 × (Bool × Bool × Bool × Bool) => fam48 q.1 q.2) =
      Finset.univ.filter Q48Cond := by
    refine Finset.eq_of_subset_of_card_le (fun g hg => ?_) ?_
    · obtain ⟨⟨i, u⟩, -, rfl⟩ := Finset.mem_image.1 hg
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, q48Cond_fam48 i u⟩
    · rw [card_filter_q48, Finset.card_image_of_injective _ hinj]
      rfl
  have hmem : σ ∈ Finset.univ.image
      (fun q : Fin 3 × (Bool × Bool × Bool × Bool) => fam48 q.1 q.2) := by
    rw [himage]
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, mem_q48_iff.1 h⟩
  obtain ⟨⟨i, u⟩, -, hq⟩ := Finset.mem_image.1 hmem
  exact ⟨i, u, hq.symm⟩

theorem q48_le_stab016 : q48 ≤ stab016 := inf_le_left

theorem cyc016_mem_q48 : cyc016 ∈ q48 := by
  rw [mem_q48_iff]
  decide +kernel

theorem word_mem_q48 : ∀ u, sevenWord u ∈ q48 := by
  intro u
  rw [mem_q48_iff]
  revert u
  decide +kernel

theorem fam48_pow_four_of_r3 : ∀ i u, (∀ k, r3fun (fam48 i u) k = k) → fam48 i u ^ 4 = 1 := by
  decide +kernel

theorem fam48_pow_four_of_r3_cycle : ∀ i u, (∀ k, r3fun (fam48 i u) k ≠ k) →
    i ≠ 0 ∧ fam48 i u ^ 4 = cyc016 ^ (i : ℕ) := by
  decide +kernel

theorem s3_comm_cycle : ∀ τ c : Perm (Fin 3), sign τ = -1 → (∀ k, c k ≠ k) →
    (∀ k, ⁅τ, c⁆ k ≠ k) := by
  decide

theorem s3_even_no_fix : ∀ τ : Perm (Fin 3), sign τ = 1 → τ ≠ 1 → ∀ k, τ k ≠ k := by
  decide

theorem s3_cube_of_no_fix : ∀ τ : Perm (Fin 3), (∀ k, τ k ≠ k) → τ ^ 3 = 1 := by
  decide

theorem cyc016_pow_mod (n : ℕ) :
    cyc016 ^ n = cyc016 ^ ((⟨n % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3) : ℕ) := by
  conv_lhs => rw [← Nat.mod_add_div n 3, pow_add, pow_mul, cyc016_pow_three, one_pow, mul_one]

theorem cyc016_pow_ne_one : ∀ i : Fin 3, i ≠ 0 → cyc016 ^ (i : ℕ) ≠ 1 := fam27_none_ne_one

theorem cyc016_pow_eq_pow' : ∀ i j : Fin 3, i ≠ 0 → j ≠ 0 →
    (cyc016 ^ (i : ℕ)) ^ 1 = cyc016 ^ (j : ℕ) ∨ (cyc016 ^ (i : ℕ)) ^ 2 = cyc016 ^ (j : ℕ) := by
  decide +kernel

theorem cyc016_pow_eq_pow (i j : Fin 3) (hi : i ≠ 0) (hj : j ≠ 0) :
    ∃ m : ℕ, (m = 1 ∨ m = 2) ∧ (cyc016 ^ (i : ℕ)) ^ m = cyc016 ^ (j : ℕ) := by
  rcases cyc016_pow_eq_pow' i j hi hj with h | h
  · exact ⟨1, Or.inl rfl, h⟩
  · exact ⟨2, Or.inr rfl, h⟩

theorem r3fun_cyc016_pow : ∀ i : Fin 3, i ≠ 0 → ∀ k, r3fun (cyc016 ^ (i : ℕ)) k ≠ k := by
  decide +kernel

section TwoGroups

variable {G : Type} [Group G]

theorem exists_pow_eq_mul_pow {N : Subgroup G} {n s : G} (hn : n ∈ N)
    (hs : s ∈ normalizer (N : Set G)) (m : ℕ) : ∃ n' ∈ N, (n * s) ^ m = n' * s ^ m := by
  induction m with
  | zero => exact ⟨1, one_mem _, by simp⟩
  | succ m ih =>
    obtain ⟨n', hn', h1⟩ := ih
    have hsm : s ^ m ∈ normalizer (N : Set G) := pow_mem hs m
    refine ⟨n' * (s ^ m * n * (s ^ m)⁻¹), mul_mem hn' ((mem_normalizer_iff.1 hsm n).1 hn), ?_⟩
    rw [pow_succ, h1, pow_succ]
    group

theorem isPGroup_sup_inf_centralizer {L T V : Subgroup G}
    (hC2 : IsPGroup 2 (L ⊓ centralizer (V : Set G) : Subgroup G)) (hT2 : IsPGroup 2 T)
    (hTL : T ≤ normalizer (L : Set G)) :
    IsPGroup 2 ((L ⊔ T) ⊓ centralizer (V : Set G) : Subgroup G) := by
  rintro ⟨g, hg⟩
  obtain ⟨hgLT, hgC⟩ := mem_inf.1 hg
  have hgLT' : g ∈ ((L ⊔ T : Subgroup G) : Set G) := hgLT
  rw [coe_mul_of_right_le_normalizer_left L T hTL] at hgLT'
  obtain ⟨l, hl, t, ht, rfl⟩ := hgLT'
  obtain ⟨a, ha⟩ := hT2 ⟨t, ht⟩
  have ha' : t ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
  have hlt : l * t = t * (t⁻¹ * l * t) := by group
  have htl : t⁻¹ * l * t ∈ L := by
    have := (mem_normalizer_iff.1 (inv_mem (hTL ht)) l).1 hl
    rwa [inv_inv] at this
  obtain ⟨l', hl', h1⟩ := exists_pow_eq_mul_pow (N := L) hl (hTL ht) (2 ^ a)
  rw [ha', mul_one] at h1
  have h2 : (l * t) ^ 2 ^ a ∈ (L ⊓ centralizer (V : Set G) : Subgroup G) :=
    mem_inf.2 ⟨h1 ▸ hl', pow_mem hgC _⟩
  obtain ⟨b, hb⟩ := hC2 ⟨_, h2⟩
  have hb' : ((l * t) ^ 2 ^ a) ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
  refine ⟨a + b, Subtype.ext ?_⟩
  rw [SubgroupClass.coe_pow, pow_add, pow_mul]
  exact hb'

end TwoGroups

section CoordN

variable {G : Type} [Group G] {T L V : Subgroup G} {ψ : V ≃* Multiplicative (evenWeight 7)}

@[expose] noncomputable def A7NatConfig.lamN (h : A7NatConfig T L V ψ) :
    normalizer (V : Set G) →* Perm (Fin 7) :=
  coordRep ψ le_rfl h.Nact

theorem A7NatConfig.lamN_spec (h : A7NatConfig T L V ψ) (m : normalizer (V : Set G)) :
    IsCoordAct ψ m (h.lamN m) :=
  coordRep_spec ψ le_rfl h.Nact m

theorem A7NatConfig.lamN_eq (h : A7NatConfig T L V ψ) (m : normalizer (V : Set G))
    {σ : Perm (Fin 7)} (hσ : IsCoordAct ψ m σ) : h.lamN m = σ :=
  IsCoordAct.unique ψ m.2 (h.lamN_spec m) hσ

theorem A7NatConfig.lamN_eq_one_iff (h : A7NatConfig T L V ψ) (m : normalizer (V : Set G)) :
    h.lamN m = 1 ↔ (m : G) ∈ centralizer (V : Set G) :=
  coordRep_eq_one_iff ψ le_rfl h.Nact m

end CoordN

section KillK

variable {G : Type} [Group G]

theorem A7NatConfig.res3_eq_one_of_mem {T L V K W : Subgroup G}
    {ψ : V ≃* Multiplicative (evenWeight 7)} (h : A7NatConfig T L V ψ)
    (eK : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5))
    (hWN : W ≤ normalizer (V : Set G)) (hWK : W ≤ normalizer (K : Set G))
    (hWq : ∀ w (hw : w ∈ W), h.lamN ⟨w, hWN hw⟩ ∈ q48) (hWLT : W ≤ L ⊔ T)
    (hC2LT : IsPGroup 2 ((L ⊔ T) ⊓ centralizer (V : Set G) : Subgroup G))
    {d₀ : G} (hd₀W : d₀ ∈ W) (hd₀K : d₀ ∈ kerK eK) {i₀ : Fin 3} (hi₀ : i₀ ≠ 0)
    (hd₀l : IsCoordAct ψ d₀ (cyc016 ^ (i₀ : ℕ))) {w : G} (hwK : w ∈ K) (hwW : w ∈ W) :
    res3 ⟨h.lamN ⟨w, hWN hwW⟩, q48_le_stab016 (hWq w hwW)⟩ = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set lam3 : W →* Perm (Fin 3) := res3.comp ((h.lamN.comp (inclusion hWN)).codRestrict stab016
    fun w => q48_le_stab016 (hWq w w.2)) with hlam3
  have hlam3_apply : ∀ (y : G) (hy : y ∈ W), lam3 ⟨y, hy⟩ =
      res3 ⟨h.lamN ⟨y, hWN hy⟩, q48_le_stab016 (hWq y hy)⟩ := fun _ _ => rfl
  change lam3 ⟨w, hwW⟩ = 1
  by_contra hne
  have hOK2 : IsPGroup 2 (pCoreOf 2 K) := by
    rw [pCoreOf_eq_map_cfsgPCore]
    exact (CFSG.pCore_isPGroup (p := 2) (G := K)).map K.subtype
  obtain ⟨hd₀N, hd₀1⟩ := (mem_kerK eK).1 hd₀K
  have hlamd₀ : h.lamN ⟨d₀, hWN hd₀W⟩ = cyc016 ^ (i₀ : ℕ) := h.lamN_eq _ hd₀l
  have hd₀3 : ∀ k, lam3 ⟨d₀, hd₀W⟩ k ≠ k := by
    intro k
    rw [hlam3_apply, res3_apply]
    simp only
    rw [hlamd₀]
    exact r3fun_cyc016_pow i₀ hi₀ k
  have hpow_cop : ∀ (n : ℕ) (x : Perm (Fin 3)), x ^ 3 = 1 → x ^ 2 ^ n = 1 → x = 1 := by
    intro n x h3 h2
    have h4 : orderOf x ∣ Nat.gcd 3 (2 ^ n) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one h2)
    rw [show Nat.gcd 3 (2 ^ n) = 1 from Nat.Coprime.pow_right _ (by norm_num), Nat.dvd_one,
      orderOf_eq_one_iff] at h4
    exact h4
  by_cases hsign : sign (lam3 ⟨w, hwW⟩) = 1
  ·
    have hnofix := s3_even_no_fix _ hsign hne
    obtain ⟨i, u, hiu⟩ := exists_fam48 (hWq w hwW)
    have hr3 : ∀ k, r3fun (fam48 i u) k ≠ k := by
      intro k
      have h1 := hnofix k
      rw [hlam3_apply, res3_apply] at h1
      simp only at h1
      rwa [hiu] at h1
    obtain ⟨hi, h4⟩ := fam48_pow_four_of_r3_cycle i u hr3
    have hwN : w ∈ normalizer (V : Set G) := hWN hwW
    have hw₁W : w ^ 4 ∈ W := pow_mem hwW 4
    have hlamw₁ : h.lamN ⟨w ^ 4, hWN hw₁W⟩ = cyc016 ^ (i : ℕ) := by
      rw [show (⟨w ^ 4, hWN hw₁W⟩ : normalizer (V : Set G)) = ⟨w, hwN⟩ ^ 4 from rfl, map_pow,
        hiu, h4]
    have hw₁3C : (w ^ 4) ^ 3 ∈ centralizer (V : Set G) := by
      have h1 : h.lamN ⟨(w ^ 4) ^ 3, hWN (pow_mem hw₁W 3)⟩ = 1 := by
        rw [show (⟨(w ^ 4) ^ 3, hWN (pow_mem hw₁W 3)⟩ : normalizer (V : Set G)) =
          ⟨w ^ 4, hWN hw₁W⟩ ^ 3 from rfl, map_pow, hlamw₁, ← pow_mul, mul_comm, pow_mul,
          cyc016_pow_three, one_pow]
      exact (h.lamN_eq_one_iff _).1 h1
    obtain ⟨b, hb⟩ := hC2LT ⟨(w ^ 4) ^ 3, mem_inf.2 ⟨hWLT (pow_mem hw₁W 3), hw₁3C⟩⟩
    have hb' : ((w ^ 4) ^ 3) ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
    set w₂ : G := (w ^ 4) ^ 2 ^ b with hw₂def
    have hw₂3 : w₂ ^ 3 = 1 := by
      rw [hw₂def, ← pow_mul, mul_comm, pow_mul, hb']
    have hw₂W : w₂ ∈ W := pow_mem hw₁W _
    have hw₂K : w₂ ∈ K := pow_mem (pow_mem hwK 4) _
    set j : Fin 3 := ⟨((i : ℕ) * 2 ^ b) % 3, Nat.mod_lt _ (by norm_num)⟩ with hjdef
    have hlamw₂ : h.lamN ⟨w₂, hWN hw₂W⟩ = cyc016 ^ (j : ℕ) := by
      rw [show (⟨w₂, hWN hw₂W⟩ : normalizer (V : Set G)) = ⟨w ^ 4, hWN hw₁W⟩ ^ 2 ^ b from rfl,
        map_pow, hlamw₁, ← pow_mul, cyc016_pow_mod]
    have hj : j ≠ 0 := by
      intro hj0
      have h1 : ((i : ℕ) * 2 ^ b) % 3 = 0 := by
        have := congrArg Fin.val hj0
        simpa [hjdef] using this
      have h2 : 3 ∣ (i : ℕ) * 2 ^ b := Nat.dvd_of_mod_eq_zero h1
      rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h2 with h3 | h3
      · have hi3 : (i : ℕ) < 3 := i.2
        have hi0 : (i : ℕ) ≠ 0 := fun h0 => hi (Fin.ext h0)
        omega
      · exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
    obtain ⟨m, -, hm⟩ := cyc016_pow_eq_pow i₀ j hi₀ hj
    have hoW : w₂⁻¹ * d₀ ^ m ∈ W := mul_mem (inv_mem hw₂W) (pow_mem hd₀W m)
    have hoC : w₂⁻¹ * d₀ ^ m ∈ centralizer (V : Set G) := by
      have h1 : h.lamN ⟨w₂⁻¹ * d₀ ^ m, hWN hoW⟩ = 1 := by
        rw [show (⟨w₂⁻¹ * d₀ ^ m, hWN hoW⟩ : normalizer (V : Set G)) =
          (⟨w₂, hWN hw₂W⟩)⁻¹ * ⟨d₀, hWN hd₀W⟩ ^ m from rfl, map_mul, map_inv, map_pow,
          hlamw₂, hlamd₀, hm, inv_mul_cancel]
      exact (h.lamN_eq_one_iff _).1 h1
    obtain ⟨n, hn⟩ := hC2LT ⟨w₂⁻¹ * d₀ ^ m, mem_inf.2 ⟨hWLT hoW, hoC⟩⟩
    have hn' : (w₂⁻¹ * d₀ ^ m) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hw₂N : w₂ ∈ normalizer (K : Set G) := hWK hw₂W
    have hkw₂ : kAct eK ⟨w₂, hw₂N⟩ = kBar eK ⟨w₂, hw₂K⟩ := kAct_of_mem eK hw₂K
    have hkAct : (kAct eK ⟨w₂, hw₂N⟩)⁻¹ ^ 2 ^ n = 1 := by
      have h1 : kAct eK ⟨w₂⁻¹ * d₀ ^ m, hWK hoW⟩ = (kAct eK ⟨w₂, hw₂N⟩)⁻¹ := by
        rw [show (⟨w₂⁻¹ * d₀ ^ m, hWK hoW⟩ : normalizer (K : Set G)) =
          (⟨w₂, hw₂N⟩)⁻¹ * ⟨d₀, hd₀N⟩ ^ m from rfl, map_mul, map_inv, map_pow, hd₀1, one_pow,
          mul_one]
      rw [← h1, ← map_pow]
      have h2 : (⟨w₂⁻¹ * d₀ ^ m, hWK hoW⟩ : normalizer (K : Set G)) ^ 2 ^ n = 1 :=
        Subtype.ext (by simpa using hn')
      rw [h2, map_one]
    have hkbar3 : (kBar eK ⟨w₂, hw₂K⟩) ^ 3 = 1 := by
      rw [← map_pow]
      have h1 : (⟨w₂, hw₂K⟩ : K) ^ 3 = 1 := Subtype.ext (by simpa using hw₂3)
      rw [h1, map_one]
    rw [hkw₂, inv_pow, inv_eq_one] at hkAct
    have hkbar1 : kBar eK ⟨w₂, hw₂K⟩ = 1 := by
      have h4 : orderOf (kBar eK ⟨w₂, hw₂K⟩) ∣ Nat.gcd 3 (2 ^ n) :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hkbar3) (orderOf_dvd_of_pow_eq_one hkAct)
      rw [show Nat.gcd 3 (2 ^ n) = 1 from Nat.Coprime.pow_right _ (by norm_num), Nat.dvd_one,
        orderOf_eq_one_iff] at h4
      exact h4
    rw [kBar_eq_one_iff] at hkbar1
    obtain ⟨r, hr⟩ := (CFSG.pCore_isPGroup (p := 2) (G := K)) ⟨⟨w₂, hw₂K⟩, hkbar1⟩
    have hr' : w₂ ^ 2 ^ r = 1 := by
      have h5 := congrArg (fun x : ↥(CFSG.pCore 2 ↥K) => ((x : K) : G)) hr
      simpa using h5
    have hw₂1 : w₂ = 1 := by
      have h4 : orderOf w₂ ∣ Nat.gcd 3 (2 ^ r) :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hw₂3) (orderOf_dvd_of_pow_eq_one hr')
      rw [show Nat.gcd 3 (2 ^ r) = 1 from Nat.Coprime.pow_right _ (by norm_num), Nat.dvd_one,
        orderOf_eq_one_iff] at h4
      exact h4
    have h1 : h.lamN ⟨w₂, hWN hw₂W⟩ = 1 := by
      rw [show (⟨w₂, hWN hw₂W⟩ : normalizer (V : Set G)) = 1 from Subtype.ext hw₂1, map_one]
    rw [hlamw₂] at h1
    exact cyc016_pow_ne_one j hj h1
  ·
    have hsign' : sign (lam3 ⟨w, hwW⟩) = -1 := (Int.units_eq_one_or _).resolve_left hsign
    have hgW : ⁅w, d₀⁆ ∈ W := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hwW hd₀W) (inv_mem hwW)) (inv_mem hd₀W)
    have hlamg : lam3 ⟨⁅w, d₀⁆, hgW⟩ = ⁅lam3 ⟨w, hwW⟩, lam3 ⟨d₀, hd₀W⟩⁆ := by
      rw [show (⟨⁅w, d₀⁆, hgW⟩ : W) = ⁅(⟨w, hwW⟩ : W), ⟨d₀, hd₀W⟩⁆ from rfl,
        map_commutatorElement]
    have hnofix : ∀ k, lam3 ⟨⁅w, d₀⁆, hgW⟩ k ≠ k := by
      rw [hlamg]
      exact s3_comm_cycle _ _ hsign' hd₀3
    have h1 := comm_mem_of_kAct_eq_one eK hd₀N hd₀1 (inv_mem hwK)
    have hO : ⁅w, d₀⁆ ∈ pCoreOf 2 K := by
      have h2 := (mem_normalizer_iff.1 (normalizer_le_normalizer_pCoreOf_two (le_normalizer hwK))
        _).1 h1
      rw [commutatorElement_def]
      convert h2 using 1
      group
    obtain ⟨n, hn⟩ := hOK2 ⟨_, hO⟩
    have hn' : ⁅w, d₀⁆ ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have h3 : lam3 ⟨⁅w, d₀⁆, hgW⟩ ^ 2 ^ n = 1 := by
      rw [← map_pow]
      have h4 : (⟨⁅w, d₀⁆, hgW⟩ : W) ^ 2 ^ n = 1 := Subtype.ext (by simpa using hn')
      rw [h4, map_one]
    have h5 := hpow_cop n _ (s3_cube_of_no_fix _ hnofix) h3
    exact hnofix 0 (by rw [h5]; rfl)

end KillK

section Quot

variable {G : Type} [Group G]

theorem exists_rho2 {W K : Subgroup G} (hWK : W ≤ normalizer (K : Set G))
    (f : W →* Perm (Fin 3)) (hf : ∀ w (hw : w ∈ W), w ∈ K → f ⟨w, hw⟩ = 1) :
    ∃ ρ₂ : ↥(W ⊔ K) →* Perm (Fin 3), (∀ w (hw : w ∈ W), ρ₂ ⟨w, mem_sup_left hw⟩ = f ⟨w, hw⟩) ∧
      ∀ k (hk : k ∈ K), ρ₂ ⟨k, mem_sup_right hk⟩ = 1 := by
  let := Subgroup.normal_subgroupOf_of_le_normalizer hWK
  let := Subgroup.normal_subgroupOf_sup_of_le_normalizer hWK
  set e := QuotientGroup.quotientInfEquivProdNormalizerQuotient W K hWK with hedef
  have hker : K.subgroupOf W ≤ f.ker := fun w hw => hf w w.2 hw
  set fl := QuotientGroup.lift (K.subgroupOf W) f hker with hfldef
  refine ⟨fl.comp (e.symm.toMonoidHom.comp (QuotientGroup.mk' (K.subgroupOf (W ⊔ K)))),
    fun w hw => ?_, fun k hk => ?_⟩
  · have he : e (QuotientGroup.mk ⟨w, hw⟩) = QuotientGroup.mk ⟨w, mem_sup_left hw⟩ := rfl
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply]
    rw [← he, MulEquiv.symm_apply_apply]
    rfl
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply]
    rw [(QuotientGroup.eq_one_iff _).2 (mem_subgroupOf.2 hk), map_one, map_one]

end Quot

section Outer

variable {G : Type} [Group G] [Finite G]

@[expose] def V0Cond (σ : Perm (Fin 5)) : Prop :=
  NormalizesKleinV0 σ → sign σ = 1 → σ ^ 8 = 1 → σ ∈ kleinV0Set

instance (σ : Perm (Fin 5)) : Decidable (V0Cond σ) := by
  unfold V0Cond
  infer_instance

theorem v0Cond_all : ∀ σ, V0Cond σ := by
  decide +kernel

theorem exists_conj_kBar_sylow (T : Sylow 2 G) {K : Subgroup G}
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (eK : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) :
    ∃ c ∈ alternatingGroup (Fin 5), ∀ k : K,
      (k : G) ∈ (T ⊓ K : Subgroup G) ↔ c * kBar eK k * c⁻¹ ∈ kleinV0 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S : Subgroup G := T ⊓ K with hSdef
  obtain ⟨hS2, hSodd⟩ := sylow_inf_of_le_normalizer T hTK
  have hOS : pCoreOf 2 K ≤ S := le_inf (pCoreOf_le_of_le_normalizer T hTK)
    (by rw [pCoreOf_eq_map_cfsgPCore]; exact map_subtype_le _)
  have hS1 : IsPGroup 2 (S.subgroupOf K) := hS2.comap_of_injective K.subtype K.subtype_injective
  set P1 : Sylow 2 K := hS1.toSylow hSodd with hP1def
  have hP1 : (P1 : Subgroup K) = S.subgroupOf K := IsPGroup.toSylow_coe hS1 hSodd
  set P2 : Sylow 2 (alternatingGroup (Fin 5)) := P1.mapSurjective (kHom_surjective eK)
  have hP2 : (P2 : Subgroup (alternatingGroup (Fin 5))) = (S.subgroupOf K).map (kHom eK) := by
    rw [Sylow.coe_mapSurjective, hP1]
  have hP2card : Nat.card P2 = 4 :=
    nat_card_sylow_two_of_card_sixty SteinbergCB.nat_card_alternating_five P2
  set Sp : Subgroup (Perm (Fin 5)) := (P2 : Subgroup _).map (alternatingGroup (Fin 5)).subtype
  have hSpA : Sp ≤ alternatingGroup (Fin 5) := map_subtype_le _
  have hSpcard : Nat.card Sp = 4 := by
    rw [Subgroup.card_map_of_injective (subtype_injective _), hP2card]
  have hmemSp : ∀ k : K, kBar eK k ∈ Sp ↔ (k : G) ∈ S := by
    intro k
    constructor
    · rintro ⟨a, ha, hak⟩
      rw [hP2] at ha
      obtain ⟨s, hs, hsa⟩ := Subgroup.mem_map.1 ha
      rw [mem_subgroupOf] at hs
      have h1 : kBar eK (s⁻¹ * k) = 1 := by
        rw [map_mul, map_inv, ← hak]
        show ((kHom eK s : Perm (Fin 5)))⁻¹ * (a : Perm (Fin 5)) = 1
        rw [hsa]
        simp
      rw [kBar_eq_one_iff] at h1
      have h2 : ((s⁻¹ * k : K) : G) ∈ S := hOS (by
        rw [pCoreOf_eq_map_cfsgPCore]
        exact ⟨_, h1, rfl⟩)
      have h3 := mul_mem hs h2
      simpa using h3
    · intro hk
      refine ⟨kHom eK k, ?_, rfl⟩
      rw [hP2]
      exact Subgroup.mem_map_of_mem _ (mem_subgroupOf.2 hk)
  obtain ⟨c, hcA, hc⟩ := exists_conj_kleinV0 hSpA hSpcard
  exact ⟨c, hcA, fun k => (hmemSp k).symm.trans (hc _)⟩

theorem sign_kAct_of_inverts (T : Sylow 2 G) {K : Subgroup G}
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (eK : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) {k : G} (hkK : k ∈ K)
    (hkN : k ∈ normalizer ((T ⊓ K : Subgroup G) : Set G)) (hk3 : k ^ 3 = 1)
    (hkO : k ∉ pCoreOf 2 K) {t : G} (htT : t ∈ (T : Subgroup G))
    (hw : ∃ n : ℕ, (t * k * t⁻¹ * k) ^ 2 ^ n = 1) :
    sign (kAct eK ⟨t, hTK htT⟩) = -1 := by
  classical
  obtain ⟨c, hcA, hc⟩ := exists_conj_kBar_sylow T hTK eK
  have hNorm : ∀ g (hg : g ∈ normalizer (K : Set G)),
      g ∈ normalizer ((T ⊓ K : Subgroup G) : Set G) →
        NormalizesKleinV0 (c * kAct eK ⟨g, hg⟩ * c⁻¹) := by
    intro g hg hgS a ha
    have haA : c⁻¹ * a * c ∈ alternatingGroup (Fin 5) :=
      mul_mem (mul_mem (inv_mem hcA) (kleinV0_le_alternating ha)) hcA
    obtain ⟨k', hk'⟩ := kHom_surjective eK ⟨_, haA⟩
    have hk'bar : kBar eK k' = c⁻¹ * a * c := congrArg Subtype.val hk'
    have hk'S : (k' : G) ∈ (T ⊓ K : Subgroup G) := (hc k').2 (by
      rw [hk'bar, show c * (c⁻¹ * a * c) * c⁻¹ = a by group]
      exact ha)
    have h1 := kAct_conj eK hg k'.2
    have h2 : (g * k' * g⁻¹ : G) ∈ (T ⊓ K : Subgroup G) := (mem_normalizer_iff.1 hgS _).1 hk'S
    have h3 := (hc ⟨g * k' * g⁻¹, (mem_normalizer_iff.1 hg _).1 k'.2⟩).1 h2
    rw [h1] at h3
    have h4 : c * kAct eK ⟨g, hg⟩ * c⁻¹ * a * (c * kAct eK ⟨g, hg⟩ * c⁻¹)⁻¹ =
        c * (kAct eK ⟨g, hg⟩ * kBar eK ⟨(k' : G), k'.2⟩ * (kAct eK ⟨g, hg⟩)⁻¹) * c⁻¹ := by
      rw [show kBar eK ⟨(k' : G), k'.2⟩ = c⁻¹ * a * c from hk'bar]
      group
    rw [h4]
    exact h3
  have htS : t ∈ normalizer ((T ⊓ K : Subgroup G) : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨le_normalizer htT, hTK htT⟩
  set σ' : Perm (Fin 5) := c * kAct eK ⟨t, hTK htT⟩ * c⁻¹ with hσ'
  set κ' : Perm (Fin 5) := c * kAct eK ⟨k, le_normalizer hkK⟩ * c⁻¹ with hκ'
  have hσN : NormalizesKleinV0 σ' := hNorm t (hTK htT) htS
  have hκN : NormalizesKleinV0 κ' := hNorm k (le_normalizer hkK) hkN
  have hkbar : kAct eK ⟨k, le_normalizer hkK⟩ = kBar eK ⟨k, hkK⟩ := kAct_of_mem eK hkK
  have hκ3 : κ' ^ 3 = 1 := by
    rw [hκ', conj_pow, ← map_pow]
    have h1 : (⟨k, le_normalizer hkK⟩ : normalizer (K : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hk3)
    rw [h1, map_one, mul_one, mul_inv_cancel]
  have hκV : κ' ∉ kleinV0Set := by
    intro h1
    have h2 : (k : G) ∈ (T ⊓ K : Subgroup G) := (hc ⟨k, hkK⟩).2 (by
      rw [← hkbar]
      exact h1)
    obtain ⟨n, hn⟩ := T.isPGroup' ⟨k, (mem_inf.1 h2).1⟩
    have hn' : k ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have h3 : orderOf k ∣ Nat.gcd 3 (2 ^ n) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk3) (orderOf_dvd_of_pow_eq_one hn')
    rw [show Nat.gcd 3 (2 ^ n) = 1 from Nat.Coprime.pow_right _ (by norm_num), Nat.dvd_one,
      orderOf_eq_one_iff] at h3
    exact hkO (h3 ▸ one_mem _)
  have hwK : t * k * t⁻¹ * k ∈ K :=
    mul_mem ((mem_normalizer_iff.1 (hTK htT) k).1 hkK) hkK
  have hwN : t * k * t⁻¹ * k ∈ normalizer ((T ⊓ K : Subgroup G) : Set G) :=
    mul_mem (mul_mem (mul_mem htS hkN) (inv_mem htS)) hkN
  have hinvw : σ' * κ' * σ'⁻¹ * κ' = c * kAct eK ⟨_, le_normalizer hwK⟩ * c⁻¹ := by
    rw [show (⟨t * k * t⁻¹ * k, le_normalizer hwK⟩ : normalizer (K : Set G)) =
      ⟨t, hTK htT⟩ * ⟨k, le_normalizer hkK⟩ * ⟨t, hTK htT⟩⁻¹ * ⟨k, le_normalizer hkK⟩ from rfl,
      map_mul, map_mul, map_mul, map_inv, hσ', hκ']
    group
  have hinv : σ' * κ' * σ'⁻¹ * κ' ∈ kleinV0Set := by
    rw [hinvw]
    refine v0Cond_all _ (hNorm _ (le_normalizer hwK) hwN) ?_ ?_
    · rw [kAct_of_mem eK hwK, map_mul, map_mul, map_inv, mul_comm (sign c),
        mul_inv_cancel_right]
      exact (mem_alternatingGroup).1 (kBar_mem eK _)
    · obtain ⟨n, hn⟩ := hw
      set x : Perm (Fin 5) := c * kAct eK ⟨_, le_normalizer hwK⟩ * c⁻¹ with hxdef
      have hx2 : x ^ 2 ^ n = 1 := by
        rw [hxdef, conj_pow, ← map_pow]
        have h1 : (⟨t * k * t⁻¹ * k, le_normalizer hwK⟩ : normalizer (K : Set G)) ^ 2 ^ n = 1 :=
          Subtype.ext (by simpa using hn)
        rw [h1, map_one, mul_one, mul_inv_cancel]
      obtain ⟨j, hj, hjx⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hx2)
      have h120 : orderOf x ∣ 120 := by
        have := orderOf_dvd_natCard x
        rwa [Nat.card_perm, Nat.card_fin] at this
      rw [hjx] at h120
      have hj3 : j ≤ 3 := by
        by_contra hj3
        push Not at hj3
        have : 2 ^ 4 ∣ 2 ^ j := pow_dvd_pow 2 hj3
        have := this.trans h120
        norm_num at this
      have h8 : orderOf x ∣ 8 := by
        rw [hjx]
        exact (pow_dvd_pow 2 hj3).trans (by norm_num)
      exact orderOf_dvd_iff_pow_eq_one.1 h8
  have h1 := sign_eq_neg_one_of_inverts hσN hκN hκ3 hκV hinv
  rw [hσ', map_mul, map_mul, map_inv, mul_comm (sign c), mul_inv_cancel_right] at h1
  exact h1

end Outer

end CFSG.Quasithin.H13.A7

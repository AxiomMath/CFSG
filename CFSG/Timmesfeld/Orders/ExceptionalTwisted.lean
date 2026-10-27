module

public import CFSG.Timmesfeld.Orders.ExceptionalTwistedOrder
public import CFSG.Timmesfeld.Orders.ExceptionalTwistedWeylData
public import CFSG.LieType.Chevalley.GraphFixedFinitePerfect
public import CFSG.LieType.Chevalley.GraphFixedCenterTrivial

public noncomputable section

namespace CFSG.Timmesfeld.ExceptionalOrders

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open

section Kernel

variable {G : Type*} [CommGroup G]

theorem zpowMatrix_diagonal_apply {n : ℕ} (d : Fin n → ℕ) (s : Fin n → G) (j : Fin n) :
    zpowMatrix (Matrix.diagonal fun i => (d i : ℤ)) s j = s j ^ d j := by
  rw [zpowMatrix_apply, Finset.prod_eq_single j (fun i _ hij => by
    rw [Matrix.diagonal_apply_ne _ hij, zpow_zero]) (fun h => absurd (Finset.mem_univ j) h),
    Matrix.diagonal_apply_eq, zpow_natCast]

theorem zpowMatrix_smith {n : ℕ} {A P D Q : Matrix (Fin n) (Fin n) ℤ} (hA : A = P * D * Q)
    (t : Fin n → G) : zpowMatrix A t = zpowMatrix Q (zpowMatrix D (zpowMatrix P t)) := by
  rw [zpowMatrix_zpowMatrix, zpowMatrix_zpowMatrix, hA, mul_assoc]

theorem zpowMatrix_mulSingle_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) (ζ : G)
    (j : Fin n) : zpowMatrix M (Pi.mulSingle i ζ) j = ζ ^ M i j := by
  rw [zpowMatrix_apply, Finset.prod_eq_single i (fun k _ hk => by
    rw [Pi.mulSingle_eq_of_ne hk, one_zpow]) (fun h => absurd (Finset.mem_univ i) h),
    Pi.mulSingle_eq_same]

@[expose] def e6Last : Fin Tag.E6.rank := ⟨5, by decide⟩

theorem smithE6D_of_ne {j : Fin Tag.E6.rank} (hj : j ≠ e6Last) : smithE6D j = 1 := by
  revert j
  decide

theorem smithE6D_last : smithE6D e6Last = 3 :=
  rfl

theorem mem_ker_zpowMatrix_E6 {x : Fin Tag.E6.rank → G} :
    x ∈ (zpowMatrix (G := G) Tag.E6.cartan).ker ↔
      ∃ ζ : G, ζ ^ 3 = 1 ∧ x = fun j => ζ ^ smithE6P' e6Last j := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro hx
    set s := zpowMatrix smithE6P x with hs
    have hD : zpowMatrix (Matrix.diagonal fun i => (smithE6D i : ℤ)) s = 1 := by
      have h := congrArg (zpowMatrix smithE6Q') (zpowMatrix_smith smithE6 x ▸ hx)
      rwa [zpowMatrix_zpowMatrix, smithE6Q_mul, zpowMatrix_one, map_one] at h
    have hsj : ∀ j, s j ^ smithE6D j = 1 := fun j => by
      rw [← zpowMatrix_diagonal_apply, hD, Pi.one_apply]
    have hs1 : ∀ j, j ≠ e6Last → s j = 1 := fun j hj => by
      simpa [smithE6D_of_ne hj] using hsj j
    have hx' : x = zpowMatrix smithE6P' s := by
      rw [hs, zpowMatrix_zpowMatrix, smithE6P_mul, zpowMatrix_one]
    refine ⟨s e6Last, by simpa [smithE6D_last] using hsj e6Last, ?_⟩
    rw [hx']
    funext j
    rw [zpowMatrix_apply, Finset.prod_eq_single e6Last (fun k _ hk => by rw [hs1 k hk, one_zpow])
      (fun h => absurd (Finset.mem_univ _) h)]
  · rintro ⟨ζ, hζ, rfl⟩
    have hx : (fun j => ζ ^ smithE6P' e6Last j) = zpowMatrix smithE6P' (Pi.mulSingle e6Last ζ) :=
      funext fun j => (zpowMatrix_mulSingle_apply _ _ _ _).symm
    rw [hx, zpowMatrix_smith smithE6, zpowMatrix_zpowMatrix smithE6P smithE6P', smithE6P'_mul,
      zpowMatrix_one]
    have hD : zpowMatrix (Matrix.diagonal fun i => (smithE6D i : ℤ)) (Pi.mulSingle e6Last ζ) =
        1 := by
      funext j
      rw [zpowMatrix_diagonal_apply, Pi.one_apply]
      by_cases hj : j = e6Last
      · subst hj
        rw [Pi.mulSingle_eq_same, smithE6D_last, hζ]
      · rw [Pi.mulSingle_eq_of_ne hj, one_pow]
    rw [hD, map_one]

@[expose] def smithD4P : Matrix (Fin Tag.D4.rank) (Fin Tag.D4.rank) ℤ :=
  !![-1, 0, 0, 0; -1, 2, -1, 0; 2, -1, 0, 0; -1, 0, 1, 1]

@[expose] def smithD4P' : Matrix (Fin Tag.D4.rank) (Fin Tag.D4.rank) ℤ :=
  !![-1, 0, 0, 0; -2, 0, -1, 0; -3, -1, -2, 0; 2, 1, 2, 1]

@[expose] def smithD4Q : Matrix (Fin Tag.D4.rank) (Fin Tag.D4.rank) ℤ :=
  !![-2, 0, 1, 0; -3, 1, 0, 1; -2, 0, 0, 1; 1, 0, 0, 0]

@[expose] def smithD4Q' : Matrix (Fin Tag.D4.rank) (Fin Tag.D4.rank) ℤ :=
  !![0, 0, 0, 1; 0, 1, -1, 1; 1, 0, 0, 2; 0, 0, 1, 2]

@[expose] def smithD4D : Fin Tag.D4.rank → ℕ := ![1, 1, 2, 2]

theorem smithD4 :
    Tag.D4.cartan = smithD4P * Matrix.diagonal (fun i => (smithD4D i : ℤ)) * smithD4Q := by
  decide

theorem smithD4P'_mul : smithD4P' * smithD4P = 1 := by decide

theorem smithD4P_mul : smithD4P * smithD4P' = 1 := by decide

theorem smithD4Q_mul : smithD4Q * smithD4Q' = 1 := by decide

end Kernel

section Count

variable {K : Type} [Field K] [Finite K]

theorem two_pow_mod_three (f : ℕ) : 2 ^ f % 3 = if Even f then 1 else 2 := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' f
  · rw [ite_eq_left (even_two_mul k), pow_mul, Nat.pow_mod]
    norm_num
  · rw [ite_eq_right (Nat.not_even_iff_odd.2 (odd_two_mul_add_one k)), pow_succ, pow_mul,
      Nat.mul_mod, Nat.pow_mod]
    norm_num

theorem gcd_three_two_pow_add_one (f : ℕ) :
    Nat.gcd 3 (2 ^ f + 1) = if Even f then 1 else 3 := by
  rw [Nat.gcd_rec, Nat.add_mod, two_pow_mod_three]
  split_ifs <;> norm_num

theorem zpow_eq_zpow_of_dvd {G : Type*} [Group G] {ζ : G} (h3 : ζ ^ 3 = 1) {m n : ℤ}
    (h : (3 : ℤ) ∣ m - n) : ζ ^ m = ζ ^ n := by
  obtain ⟨k, hk⟩ := h
  rw [show m = n + 3 * k by omega, zpow_add, zpow_mul, show (ζ ^ (3 : ℤ)) = 1 by
    rw [zpow_ofNat, h3], one_zpow, mul_one]

theorem card_ker_zpowMatrix_D4_eq_one (hodd : Odd (Nat.card K - 1)) :
    Nat.card (zpowMatrix (G := Kˣ) Tag.D4.cartan).ker = 1 := by
  rw [card_ker_zpowMatrix_eq smithD4 smithD4P'_mul smithD4P_mul smithD4Q_mul,
    card_ker_zpowMatrix_diagonal]
  simp only [IsCyclic.card_powMonoidHom_ker, Nat.card_units]
  change ∏ i : Fin 4, (Nat.card K - 1).gcd (smithD4D i) = 1
  simp only [smithD4D, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Nat.gcd_one_right, one_mul, mul_one]
  rw [Nat.Coprime.gcd_eq_one (Nat.coprime_two_right.2 hodd)]
  rfl

theorem card_compat_inf_ker_D4 (σ : K →+* K) (hodd : Odd (Nat.card K - 1)) :
    Nat.card ↥(compatSubgroup (t := TwistTag.D4) σ ⊓
      (zpowMatrix (G := Kˣ) TwistTag.D4.tag.cartan).ker) = 1 := by
  have h1 := card_ker_zpowMatrix_D4_eq_one (K := K) hodd
  have hle : Nat.card ↥(compatSubgroup (t := TwistTag.D4) σ ⊓
      (zpowMatrix (G := Kˣ) TwistTag.D4.tag.cartan).ker) ≤ 1 :=
    h1 ▸ Subgroup.card_le_of_le inf_le_right
  have hpos : 0 < Nat.card ↥(compatSubgroup (t := TwistTag.D4) σ ⊓
      (zpowMatrix (G := Kˣ) TwistTag.D4.tag.cartan).ker) := Nat.card_pos
  omega

@[expose] def e6Exp (j : Fin TwistTag.E6.tag.rank) : ℤ :=
  smithE6P' e6Last j

theorem e6Exp_zero : e6Exp ⟨0, by decide⟩ = -5 := by decide

theorem e6Exp_perm_zero : e6Exp (TwistTag.E6.perm ⟨0, by decide⟩) = -1 := by decide

theorem e6Exp_last : e6Exp ⟨5, by decide⟩ = -1 := by decide

theorem dvd_e6Exp (i : Fin TwistTag.E6.tag.rank) :
    (3 : ℤ) ∣ e6Exp (TwistTag.E6.perm i) - 2 * e6Exp i := by
  revert i
  decide

theorem mem_ker_zpowMatrix_twistedE6 {G : Type*} [CommGroup G]
    {x : Fin TwistTag.E6.tag.rank → G} :
    x ∈ (zpowMatrix (G := G) TwistTag.E6.tag.cartan).ker ↔
      ∃ ζ : G, ζ ^ 3 = 1 ∧ x = fun j => ζ ^ e6Exp j :=
  mem_ker_zpowMatrix_E6

theorem card_compat_inf_ker_E6 {f : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    Nat.card ↥(compatSubgroup (t := TwistTag.E6) σ ⊓
      (zpowMatrix (G := Kˣ) TwistTag.E6.tag.cartan).ker) = Nat.gcd 3 (2 ^ f + 1) := by
  set q := 2 ^ f with hqdef
  set S := {ζ : Kˣ // ζ ^ 3 = 1 ∧
    ∀ i, ζ ^ e6Exp (TwistTag.E6.perm i) = ζ ^ ((q : ℤ) * e6Exp i)}
  have hmap : ∀ ζ : Kˣ, Units.map σ.toMonoidHom ζ = ζ ^ q := fun ζ =>
    Units.ext (by simp [hσ])
  have hcompat : ∀ ζ : Kˣ, (fun j => ζ ^ e6Exp j) ∈ compatSubgroup (t := TwistTag.E6) σ ↔
      ∀ i, ζ ^ e6Exp (TwistTag.E6.perm i) = ζ ^ ((q : ℤ) * e6Exp i) := fun ζ => by
    refine (mem_compatSubgroup σ).trans (forall_congr' fun i => ?_)
    rw [map_zpow, hmap, ← zpow_natCast, ← zpow_mul]
  have hcard : Nat.card ↥(compatSubgroup (t := TwistTag.E6) σ ⊓
      (zpowMatrix (G := Kˣ) TwistTag.E6.tag.cartan).ker) = Nat.card S := by
    symm
    refine Nat.card_congr (Equiv.ofBijective (fun ζ : S => ⟨fun j => ζ.1 ^ e6Exp j,
      Subgroup.mem_inf.2 ⟨(hcompat ζ.1).2 ζ.2.2,
        mem_ker_zpowMatrix_twistedE6.2 ⟨ζ.1, ζ.2.1, rfl⟩⟩⟩) ⟨fun ζ ζ' h => ?_, fun c => ?_⟩)
    · have h1 := congrFun (congrArg Subtype.val h) ⟨5, by decide⟩
      simp only [e6Exp_last, zpow_neg, zpow_one, inv_inj] at h1
      exact Subtype.ext h1
    · obtain ⟨hc, hk⟩ := Subgroup.mem_inf.1 c.2
      obtain ⟨ζ, hζ, hcζ⟩ := mem_ker_zpowMatrix_twistedE6.1 hk
      refine ⟨⟨ζ, hζ, (hcompat ζ).1 (hcζ ▸ hc)⟩, Subtype.ext ?_⟩
      exact hcζ.symm
  rw [hcard, gcd_three_two_pow_add_one]
  have hq3 := two_pow_mod_three f
  split_ifs with hf
  ·
    rw [ite_eq_left hf] at hq3
    have hS : ∀ ζ : S, ζ.1 = 1 := fun ζ => by
      obtain ⟨ζ, h3, hcond⟩ := ζ
      have h0 := hcond ⟨0, by decide⟩
      rw [e6Exp_perm_zero, e6Exp_zero] at h0
      have hdvd : (3 : ℤ) ∣ (q : ℤ) * -5 - -2 := by
        have : (q : ℤ) % 3 = 1 := by exact_mod_cast hq3
        omega
      rw [zpow_eq_zpow_of_dvd h3 hdvd] at h0
      change ζ = 1
      calc ζ = ζ ^ (-1 : ℤ) * ζ ^ (2 : ℤ) := by group
        _ = ζ ^ (-2 : ℤ) * ζ ^ (2 : ℤ) := by rw [h0]
        _ = 1 := by group
    have : Unique S := ⟨⟨⟨1, one_pow 3, fun _ => by simp⟩⟩, fun ζ => Subtype.ext (hS ζ)⟩
    exact Nat.card_unique
  ·
    rw [ite_eq_right hf] at hq3
    have hcond : ∀ ζ : Kˣ, ζ ^ 3 = 1 →
        ∀ i, ζ ^ e6Exp (TwistTag.E6.perm i) = ζ ^ ((q : ℤ) * e6Exp i) := fun ζ h3 i => by
      refine zpow_eq_zpow_of_dvd h3 ?_
      have h1 := dvd_e6Exp i
      have h2 : (3 : ℤ) ∣ (q : ℤ) - 2 := by
        have : (q : ℤ) % 3 = 2 := by exact_mod_cast hq3
        omega
      have h3' : (3 : ℤ) ∣ ((q : ℤ) - 2) * e6Exp i := dvd_mul_of_dvd_left h2 _
      have := dvd_sub h1 h3'
      convert this using 1
      ring
    have hS : Nat.card S = Nat.card (powMonoidHom 3 : Kˣ →* Kˣ).ker :=
      Nat.card_congr ⟨fun ζ => ⟨ζ.1, ζ.2.1⟩, fun ζ => ⟨ζ.1, ζ.2, hcond ζ.1 ζ.2⟩,
        fun _ => rfl, fun _ => rfl⟩
    rw [hS, IsCyclic.card_powMonoidHom_ker, Nat.card_units, hK]
    have h3 : 3 ∣ (2 ^ f) ^ 2 - 1 := by
      have := Nat.sub_one_dvd_pow_sub_one (2 ^ 2) f
      rw [← pow_mul, mul_comm, pow_mul] at this
      simpa using this
    exact Nat.gcd_eq_right h3

end Count

section Orders

variable {K : Type} [Field K] [Finite K]

theorem ncard_posRoots_twistedE6 :
    {α : Fin TwistTag.E6.tag.rank → ℤ | IsRoot TwistTag.E6.tag α ∧ 0 < height α}.ncard = 36 :=
  (ncard_setOf_isRoot_and fun α => 0 < height α).trans (by decide +kernel)

theorem ncard_posRoots_twistedD4 :
    {α : Fin TwistTag.D4.tag.rank → ℤ | IsRoot TwistTag.D4.tag α ∧ 0 < height α}.ncard = 12 :=
  (ncard_setOf_isRoot_and fun α => 0 < height α).trans (by decide +kernel)

theorem prod_orbit_E6 (q : ℕ) :
    ∏ a : Fin TwistTag.E6.foldedTag.rank, (q ^ (TwistTag.E6.orbit a).card - 1) =
      (q ^ 2 - 1) * (q ^ 2 - 1) * (q - 1) * (q - 1) := by
  change ∏ a : Fin 4, _ = _
  rw [Fin.prod_univ_four]
  have h0 : (TwistTag.E6.orbit (0 : Fin 4)).card = 2 := by decide
  have h1 : (TwistTag.E6.orbit (1 : Fin 4)).card = 2 := by decide
  have h2 : (TwistTag.E6.orbit (2 : Fin 4)).card = 1 := by decide
  have h3 : (TwistTag.E6.orbit (3 : Fin 4)).card = 1 := by decide
  rw [h0, h1, h2, h3, pow_one]

theorem prod_orbit_D4 (q : ℕ) :
    ∏ a : Fin TwistTag.D4.foldedTag.rank, (q ^ (TwistTag.D4.orbit a).card - 1) =
      (q ^ 3 - 1) * (q - 1) := by
  change ∏ a : Fin 2, _ = _
  rw [Fin.prod_univ_two]
  have h0 : (TwistTag.D4.orbit (0 : Fin 2)).card = 3 := by decide
  have h1 : (TwistTag.D4.orbit (1 : Fin 2)).card = 1 := by decide
  rw [h0, h1, pow_one]

theorem ordTwistedE6_mul (q : ℕ) (hq : 1 ≤ q) :
    (q ^ 2 - 1) * (q ^ 2 - 1) * (q - 1) * (q - 1) * q ^ 36 *
      (geomSum 2 2 q * geomSum 3 2 q * (geomSum 2 5 q * geomSum 2 3 q * geomSum 2 1 q) *
        (geomSum 2 9 q * geomSum 2 6 q * geomSum 2 4 q * geomSum 3 1 q)) =
      q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) *
        (q ^ 2 - 1) := by
  have h : ∀ n, 1 ≤ q ^ n := fun n => Nat.one_le_pow _ _ hq
  unfold geomSum
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  zify [hq, h 12, h 8, h 6, h 2]
  ring

theorem ordTrialityD4_eq (q : ℕ) (hq : 1 ≤ q) :
    (q ^ 3 - 1) * (q - 1) * q ^ 12 * (geomSum 2 3 q * (geomSum 3 4 q * geomSum 2 1 q)) =
      ordTrialityD4 q := by
  have h : ∀ n, 1 ≤ q ^ n := fun n => Nat.one_le_pow _ _ hq
  unfold ordTrialityD4 geomSum
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  zify [hq, h 6, h 3, h 2]
  ring

theorem card_graphFixedRootGroup_E6_two {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    Nat.card (graphFixedRootGroup TwistTag.E6 K σ) = ordTwistedE6 (2 ^ f) := by
  have hsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  have hq := card_orbitField (t := TwistTag.E6) Nat.prime_two hf hK hσ
  have : Fintype (WeylGroup TwistTag.E6.tag) := Fintype.ofFinite _
  have hC := card_graphFixedRootGroup hsurj hq
  rw [sum_length_relWeylTwist_E6, ncard_posRoots_twistedE6] at hC
  have hT := card_compatTorus_mul (t := TwistTag.E6) (K := K) σ
  rw [card_compat_inf_ker_E6 hK hσ, card_compatSubgroup] at hT
  simp only [hq] at hT
  rw [prod_orbit_E6] at hT
  have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  rw [ordTwistedE6, ← ordTwistedE6_mul _ hq1, ← hT, hC]
  refine (Nat.div_eq_of_eq_mul_left (Nat.gcd_pos_of_pos_left _ (by norm_num)) ?_).symm
  ring

theorem card_graphFixedRootGroup_D4_two {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
    (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    Nat.card (graphFixedRootGroup TwistTag.D4 K σ) = ordTrialityD4 (2 ^ f) := by
  have hsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  have hq := card_orbitField (t := TwistTag.D4) Nat.prime_two hf hK hσ
  have : Fintype (WeylGroup TwistTag.D4.tag) := Fintype.ofFinite _
  have hC := card_graphFixedRootGroup hsurj hq
  rw [sum_length_relWeylTwist_D4, ncard_posRoots_twistedD4] at hC
  have hodd : Odd (Nat.card K - 1) := by
    rw [hK, ← pow_mul]
    exact Nat.Even.sub_odd (Nat.one_le_two_pow) (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one
  have hT := card_compatTorus_mul (t := TwistTag.D4) (K := K) σ
  rw [card_compat_inf_ker_D4 σ hodd, card_compatSubgroup, mul_one] at hT
  simp only [hq] at hT
  rw [prod_orbit_D4] at hT
  rw [hC, hT, ← ordTrialityD4_eq _ Nat.one_le_two_pow]

end Orders

section Models

variable {G : Type} [Group G]

theorem card_derivedCentralQuotient {t : TwistTag} {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] (hK : Nat.card K = (p ^ f) ^ t.order) (σ : K →+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    Nat.card (DerivedCentralQuotient (twistedFixedGroup t K σ)) =
      Nat.card (graphFixedRootGroup t K σ) := by
  have : Finite K :=
    Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos (pow_pos hp.pos f) _).ne')
  have hsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  have hcomm := (finite_fixed_root_group_perfect t hp hf K hK σ hσ).2.2.1
  set σ' := RingEquiv.ofBijective σ ⟨σ.injective, hsurj⟩
  have hσ' : σ'.toRingHom = σ := RingHom.ext fun _ => rfl
  have hZ := exceptional_fixed_center_trivial t K σ'
  rw [hσ'] at hZ
  rw [DerivedCentralQuotient, hcomm]
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (graphFixedRootGroup t K σ))
  rw [(Subgroup.card_eq_one).2 hZ, mul_one] at h
  exact h.symm

theorem card_of_twistedChevalleyModel_E6_two {f : ℕ} (hf : 1 ≤ f)
    (h : TwistedChevalleyModel G .E6 (2 ^ f)) : Nat.card G = ordTwistedE6 (2 ^ f) := by
  obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, card_derivedCentralQuotient Nat.prime_two hf hK σ hσ]
  exact card_graphFixedRootGroup_E6_two hf hK σ hσ

theorem card_of_twistedChevalleyModel_D4_two {f : ℕ} (hf : 1 ≤ f)
    (h : TwistedChevalleyModel G .D4 (2 ^ f)) : Nat.card G = ordTrialityD4 (2 ^ f) := by
  obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, card_derivedCentralQuotient Nat.prime_two hf hK σ hσ]
  exact card_graphFixedRootGroup_D4_two hf hK σ hσ

end Models

end CFSG.Timmesfeld.ExceptionalOrders

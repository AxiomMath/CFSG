module

public import CFSG.Walter.Ree.Thompson1.Layers
public import CFSG.Walter.Ree.Thompson1.Bracket

public section

namespace CFSG.Walter.Ree.Thompson1

open scoped IsMulCommutative

theorem intCast_trichotomy {K : Type*} [Field K] [CharP K 3] (k : ℤ) :
    (k : K) = 0 ∨ (k : K) = 1 ∨ (k : K) = -1 := by
  have e : (k : K) = ZMod.castHom (dvd_refl 3) K (k : ZMod 3) := (map_intCast _ k).symm
  have h3 : ∀ z : ZMod 3, z = 0 ∨ z = 1 ∨ z = -1 := by decide
  rcases h3 (k : ZMod 3) with h | h | h <;> rw [e, h] <;> simp

variable {N : Type*} [Group N] [Finite N] {q : ℕ} {P R : Subgroup N}
  (h : ThompsonIConditions q P R) {K : Type*} [Field K] [Fintype K] [CharP K 3]
  {m : ℕ} [NeZero m] (hK : Fintype.card K = 3 ^ m) (hq : q = 3 ^ m)
include h hK hq

theorem exists_normal_coords (hm : Odd m) (hm3 : 3 ≤ m) :
    ∃ (σ : K ≃+* K) (r : Kˣ →* N) (ℓ₁ ℓ₂ ℓ₃ : N → K), NormalCoords P R σ r ℓ₁ ℓ₂ ℓ₃ := by
  classical
  have hKq : Fintype.card K = q := by rw [hK, hq]
  have hq1 : 1 < q := by rw [hq]; exact Nat.one_lt_pow (by omega) (by norm_num)
  have hq3 : 3 < Fintype.card K := by
    rw [hK]
    calc 3 < 3 ^ 3 := by norm_num
      _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm3
  have hqodd : Odd q := by rw [hq]; exact Odd.pow (by decide)
  obtain ⟨J, hJ, hJ2⟩ := exists_invol h hqodd hq1
  have hJ1 : J ≠ 1 := by
    intro h1; rw [h1, orderOf_one] at hJ2; exact absurd hJ2 (by norm_num)
  obtain ⟨ℓ₁, ℓ₂, ℓ₃, h1, h2, h3, ρ₁, ρ₂, ρ₃, h1ρ, h2ρ, h3ρ⟩ :=
    exists_eigen_coords h hKq hq (by omega) hJ hJ2
  have hρinj : Function.Injective ρ₁ := by
    rw [injective_iff_map_eq_one]
    intro r hr
    by_contra hr1
    obtain ⟨x, hx, hx1⟩ := h1.surj 1
    have hfix : ℓ₁ (r.1⁻¹ * x * r.1) = ℓ₁ x := by rw [h1ρ r x hx, hr]; simp
    have hx2 := fixed_L1 h hJ hJ2 r.2 (fun h' => hr1 (Subtype.ext h')) hx
      ((h1.eq_iff (conj_mem_P h hx) hx).1 hfix)
    have := (h1.ker x hx).2 hx2
    rw [hx1] at this
    exact one_ne_zero this
  have hρbij : Function.Bijective ρ₁ := hρinj.bijective_of_nat_card_le (by
    rw [Nat.card_units, h.card_R, Nat.card_eq_fintype_card, hKq])
  set χ : R ≃* Kˣ := MulEquiv.ofBijective ρ₁ hρbij with hχ
  have hχ1 : ∀ r : R, χ r = ρ₁ r := fun r => rfl
  have hρJ : (ρ₁ ⟨J, hJ⟩ : K) = -1 := by
    have h2' : (ρ₁ ⟨J, hJ⟩) ^ 2 = 1 := by
      rw [← map_pow, show (⟨J, hJ⟩ : R) ^ 2 = 1 from Subtype.ext (by
        rw [Subgroup.coe_pow, ← hJ2, pow_orderOf_eq_one, Subgroup.coe_one]), map_one]
    have hne : ρ₁ ⟨J, hJ⟩ ≠ 1 := fun h' => hJ1 (congrArg Subtype.val
      (hρinj (h'.trans (map_one ρ₁).symm)))
    have h2'' : ((ρ₁ ⟨J, hJ⟩ : K)) ^ 2 = 1 := by
      have := congrArg (fun u : Kˣ => (u : K)) h2'
      simpa using this
    have h3' : ((ρ₁ ⟨J, hJ⟩ : K) - 1) * ((ρ₁ ⟨J, hJ⟩ : K) + 1) = 0 := by
      linear_combination h2''
    rcases mul_eq_zero.1 h3' with h' | h'
    · exact absurd (Units.ext (by simpa using sub_eq_zero.1 h')) hne
    · linear_combination h'
  have h3K : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  have hlift : ∀ α : K, ∃ x ∈ P, ℓ₁ x = α ∧ J⁻¹ * x * J = x⁻¹ := by
    intro α
    obtain ⟨x₁, hx₁, rfl⟩ := h1.surj α
    refine ⟨x₁⁻¹ * (J⁻¹ * x₁ * J), P.mul_mem (P.inv_mem hx₁) (conj_mem_P h hx₁), ?_,
      invol_conj_inverted hJ2 x₁⟩
    rw [h1.add _ (P.inv_mem hx₁) _ (conj_mem_P h hx₁), h1.inv hx₁, h1ρ ⟨J, hJ⟩ x₁ hx₁, hρJ]
    linear_combination (-ℓ₁ x₁) * h3K
  have hc_inj : ∀ x ∈ P, ℓ₁ x ≠ 0 → J⁻¹ * x * J = x⁻¹ → ∀ y ∈ ⁅P, P⁆, ℓ₃ (tc y x) = 0 →
      ℓ₂ y = 0 := by
    intro x hx hx0 hxinv y hy hyx
    have hxP2 : x ∉ ⁅P, P⁆ := fun hm' => hx0 ((h1.ker x hx).2 hm')
    have hx3 := cube_mem_zc_of_coord h h1 hJ hJ2 hx hxinv
    have h1' := (h3.ker _ (tc_mem_zc h hy hx)).1 hyx
    rw [Subgroup.mem_bot, tc_eq_one_iff] at h1'
    exact (h2.ker y hy).2 (centralizer_inf_commutator h h1 hx hxP2 hx3 hy h1')
  choose s₁ hs₁P hs₁ using h1.surj
  choose s₂ hs₂P hs₂ using h2.surj
  set b : K → K → K := fun α β => ℓ₂ (tc (s₁ α) (s₁ β)) with hbdef
  set c : K → K → K := fun x y => ℓ₃ (tc (s₂ x) (s₁ y)) with hcdef
  have hbwd : ∀ x y, x ∈ P → y ∈ P → ℓ₂ (tc x y) = b (ℓ₁ x) (ℓ₁ y) := fun x y hx hy =>
    B_wd h h1 h2 hx hy (hs₁P _) (hs₁P _) (hs₁ _).symm (hs₁ _).symm
  have hcwd : ∀ y x, y ∈ ⁅P, P⁆ → x ∈ P → ℓ₃ (tc y x) = c (ℓ₂ y) (ℓ₁ x) := fun y x hy hx =>
    C_wd h h1 h2 hy hx (hs₂P _) (hs₁P _) (hs₂ _).symm (hs₁ _).symm
  have hb1 : ∀ x x' y, b (x + x') y = b x y + b x' y := by
    intro x x' y
    have e : ℓ₁ (s₁ x * s₁ x') = x + x' := by rw [h1.add _ (hs₁P x) _ (hs₁P x'), hs₁, hs₁]
    calc b (x + x') y = b (ℓ₁ (s₁ x * s₁ x')) (ℓ₁ (s₁ y)) := by rw [e, hs₁]
      _ = ℓ₂ (tc (s₁ x * s₁ x') (s₁ y)) := (hbwd _ _ (P.mul_mem (hs₁P x) (hs₁P x')) (hs₁P y)).symm
      _ = b x y + b x' y := B_add_left h h2 (hs₁P x) (hs₁P x') (hs₁P y)
  have hb2 : ∀ x y y', b x (y + y') = b x y + b x y' := by
    intro x y y'
    have e : ℓ₁ (s₁ y * s₁ y') = y + y' := by rw [h1.add _ (hs₁P y) _ (hs₁P y'), hs₁, hs₁]
    calc b x (y + y') = b (ℓ₁ (s₁ x)) (ℓ₁ (s₁ y * s₁ y')) := by rw [e, hs₁]
      _ = ℓ₂ (tc (s₁ x) (s₁ y * s₁ y')) := (hbwd _ _ (hs₁P x) (P.mul_mem (hs₁P y) (hs₁P y'))).symm
      _ = b x y + b x y' := B_add_right h h2 (hs₁P x) (hs₁P y) (hs₁P y')
  have hc1 : ∀ x x' y, c (x + x') y = c x y + c x' y := by
    intro x x' y
    have hm' := (⁅P, P⁆ : Subgroup N).mul_mem (hs₂P x) (hs₂P x')
    have e : ℓ₂ (s₂ x * s₂ x') = x + x' := by rw [h2.add _ (hs₂P x) _ (hs₂P x'), hs₂, hs₂]
    calc c (x + x') y = c (ℓ₂ (s₂ x * s₂ x')) (ℓ₁ (s₁ y)) := by rw [e, hs₁]
      _ = ℓ₃ (tc (s₂ x * s₂ x') (s₁ y)) := (hcwd _ _ hm' (hs₁P y)).symm
      _ = c x y + c x' y := by
        rw [tc_mul_left_of_mem h (hs₂P x) (commutator_le h (hs₂P x')) (hs₁P y),
          h3.add _ (tc_mem_zc h (hs₂P x) (hs₁P y)) _ (tc_mem_zc h (hs₂P x') (hs₁P y))]
  have hc2 : ∀ x y y', c x (y + y') = c x y + c x y' := by
    intro x y y'
    have e : ℓ₁ (s₁ y * s₁ y') = y + y' := by rw [h1.add _ (hs₁P y) _ (hs₁P y'), hs₁, hs₁]
    calc c x (y + y') = c (ℓ₂ (s₂ x)) (ℓ₁ (s₁ y * s₁ y')) := by rw [e, hs₂]
      _ = ℓ₃ (tc (s₂ x) (s₁ y * s₁ y')) := (hcwd _ _ (hs₂P x) (P.mul_mem (hs₁P y) (hs₁P y'))).symm
      _ = c x y + c x y' := by
        rw [tc_mul_right_of_mem h (hs₂P x) (hs₁P y) (hs₁P y'),
          h3.add _ (tc_mem_zc h (hs₂P x) (hs₁P y)) _ (tc_mem_zc h (hs₂P x) (hs₁P y'))]
  have halt : ∀ α, b α α = 0 := fun α => by
    show ℓ₂ (tc (s₁ α) (s₁ α)) = 0
    rw [tc_eq_one_iff.2 rfl, h2.one]
  have hχs : ∀ (κ : K) (hκ : κ ≠ 0), (ρ₁ (χ.symm (Units.mk0 κ hκ)) : K) = κ := by
    intro κ hκ
    rw [← hχ1, MulEquiv.apply_symm_apply, Units.val_mk0]
  set ψ₂ : K → K := fun κ => if hκ : κ = 0 then 0 else (ρ₂ (χ.symm (Units.mk0 κ hκ)) : K)
    with hψ₂def
  set ψ₃ : K → K := fun κ => if hκ : κ = 0 then 0 else (ρ₃ (χ.symm (Units.mk0 κ hκ)) : K)
    with hψ₃def
  have hψ₂ : ∀ κ : K, κ ≠ 0 → ∀ α β, b (κ * α) (κ * β) = ψ₂ κ * b α β := by
    intro κ hκ α β
    set g := χ.symm (Units.mk0 κ hκ)
    have e1 : ∀ x ∈ P, ℓ₁ (g.1⁻¹ * x * g.1) = κ * ℓ₁ x := fun x hx => by
      rw [h1ρ g x hx, hχs κ hκ]
    calc b (κ * α) (κ * β) = b (ℓ₁ (g.1⁻¹ * s₁ α * g.1)) (ℓ₁ (g.1⁻¹ * s₁ β * g.1)) := by
          rw [e1 _ (hs₁P α), e1 _ (hs₁P β), hs₁, hs₁]
      _ = ℓ₂ (g.1⁻¹ * tc (s₁ α) (s₁ β) * g.1) := by
          rw [← hbwd _ _ (conj_mem_P h (hs₁P α)) (conj_mem_P h (hs₁P β)), tc_conj]
      _ = ψ₂ κ * b α β := by
          rw [h2ρ g _ (tc_mem_commutator (hs₁P α) (hs₁P β))]
          simp only [hψ₂def, hκ, dite_false]
          rfl
  have hψ₃ : ∀ κ : K, κ ≠ 0 → ∀ x y, c (ψ₂ κ * x) (κ * y) = ψ₃ κ * c x y := by
    intro κ hκ x y
    set g := χ.symm (Units.mk0 κ hκ)
    have e1 : ℓ₁ (g.1⁻¹ * s₁ y * g.1) = κ * y := by rw [h1ρ g _ (hs₁P y), hχs κ hκ, hs₁]
    have e2 : ℓ₂ (g.1⁻¹ * s₂ x * g.1) = ψ₂ κ * x := by
      rw [h2ρ g _ (hs₂P x), hs₂]
      simp only [hψ₂def, hκ, dite_false]
      rfl
    calc c (ψ₂ κ * x) (κ * y) = c (ℓ₂ (g.1⁻¹ * s₂ x * g.1)) (ℓ₁ (g.1⁻¹ * s₁ y * g.1)) := by
          rw [e1, e2]
      _ = ℓ₃ (g.1⁻¹ * tc (s₂ x) (s₁ y) * g.1) := by
          rw [← hcwd _ _ (conj_mem_commutator h (hs₂P x)) (conj_mem_P h (hs₁P y)), tc_conj]
      _ = ψ₃ κ * c x y := by
          rw [h3ρ g _ (tc_mem_zc h (hs₂P x) (hs₁P y))]
          simp only [hψ₃def, hκ, dite_false]
          rfl
  have hjac : ∀ α β γ, c (b α β) γ + c (b β γ) α + c (b γ α) β = 0 := by
    intro α β γ
    have hx := hs₁P α
    have hy := hs₁P β
    have hz := hs₁P γ
    have e : ∀ {u v w : N}, u ∈ P → v ∈ P → w ∈ P →
        c (b (ℓ₁ u) (ℓ₁ v)) (ℓ₁ w) = ℓ₃ (tc (tc u v) w) := fun hu hv hw => by
      rw [← hbwd _ _ hu hv, hcwd _ _ (tc_mem_commutator hu hv) hw]
    have := jacobi h hx hy hz
    have hm1 := tc_mem_zc h (tc_mem_commutator hx hy) hz
    have hm2 := tc_mem_zc h (tc_mem_commutator hz hx) hy
    have hm3 := tc_mem_zc h (tc_mem_commutator hy hz) hx
    have hsum := congrArg ℓ₃ this
    rw [h3.add _ ((zc P).mul_mem hm1 hm2) _ hm3, h3.add _ hm1 _ hm2, h3.one] at hsum
    rw [← hs₁ α, ← hs₁ β, ← hs₁ γ, e hx hy hz, e hy hz hx, e hz hx hy]
    linear_combination hsum
  have hnd2 : ∀ x y, y ≠ 0 → c x y = 0 → x = 0 := by
    intro x y hy hc0
    obtain ⟨x₁, hx₁, hx₁y, hx₁inv⟩ := hlift y
    have : ℓ₃ (tc (s₂ x) x₁) = 0 := by rw [hcwd _ _ (hs₂P x) hx₁, hs₂, hx₁y]; exact hc0
    have := hc_inj x₁ hx₁ (hx₁y ▸ hy) hx₁inv (s₂ x) (hs₂P x) this
    rwa [hs₂] at this
  have hnd1 : ∀ α β, α ≠ 0 → b α β = 0 → β = 0 ∨ β = α ∨ β = -α := by
    intro α β hα hb0
    obtain ⟨x, hx, hxα, hxinv⟩ := hlift α
    have hxP2 : x ∉ ⁅P, P⁆ := fun hm' => hα (hxα ▸ (h1.ker x hx).2 hm')
    set y := s₁ β
    have hy := hs₁P β
    have hxy : tc x y ∈ zc P := by
      refine (h2.ker _ (tc_mem_commutator hx hy)).1 ?_
      rw [hbwd _ _ hx hy, hxα, hs₁]
      exact hb0
    have hcα : Function.Injective fun l => c l α := by
      intro l l' hll
      have h0 : c (l - l') α = 0 := by
        have e := hc1 (l - l') l' α
        rw [sub_add_cancel] at e
        simp only at hll
        linear_combination hll - e
      have := hnd2 _ _ hα h0
      exact sub_eq_zero.1 this
    obtain ⟨l, hl⟩ := (Finite.injective_iff_surjective.1 hcα) (ℓ₃ (tc x y))
    set w := s₂ l
    have hw := hs₂P l
    have hwx : tc w x = tc x y := by
      have e : ℓ₃ (tc w x) = ℓ₃ (tc x y) := by
        rw [hcwd _ _ hw hx, hs₂, hxα]
        exact hl
      have := (h3.eq_iff (tc_mem_zc h hw hx) hxy).1 e
      rw [Subgroup.mem_bot, inv_mul_eq_one] at this
      exact this.symm
    have hcomm : x * (y * w) = (y * w) * x := by
      have e1 : w⁻¹ * tc x y * w = tc x y := by
        rw [mul_assoc, zc_comm hxy (commutator_le h hw), ← mul_assoc, inv_mul_cancel, one_mul]
      have e : tc x (y * w) = 1 := by
        rw [tc_mul_right, e1, ← tc_inv, hwx, inv_mul_cancel]
      exact tc_eq_one_iff.1 e
    have hyw : y * w ∈ P ⊓ Subgroup.centralizer {x} :=
      ⟨P.mul_mem hy (commutator_le h hw), Subgroup.mem_centralizer_singleton_iff.2 hcomm.symm⟩
    rw [h.centralizer_of_notMem_commutator x hx hxP2] at hyw
    have hyw' : y * w ∈ Subgroup.zpowers x ⊔ zc P := hyw
    have := zc_normal' h
    obtain ⟨u, hu, z, hz, huz⟩ := Subgroup.mem_sup_of_normal_right.1 hyw'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    have e : β = (k : K) * α := by
      have e1 := congrArg ℓ₁ huz
      rw [h1.add _ (P.zpow_mem hx k) _ (zc_le P hz), h1.zpow hx,
        (h1.ker _ (zc_le P hz)).2 (zc_le_commutator h hz), add_zero, hxα,
        h1.add _ hy _ (commutator_le h hw), (h1.ker _ (commutator_le h hw)).2 hw, add_zero,
        hs₁] at e1
      exact e1.symm
    rcases intCast_trichotomy (K := K) k with hk | hk | hk
    · left; rw [e, hk, zero_mul]
    · right; left; rw [e, hk, one_mul]
    · right; right; rw [e, hk, neg_one_mul]
  obtain ⟨s, t₁, t₃, u₂, u₃, hu₂, hu₃, -, hfix, hbf, hcf⟩ :=
    bracket_normal_form hK hm hq3 hb1 hb2 hc1 hc2 hψ₂ hψ₃ halt hjac hnd1 hnd2
  set σ : K ≃+* K := frE hK s with hσ
  set τ₁ : K ≃+* K := frE hK t₁ with hτ₁
  set χ' : R ≃* Kˣ := χ.trans (Units.mapEquiv τ₁.toMulEquiv) with hχ'
  have hχ'v : ∀ g : R, (χ' g : K) = fr m t₁ (ρ₁ g : K) := fun g => rfl
  have hχ's : ∀ κ : Kˣ, fr m t₁ (ρ₁ (χ'.symm κ) : K) = κ := fun κ => by
    rw [← hχ'v, MulEquiv.apply_symm_apply]
  have hfr_inv : ∀ (t : ZMod m) (a : K), fr m t (fr m (-t) a) = a := fun t a => by
    rw [fr_fr hK, add_neg_cancel, fr_zero_idx]
  refine ⟨σ, R.subtype.comp χ'.symm.toMonoidHom, fun x => fr m t₁ (ℓ₁ x),
    fun y => u₂ * ℓ₂ y, fun z => fr m t₃ (u₃ * ℓ₃ z), ?_⟩
  have c1 : IsCoord P ⁅P, P⁆ fun x => fr m t₁ (ℓ₁ x) :=
    ⟨fun x hx y hy => by simp only [h1.add x hx y hy, fr_add_arg],
      fun x hx => by simp only [fr_eq_zero_iff, h1.ker x hx],
      fun a => by
        obtain ⟨x, hx, hxa⟩ := h1.surj (fr m (-t₁) a)
        exact ⟨x, hx, by simp only [hxa, hfr_inv]⟩⟩
  have c2 : IsCoord ⁅P, P⁆ (zc P) fun y => u₂ * ℓ₂ y :=
    ⟨fun x hx y hy => by simp only [h2.add x hx y hy, mul_add],
      fun x hx => by simp only [mul_eq_zero, hu₂, false_or, h2.ker x hx],
      fun a => by
        obtain ⟨x, hx, hxa⟩ := h2.surj (u₂⁻¹ * a)
        exact ⟨x, hx, by simp only [hxa, mul_inv_cancel_left₀ hu₂]⟩⟩
  have c3 : IsCoord (zc P) ⊥ fun z => fr m t₃ (u₃ * ℓ₃ z) :=
    ⟨fun x hx y hy => by simp only [h3.add x hx y hy, mul_add, fr_add_arg],
      fun x hx => by simp only [fr_eq_zero_iff, mul_eq_zero, hu₃, false_or, h3.ker x hx],
      fun a => by
        obtain ⟨x, hx, hxa⟩ := h3.surj (u₃⁻¹ * fr m (-t₃) a)
        exact ⟨x, hx, by simp only [hxa, mul_inv_cancel_left₀ hu₃, hfr_inv]⟩⟩
  have br1 : ∀ x y : N, x ∈ P → y ∈ P → u₂ * ℓ₂ (tc x y) =
      σ (fr m t₁ (ℓ₁ x)) * fr m t₁ (ℓ₁ y) - fr m t₁ (ℓ₁ x) * σ (fr m t₁ (ℓ₁ y)) := by
    intro x y hx hy
    rw [hbwd x y hx hy, hbf]
    rfl
  have br2 : ∀ y x : N, y ∈ ⁅P, P⁆ → x ∈ P →
      fr m t₃ (u₃ * ℓ₃ (tc y x)) = u₂ * ℓ₂ y * fr m t₁ (ℓ₁ x) := by
    intro y x hy hx
    rw [hcwd y x hy hx, hcf]
  have heq1 : ∀ (κ : Kˣ) (x : N), x ∈ P →
      fr m t₁ (ℓ₁ ((χ'.symm κ).1⁻¹ * x * (χ'.symm κ).1)) = κ * fr m t₁ (ℓ₁ x) := by
    intro κ x hx
    rw [h1ρ _ x hx, fr_mul_arg, hχ's]
  obtain ⟨y₀, hy₀⟩ : ∃ y : K, σ y ≠ y := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset K) ⊆ {0, 1, -1} := fun x _ => by
      rcases hfix x (hcon x) with h' | h' | h' <;> simp [h']
    have := Finset.card_le_card hsub
    rw [Finset.card_univ] at this
    have h3' : ({0, 1, -1} : Finset K).card ≤ 3 := Finset.card_le_three
    omega
  obtain ⟨x₁, hx₁, hx₁1⟩ := c1.surj 1
  obtain ⟨y₁, hy₁, hy₁0⟩ := c1.surj y₀
  obtain ⟨y₂, hy₂, hy₂1⟩ := c2.surj 1
  have hρ₂ : ∀ κ : Kˣ, (ρ₂ (χ'.symm κ) : K) = κ * σ κ := by
    intro κ
    set g := χ'.symm κ
    have hA : u₂ * ℓ₂ (tc x₁ y₁) = y₀ - σ y₀ := by rw [br1 _ _ hx₁ hy₁, hx₁1, hy₁0]; simp
    have hA0 : y₀ - σ y₀ ≠ 0 := sub_ne_zero.2 (Ne.symm hy₀)
    have e1 := h2ρ g _ (tc_mem_commutator hx₁ hy₁)
    rw [tc_conj] at e1
    have e2 := br1 (g.1⁻¹ * x₁ * g.1) (g.1⁻¹ * y₁ * g.1) (conj_mem_P h hx₁) (conj_mem_P h hy₁)
    rw [heq1 κ x₁ hx₁, heq1 κ y₁ hy₁, e1, hx₁1, hy₁0] at e2
    have key : ((ρ₂ g : K) - κ * σ κ) * (y₀ - σ y₀) = 0 := by
      simp only [map_mul, mul_one] at e2
      linear_combination e2 - (ρ₂ g : K) * hA
    exact sub_eq_zero.1 ((mul_eq_zero.1 key).resolve_right hA0)
  have hρ₃ : ∀ κ : Kˣ, fr m t₃ (ρ₃ (χ'.symm κ) : K) = κ ^ 2 * σ κ := by
    intro κ
    set g := χ'.symm κ
    have hB : fr m t₃ (u₃ * ℓ₃ (tc y₂ x₁)) = 1 := by rw [br2 _ _ hy₂ hx₁, hy₂1, hx₁1, one_mul]
    have e1 := h3ρ g _ (tc_mem_zc h hy₂ hx₁)
    rw [tc_conj] at e1
    have e2 := br2 (g.1⁻¹ * y₂ * g.1) (g.1⁻¹ * x₁ * g.1) (conj_mem_commutator h hy₂)
      (conj_mem_P h hx₁)
    calc fr m t₃ (ρ₃ g : K) = fr m t₃ (ρ₃ g : K) * fr m t₃ (u₃ * ℓ₃ (tc y₂ x₁)) := by
          rw [hB, mul_one]
      _ = fr m t₃ (u₃ * ℓ₃ (tc (g.1⁻¹ * y₂ * g.1) (g.1⁻¹ * x₁ * g.1))) := by
          rw [e1, ← fr_mul_arg]; ring_nf
      _ = u₂ * ℓ₂ (g.1⁻¹ * y₂ * g.1) * fr m t₁ (ℓ₁ (g.1⁻¹ * x₁ * g.1)) := e2
      _ = (ρ₂ g : K) * (u₂ * ℓ₂ y₂) * (κ * fr m t₁ (ℓ₁ x₁)) := by
          rw [h2ρ g y₂ hy₂, heq1 κ x₁ hx₁]; ring
      _ = κ ^ 2 * σ κ := by rw [hρ₂ κ, hy₂1, hx₁1]; ring
  exact ⟨hfix, fun κ => (χ'.symm κ).2, fun x hx => ⟨χ' ⟨x, hx⟩, by simp⟩,
    fun κ κ' hκ => χ'.symm.injective (Subtype.ext hκ), c1, c2, c3,
    fun κ x hx => heq1 κ x hx,
    fun κ y hy => by
      show u₂ * ℓ₂ ((χ'.symm κ).1⁻¹ * y * (χ'.symm κ).1) = κ * σ κ * (u₂ * ℓ₂ y)
      rw [h2ρ _ y hy, hρ₂]; ring,
    fun κ z hz => by
      show fr m t₃ (u₃ * ℓ₃ ((χ'.symm κ).1⁻¹ * z * (χ'.symm κ).1)) =
        κ ^ 2 * σ κ * fr m t₃ (u₃ * ℓ₃ z)
      rw [h3ρ _ z hz, show u₃ * ((ρ₃ (χ'.symm κ) : K) * ℓ₃ z) =
        (ρ₃ (χ'.symm κ) : K) * (u₃ * ℓ₃ z) by ring, fr_mul_arg, hρ₃],
    br1, br2⟩

end CFSG.Walter.Ree.Thompson1

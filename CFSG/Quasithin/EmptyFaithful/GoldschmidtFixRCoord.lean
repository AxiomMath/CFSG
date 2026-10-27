module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFixRGeom
public import CFSG.Quasithin.EmptyFaithful.SBc16FCoord
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFixRMod2

public section

namespace CFSG.Quasithin.FixR

open CFSG.Quasithin CFSG.Quasithin.SBc16

variable {W : Type} [CommGroup W]

@[expose] def Ru (R : Z52 →* MulAut W) (u : Vec) : MulAut W := R (Multiplicative.ofAdd u)

theorem Ru_add (R : Z52 →* MulAut W) (u v : Vec) : Ru R (u + v) = Ru R u * Ru R v := by
  simp [Ru, ofAdd_add, map_mul]

theorem Ru_zero (R : Z52 →* MulAut W) : Ru R 0 = 1 := by simp [Ru]

theorem Ru_nsmul (R : Z52 →* MulAut W) (n : ℕ) (u : Vec) : Ru R (n • u) = Ru R u ^ n := by
  rw [Ru, ofAdd_nsmul, map_pow]
  rfl

theorem Ru_mem (R : Z52 →* MulAut W) (u : Vec) : Ru R u ∈ R.range := ⟨_, rfl⟩

theorem Ru_pow_five (R : Z52 →* MulAut W) (u : Vec) : Ru R u ^ 5 = 1 := by
  rw [← Ru_nsmul]
  have h5 : (5 : ZMod 5) = 0 := by decide
  have : (5 : ℕ) • u = 0 := by
    ext i
    simp [nsmul_eq_mul, h5]
  rw [this, Ru_zero]

theorem Ru_injective {R : Z52 →* MulAut W} (hR : Function.Injective R) :
    Function.Injective (Ru R) := fun _ _ h =>
  Multiplicative.ofAdd.injective (hR h)

theorem Ru_ne_one {R : Z52 →* MulAut W} (hR : Function.Injective R) {u : Vec} (hu : u ≠ 0) :
    Ru R u ≠ 1 := by
  intro h
  exact hu (Ru_injective hR (h.trans (Ru_zero R).symm))

theorem orderOf_Ru {R : Z52 →* MulAut W} (hR : Function.Injective R) {u : Vec} (hu : u ≠ 0) :
    orderOf (Ru R u) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime (Ru_pow_five R u) (Ru_ne_one hR hu)

@[expose] def ln (R : Z52 →* MulAut W) (u : Vec) : Subgroup (MulAut W) :=
  Subgroup.zpowers (Ru R u)

theorem ln_le (R : Z52 →* MulAut W) (u : Vec) : ln R u ≤ R.range :=
  (Subgroup.zpowers_le).mpr (Ru_mem R u)

theorem card_ln {R : Z52 →* MulAut W} (hR : Function.Injective R) {u : Vec} (hu : u ≠ 0) :
    Nat.card (ln R u) = 5 := by
  rw [ln, Nat.card_zpowers, orderOf_Ru hR hu]

theorem ln_ne {R : Z52 →* MulAut W} (hR : Function.Injective R) {u v : Vec}
    (h : det2 u v ≠ 0) : ln R u ≠ ln R v := by
  intro heq
  have hu : u ≠ 0 := by
    rintro rfl
    apply h
    simp [det2]
  have hv : Ru R v ∈ ln R u := by
    rw [heq]
    exact Subgroup.mem_zpowers _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hv
  have hk' : (Ru R u) ^ (k % (5 : ℤ)) = Ru R v := by
    have := zpow_mod_orderOf (Ru R u) k
    rw [orderOf_Ru hR hu] at this
    rw [show ((5 : ℕ) : ℤ) = 5 from rfl] at this
    rw [this]
    exact hk
  have hn' : (((k % 5).toNat : ℕ) : ℤ) = k % 5 :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
  have hRn : Ru R ((k % 5).toNat • u) = Ru R v := by
    rw [Ru_nsmul, ← zpow_natCast, hn']
    exact hk'
  have hvu : v = (k % 5).toNat • u := (Ru_injective hR hRn).symm
  apply h
  rw [hvu]
  simp [det2]
  ring

@[expose] noncomputable def cmHom (R : Z52 →* MulAut W) (hR : Function.Injective R) :
    ↥(Subgroup.normalizer (R.range : Set (MulAut W))) →* Matrix (Fin 2) (Fin 2) (ZMod 5) :=
  matHom.comp ((MulAut.congr (MonoidHom.ofInjective hR).symm).toMonoidHom.comp
    R.range.normalizerMonoidHom)

theorem R_conj {R : Z52 →* MulAut W} (hR : Function.Injective R)
    (γ : ↥(Subgroup.normalizer (R.range : Set (MulAut W)))) (z : Z52) :
    R ((MulAut.congr (MonoidHom.ofInjective hR).symm (R.range.normalizerMonoidHom γ)) z) =
      (γ : MulAut W) * R z * (γ : MulAut W)⁻¹ := by
  have h3 : (((MonoidHom.ofInjective hR)
      ((MulAut.congr (MonoidHom.ofInjective hR).symm (R.range.normalizerMonoidHom γ)) z) :
        ↥R.range) : MulAut W) =
      (((R.range.normalizerMonoidHom γ) ((MonoidHom.ofInjective hR) z) : ↥R.range) :
        MulAut W) := by
    congr 1
    exact MulEquiv.apply_symm_apply _ _
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h3
  exact h3

theorem conj_Ru {R : Z52 →* MulAut W} (hR : Function.Injective R)
    (γ : ↥(Subgroup.normalizer (R.range : Set (MulAut W)))) (e : Vec) :
    (γ : MulAut W) * Ru R e * (γ : MulAut W)⁻¹ = Ru R ((cmHom R hR γ).mulVec e) := by
  have h1 : cmHom R hR γ = matOf ((MulAut.congr (MonoidHom.ofInjective hR).symm)
      (R.range.normalizerMonoidHom γ)) := rfl
  rw [h1, ← matOf_apply]
  exact (R_conj hR γ (Multiplicative.ofAdd e)).symm

theorem centralizes_of_cm_eq_one {R : Z52 →* MulAut W} (hR : Function.Injective R)
    {γ : ↥(Subgroup.normalizer (R.range : Set (MulAut W)))} (h : cmHom R hR γ = 1) :
    ∀ κ ∈ R.range, (γ : MulAut W) * κ = κ * (γ : MulAut W) := by
  rintro κ ⟨z, rfl⟩
  have h1 := conj_Ru hR γ (Multiplicative.toAdd z)
  rw [h, Matrix.one_mulVec] at h1
  have h2 : Ru R (Multiplicative.toAdd z) = R z := rfl
  rw [h2] at h1
  exact mul_inv_eq_iff_eq_mul.mp h1

theorem matrix_eq_one_of_mulVec (M : Matrix (Fin 2) (Fin 2) (ZMod 5))
    (h : ∀ e : Vec, M.mulVec e = e) : M = 1 := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply, eq_comm] using this

theorem cm_eq_one_of_centralizes {R : Z52 →* MulAut W} (hR : Function.Injective R)
    {γ : ↥(Subgroup.normalizer (R.range : Set (MulAut W)))}
    (h : ∀ κ ∈ R.range, (γ : MulAut W) * κ = κ * (γ : MulAut W)) : cmHom R hR γ = 1 := by
  apply matrix_eq_one_of_mulVec
  intro e
  apply Ru_injective hR
  rw [← conj_Ru hR γ e, mul_inv_eq_iff_eq_mul]
  exact h _ (Ru_mem R e)

theorem basis_bijective {u₀ u₁ : Vec} (hdet : det2 u₀ u₁ ≠ 0) :
    Function.Bijective (fun p : ZMod 5 × ZMod 5 => p.1 • u₀ + p.2 • u₁) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hinj : Function.Injective (fun p : ZMod 5 × ZMod 5 => p.1 • u₀ + p.2 • u₁) := by
    rintro ⟨s, t⟩ ⟨s', t'⟩ h
    have e0 := congrFun h 0
    have e1 := congrFun h 1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e0 e1
    have hs : (s - s') * det2 u₀ u₁ = 0 := by
      simp only [det2]
      linear_combination u₁ 1 * e0 - u₁ 0 * e1
    have ht : (t - t') * det2 u₀ u₁ = 0 := by
      simp only [det2]
      linear_combination u₀ 0 * e1 - u₀ 1 * e0
    have hs' : s = s' := sub_eq_zero.mp ((mul_eq_zero.mp hs).resolve_right hdet)
    have ht' : t = t' := sub_eq_zero.mp ((mul_eq_zero.mp ht).resolve_right hdet)
    rw [hs', ht']
  refine hinj.bijective_of_nat_card_le ?_
  simp [Nat.card_eq_fintype_card, ZMod.card]

@[expose] noncomputable def Nu (R : Z52 →* MulAut W) (u : Vec) (w : W) : W :=
  ∏ t : ZMod 5, Ru R (t • u) w

theorem Ru_Nu (R : Z52 →* MulAut W) (u : Vec) (w : W) : Ru R u (Nu R u w) = Nu R u w := by
  unfold Nu
  rw [map_prod]
  refine Fintype.prod_equiv (Equiv.addRight (1 : ZMod 5)) _ _ (fun t => ?_)
  show (Ru R u * Ru R (t • u)) w = Ru R ((t + 1) • u) w
  rw [← Ru_add, add_smul, one_smul, add_comm]

theorem Nu_mem_commV (R : Z52 →* MulAut W) {w : W} (hw : w ∈ commV R.range) (u : Vec) :
    Nu R u w ∈ commV R.range := by
  unfold Nu
  exact Subgroup.prod_mem _ fun t _ =>
    apply_mem_commV R.range (Subgroup.le_normalizer (Ru_mem R _)) hw

theorem Nu_mem_tp (R : Z52 →* MulAut W) {w : W} (hw : w ∈ commV R.range) (u : Vec) :
    Nu R u w ∈ tp R.range (ln R u) := by
  refine ⟨?_, Nu_mem_commV R hw u⟩
  have : ln R u ≤ MulAction.stabilizer (MulAut W) (Nu R u w) :=
    (Subgroup.zpowers_le).mpr (Ru_Nu R u w)
  exact fun x hx => this hx

theorem prod_identity (F : ZMod 5 → ZMod 5 → W) :
    (∏ j : ZMod 5, ∏ t : ZMod 5, F t (t * j)) * ∏ t : ZMod 5, F 0 t =
      F 0 0 ^ 5 * ∏ s : ZMod 5, ∏ t : ZMod 5, F s t := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [Finset.prod_comm]
  set G : ZMod 5 → W := fun t => ∏ j : ZMod 5, F t (t * j) with hGdef
  set H : ZMod 5 → W := fun t => ∏ j : ZMod 5, F t j with hHdef
  have h0 : G 0 = F 0 0 ^ 5 := by simp [hGdef]
  have hne : ∀ t ∈ (Finset.univ : Finset (ZMod 5)).erase 0, G t = H t := by
    intro t ht
    have ht0 : t ≠ 0 := Finset.ne_of_mem_erase ht
    exact Fintype.prod_equiv (Equiv.mulLeft₀ t ht0) _ _ (fun j => rfl)
  have e1 : ∏ t, G t = G 0 * ∏ t ∈ (Finset.univ : Finset (ZMod 5)).erase 0, H t := by
    rw [← Finset.mul_prod_erase Finset.univ G (Finset.mem_univ 0)]
    congr 1
    exact Finset.prod_congr rfl hne
  have e2 : ∏ t, H t = H 0 * ∏ t ∈ (Finset.univ : Finset (ZMod 5)).erase 0, H t :=
    (Finset.mul_prod_erase Finset.univ H (Finset.mem_univ 0)).symm
  show (∏ t, G t) * H 0 = F 0 0 ^ 5 * ∏ s, H s
  rw [e1, e2, h0]
  ac_rfl

theorem Nu_identity (R : Z52 →* MulAut W) (hW : ∀ w : W, w ^ 2 = 1) {u₀ u₁ : Vec}
    (hdet : det2 u₀ u₁ ≠ 0) (w : W) :
    (∏ j : ZMod 5, Nu R (u₀ + j • u₁) w) * Nu R u₁ w = w * ∏ e : Vec, Ru R e w := by
  set F : ZMod 5 → ZMod 5 → W := fun s t => Ru R (s • u₀ + t • u₁) w with hF
  have hN : ∀ j : ZMod 5, Nu R (u₀ + j • u₁) w = ∏ t, F t (t * j) := by
    intro j
    unfold Nu
    refine Finset.prod_congr rfl fun t _ => ?_
    simp only [hF, smul_add, smul_smul]
  have hN1 : Nu R u₁ w = ∏ t, F 0 t := by
    unfold Nu
    refine Finset.prod_congr rfl fun t _ => ?_
    simp only [hF, zero_smul, zero_add]
  have hall : ∏ e : Vec, Ru R e w = ∏ s : ZMod 5, ∏ t : ZMod 5, F s t := by
    rw [← Fintype.prod_prod_type (fun p : ZMod 5 × ZMod 5 => F p.1 p.2)]
    exact (Fintype.prod_equiv (Equiv.ofBijective _ (basis_bijective hdet))
      (fun p : ZMod 5 × ZMod 5 => F p.1 p.2) (fun e : Vec => Ru R e w) (fun p => rfl)).symm
  have hF00 : F 0 0 = w := by simp [hF, Ru_zero]
  have hw5 : w ^ 5 = w := by
    have : w ^ 5 = (w ^ 2) ^ 2 * w := by rw [← pow_mul, ← pow_succ]
    rw [this, hW w, one_pow, one_mul]
  simp only [hN, hN1, hall]
  rw [prod_identity F, hF00, hw5]

theorem card_Z52 : Nat.card Z52 = 25 := by
  rw [Nat.card_congr (Multiplicative.toAdd : Z52 ≃ (Fin 2 → ZMod 5))]
  simp [Nat.card_eq_fintype_card, ZMod.card]

theorem card_range {R : Z52 →* MulAut W} (hR : Function.Injective R) :
    Nat.card R.range = 25 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective hR).toEquiv, card_Z52]

theorem normHom_fixed (P : Subgroup (MulAut W)) [Fintype ↥P] {x : MulAut W} (hx : x ∈ P) (w : W) :
    x (normHom P w) = normHom P w := by
  rw [normHom_apply, map_prod]
  exact Fintype.prod_equiv (Equiv.mulLeft (⟨x, hx⟩ : ↥P)) _ _ (fun κ => rfl)

theorem normHom_eq_prod {R : Z52 →* MulAut W} (hR : Function.Injective R) [Fintype ↥R.range]
    (w : W) : normHom R.range w = ∏ e : Vec, Ru R e w := by
  rw [normHom_apply]
  refine (Fintype.prod_equiv (Equiv.ofBijective
    (fun e : Vec => (⟨Ru R e, Ru_mem R e⟩ : ↥R.range)) ⟨fun e e' h => ?_, ?_⟩)
    (fun e : Vec => Ru R e w) (fun κ : ↥R.range => (κ : MulAut W) w) (fun e => rfl)).symm
  · exact Ru_injective hR (congrArg Subtype.val h)
  · rintro ⟨_, z, rfl⟩
    exact ⟨Multiplicative.toAdd z, rfl⟩

theorem eq_one_of_fixes_commV (hW : ∀ w : W, w ^ 2 = 1) (P : Subgroup (MulAut W)) [Fintype ↥P]
    (hP : Fintype.card ↥P = 25) {γ : MulAut W} (hγ : γ ∈ P) (hc : ∀ w ∈ commV P, γ w = w) :
    γ = 1 := by
  refine MulEquiv.ext fun w => ?_
  rw [MulAut.one_apply]
  have hu : (∏ κ : ↥P, ((κ : MulAut W) w * w⁻¹)) ∈ commV P :=
    Subgroup.prod_mem _ fun κ _ => Subgroup.subset_closure ⟨κ, κ.2, w, rfl⟩
  have hu' : (∏ κ : ↥P, ((κ : MulAut W) w * w⁻¹)) = normHom P w * w := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hP, inv_eq_self_of_sq hW,
      normHom_apply]
    have : w ^ 25 = w := by
      have h : w ^ 25 = (w ^ 2) ^ 12 * w := by rw [← pow_mul, ← pow_succ]
      rw [h, hW w, one_pow, one_mul]
    rw [this]
  have h1 := hc _ hu
  rw [hu', map_mul, normHom_fixed P hγ] at h1
  exact mul_left_cancel h1

theorem exists_part_ne_bot [Finite W] (hW : ∀ w : W, w ^ 2 = 1) (R : Z52 →* MulAut W)
    (hR : Function.Injective R) {u₀ : Vec} (hu₀ : u₀ ≠ 0) :
    ∃ u : Vec, det2 u₀ u ≠ 0 ∧ tp R.range (ln R u) ≠ ⊥ := by
  by_contra hcon
  push Not at hcon
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fintype ↥R.range := Fintype.ofFinite _
  obtain ⟨u₁, hdet⟩ := exists_indep u₀ hu₀
  have hP : Fintype.card ↥R.range = 25 := by
    rw [← Nat.card_eq_fintype_card, card_range hR]
  have key : ∀ w ∈ commV R.range, Ru R u₀ w = w := by
    intro w hw
    have hid := Nu_identity R hW hdet w
    have h1 : ∀ j : ZMod 5, j ≠ 0 → Nu R (u₀ + j • u₁) w = 1 := by
      intro j hj
      have hd : det2 u₀ (u₀ + j • u₁) ≠ 0 := by
        have : det2 u₀ (u₀ + j • u₁) = j * det2 u₀ u₁ := by
          simp only [det2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          ring
        rw [this]
        exact mul_ne_zero hj hdet
      have := Nu_mem_tp R hw (u₀ + j • u₁)
      rw [hcon _ hd] at this
      exact Subgroup.mem_bot.mp this
    have h2 : Nu R u₁ w = 1 := by
      have := Nu_mem_tp R hw u₁
      rw [hcon _ hdet] at this
      exact Subgroup.mem_bot.mp this
    have hprod : ∏ j : ZMod 5, Nu R (u₀ + j • u₁) w = Nu R u₀ w := by
      rw [Finset.prod_eq_single (0 : ZMod 5)]
      · simp
      · intro j _ hj
        exact h1 j hj
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hnorm : ∏ e : Vec, Ru R e w = 1 := by
      rw [← normHom_eq_prod hR]
      exact MonoidHom.mem_ker.mp (commV_le_ker_normHom R.range hw)
    rw [hprod, h2, mul_one, hnorm, mul_one] at hid
    calc Ru R u₀ w = Ru R u₀ (Nu R u₀ w) := by rw [hid]
      _ = Nu R u₀ w := Ru_Nu R u₀ w
      _ = w := hid
  have h1 : Ru R u₀ = 1 := eq_one_of_fixes_commV hW R.range hP (Ru_mem R u₀) key
  exact hu₀ (Ru_injective hR (h1.trans (Ru_zero R).symm))

end CFSG.Quasithin.FixR

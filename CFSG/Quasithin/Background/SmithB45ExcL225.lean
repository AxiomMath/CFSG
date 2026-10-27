module

public import CFSG.Quasithin.Background.SmithB45ExcL2Sq

public section

namespace CFSG.Quasithin.B45Exc

open Module CFSG.QuasithinUnique.Setup.Family

section Blocks

variable {p : ℕ} [hpf : Fact p.Prime] {K : Type} [Field K] [Fintype K] [CharP K p]
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Module.Finite (ZMod 2) E]
variable (hK : Fintype.card K = p ^ 2) (U : Multiplicative K →* (E ≃ₗ[ZMod 2] E))

include hK in
theorem two_le_rank_Bl (hp5 : 5 ≤ p) {g : Kˣ} (hg : ∀ x : Kˣ, x ∈ Subgroup.zpowers g)
    {s : E ≃ₗ[ZMod 2] E} (hs : s * s = 1)
    (hsU : ∀ a : K, s * U (Multiplicative.ofAdd a) * s⁻¹ = U (Multiplicative.ofAdd (-a)))
    {j : ℕ} (hj : Bl U g j ≠ 0) :
    2 ≤ finrank (ZMod 2) ((LinearMap.range (Bl U g j)).map (sub1 s)) := by
  set M := LinearMap.range (Bl U g j) with hM
  set a : K := (g : K) ^ (j + 1) with ha
  set v := U (Multiplicative.ofAdd a) with hv
  have hne : ¬ j ≡ j + 1 [MOD p + 1] := by
    intro h
    have h1 : 0 ≡ 1 [MOD p + 1] := Nat.ModEq.add_left_cancel' j (by simpa using h)
    have h2 : (1 : ℕ) % (p + 1) = 1 := Nat.mod_eq_of_lt (by omega)
    unfold Nat.ModEq at h1
    rw [Nat.zero_mod, h2] at h1
    exact absurd h1 (by norm_num)
  have hab : ∀ l : ZMod p, a ≠ fpMap p K l * (g : K) ^ j :=
    not_mem_line_of_not_modEq hK hg hne
  have hb0 : (g : K) ^ j ≠ 0 := pow_ne_zero _ g.ne_zero
  have hfpf : ∀ x ∈ M, v x = x → x = 0 := fun x hx hvx => fpf_Eb hK U hp5 hb0 hab hx hvx
  have hvp : v ^ p = 1 := by
    rw [hv, ← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, ofAdd_zero,
      map_one]
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hsv : s * v * s = v⁻¹ := by
    have := hsU a
    rw [hsinv] at this
    rw [hv, this, ofAdd_neg, map_inv]
  have hsM : ∀ x ∈ M, s x ∈ M := by
    rintro _ ⟨y, rfl⟩
    exact ⟨s y, (LinearMap.congr_fun (inv_mul_Bl U hsU g j) y).symm⟩
  have hvM : ∀ x ∈ M, v x ∈ M := by
    rintro _ ⟨y, rfl⟩
    exact ⟨v y, (LinearMap.congr_fun (Uop_mul_Eb U a ((g : K) ^ j)) y).symm⟩
  have hhalf := finrank_half M hs hsv (hp_odd hp5) hvp hsM hvM hfpf
  have hdvd := orderOf_two_dvd_finrank_of_fpf hvp M hvM hfpf
  have hMne : M ≠ ⊥ := fun h0 => hj (LinearMap.range_eq_bot.1 h0)
  have hMpos := Submodule.one_le_finrank_iff.2 hMne
  have hpos : 0 < finrank (ZMod 2) (M.map (sub1 s)) := by omega
  rw [hhalf] at hdvd
  have h3 := three_le_orderOf_two (p := p) hp5
  have h4 := Nat.le_of_dvd (by omega) hdvd
  omega

include hK in
theorem six_le_rank_of_inv (hp5 : 5 ≤ p)
    (hU1 : ∀ a : K, a ≠ 0 → U (Multiplicative.ofAdd a) ≠ 1)
    (hT : ∀ c : K, c ≠ 0 → ∃ T : E ≃ₗ[ZMod 2] E, ∀ a : K,
      T * U (Multiplicative.ofAdd a) * T⁻¹ = U (Multiplicative.ofAdd (c ^ 2 * a)))
    {s : E ≃ₗ[ZMod 2] E} (hs : s * s = 1)
    (hsU : ∀ a : K, s * U (Multiplicative.ofAdd a) * s⁻¹ = U (Multiplicative.ofAdd (-a))) :
    6 ≤ finrank (ZMod 2) (LinearMap.range (sub1 s)) := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  obtain ⟨j₀, hj₀⟩ := exists_nonzero_Bl hK U hg hp5 hU1
  have hne : ∀ k : ℕ, Bl U g (j₀ + 2 * k) ≠ 0 := by
    intro k
    obtain ⟨T, hT'⟩ := hT ((g : K) ^ k) (pow_ne_zero _ g.ne_zero)
    exact Bl_ne_zero_add U hT' hj₀
  have hmod : ∀ k k' : ℕ, k < 3 → k' < 3 → k ≠ k' →
      ¬ (j₀ + 2 * k) ≡ (j₀ + 2 * k') [MOD p + 1] := by
    intro k k' hk hk' hkk' h
    have h1 := Nat.ModEq.add_left_cancel' j₀ h
    unfold Nat.ModEq at h1
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1
    omega
  have := sum_le_finrank_range_sub1 s (Finset.range 3) (fun k => Bl U g (j₀ + 2 * k))
    (fun k _ => Bl_mul_Bl_of_modEq U hK hg hp5 (Nat.ModEq.refl _))
    (fun k hk k' hk' hkk' => Bl_mul_Bl_of_not_modEq U hK hg hp5
      (hmod k k' (Finset.mem_range.1 hk) (Finset.mem_range.1 hk') hkk'))
    (fun k _ => inv_mul_Bl U hsU g _) (fun _ => 2)
    (fun k _ => two_le_rank_Bl hK U hp5 hg hs hsU (hne k))
  simpa using this

include hK in
theorem eight_le_rank_of_three_cycle (hp5 : p = 5) {g : Kˣ}
    (hg : ∀ x : Kˣ, x ∈ Subgroup.zpowers g)
    (hU1 : ∀ a : K, a ≠ 0 → U (Multiplicative.ofAdd a) ≠ 1)
    (hT : ∀ c : K, c ≠ 0 → ∃ T : E ≃ₗ[ZMod 2] E, ∀ a : K,
      T * U (Multiplicative.ofAdd a) * T⁻¹ = U (Multiplicative.ofAdd (c ^ 2 * a)))
    {Y : E ≃ₗ[ZMod 2] E} (hY : ∀ a : K, Y * U (Multiplicative.ofAdd a) * Y⁻¹ =
      U (Multiplicative.ofAdd (((g : K) ^ 16) ^ 2 * a))) :
    8 ≤ finrank (ZMod 2) (LinearMap.range (sub1 Y)) := by
  have hp5' : 5 ≤ p := by omega
  have hp7 : p ≠ 7 := by omega
  obtain ⟨j, hj⟩ := exists_nonzero_Bl hK U hg hp5' hU1
  obtain ⟨T1, hT1⟩ := hT ((g : K) ^ 1) (pow_ne_zero _ g.ne_zero)
  have hj2 : Bl U g (j + 2 * 1) ≠ 0 := Bl_ne_zero_add U hT1 hj
  have hmod : ∀ a b : ℕ, a % 6 = b % 6 → a ≡ b [MOD p + 1] := by
    intro a b h
    show a % (p + 1) = b % (p + 1)
    rw [hp5]
    exact h
  have hnmod : ∀ a b : ℕ, a % 6 ≠ b % 6 → ¬ a ≡ b [MOD p + 1] := by
    intro a b h h'
    apply h
    have : a % (p + 1) = b % (p + 1) := h'
    rwa [hp5] at this
  set P := Bl U g j with hP
  set Q := Bl U g (j + 2 * 1) with hQ
  set R := Bl U g (j + 2 * 1 + 2 * 1) with hR
  have hYP : (Y : Module.End (ZMod 2) E) * P = Q * (Y : Module.End (ZMod 2) E) := by
    rw [hP, hQ, torus_mul_Bl U hY j,
      Bl_eq_of_modEq U hK hg (j := j + 2 * 16) (j' := j + 2 * 1) (hmod _ _ (by omega))]
  have hYQ : (Y : Module.End (ZMod 2) E) * Q = R * (Y : Module.End (ZMod 2) E) := by
    rw [hQ, hR, torus_mul_Bl U hY (j + 2 * 1),
      Bl_eq_of_modEq U hK hg (j := j + 2 * 1 + 2 * 16) (j' := j + 2 * 1 + 2 * 1)
        (hmod _ _ (by omega))]
  have hPP : P * P = P := Bl_mul_Bl_of_modEq U hK hg hp5' (Nat.ModEq.refl _)
  have hQQ : Q * Q = Q := Bl_mul_Bl_of_modEq U hK hg hp5' (Nat.ModEq.refl _)
  have hPQ : P * Q = 0 := Bl_mul_Bl_of_not_modEq U hK hg hp5' (hnmod _ _ (by omega))
  have hQP : Q * P = 0 := Bl_mul_Bl_of_not_modEq U hK hg hp5' (hnmod _ _ (by omega))
  have hPR : P * R = 0 := Bl_mul_Bl_of_not_modEq U hK hg hp5' (hnmod _ _ (by omega))
  have hQR : Q * R = 0 := Bl_mul_Bl_of_not_modEq U hK hg hp5' (hnmod _ _ (by omega))
  have ap : ∀ {A B C : Module.End (ZMod 2) E}, A * B = C → ∀ y, A (B y) = C y :=
    fun h y => LinearMap.congr_fun h y
  have ap0 : ∀ {A B : Module.End (ZMod 2) E}, A * B = 0 → ∀ y, A (B y) = 0 :=
    fun h y => by simpa using LinearMap.congr_fun h y
  set N := LinearMap.range P ⊔ LinearMap.range Q with hN
  have hinj : ∀ x ∈ N, sub1 Y x = 0 → x = 0 := by
    intro x hx h0
    obtain ⟨x1, hx1, x2, hx2, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨y1, rfl⟩ := hx1
    obtain ⟨y2, rfl⟩ := hx2
    have hfix : Y (P y1 + Q y2) = P y1 + Q y2 := by
      rw [sub1_apply, sub_eq_zero] at h0
      exact h0
    have hY1 : Y (P y1) = Q (Y y1) := ap hYP y1
    have hY2 : Y (Q y2) = R (Y y2) := ap hYQ y2
    rw [map_add, hY1, hY2] at hfix
    have e1 := congrArg P hfix
    rw [map_add, map_add, ap0 hPQ, ap0 hPR, ap hPP, ap0 hPQ] at e1
    simp only [add_zero] at e1
    have e2 := congrArg Q hfix
    rw [map_add, map_add, ap hQQ, ap0 hQR, ap0 hQP, ap hQQ] at e2
    simp only [add_zero, zero_add] at e2
    have hP1 : P y1 = 0 := e1.symm
    have hQ1 : Q (Y y1) = 0 := by rw [← hY1, hP1, map_zero]
    have hQ2 : Q y2 = 0 := by rw [← e2, hQ1]
    rw [hP1, hQ2, add_zero]
  have hdisj : LinearMap.range P ⊓ LinearMap.range Q = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩ := Submodule.mem_inf.1 hx
    rw [Submodule.mem_bot]
    have h1 : P (P a) = P a := ap hPP a
    rw [← hb, ap0 hPQ] at h1
    rw [← hb]
    exact h1.symm
  have hdP := (block_dim hK U hp5' (b := (g : K) ^ j) hj).2 hp7
  have hdQ := (block_dim hK U hp5' (b := (g : K) ^ (j + 2 * 1)) hj2).2 hp7
  have hdN : finrank (ZMod 2) N = finrank (ZMod 2) (LinearMap.range P) +
      finrank (ZMod 2) (LinearMap.range Q) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range P) (LinearMap.range Q)
    rw [hdisj, finrank_bot, add_zero] at h
    exact h
  have h8 := finrank_le_range_of_injOn (sub1 Y) N hinj
  have hdP' : 4 ≤ finrank (ZMod 2) (LinearMap.range P) := hdP
  have hdQ' : 4 ≤ finrank (ZMod 2) (LinearMap.range Q) := hdQ
  omega

end Blocks

section PSL

open CFSG CFSG.GorensteinWalter CFSG.QuasithinUnique.Setup.X3 CFSG.SectionRank.OddCover

variable {p : ℕ} [hpf : Fact p.Prime] {K : Type} [Field K] [Fintype K] [CharP K p]

theorem psl2_square_inner_rank6 (hp5 : 5 ≤ p) (hK : Fintype.card K = p ^ 2) {E : Type*}
    [AddCommGroup E] [Module (ZMod 2) E] [Module.Finite (ZMod 2) E]
    (ρ : PSL2 K →* (E ≃ₗ[ZMod 2] E)) (hρ : Function.Injective ρ) {t : PSL2 K} (ht1 : t ≠ 1)
    (ht2 : t * t = 1) : 6 ≤ Module.finrank (ZMod 2) (LinearMap.range (disp ρ t)) := by
  have hodd : Odd p := hp_odd hp5
  obtain ⟨i0, hi0⟩ : IsSquare (-1 : K) := by
    rw [FiniteField.isSquare_neg_one_iff, hK, Nat.pow_mod]
    have h4 : p % 4 = 1 ∨ p % 4 = 3 := by have := Nat.odd_iff.1 hodd; omega
    rcases h4 with h4 | h4 <;> rw [h4] <;> norm_num
  have hi0' : i0 * i0 = -1 := hi0.symm
  have hi0ne : i0 ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hi0'
    exact one_ne_zero (neg_eq_zero.1 hi0'.symm)
  set i : Kˣ := Units.mk0 i0 hi0ne with hidef
  have hival : ((i : Kˣ) : K) = i0 := Units.val_mk0 _
  set t₀ : PSL2 K := pslMk (slD i) with ht₀def
  have ht₀U : ∀ a : K, t₀ * pslU (Multiplicative.ofAdd a) * t₀⁻¹ =
      pslU (Multiplicative.ofAdd (-a)) := by
    intro a
    rw [ht₀def, pslD_conj_pslU, hival, sq, hi0', neg_one_mul]
  have ht₀2 : t₀ * t₀ = 1 := pslMk_slD_sq (i := i) (by rw [hival]; exact hi0')
  have ht₀1 : t₀ ≠ 1 := by
    intro h
    have h1 := ht₀U 1
    rw [h, one_mul, inv_one, mul_one] at h1
    have h2 := pslU_injective h1
    have h3 : (1 : K) = -1 := Multiplicative.ofAdd.injective h2
    have h4 : (2 : K) = 0 := by linear_combination h3
    exact two_ne_zero_of_charP hp5 h4
  have hKodd := isOddPrimePower_sq (K := K) hp5 hK
  obtain ⟨c, hc⟩ := psl2_involutions_conjugate_of_odd_prime_power K hKodd t t₀
    ⟨ht1, by rw [pow_two]; exact ht2⟩ ⟨ht₀1, by rw [pow_two]; exact ht₀2⟩
  have hrank : Module.finrank (ZMod 2) (LinearMap.range (disp ρ t)) =
      Module.finrank (ZMod 2) (LinearMap.range (disp ρ t₀)) := by
    rw [← hc]
    exact (finrank_range_disp_conj ρ t c).symm
  rw [hrank]
  let U : Multiplicative K →* (E ≃ₗ[ZMod 2] E) := ρ.comp pslU
  have hU1 : ∀ a : K, a ≠ 0 → U (Multiplicative.ofAdd a) ≠ 1 := by
    intro a ha h
    have h1 : pslU (Multiplicative.ofAdd a) = 1 := hρ (by rw [map_one]; exact h)
    have h2 : Multiplicative.ofAdd a = 1 := pslU_injective (by rw [h1, map_one])
    exact ha (ofAdd_eq_one.1 h2)
  have hT : ∀ c : K, c ≠ 0 → ∃ T : E ≃ₗ[ZMod 2] E, ∀ a : K,
      T * U (Multiplicative.ofAdd a) * T⁻¹ = U (Multiplicative.ofAdd (c ^ 2 * a)) := by
    intro c hc
    refine ⟨ρ (pslMk (slD (Units.mk0 c hc))), fun a => ?_⟩
    have h2 := pslD_conj_pslU (K := K) (Units.mk0 c hc) a
    have h3 := congrArg ρ h2
    simpa [U, map_mul, map_inv] using h3
  have hs : ρ t₀ * ρ t₀ = 1 := by rw [← map_mul, ht₀2, map_one]
  have hsU : ∀ a : K, ρ t₀ * U (Multiplicative.ofAdd a) * (ρ t₀)⁻¹ =
      U (Multiplicative.ofAdd (-a)) := by
    intro a
    have h3 := congrArg ρ (ht₀U a)
    simpa [U, map_mul, map_inv] using h3
  exact six_le_rank_of_inv hK U hp5 hU1 hT hs hsU

end PSL

section Coset

open CFSG CFSG.GorensteinWalter CFSG.QuasithinUnique.Setup.X3

variable {p : ℕ} [hpf : Fact p.Prime] {K : Type} [Field K] [Fintype K] [CharP K p]

theorem mul_inv_frob_mem_pglS (hp2 : p ≠ 2) (hK : Fintype.card K = p ^ 2) {σ : K ≃+* K}
    (hσ : σ ≠ 1) (C : PGL2 K) : C * pgl2FieldAut K σ C⁻¹ ∈ pglS K := by
  obtain ⟨X, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective C
  have hσp : ∀ a, σ a = a ^ p := ringAut_eq_frob hK hσ
  set Y := Matrix.GeneralLinearGroup.map σ.toRingHom X⁻¹ with hY
  have hmapY : pgl2FieldAut K σ (Matrix.ProjGenLinGroup.mk X)⁻¹ =
      Matrix.ProjGenLinGroup.mk Y := by
    rw [← map_inv, pgl2FieldAut_apply]
    exact pgl2RingEquiv_mk σ X⁻¹
  rw [hmapY, ← map_mul]
  set d : Kˣ := Matrix.GeneralLinearGroup.det X with hd
  set μ : Kˣ := d ^ ((p - 1) / 2) with hμ
  set M : GL (Fin 2) K := X * Y * Matrix.GeneralLinearGroup.scalar (Fin 2) μ with hM
  have hodd : Odd p := hpf.out.odd_of_ne_two hp2
  have hp1 : 2 * ((p - 1) / 2) = p - 1 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have hdXinv : ((X⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = ((d⁻¹ : Kˣ) : K) := by
    rw [hd, ← map_inv]
    rfl
  have hdetY : ((Matrix.GeneralLinearGroup.det Y : Kˣ) : K) = σ (((d⁻¹ : Kˣ) : K)) := by
    show ((Y : Matrix (Fin 2) (Fin 2) K)).det = _
    have hYv : ((Y : Matrix (Fin 2) (Fin 2) K)) =
        (σ.toRingHom.mapMatrix) ((X⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := rfl
    rw [hYv, ← RingHom.map_det, hdXinv]
    rfl
  have hdetM1 : Matrix.GeneralLinearGroup.det M = 1 := by
    apply Units.ext
    rw [hM, map_mul, map_mul, Units.val_mul, Units.val_mul, hdetY,
      Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, hσp, Units.val_one, hμ,
      ← pow_mul, mul_comm ((p - 1) / 2) 2, hp1, Units.val_pow_eq_pow_val,
      Units.val_inv_eq_inv_val]
    have hd0 : (d : K) ≠ 0 := d.ne_zero
    have h1p : 1 ≤ p := hpf.out.one_lt.le
    calc (d : K) * ((d : K)⁻¹) ^ p * (d : K) ^ (p - 1)
        = ((d : K) * (d : K) ^ (p - 1)) * ((d : K)⁻¹) ^ p := by ring
      _ = (d : K) ^ p * ((d : K)⁻¹) ^ p := by
          rw [← pow_succ', Nat.sub_add_cancel h1p]
      _ = 1 := by rw [← mul_pow, mul_inv_cancel₀ hd0, one_pow]
  have hdetM : ((M : Matrix (Fin 2) (Fin 2) K)).det = 1 := by
    have := congrArg Units.val hdetM1
    simpa using this
  refine ⟨QuotientGroup.mk ⟨(M : Matrix (Fin 2) (Fin 2) K), hdetM⟩, ?_⟩
  have hM' : Matrix.SpecialLinearGroup.toGL
      (⟨(M : Matrix (Fin 2) (Fin 2) K), hdetM⟩ : Matrix.SpecialLinearGroup (Fin 2) K) = M :=
    Units.ext rfl
  show Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL
    (⟨(M : Matrix (Fin 2) (Fin 2) K), hdetM⟩ : Matrix.SpecialLinearGroup (Fin 2) K)) = _
  rw [hM', Matrix.ProjGenLinGroup.mk_eq_mk_iff]
  exact ⟨μ⁻¹, by rw [hM, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]⟩

theorem left_mem_pglS_of_field (hp2 : p ≠ 2) (hK : Fintype.card K = p ^ 2)
    (hoddpp : IsOddPrimePower (Nat.card K)) {x : PGammaL2 K} (hx : orderOf x = 2)
    (hf : x.right ≠ 1) : x.left ∈ pglS K := by
  obtain ⟨C, hC⟩ := pGammaL2_involution_conj_inr hoddpp x hx hf
  have hx' : x = SemidirectProduct.inl C * SemidirectProduct.inr x.right *
      (SemidirectProduct.inl C)⁻¹ := by
    rw [← hC]
    group
  have hleft : x.left = C * pgl2FieldAut K x.right C⁻¹ := by
    conv_lhs => rw [hx']
    simp [SemidirectProduct.mul_left, SemidirectProduct.inv_left]
  rw [hleft]
  exact mul_inv_frob_mem_pglS hp2 hK hf C

end Coset

section Diag

open CFSG CFSG.GorensteinWalter

variable {K : Type*} [Field K]

theorem pgl2_conj_diag (h2 : (2 : K) ≠ 0) {D : GL (Fin 2) K}
    (hD01 : (D : Matrix (Fin 2) (Fin 2) K) 0 1 = 0) (hD10 : (D : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (hD11 : (D : Matrix (Fin 2) (Fin 2) K) 1 1 = -(D : Matrix (Fin 2) (Fin 2) K) 0 0)
    {V : GL (Fin 2) K}
    (hv2 : Matrix.ProjGenLinGroup.mk V * Matrix.ProjGenLinGroup.mk V = 1)
    (hv1 : Matrix.ProjGenLinGroup.mk V ≠ 1)
    (hvd : Matrix.ProjGenLinGroup.mk V ≠ Matrix.ProjGenLinGroup.mk D)
    (hvc : Matrix.ProjGenLinGroup.mk V * Matrix.ProjGenLinGroup.mk D =
      Matrix.ProjGenLinGroup.mk D * Matrix.ProjGenLinGroup.mk V)
    {R : GL (Fin 2) K} (hR01 : (R : Matrix (Fin 2) (Fin 2) K) 0 1 = 0)
    (hR10 : (R : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) :
    Matrix.ProjGenLinGroup.mk V * Matrix.ProjGenLinGroup.mk R * Matrix.ProjGenLinGroup.mk V =
      (Matrix.ProjGenLinGroup.mk R)⁻¹ := by
  set δ := (D : Matrix (Fin 2) (Fin 2) K) 0 0 with hδ
  have hδ0 : δ ≠ 0 := by
    intro h0
    have hd := (Matrix.GeneralLinearGroup.det D).ne_zero
    apply hd
    change Matrix.det (D : Matrix (Fin 2) (Fin 2) K) = 0
    rw [Matrix.det_fin_two, hD01, ← hδ, h0]
    ring
  rw [← map_mul, ← map_mul, Matrix.ProjGenLinGroup.mk_eq_mk_iff] at hvc
  obtain ⟨u, hu⟩ := hvc
  have hm := congrArg (fun X : GL (Fin 2) K => (X : Matrix (Fin 2) (Fin 2) K)) hu
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar] at hm
  rw [coe_eq_of_entries V, coe_eq_of_entries D, hD01, hD10, hD11, ← hδ, scalar_fin_two] at hm
  simp only [Matrix.mul_fin_two] at hm
  have e00 := congrFun (congrFun hm 0) 0
  have e01 := congrFun (congrFun hm 0) 1
  have e10 := congrFun (congrFun hm 1) 0
  have e11 := congrFun (congrFun hm 1) 1
  simp at e00 e01 e10 e11
  set a := (V : Matrix (Fin 2) (Fin 2) K) 0 0 with ha
  set b := (V : Matrix (Fin 2) (Fin 2) K) 0 1 with hb
  set c := (V : Matrix (Fin 2) (Fin 2) K) 1 0 with hc
  set d := (V : Matrix (Fin 2) (Fin 2) K) 1 1 with hd
  have ha' : δ * (a * ((u : K) - 1)) = 0 := by linear_combination e00
  have hb' : δ * (b * ((u : K) + 1)) = 0 := by linear_combination -e01
  have hc' : δ * (c * ((u : K) + 1)) = 0 := by linear_combination e10
  have hd' : δ * (d * ((u : K) - 1)) = 0 := by linear_combination e11
  have ha0 := (mul_eq_zero.1 ha').resolve_left hδ0
  have hb0 := (mul_eq_zero.1 hb').resolve_left hδ0
  have hc0 := (mul_eq_zero.1 hc').resolve_left hδ0
  have hd0 := (mul_eq_zero.1 hd').resolve_left hδ0
  by_cases hu1 : (u : K) = 1
  ·
    exfalso
    have hu2 : (u : K) + 1 ≠ 0 := by rw [hu1, one_add_one_eq_two]; exact h2
    have hb00 : b = 0 := (mul_eq_zero.1 hb0).resolve_right hu2
    have hc00 : c = 0 := (mul_eq_zero.1 hc0).resolve_right hu2
    rw [← map_mul, Matrix.ProjGenLinGroup.mk_eq_one,
      Matrix.GeneralLinearGroup.center_eq_range_scalar] at hv2
    obtain ⟨w, hw⟩ := hv2
    have hm2 := congrArg (fun X : GL (Fin 2) K => (X : Matrix (Fin 2) (Fin 2) K)) hw
    simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar] at hm2
    rw [coe_eq_of_entries V, scalar_fin_two, Matrix.mul_fin_two, ← ha, ← hb, ← hc, ← hd,
      hb00, hc00] at hm2
    have f00 := congrFun (congrFun hm2 0) 0
    have f11 := congrFun (congrFun hm2 1) 1
    simp at f00 f11
    have had : (a - d) * (a + d) = 0 := by linear_combination f11 - f00
    rcases mul_eq_zero.1 had with h | h
    · apply hv1
      exact mk_eq_one_of_entries (by rw [← hb, hb00]) (by rw [← hc, hc00])
        (by rw [← hd, ← ha]; linear_combination -h)
    · apply hvd
      rw [Matrix.ProjGenLinGroup.mk_eq_mk_iff]
      have ha0' : a ≠ 0 := by
        intro h0
        rcases first_row_ne_zero V with h1 | h1
        · exact h1 h0
        · exact h1 hb00
      refine ⟨Units.mk0 (δ / a) (div_ne_zero hδ0 ha0'), ?_⟩
      apply Units.ext
      rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0, scalar_fin_two,
        coe_eq_of_entries V, coe_eq_of_entries D, hD01, hD10, hD11, ← hδ, ← ha, ← hb, ← hc,
        ← hd, hb00, hc00, show d = -a by linear_combination h]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp
  ·
    have hu' : (u : K) - 1 ≠ 0 := sub_ne_zero.2 hu1
    have ha00 : a = 0 := (mul_eq_zero.1 ha0).resolve_right hu'
    have hd00 : d = 0 := (mul_eq_zero.1 hd0).resolve_right hu'
    have hVRVR : Matrix.ProjGenLinGroup.mk (V * R * V * R) = 1 := by
      rw [Matrix.ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar]
      set r := (R : Matrix (Fin 2) (Fin 2) K) 0 0 with hr
      set t := (R : Matrix (Fin 2) (Fin 2) K) 1 1 with ht
      have hbc : b * c ≠ 0 := by
        intro h0
        have hdV := (Matrix.GeneralLinearGroup.det V).ne_zero
        apply hdV
        change Matrix.det (V : Matrix (Fin 2) (Fin 2) K) = 0
        rw [Matrix.det_fin_two, ← ha, ← hb, ← hc, ← hd, ha00, hd00]
        linear_combination -h0
      have hrt : r * t ≠ 0 := by
        intro h0
        have hdR := (Matrix.GeneralLinearGroup.det R).ne_zero
        apply hdR
        change Matrix.det (R : Matrix (Fin 2) (Fin 2) K) = 0
        rw [Matrix.det_fin_two, hR01, hR10, ← hr, ← ht]
        linear_combination h0
      refine ⟨Units.mk0 ((b * c) * (r * t)) (mul_ne_zero hbc hrt), ?_⟩
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
      simp only [Units.val_mul]
      rw [coe_eq_of_entries V, coe_eq_of_entries R, ← ha, ← hb, ← hc, ← hd, ha00, hd00, hR01,
        hR10, ← hr, ← ht, scalar_fin_two]
      simp only [Matrix.mul_fin_two]
      ext i j
      fin_cases i <;> fin_cases j <;> simp <;> ring
    have h1 : Matrix.ProjGenLinGroup.mk V * Matrix.ProjGenLinGroup.mk R *
        Matrix.ProjGenLinGroup.mk V * Matrix.ProjGenLinGroup.mk R = 1 := by
      rw [← map_mul, ← map_mul, ← map_mul]
      exact hVRVR
    exact eq_inv_of_mul_eq_one_left h1

end Diag

section Offender

open CFSG CFSG.GorensteinWalter CFSG.QuasithinUnique.Setup.X3 CFSG.SectionRank.OddCover
  CFSG.LocalAnalysis.ComponentInitial CFSG.Quasithin CFSG.Assembly.LowTwoRank

variable {p : ℕ} [hpf : Fact p.Prime] {K : Type} [Field K] [Fintype K] [CharP K p]

omit hpf [Fintype K] [CharP K p] in
theorem slD_mul_comm (a b : Kˣ) : slD a * slD b = slD b * slD a := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_slD, coe_slD]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem fixedSub_eq_ker_of_le {G E : Type*} [Group G] [AddCommGroup E] [Module (ZMod 2) E]
    [Module.Finite (ZMod 2) E] (ρ : G →* (E ≃ₗ[ZMod 2] E)) {B : Subgroup G} {a : G} (ha : a ∈ B)
    (h : finrank (ZMod 2) E - finrank (ZMod 2) (fixedSub ρ B) ≤
      finrank (ZMod 2) (LinearMap.range (disp ρ a))) :
    fixedSub ρ B = LinearMap.ker (disp ρ a) := by
  have hle := fixedSub_le_ker_disp ρ ha
  have h1 := LinearMap.finrank_range_add_finrank_ker (disp ρ a)
  have h2 := Submodule.finrank_le (fixedSub ρ B)
  exact Submodule.eq_of_le_of_finrank_le hle (by omega)

theorem no_offender2_gamma25
    (hp5 : p = 5) (hK : Fintype.card K = p ^ 2) {E : Type*}
    [AddCommGroup E] [Module (ZMod 2) E] [Module.Finite (ZMod 2) E] {Hg : Type*} [Group Hg]
    (ρ : Hg →* (E ≃ₗ[ZMod 2] E)) (hρ : Function.Injective ρ) (j : Hg →* PGammaL2 K)
    (hj : Function.Injective j) (ι : PSL2 K →* Hg)
    (hjι : ∀ y, j (ι y) = SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL y))
    {B : Subgroup Hg} (hB1 : B ≠ ⊥) (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hB2 : ∀ a ∈ B, a * a = 1)
    (hoff : finrank (ZMod 2) E - finrank (ZMod 2) (fixedSub ρ B) ≤
      2 * Nat.log 2 (Nat.card B)) : False := by
  have hp5' : 5 ≤ p := by omega
  have hp2 : p ≠ 2 := by omega
  have hoddpp := isOddPrimePower_sq hp5' hK
  have hcard3 := three_lt_card_sq hp5' hK
  have hch : ringChar K ≠ 2 := ringChar_ne_two_sq (K := K) (p := p) hp5'
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of_charP hp5'
  have hcardAut : Nat.card (K ≃+* K) = 2 :=
    (card_ringAut_and_isCyclic hpf.out K (by rw [Nat.card_eq_fintype_card, hK])).1
  have hι : Function.Injective ι := by
    intro y z hyz
    have h1 := hjι y
    rw [hyz, hjι z] at h1
    exact Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
      (SemidirectProduct.inl_injective h1.symm)
  obtain ⟨-, hidx, -, -, hpair⟩ := projective_involution_pairing K hch
  have hB8 : Nat.card B ≤ 8 := card_le_eight hch hcardAut hj hBc hB2
  have hinner : ∀ a : Hg, ∀ ha : a ∈ linPart j, linMap j ⟨a, ha⟩ ∈ pglS K → a ≠ 1 →
      a * a = 1 → 6 ≤ finrank (ZMod 2) (LinearMap.range (disp ρ a)) := by
    intro a haL haS ha1 ha2
    obtain ⟨y, hy⟩ := haS
    have hia : ι y = a := by
      apply hj
      rw [hjι, hy]
      exact (j_eq_inl j ⟨a, haL⟩).symm
    have hy1 : y ≠ 1 := by
      rintro rfl
      apply ha1
      rw [← hia, map_one]
    have hy2 : y * y = 1 := hι (by rw [map_mul, map_one, hia]; exact ha2)
    have h := psl2_square_inner_rank6 hp5' hK (ρ.comp ι) (hρ.comp hι) hy1 hy2
    have e : disp (ρ.comp ι) y = disp ρ a := by
      show disp ρ (ι y) = disp ρ a
      rw [hia]
    rwa [e] at h
  let φ : ↥B →* (K ≃+* K) := SemidirectProduct.rightHom.comp (j.comp B.subtype)
  have h1 : Nat.card φ.ker * Nat.card φ.range = Nat.card B := Subgroup.card_ker_mul_card_range φ
  have h2 : Nat.card φ.range ≤ 2 := by
    have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; norm_num)
    rw [← hcardAut]
    exact Subgroup.card_le_card_group _
  have hkerL : ∀ x ∈ φ.ker, (x : Hg) ∈ linPart j := fun x hx => hx
  by_cases hcase : ∃ a ∈ B, ∃ ha : a ∈ linPart j, linMap j ⟨a, ha⟩ ∈ pglS K ∧ a ≠ 1
  · obtain ⟨a, haB, haL, haS, ha1⟩ := hcase
    have h6 := hinner a haL haS ha1 (hB2 a haB)
    by_cases hB4 : Nat.card B ≤ 4
    · have hlog : Nat.log 2 (Nat.card B) ≤ 2 := (Nat.log_mono_right hB4).trans (by norm_num)
      have h7 := finrank_range_disp_le_of_offender ρ haB (L := 4) (hoff.trans (by omega))
      omega
    ·
      push Not at hB4
      have hlog : Nat.log 2 (Nat.card B) ≤ 3 := (Nat.log_mono_right hB8).trans (by norm_num)
      have hoff6 : finrank (ZMod 2) E - finrank (ZMod 2) (fixedSub ρ B) ≤ 6 :=
        hoff.trans (by omega)
      have hF : fixedSub ρ B = LinearMap.ker (disp ρ a) :=
        fixedSub_eq_ker_of_le ρ haB (hoff6.trans h6)
      have hker4 : 2 < Nat.card φ.ker := by
        by_contra hcon
        push Not at hcon
        have : Nat.card B ≤ 2 * 2 := by rw [← h1]; exact Nat.mul_le_mul hcon h2
        omega
      obtain ⟨u, hu, hu1, hua⟩ : ∃ u ∈ φ.ker, (u : Hg) ≠ 1 ∧ (u : Hg) ≠ a := by
        by_contra hcon
        push Not at hcon
        have := card_le_two_of_forall_eq (H := φ.ker) (⟨a, haB⟩ : ↥B) (fun y hy => by
          by_cases hy1 : (y : Hg) = 1
          · exact Or.inl (Subtype.ext hy1)
          · exact Or.inr (Subtype.ext (hcon y hy hy1)))
        omega
      have huB : (u : Hg) ∈ B := u.2
      have huL : (u : Hg) ∈ linPart j := hkerL u hu
      obtain ⟨ya, hya⟩ := haS
      have hia : ι ya = a := by
        apply hj
        rw [hjι, hya]
        exact (j_eq_inl j ⟨a, haL⟩).symm
      have hya1 : ya ≠ 1 := by
        rintro rfl
        apply ha1
        rw [← hia, map_one]
      have hya2 : ya * ya = 1 := hι (by rw [map_mul, map_one, hia]; exact hB2 a haB)
      obtain ⟨i0, hi0⟩ : IsSquare (-1 : K) := by
        rw [FiniteField.isSquare_neg_one_iff, hK, hp5]
        norm_num
      have hi0' : i0 * i0 = -1 := hi0.symm
      have hi0ne : i0 ≠ 0 := by
        rintro rfl
        rw [zero_mul] at hi0'
        exact one_ne_zero (neg_eq_zero.1 hi0'.symm)
      set i : Kˣ := Units.mk0 i0 hi0ne with hidef
      have hival : ((i : Kˣ) : K) = i0 := Units.val_mk0 _
      set t₀ : PSL2 K := pslMk (slD i) with ht₀def
      have ht₀2 : t₀ * t₀ = 1 := pslMk_slD_sq (i := i) (by rw [hival]; exact hi0')
      have ht₀1 : t₀ ≠ 1 := by
        intro h
        have h3 := pslD_conj_pslU (K := K) i 1
        rw [← ht₀def, h, one_mul, inv_one, mul_one, hival, sq, hi0', mul_one] at h3
        have h4 := pslU_injective h3
        have h5 : (1 : K) = -1 := Multiplicative.ofAdd.injective h4
        have h6 : (2 : K) = 0 := by linear_combination h5
        exact h2K h6
      obtain ⟨c, hc⟩ := psl2_involutions_conjugate_of_odd_prime_power K hoddpp ya t₀
        ⟨hya1, by rw [pow_two]; exact hya2⟩ ⟨ht₀1, by rw [pow_two]; exact ht₀2⟩
      set Cm := Matrix.ProjectiveSpecialLinearGroup.toPGL c with hCm
      set Um := linMap j ⟨(u : Hg), huL⟩ with hUm
      set Am := linMap j ⟨a, haL⟩ with hAm
      have hjU : j (u : Hg) = SemidirectProduct.inl Um := j_eq_inl j ⟨(u : Hg), huL⟩
      have hjA : j a = SemidirectProduct.inl Am := j_eq_inl j ⟨a, haL⟩
      have hAmya : Am = Matrix.ProjectiveSpecialLinearGroup.toPGL ya := hya.symm
      have hU2 : Um * Um = 1 := by
        rw [hUm, ← map_mul]
        have : (⟨(u : Hg), huL⟩ : linPart j) * ⟨(u : Hg), huL⟩ = 1 :=
          Subtype.ext (hB2 _ huB)
        rw [this, map_one]
      have hU1' : Um ≠ 1 := by
        intro h
        apply hu1
        have := linMap_injective hj (h.trans (map_one _).symm)
        exact congrArg Subtype.val this
      have hUA : Um ≠ Am := by
        intro h
        apply hua
        exact congrArg Subtype.val (linMap_injective hj h)
      have hUAc : Um * Am = Am * Um := by
        rw [hUm, hAm, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (hBc _ huB _ haB)
      set U' := Cm * Um * Cm⁻¹ with hU'
      have hT0 : Matrix.ProjectiveSpecialLinearGroup.toPGL t₀ = Cm * Am * Cm⁻¹ := by
        rw [← hc, map_mul, map_mul, map_inv, hAmya]
      have hU'2 : U' * U' = 1 := by
        rw [hU']
        calc Cm * Um * Cm⁻¹ * (Cm * Um * Cm⁻¹) = Cm * (Um * Um) * Cm⁻¹ := by group
          _ = 1 := by rw [hU2]; group
      have hU'1 : U' ≠ 1 := by
        intro h
        apply hU1'
        have : Um = Cm⁻¹ * U' * Cm := by rw [hU']; group
        rw [this, h]
        group
      have hU't : U' ≠ Matrix.ProjectiveSpecialLinearGroup.toPGL t₀ := by
        intro h
        apply hUA
        rw [hT0, hU'] at h
        have := congrArg (fun X => Cm⁻¹ * X * Cm) h
        simpa [mul_assoc] using this
      have hU'c : U' * Matrix.ProjectiveSpecialLinearGroup.toPGL t₀ =
          Matrix.ProjectiveSpecialLinearGroup.toPGL t₀ * U' := by
        rw [hT0, hU']
        calc Cm * Um * Cm⁻¹ * (Cm * Am * Cm⁻¹) = Cm * (Um * Am) * Cm⁻¹ := by group
          _ = Cm * (Am * Um) * Cm⁻¹ := by rw [hUAc]
          _ = Cm * Am * Cm⁻¹ * (Cm * Um * Cm⁻¹) := by group
      obtain ⟨V, hV⟩ := Matrix.ProjGenLinGroup.mk_surjective U'
      set D : GL (Fin 2) K := Matrix.SpecialLinearGroup.toGL (slD i) with hD
      have htD : Matrix.ProjectiveSpecialLinearGroup.toPGL t₀ = Matrix.ProjGenLinGroup.mk D := rfl
      have hDent : (D : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧ (D : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
          (D : Matrix (Fin 2) (Fin 2) K) 1 1 = -(D : Matrix (Fin 2) (Fin 2) K) 0 0 := by
        refine ⟨rfl, rfl, ?_⟩
        show ((i⁻¹ : Kˣ) : K) = -(i : K)
        rw [Units.val_inv_eq_inv_val, hival]
        rw [inv_eq_of_mul_eq_one_right (show i0 * -i0 = 1 by linear_combination -hi0')]
      obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
      set h₀ : PSL2 K := pslMk (slD (g ^ 8)) with hh₀
      set T₀ := Matrix.ProjectiveSpecialLinearGroup.toPGL h₀ with hT₀
      have hT₀D : T₀ = Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL (slD (g ^ 8))) :=
        rfl
      have hinvT : U' * T₀ * U' = T₀⁻¹ := by
        rw [← hV, hT₀D]
        refine pgl2_conj_diag h2K hDent.1 hDent.2.1 hDent.2.2 ?_ ?_ ?_ ?_ rfl rfl
        · rw [hV]; exact hU'2
        · rw [hV]; exact hU'1
        · rw [hV, ← htD]; exact hU't
        · rw [hV, ← htD]; exact hU'c
      have hinvT' : U' * T₀⁻¹ * U' = T₀ := by
        have hUinv : U'⁻¹ = U' := inv_eq_of_mul_eq_one_right hU'2
        calc U' * T₀⁻¹ * U' = (U'⁻¹ * T₀ * U'⁻¹)⁻¹ := by group
          _ = (U' * T₀ * U')⁻¹ := by rw [hUinv]
          _ = T₀ := by rw [hinvT, inv_inv]
      set hh : Hg := ι (c⁻¹ * h₀ * c) with hhh
      have hjh : j hh = SemidirectProduct.inl (Cm⁻¹ * T₀ * Cm) := by
        rw [hhh, hjι]
        congr 1
        rw [map_mul, map_mul, map_inv]
      have hha : hh * a = a * hh := by
        rw [hhh, ← hia, ← map_mul, ← map_mul]
        congr 1
        have hct : c * ya * c⁻¹ = t₀ := hc
        have hht : h₀ * t₀ = t₀ * h₀ := by
          rw [hh₀, ht₀def, ← map_mul, ← map_mul, slD_mul_comm]
        have hya' : ya = c⁻¹ * t₀ * c := by rw [← hct]; group
        rw [hya']
        calc c⁻¹ * h₀ * c * (c⁻¹ * t₀ * c) = c⁻¹ * (h₀ * t₀) * c := by group
          _ = c⁻¹ * (t₀ * h₀) * c := by rw [hht]
          _ = c⁻¹ * t₀ * c * (c⁻¹ * h₀ * c) := by group
      set y : Hg := hh * (u : Hg) * hh⁻¹ * (u : Hg) with hy
      have hjy : j y = j (ι (c⁻¹ * h₀ ^ 2 * c)) := by
        have e1 : j y = j hh * j (u : Hg) * (j hh)⁻¹ * j (u : Hg) := by
          rw [hy, map_mul, map_mul, map_mul, map_inv]
        rw [e1, hjh, hjU, hjι, ← map_inv SemidirectProduct.inl,
          ← map_mul SemidirectProduct.inl, ← map_mul SemidirectProduct.inl,
          ← map_mul SemidirectProduct.inl]
        congr 1
        rw [map_mul, map_mul, map_inv, map_pow, ← hT₀, ← hCm]
        have hUm' : Um = Cm⁻¹ * U' * Cm := by rw [hU']; group
        rw [hUm']
        calc Cm⁻¹ * T₀ * Cm * (Cm⁻¹ * U' * Cm) * (Cm⁻¹ * T₀ * Cm)⁻¹ * (Cm⁻¹ * U' * Cm)
            = Cm⁻¹ * (T₀ * (U' * T₀⁻¹ * U')) * Cm := by group
          _ = Cm⁻¹ * T₀ ^ 2 * Cm := by rw [hinvT', sq]
      have hyι : y = ι (c⁻¹ * h₀ ^ 2 * c) := hj hjy
      have hhF : ∀ v ∈ fixedSub ρ B, ρ hh⁻¹ v ∈ fixedSub ρ B := by
        intro v hv
        rw [hF] at hv ⊢
        rw [LinearMap.mem_ker, disp_apply, sub_eq_zero] at hv ⊢
        have hha' : a * hh⁻¹ = hh⁻¹ * a := by
          calc a * hh⁻¹ = hh⁻¹ * (hh * a) * hh⁻¹ := by group
            _ = hh⁻¹ * (a * hh) * hh⁻¹ := by rw [hha]
            _ = hh⁻¹ * a := by group
        rw [← LinearEquiv.mul_apply, ← map_mul, hha', map_mul, LinearEquiv.mul_apply, hv]
      have hyF : fixedSub ρ B ≤ LinearMap.ker (disp ρ y) := by
        intro v hv
        rw [LinearMap.mem_ker, disp_apply, sub_eq_zero]
        have hu' : ∀ w ∈ fixedSub ρ B, ρ (u : Hg) w = w := fun w hw => mem_fixedSub.1 hw _ huB
        have h3 : ρ hh⁻¹ (ρ (u : Hg) v) = ρ hh⁻¹ v := by rw [hu' v hv]
        rw [hy, map_mul, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
          LinearEquiv.mul_apply, hu' v hv, hu' _ (hhF v hv), ← LinearEquiv.mul_apply, ← map_mul,
          mul_inv_cancel, map_one]
        rfl
      have hrk_le : finrank (ZMod 2) (LinearMap.range (disp ρ y)) ≤ 6 := by
        have h4 := LinearMap.finrank_range_add_finrank_ker (disp ρ y)
        have h5 := Submodule.finrank_mono hyF
        omega
      have hrk_ge : 8 ≤ finrank (ZMod 2) (LinearMap.range (disp ρ y)) := by
        rw [hyι]
        have h3 := finrank_range_disp_conj (ρ.comp ι) (h₀ ^ 2) c⁻¹
        rw [inv_inv] at h3
        have e : disp (ρ.comp ι) (c⁻¹ * h₀ ^ 2 * c) = disp ρ (ι (c⁻¹ * h₀ ^ 2 * c)) := rfl
        rw [← e, h3]
        let U : Multiplicative K →* (E ≃ₗ[ZMod 2] E) := (ρ.comp ι).comp pslU
        have hU1 : ∀ a : K, a ≠ 0 → U (Multiplicative.ofAdd a) ≠ 1 := by
          intro a ha h
          have h4 : pslU (Multiplicative.ofAdd a) = 1 :=
            (hρ.comp hι) (show ρ (ι (pslU (Multiplicative.ofAdd a))) = ρ (ι 1) by
              rw [map_one, map_one]; exact h)
          have h5 : Multiplicative.ofAdd a = 1 := pslU_injective (by rw [h4, map_one])
          exact ha (ofAdd_eq_one.1 h5)
        have hT : ∀ c : K, c ≠ 0 → ∃ T : E ≃ₗ[ZMod 2] E, ∀ a : K,
            T * U (Multiplicative.ofAdd a) * T⁻¹ = U (Multiplicative.ofAdd (c ^ 2 * a)) := by
          intro c hc
          refine ⟨ρ (ι (pslMk (slD (Units.mk0 c hc)))), fun a => ?_⟩
          have h4 := pslD_conj_pslU (K := K) (Units.mk0 c hc) a
          have h5 := congrArg (fun z => ρ (ι z)) h4
          simpa [U, map_mul, map_inv] using h5
        have hY0 : ∀ a : K, (ρ.comp ι) h₀ * U (Multiplicative.ofAdd a) * ((ρ.comp ι) h₀)⁻¹ =
            U (Multiplicative.ofAdd ((g : K) ^ 16 * a)) := by
          intro a
          have h4 := pslD_conj_pslU (K := K) (g ^ 8) a
          have h5 := congrArg (fun z => ρ (ι z)) h4
          have e1 : (((g ^ 8 : Kˣ) : K)) ^ 2 = (g : K) ^ 16 := by
            rw [Units.val_pow_eq_pow_val, ← pow_mul]
          simp only [map_mul, map_inv] at h5
          rw [e1] at h5
          simpa [U, hh₀] using h5
        have hY : ∀ a : K, (ρ.comp ι) (h₀ ^ 2) * U (Multiplicative.ofAdd a) *
            ((ρ.comp ι) (h₀ ^ 2))⁻¹ = U (Multiplicative.ofAdd (((g : K) ^ 16) ^ 2 * a)) := by
          intro a
          rw [map_pow, sq, mul_inv_rev]
          calc (ρ.comp ι) h₀ * (ρ.comp ι) h₀ * U (Multiplicative.ofAdd a) *
                (((ρ.comp ι) h₀)⁻¹ * ((ρ.comp ι) h₀)⁻¹)
              = (ρ.comp ι) h₀ * ((ρ.comp ι) h₀ * U (Multiplicative.ofAdd a) *
                ((ρ.comp ι) h₀)⁻¹) * ((ρ.comp ι) h₀)⁻¹ := by group
            _ = U (Multiplicative.ofAdd (((g : K) ^ 16) ^ 2 * a)) := by
                rw [hY0, hY0]
                congr 2
                ring
        exact eight_le_rank_of_three_cycle hK U hp5 hg hU1 hT hY
      omega
  · push Not at hcase
    have hkerS : ∀ x : ↥B, ∀ hx : x ∈ φ.ker, (x : Hg) ≠ 1 →
        linMap j ⟨(x : Hg), hkerL x hx⟩ ∉ pglS K :=
      fun x hx hx1 hS => hx1 (hcase x x.2 (hkerL x hx) hS)
    by_cases hk : ∃ x ∈ φ.ker, (x : Hg) ≠ 1
    ·
      obtain ⟨x, hx, hx1⟩ := hk
      set d : Hg := (x : Hg) with hd
      have hdB : d ∈ B := x.2
      have hdL : d ∈ linPart j := hkerL x hx
      have hd2 : d * d = 1 := hB2 d hdB
      set Dm := linMap j ⟨d, hdL⟩ with hDm
      have hDS : Dm ∉ pglS K := hkerS x hx hx1
      have hjd : j d = SemidirectProduct.inl Dm := j_eq_inl j ⟨d, hdL⟩
      have hall : ∀ t ∈ B, (j t).right = 1 := by
        intro t htB
        by_contra htf
        have ht2 : t * t = 1 := hB2 t htB
        have ht1 : t ≠ 1 := by
          rintro rfl
          exact htf (by simp)
        have hord : orderOf (j t) = 2 := by
          rw [orderOf_injective j hj t]
          exact orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1
        have hS1 := left_mem_pglS_of_field hp2 hK hoddpp hord htf
        have hdt2 : (d * t) * (d * t) = 1 := by
          calc (d * t) * (d * t) = d * (t * d) * t := by group
            _ = d * (d * t) * t := by rw [hBc t htB d hdB]
            _ = (d * d) * (t * t) := by group
            _ = 1 := by rw [hd2, ht2, one_mul]
        have hdt1 : d * t ≠ 1 := by
          intro h
          apply htf
          have h3 : (j (d * t)).right = 1 := by rw [h, map_one]; rfl
          rw [map_mul, hjd] at h3
          simpa using h3
        have hordt : orderOf (j (d * t)) = 2 := by
          rw [orderOf_injective j hj _]
          exact orderOf_eq_prime (by rw [pow_two]; exact hdt2) hdt1
        have hfdt : (j (d * t)).right ≠ 1 := by
          rw [map_mul, hjd]
          simpa using htf
        have hS2 := left_mem_pglS_of_field hp2 hK hoddpp hordt hfdt
        rw [map_mul, hjd] at hS2
        have h3 : (SemidirectProduct.inl Dm * j t).left = Dm * (j t).left := by
          simp [SemidirectProduct.mul_left]
        rw [h3] at hS2
        apply hDS
        have h4 : Dm = Dm * (j t).left * ((j t).left)⁻¹ := by group
        rw [h4]
        exact (pglS K).mul_mem hS2 ((pglS K).inv_mem hS1)
      have hsub : ∀ y ∈ B, y = 1 ∨ y = d := by
        intro y hy
        by_cases hy1 : y = 1
        · exact Or.inl hy1
        · right
          have hyL : y ∈ linPart j := hall y hy
          have hyS : linMap j ⟨y, hyL⟩ ∉ pglS K := fun hS => hy1 (hcase y hy hyL hS)
          have hDS' : linMap j ⟨d, hdL⟩ ∉ pglS K := hDS
          have hmem : linMap j (⟨y, hyL⟩ * (⟨d, hdL⟩)⁻¹) ∈ pglS K := by
            rw [map_mul, map_inv, Subgroup.mul_mem_iff_of_index_two hidx]
            simp [hyS, hDS']
          have hyd : y * d⁻¹ ∈ linPart j := (linPart j).mul_mem hyL ((linPart j).inv_mem hdL)
          have h3 := hcase (y * d⁻¹) (B.mul_mem hy (B.inv_mem hdB)) hyd hmem
          exact mul_inv_eq_one.1 h3
      have hB2' : Nat.card B ≤ 2 := card_le_two_of_forall_eq d hsub
      have hlog : Nat.log 2 (Nat.card B) ≤ 1 := (Nat.log_mono_right hB2').trans (by norm_num)
      have hD2 : Dm * Dm = 1 := by
        rw [hDm, ← map_mul]
        have : (⟨d, hdL⟩ : linPart j) * ⟨d, hdL⟩ = 1 := Subtype.ext hd2
        rw [this, map_one]
      have hD1 : Dm ≠ 1 := fun h => hDS (h ▸ (pglS K).one_mem)
      obtain ⟨s, hsS, hst, hcomm⟩ := hpair Dm hD2 hD1
      obtain ⟨y₀, hy₀⟩ := hsS
      set s₀ : Hg := ι y₀ with hs₀
      have hjs₀ : j s₀ = SemidirectProduct.inl s := by rw [hs₀, hjι, hy₀]
      set d' : Hg := s₀⁻¹ * d * s₀ with hd'
      have hjd' : j d' = SemidirectProduct.inl (s⁻¹ * Dm * s) := by
        rw [hd', map_mul j (s₀⁻¹ * d) s₀, map_mul j s₀⁻¹ d, map_inv, hjs₀, hjd, ← map_inv,
          ← map_mul, ← map_mul]
      have hjdd : j (d * d') = SemidirectProduct.inl (Dm * (s⁻¹ * Dm * s)) := by
        rw [map_mul j d d', hjd, hjd', ← map_mul]
      have hddL : d * d' ∈ linPart j := by
        show (j (d * d')).right = 1
        rw [hjdd]
        rfl
      have hddlin : linMap j ⟨d * d', hddL⟩ = Dm * (s⁻¹ * Dm * s) := by
        show (j (d * d')).left = _
        rw [hjdd]
        rfl
      have hsDS : s⁻¹ * Dm * s ∉ pglS K := by
        intro h
        apply hDS
        have hs' : s ∈ pglS K := ⟨y₀, hy₀⟩
        have : Dm = s * (s⁻¹ * Dm * s) * s⁻¹ := by group
        rw [this]
        exact (pglS K).mul_mem ((pglS K).mul_mem hs' h) ((pglS K).inv_mem hs')
      have hddS : linMap j ⟨d * d', hddL⟩ ∈ pglS K := by
        rw [hddlin, Subgroup.mul_mem_iff_of_index_two hidx]
        simp [hDS, hsDS]
      have hdd1 : d * d' ≠ 1 := by
        intro h
        apply hst
        have h3 : j (d * d') = 1 := by rw [h, map_one]
        rw [hjdd] at h3
        have h4 : Dm * (s⁻¹ * Dm * s) = 1 :=
          SemidirectProduct.inl_injective (h3.trans (map_one _).symm)
        have h5 : s⁻¹ * Dm * s = Dm⁻¹ := eq_inv_of_mul_eq_one_right h4
        rw [h5]
        exact inv_eq_of_mul_eq_one_right hD2
      have hcomm' : d * d' = d' * d := by
        apply hj
        rw [map_mul j d d', map_mul j d' d, hjd, hjd', ← map_mul, ← map_mul, hcomm.eq]
      have hd'2 : d' * d' = 1 := by
        calc d' * d' = s₀⁻¹ * (d * d) * s₀ := by rw [hd']; group
          _ = 1 := by rw [hd2]; group
      have hdd2 : (d * d') * (d * d') = 1 := by
        calc (d * d') * (d * d') = d * (d' * d) * d' := by group
          _ = d * (d * d') * d' := by rw [← hcomm']
          _ = (d * d) * (d' * d') := by group
          _ = 1 := by rw [hd2, hd'2, mul_one]
      have h6 := hinner (d * d') hddL hddS hdd1 hdd2
      have hsum := finrank_range_disp_mul_le ρ d d'
      have hconj : finrank (ZMod 2) (LinearMap.range (disp ρ d')) =
          finrank (ZMod 2) (LinearMap.range (disp ρ d)) := by
        have h3 := finrank_range_disp_conj ρ d s₀⁻¹
        rw [inv_inv] at h3
        rw [hd', h3]
      have hdle := finrank_range_disp_le_of_offender ρ hdB (L := 2) (hoff.trans (by omega))
      omega
    ·
      push Not at hk
      have hker1 : Nat.card φ.ker ≤ 1 := by
        have : φ.ker = ⊥ := (Subgroup.eq_bot_iff_forall _).2 fun x hx => Subtype.ext (hk x hx)
        rw [this, Subgroup.card_bot]
      have hB2' : Nat.card B ≤ 2 := by
        calc Nat.card B = Nat.card φ.ker * Nat.card φ.range := h1.symm
          _ ≤ 1 * 2 := Nat.mul_le_mul hker1 h2
          _ = 2 := by norm_num
      have hlog : Nat.log 2 (Nat.card B) ≤ 1 := (Nat.log_mono_right hB2').trans (by norm_num)
      obtain ⟨t, htB, ht1⟩ : ∃ t ∈ B, t ≠ 1 := by
        obtain ⟨t, ht⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hB1
        exact ⟨t, t.2, fun h => ht (Subtype.ext h)⟩
      have htf : (j t).right ≠ 1 := fun h => ht1 (hk ⟨t, htB⟩ h)
      have ht2 : t * t = 1 := hB2 t htB
      have hord : orderOf (j t) = 2 := by
        rw [orderOf_injective j hj t]
        exact orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1
      obtain ⟨C, hC⟩ := pGammaL2_involution_conj_inr hoddpp (j t) hord htf
      let j' : Hg →* PGammaL2 K :=
        (MulAut.conj ((SemidirectProduct.inl C)⁻¹ : PGammaL2 K)).toMonoidHom.comp j
      let ι' : PSL2 K →* Hg := ι.comp (pgl2InnerAutPSL2 K hoddpp hcard3 C).toMonoidHom
      have hj' : Function.Injective j' := (MulAut.conj _).injective.comp hj
      have hjι' : ∀ y, j' (ι' y) =
          SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL y) := by
        intro y
        show (SemidirectProduct.inl C)⁻¹ * j (ι (pgl2InnerAutPSL2 K hoddpp hcard3 C y)) *
          ((SemidirectProduct.inl C)⁻¹)⁻¹ = _
        rw [hjι, toPGL_pgl2InnerAutPSL2_apply]
        simp only [map_mul, map_inv, inv_inv]
        group
      have hjt' : j' t = SemidirectProduct.inr (j t).right := by
        show (SemidirectProduct.inl C)⁻¹ * j t * ((SemidirectProduct.inl C)⁻¹)⁻¹ = _
        rw [inv_inv]
        exact hC
      have h4 := field_involution_rank hp5' hK ρ hρ j' hj' ι' hjι' htf hjt'
      have h5 := finrank_range_disp_le_of_offender ρ htB (L := 2) (hoff.trans (by omega))
      omega

end Offender

section Final

open CFSG CFSG.GorensteinWalter CFSG.QuasithinUnique.Setup.X3 CFSG.SectionRank.OddCover
  CFSG.LocalAnalysis.ComponentInitial CFSG.Quasithin CFSG.Assembly.LowTwoRank
  CFSG.QuasithinUnique.Setup

theorem primeSquareFiveExclusion2F
    (p : ℕ) (hp : p.Prime) (hp5 : p = 5) (W : Type) [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) (Lb : Subgroup (MulAut W)) (hperf : Group.IsPerfect ↥Lb)
    (hirr : X1.IsIrrOn Lb) (hmod : StatedClassicalModel (CQ Lb) .PSL 2 p 2)
    (A : Subgroup (MulAut W)) (hAN : A ≤ Subgroup.normalizer (Lb : Set (MulAut W)))
    (hA1 : A ≠ ⊥) (hA2 : IsElemAbelian2 A) :
    Nat.card A ^ 2 * Nat.card (fixV A) < Nat.card W := by
  have hp5' : 5 ≤ p := by omega
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (∀ w : W, w * w = 1) := ⟨hW⟩
  have : Nontrivial W := hirr.1
  have hp2 : p ≠ 2 := by omega
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have := hperf
  have hodd := odd_card_center_of_irreducible hW hirr.2
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
  have : Fintype K := Fintype.ofFinite K
  have hKcard : Fintype.card K = p ^ 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hK
  have : CharP K p := charP_of_card_eq_prime_pow hKcard
  have hoddpp := isOddPrimePower_sq hp5' hKcard
  have hcard3 := three_lt_card_sq hp5' hKcard
  let π : ↥Lb →* StatedProj (StatedSL 2 K) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥Lb))
  have hπs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center ↥Lb := ker_comp_mk'_center e
  have hcenter : Subgroup.center ↥Lb = ⊥ := by
    have h25 : 25 ≤ p ^ 2 := by nlinarith
    have h := (odd_psl_two_perfect_odd_cover_kernel (p := p) (f := 2) hp2 hK π hπs hker.le
      (hker ▸ hodd)).1 (by omega)
    rw [← hker]
    exact h
  have hπinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).1 (hker.trans hcenter)
  let θ : ↥Lb ≃* PSL2 K :=
    (MulEquiv.ofBijective π ⟨hπinj, hπs⟩).trans
      (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  have hHn : Lb ⊔ A ≤ Subgroup.normalizer (Lb : Set (MulAut W)) :=
    sup_le Subgroup.le_normalizer hAN
  have hNnormal : (Lb.subgroupOf (Lb ⊔ A)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 hHn
  let θ' : (Lb.subgroupOf (Lb ⊔ A)) ≃* PSL2 K :=
    (Subgroup.subgroupOfEquivOfLe (le_sup_left : Lb ≤ Lb ⊔ A)).trans θ
  have hC := centralizer_trivial hW hirr.2 hcenter hAN hA2
  have hCbot : Subgroup.centralizer
      ((Lb.subgroupOf (Lb ⊔ A) : Subgroup ↥(Lb ⊔ A)) : Set ↥(Lb ⊔ A)) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    apply hC z
    intro n hn
    exact (Subgroup.mem_centralizer_iff.1 hz n hn).symm
  have hsurj : Function.Surjective (pGammaL2ToMulAutPSL2 K hoddpp hcard3) :=
    pGammaL2ToMulAutPSL2_surjective K (p := p) (f := 2) hK hoddpp hcard3
  let j := normalPSL2ToPGammaL2 (Lb.subgroupOf (Lb ⊔ A)) K hoddpp hcard3 θ' hsurj
  have hj : Function.Injective j :=
    normalPSL2ToPGammaL2_injective _ K hoddpp hcard3 θ' hCbot hsurj
  let ι : PSL2 K →* ↥(Lb ⊔ A) := (Lb.subgroupOf (Lb ⊔ A)).subtype.comp θ'.symm.toMonoidHom
  have hjι : ∀ y, j (ι y) =
      SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL y) := fun y =>
    normalPSL2ToPGammaL2_apply _ K hoddpp hcard3 θ' hsurj y
  let ρH : ↥(Lb ⊔ A) →* (Additive W ≃ₗ[ZMod 2] Additive W) := binaryLin.comp (Lb ⊔ A).subtype
  have hρH : ∀ (g : ↥(Lb ⊔ A)) (v : Additive W),
      ρH g v = Additive.ofMul ((g : MulAut W) (Additive.toMul v)) := fun g v => rfl
  have hρinj : Function.Injective ρH := by
    intro g g' h
    apply Subtype.ext
    apply MulEquiv.ext
    intro w
    have h1 := LinearEquiv.congr_fun h (Additive.ofMul w)
    rw [hρH, hρH] at h1
    exact Additive.ofMul.injective h1
  by_contra hne
  push Not at hne
  have hAH : A ≤ Lb ⊔ A := le_sup_right
  have hB1 : A.subgroupOf (Lb ⊔ A) ≠ ⊥ := by
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA1
    refine Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨⟨a, hAH a.2⟩, a.2⟩, fun h => ha ?_⟩
    exact Subtype.ext
      (congrArg (fun x : ↥(A.subgroupOf (Lb ⊔ A)) => ((x : ↥(Lb ⊔ A)) : MulAut W)) h)
  have hBc : ∀ a ∈ A.subgroupOf (Lb ⊔ A), ∀ b ∈ A.subgroupOf (Lb ⊔ A), a * b = b * a :=
    fun a ha b hb => Subtype.ext (hA2.1 _ ha _ hb)
  have hB2 : ∀ a ∈ A.subgroupOf (Lb ⊔ A), a * a = 1 := fun a ha => by
    apply Subtype.ext
    have := hA2.2 _ ha
    rwa [pow_two] at this
  have hfix : Nat.card (fixedSub ρH (A.subgroupOf (Lb ⊔ A))) = Nat.card (fixV A) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨Additive.toMul x.1, fun a ha => ?_⟩
        invFun := fun w => ⟨Additive.ofMul w.1, fun b hb => ?_⟩
        left_inv := fun x => Subtype.ext rfl
        right_inv := fun w => Subtype.ext rfl }
    · have h1 := x.2 ⟨a, hAH ha⟩ ha
      exact congrArg Additive.toMul h1
    · have hb' : (b : MulAut W) ∈ A := hb
      have h1 := w.2 (b : MulAut W) hb'
      exact congrArg Additive.ofMul h1
  have hcardB : Nat.card (A.subgroupOf (Lb ⊔ A)) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv
  have hpgrp : IsPGroup 2 (A.subgroupOf (Lb ⊔ A)) := fun a => ⟨1, by
    rw [pow_one, pow_two]
    exact Subtype.ext (hB2 (a : ↥(Lb ⊔ A)) a.2)⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hpgrp
  have hcardE : Nat.card (Additive W) = Nat.card W := Nat.card_congr Additive.toMul
  have hoff : finrank (ZMod 2) (Additive W) -
      finrank (ZMod 2) (fixedSub ρH (A.subgroupOf (Lb ⊔ A))) ≤
        2 * Nat.log 2 (Nat.card (A.subgroupOf (Lb ⊔ A))) := by
    refine finrank_sub_le_two_log_of_card_le _ hk ?_
    rw [hcardE, hcardB, hfix]
    exact hne
  exact no_offender2_gamma25 hp5 hKcard ρH hρinj j hj ι hjι hB1 hBc hB2 hoff

end Final

end CFSG.Quasithin.B45Exc

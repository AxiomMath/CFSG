module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OFixW
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16ONorm
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214Rk
public import CFSG.Quasithin.Background.HMultNorm
public import CFSG.Quasithin.Vol2.Ch11SecBK8Base4

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Open
open scoped Matrix

theorem quadForm_ne_zero_of_isometry_line {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (hsep : ∀ w : V, w ≠ 0 → ∃ v, QuadraticMap.polar Q v w ≠ 0)
    (g : V →ₗ[K] V) (hg : ∀ v, Q (g v) = Q v) {w : V}
    (hline : ∀ v, ∃ c : K, g v - v = c • w) (hw : ∃ v, g v - v = w) (hw0 : w ≠ 0) :
    Q w ≠ 0 := by
  intro hQw
  have key : ∀ (v : V) (c : K), g v - v = c • w → c * QuadraticMap.polar Q v w = 0 := by
    intro v c hc
    have h1 : g v = v + c • w := by rw [← hc]; abel
    have h2 := hg v
    rw [h1, QuadraticMap.map_add (⇑Q) v (c • w), QuadraticMap.map_smul, hQw,
      QuadraticMap.polar_smul_right] at h2
    simp only [smul_eq_mul, mul_zero, add_zero] at h2
    linear_combination h2
  obtain ⟨v₁, hv₁⟩ := hw
  obtain ⟨v₂, hv₂⟩ := hsep w hw0
  obtain ⟨c₂, hc₂⟩ := hline v₂
  have hk1 : QuadraticMap.polar Q v₁ w = 0 := by
    simpa using key v₁ 1 (by rw [one_smul]; exact hv₁)
  have hk2 : c₂ = 0 := (mul_eq_zero.mp (key v₂ c₂ hc₂)).resolve_right hv₂
  have h0 : g v₂ - v₂ = 0 := by rw [hc₂, hk2, zero_smul]
  have h3 : g (v₁ + v₂) - (v₁ + v₂) = (1 : K) • w := by
    rw [map_add, one_smul]
    calc g v₁ + g v₂ - (v₁ + v₂) = (g v₁ - v₁) + (g v₂ - v₂) := by abel
      _ = w := by rw [hv₁, h0, add_zero]
  have h4 := key (v₁ + v₂) 1 h3
  rw [one_mul, QuadraticMap.polar_add_left, hk1, zero_add] at h4
  exact hv₂ h4

theorem exists_elemAbelian_fix_of_quadMinus_ne_zero {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {n p : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    (hp : p.Prime) (hcong : (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)])
    {a : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K}
    (ha : StatedQuadMinus 3 K b c a ≠ 0) :
    ∃ E : Subgroup (GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K),
      E ≤ StatedOmega (StatedQuadMinus 3 K b c) ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
        ∀ γ ∈ E, ((γ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) :
          Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
            (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) *ᵥ a = a := by
  obtain ⟨M⟩ := CFSG.LocalAnalysis.RankThreeUC.nonempty_normModel (F := K) (b := b) (c := c)
    hirr hK hn
  have hpq : p ∣ Nat.card K + 1 := by
    rw [hK]
    exact CFSG.LocalAnalysis.UniquenessCase.UC22.P2214R.dvd_of_cong hcong
  exact CFSG.LocalAnalysis.RankThreeUC.exists_stab_nonsing M hirr hp hpq ha

open CFSG.Quasithin.H.Mult in
theorem omegaMinus_smallComm_diag_three {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {n k p : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    [NeZero k] (hk : k ≤ 2) (hp : p.Prime) (hcong : (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)])
    {T : MulAut (StdMod (Fin k × (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)) K)}
    (hT : T ∈ Subgroup.normalizer
      (natImage (diagSub k (StatedOmega (StatedQuadMinus 3 K b c))) :
        Set (MulAut (StdMod (Fin k × (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)) K))))
    (hT2 : ∃ m : ℕ, orderOf T = 2 ^ m)
    (hcard : Nat.card (StdMod (Fin k × (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)) K) <
      2 ^ (2 * n * k) * Nat.card (fixV (Subgroup.zpowers T)))
    {z : StdMod (Fin k × (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)) K} (hz1 : z ≠ 1)
    (hz : z ∈ commSub ⊤ (Subgroup.zpowers T)) :
    ∃ E : Subgroup (GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K),
      E ≤ StatedOmega (StatedQuadMinus 3 K b c) ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
        ∀ γ ∈ E, matAut (diagGL k γ) z = z := by
  classical
  have hΓ : HasScalarCommutant (StatedOmega (StatedQuadMinus 3 K b c)) :=
    fun f hf => CFSG.LocalAnalysis.RankThreeUC.omega_commutant hirr f hf
  obtain ⟨A, σ, B, -, hAσ, hTσ, hform, hconj⟩ := exists_of_mem_normalizer_diag hΓ hT
  have hcardι : Fintype.card (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) = 6 := by simp
  have hW : Nat.card (StdMod (Fin k × (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)) K) =
      2 ^ (n * (k * 6)) := by
    rw [card_stdMod, hK, ← pow_mul, Fintype.card_prod, hcardι, Fintype.card_fin]
  have hkpos : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hσ : σ = RingEquiv.refl K := by
    by_contra hσ
    have h1 := CFSG.Quasithin.Vol2.Ch11.SecB.K8.card_fix_sq_le hTσ hσ
    rw [← card_fixV_zpowers] at h1
    have h1' : Nat.card (fixV (Subgroup.zpowers T)) ^ 2 ≤ 2 ^ (n * (k * 6)) := by
      rw [← hW]
      exact h1
    rw [hW] at hcard
    set F := Nat.card (fixV (Subgroup.zpowers T))
    have h2 : (2 ^ (n * (k * 6))) * 2 ^ (n * (k * 6)) <
        (2 ^ (2 * n * k) * F) * (2 ^ (2 * n * k) * F) := Nat.mul_self_lt_mul_self hcard
    have h3 : (2 ^ (2 * n * k) * F) * (2 ^ (2 * n * k) * F) ≤
        (2 ^ (2 * n * k) * 2 ^ (2 * n * k)) * 2 ^ (n * (k * 6)) := by
      calc (2 ^ (2 * n * k) * F) * (2 ^ (2 * n * k) * F)
          = (2 ^ (2 * n * k) * 2 ^ (2 * n * k)) * F ^ 2 := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ h1'
    have h4 : 2 ^ (n * (k * 6)) < 2 ^ (2 * n * k) * 2 ^ (2 * n * k) :=
      Nat.lt_of_mul_lt_mul_right (lt_of_lt_of_le h2 h3)
    rw [← pow_add] at h4
    have h5 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h4
    nlinarith
  subst hσ
  have hidx : rkIdx (fixV (Subgroup.zpowers T)) < 2 * n * k := by
    have h1 := (fixV (Subgroup.zpowers T)).card_mul_index
    rw [hW] at h1
    have hdvd : (fixV (Subgroup.zpowers T)).index ∣ 2 ^ (n * (k * 6)) := Dvd.intro_left _ h1
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hr : rkIdx (fixV (Subgroup.zpowers T)) = m := by
      unfold rkIdx
      rw [hm, padicValNat.prime_pow]
    rw [hr]
    rw [hW, ← h1, hm, mul_comm] at hcard
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp
      (Nat.lt_of_mul_lt_mul_right hcard)
  obtain ⟨c0, hc0⟩ : ∃ c0 : K,
      (B : Matrix (Fin k) (Fin k) K) = c0 • (1 : Matrix (Fin k) (Fin k) K) := by
    by_contra hB
    push Not at hB
    have h1 := le_rkIdx_fixV_of_nonscalar hK hAσ hform hB
    rw [hcardι] at h1
    nlinarith
  have hc0ne : c0 ≠ 0 := by
    rintro rfl
    have h1 : (B : Matrix (Fin k) (Fin k) K) * ((B⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K)
        = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [hc0, zero_smul, Matrix.zero_mul] at h1
    have h2 := congrFun (congrFun h1 0) 0
    simp at h2
  let s : MulAut (StdMod (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) :=
    { toFun := fun x => Multiplicative.ofAdd (c0 • Multiplicative.toAdd x)
      invFun := fun x => Multiplicative.ofAdd (c0⁻¹ • Multiplicative.toAdd x)
      left_inv := fun x => by
        simp only [toAdd_ofAdd, smul_smul, inv_mul_cancel₀ hc0ne, one_smul, ofAdd_toAdd]
      right_inv := fun x => by
        simp only [toAdd_ofAdd, smul_smul, mul_inv_cancel₀ hc0ne, one_smul, ofAdd_toAdd]
      map_mul' := fun x y => by
        simp only [toAdd_mul, smul_add, ofAdd_add] }
  set A' := s * A with hA'
  have hA'x : ∀ x, toAddMap A' x = c0 • toAddMap A x := fun x => rfl
  have hform' : ∀ (v : Fin k × (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) → K)
      (p : Fin k × (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)),
      toAddMap T v p = toAddMap A' (fun i => v (p.1, i)) p.2 := by
    intro v p
    rw [hform v p, hA'x]
    have hsum : (fun i => ∑ j, (B : Matrix (Fin k) (Fin k) K) p.1 j * v (j, i)) =
        c0 • fun i => v (p.1, i) := by
      funext i
      rw [hc0]
      simp [Matrix.smul_apply, Matrix.one_apply]
    rw [hsum, hAσ]
    rfl
  have hA'lin : IsSemilinear A' (RingEquiv.refl K) := by
    intro d x
    rw [hA'x, hA'x, hAσ, smul_comm]
  obtain ⟨M, hM⟩ := exists_matAut_of_mem_linSub (mem_linSub.mpr hA'lin)
  obtain ⟨m, hm⟩ := hT2
  have hTpow : T ^ (2 ^ m) = 1 := by rw [← hm]; exact pow_orderOf_eq_one T
  have hpowform : ∀ j : ℕ, ∀ (v : Fin k × (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) → K)
      (p : Fin k × (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)),
      toAddMap (T ^ j) v p = toAddMap (A' ^ j) (fun i => v (p.1, i)) p.2 := by
    intro j
    induction j with
    | zero => intro v p; rfl
    | succ j ih =>
      intro v p
      have hfun : (fun i => toAddMap T v (p.1, i)) = toAddMap A' (fun i => v (p.1, i)) :=
        funext fun i => hform' v (p.1, i)
      rw [pow_succ, pow_succ, toAddMap_mul, toAddMap_mul, ih, hfun]
  have hblock : ∀ x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K,
      (fun i => blockVec (k := k) (0 : Fin k) x ((0 : Fin k), i)) = x := by
    intro x
    funext i
    simp [blockVec]
  have hA'pow : A' ^ (2 ^ m) = 1 := by
    apply toAddMap_injective
    intro x
    funext i
    have h1 := hpowform (2 ^ m) (blockVec (0 : Fin k) x) ((0 : Fin k), i)
    dsimp only at h1
    rw [hTpow, toAddMap_one, hblock] at h1
    rw [toAddMap_one, ← h1]
    simp [blockVec]
  have hMpow : M ^ (2 ^ m) = 1 := by
    apply matHom_injective
    rw [map_pow, map_one, matHom_apply, ← hM, hA'pow]
  have hMx : ∀ y, (M : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
      (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) *ᵥ y = c0 • toAddMap A y := fun y => by
    rw [← toAddMap_matAut, ← hM, hA'x]
  have hN : ∀ g ∈ StatedOmega (StatedQuadMinus 3 K b c),
      ∃ g' ∈ StatedOmega (StatedQuadMinus 3 K b c), ∀ x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K,
        (M : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) *ᵥ
          ((g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
            (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) *ᵥ x) =
          (g' : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
            (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) *ᵥ
            ((M : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
              (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) *ᵥ x) := by
    intro g hg
    obtain ⟨g', hg', hAg, -⟩ := hconj g hg
    refine ⟨g', hg', fun x => ?_⟩
    have h1 : A * matAut g = matAut g' * A := by
      rw [← hAg]
      group
    have h2 := congrArg
      (fun f : MulAut (StdMod (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) => toAddMap f x) h1
    simp only [toAddMap_mul, toAddMap_matAut] at h2
    rw [hMx, hMx, h2, Matrix.mulVec_smul]
  have hiso : ∀ x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K,
      StatedQuadMinus 3 K b c ((M : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
        (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) *ᵥ x) = StatedQuadMinus 3 K b c x :=
    CFSG.LocalAnalysis.RankThreeUC.omega_isometry_of_normalizes_pow hirr _ m
      (by simpa using congrArg Units.val hMpow) hN
  let f : (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) →ₗ[K]
      (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) :=
    Matrix.mulVecLin (M : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
      (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) - LinearMap.id
  have hf : ∀ x, f x = (M : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
      (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) *ᵥ x - x := fun x => rfl
  have hrk : rkIdx (fixV (Subgroup.zpowers A')) =
      n * (Fintype.card (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) -
        Module.finrank K (LinearMap.ker f)) :=
    rkIdx_fixV_eq_of_linear hK (LinearMap.ker f) (fun v => by
      rw [LinearMap.mem_ker, hf, sub_eq_zero, hM, toAddMap_matAut])
  have hrkA' : rkIdx (fixV (Subgroup.zpowers A')) < 2 * n := by
    have h1 := rkIdx_fixV_of_diag_formula hform'
    rw [h1, show 2 * n * k = k * (2 * n) by ring] at hidx
    exact Nat.lt_of_mul_lt_mul_left hidx
  have hker : 5 ≤ Module.finrank K (LinearMap.ker f) := by
    rw [hrk, hcardι] at hrkA'
    have hn0 : 0 < n := by omega
    have : 6 - Module.finrank K (LinearMap.ker f) < 2 := by
      by_contra hcon
      push Not at hcon
      nlinarith
    omega
  have hrange : Module.finrank K (LinearMap.range f) ≤ 1 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker f
    rw [Module.finrank_fintype_fun_eq_card, hcardι] at h1
    omega
  rw [commSub_zpowers_eq_map (fun _ _ _ _ => Subgroup.mem_top _)] at hz
  obtain ⟨v, -, rfl⟩ := Subgroup.mem_map.mp hz
  have hzb : ∀ j : Fin k, (fun i => Multiplicative.toAdd (commHom T v) (j, i)) =
      f (fun i => Multiplicative.toAdd v (j, i)) := by
    intro j
    funext i
    have h1 : toAddMap T (Multiplicative.toAdd v) (j, i) =
        ((M : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) *ᵥ
          fun i => Multiplicative.toAdd v (j, i)) i := by
      rw [hform', hM, toAddMap_matAut]
    rw [hf, Pi.sub_apply, ← h1, commHom_apply, toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply,
      sub_eq_add_neg]
    rfl
  obtain ⟨j₀, hj₀⟩ : ∃ j : Fin k, (fun i => Multiplicative.toAdd (commHom T v) (j, i)) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hz1
    apply Multiplicative.toAdd.injective
    funext q
    have := congrFun (hcon q.1) q.2
    simpa using this
  set a := f (fun i => Multiplicative.toAdd v (j₀, i)) with ha
  have ha0 : a ≠ 0 := by rw [ha, ← hzb j₀]; exact hj₀
  have hline : ∀ x, ∃ c : K, f x = c • a := by
    intro x
    have ha_mem : a ∈ LinearMap.range f := LinearMap.mem_range_self f _
    have hne : (⟨a, ha_mem⟩ : LinearMap.range f) ≠ 0 := fun h => ha0 (congrArg Subtype.val h)
    have h1 : Module.finrank K (LinearMap.range f) = 1 := by
      have hpos : 0 < Module.finrank K (LinearMap.range f) :=
        Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hne⟩
      omega
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp h1
      ⟨f x, LinearMap.mem_range_self f x⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩
  have hQa : StatedQuadMinus 3 K b c a ≠ 0 := by
    have hcoe : ⇑(CFSG.LieType.Universal.Spin.quadMinus 3 K b c) = StatedQuadMinus 3 K b c :=
      CFSG.LieType.Universal.Spin.coe_quadMinus 3 K b c
    have hnd := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 3 K hirr
    rw [← hcoe]
    refine quadForm_ne_zero_of_isometry_line (CFSG.LieType.Universal.Spin.quadMinus 3 K b c) ?_
      (Matrix.mulVecLin (M : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
        (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K)) ?_ (w := a) (fun x => hline x)
      ⟨_, rfl⟩ ha0
    · intro w hw
      by_contra hcon
      push Not at hcon
      apply hw
      apply hnd.1 w
      intro u
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]
      exact hcon u
    · intro x
      rw [hcoe]
      exact hiso x
  obtain ⟨E, hEΓ, hEa, hEcard, hEfix⟩ :=
    exists_elemAbelian_fix_of_quadMinus_ne_zero hirr (by omega) hK hp hcong hQa
  refine ⟨E, hEΓ, hEa, hEcard, fun γ hγ => ?_⟩
  apply Multiplicative.toAdd.injective
  funext q
  change (((diagGL k γ : GL _ K) : Matrix _ _ K) *ᵥ Multiplicative.toAdd (commHom T v)) q = _
  rw [diagGL_mulVec, hzb q.1]
  obtain ⟨c', hc'⟩ := hline (fun i => Multiplicative.toAdd v (q.1, i))
  rw [hc', Matrix.mulVec_smul, hEfix γ hγ, ← hc', ← hzb q.1]

open CFSG.Quasithin.H.Mult in
theorem omegaMinus_smallComm_diag {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {n k p : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    [NeZero k] (hk : k ≤ 2) (hp : p.Prime) (hcong : (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)])
    {T : MulAut (StdMod (Fin k × (Fin (6 / 2 - 1) ⊕ Fin (6 / 2 - 1) ⊕ Fin 2)) K)}
    (hT : T ∈ Subgroup.normalizer
      (natImage (diagSub k (StatedOmega (StatedQuadMinus (6 / 2) K b c))) :
        Set (MulAut (StdMod (Fin k × (Fin (6 / 2 - 1) ⊕ Fin (6 / 2 - 1) ⊕ Fin 2)) K))))
    (hT2 : ∃ m : ℕ, orderOf T = 2 ^ m)
    (hcard : Nat.card (StdMod (Fin k × (Fin (6 / 2 - 1) ⊕ Fin (6 / 2 - 1) ⊕ Fin 2)) K) <
      2 ^ (2 * n * k) * Nat.card (fixV (Subgroup.zpowers T)))
    {z : StdMod (Fin k × (Fin (6 / 2 - 1) ⊕ Fin (6 / 2 - 1) ⊕ Fin 2)) K} (hz1 : z ≠ 1)
    (hz : z ∈ commSub ⊤ (Subgroup.zpowers T)) :
    ∃ E : Subgroup (GL (Fin (6 / 2 - 1) ⊕ Fin (6 / 2 - 1) ⊕ Fin 2) K),
      E ≤ StatedOmega (StatedQuadMinus (6 / 2) K b c) ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
        ∀ γ ∈ E, matAut (diagGL k γ) z = z :=
  omegaMinus_smallComm_diag_three hirr hn hK hk hp hcong hT hT2 hcard hz1 hz

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18


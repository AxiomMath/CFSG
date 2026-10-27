module

public import CFSG.Quasithin.Background.HFL3Res

public section

namespace CFSG.Quasithin.H.L3Nine

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.Quasithin.H.SU3

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem norm_eq_one_of_rhoT_smul (hK : Nat.card K = (2 ^ n) ^ 2) {B : GL (Fin 3) K} {d : K}
    (hd : (B : Matrix (Fin 3) (Fin 3) K) = d • 1) (h : rhoT hK B = 1) : d * bar n d = 1 := by
  have h1 := congrArg (fun Y : HMod n K => mat Y 0 0) (congrArg (fun f => f (e00 hK)) h)
  simp only [MulAut.one_apply, mat_rhoT, hd, tw, mat_pt, rk1_apply] at h1
  simpa [Matrix.mul_apply, Fin.sum_univ_three, conjM, Matrix.smul_apply, rk1_apply] using h1

theorem det_pow_eq_one_of_mem_img (hK : Nat.card K = (2 ^ n) ^ 2) {A : GL (Fin 3) K}
    (hA : rhoT hK A ∈ img hK) : (A : Matrix (Fin 3) (Fin 3) K).det ^ (2 ^ n + 1) = 1 := by
  obtain ⟨g, hg⟩ := hA
  have hg' : rhoT hK (SpecialLinearGroup.toGL g) = rhoT hK A := hg
  have h : rhoT hK (A * (SpecialLinearGroup.toGL g)⁻¹) = 1 := by
    rw [map_mul, map_inv, hg', mul_inv_cancel]
  obtain ⟨d, hd⟩ := scalar_of_rhoT_eq_one hK h
  have hdd := norm_eq_one_of_rhoT_smul hK hd h
  have hdq : d ^ (2 ^ n + 1) = 1 := by
    rw [pow_succ, ← bar_apply, mul_comm]
    exact hdd
  have hA' : (A : Matrix (Fin 3) (Fin 3) K) = d • (g : Matrix (Fin 3) (Fin 3) K) := by
    have e : A = A * (SpecialLinearGroup.toGL g)⁻¹ * SpecialLinearGroup.toGL g := by group
    rw [e, Units.val_mul, hd, Matrix.smul_mul, Matrix.one_mul]
    rfl
  have hdet : (A : Matrix (Fin 3) (Fin 3) K).det = d ^ 3 := by
    rw [hA', Matrix.det_smul, g.2, Fintype.card_fin, mul_one]
  rw [hdet, ← pow_mul, mul_comm, pow_mul, hdq, one_pow]

omit [Finite K] [CharP K 2] in
theorem not_dvd_two_pow_add_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n - 1) :
    ¬ p ∣ 2 ^ n + 1 := by
  intro h
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h2 : p ∣ 2 ^ n + 1 - (2 ^ n - 1) := Nat.dvd_sub h hpq
  have h3 : 2 ^ n + 1 - (2 ^ n - 1) = 2 := by omega
  rw [h3] at h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)

theorem rhoT_eq_one_of_smul (hK : Nat.card K = (2 ^ n) ^ 2) {B : GL (Fin 3) K} {d : K}
    (hd : (B : Matrix (Fin 3) (Fin 3) K) = d • 1) (hdd : d * bar n d = 1) : rhoT hK B = 1 := by
  have hd0 : d ≠ 0 := fun h0 => by rw [h0, zero_mul] at hdd; exact zero_ne_one hdd
  have hB : B = scalGL (Units.mk0 d hd0) := Units.ext (by rw [hd, coe_scalGL, Units.val_mk0])
  refine MulEquiv.ext fun X => mat_injective ?_
  rw [hB, mat_rhoT_scalGL, Units.val_mk0, hdd, one_smul]
  rfl

theorem rhoT_mem_img_sup (hK : Nat.card K = (2 ^ n) ^ 2) {A D : GL (Fin 3) K} {m : ℕ} {l : Kˣ}
    (hl : (l : K) * bar n (l : K) = 1)
    (hdet : (A : Matrix (Fin 3) (Fin 3) K).det =
      (D : Matrix (Fin 3) (Fin 3) K).det ^ m * (l : K) ^ 3) :
    rhoT hK A ∈ img hK ⊔ Subgroup.zpowers (rhoT hK D) := by
  set B := A * (D ^ m)⁻¹ * scalGL l⁻¹ with hBdef
  have hB : (B : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    have h1 : Matrix.GeneralLinearGroup.det B = 1 := by
      have hA : Matrix.GeneralLinearGroup.det A =
          Matrix.GeneralLinearGroup.det D ^ m * l ^ 3 := Units.ext (by
        simp only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_mul, Units.val_pow_eq_pow_val]
        exact hdet)
      rw [hBdef, map_mul, map_mul, map_inv, map_pow, hA, scalGL,
        Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin,
        mul_right_comm (Matrix.GeneralLinearGroup.det D ^ m) (l ^ 3), mul_inv_cancel, one_mul,
        inv_pow, mul_inv_cancel]
    have := congrArg Units.val h1
    rwa [Matrix.GeneralLinearGroup.val_det_apply] at this
  have hscal : rhoT hK (scalGL l⁻¹) = 1 := by
    refine rhoT_eq_one_of_smul hK (d := ((l⁻¹ : Kˣ) : K)) (coe_scalGL _) ?_
    rw [Units.val_inv_eq_inv_val, map_inv₀, ← mul_inv, hl, inv_one]
  have e : rhoT hK A = rhoT hK B * rhoT hK D ^ m := by
    rw [hBdef, map_mul, map_mul, hscal, mul_one, map_inv, map_pow, inv_mul_cancel_right]
  rw [e]
  exact Subgroup.mul_mem_sup (rhoT_mem_img hK hB) (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) m)

theorem entries_of_fix_blkW (hK : Nat.card K = (2 ^ n) ^ 2) {D : GL (Fin 3) K}
    (hfix : ∀ X ∈ blkW n K, rhoT hK D X = X) :
    (D : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 ∧ (D : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 ∧
      (D : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 ∧ (D : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 ∧
      (D : Matrix (Fin 3) (Fin 3) K) 1 1 = (D : Matrix (Fin 3) (Fin 3) K) 0 0 ∧
      (D : Matrix (Fin 3) (Fin 3) K) 0 0 * bar n ((D : Matrix (Fin 3) (Fin 3) K) 0 0) = 1 := by
  set M := (D : Matrix (Fin 3) (Fin 3) K) with hM
  have key : ∀ v : Fin 3 → K, v 2 = 0 → ∀ i j,
      (M *ᵥ v) i * bar n ((M *ᵥ v) j) = v i * bar n (v j) := by
    intro v hv i j
    have h := congrArg mat (hfix _ (pt_mem_blkW hK hv))
    rw [rhoT_pt, mat_pt, mat_pt] at h
    have := congrFun (congrFun h i) j
    rwa [rk1_apply, rk1_apply] at this
  have k0 := key (Pi.single 0 1) (by simp)
  have k1 := key (Pi.single 1 1) (by simp)
  have k2 := key ![1, 1, 0] (by simp)
  have a11 := k0 1 1
  have a22 := k0 2 2
  have a00 := k0 0 0
  have b00 := k1 0 0
  have b22 := k1 2 2
  have b11 := k1 1 1
  have c01 := k2 0 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at a11 a22 a00 b00 b22 b11 c01
  have e10 : M 1 0 = 0 := a11
  have e20 : M 2 0 = 0 := a22
  have e01 : M 0 1 = 0 := b00
  have e21 : M 2 1 = 0 := b22
  rw [e01, e10] at c01
  simp at c01
  refine ⟨e10, e20, e01, e21, ?_, a00⟩
  have hb : bar n (M 1 1) ≠ 0 := fun h0 => by rw [h0, mul_zero] at b11; exact zero_ne_one b11
  exact (mul_right_cancel₀ hb (b11.trans c01.symm))


theorem three_le_pRank_of_fix_blkW (hK : Nat.card K = (2 ^ n) ^ 2) {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n - 1) {D : GL (Fin 3) K} (hyo : orderOf (rhoT hK D) = p)
    (hfix : ∀ X ∈ blkW n K, rhoT hK D X = X) :
    rhoT hK D ∉ img hK ∧ 3 ≤ CFSG.Open.pRank p (img hK ⊔ Subgroup.zpowers (rhoT hK D)) := by
  obtain ⟨e10, e20, e01, e21, e11, hbb⟩ := entries_of_fix_blkW hK hfix
  set M := (D : Matrix (Fin 3) (Fin 3) K) with hM
  set b := M 0 0 with hb
  set c := M 2 2 with hc
  have hMeta : M = !![b, 0, M 0 2; 0, b, M 1 2; 0, 0, c] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [e10, e20, e01, e21, e11, hb, hc]
  have hb0 : b ≠ 0 := fun h0 => by rw [h0, zero_mul] at hbb; exact zero_ne_one hbb
  have hdetM : M.det = b * b * c := by
    rw [hMeta, Matrix.det_fin_three]
    simp
  have hdet0 : M.det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero D
  have hc0 : c ≠ 0 := fun h0 => hdet0 (by rw [hdetM, h0, mul_zero])
  have hbq : b ^ (2 ^ n + 1) = 1 := by
    rw [pow_succ, ← bar_apply, mul_comm]
    exact hbb
  set ζ := c * b⁻¹ with hζ
  have hζ0 : ζ ≠ 0 := mul_ne_zero hc0 (inv_ne_zero hb0)
  have hDp : rhoT hK (D ^ p) = 1 := by rw [map_pow, ← hyo, pow_orderOf_eq_one]
  obtain ⟨d, hd⟩ := scalar_of_rhoT_eq_one hK hDp
  obtain ⟨s, hs⟩ := exists_blk_pow b (M 0 2) (M 1 2) c p
  have hMp : !![b, 0, M 0 2; 0, b, M 1 2; 0, 0, c] ^ p = d • 1 := by
    rw [← hMeta, hM, ← Units.val_pow_eq_pow_val]
    exact hd
  rw [hs] at hMp
  have h1 : b ^ p = d := by simpa using congrFun (congrFun hMp 0) 0
  have h2 : c ^ p = d := by simpa using congrFun (congrFun hMp 2) 2
  have hζp : ζ ^ p = 1 := by
    rw [hζ, mul_pow, inv_pow, h2, ← h1, mul_inv_cancel₀ (pow_ne_zero _ hb0)]
  have hζ1 : ζ ≠ 1 := by
    intro h
    have hcb : c = b := by
      have := congrArg (· * b) h
      simpa [hζ, mul_assoc, inv_mul_cancel₀ hb0] using this
    have hM2 : M * M = (b ^ 2) • (1 : Matrix (Fin 3) (Fin 3) K) := by
      have h2' : (2 : K) = 0 := CharTwo.two_eq_zero
      rw [hMeta, hcb, Matrix.mul_fin_three]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [sq] <;> ring_nf <;> simp [h2']
    have hy2 : rhoT hK D ^ 2 = 1 := by
      rw [← map_pow]
      refine rhoT_eq_one_of_smul hK (d := b ^ 2) ?_ ?_
      · rw [Units.val_pow_eq_pow_val, sq, ← hM]
        exact hM2
      · rw [map_pow, ← mul_pow, hbb, one_pow]
    have := orderOf_dvd_of_pow_eq_one hy2
    rw [hyo] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)
  have hcop : Nat.Coprime p (2 ^ n + 1) :=
    (Nat.Prime.coprime_iff_not_dvd hp.out).mpr (not_dvd_two_pow_add_one hp.out hp2 hpq)
  have hnot : rhoT hK D ∉ img hK := by
    intro hmem
    have h := det_pow_eq_one_of_mem_img hK hmem
    rw [← hM, hdetM, mul_pow, mul_pow, hbq, one_mul, one_mul] at h
    have hζq : ζ ^ (2 ^ n + 1) = 1 := by rw [hζ, mul_pow, h, inv_pow, hbq, inv_one, one_mul]
    have h3 := pow_gcd_eq_one.mpr ⟨hζp, hζq⟩
    rw [hcop.gcd_eq_one, pow_one] at h3
    exact hζ1 h3
  refine ⟨hnot, ?_⟩
  set ζu : Kˣ := Units.mk0 ζ hζ0 with hζu
  have hζuo : orderOf ζu = p := by
    refine orderOf_eq_prime (Units.ext ?_) fun h => hζ1 ?_
    · rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one, hζp]
    · simpa [hζu] using congrArg Units.val h
  set Z := Subgroup.zpowers ζu with hZ
  have hZc : Nat.card Z = p := by rw [hZ, Nat.card_zpowers, hζuo]
  let δ : (Fin 3 → ↥Z) →* GL (Fin 3) K :=
    { toFun := fun t => ⟨Matrix.diagonal fun i => ((t i : Kˣ) : K),
        Matrix.diagonal fun i => (((t i : Kˣ)⁻¹ : Kˣ) : K), by simp [Matrix.diagonal_mul_diagonal],
        by simp [Matrix.diagonal_mul_diagonal]⟩
      map_one' := Units.ext (by simp)
      map_mul' := fun t t' => Units.ext (by simp [Matrix.diagonal_mul_diagonal]) }
  have hδ : ∀ t, ((δ t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal fun i => ((t i : Kˣ) : K) := fun t => rfl
  have hpow : ∀ a : Fin 3 → ↥Z, a ^ p = 1 := fun a => funext fun i => by
    rw [Pi.pow_apply, Pi.one_apply, ← hZc]
    exact pow_card_eq_one'
  have hcardA : Nat.card (Fin 3 → ↥Z) = p ^ 3 := by
    rw [Nat.card_fun, hZc, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hinj : Function.Injective ((rhoT hK).comp δ) := by
    rw [injective_iff_map_eq_one]
    intro t ht
    obtain ⟨d', hd'⟩ := scalar_of_rhoT_eq_one hK ht
    have hdd := norm_eq_one_of_rhoT_smul hK hd' ht
    have hdi : ∀ i, ((t i : Kˣ) : K) = d' := fun i => by
      have := congrFun (congrFun hd' i) i
      simpa [hδ] using this
    have hd'q : d' ^ (2 ^ n + 1) = 1 := by
      rw [pow_succ, ← bar_apply, mul_comm]
      exact hdd
    have hd'p : d' ^ p = 1 := by
      rw [← hdi 0]
      have := congrArg (fun u : ↥Z => ((u : Kˣ) : K)) (congrFun (hpow t) 0)
      simpa using this
    have hd1 : d' = 1 := by
      have h3 := pow_gcd_eq_one.mpr ⟨hd'p, hd'q⟩
      rwa [hcop.gcd_eq_one, pow_one] at h3
    funext i
    apply Subtype.ext
    apply Units.ext
    rw [hdi i, hd1]
    rfl
  refine CFSG.SectionRank.le_pRank_of_injective hp.out.one_lt (fun a b => mul_comm a b) hpow
    hcardA _ hinj ?_
  rintro _ ⟨t, rfl⟩
  have hmem : ∀ i, ∃ k : ℕ, ζu ^ k = (t i : Kˣ) := fun i =>
    (mem_powers_iff_mem_zpowers.mpr (t i).2)
  choose k hk using hmem
  set m := k 0 + k 1 + k 2 with hm
  have hbu : (((Units.mk0 b hb0)⁻¹ ^ m : Kˣ) : K) *
      bar n (((Units.mk0 b hb0)⁻¹ ^ m : Kˣ) : K) = 1 := by
    rw [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mk0, map_pow, map_inv₀,
      ← mul_pow, ← mul_inv, hbb, inv_one, one_pow]
  refine rhoT_mem_img_sup hK (m := m) (l := (Units.mk0 b hb0)⁻¹ ^ m) hbu ?_
  rw [hδ, Matrix.det_diagonal, Fin.prod_univ_three, ← hk 0, ← hk 1, ← hk 2, ← hM, hdetM]
  simp only [hζu, Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_inv_eq_inv_val]
  have hcz : c = ζ * b := by rw [hζ, mul_assoc, inv_mul_cancel₀ hb0, mul_one]
  have key : (b * b * (ζ * b)) ^ m * (b⁻¹ ^ m) ^ 3 = ζ ^ m * (b * b⁻¹) ^ (3 * m) := by ring
  rw [hcz, key, mul_inv_cancel₀ hb0, one_pow, mul_one, hm, pow_add, pow_add]

theorem three_le_pRank_of_large (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {A : Subgroup (MulAut (HMod n K))} (hA : A ≤ img hK) (hAe : IsElemAbelian2 A)
    (hcard : 2 ^ (3 * n) < Nat.card A) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n - 1) {y : MulAut (HMod n K)} (hy : y ∈ linImg hK) (hyo : orderOf y = p)
    {Z : Subgroup (HMod n K)} (hZA : Z ≤ fixV A) (hZy : Z ≤ fixV (Subgroup.zpowers y))
    (hZ : 2 ^ (3 * n) < Nat.card Z) :
    y ∉ img hK ∧ 3 ≤ CFSG.Open.pRank p (img hK ⊔ Subgroup.zpowers y) := by
  obtain ⟨g, P, hPU, -, hinj, hmap⟩ :=
    exists_conj_uni3 hK (hA.trans (img_le_linImg hK)) (IsElemAbelian2.isPGroup hAe)
  set c := rho hK g with hc
  rw [conj_eq_congrHom] at hmap
  have hAe' := (isElemAbelian2_map_congrHom c).2 hAe
  have hmem : ∀ x ∈ P, rho hK x ∈ A.map (congrHom c) := fun x hx => hmap ▸ ⟨x, hx, rfl⟩
  have hc' : ∀ x ∈ P, ∀ x' ∈ P, x * x' = x' * x := by
    intro x hx x' hx'
    have h1 : rho hK (x * x' * (x' * x)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, hAe'.1 _ (hmem x hx) _ (hmem x' hx'),
        mul_inv_cancel]
    exact mul_inv_eq_one.1 (hinj _ (P.mul_mem (P.mul_mem hx hx') (P.inv_mem (P.mul_mem hx' hx)))
      h1)
  have hs : ∀ x ∈ P, x * x = 1 := by
    intro x hx
    refine hinj _ (P.mul_mem hx hx) ?_
    rw [map_mul, ← sq]
    exact hAe'.2 _ (hmem x hx)
  have hcP : Nat.card P = Nat.card A := by
    rw [← card_map_rho_of_inj hK hinj, hmap, card_map_congrHom]
  set Z' := Z.map c.toMonoidHom with hZ'
  have hcZ' : Nat.card Z' = Nat.card Z := Subgroup.card_map_of_injective c.injective
  have hZ'A : Z' ≤ fixV (P.map (rho hK)) := by
    rw [hmap, fixV_map_congrHom]
    exact Subgroup.map_mono hZA
  have hcI : c ∈ img hK := ⟨g, rfl⟩
  rcases uni3_cases hPU hc' hs with hQ | hQ
  · exfalso
    have h1 := card_fixV_le_of_Q1 hn hK hPU hQ (hcP ▸ hcard)
    have h2 := (Subgroup.card_le_of_le hZ'A).trans h1
    rw [hcZ'] at h2
    have : 2 ^ n ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hfix := fixV_eq_blkW_of_Q2 hn hK hPU hQ (by
    rw [hcP]
    exact lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (by omega)) hcard)
  set y' := c * y * c⁻¹ with hy'
  obtain ⟨D, hD⟩ : y' ∈ linImg hK :=
    mul_mem (mul_mem (img_le_linImg hK hcI) hy) (inv_mem (img_le_linImg hK hcI))
  have hy'o : orderOf (rhoT hK D) = p := by
    rw [hD, hy', ← hyo]
    exact orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective y
  have hZ'y : Z' ≤ fixV (Subgroup.zpowers (rhoT hK D)) := by
    rintro _ ⟨v, hv, rfl⟩
    refine mem_fixV_zpowers_iff.mpr ?_
    have h1 : y v = v := mem_fixV_zpowers_iff.mp (hZy hv)
    show rhoT hK D (c v) = c v
    rw [hD, hy']
    show c (y (c⁻¹ (c v))) = c v
    rw [MulAut.inv_apply_self, h1]
  have hble : blkW n K ≤ fixV (Subgroup.zpowers (rhoT hK D)) := by
    refine blkW_le_fixV_of_card hn hK ?_
    have hle : Z' ≤ fixV (Subgroup.zpowers (rhoT hK D)) ⊓ blkW n K := le_inf hZ'y (hfix ▸ hZ'A)
    exact lt_of_lt_of_le (hcZ' ▸ hZ) (Subgroup.card_le_of_le hle)
  obtain ⟨hnot, hrk⟩ := three_le_pRank_of_fix_blkW hK hp2 hpq hy'o fun X hX =>
    mem_fixV_zpowers_iff.mp (hble hX)
  refine ⟨fun hyI => hnot ?_, ?_⟩
  · rw [hD, hy']
    exact mul_mem (mul_mem hcI hyI) (inv_mem hcI)
  · refine hrk.trans ((CFSG.SectionRank.pRank_le_map (Fact.out : p.Prime).one_lt
      (MulAut.conj c⁻¹).toMonoidHom (MulAut.conj c⁻¹).injective _).trans
      (CFSG.SectionRank.pRank_mono (Fact.out : p.Prime).one_lt ?_))
    rw [Subgroup.map_sup, sup_le_iff]
    constructor
    · rintro _ ⟨x, hx, rfl⟩
      exact le_sup_left (a := img hK) (mul_mem (mul_mem (inv_mem hcI) hx) (inv_mem (inv_mem hcI)))
    · rw [MonoidHom.map_zpowers, hD, hy']
      have : (MulAut.conj c⁻¹).toMonoidHom (c * y * c⁻¹) = y := by
        simp [mul_assoc]
      rw [this]
      exact le_sup_right

end CFSG.Quasithin.H.L3Nine

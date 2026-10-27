module

public import CFSG.Quasithin.Background.HSL3Two

public section

namespace CFSG.Quasithin

namespace H

namespace SL3One

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix SL3Pair
open scoped Matrix

theorem card_le_card_fixV_sq {W : Type*} [CommGroup W] [Finite W] (hW : ∀ v : W, v ^ 2 = 1)
    {t : MulAut W} (ht : t * t = 1) :
    Nat.card W ≤ Nat.card ↥(fixV (Subgroup.zpowers t)) ^ 2 := by
  let φ : W →* W :=
    { toFun := fun v => t v * v⁻¹
      map_one' := by rw [map_one, inv_one, mul_one]
      map_mul' := fun a b => by
        change t (a * b) * (a * b)⁻¹ = t a * a⁻¹ * (t b * b⁻¹)
        rw [map_mul, mul_inv]
        exact mul_mul_mul_comm _ _ _ _ }
  have hφ : ∀ v, φ v = t v * v⁻¹ := fun v => rfl
  have htt : ∀ v, t (t v) = v := fun v => by
    change (t * t) v = v
    rw [ht]
    rfl
  have hker : φ.ker = fixV (Subgroup.zpowers t) := by
    ext v
    rw [MonoidHom.mem_ker, hφ, mul_inv_eq_one, H.mem_fixV_zpowers_iff]
  have hle : φ.range ≤ φ.ker := by
    rintro _ ⟨v, rfl⟩
    rw [MonoidHom.mem_ker, hφ, hφ, map_mul, map_inv, htt, _root_.mul_inv_rev, inv_inv]
    have h := hW (v * (t v)⁻¹)
    rwa [sq] at h
  have h1 := Subgroup.card_ker_mul_card_range φ
  have h2 := Subgroup.card_le_of_le hle
  rw [hker] at h1 h2
  rw [← h1, sq]
  exact Nat.mul_le_mul_left _ h2

theorem card_mul_le_card_inf_mul_card_sup {W : Type*} [CommGroup W] [Finite W]
    (A B : Subgroup W) :
    Nat.card A * Nat.card B ≤ Nat.card ↥(A ⊓ B) * Nat.card ↥(A ⊔ B) := by
  let μ : ↥A × ↥B →* W := A.subtype.coprod B.subtype
  have hμ : ∀ p : ↥A × ↥B, μ p = (p.1 : W) * (p.2 : W) := fun p => rfl
  have h1 := Subgroup.card_ker_mul_card_range μ
  rw [Nat.card_prod] at h1
  have hr : μ.range ≤ A ⊔ B := by
    rintro _ ⟨p, rfl⟩
    rw [hμ]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)
  have hrel : ∀ p : μ.ker, ((p : ↥A × ↥B).1 : W) = ((p : ↥A × ↥B).2 : W)⁻¹ := fun p => by
    have h := p.2
    rw [MonoidHom.mem_ker, hμ] at h
    exact eq_inv_of_mul_eq_one_left h
  have hk : Nat.card μ.ker ≤ Nat.card ↥(A ⊓ B) := by
    refine Nat.card_le_card_of_injective
      (fun p => ⟨((p : ↥A × ↥B).1 : W), (p : ↥A × ↥B).1.2, ?_⟩) ?_
    · rw [hrel p]
      exact B.inv_mem (p : ↥A × ↥B).2.2
    · intro p q h
      have h1 : ((p : ↥A × ↥B).1 : W) = ((q : ↥A × ↥B).1 : W) :=
        congrArg (fun z : ↥(A ⊓ B) => (z : W)) h
      have h2 : ((p : ↥A × ↥B).2 : W) = ((q : ↥A × ↥B).2 : W) := by
        rw [← inv_inv ((p : ↥A × ↥B).2 : W), ← inv_inv ((q : ↥A × ↥B).2 : W), ← hrel p,
          ← hrel q, h1]
      exact Subtype.ext (Prod.ext (Subtype.ext h1) (Subtype.ext h2))
  calc Nat.card A * Nat.card B = Nat.card μ.ker * Nat.card μ.range := h1.symm
    _ ≤ Nat.card ↥(A ⊓ B) * Nat.card ↥(A ⊔ B) :=
      Nat.mul_le_mul hk (Subgroup.card_le_of_le hr)

theorem isElemAbelian2_zpowers_of_mul_self {W : Type*} [CommGroup W] {t : MulAut W}
    (ht : t * t = 1) : IsElemAbelian2 (Subgroup.zpowers t) := by
  refine ⟨?_, ?_⟩
  · rintro a ⟨m, rfl⟩ b ⟨n, rfl⟩
    exact (Commute.zpow_zpow_self t m n).eq
  · rintro a ⟨m, rfl⟩
    rw [← _root_.zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
      _root_.zpow_natCast, sq, ht, _root_.one_zpow]

theorem card_zpowers_eq_two {W : Type*} [Group W] {t : W} (ht : t * t = 1) (ht1 : t ≠ 1) :
    Nat.card (Subgroup.zpowers t) = 2 := by
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [sq]; exact ht) ht1

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
theorem stdMod_sq_eq_one (v : StdMod (Fin 3) K) : v ^ 2 = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one, two_nsmul]
  funext i
  show Multiplicative.toAdd v i + Multiplicative.toAdd v i = 0
  exact CharTwo.add_self_eq_zero _

omit [Finite K] in
theorem pairMod_sq_eq_one (v : PairMod K) : v ^ 2 = 1 :=
  Prod.ext (stdMod_sq_eq_one v.1) (stdMod_sq_eq_one v.2)

theorem card_pairMod_two (hK : Nat.card K = 2) : Nat.card (PairMod K) = 2 ^ 6 := by
  rw [card_pairMod, hK]

theorem card_fstSub_le_two_of_swap (hK : Nat.card K = 2) {E : Subgroup (MulAut (PairMod K))}
    (hEN : E ≤ pairNorm K) (hE2 : IsElemAbelian2 E) {y : MulAut (PairMod K)} (hyE : y ∈ E)
    (hy : y ∉ pairSub K) : Nat.card (fstSub E) ≤ 2 := by
  have : Finite (MulAut (StdMod (Fin 3) K)) := MulEquiv.finite_left
  have hF2 := isElemAbelian2_fstSub hE2
  obtain ⟨s, hsN, hyeq⟩ := exists_swap_decomp (hEN hyE) hy
  obtain ⟨hz₁, -⟩ := fstHom_mem_natNorm hsN
  have hΓ := hasScalarCommutant_statedSL (K := K) (by norm_num : 2 ≤ 3)
  have hzsl := isSemilinear_fieldAut hΓ ⟨_, hz₁⟩
  have h3 : Nat.card (linMat (fstSub E)) ≤ Nat.card K := by
    refine card_le_of_comm_transpose (linMat (fstSub E)) (linMat_sq hF2) (linMat_comm hF2)
      hzsl fun A hA v => ?_
    obtain ⟨x, hx, hxA⟩ := matAut_mem_of_mem_linMat hA
    have hxE : (x : MulAut (PairMod K)) ∈ E := (Subgroup.mem_subgroupOf.mp hx).1
    have hx2 : (x : MulAut (PairMod K)) * x = 1 := by
      rw [← sq]
      exact hE2.2 _ hxE
    obtain ⟨-, hμ1⟩ := snd_eq_transpose (hEN hxE) hx2 hxA
    have hxe := eq_pairAut x
    rw [hxA] at hxe
    have hxy : y * x = x * y := hE2.1 _ hyE _ hxE
    rw [hyeq, hxe, mul_assoc, pairAut_mul, ← mul_assoc, pairAut_mul_swapAut, mul_assoc,
      pairAut_mul] at hxy
    have hxy' := (pairAut_injective (mul_left_cancel hxy)).1
    have := congrArg (fun g => toAddMap g v) hxy'
    simp only [toAddMap_mul, toAddMap_matAut, hμ1] at this
    exact this
  rw [card_linMat, inf_eq_left.mpr fun a _ => mem_linSub_of_two hK a, hK] at h3
  exact h3

theorem card_le_four (hK : Nat.card K = 2) {E : Subgroup (MulAut (PairMod K))}
    (hEN : E ≤ pairNorm K) (hE2 : IsElemAbelian2 E) : Nat.card E ≤ 4 := by
  have : Finite (MulAut (StdMod (Fin 3) K)) := MulEquiv.finite_left
  have h1 := card_le_card_fstSub hEN hE2
  by_cases hsub : E ≤ pairSub K
  · rw [inf_eq_left.mpr hsub] at h1
    have h2 := card_le_of_le_natNorm (n := 1) le_rfl (by rw [hK, pow_one])
      (fstSub_le_natNorm hEN) (isElemAbelian2_fstSub hE2)
    rw [hK] at h2
    have h4 : (2 : ℕ) ^ 2 = 4 := by norm_num
    omega
  · obtain ⟨y, hyE, hy⟩ : ∃ y ∈ E, y ∉ pairSub K := by
      by_contra h
      push Not at h
      exact hsub h
    have h3 := card_fstSub_le_two_of_swap hK hEN hE2 hyE hy
    have h5 := card_le_two_mul_card_inf_pairSub hEN
    omega

theorem pRank_le (hK : Nat.card K = 2) {X : Subgroup (MulAut (PairMod K))}
    (hXN : X ≤ pairNorm K) : CFSG.Open.pRank 2 X ≤ 2 := by
  have : Finite (MulAut (PairMod K)) := MulEquiv.finite_left
  obtain ⟨E, hEX, hE, hEc⟩ := exists_isElemAbelian_card_pRank X
  have hE2 : IsElemAbelian2 E := isElemAbelian2_iff.mpr hE
  have h4 := card_le_four hK (hEX.trans hXN) hE2
  rw [hEc] at h4
  by_contra h
  push Not at h
  have : 2 ^ 3 ≤ 2 ^ CFSG.Open.pRank 2 X := Nat.pow_le_pow_right (by norm_num) h
  omega

theorem sixteen_le_card_fixV (hK : Nat.card K = 2) {x : MulAut (PairMod K)}
    (hxS : x ∈ pairSub K) (hx2 : x * x = 1) : 16 ≤ Nat.card ↥(fixV (Subgroup.zpowers x)) := by
  set s : ↥(pairSub K) := ⟨x, hxS⟩ with hs
  have hxe : x = pairAut (fstHom K s) (sndHom K s) := eq_pairAut s
  set a := fstHom K s with ha
  set b := sndHom K s with hb
  have hab : a * a = 1 ∧ b * b = 1 := by
    have h := hx2
    rw [hxe, pairAut_mul] at h
    exact pairAut_injective (h.trans pairAut_one.symm)
  have hfour : ∀ c : MulAut (StdMod (Fin 3) K), c * c = 1 →
      4 ≤ Nat.card ↥(fixV (Subgroup.zpowers c)) := by
    intro c hc
    have h1 := card_le_card_fixV_sq stdMod_sq_eq_one hc
    rw [card_stdMod, hK, Fintype.card_fin] at h1
    have h2 := card_eq_two_pow stdMod_sq_eq_one (fixV (Subgroup.zpowers c))
    rw [h2, ← pow_mul] at h1
    have h3 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
    rw [h2]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ rk ↥(fixV (Subgroup.zpowers c)) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hemb : Nat.card ↥(fixV (Subgroup.zpowers a)) * Nat.card ↥(fixV (Subgroup.zpowers b)) ≤
      Nat.card ↥(fixV (Subgroup.zpowers x)) := by
    rw [← Nat.card_prod]
    refine Nat.card_le_card_of_injective
      (fun p => ⟨((p.1 : StdMod (Fin 3) K), (p.2 : StdMod (Fin 3) K)), ?_⟩) ?_
    · rw [H.mem_fixV_zpowers_iff, hxe, pairAut_apply, H.mem_fixV_zpowers_iff.mp p.1.2,
        H.mem_fixV_zpowers_iff.mp p.2.2]
    · intro p q h
      have h' := congrArg (fun z : ↥(fixV (Subgroup.zpowers x)) => (z : PairMod K)) h
      exact Prod.ext (Subtype.ext (congrArg Prod.fst h')) (Subtype.ext (congrArg Prod.snd h'))
  have h4a := hfour a hab.1
  have h4b := hfour b hab.2
  calc 16 = 4 * 4 := by norm_num
    _ ≤ _ := Nat.mul_le_mul h4a h4b
    _ ≤ _ := hemb

theorem card_fixV_le_sixteen (hK : Nat.card K = 2) {x : MulAut (PairMod K)}
    (hx : x ∈ pairNorm K) (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    Nat.card ↥(fixV (Subgroup.zpowers x)) ≤ 16 := by
  have hle : Subgroup.zpowers x ≤ pairNorm K := Subgroup.zpowers_le.mpr hx
  have hne : Subgroup.zpowers x ≠ ⊥ := fun h => hx1 (Subgroup.zpowers_eq_bot.mp h)
  have h := card_mul_le_two hK hle (isElemAbelian2_zpowers_of_mul_self hx2) hne
  rw [card_zpowers_eq_two hx2 hx1] at h
  have e : (2 : ℕ) ^ 5 = 2 * 16 := by norm_num
  rw [e] at h
  exact Nat.le_of_mul_le_mul_left h (by norm_num)

theorem rkIdx_fixV_le_three {W : Type*} [CommGroup W] [Finite W] (hW : ∀ v : W, v ^ 2 = 1)
    (hcard : Nat.card W = 2 ^ 6) {t : MulAut W} (ht : t * t = 1) :
    rkIdx (fixV (Subgroup.zpowers t)) ≤ 3 := by
  have h1 := card_le_card_fixV_sq hW ht
  rw [hcard, SL3Pair.card_eq_two_pow_sub_rkIdx hcard, ← pow_mul] at h1
  have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
  omega

theorem mem_pairSL_of_mem_pairSub (hK : Nat.card K = 2) {x : MulAut (PairMod K)}
    (hxN : x ∈ pairNorm K) (hxS : x ∈ pairSub K) : x ∈ pairSL K := by
  have h01 : ∀ c : K, c = 0 ∨ c = 1 := by
    intro c
    by_contra hc
    push Not at hc
    have hinj : Function.Injective (![0, 1, c] : Fin 3 → K) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp_all [eq_comm, zero_ne_one]
    have := Nat.card_le_card_of_injective _ hinj
    rw [hK, Nat.card_eq_fintype_card, Fintype.card_fin] at this
    omega
  set s : ↥(pairSub K) := ⟨x, hxS⟩ with hs
  have hxe : x = pairAut (fstHom K s) (sndHom K s) := eq_pairAut s
  obtain ⟨A, hA⟩ := exists_matAut_of_mem_linSub (mem_linSub_of_two hK (fstHom K s))
  rw [hA] at hxe
  obtain ⟨μ, hμ⟩ := rel_linear (hxe ▸ hxN)
  have hμ1 : μ = 1 := by
    rcases h01 μ with h0 | h1
    · exfalso
      have hv := hμ (Pi.single 0 1)
      rw [h0, zero_smul, toAddMap_eq_zero_iff] at hv
      have := congrFun hv 0
      simp at this
    · exact h1
  have hb : sndHom K s = matAut (dualGL A) := toAddMap_injective fun w => by
    rw [hμ, hμ1, one_smul, toAddMap_matAut]
  have hAmem : A ∈ StatedSL 3 K := by
    rw [mem_statedSL_iff]
    have hdet : (A : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]
      exact Units.ne_zero _
    exact (h01 _).resolve_left hdet
  refine ⟨A, hAmem, ?_⟩
  rw [pairHom_apply, hxe, hb]

omit [Finite K] in
theorem orderOf_pairHom_tGL :
    orderOf (pairHom (tGL (K := K) 0 1 (by decide) 1)) = 2 := by
  have ht2 : tGL (K := K) 0 1 (by decide) 1 * tGL 0 1 (by decide) 1 = 1 := by
    apply Units.ext
    rw [Units.val_mul, coe_tGL, Matrix.transvection_mul_transvection_same (i := (0 : Fin 3))
      (j := 1) (by decide) (1 : K) 1, CharTwo.add_self_eq_zero, Matrix.transvection_zero,
      Units.val_one]
  have ht1 : tGL (K := K) 0 1 (by decide) 1 ≠ 1 := by
    intro h
    have h' := congrFun (congrFun (congrArg
      (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) h) 0) 1
    simp [coe_tGL, Matrix.transvection, Matrix.one_apply] at h'
  have hp1 : pairHom (tGL (K := K) 0 1 (by decide) 1) ≠ 1 := by
    intro h
    apply ht1
    apply matHom_injective
    rw [map_one, matHom_apply]
    have h' := h.trans pairAut_one.symm
    rw [pairHom_apply] at h'
    exact (pairAut_injective h').1
  refine orderOf_eq_prime ?_ hp1
  rw [sq, ← map_mul, ht2, map_one]

theorem two_le_mParam (hK : Nat.card K = 2) {X : Subgroup (MulAut (PairMod K))}
    (hXN : X ≤ pairNorm K) : 2 ≤ E3.mParam X := by
  classical
  have : Finite (MulAut (PairMod K)) := MulEquiv.finite_left
  unfold E3.mParam
  split_ifs with hev
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 2 (even_iff_two_dvd.mp hev)
    refine le_csInf ⟨_, (t : MulAut (PairMod K)), t.2,
      (Subgroup.orderOf_coe t).trans ht, rfl⟩ ?_
    rintro n ⟨s, hsX, hs2, rfl⟩
    have hss : s * s = 1 := by
      have h := pow_orderOf_eq_one s
      rw [hs2, sq] at h
      exact h
    have hs1 : s ≠ 1 := fun h => by rw [h, orderOf_one] at hs2; omega
    have h16 := card_fixV_le_sixteen hK (hXN hsX) hss hs1
    refine SL3Pair.le_rkIdx_of_card_mul_le (card_pairMod_two hK) _ ?_
    calc Nat.card ↥(fixV (Subgroup.zpowers s)) * 2 ^ 2 ≤ 16 * 2 ^ 2 :=
          Nat.mul_le_mul_right _ h16
      _ = 2 ^ 6 := by norm_num
  · rw [rk, card_pairMod_two hK]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [padicValNat.prime_pow]
    norm_num

theorem mParam_le_three (hK : Nat.card K = 2) {X : Subgroup (MulAut (PairMod K))}
    {t : MulAut (PairMod K)} (htX : t ∈ X) (ht2 : orderOf t = 2) : E3.mParam X ≤ 3 := by
  classical
  have : Finite (MulAut (PairMod K)) := MulEquiv.finite_left
  have htt : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht2, sq] at h
    exact h
  have hev : Even (Nat.card X) := by
    have h := Subgroup.orderOf_dvd_natCard (s := X) htX
    rw [ht2] at h
    exact even_iff_two_dvd.mpr h
  unfold E3.mParam
  rw [if_pos hev]
  refine le_trans (Nat.sInf_le ?_)
    (rkIdx_fixV_le_three pairMod_sq_eq_one (card_pairMod_two hK) htt)
  exact ⟨t, htX, ht2, rfl⟩

theorem exists_mem_pairSub (hK : Nat.card K = 2) {E : Subgroup (MulAut (PairMod K))}
    (hEN : E ≤ pairNorm K) (h4 : 4 ≤ Nat.card E) :
    ∃ x ∈ E, x ∈ pairSub K ∧ x ≠ 1 := by
  have h5 := card_le_two_mul_card_inf_pairSub hEN
  by_contra hcon
  push Not at hcon
  have hbot : E ⊓ pairSub K = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    exact Subgroup.mem_bot.mpr (hcon z hz.1 hz.2)
  rw [hbot, Subgroup.card_bot] at h5
  omega

theorem not_mem_aSet (hK : Nat.card K = 2) {X : Subgroup (MulAut (PairMod K))}
    (hXN : X ≤ pairNorm K) {k : ℕ} (hk : 2 ≤ k) {A : Subgroup (MulAut (PairMod K))} :
    A ∉ E3.aSet k X := by
  rintro ⟨hAX, hA1, hA2, hB⟩
  have : Finite (MulAut (PairMod K)) := MulEquiv.finite_left
  have hB' : ∀ B : Subgroup (MulAut (PairMod K)), B ≤ A →
      E3.mQuot A B < k → fixV B = fixV A := hB
  have hA1' : A ≠ (⊥ : Subgroup (MulAut (PairMod K))) := hA1
  have hAN : A ≤ pairNorm K := hAX.trans hXN
  have hpg : IsPGroup 2 ↥A := E3.isPGroup_of_isElemAbelian2 hA2
  have h4 := card_le_four hK hAN hA2
  by_cases h2 : Nat.card A ≤ 2
  ·
    have hrk : rk ↥A ≤ 1 := by
      have hAc : Nat.card A = 2 ^ rk ↥A := card_eq_two_pow_of_isPGroup hpg
      rw [hAc] at h2
      by_contra h
      push Not at h
      have : 2 ^ 2 ≤ 2 ^ rk ↥A := Nat.pow_le_pow_right (by norm_num) h
      omega
    have h1 := hB' ⊥ bot_le (by rw [mQuot_bot_eq_rk]; omega)
    refine hA1' ((Subgroup.eq_bot_iff_forall A).mpr fun a ha => MulEquiv.ext fun v => ?_)
    have hv0 : v ∈ fixV (⊥ : Subgroup (MulAut (PairMod K))) := fun x hx => by
      rw [Subgroup.mem_bot.mp hx]
      rfl
    rw [h1] at hv0
    exact hv0 a ha
  ·
    push Not at h2
    have h4' : 4 ≤ Nat.card A := by
      have hAc : Nat.card A = 2 ^ rk ↥A := card_eq_two_pow_of_isPGroup hpg
      rw [hAc] at h2 ⊢
      by_contra h
      push Not at h
      have h1 : rk ↥A ≤ 1 := by
        by_contra h'
        push Not at h'
        have : 2 ^ 2 ≤ 2 ^ rk ↥A := Nat.pow_le_pow_right (by norm_num) h'
        omega
      have : 2 ^ rk ↥A ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
      omega
    obtain ⟨x, hxA, hxS, hx1⟩ := exists_mem_pairSub hK hAN h4'
    have hxx : x * x = 1 := by
      rw [← sq]
      exact hA2.2 x hxA
    have hBA : Subgroup.zpowers x ≤ A := Subgroup.zpowers_le.mpr hxA
    have hm := E3.card_eq_two_pow_mul hpg hBA
    rw [card_zpowers_eq_two hxx hx1] at hm
    have hm1 : E3.mQuot A (Subgroup.zpowers x) < k := by
      by_contra h
      push Not at h
      have : 2 ^ 2 ≤ 2 ^ E3.mQuot A (Subgroup.zpowers x) :=
        Nat.pow_le_pow_right (by norm_num) (hk.trans h)
      have h8 : 2 ^ 2 * 2 ≤ Nat.card A := by
        rw [hm]
        exact Nat.mul_le_mul_right _ this
      omega
    have hfix := hB' _ hBA hm1
    have h16 := sixteen_le_card_fixV hK hxS hxx
    have h32 := card_mul_le_two hK hAN hA2 hA1
    rw [hfix] at h16
    have e : (2 : ℕ) ^ 5 = 32 := by norm_num
    rw [e] at h32
    have : 4 * 16 ≤ Nat.card A * Nat.card ↥(fixV A) := Nat.mul_le_mul h4' h16
    omega

theorem aParam_le (hK : Nat.card K = 2) {X : Subgroup (MulAut (PairMod K))}
    (hXN : X ≤ pairNorm K) : E3.aParam X ≤ 1 := by
  unfold E3.aParam
  split_ifs
  · apply csSup_le'
    rintro k ⟨-, A, hA⟩
    by_contra hk
    push Not at hk
    exact not_mem_aSet hK hXN hk hA
  · norm_num

theorem card_fixV_le_four_of_swap (hK : Nat.card K = 2) {E : Subgroup (MulAut (PairMod K))}
    (hEN : E ≤ pairNorm K) (hE2 : IsElemAbelian2 E) (h4 : Nat.card E = 4)
    {y : MulAut (PairMod K)} (hyE : y ∈ E) (hy : y ∉ pairSub K) :
    Nat.card ↥(fixV E) ≤ 4 := by
  classical
  have : Finite (MulAut (StdMod (Fin 3) K)) := MulEquiv.finite_left
  have hK1 : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  obtain ⟨s, -, hyeq⟩ := exists_swap_decomp (hEN hyE) hy
  have hfix : Nat.card ↥(fixV E) ≤
      Nat.card {v : StdMod (Fin 3) K // ∀ f ∈ fstSub E, f v = v} := by
    refine Nat.card_le_card_of_injective (fun v => ⟨(v : PairMod K).1, ?_⟩) fun v w h => ?_
    · rintro _ ⟨x, hx, rfl⟩
      have hxE : (x : MulAut (PairMod K)) ∈ E := (Subgroup.mem_subgroupOf.mp hx).1
      have := v.2 _ hxE
      rw [eq_pairAut x, pairAut_apply] at this
      exact congrArg Prod.fst this
    · have h' : (v : PairMod K).1 = (w : PairMod K).1 := congrArg Subtype.val h
      have hv := v.2 _ hyE
      have hw := w.2 _ hyE
      rw [hyeq] at hv hw
      have hv2 : (v : PairMod K).2 = fstHom K s (v : PairMod K).1 :=
        (congrArg Prod.snd hv).symm
      have hw2 : (w : PairMod K).2 = fstHom K s (w : PairMod K).1 :=
        (congrArg Prod.snd hw).symm
      exact Subtype.ext (Prod.ext h' (by rw [hv2, hw2, h']))
  obtain ⟨x, hxE, hxS, hx1⟩ := exists_mem_pairSub hK hEN h4.ge
  have hF1 : fstSub E ≠ ⊥ := by
    intro hF
    have h1 := card_le_card_fstSub hEN hE2
    rw [hF, Subgroup.card_bot] at h1
    have h2 : 1 < Nat.card ↥(E ⊓ pairSub K) := by
      rw [Finite.one_lt_card_iff_nontrivial]
      exact ⟨⟨⟨x, hxE, hxS⟩, 1, fun h => hx1 (congrArg Subtype.val h)⟩⟩
    omega
  obtain ⟨⟨f, hf⟩, hf1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hF1
  have hf2 : (f : MulAut (StdMod (Fin 3) K)) ^ 2 = 1 := (isElemAbelian2_fstSub hE2).2 _ hf
  have hfN := fstSub_le_natNorm hEN hf
  have hq2 : Nat.card {v : StdMod (Fin 3) K // ∀ f ∈ fstSub E, f v = v} ≤ Nat.card K ^ 2 := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun v : {v : StdMod (Fin 3) K // ∀ f ∈ fstSub E, f v = v} =>
        (⟨v.1, v.2 _ hf⟩ : {v : StdMod (Fin 3) K // (f : MulAut _) v = v}))
      fun v w h => Subtype.ext ?_) ?_
    · exact congrArg (fun z : {v : StdMod (Fin 3) K // (f : MulAut _) v = v} => z.1) h
    · exact card_fix_le_sq le_rfl hK1 hfN hf2 (fun h => hf1 (Subtype.ext h))
  rw [hK] at hq2
  have e : (2 : ℕ) ^ 2 = 4 := by norm_num
  rw [e] at hq2
  exact hfix.trans hq2

theorem card_sup_ge_of_swap (hK : Nat.card K = 2) {E : Subgroup (MulAut (PairMod K))}
    (hEN : E ≤ pairNorm K) (hE2 : IsElemAbelian2 E) (h4 : Nat.card E = 4)
    {x y : MulAut (PairMod K)} (hxE : x ∈ E) (hxS : x ∈ pairSub K) (hx1 : x ≠ 1) (hyE : y ∈ E)
    (hy : y ∉ pairSub K) :
    2 ^ 5 ≤ Nat.card ↥(fixV (Subgroup.zpowers x) ⊔ fixV (Subgroup.zpowers y)) := by
  have hxx : x * x = 1 := by
    rw [← sq]
    exact hE2.2 x hxE
  have hyy : y * y = 1 := by
    rw [← sq]
    exact hE2.2 y hyE
  have h16 := sixteen_le_card_fixV hK hxS hxx
  have h8 : 8 ≤ Nat.card ↥(fixV (Subgroup.zpowers y)) := by
    have h1 := card_le_card_fixV_sq pairMod_sq_eq_one hyy
    rw [card_pairMod_two hK] at h1
    have h2 := card_eq_two_pow pairMod_sq_eq_one (fixV (Subgroup.zpowers y))
    rw [h2, ← pow_mul] at h1
    have h3 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
    rw [h2]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ rk ↥(fixV (Subgroup.zpowers y)) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hinf : Nat.card ↥(fixV (Subgroup.zpowers x) ⊓ fixV (Subgroup.zpowers y)) ≤ 4 := by
    classical
    have : Finite (MulAut (StdMod (Fin 3) K)) := MulEquiv.finite_left
    have hK1 : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
    obtain ⟨s, -, hyeq⟩ := exists_swap_decomp (hEN hyE) hy
    set t : ↥(pairSub K) := ⟨x, hxS⟩ with ht
    have hxe : x = pairAut (fstHom K t) (sndHom K t) := eq_pairAut t
    have hab : fstHom K t * fstHom K t = 1 ∧ sndHom K t * sndHom K t = 1 := by
      have h := hxx
      rw [hxe, pairAut_mul] at h
      exact pairAut_injective (h.trans pairAut_one.symm)
    have ha1 : fstHom K t ≠ 1 := by
      intro h1
      apply hx1
      have hxN : pairAut 1 (sndHom K t) ∈ pairNorm K := by
        rw [← h1, ← hxe]
        exact hEN hxE
      rw [hxe, h1, eq_one_of_pairAut_one hxN hab.2]
      rfl
    have haN : fstHom K t ∈ natNorm (StatedSL 3 K) := (fstHom_mem_natNorm (x := t) (hEN hxE)).1
    have hq := card_fix_le_sq le_rfl hK1 haN (by rw [sq]; exact hab.1) ha1
    rw [hK] at hq
    have e : (2 : ℕ) ^ 2 = 4 := by norm_num
    rw [e] at hq
    refine le_trans (Nat.card_le_card_of_injective
      (fun v : ↥(fixV (Subgroup.zpowers x) ⊓ fixV (Subgroup.zpowers y)) =>
        (⟨(v : PairMod K).1, ?_⟩ : {w : StdMod (Fin 3) K // fstHom K t w = w})) ?_) hq
    · have key : ∀ u : PairMod K, x u = u → fstHom K t u.1 = u.1 := by
        intro u hu
        rw [hxe, pairAut_apply] at hu
        exact congrArg Prod.fst hu
      exact key _ (H.mem_fixV_zpowers_iff.mp v.2.1)
    · intro v w h
      have h' : (v : PairMod K).1 = (w : PairMod K).1 := congrArg Subtype.val h
      have key : ∀ u : PairMod K, y u = u → u.2 = fstHom K s u.1 := by
        intro u hu
        rw [hyeq] at hu
        exact (congrArg Prod.snd hu).symm
      have hv2 := key _ (H.mem_fixV_zpowers_iff.mp v.2.2)
      have hw2 := key _ (H.mem_fixV_zpowers_iff.mp w.2.2)
      exact Subtype.ext (Prod.ext h' (by rw [hv2, hw2, h']))
  have hprod := card_mul_le_card_inf_mul_card_sup (fixV (Subgroup.zpowers x))
    (fixV (Subgroup.zpowers y))
  have h128 : 16 * 8 ≤ Nat.card ↥(fixV (Subgroup.zpowers x)) *
      Nat.card ↥(fixV (Subgroup.zpowers y)) := Nat.mul_le_mul h16 h8
  have hpos : 0 < Nat.card ↥(fixV (Subgroup.zpowers x) ⊓ fixV (Subgroup.zpowers y)) :=
    Nat.card_pos
  have e : (2 : ℕ) ^ 5 = 32 := by norm_num
  rw [e]
  by_contra hlt
  push Not at hlt
  have : Nat.card ↥(fixV (Subgroup.zpowers x) ⊓ fixV (Subgroup.zpowers y)) *
      Nat.card ↥(fixV (Subgroup.zpowers x) ⊔ fixV (Subgroup.zpowers y)) < 4 * 32 := by
    calc _ ≤ 4 * Nat.card ↥(fixV (Subgroup.zpowers x) ⊔ fixV (Subgroup.zpowers y)) :=
          Nat.mul_le_mul_right _ hinf
      _ < 4 * 32 := by omega
  omega

theorem card_fixV_le_eight_of_sub (hK : Nat.card K = 2) {E : Subgroup (MulAut (PairMod K))}
    (hEN : E ≤ pairNorm K) (hE2 : IsElemAbelian2 E) (h4 : 4 ≤ Nat.card E)
    (hsub : E ≤ pairSub K) : Nat.card ↥(fixV E) ≤ 8 := by
  classical
  have : Finite (MulAut (StdMod (Fin 3) K)) := MulEquiv.finite_left
  have hlin : fstSub E ≤ linSub := fun a _ => mem_linSub_of_two hK a
  have hF2 := isElemAbelian2_fstSub hE2
  set E₀ := linMat (fstSub E) with hE₀
  have hEcard : Nat.card E₀ = Nat.card (fstSub E) := by
    rw [hE₀, card_linMat, inf_eq_left.mpr hlin]
  have h1 := card_le_card_fstSub hEN hE2
  rw [inf_eq_left.mpr hsub] at h1
  obtain ⟨hRC, hcard⟩ := card_le_of_elemAbelian_GL3' E₀ (linMat_sq hF2) (linMat_comm hF2)
  have hfix : Nat.card ↥(fixV E) ≤ Nat.card ↥(fixSp E₀) *
      Nat.card {w : Fin 3 → K // ∀ B ∈ E₀, (B : Matrix (Fin 3) (Fin 3) K)ᵀ *ᵥ w = w} := by
    rw [← Nat.card_prod]
    refine Nat.card_le_card_of_injective
      (fun v => (⟨Multiplicative.toAdd (v : PairMod K).1, ?_⟩,
        ⟨Multiplicative.toAdd (v : PairMod K).2, ?_⟩)) fun v w h => ?_
    · refine (Submodule.mem_iInf _).mpr fun B => ?_
      obtain ⟨⟨x, hx, hxB⟩, -⟩ := B.2
      have hxA : (x : MulAut (PairMod K)) ∈ E := (Subgroup.mem_subgroupOf.mp hx).1
      have h := v.2 _ hxA
      rw [eq_pairAut x, pairAut_apply, hxB] at h
      have h' : ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
          Multiplicative.toAdd (v : PairMod K).1 =
          Multiplicative.toAdd (v : PairMod K).1 :=
        congrArg (fun z : PairMod K => Multiplicative.toAdd z.1) h
      rw [LinearMap.mem_ker, nOf_apply, h', sub_self]
    · intro B hB
      obtain ⟨⟨x, hx, hxB⟩, -⟩ := hB
      have hxA : (x : MulAut (PairMod K)) ∈ E := (Subgroup.mem_subgroupOf.mp hx).1
      have hx2 : (x : MulAut (PairMod K)) * x = 1 := by
        rw [← sq]
        exact hE2.2 _ hxA
      obtain ⟨-, hT⟩ := snd_eq_transpose (hEN hxA) hx2 hxB
      have h := v.2 _ hxA
      rw [eq_pairAut x, pairAut_apply] at h
      have h' : toAddMap (sndHom K x) (Multiplicative.toAdd (v : PairMod K).2) =
          Multiplicative.toAdd (v : PairMod K).2 :=
        congrArg (fun z : PairMod K => Multiplicative.toAdd z.2) h
      rw [← hT]
      exact h'
    · have h1 := congrArg (fun p => (p.1 : Fin 3 → K)) h
      have h2 := congrArg (fun p => (p.2 : Fin 3 → K)) h
      exact Subtype.ext (Prod.ext h1 h2)
  have hD := card_transpose_fix_le E₀
  have hC : Nat.card ↥(fixSp E₀) = Nat.card K ^ Module.finrank K (fixSp E₀) :=
    Module.natCard_eq_pow_finrank (K := K) (V := fixSp E₀)
  have hc3 : Module.finrank K (fixSp E₀) ≤ 3 := by
    have := Submodule.finrank_le (fixSp E₀)
    rwa [Module.finrank_fin_fun] at this
  have hrc := Submodule.finrank_mono hRC
  have he : 2 ≤ (3 - Module.finrank K (fixSp E₀)) * Module.finrank K (commSp E₀) := by
    have hq : Nat.card K ^ ((3 - Module.finrank K (fixSp E₀)) * Module.finrank K (commSp E₀)) =
        2 ^ ((3 - Module.finrank K (fixSp E₀)) * Module.finrank K (commSp E₀)) := by rw [hK]
    have h4' : 2 ^ 2 ≤ 2 ^ ((3 - Module.finrank K (fixSp E₀)) * Module.finrank K (commSp E₀)) :=
      calc 2 ^ 2 = 4 := by norm_num
        _ ≤ Nat.card E := h4
        _ ≤ Nat.card E₀ := h1.trans hEcard.symm.le
        _ ≤ _ := hcard
        _ = _ := hq
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h4'
  have hexp : Module.finrank K (fixSp E₀) + (3 - Module.finrank K (commSp E₀)) ≤ 3 := by
    generalize Module.finrank K (fixSp E₀) = c at hc3 hrc he ⊢
    generalize Module.finrank K (commSp E₀) = r at hrc he ⊢
    interval_cases c <;> interval_cases r <;> omega
  calc Nat.card ↥(fixV E)
      ≤ Nat.card K ^ Module.finrank K (fixSp E₀) *
          Nat.card K ^ (3 - Module.finrank K (commSp E₀)) := by
        rw [← hC]
        exact hfix.trans (Nat.mul_le_mul_left _ hD)
    _ = 2 ^ (Module.finrank K (fixSp E₀) + (3 - Module.finrank K (commSp E₀))) := by
        rw [hK, ← pow_add]
    _ ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hexp
    _ = 8 := by norm_num

omit [Finite K] in
theorem mulVec_sub_fix {A B : GL (Fin 3) K} (hA : A * A = 1) (hB : B * B = 1)
    (hAB : A * B = B * A) (v : Fin 3 → K) :
    (B : Matrix (Fin 3) (Fin 3) K) *ᵥ ((A : Matrix (Fin 3) (Fin 3) K) *ᵥ v - v) =
      (A : Matrix (Fin 3) (Fin 3) K) *ᵥ v - v := by
  have h := comp_eq_zero_of_sq_eq_zero (Module.finrank_fin_fun K) (nOf_sq hB) (nOf_sq hA)
    (nOf_comm hAB.symm)
  have h' := LinearMap.congr_fun h v
  rw [LinearMap.comp_apply, nOf_apply, nOf_apply, LinearMap.zero_apply] at h'
  exact sub_eq_zero.mp h'

theorem fix_comm_of_sub (hK : Nat.card K = 2) {x y : MulAut (PairMod K)} (hxN : x ∈ pairNorm K)
    (hyN : y ∈ pairNorm K) (hxS : x ∈ pairSub K) (hyS : y ∈ pairSub K) (hx2 : x * x = 1)
    (hy2 : y * y = 1) (hxy : x * y = y * x) (v : PairMod K) : y (x v * v⁻¹) = x v * v⁻¹ := by
  set s : ↥(pairSub K) := ⟨x, hxS⟩ with hs
  set t : ↥(pairSub K) := ⟨y, hyS⟩ with ht
  obtain ⟨A, hA⟩ := exists_matAut_of_mem_linSub (mem_linSub_of_two hK (fstHom K s))
  obtain ⟨B, hB⟩ := exists_matAut_of_mem_linSub (mem_linSub_of_two hK (fstHom K t))
  obtain ⟨hA2, hAT⟩ := snd_eq_transpose (x := s) hxN hx2 hA
  obtain ⟨hB2, hBT⟩ := snd_eq_transpose (x := t) hyN hy2 hB
  have hxe : x = pairAut (matAut A) (sndHom K s) := by rw [← hA]; exact eq_pairAut s
  have hye : y = pairAut (matAut B) (sndHom K t) := by rw [← hB]; exact eq_pairAut t
  have hAB : A * B = B * A := by
    have h := hxy
    rw [hxe, hye, pairAut_mul, pairAut_mul] at h
    apply matHom_injective
    rw [map_mul, map_mul, matHom_apply, matHom_apply]
    exact (pairAut_injective h).1
  have hAinv : (A⁻¹ : GL (Fin 3) K) = A := inv_eq_of_mul_eq_one_right hA2
  have hBinv : (B⁻¹ : GL (Fin 3) K) = B := inv_eq_of_mul_eq_one_right hB2
  have hdA : ((dualGL A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (A : Matrix (Fin 3) (Fin 3) K)ᵀ := by rw [coe_dualGL, hAinv]
  have hdB : ((dualGL B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (B : Matrix (Fin 3) (Fin 3) K)ᵀ := by rw [coe_dualGL, hBinv]
  have hdA2 : dualGL A * dualGL A = 1 := by rw [← dualHom_apply, ← map_mul, hA2, map_one]
  have hdB2 : dualGL B * dualGL B = 1 := by rw [← dualHom_apply, ← map_mul, hB2, map_one]
  have hdAB : dualGL A * dualGL B = dualGL B * dualGL A := by
    rw [← dualHom_apply, ← dualHom_apply, ← map_mul, ← map_mul, hAB]
  have hcomp : ∀ (f g : MulAut (StdMod (Fin 3) K)) (P Q : GL (Fin 3) K), P * P = 1 →
      Q * Q = 1 → P * Q = Q * P →
      (∀ w, toAddMap f w = (P : Matrix (Fin 3) (Fin 3) K) *ᵥ w) →
      (∀ w, toAddMap g w = (Q : Matrix (Fin 3) (Fin 3) K) *ᵥ w) →
      ∀ a : StdMod (Fin 3) K, g (f a * a⁻¹) = f a * a⁻¹ := by
    intro f g P Q hP hQ hPQ hf hg a
    apply Multiplicative.toAdd.injective
    have e1 : Multiplicative.toAdd (f a * a⁻¹) =
        (P : Matrix (Fin 3) (Fin 3) K) *ᵥ Multiplicative.toAdd a - Multiplicative.toAdd a := by
      rw [toAdd_mul, toAdd_inv, ← sub_eq_add_neg]
      exact congrArg (· - Multiplicative.toAdd a) (hf (Multiplicative.toAdd a))
    have e2 : Multiplicative.toAdd (g (f a * a⁻¹)) =
        (Q : Matrix (Fin 3) (Fin 3) K) *ᵥ Multiplicative.toAdd (f a * a⁻¹) :=
      hg (Multiplicative.toAdd (f a * a⁻¹))
    rw [e2, e1]
    exact mulVec_sub_fix hP hQ hPQ _
  rw [hxe, hye]
  refine Prod.ext ?_ ?_
  · exact hcomp (matAut A) (matAut B) A B hA2 hB2 hAB (fun w => rfl) (fun w => rfl) v.1
  · exact hcomp (sndHom K s) (sndHom K t) (dualGL A) (dualGL B) hdA2 hdB2 hdAB
      (fun w => by rw [hAT, hdA]) (fun w => by rw [hBT, hdB]) v.2

theorem H4_SL3One {V : Type*} [CommGroup V] [Finite V] {H M : Subgroup (MulAut V)}
    {V₁ : Subgroup V} (hreal : BinaryNaturalSL H V₁ ⊥ 3 1) {φ : MulAut V}
    (hφ : φ ∈ Subgroup.normalizer (H : Set (MulAut V)))
    (hinf : V₁ ⊓ V₁.map φ.toMonoidHom = ⊥) (hsup : V₁ ⊔ V₁.map φ.toMonoidHom = ⊤)
    (hniso : ¬ Pair.IsoMod H V₁ (V₁.map φ.toMonoidHom)) (hHM : H ≤ M)
    (hMN : M ≤ Subgroup.normalizer (H : Set (MulAut V))) :
    Nat.card V = 2 ^ 6 ∧ CFSG.Open.pRank 2 M ≤ 2 ∧ 2 ≤ E3.mParam M ∧ E3.mParam M ≤ 3 ∧
      E3.aParam M ≤ 1 ∧
      ∀ E : Subgroup (MulAut V), E ≤ M → IsElemAbelian2 E → Nat.card E = 4 → ¬ E ≤ H →
        Nat.card ↥(fixV E) ≤ 4 ∧ ∃ x ∈ E, ∃ y ∈ E, x ∈ H ∧ x ≠ 1 ∧ y ∉ H ∧
          2 ^ 5 ≤ Nat.card ↥(fixV (Subgroup.zpowers x) ⊔ fixV (Subgroup.zpowers y)) := by
  obtain ⟨K, _, _, hK, hreal'⟩ := hreal
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two le_rfl hK
  have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
  obtain ⟨e, he⟩ := exists_pair_model hreal' hφ hinf hsup hniso
  have : Finite (PairMod K) := Finite.of_equiv V e.toEquiv
  have h1 : pairSL K ≤ M.map (congrHom e) := he ▸ Subgroup.map_mono hHM
  have h2 : M.map (congrHom e) ≤ pairNorm K := by
    have h3 : (Subgroup.normalizer (H : Set (MulAut V))).map (congrHom e) =
        Subgroup.normalizer ((H.map (congrHom e) : Subgroup (MulAut (PairMod K))) :
          Set (MulAut (PairMod K))) :=
      Subgroup.map_equiv_normalizer_eq H (MulAut.congr e)
    rw [pairNorm, ← he, ← h3]
    exact Subgroup.map_mono hMN
  have ht₀ : pairHom (tGL (K := K) 0 1 (by decide) 1) ∈ pairSL K :=
    ⟨_, tGL_mem 0 1 (by decide) 1, rfl⟩
  refine ⟨(Nat.card_congr e.toEquiv).trans (card_pairMod_two hK2), ?_, ?_, ?_, ?_,
    fun E hEM hE2 hE4 hEH => ?_⟩
  · rw [← pRank_two_map_congrHom e]
    exact pRank_le hK2 h2
  · rw [← mParam_map_congrHom e]
    exact two_le_mParam hK2 h2
  · rw [← mParam_map_congrHom e]
    exact mParam_le_three hK2 (h1 ht₀) orderOf_pairHom_tGL
  · rw [← aParam_map_congrHom e]
    exact aParam_le hK2 h2
  ·
    have hE'N : E.map (congrHom e) ≤ pairNorm K := (Subgroup.map_mono hEM).trans h2
    have hE'2 : IsElemAbelian2 (E.map (congrHom e)) := (isElemAbelian2_map_congrHom e).mpr hE2
    have hE'4 : Nat.card ↥(E.map (congrHom e)) = 4 := by rw [card_map_congrHom, hE4]
    have hmemH : ∀ z : MulAut V, congrHom e z ∈ pairSL K ↔ z ∈ H := by
      intro z
      rw [← he]
      exact ⟨fun ⟨w, hw, hwz⟩ => congrHom_injective e hwz ▸ hw, fun hz => ⟨z, hz, rfl⟩⟩
    obtain ⟨y, hyE, hyH⟩ : ∃ y ∈ E, y ∉ H := by
      by_contra h
      push Not at h
      exact hEH h
    have hyS : congrHom e y ∉ pairSub K := fun hS =>
      hyH ((hmemH y).mp (mem_pairSL_of_mem_pairSub hK2 (hE'N ⟨y, hyE, rfl⟩) hS))
    obtain ⟨x', hx'E, hx'S, hx'1⟩ := exists_mem_pairSub hK2 hE'N hE'4.ge
    obtain ⟨x, hxE, rfl⟩ := hx'E
    have hxH : x ∈ H := (hmemH x).mp (mem_pairSL_of_mem_pairSub hK2 (hE'N ⟨x, hxE, rfl⟩) hx'S)
    have hx1 : x ≠ 1 := fun h => hx'1 (by rw [h, map_one])
    have hfix := card_fixV_le_four_of_swap hK2 hE'N hE'2 hE'4 ⟨y, hyE, rfl⟩ hyS
    have hsup' := card_sup_ge_of_swap hK2 hE'N hE'2 hE'4 ⟨x, hxE, rfl⟩ hx'S hx'1
      ⟨y, hyE, rfl⟩ hyS
    have hcardmap : ∀ U : Subgroup V, Nat.card ↥(U.map e.toMonoidHom) = Nat.card U :=
      fun U => Subgroup.card_map_of_injective e.injective
    refine ⟨?_, x, hxE, y, hyE, hxH, hx1, hyH, ?_⟩
    · rw [fixV_map_congrHom, hcardmap] at hfix
      exact hfix
    · rw [← MonoidHom.map_zpowers, ← MonoidHom.map_zpowers, fixV_map_congrHom,
        fixV_map_congrHom, ← Subgroup.map_sup, hcardmap] at hsup'
      exact hsup'

end SL3One

end H

end CFSG.Quasithin

module

public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenN2Kernel
public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenN2D10Matrix

public noncomputable section
public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open

theorem hGaloisLinearEquiv_congr {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) {h : MulAut W}
    (hc₁ hc₂ : h * x = x * h) :
    hGaloisLinearEquiv hw2 x hx3 hfix h hc₁ =
      hGaloisLinearEquiv hw2 x hx3 hfix h hc₂ :=
  congrArg (fun hc => hGaloisLinearEquiv hw2 x hx3 hfix h hc)
    (Subsingleton.elim hc₁ hc₂)

theorem hGaloisLinearEquiv_apply_congr {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) {h : MulAut W}
    (hc₁ hc₂ : h * x = x * h) (v : Additive W) :
    hGaloisLinearEquiv hw2 x hx3 hfix h hc₁ v =
      hGaloisLinearEquiv hw2 x hx3 hfix h hc₂ v := by
  rw [hGaloisLinearEquiv_congr hw2 x hx3 hfix hc₁ hc₂]

theorem hGL_eq_scalar_of_smul {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16)
    {h : MulAut W} (hcomm : h * x = x * h) (c : GaloisField 2 2)
    (hc : letI := galoisModule hw2 x hx3 hfix;
      ∀ v : Additive W, hGaloisLinearEquiv hw2 x hx3 hfix h hcomm v = c • v)
    (hc0 : c ≠ 0) :
    hGL hw2 x hx3 hfix h hcomm hW =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c hc0) := by
  letI := galoisModule hw2 x hx3 hfix
  let b := galoisBasis hw2 x hx3 hfix hW
  have hcomm1 : (1 : MulAut W) * x = x * 1 := by group
  have hGL1 : hGL hw2 x hx3 hfix (1 : MulAut W) hcomm1 hW = 1 :=
    hGL_one hw2 x hx3 hfix hcomm1 hW
  have hbasis : ∀ j : Fin 2,
      galoisEquivFun hw2 x hx3 hfix hW (b j) = Pi.single j (1 : GaloisField 2 2) := by
    intro j
    have hcol1 := hGL_equivFun_basis hw2 x hx3 hfix hW
      (h := (1 : MulAut W)) hcomm1 j
    have hauto1 : autAddHom (1 : MulAut W) (b j) = b j := by
      have h := hGaloisLinearEquiv_apply hw2 x hx3 hfix
        (h := (1 : MulAut W)) hcomm1 (b j)
      rw [hGaloisLinearEquiv_one hw2 x hx3 hfix hcomm1] at h
      simpa using h.symm
    rw [← hauto1, hcol1, hGL1]
    ext i
    simp [Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply, Pi.single_apply, eq_comm]
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  have h1 : autAddHom h (b j) = c • b j := by
    rw [← hGaloisLinearEquiv_apply hw2 x hx3 hfix h hcomm (b j)]
    exact hc (b j)
  have h2 : galoisEquivFun hw2 x hx3 hfix hW (c • b j) =
      fun i => (hGL hw2 x hx3 hfix h hcomm hW) i j := by
    rw [← h1]
    exact hGL_equivFun_basis hw2 x hx3 hfix hW hcomm j
  have h3 : galoisEquivFun hw2 x hx3 hfix hW (c • b j) = Pi.single j c := by
    rw [map_smul, hbasis j]
    ext i
    by_cases hij : i = j <;>
      simp [Pi.smul_apply, Pi.single_apply, hij, smul_eq_mul]
  have hentry : (hGL hw2 x hx3 hfix h hcomm hW) i j = if i = j then c else 0 := by
    rw [← congrFun h2 i, h3]
    simp [Pi.single_apply]
  rw [hentry, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply]
  by_cases hij : i = j <;> simp [hij]

theorem hGL_pow {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16)
    {h : MulAut W} (hcomm : h * x = x * h) (n : ℕ) :
    hGL hw2 x hx3 hfix (h ^ n) ((Commute.pow_left hcomm n).eq) hW =
      (hGL hw2 x hx3 hfix h hcomm hW) ^ n := by
  induction n with
  | zero =>
      have hc1 : (1 : MulAut W) * x = x * 1 := by group
      calc hGL hw2 x hx3 hfix (h ^ 0) ((Commute.pow_left hcomm 0).eq) hW
          = hGL hw2 x hx3 hfix 1 hc1 hW :=
            hGL_congr hw2 x hx3 hfix hW _ hc1 (pow_zero h)
        _ = 1 := hGL_one hw2 x hx3 hfix hc1 hW
        _ = (hGL hw2 x hx3 hfix h hcomm hW) ^ 0 := by rw [pow_zero]
  | succ n ih =>
      have hc1 : (h ^ n) * x = x * (h ^ n) := (Commute.pow_left hcomm n).eq
      have hc : (h ^ n * h) * x = x * (h ^ n * h) :=
        ((Commute.pow_left hcomm n).mul_left hcomm).eq
      calc hGL hw2 x hx3 hfix (h ^ (n + 1))
            ((Commute.pow_left hcomm (n + 1)).eq) hW
          = hGL hw2 x hx3 hfix (h ^ n * h) hc hW :=
            hGL_congr hw2 x hx3 hfix hW _ hc (pow_succ h n)
        _ = hGL hw2 x hx3 hfix (h ^ n) hc1 hW *
              hGL hw2 x hx3 hfix h hcomm hW :=
            hGL_mul hw2 x hx3 hfix (h ^ n) h hc1 hcomm hc hW
        _ = (hGL hw2 x hx3 hfix h hcomm hW) ^ n *
              hGL hw2 x hx3 hfix h hcomm hW := by rw [ih]
        _ = (hGL hw2 x hx3 hfix h hcomm hW) ^ (n + 1) := by rw [pow_succ]

theorem hGL_eq_one_imp_eq_one {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16)
    {h : MulAut W} (hcomm : h * x = x * h)
    (h1 : hGL hw2 x hx3 hfix h hcomm hW = 1) : h = 1 := by
  letI := galoisModule hw2 x hx3 hfix
  let b := galoisBasis hw2 x hx3 hfix hW
  have hfixb : ∀ j : Fin 2,
      hGaloisLinearEquiv hw2 x hx3 hfix h hcomm (b j) = b j := by
    intro j
    rw [hGaloisLinearEquiv_apply hw2 x hx3 hfix h hcomm]
    rw [hGL_expansion hw2 x hx3 hfix hW hcomm j, h1]
    simp [b, Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply]
  have hL : hGaloisLinearEquiv hw2 x hx3 hfix h hcomm = 1 := by
    apply b.ext'
    intro j
    rw [hfixb j]
    rfl
  by_contra hne
  exact hGaloisLinearEquiv_ne_one hw2 x hx3 hfix hcomm hne hL

theorem eq_fifteen_of_dvd_fifteen {n : ℕ} (h : n ∣ 15) (h1 : n ≠ 1)
    (h3 : n ≠ 3) (h5 : n ≠ 5) : n = 15 := by
  have hpos : 0 < n := Nat.pos_of_dvd_of_pos h (by norm_num)
  have hle : n ≤ 15 := Nat.le_of_dvd (by norm_num) h
  interval_cases n <;> norm_num at *

theorem false_of_card_thirty_of_transitive {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16)
    {G X H : Subgroup (MulAut W)} {s : MulAut W}
    (hH : H = G ⊓ Subgroup.centralizer (X : Set (MulAut W)))
    (hxgen : X = Subgroup.zpowers x) (hXcard : Nat.card X = 3) (hXG : X ≤ G)
    (hXnorm : ∀ g ∈ G, ∀ y ∈ X, g * y * g⁻¹ ∈ X)
    (hsG : s ∈ G) (hs_ord2 : orderOf s = 2)
    (hs_not_cent : s ∉ Subgroup.centralizer (X : Set (MulAut W)))
    (hcommH : ∀ h ∈ H, h * x = x * h)
    (htrans : letI := galoisModule hw2 x hx3 hfix;
      ∀ L M : LineOf (K := GaloisField 2 2) (V := Additive W),
        ∃ h : ↥H, lineMap (HLinHom hw2 x hx3 hfix H hcommH h) L = M)
    (hcard : Nat.card H = 30) :
    False := by
  classical
  letI := galoisModule hw2 x hx3 hfix
  let C : Subgroup (MulAut W) := Subgroup.centralizer (X : Set (MulAut W))
  have hxX : x ∈ X := by
    rw [hxgen]
    exact Subgroup.mem_zpowers x
  have hx3ord : orderOf x = 3 := by
    rw [← Nat.card_zpowers, ← hxgen, hXcard]
  have hX_le : X ≤ G ⊓ C := le_inf_centralizer_self hXG hXcard
  have hxH : x ∈ H := by
    rw [hH]
    exact hX_le hxX
  have hx2H : x ^ 2 ∈ H := H.pow_mem hxH 2
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨rH, hrordH⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥H) 5 (by rw [hcard]; norm_num)
  let r : MulAut W := rH
  have hrH : r ∈ H := rH.2
  have hordr : orderOf r = 5 := by
    simpa [r] using (Subgroup.orderOf_coe rH).trans hrordH
  have hrcommx : Commute r x := hcommH r hrH
  let T : MulAut W := r * x
  have hTH : T ∈ H := H.mul_mem hrH hxH
  have hordT : orderOf T = 15 := by
    dsimp [T]
    rw [hrcommx.orderOf_mul_eq_mul_orderOf_of_coprime
      (by rw [hordr, hx3ord]; norm_num), hordr, hx3ord]
  have hT5 : T ^ 5 = x ^ 2 := by
    dsimp [T]
    rw [hrcommx.mul_pow]
    have hr5 : r ^ 5 = 1 := by
      rw [← hordr]
      exact pow_orderOf_eq_one r
    rw [hr5, one_mul, show (5 : ℕ) = 3 + 2 by norm_num, pow_add, hx3, one_mul]
  have hcommT : T * x = x * T := hcommH T hTH
  let T' : Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 2) :=
    hGL hw2 x hx3 hfix T hcommT hW
  have hx2X : x ^ 2 ∈ X := X.pow_mem hxX 2
  obtain ⟨c, hc⟩ :=
    X_scalar_of_transitive hw2 x hx3 hfix hW hH hxgen hcommH htrans (x ^ 2) hx2X
  have hcommX2 : (x ^ 2) * x = x * (x ^ 2) := by group
  have hcX2 : ∀ v : Additive W,
      hGaloisLinearEquiv hw2 x hx3 hfix (x ^ 2) hcommX2 v = c • v := by
    intro v
    exact (hGaloisLinearEquiv_apply_congr hw2 x hx3 hfix hcommX2 _ v).trans (hc v)
  haveI : Nontrivial W :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hW]; norm_num)
  obtain ⟨v0, hv0⟩ := exists_ne (0 : Additive W)
  have hc0 : c ≠ 0 := by
    intro hc0
    let L : Additive W ≃ₗ[GaloisField 2 2] Additive W :=
      hGaloisLinearEquiv hw2 x hx3 hfix (x ^ 2) hcommX2
    have hLv : L v0 = 0 := by
      have h := (hGaloisLinearEquiv_apply_congr hw2 x hx3 hfix hcommX2 _ v0).trans (hc v0)
      dsimp [L]
      rw [hc0, zero_smul] at h
      exact h
    exact hv0 (L.injective (hLv.trans (map_zero L).symm))
  have hGL_x2_scalar : hGL hw2 x hx3 hfix (x ^ 2) hcommX2 hW =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c hc0) :=
    hGL_eq_scalar_of_smul hw2 x hx3 hfix hW hcommX2 c hcX2 hc0
  have hT'5_scalar : T' ^ 5 =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c hc0) := by
    rw [← hGL_pow hw2 x hx3 hfix hW hcommT 5]
    rw [show hGL hw2 x hx3 hfix (T ^ 5) ((Commute.pow_left hcommT 5).eq) hW =
          hGL hw2 x hx3 hfix (x ^ 2) hcommX2 hW from
        hGL_congr hw2 x hx3 hfix hW _ hcommX2 hT5]
    exact hGL_x2_scalar
  have hT'15 : T' ^ 15 = 1 := by
    rw [← hGL_pow hw2 x hx3 hfix hW hcommT 15]
    rw [show hGL hw2 x hx3 hfix (T ^ 15) ((Commute.pow_left hcommT 15).eq) hW =
          hGL hw2 x hx3 hfix 1 (by group) hW from
        hGL_congr hw2 x hx3 hfix hW _ (by group)
          (by rw [← hordT]; exact pow_orderOf_eq_one T)]
    exact hGL_one hw2 x hx3 hfix (by group) hW
  have hT'3_ne : T' ^ 3 ≠ 1 := by
    intro h3
    have hGLT3 : hGL hw2 x hx3 hfix (T ^ 3) ((Commute.pow_left hcommT 3).eq) hW = 1 := by
      rw [hGL_pow hw2 x hx3 hfix hW hcommT 3]
      exact h3
    have hT3 : T ^ 3 = 1 :=
      hGL_eq_one_imp_eq_one hw2 x hx3 hfix hW ((Commute.pow_left hcommT 3).eq) hGLT3
    have hdvd : orderOf T ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hT3
    rw [hordT] at hdvd
    norm_num at hdvd
  have hT'5_ne : T' ^ 5 ≠ 1 := by
    intro h5
    have hGLT5 : hGL hw2 x hx3 hfix (T ^ 5) ((Commute.pow_left hcommT 5).eq) hW = 1 := by
      rw [hGL_pow hw2 x hx3 hfix hW hcommT 5]
      exact h5
    have hT5one : T ^ 5 = 1 :=
      hGL_eq_one_imp_eq_one hw2 x hx3 hfix hW ((Commute.pow_left hcommT 5).eq) hGLT5
    have hdvd : orderOf T ∣ 5 := orderOf_dvd_iff_pow_eq_one.mpr hT5one
    rw [hordT] at hdvd
    norm_num at hdvd
  have hT'ne1 : T' ≠ 1 := by
    intro h1
    exact hT'3_ne (by rw [h1, one_pow])
  have hordT' : orderOf T' = 15 :=
    eq_fifteen_of_dvd_fifteen (orderOf_dvd_iff_pow_eq_one.mpr hT'15)
      (by intro hn; exact hT'ne1 (orderOf_eq_one_iff.mp hn))
      (by intro hn; exact hT'3_ne (by rw [← hn]; exact pow_orderOf_eq_one T'))
      (by intro hn; exact hT'5_ne (by rw [← hn]; exact pow_orderOf_eq_one T'))
  have hs2 : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [hs_ord2] at h
    simpa [pow_two] using h
  have hsx_mem : s * x * s⁻¹ ∈ X := hXnorm s hsG x hxX
  have hsx_ne : s * x * s⁻¹ ≠ x := by
    intro h
    exact hs_not_cent (mem_centralizer_of_conj_eq_self hxgen h)
  have hsx : s * x * s⁻¹ = x ^ 2 :=
    conj_eq_sq_of_zpowers_three_of_mem hxgen hx3ord hsx_mem hsx_ne
  let Tconj : MulAut W := s * T * s⁻¹
  have hTH_inf : T ∈ G ⊓ C := hH ▸ hTH
  have hTconj_inf : Tconj ∈ G ⊓ C := by
    dsimp [Tconj]
    exact conj_mem_centralizer_of_normal_in_G hXnorm hsG (G.inv_mem hsG)
      (Subgroup.mem_inf.mp hTH_inf).1 (Subgroup.mem_inf.mp hTH_inf).2
  have hTconjH : Tconj ∈ H := by
    rw [hH]
    exact hTconj_inf
  have hordTconj : orderOf Tconj = 15 := by
    have hsem : SemiconjBy s T Tconj := by
      dsimp [Tconj, SemiconjBy]
      group
    have h := SemiconjBy.orderOf_eq s hsem
    rw [hordT] at h
    exact h.symm
  let K : Subgroup (MulAut W) := Subgroup.zpowers T
  have hKcard : Nat.card K = 15 := by
    dsimp [K]
    rw [Nat.card_zpowers, hordT]
  have hKleH : K ≤ H := by
    intro y hy
    dsimp [K] at hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← hk]
    exact H.zpow_mem hTH k
  have hKinf : K ⊓ H = K := inf_eq_left.mpr hKleH
  have hrel : K.relIndex H = 2 := by
    have h := Subgroup.relIndex_mul_card (H := K) (K := H)
    rw [hKinf, hKcard, hcard] at h
    omega
  have hIdx : (K.subgroupOf H).index = 2 := by
    simpa [Subgroup.relIndex] using hrel
  have hTconj2K : Tconj ^ 2 ∈ K := by
    have h := Subgroup.sq_mem_of_index_two hIdx ⟨Tconj, hTconjH⟩
    change Tconj ^ 2 ∈ K at h
    exact h
  have hTconj_eq : (Tconj ^ 2) ^ 8 = Tconj := by
    have h16 : Tconj ^ 16 = Tconj := by
      rw [show (16 : ℕ) = 15 + 1 by norm_num, pow_add,
        show Tconj ^ 15 = 1 by rw [← hordTconj]; exact pow_orderOf_eq_one Tconj,
        one_mul, pow_one]
    calc (Tconj ^ 2) ^ 8 = Tconj ^ (2 * 8) := by rw [pow_mul]
      _ = Tconj ^ 16 := by norm_num
      _ = Tconj := h16
  have hTconjK : Tconj ∈ K := by
    rw [← hTconj_eq]
    exact K.pow_mem hTconj2K 8
  have hmem : Tconj ∈ (Finset.range (orderOf T)).image (fun k => T ^ k) :=
    (mem_zpowers_iff_mem_range_orderOf (x := T) (y := Tconj)).mp
      (by simpa [K] using hTconjK)
  rw [Finset.mem_image] at hmem
  obtain ⟨a, -, ha⟩ := hmem
  have hTconj_GL : hGL hw2 x hx3 hfix Tconj
      (conj_commutes_x hs2 hx3 hsx hcommT) hW = T' ^ a := by
    rw [hGL_congr hw2 x hx3 hfix hW
      (conj_commutes_x hs2 hx3 hsx hcommT)
      ((Commute.pow_left hcommT a).eq) ha.symm]
    exact hGL_pow hw2 x hx3 hfix hW hcommT a
  have hphi : twist (sUnit hw2 x hx3 hfix hW hs2 hsx) T' = T' ^ a := by
    rw [← hGL_conj hw2 x hx3 hfix hW hs2 hsx hcommT]
    exact hTconj_GL
  exact no_twist_involution_on_order15_cyclic
    (sUnit hw2 x hx3 hfix hW hs2 hsx) T' a (Units.mk0 c hc0)
    hordT' hT'5_scalar (sUnit_mul_frob hw2 x hx3 hfix hW hs2 hsx) hphi

end CFSG.LocalAnalysis.WeakClosure81

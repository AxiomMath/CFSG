module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemL43Groups
public import CFSG.RankThree.Asc83Table.E9
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434RemL43

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem coe_inv_mul_mul (k x : SL4) :
    ((k⁻¹ * x * k : SL4) : Mat4) = ((k⁻¹ : SL4) : Mat4) * (x : Mat4) * (k : Mat4) :=
  rfl

theorem coe_mul_mul_inv (k x : SL4) :
    ((k * x * k⁻¹ : SL4) : Mat4) = (k : Mat4) * (x : Mat4) * ((k⁻¹ : SL4) : Mat4) :=
  rfl

theorem coe_mul' (x y : SL4) : ((x * y : SL4) : Mat4) = (x : Mat4) * (y : Mat4) :=
  rfl

theorem eq_uMat_of_mem {x : SL4} (hx : x ∈ unitriangular 4 (ZMod 3)) (h01 : (x : Mat4) 0 1 = 1)
    (h23 : (x : Mat4) 2 3 = 0) :
    (x : Mat4) = uMat ((x : Mat4) 0 2) ((x : Mat4) 0 3) ((x : Mat4) 1 2) ((x : Mat4) 1 3) := by
  obtain ⟨hlow, hdiag⟩ := mem_unitriangular.mp hx
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat, h01, h23, hdiag, hlow]

theorem eq_vMat_of_mem {x : SL4} (hx : x ∈ unitriangular 4 (ZMod 3)) (h01 : (x : Mat4) 0 1 = 0)
    (h23 : (x : Mat4) 2 3 = 1) :
    (x : Mat4) = vMat ((x : Mat4) 0 2) ((x : Mat4) 0 3) ((x : Mat4) 1 2) ((x : Mat4) 1 3) := by
  obtain ⟨hlow, hdiag⟩ := mem_unitriangular.mp hx
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vMat, h01, h23, hdiag, hlow]

theorem isR_of_mem {x : SL4} (hx : x ∈ unitriangular 4 (ZMod 3)) (h01 : (x : Mat4) 0 1 = 0)
    (h23 : (x : Mat4) 2 3 = 0) : IsR (x : Mat4) := by
  obtain ⟨hlow, hdiag⟩ := mem_unitriangular.mp hx
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rMat, h01, h23, hdiag, hlow]

theorem rGrp_le_unitriangular : rGrp ≤ unitriangular 4 (ZMod 3) := by
  intro x hx
  have h := mem_rGrp_iff.mp hx
  refine mem_unitriangular.mpr ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [h]
    fin_cases i <;> fin_cases j <;> simp_all [rMat]
  · rw [h]
    fin_cases i <;> simp [rMat]

theorem pZeroGrp_le_unitriangular : pZeroGrp ≤ unitriangular 4 (ZMod 3) := by
  intro x hx
  have h := mem_pZeroGrp_iff.mp hx
  refine mem_unitriangular.mpr ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [h]
    fin_cases i <;> fin_cases j <;> simp_all [p0Mat]
  · rw [h]
    fin_cases i <;> simp [p0Mat]

theorem entries_mul_of_mem {x y : SL4} (hx : x ∈ unitriangular 4 (ZMod 3))
    (hy : y ∈ unitriangular 4 (ZMod 3)) :
    ((x * y : SL4) : Mat4) 0 1 = (x : Mat4) 0 1 + (y : Mat4) 0 1 ∧
      ((x * y : SL4) : Mat4) 2 3 = (x : Mat4) 2 3 + (y : Mat4) 2 3 := by
  obtain ⟨hxl, hxd⟩ := mem_unitriangular.mp hx
  obtain ⟨hyl, hyd⟩ := mem_unitriangular.mp hy
  rw [coe_mul']
  simp only [Matrix.mul_apply, Fin.sum_univ_four]
  refine ⟨?_, ?_⟩
  · rw [hxd 0, hyd 1, hyl 2 1 (by decide), hyl 3 1 (by decide)]
    ring
  · rw [hxl 2 0 (by decide), hxl 2 1 (by decide), hxd 2, hyd 3]
    ring

@[expose] noncomputable def rhoU :
    unitriangular 4 (ZMod 3) →* Multiplicative (ZMod 3 × ZMod 3) where
  toFun g := Multiplicative.ofAdd (((g : SL4) : Mat4) 0 1, ((g : SL4) : Mat4) 2 3)
  map_one' := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_ofAdd, toAdd_one, OneMemClass.coe_one]
    rfl
  map_mul' g h := by
    apply Multiplicative.toAdd.injective
    obtain ⟨e1, e2⟩ := entries_mul_of_mem g.2 h.2
    simp only [toAdd_ofAdd, toAdd_mul, Subgroup.coe_mul, Prod.mk_add_mk]
    rw [e1, e2]

theorem rhoU_eq_one_iff (g : unitriangular 4 (ZMod 3)) : rhoU g = 1 ↔ (g : SL4) ∈ rGrp := by
  rw [mem_rGrp_iff]
  constructor
  · intro h
    have h' := congrArg Multiplicative.toAdd h
    simp only [rhoU, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, toAdd_one, Prod.mk_eq_zero]
      at h'
    exact isR_of_mem g.2 h'.1 h'.2
  · intro h
    apply Multiplicative.toAdd.injective
    simp only [rhoU, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, toAdd_one]
    rw [h]
    simp [rMat]

@[expose] noncomputable def rhoP {P : Subgroup SL4} (hPU : P ≤ unitriangular 4 (ZMod 3)) :
    P →* Multiplicative (ZMod 3 × ZMod 3) :=
  rhoU.comp (Subgroup.inclusion hPU)

theorem rhoP_apply {P : Subgroup SL4} (hPU : P ≤ unitriangular 4 (ZMod 3)) (x : P) :
    rhoP hPU x = Multiplicative.ofAdd ((((x : SL4)) : Mat4) 0 1, ((x : SL4) : Mat4) 2 3) :=
  rfl

theorem card_ker_rhoP {P : Subgroup SL4} (hPU : P ≤ unitriangular 4 (ZMod 3)) :
    Nat.card (rhoP hPU).ker = Nat.card (P ⊓ rGrp : Subgroup SL4) := by
  have hmap : (rhoP hPU).ker.map P.subtype = P ⊓ rGrp := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      exact (rhoU_eq_one_iff (Subgroup.inclusion hPU y)).mp hy
    · rintro ⟨hxP, hxR⟩
      exact ⟨⟨x, hxP⟩, (rhoU_eq_one_iff (Subgroup.inclusion hPU ⟨x, hxP⟩)).mpr hxR, rfl⟩
  rw [← hmap, Subgroup.card_map_of_injective P.subtype_injective]

theorem card_eq_mul_rhoP {P : Subgroup SL4} (hPU : P ≤ unitriangular 4 (ZMod 3)) :
    Nat.card P = Nat.card (P ⊓ rGrp : Subgroup SL4) * Nat.card (rhoP hPU).range := by
  rw [← card_ker_rhoP hPU, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv,
    mul_comm]
  exact (rhoP hPU).ker.card_eq_card_quotient_mul_card_subgroup

theorem eq_of_mem_zpowers_three {G : Type*} [Group G] {x y : G} (hx : x ^ 3 = 1)
    (hy : y ∈ Subgroup.zpowers x) : y = 1 ∨ y = x ∨ y = x ^ 2 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hk : x ^ k = x ^ (k % 3) := by
    have e : k = 3 * (k / 3) + k % 3 := (Int.mul_ediv_add_emod k 3).symm
    conv_lhs => rw [e]
    rw [_root_.zpow_add, _root_.zpow_mul, show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl,
      _root_.zpow_natCast, hx, _root_.one_zpow, one_mul]
  rw [hk]
  have h0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  have h3 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
  interval_cases (k % 3)
  · left; exact _root_.zpow_zero x
  · right; left; exact _root_.zpow_one x
  · right; right; exact _root_.zpow_natCast x 2

theorem card_closure_pair {x z : SL4} (hx : x ^ 3 = 1) (hz : z ^ 3 = 1) (hxz : x * z = z * x)
    {p q : Fin 4} (hpq : p ≠ q) (hxpq : (x : Mat4) p q = 1) (hzpq : (z : Mat4) p q = 0)
    (hx2 : ((x ^ 2 : SL4) : Mat4) p q = 2) (hz1 : z ≠ 1) :
    Nat.card (Subgroup.closure ({x, z} : Set SL4)) = 9 := by
  refine CFSG.RankThree.Asc83Table.card_closure_pair_eq_nine hx hz hxz ?_ ?_
  · intro h1
    rw [h1] at hxpq
    have h0 : ((1 : SL4) : Mat4) p q = 0 := Matrix.one_apply_ne hpq
    rw [h0] at hxpq
    exact absurd hxpq (by decide)
  · intro hmem
    rcases eq_of_mem_zpowers_three hx hmem with h | h | h
    · exact hz1 h
    · rw [h, hxpq] at hzpq
      exact absurd hzpq (by decide)
    · rw [h, hx2] at hzpq
      exact absurd hzpq (by decide)

@[expose] def zSL : SL4 := ⟨zMat, det_rMat 0 1 0 0⟩

theorem zSL_mem_rGrp : zSL ∈ rGrp := mem_rGrp_iff.mpr (by decide)

theorem zSL_pow_three : zSL ^ 3 = 1 := isElemAbelian_rGrp.2 _ zSL_mem_rGrp

theorem zSL_ne_one : zSL ≠ 1 := by
  intro h
  have h' := congrArg (fun x : SL4 => (x : Mat4) 0 3) h
  revert h'
  decide

theorem eq_rMat_of_comm {w u v : SL4} (hw : w ∈ rGrp) {a b d a' b' d' : ZMod 3}
    (hu : (u : Mat4) = uMat a b 0 d) (hv : (v : Mat4) = vMat a' b' 0 d') (hwu : w * u = u * w)
    (hwv : w * v = v * w) : (w : Mat4) = rMat 0 ((w : Mat4) 0 3) 0 0 := by
  have hwR := mem_rGrp_iff.mp hw
  have e1 : rMat ((w : Mat4) 0 2) ((w : Mat4) 0 3) ((w : Mat4) 1 2) ((w : Mat4) 1 3) *
      uMat a b 0 d = uMat a b 0 d *
        rMat ((w : Mat4) 0 2) ((w : Mat4) 0 3) ((w : Mat4) 1 2) ((w : Mat4) 1 3) := by
    rw [← hwR, ← hu]
    exact congrArg (fun x : SL4 => (x : Mat4)) hwu
  have e2 : rMat ((w : Mat4) 0 2) ((w : Mat4) 0 3) ((w : Mat4) 1 2) ((w : Mat4) 1 3) *
      vMat a' b' 0 d' = vMat a' b' 0 d' *
        rMat ((w : Mat4) 0 2) ((w : Mat4) 0 3) ((w : Mat4) 1 2) ((w : Mat4) 1 3) := by
    rw [← hwR, ← hv]
    exact congrArg (fun x : SL4 => (x : Mat4)) hwv
  obtain ⟨h12, h13⟩ := eq_of_rMat_comm_uMat e1
  have h02 := eq_of_rMat_comm_vMat e2
  rw [hwR, h02, h12, h13]
  simp [rMat]

theorem zSL_mem_zpowers {w : SL4} (hw : (w : Mat4) = rMat 0 ((w : Mat4) 0 3) 0 0) (hw1 : w ≠ 1) :
    zSL ∈ Subgroup.zpowers w := by
  have hβ : (w : Mat4) 0 3 = 1 ∨ (w : Mat4) 0 3 = 2 := by
    have hne : (w : Mat4) 0 3 ≠ 0 := by
      intro h0
      apply hw1
      apply Subtype.ext
      rw [hw, h0]
      decide
    generalize (w : Mat4) 0 3 = β at hne ⊢
    revert β
    decide
  rcases hβ with h | h
  · have : w = zSL := Subtype.ext (by rw [hw, h]; rfl)
    rw [this]
    exact Subgroup.mem_zpowers _
  · have : w ^ 2 = zSL := Subtype.ext (by
      change (w : Mat4) ^ 2 = zMat
      rw [hw, h, sq, rMat_mul]
      decide)
    rw [← this]
    exact Subgroup.npow_mem_zpowers _ 2

theorem classify {P : Subgroup SL4} (hPU : P ≤ unitriangular 4 (ZMod 3))
    (hPe : CFSG.Assembly.IsElemAbelian 3 P) (hP27 : Nat.card P = 27) :
    (∃ k : SL4, ∃ B : Subgroup SL4, B ≤ P ∧ 9 ≤ Nat.card B ∧ ∀ b ∈ B, k⁻¹ * b * k ∈ rGrp) ∨
      ∃ k : SL4, P.map (MulAut.conj k).toMonoidHom = pZeroGrp := by
  have hPc : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hPe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  set I := P ⊓ rGrp with hI
  have hIdvd : Nat.card I ∣ 27 := hP27 ▸ Subgroup.card_dvd_of_le inf_le_left
  by_cases h9 : 9 ≤ Nat.card I
  · refine Or.inl ⟨1, I, inf_le_left, h9, fun b hb => ?_⟩
    rw [inv_one, one_mul, mul_one]
    exact hb.2
  have hI3 : Nat.card I ≤ 3 := by
    have hpos : 0 < Nat.card I := Nat.card_pos
    have : Nat.card I = 1 ∨ Nat.card I = 3 ∨ Nat.card I = 9 ∨ Nat.card I = 27 := by
      have h := (Nat.dvd_prime_pow (p := 3) Nat.prime_three).mp (show Nat.card I ∣ 3 ^ 3 from hIdvd)
      obtain ⟨m, hm, hm'⟩ := h
      interval_cases m <;> simp_all
    omega
  have hcard : 27 = Nat.card I * Nat.card (rhoP hPU).range := by
    rw [hI, ← hP27]
    exact card_eq_mul_rhoP hPU
  have hrange : (rhoP hPU).range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    have hcod : Nat.card (Multiplicative (ZMod 3 × ZMod 3)) = 9 := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_zmod]
    have hle : Nat.card (rhoP hPU).range ≤ 9 :=
      hcod ▸ Subgroup.card_le_card_group _
    have hpos : 0 < Nat.card (rhoP hPU).range := Nat.card_pos
    rw [hcod]
    by_contra hne
    have hlt : Nat.card (rhoP hPU).range ≤ 8 := by omega
    have : Nat.card I * Nat.card (rhoP hPU).range ≤ 3 * 8 := Nat.mul_le_mul hI3 hlt
    omega
  have hI3' : Nat.card I = 3 := by
    have hcod : Nat.card (rhoP hPU).range = 9 := by
      rw [hrange, Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, Nat.card_prod,
        Nat.card_zmod]
    rw [hcod] at hcard
    omega
  obtain ⟨u, hu⟩ : ∃ u : P, rhoP hPU u = Multiplicative.ofAdd (1, 0) := by
    have : Multiplicative.ofAdd ((1 : ZMod 3), (0 : ZMod 3)) ∈ (rhoP hPU).range := by
      rw [hrange]; exact Subgroup.mem_top _
    exact this
  obtain ⟨v, hv⟩ : ∃ v : P, rhoP hPU v = Multiplicative.ofAdd (0, 1) := by
    have : Multiplicative.ofAdd ((0 : ZMod 3), (1 : ZMod 3)) ∈ (rhoP hPU).range := by
      rw [hrange]; exact Subgroup.mem_top _
    exact this
  rw [rhoP_apply] at hu hv
  have hu' := congrArg Multiplicative.toAdd hu
  have hv' := congrArg Multiplicative.toAdd hv
  simp only [toAdd_ofAdd, Prod.mk.injEq] at hu' hv'
  have huU : (u : SL4) ∈ unitriangular 4 (ZMod 3) := hPU u.2
  have hvU : (v : SL4) ∈ unitriangular 4 (ZMod 3) := hPU v.2
  set a := ((u : SL4) : Mat4) 0 2 with ha
  set b := ((u : SL4) : Mat4) 0 3 with hb
  set c := ((u : SL4) : Mat4) 1 2 with hc
  set d := ((u : SL4) : Mat4) 1 3 with hd
  set a' := ((v : SL4) : Mat4) 0 2 with ha'
  set b' := ((v : SL4) : Mat4) 0 3 with hb'
  set c' := ((v : SL4) : Mat4) 1 2 with hc'
  set d' := ((v : SL4) : Mat4) 1 3 with hd'
  have huM : ((u : SL4) : Mat4) = uMat a b c d := eq_uMat_of_mem huU hu'.1 hu'.2
  have hvM : ((v : SL4) : Mat4) = vMat a' b' c' d' := eq_vMat_of_mem hvU hv'.1 hv'.2
  have huv : uMat a b c d * vMat a' b' c' d' = vMat a' b' c' d' * uMat a b c d := by
    rw [← huM, ← hvM]
    exact congrArg (fun x : SL4 => (x : Mat4)) (hPc _ u.2 _ v.2)
  obtain ⟨hc0, hc'0, hd'a⟩ := eq_of_uMat_mul_vMat_comm huv
  rw [hc0] at huM
  rw [hc'0, hd'a] at hvM
  obtain ⟨w, hwI, hw1⟩ : ∃ w ∈ I, w ≠ 1 := by
    by_contra hall
    push Not at hall
    have : I = ⊥ := eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (hall x hx)
    rw [this, Subgroup.card_bot] at hI3'
    omega
  have hwshape := eq_rMat_of_comm hwI.2 huM hvM (hPc _ hwI.1 _ u.2) (hPc _ hwI.1 _ v.2)
  have hzI : zSL ∈ I := (Subgroup.zpowers_le.mpr hwI) (zSL_mem_zpowers hwshape hw1)
  have hzP : zSL ∈ P := hzI.1
  have hIz : I = Subgroup.zpowers zSL := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzI) ?_
    rw [hI3', Nat.card_zpowers, orderOf_eq_prime zSL_pow_three zSL_ne_one]
  have hu3 : (u : SL4) ^ 3 = 1 := hPe.2 _ u.2
  have hv3 : (v : SL4) ^ 3 = 1 := hPe.2 _ v.2
  have hcases : d = 0 ∨ a' = 0 ∨ d + a' = 0 ∨ (d ≠ 0 ∧ a' = d) := by
    generalize d = x
    generalize a' = y
    revert x y
    decide
  rcases hcases with hd0 | ha'0 | hda | ⟨hdne, ha'd⟩
  ·
    refine Or.inl ⟨hOneSL a, Subgroup.closure {(u : SL4), zSL}, ?_, ?_, ?_⟩
    · rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact u.2
      · exact hzP
    · refine (card_closure_pair hu3 zSL_pow_three (hPc _ u.2 _ hzP) (p := 0) (q := 1) (by decide)
        ?_ ?_ ?_
        zSL_ne_one).ge
      · rw [huM]; rfl
      · decide
      · change (((u : SL4) : Mat4) ^ 2) 0 1 = 2
        rw [huM, sq]
        simp [uMat, Matrix.mul_apply, Fin.sum_univ_four]
        decide
    · intro x hx
      have hle : Subgroup.closure {(u : SL4), zSL} ≤
          rGrp.comap (MulAut.conj (hOneSL a)⁻¹).toMonoidHom := by
        rw [Subgroup.closure_le]
        rintro y (rfl | rfl)
        · change (hOneSL a)⁻¹ * (u : SL4) * (hOneSL a)⁻¹⁻¹ ∈ rGrp
          rw [inv_inv, mem_rGrp_iff, coe_inv_mul_mul, val_hOneSL_inv, huM, hd0]
          exact (k2a_check a b).1
        · change (hOneSL a)⁻¹ * zSL * (hOneSL a)⁻¹⁻¹ ∈ rGrp
          rw [inv_inv, mem_rGrp_iff, coe_inv_mul_mul, val_hOneSL_inv]
          exact (k2a_check a b).2
      have h1 := hle hx
      change (hOneSL a)⁻¹ * x * (hOneSL a)⁻¹⁻¹ ∈ rGrp at h1
      rwa [inv_inv] at h1
  ·
    refine Or.inl ⟨hOneSL a, Subgroup.closure {(v : SL4), zSL}, ?_, ?_, ?_⟩
    · rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact v.2
      · exact hzP
    · refine (card_closure_pair hv3 zSL_pow_three (hPc _ v.2 _ hzP) (p := 2) (q := 3) (by decide)
        ?_ ?_ ?_
        zSL_ne_one).ge
      · rw [hvM]; rfl
      · decide
      · change (((v : SL4) : Mat4) ^ 2) 2 3 = 2
        rw [hvM, sq]
        simp [vMat, Matrix.mul_apply, Fin.sum_univ_four]
        decide
    · intro x hx
      have hle : Subgroup.closure {(v : SL4), zSL} ≤
          rGrp.comap (MulAut.conj (hOneSL a)⁻¹).toMonoidHom := by
        rw [Subgroup.closure_le]
        rintro y (rfl | rfl)
        · change (hOneSL a)⁻¹ * (v : SL4) * (hOneSL a)⁻¹⁻¹ ∈ rGrp
          rw [inv_inv, mem_rGrp_iff, coe_inv_mul_mul, val_hOneSL_inv, hvM, ha'0]
          exact k2b_check a b'
        · change (hOneSL a)⁻¹ * zSL * (hOneSL a)⁻¹⁻¹ ∈ rGrp
          rw [inv_inv, mem_rGrp_iff, coe_inv_mul_mul, val_hOneSL_inv]
          exact (k2a_check a b).2
      have h1 := hle hx
      change (hOneSL a)⁻¹ * x * (hOneSL a)⁻¹⁻¹ ∈ rGrp at h1
      rwa [inv_inv] at h1
  ·
    have ha'eq : a' = -d := eq_neg_of_add_eq_zero_right hda
    have huvP : (u : SL4) * v ∈ P := P.mul_mem u.2 v.2
    have huv3 : ((u : SL4) * v) ^ 3 = 1 := hPe.2 _ huvP
    have huvM : (((u : SL4) * v : SL4) : Mat4) = uMat a b 0 d * vMat (-d) b' 0 (-a) := by
      rw [coe_mul', huM, hvM, ha'eq]
      exact rfl
    refine Or.inl ⟨hOneSL (a - d), Subgroup.closure {(u : SL4) * v, zSL}, ?_, ?_, ?_⟩
    · rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact huvP
      · exact hzP
    · refine (card_closure_pair huv3 zSL_pow_three (hPc _ huvP _ hzP) (p := 0) (q := 1)
        (by decide) ?_ ?_
        ?_
        zSL_ne_one).ge
      · rw [huvM]
        simp [uMat, vMat, Matrix.mul_apply, Fin.sum_univ_four]
      · decide
      · change ((((u : SL4) * v : SL4) : Mat4) ^ 2) 0 1 = 2
        rw [huvM, sq]
        simp [uMat, vMat, Matrix.mul_apply, Fin.sum_univ_four]
        decide
    · intro x hx
      have hle : Subgroup.closure {(u : SL4) * v, zSL} ≤
          rGrp.comap (MulAut.conj (hOneSL (a - d))⁻¹).toMonoidHom := by
        rw [Subgroup.closure_le]
        rintro y (rfl | rfl)
        · change (hOneSL (a - d))⁻¹ * ((u : SL4) * v) * (hOneSL (a - d))⁻¹⁻¹ ∈ rGrp
          rw [inv_inv, mem_rGrp_iff, coe_inv_mul_mul, val_hOneSL_inv, huvM]
          exact k2c_check a b d b'
        · change (hOneSL (a - d))⁻¹ * zSL * (hOneSL (a - d))⁻¹⁻¹ ∈ rGrp
          rw [inv_inv, mem_rGrp_iff, coe_inv_mul_mul, val_hOneSL_inv]
          exact (k2a_check (a - d) b).2
      have h1 := hle hx
      change (hOneSL (a - d))⁻¹ * x * (hOneSL (a - d))⁻¹⁻¹ ∈ rGrp at h1
      rwa [inv_inv] at h1
  ·
    rw [ha'd] at hvM
    obtain ⟨k, hk⟩ : ∃ k : SL4, k = hThreeSL a d hdne := ⟨_, rfl⟩
    have hconj : ∀ y : SL4, IsP0 (hThree a d * (y : Mat4) * hThreeInv a d) →
        MulAut.conj k y ∈ pZeroGrp := by
      intro y hy
      change k * y * k⁻¹ ∈ pZeroGrp
      rw [mem_pZeroGrp_iff, coe_mul_mul_inv, hk, val_hThreeSL_inv]
      exact hy
    have hku : MulAut.conj k (u : SL4) ∈ pZeroGrp := hconj _ (by
      rw [huM]; exact (ns_check a b b' d hdne).1)
    have hkv : MulAut.conj k (v : SL4) ∈ pZeroGrp := hconj _ (by
      rw [hvM]; exact (ns_check a b b' d hdne).2.1)
    have hkz : MulAut.conj k zSL ∈ pZeroGrp := hconj _ (ns_check a b b' d hdne).2.2
    refine Or.inr ⟨k, ?_⟩
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨i, hi⟩ : ∃ i : ZMod 3, i = (x : Mat4) 0 1 := ⟨_, rfl⟩
      obtain ⟨j, hj⟩ : ∃ j : ZMod 3, j = (x : Mat4) 2 3 := ⟨_, rfl⟩
      obtain ⟨y, hy⟩ : ∃ y : SL4, y = x * ((u : SL4) ^ i.val * (v : SL4) ^ j.val)⁻¹ := ⟨_, rfl⟩
      have hyP : y ∈ P := hy ▸ P.mul_mem hx (P.inv_mem (P.mul_mem (P.pow_mem u.2 _)
        (P.pow_mem v.2 _)))
      have hrho : rhoP hPU ⟨y, hyP⟩ = 1 := by
        have e : (⟨y, hyP⟩ : P) = ⟨x, hx⟩ * (u ^ i.val * v ^ j.val)⁻¹ := Subtype.ext hy
        rw [e, map_mul, map_inv, map_mul, map_pow, map_pow, rhoP_apply, rhoP_apply, rhoP_apply,
          hu'.1, hu'.2, hv'.1, hv'.2]
        apply Multiplicative.toAdd.injective
        simp only [toAdd_mul, toAdd_inv, toAdd_pow, toAdd_ofAdd, toAdd_one, Prod.smul_mk,
          Prod.mk_add_mk, Prod.neg_mk, nsmul_eq_mul, mul_one, mul_zero, add_zero, zero_add,
          ZMod.natCast_val, ZMod.cast_id', id_eq]
        simp only [← hi, ← hj, Prod.mk_eq_zero]
        exact ⟨add_neg_cancel i, add_neg_cancel j⟩
      have hyR : y ∈ rGrp := (rhoU_eq_one_iff (Subgroup.inclusion hPU ⟨y, hyP⟩)).mp hrho
      have hyz : y ∈ Subgroup.zpowers zSL := hIz ▸ ⟨hyP, hyR⟩
      have hxeq : x = y * ((u : SL4) ^ i.val * (v : SL4) ^ j.val) := by rw [hy]; group
      rw [hxeq, map_mul, map_mul, map_pow, map_pow]
      refine pZeroGrp.mul_mem ?_ (pZeroGrp.mul_mem (pZeroGrp.pow_mem hku _)
        (pZeroGrp.pow_mem hkv _))
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hyz
      rw [← hm, map_zpow]
      exact pZeroGrp.zpow_mem hkz _
    · have h1 : Nat.card (P.map (MulAut.conj k).toMonoidHom) = Nat.card P :=
        Subgroup.card_map_of_injective (MulAut.conj k).injective
      rw [h1, hP27, card_pZeroGrp]

end CFSG.RankThree.PartTwo.Sec4.Item434RemL43

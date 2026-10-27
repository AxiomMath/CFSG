module

public import CFSG.RankThree.PartTwo.Sec6.Item611Res4ProofE81Tools
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemL43

public section

namespace CFSG.RankThree.PartTwo.Sec6.Res611Res4

open CFSG.RankThree.PartTwo.Sec4.Item434RemL43 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

theorem comm_rMat_entries {T : Mat4} (hlow : ∀ i j : Fin 4, j < i → T i j = 0)
    (hdiag : ∀ i, T i i = 1) {a b c d : ZMod 3} (h : rMat a b c d * T = T * rMat a b c d) :
    c * T 0 1 = 0 ∧ c * T 2 3 = 0 ∧ T 0 1 * d = T 2 3 * a := by
  have h10 := hlow 1 0 (by decide)
  have h20 := hlow 2 0 (by decide)
  have h21 := hlow 2 1 (by decide)
  have h30 := hlow 3 0 (by decide)
  have h31 := hlow 3 1 (by decide)
  have h32 := hlow 3 2 (by decide)
  have d0 := hdiag 0
  have d1 := hdiag 1
  have d2 := hdiag 2
  have d3 := hdiag 3
  have l02 : (rMat a b c d * T) 0 2 = T 0 2 + a * T 2 2 + b * T 3 2 := by
    simp [Matrix.mul_apply, Fin.sum_univ_four, rMat]
  have r02 : (T * rMat a b c d) 0 2 = T 0 0 * a + T 0 1 * c + T 0 2 := by
    simp [Matrix.mul_apply, Fin.sum_univ_four, rMat]
  have l13 : (rMat a b c d * T) 1 3 = T 1 3 + c * T 2 3 + d * T 3 3 := by
    simp [Matrix.mul_apply, Fin.sum_univ_four, rMat]
  have r13 : (T * rMat a b c d) 1 3 = T 1 0 * b + T 1 1 * d + T 1 3 := by
    simp [Matrix.mul_apply, Fin.sum_univ_four, rMat]
  have l03 : (rMat a b c d * T) 0 3 = T 0 3 + a * T 2 3 + b * T 3 3 := by
    simp [Matrix.mul_apply, Fin.sum_univ_four, rMat]
  have r03 : (T * rMat a b c d) 0 3 = T 0 0 * b + T 0 1 * d + T 0 3 := by
    simp [Matrix.mul_apply, Fin.sum_univ_four, rMat]
  have e02 := congrFun (congrFun h 0) 2
  have e13 := congrFun (congrFun h 1) 3
  have e03 := congrFun (congrFun h 0) 3
  rw [l02, r02, d0, d2, h32] at e02
  rw [l13, r13, d1, d3, h10] at e13
  rw [l03, r03, d0, d3] at e03
  refine ⟨?_, ?_, ?_⟩
  · linear_combination -e02
  · linear_combination e13
  · linear_combination -e03

theorem mem_rGrp_of_unitriangular {t : SL4} (ht : t ∈ unitriangular 4 (ZMod 3))
    (h01 : (t : Mat4) 0 1 = 0) (h23 : (t : Mat4) 2 3 = 0) : t ∈ rGrp := by
  obtain ⟨hlow, hdiag⟩ := mem_unitriangular.mp ht
  rw [mem_rGrp_iff, IsR]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rMat, h01, h23, hdiag, hlow 1 0 (by decide), hlow 2 0 (by decide),
      hlow 2 1 (by decide), hlow 3 0 (by decide), hlow 3 1 (by decide), hlow 3 2 (by decide)]

theorem card_zmod_three_prod : Nat.card (ZMod 3 × ZMod 3) = 9 := by
  rw [Nat.card_prod, Nat.card_zmod]

theorem card_le_nine_of_coords {H : Subgroup SL4} (f : SL4 → ZMod 3 × ZMod 3)
    (hf : ∀ x ∈ H, ∀ y ∈ H, f x = f y → x = y) : Nat.card H ≤ 9 := by
  have hinj : Function.Injective (fun x : H => f x) := fun x y h =>
    Subtype.ext (hf x x.2 y y.2 h)
  have := Nat.card_le_card_of_injective _ hinj
  rwa [card_zmod_three_prod] at this

theorem val_eq_rMat {r : SL4} (hr : r ∈ rGrp) :
    (r : Mat4) = rMat ((r : Mat4) 0 2) ((r : Mat4) 0 3) ((r : Mat4) 1 2) ((r : Mat4) 1 3) :=
  mem_rGrp_iff.mp hr

theorem card_rGrp_inf_centralizer_le {t : SL4} (ht : t ∈ unitriangular 4 (ZMod 3))
    (htR : t ∉ rGrp) :
    Nat.card (rGrp ⊓ Subgroup.centralizer ({t} : Set SL4) : Subgroup SL4) ≤ 9 := by
  obtain ⟨hlow, hdiag⟩ := mem_unitriangular.mp ht
  have hne : ¬ ((t : Mat4) 0 1 = 0 ∧ (t : Mat4) 2 3 = 0) := fun h =>
    htR (mem_rGrp_of_unitriangular ht h.1 h.2)
  have hcond : ∀ r ∈ rGrp ⊓ Subgroup.centralizer ({t} : Set SL4),
      (r : Mat4) 1 2 * (t : Mat4) 0 1 = 0 ∧ (r : Mat4) 1 2 * (t : Mat4) 2 3 = 0 ∧
        (t : Mat4) 0 1 * (r : Mat4) 1 3 = (t : Mat4) 2 3 * (r : Mat4) 0 2 := by
    rintro r ⟨hrR, hrc⟩
    have hrt : r * t = t * r := Subgroup.mem_centralizer_singleton_iff.mp hrc
    have h' : (r : Mat4) * (t : Mat4) = (t : Mat4) * (r : Mat4) := by
      change ((r * t : SL4) : Mat4) = ((t * r : SL4) : Mat4)
      rw [hrt]
    rw [val_eq_rMat hrR] at h'
    exact comm_rMat_entries hlow hdiag h'
  have hext : ∀ r ∈ rGrp, ∀ r' ∈ rGrp, (r : Mat4) 0 2 = (r' : Mat4) 0 2 →
      (r : Mat4) 0 3 = (r' : Mat4) 0 3 → (r : Mat4) 1 2 = (r' : Mat4) 1 2 →
      (r : Mat4) 1 3 = (r' : Mat4) 1 3 → r = r' := by
    intro r hr r' hr' h1 h2 h3 h4
    apply Subtype.ext
    rw [val_eq_rMat hr, val_eq_rMat hr', h1, h2, h3, h4]
  have hfield : ∀ x y : ZMod 3, x ≠ 0 → y * x = 0 → y = 0 := fun x y hx hxy =>
    (mul_eq_zero.mp hxy).resolve_right hx
  by_cases h01 : (t : Mat4) 0 1 = 0
  ·
    have h23 : (t : Mat4) 2 3 ≠ 0 := fun h => hne ⟨h01, h⟩
    refine card_le_nine_of_coords (fun r => ((r : Mat4) 0 3, (r : Mat4) 1 3)) ?_
    intro r hr r' hr' hrr
    obtain ⟨-, c2, c3⟩ := hcond r hr
    obtain ⟨-, c2', c3'⟩ := hcond r' hr'
    have hc : (r : Mat4) 1 2 = 0 := hfield _ _ h23 c2
    have hc' : (r' : Mat4) 1 2 = 0 := hfield _ _ h23 c2'
    rw [h01, zero_mul] at c3 c3'
    have ha : (r : Mat4) 0 2 = 0 := hfield _ _ h23 (by rw [mul_comm]; exact c3.symm)
    have ha' : (r' : Mat4) 0 2 = 0 := hfield _ _ h23 (by rw [mul_comm]; exact c3'.symm)
    obtain ⟨hb, hd⟩ := Prod.mk.inj hrr
    exact hext r hr.1 r' hr'.1 (ha.trans ha'.symm) hb (hc.trans hc'.symm) hd
  ·
    refine card_le_nine_of_coords (fun r => ((r : Mat4) 0 2, (r : Mat4) 0 3)) ?_
    intro r hr r' hr' hrr
    obtain ⟨c1, -, c3⟩ := hcond r hr
    obtain ⟨c1', -, c3'⟩ := hcond r' hr'
    have hc : (r : Mat4) 1 2 = 0 := hfield _ _ h01 c1
    have hc' : (r' : Mat4) 1 2 = 0 := hfield _ _ h01 c1'
    obtain ⟨ha, hb⟩ := Prod.mk.inj hrr
    have hd : (r : Mat4) 1 3 = (r' : Mat4) 1 3 := by
      have e : (t : Mat4) 0 1 * ((r : Mat4) 1 3 - (r' : Mat4) 1 3) = 0 := by
        rw [mul_sub, c3, c3', ha, sub_self]
      exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left h01)
    exact hext r hr.1 r' hr'.1 ha hb (hc.trans hc'.symm) hd

theorem uSL_mem_unitriangular : uSL 0 0 0 0 ∈ unitriangular 4 (ZMod 3) := by
  rw [mem_unitriangular]
  exact ⟨fun i j hij => by fin_cases i <;> fin_cases j <;> simp_all [uSL, uMat],
    fun i => by fin_cases i <;> simp [uSL, uMat]⟩

theorem vSL_mem_unitriangular : vSL 0 0 0 0 ∈ unitriangular 4 (ZMod 3) := by
  rw [mem_unitriangular]
  exact ⟨fun i j hij => by fin_cases i <;> fin_cases j <;> simp_all [vSL, vMat],
    fun i => by fin_cases i <;> simp [vSL, vMat]⟩

theorem card_center_unitriangular_le :
    Nat.card (unitriangular 4 (ZMod 3) ⊓
      Subgroup.centralizer ((unitriangular 4 (ZMod 3) : Subgroup SL4) : Set SL4) :
        Subgroup SL4) ≤ 3 := by
  have hR : rGrp ≤ unitriangular 4 (ZMod 3) := by
    intro r hr
    rw [mem_unitriangular, val_eq_rMat hr]
    refine ⟨?_, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> first | (exact absurd hij (by decide)) | simp [rMat]
    · intro i
      fin_cases i <;> simp [rMat]
  have hzR : ∀ z ∈ unitriangular 4 (ZMod 3) ⊓
      Subgroup.centralizer ((unitriangular 4 (ZMod 3) : Subgroup SL4) : Set SL4), z ∈ rGrp := by
    rintro z ⟨hzU, hzc⟩
    by_contra hzR
    have hle := card_rGrp_inf_centralizer_le hzU hzR
    have hRle : rGrp ≤ rGrp ⊓ Subgroup.centralizer ({z} : Set SL4) := by
      refine le_inf le_rfl fun r hr => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hzc r (hR hr)
    have := Subgroup.card_le_of_le hRle
    rw [card_rGrp] at this
    omega
  have hcomm : ∀ z ∈ unitriangular 4 (ZMod 3) ⊓
      Subgroup.centralizer ((unitriangular 4 (ZMod 3) : Subgroup SL4) : Set SL4),
      ∀ u ∈ unitriangular 4 (ZMod 3), (z : Mat4) * (u : Mat4) = (u : Mat4) * (z : Mat4) := by
    rintro z ⟨-, hzc⟩ u hu
    change ((z * u : SL4) : Mat4) = ((u * z : SL4) : Mat4)
    rw [(Subgroup.mem_centralizer_iff.mp hzc u hu).symm]
  have hinj : Function.Injective (fun z : (unitriangular 4 (ZMod 3) ⊓
      Subgroup.centralizer ((unitriangular 4 (ZMod 3) : Subgroup SL4) : Set SL4) :
        Subgroup SL4) => ((z : SL4) : Mat4) 0 3) := by
    rintro ⟨z, hz⟩ ⟨z', hz'⟩ h
    have h' : ((z : SL4) : Mat4) 0 3 = ((z' : SL4) : Mat4) 0 3 := h
    have hzr := hzR z hz
    have hzr' := hzR z' hz'
    have key : ∀ y ∈ unitriangular 4 (ZMod 3) ⊓
        Subgroup.centralizer ((unitriangular 4 (ZMod 3) : Subgroup SL4) : Set SL4),
        (y : Mat4) 0 2 = 0 ∧ (y : Mat4) 1 2 = 0 ∧ (y : Mat4) 1 3 = 0 := by
      intro y hy
      have hyr := hzR y hy
      have hu := hcomm y hy _ uSL_mem_unitriangular
      have hv := hcomm y hy _ vSL_mem_unitriangular
      rw [val_eq_rMat hyr] at hu hv
      have hU := comm_rMat_entries (T := uMat 0 0 0 0)
        (fun i j hij => by fin_cases i <;> fin_cases j <;> simp_all [uMat])
        (fun i => by fin_cases i <;> simp [uMat]) hu
      have hV := comm_rMat_entries (T := vMat 0 0 0 0)
        (fun i j hij => by fin_cases i <;> fin_cases j <;> simp_all [vMat])
        (fun i => by fin_cases i <;> simp [vMat]) hv
      have u01 : uMat 0 0 0 0 0 1 = 1 := by decide
      have u23 : uMat 0 0 0 0 2 3 = 0 := by decide
      have v01 : vMat 0 0 0 0 0 1 = 0 := by decide
      have v23 : vMat 0 0 0 0 2 3 = 1 := by decide
      rw [u01, u23] at hU
      rw [v01, v23] at hV
      simp only [mul_one, mul_zero, one_mul, zero_mul] at hU hV
      exact ⟨hV.2.2.symm, hU.1, hU.2.2⟩
    obtain ⟨a, c, d⟩ := key z hz
    obtain ⟨a', c', d'⟩ := key z' hz'
    refine Subtype.ext (Subtype.ext ?_)
    rw [val_eq_rMat hzr, val_eq_rMat hzr', a, c, d, a', c', d', h']
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_zmod] at this

theorem card_unitriangular_four_three : Nat.card (unitriangular 4 (ZMod 3)) = 729 := by
  rw [card_unitriangular, Nat.card_zmod]
  norm_num

theorem eq_rGrp_of_le_unitriangular {B : Subgroup SL4} (hBU : B ≤ unitriangular 4 (ZMod 3))
    (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (h81 : 81 ≤ Nat.card B) : B = rGrp := by
  have hR : rGrp ≤ unitriangular 4 (ZMod 3) := by
    intro r hr
    rw [mem_unitriangular, val_eq_rMat hr]
    refine ⟨?_, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> first | (exact absurd hij (by decide)) | simp [rMat]
    · intro i
      fin_cases i <;> simp [rMat]
  have hle := le_of_abelian_card_ge hR (fun a ha b hb => rGrp_comm ha hb)
    card_unitriangular_four_three card_rGrp
    (fun t ht htR => card_rGrp_inf_centralizer_le ht htR) card_center_unitriangular_le hBU hBc
    h81
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_rGrp]; exact h81)

theorem piL_injOn_unitriangular {x y : SL4} (hx : x ∈ unitriangular 4 (ZMod 3))
    (hy : y ∈ unitriangular 4 (ZMod 3)) (h : piL x = piL y) : x = y :=
  proj_injOn_unitriangular 4 hx hy h

theorem eq_map_rGrp_of_le {B : Subgroup PSL43} (hBU : B ≤ projUnitriangular 4 (ZMod 3))
    (hBc : IsMulCommutative B) (h81 : 81 ≤ Nat.card B) : B = rGrp.map piL := by
  set Bt := B.comap piL ⊓ unitriangular 4 (ZMod 3) with hBt
  have hBtU : Bt ≤ unitriangular 4 (ZMod 3) := inf_le_right
  have hBtmap : Bt.map piL = B := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.1
    · intro y hy
      obtain ⟨x, hxU, rfl⟩ := hBU hy
      exact ⟨x, ⟨hy, hxU⟩, rfl⟩
  have hBtcard : Nat.card Bt = Nat.card B := by
    rw [← card_map_piL_of_le hBtU, hBtmap]
  have hBtc : ∀ x ∈ Bt, ∀ y ∈ Bt, x * y = y * x := by
    intro x hx y hy
    refine piL_injOn_unitriangular ((unitriangular 4 (ZMod 3)).mul_mem (hBtU hx) (hBtU hy))
      ((unitriangular 4 (ZMod 3)).mul_mem (hBtU hy) (hBtU hx)) ?_
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (hBc.is_comm.comm ⟨piL x, hx.1⟩ ⟨piL y, hy.1⟩)
  have hBtR := eq_rGrp_of_le_unitriangular hBtU hBtc (hBtcard ▸ h81)
  rw [← hBtmap, hBtR]

@[expose] def tMat : Mat4 := !![-1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, 1]

theorem det_tMat : tMat.det = 1 := by decide

@[expose] def tSL : SL4 := ⟨tMat, det_tMat⟩

theorem tMat_mul_self : tMat * tMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tMat, Matrix.mul_apply, Fin.sum_univ_four]

theorem tSL_sq : tSL ^ 2 = 1 := by
  rw [pow_two]
  exact Subtype.ext tMat_mul_self

theorem tSL_inv : tSL⁻¹ = tSL := by
  rw [inv_eq_iff_mul_eq_one, ← pow_two, tSL_sq]

theorem tMat_mul_rMat (a b c d : ZMod 3) :
    tMat * rMat a b c d = rMat a (-b) (-c) d * tMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tMat, rMat, Matrix.mul_apply, Fin.sum_univ_four]

theorem tSL_conj_mem {r : SL4} (hr : r ∈ rGrp) : tSL * r * tSL⁻¹ ∈ rGrp := by
  rw [tSL_inv, mem_rGrp_iff, IsR]
  have hv : ((tSL * r * tSL : SL4) : Mat4) = tMat * (r : Mat4) * tMat := rfl
  rw [hv, val_eq_rMat hr, tMat_mul_rMat, mul_assoc, tMat_mul_self, mul_one]
  simp [rMat]

theorem tSL_mem_normalizer : tSL ∈ Subgroup.normalizer (rGrp : Set SL4) := by
  rw [Subgroup.mem_normalizer_iff]
  intro r
  constructor
  · exact tSL_conj_mem
  · intro h
    have h' := tSL_conj_mem h
    simp only [tSL_inv] at h'
    have h2 : tSL * tSL = 1 := by rw [← pow_two, tSL_sq]
    have e : tSL * (tSL * r * tSL) * tSL = r := by
      calc tSL * (tSL * r * tSL) * tSL = (tSL * tSL) * r * (tSL * tSL) := by group
        _ = r := by rw [h2]; group
    rwa [e] at h'

theorem piL_tSL_ne_one : piL tSL ≠ 1 := by
  intro h
  rw [← map_one piL, proj_eq_proj_iff] at h
  have h' : tSL ∈ scalars 4 (ZMod 3) := by
    have := (scalars 4 (ZMod 3)).inv_mem h
    simpa using this
  rcases val_eq_one_or_neg_one_of_mem_scalars h' with h1 | h1
  · have := congrFun (congrFun h1 0) 0
    revert this
    change tMat 0 0 = (1 : Mat4) 0 0 → False
    decide
  · have := congrFun (congrFun h1 1) 1
    revert this
    change tMat 1 1 = (-1 : Mat4) 1 1 → False
    decide

theorem card_rGrp_inf_centralizer_tSL :
    Nat.card (rGrp ⊓ Subgroup.centralizer ({tSL} : Set SL4) : Subgroup SL4) = 9 := by
  have hcond : ∀ r ∈ rGrp ⊓ Subgroup.centralizer ({tSL} : Set SL4),
      (r : Mat4) 0 3 = 0 ∧ (r : Mat4) 1 2 = 0 := by
    rintro r ⟨hrR, hrc⟩
    have hrt : r * tSL = tSL * r := Subgroup.mem_centralizer_singleton_iff.mp hrc
    have h' : (r : Mat4) * tMat = tMat * (r : Mat4) := by
      change ((r * tSL : SL4) : Mat4) = ((tSL * r : SL4) : Mat4)
      rw [hrt]
    rw [val_eq_rMat hrR, tMat_mul_rMat] at h'
    have e03 := congrFun (congrFun h' 0) 3
    have e12 := congrFun (congrFun h' 1) 2
    simp [rMat, tMat, Matrix.mul_apply, Fin.sum_univ_four] at e03 e12
    have h2 : ∀ x : ZMod 3, x = -x → x = 0 := by decide
    exact ⟨h2 _ e03, h2 _ e12.symm⟩
  apply le_antisymm
  · refine card_le_nine_of_coords (fun r => ((r : Mat4) 0 2, (r : Mat4) 1 3)) ?_
    intro r hr r' hr' hrr
    obtain ⟨hb, hc⟩ := hcond r hr
    obtain ⟨hb', hc'⟩ := hcond r' hr'
    obtain ⟨ha, hd⟩ := Prod.mk.inj hrr
    apply Subtype.ext
    rw [val_eq_rMat hr.1, val_eq_rMat hr'.1, ha, hd, hb, hb', hc, hc']
  ·
    have hmem : ∀ p : ZMod 3 × ZMod 3, rHom (Multiplicative.ofAdd ![p.1, 0, 0, p.2]) ∈
        rGrp ⊓ Subgroup.centralizer ({tSL} : Set SL4) := by
      intro p
      refine Subgroup.mem_inf.mpr ⟨⟨_, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      apply Subtype.ext
      change rMat p.1 0 0 p.2 * tMat = tMat * rMat p.1 0 0 p.2
      rw [tMat_mul_rMat]
      simp
    let f : ZMod 3 × ZMod 3 → (rGrp ⊓ Subgroup.centralizer ({tSL} : Set SL4) : Subgroup SL4) :=
      fun p => ⟨rHom (Multiplicative.ofAdd ![p.1, 0, 0, p.2]), hmem p⟩
    have hf : Function.Injective f := by
      rintro ⟨a, d⟩ ⟨a', d'⟩ h
      have h1 : rMat a 0 0 d 0 2 = rMat a' 0 0 d' 0 2 :=
        congrArg (fun x : (rGrp ⊓ Subgroup.centralizer ({tSL} : Set SL4) : Subgroup SL4) =>
          ((x : SL4) : Mat4) 0 2) h
      have h2 : rMat a 0 0 d 1 3 = rMat a' 0 0 d' 1 3 :=
        congrArg (fun x : (rGrp ⊓ Subgroup.centralizer ({tSL} : Set SL4) : Subgroup SL4) =>
          ((x : SL4) : Mat4) 1 3) h
      simp [rMat] at h1 h2
      rw [h1, h2]
    have := Nat.card_le_card_of_injective f hf
    rwa [card_zmod_three_prod] at this

theorem e81InvAt_PSL43 : E81InvAt PSL43 := by
  obtain ⟨S, hS⟩ := exists_sylow_projUnitriangular (K := ZMod 3) 3 (n := 4) (by norm_num)
  have hT : Nat.card (projUnitriangular 4 (ZMod 3)) = 3 ^ (Nat.card PSL43).factorization 3 := by
    rw [← hS]
    exact Sylow.card_eq_multiplicity S
  have hR : rGrp ≤ unitriangular 4 (ZMod 3) := by
    intro r hr
    rw [mem_unitriangular, val_eq_rMat hr]
    refine ⟨?_, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> first | (exact absurd hij (by decide)) | simp [rMat]
    · intro i
      fin_cases i <;> simp [rMat]
  have hA : ∀ B : Subgroup PSL43, B ≤ projUnitriangular 4 (ZMod 3) → IsMulCommutative B →
      81 ≤ Nat.card B → B = rGrp.map piL := fun B hBU hBc h81 => eq_map_rGrp_of_le hBU hBc h81
  have hDe : CFSG.Assembly.IsElemAbelian 3 (rGrp.map piL) := isElemAbelian_map _ isElemAbelian_rGrp
  have hD81 : 81 ≤ Nat.card (rGrp.map piL) := by rw [card_map_piL_of_le hR, card_rGrp]
  have htN : piL tSL ∈ Subgroup.normalizer ((rGrp.map piL : Subgroup PSL43) : Set PSL43) :=
    Subgroup.le_normalizer_map piL ⟨tSL, tSL_mem_normalizer, rfl⟩
  have ht2 : piL tSL ^ 2 = 1 := by rw [← map_pow, tSL_sq, map_one]
  have htC : Nat.card (rGrp.map piL ⊓ Subgroup.centralizer {piL tSL} : Subgroup PSL43) = 9 := by
    have heq : rGrp.map piL ⊓ Subgroup.centralizer {piL tSL} =
        (rGrp ⊓ Subgroup.centralizer ({tSL} : Set SL4)).map piL := by
      apply le_antisymm
      · intro y hy
        obtain ⟨hyR, hyc⟩ := Subgroup.mem_inf.mp hy
        obtain ⟨r, hr, rfl⟩ := hyR
        refine ⟨r, Subgroup.mem_inf.mpr ⟨hr, ?_⟩, rfl⟩
        rw [Subgroup.mem_centralizer_singleton_iff] at hyc ⊢
        exact (mul_comm_of_proj_mul_comm (isElemAbelian_rGrp.2 r hr) hyc.symm).symm
      · rintro _ ⟨r, hr', rfl⟩
        obtain ⟨hr, hrc⟩ := Subgroup.mem_inf.mp hr'
        refine Subgroup.mem_inf.mpr ⟨⟨r, hr, rfl⟩, ?_⟩
        rw [Subgroup.mem_centralizer_singleton_iff] at hrc ⊢
        rw [← map_mul, ← map_mul, hrc]
    rw [heq, card_map_piL_of_le (inf_le_left.trans hR), card_rGrp_inf_centralizer_tSL]
  exact e81InvAt_of_unique hT hA hDe hD81 htN piL_tSL_ne_one ht2 htC

theorem e81InvAt_of_mulEquiv_l43 {X : Type*} [Group X]
    (φ : X ≃* CFSG.Assembly.RankThreeEven.projSL 4 (GaloisField 3 1)) : E81InvAt X :=
  e81InvAt_of_mulEquiv (φ.trans projSLEquivPSL43) e81InvAt_PSL43

end CFSG.RankThree.PartTwo.Sec6.Res611Res4

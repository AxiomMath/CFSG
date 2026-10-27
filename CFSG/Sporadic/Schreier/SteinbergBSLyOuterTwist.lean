module

public import CFSG.Sporadic.Schreier.SteinbergBSLyOuterCertificate
public import CFSG.Sporadic.Schreier.LyDoubleCover

public noncomputable section

namespace CFSG.Sporadic.LySchreier

open CFSG.Sporadic.Ly CFSG.Sporadic.Ly.Native CFSG.Sporadic.LySchreier.Native
open CFSG.Sporadic.He.Native

@[expose] def bsCz (j : ℕ) : J := if j < 12 then cStar j else lyz

@[expose] def bsT (i : ℕ) : J :=
  if i < 9 then evalWord bsCz (bsTWordsN.getD i []) else if i = 9 then lyz else 1

@[expose] def bsF : J :=
  evalWord cStar sylowWords[2]! * evalWord cStar sylowWords[1]! * evalWord cStar sylowWords[2]! *
    evalWord cStar sylowWords[1]!

@[expose] def bsH : J := a * b * a * (b⁻¹ * a)

@[expose] def bsG : J := (bsH * bsF) ^ 7 * (a * bsH) ^ 4

theorem bsRepM_pow {X : Mat} {g : J} (h : RepM X g) (n : ℕ) :
    RepM (powM 5 111 X n) (g ^ n) := by
  unfold RepM at *
  rw [toMat_powM, h, mat_pow' g n]

theorem bsRepM_eq
    {X Y : Mat} {g h : J} (hX : RepM X g) (hY : RepM Y h)
    (e : (X == Y) = true) : g = h := by
  have hXY : X = Y := beq_iff_eq.1 e
  subst hXY
  exact hX.unique hY

theorem bsRepM_cz
    (j : ℕ) : RepM (bsCzM csArr j) (bsCz j) ∧ RepM (bsCzMi csArr j) (bsCz j)⁻¹ := by
  unfold bsCzM bsCzMi bsCz
  split_ifs with hj
  · exact repM_csArr j
  · refine ⟨repM_matA, ?_⟩
    rw [lyz, a_inv']
    exact repM_matA

theorem bsRepM_TM
    (i : ℕ) : RepM (bsTM csArr i) (bsT i) := by
  unfold bsTM bsT
  split_ifs with h1 h2
  · exact repM_evalWordM (fun j => (bsRepM_cz j).1) (fun j => (bsRepM_cz j).2) _
  · exact repM_matA
  · exact repM_id

theorem bs_getD_ofFn (F : ℕ → Mat) (hF : ∀ i, 10 ≤ i → F i = idM 111) (i : ℕ) :
    (Array.ofFn (n := 10) fun k => F k.val).getD i (idM 111) = F i := by
  by_cases hi : i < 10
  · simp [Array.getD, hi]
  · rw [hF i (by omega)]
    simp [Array.getD, hi]

abbrev bsTa (i : ℕ) : Mat := (Array.ofFn (n := 10) fun k => bsTM csArr k.val).getD i (idM 111)

abbrev bsTia (i : ℕ) : Mat := (Array.ofFn (n := 10) fun k => bsTMi csArr k.val).getD i (idM 111)

abbrev bsFM : Mat :=
  mulM 5 111 (mulM 5 111 (mulM 5 111 (sylowGens csArr)[2]! (sylowGens csArr)[1]!)
    (sylowGens csArr)[2]!) (sylowGens csArr)[1]!

abbrev bsGM : Mat := r3eGM (r3eHM (powM 5 111 matB 4)) bsFM

theorem bsTa_eq (i : ℕ) : bsTa i = bsTM csArr i := by
  refine bs_getD_ofFn _ (fun i hi => ?_) i
  unfold bsTM
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

theorem bsTia_eq (i : ℕ) : bsTia i = bsTMi csArr i := by
  refine bs_getD_ofFn _ (fun i hi => ?_) i
  unfold bsTMi
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

theorem bs_word_checks
    : bsWordChecks bsTa bsTia bsFM bsGM = true := by
  have h : bsChecks (powM 5 111 matB 4) csArr (sylowGens csArr) = true := by
    rw [csArr_def]
    exact bs_ly_outer_certificate
  exact h

theorem bs_parts :
    (∀ i ∈ List.range 9,
      (mulM 5 111 (mulM 5 111 (bsTa i) (bsTa i)) (bsTa i) == idM 111) = true) ∧
    (evalWordM bsTa bsTia bsWfN == bsFM) = true ∧
    (mulM 5 111 bsGM matA == mulM 5 111 bsFM bsGM) = true ∧
    (mulM 5 111 (evalWordM bsTa bsTia bsWmN) bsGM ==
      mulM 5 111 bsGM (evalWordM bsTa bsTia bsVN)) = true ∧
    (mulM 5 111 (evalWordM (fun i => bsTa (bsSwI i)) (fun i => bsTia (bsSwI i)) bsWmN) bsGM ==
      mulM 5 111 bsGM (evalWordM bsTa bsTia bsUN)) = true := by
  have h := bs_word_checks
  unfold bsWordChecks at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem bsRepM_Ta
    (i : ℕ) : RepM (bsTa i) (bsT i) := by
  rw [bsTa_eq]
  exact bsRepM_TM i

theorem bsT_cube
    {i : ℕ} (hi : i < 9) : bsT i ^ 3 = 1 := by
  have h := bs_parts.1 i (List.mem_range.2 hi)
  rw [pow_three']
  exact bsRepM_eq (((bsRepM_Ta i).mul (bsRepM_Ta i)).mul (bsRepM_Ta i)) repM_id h

theorem bsRepM_Tia
    (i : ℕ) : RepM (bsTia i) (bsT i)⁻¹ := by
  rw [bsTia_eq]
  unfold bsTMi
  split_ifs with h1 h2
  · have e : (bsT i)⁻¹ = bsT i * bsT i := by
      apply inv_eq_of_mul_eq_one_right
      rw [← mul_assoc, ← pow_three', bsT_cube h1]
    rw [e]
    exact (bsRepM_TM i).mul (bsRepM_TM i)
  · have e : bsT i = lyz := by
      unfold bsT
      rw [ite_eq_right h1, ite_eq_left h2]
    rw [e, lyz, a_inv']
    exact repM_matA
  · have e : bsT i = 1 := by
      unfold bsT
      rw [ite_eq_right h1, ite_eq_right h2]
    rw [e, inv_one]
    exact repM_id

theorem bsRepM_word
    (w : List ℤ) : RepM (evalWordM bsTa bsTia w) (evalWord bsT w) :=
  repM_evalWordM bsRepM_Ta bsRepM_Tia w

theorem bsRepM_word_swap
    (w : List ℤ) :
    RepM (evalWordM (fun i => bsTa (bsSwI i)) (fun i => bsTia (bsSwI i)) w)
      (evalWord (fun i => bsT (bsSwI i)) w) :=
  repM_evalWordM (fun i => bsRepM_Ta (bsSwI i)) (fun i => bsRepM_Tia (bsSwI i)) w

theorem bsRepM_syl
    {k : ℕ} (hk : k < 5) :
    RepM (sylowGens csArr)[k]! (evalWord cStar sylowWords[k]!) := by
  rw [getElem!_pos (sylowGens csArr) k (by simp [sylowGens]; omega)]
  simp only [sylowGens, Array.getElem_push, Array.size_ofFn, Array.getElem_ofFn]
  rw [dite_eq_left hk]
  exact repM_evalWordM (fun i => (repM_csArr i).1) (fun i => (repM_csArr i).2) _

theorem bsRepM_F : RepM bsFM bsF :=
  (((bsRepM_syl (by norm_num)).mul (bsRepM_syl (by norm_num))).mul
    (bsRepM_syl (by norm_num))).mul (bsRepM_syl (by norm_num))

theorem bsRepM_H : RepM (r3eHM (powM 5 111 matB 4)) bsH :=
  ((repM_matA.mul repM_matB).mul repM_matA).mul (repM_b4.mul repM_matA)

theorem bsRepM_G : RepM bsGM bsG :=
  (bsRepM_pow (bsRepM_H.mul bsRepM_F) 7).mul (bsRepM_pow (repM_matA.mul bsRepM_H) 4)

theorem bsF_eq :
    evalWord bsT bsWfN = bsF :=
  bsRepM_eq (bsRepM_word _) bsRepM_F bs_parts.2.1

theorem bsG_mul_lyz :
    bsG * lyz = bsF * bsG :=
  bsRepM_eq (bsRepM_G.mul repM_matA) (bsRepM_F.mul bsRepM_G) bs_parts.2.2.1

theorem bsWm_mul_G :
    evalWord bsT bsWmN * bsG = bsG * evalWord bsT bsVN :=
  bsRepM_eq ((bsRepM_word _).mul bsRepM_G) (bsRepM_G.mul (bsRepM_word _)) bs_parts.2.2.2.1

theorem bsWm_swap_mul_G :
    evalWord (fun i => bsT (bsSwI i)) bsWmN * bsG = bsG * evalWord bsT bsUN :=
  bsRepM_eq ((bsRepM_word_swap _).mul bsRepM_G) (bsRepM_G.mul (bsRepM_word _)) bs_parts.2.2.2.2

@[expose] def bsCyc (i : ℕ) : Equiv.Perm (Fin 11) :=
  if h : i < 9 then Equiv.swap 0 ⟨i + 2, by omega⟩ * Equiv.swap 0 1 else 1

@[expose] def bsPz (j : ℕ) : Equiv.Perm (Fin 11) := if j < 12 then pPerm j else 1

theorem bs_pz_words : ∀ i : Fin 9, ∀ x : Fin 11,
    evalWord bsPz (bsTWordsN.getD i.val []) x = bsCyc i.val x := by
  decide +kernel

theorem bs_cyc_swap : ∀ i : Fin 9, ∀ x : Fin 11,
    (Equiv.swap (8 : Fin 11) 9 * bsCyc i.val * Equiv.swap 8 9 : Equiv.Perm (Fin 11)) x =
      bsCyc (bsSwI i.val) x := by
  decide +kernel

theorem bs_lam_fixfree : ∀ x : Fin 11, evalWord (fun i => bsCyc (bsSwI i)) bsVN x ≠ x := by
  decide +kernel

theorem bs_rho_fix : evalWord bsCyc bsUN 5 = 5 := by
  decide +kernel

theorem bs_wf_letters : ∀ l ∈ bsWfN, bsSwI (letterIdx l) = letterIdx l := by
  decide

theorem bsCz_mem
    (j : ℕ) : bsCz j ∈ lyC := by
  unfold bsCz
  split_ifs
  · exact cStar_mem j
  · exact lyz_mem_lyC

theorem bsT_mem
    (i : ℕ) : bsT i ∈ lyC := by
  unfold bsT
  split_ifs
  · exact evalWord_mem fun _ _ => bsCz_mem _
  · exact lyz_mem_lyC
  · exact lyC.one_mem

@[expose] def bsCzC
    (j : ℕ) : lyC := ⟨bsCz j, bsCz_mem j⟩

@[expose] def bsTC
    (i : ℕ) : lyC := ⟨bsT i, bsT_mem i⟩

theorem imgC_bsCzC
    (j : ℕ) : imgC (bsCzC j) = bsPz j := by
  by_cases hj : j < 12
  · have e : bsCzC j = ⟨cStar j, cStar_mem j⟩ := Subtype.ext (by simp [bsCzC, bsCz, hj])
    rw [e, imgC_cStar hj, bsPz, ite_eq_left hj]
  · have e : bsCzC j = zC := Subtype.ext (by simp [bsCzC, bsCz, hj, zC])
    rw [e, imgC_zC, bsPz, ite_eq_right hj]

theorem coe_evalWord_lyC (g : ℕ → lyC) (w : List ℤ) :
    ((evalWord g w : lyC) : J) = evalWord (fun i => (g i : J)) w := by
  rw [← Subgroup.coe_subtype, map_evalWord]

theorem imgC_bsTC
    (i : ℕ) : imgC (bsTC i) = bsCyc i := by
  by_cases h9 : i < 9
  · have e : bsTC i = evalWord bsCzC (bsTWordsN.getD i []) := by
      apply Subtype.ext
      rw [coe_evalWord_lyC]
      simp only [bsTC, bsT, ite_eq_left h9]
      rfl
    rw [e, map_evalWord]
    ext x
    rw [show (fun j => imgC (bsCzC j)) = bsPz from funext imgC_bsCzC]
    exact congrArg Fin.val (bs_pz_words ⟨i, h9⟩ x)
  · by_cases h9' : i = 9
    · have e : bsTC i = zC := Subtype.ext (by simp [bsTC, bsT, h9', zC])
      rw [e, imgC_zC, bsCyc, dite_eq_right h9]
    · have e : bsTC i = 1 := Subtype.ext (by simp [bsTC, bsT, h9, h9'])
      rw [e, map_one, bsCyc, dite_eq_right h9]

theorem coe_bsTC_pow
    (i : ℕ) (n : ℕ) : ((bsTC i ^ n : lyC) : J) = bsT i ^ n := by
  rw [Subgroup.coe_pow]
  rfl

theorem zC_ne_one : zC ≠ 1 := by
  intro h
  have := orderOf_zC
  rw [h, orderOf_one] at this
  exact absurd this (by norm_num)

theorem bs_cube_aux {G : Type*} [Group G] {z t : G} (hzt : z * t = t * z) (hz : z ^ 2 = 1)
    (ht : t ^ 3 = 1) (h : (z * t) ^ 3 = 1) : z = 1 := by
  rw [(Commute.mul_pow hzt 3), ht, mul_one, show (3 : ℕ) = 2 + 1 from rfl, pow_succ, hz,
    one_mul] at h
  exact h

theorem bs_no_swap_twist
    (hC : lyC = Subgroup.centralizer ({lyz} : Set J)) (α : MulAut J)
    (β : MulAut lyC) (hαβ : ∀ x : lyC, (β x : J) = α x) (hz : α lyz = lyz)
    (hβ : ∀ x : lyC, imgC (β x) = Equiv.swap 8 9 * imgC x * Equiv.swap 8 9) : False := by
  have hT : ∀ i, β (bsTC i) = bsTC (bsSwI i) := by
    intro i
    by_cases h9 : i < 9
    · have hsw : bsSwI i < 9 := by unfold bsSwI; split_ifs <;> omega
      have himg : imgC (β (bsTC i) * (bsTC (bsSwI i))⁻¹) = 1 := by
        rw [map_mul, map_inv, hβ, imgC_bsTC, imgC_bsTC]
        have e : Equiv.swap (8 : Fin 11) 9 * bsCyc i * Equiv.swap 8 9 = bsCyc (bsSwI i) :=
          Equiv.ext (bs_cyc_swap ⟨i, h9⟩)
        rw [e, mul_inv_cancel]
      rcases mem_zGroup.1 ((imgC_eq_one_iff _).1 himg) with h | h
      · exact mul_inv_eq_one.1 h
      · exfalso
        have hb : β (bsTC i) = zC * bsTC (bsSwI i) := (mul_inv_eq_iff_eq_mul (G := lyC)).1 h
        have hc1 : bsTC i ^ 3 = 1 := Subtype.ext (by rw [coe_bsTC_pow, bsT_cube h9]; rfl)
        have hc2 : bsTC (bsSwI i) ^ 3 = 1 :=
          Subtype.ext (by rw [coe_bsTC_pow, bsT_cube hsw]; rfl)
        have hcomm : zC * bsTC (bsSwI i) = bsTC (bsSwI i) * zC :=
          (Subgroup.mem_center_iff.1 zC_mem_center (bsTC (bsSwI i))).symm
        have h1 : β (bsTC i) ^ 3 = 1 := by rw [← map_pow, hc1, map_one]
        rw [hb] at h1
        have h2 : zC ^ 2 = 1 := by rw [← orderOf_zC]; exact pow_orderOf_eq_one zC
        exact zC_ne_one (bs_cube_aux (G := lyC) hcomm h2 hc2 h1)
    · by_cases h9' : i = 9
      · subst h9'
        have e : bsTC 9 = zC := Subtype.ext (by simp [bsTC, bsT, zC])
        rw [e, show bsSwI 9 = 9 from rfl]
        exact Subtype.ext ((hαβ zC).trans hz)
      · have e1 : bsTC i = 1 := Subtype.ext (by simp [bsTC, bsT, h9, h9'])
        have e2 : bsSwI i = i := by unfold bsSwI; split_ifs <;> omega
        rw [e2, e1, map_one]
  have hTα : ∀ i, α (bsT i) = bsT (bsSwI i) := by
    intro i
    have h := hαβ (bsTC i)
    rw [hT i] at h
    exact h.symm
  have hW : ∀ w, α (evalWord bsT w) = evalWord (fun i => bsT (bsSwI i)) w := by
    intro w
    induction w with
    | nil => rw [evalWord_nil, evalWord_nil, map_one]
    | cons l w ih =>
      rw [evalWord_cons, evalWord_cons, map_mul, ih]
      congr 1
      unfold letterVal
      split_ifs
      · exact hTα _
      · rw [map_inv, hTα]
  have hF : α bsF = bsF := by
    rw [← bsF_eq, hW]
    exact evalWord_congr fun l hl => by rw [bs_wf_letters l hl]
  set y := α bsG with hy
  have hyz : y * lyz = bsF * y := by
    have h := congrArg α bsG_mul_lyz
    rwa [map_mul, map_mul, hz, hF] at h
  have hc : bsG⁻¹ * y ∈ lyC := by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    have e : lyz * bsG⁻¹ = bsG⁻¹ * bsF := by
      rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, bsG_mul_lyz, mul_assoc, mul_inv_cancel, mul_one]
    rw [← mul_assoc, e, mul_assoc, mul_assoc, hyz]
  set c : lyC := ⟨bsG⁻¹ * y, hc⟩ with hcdef
  have hyc : y = bsG * (c : J) := by
    rw [hcdef]
    simp only
    rw [← mul_assoc, mul_inv_cancel, one_mul]
  have hkey : evalWord bsT bsUN * (c : J) = (c : J) * evalWord (fun i => bsT (bsSwI i)) bsVN := by
    have h := congrArg α bsWm_mul_G
    rw [map_mul, map_mul, hW, hW, ← hy, hyc, ← mul_assoc, bsWm_swap_mul_G, mul_assoc,
      mul_assoc] at h
    exact mul_left_cancel h
  have hkeyC : evalWord bsTC bsUN * c = c * evalWord (fun i => bsTC (bsSwI i)) bsVN := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_evalWord_lyC, coe_evalWord_lyC]
    exact hkey
  have himg := congrArg imgC hkeyC
  rw [map_mul, map_mul, map_evalWord, map_evalWord] at himg
  simp only [imgC_bsTC] at himg
  set σ := imgC c
  have hx := congrArg (fun p : Equiv.Perm (Fin 11) => p (σ⁻¹ 5)) himg
  simp only [Equiv.Perm.coe_mul, Function.comp_apply] at hx
  have h5 : σ (σ⁻¹ 5) = 5 := σ.apply_symm_apply 5
  rw [h5, show evalWord (fun i => bsCyc i) bsUN 5 = 5 from bs_rho_fix] at hx
  exact bs_lam_fixfree (σ⁻¹ 5) (Equiv.Perm.eq_inv_iff_eq.2 hx.symm)

end CFSG.Sporadic.LySchreier

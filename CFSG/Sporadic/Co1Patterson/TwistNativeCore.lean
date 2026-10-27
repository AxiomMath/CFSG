module

public import CFSG.Sporadic.Co1Patterson.TwistNativeAct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson.TwistNative

open Subgroup CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier CFSG.LargeExtraspecial
open CFSG.Blueprint (NativeSporadic.Co1)
open CFSG.EvenSmallLie.OmegaEight (ind bNat qNat eichNat)

theorem colsMul_getD_lt {m n : List ℕ} (hm : ∀ k, m.getD k 0 < 256) (k : ℕ) :
    (colsMul m n).getD k 0 < 256 := by
  by_cases hk : k < 8
  · rw [colsMul, List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map,
      List.getElem_range]
    exact colsApply_lt hm _
  · rw [List.getD_eq_default _ _ (by simp [colsMul]; omega)]
    norm_num

theorem idCols_getD_lt (k : ℕ) : idCols.getD k 0 < 256 := by
  by_cases hk : k < 8
  · rw [idCols, List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map,
      List.getElem_range]
    exact Nat.pow_lt_pow_right (by norm_num) hk |>.trans_le (by norm_num)
  · rw [List.getD_eq_default _ _ (by simp [idCols]; omega)]
    norm_num

theorem mprodCols_getD_lt (c k : ℕ) : (mprodCols c).getD k 0 < 256 := by
  have key : ∀ (l : List ℕ) (m : List ℕ), (∀ i ∈ l, i < 6) → (∀ k, m.getD k 0 < 256) →
      ∀ k, (l.foldl (fun acc i => if c.testBit i then colsMul acc (wordCols (uWords.getD i []))
        else acc) m).getD k 0 < 256 := by
    intro l
    induction l with
    | nil => exact fun m _ hm => hm
    | cons i l ih =>
      intro m hl hm
      simp only [List.foldl_cons]
      refine ih _ (fun j hj => hl j (List.mem_cons_of_mem _ hj)) ?_
      by_cases hb : c.testBit i
      · rw [ite_eq_left hb]
        exact colsMul_getD_lt hm
      · rw [ite_eq_right hb]
        exact hm
  exact key (List.range 6) idCols (fun i hi => List.mem_range.1 hi) idCols_getD_lt k

theorem hasCols_foldl_if (l : List ℕ) (p : ℕ → Bool) (f : ℕ → L₀) (g : ℕ → List ℕ)
    (hfg : ∀ i ∈ l, HasCols ((f i : L₀) : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) (g i))
    {a : L₀} {m : List ℕ}
    (ha : HasCols ((a : L₀) : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) m) :
    HasCols (((l.foldl (fun acc i => if p i then acc * f i else acc) a : L₀) :
      (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) : (Fin 8 → ZMod 2) →ₗ[ZMod 2] _)
      (l.foldl (fun acc i => if p i then colsMul acc (g i) else acc) m) := by
  induction l generalizing a m with
  | nil => exact ha
  | cons i l ih =>
    simp only [List.foldl_cons]
    refine ih (fun j hj => hfg j (List.mem_cons_of_mem _ hj)) ?_
    by_cases hb : p i
    · rw [ite_eq_left hb, ite_eq_left hb]
      exact hasCols_mul ha (hfg i List.mem_cons_self)
    · rw [ite_eq_right hb, ite_eq_right hb]
      exact ha

theorem eq_xor_of_land {u k : ℕ} (hu : u < 256) (hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 5 ∨ k = 6 ∨
    k = 7) (h : u &&& 254 = 2 ^ k) : u = 2 ^ k ^^^ (u.testBit 0).toNat := by
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> interval_cases u <;> simp_all

theorem mem_allBools : ∀ {n : ℕ} (l : List Bool), l.length = n → l ∈ allBools n
  | 0, [], _ => by simp [allBools]
  | n + 1, b :: l, h => by
    rw [allBools, List.mem_flatMap]
    refine ⟨l, mem_allBools l (by simpa using h), ?_⟩
    cases b <;> simp

theorem mem_aList {p : ℕ × ℕ} :
    p ∈ aList ↔ p.1 < 256 ∧ p.1.testBit 4 = false ∧ (p.2 = 0 ∨ p.2 = 1) := by
  obtain ⟨c, d⟩ := p
  simp only [aList, List.mem_flatMap, List.mem_filter, List.mem_range, Bool.not_eq_eq_eq_not,
    Bool.not_true, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨c', ⟨hc, hb⟩, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
    · exact ⟨hc, hb, Or.inl rfl⟩
    · exact ⟨hc, hb, Or.inr rfl⟩
  · rintro ⟨hc, hb, rfl | rfl⟩
    · exact ⟨c, ⟨hc, hb⟩, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨c, ⟨hc, hb⟩, Or.inr ⟨rfl, rfl⟩⟩

theorem uOK_parts :
    (∀ c < 64, ∀ v ∈ wVecs, actW (mprodCols c) v = v) ∧
    ∀ c < 64, ∀ c' < 64, colsApply (mprodCols c) 16 = colsApply (mprodCols c') 16 → c = c' := by
  have h := tw_u_check
  simp only [uOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  refine ⟨h.1, fun c hc c' hc' he => ?_⟩
  rcases h.2 c hc c' hc' with h1 | h1
  · exact absurd he h1
  · exact h1

theorem isoCols_congr {m m' : List ℕ} (h : ∀ k < 8, m.getD k 0 = m'.getD k 0) :
    isoCols m = isoCols m' := by
  unfold isoCols
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  refine forall₂_congr fun j hj => ?_
  rw [h j (List.mem_range.1 hj)]
  simp only [Bool.and_eq_true, List.all_eq_true]
  refine and_congr Iff.rfl (forall₂_congr fun k hk => ?_)
  rw [h k (List.mem_range.1 hk)]

theorem uSetOK_parts : ∀ bs ∈ allBools 6, ∀ mu < 256,
    isoCols (candCols bs mu) = true →
      ∃ c < 64, ∀ k < 8, (mprodCols c).getD k 0 = (candCols bs mu).getD k 0 := by
  have h := tw_uSet_check
  simp only [uSetOK, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    List.any_eq_true, beq_iff_eq] at h
  intro bs hbs mu hmu hiso
  rcases h bs hbs mu hmu with h1 | ⟨c, hc, hk⟩
  · rw [hiso] at h1
    exact absurd h1 (by decide)
  · exact ⟨c, hc, hk⟩

theorem phi_yprodH (c : ℕ) : typeSystemC.φ (yprodH c) = 1 :=
  (Setting.phiV₀_eq_one_iff nativeSetting coordIso nativeOmega (yprodH c)).2 (yprodH_mem_QG c)

theorem phi_aElt (p : ℕ × ℕ) : typeSystemC.φ (aElt p) = 1 := by
  rw [aElt]
  split_ifs
  · rw [map_mul, phi_yprodH, typeSystemC.φ_z, one_mul]
  · exact phi_yprodH _

theorem vec_aElt (p : ℕ × ℕ) : typeSystemC.vec (aElt p) = bv p.1 := by
  rw [aElt]
  split_ifs
  · exact vec_yprodH_mul_z _
  · exact vec_yprodH _

theorem eq_yprodH_of_phi {q : centralizer ({aNC} : Set NativeSporadic.Co1)}
    (hq : typeSystemC.φ q = 1) :
    q = yprodH (enc (typeSystemC.vec q)) ∨
      q = yprodH (enc (typeSystemC.vec q)) * typeSystemC.z := by
  have hφ : typeSystemC.φ (q⁻¹ * yprodH (enc (typeSystemC.vec q))) = 1 := by
    rw [map_mul, map_inv, hq, inv_one, one_mul, phi_yprodH]
  have hv : typeSystemC.vec (q⁻¹ * yprodH (enc (typeSystemC.vec q))) = 0 := by
    rw [typeSystemC.vec_mul q⁻¹ _ (by rw [map_inv, hq, inv_one]) (phi_yprodH _),
      typeSystemC.vec_inv hq, vec_yprodH, bv_enc]
    exact vec_add_self _
  rcases (typeSystemC.vec_eq_zero (q⁻¹ * yprodH (enc (typeSystemC.vec q))) hφ).1 hv with h1 | h1
  · exact Or.inl (inv_mul_eq_one.1 h1)
  · right
    have h2 : yprodH (enc (typeSystemC.vec q)) = q * typeSystemC.z := by
      rw [← h1, mul_inv_cancel_left]
    calc q = q * typeSystemC.z * typeSystemC.z := by
          rw [mul_assoc, typeSystemC.z_mul_self, mul_one]
      _ = yprodH (enc (typeSystemC.vec q)) * typeSystemC.z := by rw [h2]

theorem aElt_mem_K₀ {p : ℕ × ℕ} (hp : p ∈ aList) : aElt p ∈ K₀ := by
  obtain ⟨hc, hb, -⟩ := mem_aList.1 hp
  have hy : yprodH p.1 * yH 0 = yH 0 * yprodH p.1 := by
    apply centEmb_injective
    rw [map_mul, map_mul, centEmb_yprodH, centEmb_yH]
    exact (yprodG_comm_iff hc (show 4 < 8 by norm_num)).2 hb
  refine mem_K₀.2 ?_
  have hz := typeSystemC.z_comm (yH 0)
  rw [aElt]
  split_ifs
  · calc yprodH p.1 * typeSystemC.z * yH 0 = yprodH p.1 * (yH 0 * typeSystemC.z) := by
          rw [mul_assoc, hz]
      _ = yH 0 * (yprodH p.1 * typeSystemC.z) := by rw [← mul_assoc, hy, mul_assoc]
  · exact hy

theorem hcH_mem_K₀ (c : ℕ) : hcH c ∈ K₀ := hcH_mem_centralizer c

theorem hasCols_hcH (c : ℕ) :
    HasCols (((typeSystemC.φ (hcH c) : L₀) : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) :
      (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2)) (mprodCols c) := by
  rw [phi_hcH]
  exact hasCols_foldl_if _ _ _ _ (fun i hi => hasCols_eichWord _
    (uWords_lt i (List.mem_range.1 hi))) hasCols_one

@[expose] noncomputable def R₀ : Subgroup (centralizer ({aNC} : Set NativeSporadic.Co1)) where
  carrier := {h | h ∈ K₀ ∧ ∀ x ∈ W₀, actV h x = x}
  mul_mem' {h h'} hh hh' := ⟨mul_mem hh.1 hh'.1, fun x hx => by
    rw [actV_mul hh.1, hh'.2 x hx, hh.2 x hx]⟩
  one_mem' := ⟨one_mem _, fun _ hx => actV_one hx⟩
  inv_mem' {h} hh := ⟨inv_mem hh.1, fun x hx => by
    have h1 := actV_mul hh.1 (h' := h⁻¹) x
    rw [mul_inv_cancel, actV_one hx, hh.2 _ (actV_mem (inv_mem hh.1) hx)] at h1
    exact h1.symm⟩

theorem R₀_le_K₀ : R₀ ≤ K₀ := fun _ hh => hh.1

theorem conj_mem_R₀ {k : centralizer ({aNC} : Set NativeSporadic.Co1)} (hk : k ∈ K₀)
    {h : centralizer ({aNC} : Set NativeSporadic.Co1)} (hh : h ∈ R₀) : k * h * k⁻¹ ∈ R₀ :=
  ⟨mul_mem (mul_mem hk hh.1) (inv_mem hk), fun x hx => by
    rw [actV_mul (mul_mem hk hh.1), actV_mul hk, hh.2 _ (actV_mem (inv_mem hk) hx),
      ← actV_mul hk, mul_inv_cancel, actV_one hx]⟩

theorem le_R₀ {P : Subgroup (centralizer ({aNC} : Set NativeSporadic.Co1))} (hPK : P ≤ K₀)
    (hnorm : ∀ k ∈ K₀, ∀ p ∈ P, k * p * k⁻¹ ∈ P) (hP : IsPGroup 2 P) : P ≤ R₀ :=
  fun p hp => ⟨hPK hp, actV_eq_of_isPGroup hPK hnorm hP p hp⟩

theorem hcH_mul_aElt_mem {c : ℕ} (hc : c < 64) {p : ℕ × ℕ} (hp : p ∈ aList) :
    hcH c * aElt p ∈ R₀ := by
  refine ⟨mul_mem (hcH_mem_K₀ c) (aElt_mem_K₀ hp), fun x hx => ?_⟩
  rw [actV_mul (hcH_mem_K₀ c)]
  have ha : actV (aElt p) x = x := by
    rw [actV, phi_aElt, OneMemClass.coe_one, LinearEquiv.coe_one, id, clean_of_mem hx]
  rw [ha, ← bv_enc x]
  have h1 := (hasCols_hcH c).apply (enc x)
  simp only [LinearEquiv.coe_coe] at h1
  rw [actV, h1, clean_bv]
  exact congrArg bv (uOK_parts.1 c hc _ (enc_mem_wVecs hx))

theorem exists_c_of_mem_R₀ {h : centralizer ({aNC} : Set NativeSporadic.Co1)} (hh : h ∈ R₀) :
    ∃ c < 64, typeSystemC.φ h = typeSystemC.φ (hcH c) := by
  set f : (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2) :=
    (((typeSystemC.φ h : L₀) : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) :
      (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2)) with hf
  have hfv : ∀ k < 8, f (bv (2 ^ k)) = bv ((cols f).getD k 0) := fun k hk =>
    (hasCols_cols f) k hk
  have hlt : ∀ k, (cols f).getD k 0 < 256 := cols_getD_lt f
  have h0 : (cols f).getD 0 0 = 1 := by
    rw [cols_getD f (by norm_num), pow_zero]
    exact (congrArg enc (phi_e₀ hh.1)).trans (enc_bv (by norm_num))
  have hW : ∀ k, (k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 5 ∨ k = 6 ∨ k = 7) →
      (cols f).getD k 0 = 2 ^ k ^^^ (((cols f).getD k 0).testBit 0).toNat := by
    intro k hk
    have hk8 : k < 8 := by omega
    have hmem : 2 ^ k ∈ wVecs := by
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have h1 := hh.2 _ (bv_mem_W₀ hmem)
    have hfk : ((typeSystemC.φ h : L₀) : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2))
        (bv (2 ^ k)) = bv ((cols f).getD k 0) := hfv k hk8
    rw [actV, hfk, clean_bv] at h1
    have h2 := bv_inj (lt_of_le_of_lt Nat.and_le_right (by norm_num))
      (Nat.pow_lt_pow_right (by norm_num) hk8 |>.trans_le (by norm_num)) h1
    exact eq_xor_of_land (hlt k) hk h2
  set bs : List Bool := [((cols f).getD 1 0).testBit 0, ((cols f).getD 2 0).testBit 0,
    ((cols f).getD 3 0).testBit 0, ((cols f).getD 5 0).testBit 0, ((cols f).getD 6 0).testBit 0,
    ((cols f).getD 7 0).testBit 0]
  have hagree : ∀ k < 8, (candCols bs ((cols f).getD 4 0)).getD k 0 = (cols f).getD k 0 := by
    intro k hk
    interval_cases k
    · exact h0.symm
    · exact (hW 1 (by omega)).symm
    · exact (hW 2 (by omega)).symm
    · exact (hW 3 (by omega)).symm
    · rfl
    · exact (hW 5 (by omega)).symm
    · exact (hW 6 (by omega)).symm
    · exact (hW 7 (by omega)).symm
  have hiso : isoCols (cols f) = true := by
    simp only [isoCols, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq]
    intro j hj
    refine ⟨ind_injective ?_, fun k hk => ind_injective ?_⟩
    · rw [← q₀_bv, ← q₀_bv, ← hfv j hj]
      exact q₀_L₀ _ _
    · rw [← polar_q₀_bv, ← polar_q₀_bv, ← hfv j hj, ← hfv k hk]
      exact polar_L₀ _ _ _
  obtain ⟨c, hc, hck⟩ := uSetOK_parts bs (mem_allBools bs rfl) _ (hlt 4)
    ((isoCols_congr hagree).trans hiso)
  refine ⟨c, hc, Subtype.ext (LinearEquiv.toLinearMap_injective (HasCols.ext
    (m := mprodCols c) (fun k hk => ?_) (hasCols_hcH c)))⟩
  rw [hfv k hk, hck k hk, hagree k hk]

theorem testBit_four_of_comm {q : centralizer ({aNC} : Set NativeSporadic.Co1)}
    (hq : typeSystemC.φ q = 1) (hk : q ∈ K₀) :
    (enc (typeSystemC.vec q)).testBit 4 = false := by
  set c := enc (typeSystemC.vec q) with hcdef
  have hc : c < 256 := enc_lt _
  have hqc : q * yH 0 = yH 0 * q := mem_K₀.1 hk
  have hy : yprodH c * yH 0 = yH 0 * yprodH c := by
    rcases eq_yprodH_of_phi hq with h1 | h1
    · rw [← hcdef] at h1
      rw [← h1]
      exact hqc
    · rw [← hcdef] at h1
      have h2 : yprodH c = q * typeSystemC.z := by
        rw [h1, mul_assoc, typeSystemC.z_mul_self, mul_one]
      rw [h2, mul_assoc, ← typeSystemC.z_comm (yH 0), ← mul_assoc, hqc, mul_assoc]
  have h3 := congrArg centEmb hy
  rw [map_mul, map_mul, centEmb_yprodH, centEmb_yH] at h3
  exact (yprodG_comm_iff hc (show 4 < 8 by norm_num)).1 h3

theorem mem_R₀_iff {h : centralizer ({aNC} : Set NativeSporadic.Co1)} :
    h ∈ R₀ ↔ ∃ c < 64, ∃ p ∈ aList, h = hcH c * aElt p := by
  refine ⟨fun hh => ?_, fun ⟨c, hc, p, hp, he⟩ => he ▸ hcH_mul_aElt_mem hc hp⟩
  obtain ⟨c, hc, hφ⟩ := exists_c_of_mem_R₀ hh
  set q := (hcH c)⁻¹ * h
  have hq : typeSystemC.φ q = 1 := by rw [map_mul, map_inv, hφ, inv_mul_cancel]
  have hqK : q ∈ K₀ := mul_mem (inv_mem (hcH_mem_K₀ c)) hh.1
  have hb := testBit_four_of_comm hq hqK
  have hlt := enc_lt (typeSystemC.vec q)
  have hhq : h = hcH c * q := by rw [mul_inv_cancel_left]
  rcases eq_yprodH_of_phi hq with h1 | h1
  · refine ⟨c, hc, (enc (typeSystemC.vec q), 0), mem_aList.2 ⟨hlt, hb, Or.inl rfl⟩, ?_⟩
    rw [hhq, aElt, ite_eq_right (by norm_num)]
    exact congrArg _ h1
  · refine ⟨c, hc, (enc (typeSystemC.vec q), 1), mem_aList.2 ⟨hlt, hb, Or.inr rfl⟩, ?_⟩
    rw [hhq, aElt, ite_eq_left rfl]
    exact congrArg _ h1

theorem eq_of_phi_hcH {c c' : ℕ} (hc : c < 64) (hc' : c' < 64)
    (hφ : typeSystemC.φ (hcH c) = typeSystemC.φ (hcH c')) : c = c' := by
  have h16 : ((typeSystemC.φ (hcH c) : L₀) : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2))
      (bv 16) = ((typeSystemC.φ (hcH c') : L₀) :
        (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) (bv 16) := by rw [hφ]
  have e1 := (hasCols_hcH c).apply 16
  have e2 := (hasCols_hcH c').apply 16
  simp only [LinearEquiv.coe_coe] at e1 e2
  rw [e1, e2] at h16
  exact uOK_parts.2 c hc c' hc' (bv_inj (colsApply_lt (mprodCols_getD_lt c) _)
    (colsApply_lt (mprodCols_getD_lt c') _) h16)

theorem eq_of_aElt_eq {p p' : ℕ × ℕ} (hp : p ∈ aList) (hp' : p' ∈ aList)
    (ha : aElt p = aElt p') : p = p' := by
  obtain ⟨h1, -, h2⟩ := mem_aList.1 hp
  obtain ⟨h1', -, h2'⟩ := mem_aList.1 hp'
  have hv := congrArg typeSystemC.vec ha
  rw [vec_aElt, vec_aElt] at hv
  have hfst := bv_inj h1 h1' hv
  refine Prod.ext hfst ?_
  have hz := typeSystemC.z_ne_one
  rcases h2 with h2 | h2 <;> rcases h2' with h2' | h2'
  · rw [h2, h2']
  · exfalso
    have e : aElt p = yprodH p.1 := by rw [aElt, h2]; rfl
    have e' : aElt p' = yprodH p.1 * typeSystemC.z := by rw [aElt, h2', hfst]; rfl
    rw [e, e'] at ha
    exact hz (mul_left_cancel (ha.symm.trans (mul_one _).symm))
  · exfalso
    have e : aElt p = yprodH p.1 * typeSystemC.z := by rw [aElt, h2]; rfl
    have e' : aElt p' = yprodH p.1 := by rw [aElt, h2', hfst]; rfl
    rw [e, e'] at ha
    exact hz (mul_left_cancel (ha.trans (mul_one _).symm))
  · rw [h2, h2']

theorem hcH_mul_aElt_inj {c c' : ℕ} (hc : c < 64) (hc' : c' < 64) {p p' : ℕ × ℕ}
    (hp : p ∈ aList) (hp' : p' ∈ aList) (h : hcH c * aElt p = hcH c' * aElt p') :
    c = c' ∧ p = p' := by
  have hφ : typeSystemC.φ (hcH c) = typeSystemC.φ (hcH c') := by
    have := congrArg typeSystemC.φ h
    rwa [map_mul, map_mul, phi_aElt, phi_aElt, mul_one, mul_one] at this
  have hcc := eq_of_phi_hcH hc hc' hφ
  subst hcc
  exact ⟨rfl, eq_of_aElt_eq hp hp' (mul_left_cancel h)⟩

end CFSG.Sporadic.Co1Patterson.TwistNative

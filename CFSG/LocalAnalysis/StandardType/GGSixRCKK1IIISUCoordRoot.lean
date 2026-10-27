module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIISUCoord
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2GeoSU
public import CFSG.Quasithin.Vol2.KGFactC31RuRef

public section

namespace CFSG.StandardType.RCKK1IIISU

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.BorelTits
  CFSG.LieType.RootSystem CFSG.Assembly CFSG.StandardType.RCKC1 CFSG.Open

variable {k : ℕ}

private noncomputable def suHom (hk : 4 ≤ k) :
    Multiplicative (Fin 4 → ZMod 2) →* SUG k :=
  MonoidHom.mk' (fun v => suZ hk v.toAdd) (fun v w => (suZ_add hk v.toAdd w.toAdd).symm)

private theorem suHom_apply (hk : 4 ≤ k) (v : Multiplicative (Fin 4 → ZMod 2)) :
    suHom hk v = suZ hk v.toAdd := rfl

private theorem suHom_injective (hk : 4 ≤ k) : Function.Injective (suHom hk) := by
  intro v w h
  have h' : suZ hk v.toAdd = suZ hk w.toAdd := h
  exact Multiplicative.toAdd.injective (suZ_injective hk h')

@[expose] noncomputable def suR (hk : 4 ≤ k) : SUG k := suZ hk ![0, 1, 0, 0]

@[expose] noncomputable def suV (hk : 4 ≤ k) : Subgroup (SUG k) :=
  Subgroup.closure {suZ hk ![0, 1, 0, 0], suZ hk ![0, 0, 1, 0]}

theorem suR_mem_suV (hk : 4 ≤ k) : suR hk ∈ suV hk := by
  rw [suR]
  exact Subgroup.subset_closure (by simp)

theorem suR_ne_one (hk : 4 ≤ k) : suR hk ≠ 1 := by
  intro h
  have h0 : (![0, 1, 0, 0] : Fin 4 → ZMod 2) = 0 :=
    suZ_injective hk (by rw [← suR, h, suZ_zero])
  have h1 := congrFun h0 1
  simp at h1

theorem suV_le_suZ0 (hk : 4 ≤ k) : suV hk ≤ suZ0 hk := by
  rw [suV, Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | rfl
  · exact ⟨Multiplicative.ofAdd ![0, 1, 0, 0], rfl⟩
  · exact ⟨Multiplicative.ofAdd ![0, 0, 1, 0], rfl⟩

theorem isElemAbelian_suV (hk : 4 ≤ k) : IsElemAbelian 2 (suV hk) := by
  change IsMulCommutative (suV hk) ∧ ∀ x ∈ suV hk, x ^ 2 = 1
  constructor
  · refine ⟨⟨?_⟩⟩
    intro x y
    obtain ⟨v, hv⟩ := suV_le_suZ0 hk x.2
    obtain ⟨w, hw⟩ := suV_le_suZ0 hk y.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hv, ← hw]
    change suZ hk v.toAdd * suZ hk w.toAdd = suZ hk w.toAdd * suZ hk v.toAdd
    rw [suZ_add, suZ_add, add_comm]
  · intro x hx
    obtain ⟨v, hv⟩ := suV_le_suZ0 hk hx
    rw [← hv]
    change (suZ hk v.toAdd) ^ 2 = 1
    rw [sq, suZ_add]
    have hv2 : v.toAdd + v.toAdd = 0 := by
      funext i
      exact (by decide : ∀ a : ZMod 2, a + a = 0) (v.toAdd i)
    rw [hv2, suZ_zero]

private def suWm : Subgroup (Multiplicative (Fin 4 → ZMod 2)) where
  carrier := {v | v.toAdd 0 = 0 ∧ v.toAdd 3 = 0}
  mul_mem' := by
    intro a b ha hb
    obtain ⟨ha0, ha3⟩ := ha
    obtain ⟨hb0, hb3⟩ := hb
    refine ⟨?_, ?_⟩
    · change a.toAdd 0 + b.toAdd 0 = 0
      rw [ha0, hb0, add_zero]
    · change a.toAdd 3 + b.toAdd 3 = 0
      rw [ha3, hb3, add_zero]
  one_mem' := by refine ⟨?_, ?_⟩ <;> simp
  inv_mem' := by
    intro a ha
    obtain ⟨ha0, ha3⟩ := ha
    refine ⟨?_, ?_⟩
    · change -(a.toAdd 0) = 0
      rw [ha0, neg_zero]
    · change -(a.toAdd 3) = 0
      rw [ha3, neg_zero]

private noncomputable def suWmEquiv : suWm ≃ ZMod 2 × ZMod 2 where
  toFun v := (v.1.toAdd 1, v.1.toAdd 2)
  invFun p := ⟨Multiplicative.ofAdd ![0, p.1, p.2, 0], by
    refine ⟨?_, ?_⟩ <;> simp⟩
  left_inv v := by
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext i
    have hv0 : v.1.toAdd 0 = 0 := v.2.1
    have hv3 : v.1.toAdd 3 = 0 := v.2.2
    fin_cases i <;> simp [hv0, hv3]
  right_inv p := by
    ext <;> simp

private theorem suWm_card : Nat.card suWm = 4 := by
  rw [Nat.card_congr suWmEquiv, Nat.card_prod]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

private theorem suV_eq_map (hk : 4 ≤ k) : suV hk = suWm.map (suHom hk) := by
  rw [suV]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact ⟨Multiplicative.ofAdd ![0, 1, 0, 0], by refine ⟨?_, ?_⟩ <;> simp, rfl⟩
    · exact ⟨Multiplicative.ofAdd ![0, 0, 1, 0], by refine ⟨?_, ?_⟩ <;> simp, rfl⟩
  · rintro x ⟨v, hv, rfl⟩
    have hv_eq : v.toAdd = (v.toAdd 1) • ![0, 1, 0, 0] + (v.toAdd 2) • ![0, 0, 1, 0] := by
      funext i
      fin_cases i <;> simp [hv.1, hv.2]
    rw [suHom_apply, hv_eq, ← suZ_add]
    refine Subgroup.mul_mem _ ?_ ?_
    · have h1 : v.toAdd 1 = 0 ∨ v.toAdd 1 = 1 :=
        (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (v.toAdd 1)
      rcases h1 with h1 | h1
      · rw [h1, zero_smul, suZ_zero]; exact Subgroup.one_mem _
      · rw [h1, one_smul]; exact Subgroup.subset_closure (by simp)
    · have h2 : v.toAdd 2 = 0 ∨ v.toAdd 2 = 1 :=
        (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (v.toAdd 2)
      rcases h2 with h2 | h2
      · rw [h2, zero_smul, suZ_zero]; exact Subgroup.one_mem _
      · rw [h2, one_smul]; exact Subgroup.subset_closure (by simp)

theorem card_suV (hk : 4 ≤ k) : Nat.card (suV hk) = 4 := by
  rw [suV_eq_map hk, Subgroup.card_map_of_injective (suHom_injective hk), suWm_card]

theorem mem_suV_iff (hk : 4 ≤ k) {x : SUG k} :
    x ∈ suV hk ↔ ∃ a b : ZMod 2, x = suZ hk ![0, a, b, 0] := by
  change x ∈ (suV hk : Set (SUG k)) ↔ _
  rw [suV_eq_map]
  constructor
  · intro hx
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hx
    refine ⟨v.toAdd 1, v.toAdd 2, ?_⟩
    rw [suHom_apply]
    have hv_eq : v.toAdd = ![0, v.toAdd 1, v.toAdd 2, 0] := by
      funext i
      fin_cases i <;> simp [hv.1, hv.2]
    rw [hv_eq]
    simp
  · rintro ⟨a, b, rfl⟩
    refine ⟨Multiplicative.ofAdd ![0, a, b, 0], ?_, ?_⟩
    · refine ⟨?_, ?_⟩ <;> simp
    · rw [suHom_apply]
      rfl

private theorem rckSUr_card : Nat.card SUF = 4 := by
  rw [GaloisField.card 2 (2 * 1) (by norm_num)]
  norm_num
private theorem rckSUr_card_sq : Nat.card SUF = (2 ^ 1) ^ 2 := by
  rw [rckSUr_card]; norm_num
private theorem rckSUr_sigma_involutive : ∀ c : SUF, SUσ (SUσ c) = c :=
  unitaryInvolution_involutive rckSUr_card_sq
private theorem rckSUr_sigma_apply (c : SUF) : SUσ c = c ^ 2 := by
  rw [SUσ, unitaryInvolution_apply]; norm_num
private theorem rckSUr_neg_eq (x : SUF) : -x = x := by
  have h2 : (2 : SUF) = 0 := CharP.cast_eq_zero SUF 2
  have hxx : x + x = 0 := by rw [← two_mul, h2, zero_mul]
  exact neg_eq_of_add_eq_zero_left hxx
private theorem rckSUr_sI0_ne_sI1 (hk : 4 ≤ k) : sI0 hk ≠ sI1 hk := by
  intro h; have hv := congrArg Fin.val h; simp [sI0, sI1] at hv
private theorem rckSUr_sI0_ne_rev_sI0 (hk : 4 ≤ k) : sI0 hk ≠ Fin.rev (sI0 hk) := by
  intro h; have hv := congrArg Fin.val h; simp [sI0, Fin.val_rev] at hv; omega
private theorem rckSUr_sI1_ne_rev_sI1 (hk : 4 ≤ k) : sI1 hk ≠ Fin.rev (sI1 hk) := by
  intro h; have hv := congrArg Fin.val h; simp [sI1, Fin.val_rev] at hv; omega
private theorem rckSUr_sI0_ne_rev_sI1 (hk : 4 ≤ k) : sI0 hk ≠ Fin.rev (sI1 hk) := by
  intro h; have hv := congrArg Fin.val h; simp [sI0, sI1, Fin.val_rev] at hv; omega
private theorem rckSUr_sI1_ne_rev_sI0 (hk : 4 ≤ k) : sI1 hk ≠ Fin.rev (sI0 hk) := by
  intro h; have hv := congrArg Fin.val h; simp [sI0, sI1, Fin.val_rev] at hv; omega
private theorem rckSUr_rev_sI1_ne_sI1 (hk : 4 ≤ k) : Fin.rev (sI1 hk) ≠ sI1 hk :=
  (rckSUr_sI1_ne_rev_sI1 hk).symm
private theorem rckSUr_rev_sI1_ne_sI0 (hk : 4 ≤ k) : Fin.rev (sI1 hk) ≠ sI0 hk :=
  fun h => rckSUr_sI0_ne_rev_sI1 hk h.symm
private theorem rckSUr_rev_sI1_ne_rev_sI0 (hk : 4 ≤ k) :
    Fin.rev (sI1 hk) ≠ Fin.rev (sI0 hk) :=
  fun h => rckSUr_sI0_ne_sI1 hk (Fin.rev_injective h).symm
private theorem rckSUr_rev_sI1_ne_rev_rev_sI1 (hk : 4 ≤ k) :
    Fin.rev (sI1 hk) ≠ Fin.rev (Fin.rev (sI1 hk)) := by
  simpa only [Fin.rev_rev] using rckSUr_rev_sI1_ne_sI1 hk
private theorem rckSUr_suOmega_ne_zero : suOmega ≠ 0 := by
  intro h
  have hspec := suOmega_spec
  rw [h] at hspec
  norm_num at hspec
private theorem rckSUr_suOmega_sq : suOmega ^ 2 = suOmega + 1 := by
  have h := suOmega_spec
  have h2 : (2 : SUF) = 0 := CharP.cast_eq_zero SUF 2
  linear_combination h - (suOmega + 1) * h2
private theorem rckSUr_pow_three (c : SUF) (hc : c ≠ 0) : c ^ 3 = 1 := by
  haveI : Fintype SUF := Fintype.ofFinite SUF
  have h := FiniteField.pow_card_sub_one_eq_one c hc
  rwa [← Nat.card_eq_fintype_card, rckSUr_card] at h
private theorem rckSUr_inv_eq_sq (c : SUF) (hc : c ≠ 0) : c⁻¹ = c ^ 2 :=
  inv_eq_of_mul_eq_one_right (by
    rw [← pow_succ', show (2 : ℕ) + 1 = 3 by norm_num, rckSUr_pow_three c hc])
private theorem rckSUr_inv_sq (c : SUF) (hc : c ≠ 0) : (c ^ 2)⁻¹ = c :=
  inv_eq_of_mul_eq_one_right (by
    rw [← pow_succ, show (2 : ℕ) + 1 = 3 by norm_num, rckSUr_pow_three c hc])
private theorem rckSUr_shortTorusFun_ne_zero (hk : 4 ≤ k) {c : SUF} (hc : c ≠ 0)
    (s : Fin k) : shortTorusFun SUσ (sI0 hk) (sI1 hk) c s ≠ 0 := by
  have hc' : SUσ c ≠ 0 := (map_ne_zero SUσ).mpr hc
  simp only [shortTorusFun]
  split_ifs <;> simp [hc, hc']
private noncomputable def rckSUr_corner (hk : 4 ≤ k) (x : SUF) :
    Matrix (Fin k) (Fin k) SUF :=
  1 + Matrix.single (sI0 hk) (Fin.rev (sI1 hk)) x +
    Matrix.single (sI1 hk) (Fin.rev (sI0 hk)) (SUσ x)
private theorem rckSUr_mat_neg_eq (M : Matrix (Fin k) (Fin k) SUF) : -M = M := by
  ext i j
  rw [Matrix.neg_apply]
  exact rckSUr_neg_eq (M i j)
private theorem rckSUr_corner_eq_rootMatrix (hk : 4 ≤ k) (x : SUF) :
    rckSUr_corner hk x = rootMatrix SUσ (sI0 hk) (Fin.rev (sI1 hk)) x := by
  rw [rckSUr_corner, rootMatrix, Fin.rev_rev, sub_eq_add_neg, rckSUr_mat_neg_eq]
private theorem rckSUr_suCorner_eq_corner (hk : 4 ≤ k) (v : Fin 4 → ZMod 2)
    (hv0 : v 0 = 0) (hv3 : v 3 = 0) :
    suCorner hk v = rckSUr_corner hk
      (algebraMap (ZMod 2) SUF (v 1) + algebraMap (ZMod 2) SUF (v 2) * suOmega) := by
  simp [suCorner, rckSUr_corner, hv0, hv3]
private theorem rckSUr_suCorner_suR (hk : 4 ≤ k) :
    suCorner hk ![0, 1, 0, 0] = rckSUr_corner hk 1 := by
  rw [rckSUr_suCorner_eq_corner hk ![0, 1, 0, 0] (by simp) (by simp)]
  simp
theorem coe_suR (hk : 4 ≤ k) :
    (((suR hk : SUG k) : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF) =
      1 + Matrix.single (sI0 hk) (Fin.rev (sI1 hk)) 1 +
        Matrix.single (sI1 hk) (Fin.rev (sI0 hk)) 1 := by
  rw [suR, suZ_val, rckSUr_suCorner_suR, rckSUr_corner, map_one]
theorem exists_coe_eq_of_mem_suV (hk : 4 ≤ k) {w : SUG k} (hw : w ∈ suV hk) :
    ∃ x : SUF, ((w : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF) =
      1 + Matrix.single (sI0 hk) (Fin.rev (sI1 hk)) x +
        Matrix.single (sI1 hk) (Fin.rev (sI0 hk)) (SUσ x) := by
  rw [suV_eq_map hk] at hw
  obtain ⟨v, ⟨hv0, hv3⟩, rfl⟩ := hw
  exact ⟨_, by rw [suHom_apply, suZ_val, rckSUr_suCorner_eq_corner hk _ hv0 hv3]; rfl⟩
private theorem rckSUr_suZ_eq_rootHom (hk : 4 ≤ k) (hσ : ∀ c : SUF, SUσ (SUσ c) = c)
    (x : SUF) (v : Fin 4 → ZMod 2) (hv0 : v 0 = 0) (hv3 : v 3 = 0)
    (hb : algebraMap (ZMod 2) SUF (v 1) + algebraMap (ZMod 2) SUF (v 2) * suOmega = x) :
    suZ hk v = rootHom SUσ hσ (rckSUr_sI0_ne_rev_sI1 hk) (rckSUr_sI0_ne_rev_sI0 hk)
      (rckSUr_rev_sI1_ne_rev_rev_sI1 hk) (Multiplicative.ofAdd x) := by
  apply Subtype.ext
  apply Units.ext
  simp only [suZ_val, coe_rootHom, toAdd_ofAdd, rckSUr_suCorner_eq_corner hk v hv0 hv3, hb,
    rckSUr_corner_eq_rootMatrix]
private theorem rckSUr_diag_single_diag (d : Fin k → SUF)
    (i j : Fin k) (x : SUF) :
    Matrix.diagonal d * Matrix.single i j x *
        Matrix.diagonal (fun s => (d s)⁻¹) =
      Matrix.single i j (d i * x * (d j)⁻¹) := by
  ext p q
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply]
  by_cases h : i = p ∧ j = q
  · obtain ⟨rfl, rfl⟩ := h; simp
  · simp [h]
private theorem rckSUr_diag_conj (hk : 4 ≤ k) {c : SUF} (hc : c ≠ 0) :
    Matrix.diagonal (shortTorusFun SUσ (sI0 hk) (sI1 hk) c) * rckSUr_corner hk 1 *
        Matrix.diagonal (fun s => (shortTorusFun SUσ (sI0 hk) (sI1 hk) c s)⁻¹) =
      rckSUr_corner hk c⁻¹ := by
  have hd0 : ∀ s, shortTorusFun SUσ (sI0 hk) (sI1 hk) c s ≠ 0 :=
    rckSUr_shortTorusFun_ne_zero hk hc
  have hfun : (fun s => shortTorusFun SUσ (sI0 hk) (sI1 hk) c s *
      (shortTorusFun SUσ (sI0 hk) (sI1 hk) c s)⁻¹) = (fun _ => (1 : SUF)) := by
    funext s
    exact mul_inv_cancel₀ (hd0 s)
  have hdiag : Matrix.diagonal (shortTorusFun SUσ (sI0 hk) (sI1 hk) c) *
      Matrix.diagonal (fun s => (shortTorusFun SUσ (sI0 hk) (sI1 hk) c s)⁻¹) =
      (1 : Matrix (Fin k) (Fin k) SUF) := by
    rw [Matrix.diagonal_mul_diagonal, hfun, Matrix.diagonal_one]
  have hba : shortTorusFun SUσ (sI0 hk) (sI1 hk) c (sI0 hk) = c := shortTorusFun_left _ _ _
  have hbb : shortTorusFun SUσ (sI0 hk) (sI1 hk) c (Fin.rev (sI1 hk)) = SUσ c := by
    rw [shortTorusFun]
    rw [if_neg (rckSUr_rev_sI1_ne_sI0 hk), if_neg (rckSUr_rev_sI1_ne_sI1 hk),
      if_neg (rckSUr_rev_sI1_ne_rev_sI0 hk), if_pos rfl]
  have hcc : shortTorusFun SUσ (sI0 hk) (sI1 hk) c (Fin.rev (sI0 hk)) = (SUσ c)⁻¹ := by
    rw [shortTorusFun]
    rw [if_neg (rckSUr_sI0_ne_rev_sI0 hk).symm, if_neg (rckSUr_sI1_ne_rev_sI0 hk).symm,
      if_pos rfl]
  have hdd : shortTorusFun SUσ (sI0 hk) (sI1 hk) c (sI1 hk) = c⁻¹ :=
    shortTorusFun_right (rckSUr_sI0_ne_sI1 hk) c
  have h1 : c * (1 : SUF) * (SUσ c)⁻¹ = c⁻¹ := by
    simp only [rckSUr_sigma_apply]
    field_simp
  have h2 : c⁻¹ * (SUσ 1) * ((SUσ c)⁻¹)⁻¹ = SUσ c⁻¹ := by
    simp only [rckSUr_sigma_apply, map_one, map_inv₀, inv_inv]
    field_simp
    rw [rckSUr_pow_three c hc]
  rw [rckSUr_corner, rckSUr_corner]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one]
  rw [hdiag, rckSUr_diag_single_diag, rckSUr_diag_single_diag]
  rw [hba, hbb, hcc, hdd, h1, h2]
private noncomputable def rckSUr_torus (hk : 4 ≤ k) (c : SUF) : SUG k :=
  shortTorus SUσ rckSUr_sigma_involutive (rckSUr_sI0_ne_sI1 hk)
    (rckSUr_sI0_ne_rev_sI0 hk) (rckSUr_sI1_ne_rev_sI1 hk) c
private theorem rckSUr_torus_mat (hk : 4 ≤ k) {c : SUF} (hc : c ≠ 0) :
    mat SUσ k (rckSUr_torus hk c) =
      Matrix.diagonal (shortTorusFun SUσ (sI0 hk) (sI1 hk) c) := by
  rw [mat_apply, rckSUr_torus]
  exact coe_shortTorus SUσ rckSUr_sigma_involutive (rckSUr_sI0_ne_sI1 hk)
    (rckSUr_sI0_ne_rev_sI0 hk) (rckSUr_sI1_ne_rev_sI1 hk) (rckSUr_sI1_ne_rev_sI0 hk) hc
private theorem rckSUr_torus_inv_mat (hk : 4 ≤ k) {c : SUF} (hc : c ≠ 0) :
    mat SUσ k (rckSUr_torus hk c)⁻¹ =
      Matrix.diagonal (fun s => (shortTorusFun SUσ (sI0 hk) (sI1 hk) c s)⁻¹) :=
  diagonal_inv_eq (g := rckSUr_torus hk c)
    (t := shortTorusFun SUσ (sI0 hk) (sI1 hk) c)
    (rckSUr_shortTorusFun_ne_zero hk hc) (rckSUr_torus_mat hk hc)
private theorem rckSUr_conj_of_suB (hk : 4 ≤ k) (c : SUF) (hc : c ≠ 0)
    (v : Fin 4 → ZMod 2) (hv0 : v 0 = 0) (hv3 : v 3 = 0)
    (hb : algebraMap (ZMod 2) SUF (v 1) + algebraMap (ZMod 2) SUF (v 2) * suOmega = c⁻¹) :
    suZ hk v = rckSUr_torus hk c * suR hk * (rckSUr_torus hk c)⁻¹ := by
  apply mat_injective
  simp only [map_mul, rckSUr_torus_mat hk hc, rckSUr_torus_inv_mat hk hc]
  simp only [suR, mat_apply, suZ_val, rckSUr_suCorner_eq_corner hk v hv0 hv3, hb,
    rckSUr_suCorner_suR]
  exact (rckSUr_diag_conj hk hc).symm
theorem suV_conj (hk : 4 ≤ k) :
    ∀ v ∈ suV hk, v ≠ 1 → ∃ j : SUG k, v = j * suR hk * j⁻¹ := by
  intro v hv hne
  rw [suV_eq_map hk] at hv
  obtain ⟨w, hw, rfl⟩ := hv
  obtain ⟨hw0, hw3⟩ := hw
  have hu_eq : w.toAdd = ![0, w.toAdd 1, w.toAdd 2, 0] := by
    funext i; fin_cases i <;> simp [hw0, hw3]
  have h1 : w.toAdd 1 = 0 ∨ w.toAdd 1 = 1 :=
    (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (w.toAdd 1)
  have h2 : w.toAdd 2 = 0 ∨ w.toAdd 2 = 1 :=
    (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (w.toAdd 2)
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exfalso
    apply hne
    have hzero : w.toAdd = 0 := by
      rw [hu_eq, h1, h2]; funext i; fin_cases i <;> rfl
    rw [suHom_apply, hzero, suZ_zero]
  · refine ⟨rckSUr_torus hk (suOmega ^ 2), ?_⟩
    have hv1 : w.toAdd = ![0, 0, 1, 0] := by rw [hu_eq, h1, h2]
    rw [suHom_apply, hv1]
    refine rckSUr_conj_of_suB hk (suOmega ^ 2) (pow_ne_zero 2 rckSUr_suOmega_ne_zero)
      ![0, 0, 1, 0] (by simp) (by simp) ?_
    have h2inv : (suOmega ^ 2)⁻¹ = suOmega := rckSUr_inv_sq suOmega rckSUr_suOmega_ne_zero
    rw [h2inv]; simp
  · refine ⟨1, ?_⟩
    have hv1 : w.toAdd = ![0, 1, 0, 0] := by rw [hu_eq, h1, h2]
    rw [suHom_apply, hv1, suR, one_mul, inv_one, mul_one]
  · refine ⟨rckSUr_torus hk suOmega, ?_⟩
    have hv1 : w.toAdd = ![0, 1, 1, 0] := by rw [hu_eq, h1, h2]
    rw [suHom_apply, hv1]
    refine rckSUr_conj_of_suB hk suOmega rckSUr_suOmega_ne_zero ![0, 1, 1, 0]
      (by simp) (by simp) ?_
    rw [rckSUr_inv_eq_sq suOmega rckSUr_suOmega_ne_zero]
    simp [rckSUr_suOmega_sq]
    ring
private def rckSUr_i0 (hk : 4 ≤ k) : Fin (k / 2) := ⟨0, by omega⟩
private def rckSUr_i1 (hk : 4 ≤ k) : Fin (k / 2) := ⟨1, by omega⟩
private def rckSUr_betaEven (hk : 4 ≤ k) : Fin (k / 2) → ℤ :=
  fun a => if a.val = 0 then 1 else if a.val + 1 = k / 2 then 1 else 2
private def rckSUr_betaOdd (hk : 4 ≤ k) : Fin (k / 2) → ℤ :=
  fun a => if a.val = 0 then 1 else 2
private def rckSUr_beta (hk : 4 ≤ k) : Fin (k / 2) → ℤ :=
  if Even k then rckSUr_betaEven hk else rckSUr_betaOdd hk
private theorem rckSUr_t_i0 (hk : 4 ≤ k) :
    (weight k (sI0 hk) - weight k (Fin.rev (sI1 hk))) (rckSUr_i0 hk) = 1 := by
  rw [Pi.sub_apply, SUExtras.weight_apply', SUExtras.weight_apply']
  rw [if_pos (by simp [sI0, rckSUr_i0]),
    if_neg (by simp [sI1, rckSUr_i0, Fin.val_rev]; omega),
    if_neg (by simp [sI1, rckSUr_i0, Fin.val_rev]; omega)]
  norm_num
private theorem rckSUr_t_i1 (hk : 4 ≤ k) :
    (weight k (sI0 hk) - weight k (Fin.rev (sI1 hk))) (rckSUr_i1 hk) = 1 := by
  rw [Pi.sub_apply, SUExtras.weight_apply', SUExtras.weight_apply']
  rw [if_neg (by simp [sI0, rckSUr_i1]),
    if_neg (by simp [sI0, rckSUr_i1]; omega),
    if_neg (by simp [sI1, rckSUr_i1, Fin.val_rev]; omega),
    if_pos (by simp [sI1, rckSUr_i1, Fin.val_rev]; omega)]
  norm_num
private theorem rckSUr_toStd_betaEven (hk : 4 ≤ k) (he : Even k) :
    toStd k (rckSUr_betaEven hk) =
      weight k (sI0 hk) - weight k (Fin.rev (sI1 hk)) := by
  have hk2 : k = 2 * (k / 2) := by
    have h := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero (Nat.even_iff.mp he))
    omega
  funext a
  have ha : a.val < k / 2 := a.isLt
  rw [toStd, if_pos he]
  simp only [CFSG.LieType.Universal.Symplectic.toStd, rckSUr_betaEven, Pi.sub_apply,
    SUExtras.weight_apply', sI0, sI1, Fin.val_rev]
  split_ifs <;> omega
private theorem rckSUr_toStd_betaOdd (hk : 4 ≤ k) (he : ¬Even k) :
    toStd k (rckSUr_betaOdd hk) =
      weight k (sI0 hk) - weight k (Fin.rev (sI1 hk)) := by
  have hk2 : k = 2 * (k / 2) + 1 := by
    have hmod : k % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one k with h | h
      · exact absurd (Nat.even_iff.mpr h) he
      · exact h
    calc k = 2 * (k / 2) + k % 2 := (Nat.div_add_mod k 2).symm
      _ = 2 * (k / 2) + 1 := by rw [hmod]
  funext a
  have ha : a.val < k / 2 := a.isLt
  rw [toStd, if_neg he]
  simp only [rckSUr_betaOdd, Pi.sub_apply, SUExtras.weight_apply', sI0, sI1, Fin.val_rev]
  split_ifs <;> omega
private theorem rckSUr_toStd_beta (hk : 4 ≤ k) :
    toStd k (rckSUr_beta hk) =
      weight k (sI0 hk) - weight k (Fin.rev (sI1 hk)) := by
  by_cases he : Even k
  · rw [rckSUr_beta, if_pos he]; exact rckSUr_toStd_betaEven hk he
  · rw [rckSUr_beta, if_neg he]; exact rckSUr_toStd_betaOdd hk he
private theorem rckSUr_beta_mem_roots (hk : 4 ≤ k) :
    rckSUr_beta hk ∈ roots (isFiniteType_cartan k) (divisible k) := by
  rw [roots_eq]
  refine Or.inl ⟨sI0 hk, Fin.rev (sI1 hk), rckSUr_sI0_ne_rev_sI1 hk,
    rckSUr_sI0_ne_rev_sI0 hk, rckSUr_rev_sI1_ne_rev_rev_sI1 hk,
    rckSUr_rev_sI1_ne_rev_sI0 hk, ?_⟩
  exact rckSUr_toStd_beta hk
theorem rckSU_shortRoot (hk : 4 ≤ k) (hF : Nat.card SUF = (2 ^ 1) ^ 2) :
    ∃ β : Fin (Unitary.rootDatum (F := SUF) (p := 2) (f := 1) hF k).rank → ℤ,
      β ∈ (Unitary.rootDatum (F := SUF) (p := 2) (f := 1) hF k).roots ∧
      ¬ GGLongRoot (Unitary.rootDatum (F := SUF) (p := 2) (f := 1) hF k) β ∧
      2 • β ∉ (Unitary.rootDatum (F := SUF) (p := 2) (f := 1) hF k).roots ∧
      suV hk ≤ (Unitary.rootDatum (F := SUF) (p := 2) (f := 1) hF k).rootGroup β := by
  let β := rckSUr_beta hk
  have hβstd := rckSUr_toStd_beta hk
  have hβmem : β ∈ (Unitary.rootDatum (F := SUF) (p := 2) (f := 1) hF k).roots := by
    change β ∈ roots (isFiniteType_cartan k) (divisible k)
    exact rckSUr_beta_mem_roots hk
  have hβnl : ¬ GGLongRoot (Unitary.rootDatum (F := SUF) (p := 2) (f := 1) hF k) β := by
    intro hl
    obtain ⟨i, hi, hieq⟩ :=
      CFSG.StandardType.LieKnownR2.Geo.exists_weight_of_ggLongRoot hF hβmem hl
    have h0 := congrFun (hβstd.symm.trans hieq) (rckSUr_i0 hk)
    rw [rckSUr_t_i0 hk, Pi.smul_apply, nsmul_eq_mul] at h0
    have hw : weight k i (rckSUr_i0 hk) = 0 ∨ weight k i (rckSUr_i0 hk) = 1 ∨
        weight k i (rckSUr_i0 hk) = -1 := by
      rw [SUExtras.weight_apply']; split_ifs <;> simp
    rcases hw with hw | hw | hw <;> omega
  have h2β : 2 • β ∉ (Unitary.rootDatum (F := SUF) (p := 2) (f := 1) hF k).roots := by
    intro h2
    have h2' : 2 • β ∈ roots (isFiniteType_cartan k) (divisible k) := h2
    have h2t : toStd k (2 • β) = 2 • (weight k (sI0 hk) - weight k (Fin.rev (sI1 hk))) := by
      rw [toStd_nsmul_two, hβstd]
    rw [roots_eq] at h2'
    rcases h2' with ⟨i, j, hij, hi, hj, hji, heq⟩ | ⟨i, hi, heq⟩ | ⟨he, i, hi, heq⟩
    · have h0 := congrFun (h2t.symm.trans heq) (rckSUr_i0 hk)
      have h1 := congrFun (h2t.symm.trans heq) (rckSUr_i1 hk)
      rw [Pi.smul_apply, nsmul_eq_mul, rckSUr_t_i0 hk, Pi.sub_apply,
        SUExtras.weight_apply', SUExtras.weight_apply'] at h0
      rw [Pi.smul_apply, nsmul_eq_mul, rckSUr_t_i1 hk, Pi.sub_apply,
        SUExtras.weight_apply', SUExtras.weight_apply'] at h1
      simp only [rckSUr_i0, rckSUr_i1, Fin.val_mk] at h0 h1
      split_ifs at h0 h1 <;> omega
    · have ht : weight k (sI0 hk) - weight k (Fin.rev (sI1 hk)) = weight k i :=
        SUExtras.two_nsmul_injective' (h2t.symm.trans heq)
      have h0 := congrFun ht (rckSUr_i0 hk)
      have h1 := congrFun ht (rckSUr_i1 hk)
      rw [rckSUr_t_i0 hk, SUExtras.weight_apply'] at h0
      rw [rckSUr_t_i1 hk, SUExtras.weight_apply'] at h1
      simp only [rckSUr_i0, rckSUr_i1, Fin.val_mk] at h0 h1
      split_ifs at h0 h1 <;> omega
    · have h0 := congrFun (h2t.symm.trans heq) (rckSUr_i0 hk)
      rw [Pi.smul_apply, nsmul_eq_mul, rckSUr_t_i0 hk, SUExtras.weight_apply'] at h0
      simp only [rckSUr_i0, Fin.val_mk] at h0
      split_ifs at h0 <;> omega
  have hV : suV hk ≤ (Unitary.rootDatum (F := SUF) (p := 2) (f := 1) hF k).rootGroup β := by
    change suV hk ≤ rootGroup SUσ (unitaryInvolution_involutive hF) k β
    rw [suV, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · have hx1 := rckSUr_suZ_eq_rootHom hk (unitaryInvolution_involutive hF) 1
        ![0, 1, 0, 0] (by simp) (by simp) (by simp)
      rw [hx1]
      exact rootHom_mem (unitaryInvolution_involutive hF) (rckSUr_sI0_ne_rev_sI1 hk)
        (rckSUr_sI0_ne_rev_sI0 hk) (rckSUr_rev_sI1_ne_rev_rev_sI1 hk) (rckSUr_rev_sI1_ne_rev_sI0 hk)
        hβstd.symm (Multiplicative.ofAdd 1)
    · have hx1 := rckSUr_suZ_eq_rootHom hk (unitaryInvolution_involutive hF) suOmega
        ![0, 0, 1, 0] (by simp) (by simp) (by simp)
      rw [hx1]
      exact rootHom_mem (unitaryInvolution_involutive hF) (rckSUr_sI0_ne_rev_sI1 hk)
        (rckSUr_sI0_ne_rev_sI0 hk) (rckSUr_rev_sI1_ne_rev_rev_sI1 hk) (rckSUr_rev_sI1_ne_rev_sI0 hk)
        hβstd.symm (Multiplicative.ofAdd suOmega)
  exact ⟨β, hβmem, hβnl, h2β, hV⟩
end CFSG.StandardType.RCKK1IIISU
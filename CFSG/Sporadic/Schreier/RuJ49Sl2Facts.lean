module

public import CFSG.Sporadic.Schreier.RuJ49Facts
public import Certificates.Certificate7351
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.Sporadic.RuSchreier.J49.Sl2

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native Matrix

abbrev SL5 : Type := SpecialLinearGroup (Fin 2) (ZMod 5)

theorem dA_enc {a b c d : ℕ} (ha : a < 5) : dA (enc a b c d) = a := by
  unfold dA enc; omega

theorem dB_enc {a b c d : ℕ} (ha : a < 5) (hb : b < 5) : dB (enc a b c d) = b := by
  unfold dB enc; omega

theorem dC_enc {a b c d : ℕ} (ha : a < 5) (hb : b < 5) (hc : c < 5) : dC (enc a b c d) = c := by
  unfold dC enc; omega

theorem dD_enc {a b c d : ℕ} (ha : a < 5) (hb : b < 5) (hc : c < 5) (hd : d < 5) :
    dD (enc a b c d) = d := by
  unfold dD enc; omega

def keyOf (m : SL5) : ℕ := enc (m.1 0 0).val (m.1 0 1).val (m.1 1 0).val (m.1 1 1).val

theorem dA_keyOf (m : SL5) : dA (keyOf m) = (m.1 0 0).val := dA_enc (ZMod.val_lt _)

theorem dB_keyOf (m : SL5) : dB (keyOf m) = (m.1 0 1).val :=
  dB_enc (ZMod.val_lt _) (ZMod.val_lt _)

theorem dC_keyOf (m : SL5) : dC (keyOf m) = (m.1 1 0).val :=
  dC_enc (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _)

theorem dD_keyOf (m : SL5) : dD (keyOf m) = (m.1 1 1).val :=
  dD_enc (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _)

theorem keyOf_lt (m : SL5) : keyOf m < 625 := by
  have h1 := ZMod.val_lt (m.1 0 0)
  have h2 := ZMod.val_lt (m.1 0 1)
  have h3 := ZMod.val_lt (m.1 1 0)
  have h4 := ZMod.val_lt (m.1 1 1)
  unfold keyOf enc
  omega

theorem keyMul_lt (k l : ℕ) : keyMul k l < 625 := by
  unfold keyMul enc
  omega

theorem val_add_mul (x y z w : ZMod 5) :
    (x * y + z * w).val = (x.val * y.val + z.val * w.val) % 5 := by
  rw [ZMod.val_add, ZMod.val_mul, ZMod.val_mul, ← Nat.add_mod]

theorem keyOf_mul (m n : SL5) : keyOf (m * n) = keyMul (keyOf m) (keyOf n) := by
  unfold keyMul
  rw [dA_keyOf m, dA_keyOf n, dB_keyOf m, dB_keyOf n, dC_keyOf m, dC_keyOf n, dD_keyOf m,
    dD_keyOf n]
  have e00 : (m * n).1 0 0 = m.1 0 0 * n.1 0 0 + m.1 0 1 * n.1 1 0 := by
    simp [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have e01 : (m * n).1 0 1 = m.1 0 0 * n.1 0 1 + m.1 0 1 * n.1 1 1 := by
    simp [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have e10 : (m * n).1 1 0 = m.1 1 0 * n.1 0 0 + m.1 1 1 * n.1 1 0 := by
    simp [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : (m * n).1 1 1 = m.1 1 0 * n.1 0 1 + m.1 1 1 * n.1 1 1 := by
    simp [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  unfold keyOf
  rw [e00, e01, e10, e11, val_add_mul, val_add_mul, val_add_mul, val_add_mul]

theorem keyOf_inj {m n : SL5} (h : keyOf m = keyOf n) : m = n := by
  have h1 : (m.1 0 0).val = (n.1 0 0).val := by rw [← dA_keyOf m, ← dA_keyOf n, h]
  have h2 : (m.1 0 1).val = (n.1 0 1).val := by rw [← dB_keyOf m, ← dB_keyOf n, h]
  have h3 : (m.1 1 0).val = (n.1 1 0).val := by rw [← dC_keyOf m, ← dC_keyOf n, h]
  have h4 : (m.1 1 1).val = (n.1 1 1).val := by rw [← dD_keyOf m, ← dD_keyOf n, h]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · exact ZMod.val_injective 5 h1
  · exact ZMod.val_injective 5 h2
  · exact ZMod.val_injective 5 h3
  · exact ZMod.val_injective 5 h4

theorem isSL_of_det (a b c d : ZMod 5) (h : a * d - b * c = 1) :
    ((a.val * d.val + 4 * (b.val * c.val)) % 5 == 1) = true := by
  revert a b c d
  decide

theorem keyOf_mem (m : SL5) : keyOf m ∈ slKeys () := by
  have hdet : m.1 0 0 * m.1 1 1 - m.1 0 1 * m.1 1 0 = 1 := by
    have := m.2
    rwa [Matrix.det_fin_two] at this
  have hs : isSL (keyOf m) = true := by
    unfold isSL
    rw [dA_keyOf, dB_keyOf, dC_keyOf, dD_keyOf]
    exact isSL_of_det _ _ _ _ hdet
  unfold slKeys
  rw [List.mem_filter, List.mem_range]
  exact ⟨keyOf_lt m, hs⟩

def Me : SL5 := ⟨!![3, 1; 1, 4], by rw [Matrix.det_fin_two_of]; decide⟩

def Mf : SL5 := ⟨!![2, 1; 4, 0], by rw [Matrix.det_fin_two_of]; decide⟩

theorem keyOf_Me : keyOf Me = 533 := by decide

theorem keyOf_Mf : keyOf Mf = 107 := by decide

theorem keyOf_one : keyOf 1 = 126 := by decide

theorem rep_tabK {g0 g3 : Array ℕ} {G0 G3 : Equiv.Perm (Fin 4060)} (h0 : Rep 4060 g0 G0)
    (h3 : Rep 4060 g3 G3) (i0 : isInvA 4060 g0 (ruInv g0) = true)
    (i3 : isInvA 4060 g3 (ruInv g3) = true) {k : ℕ}
    (hk : ∀ l ∈ wordOf (rows ()) k, l = 1 ∨ l = 2) :
    Rep 4060 (tabK #[g0, g3] #[ruInv g0, ruInv g3] (rows ()) k)
      (evalSigned [G0, G3] (wordOf (rows ()) k)) := by
  have hl : lettersOK 2 (wordOf (rows ()) k) = true := by
    simp only [lettersOK, List.all_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
    intro l hl
    rcases hk l hl with rfl | rfl <;> decide
  exact rep_wordA_evalSigned (k := 2) (rep_pair_getD h0 h3)
    (rep_pair_getD_inv (rep_ruInv h0 i0) (rep_ruInv h3 i3)) _ hl

noncomputable def PhiG (G0 G3 : Equiv.Perm (Fin 4060)) (k : ℕ) : Equiv.Perm (Fin 4060) :=
  evalSigned [G0, G3] (wordOf (rows ()) k)

@[expose] def Facts (G0 G3 : Equiv.Perm (Fin 4060)) : Prop :=
  (∀ k < 625, ∀ l ∈ wordOf (rows ()) k, l = 1 ∨ l = 2) ∧
  (∀ k ∈ slKeys (), keyProd (wordOf (rows ()) k) = k) ∧
  (∀ k ∈ slKeys (), PhiG G0 G3 (keyMul k 533) = PhiG G0 G3 k * G0 ∧
      PhiG G0 G3 (keyMul k 107) = PhiG G0 G3 k * G3) ∧
  (∀ k ∈ slKeys (), k ≠ 126 → PhiG G0 G3 k ≠ 1) ∧
  wordOf (rows ()) 126 = [] ∧ wordOf (rows ()) 533 = [1] ∧ wordOf (rows ()) 107 = [2]

theorem checkG_sound {g0 g3 : Array ℕ} {G0 G3 : Equiv.Perm (Fin 4060)} (h0 : Rep 4060 g0 G0)
    (h3 : Rep 4060 g3 G3) (h : checkG g0 g3 = true) : Facts G0 G3 := by
  unfold checkG at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨i0, i3⟩, hlet⟩, hkey⟩, hmat⟩, hker⟩, h126⟩, h533⟩, h107⟩ := h
  have hlet' : ∀ k < 625, ∀ l ∈ wordOf (rows ()) k, l = 1 ∨ l = 2 := fun k hk l hl =>
    hlet k hk l hl
  have hk625 : ∀ k ∈ slKeys (), k < 625 := fun k hk => by
    unfold slKeys at hk
    exact List.mem_range.1 (List.mem_filter.1 hk).1
  have rep : ∀ k < 625, Rep 4060 (tabK #[g0, g3] #[ruInv g0, ruInv g3] (rows ()) k)
      (PhiG G0 G3 k) := fun k hk => rep_tabK h0 h3 i0 i3 (hlet' k hk)
  refine ⟨hlet', hkey, ?_, ?_, h126, h533, h107⟩
  · intro k hk
    obtain ⟨e1, e2⟩ := hmat k hk
    exact ⟨(eqA_iff (rep _ (keyMul_lt k 533)) (rep_compA (rep k (hk625 k hk)) h0)).1 e1,
      (eqA_iff (rep _ (keyMul_lt k 107)) (rep_compA (rep k (hk625 k hk)) h3)).1 e2⟩
  · intro k hk hne h1
    rcases hker k hk with h | h
    · exact hne h
    · have := (eqA_iff (rep k (hk625 k hk)) (rep_idA (n := 4060))).2 h1
      rw [this] at h
      exact absurd h (by simp)

def gm (l : ℤ) : SL5 := if l = 1 then Me else Mf

def Ew : List ℤ → SL5
  | [] => 1
  | l :: w => gm l * Ew w

theorem keyOf_gm (l : ℤ) : keyOf (gm l) = gkey l := by
  unfold gm gkey
  split_ifs
  · exact keyOf_Me
  · exact keyOf_Mf

theorem keyOf_Ew (w : List ℤ) : keyOf (Ew w) = keyProd w := by
  induction w with
  | nil => exact keyOf_one
  | cons l w ih => rw [Ew, keyProd, keyOf_mul, keyOf_gm, ih]

noncomputable def PhM (G0 G3 : Equiv.Perm (Fin 4060)) (m : SL5) : Equiv.Perm (Fin 4060) :=
  PhiG G0 G3 (keyOf m)

section Hom

variable {G0 G3 : Equiv.Perm (Fin 4060)} (hF : Facts G0 G3)
include hF

theorem Facts.PhM_gm {l : ℤ} (hl : l = 1 ∨ l = 2) :
    PhM G0 G3 (gm l) = if l = 1 then G0 else G3 := by
  obtain ⟨-, -, -, -, -, h533, h107⟩ := id hF
  rcases hl with rfl | rfl
  · simp only [PhM, keyOf_gm, gkey, if_true, PhiG, h533, evalSigned]
    simp
  · have : (2 : ℤ) ≠ 1 := by norm_num
    simp only [PhM, keyOf_gm, gkey, this, if_false, PhiG, h107, evalSigned]
    simp

theorem Facts.PhM_one : PhM G0 G3 1 = 1 := by
  obtain ⟨-, -, -, -, h126, -⟩ := id hF
  simp [PhM, keyOf_one, PhiG, h126, evalSigned]

theorem Facts.PhM_mul_gm (m : SL5) {l : ℤ} (hl : l = 1 ∨ l = 2) :
    PhM G0 G3 (m * gm l) = PhM G0 G3 m * PhM G0 G3 (gm l) := by
  obtain ⟨-, -, hmat, -⟩ := id hF
  have hk := hmat (keyOf m) (keyOf_mem m)
  rw [hF.PhM_gm hl]
  unfold PhM
  rcases hl with rfl | rfl
  · simp only [gm, if_true]
    rw [keyOf_mul, keyOf_Me]
    exact hk.1
  · have : (2 : ℤ) ≠ 1 := by norm_num
    simp only [gm, this, if_false]
    rw [keyOf_mul, keyOf_Mf]
    exact hk.2

theorem Facts.PhM_mul_Ew {w : List ℤ} (hw : ∀ l ∈ w, l = 1 ∨ l = 2) (m : SL5) :
    PhM G0 G3 (m * Ew w) = PhM G0 G3 m * PhM G0 G3 (Ew w) := by
  induction w generalizing m with
  | nil => simp [Ew, hF.PhM_one]
  | cons l w ih =>
    have hl := hw l (List.mem_cons_self ..)
    have hw' : ∀ l' ∈ w, l' = 1 ∨ l' = 2 := fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')
    have h1 := ih hw' (m * gm l)
    have h2 := ih hw' (gm l)
    have h3 := hF.PhM_mul_gm m hl
    rw [Ew, ← mul_assoc, h1, h3, h2, mul_assoc]

theorem Facts.PhM_mul (m n : SL5) : PhM G0 G3 (m * n) = PhM G0 G3 m * PhM G0 G3 n := by
  obtain ⟨hlet, hkey, -⟩ := id hF
  have hn : n = Ew (wordOf (rows ()) (keyOf n)) := by
    apply keyOf_inj
    rw [keyOf_Ew]
    exact (hkey (keyOf n) (keyOf_mem n)).symm
  have hw := hlet (keyOf n) (keyOf_lt n)
  rw [hn]
  exact hF.PhM_mul_Ew hw m

noncomputable def Facts.phHom : SL5 →* Equiv.Perm (Fin 4060) :=
  MonoidHom.mk' (PhM G0 G3) hF.PhM_mul

theorem Facts.phHom_injective : Function.Injective hF.phHom := by
  rw [injective_iff_map_eq_one]
  intro m hm
  by_contra hne
  obtain ⟨-, -, -, hker, -⟩ := id hF
  have hk : keyOf m ≠ 126 := fun h => hne (keyOf_inj (h.trans keyOf_one.symm))
  exact hker (keyOf m) (keyOf_mem m) hk hm

theorem Facts.range_phHom : hF.phHom.range = Subgroup.zpowers G0 ⊔ Subgroup.zpowers G3 := by
  apply le_antisymm
  · rintro _ ⟨m, rfl⟩
    show PhiG G0 G3 (keyOf m) ∈ _
    refine evalSigned_mem (gens := [G0, G3]) (fun g hg => ?_) _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  · refine sup_le (Subgroup.zpowers_le.2 ⟨Me, ?_⟩) (Subgroup.zpowers_le.2 ⟨Mf, ?_⟩)
    · have := hF.PhM_gm (l := 1) (Or.inl rfl)
      show PhM G0 G3 Me = G0
      simpa [gm] using this
    · have := hF.PhM_gm (l := 2) (Or.inr rfl)
      show PhM G0 G3 Mf = G3
      simpa [gm] using this

theorem Facts.equiv_sl2 :
    Nonempty (↥(Subgroup.zpowers G0 ⊔ Subgroup.zpowers G3) ≃* SL5) :=
  ⟨((MonoidHom.ofInjective hF.phHom_injective).trans
    (MulEquiv.subgroupCongr hF.range_phHom)).symm⟩

end Hom

theorem exists_equiv_sl2 :
    Nonempty (↥(Subgroup.zpowers (gel 0) ⊔ Subgroup.zpowers (gel 3)) ≃* SL5) := by
  have h := Certificates.certificate7351
  unfold check at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨-, hw⟩, hG⟩ := h
  exact (checkG_sound (rep_tabOf hw 0) (rep_tabOf hw 3) hG).equiv_sl2

end CFSG.Sporadic.RuSchreier.J49.Sl2

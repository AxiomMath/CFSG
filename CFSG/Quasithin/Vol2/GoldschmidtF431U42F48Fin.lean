module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42F48Wrd

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin U42F431

section Rigid

variable (π : ↥P1 →* P45)
  (hB : ∀ y : ↥P1, (y : Y) ∈ P2 → π y = ((y : Y) : P45))
  (hN : ∀ (y : ↥P1) (m : Fin 45), f48Coll0 m → π y m = ((y : Y) : P45) m)

@[expose] def f48n1 : ↥P1 := ⟨f48W f48N1, f48W_mem_P1 f48_n1_fix⟩

@[expose] def f48Sig : P45 := (wordP f48N1)⁻¹ * π f48n1

include hN in
theorem f48Sig_near (m : Fin 45) (hm : f48Near.contains m.val = true) : f48Sig π m = m := by
  obtain ⟨k, hk, h0, hkm⟩ := f48_near_coll m.val m.2 hm
  have := hN f48n1 m ⟨k, hk, h0, hkm⟩
  rw [f48Sig, Equiv.Perm.mul_apply, this]
  show (wordP f48N1)⁻¹ ((wordP f48N1) m) = m
  simp

include hB in
theorem f48Sig_comm {w : List ℕ} (h1 : inB (evalW w) = true)
    (h2 : inB (evalW (f48Cj w)) = true) :
    f48Sig π * wordP w = wordP w * f48Sig π := by
  have hb := f48W_mem_B0 h1
  have hc := f48W_mem_B0 h2
  have hbP : (⟨f48W w, B0_le_P1 hb⟩ : ↥P1) = ⟨f48W w, B0_le_P1 hb⟩ := rfl
  have e1 := hB ⟨f48W w, B0_le_P1 hb⟩ (B0_le_P2 hb)
  have e2 := hB ⟨f48W (f48Cj w), B0_le_P1 hc⟩ (B0_le_P2 hc)
  have e3 : (⟨f48W (f48Cj w), B0_le_P1 hc⟩ : ↥P1) = f48n1 * ⟨f48W w, B0_le_P1 hb⟩ * f48n1⁻¹ :=
    Subtype.ext (f48W_Cj w)
  rw [e3, map_mul, map_mul, map_inv, e1] at e2
  have e4 : ((f48W (f48Cj w) : Y) : P45) = wordP (f48Cj w) := rfl
  have e5 : π f48n1 * wordP w * (π f48n1)⁻¹ = wordP f48N1 * wordP w * (wordP f48N1)⁻¹ := by
    have := e2
    simp only [f48W_coe, Subgroup.coe_mul, Subgroup.coe_inv, f48n1] at this
    exact this
  unfold f48Sig
  calc (wordP f48N1)⁻¹ * π f48n1 * wordP w
      = (wordP f48N1)⁻¹ * (π f48n1 * wordP w * (π f48n1)⁻¹) * π f48n1 := by group
    _ = wordP w * ((wordP f48N1)⁻¹ * π f48n1) := by rw [e5]; group

theorem f48T_getD (k : ℕ) (i : Fin 45) : (f48T k).getD i 0 =
    if f48Near.contains i.val then i.val else applyW (f48Bz.getD i []) k := by
  simp [f48T, List.getD_eq_getElem?_getD]

include hB hN in
theorem f48Sig_repL :
    RepL (f48T ((f48Sig π f48f0 : Fin 45) : ℕ)) (f48Sig π) := by
  refine ⟨by simp [f48T], fun i => ?_⟩
  rw [f48T_getD]
  split_ifs with hn
  · rw [f48Sig_near π hN i hn]
  · have hfar : f48Near.contains i.val = false := by simpa using hn
    obtain ⟨h1, h2, h3⟩ := f48_bz_spec i.val i.2 hfar
    have hc := f48Sig_comm π hB h1 h2
    have e1 := f48_wordP_apply_f0 (w := f48Bz.getD i []) i.2 h3
    have e2 : f48Sig π i = (wordP (f48Bz.getD i [])) (f48Sig π f48f0) := by
      have := f48_comm_apply hc f48f0
      rw [e1] at this
      exact this
    rw [e2]
    exact (applyW_eq _ _).symm

theorem f48_repL_nodup {n : ℕ} {l : List ℕ} {σ : Equiv.Perm (Fin n)} (h : RepL l σ) :
    l.Nodup := by
  rw [List.nodup_iff_injective_get]
  intro i j hij
  have hi : (i : ℕ) < n := h.1 ▸ i.2
  have hj : (j : ℕ) < n := h.1 ▸ j.2
  have e1 := h.2 ⟨i, hi⟩
  have e2 := h.2 ⟨j, hj⟩
  rw [List.getD_eq_getElem _ _ i.2] at e1
  rw [List.getD_eq_getElem _ _ j.2] at e2
  have h4 : l[(i : ℕ)] = l[(j : ℕ)] := by simpa using hij
  have h3 : σ ⟨i, hi⟩ = σ ⟨j, hj⟩ := Fin.ext (e1.symm.trans (h4.trans e2))
  exact Fin.ext (by simpa using congrArg Fin.val (σ.injective h3))

include hB hN in
theorem f48Sig_cases :
    f48Sig π = 1 ∨ RepL (f48T 2) (f48Sig π) := by
  have hrep := f48Sig_repL π hB hN
  have hstab : ∀ s ∈ f48Stab, applyW s ((f48Sig π f48f0 : Fin 45) : ℕ) = (f48Sig π f48f0 : ℕ) := by
    intro s hs
    obtain ⟨h1, h2, h3⟩ := f48_stab_spec s hs
    have hc := f48Sig_comm π hB h1 h2
    have e1 := f48_wordP_apply_f0 (w := s) f48f0.2 h3
    have := f48_comm_apply hc f48f0
    rw [e1] at this
    rw [← applyW_eq, ← this]
  rcases f48_keyCheck _ (f48Sig π f48f0).2 (f48_repL_nodup hrep) hstab with h | h
  · left
    rw [h] at hrep
    exact eq_of_repL hrep (repL_one 45)
  · right
    rw [h] at hrep
    exact hrep

theorem f48_wordP_eq_one_of_evalW {w : List ℕ} (h : evalW w = idL) : wordP w = 1 := by
  refine eq_of_repL (repL_wordP w) ?_
  rw [h]
  exact repL_one 45

include hB hN in
theorem f48_pi_n1 : π f48n1 = wordP f48N1 := by
  rcases f48Sig_cases π hB hN with h | h
  · exact (inv_mul_eq_one.1 h).symm
  · exfalso
    obtain ⟨hr1, -, hr3⟩ := f48_rel_spec
    have hb := f48W_mem_B0 hr1
    have hπb := hB ⟨f48W f48Rel, B0_le_P1 hb⟩ (B0_le_P2 hb)
    have h3 : (f48n1 * ⟨f48W f48Rel, B0_le_P1 hb⟩) ^ 3 = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      have := f48_wordP_eq_one_of_evalW hr3
      simp only [wordP_append] at this
      show (wordP f48N1 * wordP f48Rel) ^ 3 = 1
      rw [pow_three]
      simpa [mul_assoc] using this
    have h4 := congrArg π h3
    rw [map_pow, map_mul, map_one, hπb] at h4
    have e1 : π f48n1 = wordP f48N1 * f48Sig π := by simp [f48Sig]
    have hg : RepL (compL (compL (evalW f48N1) (f48T 2)) (evalW f48Rel))
        ((wordP f48N1 * f48Sig π) * wordP f48Rel) :=
      repL_mul (repL_mul (repL_wordP _) h) (repL_wordP _)
    have hg3 := repL_mul hg (repL_mul hg hg)
    rw [e1] at h4
    have h5 : ((wordP f48N1 * f48Sig π) * wordP f48Rel) *
        (((wordP f48N1 * f48Sig π) * wordP f48Rel) *
          ((wordP f48N1 * f48Sig π) * wordP f48Rel)) = 1 := by
      rw [← pow_three]
      exact h4
    rw [h5] at hg3
    exact f48_relCheck (repL_unique hg3 (repL_one 45))

include hB hN in
theorem f48_rigid (y : ↥P1) : π y = ((y : Y) : P45) := by
  have hn1 := f48_pi_n1 π hB hN
  have hb2 := f48W_mem_B0 f48_rel_spec.2.1
  have hπb2 : π ⟨f48W f48B2, B0_le_P1 hb2⟩ = wordP f48B2 := hB _ (B0_le_P2 hb2)
  rcases f48_P1_cases y with h | h | h
  · exact hB y (B0_le_P2 h)
  · have hbP : ((f48W f48N1)⁻¹ * (y : Y)) ∈ P1 :=
      B0_le_P1 h
    have e : y = f48n1 * ⟨(f48W f48N1)⁻¹ * (y : Y), hbP⟩ := by
      apply Subtype.ext
      show (y : Y) = f48W f48N1 * ((f48W f48N1)⁻¹ * (y : Y))
      simp
    have hπ := hB ⟨(f48W f48N1)⁻¹ * (y : Y), hbP⟩ (B0_le_P2 h)
    rw [e, map_mul, hn1, hπ]
    rfl
  · have hbP : ((f48W (f48B2 ++ f48N1))⁻¹ * (y : Y)) ∈ P1 := B0_le_P1 h
    have e : y = ⟨f48W f48B2, B0_le_P1 hb2⟩ * f48n1 *
        ⟨(f48W (f48B2 ++ f48N1))⁻¹ * (y : Y), hbP⟩ := by
      apply Subtype.ext
      show (y : Y) = f48W f48B2 * f48W f48N1 * ((f48W (f48B2 ++ f48N1))⁻¹ * (y : Y))
      rw [← f48W_append]
      simp
    have hπ := hB ⟨(f48W (f48B2 ++ f48N1))⁻¹ * (y : Y), hbP⟩ (B0_le_P2 h)
    rw [e, map_mul, map_mul, hn1, hπb2, hπ]
    rfl

end Rigid

end CFSG.Quasithin.H13.F431.U42

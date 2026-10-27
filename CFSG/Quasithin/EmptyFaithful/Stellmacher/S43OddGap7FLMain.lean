module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddGap7FLAlg
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddGap7FLEnum
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddGap7FLVerA
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddGap7FLVerB
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddGap7FLVerC

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.F53Mod Equiv

namespace F53.Stellmacher.S43

namespace Odd

namespace Gap7

namespace FL

abbrev Frm : Type := Perm (Fin 5) → Perm (Fin 5) → orth.W

@[expose] def BL : List Frm := (List.range 18).map basC

@[expose] def evObs (h h' : Perm (Fin 5)) : Frm →* orth.W :=
  MonoidHom.mk' (fun c => c h h') fun _ _ => rfl

@[expose] def concObs (k s : Perm (Fin 5)) : Frm →* orth.W :=
  MonoidHom.mk' (fun c => orth.act k⁻¹ (c 1 s * c S5g s)) fun c c' => by
    simp only [Pi.mul_apply, ← map_mul]
    congr 1
    exact mul_mul_mul_comm _ _ _ _

@[expose] def sumObs (x : List (Perm (Fin 5))) (h₀ : Perm (Fin 5)) : Frm →* orth.W :=
  MonoidHom.mk' (fun c => (x.map fun h => c h h₀).prod) fun c c' => by
    simp only [Pi.mul_apply]
    exact List.prod_map_mul

theorem qL_mul (c c' : Frm) : ∀ x, qL (c * c') x = qL c x * qL c' x
  | [] => by simp [qL]
  | h :: t => by
    simp only [qL, qL_mul c c' t, Pi.mul_apply, List.prod_map_mul]
    exact mul_mul_mul_comm _ _ _ _

@[expose] def qObs (x : List (Perm (Fin 5))) : Frm →* orth.W :=
  MonoidHom.mk' (fun c => qL c x) fun c c' => qL_mul c c' x

theorem enc_prodSel : ∀ (bs : List Bool) (xs : List orth.W),
    enc (prodSel bs xs) = xorSel bs (xs.map enc)
  | b :: bs, x :: xs => by
    simp only [prodSel, enc_mul, enc_prodSel bs xs, List.map_cons, xorSel]
    cases b <;> simp [enc_one]
  | [], _ => enc_one
  | _ :: _, [] => enc_one

theorem lin_eval (m : List Bool) (φ : Frm →* orth.W) (ψ : ℕ → ℕ)
    (hψ : ∀ a b, ψ (a ^^^ b) = ψ a ^^^ ψ b) (hψ0 : ψ 0 = 0) :
    ψ (enc (φ (prodSel m BL))) = xorSel m ((List.range 18).map fun l => ψ (enc (φ (basC l)))) := by
  rw [map_prodSel, enc_prodSel, xorSel_map ψ hψ hψ0, BL, List.map_map, List.map_map,
    List.map_map]
  rfl

theorem complete (c : Frm) (hequi : ∀ k h h', c (k * h) (k * h') = orth.act k (c h h'))
    (hright : ∀ h h' t, t ∈ S5That → c (h * t) h' = c h h')
    (hsymm : ∀ h h', c h h' = c h' h) (hblock : ∀ h d, d ∈ S5Syl → c h (h * d) = 1) :
    ∃ m : List Bool, m.length = 18 ∧ c = prodSel m BL := by
  have C0 : ∀ h h', c h h' = orth.act h (c 1 (h⁻¹ * h')) := by
    intro h h'
    have := hequi h 1 (h⁻¹ * h')
    rwa [mul_one, mul_inv_cancel_left] at this
  have C1 : ∀ s t t', t ∈ S5That → t' ∈ S5That → c 1 (t * s * t') = orth.act t (c 1 s) := by
    intro s t t' ht ht'
    rw [hsymm, hright _ _ _ ht', hsymm]
    have h1 := hequi t t⁻¹ s
    rw [mul_inv_cancel] at h1
    rw [h1]
    have h2 := hright 1 s t⁻¹ (inv_mem ht)
    rw [one_mul] at h2
    rw [h2]
  have C2 : ∀ s, c 1 s⁻¹ = orth.act s⁻¹ (c 1 s) := by
    intro s
    have := hequi s⁻¹ s 1
    rw [inv_mul_cancel, mul_one] at this
    rw [this, hsymm]
  have C3 : ∀ d ∈ S5Syl, c 1 d = 1 := by
    intro d hd
    have := hblock 1 d hd
    rwa [one_mul] at this
  have hT : ∀ i < 4, tHat i ∈ S5That := fun i hi => (mem_S5That_iff _).mpr (tHat_mem i hi)
  have hstab : ∀ k, ∀ e ∈ stabL, e.1 = k →
      orth.act (stabElt e) (c 1 (orbRep k)) = c 1 (orbRep k) := by
    intro k e he hk
    subst hk
    obtain ⟨heq, hb1, hb2⟩ := stab_eq e he
    have key : c 1 (orbRep e.1) = orth.act (stabElt e) (c 1 (orbRep e.1)) := by
      calc c 1 (orbRep e.1) = c 1 (tHat e.2.1 * stabRep e * tHat e.2.2.1) := by rw [heq]
        _ = orth.act (tHat e.2.1) (c 1 (stabRep e)) := C1 _ _ _ (hT _ hb1) (hT _ hb2)
        _ = orth.act (stabElt e) (c 1 (orbRep e.1)) := by
          unfold stabElt stabRep
          split_ifs
          · rw [C2, act_mul_apply]
          · rw [mul_one]
    exact key.symm
  refine ⟨(List.range 18).map fun l => coord l (c 1 (orbRep (prmOrb l))), by simp, ?_⟩
  set m : List Bool := (List.range 18).map fun l => coord l (c 1 (orbRep (prmOrb l))) with hm
  have hf : ∀ s, c 1 s = prodSel m ((List.range 18).map fun l => basF l s) := by
    intro s
    rcases decomp s with ⟨h7, hD⟩ | ⟨hk, hTs⟩
    · rw [C3 s ((mem_S5Syl_iff s).mpr hD)]
      symm
      apply prodSel_eq_one
      intro x hx
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
      have := prmOrb_lt l (List.mem_range.mp hl)
      have hne : ptOrb s ≠ prmOrb l := by omega
      simp [basF, hne]
    · have h1 : c 1 s = orth.act (ptAct s) (c 1 (orbRep (ptOrb s))) := by
        calc c 1 s = c 1 (tHat (ptD s % 4) * orbRepE s *
              ((tHat (ptD s % 4) * orbRepE s)⁻¹ * s)) := by rw [mul_inv_cancel_left]
          _ = orth.act (tHat (ptD s % 4)) (c 1 (orbRepE s)) :=
            C1 _ _ _ (hT _ (Nat.mod_lt _ (by norm_num))) ((mem_S5That_iff _).mpr hTs)
          _ = orth.act (ptAct s) (c 1 (orbRep (ptOrb s))) := by
            unfold ptAct orbRepE
            split_ifs
            · rw [C2, act_mul_apply]
            · rw [mul_one]
      have h2 := fix_eq (ptOrb s) hk (c 1 (orbRep (ptOrb s))) fun e he hek =>
        hstab (ptOrb s) e he hek
      rw [h1, h2, prodSel_map_congr _ (fun l => coord l (c 1 (orbRep (prmOrb l)))) _ _ ?_,
        map_prodSel, List.map_map]
      · congr 1
        apply List.map_congr_left
        intro l _
        simp only [Function.comp_apply, basF]
        split_ifs with h3 h4 h4
        · rfl
        · exact absurd h3.symm h4
        · exact absurd h4.symm h3
        · exact map_one _
      · intro l _
        by_cases h3 : prmOrb l = ptOrb s
        · left; rw [h3]
        · right; simp [h3]
  funext h h'
  have e1 : prodSel m BL h h' = prodSel m ((List.range 18).map fun l => basC l h h') := by
    have := map_prodSel (evObs h h') m BL
    rw [BL, List.map_map] at this
    exact this
  rw [e1, C0, hf, map_prodSel, List.map_map]
  rfl

theorem key (c : Frm) (m : List Bool) (hm : m.length = 18) (hc : c = prodSel m BL)
    (hP1 : ∀ i < 30, ∀ j < 30,
      (pY (enc (c (ptRep i) 1)) = 0 ∧ pY (enc (c (ptRep i) S5g)) = 0) ∨
      (pY (enc (c (ptRep j) 1)) = 0 ∧ pY (enc (c (ptRep j) S5g)) = 0) ∨
      (pY (enc (c (ptRep i) 1)) = pY (enc (c (ptRep j) 1)) ∧
        pY (enc (c (ptRep i) S5g)) = pY (enc (c (ptRep j) S5g))))
    (hP2 : ∀ i < 30, ¬ (pY (enc (c (ptRep i) 1)) = 0 ∧ pY (enc (c (ptRep i) S5g)) = 0) →
      pY (enc (c (ptRep i) 1)) ≠ 0 ∧ pY (enc (c (ptRep i) S5g)) ≠ 0 ∧
        pY (enc (c (ptRep i) 1)) ≠ pY (enc (c (ptRep i) S5g))) :
    (∀ k : Perm (Fin 5), pY (enc (orth.act k⁻¹ (c 1 k * c S5g k))) = 0 ∧
      pY (enc (orth.act k⁻¹ (c 1 (k * S5g) * c S5g (k * S5g)))) = 0) ∨
    ∃ n < 11, ((wit n).map fun h => c h 1).prod = 1 ∧ ((wit n).map fun h => c h S5g).prod = 1 ∧
      pY (enc (qL c (wit n))) ≠ 0 := by
  subst hc
  have hfld : ∀ p w, fld (xorSel m cols) p w = xorSel m (cols.map fun x => fld x p w) :=
    fun p w => xorSel_map (fun x => fld x p w) (fun a b => fld_xor a b p w) (fld_zero p w) m cols
  have hid : ∀ a b : ℕ, id (a ^^^ b) = id a ^^^ id b := fun _ _ => rfl
  have hPa : ∀ i < 30, fld (xorSel m cols) (4 * i) 2 = pY (enc (prodSel m BL (ptRep i) 1)) := by
    intro i hi
    rw [hfld, (cols_P i hi).1]
    exact (lin_eval m (evObs (ptRep i) 1) pY pY_xor pY_zero).symm
  have hPb : ∀ i < 30,
      fld (xorSel m cols) (4 * i + 2) 2 = pY (enc (prodSel m BL (ptRep i) S5g)) := by
    intro i hi
    rw [hfld, (cols_P i hi).2]
    exact (lin_eval m (evObs (ptRep i) S5g) pY pY_xor pY_zero).symm
  have hnb : ∀ i < 30, nb (xorSel m cols) i =
      pY (enc (prodSel m BL (ptRep i) 1)) + 4 * pY (enc (prodSel m BL (ptRep i) S5g)) := by
    intro i hi
    rw [nb_eq, hPa i hi, hPb i hi]
  have hlt : ∀ i < 30, pY (enc (prodSel m BL (ptRep i) 1)) < 4 ∧
      pY (enc (prodSel m BL (ptRep i) S5g)) < 4 := by
    intro i hi
    rw [← hPa i hi, ← hPb i hi]
    exact ⟨fld_two_lt _ _, fld_two_lt _ _⟩
  have hp : pChk (xorSel m cols) = true := by
    apply pChk_of
    · intro i hi j hj
      rw [hnb i hi, hnb j hj]
      have := hlt i hi
      have := hlt j hj
      rcases hP1 i hi j hj with h | h | h <;> omega
    · intro i hi hne
      rw [hnb i hi] at hne ⊢
      have h4 := hlt i hi
      obtain ⟨h1, h2, h3⟩ := hP2 i hi (by omega)
      exact (goodN_iff _ h4.1 _ h4.2).mpr ⟨h1, h2, h3⟩
  have hsplit : xorSel m cols = xorSel (m.take 14) colsP ^^^ xorSel (m.drop 14) colsN := by
    have h := xorSel_append (m.take 14) (m.drop 14) colsP colsN (by simp [hm, colsP])
    rwa [List.take_append_drop] at h
  have hY : ∀ i < 30, nb (xorSel (m.drop 14) colsN) i = 0 := fun i hi =>
    xorSel_map_eq_zero (fun x => nb x i) (fun a b => nb_xor a b i) (nb_zero i) _ _
      fun x hx => colsN_nb i hi x hx
  have hp' : pChk (0 ^^^ xorSel (m.take 14) colsP) = true := by
    rw [Nat.zero_xor, ← hp]
    apply pChk_congr
    intro i hi
    rw [hsplit, nb_xor, hY i hi, Nat.xor_zero]
  have hN := enumP_sound colsN colsP 0 enum_true (m.take 14) (by simp [hm, colsP]) hp'
  have hL := enumN_sound colsN _ hN (m.drop 14) (by simp [hm, colsN])
  rw [Nat.zero_xor, ← hsplit] at hL
  simp only [leafN, Bool.or_eq_true, Nat.beq_eq] at hL
  rcases hL with hL | hL
  · left
    intro k
    constructor
    · have h2 := hfld (OC + 4 * pos k) 2
      rw [(cols_C k).1, fld_of_shiftRight_eq_zero hL] at h2
      exact (lin_eval m (concObs k k) pY pY_xor pY_zero).trans h2.symm
    · have h2 := hfld (OC + 4 * pos k + 2) 2
      rw [(cols_C k).2, Nat.add_assoc, fld_of_shiftRight_eq_zero hL] at h2
      exact (lin_eval m (concObs k (k * S5g)) pY pY_xor pY_zero).trans h2.symm
  · right
    obtain ⟨n, hn, hw⟩ := exists_witAt 11 hL
    simp only [witAt, Bool.and_eq_true, Nat.beq_eq] at hw
    obtain ⟨⟨hw1, hw2⟩, hw3⟩ := hw
    refine ⟨n, hn, ?_, ?_, ?_⟩
    · apply enc_inj
      rw [enc_one]
      have h2 := hfld (OW + 12 * n) 5
      rw [(cols_W n hn).1, hw1] at h2
      exact (lin_eval m (sumObs (wit n) 1) id hid rfl).trans h2.symm
    · apply enc_inj
      rw [enc_one]
      have h2 := hfld (OW + 12 * n + 5) 5
      rw [(cols_W n hn).2.1, hw2] at h2
      exact (lin_eval m (sumObs (wit n) S5g) id hid rfl).trans h2.symm
    · intro h0
      have h2 := hfld (OW + 12 * n + 10) 2
      rw [(cols_W n hn).2.2] at h2
      have h3 := (lin_eval m (qObs (wit n)) pY pY_xor pY_zero).trans h2.symm
      have h4 : fld (xorSel m cols) (OW + 12 * n + 10) 2 = 0 := h3.symm.trans h0
      rw [h4] at hw3
      exact absurd hw3 (by decide)

end FL

end Gap7

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin

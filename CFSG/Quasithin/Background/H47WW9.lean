module

public import CFSG.Quasithin.Background.H47WBase
public import CFSG.Quasithin.Background.H47WCheck9
public import CFSG.Quasithin.Background.H47WW9Fld
public import CFSG.Quasithin.Vol2.Ch9L34NormGen

public section

namespace CFSG.Quasithin.H47W

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.Ch9.L34M
  CFSG.Quasithin.H13.Ch9.L34N CFSG.Quasithin.H13.Ch9.Herm9 CFSG.Quasithin.H.L3W9
  CFSG.Fischer

theorem card_W9 : Nat.card W9 = 2 ^ 9 := card_of_coords (MaskCoords.std 9)

theorem rk_W9 : rk W9 = 9 := by
  unfold rk
  rw [card_W9, padicValNat.prime_pow]

theorem sq_eq_one_W9 (v : W9) : v ^ 2 = 1 := by
  rw [sq]
  exact mul_self_of_coords (MaskCoords.std 9) v

theorem rk_fixV_one : rk ↥(fixV (Subgroup.zpowers (1 : MulAut W9))) = 9 := by
  have h : fixV (Subgroup.zpowers (1 : MulAut W9)) = ⊤ := by
    ext v
    simp only [Subgroup.mem_top, iff_true]
    exact mem_fixV_zpowers_iff_apply.2 rfl
  rw [h, rk_top]
  exact rk_W9

theorem sig9_mem_Sig9 (p : ℕ) : sig9 p ∈ Sig9 := by
  show (sig9 p).left ∈ U
  exact mem_U.2 ⟨_, _, _, rfl⟩

theorem sig9_left (p : ℕ) : (sig9 p).left = uGL (f4c p) (f4c (p / 4)) (f4c (p / 16)) := rfl

theorem sig9_right_val (p : ℕ) :
    Multiplicative.toAdd (sig9 p).right = ((p / 64 % 2 : ℕ) : ZMod 2) := rfl

theorem rho9G_sig9_inner {p : ℕ} (hp : p < 64) : rho9G (sig9 p) ∈ img9 := by
  have h0 : p / 64 % 2 = 0 := by
    rw [Nat.div_eq_of_lt hp]
  have hr : (sig9 p).right = 1 := by
    apply Multiplicative.toAdd.injective
    rw [sig9_right_val, h0]
    rfl
  rw [rho9G_apply, hr, map_one, mul_one, sig9_left, ← toGL_uSL]
  exact ⟨uSL (f4c p) (f4c (p / 4)) (f4c (p / 16)), rfl⟩

theorem rho9G_sig9_outer {p : ℕ} (hp : 64 ≤ p) (hp' : p < 128) :
    rho9G (sig9 p) = rho9 (Matrix.SpecialLinearGroup.toGL
      (uSL (f4c p) (f4c (p / 4)) (f4c (p / 16)))) * fld9 := by
  have h1 : p / 64 % 2 = 1 := by
    have : p / 64 = 1 := by omega
    rw [this]
  have hr : (sig9 p).right = Multiplicative.ofAdd 1 := by
    apply Multiplicative.toAdd.injective
    rw [sig9_right_val, h1]
    rfl
  rw [rho9G_apply, hr, sig9_left, toGL_uSL]
  congr 1

theorem actsBy_cols9_sig9 {p : ℕ} (hp : p < 128) :
    ActsBy (MaskCoords.std 9) (rho9G (sig9 p)) (cols9 p) := actsBy_cols9 hp

theorem isInvN_of_actsBy {s : MulAut W9} {cs : List ℕ} (hA : ActsBy (MaskCoords.std 9) s cs)
    (hs2 : s * s = 1) (hcs : AllLt 9 cs = true) : isInvN 9 cs = true := by
  unfold isInvN
  rw [List.all_eq_true]
  intro i hi
  rw [List.mem_range] at hi
  have hi' : 2 ^ i < 2 ^ 9 := Nat.pow_lt_pow_right (by norm_num) hi
  have hlt := actM_lt (allLt_spec hcs) (2 ^ i)
  have h := congrArg (fun f : MulAut W9 => f (toW 9 (2 ^ i))) hs2
  simp only [MulAut.mul_apply, MulAut.one_apply] at h
  have hA1 : ∀ m < 2 ^ 9, s (toW 9 m) = toW 9 (actM cs m) := fun m hm => hA m hm
  rw [hA1 _ hi', hA1 _ hlt] at h
  have := (MaskCoords.std 9).vm_inj _ _ (actM_lt (allLt_spec hcs) _) hi' h
  exact beq_iff_eq.2 this

theorem rk_fixV_inner_le {p : ℕ} (hp : p < 64) (hp0 : p ≠ 0) {s : MulAut W9}
    (hs : s = rho9G (sig9 p)) (hs2 : s * s = 1) :
    rk ↥(fixV (Subgroup.zpowers s)) ≤ 5 := by
  have hA : ActsBy (MaskCoords.std 9) s (cols9 p) := by
    rw [hs]
    exact actsBy_cols9_sig9 (by omega)
  have hinv := isInvN_of_actsBy hA hs2 (allLt_cols9 (by omega : p < 128))
  have hc := List.all_eq_true.1 chkIn9 p (List.mem_range.2 hp)
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
  have hr : rankOK 4 9 (cols9 p) (pickUnit 9 4 (cols9 p)) = true := by
    rcases hc with (h | h) | h
    · exact absurd h hp0
    · simp [hinv] at h
    · exact h
  obtain ⟨h4, hws, hnd⟩ := rankOK_spec hr
  have key := two_pow_mul_card_le (t := s) (cs := cols9 p) (ws := pickUnit 9 4 (cols9 p)) hA
    (allLt_cols9 (by omega : p < 128)) hws hnd (F := fixV (Subgroup.zpowers s))
    (fun v hv => (mem_fixV_zpowers_iff_apply).1 hv)
  have h1 : 2 ^ 4 ≤ 2 ^ (pickUnit 9 4 (cols9 p)).length := Nat.pow_le_pow_right (by norm_num) h4
  have h2 := le_trans (Nat.mul_le_mul_right _ h1) key
  have h3 : Nat.card ↥(fixV (Subgroup.zpowers s)) ≤ 2 ^ 5 := by
    norm_num at h2 ⊢
    omega
  exact rk_le_of_card_le sq_eq_one_W9 _ h3

theorem rk_fixV_outer_eq {p : ℕ} (hp64 : 64 ≤ p) (hp' : p < 128) {s : MulAut W9}
    (hs : s = rho9G (sig9 p)) (hs2 : s * s = 1) (hs1 : s ≠ 1) :
    rk ↥(fixV (Subgroup.zpowers s)) = 6 := by
  have hA : ActsBy (MaskCoords.std 9) s (cols9 p) := by
    rw [hs]
    exact actsBy_cols9_sig9 hp'
  have hinv := isInvN_of_actsBy hA hs2 (allLt_cols9 hp')
  have hmem : p ∈ outW9.map Prod.fst := by
    have hc := List.all_eq_true.1 chkOutCover (p - 64) (List.mem_range.2 (by omega))
    have e : p - 64 + 64 = p := by omega
    rw [e] at hc
    simpa [hinv] using hc
  obtain ⟨pw, hpw, hpwp⟩ := List.mem_map.1 hmem
  have hc := List.all_eq_true.1 chkOut9 pw hpw
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, hlen⟩, hfix⟩, hnd⟩ := hc
  rw [hpwp] at hfix
  have hlow : 2 ^ 6 ≤ Nat.card ↥(fixV (Subgroup.zpowers s)) := by
    have hU : ∀ a ∈ pw.2, (MaskCoords.std 9).vm a ∈ fixV (Subgroup.zpowers s) := by
      intro a ha
      refine mem_fixV_zpowers_iff_apply.2 ?_
      have h1 : a < 2 ^ 9 := by
        have := (hfix a ha).1
        norm_num
        omega
      have h2 := hA a h1
      rw [(hfix a ha).2] at h2
      exact h2
    have key := (MaskCoords.std 9).pow_le_card (fixV (Subgroup.zpowers s)) pw.2 hnd
      (fun a ha => by
        have := (hfix a ha).1
        norm_num
        omega) hU
    rw [hlen] at key
    exact key
  have hupp : Nat.card ↥(fixV (Subgroup.zpowers s)) ≤ 2 ^ 6 := by
    have hsS : s ∈ Sig9.map rho9G := Subgroup.mem_map.2 ⟨sig9 p, sig9_mem_Sig9 p, hs.symm⟩
    obtain ⟨d, hd, hdA⟩ := cov9 s hsS hs2 hs1
    obtain ⟨hall, hr⟩ := (chk1_spec chk1_dat9).1 d hd
    obtain ⟨h3, hws, hnd3⟩ := rankOK_spec hr
    have key := two_pow_mul_card_le (t := s) (cs := d.1) (ws := d.2) hdA hall hws hnd3
      (F := fixV (Subgroup.zpowers s)) (fun v hv => mem_fixV_zpowers_iff_apply.1 hv)
    have h1 : 2 ^ 3 ≤ 2 ^ d.2.length := Nat.pow_le_pow_right (by norm_num) h3
    have h2 := le_trans (Nat.mul_le_mul_right _ h1) key
    norm_num at h2
    norm_num
    omega
  exact le_antisymm (rk_le_of_card_le sq_eq_one_W9 _ hupp) (le_rk_of_pow_le sq_eq_one_W9 _ hlow)

theorem exists_sylow_w9 {t : MulAut W9} (ht : t * t = 1) (hN : t ∈ rho9G.range) :
    ∃ h ∈ rho9G.range, ∃ p < 128, h * t * h⁻¹ = rho9G (sig9 p) := by
  have hsq : ∀ x : ↥(Subgroup.zpowers t), x ^ 2 = 1 := by
    intro x
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 x.2
    rw [sq]
    apply Subtype.ext
    show (x : MulAut W9) * (x : MulAut W9) = 1
    rw [← hk]
    exact sq_zpow_of_sq_eq_one ht k
  have h2 : IsPGroup 2 (Subgroup.zpowers t) := isPGroup_two_of_sq_eq_one hsq
  obtain ⟨g, hg⟩ := CFSG.Quasithin.H13.Ch9.L34M.exists_conj_le rho9G sylSig9
    (B := Subgroup.zpowers t) (Subgroup.zpowers_le.2 hN) h2
  have hmem := hg (Subgroup.mem_map.2 ⟨t, Subgroup.mem_zpowers t, rfl⟩)
  obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.1 hmem
  rw [coe_sylSig9] at hx
  obtain ⟨p, hp, rfl⟩ := exists_sig9 hx
  exact ⟨(rho9G g)⁻¹, Subgroup.inv_mem _ ⟨g, rfl⟩, p, hp, hxe.symm⟩

theorem rho9G_range_le_normalizer :
    rho9G.range ≤ Subgroup.normalizer (img9 : Set (MulAut W9)) := by
  rintro _ ⟨x, rfl⟩
  rw [rho9G_apply]
  apply Subgroup.mul_mem
  · exact rho_mem_normalizer rho9 x.left
  · unfold CFSG.Quasithin.H13.Ch9.L34M.fldHom
    rw [c2Hom_apply]
    split_ifs
    · exact Subgroup.one_mem _
    · exact frob_mem_normalizer rho9 (fun g => rho9_frobGL g)

theorem img9_conj_mem {h : MulAut W9} (hh : h ∈ rho9G.range) {x : MulAut W9} (hx : x ∈ img9) :
    h * x * h⁻¹ ∈ img9 :=
  (Subgroup.mem_normalizer_iff.1 (rho9G_range_le_normalizer hh) x).1 hx

theorem img9_le_range : img9 ≤ rho9G.range := by
  rintro _ ⟨A, rfl⟩
  exact ⟨⟨Matrix.SpecialLinearGroup.toGL A, 1⟩, by simp [rho9G_apply]⟩

theorem fld9_mem_range : fld9 ∈ rho9G.range :=
  ⟨⟨1, Multiplicative.ofAdd 1⟩, by simp [rho9G_apply, fldHom, c2Hom_apply]⟩

theorem w9_outer_of_rank {t : MulAut W9} (ht : t * t = 1) (hN : t ∈ rho9G.range)
    (hrk : rk ↥(commV (Subgroup.zpowers t)) = 3) :
    ∃ h ∈ rho9G.range, ∃ u : Matrix.SpecialLinearGroup (Fin 3) F4,
      h * t * h⁻¹ = rho9 (Matrix.SpecialLinearGroup.toGL u) * fld9 := by
  obtain ⟨h, hh, p, hp, hsh⟩ := exists_sylow_w9 ht hN
  have hsum : rk ↥(commV (Subgroup.zpowers t)) + rk ↥(fixV (Subgroup.zpowers t)) = 9 :=
    (rk_commV_zpowers_eq_sub t).trans rk_W9
  have hc : rk ↥(fixV (Subgroup.zpowers (h * t * h⁻¹))) = rk ↥(fixV (Subgroup.zpowers t)) :=
    rk_fixV_zpowers_conj h t
  have hfix : rk ↥(fixV (Subgroup.zpowers (rho9G (sig9 p)))) = 6 := by
    rw [← hsh]
    omega
  by_cases hp64 : 64 ≤ p
  · refine ⟨h, hh, uSL (f4c p) (f4c (p / 4)) (f4c (p / 16)), ?_⟩
    rw [hsh, rho9G_sig9_outer hp64 hp]
  · exfalso
    rcases Nat.eq_zero_or_pos p with h0 | hpos
    · subst h0
      rw [sig9_zero, map_one] at hfix
      rw [rk_fixV_one] at hfix
      norm_num at hfix
    · have hsq : rho9G (sig9 p) * rho9G (sig9 p) = 1 := by
        rw [← hsh]
        calc h * t * h⁻¹ * (h * t * h⁻¹) = h * (t * t) * h⁻¹ := by group
          _ = 1 := by rw [ht]; group
      have hle := rk_fixV_inner_le (s := rho9G (sig9 p)) (p := p) (by omega) (by omega) rfl hsq
      omega

theorem w9_rank_of_fld {t : MulAut W9} (ht : t * t = 1) {l : MulAut W9} (hl : l ∈ img9)
    (htl : t = l * fld9) : rk ↥(commV (Subgroup.zpowers t)) = 3 := by
  have hN : t ∈ rho9G.range := by
    rw [htl]
    exact Subgroup.mul_mem _ (img9_le_range hl) fld9_mem_range
  obtain ⟨h, hh, p, hp, hsh⟩ := exists_sylow_w9 ht hN
  have hfld : fld9 = l⁻¹ * t := by rw [htl, inv_mul_cancel_left]
  have hfix : rk ↥(fixV (Subgroup.zpowers t)) = 6 := by
    by_cases hp64 : 64 ≤ p
    · have ht1 : t ≠ 1 := by
        intro h1
        have hf : fld9 = l⁻¹ := by rw [hfld, h1, mul_one]
        exact fld9_not_mem_img9 (by rw [hf]; exact img9.inv_mem hl)
      have hs1 : rho9G (sig9 p) ≠ 1 := by
        intro h1
        apply ht1
        have : t = h⁻¹ * (h * t * h⁻¹) * h := by group
        rw [this, hsh, h1]
        group
      have hsq : rho9G (sig9 p) * rho9G (sig9 p) = 1 := by
        rw [← hsh]
        calc h * t * h⁻¹ * (h * t * h⁻¹) = h * (t * t) * h⁻¹ := by group
          _ = 1 := by rw [ht]; group
      have hs := rk_fixV_outer_eq hp64 hp rfl hsq hs1
      have hc : rk ↥(fixV (Subgroup.zpowers (h * t * h⁻¹))) = rk ↥(fixV (Subgroup.zpowers t)) :=
        rk_fixV_zpowers_conj h t
      rw [hsh] at hc
      omega
    · exfalso
      have hsn : rho9G (sig9 p) ∈ img9 := rho9G_sig9_inner (by omega)
      have ht_img : t ∈ img9 := by
        have : t = h⁻¹ * (h * t * h⁻¹) * h⁻¹⁻¹ := by group
        rw [this, hsh]
        exact img9_conj_mem (Subgroup.inv_mem _ hh) hsn
      apply fld9_not_mem_img9
      rw [hfld]
      exact img9.mul_mem (img9.inv_mem hl) ht_img
  have hsum : rk ↥(commV (Subgroup.zpowers t)) + rk ↥(fixV (Subgroup.zpowers t)) = 9 :=
    (rk_commV_zpowers_eq_sub t).trans rk_W9
  omega

end CFSG.Quasithin.H47W

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritExcZ3Gen
public import CFSG.Quasithin.EmptyFaithful.S151bModule
public import CFSG.CharacterTheory.Semidihedral.Principal.ParameterFiveTorusNormalizerSupport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

private theorem s16h_zpowers_eq_of_mem_of_ne_one {W : Type} [Group W]
    {L : Subgroup (MulAut W)} (hL : Nat.card ↥L = 3) {l : MulAut W} (hl : l ∈ L) (hlne : l ≠ 1) :
    Subgroup.zpowers l = L := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hgen0 : Subgroup.zpowers (⟨l, hl⟩ : ↥L) = ⊤ :=
    zpowers_eq_top_of_prime_card hL (by simpa using hlne)
  have hmap := MonoidHom.map_zpowers L.subtype (⟨l, hl⟩ : ↥L)
  have htop : (⊤ : Subgroup ↥L).map L.subtype = L := by
    ext y
    simp [Subgroup.mem_map]
  rw [hgen0, htop] at hmap
  simpa using hmap.symm

private theorem s16h_pow_three_eq_one_of_mem {W : Type} [Group W]
    {L : Subgroup (MulAut W)} (hL : Nat.card ↥L = 3) {l : MulAut W} (hl : l ∈ L) :
    l ^ 3 = 1 := by
  have h := pow_card_eq_one' (G := ↥L) (x := (⟨l, hl⟩ : ↥L))
  rw [hL] at h
  simpa using congrArg Subtype.val h

private theorem s16h_even_of_two_pow_modEq_one {r : ℕ} (h : 2 ^ r ≡ 1 [MOD 3]) : Even r := by
  rcases Nat.even_or_odd' r with ⟨k, hk | hk⟩
  · rw [hk]
    exact even_two_mul k
  · exfalso
    have h4 : (4 : ℕ) ≡ 1 [MOD 3] := by decide
    have hp : (2 : ℕ) ^ (2 * k + 1) ≡ 2 [MOD 3] := by
      have h1 : (2 : ℕ) ^ (2 * k + 1) = 4 ^ k * 2 := by
        rw [pow_succ, pow_mul]
        norm_num
      rw [h1]
      simpa using (h4.pow k).mul (Nat.ModEq.refl 2)
    have h' : (2 : ℕ) ^ (2 * k + 1) ≡ 1 [MOD 3] := by
      rw [hk] at h
      exact h
    have h21 : (2 : ℕ) ≡ 1 [MOD 3] := hp.symm.trans h'
    norm_num at h21

theorem s16h_three_le_rk_of_inverts_Z3 {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)} (hL : Nat.card ↥L = 3)
    (hrk : rk ↥(commSub (⊤ : Subgroup W) L) = 6)
    (hfix : commSub (⊤ : Subgroup W) L ⊓ fixV L = ⊥) {τ : MulAut W}
    (hinv : ∀ l ∈ L, τ * l * τ⁻¹ = l⁻¹) :
    3 ≤ rk ↥(commSub (commSub (⊤ : Subgroup W) L) (Subgroup.zpowers τ)) := by
  classical
  obtain ⟨l, hlL, hlne⟩ : ∃ l ∈ L, l ≠ 1 := by
    rcases Subgroup.bot_or_exists_ne_one L with h | ⟨l, hlL, hlne⟩
    · exfalso
      rw [h, Subgroup.card_bot] at hL
      norm_num at hL
    · exact ⟨l, hlL, hlne⟩
  have hgen : Subgroup.zpowers l = L := s16h_zpowers_eq_of_mem_of_ne_one hL hlL hlne
  have hl3 : l ^ 3 = 1 := s16h_pow_three_eq_one_of_mem hL hlL
  set U : Subgroup W := commSub (⊤ : Subgroup W) L with hU
  have hrkU : rk U = 6 := by rw [hU]; exact hrk
  have hτstab : ∀ c ∈ U, τ c ∈ U := by
    rw [hU]
    exact commSub_top_stable151b (fun x hx => by rw [hinv x hx]; exact L.inv_mem hx)
  have hinv' : ∀ x ∈ L, τ⁻¹ * x * τ = x⁻¹ := by
    intro x hx
    have h := hinv x hx
    have h2 : x = τ⁻¹ * x⁻¹ * τ := by
      calc x = τ⁻¹ * (τ * x * τ⁻¹) * τ := by group
        _ = τ⁻¹ * x⁻¹ * τ := by rw [h]
    have h3 := congrArg (fun y => y⁻¹) h2
    simpa [mul_assoc] using h3.symm
  have hτinv : ∀ c ∈ U, τ⁻¹ c ∈ U := by
    rw [hU]
    exact commSub_top_stable151b (fun x hx => by rw [inv_inv, hinv' x hx]; exact L.inv_mem hx)
  have hτmem : τ ∈ stabSub U := by
    rw [mem_stabSub]
    intro u
    constructor
    · intro h
      simpa using hτinv (τ u) h
    · exact hτstab u
  have hlstab : ∀ c ∈ U, l c ∈ U := by
    rw [hU]
    exact commSub_top_stable151b (fun x hx => L.mul_mem (L.mul_mem hlL hx) (L.inv_mem hlL))
  have hUinv : ∀ x ∈ Subgroup.zpowers τ, ∀ w ∈ U, x w ∈ U := by
    intro x hx w hw
    have hx' : x ∈ stabSub U := (Subgroup.zpowers_le.mpr hτmem) hx
    exact (mem_stabSub.mp hx' w).mpr hw
  have hrank := rk_commSub_add_rk_inf_fixV (V := W) (g := τ) (W := U) hUinv
  rw [hrkU] at hrank
  set F : Subgroup W := U ⊓ fixV (Subgroup.zpowers τ) with hF
  have hdisj : F ⊓ F.map l.toMonoidHom = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro u hu
    rw [Subgroup.mem_inf] at hu
    obtain ⟨huF, huMap⟩ := hu
    have hτu : τ u = u := mem_fixV_zpowers_iff_apply.mp (Subgroup.mem_inf.mp huF).2
    obtain ⟨v, hvF, hvu⟩ := Subgroup.mem_map.mp huMap
    have hτv : τ v = v := mem_fixV_zpowers_iff_apply.mp (Subgroup.mem_inf.mp hvF).2
    have hvU : v ∈ U := (Subgroup.mem_inf.mp hvF).1
    have hτlv : τ (l v) = l⁻¹ v := by
      calc τ (l v) = (τ * l * τ⁻¹) (τ v) := by
            simp [MulAut.mul_apply, MulAut.inv_apply_self]
        _ = l⁻¹ v := by rw [hinv l hlL, hτv]
    rw [← hvu] at hτu
    simp only [MulEquiv.coe_toMonoidHom] at hτu
    have hlv : l v = l⁻¹ v := by
      rw [hτlv] at hτu
      exact hτu.symm
    have h2v : l (l v) = v := by
      calc l (l v) = l (l⁻¹ v) := by rw [hlv]
        _ = v := MulAut.apply_inv_self (M := W) l v
    have hlvv : l v = v := by
      have h3 : (l ^ 3) v = l v := by
        calc (l ^ 3) v = l (l (l v)) := by simp [pow_succ, MulAut.mul_apply]
          _ = l v := by rw [h2v]
      rw [hl3, MulAut.one_apply] at h3
      exact h3.symm
    have hvfix : v ∈ fixV L := by
      rw [← hgen]
      exact mem_fixV_zpowers_iff_apply.mpr hlvv
    have hvbot : v ∈ (⊥ : Subgroup W) := by
      rw [← hfix]
      exact Subgroup.mem_inf.mpr ⟨hvU, hvfix⟩
    rw [Subgroup.mem_bot] at hvbot
    rw [← hvu]
    rw [hvbot, map_one]
  have hmap_le : F.map l.toMonoidHom ≤ U := by
    intro x hx
    obtain ⟨v, hvF, rfl⟩ := Subgroup.mem_map.mp hx
    exact hlstab v (Subgroup.mem_inf.mp hvF).1
  have hsup_le : F ⊔ F.map l.toMonoidHom ≤ U := sup_le inf_le_left hmap_le
  have hcardF : rk F = rk (F.map l.toMonoidHom) := by
    unfold rk
    rw [Subgroup.card_map_of_injective l.injective]
  have hsum := rk_sup_add_rk_inf F (F.map l.toMonoidHom)
  rw [hdisj, rk_bot, hcardF] at hsum
  have hle6 : rk ↥(F ⊔ F.map l.toMonoidHom) ≤ 6 := by
    have h := rk_mono hsup_le
    rw [hrkU] at h
    exact h
  have hFle3 : rk F ≤ 3 := by omega
  omega

theorem s16h_even_rk_of_fpf_three {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)} (hL : Nat.card ↥L = 3) {X : Subgroup W}
    (hX : ∀ l ∈ L, ∀ u ∈ X, l u ∈ X) (hfix : X ⊓ fixV L = ⊥) : Even (rk ↥X) := by
  classical
  have hR : ∀ x ∈ L, x ≠ 1 → Nat.card ↥(X ⊓ fixV (Subgroup.zpowers x)) = 1 := by
    intro x hxL hxne
    have hgen : Subgroup.zpowers x = L := s16h_zpowers_eq_of_mem_of_ne_one hL hxL hxne
    have hbot : X ⊓ fixV (Subgroup.zpowers x) = ⊥ := by rw [hgen, hfix]
    rw [hbot, Subgroup.card_bot]
  have hdvd : Nat.card ↥L ∣ Nat.card ↥X - 1 :=
    s16h_card_dvd_sub_of_fix_card (R := L) (U := X) hX (c := 1) hR
  rw [hL] at hdvd
  have hcard : Nat.card ↥X = 2 ^ rk ↥X := card_eq_two_pow hW X
  have hmod : 2 ^ rk ↥X ≡ 1 [MOD 3] := by
    rw [← hcard]
    exact (Nat.modEq_iff_dvd' Nat.card_pos).mpr hdvd |>.symm
  exact s16h_even_of_two_pow_modEq_one hmod

theorem s16h_z3_commute_of_rk_le_two {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)} (hL : Nat.card ↥L = 3)
    (hrk : rk ↥(commSub (⊤ : Subgroup W) L) = 6)
    (hfix : commSub (⊤ : Subgroup W) L ⊓ fixV L = ⊥) {i : MulAut W}
    (hiL : i ∈ normalizer (L : Set (MulAut W)))
    (hri : rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers i)) ≤ 2) :
    ∀ l ∈ L, i * l = l * i := by
  rcases CFSG.Semidihedral.Principal.conj_eq_or_inv_of_mem_normalizer_of_card_three hL hiL with
    hcen | hinv
  · intro l hl
    have h := hcen l hl
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h
  · intro l hl
    exfalso
    have h3 := s16h_three_le_rk_of_inverts_Z3 hW hL hrk hfix hinv
    have hle : commSub (commSub (⊤ : Subgroup W) L) (Subgroup.zpowers i) ≤
        commSub (⊤ : Subgroup W) (Subgroup.zpowers i) :=
      commSub_mono le_top le_rfl
    have h4 := rk_mono hle
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

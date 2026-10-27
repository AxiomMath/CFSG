module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4RadM2Fam

public section

namespace CFSG.Quasithin.J4Rad

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2 CFSG.Quasithin.F134.J4E9
  CFSG.Quasithin.J4Loc

theorem not_isPrimePow_77 : ¬ IsPrimePow 77 := by
  rintro ⟨p, k, hp, hk, h⟩
  have hp' : Nat.Prime p := Nat.prime_iff.mpr hp
  have hdvd : p ∣ 77 := h ▸ dvd_pow_self p hk.ne'
  have h7 : p ∣ 7 * 11 := by simpa using hdvd
  rcases (Nat.Prime.dvd_mul hp').mp h7 with h | h
  · have : p = 7 := (Nat.prime_dvd_prime_iff_eq hp' (by norm_num)).mp h
    subst this
    have : k ≤ 2 := by
      by_contra hlt
      have : 7 ^ 3 ≤ 7 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases k
    all_goals omega
  · have : p = 11 := (Nat.prime_dvd_prime_iff_eq hp' (by norm_num)).mp h
    subst this
    have : k ≤ 1 := by
      by_contra hlt
      have : 11 ^ 2 ≤ 11 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases k
    all_goals omega

section Main


theorem le_C_of_solvable_normal (hF : J4Facts) {R : Subgroup J}
    (hRM : R ≤ Subgroup.centralizer ({z0} : Set J))
    (hN : Subgroup.centralizer ({z0} : Set J) ≤ Subgroup.normalizer (R : Set J))
    (hs : Group.IsSolvable ↥R) : R ≤ Subgroup.centralizer ({z0} : Set J) ⊓ Hj := by
  have hz0 : z0 ∈ Zl := z0_mem_Zl
  have hcard := card_centralizer_eq hF hz0
  have hCpos : 0 < Nat.card ↥(Subgroup.centralizer ({z0} : Set J) ⊓ Hj) := Nat.card_pos
  have hrel : ((Subgroup.centralizer ({z0} : Set J) ⊓ Hj).subgroupOf
      (Subgroup.centralizer ({z0} : Set J))).index = 77 := by
    have h := card_mul_relIndex (Subgroup.centralizer ({z0} : Set J))
      (Subgroup.centralizer ({z0} : Set J) ⊓ Hj) inf_le_left
    rw [hcard] at h
    generalize Nat.card ↥(Subgroup.centralizer ({z0} : Set J) ⊓ Hj) = c at h hCpos
    generalize ((Subgroup.centralizer ({z0} : Set J) ⊓ Hj).subgroupOf
      (Subgroup.centralizer ({z0} : Set J))).index = i at h ⊢
    have h' : c * i = c * 77 := by rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_left hCpos h'
  refine solvable_normal_le_of_maximal (G := Subgroup.centralizer ({z0} : Set J))
    (C := Subgroup.centralizer ({z0} : Set J) ⊓ Hj) inf_le_left ?_
    (centralizer_maximal hF hz0) ?_ hRM hN hs
  · intro h
    have h1 : ((Subgroup.centralizer ({z0} : Set J) ⊓ Hj).subgroupOf
        (Subgroup.centralizer ({z0} : Set J))).index = 1 := by
      rw [h, Subgroup.subgroupOf_self, Subgroup.index_top]
    rw [hrel] at h1
    omega
  · rw [Subgroup.relIndex, hrel]
    exact not_isPrimePow_77

theorem conj_w15 (hM : MatFacts) {w : List Int} (hw : ∀ ℓ ∈ w, ℓ ∈ letters) {W : List ℕ}
    (hW : W ∈ w15L) (hW' : imgW w W ∈ w15L) :
    conjSub (wordElt w) (maskSub W) = maskSub (imgW w W) :=
  conjSub_wordElt_maskSub hM hw (w15_subset_trio _ hW) (w15_subset_trio _ hW')

theorem maskSub_ne_w15 (hM : MatFacts) {A B : List ℕ} (hA : A ∈ w15L) (hB : B ∈ w15L)
    (h : A.toFinset ≠ B.toFinset) : maskSub A ≠ maskSub B :=
  maskSub_ne_of_toFinset_ne hM (w15_subset_trio _ hA) (w15_subset_trio _ hB) h

theorem rad_M2 (hF : J4Facts) {R : Subgroup J}
    (hRM : R ≤ Subgroup.centralizer ({z0} : Set J))
    (hN : Subgroup.centralizer ({z0} : Set J) ≤ Subgroup.normalizer (R : Set J))
    (hs : Group.IsSolvable ↥R) : ¬ 9 ∣ Nat.card ↥R := by
  have hM := hF.mat
  have hspec := c15_spec
  have hRC := le_C_of_solvable_normal hF hRM hN hs
  have hRH : R ≤ Hj := hRC.trans inf_le_right
  have hRK : R ≤ kerSub (Subgroup.centralizer ({z0} : Set J) ⊓ Hj) X15 := by
    intro r hr
    refine ⟨hRC hr, fun A hA => ?_⟩
    obtain ⟨W, hW, rfl⟩ := hA
    exact normalizes_maskSub hF hRH hN hW hr
  have hgA := wordElt_mem_C hM hspec.letA hspec.fixA
  have hgB := wordElt_mem_C hM hspec.letB hspec.fixB
  have h9 := nine_dvd_relIndex_kerSub (Subgroup.centralizer ({z0} : Set J) ⊓ Hj) X15
    (X15_closed hM) (wordElt wordA) (wordElt wordB) hgA hgB ?_ ?_ ?_ ?_ ?_ ?_ ?_
  ·
    have hker : kerSub (Subgroup.centralizer ({z0} : Set J) ⊓ Hj) X15 ≤
        Subgroup.centralizer ({z0} : Set J) ⊓ Hj := fun c hc => hc.1
    have hz0 : z0 ∈ Zl := z0_mem_Zl
    have hcardC := card_inf_Hj_of_mem_Zl hF hz0
    have hmul := card_mul_relIndex (Subgroup.centralizer ({z0} : Set J) ⊓ Hj)
      (kerSub (Subgroup.centralizer ({z0} : Set J) ⊓ Hj) X15) hker
    rw [hcardC] at hmul
    have hRdvd : Nat.card ↥R ∣ Nat.card ↥(kerSub (Subgroup.centralizer ({z0} : Set J) ⊓ Hj) X15) :=
      Subgroup.card_dvd_of_le hRK
    intro h9R
    have h99 := Nat.mul_dvd_mul (h9R.trans hRdvd) h9
    rw [Subgroup.relIndex] at h99
    generalize Nat.card ↥(kerSub (Subgroup.centralizer ({z0} : Set J) ⊓ Hj) X15) = a at hmul h99
    generalize ((kerSub (Subgroup.centralizer ({z0} : Set J) ⊓ Hj) X15).subgroupOf
      (Subgroup.centralizer ({z0} : Set J) ⊓ Hj)).index = b at hmul h99
    rw [hmul] at h99
    omega
  · rintro A ⟨W, hW, rfl⟩
    obtain ⟨hAW, hBW⟩ := hspec.memAB W hW
    have hBB := (hspec.memAB _ hBW).1
    have hAA := (hspec.memAB _ hAW).2
    rw [conj_w15 hM hspec.letB hW hBW, conj_w15 hM hspec.letA hBW hBB,
      conj_w15 hM hspec.letA hW hAW,
      conj_w15 hM hspec.letB hAW hAA, hspec.comm W hW]
  · rintro A ⟨W, hW, rfl⟩
    have h1 := (hspec.memAB W hW).1
    have h2 := (hspec.memAB _ h1).1
    have h3 : imgW wordA (imgW wordA (imgW wordA W)) ∈ w15L := by
      rw [hspec.ordA W hW]
      exact hW
    rw [conj_w15 hM hspec.letA hW h1, conj_w15 hM hspec.letA h1 h2,
      conj_w15 hM hspec.letA h2 h3, hspec.ordA W hW]
  · rintro A ⟨W, hW, rfl⟩
    have h1 := (hspec.memAB W hW).2
    have h2 := (hspec.memAB _ h1).2
    have h3 : imgW wordB (imgW wordB (imgW wordB W)) ∈ w15L := by
      rw [hspec.ordB W hW]
      exact hW
    rw [conj_w15 hM hspec.letB hW h1, conj_w15 hM hspec.letB h1 h2,
      conj_w15 hM hspec.letB h2 h3, hspec.ordB W hW]
  · obtain ⟨W, hW, hne⟩ := hspec.neA
    refine ⟨maskSub W, ⟨W, hW, rfl⟩, ?_⟩
    rw [conj_w15 hM hspec.letA hW (hspec.memAB W hW).1]
    exact maskSub_ne_w15 hM (hspec.memAB W hW).1 hW hne
  · obtain ⟨W, hW, hne⟩ := hspec.neB0
    refine ⟨maskSub W, ⟨W, hW, rfl⟩, ?_⟩
    rw [conj_w15 hM hspec.letB hW (hspec.memAB W hW).2]
    exact maskSub_ne_w15 hM (hspec.memAB W hW).2 hW hne
  · obtain ⟨W, hW, hne⟩ := hspec.neB1
    refine ⟨maskSub W, ⟨W, hW, rfl⟩, ?_⟩
    rw [conj_w15 hM hspec.letB hW (hspec.memAB W hW).2,
      conj_w15 hM hspec.letA hW (hspec.memAB W hW).1]
    exact maskSub_ne_w15 hM (hspec.memAB W hW).2 (hspec.memAB W hW).1 hne
  · obtain ⟨W, hW, hne⟩ := hspec.neB2
    refine ⟨maskSub W, ⟨W, hW, rfl⟩, ?_⟩
    have h1 := (hspec.memAB W hW).1
    have h2 := (hspec.memAB _ h1).1
    rw [conj_w15 hM hspec.letB hW (hspec.memAB W hW).2, conj_w15 hM hspec.letA hW h1,
      conj_w15 hM hspec.letA h1 h2]
    exact maskSub_ne_w15 hM (hspec.memAB W hW).2 h2 hne

end Main

end CFSG.Quasithin.J4Rad

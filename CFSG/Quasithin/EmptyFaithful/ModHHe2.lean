module

public import CFSG.Quasithin.EmptyFaithful.ModHHe1
public import CFSG.Quasithin.EmptyFaithful.ModHCfg2
public import CFSG.RankThree.PartOne.K1214.Basic
public import CFSG.Quasithin.EmptyFaithful.ModHSolv

public section

namespace CFSG.Quasithin.ModH.He2

open CFSG.QuasithinUnique.Ch1.SporLat.He (heIncl)
open CFSG.Open CFSG.Quasithin.ModH CFSG.Quasithin.ModH.He1

variable {J : Type} [Group J] [Finite J] (hl : HeLat J)

omit [Finite J] in
theorem card_map_aut (α : MulAut J) (X : Subgroup J) :
    Nat.card ↥(X.map α.toMonoidHom) = Nat.card ↥X :=
  (Nat.card_congr (X.equivMapOfInjective α.toMonoidHom α.injective).toEquiv).symm

omit [Finite J] in
theorem S_le_map {X : Subgroup J} {α : MulAut J} (hX : hl.S ≤ X)
    (hα : hl.S.map α.toMonoidHom = hl.S) : hl.S ≤ X.map α.toMonoidHom := by
  calc hl.S = hl.S.map α.toMonoidHom := hα.symm
    _ ≤ X.map α.toMonoidHom := Subgroup.map_mono hX

omit [Finite J] in
theorem Y_le {j jj : ℕ} (hj : j < 11) (hjj : jj < 11) (h : jj ∈ heIncl[j]!) :
    hl.Y j ≤ hl.Y jj := (hl.le_iff hj hjj).2 h

omit [Finite J] in
theorem Y_not_le {j jj : ℕ} (hj : j < 11) (hjj : jj < 11) (h : jj ∉ heIncl[j]!) :
    ¬ hl.Y j ≤ hl.Y jj := fun hle => h ((hl.le_iff hj hjj).1 hle)

omit [Finite J] in
theorem card_Y3 : Nat.card ↥(hl.Y 3) = 138240 := by
  rw [hl.card_Y 3 (by norm_num)]; rfl

omit [Finite J] in
theorem card_Y4 : Nat.card ↥(hl.Y 4) = 138240 := by
  rw [hl.card_Y 4 (by norm_num)]; rfl

omit [Finite J] in
theorem card_Y2 : Nat.card ↥(hl.Y 2) = 9216 := by
  rw [hl.card_Y 2 (by norm_num)]; rfl

omit [Finite J] in
theorem card_Y5 : Nat.card ↥(hl.Y 5) = 9216 := by
  rw [hl.card_Y 5 (by norm_num)]; rfl

omit [Finite J] in
theorem card_Y9 : Nat.card ↥(hl.Y 9) = 9216 := by
  rw [hl.card_Y 9 (by norm_num)]; rfl

omit [Finite J] in
theorem Y3_ne_Y4 : hl.Y 3 ≠ hl.Y 4 := fun h =>
  Y_not_le hl (j := 3) (jj := 4) (by norm_num) (by norm_num) (by decide) (h ▸ le_refl _)

omit [Finite J] in
theorem Y2_ne_Y5 : hl.Y 2 ≠ hl.Y 5 := fun h =>
  Y_not_le hl (j := 2) (jj := 5) (by norm_num) (by norm_num) (by decide) (h ▸ le_refl _)

omit [Finite J] in
theorem Y2_ne_Y9 : hl.Y 2 ≠ hl.Y 9 := fun h =>
  Y_not_le hl (j := 2) (jj := 9) (by norm_num) (by norm_num) (by decide) (h ▸ le_refl _)

omit [Finite J] in
theorem aut_Y34 {α : MulAut J} (hα : hl.S.map α.toMonoidHom = hl.S) :
    ((hl.Y 3).map α.toMonoidHom = hl.Y 3 ∧ (hl.Y 4).map α.toMonoidHom = hl.Y 4) ∨
      ((hl.Y 3).map α.toMonoidHom = hl.Y 4 ∧ (hl.Y 4).map α.toMonoidHom = hl.Y 3) := by
  have hinj := Subgroup.map_injective (f := α.toMonoidHom) α.injective
  have h3 := eq_Y3_or_Y4 hl (S_le_map hl (hl.S_le_Y 3) hα) (by rw [card_map_aut, card_Y3 hl])
  have h4 := eq_Y3_or_Y4 hl (S_le_map hl (hl.S_le_Y 4) hα) (by rw [card_map_aut, card_Y4 hl])
  rcases h3 with h3 | h3 <;> rcases h4 with h4 | h4
  · exact absurd (hinj (h3.trans h4.symm)) (Y3_ne_Y4 hl)
  · exact Or.inl ⟨h3, h4⟩
  · exact Or.inr ⟨h3, h4⟩
  · exact absurd (hinj (h3.trans h4.symm)) (Y3_ne_Y4 hl)

theorem normalizes_of_fixed {A : Set (MulAut J)} {Yb : Subgroup J}
    (hd : Config2 J A hl.S Yb) {w : ℕ} (hw : w = 3 ∨ w = 4)
    (hZW : Yb ⊔ hl.S ≤ hl.Y w) (hfix : ∀ α ∈ A, (hl.Y w).map α.toMonoidHom = hl.Y w) :
    hl.Y w ≤ Subgroup.normalizer (Yb : Set J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNp : IsPGroup 2 ↥(pCoreOf 2 (hl.Y w)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hZN : Yb ⊔ hl.S ≤ Subgroup.normalizer ((pCoreOf 2 (hl.Y w) : Subgroup J) : Set J) :=
    hZW.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hinv : ∀ α ∈ A, (pCoreOf 2 (hl.Y w)).map α.toMonoidHom = pCoreOf 2 (hl.Y w) := by
    intro α hα
    have h := CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 α (hl.Y w)
    rw [hfix α hα] at h
    exact h.symm
  have hmax := hd.maximal _ hNp (hl.o2_ne_bot w hw) hZN hinv (normalizer_pCore_ne_top hl hw)
  exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _).trans hmax

omit [Finite J] in
theorem not_normal {Yb : Subgroup J} {a a' w : ℕ} (ha : a < 11) (ha' : a' < 11) (hw : w < 11)
    (hZ : Yb ⊔ hl.S = hl.Y a) (hca : Nat.card ↥(hl.Y a) = 9216)
    (hca' : Nat.card ↥(hl.Y a') = 9216) (hcw : Nat.card ↥(hl.Y w) = 138240)
    (huniq : ∀ j < 11, j ∈ heIncl[a]! → j ∈ heIncl[a']! → w ∈ heIncl[j]! → j = w)
    (haw : hl.Y a ≤ hl.Y w) (ha'w : hl.Y a' ≤ hl.Y w)
    (hnorm : hl.Y w ≤ Subgroup.normalizer (Yb : Set J)) : False := by
  have hYbZ : Yb ≤ hl.Y a := hZ ▸ le_sup_left
  have hB : hl.Y a' ≤ Subgroup.normalizer (Yb : Set J) := ha'w.trans hnorm
  have hprod := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hB
  have hSW' : hl.S ≤ Yb ⊔ hl.Y a' := (hl.S_le_Y a').trans le_sup_right
  have hle1 : Yb ⊔ hl.Y a' ≤ hl.Y w := sup_le (hYbZ.trans haw) ha'w
  have hYa : hl.Y a ≤ Yb ⊔ hl.Y a' := by
    rw [← hZ]
    exact sup_le_sup_left (hl.S_le_Y a') Yb
  have heq : Yb ⊔ hl.Y a' = hl.Y w := by
    rcases member_of_complete hl hSW' with ⟨j, hj, hjeq⟩ | htop
    · have h1 : hl.Y a ≤ hl.Y j := hjeq ▸ hYa
      have h2 : hl.Y a' ≤ hl.Y j := hjeq ▸ le_sup_right
      have h3 : hl.Y j ≤ hl.Y w := hjeq ▸ hle1
      have hjw := huniq j hj ((hl.le_iff ha hj).1 h1) ((hl.le_iff ha' hj).1 h2)
        ((hl.le_iff hj hw).1 h3)
      rw [hjeq, hjw]
    · exfalso
      rw [htop] at hle1
      have : hl.Y w = ⊤ := top_le_iff.1 hle1
      have h4 := congrArg (fun K : Subgroup J => Nat.card ↥K) this
      rw [hcw, card_top hl] at h4
      omega
  rw [heq, hcw, hca'] at hprod
  have hdvd : Nat.card ↥Yb ∣ 9216 := hca ▸ Subgroup.card_dvd_of_le hYbZ
  have h5 : 5 ∣ Nat.card ↥Yb * 9216 := by
    rw [← hprod]
    exact Dvd.dvd.mul_right (by norm_num) _
  rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 5)).1 h5 with h | h
  · have := h.trans hdvd
    omega
  · omega

omit [Finite J] in
theorem swap_contra {A : Set (MulAut J)} {Yb : Subgroup J} (hd : Config2 J A hl.S Yb)
    (hZ : Yb ⊔ hl.S = hl.Y 2) {α : MulAut J} (hα : α ∈ A)
    (h34 : (hl.Y 3).map α.toMonoidHom = hl.Y 4) : False := by
  have hαS := hd.inv_S α hα
  have hαZ : (hl.Y 2).map α.toMonoidHom = hl.Y 2 := by
    rw [← hZ, Subgroup.map_sup, hd.inv_Y α hα, hαS]
  have hinj := Subgroup.map_injective (f := α.toMonoidHom) α.injective
  have h43 : (hl.Y 4).map α.toMonoidHom = hl.Y 3 := by
    rcases aut_Y34 hl hαS with ⟨h3, -⟩ | ⟨-, h4⟩
    · exact absurd (h3.symm.trans h34) (Y3_ne_Y4 hl)
    · exact h4
  have h59 : (hl.Y 5).map α.toMonoidHom = hl.Y 9 := by
    have hle : (hl.Y 5).map α.toMonoidHom ≤ hl.Y 4 := by
      rw [← h34]
      exact Subgroup.map_mono (Y_le hl (j := 5) (jj := 3) (by norm_num) (by norm_num) (by decide))
    have hS' := S_le_map hl (hl.S_le_Y 5) hαS
    have hc : Nat.card ↥((hl.Y 5).map α.toMonoidHom) = 9216 := by rw [card_map_aut, card_Y5 hl]
    rcases eq_Y2_Y5_Y9 hl hS' hc with h | h | h
    · exact absurd (hinj (h.trans hαZ.symm)) (Y2_ne_Y5 hl).symm
    · rw [h] at hle
      exact (Y_not_le hl (j := 5) (jj := 4) (by norm_num) (by norm_num) (by decide) hle).elim
    · exact h
  have h95 : (hl.Y 9).map α.toMonoidHom = hl.Y 5 := by
    have hle : (hl.Y 9).map α.toMonoidHom ≤ hl.Y 3 := by
      rw [← h43]
      exact Subgroup.map_mono (Y_le hl (j := 9) (jj := 4) (by norm_num) (by norm_num) (by decide))
    have hS' := S_le_map hl (hl.S_le_Y 9) hαS
    have hc : Nat.card ↥((hl.Y 9).map α.toMonoidHom) = 9216 := by rw [card_map_aut, card_Y9 hl]
    rcases eq_Y2_Y5_Y9 hl hS' hc with h | h | h
    · exact absurd (hinj (h.trans hαZ.symm)) (Y2_ne_Y9 hl).symm
    · exact h
    · rw [h] at hle
      exact (Y_not_le hl (j := 9) (jj := 3) (by norm_num) (by norm_num) (by decide) hle).elim
  obtain ⟨g, hSg, hgZ, hgne, hg3, hig⟩ := hd.third
  rw [hZ] at hgZ hgne
  have hg := hig α hα
  rcases member_of_complete hl hSg with ⟨j, hj, rfl⟩ | rfl
  · have hj2 : 2 ∈ heIncl[j]! := (hl.le_iff hj (by norm_num)).1 hgZ
    have hcases : ∀ j < 11, 2 ∈ heIncl[j]! → j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 6 := by decide
    rcases hcases j hj hj2 with rfl | rfl | rfl | rfl
    · rw [hl.card_Y 0 (by norm_num)] at hg3
      revert hg3
      decide
    ·
      have h1 : (hl.Y 1).map α.toMonoidHom ≤ (hl.Y 9).map α.toMonoidHom :=
        Subgroup.map_mono (Y_le hl (j := 1) (jj := 9) (by norm_num) (by norm_num) (by decide))
      rw [hg, h95] at h1
      exact Y_not_le hl (j := 1) (jj := 5) (by norm_num) (by norm_num) (by decide) h1
    · exact hgne rfl
    ·
      have h1 : (hl.Y 6).map α.toMonoidHom ≤ (hl.Y 5).map α.toMonoidHom :=
        Subgroup.map_mono (Y_le hl (j := 6) (jj := 5) (by norm_num) (by norm_num) (by decide))
      rw [hg, h59] at h1
      exact Y_not_le hl (j := 6) (jj := 9) (by norm_num) (by norm_num) (by decide) h1
  · have : hl.Y 2 = ⊤ := top_le_iff.1 hgZ
    have h4 := congrArg (fun K : Subgroup J => Nat.card ↥K) this
    rw [card_Y2 hl, card_top hl] at h4
    omega

theorem not_config2_he {A : Set (MulAut J)} {Yb : Subgroup J} (hd : Config2 J A hl.S Yb) :
    False := by
  have hZs : Group.IsSolvable ↥(Yb ⊔ hl.S) :=
    isSolvable_sup_of_le_normalizer hd.solvable hl.S_pgroup hd.normalizes
  have h9 : 9 ∣ Nat.card ↥(Yb ⊔ hl.S) := hd.nine.trans (Subgroup.card_dvd_of_le le_sup_left)
  have hαZ : ∀ α ∈ A, (Yb ⊔ hl.S).map α.toMonoidHom = Yb ⊔ hl.S := by
    intro α hα
    rw [Subgroup.map_sup, hd.inv_Y α hα, hd.inv_S α hα]
  rcases Z_cases hl hd.nonsolvable le_sup_right hZs h9 with hZ | hZ | hZ
  ·
    by_cases hfix : ∀ α ∈ A, (hl.Y 3).map α.toMonoidHom = hl.Y 3
    · have hnorm := normalizes_of_fixed hl hd (Or.inl rfl) (hZ ▸ Y_le hl (j := 2) (jj := 3)
        (by norm_num) (by norm_num) (by decide)) hfix
      exact not_normal hl (a := 2) (a' := 5) (w := 3) (by norm_num) (by norm_num) (by norm_num) hZ
        (card_Y2 hl) (card_Y5 hl) (card_Y3 hl) (by decide)
        (Y_le hl (by norm_num) (by norm_num) (by decide))
        (Y_le hl (by norm_num) (by norm_num) (by decide)) hnorm
    · obtain ⟨α, hα, hne⟩ : ∃ α ∈ A, (hl.Y 3).map α.toMonoidHom ≠ hl.Y 3 := by
        by_contra hcon
        exact hfix (fun α hα => by
          by_contra hne
          exact hcon ⟨α, hα, hne⟩)
      rcases aut_Y34 hl (hd.inv_S α hα) with ⟨h3, -⟩ | ⟨h3, -⟩
      · exact absurd h3 hne
      · exact swap_contra hl hd hZ hα h3
  ·
    have hfix : ∀ α ∈ A, (hl.Y 3).map α.toMonoidHom = hl.Y 3 := by
      intro α hα
      rcases aut_Y34 hl (hd.inv_S α hα) with ⟨h3, -⟩ | ⟨h3, -⟩
      · exact h3
      · exfalso
        have h1 : (hl.Y 5).map α.toMonoidHom ≤ (hl.Y 3).map α.toMonoidHom :=
          Subgroup.map_mono (Y_le hl (j := 5) (jj := 3) (by norm_num) (by norm_num) (by decide))
        rw [← hZ, hαZ α hα, h3, hZ] at h1
        exact Y_not_le hl (j := 5) (jj := 4) (by norm_num) (by norm_num) (by decide) h1
    have hnorm := normalizes_of_fixed hl hd (Or.inl rfl) (hZ ▸ Y_le hl (j := 5) (jj := 3)
      (by norm_num) (by norm_num) (by decide)) hfix
    exact not_normal hl (a := 5) (a' := 2) (w := 3) (by norm_num) (by norm_num) (by norm_num) hZ
      (card_Y5 hl) (card_Y2 hl) (card_Y3 hl) (by decide)
      (Y_le hl (by norm_num) (by norm_num) (by decide))
      (Y_le hl (by norm_num) (by norm_num) (by decide)) hnorm
  ·
    have hfix : ∀ α ∈ A, (hl.Y 4).map α.toMonoidHom = hl.Y 4 := by
      intro α hα
      rcases aut_Y34 hl (hd.inv_S α hα) with ⟨-, h4⟩ | ⟨-, h4⟩
      · exact h4
      · exfalso
        have h1 : (hl.Y 9).map α.toMonoidHom ≤ (hl.Y 4).map α.toMonoidHom :=
          Subgroup.map_mono (Y_le hl (j := 9) (jj := 4) (by norm_num) (by norm_num) (by decide))
        rw [← hZ, hαZ α hα, h4, hZ] at h1
        exact Y_not_le hl (j := 9) (jj := 3) (by norm_num) (by norm_num) (by decide) h1
    have hnorm := normalizes_of_fixed hl hd (Or.inr rfl) (hZ ▸ Y_le hl (j := 9) (jj := 4)
      (by norm_num) (by norm_num) (by decide)) hfix
    exact not_normal hl (a := 9) (a' := 2) (w := 4) (by norm_num) (by norm_num) (by norm_num) hZ
      (card_Y9 hl) (card_Y2 hl) (card_Y4 hl) (by decide)
      (Y_le hl (by norm_num) (by norm_num) (by decide))
      (Y_le hl (by norm_num) (by norm_num) (by decide)) hnorm

end CFSG.Quasithin.ModH.He2

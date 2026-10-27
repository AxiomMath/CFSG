module

public import CFSG.LocalAnalysis.StandardType.GGInnerD4Regimes
public import CFSG.LocalAnalysis.StandardType.GGK1ScMain
public import CFSG.LocalAnalysis.StandardType.GGMultTableCl
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ltrd4a_three_dvd (n : ℕ) : 3 ∣ 2 ^ n - 1 ∨ 3 ∣ 2 ^ n + 1 := by
  induction n with
  | zero => left; norm_num
  | succ n ih =>
    rcases ih with h | h
    · right
      obtain ⟨k, hk⟩ := h
      have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      refine ⟨2 * k + 1, ?_⟩
      rw [pow_succ]; omega
    · left
      obtain ⟨k, hk⟩ := h
      have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      refine ⟨2 * k - 1, ?_⟩
      rw [pow_succ]; omega

private def ltrd4a_Sunion (lab : LargeEvenLabel) : Prop :=
  ((lab.tag = .A ∧ ¬ (3 ∣ lab.rank + 1 ∧ 3 ∣ 2 ^ lab.n - 1)) ∨
    (lab.tag = .twA ∧ ¬ (3 ∣ lab.rank + 1 ∧ 3 ∣ 2 ^ lab.n + 1))) ∨
  ((lab.tag = .D ∨ lab.tag = .twD) ∧ lab.rank ≤ 3)

private theorem ltrd4a_generic {lab : LargeEvenLabel} (hS : ltrd4a_Sunion lab) :
    GGKacGenericCl lab 3 := by
  refine ⟨by norm_num, by norm_num, ltrd4a_three_dvd lab.n, ?_, ?_, ?_⟩
  · rcases hS with (h | h) | h
    · exact Or.inl h.1
    · exact Or.inr (Or.inl h.1)
    · rcases h.1 with hD | htwD
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hD))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr htwD))))
  · rintro ⟨hA, h1, h2⟩
    rcases hS with (h | h) | h
    · exact h.2 ⟨h1, h2⟩
    · exact absurd (hA.symm.trans h.1) (by decide)
    · rcases h.1 with hD | htwD
      · exact absurd (hA.symm.trans hD) (by decide)
      · exact absurd (hA.symm.trans htwD) (by decide)
  · rintro ⟨hA, h1, h2⟩
    rcases hS with (h | h) | h
    · exact absurd (hA.symm.trans h.1) (by decide)
    · exact h.2 ⟨h1, h2⟩
    · rcases h.1 with hD | htwD
      · exact absurd (hA.symm.trans hD) (by decide)
      · exact absurd (hA.symm.trans htwD) (by decide)

private theorem ltrd4a_blockA_tag (r nf d : ℕ) :
    (ggMultBlockA r nf d).lab.tag = .A ∨ (ggMultBlockA r nf d).lab.tag = .twA := by
  unfold ggMultBlockA
  split_ifs <;> simp

private theorem ltrd4a_datumA_tag {p nf d : ℕ} {tw : Bool} {m : List ℕ} {o : GGKacOrbit}
    (ho : o ∈ (ggMultDatumA p nf d tw m).orbits) :
    o.lab.tag = .A ∨ o.lab.tag = .twA := by
  unfold ggMultDatumA at ho
  dsimp only at ho
  by_cases htriv : (tw = false ∧ d = 1) ∨ (tw = true ∧ d = 2)
  · rw [if_pos htriv] at ho
    dsimp only at ho
    rw [List.mem_map] at ho
    obtain ⟨j, -, rfl⟩ := ho
    exact ltrd4a_blockA_tag _ _ _
  · rw [if_neg htriv] at ho
    dsimp only at ho
    rw [List.mem_append] at ho
    rcases ho with ho | ho
    · by_cases hhead : 2 ≤ m.headD 0
      · rw [if_pos hhead] at ho
        by_cases htw : tw = false
        · rw [if_pos htw] at ho
          rw [List.mem_singleton] at ho
          subst ho
          exact Or.inl rfl
        · rw [if_neg htw] at ho
          rw [List.mem_singleton] at ho
          subst ho
          exact ltrd4a_blockA_tag _ _ _
      · rw [if_neg hhead] at ho
        simp at ho
    · rw [List.mem_map] at ho
      obtain ⟨j, -, rfl⟩ := ho
      exact Or.inl rfl

private theorem ltrd4a_A_table_no_D {r p n : ℕ} {tw : Bool} {D : GGKacDatum}
    (hmem : D ∈ ggMultTableCl (.A r) tw p n) {o : GGKacOrbit} (ho : o ∈ D.orbits) :
    o.lab.tag ≠ .D := by
  have hd : ggMultOrd p n ≠ 0 := by
    intro h0
    have hnil : ggMultTableCl (.A r) tw p n = [] := by
      simp [ggMultTableCl, h0]
    rw [hnil] at hmem
    simp at hmem
  obtain ⟨m', -, -, -, hD'⟩ := (mem_ggMultTableCl_A hd).mp hmem
  rw [hD'] at ho
  rcases ltrd4a_datumA_tag ho with h | h <;> rw [h] <;> decide

private theorem ltrd4a_typeCl_A {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hS : ltrd4a_Sunion lab) {T : GGKacTypeCl} {tw : Bool} {m : ℕ}
    (hT : ggKacTypeClOfLabel lab = some (T, tw, m)) :
    ∃ r' : ℕ, T = .A r' := by
  obtain ⟨tag, r, n⟩ := lab
  rcases hS with (h | h) | h
  · have ht : tag = .A := h.1
    subst ht
    simp [ggKacTypeClOfLabel] at hT
    exact ⟨r, hT.1.symm⟩
  · have ht : tag = .twA := h.1
    subst ht
    simp [ggKacTypeClOfLabel] at hT
    exact ⟨r, hT.1.symm⟩
  · have hrk : r ≤ 3 := h.2
    rcases h.1 with hD | htwD
    · have ht : tag = .D := hD
      subst ht
      have hrank : 3 ≤ r := hΛ.2
      have hr3 : r = 3 := by omega
      subst hr3
      simp [ggKacTypeClOfLabel] at hT
      exact ⟨3, hT.1.symm⟩
    · have ht : tag = .twD := htwD
      subst ht
      have hrank : 2 ≤ r := hΛ.2
      have hr : r = 2 ∨ r = 3 := by omega
      rcases hr with hr2 | hr3
      · subst hr2
        simp [ggKacTypeClOfLabel] at hT
        exact ⟨1, hT.1.symm⟩
      · subst hr3
        simp [ggKacTypeClOfLabel] at hT
        exact ⟨3, hT.1.symm⟩

private theorem ltrd4a_no_D {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hS : ltrd4a_Sunion lab) {D : GGKacDatum} (hD : GGMultValidCl lab 3 D)
    {o : GGKacOrbit} (ho : o ∈ D.orbits) : o.lab.tag ≠ .D := by
  obtain ⟨T, tw, m, hT, hmem⟩ := hD
  obtain ⟨r', hr'⟩ := ltrd4a_typeCl_A hΛ hS hT
  subst hr'
  exact ltrd4a_A_table_no_D hmem ho

private theorem ltrd4a_iso_eq {o_lab labJ : LargeEvenLabel}
    (htag : labJ.tag = .D) (hrk : labJ.rank = 4) (hiso : GGLabelIso o_lab labJ) :
    o_lab = labJ := by
  obtain ⟨t, r, n⟩ := labJ
  have ht : t = .D := by simpa using htag
  have hr : r = 4 := by simpa using hrk
  subst ht
  subst hr
  unfold GGLabelIso at hiso
  rcases hiso with h | h | h | h | h | h | h | h <;> simp_all

private theorem ltrd4a_datum
    (hB : GGK0MainBS GGKacGenericCl GGMultValidCl)
    {L : Type} [Group L] [Finite L] {J : Subgroup L} {y : MulAut L}
    {E : Subgroup (MulAut L)} {labL : LargeEvenLabel}
    (hΛL : LargeEvenInLambda2 labL)
    (hgen : GGKacGenericCl labL 3) (hperfL : commutator L = ⊤)
    (hraw : LargeEvenRawDatum labL (fun R _ I F =>
      IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : L ⧸ Subgroup.center L ≃* R, GGInducedInn E θ I))
    (hyE : y ∈ E) (hy3 : y ^ 3 = 1)
    (hcomp : IsComponentOf J (ggAutFixedSubgroup y)) :
    ∃ D : GGKacDatum, GGMultValidCl labL 3 D ∧ ∃ o ∈ D.orbits,
      LargeEvenInLambda2 o.lab ∧ GGHasLabel o.lab (J ⧸ Subgroup.center J) := by
  have hmain := hB 3 labL hΛL hgen _ hraw
  obtain ⟨R, hRgrp, I, F, hQR⟩ := largeEvenRawDatum_exists hmain
  obtain ⟨hsimple, hna, θ, hInd⟩ := hQR.1
  let ψ : L →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hψ : Function.Surjective ψ := by
    intro r
    obtain ⟨q, hq⟩ := θ.surjective r
    obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (Subgroup.center L) q
    refine ⟨l, ?_⟩
    show θ (QuotientGroup.mk' (Subgroup.center L) l) = r
    rw [hl]
    exact hq
  have hker_le : ψ.ker ≤ Subgroup.center L := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl
    have hl' : θ (QuotientGroup.mk' (Subgroup.center L) l) = 1 := by simpa [ψ] using hl
    have hl'' : QuotientGroup.mk' (Subgroup.center L) l = 1 :=
      θ.injective (by simpa using hl')
    exact (QuotientGroup.eq_one_iff l).mp hl''
  have hfixsub : ggFixSub y = ggAutFixedSubgroup y := by ext l; rfl
  have hcomp' : IsComponentOf J (ggFixSub y) := by rw [hfixsub]; exact hcomp
  have hφ_apply : ∀ l : L, ggInducedAut θ y (ψ l) = ψ (y l) := by
    intro l
    change ggInducedAut θ y (θ (l : L ⧸ Subgroup.center L)) =
      θ ((y l : L) : L ⧸ Subgroup.center L)
    exact ggInducedAut_apply θ y l
  have hφ_mem : ggInducedAut θ y ∈ I := hInd y hyE
  obtain ⟨D, hDval, ha, -⟩ :=
    hQR.2 L ψ hψ hker_le hperfL y hy3 ⟨ggInducedAut θ y, hφ_mem, hφ_apply⟩
  obtain ⟨o, ho, hqs, hdvd, hΛo, hHasO⟩ := ha J hcomp'
  exact ⟨D, hDval, o, ho, hΛo, hHasO⟩

private theorem ltrd4a_vacuous :
    GGInnerOnD4On ltrd4a_Sunion := by
  intro X _ _ A σ J hA hσ hJ hN hmark labJ hΛJ htag hrk hlab a ha
  exfalso
  obtain ⟨hX, lab', hΛlab', hrawS⟩ := hmark
  have hraw : LargeEvenRawDatum lab' (fun R _ I F =>
      IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : X ⧸ Subgroup.center X ≃* R, GGInducedInn A θ I) :=
    largeEvenRawDatum_mono (fun R _ I F h => by
      obtain ⟨hs, hna, θ, -, hInd⟩ := h
      exact ⟨hs, hna, θ, hInd⟩) hrawS
  have hS : ltrd4a_Sunion lab' := by
    obtain ⟨R₀, _, I₀, F₀, hQR₀⟩ := largeEvenRawDatum_exists hrawS
    obtain ⟨-, -, -, hS, -⟩ := hQR₀
    exact hS
  have hgen : GGKacGenericCl lab' 3 := ltrd4a_generic hS
  have hσ3 : σ ^ 3 = 1 := hA.2 σ hσ
  obtain ⟨D, hDval, o, ho, hΛo, hHasO⟩ :=
    ltrd4a_datum ggK0MainBS_cl hΛlab' hgen hX hraw hσ hσ3 hJ
  have hiso : GGLabelIso o.lab labJ :=
    ggLabelRigidInput_holds o.lab labJ (J ⧸ Subgroup.center J) hΛo hΛJ hHasO hlab
  have hoeq : o.lab = labJ := ltrd4a_iso_eq htag hrk hiso
  have hnoD : o.lab.tag ≠ .D := ltrd4a_no_D hΛlab' hS hDval ho
  have htagD : o.lab.tag = .D := by rw [hoeq]; exact htag
  exact hnoD htagD

theorem ggInnerOnD4_tagAGen :
    GGInnerOnD4On fun lab =>
      (lab.tag = .A ∧ ¬ (3 ∣ lab.rank + 1 ∧ 3 ∣ 2 ^ lab.n - 1)) ∨
        (lab.tag = .twA ∧ ¬ (3 ∣ lab.rank + 1 ∧ 3 ∣ 2 ^ lab.n + 1)) :=
  GGInnerOnD4On.mono (fun lab h => Or.inl h) ltrd4a_vacuous

theorem ggInnerOnD4_tagDLow :
    GGInnerOnD4On fun lab => (lab.tag = .D ∨ lab.tag = .twD) ∧ lab.rank ≤ 3 :=
  GGInnerOnD4On.mono (fun lab h => Or.inr h) ltrd4a_vacuous

end CFSG.StandardType

end

module

public import CFSG.LocalAnalysis.StandardType.GGInnerD4Regimes
public import CFSG.LocalAnalysis.StandardType.GGK1ScMain
public import CFSG.LocalAnalysis.StandardType.GGMultTableCl
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ltrd4b_three_dvd (n : ℕ) : 3 ∣ 2 ^ n - 1 ∨ 3 ∣ 2 ^ n + 1 := by
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

private theorem ltrd4b_typeCl {lab : LargeEvenLabel} {T : GGKacTypeCl} {tw : Bool} {m : ℕ}
    (h : ggKacTypeClOfLabel lab = some (T, tw, m))
    (hΛ : LargeEvenInLambda2 lab) (hS : lab.tag = .B ∨ lab.tag = .C) :
    T = .C lab.rank ∧ tw = false ∧ m = lab.n := by
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨-, hΛ'⟩ := hΛ
  have hr : 2 ≤ r := by
    rcases hS with h | h
    · rw [h] at hΛ'; exact hΛ'.1
    · rw [h] at hΛ'; exact hΛ'.1
  rcases hS with ht | ht
  · subst ht
    simp only [ggKacTypeClOfLabel, if_pos hr, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩
  · subst ht
    simp only [ggKacTypeClOfLabel, if_pos hr, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

private theorem ltrd4b_ord_ne_zero {n : ℕ} (h : 3 ∣ 2 ^ n - 1 ∨ 3 ∣ 2 ^ n + 1) :
    ggMultOrd 3 n ≠ 0 := by
  rcases h with h | h
  · simp only [ggMultOrd, if_pos h]; norm_num
  · have hnot : ¬ (3 ∣ 2 ^ n - 1) := by
      intro h1
      have h2 : 3 ∣ 2 ^ n + 1 - (2 ^ n - 1) :=
        Nat.dvd_sub h h1
      have hdiff : 2 ^ n + 1 - (2 ^ n - 1) = 2 := by
        have := Nat.one_le_two_pow (n := n); omega
      rw [hdiff] at h2
      norm_num at h2
    simp only [ggMultOrd, if_neg hnot, if_pos h]; norm_num

private theorem ltrd4b_blockA_tag (r nf d : ℕ) :
    (ggMultBlockA r nf d).lab.tag = .A ∨ (ggMultBlockA r nf d).lab.tag = .twA := by
  unfold ggMultBlockA
  split_ifs <;> simp

private theorem ltrd4b_datumC_orbit_tag {p nf d : ℕ} {m : List ℕ} {o : GGKacOrbit}
    (ho : o ∈ (ggMultDatumC p nf d m).orbits) :
    o.lab.tag = .A ∨ o.lab.tag = .twA ∨ o.lab.tag = .B2der ∨ o.lab.tag = .C := by
  unfold ggMultDatumC at ho
  dsimp only at ho
  rw [List.mem_append] at ho
  rcases ho with ho | ho
  · split_ifs at ho
    all_goals simp_all
  · rw [List.mem_map] at ho
    obtain ⟨j, -, rfl⟩ := ho
    rcases ltrd4b_blockA_tag (m.getD j 0 - 1) nf d with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

private theorem ltrd4b_datumC_no_D {p nf d : ℕ} {m : List ℕ} {o : GGKacOrbit}
    (ho : o ∈ (ggMultDatumC p nf d m).orbits) : o.lab.tag ≠ .D := by
  rcases ltrd4b_datumC_orbit_tag ho with h | h | h | h <;> rw [h] <;> decide

private theorem ltrd4b_iso_eq {o_lab labJ : LargeEvenLabel}
    (htag : labJ.tag = .D) (hrk : labJ.rank = 4) (hiso : GGLabelIso o_lab labJ) :
    o_lab = labJ := by
  obtain ⟨t, r, n⟩ := labJ
  have ht : t = .D := by simpa using htag
  have hr : r = 4 := by simpa using hrk
  subst ht
  subst hr
  unfold GGLabelIso at hiso
  rcases hiso with h | h | h | h | h | h | h | h <;> simp_all

private theorem ltrd4b_datum
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

theorem ggInnerOnD4_tagBC :
    GGInnerOnD4On fun lab => lab.tag = .B ∨ lab.tag = .C := by
  intro X _ _ A σ J hA hσ hJ hN hmark labJ hΛJ htag hrk hlab a ha
  exfalso
  obtain ⟨hX, lab', hΛlab', hrawS⟩ := hmark
  have hraw : LargeEvenRawDatum lab' (fun R _ I F =>
      IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : X ⧸ Subgroup.center X ≃* R, GGInducedInn A θ I) :=
    largeEvenRawDatum_mono (fun R _ I F h => by
      obtain ⟨hs, hna, θ, -, hInd⟩ := h
      exact ⟨hs, hna, θ, hInd⟩) hrawS
  have hS : lab'.tag = .B ∨ lab'.tag = .C := by
    obtain ⟨R₀, _, I₀, F₀, hQR₀⟩ := largeEvenRawDatum_exists hrawS
    obtain ⟨-, -, -, hS, -⟩ := hQR₀
    exact hS
  have hgen : GGKacGenericCl lab' 3 := by
    refine ⟨by norm_num, by norm_num, ltrd4b_three_dvd lab'.n, ?_, ?_, ?_⟩
    · rcases hS with h | h <;> rw [h]
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · rintro ⟨hA, -⟩
      rcases hS with h | h <;> rw [h] at hA <;> exact absurd hA (by decide)
    · rintro ⟨hA, -⟩
      rcases hS with h | h <;> rw [h] at hA <;> exact absurd hA (by decide)
  have hσ3 : σ ^ 3 = 1 := hA.2 σ hσ
  obtain ⟨D, hDval, o, ho, hΛo, hHasO⟩ :=
    ltrd4b_datum ggK0MainBS_cl hΛlab' hgen hX hraw hσ hσ3 hJ
  have hiso : GGLabelIso o.lab labJ :=
    ggLabelRigidInput_holds o.lab labJ (J ⧸ Subgroup.center J) hΛo hΛJ hHasO hlab
  have hoeq : o.lab = labJ := ltrd4b_iso_eq htag hrk hiso
  obtain ⟨T, tw, m, hTtw, hDmem⟩ := hDval
  obtain ⟨hTeq, htw, hm⟩ := ltrd4b_typeCl hTtw hΛlab' hS
  subst hTeq
  subst htw
  subst hm
  have hord : ggMultOrd 3 lab'.n ≠ 0 := ltrd4b_ord_ne_zero (ltrd4b_three_dvd lab'.n)
  obtain ⟨m', -, -, hD'⟩ := (mem_ggMultTableCl_C hord).mp hDmem
  have ho' : o ∈ (ggMultDatumC 3 lab'.n (ggMultOrd 3 lab'.n) m').orbits := by
    rw [← hD']; exact ho
  have hnoD : o.lab.tag ≠ .D := ltrd4b_datumC_no_D ho'
  have htagD : o.lab.tag = .D := by rw [hoeq]; exact htag
  exact hnoD htagD

end CFSG.StandardType

end

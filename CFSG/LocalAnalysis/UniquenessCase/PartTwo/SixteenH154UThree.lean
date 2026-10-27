module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Good
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNineBasic
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ui

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

private theorem s16h_not_dvd_two_pow_three (n : ℕ) : ¬ 3 ∣ 2 ^ n := fun hdvd =>
  absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
    (Nat.prime_three.dvd_of_dvd_pow hdvd)) (by norm_num)

private theorem s16h_conjSubgroup_mono {A B : Subgroup G} (h : A ≤ B) (x : G) :
    conjSubgroup A x ≤ conjSubgroup B x := by
  intro y hy
  rw [mem_conjSubgroup_iff] at hy ⊢
  exact h hy

private theorem s16h_conjSubgroup_le_of_mem {A M : Subgroup G} (hA : A ≤ M) {x : G}
    (hx : x ∈ M) : conjSubgroup A x ≤ M := by
  intro y hy
  rw [mem_conjSubgroup_iff] at hy
  have h1 : x⁻¹ * (x * y * x⁻¹) * x ∈ M := M.mul_mem (M.mul_mem (M.inv_mem hx) (hA hy)) hx
  have e : x⁻¹ * (x * y * x⁻¹) * x = y := by group
  rwa [e] at h1

private theorem s16h_isPGroup_conj {p : ℕ} {P : Subgroup G} (hP : IsPGroup p P) (x : G) :
    IsPGroup p (conjSubgroup P x) :=
  hP.of_equiv (Subgroup.equivMapOfInjective P (MulAut.conj x⁻¹).toMonoidHom
    (MulAut.conj x⁻¹).injective)

private theorem s16h_not_isCyclic_conj {P : Subgroup G} (hP : ¬ IsCyclic ↥P) (x : G) :
    ¬ IsCyclic ↥(conjSubgroup P x) := fun hc =>
  hP ((Subgroup.equivMapOfInjective P (MulAut.conj x⁻¹).toMonoidHom
    (MulAut.conj x⁻¹).injective).isCyclic.2 hc)

theorem s16h_uniqueMax_of_noncyclic_three (D : Data G) (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D)
    (hk : IsStronglyPEmbedded 3 D.M) {P X : Subgroup G} (hP : IsPGroup 3 P)
    (hPc : ¬ IsCyclic ↥P) (hPX : P ≤ X) (hXM : X ≤ D.M) : UniqueMax D.M X :=
  uc22p22u_uniqueMax_mono D hPX hXM
    (uc22p22u_uniqueMax_of_noncyclic D h61 h63 Nat.prime_three (by norm_num) (hPX.trans hXM) hP
      hPc (Or.inl (ElevenNine.gamma_le_of_stronglyEmbedded D Nat.prime_three hk
        (hPX.trans hXM) hP)))

theorem s16h_uniqueMax_cent_of_cElt_three (D : Data G) (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D)
    (h127 : R127 D) (hk : IsStronglyPEmbedded 3 D.M) {V₀ V : Subgroup G} (h : Hyp16 D V₀ V)
    {P : Subgroup G} (hPp : IsPGroup 3 P) (hPc : ¬ IsCyclic ↥P) {w : G} (hwV : w ∈ V)
    (hwV₀ : w ∉ V₀) (hP : P ≤ F11.CElt D.M V₀ w) :
    UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  obtain ⟨n, -, hn⟩ := r113_holds D V₀ V (Hyp125.hyp11 h127 h.hyp125)
    (s16c34_card_v0_le_four D h) w hwV hwV₀
  have hindex : ¬ 3 ∣ (D.M ⊓ centralizer ({w} : Set G)).relIndex (F11.CElt D.M V₀ w) := by
    rw [hn]
    exact s16h_not_dvd_two_pow_three n
  obtain ⟨B, hB, hBp, hBc⟩ :=
    c23_exists_noncyclic_le_of_not_dvd_relIndex Nat.prime_three hP hindex hPp hPc
  exact s16h_uniqueMax_of_noncyclic_three D h61 h63 hk hBp hBc hB inf_le_left

theorem s16h_exists_noncyclic_of_pRank {q : ℕ} (hq : q.Prime) {X : Subgroup G}
    (h2 : 2 ≤ CFSG.Open.pRank q X) :
    ∃ E : Subgroup G, E ≤ X ∧ IsPGroup q E ∧ ¬ IsCyclic ↥E := by
  obtain ⟨E, hEX, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hq.one_lt X
  refine ⟨E, hEX, CFSG.Open.IsElemAbelian.isPGroup hE, fun hcyc => ?_⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := E)
  have h1 : orderOf g ∣ q :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hE.2 g g.2))
  rw [hg, hEc] at h1
  have h3 : q ^ 2 ≤ q ^ CFSG.Open.pRank q X := Nat.pow_le_pow_right hq.pos h2
  have h4 : q < q ^ 2 := by nlinarith [hq.one_lt]
  have := Nat.le_of_dvd hq.pos h1
  omega

theorem s16h_uniqueMax_cent_of_pRank_three (D : Data G) (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D)
    (h127 : R127 D) (hk : IsStronglyPEmbedded 3 D.M) {V₀ V : Subgroup G} (h : Hyp16 D V₀ V)
    {w : G} (hwV : w ∈ V) (hwV₀ : w ∉ V₀) (h2 : 2 ≤ CFSG.Open.pRank 3 (F11.CElt D.M V₀ w)) :
    UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  obtain ⟨E, hE, hEp, hEc⟩ := s16h_exists_noncyclic_of_pRank Nat.prime_three h2
  exact s16h_uniqueMax_cent_of_cElt_three D h61 h63 h127 hk h hEp hEc hwV hwV₀ hE

theorem s16h_condU_of_pRank_three (D : Data G) (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D)
    (h127 : R127 D) (hk : IsStronglyPEmbedded 3 D.M) {V₀ V L : Subgroup G}
    (h : Setting16 D V₀ V L)
    (h2 : 2 ≤ CFSG.Open.pRank 3 (lBar V₀ V h.hyp151.isElemAbelian L)) :
    s16h_CondU D V₀ V L h.hyp151.isElemAbelian := by
  have hV := h.hyp151.isElemAbelian
  obtain ⟨P, hPL, hPp, hPc⟩ := s16c34_exists_noncyclic_of_lBar hV Nat.prime_three h2
  intro x hx w hw hw0
  have hwV : w ∈ V := preTil_le V₀ V hV _ hw
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer
      h.hyp151.hyp125.pairFacts.le_normalizer₀
  have hLx : conjSubgroup L x ≤ D.M := s16h_conjSubgroup_le_of_mem h.hyp151.le hx
  have hLxY := le_preBarSub_barSub (M := D.M) (V₀ := V₀) hV hLx (hLx.trans hMs)
  obtain ⟨y, hyval, hyfix⟩ := (mem_preTil V₀ V hV _).1 hw
  have hY := s16c34_preBarSub_le_cElt (M := D.M) hV hyfix
  rw [hyval] at hY
  exact s16h_uniqueMax_cent_of_cElt_three D h61 h63 h127 hk h.hyp16 (s16h_isPGroup_conj hPp x)
    (s16h_not_isCyclic_conj hPc x) hwV hw0
    ((s16h_conjSubgroup_mono hPL x).trans (hLxY.trans hY))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

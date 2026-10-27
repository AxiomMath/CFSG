module

public import CFSG.Timmesfeld.Exceptional.DeepJ2Split
public import CFSG.Timmesfeld.Exceptional.DeepWorldCBasic
public import CFSG.Timmesfeld.Exceptional.DeepFixed
public import CFSG.Timmesfeld.Exceptional.DeepW1
public import CFSG.Timmesfeld.Bridge.RootStructTwoLocalIso

public section

namespace CFSG.Timmesfeld.Moufang

open CFSG.Blueprint Deep

theorem ncard_collinearSet_eq_four_or_ten {G : Type} [Group G] {D : Set G} (hH : Hyp G D)
    (hsing : ∀ d ∈ D, rootSet D d = {d}) (hNL : NoLevi D) (hPl : ExcNoPlane D) {d : G}
    (hd : d ∈ D) (h1 : (collinearSet D d).ncard % 3 = 1) :
    (collinearSet D d).ncard = 4 ∨ (collinearSet D d).ncard = 10 := by
  have S : Bridge.TwoLocalSetting G D := ⟨hH, hsing, hNL, hPl⟩
  obtain ⟨n, hn, hk⟩ := S.exists_ncard_rootLines hd
  rw [S.ncard_collinearSet hd, hk] at h1 ⊢
  interval_cases n
  · exact Or.inl rfl
  · norm_num at h1
  · exact Or.inr rfl
  · norm_num at h1

theorem excCycInput_of (hWC : ExcWorldCInput) : ExcCycInput := by
  intro G _ D hH _ hsing _ hJ hNL hPl h1
  have := hH.finite
  have hD := hH.root
  have hclass := hH.isClass
  have hconj : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D := fun g x hx => hH.conj_mem g hx
  have hNP := hNL.noPolar hclass hD hsing hPl
  have hP1 := p1_of_noPolar_noPlane hH hNP hPl
  have hQ := commLambda_of_noPolar_noPlane hD hconj hNP hPl
  have hconn := Bridge.commConnected_of_noPolar
    (Bridge.asc73Input_of_theoremTwo CFSG.ShultStronglyClosedTI.theoremTwo) hH hNP
  have hconst : ∀ d ∈ D, ∀ e ∈ D, (collinearSet D d).ncard = (collinearSet D e).ncard := by
    intro d hd e he
    obtain ⟨d₀, hD₀⟩ := hH.isClass
    rw [hD₀] at hd he
    obtain ⟨g, rfl⟩ := isConj_iff.1 (hd.symm.trans he)
    exact (ncard_collinearSet_conj hH.isClass g d).symm
  intro p hp c hc _
  rcases ncard_collinearSet_eq_four_or_ten hH hsing hNL hPl hp (h1 p hp) with h4 | h10
  ·
    have h4' : ∀ d ∈ D, (collinearSet D d).ncard = 4 := fun d hd => (hconst d hd p hp).trans h4
    have key : ∀ k, nbhd D c k ⊆ nbhd D c 4 := by
      intro k
      induction k with
      | zero => exact nbhd_mono (by norm_num)
      | succ k ih =>
        intro d hd
        obtain ⟨hdD, e, he, hde⟩ := (mem_nbhd_succ_iff hc).1 hd
        have heD := nbhd_subset hc k he
        have he4 := ih he
        by_cases he3 : e ∈ nbhd D c 3
        · exact mem_nbhd_succ_of_commute hdD he3 hde
        obtain ⟨x, hx, hx3, h10, h10'⟩ :=
          exists_two_near hclass hD hNL hNP hPl hP1 hc heD he4 he3
        have hoff : offLines D e x = ∅ := by
          have hcard := ncard_offLines hD heD hx h10 h10'
          rw [h4' e heD] at hcard
          exact (Set.ncard_eq_zero (Set.toFinite _)).1 (by omega)
        by_cases hed : d = e
        · rw [hed]
          exact he4
        have hdΛ : d ∈ collinearSet D e := ⟨hdD, hde.symm, hNP e heD d hdD hde.symm (Ne.symm hed)⟩
        have hon : ∃ i, d = x i ∨ d = e * x i := by
          by_contra hno
          push Not at hno
          have hmem : d ∈ offLines D e x := ⟨hdΛ, fun i => hno i⟩
          rw [hoff] at hmem
          exact hmem
        obtain ⟨i, hi | hi⟩ := hon
        · rw [hi]
          exact nbhd_mono (by norm_num) (hx3 i)
        · rw [hi]
          exact mem_nbhd_succ_of_commute (hx i).2.2 (hx3 i)
            ((hx i).2.1.mul_left (Commute.refl (x i)))
    obtain ⟨k, hk⟩ := exists_mem_nbhd hconn hc hp
    exact key k hk
  ·
    have h10' : ∀ d ∈ D, (collinearSet D d).ncard = 10 := fun d hd =>
      (hconst d hd p hp).trans h10
    have hW1 : ∀ c ∈ D, ∀ p ∈ D, p ∉ nbhd D c 3 → ¬ ThreeNear D c p := by
      rintro c' hc' p' hp' hp3 ⟨x, hx, hx3, hne⟩
      have hp4 : p' ∈ nbhd D c' 4 := mem_nbhd_succ_of_commute hp' (hx3 0) (hx 0).2.1
      exact hJ (isSporadicJ2_of_three_near hH hNP hNL hPl hP1 hc' hp' hp4 hp3 hx hx3 hne
        (h10' p' hp'))
    have key : ∀ k, nbhd D c k ⊆ nbhd D c 3 := by
      intro k
      induction k with
      | zero => exact nbhd_mono (by norm_num)
      | succ k ih =>
        intro d hd
        obtain ⟨hdD, e, he, hde⟩ := (mem_nbhd_succ_iff hc).1 hd
        have hd4 : d ∈ nbhd D c 4 := mem_nbhd_succ_of_commute hdD (ih he) hde
        by_contra hd3
        obtain ⟨x, hx, hx3, h01, h01'⟩ :=
          exists_two_near hclass hD hNL hNP hPl hP1 hc hdD hd4 hd3
        exact hWC G D hH hsing hNL hPl h10' hW1 c hc d hdD hd4 hd3 x hx hx3 h01 h01'
          fun q hq hzq => false_of_commute_offLines hclass hD hsing hQ hNL hNP hPl hP1 hW1 hc
            hdD hd4 hd3 hx hx3 h01 h01' hq hzq
    obtain ⟨k, hk⟩ := exists_mem_nbhd hconn hc hp
    exact nbhd_mono (by norm_num) (key k hk)

end CFSG.Timmesfeld.Moufang

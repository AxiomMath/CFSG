module

public import CFSG.Quasithin.Background.B5Models
public import CFSG.Quasithin.Background.B5B42
public import CFSG.Quasithin.Background.B5Gen
public import CFSG.Quasithin.Background.B5Bot
public import CFSG.Quasithin.Background.B6Offenders

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped commutatorElement

namespace B5

section CommAut

variable {V : Type*} [CommGroup V] {W U : Subgroup V} {M : Subgroup (MulAut V)}
  (hMW : M ≤ stabSub W) (hMU : M ≤ stabSub U)

include hMW hMU

theorem autSec_commutator :
    autSec ⁅M, M⁆ W U = ⁅autSec M W U, autSec M W U⁆ := by
  have hle : ⁅M, M⁆ ≤ M := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact M.mul_mem (M.mul_mem (M.mul_mem ha hb) (M.inv_mem ha)) (M.inv_mem hb)
  rw [← map_secHom_eq_autSec M hMW hMU hle]
  have h1 : ⁅M, M⁆.subgroupOf M = commutator ↥M := by
    rw [← Subgroup.map_subtype_commutator]
    exact Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
  rw [h1, commutator, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    range_secHom M hMW hMU]

theorem eq_of_autSec_eq (hfaith : M ⊓ centSec W U = ⊥) {L L' : Subgroup (MulAut V)} (hL : L ≤ M)
    (hL' : L' ≤ M) (h : autSec L W U = autSec L' W U) : L = L' := by
  have hinj : Function.Injective (secHom M hMW hMU) :=
    (MonoidHom.ker_eq_bot_iff _).1 (ker_secHom_eq_bot M hMW hMU hfaith)
  have h1 := map_secHom_eq_autSec M hMW hMU hL
  have h2 := map_secHom_eq_autSec M hMW hMU hL'
  have h3 : L.subgroupOf M = L'.subgroupOf M := by
    apply Subgroup.map_injective hinj
    rw [h1, h2, h]
  have h4 := congrArg (Subgroup.map M.subtype) h3
  rwa [Subgroup.map_subgroupOf_eq_of_le hL, Subgroup.map_subgroupOf_eq_of_le hL'] at h4

omit hMW hMU in
theorem le_of_autSec_le (hMW : M ≤ stabSub W) (hMU : M ≤ stabSub U) (hfaith : M ⊓ centSec W U = ⊥)
    {L A : Subgroup (MulAut V)} (hL : L ≤ M) (hA : A ≤ M)
    (h : autSec A W U ≤ autSec L W U) : A ≤ L := by
  have hinj : Function.Injective (secHom M hMW hMU) :=
    (MonoidHom.ker_eq_bot_iff _).1 (ker_secHom_eq_bot M hMW hMU hfaith)
  have h1 := map_secHom_eq_autSec M hMW hMU hL
  have h2 := map_secHom_eq_autSec M hMW hMU hA
  have h3 : A.subgroupOf M ≤ L.subgroupOf M := by
    intro x hx
    have hx2 : secHom M hMW hMU x ∈ autSec A W U := by
      rw [← h2]; exact ⟨x, hx, rfl⟩
    have hx3 := h hx2
    rw [← h1] at hx3
    obtain ⟨y, hy, hyx⟩ := hx3
    have : y = x := hinj hyx
    rw [← this]; exact hy
  intro a ha
  have := h3 (show (⟨a, hA ha⟩ : ↥M) ∈ A.subgroupOf M from ha)
  exact this

end CommAut

section Alpha

variable {V : Type} [CommGroup V] [Finite V] {G L T : Subgroup (MulAut V)}

omit [Finite V] in
theorem one_le_of_binaryNaturalSL {H : Subgroup (MulAut V)} {U Z : Subgroup V} {d n : ℕ}
    (h : BinaryNaturalSL H U Z d n) : 1 ≤ n := by
  obtain ⟨K, hK, hf, hc, -⟩ := h
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  rw [hc] at h1
  by_contra h0
  have : n = 0 := by omega
  rw [this] at h1
  simp at h1

theorem isFFStarOffenderOn_of {A : Subgroup (MulAut V)} (hA : IsFFStarOffender G A) (hAT : A ≤ T)
    (U : Subgroup V) : IsFFStarOffenderOn T A U := by
  refine ⟨hAT, hA.2.1, hA.2.2.1, fun B hB => ?_⟩
  have := (B1.card_inf_fixV_aux hA hB U).1
  simpa [inf_comm] using this

theorem secConfig (hV : ∀ v : V, v ^ 2 = 1) (h : B51Hyp G L) (hU : commV L ∈ IrrPlus L ⊤)
    (hT : IsSylowTwoOf T G) {C : Subgroup V} (hC : C = fixV L ⊓ commV L) :
    C ≤ commV L ∧ C < commV L ∧ G ≤ stabSub (commV L) ∧ G ≤ stabSub C ∧
      L ⊓ centSec (commV L) C = ⊥ ∧ (L ⊔ T) ⊓ centSec (commV L) C = ⊥ := by
  subst hC
  have hn := normal_L h
  obtain ⟨-, -, hlt, -⟩ := irr_data hU
  rw [inf_comm] at hlt
  exact ⟨inf_le_right, hlt, le_stabSub_commV hn (fun g hg => G.inv_mem hg),
    le_stabSub_fixV_inf_commV hn (fun g hg => G.inv_mem hg), L_inf_centSec_eq_bot h hV,
    sup_inf_centSec_eq_bot h hV hT.1 hT.2.1⟩

theorem alpha_branch (hI16 : AsI16Cover) (hnon : AsB51NonsplitOff) (hV : ∀ v : V, v ^ 2 = 1)
    (h : B51Hyp G L) (hU : commV L ∈ IrrPlus L ⊤) (hT : IsSylowTwoOf T G) {C : Subgroup V}
    (hC : C = fixV L ⊓ commV L)
    (hJ : ffJ (autSec (L ⊔ T) (commV L) C) = autSec L (commV L) C)
    (hQ : B42QData (autSec (L ⊔ T) (commV L) C) (autSec L (commV L) C)) : G = L := by
  have hn := normal_L h
  have hLG := le_G h
  have hTG : T ≤ G := hT.1
  have hT2 : IsPGroup 2 T := hT.2.1
  obtain ⟨hUC, hlt, hGU, hGC, hfL, hfM⟩ := secConfig hV h hU hT hC
  have hMG : L ⊔ T ≤ G := sup_le hLG hTG
  have hMU : L ⊔ T ≤ stabSub (commV L) := hMG.trans hGU
  have hMC : L ⊔ T ≤ stabSub C := hMG.trans hGC
  have hLU : L ≤ stabSub (commV L) := hLG.trans hGU
  have hLC : L ≤ stabSub C := hLG.trans hGC
  apply eq_of_offenders_le h hT
  intro A hA hAT
  have hAM : IsFFStarOffender (L ⊔ T) A := ⟨hAT.trans le_sup_right, hA.2.1, hA.2.2.1, hA.2.2.2⟩
  have hF : quasithinGenFitting (L ⊔ T) = L := genFitting_sup_eq h hTG hT2
  have hq : CFSG.IsQuasisimple ↥(quasithinGenFitting (L ⊔ T)) := by rw [hF]; exact quasi_L h
  have hS : ¬ commSub (commV L) (quasithinGenFitting (L ⊔ T)) ≤ C := by
    obtain ⟨-, hcomm, -, -⟩ := irr_data hU
    rw [hF, hcomm]
    intro hle
    exact (lt_irrefl _) (lt_of_lt_of_le hlt hle)
  obtain ⟨hfaithA, -, hq1clause⟩ := B1_5_8 hV hAM (W := commV L) (U := C) hUC hMU hMC hq
    (pCoreOf_sup_eq_bot h hTG hT2) hS
  have hLM : L ≤ L ⊔ T := le_sup_left
  have hAMle : A ≤ L ⊔ T := hAT.trans le_sup_right
  by_cases hq1 : qOf (autSec (L ⊔ T) (commV L) C) = ((1 : ℚ) : WithTop ℚ)
  · have hoff := (hq1clause hq1).1
    have h1 : autSec A (commV L) C ≤ autSec L (commV L) C := hJ ▸ B6.le_ffJ hoff
    exact le_of_autSec_le hMU hMC hfM hLM hAMle h1
  · by_cases hC0 : C = ⊥
    · subst hC0
      have hoff := isFFStarOffender_autSec_bot hAM hMU hfaithA
      have h1 : autSec A (commV L) ⊥ ≤ autSec L (commV L) ⊥ := hJ ▸ B6.le_ffJ hoff
      exact le_of_autSec_le hMU hMC hfM hLM hAMle h1
    · have hCne : fixV L ⊓ commV L ≠ ⊥ := hC ▸ hC0
      have hAon := isFFStarOffenderOn_of hA hAT (commV L)
      have hnon' := hnon V hV G L T h hU hT hCne
      have hi16 := hI16 V hV L hU
      rcases hQ with hq' | ⟨n, hn3⟩ | ⟨n, hn4⟩ | h4 | h5
      · exact absurd hq' hq1
      · have h3 := binaryNaturalSL_of_autSec hUC hLU hLC hfL hn3
        rw [hC] at h3
        by_cases hn1 : n = 1
        · subst hn1
          exact hnon' (Or.inl h3) A hAon
        · have hn0 : 1 ≤ n := one_le_of_binaryNaturalSL h3
          exact absurd (hi16 (Or.inl ⟨n, by omega, h3⟩)) hCne
      · have h4' := binaryNaturalSp4_of_autSec hUC hLU hLC hfL hn4
        rw [hC] at h4'
        exact hnon' (Or.inr ⟨n, h4'⟩) A hAon
      · have h4' := binaryNaturalSL_of_autSec hUC hLU hLC hfL h4
        rw [hC] at h4'
        exact absurd (hi16 (Or.inr (Or.inl h4'))) hCne
      · have h5' := binaryNaturalSL_of_autSec hUC hLU hLC hfL h5
        rw [hC] at h5'
        exact absurd (hi16 (Or.inr (Or.inr h5'))) hCne


end Alpha

structure B51IrrInputs : Prop where
  b42 : AsB42
  ident : AsB42Ident
  sp4s6 : AsSp4S6
  s8d8 : AsS8D8
  outAbelian : AsOutAbelian
  i16 : AsI16Cover
  nonsplit : AsB51NonsplitOff

section Beta

variable {V : Type} [CommGroup V] [Finite V] {G L T : Subgroup (MulAut V)}

theorem beta_branch (hI : B51IrrInputs) (hV : ∀ v : V, v ^ 2 = 1) (h : B51Hyp G L)
    (hU : commV L ∈ IrrPlus L ⊤) (hT : IsSylowTwoOf T G) {C : Subgroup V}
    (hC : C = fixV L ⊓ commV L)
    (hbeta : B42BetaData (autSec (L ⊔ T) (commV L) C) (autSec L (commV L) C)) :
    B42ModulePair L (commV L) C ∧ G = L ⊔ T ∧
      ((∃ n, 5 ≤ n ∧ n ≤ 8 ∧ SymmetricNatural G (commV L) C n) ∨ G2Natural G (commV L) C 1) := by
  have hn := normal_L h
  have hLG := le_G h
  have hTG : T ≤ G := hT.1
  have hT2 : IsPGroup 2 T := hT.2.1
  obtain ⟨hUC, hlt, hGU, hGC, hfL, hfM⟩ := secConfig hV h hU hT hC
  have hMG : L ⊔ T ≤ G := sup_le hLG hTG
  have hMU : L ⊔ T ≤ stabSub (commV L) := hMG.trans hGU
  have hMC : L ⊔ T ≤ stabSub C := hMG.trans hGC
  have hLU : L ≤ stabSub (commV L) := hLG.trans hGU
  have hLC : L ≤ stabSub C := hLG.trans hGC
  obtain ⟨hGJ, hLcomm, hstruct, hmodels⟩ := hbeta
  have hcommle : ⁅L ⊔ T, L ⊔ T⁆ ≤ L ⊔ T := commutator_le_self _
  have hLeq : L = ⁅L ⊔ T, L ⊔ T⁆ := by
    refine eq_of_autSec_eq hMU hMC hfM le_sup_left hcommle ?_
    rw [autSec_commutator hMU hMC]
    exact hLcomm
  have hOutL : OutAbelian ↥L := by
    have hstruct' : ((∃ n : ℕ, 5 ≤ n ∧ n ≤ 8 ∧ Nonempty (↥(L ⊔ T) ≃* Equiv.Perm (Fin n))) ∨
        ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧
          Nonempty (↥(L ⊔ T) ≃* ↥(CFSG.Open.quasithinG2 K))) := by
      have ι := secEquiv (L ⊔ T) hMU hMC hfM
      rcases hstruct with ⟨n, h5, h8, ⟨e⟩⟩ | ⟨K, hK, hf, hc, ⟨e⟩⟩
      · exact Or.inl ⟨n, h5, h8, ⟨ι.trans e⟩⟩
      · exact Or.inr ⟨K, hK, hf, hc, ⟨ι.trans e⟩⟩
    have := hI.outAbelian V (L ⊔ T) hstruct'
    rw [← hLeq] at this
    exact this
  have hGeq : G = L ⊔ T := eq_sup_of_outAbelian h hOutL hT
  have fin_sym : ∀ n : ℕ, 5 ≤ n → n ≤ 8 → SymmetricNatural (autSec (L ⊔ T) (commV L) C)
      (⊤ : Subgroup (Sec (commV L) C)) ⊥ n →
      G = L ⊔ T ∧ ((∃ n, 5 ≤ n ∧ n ≤ 8 ∧ SymmetricNatural G (commV L) C n) ∨ G2Natural G (commV L) C 1) ∧
        SymmetricNatural (L ⊔ T) (commV L) C n := by
    intro n h5 h8 hS
    have hS' := symmetricNatural_of_autSec hUC hMU hMC hfM hS
    refine ⟨hGeq, Or.inl ⟨n, h5, h8, ?_⟩, hS'⟩
    rw [hGeq]; exact hS'
  have alt : ∀ n : ℕ, 5 ≤ n → SymmetricNatural (L ⊔ T) (commV L) C n →
      AlternatingNatural L (commV L) C n := by
    intro n hn hS
    have e : AlternatingNatural ⁅L ⊔ T, L ⊔ T⁆ (commV L) C n := alternatingNatural_derived hn hS
    exact (congrArg (fun X : Subgroup (MulAut V) => AlternatingNatural X (commV L) C n) hLeq).mpr e
  rcases hmodels with hSp4 | hG2 | ⟨n, hn57, hS⟩ | ⟨hExt, ⟨e8⟩⟩
  · have hS6 := hI.sp4s6 _ _ _ _ hSp4
    obtain ⟨hGe, hcon, hS'⟩ := fin_sym 6 (by norm_num) (by norm_num) hS6
    have h1 := alt 6 (by norm_num) hS'
    refine ⟨?_, hGe, hcon⟩
    unfold B42ModulePair
    tauto
  · have hG2' := g2Natural_of_autSec hUC hMU hMC hfM hG2
    refine ⟨?_, hGeq, Or.inr (by rw [hGeq]; exact hG2')⟩
    have h1 : G2NaturalDerived L (commV L) C 1 := by
      have e : G2NaturalDerived ⁅L ⊔ T, L ⊔ T⁆ (commV L) C 1 := g2NaturalDerived_of_g2Natural hG2'
      exact (congrArg (fun X : Subgroup (MulAut V) => G2NaturalDerived X (commV L) C 1) hLeq).mpr e
    unfold B42ModulePair
    tauto
  · have h5 : 5 ≤ n := by rcases hn57 with rfl | rfl <;> norm_num
    have h8 : n ≤ 8 := by rcases hn57 with rfl | rfl <;> norm_num
    obtain ⟨hGe, hcon, hS'⟩ := fin_sym n h5 h8 hS
    have h1 := alt n h5 hS'
    refine ⟨?_, hGe, hcon⟩
    rcases hn57 with rfl | rfl
    · unfold B42ModulePair
      tauto
    · unfold B42ModulePair
      tauto
  · have hS8 : SymmetricNatural (autSec (L ⊔ T) (commV L) C) (⊤ : Subgroup (Sec (commV L) C)) ⊥ 8 := by
      refine hI.s8d8 _ _ _ _ ⟨e8⟩ ?_ (fun _ _ _ _ => trivial) ?_
      · rw [← hLcomm]
        exact hExt
      · intro g _ z hz
        rw [Subgroup.mem_bot] at hz ⊢
        rw [hz]
        exact map_one g
    obtain ⟨hGe, hcon, -⟩ := fin_sym 8 (by norm_num) (by norm_num) hS8
    refine ⟨?_, hGe, hcon⟩
    have h1 := slExteriorTwo_of_autSec hUC hLU hLC hfL hExt
    unfold B42ModulePair
    tauto


end Beta

section Main

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}

theorem exists_isSylowTwoOf (H : Subgroup (MulAut V)) : ∃ S : Subgroup (MulAut V), IsSylowTwoOf S H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q⟩ : Nonempty (Sylow 2 ↥H) := inferInstance
  refine ⟨(Q : Subgroup ↥H).map H.subtype, ⟨Subgroup.map_subtype_le _, Q.isPGroup'.map _, ?_⟩⟩
  have : ((Q : Subgroup ↥H).map H.subtype).subgroupOf H = (Q : Subgroup ↥H) :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  rw [this]
  exact Q.not_dvd_index

theorem b4Hyp_section' (hV : ∀ v : V, v ^ 2 = 1) (h : B51Hyp G L) (hU : commV L ∈ IrrPlus L ⊤)
    {T : Subgroup (MulAut V)} (hTG : T ≤ G) (hT2 : IsPGroup 2 T) {C : Subgroup V}
    (hC : C = fixV L ⊓ commV L) :
    B4Hyp (autSec (L ⊔ T) (commV L) C) (autSec L (commV L) C) := by
  subst hC
  exact b4Hyp_section hV h hU hTG hT2

theorem exists_section_offender' (hV : ∀ v : V, v ^ 2 = 1) (h : B51Hyp G L)
    (hU : commV L ∈ IrrPlus L ⊤) {T : Subgroup (MulAut V)} (hT : IsSylowTwoOf T G) {C : Subgroup V}
    (hC : C = fixV L ⊓ commV L) :
    ∃ A, IsFFStarOffender G A ∧ A ≤ T ∧ ∃ B, B ≤ autSec A (commV L) C ∧
      IsFFStarOffender (autSec (L ⊔ T) (commV L) C) B := by
  subst hC
  exact exists_section_offender hV h hU hT

theorem b51_case1i (hI : B51IrrInputs) (hV : ∀ v : V, v ^ 2 = 1) (h : B51Hyp G L)
    (hU : commV L ∈ IrrPlus L ⊤) : B51Case1i G L := by
  have key : ∀ T, IsSylowTwoOf T G →
      B42ModulePair L (commV L) (fixV L ⊓ commV L) ∧
        (G = L ∨ (G = L ⊔ T ∧
          ((∃ n, 5 ≤ n ∧ n ≤ 8 ∧ SymmetricNatural G (commV L) (fixV L ⊓ commV L) n) ∨
            G2Natural G (commV L) (fixV L ⊓ commV L) 1))) := by
    intro T hT
    obtain ⟨C, hC⟩ : ∃ C : Subgroup V, C = fixV L ⊓ commV L := ⟨_, rfl⟩
    obtain ⟨hUC, hlt, hGU, hGC, hfL, hfM⟩ := secConfig hV h hU hT hC
    have hLU : L ≤ stabSub (commV L) := (le_G h).trans hGU
    have hLC : L ≤ stabSub C := (le_G h).trans hGC
    obtain ⟨A, hAG, hAT, B, hBA, hB⟩ := exists_section_offender' hV h hU hT hC
    have hb4 := b4Hyp_section' hV h hU hT.1 hT.2.1 hC
    have hconcl := hI.b42 (Sec (commV L) C) (sq_eq_one_sec hV _ _) _ _ hb4 B hB
    have hcases := b42_cases hI.ident (sq_eq_one_sec hV _ _) hb4 hB hconcl
    rcases hcases with ⟨hJL, hpair, hQ⟩ | ⟨hJne, hbeta⟩
    · have hGL : G = L := alpha_branch hI.i16 hI.nonsplit hV h hU hT hC hJL hQ
      have hp := b42ModulePair_of_autSec hUC hLU hLC hfL hpair
      subst hC
      exact ⟨hp, Or.inl hGL⟩
    · obtain ⟨hp, hGe, hmod⟩ := beta_branch hI hV h hU hT hC hbeta
      subst hC
      exact ⟨hp, Or.inr ⟨hGe, hmod⟩⟩
  obtain ⟨T0, hT0⟩ := exists_isSylowTwoOf G
  exact ⟨hU, (key T0 hT0).1, fun T hT => (key T hT).2⟩

end Main

end B5

end CFSG.Quasithin

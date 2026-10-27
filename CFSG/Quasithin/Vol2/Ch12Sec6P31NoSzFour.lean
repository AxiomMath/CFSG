module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31NoSzMod
public import CFSG.Quasithin.H13.A6S13816j
public import CFSG.Quasithin.H13.KGFactSzEnd

public section

namespace CFSG.Quasithin.H13.P31Sz

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.F126 S126 S126P31
open CFSG.QuasithinUnique

section Setting

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K I : Subgroup G}

attribute [local instance] commGroupOfFact

theorem isSz_autIH [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) (hKK : conjClosure K T = K)
    {n : ℕ} (hSzN : IsSz n ↥(star H K)) (hs : IsSimpleGroup ↥(star H K))
    (hne : autIH V₁ I H (conjClosure K T) ≠ ⊥) :
    IsSz n ↥(autIH V₁ I H (conjClosure K T)) := by
  let π : ↥(star H K) →* MulAut ↥(tildeOf V₁ (conjClosure I H)) :=
    (rhoQ h hIU).comp (star H K).subtype
  have hrange : π.range = autIH V₁ I H (conjClosure K T) := by
    ext x
    rw [MonoidHom.mem_range, mem_autIH_iff h hIU hKK]
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨n, n.2, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n, hn⟩, rfl⟩
  have hinj : Function.Injective π := by
    apply injective_of_isSimpleGroup
    obtain ⟨y, hy, hy1⟩ : ∃ y ∈ autIH V₁ I H (conjClosure K T), y ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hne ((Subgroup.eq_bot_iff_forall _).mpr hcon)
    rw [← hrange] at hy
    obtain ⟨s, rfl⟩ := hy
    exact ⟨s, hy1⟩
  exact isSz_congr ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)) hSzN

end Setting

section Main

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}

attribute [local instance] commGroupOfFact

theorem false_of_isSz_eq
    (h310 : D310) (h391 : D391) (hI4 : Insp4) (h : HypF918 T V L V₁ Vp H K)
    (hHq : SQTKGroup ↥H) (hKK : conjClosure K T = K) {n : ℕ} (hSzN : IsSz n ↥(star H K))
    (hs : IsSimpleGroup ↥(star H K)) (E : Subgroup (HStar H))
    (hE3 : ∀ e ∈ E, ∃ k : ℕ, e ^ 3 ^ k = 1)
    (hEC : E ≤ Subgroup.centralizer (star H K : Set (HStar H)))
    (hfpf : ∀ w : ↥(UT V₁ Vp H), (∀ e ∈ E, psiH h.toHypF98.toHypF91 e w = w) → w = 1) : False := by
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  obtain ⟨I, hV₁I, hIU, Wa, hWa, hirr⟩ := exists_isIrrPlusTildeU h
  haveI hFI := factElem h hIU
  have hIT := isIrrPlusTildeT_of_ambient h hIU Wa hWa hirr
  have hirr' : subM V₁ (conjClosure I H) I ∈
      IrrPlusOn (autIH V₁ I H (conjClosure K T))
        (orbSup (autIH V₁ I H T) (subM V₁ (conjClosure I H) I))
        (autIH V₁ I H T) := hIT
  have hnt := hnt_of_irrSec h hIU hirr'.1.2.2.2.1
  have hneL : autIH V₁ I H K ≠ ⊥ := by
    rw [autIH_eq_map h hKH]
    exact map_K_ne_bot h hIU hnt
  have hMpL : autIH V₁ I H (conjClosure K T) = autIH V₁ I H K := by rw [hKK]
  have hLSz : IsSz n ↥(autIH V₁ I H (conjClosure K T)) :=
    isSz_autIH h hIU hKK hSzN hs (by rw [hMpL]; exact hneL)
  have hW2 : ∀ w : ↥(tildeOf V₁ (conjClosure I H)), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using hFI.out.2 w.1 w.2)
  have hVinv : autIH V₁ I H (conjClosure K T) ≤ stabSub (subM V₁ (conjClosure I H) I) :=
    B1.le_stabSub_of_invariant fun g hg w hw => hirr'.1.2.1 ⟨g, hg⟩ w hw
  have hCinv : autIH V₁ I H (conjClosure K T) ≤
      stabSub (XMod.fixed ↥(autIH V₁ I H (conjClosure K T)) (subM V₁ (conjClosure I H) I)) :=
    B1.le_stabSub_of_invariant fun g hg w hw => XMod.isInv_fixed _ ⟨g, hg⟩ w hw
  have hCV := hirr'.1.2.2.2.1
  have hirrM : ∀ J : Subgroup ↥(tildeOf V₁ (conjClosure I H)),
      (∀ x ∈ autIH V₁ I H (conjClosure K T), ∀ w ∈ J, x w ∈ J) →
      XMod.fixed ↥(autIH V₁ I H (conjClosure K T)) (subM V₁ (conjClosure I H) I) ≤ J →
      J ≤ subM V₁ (conjClosure I H) I →
      J = XMod.fixed ↥(autIH V₁ I H (conjClosure K T)) (subM V₁ (conjClosure I H) I) ∨
        J = subM V₁ (conjClosure I H) I :=
    fun J hJ hCJ hJV => hirr'.1.2.2.2.2 J (fun g w hw => hJ g g.2 w hw) hCJ hJV
  have hntM : ¬ autIH V₁ I H (conjClosure K T) ≤
      centSec (subM V₁ (conjClosure I H) I)
        (XMod.fixed ↥(autIH V₁ I H (conjClosure K T)) (subM V₁ (conjClosure I H) I)) := by
    intro hle
    have h1 : XMod.commOf ↥(autIH V₁ I H (conjClosure K T)) (subM V₁ (conjClosure I H) I) ≤
        XMod.fixed ↥(autIH V₁ I H (conjClosure K T)) (subM V₁ (conjClosure I H) I) := by
      rw [XMod.commOf, Subgroup.closure_le]
      rintro _ ⟨g, w, hw, rfl⟩
      exact (hle g.2).2 w hw
    rw [hirr'.1.2.2.1] at h1
    exact lt_irrefl _ (lt_of_le_of_lt h1 hCV)
  have hTMp := autIH_T_le_normalizer h I
  obtain ⟨-, hF4⟩ := F918_4' h hHq hKK hV₁I hIU Wa hWa hirr h310 h391 hI4
  have hF4' : H ≤ Subgroup.normalizer (I : Set G) ∨
      ModFourRest (autIH V₁ I H (conjClosure K T)) (autIH V₁ I H T) (autIH V₁ I H K)
        (subM V₁ (conjClosure I H) I) := hF4
  rw [← hMpL] at hF4'
  rcases hF4' with hinv | ⟨hVT, hFF⟩ | hD
  ·
    have hcl : conjClosure I H = I := le_antisymm
      (conjClosure_le fun h hh i hi => (Subgroup.mem_normalizer_iff.mp (hinv hh) i).mp hi)
      (le_conjClosure I H)
    have hVtop : ∀ w : ↥(tildeOf V₁ (conjClosure I H)), w ∈ subM V₁ (conjClosure I H) I := by
      intro w
      rw [mem_subM_iff]
      have h2 : tildeOf V₁ (conjClosure I H) = tildeOf V₁ I := by rw [hcl]
      exact h2.le w.2
    have hTV : autIH V₁ I H T ≤ stabSub (subM V₁ (conjClosure I H) I) :=
      fun t _ w => ⟨fun _ => hVtop w, fun _ => hVtop _⟩
    have hTC : autIH V₁ I H T ≤
        stabSub (XMod.fixed ↥(autIH V₁ I H (conjClosure K T)) (subM V₁ (conjClosure I H) I)) :=
      fun t ht => A6.SzSec.mem_stabSub_fixed (hTV ht) (hTMp ht)
    have hKI := K₀_le_normalizer_of_isInv h hIU hV₁I hirr'.1.2.1
    obtain ⟨B, hQ⟩ := qOff_of_hyp h hIU hV₁I hKI hnt
    have hAr := (rAV_le_two_iff hW2 (X := autIH V₁ I H B)
      ⟨le_rfl, hQ.ne, hQ.elem⟩).mp hQ.rat
    have hnat := A6.SzSec.binaryNaturalSz_of_offender hW2 hLSz hCV hVinv hCinv hirrM hntM
      (hQ.le.trans hTV) (hQ.le.trans hTC) (hQ.le.trans hTMp) hQ.ne hQ.elem hAr hQ.faithMp
    exact false_of_normalizer KGSz.szEnd_holds h hIU hIT hKK hinv hnat E hE3 hEC hfpf
  ·
    have hTV : autIH V₁ I H T ≤ stabSub (subM V₁ (conjClosure I H) I) := by
      refine B1.le_stabSub_of_invariant fun t ht w hw => ?_
      rw [hVT] at hw ⊢
      exact A6.SzSec.map_mem_orbSup ht hw
    have hTC : autIH V₁ I H T ≤
        stabSub (XMod.fixed ↥(autIH V₁ I H (conjClosure K T)) (subM V₁ (conjClosure I H) I)) :=
      fun t ht => A6.SzSec.mem_stabSub_fixed (hTV ht) (hTMp ht)
    refine A6.SzSec.not_isFFModule hW2 hLSz hCV hVinv hCinv hirrM hntM hTV hTC hTMp
      (A6.SzSec.isFFModule_autSec_congr ?_ hFF)
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, XMod.mem_fixed]
    exact ⟨fun h => ⟨x.2, fun a => h a a.2⟩, fun h a ha => h.2 ⟨a, ha⟩⟩
  ·
    exact A6.SzSec.not_d310Two_of_isSz hLSz hD

end Main

end CFSG.Quasithin.H13.P31Sz

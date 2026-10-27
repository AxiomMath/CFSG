module

public import CFSG.Quasithin.H13.A6S13816j

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G]

theorem false_of_sz_of_hypF918
    {T V L V₁ Vp H K : Subgroup G} (hF : HypF918 T V L V₁ Vp H K) (hHq : SQTKGroup ↥H)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h310 : D310) (h391 : D391) (hI4 : Insp4)
    (hD36 : D36) (hD37 : D37) (hD321 : D321) (hI5 : Insp5a) (hSzE : A6.SzEnd)
    {c : G} (hcH : c ∈ H) (hc3 : c ^ 3 = 1)
    (hfix : ∀ a ∈ conjClosure Vp H, (c * a * c⁻¹)⁻¹ * a ∈ V₁ → a ∈ V₁)
    (hcomm : ∀ k ∈ conjClosure K T, c * k * c⁻¹ * k⁻¹ ∈ pCoreOf 2 H)
    {n : ℕ} (hSz : IsSz n (↥K ⧸ CFSG.pCore 2 ↥K)) : False := by
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  obtain ⟨I, hV₁I, hIU, Wa, hWa, hirr⟩ := exists_isIrrPlusTildeU hF
  have hFI := factElem hF hIU
  have hIT := isIrrPlusTildeT_of_ambient hF hIU Wa hWa hirr
  have hirr' : subM V₁ (conjClosure I H) I ∈
      IrrPlusOn (autIH V₁ I H (conjClosure K T))
        (orbSup (autIH V₁ I H T) (subM V₁ (conjClosure I H) I)) (autIH V₁ I H T) := hIT
  have hnt := hnt_of_irrSec hF hIU hirr'.1.2.2.2.1
  have hneL : autIH V₁ I H K ≠ ⊥ := by
    rw [autIH_eq_map hF hKH]
    exact map_K_ne_bot hF hIU hnt
  have hW2 : ∀ w : ↥(tildeOf V₁ (conjClosure I H)), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using hFI.out.2 w.1 w.2)
  set φ := actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) with hφ
  set σ := φ ⟨c, hcH⟩ with hσ
  have hσ3 : σ ^ 3 = 1 := by
    rw [hσ, ← map_pow]
    have : (⟨c, hcH⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    rw [this, map_one]
  have hσMp : ∀ m ∈ autIH V₁ I H (conjClosure K T), σ * m = m * σ := by
    intro m hm
    rw [autIH_eq_map hF hF.K₀_le_H] at hm
    obtain ⟨y, hy, rfl⟩ := hm
    have hx : (((⟨c, hcH⟩ : ↥H) * y * (⟨c, hcH⟩ : ↥H)⁻¹ * y⁻¹ : ↥H) : G) ∈ pCoreOf 2 H :=
      hcomm _ (Subgroup.mem_subgroupOf.mp hy)
    have h2 := hF.actH_eq_one_of_mem_pCoreOf hIU hx
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h2)
  have hIHN := hF.conjClosure_le_normalizer_V₁ hIU
  have hIHU : conjClosure I H ≤ conjClosure Vp H := conjClosure_le_conjClosure_U hIU le_rfl
  have hfpf : ∀ w, σ w = w → w = 1 := by
    intro w hw
    obtain ⟨a, haIH, hau⟩ := exists_mk_of_mem_tilde w
    have hwa : w = modMk hIHN (a : G) haIH := Subtype.ext hau.symm
    rw [hwa, hσ, actH_modMk hF.H_le_normalizer_V₁ hIHN (le_normalizer_conjClosure I H) _ haIH]
      at hw
    have hfixa := (secMk_eq_secMk_iff).mp (congrArg Subtype.val hw)
    have haV := hfix a (hIHU haIH) hfixa
    rw [hwa]
    exact Subtype.ext ((secMk_eq_one_iff).mpr haV)
  by_cases hKK : conjClosure K T = K
  ·
    have hA38K : A38Types (↥K ⧸ CFSG.pCore 2 ↥K) := Or.inr (Or.inl ⟨n, hSz⟩)
    have hsimple := CFSG.QuasithinUnique.Vol2Native.L122A.isSimpleGroup_of_a38Types hA38K
    obtain ⟨eL⟩ := nonempty_mulEquiv_quotient_autI hF hIU hsimple hneL
    have hMpL : autIH V₁ I H (conjClosure K T) = autIH V₁ I H K := by
      rw [hKK]
    have hLSz : IsSz n ↥(autIH V₁ I H (conjClosure K T)) := by
      rw [hMpL]
      exact isSz_congr eL hSz
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
    have hTMp := autIH_T_le_normalizer hF I
    obtain ⟨-, hF4⟩ := F918_4' hF hHq hKK hV₁I hIU Wa hWa hirr h310 h391 hI4
    have hF4' : H ≤ Subgroup.normalizer (I : Set G) ∨
        ModFourRest (autIH V₁ I H (conjClosure K T)) (autIH V₁ I H T)
          (autIH V₁ I H K) (subM V₁ (conjClosure I H) I) := hF4
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
          stabSub (XMod.fixed ↥(autIH V₁ I H (conjClosure K T))
            (subM V₁ (conjClosure I H) I)) := fun t ht =>
        A6.SzSec.mem_stabSub_fixed (hTV ht) (hTMp ht)
      have hKI := K₀_le_normalizer_of_isInv hF hIU hV₁I hirr'.1.2.1
      obtain ⟨B, hQ⟩ := qOff_of_hyp hF hIU hV₁I hKI hnt
      have hAr := (rAV_le_two_iff hW2 (X := autIH V₁ I H B) ⟨le_rfl, hQ.ne, hQ.elem⟩).mp hQ.rat
      have hnat := A6.SzSec.binaryNaturalSz_of_offender hW2 hLSz hCV hVinv hCinv hirrM hntM
        (hQ.le.trans hTV) (hQ.le.trans hTC) (hQ.le.trans hTMp) hQ.ne hQ.elem hAr hQ.faithMp
      have hσC : ∀ u ∈ XMod.fixed ↥(autIH V₁ I H (conjClosure K T))
          (subM V₁ (conjClosure I H) I), σ u ∈ XMod.fixed
            ↥(autIH V₁ I H (conjClosure K T)) (subM V₁ (conjClosure I H) I) := by
        intro u hu
        refine ⟨hVtop _, fun a => ?_⟩
        have e : (a : MulAut _) (σ u) = σ ((a : MulAut _) u) := by
          have := congrArg (fun ψ : MulAut _ => ψ u) (hσMp a a.2)
          simpa [MulAut.mul_apply] using this.symm
        have hu' := hu.2 a
        rw [Subgroup.smul_def, MulAut.smul_def] at hu' ⊢
        rw [e, hu']
      have hE := hSzE _ _ _ _ n hnat σ ⟨1, by rw [pow_one]; exact hσ3⟩ (fun u _ => hVtop _) hσC
        hσMp
      have hall := A6.SzSec.mem_of_trivial_mod hW2 hσ3 hfpf hσC (fun w => hE w (hVtop w))
      exact lt_irrefl _ (lt_of_lt_of_le hCV fun w _ => hall w)
    ·
      have hTV : autIH V₁ I H T ≤ stabSub (subM V₁ (conjClosure I H) I) := by
        refine B1.le_stabSub_of_invariant fun t ht w hw => ?_
        rw [hVT] at hw ⊢
        exact A6.SzSec.map_mem_orbSup ht hw
      have hTC : autIH V₁ I H T ≤
          stabSub (XMod.fixed ↥(autIH V₁ I H (conjClosure K T))
            (subM V₁ (conjClosure I H) I)) := fun t ht =>
        A6.SzSec.mem_stabSub_fixed (hTV ht) (hTMp ht)
      refine A6.SzSec.not_isFFModule hW2 hLSz hCV hVinv hCinv hirrM hntM hTV hTC hTMp
        (A6.SzSec.isFFModule_autSec_congr ?_ hFF)
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, XMod.mem_fixed]
      exact ⟨fun h => ⟨x.2, fun a => h a a.2⟩, fun h a ha => h.2 ⟨a, ha⟩⟩
    ·
      exact A6.SzSec.not_d310Two_of_isSz hLSz hD
  ·
    obtain ⟨hA38K, -⟩ := five_group_data hF hHq h37 h38 hKK
    have hsimple := CFSG.QuasithinUnique.Vol2Native.L122A.isSimpleGroup_of_a38Types hA38K
    obtain ⟨eL⟩ := nonempty_mulEquiv_quotient_autI hF hIU hsimple hneL
    have hLSz : IsSz n ↥(autIH V₁ I H K) := isSz_congr eL hSz
    obtain ⟨t, htT, htK⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (K : Set G) := by
      by_contra hcon
      push Not at hcon
      apply hKK
      apply le_antisymm
      · exact conjClosure_le fun t ht z hz =>
          (Subgroup.mem_normalizer_iff.mp (hcon t ht) z).mp hz
      · exact le_conjClosure K T
    obtain ⟨-, hFive⟩ := F918_5' hF hHq hKK hV₁I hIU Wa hWa hirr hD36 hD37 hD321 hI5 h37 h38
    have h5 := hFive t htT htK
    obtain ⟨-, -, hprelim⟩ := five_prelim hF hHq hKK hIU hnt h37 h38
    obtain ⟨htT', -, hMp, -⟩ := hprelim t htT htK
    have htMp := autIH_T_le_normalizer hF I htT'
    exact A6.SzMod.false_of_modFive hW2 hSzE hLSz hσ3 hfpf hσMp hMp htMp h5

end CFSG.Quasithin.H13.L32A

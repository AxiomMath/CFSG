module

public import CFSG.Quasithin.H13.A6S13816j
public import CFSG.Quasithin.H13.A6S13816i

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

attribute [local instance] commGroupOfFact

theorem case13816SzNormalMod_of
    (h36 : QuasithinUnique.Vol2Native.A36CoreForSQTKCat)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h310 : D310) (h391 : D391) (hI4 : Insp4)
    (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4) (h13 : Lem13813) (hSzE : SzEnd) :
    Case13816SzNormalMod := by
  intro G _ _ T L V S hS hhat H hH K hK hKN hHeq hHN hcomm ⟨n, hSz⟩
  obtain ⟨-, -, hF⟩ := S.hypF918_K0 h36 h37 h38 h139 h1334 h13 hS hH hK
  rw [← hHeq] at hF
  have hHq : SQTKGroup ↥H := S.sqtkGroup_of_mem_Hz hH
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hKK : conjClosure K T = K := by
    refine le_antisymm (conjClosure_le fun t ht k hk => ?_) (le_conjClosure K T)
    exact (Subgroup.mem_normalizer_iff.mp (hKN (le_sup_right.trans hH.1.1 ht)) k).mp hk
  obtain ⟨I, hV₁I, hIU, Wa, hWa, hirr⟩ := exists_isIrrPlusTildeU hF
  have hFI := factElem hF hIU
  have hIT := isIrrPlusTildeT_of_ambient hF hIU Wa hWa hirr
  have hirr' : subM (fsuV1 T V) (conjClosure I H) I ∈
      IrrPlusOn (autIH (fsuV1 T V) I H (conjClosure K T))
        (orbSup (autIH (fsuV1 T V) I H T) (subM (fsuV1 T V) (conjClosure I H) I))
        (autIH (fsuV1 T V) I H T) := hIT
  have hnt := hnt_of_irrSec hF hIU hirr'.1.2.2.2.1
  have hA38K : A38Types (↥K ⧸ CFSG.pCore 2 ↥K) := Or.inr (Or.inl ⟨n, hSz⟩)
  have hsimple := CFSG.QuasithinUnique.Vol2Native.L122A.isSimpleGroup_of_a38Types hA38K
  have hneL : autIH (fsuV1 T V) I H K ≠ ⊥ := by
    rw [autIH_eq_map hF hKH]
    exact map_K_ne_bot hF hIU hnt
  obtain ⟨eL⟩ := nonempty_mulEquiv_quotient_autI hF hIU hsimple hneL
  have hMpL : autIH (fsuV1 T V) I H (conjClosure K T) = autIH (fsuV1 T V) I H K := by
    rw [hKK]
  have hLSz : IsSz n ↥(autIH (fsuV1 T V) I H (conjClosure K T)) := by
    rw [hMpL]
    exact isSz_congr eL hSz
  have hW2 : ∀ w : ↥(tildeOf (fsuV1 T V) (conjClosure I H)), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using hFI.out.2 w.1 w.2)
  have hVinv : autIH (fsuV1 T V) I H (conjClosure K T) ≤
      stabSub (subM (fsuV1 T V) (conjClosure I H) I) :=
    B1.le_stabSub_of_invariant fun g hg w hw => hirr'.1.2.1 ⟨g, hg⟩ w hw
  have hCinv : autIH (fsuV1 T V) I H (conjClosure K T) ≤
      stabSub (XMod.fixed ↥(autIH (fsuV1 T V) I H (conjClosure K T))
        (subM (fsuV1 T V) (conjClosure I H) I)) :=
    B1.le_stabSub_of_invariant fun g hg w hw => XMod.isInv_fixed _ ⟨g, hg⟩ w hw
  have hCV := hirr'.1.2.2.2.1
  have hirrM : ∀ J : Subgroup ↥(tildeOf (fsuV1 T V) (conjClosure I H)),
      (∀ x ∈ autIH (fsuV1 T V) I H (conjClosure K T), ∀ w ∈ J, x w ∈ J) →
      XMod.fixed ↥(autIH (fsuV1 T V) I H (conjClosure K T))
        (subM (fsuV1 T V) (conjClosure I H) I) ≤ J →
      J ≤ subM (fsuV1 T V) (conjClosure I H) I →
      J = XMod.fixed ↥(autIH (fsuV1 T V) I H (conjClosure K T))
        (subM (fsuV1 T V) (conjClosure I H) I) ∨
        J = subM (fsuV1 T V) (conjClosure I H) I :=
    fun J hJ hCJ hJV => hirr'.1.2.2.2.2 J (fun g w hw => hJ g g.2 w hw) hCJ hJV
  have hntM : ¬ autIH (fsuV1 T V) I H (conjClosure K T) ≤
      centSec (subM (fsuV1 T V) (conjClosure I H) I)
        (XMod.fixed ↥(autIH (fsuV1 T V) I H (conjClosure K T))
          (subM (fsuV1 T V) (conjClosure I H) I)) := by
    intro hle
    have h1 : XMod.commOf ↥(autIH (fsuV1 T V) I H (conjClosure K T))
        (subM (fsuV1 T V) (conjClosure I H) I) ≤
        XMod.fixed ↥(autIH (fsuV1 T V) I H (conjClosure K T))
          (subM (fsuV1 T V) (conjClosure I H) I) := by
      rw [XMod.commOf, Subgroup.closure_le]
      rintro _ ⟨g, w, hw, rfl⟩
      exact (hle g.2).2 w hw
    rw [hirr'.1.2.2.1] at h1
    exact lt_irrefl _ (lt_of_le_of_lt h1 hCV)
  have hTMp := autIH_T_le_normalizer hF I
  obtain ⟨-, hF4⟩ := F918_4' hF hHq hKK hV₁I hIU Wa hWa hirr h310 h391 hI4
  have hF4' : H ≤ Subgroup.normalizer (I : Set G) ∨
      ModFourRest (autIH (fsuV1 T V) I H (conjClosure K T)) (autIH (fsuV1 T V) I H T)
        (autIH (fsuV1 T V) I H K) (subM (fsuV1 T V) (conjClosure I H) I) := hF4
  rw [← hMpL] at hF4'
  rcases hF4' with hinv | ⟨hVT, hFF⟩ | hD
  ·
    have hcl : conjClosure I H = I := le_antisymm
      (conjClosure_le fun h hh i hi => (Subgroup.mem_normalizer_iff.mp (hinv hh) i).mp hi)
      (le_conjClosure I H)
    have hVtop : ∀ w : ↥(tildeOf (fsuV1 T V) (conjClosure I H)),
        w ∈ subM (fsuV1 T V) (conjClosure I H) I := by
      intro w
      rw [mem_subM_iff]
      have h2 : tildeOf (fsuV1 T V) (conjClosure I H) = tildeOf (fsuV1 T V) I := by rw [hcl]
      exact h2.le w.2
    have hTV : autIH (fsuV1 T V) I H T ≤ stabSub (subM (fsuV1 T V) (conjClosure I H) I) :=
      fun t _ w => ⟨fun _ => hVtop w, fun _ => hVtop _⟩
    have hTC : autIH (fsuV1 T V) I H T ≤
        stabSub (XMod.fixed ↥(autIH (fsuV1 T V) I H (conjClosure K T))
          (subM (fsuV1 T V) (conjClosure I H) I)) := fun t ht =>
      SzSec.mem_stabSub_fixed (hTV ht) (hTMp ht)
    have hKI := K₀_le_normalizer_of_isInv hF hIU hV₁I hirr'.1.2.1
    obtain ⟨B, hQ⟩ := qOff_of_hyp hF hIU hV₁I hKI hnt
    have hAr := (rAV_le_two_iff hW2 (X := autIH (fsuV1 T V) I H B)
      ⟨le_rfl, hQ.ne, hQ.elem⟩).mp hQ.rat
    have hnat := SzSec.binaryNaturalSz_of_offender hW2 hLSz hCV hVinv hCinv hirrM hntM
      (hQ.le.trans hTV) (hQ.le.trans hTC) (hQ.le.trans hTMp) hQ.ne hQ.elem hAr hQ.faithMp
    set φ := actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) with hφ
    have hcL1 : (S.cL1 hhat : G) ∈ S.L1 := S.cL1_mem hhat
    have hcH : (S.cL1 hhat : G) ∈ H := (le_sup_left.trans hH.1.1) hcL1
    set σ := φ ⟨S.cL1 hhat, hcH⟩ with hσ
    have hσ3 : σ ^ 3 = 1 := by
      rw [hσ, ← map_pow]
      have : (⟨S.cL1 hhat, hcH⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using S.cL1_cube hhat)
      rw [this, map_one]
    have hσMp : ∀ m ∈ autIH (fsuV1 T V) I H (conjClosure K T), σ * m = m * σ := by
      intro m hm
      rw [autIH_eq_map hF hF.K₀_le_H] at hm
      obtain ⟨y, hy, rfl⟩ := hm
      have hyK : (y : G) ∈ K := hKK ▸ Subgroup.mem_subgroupOf.mp hy
      have hx : (((⟨S.cL1 hhat, hcH⟩ : ↥H) * y * (⟨S.cL1 hhat, hcH⟩ : ↥H)⁻¹ * y⁻¹ : ↥H) : G) ∈
          pCoreOf 2 H := hcomm _ hcL1 _ hyK
      have h2 := hF.actH_eq_one_of_mem_pCoreOf hIU hx
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
      exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h2)
    have hIHN := hF.conjClosure_le_normalizer_V₁ hIU
    have hIHU : conjClosure I H ≤ conjClosure S.V3 H := conjClosure_le_conjClosure_U hIU le_rfl
    have hfpf : ∀ w, σ w = w → w = 1 := by
      intro w hw
      obtain ⟨a, haIH, hau⟩ := exists_mk_of_mem_tilde w
      have hwa : w = modMk hIHN (a : G) haIH := Subtype.ext hau.symm
      rw [hwa, hσ, actH_modMk hF.H_le_normalizer_V₁ hIHN (le_normalizer_conjClosure I H) _
        haIH] at hw
      have hfix := (secMk_eq_secMk_iff).mp (congrArg Subtype.val hw)
      have haV := S.mem_V1_of_fix_c hS hhat hH hHN (hIHU haIH) hfix
      rw [hwa]
      exact Subtype.ext ((secMk_eq_one_iff).mpr haV)
    have hσC : ∀ u ∈ XMod.fixed ↥(autIH (fsuV1 T V) I H (conjClosure K T))
        (subM (fsuV1 T V) (conjClosure I H) I), σ u ∈ XMod.fixed
          ↥(autIH (fsuV1 T V) I H (conjClosure K T)) (subM (fsuV1 T V) (conjClosure I H) I) := by
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
    have hall := SzSec.mem_of_trivial_mod hW2 hσ3 hfpf hσC (fun w => hE w (hVtop w))
    exact lt_irrefl _ (lt_of_lt_of_le hCV fun w _ => hall w)
  ·
    have hTV : autIH (fsuV1 T V) I H T ≤ stabSub (subM (fsuV1 T V) (conjClosure I H) I) := by
      refine B1.le_stabSub_of_invariant fun t ht w hw => ?_
      rw [hVT] at hw ⊢
      exact SzSec.map_mem_orbSup ht hw
    have hTC : autIH (fsuV1 T V) I H T ≤
        stabSub (XMod.fixed ↥(autIH (fsuV1 T V) I H (conjClosure K T))
          (subM (fsuV1 T V) (conjClosure I H) I)) := fun t ht =>
      SzSec.mem_stabSub_fixed (hTV ht) (hTMp ht)
    refine SzSec.not_isFFModule hW2 hLSz hCV hVinv hCinv hirrM hntM hTV hTC hTMp
      (SzSec.isFFModule_autSec_congr ?_ hFF)
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, XMod.mem_fixed]
    exact ⟨fun h => ⟨x.2, fun a => h a a.2⟩, fun h a ha => h.2 ⟨a, ha⟩⟩
  ·
    exact SzSec.not_d310Two_of_isSz hLSz hD

end CFSG.Quasithin.H13.A6

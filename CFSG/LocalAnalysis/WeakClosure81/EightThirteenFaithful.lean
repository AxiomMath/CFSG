module

public import CFSG.LocalAnalysis.WeakClosure81.EightTwelveDefs
public import CFSG.LocalAnalysis.WeakClosure81.EightTwo

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G]

theorem eight_thirteen_faithful {V H T A : Subgroup G} {i : ℕ} (hV7 : Hyp7 V)
    (hH0 : IsCalH0 V H) (hT : IsSylowIn 2 T (H ⊓ normalizer (V : Set G)))
    (hA : A ∈ E3.gammaSet V i T)
    (hAM : ∃ x ∈ H, ¬ conjSubgroup A x ≤ normalizer (V : Set G)) :
    A ⊓ centralizer (eGrp H T : Set G) = ⊥ ∧
      ∀ a ∈ A, a ≠ 1 →
        eGrp H T ⊓ centralizer (A : Set G) = eGrp H T ⊓ centralizer ({a} : Set G) := by
  have hV : IsElemAbelian 2 V := hV7.1
  have hTI := hV7.2.2
  have hVne : V ≠ ⊥ := by
    intro hb
    have h2 := hV7.2.1
    rw [hb, Subgroup.card_bot] at h2
    omega
  have hH : IsCalH V H := hH0.1
  have hTH : IsSylowIn 2 T H := isSylowIn_of_isCalH hH hT
  have hVT : V ≤ T := le_of_isCalH hV hH hT
  obtain ⟨hAT, g, hAg, -⟩ := hA
  have hEHE : eSub V H T ≤ eGrp H T := by
    unfold eSub eGrp
    refine conjClosure_le fun h hh z hz => ?_
    refine mem_conjClosure hh ?_
    obtain ⟨hzV, hzC⟩ := Subgroup.mem_inf.mp hz
    exact mem_omegaOneCenterOf (hVT hzV) (fun y hy => Subgroup.mem_centralizer_iff.mp hzC y hy)
      (hV.2 z hzV)
  have hEO : eGrp H T ≤ omegaOneCenterOf (pCoreOf 2 H) := by
    have hO2T : pCoreOf 2 H ≤ T := pCoreOf_le_of_isCalH hH hT
    have hC : omegaOneCenterOf T ≤ omegaOneCenterOf (pCoreOf 2 H) := by
      intro c hc
      have hcT : c ∈ T := omegaOneCenterOf_le T hc
      have hcC : ∀ y ∈ T, y * c = c * y := fun y hy =>
        mem_centralizer_of_mem_omegaOneCenterOf hc hy
      have hcCen : c ∈ centralizer (pCoreOf 2 H : Set G) :=
        Subgroup.mem_centralizer_iff.mpr fun y hy => hcC y (hO2T hy)
      have hcO2 : c ∈ pCoreOf 2 H := hH.2.1 ⟨hTH.le hcT, hcCen⟩
      exact mem_omegaOneCenterOf hcO2 (fun y hy => hcC y (hO2T hy))
        ((B2F.isElemAbelian_omegaOneCenterOf T).2 c hc)
    unfold eGrp
    refine conjClosure_le fun h hh c hc => ?_
    have hHnorm : H ≤ Subgroup.normalizer (omegaOneCenterOf (pCoreOf 2 H) : Set G) :=
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) H).trans
        (normalizer_le_normalizer_omegaOneCenterOf (pCoreOf 2 H))
    exact (Subgroup.mem_normalizer_iff.mp (hHnorm hh) c).1 (hC hc)
  have hEab : IsElemAbelian 2 (eGrp H T) :=
    CFSG.Open.IsElemAbelian.mono (B2F.isElemAbelian_omegaOneCenterOf (pCoreOf 2 H)) hEO
  have hEH : eGrp H T ≤ H :=
    hEO.trans ((omegaOneCenterOf_le _).trans (CFSG.openPCoreOf_le 2 H))
  have hAH : A ≤ H := hAT.trans hTH.le
  have hAN : A ≤ normalizer (eGrp H T : Set G) := fun a ha =>
    le_normalizer_conjClosure (omegaOneCenterOf T) H (hAH ha)
  have hAU : A ≤ conjSubgroup V g ⊓ H := le_inf hAg hAH
  rcases eight_four_one hV hTI hVne hH0 hT g with ⟨-, hn⟩ | ⟨hb, -⟩
  · exfalso
    obtain ⟨x, hx, hxM⟩ := hAM
    exact hxM ((E3.conjSubgroup_mono_left x hAU).trans (hn x hx))
  · refine ⟨?_, fun a ha ha1 => ?_⟩
    · refine eq_bot_iff.mpr fun a ha => ?_
      obtain ⟨haA, haC⟩ := Subgroup.mem_inf.mp ha
      have hmem : a ∈ (conjSubgroup V g ⊓ H) ⊓ centralizer (eSub V H T : Set G) :=
        Subgroup.mem_inf.mpr ⟨hAU haA, Subgroup.centralizer_le hEHE haC⟩
      rw [hb] at hmem
      exact hmem
    · have hEV : eGrp H T ⊓ conjSubgroup V g = ⊥ := by
        refine eq_bot_iff.mpr fun e he => ?_
        obtain ⟨heE, heV⟩ := Subgroup.mem_inf.mp he
        have heC : e ∈ centralizer (eGrp H T : Set G) :=
          Subgroup.mem_centralizer_iff.mpr fun y hy =>
            (E1.commute_of_isElemAbelian hEab heE hy).symm
        have hmem : e ∈ (conjSubgroup V g ⊓ H) ⊓ centralizer (eSub V H T : Set G) :=
          Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨heV, hEH heE⟩,
            Subgroup.centralizer_le hEHE heC⟩
        rw [hb] at hmem
        exact hmem
      exact eight_one (isTI_conj hTI g) hAg hAN hEV ha ha1

end CFSG.LocalAnalysis.WeakClosure81

end

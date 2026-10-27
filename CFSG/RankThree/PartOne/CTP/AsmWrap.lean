module

public import CFSG.RankThree.PartOne.CTP.AsmFrame
public import CFSG.RankThree.PartOne.S12.Sec12Three
import CFSG.RankThree.PartOne.S11d.FixedRes

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG CFSG.RankThree.PartOne CFSG.RankThree
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

theorem kf1214U5Frame_of_std
    (hsel : SelectedPrimeElementsNormalizeThetaComponents) (hGA h107 h109 : Prop) (hg : hGA)
    (hg107 : h107) (hg109 : h109) (hI : IStd hGA) (hL : LStd hGA h107 h109) :
    Kf1214U5Frame := by
  intro G _ _ p A c L E ctx hrow b K I X P Q hLay hC hF
  obtain ⟨hp5, hZ, f₀, hf1, h5, h25, hmodL⟩ := hrow
  subst hp5
  obtain ⟨F⟩ := hL hg hg107 hg109 G A c L E ctx f₀ hf1 h5 h25 hmodL b K I hLay
  have hh := ctx.hyp
  have hcomm : ∀ l ∈ L, c * l = l * c := Sec12Three.comm_c_L hh
  have hf2 : 2 ≤ f₀ := by
    by_contra h
    have h1 : f₀ = 1 := by omega
    subst h1
    norm_num at h5
  have hRq := fixedRes_isQuasisimple hF.field
  have hKR := S12K.kLayer_eq_fixedResidual ctx hLay hRq
  have hcfg0 : IConfig c f₀ I K (E ⊓ L ⊓ K) (fun a b => F.J (e3 a) (e3 b)) :=
    { f_two := hf2
      dvd5 := h5
      ndvd25 := h25
      model := hF.model.1 f₀ hf1 h5 (Or.inr hmodL)
      perfect := isPerfect_of_mem_thetaComponentsAt hLay.I_mem
      c_norm := hF.field.1
      c_pow := Sec12Three.pow_eq_one_of_mem_E hh (hh.A_le_E hh.c_mem)
      c_outer := hF.field.2.1
      K_eq := hKR
      K_le := hLay.K_le
      triangle := F.std }
  have hw : ∀ σ : Equiv.Perm (Fin 5), F.W σ * c = c * F.W σ := fun σ =>
    (hcomm _ (F.W_L σ)).symm
  have hA : Asm c F I :=
    { hI := hLay.I_mem
      cfg := fun σ => hcfg0.conj (F.W σ) (hw σ)
      facts := fun σ => hI hg G c f₀ _ _ _ _ (hcfg0.conj (F.W σ) (hw σ))
      h5norm := fun σ x hx hord =>
        Sec12Fus.pElement_normalizes_thetaComponentsAt_gen hsel hh.evenRank_eq.le hh.prime
          hh.three_lt hx hord (Isg_mem_theta F I hLay.I_mem σ) }
  have hG : Sec12TwoGeneric 5 c L E := by
    rcases ctx.facts.two with hG | hS
    · exact hG
    · exact absurd (by rw [hS.center_card]) hZ
  have hR := hh.restr_of_generic hG
  exact frame_of_asm hA inf_le_left ctx.ten.2.1 (hR.E_eq.trans (sup_comm _ _))

end CFSG.RankThree.PartOne.CTP

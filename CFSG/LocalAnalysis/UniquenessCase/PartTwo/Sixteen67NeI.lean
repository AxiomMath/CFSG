module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67NeH
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67NeD
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67Pre
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67NeC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section Certified


namespace Cfg1667Ne

variable {M V₀ V W₁ W₂ : Subgroup G} {g : G}

theorem inCalOStar (h : Cfg1667Ne M V₀ V W₁ W₂) (hg : InCalO 1 M V₀ V g) :
    InCalOStar 1 M V₀ V g :=
  WeakClosure81.Hyp65.inCalOStar_of_lt_rMV (h.hyp65 hg) h.lt_rMV

theorem inCalOStar_conj (h : Cfg1667Ne M V₀ V W₁ W₂) (hg : InCalO 1 M V₀ V g) :
    InCalOStar 1 (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) g⁻¹ :=
  inCalOStar (h.conj g) (WeakClosure81.inCalO_swap hg)

end Cfg1667Ne

theorem r16_67_preNe_holds (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h21 : R1621 D) (h61 : UC6.R6_1 D) (h1217 : R1217 D) (h129 : R129_1 D) (h159 : R15_9Small D) :
    R16_67_preNe D := by
  intro V₀ V L hV hS hs h0 g hg
  obtain ⟨x, hxM, hxn⟩ :=
    c23_exists_mem_not_nBar D hS.setting.hyp151 hV hs.1.2.2.1
  have hcfg := s1667ne_cfg D hSg h1219 h21 h61 h1217 h129 h159 hS hs h0 hxM hxn
  have hg' : InCalO 1 D.M V₀ V g :=
    inCalO_of_mem_calO hcfg.normalizer_eq hcfg.le_normalizer₀ hg
  have hE : hcfg.elemAbelian = hV := Subsingleton.elim _ _
  unfold Concl1667pre
  simpa only [hE] using hcfg.concl (hcfg.inCalOStar hg') (hcfg.inCalOStar_conj hg')

theorem r16_67_pre_holds (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h21 : R1621 D) (h61 : UC6.R6_1 D) (h1217 : R1217 D) (h129 : R129_1 D) (h159 : R15_9Small D) :
    R16_67_pre D :=
  r16_67_pre_of_ne D hSg h1219 h61 h1217 h129 h159
    (r16_67_preNe_holds D hSg h1219 h21 h61 h1217 h129 h159)

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

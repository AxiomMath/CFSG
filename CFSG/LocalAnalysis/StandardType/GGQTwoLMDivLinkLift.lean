module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivLink
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerTlift
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerTor
public import CFSG.LocalAnalysis.StandardType.GGQTwoFrameLDefs

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.ClassicalInvolution.Phan

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs L D J : Subgroup G} {x : G}

section Lift

variable (F : QTwoFrameL p B Bs x L D J)

local instance : Field F.F0 := F.fieldF0
local instance : Finite F.F0 := F.finiteF0
local instance : CharP F.F0 2 := F.charF0
local instance : Group F.L0 := F.groupL0
local instance : Finite F.L0 := F.finiteL0

theorem qTwoFrameL_hlift (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (h3 : 3 ∣ F.m) :
    ∀ u : Su F.F0 2 1 F.m, ggIsDiagMat (u : GL (Fin F.m) F.F0) →
      ∃ ℓ : ↥L, F.c ℓ = F.πSU u ∧ (ℓ : G) ∈ Bs := by
  obtain ⟨δ, hδ⟩ := qTwoLMDivCoordInner_torus (F0 := F.F0) F.hcardF0 h3
  obtain ⟨τ, hτ⟩ := qTwoLMDivCoordInner_tlift (c := F.c) (π := F.πSU) (ρ := F.ρ) hBs hN
    ⟨F.hcardF0, F.hc_surj, F.hc_ker, F.hc_two, F.hπ_surj, F.hπ_ker, F.hdiag, F.hρ_induced⟩ hδ
  intro u hu
  obtain ⟨f, hf⟩ := hδ.surj_diag u hu
  exact ⟨τ f, by rw [hτ.comm f, hf], hτ.mem f⟩

end Lift

theorem qTwoLMSkel_div_link {m : ℕ} (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (h3 : 3 ∣ m)
    (hFrameL : QTwoFrameL 3 B Bs x L D J) (hFm : hFrameL.m = m) :
    ∀ n : ↥L, MulAut.conj n ∈
        Subgroup.normalizer ((ggGamma L hN).range : Set (MulAut ↥L)) →
      ∃ n' : ↥L, (n' : G) ∈ Subgroup.normalizer (Bs : Set G) ∧
        MulAut.conj n' = MulAut.conj n :=
  fun n hn => qTwoFrameL_link_of_lift hFrameL hBs hN
    (qTwoFrameL_hlift hFrameL hBs hN (by rw [hFm]; exact h3)) n hn

end CFSG.StandardType.QTwo

end

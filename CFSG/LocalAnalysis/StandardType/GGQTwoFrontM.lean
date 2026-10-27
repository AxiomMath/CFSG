module

public import CFSG.LocalAnalysis.StandardType.GGQTwoFrontMSolv
public import CFSG.LocalAnalysis.StandardType.GGQTwoFrontMInner
public import CFSG.LocalAnalysis.StandardType.GGQTwoFrontMComp
public import CFSG.LocalAnalysis.StandardType.GGQTwoJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoPThree
public import CFSG.LocalAnalysis.StandardType.GGSpJoinNbrModel

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.Open CFSG.ClassicalInvolution.Phan

variable {G : Type} [Group G] [Finite G]

theorem qTwoFrontM_core {B Bs L D J : Subgroup G} {x : G} (hT : GGThmIHyp 3 B x L)
    (hBs : GGBstar 3 B Bs) (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hstd : LargeEvenStdSubPre 3 B x L D J) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ 1))) :
    False := by
  obtain ⟨hDB, hDab, hDcard, hxD, -, hJ, -⟩ := hstd
  obtain ⟨y, hyD, hyx⟩ := qTwoFrontM_exists_y hDab hDcard hxD
  have hyBs : y ∈ Bs := hBs.1 (hDB hyD)
  have hy3 : y ^ 3 = 1 := hDab.2 y hyD
  obtain ⟨a, ha, hs1, hs3⟩ := qTwoFrontM_inner_class hT hBs hN hK e hyBs hy3 hyx
  have hker : (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))).ker
      ≤ Subgroup.center ↥L := by
    intro l hl
    have h1 : e (QuotientGroup.mk l) = 1 := hl
    have h2 : (QuotientGroup.mk l : ↥L ⧸ Subgroup.center ↥L) = 1 := by
      simpa using h1
    exact (QuotientGroup.eq_one_iff l).mp h2
  exact qTwoFrontM_comp_false hyD hJ
    (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))) hker ha
    (qTwoFrontM_centralizer_solvable hK hs1 hs3)

theorem qTwoFront_m_ge_five
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hG : QTwoJoinGuard p B Bs x L D J 𝒦)
    {K : Type} [Field K] [Finite K] {f m : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2) (hm : 4 ≤ m)
    (hf : f = 1) (hperf : commutator L = ⊤)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (LargeEvenSUGroup (Fin m) K (2 ^ f))) :
    5 ≤ m := by
  by_contra hlt
  have hm4 : m = 4 := by omega
  subst hm4
  subst hf
  obtain ⟨hcfg, -, -, ι, M, eM, hpres, -, r, hrA, hrC, h6⟩ := hG
  have hp3 : p = 3 := ggQTwo_p_eq_three hcfg M eM hpres hrA hrC h6
  subst hp3
  obtain ⟨hT, hBs, hstdsub⟩ := hcfg.1.1
  have hN : Bs ≤ Subgroup.normalizer (L : Set G) := GGInnerDiagOn.le_normalizer hcfg.1.2.2.1.1
  exact qTwoFrontM_core hT hBs hN hstdsub.1 (by simpa using hK) e

end CFSG.StandardType.QTwo

end

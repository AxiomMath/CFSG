module

public import CFSG.LocalAnalysis.StandardType.GGXInLUDefs
import CFSG.LocalAnalysis.StandardType.GGXInLUCover
import CFSG.LocalAnalysis.StandardType.GGXInLUF0
import CFSG.LocalAnalysis.StandardType.GGXInLUF0Eps
import CFSG.LocalAnalysis.StandardType.GGXInLUF1
import CFSG.LocalAnalysis.StandardType.GGXInLUF2
import CFSG.LocalAnalysis.StandardType.GGXInLUF3
import CFSG.LocalAnalysis.StandardType.GGXInLUTorus
import CFSG.LocalAnalysis.StandardType.GGXInLUCox

public section

open scoped Pointwise

attribute [local instance] commutatorElement

namespace CFSG.StandardType.GGXInL

open CFSG.Assembly

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G} {n : ℕ} {K : Type} [Field K] [Finite K]

theorem lup8f_mem_commutator_unitary
    (hS : GGQTwoSetting p B Bs x L D J) (hxL : x ∈ L) (M : lup8f_UnitaryMarking Bs L n K)
    (hp : p = 3) (hdvd : 3 ∣ n) (hn : 6 ≤ n) :
    x ∈ ⁅Bs, L ⊓ Subgroup.normalizer (Bs : Set G)⁆ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let C := lup8f_central_cover M
  haveI : C.N.Normal := C.normal
  obtain ⟨eps, heps⟩ := lup8f_frame0_eps hS hxL M C hp hdvd hn
  let F1 := lup8f_frame1 hS hxL M C (lup8f_frame0_of_eps (lup8f_L_perfect hS) M C eps heps)
    hp hdvd hn
  let F3 := lup8f_frame3 hS hxL M C (lup8f_frame2 hS hxL M C F1 hp hdvd hn) hp hdvd hn
  have hT := lup8f_frame_torus hS hxL M C F3 hp hdvd hn
  obtain ⟨Nsub, hCox⟩ := lup8f_frame_coxeter hS hxL M C F3 hT hp hdvd hn
  have hz := lup8f_commutator_of_frame (lup8f_frame_pack hT hCox)
  have hSStar : LargeEvenSStar p B x L := hS.1.1.1.2.2.2.2.2.2.1
  have hxBs : x ∈ Bs := hS.1.1.2.1.1 hSStar.2.1
  have hEp : IsPGroup 3 (lup8f_E' L Bs) := by
    intro g
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    have h := hS.1.1.2.1.2.1.2 _ (Subgroup.mem_subgroupOf.mp g.2)
    rw [hp] at h
    simpa using h
  rw [lup8f_mem_commutator_sup hxL]
  exact (mem_commutator_iff_map_quotient (lup8f_L' L Bs) (lup8f_E' L Bs) C.N C.le_L C.coprime
    hEp (Subgroup.mem_subgroupOf.mpr hxBs)).mpr hz

end CFSG.StandardType.GGXInL

end

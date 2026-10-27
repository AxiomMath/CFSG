module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutOutdiagE6Model
import CFSG.LocalAnalysis.StandardType.GGFinModelBridgeE6
import CFSG.LocalAnalysis.StandardType.GGLieOddCover
import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms

public section
namespace CFSG.StandardType.RCKC1
open CFSG CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType
open CFSG.ComponentClassification.PerfectAutomorphisms


theorem exists_conj_of_e6_two_of_pow_eq_one
    {G : Type} [Group G] [Finite G] (hperf : commutator G = ⊤)
    (hM : LieModel (G ⧸ Subgroup.center G) .E6 0 2 1)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {α : MulAut G} (hαp : α ^ p = 1) : ∃ g : G, α = MulAut.conj g := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsPerfect G := ⟨hperf⟩
  obtain ⟨π, hπ, hπker⟩ := LieOddCover.exists_ggU_central_cover_of_lieModel
    (by simp [S2MathFi1035Pos.GGPosTag] : S2MathFi1035Pos.GGPosTag .E6) hM.admissible hM
  have hπZ : Subgroup.center (ggU .E6 0 1).K ≤ π.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have hzQ : π z ∈ Subgroup.center (G ⧸ Subgroup.center G) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨y, rfl⟩ := hπ q
      simpa only [map_mul] using congrArg π (Subgroup.mem_center_iff.mp hz y)
    rw [Group.IsPerfect.center_quotient_center_eq_bot (G := G), Subgroup.mem_bot] at hzQ
    exact hzQ
  have hker : π.ker = Subgroup.center (ggU .E6 0 1).K := le_antisymm hπker hπZ
  have ε₀ := QuotientGroup.quotientKerEquivOfSurjective (φ := π) hπ
  let ε := (ε₀.symm.trans (QuotientGroup.quotientMulEquivOfEq hker)).trans
    (GGFinModel.ggKbEquivE6 0 1)
  let β := MulAut.congr ε (centerQuotientHom G α)
  have hβp : β ^ p = 1 := by
    change (MulAut.congr ε (centerQuotientHom G α)) ^ p = 1
    rw [← map_pow, ← map_pow, hαp, map_one, map_one]
  obtain ⟨s, hs⟩ := OutdiagE6.mem_inner_of_pow_eq_one (f := 1) (r := p)
    (by decide) hp hp2 hp3 hp.not_dvd_one hβp
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) (ε.symm s)
  refine ⟨g, ?_⟩
  apply centerQuotientHom_injective G
  apply (MulAut.congr ε).injective
  rw [centerQuotientHom_conj]
  change β = MulAut.congr ε (MulAut.conj (QuotientGroup.mk' (Subgroup.center G) g))
  have hc : MulAut.congr ε (MulAut.conj (QuotientGroup.mk' (Subgroup.center G) g)) =
      MulAut.conj s := by
    ext x
    simp [MulAut.congr_apply, MulEquiv.trans_apply, MulAut.conj_apply, hg]
  exact hs.symm.trans hc.symm

end CFSG.StandardType.RCKC1

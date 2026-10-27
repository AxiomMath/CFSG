module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIISpGen
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIISpRoot
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIISpPair
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIISpModel
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIpIso
public import CFSG.LocalAnalysis.StandardType.GGPRankBoundsSp
public import CFSG.ClassicalGroups.Symplectic.ComponentCartanRank
public import CFSG.ClassicalGroups.Symplectic.DiagonalTorusRank

public section

namespace CFSG.StandardType.RCKK1IIISp

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.RCKRP
  CFSG.StandardType.LieOddCover CFSG.StandardType.RCKK1IIp
open CFSG.Open

theorem rckRowK1_III_sp
    (hcov : GGLieOddCover) {Jb : Type} [Group Jb] [Finite Jb]
    (hodd : Odd (Nat.card (Subgroup.center Jb)))
    (hmark : LargeEvenMarking Jb (fun lab _ _ _ _ _ =>
      ggSixRCKLabelRow lab = .III ∧ (lab.tag = .B ∨ lab.tag = .C))) :
    ∃ (rb : Jb ⧸ Subgroup.center Jb) (Vb : Subgroup (Jb ⧸ Subgroup.center Jb)),
      RCKK1Data rb Vb ∧ RCKPosShort Jb rb Vb := by
  obtain ⟨m, φ, hm, hsurj, hker⟩ := rckK1IIISp_model hcov hodd hmark
  have hZ : Subgroup.center ↥(StatedSp m (GaloisField 2 1)) = ⊥ :=
    CFSG.ClassicalGroups.Symplectic.center_statedSp_eq_bot_of_charP_two (by omega)
  let ψ : ↥(StatedSp m (GaloisField 2 1)) →* Jb := φ
  have hψsurj : Function.Surjective ψ := hsurj
  have hψker : ψ.ker ≤ Subgroup.center ↥(StatedSp m (GaloisField 2 1)) := hker
  have hinj : Function.Injective ψ :=
    (MonoidHom.ker_eq_bot_iff ψ).1 (le_antisymm (hψker.trans (le_of_eq hZ)) bot_le)
  let e : ↥(StatedSp m (GaloisField 2 1)) ≃* Jb := MulEquiv.ofBijective ψ ⟨hinj, hψsurj⟩
  have hZJ : Subgroup.center Jb = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : e.symm z ∈ Subgroup.center ↥(StatedSp m (GaloisField 2 1)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact Subgroup.mem_center_iff.1 hz (e g)
    rw [hZ, Subgroup.mem_bot] at hz'
    rw [Subgroup.mem_bot, ← e.apply_symm_apply z, hz', map_one]
  have hqinj : Function.Injective (QuotientGroup.mk' (Subgroup.center Jb)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hZJ]
  let E : ↥(StatedSp m (GaloisField 2 1)) ≃* (Jb ⧸ Subgroup.center Jb) :=
    MulEquiv.ofBijective ((QuotientGroup.mk' (Subgroup.center Jb)).comp ψ)
      ⟨hqinj.comp hinj, (QuotientGroup.mk'_surjective _).comp hψsurj⟩
  obtain ⟨β, hβ, hs, h2β⟩ := rckSp_shortRoot m 1 (by omega)
  obtain ⟨r, V, hrβ, hr1, hrV, hV, hcard, hconj, hN⟩ := rckSp_pair hm hβ hs
  have hinn : ∀ σ : MulAut ↥(StatedSp m (GaloisField 2 1)), ∃ c, σ = MulAut.conj c := by
    intro σ
    obtain ⟨c, hc⟩ := CFSG.StandardType.PRankBounds.exists_conj_of_mulAut_spTwo hm σ
    exact ⟨c, MulEquiv.ext hc⟩
  have hdata : RCKK1Data r V := ⟨hrV, hr1, hV, hcard, hconj, rckK1b_of_inner hZ hinn r V hN⟩
  refine ⟨E r, V.map E.toMonoidHom, rckK1Data_map E hdata, ?_⟩
  refine ⟨.PSp, m, 1, β, ggRootSub (ggU .PSp m 1).D φ β 1, Or.inl rfl, le_rfl, hβ, hs, h2β,
    ⟨φ, MonoidHom.range_eq_top.2 hsurj, hker, 1, rfl⟩, ?_⟩
  exact Subgroup.mem_map.2 ⟨φ r, Subgroup.mem_map.2 ⟨r, Subgroup.mem_map.2 ⟨r, hrβ,
    by simp [MulAut.conj_apply]; rfl⟩, rfl⟩, rfl⟩

end CFSG.StandardType.RCKK1IIISp

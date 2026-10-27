module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.SigmaCentZ
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.AutZCartan.KFact
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.AutZCartan.Semilinear
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.SL3GeomTransfer
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.Holds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem odd_relIndex_centralizer (D : Data G) :
    Odd ((D.M ⊓ Subgroup.centralizer (D.Z : Set G)).relIndex D.M) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT_CGZ : D.T ≤ Subgroup.centralizer (D.Z : Set G) :=
    Subgroup.le_centralizer_iff.mp fun z hz =>
      (Subgroup.mem_inf.mp
        (CFSG.LocalAnalysis.RankThreeUC.omegaOneCenterIn_le_inf_centralizer D.T hz)).2
  have hTodd : Odd (D.T.relIndex D.M) :=
    Nat.not_even_iff_odd.mp fun he =>
      (CFSG.ABGLocalTools.isSylowOf_iff.mp D.sylowM).2.2 (even_iff_two_dvd.mp he)
  exact Odd.of_dvd_nat hTodd
    (Subgroup.relIndex_dvd_of_le_left D.M (le_inf D.sylowM.le hT_CGZ))

private theorem zpow_conj_transitive {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V)
    {y : ↥c.L} {h : ↥(c.H hV)} (hy : c.phiL hV y = h)
    (htr : ∀ v ∈ c.Ztil hV, ∀ w ∈ c.Ztil hV, v ≠ 1 → w ≠ 1 →
      ∃ k : ℤ, ((h ^ k : ↥(c.H hV)) : MulAut (c.W hV)) v = w) :
    ∀ z ∈ D.Z, ∀ w ∈ D.Z, z ≠ 1 → w ≠ 1 →
      ∃ k : ℤ, (y : G) ^ k * z * ((y : G) ^ k)⁻¹ = w := by
  intro z hz w hw hz1 hw1
  have hzV : z ∈ c.V := uc22p22v_le_conjClosure c.N D.Z hz
  have hwV : w ∈ c.V := uc22p22v_le_conjClosure c.N D.Z hw
  let vz : IntMod c.V hV := IntMod.mk hV ⟨z, hzV⟩
  let vw : IntMod c.V hV := IntMod.mk hV ⟨w, hwV⟩
  have hvz : mkTil (⊥ : Subgroup G) c.V hV vz ∈ c.Ztil hV :=
    (mem_imgTil (⊥ : Subgroup G) c.V hV D.Z _).2 ⟨vz, hz, rfl⟩
  have hvw : mkTil (⊥ : Subgroup G) c.V hV vw ∈ c.Ztil hV :=
    (mem_imgTil (⊥ : Subgroup G) c.V hV D.Z _).2 ⟨vw, hw, rfl⟩
  have hvz1 : mkTil (⊥ : Subgroup G) c.V hV vz ≠ 1 := by
    intro h1
    have h2 : vz = 1 := mkTil_injective_bot c.V hV (h1.trans (map_one _).symm)
    exact hz1 (congrArg IntMod.val h2)
  have hvw1 : mkTil (⊥ : Subgroup G) c.V hV vw ≠ 1 := by
    intro h1
    have h2 : vw = 1 := mkTil_injective_bot c.V hV (h1.trans (map_one _).symm)
    exact hw1 (congrArg IntMod.val h2)
  obtain ⟨k, hk⟩ := htr _ hvz _ hvw hvz1 hvw1
  refine ⟨k, ?_⟩
  let g : ↥c.L := y ^ k
  have hk' : (c.phiL hV g : MulAut (c.W hV))
      (mkTil (⊥ : Subgroup G) c.V hV vz) = mkTil (⊥ : Subgroup G) c.V hV vw := by
    have h := hk
    rw [← hy, ← map_zpow] at h
    exact h
  have heq : actStab (⊥ : Subgroup G) c.V hV
      ⟨g, c.L_le_stabTil g.2⟩ vz = vw := by
    apply mkTil_injective_bot c.V hV
    rw [← c.phiL_apply_mkTil hV g vz]
    exact hk'
  have hval := congrArg IntMod.val heq
  rw [actStab_apply_val] at hval
  simpa [vz, vw, g, IntMod.mk, IntMod.val, Subgroup.coe_zpow] using hval

theorem autZCartan_of (D : Data G) (Ch : Choice2011 G) (h2 : S23_2_natural D Ch)
    (h3 : S23_3 D Ch) (h4 : S23_4 D Ch) : AutZCartan D Ch := by
  intro h1930 c
  obtain ⟨hV, hnat⟩ := Ctx23L.exists_isNaturalClassicalModule D Ch h2 h3 h4 h1930 c
  have hZ : IsElemAbelian 2 D.Z := c.isElemAbelian_Z h4 h1930
  have hZcard : Nat.card D.Z = 2 ^ CFSG.Open.pRank (G := G) 2 D.Z :=
    CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_two hZ
  have hZ1 : D.Z ≠ ⊥ := uc22main1_Z_ne_bot D
  have hMZ : D.M ≤ Subgroup.normalizer (D.Z : Set G) := by
    obtain ⟨hUZ, -, hMN⟩ := h4 h1930 c
    simpa [hUZ] using hMN
  have hodd := odd_relIndex_centralizer D
  letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.W hV) :=
    MulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (Set (c.W hV)) := Set.mulActionSet
  letI : MulDistribMulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  letI : MulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  obtain ⟨h, hh, htr⟩ := AutZC.kLineTransitive_holds (c.W hV) (c.H hV)
    (CFSG.Open.pRank (G := G) 2 D.Z) hnat (c.commutator_H_eq hV) (c.sylowStar hV)
  have hfix : (CFSG.fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) :
      Subgroup (c.W hV)) = c.Ztil hV :=
    c.fixedPointSubgroup_sylowStar_eq_Ztil hV kTab23a_holds hnat h4 h1930
  have htrZ : ∀ v ∈ c.Ztil hV, ∀ w ∈ c.Ztil hV, v ≠ 1 → w ≠ 1 →
      ∃ k : ℤ, ((h ^ k : ↥(c.H hV)) : MulAut (c.W hV)) v = w := by
    intro v hv w hw hv1 hw1
    rw [← hfix] at hv hw
    exact htr v hv w hw hv1 hw1
  have hhstab : h ∈ MulAction.stabilizer ↥(c.H hV)
      ((c.Ztil hV : Subgroup (c.W hV)) : Set (c.W hV)) := by
    have hmem := hh
    rw [show KTabD.pointStab (c.H hV) (c.sylowStar hV) =
        MulAction.stabilizer ↥(c.H hV)
          (((CFSG.fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) :
            Subgroup (c.W hV)) : Set (c.W hV))) from rfl, hfix] at hmem
    exact hmem
  obtain ⟨y, hyφ⟩ := c.phiL_surjective hV h
  have hyM : (y : G) ∈ D.M :=
    (c.phiL_mem_stabilizer_Ztil_iff hV h4 h1930 y).1 (hyφ ▸ hhstab)
  have htrans := zpow_conj_transitive c hV (y := y) (h := h) hyφ htrZ
  obtain ⟨C, h1, h2', h3', hrel, h5⟩ :=
    AutZC.exists_cartan_of_zpowers_transitive (M := D.M) (Z := D.Z) hZ hZ1 hMZ hodd hyM
      htrans
  exact ⟨C, h1, h2', h3', by rw [hZcard] at hrel; exact hrel, h5⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22

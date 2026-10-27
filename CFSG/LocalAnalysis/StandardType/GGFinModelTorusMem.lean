module

public import CFSG.LocalAnalysis.StandardType.GGFinModelRat
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.Weyl
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.F4ModWeyl
import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesWeyl
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwFrob
import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleLang
import CFSG.Certificates.WordSubgroupRel
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcField
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSplit
import CFSG.HardMathSupport.Timmesfeld.LangTorus.Assembly
import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerTorus
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
import CFSG.LieType.AlgebraicGroups.ConnectedToralLang
import CFSG.LieType.Chevalley.OrdinaryRootCentralizerGeneration
import CFSG.LieType.Multipliers.ProductKernel
import CFSG.LieType.Multipliers.U42Bridge
import CFSG.LieType.Multipliers.U43Action
import CFSG.LieType.Multipliers.U43BridgeInputs
import CFSG.LieType.Multipliers.U62Action
import CFSG.LieType.Multipliers.U62Bridge
import CFSG.LieType.Multipliers.U62Kernel
import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type
import CFSG.Monster.B.Classical.PlaneAut
import CFSG.Monster.B.TwoA.Amalgam.Data
import CFSG.Monster.B.TwoA.Sp8.Par1
import CFSG.Monster.B.TwoA.Unitary.LinThree
import CFSG.RankThree.PartOne.K133H.G2Plane
import CFSG.RankThree.PartOne.KF.F128Cyclic
import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite
import CFSG.Sporadic.Presentation.Common
import CFSG.Sporadic.Schreier.TitsOther
import CFSG.Sporadic.SmallOddCore.CheckSpec
import CFSG.YGroups.Y322Central
import Certificates.Certificate10005
import Certificates.Certificate10006
import Certificates.Certificate10007
import Certificates.Certificate10008
import Certificates.Certificate10009
import Certificates.Certificate10010
import Certificates.Certificate10012
import Certificates.Certificate10013
import Certificates.Certificate10014
import Certificates.Certificate10016
import Certificates.Certificate10018
import Certificates.Certificate12041
import Certificates.Certificate12042
import Certificates.Certificate12043
import Certificates.Certificate12044
import Certificates.Certificate12045
import Certificates.Certificate12046
import Certificates.Certificate16015
import Certificates.Certificate16040
import Certificates.Certificate2154
import Certificates.Certificate2157
import Certificates.Certificate2326
import Certificates.Certificate3006
import Certificates.Certificate3007
import Certificates.Certificate3008
import Certificates.Certificate3063
import Certificates.Certificate3077
import Certificates.Certificate3082
import Certificates.Certificate3083
import Certificates.Certificate9130

public section

namespace CFSG.StandardType.GGFinModel

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE.CTTorus

private lemma ggMat_mulVec_permLattice {τ : Tag} (ε : ℤ) (π' : Equiv.Perm (Fin τ.rank))
    (x : Fin τ.rank → ℤ) :
    Matrix.mulVec (Matrix.of fun i j => if π'.symm i = j then ε else 0) x =
      ε • permLattice π' x := by
  ext i
  rw [Matrix.mulVec_apply_eq_sum]
  simp only [Matrix.of_apply, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp [permLattice, Pi.smul_apply, smul_eq_mul]

private lemma ggRootChar_frob {τ : Tag} {f p : ℕ} {ζ : GGLˣ} (hζ : orderOf ζ = p)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (hpε : (p : ℤ) ∣ ε * 2 ^ f - 1)
    (π' : Equiv.Perm (Fin τ.rank)) {a : Fin τ.rank → GGLˣ}
    (ha_pow : ∀ i, a i ^ p = 1) (hafix : ∀ i, a (π' i) = a i)
    (u : Fin τ.rank → ℤ) :
    rootChar a (ε • permLattice π' u) = Units.map (ggFrobT f).toMonoidHom (rootChar a u) := by
  set x : GGLˣ := rootChar a u with hxdef
  have hfun : (fun i => a (π' i)) = a := funext hafix
  have hfix : rootChar a (permLattice π' u) = x := by
    rw [rootChar_permLattice, hfun, hxdef]
  have hdiv : orderOf x ∣ p := orderOf_dvd_iff_pow_eq_one.mpr (rootChar_pow_eq_one ha_pow u)
  have hdivZ : (orderOf x : ℤ) ∣ (p : ℤ) := by exact_mod_cast hdiv
  have hx1 : x ^ (ε * 2 ^ f - 1) = 1 :=
    orderOf_dvd_iff_zpow_eq_one.mp (dvd_trans hdivZ hpε)
  have hmap : Units.map (ggFrobT f).toMonoidHom x = x ^ (2 : ℕ) ^ f := by
    ext
    simp [Units.val_pow_eq_pow_val, ggFrobT_apply]
  rcases hε with rfl | rfl
  · rw [one_smul]
    have hx2 : x ^ (2 : ℕ) ^ f = x := by
      rw [← zpow_natCast, Nat.cast_pow]
      have h1 : x ^ ((2 : ℤ) ^ f - 1) = 1 := by simpa using hx1
      calc x ^ ((2 : ℤ) ^ f) = x ^ (((2 : ℤ) ^ f - 1) + 1) := by ring
        _ = x ^ ((2 : ℤ) ^ f - 1) * x ^ (1 : ℤ) := by rw [zpow_add]
        _ = 1 * x := by rw [h1, zpow_one]
        _ = x := one_mul x
    rw [hfix, hmap]
    exact hx2.symm
  · rw [neg_one_smul]
    have hneg : rootChar a (-permLattice π' u) = (rootChar a (permLattice π' u))⁻¹ := by
      have h := rootChar_sub a 0 (permLattice π' u)
      rwa [zero_sub, rootChar_zero, one_mul] at h
    have hx2 : x ^ (2 : ℕ) ^ f = x⁻¹ := by
      rw [← zpow_natCast, Nat.cast_pow]
      have h1 : x ^ ((2 : ℤ) ^ f + 1) = 1 := by
        have h0 : x ^ (-((2 : ℤ) ^ f + 1)) = 1 := by
          have he : (-((2 : ℤ) ^ f + 1)) = (-1) * 2 ^ f - 1 := by ring
          rw [he]
          exact hx1
        rw [zpow_neg] at h0
        exact inv_eq_one.mp h0
      calc x ^ ((2 : ℤ) ^ f) = x ^ (((2 : ℤ) ^ f + 1) + (-1)) := by ring
        _ = x ^ ((2 : ℤ) ^ f + 1) * x ^ (-1 : ℤ) := by rw [zpow_add]
        _ = 1 * x⁻¹ := by rw [h1, zpow_neg_one]
        _ = x⁻¹ := one_mul x⁻¹
    rw [hneg, hfix, hmap]
    exact hx2.symm

section TorusMem


theorem ggTorusMem_untw {τ : Tag} {f : ℕ} (D : LangDatum τ GGL) (w : WeylGroup τ)
    (hΦ : D.Φ = Units.map (entrywiseHom (ggFrobT f)))
    (hn : D.n = canonicalRep (coxeterSystem τ) GGL w) {p : ℕ} {ζ : GGLˣ} (hζ : orderOf ζ = p)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (hpε : (p : ℤ) ∣ ε * 2 ^ f - 1)
    (π' : Equiv.Perm (Fin τ.rank))
    (hw : ∀ u : Fin τ.rank → ℤ, w • u = ε • permLattice π' u)
    (z : Fin τ.rank → ZMod p) (hz : ∀ i, z (π' i) = z i) :
    rootDiagUnit τ (fun j => ζ ^ ZMod.val (z j)) ∈ D.torus := by
  let a : Fin τ.rank → GGLˣ := fun j => ζ ^ ZMod.val (z j)
  have ha_pow : ∀ i, a i ^ p = 1 := by
    intro i
    have hζp : ζ ^ p = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
    change (ζ ^ ZMod.val (z i)) ^ p = 1
    calc (ζ ^ ZMod.val (z i)) ^ p = ζ ^ (ZMod.val (z i) * p) := by rw [pow_mul]
      _ = ζ ^ (p * ZMod.val (z i)) := by rw [mul_comm]
      _ = (ζ ^ p) ^ ZMod.val (z i) := by rw [pow_mul]
      _ = 1 := by rw [hζp, one_pow]
  have hafix : ∀ i, a (π' i) = a i := by
    intro i
    change ζ ^ ZMod.val (z (π' i)) = ζ ^ ZMod.val (z i)
    rw [hz i]
  have ha : a ∈ twistedFixedTuples w (ggFrobT f) :=
    (mem_twistedFixedTuples_iff (w := w) (Fr := ggFrobT f) (a := a)).2 fun u => by
      rw [hw u]
      exact ggRootChar_frob hζ hε hpε π' ha_pow hafix u
  rw [LangDatum.torus, hΦ, hn]
  exact mem_twistedTorusOf.2
    ⟨rootDiagUnit_mem_torusGroup a, (mem_twistedFixedTuples_iff_conj (a := a)).1 ha⟩

theorem ggTorusMem_tw {f : ℕ} (D : LangDatum TwistTag.E6.tag GGL) (w : WeylGroup TwistTag.E6.tag)
    (hΦ : D.Φ = twistHom TwistTag.E6 GGL (ggFrobT f))
    (hn : D.n = canonicalRep (coxeterSystem TwistTag.E6.tag) GGL w) {p : ℕ} {ζ : GGLˣ}
    (hζ : orderOf ζ = p) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (hpε : (p : ℤ) ∣ ε * 2 ^ f - 1)
    (π' : Equiv.Perm (Fin TwistTag.E6.tag.rank))
    (hw : ∀ u : Fin TwistTag.E6.tag.rank → ℤ,
      w • permLattice (TwistTag.perm .E6) u = ε • permLattice π' u)
    (z : Fin TwistTag.E6.tag.rank → ZMod p) (hz : ∀ i, z (π' i) = z i) :
    rootDiagUnit TwistTag.E6.tag (fun j => ζ ^ ZMod.val (z j)) ∈ D.torus := by
  let a : Fin TwistTag.E6.tag.rank → GGLˣ := fun j => ζ ^ ZMod.val (z j)
  have ha_pow : ∀ i, a i ^ p = 1 := by
    intro i
    have hζp : ζ ^ p = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
    change (ζ ^ ZMod.val (z i)) ^ p = 1
    calc (ζ ^ ZMod.val (z i)) ^ p = ζ ^ (ZMod.val (z i) * p) := by rw [pow_mul]
      _ = ζ ^ (p * ZMod.val (z i)) := by rw [mul_comm]
      _ = (ζ ^ p) ^ ZMod.val (z i) := by rw [pow_mul]
      _ = 1 := by rw [hζp, one_pow]
  have hafix : ∀ i, a (π' i) = a i := by
    intro i
    change ζ ^ ZMod.val (z (π' i)) = ζ ^ ZMod.val (z i)
    rw [hz i]
  let M : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ :=
    Matrix.of fun i j => if π'.symm i = j then ε else 0
  have hvM : ∀ x, w • permLattice (TwistTag.perm .E6) x = Matrix.mulVec M x := fun x => by
    rw [hw x]
    exact (ggMat_mulVec_permLattice (τ := TwistTag.E6.tag) ε π' x).symm
  have ha : a ∈ fixedCharTuples M (ggFrobT f) := by
    rw [mem_fixedCharTuples_iff]
    intro u
    rw [← hvM u]
    rw [hw u]
    exact ggRootChar_frob hζ hε hpε π' ha_pow hafix u
  rw [LangDatum.torus, hΦ, hn]
  rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedTorusOf_twistHom_eq_map
    TwistTag.E6 (ggFrobT f) w M hvM]
  exact ⟨a, ha, rfl⟩

theorem ggRho_untw {τ : Tag} {f : ℕ} (D : LangDatum τ GGL) (w : WeylGroup τ)
    (hΦ : D.Φ = Units.map (entrywiseHom (ggFrobT f)))
    (hn : D.n = canonicalRep (coxeterSystem τ) GGL w) {ε : ℤ} (π' : Equiv.Perm (Fin τ.rank))
    (hw : ∀ u : Fin τ.rank → ℤ, w • u = ε • permLattice π' u)
    (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (hρ : FrobRootMap D ρ) {v : Fin τ.rank → ℤ}
    (hv : IsRoot τ v) : ρ v = ε • permLattice π' v := by
  obtain ⟨ε₂, hε₂, h₂⟩ := exists_canonicalRep_mul_pinnedX_mul_inv GGL w hv
  have hμ : ε₂ ≠ 0 := fun h => by
    rw [h, mul_zero] at hε₂
    exact one_ne_zero hε₂.symm
  have hsurj : Function.Surjective (fun c : GGL => ε₂ * c ^ 2 ^ f) := by
    intro y
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (n := 2 ^ f) (y / ε₂)
      (pow_pos (by norm_num : (0 : ℕ) < 2) f)
    refine ⟨x, ?_⟩
    show ε₂ * x ^ 2 ^ f = y
    rw [hx]
    field_simp
  have hstep : ∀ c : GGL, D.step (pinnedX τ GGL v c) =
      pinnedX τ GGL (w • v) (ε₂ * c ^ 2 ^ f) := by
    intro c
    have hs : D.step (pinnedX τ GGL v c) =
        D.n * D.Φ (pinnedX τ GGL v c) * D.n⁻¹ := by
      simp [LangDatum.step, MulAut.conj_apply]
    rw [hs, hΦ, hn, units_map_entrywiseHom_pinnedX, ggFrobT_apply]
    exact h₂ (c ^ 2 ^ f)
  have hmap : (rootSubgroup τ GGL v).map D.step = rootSubgroup τ GGL (w • v) :=
    map_rootSubgroup_eq_of_forall hsurj hstep
  have heq : rootSubgroup τ GGL (ρ v) = rootSubgroup τ GGL (w • v) := by
    rw [← hρ.map_rootSubgroup v hv, hmap]
  have hmem : pinnedX τ GGL (w • v) 1 ∈ rootSubgroup τ GGL (ρ v) := by
    rw [heq]
    exact mem_rootSubgroup.2 ⟨1, rfl⟩
  have hwv : w • v = ρ v :=
    eq_of_pinnedX_one_mem_rootSubgroup (IsRoot.smul hv w) ((hρ.isRoot_iff v).2 hv) hmem
  rw [← hwv]
  exact hw v

theorem ggRho_tw {f : ℕ} (D : LangDatum TwistTag.E6.tag GGL) (w : WeylGroup TwistTag.E6.tag)
    (hΦ : D.Φ = twistHom TwistTag.E6 GGL (ggFrobT f))
    (hn : D.n = canonicalRep (coxeterSystem TwistTag.E6.tag) GGL w) {ε : ℤ}
    (π' : Equiv.Perm (Fin TwistTag.E6.tag.rank))
    (hw : ∀ u : Fin TwistTag.E6.tag.rank → ℤ,
      w • permLattice (TwistTag.perm .E6) u = ε • permLattice π' u)
    (ρ : Equiv.Perm (Fin TwistTag.E6.tag.rank → ℤ)) (hρ : FrobRootMap D ρ)
    {v : Fin TwistTag.E6.tag.rank → ℤ} (hv : IsRoot TwistTag.E6.tag v) :
    ρ v = ε • permLattice π' v := by
  have hFr : Function.Surjective (ggFrobT f) := by
    intro y
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (n := 2 ^ f) y
      (pow_pos (by norm_num : (0 : ℕ) < 2) f)
    exact ⟨x, by rw [ggFrobT_apply, hx]⟩
  have hstep_eq : D.step = CFSG.HardMathSupport.Timmesfeld.CrossChar.twFrob TwistTag.E6
      (canonicalRep (coxeterSystem TwistTag.E6.tag) GGL w) (ggFrobT f) := by
    rw [LangDatum.step, hn, hΦ, CFSG.HardMathSupport.Timmesfeld.CrossChar.twFrob]
  have hmap : (rootSubgroup TwistTag.E6.tag GGL v).map D.step =
      rootSubgroup TwistTag.E6.tag GGL (w • permLattice (TwistTag.perm .E6) v) := by
    rw [hstep_eq]
    exact CFSG.HardMathSupport.Timmesfeld.CrossChar.map_twFrob_rootSubgroup
      TwistTag.E6 hFr w hv
  have heq : rootSubgroup TwistTag.E6.tag GGL (ρ v) =
      rootSubgroup TwistTag.E6.tag GGL (w • permLattice (TwistTag.perm .E6) v) := by
    rw [← hρ.map_rootSubgroup v hv, hmap]
  have hroot : IsRoot TwistTag.E6.tag (w • permLattice (TwistTag.perm .E6) v) :=
    IsRoot.smul (hv.permLattice TwistTag.E6.cartan_perm) w
  have hmem : pinnedX TwistTag.E6.tag GGL
      (w • permLattice (TwistTag.perm .E6) v) 1 ∈ rootSubgroup TwistTag.E6.tag GGL (ρ v) := by
    rw [heq]
    exact mem_rootSubgroup.2 ⟨1, rfl⟩
  have hwv : w • permLattice (TwistTag.perm .E6) v = ρ v :=
    eq_of_pinnedX_one_mem_rootSubgroup hroot ((hρ.isRoot_iff v).2 hv) hmem
  rw [← hwv]
  exact hw v

theorem ggWeylNeg_exists {τ : Tag} (hτ : τ = .F4 ∨ τ = .E7 ∨ τ = .E8) :
    ∃ w : WeylGroup τ, ∀ u : Fin τ.rank → ℤ, w • u = -u := by
  rcases hτ with rfl | rfl | rfl
  · exact CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.exists_weyl_neg_F4'
  · exact exists_weyl_neg_E7
  · exact exists_weyl_neg_E8

theorem ggWeylE6_exists :
    ∃ w : WeylGroup TwistTag.E6.tag, ∀ u : Fin TwistTag.E6.tag.rank → ℤ,
      w • u = -permLattice (TwistTag.perm .E6) u := by
  exact ⟨(coxeterSystem TwistTag.E6.tag).wordProd
      CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.e6W0Word,
    CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.e6W0_smul⟩

end TorusMem

end CFSG.StandardType.GGFinModel

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsFiveLineA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsFiveTransfer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsTwentyEight
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsFiveLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsFiveKNshape
public import CFSG.Adapters.LieModelSimple
import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx23L

variable {D : Data G} {Ch : Choice2011 G}

theorem commutator_L_eq_top (c : Ctx23L D Ch) :
    ⁅(⊤ : Subgroup ↥c.L), (⊤ : Subgroup ↥c.L)⁆ = ⊤ := by
  haveI : Group.IsPerfect ↥c.L := Subgroup.isPerfect_iff.mpr c.hL.1.2.1
  rw [← commutator_def]
  exact Group.IsPerfect.commutator_eq_top

private theorem commutator_H_eq_top (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) :
    ⁅(⊤ : Subgroup ↥(c.H hV)), (⊤ : Subgroup ↥(c.H hV))⁆ = ⊤ := by
  haveI : Group.IsPerfect ↥(c.H hV) := Subgroup.isPerfect_iff.mpr (c.commutator_H_eq hV)
  rw [← commutator_def]
  exact Group.IsPerfect.commutator_eq_top

private theorem Hinf_top_eq_top (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) :
    Hinf (⊤ : Subgroup ↥(c.H hV)) = ⊤ :=
  le_antisymm (uc22p21c_Hinf_le ⊤) (uc22p21c_le_Hinf le_rfl (c.commutator_H_eq_top hV))

theorem phiL_ker_commutator_mem_pCore (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hK : KOrdNatural) {n : ℕ} (hnat : IsNaturalClassicalModule (c.H hV) n) :
    ∀ x ∈ (c.phiL hV).ker, ∀ y : ↥c.L, x * y * x⁻¹ * y⁻¹ ∈ CFSG.pCore 2 ↥c.L := by
  intro x hx y
  have hx1 : c.phiL hV x = 1 := hx
  have hxV : (x : G) ∈ Subgroup.centralizer (c.V : Set G) :=
    (c.phiL_eq_one_iff hV x).1 hx1
  have hcomm := c.commutator_mem_pCoreOf hV hK hnat (x : G)
    (Subgroup.mem_inf.mpr ⟨x.2, hxV⟩) (y : G) y.2
  obtain ⟨z, hz, hzval⟩ := Subgroup.mem_map.mp
    (show (x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹ ∈
      (CFSG.pCore 2 ↥c.L).map c.L.subtype from hcomm)
  rw [show (x * y * x⁻¹ * y⁻¹ : ↥c.L) = z from Subtype.ext hzval.symm]
  exact hz

theorem nonempty_bar2_mulEquiv (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hK : KOrdNatural) {n j : ℕ} (hnat : IsNaturalClassicalModule (c.H hV) n) (hS : KSchurL2)
    (hshape : IsL2 (↥(c.H hV) ⧸ CFSG.pCore 2 ↥(c.H hV)) j ∨
      IsL2Square (↥(c.H hV) ⧸ CFSG.pCore 2 ↥(c.H hV)) j) :
    Nonempty (Bar2 c.L ≃* ↥(c.H hV)) :=
  (comap_pCore_eq_of_pCore_eq_bot (c.phiL hV) (c.phiL_surjective hV) (c.commutator_L_eq_top)
    (c.phiL_ker_commutator_mem_pCore hV hK hnat) hS hshape (hK.1 hnat)).2

private theorem one_le_of_isOmegaMinus_four {X : Type} [Group X] {m : ℕ}
    (h : IsOmegaMinus X 4 m) : 1 ≤ m := by
  obtain ⟨-, K, hKfield, hKfinite, b, q, hKcard, -, -⟩ := h
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  refine Nat.one_le_iff_ne_zero.mpr fun h0 => ?_
  have hKgt : 1 < Nat.card K := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  rw [hKcard, h0, pow_zero] at hKgt
  exact lt_irrefl 1 hKgt

private theorem isL2_bar2_L0_of_alt (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hK : KOrdNatural) {n : ℕ} (hnat : IsNaturalClassicalModule (c.H hV) n) (hS : KSchurL2)
    {Pstar : Subgroup ↥(c.H hV)} (hY0 : Hinf Pstar = c.Y0 hV)
    (h : IsL2 (Bar2 (Hinf Pstar)) (CFSG.Open.pRank 2 D.Z) ∨
      (CFSG.Open.pRank 2 D.Z = 1 ∧ Hinf Pstar = ⊥)) :
    IsL2 (Bar2 c.L0) (CFSG.Open.pRank 2 D.Z) := by
  rcases h with h | ⟨-, hbot⟩
  · exact c.isL2_bar2_L0_of hV hK hnat hS (hY0 ▸ h)
  · have hbot' : c.Y0 hV = ⊥ := hY0 ▸ hbot
    exact absurd hbot' (c.map_L0_ne_bot hV hK hnat)

private def Good23 (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) :
    Subgroup ↥(c.H hV) → Prop :=
  letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.W hV) :=
    MulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (Set (c.W hV)) := Set.mulActionSet
  letI : MulDistribMulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  let ℓ : Subgroup (c.W hV) := fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV)
  let Pℓ : Subgroup ↥(c.H hV) := MulAction.stabilizer ↥(c.H hV) (ℓ : Set (c.W hV))
  fun Pstar =>
    IsParabolicTwo ↥(c.H hV) Pstar ∧ (c.sylowStar hV : Subgroup ↥(c.H hV)) ≤ Pstar ∧
    (∀ t ∈ c.Tstar hV,
      (Pstar.map (c.H hV).subtype).map (MulAut.conj t).toMonoidHom =
        Pstar.map (c.H hV).subtype) ∧
    ¬ Pstar ≤ Pℓ

private theorem fixedPointSubgroup_sylowStar_eq_Ztil' (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) (hA : KTab23a)
    (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z)) (h4 : S23_4 D Ch)
    (h1930 : H1930 D) :
    letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
      MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
    letI : MulAction ↥(c.H hV) (c.W hV) :=
      MulAction.compHom (c.W hV) (c.H hV).subtype
    letI : MulDistribMulAction ↥(c.sylowStar hV) (c.W hV) :=
      MulDistribMulAction.compHom (c.W hV)
        ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
    fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) = c.Ztil hV := by
  letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.W hV) :=
    MulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulDistribMulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  simpa only [MulDistribMulAction.compHom] using
    c.fixedPointSubgroup_sylowStar_eq_Ztil hV hA hnat h4 h1930

private theorem mkTil_mem_fixedPointSubgroup (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {v : G} (hvV : v ∈ c.V)
    (hvC : v ∈ Subgroup.centralizer (((D.T ⊓ c.L : Subgroup G) : Set G))) :
    letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
      MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
    letI : MulAction ↥(c.H hV) (c.W hV) :=
      MulAction.compHom (c.W hV) (c.H hV).subtype
    letI : MulDistribMulAction ↥(c.sylowStar hV) (c.W hV) :=
      MulDistribMulAction.compHom (c.W hV)
        ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
    letI : MulAction ↥(c.sylowStar hV) (c.W hV) :=
      MulAction.compHom (c.W hV)
        ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
    mkTil (⊥ : Subgroup G) c.V hV (CFSG.Quasithin.IntMod.mk hV ⟨v, hvV⟩) ∈
      fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) := by
  letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.W hV) :=
    MulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulDistribMulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  letI : MulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  rw [FixedPoints.mem_subgroup]
  intro s
  have hs : (s : ↥(c.H hV)) ∈ (c.sylowStar hV : Subgroup ↥(c.H hV)) := s.2
  rw [c.sylowStar_coe hV] at hs
  obtain ⟨y, hy, hyφ⟩ := Subgroup.mem_map.mp hs
  have hyT : (y : G) ∈ D.T := Subgroup.mem_subgroupOf.mp hy
  have hcomm : (y : G) * v * (y : G)⁻¹ = v := by
    have hc := Subgroup.mem_centralizer_iff.mp hvC (y : G) ⟨hyT, y.2⟩
    calc (y : G) * v * (y : G)⁻¹ = v * (y : G) * (y : G)⁻¹ := by rw [hc]
      _ = v := by group
  simp only [MulAction.compHom_smul_def, MulAut.smul_def, MonoidHom.comp_apply,
    show (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype s = c.phiL hV y from hyφ.symm]
  change (c.phiL hV y : MulAut (c.W hV)) (mkTil (⊥ : Subgroup G) c.V hV
    (CFSG.Quasithin.IntMod.mk hV ⟨v, hvV⟩)) =
    mkTil (⊥ : Subgroup G) c.V hV (CFSG.Quasithin.IntMod.mk hV ⟨v, hvV⟩)
  rw [c.phiL_apply_mkTil hV y]
  congr 1
  apply CFSG.Quasithin.IntMod.val_injective
  rw [actStab_apply_val]
  simpa only [CFSG.Quasithin.IntMod.mk, CFSG.Quasithin.IntMod.val] using hcomm

private theorem infCentralizer_eq_Z (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hA : KTab23a) (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z))
    (h4 : S23_4 D Ch) (h1930 : H1930 D) :
    D.Z = c.V ⊓ Subgroup.centralizer (((D.T ⊓ c.L : Subgroup G) : Set G)) := by
  letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.W hV) :=
    MulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulDistribMulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  letI : MulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  have hZV : D.Z ≤ c.V := uc22p22v_le_conjClosure c.N D.Z
  have hZC : D.Z ≤ Subgroup.centralizer (((D.T ⊓ c.L : Subgroup G) : Set G)) :=
    (Subgroup.le_centralizer_iff.mp
      (CFSG.LocalAnalysis.RankThreeUC.le_centralizer_omegaOneCenterIn D.T)).trans
      (Subgroup.centralizer_le (inf_le_left : D.T ⊓ c.L ≤ D.T))
  refine le_antisymm (le_inf hZV hZC) ?_
  intro v hv
  obtain ⟨hvV, hvC⟩ := Subgroup.mem_inf.mp hv
  have hℓ : fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) = c.Ztil hV :=
    c.fixedPointSubgroup_sylowStar_eq_Ztil' hV hA hnat h4 h1930
  have hfix := c.mkTil_mem_fixedPointSubgroup hV hvV hvC
  rw [hℓ] at hfix
  have hpre : v ∈ preTil (⊥ : Subgroup G) c.V hV
      (imgTil (⊥ : Subgroup G) c.V hV D.Z) :=
    (mem_preTil_iff_of_mem (⊥ : Subgroup G) c.V hV _ hvV).2 hfix
  rwa [CFSG.LocalAnalysis.WeakClosure81.preTil_imgTil_of_le hV hZV bot_le] at hpre

private theorem normalizer_infCentralizer_le_normalizer_Z (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) (hA : KTab23a)
    (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z))
    (h4 : S23_4 D Ch) (h1930 : H1930 D) :
    c.L ⊓ Subgroup.normalizer (((D.T ⊓ c.L : Subgroup G) : Set G)) ≤
      Subgroup.normalizer (D.Z : Set G) := by
  have hZeq := c.infCentralizer_eq_Z hV hA hnat h4 h1930
  have hpres : ∀ {x : G}, x ∈ c.L →
      x ∈ Subgroup.normalizer (((D.T ⊓ c.L : Subgroup G) : Set G)) →
      ∀ w ∈ c.V ⊓ Subgroup.centralizer (((D.T ⊓ c.L : Subgroup G) : Set G)),
        x * w * x⁻¹ ∈ c.V ⊓
          Subgroup.centralizer (((D.T ⊓ c.L : Subgroup G) : Set G)) := by
    intro x hxL hxN w hw
    have hxV : x ∈ Subgroup.normalizer (c.V : Set G) :=
      ((le_sup_left : c.L ≤ c.L ⊔ D.T).trans (sup_le_normalizer_V D Ch c)) hxL
    have hxInvN : x⁻¹ ∈ Subgroup.normalizer (((D.T ⊓ c.L : Subgroup G) : Set G)) :=
      Subgroup.inv_mem _ hxN
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hxV w).1 hw.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : x⁻¹ * y * x ∈ D.T ⊓ c.L := by
      simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp hxInvN y).1 hy
    have hzy : (x⁻¹ * y * x) * w = w * (x⁻¹ * y * x) :=
      Subgroup.mem_centralizer_iff.mp hw.2 (x⁻¹ * y * x) hy'
    calc y * (x * w * x⁻¹) = x * ((x⁻¹ * y * x) * w) * x⁻¹ := by group
      _ = x * (w * (x⁻¹ * y * x)) * x⁻¹ := by rw [hzy]
      _ = (x * w * x⁻¹) * y := by group
  intro x hx
  obtain ⟨hxL, hxN⟩ := Subgroup.mem_inf.mp hx
  rw [hZeq, Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · rintro ⟨hzV, hzC⟩
    exact hpres hxL hxN z ⟨hzV, hzC⟩
  · intro hz
    have := hpres (c.L.inv_mem hxL) (Subgroup.inv_mem _ hxN) (x * z * x⁻¹) hz
    simpa [mul_assoc] using this

theorem L_eq_L0_of_Pstar_eq_top (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hK : KOrdNatural) (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z))
    {P : Subgroup G} (hP : MinTInvParabolic D.T D.M c.L P) (hL0P : c.L0 = Hinf P)
    (hTop : Pstar c hV P = ⊤) : c.L = c.L0 := by
  have hY0top : c.Y0 hV = ⊤ := by
    have h := c.Hinf_Pstar hV P hP hL0P
    rw [hTop] at h
    exact h.symm.trans (Hinf_top_eq_top c hV)
  have hL0leP : c.L0 ≤ P := hL0P.symm ▸ uc22p21c_Hinf_le P
  have hCLV : c.L ⊓ Subgroup.centralizer (c.V : Set G) ≤ P :=
    c.inf_centralizer_V_le_of_parabolic hV hK hnat hP.1.1
  have hLleP : c.L ≤ P := by
    intro x hx
    have hmem : c.phiL hV ⟨x, hx⟩ ∈ (c.Y0 hV : Subgroup ↥(c.H hV)) := by
      rw [hY0top]
      exact Subgroup.mem_top _
    obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.1 hmem
    have hyP : (y : G) ∈ P := hL0leP (Subgroup.mem_subgroupOf.1 hy)
    have hker : c.phiL hV (⟨x, hx⟩ * y⁻¹) = 1 := by
      rw [map_mul, map_inv, hxy, mul_inv_cancel]
    have hmem2 : ((⟨x, hx⟩ * y⁻¹ : ↥c.L) : G) ∈
        c.L ⊓ Subgroup.centralizer (c.V : Set G) :=
      Subgroup.mem_inf.mpr ⟨(⟨x, hx⟩ * y⁻¹ : ↥c.L).2, (c.phiL_eq_one_iff hV _).1 hker⟩
    have hxP : ((⟨x, hx⟩ * y⁻¹ : ↥c.L) : G) ∈ P := hCLV hmem2
    have hxeq : x = ((⟨x, hx⟩ * y⁻¹ : ↥c.L) : G) * (y : G) := by
      change x = (x * (y : G)⁻¹) * (y : G)
      group
    rw [hxeq]
    exact P.mul_mem hxP hyP
  have hPeq : P = c.L := le_antisymm (parabolicOf_iff.mp hP.1.1).1 hLleP
  have hL0eq : c.L0 = c.L := by
    rw [hL0P, hPeq]
    exact le_antisymm (uc22p21c_Hinf_le c.L) (uc22p21c_le_Hinf le_rfl c.hL.1.2.1)
  exact hL0eq.symm

private theorem omegaMinus_line (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) (hK : KOrdNatural)
    (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z)) (hS : KSchurL2)
    (hA : KTab23a) (h4 : S23_4 D Ch) (h1930 : H1930 D) (hC : KTab23c) {P : Subgroup G}
    (hP : MinTInvParabolic D.T D.M c.L P) (hL0P : c.L0 = Hinf P)
    (hOm : IsOmegaMinus ↥(c.H hV) 4 (CFSG.Open.pRank 2 D.Z))
    (hNatOm : NatOmegaMinus (c.H hV) ⊤ ⊥ 4 (CFSG.Open.pRank 2 D.Z))
    (hTop : Pstar c hV P = ⊤)
    (hL2Y : IsL2 (Bar2 (c.Y0 hV)) (2 * CFSG.Open.pRank 2 D.Z)) :
    c.L = c.L0 ∧ IsOmegaMinus (Bar2 c.L) 4 (CFSG.Open.pRank 2 D.Z) ∧
      IsL2 (Bar2 c.L0) (2 * CFSG.Open.pRank 2 D.Z) ∧
      piSet (c.B ⊓ Subgroup.centralizer (D.Z : Set G)) =
        piSet c.B ∩ {p | p.Prime ∧ p ∣ 2 ^ CFSG.Open.pRank 2 D.Z + 1} := by
  have hLL0 : c.L = c.L0 := L_eq_L0_of_Pstar_eq_top c hV hK hnat hP hL0P hTop
  have hL2 : IsL2 (Bar2 c.L0) (2 * CFSG.Open.pRank 2 D.Z) :=
    c.isL2_bar2_L0_of hV hK hnat hS hL2Y
  have hn1 : 1 ≤ CFSG.Open.pRank 2 D.Z := one_le_of_isOmegaMinus_four hOm
  have hbot : CFSG.pCore 2 ↥(c.H hV) = ⊥ := hK.1 hnat
  have hshape : IsL2 (↥(c.H hV) ⧸ CFSG.pCore 2 ↥(c.H hV))
        (2 * CFSG.Open.pRank 2 D.Z) ∨
      IsL2Square (↥(c.H hV) ⧸ CFSG.pCore 2 ↥(c.H hV)) (2 * CFSG.Open.pRank 2 D.Z) := by
    left
    exact CFSG.Blueprint.LieModel.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).symm
      (isL2_two_mul_of_isOmegaMinus_four hn1 hOm)
  obtain ⟨e⟩ := c.nonempty_bar2_mulEquiv hV hK hnat hS hshape
  have hOmBar : IsOmegaMinus (Bar2 c.L) 4 (CFSG.Open.pRank 2 D.Z) :=
    IsOmegaMinus.of_mulEquiv e.symm hOm
  have hℓ : fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) = c.Ztil hV :=
    c.fixedPointSubgroup_sylowStar_eq_Ztil' hV hA hnat h4 h1930
  have hinj : c.B ⊓ Subgroup.centralizer (c.V : Set G) = ⊥ :=
    c.inf_centralizer_V_eq_bot hV hK hnat hS (Or.inl hL2Y)
  have hCapp := hC (c.W hV) (c.H hV) (CFSG.Open.pRank 2 D.Z) hnat (c.commutator_H_eq hV)
    (c.sylowStar hV) (c.Bstar hV) (c.isMulCommutative_Bstar hV) (c.odd_card_Bstar hV hinj)
    (c.card_sup_sylowStar_Bstar hV hinj)
  have hpi := hCapp.1 ⟨hOm, hNatOm⟩
  have hpi' : piSet (c.Bstar hV ⊓ fixingSubgroupOf ↥(c.H hV) (c.W hV)
      ((fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) : Subgroup (c.W hV)) : Set (c.W hV))) =
      piSet (c.Bstar hV) ∩ {p : ℕ | p.Prime ∧ p ∣ 2 ^ CFSG.Open.pRank 2 D.Z + 1} := by
    with_unfolding_all exact hpi
  rw [hℓ] at hpi'
  refine ⟨hLL0, hOmBar, hL2, ?_⟩
  rw [← c.piSet_inf_Bstar_CH hV hinj, ← c.piSet_Bstar hV hinj]
  exact hpi'

private theorem isQuasisimple_of_isL2 {X : Type} [Group X] {j : ℕ}
    (h : IsL2 X j) : CFSG.Open.IsQuasisimple X := by
  haveI : IsSimpleGroup X :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL) (by decide) h
  obtain ⟨a, b, hab⟩ := CFSG.ComponentClassification.HarrisLit.nonabelian_of_lieModel_psl2 h
  obtain ⟨hperfect, hsimple, -⟩ :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup ⟨a, b, hab⟩).1
  exact ⟨hperfect.commutator_eq_top, hsimple⟩

theorem omegaPlus_lineA (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) (hK : KOrdNatural)
    (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z)) (hS : KSchurL2)
    (hA : KTab23a) (h4 : S23_4 D Ch) (h1930 : H1930 D) (hC : KTab23c) {P : Subgroup G}
    (hP : MinTInvParabolic D.T D.M c.L P) (hL0P : c.L0 = Hinf P)
    (hPlus : IsOmegaPlus ↥(c.H hV) 4 (CFSG.Open.pRank 2 D.Z))
    (hNatPlus : NatOmegaPlus (c.H hV) ⊤ ⊥ 4 (CFSG.Open.pRank 2 D.Z))
    (hTop : Pstar c hV P = ⊤)
    (hSq : IsL2Square (Bar2 (c.Y0 hV)) (CFSG.Open.pRank 2 D.Z)) :
    c.L = c.L0 ∧ IsL2Square (Bar2 c.L0) (CFSG.Open.pRank 2 D.Z) ∧
      ∀ A : Subgroup G, A ≤ c.L0 → IsMulCommutative A → Odd (Nat.card A) → Permutes A D.T →
        IsCyclic ↥(A ⊓ Subgroup.centralizer (D.Z : Set G)) := by
  have hLL0 : c.L = c.L0 := L_eq_L0_of_Pstar_eq_top c hV hK hnat hP hL0P hTop
  have hsq : IsL2Square (Bar2 c.L0) (CFSG.Open.pRank 2 D.Z) :=
    c.isL2Square_bar2_L0_of hV hK hnat hS hSq
  have hℓ : fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) = c.Ztil hV :=
    c.fixedPointSubgroup_sylowStar_eq_Ztil' hV hA hnat h4 h1930
  refine ⟨hLL0, hsq, ?_⟩
  intro A hA0 hAab hAodd hAT
  have hinj : A ⊓ Subgroup.centralizer (c.V : Set G) = ⊥ :=
    c.inf_centralizer_V_eq_bot_of_le hV hK hnat hS (Or.inr hSq) hA0 hAodd
  have hCapp := hC (c.W hV) (c.H hV) (CFSG.Open.pRank 2 D.Z) hnat (c.commutator_H_eq hV)
    (c.sylowStar hV) (c.Astar hV A) (c.isMulCommutative_Astar hV hAab)
    (c.odd_card_Astar hV hA0 hAodd hinj) (c.card_sup_sylowStar_Astar hV hA0 hAodd hAT hinj)
  obtain ⟨hcyc, -⟩ := hCapp.2 ⟨hPlus, hNatPlus⟩
  have hcyc' : IsCyclic ↥(c.Astar hV A ⊓ fixingSubgroupOf ↥(c.H hV) (c.W hV)
      ((fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) : Subgroup (c.W hV)) :
        Set (c.W hV))) := by
    with_unfolding_all exact hcyc
  rw [hℓ] at hcyc'
  exact c.isCyclic_inf_centralizer_Z_of_le hV hA0 hinj hcyc'

private theorem nine_line (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) (hK : KOrdNatural)
    (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z)) (hS : KSchurL2)
    (hA : KTab23a) (h4 : S23_4 D Ch) (h1930 : H1930 D) (hKN9 : KTab23cNine)
    (hnine : NineLines (c.H hV) (CFSG.Open.pRank 2 D.Z)) {P : Subgroup G}
    (hY0 : Hinf (Pstar c hV P) = c.Y0 hV)
    (hmin : Minimal (Good23 c hV) (Pstar c hV P))
    (hres : IsL2 (Bar2 (Hinf (Pstar c hV P))) (CFSG.Open.pRank 2 D.Z) ∨
      (CFSG.Open.pRank 2 D.Z = 1 ∧ Hinf (Pstar c hV P) = ⊥)) :
    IsL2 (Bar2 c.L0) (CFSG.Open.pRank 2 D.Z) ∧
      c.B ⊓ Subgroup.centralizer (D.Z : Set G) = ⊥ := by
  letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.W hV) :=
    MulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (Set (c.W hV)) := Set.mulActionSet
  letI : MulDistribMulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  have hL2 : IsL2 (Bar2 c.L0) (CFSG.Open.pRank 2 D.Z) :=
    c.isL2_bar2_L0_of_alt hV hK hnat hS hY0 hres
  have hY : IsL2 (Bar2 (c.Y0 hV)) (CFSG.Open.pRank 2 D.Z) := by
    rcases hres with h | ⟨-, hbot⟩
    · exact hY0 ▸ h
    · have hbot' : c.Y0 hV = ⊥ := by
        rw [← hY0]
        exact hbot
      exact absurd hbot' (c.map_L0_ne_bot hV hK hnat)
  have hinj : c.B ⊓ Subgroup.centralizer (c.V : Set G) = ⊥ :=
    c.inf_centralizer_V_eq_bot hV hK hnat hS (Or.inl hY)
  have hBle : c.Bstar hV ≤ Hinf (Pstar c hV P) := by
    rw [hY0]
    exact c.Astar_le_Y0 hV c.hB.1
  have hfix := hKN9 (c.W hV) (c.H hV) (CFSG.Open.pRank 2 D.Z) hnine (c.commutator_H_eq hV)
    (c.sylowStar hV) (c.Tstar hV) (c.Tstar_le_normalizer hV) (c.isPGroup_Tstar hV)
    (c.sylowStar_le_Tstar hV) (Pstar c hV P) hmin (c.Bstar hV) hBle
    (c.odd_card_Bstar hV hinj)
  have hℓ : fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) = c.Ztil hV :=
    c.fixedPointSubgroup_sylowStar_eq_Ztil' hV hA hnat h4 h1930
  have hCH : c.Bstar hV ⊓ c.CH hV = ⊥ := by
    rw [hℓ] at hfix
    with_unfolding_all exact hfix
  exact ⟨hL2, c.inf_centralizer_Z_eq_bot_of hV hinj hCH⟩

private theorem false_of_isL2_of_isL2Square {X : Type} [Group X] {j m : ℕ}
    (hsq : IsL2Square X m) (hL2 : IsL2 X j) : False :=
  not_isQuasisimple_of_isL2Square hsq (isQuasisimple_of_isL2 hL2)

private theorem omegaPlus_case (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hK : KOrdNatural) (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z))
    (hS : KSchurL2) (hA : KTab23a) (h4 : S23_4 D Ch) (h1930 : H1930 D) (hC : KTab23c)
    {P : Subgroup G} (hP : MinTInvParabolic D.T D.M c.L P) (hL0P : c.L0 = Hinf P)
    (hY0 : Hinf (Pstar c hV P) = c.Y0 hV)
    (hPlus : IsOmegaPlus ↥(c.H hV) 4 (CFSG.Open.pRank 2 D.Z))
    (hNatPlus : NatOmegaPlus (c.H hV) ⊤ ⊥ 4 (CFSG.Open.pRank 2 D.Z))
    (hTop : Pstar c hV P = ⊤)
    (hSq : IsL2Square (Bar2 (c.Y0 hV)) (CFSG.Open.pRank 2 D.Z)) :
    c.L = c.L0 ∧
      (∀ A : Subgroup G, A ≤ c.L0 → IsMulCommutative A → Odd (Nat.card A) → Permutes A D.T →
        IsCyclic ↥(A ⊓ Subgroup.centralizer (D.Z : Set G))) ∧
      c.L0 ⊓ Subgroup.normalizer ((D.T ⊓ c.L0 : Subgroup G) : Set G) ≤
        Subgroup.normalizer (D.Z : Set G) := by
  obtain ⟨hLL0, -, hAcyc⟩ := c.omegaPlus_lineA hV hK hnat hS hA h4 h1930 hC hP hL0P
    hPlus hNatPlus hTop hSq
  refine ⟨hLL0, hAcyc, ?_⟩
  intro x hx
  exact c.normalizer_infCentralizer_le_normalizer_Z hV hA hnat h4 h1930
    (by rw [hLL0]; exact hx)

private theorem false_of_isL2_alt_of_isL2Square (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) (hK : KOrdNatural)
    (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z)) (hS : KSchurL2)
    {P : Subgroup G} (hP : MinTInvParabolic D.T D.M c.L P) (hL0P : c.L0 = Hinf P)
    (hY0 : Hinf (Pstar c hV P) = c.Y0 hV)
    (hsq : IsL2Square (Bar2 c.L0) (CFSG.Open.pRank 2 D.Z)) :
    (IsL2 (Bar2 (Hinf (Pstar c hV P))) (CFSG.Open.pRank 2 D.Z) ∨
      (CFSG.Open.pRank 2 D.Z = 1 ∧ Hinf (Pstar c hV P) = ⊥)) → False :=
  fun h => false_of_isL2_of_isL2Square hsq (c.isL2_bar2_L0_of_alt hV hK hnat hS hY0 h)

private theorem omegaPlus_line (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) (hK : KOrdNatural)
    (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z)) (hS : KSchurL2)
    (hA : KTab23a) (h4 : S23_4 D Ch) (h1930 : H1930 D) (hC : KTab23c) {P : Subgroup G}
    (hP : MinTInvParabolic D.T D.M c.L P) (hL0P : c.L0 = Hinf P)
    (hPlus : IsOmegaPlus ↥(c.H hV) 4 (CFSG.Open.pRank 2 D.Z))
    (hNatPlus : NatOmegaPlus (c.H hV) ⊤ ⊥ 4 (CFSG.Open.pRank 2 D.Z))
    (hTop : Pstar c hV P = ⊤)
    (hSq : IsL2Square (Bar2 (c.Y0 hV)) (CFSG.Open.pRank 2 D.Z)) :
    c.L = c.L0 ∧ IsL2Square (Bar2 c.L0) (CFSG.Open.pRank 2 D.Z) ∧
      IsCyclic ↥(c.B ⊓ Subgroup.centralizer (D.Z : Set G)) ∧
      ∀ E : Subgroup G, E ≤ c.B → E ⊓ Subgroup.centralizer (D.Z : Set G) = ⊥ →
        IsCyclic ↥E := by
  have hLL0 : c.L = c.L0 := L_eq_L0_of_Pstar_eq_top c hV hK hnat hP hL0P hTop
  have hsq : IsL2Square (Bar2 c.L0) (CFSG.Open.pRank 2 D.Z) :=
    c.isL2Square_bar2_L0_of hV hK hnat hS hSq
  have hℓ : fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) = c.Ztil hV :=
    c.fixedPointSubgroup_sylowStar_eq_Ztil' hV hA hnat h4 h1930
  have hinj : c.B ⊓ Subgroup.centralizer (c.V : Set G) = ⊥ :=
    c.inf_centralizer_V_eq_bot hV hK hnat hS (Or.inr hSq)
  have hCapp := hC (c.W hV) (c.H hV) (CFSG.Open.pRank 2 D.Z) hnat (c.commutator_H_eq hV)
    (c.sylowStar hV) (c.Bstar hV) (c.isMulCommutative_Bstar hV) (c.odd_card_Bstar hV hinj)
    (c.card_sup_sylowStar_Bstar hV hinj)
  obtain ⟨hcyc, hcycE⟩ := hCapp.2 ⟨hPlus, hNatPlus⟩
  have hcyc' : IsCyclic ↥(c.Bstar hV ⊓ fixingSubgroupOf ↥(c.H hV) (c.W hV)
      ((fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) : Subgroup (c.W hV)) :
        Set (c.W hV))) := by
    with_unfolding_all exact hcyc
  have hcycE' : ∀ E : Subgroup ↥(c.H hV), E ≤ c.Bstar hV →
      E ⊓ fixingSubgroupOf ↥(c.H hV) (c.W hV)
        ((fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) : Subgroup (c.W hV)) :
          Set (c.W hV)) = ⊥ → IsCyclic ↥E := by
    with_unfolding_all exact hcycE
  rw [hℓ] at hcyc' hcycE'
  refine ⟨hLL0, hsq, c.isCyclic_inf_centralizer_Z_of hV hinj hcyc', ?_⟩
  intro E hE hEdisj
  exact c.isCyclic_of_isCyclic_map_subgroupOf hV hinj hE
    (hcycE' _ (c.map_subgroupOf_le_Bstar hV hE) (c.inf_map_subgroupOf_CH_eq_bot hV hE hEdisj))

private abbrev ProperLines {W : Type} [CommGroup W] (H : Subgroup (MulAut W)) (n : ℕ) : Prop :=
  (IsSp4 ↥H n ∧ NatSpn H ⊤ ⊥ 4 n) ∨
  (IsSLn ↥H 3 n ∧ CFSG.Quasithin.BinaryNaturalSL H ⊤ ⊥ 3 n) ∨
  (∃ a : ℕ, n = 2 * a ∧ IsSUn ↥H 4 a ∧ NatSUn H ⊤ ⊥ 4 a) ∨
  (IsOmegaMinus ↥H 6 n ∧ NatOmegaMinus H ⊤ ⊥ 6 n) ∨
  (IsSLn ↥H 4 n ∧ CFSG.Quasithin.BinaryNaturalSL H ⊤ ⊥ 4 n) ∨
  (IsOmegaPlus ↥H 6 n ∧ NatOmegaPlus H ⊤ ⊥ 6 n) ∨
  (IsSpn ↥H 6 n ∧ NatSpn H ⊤ ⊥ 6 n) ∨
  (IsOmega8m ↥H n ∧ NatOmegaMinus H ⊤ ⊥ 8 n)

private theorem proper_lines (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hK : KOrdNatural) (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z))
    (hS : KSchurL2) (hA : KTab23a) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hKN9 : KTab23cNine) (hB : KTab23b) {P : Subgroup G}
    (hY0 : Hinf (Pstar c hV P) = c.Y0 hV)
    (hmin : Minimal (Good23 c hV) (Pstar c hV P))
    (hrest : ProperLines (c.H hV) (CFSG.Open.pRank 2 D.Z)) :
    (IsL2 (Bar2 c.L0) (CFSG.Open.pRank 2 D.Z) ∧
        c.B ⊓ Subgroup.centralizer (D.Z : Set G) = ⊥) ∨
      IsL2 (Bar2 c.L0) (2 * CFSG.Open.pRank 2 D.Z) ∨
      IsL2Square (Bar2 c.L0) (CFSG.Open.pRank 2 D.Z) := by
  have hTab := hB (c.W hV) (c.H hV) (CFSG.Open.pRank 2 D.Z) hnat (c.commutator_H_eq hV)
    (c.sylowStar hV) (c.Tstar hV) (c.Tstar_le_normalizer hV) (c.isPGroup_Tstar hV)
    (c.sylowStar_le_Tstar hV)
  obtain ⟨-, -, -, hT4, hT5, hT6, hT7, hT8, hT9, hT10, hT11⟩ := hTab
  have go : ∀ (hnine : NineLines (c.H hV) (CFSG.Open.pRank 2 D.Z)),
      (IsL2 (Bar2 (Hinf (Pstar c hV P))) (CFSG.Open.pRank 2 D.Z) ∨
        (CFSG.Open.pRank 2 D.Z = 1 ∧ Hinf (Pstar c hV P) = ⊥)) →
      IsL2 (Bar2 c.L0) (CFSG.Open.pRank 2 D.Z) ∧
        c.B ⊓ Subgroup.centralizer (D.Z : Set G) = ⊥ :=
    fun hnine hres => c.nine_line hV hK hnat hS hA h4 h1930 hKN9 hnine hY0 hmin hres
  rcases hrest with ⟨hSp4, hN⟩ | ⟨hSL3, hN⟩ | ⟨a, hna, hSUn, hN⟩ | ⟨hOm6, hN⟩ |
    ⟨hSL4, hN⟩ | ⟨hPlus6, hN⟩ | ⟨hSpn, hN⟩ | ⟨hOm8, hN⟩
  · refine Or.inl (go (Or.inr (Or.inl ⟨hSp4, hN⟩)) (hT4 ⟨hSp4, hN⟩ _ hmin).2)
  · refine Or.inl (go (Or.inr (Or.inr (Or.inl ⟨hSL3, hN⟩))) (hT5 ⟨hSL3, hN⟩ _ hmin).2)
  · refine Or.inl (go (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, hna, hSUn, hN⟩))))
      (hT6 ⟨a, hna, hSUn, hN⟩ _ hmin).2)
  · refine Or.inl (go (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hOm6, hN⟩)))))
      (hT7 ⟨hOm6, hN⟩ _ hmin).2)
  · refine Or.inl (go (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hSL4, hN⟩))))))
      (hT8 ⟨hSL4, hN⟩ _ hmin).2)
  · refine Or.inl (go (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨hPlus6, hN⟩))))))) (hT9 ⟨hPlus6, hN⟩ _ hmin).2)
  · refine Or.inl (go (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨hSpn, hN⟩)))))))) (hT10 ⟨hSpn, hN⟩ _ hmin).2)
  · refine Or.inl (go (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr ⟨hOm8, hN⟩)))))))) (hT11 ⟨hOm8, hN⟩ _ hmin).2)

end Ctx23L

theorem s23_5_line_of (D : Data G) (Ch : Choice2011 G) (h2 : S23_2_natural D Ch)
    (h3 : S23_3 D Ch) (h4 : S23_4 D Ch) (h209 : S20_9 D) (hK : KOrdNatural) (hA : KTab23a)
    (hB : KTab23b) (hC : KTab23c) (hS : KSchurL2) : S23_5_line D Ch := by
  intro h1930 c
  obtain ⟨hV, hnat⟩ := Ctx23L.exists_isNaturalClassicalModule D Ch h2 h3 h4 h1930 c
  obtain ⟨P, hP, hL0P⟩ := (h209 h1930 c.L c.hL.1 c.L0).1 ⟨c.hL0, c.hL0L⟩
  have hmin := c.minimal_good_Pstar hV hA h4 h1930 hnat P hP
  have hY0 : Hinf (Ctx23L.Pstar c hV P) = c.Y0 hV := c.Hinf_Pstar hV P hP hL0P
  have hTab := hB (c.W hV) (c.H hV) (CFSG.Open.pRank 2 D.Z) hnat (c.commutator_H_eq hV)
    (c.sylowStar hV) (c.Tstar hV) (c.Tstar_le_normalizer hV) (c.isPGroup_Tstar hV)
    (c.sylowStar_le_Tstar hV)
  obtain ⟨hT1, hT2, hT3, hT4, hT5, hT6, hT7, hT8, hT9, hT10, hT11⟩ := hTab
  have hnat' := hnat
  rcases hnat' with ⟨hL2, hN⟩ | ⟨hOm, hN⟩ | ⟨hPlus, hN⟩ | ⟨hSp4, hN⟩ | ⟨hSL3, hN⟩ |
    ⟨a, hna, hSUn, hN⟩ | ⟨hOm6, hN⟩ | ⟨hSL4, hN⟩ | ⟨hPlus6, hN⟩ | ⟨hSpn, hN⟩ | ⟨hOm8, hN⟩
  · exact Or.inl (c.isL2_bar2_L0_of hV hK hnat hS (hY0 ▸ (hT1 ⟨hL2, hN⟩ _ hmin).2))
  · have h := hT2 ⟨hOm, hN⟩ (Ctx23L.Pstar c hV P) hmin
    exact Or.inr (Or.inl (c.omegaMinus_line hV hK hnat hS hA h4 h1930 hC hP hL0P hOm hN
      h.1 (hY0 ▸ h.2)))
  · have h := hT3 ⟨hPlus, hN, c.le_center_of_normal_of_ne_top hV hK hnat⟩
      (Ctx23L.Pstar c hV P) hmin
    exact Or.inr (Or.inr (c.omegaPlus_line hV hK hnat hS hA h4 h1930 hC hP hL0P hPlus hN
      h.1 (hY0 ▸ h.2)))
  · exact Or.inl (c.isL2_bar2_L0_of_alt hV hK hnat hS hY0 (hT4 ⟨hSp4, hN⟩ _ hmin).2)
  · exact Or.inl (c.isL2_bar2_L0_of_alt hV hK hnat hS hY0 (hT5 ⟨hSL3, hN⟩ _ hmin).2)
  · exact Or.inl (c.isL2_bar2_L0_of_alt hV hK hnat hS hY0
      (hT6 ⟨a, hna, hSUn, hN⟩ _ hmin).2)
  · exact Or.inl (c.isL2_bar2_L0_of_alt hV hK hnat hS hY0 (hT7 ⟨hOm6, hN⟩ _ hmin).2)
  · exact Or.inl (c.isL2_bar2_L0_of_alt hV hK hnat hS hY0 (hT8 ⟨hSL4, hN⟩ _ hmin).2)
  · exact Or.inl (c.isL2_bar2_L0_of_alt hV hK hnat hS hY0 (hT9 ⟨hPlus6, hN⟩ _ hmin).2)
  · exact Or.inl (c.isL2_bar2_L0_of_alt hV hK hnat hS hY0 (hT10 ⟨hSpn, hN⟩ _ hmin).2)
  · exact Or.inl (c.isL2_bar2_L0_of_alt hV hK hnat hS hY0 (hT11 ⟨hOm8, hN⟩ _ hmin).2)

theorem s23_5_lineOmegaPlus_of (D : Data G) (Ch : Choice2011 G) (h2 : S23_2_natural D Ch)
    (h3 : S23_3 D Ch) (h4 : S23_4 D Ch) (h209 : S20_9 D) (hK : KOrdNatural) (hA : KTab23a)
    (hB : KTab23b) (hC : KTab23c) (hS : KSchurL2) : S23_5_lineOmegaPlus D Ch := by
  intro h1930 c hsq
  obtain ⟨hV, hnat⟩ := Ctx23L.exists_isNaturalClassicalModule D Ch h2 h3 h4 h1930 c
  obtain ⟨P, hP, hL0P⟩ := (h209 h1930 c.L c.hL.1 c.L0).1 ⟨c.hL0, c.hL0L⟩
  have hmin := c.minimal_good_Pstar hV hA h4 h1930 hnat P hP
  have hY0 : Hinf (Ctx23L.Pstar c hV P) = c.Y0 hV := c.Hinf_Pstar hV P hP hL0P
  have key : ∀ {j : ℕ}, IsL2 (Bar2 c.L0) j → False :=
    Ctx23L.false_of_isL2_of_isL2Square hsq
  have keyAlt := c.false_of_isL2_alt_of_isL2Square hV hK hnat hS hP hL0P hY0 hsq
  have hTab := hB (c.W hV) (c.H hV) (CFSG.Open.pRank 2 D.Z) hnat (c.commutator_H_eq hV)
    (c.sylowStar hV) (c.Tstar hV) (c.Tstar_le_normalizer hV) (c.isPGroup_Tstar hV)
    (c.sylowStar_le_Tstar hV)
  obtain ⟨hT1, hT2, hT3, hT4, hT5, hT6, hT7, hT8, hT9, hT10, hT11⟩ := hTab
  have hnat' := hnat
  rcases hnat' with ⟨hL2, hN⟩ | ⟨hOm, hN⟩ | ⟨hPlus, hN⟩ | ⟨hSp4, hN⟩ | ⟨hSL3, hN⟩ |
    ⟨a, hna, hSUn, hN⟩ | ⟨hOm6, hN⟩ | ⟨hSL4, hN⟩ | ⟨hPlus6, hN⟩ | ⟨hSpn, hN⟩ | ⟨hOm8, hN⟩
  · have hL2' : IsL2 (Bar2 c.L0) (CFSG.Open.pRank 2 D.Z) :=
      c.isL2_bar2_L0_of hV hK hnat hS (hY0 ▸ (hT1 ⟨hL2, hN⟩ _ hmin).2)
    exact (key hL2').elim
  · have h := hT2 ⟨hOm, hN⟩ (Ctx23L.Pstar c hV P) hmin
    have hL2' : IsL2 (Bar2 c.L0) (2 * CFSG.Open.pRank 2 D.Z) :=
      c.isL2_bar2_L0_of hV hK hnat hS (hY0 ▸ h.2)
    exact (key hL2').elim
  · have h := hT3 ⟨hPlus, hN, c.le_center_of_normal_of_ne_top hV hK hnat⟩
      (Ctx23L.Pstar c hV P) hmin
    exact c.omegaPlus_case hV hK hnat hS hA h4 h1930 hC hP hL0P hY0 hPlus hN h.1
      (hY0 ▸ h.2)
  · exact (keyAlt (hT4 ⟨hSp4, hN⟩ _ hmin).2).elim
  · exact (keyAlt (hT5 ⟨hSL3, hN⟩ _ hmin).2).elim
  · exact (keyAlt (hT6 ⟨a, hna, hSUn, hN⟩ _ hmin).2).elim
  · exact (keyAlt (hT7 ⟨hOm6, hN⟩ _ hmin).2).elim
  · exact (keyAlt (hT8 ⟨hSL4, hN⟩ _ hmin).2).elim
  · exact (keyAlt (hT9 ⟨hPlus6, hN⟩ _ hmin).2).elim
  · exact (keyAlt (hT10 ⟨hSpn, hN⟩ _ hmin).2).elim
  · exact (keyAlt (hT11 ⟨hOm8, hN⟩ _ hmin).2).elim

theorem s23_5_lineL2_of (D : Data G) (Ch : Choice2011 G) (h2 : S23_2_natural D Ch)
    (h3 : S23_3 D Ch) (h4 : S23_4 D Ch) (h209 : S20_9 D) (hK : KOrdNatural) (hA : KTab23a)
    (hB : KTab23b) (hS : KSchurL2) (hKN9 : KTab23cNine) : S23_5_lineL2 D Ch := by
  intro h1930 c
  obtain ⟨hV, hnat⟩ := Ctx23L.exists_isNaturalClassicalModule D Ch h2 h3 h4 h1930 c
  obtain ⟨P, hP, hL0P⟩ := (h209 h1930 c.L c.hL.1 c.L0).1 ⟨c.hL0, c.hL0L⟩
  have hmin := c.minimal_good_Pstar hV hA h4 h1930 hnat P hP
  have hY0 : Hinf (Ctx23L.Pstar c hV P) = c.Y0 hV := c.Hinf_Pstar hV P hP hL0P
  have hTab := hB (c.W hV) (c.H hV) (CFSG.Open.pRank 2 D.Z) hnat (c.commutator_H_eq hV)
    (c.sylowStar hV) (c.Tstar hV) (c.Tstar_le_normalizer hV) (c.isPGroup_Tstar hV)
    (c.sylowStar_le_Tstar hV)
  obtain ⟨hT1, hT2, hT3, _⟩ := hTab
  have go : ∀ (hnine : NineLines (c.H hV) (CFSG.Open.pRank 2 D.Z)),
      (IsL2 (Bar2 (Hinf (Ctx23L.Pstar c hV P))) (CFSG.Open.pRank 2 D.Z) ∨
        (CFSG.Open.pRank 2 D.Z = 1 ∧ Hinf (Ctx23L.Pstar c hV P) = ⊥)) →
      IsL2 (Bar2 c.L0) (CFSG.Open.pRank 2 D.Z) ∧
        c.B ⊓ Subgroup.centralizer (D.Z : Set G) = ⊥ :=
    fun hnine hres => c.nine_line hV hK hnat hS hA h4 h1930 hKN9 hnine hY0 hmin hres
  have hnat' := hnat
  rcases hnat' with ⟨hL2, hN⟩ | ⟨hOm, hN⟩ | ⟨hPlus, hN⟩ | hrest
  · refine Or.inl (go ?_ (Or.inl (hT1 ⟨hL2, hN⟩ _ hmin).2))
    exact Or.inl ⟨hL2, hN⟩
  · have h := hT2 ⟨hOm, hN⟩ (Ctx23L.Pstar c hV P) hmin
    exact Or.inr (Or.inl (c.isL2_bar2_L0_of hV hK hnat hS (hY0 ▸ h.2)))
  · have h := hT3 ⟨hPlus, hN, c.le_center_of_normal_of_ne_top hV hK hnat⟩
      (Ctx23L.Pstar c hV P) hmin
    exact Or.inr (Or.inr (c.isL2Square_bar2_L0_of hV hK hnat hS (hY0 ▸ h.2)))
  · exact Ctx23L.proper_lines c hV hK hnat hS hA h4 h1930 hKN9 hB hY0 hmin hrest

end CFSG.LocalAnalysis.UniquenessCase.UC22

end

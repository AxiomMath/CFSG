module

public import CFSG.LocalAnalysis.StandardType.GGOmegaPlusRootGenDefs
public import CFSG.Assembly.Subnormal
import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcResCent
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearNative
import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
import CFSG.ClassicalInvolution.QuaternionStructure
import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8Perfect
import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8TwoLift
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
import CFSG.RankThree.PartOne.S11d.OutLinear
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Open CFSG.Quasithin
  CFSG.SeitzReduction CFSG.SeitzReduction.SymplecticPilot Subgroup Multiplicative

variable {K : Type} [Field K] {m p : ℕ} {ζ : Kˣ}

private noncomputable def omPlusParams (hζ : ζ ^ p = 1) :
    (Fin m → Multiplicative (ZMod p)) →* (Fin m → Kˣ) :=
  MonoidHom.compLeft (TableBSymp.zmodPowHom hζ) (Fin m)

private theorem omPlusParams_apply (hζ : ζ ^ p = 1)
    (f : Fin m → Multiplicative (ZMod p)) (j : Fin m) :
    omPlusParams hζ f j = TableBSymp.zmodPowHom hζ (f j) :=
  rfl

private theorem omPlusTorusGL_eq_diagOmega (hζ : ζ ^ p = 1)
    (f : Fin m → Multiplicative (ZMod p)) :
    omPlusTorusGL hζ f = OmegaPilot.diagOmega K m (omPlusParams hζ f) :=
  rfl

private theorem omPlusParams_mulSingle (hζ : ζ ^ p = 1) (j : Fin m)
    (x : Multiplicative (ZMod p)) :
    omPlusParams hζ (Pi.mulSingle j x) = Pi.mulSingle j (TableBSymp.zmodPowHom hζ x) := by
  funext k
  rw [omPlusParams_apply, Pi.mulSingle_apply, Pi.mulSingle_apply]
  by_cases h : k = j
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, map_one]

private theorem omPlusParams_sgnAut (hζ : ζ ^ p = 1) (j : Fin m)
    (f : Fin m → Multiplicative (ZMod p)) :
    omPlusParams hζ (SpCoord.sgnAut j f) =
      OmegaPilot.flipParam K {j} (omPlusParams hζ f) := by
  funext k
  rw [omPlusParams_apply, OmegaPilot.flipParam_apply, omPlusParams_apply]
  by_cases hk : k = j
  · subst hk
    rw [SpCoord.sgnAut_apply, Function.update_self, map_inv]
    simp
  · rw [SpCoord.sgnAut_apply, Function.update_of_ne hk]
    simp [hk]

private theorem permAut_swap_eq_self_iff {p k : ℕ} {a b : Fin k}
    (f : Fin k → Multiplicative (ZMod p)) :
    SpCoord.permAut (Equiv.swap a b) f = f ↔ f a = f b := by
  constructor
  · intro h
    have h1 := congrFun h a
    rw [SpCoord.permAut_apply, Function.comp_apply, Equiv.swap_inv, Equiv.swap_apply_left] at h1
    exact h1.symm
  · intro h
    funext j
    rw [SpCoord.permAut_apply, Function.comp_apply, Equiv.swap_inv]
    by_cases hja : j = a
    · subst hja
      rw [Equiv.swap_apply_left, h]
    · by_cases hjb : j = b
      · subst hjb
        rw [Equiv.swap_apply_right, h]
      · rw [Equiv.swap_apply_of_ne_of_ne hja hjb]

private theorem omPlusRefl_true_apply {i j : Fin m} (hij : i < j)
    (f : Fin m → Multiplicative (ZMod p)) (k : Fin m) :
    omPlusRefl p (⟨(i, j), hij⟩, true) f k =
      if k = i then (f j)⁻¹ else if k = j then (f i)⁻¹ else f k := by
  have hne : i ≠ j := ne_of_lt hij
  rw [omPlusRefl_true (p := p), MulAut.mul_apply, MulAut.mul_apply]
  simp only [SpCoord.sgnAut_apply, SpCoord.permAut_apply, Equiv.swap_inv]
  by_cases hki : k = i
  · subst hki
    rw [if_pos rfl]
    simp only [Function.update_self, Function.update_of_ne hne, Function.comp_apply,
      Equiv.swap_apply_left]
  · rw [if_neg hki]
    by_cases hkj : k = j
    · subst hkj
      rw [if_pos rfl]
      simp only [Function.update_self, Function.update_of_ne (Ne.symm hne),
        Function.comp_apply, Equiv.swap_apply_right]
    · rw [if_neg hkj]
      simp only [Function.update_of_ne hki, Function.update_of_ne hkj,
        Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hki hkj]

private theorem omPlusRefl_true_fixed {i j : Fin m} (hij : i < j) :
    {f : Fin m → Multiplicative (ZMod p) | omPlusRefl p (⟨(i, j), hij⟩, true) f = f} =
      SpCoord.sgnAut j '' {g : Fin m → Multiplicative (ZMod p) | g i = g j} := by
  have hne : i ≠ j := ne_of_lt hij
  ext f
  constructor
  · intro hf
    have h1 := congrFun hf i
    rw [omPlusRefl_true_apply hij, if_pos rfl] at h1
    refine ⟨SpCoord.sgnAut j f, ?_, ?_⟩
    · simp only [Set.mem_setOf_eq, SpCoord.sgnAut_apply, Function.update_of_ne hne,
        Function.update_self]
      exact h1.symm
    · rw [← MulAut.mul_apply,
        show (SpCoord.sgnAut j * SpCoord.sgnAut j :
          MulAut (Fin m → Multiplicative (ZMod p))) = 1 by
          simpa [sq] using SpCoord.sgnAut_sq (p := p) j,
        MulAut.one_apply]
  · rintro ⟨g, hg, rfl⟩
    have hg' : g i = g j := hg
    funext k
    rw [omPlusRefl_true_apply hij]
    by_cases hki : k = i
    · subst hki
      rw [if_pos rfl]
      simp only [SpCoord.sgnAut_apply, Function.update_self, Function.update_of_ne hne,
        inv_inv]
      exact hg'.symm
    · rw [if_neg hki]
      by_cases hkj : k = j
      · subst hkj
        rw [if_pos rfl]
        simp only [SpCoord.sgnAut_apply, Function.update_self, Function.update_of_ne hne, hg']
      · rw [if_neg hkj]

private theorem centralizer_omPlusTorus_image [Finite K] [CharP K 2] (hζ : ζ ^ p = 1)
    (X : Set (Fin m → Multiplicative (ZMod p))) :
    Subgroup.centralizer ((omPlusTorus (p := p) hζ :
        (Fin m → Multiplicative (ZMod p)) →* StatedOmega (StatedQuadPlus m K)) '' X) =
      (StatedOmega (StatedQuadPlus m K) ⊓
        Subgroup.centralizer
          (OmegaPilot.diagOmega K m '' (omPlusParams hζ '' X))).subgroupOf
        (StatedOmega (StatedQuadPlus m K)) := by
  ext x
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro h
    refine ⟨x.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    simpa only [Subgroup.coe_mul, coe_omPlusTorus, omPlusTorusGL_eq_diagOmega] using
      congrArg Subtype.val (h _ ⟨f, hf, rfl⟩)
  · rintro ⟨-, h⟩
    rintro _ ⟨f, hf, rfl⟩
    exact Subtype.ext (h _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩)

private theorem isComponentOf_of_perfectCore_eq {G : Type*} [Group G] {C S : Subgroup G}
    (h : perfectCore C = S) (hq : CFSG.Assembly.IsQuasisimple S) :
    CFSG.Assembly.IsComponentOf S C := by
  subst h
  exact ⟨perfectCore_le C, CFSG.Assembly.IsSubnormal.step (perfectCore_le C)
    (perfectCore_normal C) (CFSG.Assembly.IsSubnormal.refl _), hq⟩

section Components

variable [Finite K] [CharP K 2]

theorem isComponentOf_omPlusBlock (hK : 4 ≤ Nat.card K)
    (hp : p.Prime) (hp2 : p ≠ 2) (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p)
    (x : OmPlusIdx m) :
    CFSG.Assembly.IsComponentOf
      ((omPlusBlock K x).subgroupOf (StatedOmega (StatedQuadPlus m K)))
      (Subgroup.centralizer ((omPlusTorus hζ :
        (Fin m → Multiplicative (ZMod p)) →* StatedOmega (StatedQuadPlus m K)) ''
        {f | omPlusRefl p x f = f})) := by
  classical
  obtain ⟨⟨⟨i, j⟩, hij⟩, s⟩ := x
  have hne : i ≠ j := ne_of_lt hij
  have hJc : ({i, j} : Finset (Fin m)).card = 2 := Finset.card_pair hne
  have hJ2 : 2 ≤ ({i, j} : Finset (Fin m)).card := by rw [hJc]
  have hκ : ζ * ζ ≠ 1 := by
    intro h
    have h1 : orderOf ζ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h)
    rw [hζo] at h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h1)
  have hχg : TableBSymp.zmodPowHom hζ (ofAdd (1 : ZMod p)) = ζ := by
    have h1 := TableBSymp.zmodPowHom_natCast hζ 1
    rwa [Nat.cast_one, pow_one] at h1
  have hζne : (ζ : K) ≠ ((ζ⁻¹ : Kˣ) : K) := fun e =>
    units_ne_inv_of_mul_self_ne_one hκ (Units.ext e)
  have hlevel : ∀ t ∈ omPlusParams hζ ''
      {g : Fin m → Multiplicative (ZMod p) | g i = g j},
      ∀ i' ∈ ({i, j} : Finset (Fin m)), ∀ j' ∈ ({i, j} : Finset (Fin m)), t i' = t j' := by
    intro t ht i' hi' j' hj'
    obtain ⟨g, hg, rfl⟩ := ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi' hj'
    rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl
    · rfl
    · rw [omPlusParams_apply, omPlusParams_apply, hg]
    · rw [omPlusParams_apply, omPlusParams_apply, hg]
    · rfl
  have hsep : ∀ a b : Fin m ⊕ Fin m, a ≠ b →
      ¬ OmegaPilot.SameSide ({i, j} : Finset (Fin m)) a b →
      ∃ t ∈ omPlusParams hζ '' {g : Fin m → Multiplicative (ZMod p) | g i = g j},
        diagSpEntry t a ≠ diagSpEntry t b := by
    intro a b hab hside
    by_cases hbJ : planeOf b ∉ ({i, j} : Finset (Fin m))
    · refine ⟨omPlusParams hζ (Pi.mulSingle (planeOf b) (ofAdd (1 : ZMod p))),
        ⟨_, ?_, rfl⟩, ?_⟩
      · simp only [Set.mem_setOf_eq]
        rw [Pi.mulSingle_eq_of_ne (fun h => hbJ (by rw [h]; simp)),
          Pi.mulSingle_eq_of_ne (fun h => hbJ (by rw [h]; simp))]
      · rw [omPlusParams_mulSingle, hχg]
        exact diagSpEntry_mulSingle_ne hκ hab (Or.inr (mem_coords_planeOf b))
    · by_cases haJ : planeOf a ∉ ({i, j} : Finset (Fin m))
      · refine ⟨omPlusParams hζ (Pi.mulSingle (planeOf a) (ofAdd (1 : ZMod p))),
          ⟨_, ?_, rfl⟩, ?_⟩
        · simp only [Set.mem_setOf_eq]
          rw [Pi.mulSingle_eq_of_ne (fun h => haJ (by rw [h]; simp)),
            Pi.mulSingle_eq_of_ne (fun h => haJ (by rw [h]; simp))]
        · rw [omPlusParams_mulSingle, hχg]
          exact diagSpEntry_mulSingle_ne hκ hab (Or.inl (mem_coords_planeOf a))
      · have ha_mem : planeOf a ∈ ({i, j} : Finset (Fin m)) := not_not.mp haJ
        have hb_mem : planeOf b ∈ ({i, j} : Finset (Fin m)) := not_not.mp hbJ
        have hζfun : omPlusParams hζ (fun _ : Fin m => ofAdd (1 : ZMod p)) = fun _ => ζ := by
          funext k
          rw [omPlusParams_apply, hχg]
        refine ⟨omPlusParams hζ (fun _ : Fin m => ofAdd (1 : ZMod p)), ⟨_, rfl, rfl⟩, ?_⟩
        rw [hζfun]
        rcases a with x | x <;> rcases b with y | y
        · exact absurd (Or.inl ⟨x, ha_mem, y, hb_mem, rfl, rfl⟩) hside
        · simp only [diagSpEntry_inl, diagSpEntry_inr]
          exact hζne
        · simp only [diagSpEntry_inl, diagSpEntry_inr]
          exact hζne.symm
        · exact absurd (Or.inr ⟨x, ha_mem, y, hb_mem, rfl, rfl⟩) hside
  have hqSiegel : CFSG.Assembly.IsQuasisimple
      (OmegaPilot.siegelBlockGL K ({i, j} : Finset (Fin m))) := by
    have hq : CFSG.IsQuasisimple
        (Matrix.SpecialLinearGroup (Fin ({i, j} : Finset (Fin m)).card) K) := by
      rw [hJc]
      exact CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple
        2 K le_rfl (Or.inr (by omega)) (Or.inr (by omega))
    have he : Matrix.SpecialLinearGroup (Fin ({i, j} : Finset (Fin m)).card) K ≃*
        OmegaPilot.siegelBlockGL K ({i, j} : Finset (Fin m)) :=
      (siegelBlockEquiv (F := K) ({i, j} : Finset (Fin m))).trans
        (Subgroup.equivMapOfInjective _ _ (StatedSp m K).subtype_injective)
    exact CFSG.Assembly.IsQuasisimple.of_mulEquiv he.symm
      ⟨Group.isPerfect_def.mp hq.1, hq.2.1⟩
  cases s
  · rw [omPlusRefl_false (p := p) hij,
      show {f : Fin m → Multiplicative (ZMod p) | SpCoord.permAut (Equiv.swap i j) f = f} =
        {f : Fin m → Multiplicative (ZMod p) | f i = f j} from
        Set.ext fun _ => permAut_swap_eq_self_iff _]
    have hcore : perfectCore (StatedOmega (StatedQuadPlus m K) ⊓
        centralizer (OmegaPilot.diagOmega K m ''
          (omPlusParams hζ '' {f : Fin m → Multiplicative (ZMod p) | f i = f j}))) =
        omPlusBlock K (⟨(i, j), hij⟩, false) := by
      rw [OmegaPilot.perfectCore_statedOmega_inf_centralizer_eq_level hK (J := {i, j})
          hJ2 _ hlevel hsep, ← OmegaPilot.siegelBlockGL_eq_map_omegaLeviSL hK hJ2,
        omPlusBlock_false (K := K) hij]
    have hcent : Subgroup.centralizer ((omPlusTorus (p := p) hζ :
        (Fin m → Multiplicative (ZMod p)) →* StatedOmega (StatedQuadPlus m K)) ''
        {f : Fin m → Multiplicative (ZMod p) | f i = f j}) =
        (StatedOmega (StatedQuadPlus m K) ⊓
          Subgroup.centralizer (OmegaPilot.diagOmega K m ''
            (omPlusParams hζ ''
              {f : Fin m → Multiplicative (ZMod p) | f i = f j}))).subgroupOf
          (StatedOmega (StatedQuadPlus m K)) :=
      centralizer_omPlusTorus_image hζ _
    have hpc : perfectCore (Subgroup.centralizer ((omPlusTorus (p := p) hζ :
        (Fin m → Multiplicative (ZMod p)) →* StatedOmega (StatedQuadPlus m K)) ''
        {f : Fin m → Multiplicative (ZMod p) | f i = f j})) =
        (omPlusBlock K (⟨(i, j), hij⟩, false)).subgroupOf
          (StatedOmega (StatedQuadPlus m K)) := by
      rw [hcent, ← CFSG.ComponentClassification.RankTwoExceptional.Exc.perfectCore_subgroupOf
        (H := StatedOmega (StatedQuadPlus m K) ⊓
          Subgroup.centralizer (OmegaPilot.diagOmega K m ''
            (omPlusParams hζ ''
              {f : Fin m → Multiplicative (ZMod p) | f i = f j})))
        (A := StatedOmega (StatedQuadPlus m K)) inf_le_left, hcore]
    have hle : omPlusBlock K (⟨(i, j), hij⟩, false) ≤ StatedOmega (StatedQuadPlus m K) :=
      omPlusBlock_le hK _
    have hq : CFSG.Assembly.IsQuasisimple ((omPlusBlock K (⟨(i, j), hij⟩, false)).subgroupOf
        (StatedOmega (StatedQuadPlus m K))) :=
      CFSG.Assembly.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle)
        (by rwa [omPlusBlock_false (K := K) hij])
    exact isComponentOf_of_perfectCore_eq hpc hq
  · rw [omPlusRefl_true_fixed hij]
    have hflip : omPlusParams hζ '' (SpCoord.sgnAut j ''
        {g : Fin m → Multiplicative (ZMod p) | g i = g j}) =
        OmegaPilot.flipParam K {j} ''
          (omPlusParams hζ '' {g : Fin m → Multiplicative (ZMod p) | g i = g j}) := by
      ext t
      constructor
      · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
        exact ⟨omPlusParams hζ g, ⟨g, hg, rfl⟩, (omPlusParams_sgnAut hζ j g).symm⟩
      · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
        exact ⟨SpCoord.sgnAut j g, ⟨g, hg, rfl⟩, omPlusParams_sgnAut hζ j g⟩
    have hcore : perfectCore (StatedOmega (StatedQuadPlus m K) ⊓
        centralizer (OmegaPilot.diagOmega K m '' (OmegaPilot.flipParam K {j} ''
          (omPlusParams hζ ''
            {g : Fin m → Multiplicative (ZMod p) | g i = g j})))) =
        omPlusBlock K (⟨(i, j), hij⟩, true) := by
      rw [OmegaPilot.perfectCore_statedOmega_inf_centralizer_eq_signedLevel hK (J := {i, j})
          hJ2 {j} _ hlevel hsep, ← OmegaPilot.siegelBlockGL_eq_map_omegaLeviSL hK hJ2,
        omPlusBlock_true (K := K) hij]
    have hcent : Subgroup.centralizer ((omPlusTorus (p := p) hζ :
        (Fin m → Multiplicative (ZMod p)) →* StatedOmega (StatedQuadPlus m K)) ''
        (SpCoord.sgnAut j '' {g : Fin m → Multiplicative (ZMod p) | g i = g j})) =
        (StatedOmega (StatedQuadPlus m K) ⊓
          Subgroup.centralizer (OmegaPilot.diagOmega K m '' (OmegaPilot.flipParam K {j} ''
            (omPlusParams hζ ''
              {g : Fin m → Multiplicative (ZMod p) | g i = g j})))).subgroupOf
          (StatedOmega (StatedQuadPlus m K)) := by
      rw [centralizer_omPlusTorus_image hζ
        (SpCoord.sgnAut j '' {g : Fin m → Multiplicative (ZMod p) | g i = g j}), hflip]
    have hpc : perfectCore (Subgroup.centralizer ((omPlusTorus (p := p) hζ :
        (Fin m → Multiplicative (ZMod p)) →* StatedOmega (StatedQuadPlus m K)) ''
        (SpCoord.sgnAut j '' {g : Fin m → Multiplicative (ZMod p) | g i = g j}))) =
        (omPlusBlock K (⟨(i, j), hij⟩, true)).subgroupOf
          (StatedOmega (StatedQuadPlus m K)) := by
      rw [hcent, ← CFSG.ComponentClassification.RankTwoExceptional.Exc.perfectCore_subgroupOf
        (H := StatedOmega (StatedQuadPlus m K) ⊓
          Subgroup.centralizer (OmegaPilot.diagOmega K m '' (OmegaPilot.flipParam K {j} ''
            (omPlusParams hζ ''
              {g : Fin m → Multiplicative (ZMod p) | g i = g j}))))
        (A := StatedOmega (StatedQuadPlus m K)) inf_le_left, hcore]
    have hle : omPlusBlock K (⟨(i, j), hij⟩, true) ≤ StatedOmega (StatedQuadPlus m K) :=
      omPlusBlock_le hK _
    have hq : CFSG.Assembly.IsQuasisimple ((omPlusBlock K (⟨(i, j), hij⟩, true)).subgroupOf
        (StatedOmega (StatedQuadPlus m K))) :=
      CFSG.Assembly.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle)
        (by
          rw [omPlusBlock_true (K := K) hij]
          exact CFSG.Assembly.IsQuasisimple.of_mulEquiv
            (Subgroup.equivMapOfInjective (OmegaPilot.siegelBlockGL K ({i, j} : Finset (Fin m)))
              (MulAut.conj (OmegaPilot.flipGL K {j})).toMonoidHom
              (MulAut.conj (OmegaPilot.flipGL K {j})).injective).symm hqSiegel)
    exact isComponentOf_of_perfectCore_eq hpc hq

end Components

section Orders

variable [Finite K]

theorem dvd_card_omPlusBlock (hK : 4 ≤ Nat.card K)
    (hpq : p ∣ Nat.card K - 1) (x : OmPlusIdx m) :
    p ∣ Nat.card ((omPlusBlock K x).subgroupOf (StatedOmega (StatedQuadPlus m K))) := by
  obtain ⟨⟨⟨i, j⟩, hij⟩, s⟩ := x
  have hne : i ≠ j := ne_of_lt hij
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (omPlusBlock_le hK _)).toEquiv]
  have hcard : Nat.card (omPlusBlock K (⟨(i, j), hij⟩, s)) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
    cases s
    · rw [omPlusBlock_false (K := K) hij, OmegaPilot.natCard_siegelBlockGL,
        Finset.card_pair hne]
    · rw [omPlusBlock_true (K := K) hij,
        Subgroup.card_map_of_injective (MulAut.conj (OmegaPilot.flipGL K {j})).injective,
        OmegaPilot.natCard_siegelBlockGL, Finset.card_pair hne]
  rw [hcard, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  have h1 : Nat.card K - 1 ∣ Nat.card K ^ 2 - 1 := by
    have := Nat.sub_dvd_pow_sub_pow (Nat.card K) 1 2
    simpa using this
  exact Dvd.dvd.mul_left (hpq.trans h1) _

end Orders

end CFSG.StandardType

end

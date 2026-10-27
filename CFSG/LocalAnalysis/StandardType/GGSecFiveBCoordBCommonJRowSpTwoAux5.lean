module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRowSpTwoAux1
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJNativeDefs
import CFSG.LocalAnalysis.StandardType.GGTBJSympMinusBlockZ2
import CFSG.LocalAnalysis.StandardType.GGTBJSympMinusLocalize
import CFSG.LocalAnalysis.StandardType.GGTBJSympMinusUnitary
import CFSG.LocalAnalysis.StandardType.GGTPNI1BCComm
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRowSpTwoAux3
import CFSG.RankThree.PartOne.S11d.PSpGood
import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
import CFSG.ClassicalGroups.Symplectic.ComponentCartanRank
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenSymplecticNormalForm

public section

namespace CFSG.StandardType.CommonJSpTwo

open CFSG.Assembly
open CFSG.Open (StatedSp)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.StandardType.SpJoin
open CFSG.StandardType.TorC
open CFSG.RankThree.Classical CFSG.RankThree.PartOne

private lemma sparse_supp_zero {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* Matrix.SpecialLinearGroup (Fin 2) K}
    (hζ : Function.Injective ζ) (hζW : ∀ a, sl2W * ζ a * sl2W⁻¹ = ζ a⁻¹)
    {f : Fin 4 → Multiplicative (ZMod 3)} (hf : f ≠ 1) (hsparse : GGCoordSparse f)
    {J : Subgroup (StatedSp 4 K)}
    (hJ : CFSG.Assembly.IsComponentOf J
      (Subgroup.centralizer ({spPlaneTorus 4 ζ f} : Set (StatedSp 4 K)))) :
    ∀ j ∈ J, ∀ i : Fin 4, f i ≠ 1 → ∀ y : Fin 4,
      blk (((j : StatedSp 4 K) : GL (Fin 4 ⊕ Fin 4) K) :
        Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) y i = if y = i then 1 else 0 := by
  classical
  obtain ⟨i₀, hi₀⟩ := hsparse
  have hfi₀ : f i₀ ≠ 1 := by
    intro h
    apply hf
    funext j
    by_cases hj : j = i₀
    · rw [hj, h, Pi.one_apply]
    · rw [hi₀ j hj, Pi.one_apply]
  have hloc := SympMinus.sympMinus_component_localize (p := 3) (m := 4)
    Nat.prime_three (by norm_num) (by rw [hK]) hζ hζW f hJ
  rcases hloc with h | ⟨c, hc, hcu⟩
  · exact h
  · exfalso
    have hcard_le : (Finset.univ.filter fun i : Fin 4 => f i = c ∨ f i = c⁻¹).card ≤ 1 := by
      have hsub : (Finset.univ.filter fun i : Fin 4 => f i = c ∨ f i = c⁻¹) ⊆ {i₀} := by
        intro i hi
        rw [Finset.mem_filter] at hi
        rw [Finset.mem_singleton]
        by_contra hne
        have hfi : f i = 1 := hi₀ i hne
        rcases hi.2 with h | h
        · exact hc (h.symm.trans hfi)
        · exact hc (inv_eq_one.mp (h.symm.trans hfi))
      calc (Finset.univ.filter fun i : Fin 4 => f i = c ∨ f i = c⁻¹).card
          ≤ ({i₀} : Finset (Fin 4)).card := Finset.card_le_card hsub
        _ = 1 := Finset.card_singleton i₀
    have hcard_ge := (SympMinus.sympMinus_block_unitary (hq := Or.inr hK) (p := 3) (m := 4)
      Nat.prime_three (by norm_num) (by rw [hK]) hζ hζW f hc hJ hcu).1
    omega

private lemma sparse_fixedDim_ge_six {K : Type} [Field K]
    {ζ : Multiplicative (ZMod 3) →* Matrix.SpecialLinearGroup (Fin 2) K}
    {f : Fin 4 → Multiplicative (ZMod 3)} (hf : f ≠ 1) (hsparse : GGCoordSparse f)
    (blocks : CFSG.RankThree.Classical.SpPrimaryBlocks 2 1 3 (spPlaneTorus 4 ζ f)
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 4 K (spPlaneTorus 4 ζ f))) :
    6 ≤ CFSG.RankThree.PartOne.spFixedDim (spPlaneTorus 4 ζ f) := by
  classical
  obtain ⟨i₀, hi₀⟩ := hsparse
  have hfi₀ : f i₀ ≠ 1 := by
    intro h
    apply hf
    funext j
    by_cases hj : j = i₀
    · rw [hj, h, Pi.one_apply]
    · rw [hi₀ j hj, Pi.one_apply]
  have hW : SympMinus.sympMinusZ_W (K := K) f = Submodule.span K
      ({Pi.single (WitSpNs.coord 0 i₀) (1 : K),
        Pi.single (WitSpNs.coord 1 i₀) (1 : K)} : Set (Fin 4 ⊕ Fin 4 → K)) := by
    unfold SympMinus.sympMinusZ_W
    congr 1
    ext v
    constructor
    · rintro ⟨i, hi, a, rfl⟩
      have hii : i = i₀ := by
        by_contra hne
        exact hi (hi₀ i hne)
      subst hii
      fin_cases a
      · simp
      · simp
    · intro hv
      rcases hv with hv | hv
      · exact ⟨i₀, hfi₀, 0, hv⟩
      · exact ⟨i₀, hfi₀, 1, hv⟩
  have hWle : Module.finrank K (SympMinus.sympMinusZ_W (K := K) f) ≤ 2 := by
    rw [hW]
    have hne : (Pi.single (WitSpNs.coord 0 i₀) (1 : K) : Fin 4 ⊕ Fin 4 → K) ≠
        (Pi.single (WitSpNs.coord 1 i₀) (1 : K) : Fin 4 ⊕ Fin 4 → K) := by
      intro h
      have h1 := congrFun h (WitSpNs.coord 0 i₀)
      simp [WitSpNs.coord] at h1
    have hcard : ({(Pi.single (WitSpNs.coord 0 i₀) (1 : K) : Fin 4 ⊕ Fin 4 → K),
        (Pi.single (WitSpNs.coord 1 i₀) (1 : K) : Fin 4 ⊕ Fin 4 → K)} :
        Set (Fin 4 ⊕ Fin 4 → K)).toFinset.card = 2 := by
      rw [Set.toFinset_insert, Set.toFinset_singleton, Finset.card_insert_of_notMem]
      · simp
      · simpa [WitSpNs.coord] using hne
    have h := finrank_span_le_card (R := K) (M := (Fin 4 ⊕ Fin 4 → K))
      ({(Pi.single (WitSpNs.coord 0 i₀) (1 : K) : Fin 4 ⊕ Fin 4 → K),
        (Pi.single (WitSpNs.coord 1 i₀) (1 : K) : Fin 4 ⊕ Fin 4 → K)} :
        Set (Fin 4 ⊕ Fin 4 → K))
    rw [hcard] at h
    simpa only [Set.finrank] using h
  have hrange_le : Module.finrank K (LinearMap.range (spEnd (spPlaneTorus 4 ζ f) - 1)) ≤ 2 :=
    (Submodule.finrank_mono (SympMinus.sympMinusZ_range_sub_one_le_W ζ f)).trans hWle
  have hsum : Module.finrank K (LinearMap.range (spEnd (spPlaneTorus 4 ζ f) - 1)) +
      Module.finrank K (LinearMap.ker (spEnd (spPlaneTorus 4 ζ f) - 1)) = 8 := by
    have h := LinearMap.finrank_range_add_finrank_ker (spEnd (spPlaneTorus 4 ζ f) - 1)
    simpa [Module.finrank_fintype_fun_eq_card, Fintype.card_sum] using h
  have hker : Module.finrank K (LinearMap.ker (spEnd (spPlaneTorus 4 ζ f) - 1)) =
      CFSG.RankThree.PartOne.spFixedDim (spPlaneTorus 4 ζ f) := by
    rw [CFSG.RankThree.PartOne.spFixedDim, blocks.fixed_eq]
  omega

theorem ggCommonJSpTwo_sparse {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* Matrix.SpecialLinearGroup (Fin 2) K}
    (hζ : Function.Injective ζ) (hζW : ∀ a, sl2W * ζ a * sl2W⁻¹ = ζ a⁻¹)
    {f : Fin 4 → Multiplicative (ZMod 3)} (hf : f ≠ 1) (hsparse : GGCoordSparse f) :
    ∃ K' : Subgroup (StatedSp 4 K),
      CFSG.Assembly.IsComponentOf K'
          (Subgroup.centralizer ({spPlaneTorus 4 ζ f} : Set (StatedSp 4 K))) ∧
        (∀ K'' : Subgroup (StatedSp 4 K),
          CFSG.Assembly.IsComponentOf K''
            (Subgroup.centralizer ({spPlaneTorus 4 ζ f} : Set (StatedSp 4 K))) → K'' = K') ∧
        (spPlaneTorus 4 ζ).range ⊓ Subgroup.centralizer (K' : Set (StatedSp 4 K)) =
          Subgroup.zpowers (spPlaneTorus 4 ζ f) ∧
        7 ∣ Nat.card K' := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1) (by simpa using hK)
  haveI : NeZero (4 : ℕ) := ⟨by norm_num⟩
  have hsparse_keep : GGCoordSparse f := hsparse
  obtain ⟨i₀, hi₀⟩ := hsparse
  have hfi₀ : f i₀ ≠ 1 := by
    intro h
    apply hf
    funext j
    by_cases hj : j = i₀
    · rw [hj, h, Pi.one_apply]
    · rw [hi₀ j hj, Pi.one_apply]
  have hS0eq : (Finset.univ.filter fun i : Fin 4 => f i = 1) = Finset.univ.erase i₀ := by
    ext j
    rw [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨-, hj⟩
      exact ⟨fun hji => hfi₀ (hji ▸ hj), Finset.mem_univ j⟩
    · rintro ⟨hji, -⟩
      exact ⟨Finset.mem_univ j, hi₀ j hji⟩
  have hS0card : (Finset.univ.filter fun i : Fin 4 => f i = 1).card = 3 := by
    rw [hS0eq, Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ,
      Fintype.card_fin]
  have hS0ne : (Finset.univ.filter fun i : Fin 4 => f i = 1).Nonempty :=
    Finset.card_pos.mp (by rw [hS0card]; norm_num)
  obtain ⟨fexp, hfexp1, hKexp, blocks⟩ :=
    SympMinus.sympMinusZ_blocks (p := 3) (m := 4) Nat.prime_three (by norm_num) ζ hζ f hf
  have hfexp : fexp = 1 := by
    have h : 2 ^ fexp = 2 ^ 1 := by rw [← hKexp, hK, pow_one]
    exact Nat.pow_right_injective (by norm_num) h
  subst hfexp
  have hdim : 6 ≤ CFSG.RankThree.PartOne.spFixedDim (spPlaneTorus 4 ζ f) := by
    change 6 ≤ CFSG.RankThree.PartOne.spFixedDim (spPlaneTorus 4 ζ f)
    exact sparse_fixedDim_ge_six (ζ := ζ) (f := f) hf hsparse_keep blocks
  obtain ⟨hFq, hFc⟩ :=
    SympMinus.sympMinusZ_fixedFactor_isComponent (p := 3) (m := 4) Nat.prime_three
      (by norm_num) ζ f (Or.inr ⟨hK, hdim⟩) (f := 1) (by norm_num) hKexp hf blocks hS0ne
  have huniq : ∀ J : Subgroup (StatedSp 4 K),
      CFSG.Assembly.IsComponentOf J
        (Subgroup.centralizer ({spPlaneTorus 4 ζ f} : Set (StatedSp 4 K))) →
        J = spFixedFactor (spPlaneTorus 4 ζ f) := by
    intro J hJ
    have hsupp := sparse_supp_zero (ζ := ζ) (f := f) hK hζ hζW hf hsparse_keep hJ
    have hle : J ≤ spFixedFactor (spPlaneTorus 4 ζ f) :=
      SympMinus.sympMinusZ_le_spFixedFactor ζ f hJ hsupp
    have hFq' : CFSG.Assembly.IsQuasisimple
        ↥(spFixedFactor (spPlaneTorus 4 ζ f)) :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native
        (↥(spFixedFactor (spPlaneTorus 4 ζ f)))).2 hFq
    exact SympMinus.sympMinusZ_eq_fixedFactor ζ f hle hJ hFq' hFc
  have hsuppF := sparse_supp_zero (ζ := ζ) (f := f) hK hζ hζW hf hsparse_keep hFc
  have hAut : FrameBs.sectionFrameAut (spPlaneTorus 4 ζ)
      (spFixedFactor (spPlaneTorus 4 ζ f)) =
      TypeBDatum.signedSupportedAut 4 3 (Finset.univ.filter fun i : Fin 4 => f i = 1) := by
    refine le_antisymm ?_ ?_
    · exact SympMinus.sympMinusZ_sectionFrameAut_le (p := 3) (m := 4) Nat.prime_three
        (by norm_num) ζ hζ f hsuppF
    · exact SympMinus.sympMinusZ_signedSupportedAut_le_sectionFrameAut ζ hζW f _ rfl
  have hlabel := ggCommonJSpTwo_label_sparse (K := K) hK (r := 4) (by norm_num) (ζ := ζ)
    hζ hζW hFc hsparse_keep (S := Finset.univ.filter fun i : Fin 4 => f i = 1) hS0card hAut
  have hlabF : GGHasLabel (⟨.C, 3, 1⟩ : LargeEvenLabel)
      (↥(spFixedFactor (spPlaneTorus 4 ζ f)) ⧸
        Subgroup.center ↥(spFixedFactor (spPlaneTorus 4 ζ f))) := by
    rcases hlabel with ⟨-, -, hlab⟩ | ⟨h3, -, hlab⟩
    · simpa using hlab
    · omega
  have hK1 : Nat.card K = 2 ^ 1 := by rw [hK]; norm_num
  have hx3 : spPlaneTorus 4 ζ f ^ 3 = 1 :=
    SympMinus.sympMinusZ_spPlaneTorus_pow ζ f
  have hx1 : spPlaneTorus 4 ζ f ≠ 1 :=
    SympMinus.sympMinusZ_spPlaneTorus_ne_one ζ hζ f hf
  have hxord : orderOf (spPlaneTorus 4 ζ f) = 3 := orderOf_eq_prime hx3 hx1
  have hprojinj : Function.Injective
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 4 K) :=
    (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo
      (r := 4) (K := K)).1
  have hxo : orderOf (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 4 K
      (spPlaneTorus 4 ζ f)) = 3 := by
    rw [orderOf_injective _ hprojinj, hxord]
  have hker : LinearMap.ker (spEnd (spPlaneTorus 4 ζ f) - 1) ≠ ⊥ := by
    intro hbot
    have h0 : CFSG.RankThree.PartOne.spFixedDim (spPlaneTorus 4 ζ f) = 0 := by
      rw [CFSG.RankThree.PartOne.spFixedDim, blocks.fixed_eq, hbot]
      simp
    omega
  obtain ⟨s, hs1, ⟨eF⟩⟩ :=
    CFSG.RankThree.PartOne.sp_fixedFactor_equiv (p := 3) (f := 1) (r := 4)
      Nat.prime_three (by norm_num) hK1 (by norm_num) (by norm_num)
      (a := spPlaneTorus 4 ζ f) hxord hxo hker
  have hcenterSp : Subgroup.center ↥(StatedSp s K) = ⊥ :=
    CFSG.ClassicalGroups.Symplectic.center_statedSp_eq_bot_of_charP_two hs1
  have hcenterF : Subgroup.center ↥(spFixedFactor (spPlaneTorus 4 ζ f)) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : eF z ∈ Subgroup.center ↥(StatedSp s K) := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro w
      obtain ⟨w', rfl⟩ := eF.surjective w
      rw [← map_mul, ← map_mul, hz w']
    rw [hcenterSp, Subgroup.mem_bot] at hz'
    rw [Subgroup.mem_bot]
    exact eF.injective (by rw [hz', map_one])
  have hquotCard : Nat.card (↥(spFixedFactor (spPlaneTorus 4 ζ f)) ⧸
      Subgroup.center ↥(spFixedFactor (spPlaneTorus 4 ζ f))) =
      Nat.card ↥(spFixedFactor (spPlaneTorus 4 ζ f)) := by
    have e : (↥(spFixedFactor (spPlaneTorus 4 ζ f)) ⧸
        Subgroup.center ↥(spFixedFactor (spPlaneTorus 4 ζ f))) ≃*
        ↥(spFixedFactor (spPlaneTorus 4 ζ f)) :=
      (QuotientGroup.quotientMulEquivOfEq hcenterF).trans
        (QuotientGroup.quotientBot (G := ↥(spFixedFactor (spPlaneTorus 4 ζ f))))
    exact Nat.card_congr e.toEquiv
  have hcardQuot : Nat.card (↥(spFixedFactor (spPlaneTorus 4 ζ f)) ⧸
      Subgroup.center ↥(spFixedFactor (spPlaneTorus 4 ζ f))) =
      Nat.card (StatedSp 3 K) :=
    tpbcB_card_of_hasLabel_C (m := 3) (n := 1) (K := K) (by norm_num) hK1 hlabF
  have h7Sp : 7 ∣ Nat.card (StatedSp 3 K) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hK1,
      show Finset.Icc 1 3 = ({1, 2, 3} : Finset ℕ) by decide]
    norm_num
  have h7F : 7 ∣ Nat.card ↥(spFixedFactor (spPlaneTorus 4 ζ f)) := by
    rw [← hquotCard, hcardQuot]
    exact h7Sp
  have hrange_el : IsElemAbelian 3 (spPlaneTorus 4 ζ).range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
    · obtain ⟨a', ha'⟩ := a.2
      obtain ⟨b', hb'⟩ := b.2
      apply Subtype.ext
      change (a : StatedSp 4 K) * b = b * a
      rw [← ha', ← hb', ← map_mul, ← map_mul, mul_comm]
    · obtain ⟨a', ha'⟩ := ha
      have h3 : a' ^ 3 = 1 := by
        funext i
        rw [Pi.pow_apply, Pi.one_apply]
        apply Multiplicative.toAdd.injective
        rw [toAdd_pow, toAdd_one]
        show (3 : ℕ) • Multiplicative.toAdd (a' i) = 0
        rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
      exact Subtype.ext (by rw [ha'.symm, ← map_pow, h3, map_one])
  let E : Subgroup (StatedSp 4 K) :=
    (spPlaneTorus 4 ζ).range ⊓
      Subgroup.centralizer ((spFixedFactor (spPlaneTorus 4 ζ f)) : Set (StatedSp 4 K))
  have hE_el : IsElemAbelian 3 E := hrange_el.mono inf_le_left
  have hxF : spPlaneTorus 4 ζ f ∈
      Subgroup.centralizer ((spFixedFactor (spPlaneTorus 4 ζ f)) : Set (StatedSp 4 K)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (spFixedFactor_le_centralizer (spPlaneTorus 4 ζ f) hj)
  have hxE : spPlaneTorus 4 ζ f ∈ E := Subgroup.mem_inf.mpr ⟨⟨f, rfl⟩, hxF⟩
  have hcommE : ∀ e ∈ E, ∀ j ∈ spFixedFactor (spPlaneTorus 4 ζ f), e * j = j * e := by
    intro e he j hj
    exact (Subgroup.mem_centralizer_iff.mp he.2 j hj).symm
  have hEeq : E ≤ Subgroup.zpowers (spPlaneTorus 4 ζ f) :=
    tpbcc_le_zpowers_of_fixed (p := 3) (m := 3) (n := 1) Nat.prime_three (by norm_num)
      (by norm_num) (by norm_num) (inferInstance) hK1
      (x := spPlaneTorus 4 ζ f) (J := spFixedFactor (spPlaneTorus 4 ζ f)) (E := E)
      blocks hprojinj hx3 hxord hxE hE_el hFc le_rfl hlabF hcommE
  have hzE : Subgroup.zpowers (spPlaneTorus 4 ζ f) ≤ E :=
    Subgroup.zpowers_le.mpr hxE
  have hE_eq : E = Subgroup.zpowers (spPlaneTorus 4 ζ f) := le_antisymm hEeq hzE
  exact ⟨spFixedFactor (spPlaneTorus 4 ζ f), hFc, fun K'' hK'' => huniq K'' hK'',
    hE_eq, h7F⟩

end CFSG.StandardType.CommonJSpTwo

end

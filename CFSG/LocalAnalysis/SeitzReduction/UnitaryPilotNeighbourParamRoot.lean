module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotNeighbourParamNormal
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotHR8FieldNormal
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotBLiftSetting
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourParamLift
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourNormalCore
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotHR8Field

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup Matrix CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore HasBLift)
open CFSG.EvenSmallLie.Child3.SelL39 (projectiveSLCongr)

section FieldRow

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {n : ℕ}

theorem mulAut_congr_trans {A B C : Type*} [Group A] [Group B] [Group C] (e₁ : A ≃* B)
    (e₂ : B ≃* C) (τ : MulAut A) :
    MulAut.congr (e₁.trans e₂) τ = MulAut.congr e₂ (MulAut.congr e₁ τ) := by
  ext x
  rfl

theorem nonempty_graphFieldNeighbourParam_of_fieldRow (e : L ≃* unitaryPSU h n) (hn : 6 ≤ n)
    (hnf : (n, f) ≠ (6, 1)) {t : G} (htL : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {a b : Fin n} (hab : a ≠ b)
    (htX : t ∈ centralizer (modelToG e (unitaryRootTorus h hab) : Set G))
    (hcomp : CFSG.Open.IsComponentOf
      (((modelToG e (blockSU h ({a, b}ᶜ : Finset (Fin n)))).subgroupOf
        (centralizer (modelToG e (unitaryRootTorus h hab) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e (unitaryRootTorus h hab) : Set G)))))
      (centralizer ({(QuotientGroup.mk' (oddCore (centralizer
        (modelToG e (unitaryRootTorus h hab) : Set G)))) ⟨t, htX⟩} :
          Set (centralizer (modelToG e (unitaryRootTorus h hab) : Set G) ⧸
            oddCore (centralizer (modelToG e (unitaryRootTorus h hab) : Set G))))))
    (hsyl : ∀ U : Subgroup (centralizer (modelToG e (unitaryRootTorus h hab) : Set G) ⧸
        oddCore (centralizer (modelToG e (unitaryRootTorus h hab) : Set G))), IsPGroup 2 U →
      U ≤ centralizer ((((modelToG e (blockSU h ({a, b}ᶜ : Finset (Fin n)))).subgroupOf
        (centralizer (modelToG e (unitaryRootTorus h hab) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e (unitaryRootTorus h hab) :
            Set G))))) : Set (centralizer (modelToG e (unitaryRootTorus h hab) : Set G) ⧸
              oddCore (centralizer (modelToG e (unitaryRootTorus h hab) : Set G)))) →
        Nat.card U ≤ 2)
    (hZ : center (((modelToG e (blockSU h ({a, b}ᶜ : Finset (Fin n)))).subgroupOf
        (centralizer (modelToG e (unitaryRootTorus h hab) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e (unitaryRootTorus h hab) :
            Set G))))) = ⊥)
    {Kc : Subgroup (centralizer (modelToG e (unitaryRootTorus h hab) : Set G) ⧸
      oddCore (centralizer (modelToG e (unitaryRootTorus h hab) : Set G)))}
    (hKcomp : IsComponent Kc)
    (hDK : ((modelToG e (blockSU h ({a, b}ᶜ : Finset (Fin n)))).subgroupOf
        (centralizer (modelToG e (unitaryRootTorus h hab) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e (unitaryRootTorus h hab) :
            Set G)))) ≤ Kc)
    (hsN : QuotientGroup.mk' (oddCore (centralizer (modelToG e (unitaryRootTorus h hab) : Set G)))
      ⟨t, htX⟩ ∈ normalizer (Kc : Set (centralizer (modelToG e (unitaryRootTorus h hab) : Set G) ⧸
        oddCore (centralizer (modelToG e (unitaryRootTorus h hab) : Set G)))))
    (hτ : Kc.normalizerMonoidHom ⟨_, hsN⟩ ∉ (MulAut.conj : Kc →* MulAut Kc).range)
    {K' : Type} [Field K'] [Finite K'] (hK' : Nat.card K' = 2 ^ (2 * f))
    (eK : Kc ≃* LinearFlag.projectiveSL (n - 2) K') {φ : K' ≃+* K'} (hφ : ∀ x, φ x = x ^ 2 ^ f)
    (heK : MulAut.congr eK (Kc.normalizerMonoidHom ⟨_, hsN⟩) =
      LinearFlag.fieldAut (n - 2) K' φ * LinearFlag.dualAut (n - 2) K')
    (hB : HasBLift Kc) :
    Nonempty (GraphFieldNeighbourParam e t (modelToG e (unitaryRootTorus h hab))
      ({a, b}ᶜ : Finset (Fin n))) := by
  have := h.finite
  have := h.charP
  have hf := h.one_le
  set Db := ((modelToG e (blockSU h ({a, b}ᶜ : Finset (Fin n)))).subgroupOf
    (centralizer (modelToG e (unitaryRootTorus h hab) : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (modelToG e (unitaryRootTorus h hab) : Set G))))
    with hDbdef
  set s := QuotientGroup.mk' (oddCore (centralizer (modelToG e (unitaryRootTorus h hab) : Set G)))
    ⟨t, htX⟩ with hsdef
  have hcard : (({a, b} : Finset (Fin n))ᶜ).card = n - 2 := card_compl_pair hab
  let eN : ({a, b}ᶜ : Finset (Fin n)) ≃ Fin (n - 2) :=
    (({a, b} : Finset (Fin n))ᶜ).equivFinOfCardEq hcard
  have : Fintype K' := Fintype.ofFinite K'
  have : Fintype K := Fintype.ofFinite K
  have hcardKK : Fintype.card K' = Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK', h.card]
  set r : K' ≃+* K := FiniteField.ringEquivOfCardEq hcardKK with hr
  set ψ₀ : Kc ≃* LinearFlag.projectiveSL (n - 2) K := eK.trans (projectiveSLCongr r) with hψ₀def
  have hψ₀ : MulAut.congr ψ₀ (Kc.normalizerMonoidHom ⟨s, hsN⟩) = graphFieldAut h (n - 2) := by
    rw [hψ₀def, mulAut_congr_trans, heK, congr_projectiveSLCongr_eq_graphFieldAut h r hφ]
  have hne : Db ≠ ⊥ := ne_bot_of_isQuasisimple hcomp.2.2
  obtain ⟨ε, hεinj, hεrange, hεapp⟩ := exists_unitaryPSU_embedding e hab eN (by omega) hne hZ hDK
  have hDs : Db ≤ centralizer ({s} : Set _) := hcomp.1
  have hεθ : ε.range ≤ fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩) := by
    rw [hεrange, F4Pilot.fixedSubgroup_normalizerMonoidHom]
    intro x hx
    exact mem_subgroupOf.mpr (hDs (mem_subgroupOf.mp hx))
  obtain ⟨ψ, hψε, hψτ⟩ := exists_mulEquiv_toPSL_eq h (by omega) (fun h' => by omega) ψ₀ hψ₀ ε
    hεinj hεθ
  have hs : orderOf s = 2 := orderOf_mk_oddCore (by rw [orderOf_mk]; exact ht)
  have hsD : s ∈ centralizer (Db : Set _) :=
    mem_centralizer_iff.mpr fun d hd => mem_centralizer_singleton_iff.mp (hDs hd)
  have hsC : s ∉ centralizer (Kc : Set _) := by
    intro hc
    apply hτ
    have h1 : (⟨s, hsN⟩ : normalizer (Kc : Set _)) ∈ Kc.normalizerMonoidHom.ker := by
      rw [Subgroup.normalizerMonoidHom_ker]
      exact hc
    exact ⟨1, by rw [map_one, MonoidHom.mem_ker.mp h1]⟩
  have hOut := LinearPilot.isSolvable_outer_of_mulEquiv (by omega) ψ₀
  have hcore := LinearPilot.perfectCore_top_eq_of_isComponent
    (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot _) hKcomp hDK hs hsD hsN hsC hsyl hOut
  obtain ⟨q, hq, hqker, hqapp⟩ :=
    LinearPilot.exists_surjective_centralizerPerfectCore_of_perfectCore_eq hcore hB
  have hsplit : 5 ≤ Nat.card K ∨ 5 ≤ n - 2 := by
    rcases Nat.lt_or_ge f 2 with hf1 | hf2
    · right
      have hf1' : f = 1 := by omega
      subst hf1'
      have : n ≠ 6 := fun hn6 => hnf (by rw [hn6])
      omega
    · left
      rw [h.card]
      calc 5 ≤ 2 ^ (2 * 2) := by norm_num
        _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have ht' : t ∈ normalizer (centralizerPerfectCore (modelToG e (unitaryRootTorus h hab)) :
      Set G) := le_normalizer_neighbourCore e htL hab
  refine nonempty_graphFieldNeighbourParam_of_proj e t eN (by omega) hsplit
    (ψ.toMonoidHom.comp q) (ψ.surjective.comp hq) ?_
    (modelToG_blockSU_compl_le_neighbourCore e hn hab) ?_ ht' ?_
    (fun c => symm_mem_normalizer_neighbourCore e hab
      (unitaryProj_torusDiagSU_mem_normalizer_unitaryRootTorus hab c))
  ·
    intro y hy
    apply hqker
    have h1 : ψ (q y) = ψ 1 := by
      rw [map_one]
      exact hy
    exact ψ.injective h1
  ·
    intro x
    have hqx : q ⟨((e.symm (unitaryProj h n (unitaryBlockSLHom h eN x)) : L) : G),
        modelToG_blockSU_compl_le_neighbourCore e hn hab (symm_mem_modelToG e
          (unitaryProj_mem_blockSU h (unitaryBlockSLHom_mem h eN x)))⟩ =
        ε (unitaryProj h (n - 2) x) := by
      apply Subtype.ext
      rw [hqapp, hεapp]
      rfl
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hqx, hψε, toPSL_unitaryProj]
  ·
    intro y
    have hqt : q ((centralizerPerfectCore (modelToG e (unitaryRootTorus h hab))).normalizerMonoidHom
        ⟨t, ht'⟩ y) = Kc.normalizerMonoidHom ⟨s, hsN⟩ (q y) := by
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hqapp, hqapp]
      have e1 : (⟨(((centralizerPerfectCore (modelToG e (unitaryRootTorus h hab))).normalizerMonoidHom
          ⟨t, ht'⟩ y : centralizerPerfectCore (modelToG e (unitaryRootTorus h hab))) : G),
            F4Pilot.centralizerPerfectCore_le_centralizer _
              ((centralizerPerfectCore (modelToG e (unitaryRootTorus h hab))).normalizerMonoidHom
                ⟨t, ht'⟩ y).2⟩ :
              centralizer (modelToG e (unitaryRootTorus h hab) : Set G)) =
          ⟨t, htX⟩ * ⟨(y : G), F4Pilot.centralizerPerfectCore_le_centralizer _ y.2⟩ *
            ⟨t, htX⟩⁻¹ := by
        apply Subtype.ext
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
        rfl
      rw [e1, map_mul, map_mul, map_inv]
    exact (congrArg ψ hqt).trans (hψτ (q y))

end FieldRow

section Seitz


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {K : Type} [Field K]
  (h : UnitaryFieldData 2 f K) {n : ℕ}

theorem nonempty_graphFieldNeighbourParam_unitaryRootTorus (hset : SeitzSetting G L)
    (hcat : SUmCatalogueClausesAt (n - 2)) (e : L ≃* unitaryPSU h n) (hn : 6 ≤ n)
    (hnf : (n, f) ≠ (6, 1)) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {a b : Fin n} (hab : a ≠ b)
    (htX : t ∈ centralizer (modelToG e (unitaryRootTorus h hab) : Set G))
    (Kc : Subgroup (centralizer (modelToG e (unitaryRootTorus h hab) : Set G) ⧸
      oddCore (centralizer (modelToG e (unitaryRootTorus h hab) : Set G))))
    (hKc : IsComponent Kc)
    (hDK : ⁅((modelToG e (blockSU h ({a, b}ᶜ : Finset (Fin n)))).subgroupOf
      (centralizer (modelToG e (unitaryRootTorus h hab) : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (modelToG e (unitaryRootTorus h hab) : Set G)))),
          Kc⁆ ≠ ⊥)
    (hKt : Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer
      (modelToG e (unitaryRootTorus h hab) : Set G))) ⟨t, htX⟩)).toMonoidHom = Kc) :
    Nonempty (GraphFieldNeighbourParam e t (modelToG e (unitaryRootTorus h hab))
      ({a, b}ᶜ : Finset (Fin n))) := by
  obtain ⟨-, hall, hZ⟩ := forall_neighbour_unitaryRootTorus_field h hset hcat e hn hnf htC ht hab
    (X := modelToG e (unitaryRootTorus h hab)) rfl htX
    (D := modelToG e (blockSU h ({a, b}ᶜ : Finset (Fin n)))) rfl
  obtain ⟨-, ⟨-, hDlt, -, hsN, hout, -, -, -⟩ | ⟨hKt', -⟩⟩ := hall Kc hKc hDK
  · obtain ⟨hsN', K', _, _, hK', eK, φ, hφ, heK⟩ := graphField_neighbour_unitaryRootTorus h hset
      hcat e hn hnf htC ht hab (X := modelToG e (unitaryRootTorus h hab)) rfl htX
      (D := modelToG e (blockSU h ({a, b}ᶜ : Finset (Fin n)))) rfl Kc hKc hDK hKt
    obtain ⟨hcomp, hsyl, -⟩ := neighbour_standard_unitaryRootTorus_of_seitzSetting h hset e hn htC
      ht hab (X := modelToG e (unitaryRootTorus h hab)) rfl htX
      (D := modelToG e (blockSU h ({a, b}ᶜ : Finset (Fin n)))) rfl
    obtain ⟨-, -, hB⟩ := bLift_unitaryRootTorus_of_seitzSetting h hset e hn htC ht hab
      (X := modelToG e (unitaryRootTorus h hab)) rfl
      (D := modelToG e (blockSU h ({a, b}ᶜ : Finset (Fin n)))) rfl
    have hDK' : ⁅Kc, ((modelToG e (blockSU h ({a, b}ᶜ : Finset (Fin n)))).subgroupOf
        (centralizer (modelToG e (unitaryRootTorus h hab) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e (unitaryRootTorus h hab) :
            Set G))))⁆ ≠ ⊥ := by
      rwa [commutator_comm]
    exact nonempty_graphFieldNeighbourParam_of_fieldRow e hn hnf htC ht hab htX hcomp hsyl hZ hKc
      hDlt.le hsN' hout hK' eK hφ heK (hB Kc Kc hKc hKc hDK' hDK').1
  · exact absurd hKt hKt'

theorem nonempty_graphFieldNeighbourParam_or_swap_unitaryRootTorus (hset : SeitzSetting G L)
    (hcat : SUmCatalogueClausesAt (n - 2)) (e : L ≃* unitaryPSU h n) (hn : 6 ≤ n)
    (hnf : (n, f) ≠ (6, 1)) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {a b : Fin n} (hab : a ≠ b)
    (htX : t ∈ centralizer (modelToG e (unitaryRootTorus h hab) : Set G)) :
    Nonempty (GraphFieldNeighbourParam e t (modelToG e (unitaryRootTorus h hab))
        ({a, b}ᶜ : Finset (Fin n))) ∨
      ∃ Kc : Subgroup (centralizer (modelToG e (unitaryRootTorus h hab) : Set G) ⧸
          oddCore (centralizer (modelToG e (unitaryRootTorus h hab) : Set G))),
        IsComponent Kc ∧
        ((modelToG e (blockSU h ({a, b}ᶜ : Finset (Fin n)))).subgroupOf
          (centralizer (modelToG e (unitaryRootTorus h hab) : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (modelToG e (unitaryRootTorus h hab) :
              Set G)))) ≤
          Kc ⊔ Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer
            (modelToG e (unitaryRootTorus h hab) : Set G))) ⟨t, htX⟩)).toMonoidHom ∧
        Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer
          (modelToG e (unitaryRootTorus h hab) : Set G))) ⟨t, htX⟩)).toMonoidHom ≠ Kc ∧
        ⁅Kc, Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer
          (modelToG e (unitaryRootTorus h hab) : Set G))) ⟨t, htX⟩)).toMonoidHom⁆ = ⊥ ∧
        center Kc = ⊥ ∧
        Nonempty (Kc ≃* ((modelToG e (blockSU h ({a, b}ᶜ : Finset (Fin n)))).subgroupOf
          (centralizer (modelToG e (unitaryRootTorus h hab) : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (modelToG e (unitaryRootTorus h hab) :
              Set G))))) := by
  obtain ⟨⟨Kc, hKc, hDKK, hK⟩, -, -⟩ := forall_neighbour_unitaryRootTorus_field h hset hcat e hn
    hnf htC ht hab (X := modelToG e (unitaryRootTorus h hab)) rfl htX
    (D := modelToG e (blockSU h ({a, b}ᶜ : Finset (Fin n)))) rfl
  rcases hK with ⟨hKt, hDlt, -⟩ | ⟨hKt', hcomm, hZK, hiso⟩
  · left
    obtain ⟨hcomp, -, -⟩ := neighbour_standard_unitaryRootTorus_of_seitzSetting h hset e hn htC
      ht hab (X := modelToG e (unitaryRootTorus h hab)) rfl htX
      (D := modelToG e (blockSU h ({a, b}ᶜ : Finset (Fin n)))) rfl
    refine nonempty_graphFieldNeighbourParam_unitaryRootTorus h hset hcat e hn hnf htC ht hab htX
      Kc hKc ?_ hKt
    intro hbot
    have hperf := Subgroup.isPerfect_iff.1 (⟨hcomp.2.2.1⟩ : Group.IsPerfect _)
    have hle := commutator_mono (le_refl ((((modelToG e (blockSU h ({a, b}ᶜ :
      Finset (Fin n)))).subgroupOf (centralizer (modelToG e (unitaryRootTorus h hab) :
        Set G))).map (QuotientGroup.mk' (oddCore (centralizer (modelToG e
          (unitaryRootTorus h hab) : Set G))))))) hDlt.le
    rw [hperf, hbot] at hle
    exact ne_bot_of_isQuasisimple hcomp.2.2 (le_bot_iff.mp hle)
  · exact Or.inr ⟨Kc, hKc, hDKK, hKt', hcomm, hZK, hiso⟩

end Seitz

end CFSG.SeitzReduction.UnitaryPilot

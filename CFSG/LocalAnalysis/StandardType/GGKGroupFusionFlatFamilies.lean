module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionFlatBasic
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionAltDefining
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionAltFamily
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitz

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Alt

open Equiv Equiv.Perm
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem ggKGroupFusionAtFlat_alternating_of (hNM : GGAltNotMarkedInput) :
    GGKGroupFusionAtFlat GGKFAlternating := by
  rintro W _ _ p H E i ⟨n, hn, rfl⟩ hyp - hKH ⟨e⟩
  obtain ⟨⟨hp, hp2, hE, hEcard, hfus⟩, ⟨hsimple, hnab, -⟩, hIIIa, -⟩ := hyp
  have : Fact p.Prime := ⟨hp⟩
  have hKn : (CFSG.generalizedFitting W).Normal :=
    CFSG.LocalCores.generalized_fitting_characteristic.2
  have hout : ¬ p ∣ Nat.card (Outer ↥(CFSG.generalizedFitting W)) := by
    rw [ggCard_outer_congr e]
    exact ggNot_dvd_outer_alternating hp hp2 hn
  have hEK : E ≤ CFSG.generalizedFitting W := fun x hx =>
    ggMem_generalizedFitting_of_pow hp hsimple hnab hout (hE.2 x hx)
  have hEH : E ≤ H := hfus.1
  have hMtop : ¬ alternatingGroup (Fin n) ≤ ggAltImage e H := by
    intro hle
    apply hKH
    intro k hk
    have h1 := hle (e ⟨k, hk⟩).2
    exact (ggMem_altImage e).mp h1
  have hEM : ggAltImage e E ≤ ggAltImage e H :=
    Subgroup.map_mono (Subgroup.map_mono (Subgroup.comap_mono hEH))
  have hEab' : ∀ x ∈ ggAltImage e E, ∀ y ∈ ggAltImage e E, x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, hk, rfl⟩ := (ggMem_altImage_iff e).mp hx
    obtain ⟨k', hk', rfl⟩ := (ggMem_altImage_iff e).mp hy
    have hc0 := hE.1.is_comm.comm (⟨k, hk⟩ : ↥E) ⟨k', hk'⟩
    have hc : k * k' = k' * k := Subtype.ext (by simpa using congrArg Subtype.val hc0)
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hc]
  have hEp' : ∀ x ∈ ggAltImage e E, x ^ p = 1 := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := (ggMem_altImage_iff e).mp hx
    have hkp : k ^ p = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hE.2 _ hk)
    rw [← Subgroup.coe_pow, ← map_pow, hkp, map_one, Subgroup.coe_one]
  have hEcard' : Nat.card (ggAltImage e E) = p ^ 2 := by
    rw [← hEcard]
    exact (Nat.card_congr (ggAltImageEquiv e hEK).toEquiv).symm
  have hctl : ∀ g ∈ alternatingGroup (Fin n), ∀ x ∈ ggAltImage e E, x ≠ 1 →
      g⁻¹ * x * g ∈ ggAltImage e H → g ∈ ggAltImage e H := by
    intro g hg x hx hx1 hgx
    obtain ⟨y, hyE, rfl⟩ := (ggMem_altImage_iff e).mp hx
    set k := e.symm ⟨g, hg⟩ with hkdef
    have hgk : ((e k : ↥(alternatingGroup (Fin n))) : Perm (Fin n)) = g := by simp [hkdef]
    have hy1 : (y : W) ≠ 1 := by
      intro h
      apply hx1
      have : y = 1 := Subtype.ext h
      rw [this, map_one, Subgroup.coe_one]
    rw [← hgk] at hgx ⊢
    have h1 : ((e (k⁻¹ * y * k) : ↥(alternatingGroup (Fin n))) : Perm (Fin n)) ∈
        ggAltImage e H := by
      simpa [map_mul, map_inv] using hgx
    have h2 := (ggMem_altImage e).mp h1
    have h3 : (k : W)⁻¹ * (y : W) * (k : W) ∈ H := by simpa using h2
    exact (ggMem_altImage e).mpr ((ggControlsStrongFusion_iff.mp hfus).2 _ hyE hy1 _ h3)
  rcases ggAltCore hp2 hMtop hEM hEab' hEp' hEcard' hctl with
    ⟨rfl, h6, hnc⟩ | ⟨rfl, ⟨k, hk2, hk4, hk⟩, hcomp⟩ | ⟨C', hC', m, hm7, hm8, ⟨eC⟩⟩
  ·
    left
    have hn6 : n = 6 := by simpa using h6
    subst hn6
    exact ⟨rfl, ⟨e⟩, fun C hC => hnc _ (ggIsComponentOf_altImage e hC)⟩
  ·
    right
    left
    have hn5 : n = 5 * k := by simpa using hk
    subst hn5
    refine ⟨rfl, ⟨k, hk2, hk4, ⟨e⟩⟩, fun C hC => ?_⟩
    obtain ⟨eA⟩ := hcomp _ (ggIsComponentOf_altImage e hC)
    have e5 : ↥C ≃* ↥(alternatingGroup (Fin 5)) :=
      (ggAltImageEquiv e (hC.1.trans inf_le_right)).trans eA
    have hsimp : IsSimpleGroup ↥C :=
      (MulEquiv.isSimpleGroup_congr e5).mpr (alternatingGroup.isSimpleGroup (by simp))
    have hnabC : ∃ a b : ↥C, a * b ≠ b * a := by
      have h5 : ¬ IsMulCommutative ↥(alternatingGroup (Fin 5)) := by
        rw [alternatingGroup.isMulCommutative_iff_card_le_three]
        simp
      by_contra h
      push Not at h
      exact h5 ⟨⟨fun a b => e5.symm.injective (by rw [map_mul, map_mul]; exact h _ _)⟩⟩
    have hZ := ggCenter_eq_bot_of_simple hnabC
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e5⟩
  ·
    exfalso
    obtain ⟨L, hLc, ⟨eL⟩⟩ := ggExists_isComponentOf_of_altImage e hC'
    have eLm : ↥L ≃* ↥(alternatingGroup (Fin m)) := eL.trans eC
    have hLsimp : IsSimpleGroup ↥L :=
      (MulEquiv.isSimpleGroup_congr eLm).mpr (alternatingGroup.isSimpleGroup (by simp; omega))
    have hLH : L ≤ H := hLc.1.trans inf_le_left
    have hnorm : ((H ⊓ CFSG.generalizedFitting W).subgroupOf H).Normal := by
      rw [Subgroup.inf_subgroupOf_left]
      exact hKn.subgroupOf H
    have hLcH : IsComponentOf L H :=
      ⟨hLH, ggIsSubnormal_trans hLc.2.1 (ggIsSubnormal_of_normal inf_le_left hnorm), hLc.2.2⟩
    have hL1 := ggIsComponentOf_subgroupOf hLcH (le_refl H)
    rw [Subgroup.subgroupOf_self] at hL1
    set π := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
    have hO2 : Group.IsSolvable ↥(CFSG.pCore 2 ↥H) := by
      have : Fact (2 : ℕ).Prime := ⟨Nat.prime_two⟩
      have : Group.IsNilpotent ↥(CFSG.pCore 2 ↥H) :=
        (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).isNilpotent
      infer_instance
    have hnotker : ¬ L.subgroupOf H ≤ π.ker := by
      rw [hπ, QuotientGroup.ker_mk']
      exact ggComponent_not_le_of_isSolvable hL1 hO2
    have hCbar := ggIsComponentOf_map π hL1 hnotker
    rw [Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective _)] at hCbar
    obtain ⟨-, hmark⟩ := hIIIa _ hCbar
    set f : ↥(L.subgroupOf H) →* GGHypQuot H := π.comp (L.subgroupOf H).subtype with hf
    have hLsub : IsSimpleGroup ↥(L.subgroupOf H) :=
      (MulEquiv.isSimpleGroup_congr (Subgroup.subgroupOfEquivOfLe hLH).symm).mp hLsimp
    have hfinj : Function.Injective f := by
      rw [← MonoidHom.ker_eq_bot_iff]
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
      · exact h
      · exfalso
        apply hnotker
        intro x hx
        have : (⟨x, hx⟩ : ↥(L.subgroupOf H)) ∈ f.ker := h ▸ Subgroup.mem_top _
        rw [MonoidHom.mem_ker] at this
        rw [MonoidHom.mem_ker]
        exact this
    have hrange : f.range = (L.subgroupOf H).map π := by
      rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
    have eCbar : ↥((L.subgroupOf H).map π) ≃* ↥(alternatingGroup (Fin m)) :=
      (MulEquiv.subgroupCongr hrange).symm.trans ((MonoidHom.ofInjective hfinj).symm.trans
        ((Subgroup.subgroupOfEquivOfLe hLH).trans eLm))
    exact hNM m hm7 hm8 _ ⟨eCbar⟩ _ hmark

end Alt

@[expose] def GGKGroupFusionDefiningInnerInputFlat : Prop :=
  ∀ (W : Type) [Group W] [Finite W] (p : ℕ) (H E : Subgroup W) (d : TauCeti.ValidLieTypeIndex),
    p = d.1.characteristic → GGHypThreeSixteenFlat p H E →
      LargeEvenLayer (⊤ : Subgroup (GGHypQuot H)) ≠ ⊥ → ¬ CFSG.generalizedFitting W ≤ H →
        Nonempty (↥(CFSG.generalizedFitting W) ≃* (TauCeti.CFSGIndex.lie d).Group) →
          E ⊓ CFSG.generalizedFitting W ≠ ⊥ →
            ∀ S : Subgroup W, S ≤ CFSG.generalizedFitting W → IsPGroup p S →
              ¬ p ∣ S.relIndex (CFSG.generalizedFitting W) → S ≤ H →
                Subgroup.normalizer (S : Set W) ≤ H → GGFusionException p H E

@[expose] def GGKGroupFusionDefiningOuterInputFlat : Prop :=
  ∀ (W : Type) [Group W] [Finite W] (p : ℕ) (H E : Subgroup W) (d : TauCeti.ValidLieTypeIndex),
    p = d.1.characteristic → GGHypThreeSixteenFlat p H E →
      LargeEvenLayer (⊤ : Subgroup (GGHypQuot H)) ≠ ⊥ → ¬ CFSG.generalizedFitting W ≤ H →
        Nonempty (↥(CFSG.generalizedFitting W) ≃* (TauCeti.CFSGIndex.lie d).Group) →
          E ⊓ CFSG.generalizedFitting W = ⊥ → GGFusionException p H E

theorem ggKGroupFusionAtFlat_lieDefining_of (h₁ : GGKGroupFusionDefiningInnerInputFlat)
    (h₂ : GGKGroupFusionDefiningOuterInputFlat) : GGKGroupFusionAtFlat GGKFLieDefining := by
  rintro W _ _ p H E i ⟨d, rfl, hpd⟩ hyp hL hKH he
  by_cases hEK : E ⊓ CFSG.generalizedFitting W = ⊥
  · exact h₂ W p H E d hpd hyp hL hKH he hEK
  · obtain ⟨S, hSK, hSp, hSidx, -, hSH, hNH⟩ :=
      hyp.1.2.2.2.2.exists_sylow_normalizer_le hyp.1.1 hyp.1.2.2.1 hEK
    exact h₁ W p H E d hpd hyp hL hKH he hEK S hSK hSp hSidx hSH hNH

theorem ggKGroupFusionDefiningInnerInputFlat_of_parabolic
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor InCatalog)
    (hpar : GGLieParabolicCharInput) : GGKGroupFusionDefiningInnerInputFlat := by
  intro W _ _ p H E d hpd hyp hL hKH he _ S hSK hSp hSidx _ hNH
  exfalso
  apply hL
  have hKn : (CFSG.generalizedFitting W).Normal :=
    CFSG.LocalCores.generalized_fitting_characteristic.2
  have hp : p.Prime := hyp.1.1
  have hp2 : p ≠ 2 := hyp.1.2.1
  have hX : IsCharacteristicP p ↥(H.subgroupOf (CFSG.generalizedFitting W)) := by
    subst hpd
    refine hpar _ d he hp2 (S.subgroupOf (CFSG.generalizedFitting W))
      (H.subgroupOf (CFSG.generalizedFitting W)) ?_ hSidx ?_ ?_
    · exact hSp.comap_of_injective _ (CFSG.generalizedFitting W).subtype_injective
    · intro k hk
      exact Subgroup.mem_subgroupOf.mpr
        (hNH (ggMem_normalizer_of_mem_normalizer_subgroupOf hSK hk))
    · intro htop
      exact hKH (Subgroup.subgroupOf_eq_top.mp htop)
  have hN := CFSG.LocalAnalysis.ComponentInitial.isCharacteristicP_of_mulEquiv
    (ggSubgroupOfEquivKer H (CFSG.generalizedFitting W)) hX
  exact ggLayer_quot_pCore_two_eq_bot hp hp2 _
    (ggIsSolvable_quot_inf_generalizedFitting_flat hSch hyp) hN

theorem ggKGroupFusionDefiningOuterInputFlat_of_fieldAut (hout : GGLieOuterFieldAutInput) :
    GGKGroupFusionDefiningOuterInputFlat := by
  intro W _ _ p H E d hpd hyp _ hKH he hEK
  exfalso
  have hKn : (CFSG.generalizedFitting W).Normal :=
    CFSG.LocalCores.generalized_fitting_characteristic.2
  obtain ⟨⟨hp, hp2, hE, hEcard, hfus⟩, ⟨hsimple, hnab, -⟩, -⟩ := hyp
  have : Fact p.Prime := ⟨hp⟩
  subst hpd
  obtain ⟨e, heE, he1, hmax⟩ := hout W E d hsimple hnab he hp2 hE hEcard hEK
  apply hKH
  have hY := hmax (H ⊓ CFSG.generalizedFitting W) inf_le_right
    (inf_le_inf_right _ (hfus.centralizer_le heE he1))
    (hfus.not_dvd_relIndex_inf hE heE he1 _)
  exact hY ▸ inf_le_left

theorem ggKGroupFusionAtFlat_lieDefining_of_inputs
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor InCatalog)
    (hpar : GGLieParabolicCharInput) (hout : GGLieOuterFieldAutInput) :
    GGKGroupFusionAtFlat GGKFLieDefining :=
  ggKGroupFusionAtFlat_lieDefining_of (ggKGroupFusionDefiningInnerInputFlat_of_parabolic hSch hpar)
    (ggKGroupFusionDefiningOuterInputFlat_of_fieldAut hout)

section Cross

open CFSG.AGLEmbeddingD2

theorem ggGeneralizedFitting_le_of_seitz_flat (hS : KFactSeitzRankTwo) {W : Type} [Group W]
    [Finite W] {p : ℕ} {H E : Subgroup W} (hyp : GGHypThreeSixteenFlat p H E)
    (d : TauCeti.ValidLieTypeIndex)
    (e : ↥(CFSG.generalizedFitting W) ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hpd : p ≠ d.1.characteristic) (hex : ¬ IsD2SeitzException p d.1) :
    CFSG.generalizedFitting W ≤ H := by
  obtain ⟨⟨hp, hp2, hE, hEcard, hfus⟩, ⟨hsimple, hnab, -⟩, -⟩ := hyp
  set K := CFSG.generalizedFitting W
  have : K.Normal := CFSG.LocalCores.generalized_fitting_characteristic.2
  have hφ : Function.Injective (MulAut.conjNormal (H := K)) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    refine ggEq_one_of_commute_generalizedFitting hsimple hnab fun k hk => ?_
    have h1 := congrArg Subtype.val (DFunLike.congr_fun hx ⟨k, hk⟩)
    rw [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    exact mul_inv_eq_iff_eq_mul.mp h1
  let ψ : W →* MulAut (TauCeti.CFSGIndex.lie d).Group :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := K))
  have hψ : Function.Injective ψ := fun x y hxy => hφ ((MulAut.congr e).injective hxy)
  have hfix : ∀ (a : W) (k : K), ψ a (e k) = e k ↔ a * (k : W) * a⁻¹ = k := by
    intro a k
    have h1 : ψ a (e k) = e (MulAut.conjNormal (H := K) a k) := by
      simp [ψ, MulAut.congr_apply]
    rw [h1, e.apply_eq_iff_eq, ← Subtype.coe_inj, MulAut.conjNormal_apply]
  have hclos := hS d p hp hp2 hpd hex (E.map ψ)
    (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p ⟨hE.1, hE.2⟩ ψ)
    (by rw [Subgroup.card_map_of_injective hψ, hEcard])
  have hle : Subgroup.closure
      {t : (TauCeti.CFSGIndex.lie d).Group | ∃ ε ∈ E.map ψ, ε ≠ 1 ∧ ε t = t} ≤
      (H.subgroupOf K).map e.toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro t ⟨_, ⟨a, haE, rfl⟩, hε1, hεt⟩
    refine ⟨e.symm t, Subgroup.mem_subgroupOf.mpr ?_, by simp⟩
    have ha1 : a ≠ 1 := by
      rintro rfl
      exact hε1 (map_one ψ)
    have hfixa : a * ((e.symm t : K) : W) * a⁻¹ = (e.symm t : K) :=
      (hfix a (e.symm t)).mp (by simpa using hεt)
    apply hfus.centralizer_le haE ha1
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (mul_inv_eq_iff_eq_mul.mp hfixa).symm
  intro k hk
  have hk' : e ⟨k, hk⟩ ∈ Subgroup.closure
      {t : (TauCeti.CFSGIndex.lie d).Group | ∃ ε ∈ E.map ψ, ε ≠ 1 ∧ ε t = t} := by
    rw [hclos]
    exact Subgroup.mem_top _
  obtain ⟨y, hy, hyk⟩ := hle hk'
  have hyk' : y = ⟨k, hk⟩ := e.injective hyk
  rw [hyk'] at hy
  exact Subgroup.mem_subgroupOf.mp hy

theorem ggKGroupFusionAtFlat_seitz (hS : KFactSeitzRankTwo) :
    GGKGroupFusionAtFlat GGKFLieSeitz := by
  rintro W _ _ p H E i ⟨d, rfl, hpd, hex⟩ hyp - hKH ⟨e⟩
  exact absurd (ggGeneralizedFitting_le_of_seitz_flat hS hyp d e hpd hex) hKH

theorem ggKGroupFusionAtFlat_lieCross_of_seitz (hS : KFactSeitzRankTwo)
    (hexc : GGKGroupFusionAtFlat GGKFLieSeitzException) : GGKGroupFusionAtFlat GGKFLieCross :=
  GGKGroupFusionAtFlat.of_cover (fun _ p _ _ ⟨d, hi, hpd⟩ => by
    by_cases hx : IsD2SeitzException p d.1
    · exact Or.inr ⟨d, hi, hx⟩
    · exact Or.inl ⟨d, hi, hpd, hx⟩) (ggKGroupFusionAtFlat_seitz hS) hexc

end Cross

end CFSG.StandardType

module

public import CFSG.Quasithin.Background.HSL
import CFSG.Quasithin.H13.VolII16Restrict
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerBin
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallRep
import CFSG.Quasithin.Background.Harris.L3.ClassifyWide
import CFSG.Quasithin.Background.HModelType
import TauCeti.RepresentationTheory.Induction.Restriction
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.Quasithin.Background.D2Coprime
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.Small

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_2

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.ComponentInitial CFSG.QuasithinUnique.Setup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
open CFSG.Blueprint (LieModel)
open scoped MatrixGroups Matrix

private lemma exists_mem_apply_mul_inv_not_mem {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}
    (hW : ∀ w : W, w ^ 2 = 1) {U V : Subgroup W} (hUV : IsIrrOn L U V)
    {z : MulAut W} (hzL : z ∈ L) (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1)
    (hfpf : fixV (Subgroup.zpowers z) = ⊥) :
    ∃ u ∈ U, z u * u⁻¹ ∉ V := by
  by_contra hcon
  push Not at hcon
  have hodd : Odd (Nat.card ↥(Subgroup.zpowers z)) := by
    have hord : orderOf z = 3 := orderOf_eq_prime hz3 hz1
    rw [Nat.card_zpowers, hord]
    decide
  have hstab : ∀ g ∈ Subgroup.zpowers z, ∀ u ∈ U, g u ∈ U := by
    intro g hg u hu
    exact hUV.2.1 g (Subgroup.zpowers_le.mpr hzL hg) u hu
  have hdec := CFSG.Quasithin.coprime_decomp hodd hW (P := Subgroup.zpowers z)
    (W := U) hstab
  have hfix : U ⊓ fixV (Subgroup.zpowers z) = ⊥ := by rw [hfpf, inf_bot_eq]
  have hUcomm : CFSG.Quasithin.commSub U (Subgroup.zpowers z) = U := by
    have h1 := hdec.1
    rw [hfix, sup_bot_eq] at h1
    exact h1
  have hle : CFSG.Quasithin.commSub U (Subgroup.zpowers z) ≤ V := by
    rw [CFSG.Quasithin.commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, u, hu, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hmod : z ^ k = z ^ (k % 3) := zpow_eq_zpow_emod (x := z) k (n := 3) hz3
    rw [hmod]
    have hk0 : 0 ≤ k % 3 := Int.emod_nonneg _ (by norm_num)
    have hk3 : k % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
    interval_cases k % 3
    · rw [zpow_zero, MulAut.one_apply, mul_inv_cancel]
      exact V.one_mem
    · simpa using hcon u hu
    · have hzu : z u ∈ U := hUV.2.1 z hzL u hu
      have h1 := hcon (z u) hzu
      have h2 := hcon u hu
      have heq : (z ^ (2 : ℤ)) u * u⁻¹ = (z (z u) * (z u)⁻¹) * (z u * u⁻¹) := by
        rw [zpow_two]
        rw [MulAut.mul_apply]
        group
      rw [heq]
      exact V.mul_mem h1 h2
  have hUleV : U ≤ V := hUcomm ▸ hle
  exact (not_le_of_gt hUV.1) hUleV

theorem pow_three_mem_of_isIrrOn {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)} (hL : IsSL3 ↥L 2)
    (hrk : rk ↥(⊤ : Subgroup W) ≤ 12) {K : Type} [Field K] [Finite K] [CharP K 2]
    (α : SL(3, K) →* ↥L) (hα : Function.Surjective α) (hK : Nat.card K = 4)
    (hcen : (LinearFlag.scalars 3 K).map α = Subgroup.center ↥L) {z : MulAut W} (hzL : z ∈ L)
    (hzc : ∀ l ∈ L, z * l = l * z) (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1)
    (hfpf : fixV (Subgroup.zpowers z) = ⊥) {U V : Subgroup W} (hUV : IsIrrOn L U V)
    {c : MulAut W} (hc : ∀ l ∈ L, c * l = l * c) (hcU : ∀ u ∈ U, c u ∈ U)
    (hcV : ∀ v ∈ V, c v ∈ V) : ∀ u ∈ U, (c ^ 3) u * u⁻¹ ∈ V := by
  classical
  have hKcard : Nat.card K = 4 := hK
  letI : Fintype K := Fintype.ofFinite K
  letI : CommGroup ↥U := inferInstance
  let ρU : ↥L →* MulAut ↥U := CFSG.Quasithin.H13.VolI.resHom L U hUV.2.1
  let Q := ↥U ⧸ (V.subgroupOf U)
  let π : ↥U →* Q := QuotientGroup.mk' (V.subgroupOf U)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hVmap : ∀ l : ↥L,
      (V.subgroupOf U).map ((ρU l : MulAut ↥U) : ↥U →* ↥U) = V.subgroupOf U := by
    intro l
    apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      exact hUV.2.2.1 l l.2 v hv
    · intro v hv
      refine ⟨(ρU l)⁻¹ v, ?_, by simp⟩
      exact hUV.2.2.1 l⁻¹ (L.inv_mem l.2) v hv
  let σ : ↥L →* MulAut Q :=
    { toFun := fun l => QuotientGroup.congr (V.subgroupOf U) (V.subgroupOf U) (ρU l) (hVmap l)
      map_one' := by
        apply MulEquiv.ext
        intro x
        induction x using QuotientGroup.induction_on with
        | H u =>
          rw [QuotientGroup.congr_mk, map_one, MulAut.one_apply, MulAut.one_apply]
      map_mul' := by
        intro l m
        apply MulEquiv.ext
        intro x
        induction x using QuotientGroup.induction_on with
        | H u =>
          rw [MulAut.mul_apply, QuotientGroup.congr_mk, QuotientGroup.congr_mk,
            QuotientGroup.congr_mk, map_mul, MulAut.mul_apply] }
  have hσ_apply : ∀ (l : ↥L) (u : ↥U), σ l (π u) = π (ρU l u) := by
    intro l u
    change QuotientGroup.congr (V.subgroupOf U) (V.subgroupOf U) (ρU l) (hVmap l)
      (QuotientGroup.mk u) = QuotientGroup.mk (ρU l u)
    rw [QuotientGroup.congr_mk]
  have hntQ : Nontrivial Q := by
    obtain ⟨hVU, hU⟩ := hUV
    obtain ⟨u, hu, huv⟩ := SetLike.exists_of_lt hVU
    refine ⟨QuotientGroup.mk (⟨u, hu⟩ : ↥U), 1, ?_⟩
    intro h
    have hv : (⟨u, hu⟩ : ↥U) ∈ V.subgroupOf U := (QuotientGroup.eq_one_iff _).mp h
    rw [Subgroup.mem_subgroupOf] at hv
    exact huv hv
  haveI : Nontrivial Q := hntQ
  have hIrrσ : IsIrrOn σ.range ⊤ ⊥ := by
    refine ⟨bot_lt_top, ?_, ?_, ?_⟩
    · intro x hx a ha
      exact Subgroup.mem_top a
    · intro x hx a ha
      rw [Subgroup.mem_bot] at ha ⊢
      rw [ha, map_one]
    · intro J hJ hbot hJtop
      let J' : Subgroup ↥U := J.comap π
      have hVJ' : V.subgroupOf U ≤ J' := by
        intro v hv
        show π v ∈ J
        have hv1 : π v = 1 := by
          change (QuotientGroup.mk v : Q) = 1
          rw [QuotientGroup.eq_one_iff]
          exact hv
        rw [hv1]
        exact J.one_mem
      have hJ'stab : ∀ (l : MulAut W) (hl : l ∈ L), ∀ u ∈ J', ρU ⟨l, hl⟩ u ∈ J' := by
        intro l hl u hu
        show π (ρU ⟨l, hl⟩ u) ∈ J
        rw [← hσ_apply]
        exact hJ (σ ⟨l, hl⟩) ⟨⟨l, hl⟩, rfl⟩ (π u) hu
      let J'' : Subgroup W := J'.map U.subtype
      have hVJ'' : V ≤ J'' := by
        intro v hv
        have hvU : v ∈ U := hUV.1.le hv
        exact ⟨⟨v, hvU⟩, hVJ' (Subgroup.mem_subgroupOf.mpr hv), rfl⟩
      have hJ''stab : StableUnder L J'' := by
        rintro l hl w ⟨u, hu, rfl⟩
        exact ⟨ρU ⟨l, hl⟩ u, hJ'stab l hl u hu, rfl⟩
      have hJ'' : J'' = V ∨ J'' = U := by
        rcases hUV.2.2.2 J'' hJ''stab hVJ'' (Subgroup.map_subtype_le J') with h | h
        · exact Or.inl h
        · exact Or.inr h
      have hJ'eq : J' = V.subgroupOf U ∨ J' = ⊤ := by
        rcases hJ'' with h | h
        · left
          rw [← Subgroup.comap_map_eq_self_of_injective U.subtype_injective J']
          change Subgroup.comap U.subtype J'' = V.subgroupOf U
          rw [h, Subgroup.comap_subtype]
        · right
          rw [← Subgroup.comap_map_eq_self_of_injective U.subtype_injective J']
          change Subgroup.comap U.subtype J'' = ⊤
          rw [h, Subgroup.comap_subtype]
          exact Subgroup.subgroupOf_self U
      rcases hJ'eq with h | h
      · left
        rw [(Subgroup.map_comap_eq_self_of_surjective hπ J).symm]
        change Subgroup.map π J' = ⊥
        rw [h, Subgroup.map_eq_bot_iff]
        intro x hx
        change (QuotientGroup.mk x : Q) = 1
        rw [QuotientGroup.eq_one_iff]
        exact hx
      · right
        rw [(Subgroup.map_comap_eq_self_of_surjective hπ J).symm]
        change Subgroup.map π J' = ⊤
        rw [h, Subgroup.map_top, MonoidHom.range_eq_top]
        exact hπ
  let τ : SL(3, K) →* MulAut Q := σ.comp α
  let X : Subgroup (MulAut Q) := τ.range
  have hXeq : X = σ.range := by
    change (σ.comp α).range = σ.range
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hα, Subgroup.map_top]
  have hIrrX : IsIrrOn X ⊤ ⊥ := hXeq ▸ hIrrσ
  obtain ⟨Ibin, hIadd, hImod, hIfin, ⟨θ⟩⟩ :=
    CFSG.QuasithinUnique.Setup.Layer.Actor.exists_binModel_of_binary
      (V := Q) (fun q => by
        induction q using QuotientGroup.induction_on with
        | H u =>
          have hu2 : (u : ↥U) * (u : ↥U) = 1 := by
            apply Subtype.ext
            have h := hW (u : W)
            rwa [pow_two] at h
          calc (QuotientGroup.mk u : Q) * QuotientGroup.mk u
              = QuotientGroup.mk ((u : ↥U) * (u : ↥U)) := (map_mul π u u).symm
            _ = QuotientGroup.mk 1 := by rw [hu2]
            _ = 1 := map_one π)
  letI : AddCommGroup Ibin := hIadd
  letI : Module (ZMod 2) Ibin := hImod
  letI : Finite Ibin := hIfin
  let τX : SL(3, K) →* ↥X := τ.codRestrict X (fun g => ⟨g, rfl⟩)
  have hτX : Function.Surjective τX := by
    intro x
    exact ⟨x.2.choose, Subtype.ext x.2.choose_spec⟩
  let ρ : Representation (ZMod 2) SL(3, K) Ibin := (subRep θ X).comp τX
  have hρ_apply : ∀ g u, ρ g u = Layer.binPsi θ (τ g) u := fun g u => rfl
  have hρ_irr : ρ.IsIrreducible :=
    (TauCeti.isIrreducible_comp_surjective_iff τX hτX (subRep θ X)).mpr
      (subRep_isIrreducible θ le_rfl hIrrX)
  have hzcenter : (⟨z, hzL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro l
    apply Subtype.ext
    exact (hzc l l.2).symm
  obtain ⟨s, hs, hαs⟩ := Subgroup.mem_map.mp (hcen ▸ hzcenter)
  have hzact : ∃ u : ↥U, (σ ⟨z, hzL⟩) (π u) ≠ π u := by
    obtain ⟨u, hu, hzu⟩ := exists_mem_apply_mul_inv_not_mem hW hUV hzL hz1 hz3 hfpf
    refine ⟨⟨u, hu⟩, ?_⟩
    rw [hσ_apply]
    intro heq
    apply hzu
    have hd := (QuotientGroup.eq_iff_div_mem).mp heq
    rw [Subgroup.mem_subgroupOf] at hd
    have hd' : (((ρU ⟨z, hzL⟩) ⟨u, hu⟩ : ↥U) : W) * (u : W)⁻¹ ∈ V := by
      simpa [div_eq_mul_inv] using hd
    have h1 : (((ρU ⟨z, hzL⟩) ⟨u, hu⟩ : ↥U) : W) = z u := rfl
    simpa [h1] using hd'
  have hτs_ne : τ s ≠ 1 := by
    intro hτ1
    have hσz : σ ⟨z, hzL⟩ = 1 := by
      have h1 : σ (α s) = 1 := hτ1
      rw [hαs] at h1
      exact h1
    obtain ⟨u, hu⟩ := hzact
    exact hu (by rw [hσz, MulAut.one_apply])
  have hρ_nt : ∃ g, ρ g ≠ 1 := by
    refine ⟨s, ?_⟩
    intro hρ1
    have hsub : subRep θ X (τX s) = 1 := by
      simpa [ρ] using hρ1
    have hsub' : subRep θ X (τX s) = subRep θ X (1 : ↥X) := by
      simpa using hsub
    have hτX1 : τX s = 1 := subRep_injective θ X hsub'
    exact hτs_ne (congrArg Subtype.val hτX1)
  have hcardI : Nat.card Ibin = 2 ^ Module.finrank (ZMod 2) Ibin := by
    haveI : Module.Finite (ZMod 2) Ibin := Module.Finite.of_finite (R := ZMod 2) (M := Ibin)
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Ibin), Nat.card_zmod]
  have hcardQ : Nat.card Q = Nat.card Ibin :=
    Nat.card_congr (θ.toEquiv.trans Multiplicative.toAdd)
  have hdiv : Nat.card Q ∣ Nat.card ↥U := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (V.subgroupOf U)
    exact ⟨Nat.card (V.subgroupOf U), h⟩
  have hrkQ : padicValNat 2 (Nat.card Q) ≤ 12 := by
    have h1 : padicValNat 2 (Nat.card Q) ≤ padicValNat 2 (Nat.card ↥U) :=
      CFSG.Quasithin.padicValNat_two_le_of_dvd (CFSG.Quasithin.card_subgroup_pos U).ne' hdiv
    have h2 : padicValNat 2 (Nat.card ↥U) ≤ padicValNat 2 (Nat.card ↥(⊤ : Subgroup W)) :=
      CFSG.Quasithin.rk_mono le_top
    exact h1.trans (h2.trans hrk)
  have hdim : Module.finrank (ZMod 2) Ibin ≤ 12 := by
    have h := hrkQ
    rw [hcardQ, hcardI, padicValNat.prime_pow] at h
    exact h
  have hUmap : U.map (c : W →* W) = U := by
    have hcard := Subgroup.card_map_of_injective (K := U) (f := (c : W →* W))
      (by exact c.injective)
    have hle : U.map (c : W →* W) ≤ U := by
      rintro _ ⟨u, hu, rfl⟩
      exact hcU u hu
    exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  have hcUinv : ∀ u ∈ U, c⁻¹ u ∈ U := by
    intro u hu
    have hmem : u ∈ U.map (c : W →* W) := hUmap.symm ▸ hu
    obtain ⟨v, hv, hvc⟩ := Subgroup.mem_map.mp hmem
    have hcv : c⁻¹ ((c : W →* W) v) = v := by
      simpa using MulAut.inv_apply_self W c v
    rw [← hvc, hcv]
    exact hv
  have hVmap' : V.map (c : W →* W) = V := by
    have hcard := Subgroup.card_map_of_injective (K := V) (f := (c : W →* W))
      (by exact c.injective)
    have hle : V.map (c : W →* W) ≤ V := by
      rintro _ ⟨v, hv, rfl⟩
      exact hcV v hv
    exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  have hcVinv : ∀ v ∈ V, c⁻¹ v ∈ V := by
    intro v hv
    have hmem : v ∈ V.map (c : W →* W) := hVmap'.symm ▸ hv
    obtain ⟨w, hw, hwv⟩ := Subgroup.mem_map.mp hmem
    have hcw : c⁻¹ ((c : W →* W) w) = w := by
      simpa using MulAut.inv_apply_self W c w
    rw [← hwv, hcw]
    exact hw
  let ρUc : MulAut ↥U := CFSG.Quasithin.H13.VolI.restrictAut U c hcU hcUinv
  have hcVmap : (V.subgroupOf U).map ((ρUc : MulAut ↥U) : ↥U →* ↥U) = V.subgroupOf U := by
    apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr (hcV v (Subgroup.mem_subgroupOf.mp hv))
    · intro v hv
      have hvw : (v : W) ∈ V := Subgroup.mem_subgroupOf.mp hv
      have hmem : (v : W) ∈ V.map (c : W →* W) := hVmap'.symm ▸ hvw
      obtain ⟨w, hw, hwv⟩ := Subgroup.mem_map.mp hmem
      refine ⟨⟨w, hUV.1.le hw⟩, Subgroup.mem_subgroupOf.mpr hw, ?_⟩
      apply Subtype.ext
      exact hwv
  let cQ : MulAut Q := QuotientGroup.congr (V.subgroupOf U) (V.subgroupOf U) ρUc hcVmap
  have hcQ_apply : ∀ u : ↥U, cQ (π u) = π (ρUc u) := by
    intro u
    change QuotientGroup.congr (V.subgroupOf U) (V.subgroupOf U) ρUc hcVmap
      (QuotientGroup.mk u) = QuotientGroup.mk (ρUc u)
    rw [QuotientGroup.congr_mk]
  have hcQ_comm : ∀ l : ↥L, cQ * σ l = σ l * cQ := by
    intro l
    apply MulEquiv.ext
    intro x
    induction x using QuotientGroup.induction_on with
    | H u =>
      change cQ ((σ l) (π u)) = (σ l) (cQ (π u))
      rw [hσ_apply, hcQ_apply, hcQ_apply, hσ_apply]
      congr 1
      apply Subtype.ext
      have hcl : c * (l : MulAut W) = (l : MulAut W) * c := hc l l.2
      have hcomm := congrArg (fun f : MulAut W => f (u : W)) hcl
      have h1 : (((ρUc) ((ρU l) u) : ↥U) : W) = c ((l : MulAut W) (u : W)) := rfl
      have h2 : (((ρU l) ((ρUc) u) : ↥U) : W) =
          (l : MulAut W) (c (u : W)) := rfl
      exact h1.trans (hcomm.trans h2.symm)
  have hcQ_commτ : ∀ g : SL(3, K), cQ * τ g = τ g * cQ := by
    intro g
    change cQ * σ (α g) = σ (α g) * cQ
    exact hcQ_comm (α g)
  have hF : Fintype.card K = 2 ^ 2 := by
    rw [← Nat.card_eq_fintype_card, hKcard]
    norm_num
  have hcQ3 : cQ ^ 3 = 1 := by
    rcases CFSG.Quasithin.G11.Harris.L3.sl3_classification_wide (f := 2) (by norm_num)
      (F := K) hF ρ hρ_irr hρ_nt (by omega) with hnat | hherm
    · obtain ⟨⟨ψ, hψ, E, hE⟩, -⟩ := hnat
      have hψsurj : Function.Surjective ψ := fun γ => ⟨ψ γ, hψ γ⟩
      let C : Ibin ≃ₗ[ZMod 2] Ibin := Layer.binPsi θ cQ
      have hCcomm : ∀ g w, C (ρ g w) = ρ g (C w) := by
        intro g w
        have h2 := congrArg (Layer.binPsi θ) (hcQ_commτ g)
        rw [map_mul, map_mul] at h2
        have h3 := congrArg (fun f : Ibin ≃ₗ[ZMod 2] Ibin => f w) h2
        simpa [C, hρ_apply, LinearEquiv.mul_apply] using h3
      let f : (Fin 3 → K) →+ (Fin 3 → K) :=
        { toFun := fun v => E (C (E.symm v))
          map_zero' := by simp
          map_add' := by
            intro a b
            simp [map_add] }
      have hf_apply : ∀ w, f (E w) = E (C w) := fun w => by simp [f]
      have hf : ∀ γ ∈ StatedSL 3 K, ∀ v, f ((γ : Matrix (Fin 3) (Fin 3) K) *ᵥ v) =
          (γ : Matrix (Fin 3) (Fin 3) K) *ᵥ f v := by
        intro γ hγ v
        let eSL := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K
        let γSL : SL(3, K) := eSL.symm ⟨γ, hγ⟩
        have hγSL : ((γSL : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
            (γ : Matrix (Fin 3) (Fin 3) K) := by
          have h := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe 3 K γSL
          have he : eSL γSL = ⟨γ, hγ⟩ := by simp [γSL]
          rw [he] at h
          exact h.symm
        obtain ⟨w, rfl⟩ := E.surjective v
        obtain ⟨g, hg⟩ := hψsurj γSL
        have hE' : E (ρ g w) = (γ : Matrix (Fin 3) (Fin 3) K) *ᵥ E w := by
          rw [hE g w, hg, hγSL]
        calc f ((γ : Matrix (Fin 3) (Fin 3) K) *ᵥ E w)
            = f (E (ρ g w)) := by rw [hE']
          _ = E (C (ρ g w)) := hf_apply _
          _ = E (ρ g (C w)) := by rw [hCcomm]
          _ = (γ : Matrix (Fin 3) (Fin 3) K) *ᵥ E (C w) := by
              rw [hE g (C w), hg, hγSL]
          _ = (γ : Matrix (Fin 3) (Fin 3) K) *ᵥ f (E w) := by rw [hf_apply]
      obtain ⟨c, hc⟩ := CFSG.Quasithin.H.hasScalarCommutant_statedSL (K := K) (d := 3)
        (by norm_num) f hf
      have hf_bij : Function.Bijective f := by
        refine ⟨?_, ?_⟩
        · intro a b hab
          have h := congrArg (fun v => E.symm v) hab
          simpa [f] using h
        · intro v
          refine ⟨E (C.symm (E.symm v)), ?_⟩
          simp [f]
      have hc0 : c ≠ 0 := by
        intro hc0
        have h0 : f 0 = 0 := map_zero f
        have h1 : f (Pi.single (0 : Fin 3) 1) = 0 := by
          rw [hc, hc0, zero_smul]
        have heq : f (Pi.single (0 : Fin 3) 1) = f 0 := by rw [h1, h0]
        have hne : (Pi.single (0 : Fin 3) (1 : K)) ≠ (0 : Fin 3 → K) := by
          intro h
          have := congrFun h 0
          simpa using this
        exact hne (hf_bij.1 heq)
      have hc3 : c ^ 3 = 1 := by
        have h := FiniteField.pow_card_sub_one_eq_one c hc0
        have hcardF : Fintype.card K = 4 := by
          rw [← Nat.card_eq_fintype_card]
          exact hKcard
        rw [hcardF] at h
        norm_num at h
        exact h
      have hf3 : ∀ v, f (f (f v)) = v := by
        intro v
        rw [hc, hc, hc, smul_smul, smul_smul]
        rw [show c * c * c = c ^ 3 by ring, hc3, one_smul]
      have hC3 : ∀ w, C (C (C w)) = w := by
        intro w
        apply E.injective
        rw [← hf_apply, ← hf_apply, ← hf_apply, hf3]
      have hC3eq : C ^ 3 = 1 := by
        apply LinearEquiv.ext
        intro w
        simpa [pow_succ, LinearEquiv.mul_apply] using hC3 w
      have hbin3 : Layer.binPsi θ (cQ ^ 3) = 1 := by
        rw [map_pow]
        change C ^ 3 = 1
        exact hC3eq
      exact (Layer.binPsi θ).injective (by simpa using hbin3)
    · exfalso
      obtain ⟨k, hfk, -, hKcard, χ, hχ, E, hE⟩ := hherm
      have hk : k = 1 := by omega
      subst hk
      have hK4 : Nat.card K = (2 ^ 1) ^ 2 := hKcard
      have hχsurj : Function.Surjective χ := fun g => ⟨χ g, hχ g⟩
      have hs_center : s ∈ Subgroup.center (SL(3, K)) := by
        rw [← LinearFlag.scalars_eq_center]
        exact hs
      have hχs_scal : χ s ∈ LinearFlag.scalars 3 K := by
        rw [LinearFlag.scalars_eq_center]
        rw [Subgroup.mem_center_iff]
        intro g
        obtain ⟨h, rfl⟩ := hχsurj g
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subgroup.mem_center_iff.mp hs_center h
      obtain ⟨l, -, hlmat⟩ := (LinearFlag.mem_scalars).mp hχs_scal
      have hχGL : Matrix.SpecialLinearGroup.toGL (χ s) =
          CFSG.Quasithin.H.L3Nine.scalGL l := by
        apply Units.ext
        change ((χ s : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
          ((CFSG.Quasithin.H.L3Nine.scalGL l : GL (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K)
        rw [hlmat, CFSG.Quasithin.H.L3Nine.coe_scalGL, Matrix.scalar_apply,
          Matrix.smul_one_eq_diagonal]
      have hrho1 : CFSG.Quasithin.H.L3Nine.rho hK4 (χ s) = 1 := by
        change CFSG.Quasithin.H.L3Nine.rhoT hK4
          (Matrix.SpecialLinearGroup.toGL (χ s)) = 1
        rw [hχGL]
        exact CFSG.Quasithin.H.ModelType.rhoT_scalGL_eq_one hK4 l
      have hρs1 : ρ s = 1 := by
        apply LinearMap.ext
        intro u
        apply Multiplicative.ofAdd.injective
        apply E.injective
        have h := hE s u
        rw [hrho1, MulAut.one_apply] at h
        exact h
      have hρs1' : subRep θ X (τX s) = 1 := by
        simpa [ρ] using hρs1
      have hτX1 : τX s = 1 := subRep_injective θ X (by simpa using hρs1')
      exact hτs_ne (congrArg Subtype.val hτX1)
  have hρUcpow : ∀ k : ℕ, ∀ x : ↥U, (((ρUc ^ k) x : ↥U) : W) = (c ^ k) (x : W) := by
    intro k
    induction k with
    | zero =>
      intro x
      simp
    | succ k ih =>
      intro x
      rw [pow_succ', MulAut.mul_apply]
      change ((ρUc) ((ρUc ^ k) x) : W) = (c ^ (k + 1)) (x : W)
      rw [show ((ρUc) ((ρUc ^ k) x) : W) = c (((ρUc ^ k) x : ↥U) : W) from rfl, ih,
        pow_succ']
      rfl
  have hcQpow : ∀ k : ℕ, ∀ x : ↥U, (cQ ^ k) (π x) = π ((ρUc ^ k) x) := by
    intro k
    induction k with
    | zero =>
      intro x
      simp
    | succ k ih =>
      intro x
      rw [pow_succ, MulAut.mul_apply, hcQ_apply, ih, pow_succ, MulAut.mul_apply]
  intro u hu
  have hfix : (cQ ^ 3) (π ⟨u, hu⟩) = π ⟨u, hu⟩ := by rw [hcQ3, MulAut.one_apply]
  have hfix3 : π ((ρUc ^ 3) ⟨u, hu⟩) = π ⟨u, hu⟩ := by
    rw [← hcQpow 3 ⟨u, hu⟩]
    exact hfix
  have hd := (QuotientGroup.eq_iff_div_mem).mp hfix3
  rw [Subgroup.mem_subgroupOf] at hd
  have hval : (((ρUc ^ 3) ⟨u, hu⟩ : ↥U) : W) = (c ^ 3) u := by
    rw [hρUcpow]
  simpa [div_eq_mul_inv, hval] using hd

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_2

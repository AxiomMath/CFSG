module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Rest15Gamma
import CFSG.LocalAnalysis.UniquenessCase.UC6R869NS
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddChain
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
import CFSG.LocalAnalysis.GL83PartI.I710.Basic
import CFSG.HardMathSupport.Malle.E27Lie.Cross.PerfectQuotient
import CFSG.GH74.GLS.AssemblyComponents
import CFSG.GroupTheory.ComponentCovering
import CFSG.CGT.Foote82.T66.BranchAGen
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CatalogSchreier
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsGroup
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_6_8
import CFSG.ClassicalInvolution.RouteD.GapsPerfect
import CFSG.LocalAnalysis.UniquenessCase.UC22P22t
public import CFSG.LocalAnalysis.AGLEmbedding.ComponentRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.ComponentClassification.OuterAutomorphisms

private theorem action_eq_one_of_quasisimple_of_inner_of_fixed_sylow
    {A K : Type*} [Group A] [Finite A] [Group K] [Finite K]
    (hA : CFSG.IsQuasisimple A) {p : ℕ} [Fact p.Prime]
    (hpA : p ∣ Nat.card A) (hK : Subgroup.center K = ⊥)
    (ρ : A →* MulAut K) (hρ : ρ.range ≤ inner K) (P : Sylow p K)
    (hfix : ∀ a : A, ∀ x ∈ (P : Subgroup K), ρ a x = x) :
    ρ = 1 := by
  classical
  have : Group.IsPerfect A := hA.1
  have : Group.IsPerfect ρ.range := Group.IsPerfect.range ρ
  let T : Sylow p A := Classical.choice Sylow.nonempty
  let T' : Sylow p ρ.range := T.mapSurjective ρ.rangeRestrict_surjective
  have hcentral : (T' : Subgroup ρ.range) ≤ Subgroup.center ρ.range := by
    intro t ht
    rw [Sylow.coe_mapSurjective] at ht
    obtain ⟨a, ha, hat⟩ := ht
    obtain ⟨n, hn⟩ := T.isPGroup' ⟨a, ha⟩
    have hpow : (ρ a) ^ (p ^ n) = 1 := by
      rw [← map_pow]
      have ha1 : a ^ (p ^ n) = 1 := congrArg Subtype.val hn
      rw [ha1, map_one]
    have hcomm : ∀ x ∈ (P : Subgroup K), ρ a * MulAut.conj x = MulAut.conj x * ρ a := by
      intro x hx
      ext y
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hfix a x hx]
    obtain ⟨x, hx, heq⟩ :=
      GL83.I710.exists_eq_conj_of_mem_inner
        hK P ⟨n, hpow⟩ hcomm (hρ ⟨a, rfl⟩)
    rw [Subgroup.mem_center_iff]
    intro b
    obtain ⟨c, hc⟩ := b.2
    apply Subtype.ext
    change (b : MulAut K) * (t : MulAut K) = (t : MulAut K) * (b : MulAut K)
    rw [← hat, ← hc]
    change ρ c * ρ a = ρ a * ρ c
    rw [heq]
    ext y
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hfix c x hx]
  have hTbot : (T' : Subgroup ρ.range) = ⊥ := by
    by_contra hne
    have hp : p ∣ Nat.card ρ.range := by
      have hcard : Nat.card (T' : Subgroup ρ.range) ≠ 1 := by
        exact ne_of_gt ((Subgroup.one_lt_card_iff_ne_bot _).mpr hne)
      rcases T'.isPGroup'.card_eq_or_dvd with h | h
      · exact False.elim (hcard h)
      · exact h.trans (Subgroup.card_subgroup_dvd_card _)
    exact CFSG.HardMathSupport.Malle.E27Lie.not_sylow_le_center_of_perfect
      (Group.IsPerfect.commutator_eq_top (G := ρ.range)) hp T' hcentral
  have hTker : (T : Subgroup A) ≤ ρ.ker := by
    intro a ha
    have hmem : ρ.rangeRestrict a ∈ (T' : Subgroup ρ.range) := by
      rw [Sylow.coe_mapSurjective]
      exact Subgroup.mem_map_of_mem _ ha
    rw [hTbot, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hA ρ.normal_ker with htop | hcent
  · apply MonoidHom.ext
    intro a
    change ρ a = 1
    exact show a ∈ ρ.ker from htop.symm ▸ Subgroup.mem_top a
  · exact False.elim (CFSG.HardMathSupport.Malle.E27Lie.not_sylow_le_center_of_perfect
      hA.1.commutator_eq_top hpA T (hTker.trans hcent))

private theorem action_eq_one_of_quasisimple_of_inner_of_fixed_sylow_perfect
    {A K : Type*} [Group A] [Finite A] [Group K] [Finite K]
    (hA : CFSG.IsQuasisimple A) (hK : Group.IsPerfect K)
    {p : ℕ} [Fact p.Prime] (hpA : p ∣ Nat.card A)
    (ρ : A →* MulAut K) (hρ : ρ.range ≤ inner K) (P : Sylow p K)
    (hfix : ∀ a : A, ∀ x ∈ (P : Subgroup K), ρ a x = x) :
    ρ = 1 := by
  have : Group.IsPerfect K := hK
  let π : K →* K ⧸ Subgroup.center K := QuotientGroup.mk' (Subgroup.center K)
  let β := CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom K
  let P' : Sylow p (K ⧸ Subgroup.center K) := P.mapSurjective (f := π) (QuotientGroup.mk'_surjective _)
  have hinner : (β.comp ρ).range ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner (K ⧸ Subgroup.center K) := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨x, hx⟩ := hρ ⟨a, rfl⟩
    refine ⟨π x, ?_⟩
    change MulAut.conj (π x) = β (ρ a)
    rw [← hx]
    exact (centerQuotient_conj x).symm
  have hfixed : ∀ a : A, ∀ x ∈ (P' : Subgroup (K ⧸ Subgroup.center K)), (β.comp ρ) a x = x := by
    intro a x hx
    rw [Sylow.coe_mapSurjective] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    change CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient (ρ a) (π y) = π y
    rw [CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk, hfix a y hy]
  have htriv := action_eq_one_of_quasisimple_of_inner_of_fixed_sylow hA hpA
    (Group.IsPerfect.center_quotient_center_eq_bot (G := K)) (β.comp ρ) hinner P' hfixed
  apply MonoidHom.ext
  intro a
  change ρ a = 1
  apply CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective K
  have h := DFunLike.congr_fun htriv a
  simpa only [MonoidHom.comp_apply, MonoidHom.one_apply, map_one] using h

private theorem component_le_or_commute_inf_of_subnormal
    {G : Type*} [Group G] [Finite G] {X A H K : Subgroup G}
    (hAH : A ≤ H) (hX : CFSG.Open.IsComponentOf X A) (hK : CFSG.Open.IsSubnormal K H) :
    X ≤ K ∨ ⁅X, K ⊓ A⁆ = ⊥ := by
  have hsub : CFSG.Open.IsSubnormal (K ⊓ A) A := by
    have h := hK.inf_of_le hAH
    simpa only [inf_comm A K] using h
  have hX' : CFSG.IsComponent (X.subgroupOf A) :=
    CFSG.CGT.Foote82.BranchAAux.isComponent_subgroupOf hX
  have hsub' : ((K ⊓ A).subgroupOf A).IsSubnormal :=
    (CFSG.Open.IsSubnormal.iff_subgroupOf inf_le_right).1 hsub
  rcases CFSG.LocalCores.component_subnormal_subgroup hX' hsub' with hle | hcomm
  · left
    have h := Subgroup.map_mono (f := A.subtype) hle
    rw [Subgroup.map_subgroupOf_eq_of_le hX.1, Subgroup.map_subgroupOf_eq_of_le inf_le_right] at h
    exact h.trans inf_le_left
  · right
    have h := congrArg (Subgroup.map A.subtype) hcomm
    rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hX.1,
      Subgroup.map_subgroupOf_eq_of_le inf_le_right, Subgroup.map_bot] at h

private theorem component_centralizes_fitting_of_le
    {G : Type*} [Group G] [Finite G] {X H M : Subgroup G}
    (hX : CFSG.Open.IsComponentOf X (H ⊓ M))
    (hF : CFSG.fittingSubgroupOf H ≤ M) :
    X ≤ Subgroup.centralizer (CFSG.fittingSubgroupOf H : Set G) := by
  let F := CFSG.fittingSubgroupOf H
  have hFH : F ≤ H := Subgroup.map_subtype_le _
  have hFA : F ≤ H ⊓ M := le_inf hFH hF
  have hFn : (F.subgroupOf (H ⊓ M)).Normal := by
    have hsub : F.subgroupOf H = CFSG.fittingSubgroup H :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    have : (F.subgroupOf H).Normal := hsub.symm ▸ inferInstance
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hFA).2
    exact inf_le_left.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hFH).1 inferInstance)
  have hFs : Group.IsSolvable F := by
    have : Group.IsNilpotent (CFSG.fittingSubgroup H) := inferInstance
    exact Group.isSolvable_of_surjective
      (f := (Subgroup.equivMapOfInjective (CFSG.fittingSubgroup H) H.subtype H.subtype_injective).toMonoidHom)
      (Subgroup.equivMapOfInjective (CFSG.fittingSubgroup H) H.subtype H.subtype_injective).surjective
  rcases CFSG.CGT.Foote82.BranchAAux.le_or_commute_of_normal hX hFA hFn with hle | hcomm
  · have : Group.IsSolvable F := hFs
    have : Group.IsPerfect X := ⟨hX.2.2.1⟩
    have : Nontrivial X := CFSG.LocalCores.isQuasisimple_nontrivial
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native X).1 hX.2.2)
    have : Group.IsSolvable X := Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective hle)
    exact False.elim (Group.IsPerfect.not_isSolvable X inferInstance)
  · exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm

private theorem card_three_components_le_three
    {H : Type} [Group H] [Finite H] (hr : CFSG.Open.pRank 3 (⊤ : Subgroup H) ≤ 3) :
    Nat.card {K : Subgroup H // CFSG.IsComponent K ∧ 3 ∣ Nat.card K} ≤ 3 := by
  let C := {K : Subgroup H // CFSG.IsComponent K ∧ 3 ∣ Nat.card K}
  have hc : ∀ c : C, CFSG.Open.IsComponentOf c.1 ⊤ := fun c =>
    (CFSG.isComponent_iff_open c.1).1 c.2.1
  have he : ∀ c : C, ∃ x : H, x ∈ c.1 ∧ IsPGroup 3 (Subgroup.zpowers x) ∧
      ∃ y ∈ c.1, x * y ≠ y * x := by
    intro c
    obtain ⟨x, hx, hxZ⟩ := CFSG.HardMathSupport.Timmesfeld.ComponentBalance.exists_orderOf_eq_prime_not_mem_center
      (hc c).2.2 Nat.prime_three (by norm_num) c.2.2
    have hn := Subgroup.mem_center_iff.not.1 hxZ
    obtain ⟨y, hy⟩ := not_forall.1 hn
    refine ⟨x, x.2, ?_, y, y.2, ?_⟩
    · have hcard : Nat.card (Subgroup.zpowers (x : H)) = 3 := by
        rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]
      exact IsPGroup.of_card (p := 3) (n := 1) (by simpa using hcard)
    · exact fun h => hy (Subtype.ext h.symm)
  choose x hx hp y hy hxy using he
  exact (CFSG.AGLEmbedding.le_pRank_of_components Nat.prime_three
    (fun c : C => c.1) hc (fun a b h => Subtype.ext h) (⊤ : Subgroup H) x
    (fun _ => Subgroup.mem_top _) hx hp (fun c => ⟨y c, hy c, hxy c⟩)).trans hr

private theorem perfect_le_normalizer_three_component
    {H : Type} [Group H] [Finite H] {X K : Subgroup H}
    (hX : Group.IsPerfect X) (hr : CFSG.Open.pRank 3 (⊤ : Subgroup H) ≤ 3)
    (hK : CFSG.IsComponent K) (h3 : 3 ∣ Nat.card K) :
    X ≤ Subgroup.normalizer (K : Set H) := by
  have : Group.IsPerfect X := hX
  let C : Set (Subgroup H) := {K | CFSG.IsComponent K ∧ 3 ∣ Nat.card K}
  have hcard : C.ncard ≤ 4 := by
    have h := card_three_components_le_three hr
    change Nat.card C ≤ 3 at h
    rw [Nat.card_coe_set_eq] at h
    omega
  have hstable : ∀ g ∈ X, ∀ A ∈ C, A.map (MulAut.conj g).toMonoidHom ∈ C := by
    intro g hg A hA
    refine ⟨CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hA.1, ?_⟩
    simpa only [Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective] using hA.2
  exact CFSG.ClassicalInvolution.RouteD.Gaps.perfect_le_normalizer_of_card_le_four X C
    (Set.toFinite _) hcard hstable ⟨hK, h3⟩

private theorem action_range_le_inner_of_schreier
    {H : Type} [Group H] [Finite H]
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections H)
    {X K : Subgroup H} (hXp : Group.IsPerfect X) (hK : CFSG.IsComponent K)
    (hN : X ≤ Subgroup.normalizer (K : Set H)) :
    (K.normalizerMonoidHom.comp (Subgroup.inclusion hN)).range ≤ inner K := by
  have : Group.IsPerfect X := hXp
  have : Group.IsPerfect K := hK.1.1
  have : Group.IsSolvable (Outer (K ⧸ Subgroup.center K)) := hSch.outer_component K hK
  have : Group.IsSolvable (Outer K) := solvable_of_centerQuotient K
  rintro _ ⟨x, rfl⟩
  obtain ⟨k, hk⟩ := perfect_action_inner
    (K.normalizerMonoidHom.comp (Subgroup.inclusion hN)) x
  exact ⟨k, hk.symm⟩

private theorem exists_three_component_not_centralized
    {H : Type} [Group H] [Finite H] {X : Subgroup H}
    (hX : CFSG.IsQuasisimple X)
    (hXF : X ≤ Subgroup.centralizer (CFSG.fittingSubgroup H : Set H))
    (hXO : X ≤ Subgroup.centralizer (CFSG.pPrimeCore 3 H : Set H)) :
    ∃ K : Subgroup H, CFSG.IsComponent K ∧ 3 ∣ Nat.card K ∧
      ¬ X ≤ Subgroup.centralizer (K : Set H) := by
  by_contra hnone
  push Not at hnone
  have hcent : ∀ K : Subgroup H, CFSG.IsComponent K →
      X ≤ Subgroup.centralizer (K : Set H) := by
    intro K hK
    by_cases h3 : 3 ∣ Nat.card K
    · exact hnone K hK h3
    · have hKO : K ≤ CFSG.pPrimeCore 3 H :=
        CFSG.GH74.GLS.le_pPrimeCore_of_subnormal 3 hK.2
          (Nat.prime_three.coprime_iff_not_dvd.2 h3)
      exact hXO.trans (Subgroup.centralizer_le hKO)
  have hXE : X ≤ Subgroup.centralizer (CFSG.layer H : Set H) := by
    rw [CFSG.layer.eq_sSup, Subgroup.le_centralizer_iff]
    exact sSup_le fun K hK => Subgroup.le_centralizer_iff.2 (hcent K hK)
  have hXFstar : X ≤ Subgroup.centralizer (CFSG.generalizedFitting H : Set H) := by
    rw [CFSG.generalizedFitting.eq_sup, Subgroup.le_centralizer_iff]
    exact sup_le (Subgroup.le_centralizer_iff.2 hXF) (Subgroup.le_centralizer_iff.2 hXE)
  have hXle : X ≤ CFSG.generalizedFitting H :=
    hXFstar.trans (CFSG.centralizer_generalizedFitting_le H)
  have hcomm : IsMulCommutative X := Subgroup.le_centralizer_iff_isMulCommutative.1
    (hXFstar.trans (Subgroup.centralizer_le hXle))
  have : Group.IsPerfect X := hX.1
  have : Nontrivial X := CFSG.LocalCores.isQuasisimple_nontrivial hX
  have : Group.IsSolvable X := Group.isSolvable_of_comm (isMulCommutative_iff.1 hcomm)
  exact Group.IsPerfect.not_isSolvable X inferInstance

private theorem exists_component_containing_of_sylow_le
    {H : Type} [Group H] [Finite H] {A X : Subgroup H}
    (hX : CFSG.Open.IsComponentOf X A) (h3X : 3 ∣ Nat.card X)
    (hr : CFSG.Open.pRank 3 (⊤ : Subgroup H) ≤ 3)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections H)
    (hXF : X ≤ Subgroup.centralizer (CFSG.fittingSubgroup H : Set H))
    (hXO : X ≤ Subgroup.centralizer (CFSG.pPrimeCore 3 H : Set H))
    (P : Sylow 3 H) (hPA : (P : Subgroup H) ≤ A) :
    ∃ K : Subgroup H, CFSG.IsComponent K ∧ X ≤ K := by
  have hXq : CFSG.IsQuasisimple X :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native X).1 hX.2.2
  obtain ⟨K, hK, h3K, hnc⟩ := exists_three_component_not_centralized hXq hXF hXO
  refine ⟨K, hK, ?_⟩
  rcases component_le_or_commute_inf_of_subnormal (show A ≤ ⊤ from le_top) hX
    ((CFSG.isComponent_iff_open K).1 hK).2.1 with hle | hcomm
  · exact hle
  · have hN := perfect_le_normalizer_three_component hXq.1 hr hK h3K
    let ρ := K.normalizerMonoidHom.comp (Subgroup.inclusion hN)
    have hinn : ρ.range ≤ inner K := action_range_le_inner_of_schreier hSch hXq.1 hK hN
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hPtop : CFSG.ABGLocalTools.IsSylowOf 3 (P : Subgroup H) ⊤ :=
      CFSG.ABGLocalTools.isSylowOf_iff.2
        ⟨le_top, P.isPGroup', by simpa using P.not_dvd_index⟩
    have hSyl : CFSG.ABGLocalTools.IsSylowOf 3 ((P : Subgroup H) ⊓ K) K :=
      CFSG.ABGLocalTools.IsSylowOf.inf_of_isSubnormal
        hPtop
        ((CFSG.isComponent_iff_open K).1 hK).2.1
    obtain ⟨S, hS⟩ := hSyl.exists_sylow_eq_subgroupOf
    have hfix : ∀ x : X, ∀ k ∈ (S : Subgroup K), ρ x k = k := by
      intro x k hk
      rw [hS] at hk
      have hkP : (k : H) ∈ (P : Subgroup H) ⊓ K := hk
      have hkA : (k : H) ∈ K ⊓ A := ⟨k.2, hPA hkP.1⟩
      have hc := Subgroup.mem_centralizer_iff.1
        ((Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm) x.2) (k : H) hkA
      apply Subtype.ext
      change (x : H) * (k : H) * (x : H)⁻¹ = (k : H)
      rw [← hc]
      group
    have htriv := action_eq_one_of_quasisimple_of_inner_of_fixed_sylow_perfect hXq hK.1.1
      h3X ρ hinn S hfix
    exact False.elim (hnc (by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h := DFunLike.congr_fun (DFunLike.congr_fun htriv ⟨x, hx⟩) ⟨k, hk⟩
      have hval := congrArg Subtype.val h
      change x * k * x⁻¹ = k at hval
      have hh := congrArg (fun z : H => z * x) hval
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh.symm))

private theorem component_centralizes_three_primeCore_of_le
    {G : Type} [Group G] [Finite G] {X H M : Subgroup G}
    (hX : CFSG.Open.IsComponentOf X (H ⊓ M)) (h3X : 3 ∣ Nat.card X)
    (hO : (CFSG.pPrimeCore 3 H).map H.subtype ≤ M) :
    X ≤ Subgroup.centralizer (((CFSG.pPrimeCore 3 H).map H.subtype : Subgroup G) : Set G) := by
  let N := (CFSG.pPrimeCore 3 H).map H.subtype
  have hNH : N ≤ H := Subgroup.map_subtype_le _
  have hNA : N ≤ H ⊓ M := le_inf hNH hO
  have hsub : N.subgroupOf H = CFSG.pPrimeCore 3 H :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hNn : (N.subgroupOf (H ⊓ M)).Normal := by
    have : (N.subgroupOf H).Normal := hsub.symm ▸ inferInstance
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hNA).2
    exact inf_le_left.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hNH).1 inferInstance)
  rcases CFSG.CGT.Foote82.BranchAAux.le_or_commute_of_normal hX hNA hNn with hle | hcomm
  · have hcop : Nat.Coprime 3 (Nat.card N) := by
      rw [Subgroup.card_map_of_injective H.subtype_injective]
      exact CFSG.pPrimeCore_coprime_card
    exact False.elim ((Nat.prime_three.coprime_iff_not_dvd.1 hcop)
      (h3X.trans (Subgroup.card_dvd_of_le hle)))
  · exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm

private theorem not_le_of_component_of_uniqueSet_subgroup
    {G : Type} [Group G] [Finite G] {M H K E : Subgroup G}
    (hM : rankThreeIsMaxTwoLocal M) (hK : CFSG.Open.IsComponentOf K H)
    (hF : CFSG.fittingSubgroupOf H ≤ M)
    (hE : E ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet M)
    (hE3 : IsPGroup 3 E) (hEK : E ≤ K) (hHM : ¬ H ≤ M) : ¬ K ≤ M := by
  intro hKM
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hNE : Subgroup.normalizer (E : Set G) ≤ M :=
    CFSG.LocalAnalysis.RankThreeUC.normalizer_le_of_mem_uniqueSet hM hE
  have hLayerM : (CFSG.layer H).map H.subtype ≤ M := by
    rw [Subgroup.map_le_iff_le_comap, CFSG.layer.eq_sSup]
    refine sSup_le fun J hJ => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    have hK' := CFSG.CGT.Foote82.BranchAAux.isComponent_subgroupOf hK
    by_cases heq : J = K.subgroupOf H
    · rw [heq, Subgroup.map_subgroupOf_eq_of_le hK.1]
      exact hKM
    · have hcomm := (CFSG.LocalCores.distinct_components_commute hJ hK').resolve_left heq
      have hmap := congrArg (Subgroup.map H.subtype) hcomm
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hK.1, Subgroup.map_bot] at hmap
      exact ((Subgroup.commutator_eq_bot_iff_le_centralizer.1 hmap).trans
        (Subgroup.centralizer_le hEK)).trans ((Subgroup.centralizer_le_normalizer _).trans hNE)
  let Fstar := (CFSG.generalizedFitting H).map H.subtype
  have hFH : Fstar ≤ H := Subgroup.map_subtype_le _
  have hFM : Fstar ≤ M := by
    dsimp only [Fstar]
    rw [CFSG.generalizedFitting.eq_sup, Subgroup.map_sup]
    exact sup_le hF hLayerM
  have hEF : E ≤ Fstar := by
    have hKL := Subgroup.map_mono (f := H.subtype)
      (CFSG.LocalCores.component_le_layer (CFSG.CGT.Foote82.BranchAAux.isComponent_subgroupOf hK))
    rw [Subgroup.map_subgroupOf_eq_of_le hK.1] at hKL
    dsimp only [Fstar]
    rw [CFSG.generalizedFitting.eq_sup, Subgroup.map_sup]
    exact (hEK.trans hKL).trans le_sup_right
  have hFN : H ≤ Subgroup.normalizer (Fstar : Set G) := by
    have hsub : Fstar.subgroupOf H = CFSG.generalizedFitting H :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    have hnorm : (CFSG.generalizedFitting H).Normal :=
      (CFSG.LocalCores.generalized_fitting_characteristic (G := H)).2
    have : (Fstar.subgroupOf H).Normal := hsub.symm ▸ hnorm
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hFH).1 inferInstance
  obtain ⟨P, hEP⟩ := (hE3.comap_subtype (K := Fstar)).exists_le_sylow
  let S : Subgroup G := (P : Subgroup Fstar).map Fstar.subtype
  have hS : CFSG.ABGLocalTools.IsSylowOf 3 S Fstar := ⟨P, rfl⟩
  have hES : E ≤ S := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hEF]
    exact Subgroup.map_mono hEP
  have hSU := CFSG.LocalAnalysis.RankThreeUC.mem_uniqueSet_of_le hE hES (hS.le.trans hFM)
  have hNS := CFSG.LocalAnalysis.RankThreeUC.normalizer_le_of_mem_uniqueSet hM hSU
  exact hHM ((uc22p22t_frattini_sup hFH hFN hS).trans
    (sup_le hFM (inf_le_right.trans hNS)))

private theorem perfect_centralizer_has_unique_e9
    {G : Type} [Group G] [Finite G]
    (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (hPart : PartIAt S.M) {L : Subgroup G} (hL : L ∈ calC S.M)
    (hL3 : 2 ≤ CFSG.Open.pRank 3 L) {a : G}
    (hodd : Odd (orderOf a)) (hpr : (orderOf a).Prime) (haL : CentralizesBar a L)
    (hGamma : ∀ Q : Subgroup G, Q ≤ L → IsPGroup 3 Q →
      2 ≤ CFSG.Open.pRank 3 Q → rankThreeGamma 1 3 Q ≤ S.M) :
    let X := CFSG.Quasithin.perfectCore
      (L ⊓ centralizer ((zpowers a : Subgroup G) : Set G))
    2 ≤ CFSG.Open.pRank 3 X ∧ ∃ E : Subgroup G, E ≤ X ∧ IsElemAbelian 3 E ∧
      Nat.card E = 9 ∧ E ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet S.M := by
  dsimp only
  let X := CFSG.Quasithin.perfectCore
    (L ⊓ centralizer ((zpowers a : Subgroup G) : Set G))
  have hspec := rest15_perfectCore_centralizer_spec hL hodd hpr haL
  have hXL : X ≤ L := hspec.1.trans inf_le_left
  have hrX : 2 ≤ CFSG.Open.pRank 3 X := hL3.trans
    (UC6.R869S.pRank_le_of_sup_pCore hXL hspec.2.2.1 Nat.prime_three (by norm_num))
  obtain ⟨E, hEX, hEe, hEc⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank Nat.prime_three hrX
  have hEL : E ≤ L := hEX.trans hXL
  have hEM : E ≤ S.M := hEL.trans hL.1.le
  have hEr : 2 ≤ CFSG.Open.pRank 3 E := CFSG.SectionRank.le_pRank
    Nat.prime_three.one_lt le_rfl hEe hEc
  have hG := hGamma E hEL hEe.isPGroup hEr
  have hUnique := UC6.r6_3_dataOfSetup4 hS hU S hPart.1 3 Nat.prime_three (by norm_num)
    E hEM hEe hEc hG
  have hEU : E ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet S.M :=
    CFSG.LocalAnalysis.RankThreeUC.mem_uniqueSet_of_forall S.maxLocal hEM (fun N hN hEN => by
      have hmem : N ∈ calMOf E := ⟨hN, hEN⟩
      rw [hUnique] at hmem
      exact Set.mem_singleton_iff.mp hmem)
  exact ⟨hrX, E, hEX, hEe, by norm_num at hEc ⊢; exact hEc, hEU⟩

private theorem exists_component_not_le_of_perfect_centralizer_of_schreier
    {G : Type} [Group G] [Finite G]
    (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (hPart : PartIAt S.M) {L : Subgroup G} (hL : L ∈ calC S.M)
    (hL3 : 2 ≤ CFSG.Open.pRank 3 L) {a : G}
    (hodd : Odd (orderOf a)) (hpr : (orderOf a).Prime) (haL : CentralizesBar a L)
    (hGamma : ∀ Q : Subgroup G, Q ≤ L → IsPGroup 3 Q →
      2 ≤ CFSG.Open.pRank 3 Q → rankThreeGamma 1 3 Q ≤ S.M)
    {H : Subgroup G}
    (hCH : L ⊓ centralizer ((zpowers a : Subgroup G) : Set G) ≤ H)
    (hHM : ¬ H ≤ S.M) (hHr : CFSG.Open.pRank 3 H ≤ 3)
    (hO3' : relPPrimeCore 3 H ≤ S.M) (hF : CFSG.fittingSubgroupOf H ≤ S.M)
    (hInter : pCoreOf 2 (H ⊓ S.M) = ⊥)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections H) :
    ∃ K : Subgroup G, CFSG.Open.IsComponentOf K H ∧
      CFSG.Quasithin.perfectCore
        (L ⊓ centralizer ((zpowers a : Subgroup G) : Set G)) ≤ K ∧ ¬ K ≤ S.M := by
  let X := CFSG.Quasithin.perfectCore
    (L ⊓ centralizer ((zpowers a : Subgroup G) : Set G))
  have hspec := rest15_perfectCore_centralizer_spec hL hodd hpr haL
  have hXcomp : CFSG.Open.IsComponentOf X (H ⊓ S.M) :=
    isComponentOf_inf_of_sup_pCore_of_pCore_eq_bot hL
      (hspec.1.trans inf_le_left) (hspec.1.trans hCH) hspec.2.2.1 hspec.2.2.2 hInter
  obtain ⟨_, E, hEX, hEe, hEc, hEU⟩ :=
    perfect_centralizer_has_unique_e9 hS hU S hPart hL hL3 hodd hpr haL hGamma
  have hXH : X ≤ H := hXcomp.1.trans inf_le_left
  have h3X : 3 ∣ Nat.card X := by
    have h3E : 3 ∣ Nat.card E := by rw [hEc]; norm_num
    exact h3E.trans (Subgroup.card_dvd_of_le hEX)
  have hO : (CFSG.pPrimeCore 3 H).map H.subtype ≤ S.M := by
    rwa [CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_eq_map
      Nat.prime_three H] at hO3'
  have hXO := component_centralizes_three_primeCore_of_le hXcomp h3X hO
  have hXF := component_centralizes_fitting_of_le hXcomp hF
  let X' := X.subgroupOf H
  let A := (H ⊓ S.M).subgroupOf H
  have hX' : CFSG.Open.IsComponentOf X' A := by
    refine ⟨fun x hx => hXcomp.1 hx, ?_, ?_⟩
    · have h := hXcomp.2.1.comap H.subtype
      exact h
    · exact CFSG.Open.IsQuasisimple.of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe hXH) hXcomp.2.2
  have h3X' : 3 ∣ Nat.card X' := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv]
  have hHr' : CFSG.Open.pRank 3 (⊤ : Subgroup H) ≤ 3 := by
    rwa [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup H]
  have hXF' : X' ≤ Subgroup.centralizer (CFSG.fittingSubgroup H : Set H) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hXF hx) f
      (Subgroup.mem_map_of_mem H.subtype hf))
  have hXO' : X' ≤ Subgroup.centralizer (CFSG.pPrimeCore 3 H : Set H) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hXO hx) f
      (Subgroup.mem_map_of_mem H.subtype hf))
  obtain ⟨P, hEP⟩ := (hEe.isPGroup.comap_subtype (K := H)).exists_le_sylow
  have hEPG : E ≤ (P : Subgroup H).map H.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le (hEX.trans hXH)]
    exact Subgroup.map_mono hEP
  have hPM := PartOne.Section9.le_of_mem_uniqueSet_of_isPGroup S.maxLocal hEU hEPG
    (P.isPGroup'.map H.subtype)
  have hPA : (P : Subgroup H) ≤ A := fun x hx => ⟨x.2, hPM (Subgroup.mem_map_of_mem H.subtype hx)⟩
  obtain ⟨K, hK, hXK⟩ := exists_component_containing_of_sylow_le hX' h3X' hHr' hSch hXF' hXO' P hPA
  let K' := K.map H.subtype
  have hK' : CFSG.Open.IsComponentOf K' H := by
    refine ⟨Subgroup.map_subtype_le _, ?_, ?_⟩
    · have h := ((CFSG.isComponent_iff_open K).1 hK).2.1.map H.subtype
      simpa only [Subgroup.map_top, Subgroup.range_subtype] using h
    · exact CFSG.Open.IsQuasisimple.of_mulEquiv
        (Subgroup.equivMapOfInjective K H.subtype H.subtype_injective).symm
        ((CFSG.isComponent_iff_open K).1 hK).2.2
  have hXK' : X ≤ K' := by
    have h := Subgroup.map_mono (f := H.subtype) hXK
    rwa [Subgroup.map_subgroupOf_eq_of_le hXH] at h
  exact ⟨K', hK', hXK', not_le_of_component_of_uniqueSet_subgroup S.maxLocal hK' hF
    hEU hEe.isPGroup (hEX.trans hXK') hHM⟩

section ActualSchreier

theorem rest15_exists_component_not_le_of_perfect_centralizer
    {G : Type} [Group G] [Finite G]
    (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (hPart : PartIAt S.M)
    {L : Subgroup G} (hL : L ∈ calC S.M)
    (hL3 : 2 ≤ CFSG.Open.pRank 3 L)
    {a : G} (hodd : Odd (orderOf a)) (hpr : (orderOf a).Prime)
    (haL : CentralizesBar a L)
    (hGamma : ∀ Q : Subgroup G, Q ≤ L → IsPGroup 3 Q →
      2 ≤ CFSG.Open.pRank 3 Q → rankThreeGamma 1 3 Q ≤ S.M)
    {H : Subgroup G}
    (hCH : L ⊓ centralizer ((zpowers a : Subgroup G) : Set G) ≤ H)
    (hHtop : H ≠ ⊤) (hHM : ¬ H ≤ S.M)
    (hHr : CFSG.Open.pRank 3 H ≤ 3)
    (hO3' : relPPrimeCore 3 H ≤ S.M)
    (hF : CFSG.fittingSubgroupOf H ≤ S.M)
    (hInter : pCoreOf 2 (H ⊓ S.M) = ⊥)
    (_hModel :
      let X := CFSG.Quasithin.perfectCore
        (L ⊓ centralizer ((zpowers a : Subgroup G) : Set G))
      IsSL3 (Bar2 X) 2 ∨ IsSU3 (Bar2 X) 3) :
    ∃ K : Subgroup G, CFSG.Open.IsComponentOf K H ∧
      CFSG.Quasithin.perfectCore
        (L ⊓ centralizer ((zpowers a : Subgroup G) : Set G)) ≤ K ∧ ¬ K ≤ S.M := by
  have hSch : CFSG.ComponentClassification.LBalance.SchreierSections H :=
    (CFSG.LocalAnalysis.RankThreeUC.S15.kSch_of_catalog CFSG.AGLEmbedding.kFactCatalogSchreier).schreierSections
      (hS.kProper.isKGroup H hHtop)
  exact exists_component_not_le_of_perfect_centralizer_of_schreier hS hU S hPart hL hL3
    hodd hpr haL hGamma hCH hHM hHr hO3' hF hInter hSch

end ActualSchreier

end CFSG.LocalAnalysis.UniquenessCase.UC22

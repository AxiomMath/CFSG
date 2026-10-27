module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandStructTags
public import CFSG.LocalAnalysis.StandardType.GGLinearFusionCyclic
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotInvolutionCentralizerOTwo
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTorus
public import CFSG.RankThree.PartOne.Q1327T.Perm3
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.SeitzReduction.LinearPilot Matrix

namespace RCSPSL

variable {m : ℕ} {F : Type} [Field F] {G : Type} [Group G]

theorem mem_centralizer_of_map [CharP F 2] (hm : 1 ≤ m)
    {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F))
    {B : SpecialLinearGroup (Fin (m + 1)) F}
    (h : ψ B ∈ Subgroup.centralizer {ψ (ggInvSL (m + 1) 1 F)}) :
    B ∈ Subgroup.centralizer {ggInvSL (m + 1) 1 F} := by
  set T := ggInvSL (m + 1) 1 F with hTdef
  have hT : T * T = 1 := ggInvSL_mul_self (by omega)
  rw [Subgroup.mem_centralizer_singleton_iff] at h ⊢
  set c := B * T * B⁻¹ with hc
  set z := c * T⁻¹ with hz
  have h1 : ψ c = ψ T := by
    rw [hc, map_mul, map_mul, map_inv, h, mul_inv_cancel_right]
  have hzc : z ∈ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F) :=
    hker (by rw [MonoidHom.mem_ker, hz, map_mul, h1, map_inv, mul_inv_cancel])
  have hc2 : c * c = 1 := by
    rw [hc, show B * T * B⁻¹ * (B * T * B⁻¹) = B * (T * T) * B⁻¹ by group, hT, mul_one,
      mul_inv_cancel]
  have hcz : c = z * T := by rw [hz, inv_mul_cancel_right]
  have hz2 : z ^ 2 = 1 := by
    have hzT : T * z = z * T := Subgroup.mem_center_iff.mp hzc T
    calc z ^ 2 = z * z * (T * T) := by rw [hT, mul_one, pow_two]
      _ = z * (T * z) * T := by rw [hzT]; group
      _ = c * c := by rw [hcz]; group
      _ = 1 := hc2
  have hz1 : z = 1 := eq_one_of_mem_center_of_sq_eq_one hzc hz2
  have hcT : c = T := by rw [hcz, hz1, one_mul]
  calc B * T = (B * T * B⁻¹) * B := by group
    _ = T * B := by rw [← hc, hcT]

theorem range_inf_centralizer [CharP F 2] (hm : 1 ≤ m)
    (ψ : SpecialLinearGroup (Fin (m + 1)) F →* G)
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F)) :
    ψ.range ⊓ Subgroup.centralizer {ψ (ggInvSL (m + 1) 1 F)} =
      (Subgroup.centralizer {ggInvSL (m + 1) 1 F}).map ψ := by
  apply le_antisymm
  · rintro _ ⟨⟨B, rfl⟩, hB⟩
    exact ⟨B, mem_centralizer_of_map hm hker hB, rfl⟩
  · rintro _ ⟨B, hB, rfl⟩
    refine ⟨⟨B, rfl⟩, ?_⟩
    have hB' : B ∈ Subgroup.centralizer {ggInvSL (m + 1) 1 F} := hB
    rw [Subgroup.mem_centralizer_singleton_iff] at hB'
    show ψ B ∈ Subgroup.centralizer {ψ (ggInvSL (m + 1) 1 F)}
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, hB', map_mul]

theorem pow_mem_core [Fintype F] (hm : 1 ≤ m) {B : SpecialLinearGroup (Fin (m + 1)) F}
    (hB : B ∈ Subgroup.centralizer {(LinFusion.ggTransPlacement hm).mat F}) :
    B ^ (Fintype.card F - 1) ∈ (LinFusion.ggTransPlacement hm).core F := by
  set P := LinFusion.ggTransPlacement hm with hP
  have hBp : B ∈ P.parabolic F := P.centralizer_le_parabolic hB
  set b : P.parabolic F := ⟨B, hBp⟩ with hb
  have hunit : ∀ φ : P.parabolic F →* F, φ b ^ (Fintype.card F - 1) = 1 := by
    intro φ
    have hne : φ b ≠ 0 := by
      intro h0
      have h1 : φ b * φ b⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
      rw [h0, zero_mul] at h1
      exact zero_ne_one h1
    exact FiniteField.pow_card_sub_one_eq_one _ hne
  have h0 : P.detU F (b ^ (Fintype.card F - 1)) = 1 := by rw [map_pow]; exact hunit _
  have h1 : P.detFree F (b ^ (Fintype.card F - 1)) = 1 := by rw [map_pow]; exact hunit _
  exact P.mem_core_of_det (pow_mem hB _) h0 h1

theorem leviOne_eq_bot {n : ℕ} (P : InvPlacement n 1) : P.leviOne F = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨a, rfl⟩
  rw [LinFusion.eq_one_of_specialLinearGroup_fin_one a, map_one]
  exact one_mem _

theorem radical_isPGroup [CharP F 2] (hm : 1 ≤ m) :
    IsPGroup 2 ((LinFusion.ggTransPlacement hm).radical F) := by
  intro x
  refine ⟨2, Subtype.ext ?_⟩
  have h := (LinFusion.ggTransPlacement hm).radical_pow_four x.2
  simpa using h

theorem oTwoPrime_eq [Finite F] [CharP F 2] (hm : 1 ≤ m)
    (ψ : SpecialLinearGroup (Fin (m + 1)) F →* G)
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F)) :
    ggOTwoPrime (ψ.range ⊓ Subgroup.centralizer {ψ (ggInvSL (m + 1) 1 F)}) =
      ((LinFusion.ggTransPlacement hm).core F).map ψ := by
  have : Fintype F := Fintype.ofFinite F
  set P := LinFusion.ggTransPlacement hm with hP
  have hmat : P.mat F = ggInvSL (m + 1) 1 F := LinFusion.ggTransPlacement_mat hm
  rw [range_inf_centralizer hm ψ hker]
  apply le_antisymm
  · rw [ggOTwoPrime, Subgroup.closure_le]
    rintro _ ⟨⟨B, hB, rfl⟩, k, hk⟩
    have hB' : B ∈ Subgroup.centralizer {P.mat F} := by rw [hmat]; exact hB
    have hBN := pow_mem_core hm hB'
    obtain ⟨n, -, hcard⟩ := FiniteField.card F 2
    have hodd : Odd (Fintype.card F - 1) := by
      rw [hcard]
      have hn : (n : ℕ) ≠ 0 := n.ne_zero
      exact Nat.Even.sub_odd (Nat.one_le_two_pow) ((Nat.even_pow).mpr ⟨even_two, hn⟩) odd_one
    have hcop : (Fintype.card F - 1).Coprime (orderOf (ψ B)) := by
      refine Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hk) ?_
      exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)
    obtain ⟨u, hu⟩ := exists_pow_eq_self_of_coprime hcop
    rw [SetLike.mem_coe, ← hu, ← map_pow, ← map_pow]
    exact ⟨_, pow_mem hBN u, rfl⟩
  · calc (P.core F).map ψ ≤ (ggOTwoPrime (Subgroup.centralizer {P.mat F})).map ψ :=
          Subgroup.map_mono (LinFusion.core_le_ggOTwoPrime P)
      _ ≤ ggOTwoPrime ((Subgroup.centralizer {P.mat F}).map ψ) :=
          LinFusion.map_ggOTwoPrime_le ψ _
      _ = ggOTwoPrime ((Subgroup.centralizer {ggInvSL (m + 1) 1 F}).map ψ) := by rw [hmat]

theorem isQuasisimple_free [Finite F] {n k : ℕ} (P : InvPlacement n k) (hJ : 2 ≤ P.free.card)
    (h : 3 ≤ P.free.card ∨ 4 ≤ Nat.card F) :
    CFSG.IsQuasisimple (SpecialLinearGroup P.free F) := by
  have hc : Fintype.card ↥P.free = P.free.card := Fintype.card_coe P.free
  have h1 := isQuasisimple_specialLinearGroup_of_le (K := F) (m := P.free.card) hJ h
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (reindexSpecialLinear (K := F) (Fintype.equivFinOfCardEq hc).symm) h1

theorem X_eq [Finite F] [CharP F 2] (hm : 1 ≤ m)
    (ψ : SpecialLinearGroup (Fin (m + 1)) F →* G)
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F)) :
    ggRCSX ψ.range (ψ (ggInvSL (m + 1) 1 F)) = ((LinFusion.ggTransPlacement hm).core F).map ψ :=
  oTwoPrime_eq hm ψ hker

theorem blockEmbed_mem_X [Finite F] [CharP F 2] (hm : 1 ≤ m)
    (ψ : SpecialLinearGroup (Fin (m + 1)) F →* G)
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F))
    (d : SpecialLinearGroup (LinFusion.ggTransPlacement hm).free F) :
    ψ (blockEmbed (LinFusion.ggTransPlacement hm).free d) ∈
      ggRCSX ψ.range (ψ (ggInvSL (m + 1) 1 F)) := by
  rw [X_eq hm ψ hker]
  refine ⟨_, (LinFusion.ggTransPlacement hm).free_le_core ?_, rfl⟩
  rw [← range_blockEmbed]
  exact ⟨d, rfl⟩

theorem radical_le_X [Finite F] [CharP F 2] (hm : 1 ≤ m)
    (ψ : SpecialLinearGroup (Fin (m + 1)) F →* G)
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F)) :
    ((LinFusion.ggTransPlacement hm).radical F).map ψ ≤
      ggRCSX ψ.range (ψ (ggInvSL (m + 1) 1 F)) := by
  rw [X_eq hm ψ hker]
  exact Subgroup.map_mono (LinFusion.ggTransPlacement hm).radical_le_core

theorem radical_normal_X [Finite F] [CharP F 2] (hm : 1 ≤ m)
    (ψ : SpecialLinearGroup (Fin (m + 1)) F →* G)
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F)) :
    ((((LinFusion.ggTransPlacement hm).radical F).map ψ).subgroupOf
      (ggRCSX ψ.range (ψ (ggInvSL (m + 1) 1 F)))).Normal := by
  set P := LinFusion.ggTransPlacement hm
  have hcorepar : P.core F ≤ P.parabolic F :=
    P.core_le_centralizer.trans P.centralizer_le_parabolic
  rw [Subgroup.normal_subgroupOf_iff (radical_le_X hm ψ hker)]
  intro a b ha hb
  rw [X_eq hm ψ hker] at hb
  obtain ⟨c, hc, rfl⟩ := hb
  obtain ⟨r, hr, rfl⟩ := ha
  exact ⟨c * r * c⁻¹, P.conj_mem_radical (hcorepar hc) hr, by rw [map_mul, map_mul, map_inv]⟩

noncomputable def freeQuotHom [Finite F] [CharP F 2] (hm : 1 ≤ m)
    (ψ : SpecialLinearGroup (Fin (m + 1)) F →* G)
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F))
    [((((LinFusion.ggTransPlacement hm).radical F).map ψ).subgroupOf
      (ggRCSX ψ.range (ψ (ggInvSL (m + 1) 1 F)))).Normal] :
    SpecialLinearGroup (LinFusion.ggTransPlacement hm).free F →*
      ↥(ggRCSX ψ.range (ψ (ggInvSL (m + 1) 1 F))) ⧸
        (((LinFusion.ggTransPlacement hm).radical F).map ψ).subgroupOf
          (ggRCSX ψ.range (ψ (ggInvSL (m + 1) 1 F))) :=
  (QuotientGroup.mk' _).comp ((ψ.comp (blockEmbed _)).codRestrict _ (blockEmbed_mem_X hm ψ hker))

theorem freeQuotHom_surjective [Finite F] [CharP F 2] (hm : 1 ≤ m)
    (ψ : SpecialLinearGroup (Fin (m + 1)) F →* G)
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F))
    [((((LinFusion.ggTransPlacement hm).radical F).map ψ).subgroupOf
      (ggRCSX ψ.range (ψ (ggInvSL (m + 1) 1 F)))).Normal] :
    Function.Surjective (freeQuotHom hm ψ hker) := by
  set P := LinFusion.ggTransPlacement hm with hP
  set f := freeQuotHom hm ψ hker with hf
  have hQX := radical_le_X hm ψ hker
  have key : ggRCSX ψ.range (ψ (ggInvSL (m + 1) 1 F)) ≤
      (f.range.comap (QuotientGroup.mk' _)).map
        (ggRCSX ψ.range (ψ (ggInvSL (m + 1) 1 F))).subtype := by
    refine (X_eq hm ψ hker).le.trans ?_
    rw [Subgroup.map_le_iff_le_comap, InvPlacement.core, leviOne_eq_bot P, bot_sup_eq]
    refine sup_le ?_ ?_
    · intro c hc
      refine ⟨⟨ψ c, hQX ⟨c, hc, rfl⟩⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      have h1 : QuotientGroup.mk' ((((LinFusion.ggTransPlacement hm).radical F).map ψ).subgroupOf
          (ggRCSX ψ.range (ψ (ggInvSL (m + 1) 1 F)))) ⟨ψ c, hQX ⟨c, hc, rfl⟩⟩ = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        exact ⟨c, hc, rfl⟩
      rw [h1]
      exact one_mem _
    · rw [← range_blockEmbed]
      rintro _ ⟨d, rfl⟩
      exact ⟨_, ⟨d, rfl⟩, rfl⟩
  intro z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ z
  obtain ⟨x', hx', hxx⟩ := key x.2
  have hx'x : x' = x := Subtype.ext hxx
  rw [← hx'x]
  exact hx'

theorem mem_of_freeQuotHom_eq_one [Finite F] [CharP F 2] (hm : 1 ≤ m)
    (ψ : SpecialLinearGroup (Fin (m + 1)) F →* G)
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F))
    [((((LinFusion.ggTransPlacement hm).radical F).map ψ).subgroupOf
      (ggRCSX ψ.range (ψ (ggInvSL (m + 1) 1 F)))).Normal]
    {d : SpecialLinearGroup (LinFusion.ggTransPlacement hm).free F}
    (hd : freeQuotHom hm ψ hker d = 1) :
    ψ (blockEmbed (LinFusion.ggTransPlacement hm).free d) ∈
      ((LinFusion.ggTransPlacement hm).radical F).map ψ := by
  have h1 := (QuotientGroup.eq_one_iff _).mp hd
  exact Subgroup.mem_subgroupOf.mp h1

theorem derivedAt_of_transvection [Finite G] [Finite F] [CharP F 2] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hm : 2 ≤ m) (hmq : m = 2 ∨ 4 ≤ m ∨ 4 ≤ Nat.card F)
    (ψ : SpecialLinearGroup (Fin (m + 1)) F →* G)
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F)) {r : G}
    (hr : r = ψ (ggInvSL (m + 1) 1 F)) : GGRootCentDerivedAt p ψ.range r := by
  subst hr
  have hm1 : 1 ≤ m := by omega
  set P := LinFusion.ggTransPlacement hm1 with hP
  have hX : ggRCSX ψ.range (ψ (ggInvSL (m + 1) 1 F)) = (P.core F).map ψ := oTwoPrime_eq hm1 ψ hker
  have hcardJ : P.free.card = m - 1 := by rw [P.card_free]; omega
  have hR2 : IsPGroup 2 ((P.radical F).map ψ) := (radical_isPGroup hm1).map ψ
  have : Subsingleton (SpecialLinearGroup (Fin 1) F) :=
    ⟨fun a b => by rw [LinFusion.eq_one_of_specialLinearGroup_fin_one a,
      LinFusion.eq_one_of_specialLinearGroup_fin_one b]⟩
  by_cases hm2 : m = 2
  ·
    left
    have hc : Fintype.card ↥P.free = 1 := by rw [Fintype.card_coe, hcardJ, hm2]
    have : Subsingleton (SpecialLinearGroup P.free F) :=
      (reindexSpecialLinear (K := F) (Fintype.equivFinOfCardEq hc)).injective.subsingleton
    have hJ : blockSpecialLinear (K := F) P.free = ⊥ := by
      rw [← range_blockEmbed, eq_bot_iff]
      rintro _ ⟨a, rfl⟩
      rw [Subsingleton.elim a 1, map_one]
      exact one_mem _
    have hcore : P.core F = P.radical F := by
      rw [InvPlacement.core, leviOne_eq_bot P, hJ, sup_bot_eq, sup_bot_eq]
    intro y hy hyp
    rw [hX, hcore] at hy
    exact ggRCS_eq_one_of_mem_two hp hp2 hR2 hy hyp
  have hJ2 : 2 ≤ P.free.card := by omega
  have hSLJ : CFSG.IsQuasisimple (SpecialLinearGroup P.free F) := by
    refine isQuasisimple_free P hJ2 ?_
    rcases hmq with h | h | h
    · exact absurd h hm2
    · left; omega
    · right; exact h
  have : Group.IsPerfect (SpecialLinearGroup P.free F) := hSLJ.1
  have hcperf : ⁅P.core F, P.core F⁆ = P.core F := P.commutator_core hJ2
  have hXperf : ⁅ggRCSX ψ.range (ψ (ggInvSL (m + 1) 1 F)),
      ggRCSX ψ.range (ψ (ggInvSL (m + 1) 1 F))⁆ = ggRCSX ψ.range (ψ (ggInvSL (m + 1) 1 F)) := by
    rw [hX, ← Subgroup.map_commutator, hcperf]
  have hQn := radical_normal_X hm1 ψ hker
  refine ggRootCentDerivedAt_of_perfect hp hXperf (radical_le_X hm1 ψ hker) hR2 fun hpX => ?_
  set f := freeQuotHom hm1 ψ hker with hf
  have hfs : Function.Surjective f := freeQuotHom_surjective hm1 ψ hker
  have hfker : f.ker ≤ Subgroup.center (SpecialLinearGroup P.free F) := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hSLJ (MonoidHom.normal_ker f) with h | h
    · exfalso
      have hall : ∀ x : ↥(ggRCSX ψ.range (ψ (ggInvSL (m + 1) 1 F))),
          (x : G) ∈ (P.radical F).map ψ := by
        intro x
        obtain ⟨d, hd⟩ := hfs (QuotientGroup.mk x)
        have hd1 : f d = 1 := by
          rw [← MonoidHom.mem_ker, h]
          exact Subgroup.mem_top d
        rw [hd1] at hd
        exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff x).mp hd.symm)
      have hX2 : IsPGroup 2 (ggRCSX ψ.range (ψ (ggInvSL (m + 1) 1 F))) := by
        intro x
        obtain ⟨k, hk⟩ := hR2 ⟨x, hall x⟩
        exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
      exact ggNot_dvd_card_of_isPGroup_two hp hp2 hX2 hpX
    · exact h
  exact CFSG.LocalCores.isQuasisimple_of_surjective hSLJ f hfs hfker

theorem exists_conj [Finite F] [CharP F 2] (hm : 1 ≤ m)
    (ψ : SpecialLinearGroup (Fin (m + 1)) F →* G)
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F)) {t : StatedLieTag}
    {r : G} (hr : GGRootInvolution (SpecialLinear.rootDatum m F) t ψ r) :
    ∃ ψ' : SpecialLinearGroup (Fin (m + 1)) F →* G, ψ'.range = ψ.range ∧
      ψ'.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F) ∧
      r = ψ' (ggInvSL (m + 1) 1 F) := by
  obtain ⟨hr2, γ, -, u₀, hru⟩ := hr
  obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hru
  have hx1 : x ≠ 1 := by
    rintro rfl
    simp at hr2
  obtain ⟨i, j, hij, c, hc, rfl⟩ := exists_transvection_of_mem_rootGroup hx hx1
  obtain ⟨g, hg⟩ := exists_conj_transvection_eq hm hij hc
  set h := u₀ * g⁻¹ with hh
  refine ⟨ψ.comp (MulAut.conj h).toMonoidHom, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulEquiv.surjective _),
      ← MonoidHom.range_eq_map]
  · intro v hv
    have hz : h * v * h⁻¹ ∈ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F) := hker hv
    have h1 := (inferInstance : (Subgroup.center
      (SpecialLinearGroup (Fin (m + 1)) F)).Normal).conj_mem _ hz h⁻¹
    rwa [inv_inv, show h⁻¹ * (h * v * h⁻¹) * h = v by group] at h1
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hg, hh]
    congr 1
    group

@[expose] def rhoTwo (F : Type) [Field F] [CharP F 2] : SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, 1; 1, 1], by
    rw [Matrix.det_fin_two_of]
    have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
    linear_combination -h2⟩

@[expose] def sigTwo (F : Type) [Field F] [CharP F 2] : SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, 1; 1, 0], by
    rw [Matrix.det_fin_two_of]
    have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
    linear_combination -h2⟩

theorem nonempty_sl2_equiv_perm [Finite F] [CharP F 2] (hF : Nat.card F = 2) :
    Nonempty (SpecialLinearGroup (Fin 2) F ≃* Equiv.Perm (Fin 3)) := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have h11 : (1 : F) + 1 = 0 := by linear_combination h2
  have hn1 : (-1 : F) = 1 := by linear_combination -h2
  have hr : ((rhoTwo F : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![0, 1; 1, 1] := rfl
  have hs : ((sigTwo F : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![0, 1; 1, 0] := rfl
  refine CFSG.RankThree.PartOne.Q1327T.nonempty_mulEquiv_perm_three (rhoTwo F) (sigTwo F)
    ?_ ?_ ?_ ?_ ?_ ?_
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hr, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, h11]
  · intro h
    have := congrArg (fun A : SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp only [hr, Matrix.SpecialLinearGroup.coe_one] at this
    simp at this
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, hs, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  · intro h
    have := congrArg (fun A : SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp only [hs, Matrix.SpecialLinearGroup.coe_one] at this
    simp at this
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv, Matrix.SpecialLinearGroup.coe_inv, hs, hr,
      Matrix.adjugate_fin_two, Matrix.adjugate_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hn1]
  · rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF]
    norm_num

theorem center_eq_bot_four [CharP F 2] :
    Subgroup.center (SpecialLinearGroup (Fin 4) F) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨c, hc4, hcz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  rw [Fintype.card_fin] at hc4
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have h0 : (c - 1) ^ 4 = 0 := by
    linear_combination hc4 + (-2 * c ^ 3 + 3 * c ^ 2 - 2 * c + 1) * h2
  have hc1 : c = 1 := by
    have := pow_eq_zero_iff (n := 4) (by norm_num) |>.mp h0
    linear_combination this
  rw [Subgroup.mem_bot]
  ext i j
  rw [← hcz, hc1, map_one, Matrix.SpecialLinearGroup.coe_one]

theorem derivedAt_fourTwo [Finite G] [Finite F] [CharP F 2] (hF : Nat.card F = 2) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (ψ : SpecialLinearGroup (Fin (3 + 1)) F →* G)
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (3 + 1)) F)) :
    GGRootCentDerivedAt p ψ.range (ψ (ggInvSL (3 + 1) 1 F)) := by
  have hm1 : 1 ≤ 3 := by norm_num
  set P := LinFusion.ggTransPlacement hm1 with hP
  have hcardJ : P.free.card = 2 := by rw [P.card_free]
  have hR2 : IsPGroup 2 ((P.radical F).map ψ) := (radical_isPGroup hm1).map ψ
  have hQn := radical_normal_X hm1 ψ hker
  set f := freeQuotHom hm1 ψ hker with hf
  have hfs : Function.Surjective f := freeQuotHom_surjective hm1 ψ hker
  have hcJ : Fintype.card ↥P.free = 2 := by rw [Fintype.card_coe, hcardJ]
  let eJ : SpecialLinearGroup P.free F ≃* SpecialLinearGroup (Fin 2) F :=
    reindexSpecialLinear (K := F) (Fintype.equivFinOfCardEq hcJ)
  have hcard6 : Nat.card (SpecialLinearGroup P.free F) = 6 := by
    rw [Nat.card_congr eJ.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF]
    norm_num
  by_cases hp3 : p = 3
  ·
    subst hp3
    refine Or.inr (Or.inr ⟨(P.radical F).map ψ, radical_le_X hm1 ψ hker, hR2, hQn, ?_⟩)
    intro _
    have hcen : Subgroup.center (SpecialLinearGroup (Fin (3 + 1)) F) = ⊥ := center_eq_bot_four
    have hinj : Function.Injective f := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro d hd
      obtain ⟨c, hcR, hcd⟩ := mem_of_freeQuotHom_eq_one hm1 ψ hker (MonoidHom.mem_ker.mp hd)
      have h2 : c⁻¹ * blockEmbed P.free d ∈ ψ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hcd, inv_mul_cancel]
      have h3 := hker h2
      rw [hcen, Subgroup.mem_bot] at h3
      have h4 : blockEmbed P.free d = c := (inv_mul_eq_one.mp h3).symm
      rw [Subgroup.mem_bot]
      ext a b
      have h5 : ((blockEmbed P.free d : SpecialLinearGroup (Fin (3 + 1)) F) :
          Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) a b = (d : Matrix P.free P.free F) a b := by
        rw [coe_blockEmbed, blockMatrix_apply, dite_eq_left_of_eq_true (eq_true ⟨a.2, b.2⟩)]
      have h6 : ((blockEmbed P.free d : SpecialLinearGroup (Fin (3 + 1)) F) :
          Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) a b =
            (1 : Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) a b := by
        rw [h4]
        exact hcR a b (by rw [P.mem_free.mp a.2, P.mem_free.mp b.2])
      rw [Matrix.SpecialLinearGroup.coe_one, ← h5, h6]
      by_cases hab : a = b
      · subst hab
        simp
      · rw [Matrix.one_apply_ne (fun h => hab (Subtype.ext h)), Matrix.one_apply_ne hab]
    obtain ⟨e3⟩ := nonempty_sl2_equiv_perm hF
    exact ⟨((MulEquiv.ofBijective f ⟨hinj, hfs⟩).symm.trans eJ).trans e3⟩
  ·
    left
    intro y hy hyp
    obtain ⟨d, hd⟩ := hfs (QuotientGroup.mk ⟨y, hy⟩)
    set z : ↥(ggRCSX ψ.range (ψ (ggInvSL (3 + 1) 1 F))) ⧸ ((P.radical F).map ψ).subgroupOf
      (ggRCSX ψ.range (ψ (ggInvSL (3 + 1) 1 F))) := QuotientGroup.mk ⟨y, hy⟩ with hz
    have h6 : z ^ 6 = 1 := by
      rw [← hd, ← map_pow, ← hcard6, pow_card_eq_one', map_one]
    have hpz : z ^ p = 1 := by
      rw [hz, ← QuotientGroup.mk_pow]
      have : (⟨y, hy⟩ : ↥(ggRCSX ψ.range (ψ (ggInvSL (3 + 1) 1 F)))) ^ p = 1 :=
        Subtype.ext (by simpa using hyp)
      rw [this, QuotientGroup.mk_one]
    have hcop : Nat.Coprime p 6 := by
      rw [show (6 : ℕ) = 2 * 3 by norm_num]
      exact Nat.Coprime.mul_right ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
        ((Nat.coprime_primes hp Nat.prime_three).mpr hp3)
    have h1 : orderOf z ∣ Nat.gcd p 6 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hpz) (orderOf_dvd_of_pow_eq_one h6)
    rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at h1
    have hyQ : y ∈ (P.radical F).map ψ :=
      Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)
    exact ggRCS_eq_one_of_mem_two hp hp2 hR2 hyQ hyp

end RCSPSL

section Tag

theorem ggRootCentDerivedTag_PSL : GGRootCentDerivedTag .PSL := by
  intro G _ _ p n f ψ hp hp2 hadm hrk hker _ _ r hr
  obtain ⟨-, -, hn, -⟩ := hadm
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 2 ≤ m := hrk
  obtain ⟨ψ', hrange, hker', hr'⟩ :=
    RCSPSL.exists_conj (F := GaloisField 2 f) (by omega) ψ hker hr
  have hR : ψ'.range = ψ.range := hrange
  rw [← hR]
  by_cases hcase : m = 2 ∨ 4 ≤ m ∨ 4 ≤ Nat.card (GaloisField 2 f)
  · exact RCSPSL.derivedAt_of_transvection hp hp2 hm hcase ψ' hker' hr'
  · push Not at hcase
    obtain ⟨h2, h4, hq⟩ := hcase
    obtain rfl : m = 3 := by omega
    have hF2 : Nat.card (GaloisField 2 f) = 2 := by
      have h1 : 1 < Nat.card (GaloisField 2 f) := Finite.one_lt_card
      have : Fintype (GaloisField 2 f) := Fintype.ofFinite _
      obtain ⟨k, -, hk⟩ := FiniteField.card (GaloisField 2 f) 2
      rw [Nat.card_eq_fintype_card] at h1 hq ⊢
      rw [hk] at h1 hq ⊢
      have hk1 : (k : ℕ) < 2 := by
        by_contra hk2
        push Not at hk2
        have : 2 ^ 2 ≤ 2 ^ (k : ℕ) := Nat.pow_le_pow_right (by norm_num) hk2
        omega
      have hk0 : (k : ℕ) ≠ 0 := k.ne_zero
      have : (k : ℕ) = 1 := by omega
      rw [this, pow_one]
    rw [hr']
    exact RCSPSL.derivedAt_fourTwo hF2 hp hp2 ψ' hker'

theorem ggRootCentSummandStructInput_of_nineTags (hPSU : GGRootCentDerivedTag .PSU)
    (hPSp : GGRootCentLayerTag .PSp) (hPlus : GGRootCentLayerTag .POmegaPlus)
    (hMinus : GGRootCentLayerTag .POmegaMinus) (hF4 : GGRootCentDerivedTag .F4)
    (hE6 : GGRootCentDerivedTag .E6) (hE7 : GGRootCentDerivedTag .E7)
    (hE8 : GGRootCentDerivedTag .E8) (hTwE6 : GGRootCentDerivedTag .twistedE6) :
    GGRootCentSummandStructInput :=
  ggRootCentSummandStructInput_of_layerTags ggRootCentDerivedTag_PSL hPSU hPSp hPlus hMinus hF4
    hE6 hE7 hE8 hTwE6

end Tag

end CFSG.StandardType

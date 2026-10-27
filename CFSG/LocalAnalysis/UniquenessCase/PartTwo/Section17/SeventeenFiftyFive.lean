module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1b
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Bar13
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeK1
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdRank
public import CFSG.Adapters.StatedSLPerfect
public import CFSG.Adapters.LieModelSimple
public import CFSG.Blueprint.LieModelAPI
public import CFSG.ClassicalInvolution.SubnormalClosure.Basic
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplectic
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08

variable {G : Type} [Group G] [Finite G]

theorem mem_uniqueSet_of_conjSetOf_eq_of_normalizer_le {M X : Subgroup G}
    (hM : Subgroup.normalizer (M : Set G) = M) (hXM : X ≤ M)
    (hNX : Subgroup.normalizer (X : Set G) ≤ M)
    (heq : conjSetOf (⊤ : Subgroup G) X ∩ {Y : Subgroup G | Y ≤ M} = conjSetOf M X) :
    X ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet M := by
  rw [← CFSG.LocalAnalysis.UniquenessCase.PartTwo.inU_iff_mem_uniqueSet]
  refine CFSG.LocalAnalysis.UniquenessCase.UC6.inU_of_normalizer_le_of_fusion hM hXM hNX ?_
  intro g hg
  have hmem : uniqueFourConj g X ∈
      conjSetOf (⊤ : Subgroup G) X ∩ {Y : Subgroup G | Y ≤ M} := by
    refine ⟨⟨g⁻¹, Subgroup.mem_top g⁻¹, ?_⟩, hg⟩
    simp [uniqueFourConj]
  rw [heq] at hmem
  obtain ⟨m, hm, hmeq⟩ := hmem
  refine ⟨m⁻¹, M.inv_mem hm, ?_⟩
  rw [hmeq]
  simp [uniqueFourConj]

theorem mem_of_map_eq_top_of_odd {H Q : Type} [Group H] [Group Q] (φ : H →* Q)
    (N : Subgroup H) [N.Normal] (hN : N.map φ = ⊤) (hker : IsPGroup 2 φ.ker)
    {g : H} (hg : Odd (orderOf g)) : g ∈ N := by
  obtain ⟨n, hn, hφn⟩ : ∃ n ∈ N, φ n = φ g := by
    have h : φ g ∈ N.map φ := by rw [hN]; trivial
    obtain ⟨n, hn, h'⟩ := h
    exact ⟨n, hn, h'⟩
  have hk : n⁻¹ * g ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hφn, inv_mul_cancel]
  obtain ⟨m, hm⟩ := hker ⟨n⁻¹ * g, hk⟩
  have hm' : (n⁻¹ * g) ^ 2 ^ m = 1 := by
    simpa using congrArg Subtype.val hm
  have hdvd1 : orderOf (n⁻¹ * g) ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm'
  have hmk : (QuotientGroup.mk g : H ⧸ N) = QuotientGroup.mk (n⁻¹ * g) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      (QuotientGroup.eq_one_iff n).mpr hn, inv_one, one_mul]
  have hdvd2 : orderOf (QuotientGroup.mk g : H ⧸ N) ∣ orderOf g :=
    orderOf_map_dvd (QuotientGroup.mk' N) g
  have hdvd3 : orderOf (QuotientGroup.mk g : H ⧸ N) ∣ 2 ^ m :=
    calc orderOf (QuotientGroup.mk g : H ⧸ N)
        = orderOf (QuotientGroup.mk (n⁻¹ * g) : H ⧸ N) := by rw [hmk]
      _ ∣ orderOf (n⁻¹ * g) := orderOf_map_dvd (QuotientGroup.mk' N) (n⁻¹ * g)
      _ ∣ 2 ^ m := hdvd1
  have hodd : Odd (orderOf (QuotientGroup.mk g : H ⧸ N)) := hg.of_dvd_nat hdvd2
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd3
  have hj0 : j = 0 := by
    rcases j with _ | j
    · rfl
    · exfalso
      apply (Nat.not_even_iff_odd.mpr hodd)
      rw [hj, pow_succ]
      exact even_iff_two_dvd.mpr (dvd_mul_left 2 (2 ^ j))
  have hone : orderOf (QuotientGroup.mk g : H ⧸ N) = 1 := by
    rw [hj, hj0]
    simp
  exact (QuotientGroup.eq_one_iff g).mp (orderOf_eq_one_iff.mp hone)

theorem isPerfect_bar2_of_isL2 {L : Subgroup G} {n : ℕ} (h : IsL2 (Bar2 L) n) :
    Group.IsPerfect (Bar2 L) := by
  obtain ⟨hadm, K, hfield, hfin, hKcard, ⟨e⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)
  letI := hfield
  letI := hfin
  have hn1 : 1 ≤ n := hadm.2.1
  have hnne1 : n ≠ 1 := by
    intro hn
    exact hadm.2.2.2.1 (by simp [hn])
  have hn2 : 2 ≤ n := by omega
  have hK4 : 4 ≤ Nat.card K := by
    rw [hKcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  have hperfSL : Group.IsPerfect ↥(CFSG.Open.StatedSL 2 K) :=
    CFSG.Open.StatedAPI.isPerfect_statedSL_two_of_four_le_card (K := K) hK4
  have hperfProj : Group.IsPerfect (CFSG.Open.StatedProj (CFSG.Open.StatedSL 2 K)) :=
    Group.IsPerfect.ofSurjective
      (f := QuotientGroup.mk'
        ((CFSG.Open.StatedScalars (Fin 2) K).subgroupOf (CFSG.Open.StatedSL 2 K)))
      (QuotientGroup.mk'_surjective _)
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem isPerfect_bar2_of_isSz {L : Subgroup G} {n : ℕ} (h : IsSz (Bar2 L) n) :
    Group.IsPerfect (Bar2 L) := by
  have hsz : CFSG.Blueprint.SuzukiModel (Bar2 L) 2 n :=
    (CFSG.Blueprint.LieModel.suzukiModel h).2
  obtain ⟨a, ha, ⟨e⟩⟩ :=
    CFSG.LieType.Simplicity.exists_mulEquiv_suzukiMatrixGroup_of_suzukiModel hsz
  have hperfSz : Group.IsPerfect (CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup a) :=
    Group.isPerfect_def.mpr
      (CFSG.ShultStronglyClosedTI.OddPrimeInverters.suzuki_commutator_eq_top a ha)
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem isPerfect_bar2_of_isL2_or_isSz {L : Subgroup G} {n : ℕ}
    (h : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) : Group.IsPerfect (Bar2 L) := by
  rcases h with h | h
  · exact isPerfect_bar2_of_isL2 h
  · exact isPerfect_bar2_of_isSz h

theorem isSimpleGroup_bar2_of_isL2_or_isSz {L : Subgroup G} {n : ℕ}
    (h : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) : IsSimpleGroup (Bar2 L) := by
  rcases h with h | h
  · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
  · exact (CFSG.LieType.Simplicity.fam_2b2_simplicity (Bar2 L) 2 n
      (CFSG.Blueprint.LieModel.suzukiModel h).2).2

theorem perfectCore_of_isL2_or_isSz_1755 {D : Data G} {L : Subgroup G} {n : ℕ}
    (hLM : L ≤ D.M) (hLN : (L.subgroupOf D.M).Normal)
    (hshape : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) :
    CFSG.Quasithin.perfectCore L ∈ calC D.M ∧
      D.M ≤ Subgroup.normalizer (CFSG.Quasithin.perfectCore L : Set G) ∧
      (IsL2 (Bar2 (CFSG.Quasithin.perfectCore L)) n ∨
        IsSz (Bar2 (CFSG.Quasithin.perfectCore L)) n) ∧
      ((CFSG.Quasithin.perfectCore L).subgroupOf L).map
        (QuotientGroup.mk' (pCore 2 ↥L)) = ⊤ := by
  have hperfBar : Group.IsPerfect (Bar2 L) := isPerfect_bar2_of_isL2_or_isSz hshape
  have hsimpleBar : IsSimpleGroup (Bar2 L) := isSimpleGroup_bar2_of_isL2_or_isSz hshape
  have hquasiBar : CFSG.Open.IsQuasisimple (Bar2 L) :=
    CFSG.ComponentClassification.Quasisimple.simple_of_perfect (Bar2 L)
  have hquasiTop : CFSG.Open.IsQuasisimple (↥(⊤ : Subgroup (Bar2 L))) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv Subgroup.topEquiv hquasiBar
  have hCtop : CFSG.Open.IsComponentOf (⊤ : Subgroup (Bar2 L)) ⊤ :=
    ⟨le_rfl, CFSG.Open.IsSubnormal.refl ⊤, hquasiTop⟩
  obtain ⟨K, hKL, hKsubL, hKp, hKq, ⟨e⟩, hKmap⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.s15_Three_core_of_component hCtop
  have hsup : (⊤ : Subgroup ↥L) = K.subgroupOf L ⊔ pCore 2 ↥L := by
    apply le_antisymm
    · intro x _
      let π : ↥L →* Bar2 L := QuotientGroup.mk' (pCore 2 ↥L)
      have hx : π x ∈ (K.subgroupOf L).map π := by rw [hKmap]; trivial
      obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.mp hx
      have hq : k⁻¹ * x ∈ pCore 2 ↥L := (QuotientGroup.eq).mp hkx
      have hxeq : x = k * (k⁻¹ * x) := by group
      rw [hxeq]
      exact Subgroup.mul_mem_sup hk hq
    · exact le_top
  have hKperfTop : ⁅K.subgroupOf L, K.subgroupOf L⁆ = K.subgroupOf L := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKL, hKp]
  have hKsubTop : CFSG.Open.IsSubnormal (K.subgroupOf L) ⊤ := by
    simpa [Subgroup.subgroupOf_self] using
      CFSG.ClassicalInvolution.isSubnormal_subgroupOf hKsubL L
  have hpc : CFSG.Quasithin.perfectCore (K.subgroupOf L ⊔ pCore 2 ↥L) = K.subgroupOf L :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.perfectCore_sup_eq
      (A := K.subgroupOf L) (Q := pCore 2 ↥L) CFSG.pCore_isPGroup hKsubTop hKperfTop
  rw [← hsup] at hpc
  have hKeq : K = CFSG.Quasithin.perfectCore L := by
    have hmap := CFSG.Quasithin.map_perfectCore L.subtype (⊤ : Subgroup ↥L)
    rw [hpc, Subgroup.map_top, Subgroup.range_subtype,
      Subgroup.map_subgroupOf_eq_of_le hKL] at hmap
    exact hmap
  have hKq' : CFSG.Open.IsQuasisimple (Bar2 (CFSG.Quasithin.perfectCore L)) := by
    rw [← hKeq]
    exact hKq
  have hshapeK : IsL2 (Bar2 K) n ∨ IsSz (Bar2 K) n := by
    have e' : Bar2 K ≃* Bar2 L := e.trans Subgroup.topEquiv
    rcases hshape with h | h
    · exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e'.symm h)
    · exact Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv e'.symm h)
  have hshapeP : IsL2 (Bar2 (CFSG.Quasithin.perfectCore L)) n ∨
      IsSz (Bar2 (CFSG.Quasithin.perfectCore L)) n := by
    rw [← hKeq]
    exact hshapeK
  have hLsubM : CFSG.Open.IsSubnormal L D.M := .step hLM hLN (.refl D.M)
  have hPcalC : CFSG.Quasithin.perfectCore L ∈ calC D.M :=
    ⟨CFSG.Quasithin.A3.subnormal_perfectCore hLsubM,
      CFSG.Quasithin.perfectCore_perfect L, hKq'⟩
  have hPN : D.M ≤ Subgroup.normalizer (CFSG.Quasithin.perfectCore L : Set G) := by
    have hML : D.M ≤ Subgroup.normalizer (L : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).1 hLN
    exact hML.trans (CFSG.Quasithin.normalizer_le_normalizer_perfectCore L)
  have hPmap : ((CFSG.Quasithin.perfectCore L).subgroupOf L).map
      (QuotientGroup.mk' (pCore 2 ↥L)) = ⊤ := by
    rw [← hKeq]
    exact hKmap
  exact ⟨hPcalC, hPN, hshapeP, hPmap⟩

theorem le_perfectCore_of_map_eq_top {L K X : Subgroup G} {r : ℕ}
    (hKmap : (K.subgroupOf L).map (QuotientGroup.mk' (pCore 2 ↥L)) = ⊤)
    (hKeq : K = CFSG.Quasithin.perfectCore L) (hrodd : Odd r)
    (hXL : X ≤ L) (hXcard : Nat.card X = r) :
    X ≤ CFSG.Quasithin.perfectCore L := by
  intro x hx
  have hxL : x ∈ L := hXL hx
  have hKmap' : ((CFSG.Quasithin.perfectCore L).subgroupOf L).map
      (QuotientGroup.mk' (pCore 2 ↥L)) = ⊤ := by
    rw [← hKeq]
    exact hKmap
  have hker : IsPGroup 2 (QuotientGroup.mk' (pCore 2 ↥L)).ker := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  have hxord : Odd (orderOf (⟨x, hxL⟩ : ↥L)) := by
    rw [Subgroup.orderOf_mk]
    have hdvd : orderOf x ∣ r := by
      have h := Subgroup.orderOf_dvd_natCard X hx
      rwa [hXcard] at h
    exact hrodd.of_dvd_nat hdvd
  haveI : ((CFSG.Quasithin.perfectCore L).subgroupOf L).Normal :=
    CFSG.Quasithin.perfectCore_normal L
  have hmem := mem_of_map_eq_top_of_odd (QuotientGroup.mk' (pCore 2 ↥L))
    ((CFSG.Quasithin.perfectCore L).subgroupOf L) hKmap' hker hxord
  exact hmem

theorem mem_uniqueSet_of_conjSetOf_eq (D : Data G) {V₀ V : Subgroup G}
    (h3 : R17_3At D V₀ V) {L X : Subgroup G}
    (hLM : L ≤ D.M) (hLN : (L.subgroupOf D.M).Normal)
    {n : ℕ} (hshape : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n)
    {s : ℕ} (hso : Odd s)
    {r : ℕ} (hr : r.Prime) (hrdvd : r ∣ 2 ^ s - 1)
    (hXL : X ≤ L) (hXcard : Nat.card X = r)
    (heq : conjSetOf (⊤ : Subgroup G) X ∩ {Y : Subgroup G | Y ≤ D.M} = conjSetOf D.M X) :
    X ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M := by
  obtain ⟨hKcalC, -, hPshape, hPmap⟩ := perfectCore_of_isL2_or_isSz_1755 hLM hLN hshape
  have hthin : Thin8 (CFSG.Quasithin.perfectCore L) := by
    intro q hq hq2
    rw [← CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_pRank_bar_top hq hq2
      (CFSG.Quasithin.perfectCore L)]
    rcases hPshape with h | h
    · exact CFSG.QuasithinUnique.Id2519.pRank_le_one_psl_two_even
        (CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)) hq hq2
    · exact CFSG.QuasithinUnique.Id2519.pRank_le_one_suzuki
        (CFSG.Blueprint.LieModel.suzukiModel h).2 hq hq2
  have hr2 : r ≠ 2 := by
    have hs1 : 1 ≤ s := by
      obtain ⟨k, rfl⟩ := hso
      omega
    exact CFSG.StandardType.ne_two_of_dvd_two_pow_sub_one hs1 hrdvd
  have hrodd : Odd r := hr.odd_of_ne_two hr2
  have hXK : X ≤ CFSG.Quasithin.perfectCore L :=
    le_perfectCore_of_map_eq_top hPmap rfl hrodd hXL hXcard
  have hM : Subgroup.normalizer (D.M : Set G) = D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6.normalizer_eq_of_isMaxTwoLocal D.maxLocal
  have hXM : X ≤ D.M := hXL.trans hLM
  have hXexists :
      ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ Nat.card X = q ∧
        X ≤ CFSG.Quasithin.perfectCore L :=
    ⟨r, hr, hr2, hXcard, hXK⟩
  have hNX : Subgroup.normalizer (X : Set G) ≤ D.M :=
    h3 (CFSG.Quasithin.perfectCore L) hKcalC hthin X hXexists
  exact mem_uniqueSet_of_conjSetOf_eq_of_normalizer_le hM hXM hNX heq

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

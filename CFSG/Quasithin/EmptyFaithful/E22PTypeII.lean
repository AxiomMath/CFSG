module

public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.Quasithin

namespace E1

open CFSG.Open CFSG.Quasithin.A1b

theorem isSylowIn_top_of_quasithinIsSylowTwo {G : Type*} [Group G] {T : Subgroup G}
    (h : quasithinIsSylowTwo T) : IsSylowIn 2 T ⊤ :=
  ⟨le_top, h.1, by rw [Subgroup.relIndex_top_right]; exact h.2⟩

theorem solvableRadical_eq_bot_of_normal_simple {Q : Type*} [Group Q] [Finite Q]
    (L : Subgroup Q) [L.Normal] [IsSimpleGroup L] (hnc : ∃ a b : L, a * b ≠ b * a)
    (hC : Subgroup.centralizer (L : Set Q) = ⊥) : CFSG.solvableRadical Q = ⊥ := by
  have hL : CFSG.IsComponent L :=
    ⟨(CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1,
      Subgroup.Normal.isSubnormal inferInstance⟩
  have h := (CFSG.LocalCores.component_solvable_centralizer
    (A3.solvableRadical_isSolvable (G := Q))
    (Subgroup.Normal.isSubnormal inferInstance)).1 L hL
  rw [Subgroup.commutator_comm] at h
  exact le_bot_iff.mp (hC ▸ Subgroup.commutator_eq_bot_iff_le_centralizer.mp h)

theorem eTwo_of_normal_simple {Q : Type*} [Group Q] [Finite Q]
    (L S B : Subgroup Q) [L.Normal] [IsSimpleGroup L] (hnc : ∃ a b : L, a * b ≠ b * a)
    (hC : Subgroup.centralizer (L : Set Q) = ⊥) (hS : IsSylowIn 2 S ⊤) (hLS : L ⊔ S = ⊤)
    (hB : B ≠ ⊥) : ETwo Q S B := by
  have hR : CFSG.solvableRadical Q = ⊥ := solvableRadical_eq_bot_of_normal_simple L hnc hC
  have hLq := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc
  have hLc : CFSG.IsComponent L := ⟨hLq.1, Subgroup.Normal.isSubnormal inferInstance⟩
  have hLperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hLq.1.1
  have hLcC : L ∈ cComp (⊤ : Subgroup Q) := mem_cComp_top_of_isComponent hLc
  have hnormtop : ∀ g : Q, g ∈ Subgroup.normalizer (L : Set Q) := fun g => by
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]; exact Subgroup.mem_top g
  have h2 : ∀ x : Q, ∃ k : ℕ, x ^ 2 ^ k ∈ L := fun x =>
    B6.isTwoQuotient_of_sup_eq hS.isPGroup (D := ⊤) (C := L) (fun g _ => hnormtop g)
      (by rw [sup_comm]; exact hLS) x (Subgroup.mem_top x)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hR]
    refine ⟨⊥, ⟨le_rfl, IsPGroup.of_bot, ?_⟩, Subgroup.Normal.subgroupOf inferInstance _⟩
    rw [Subgroup.relIndex_self]
    omega
  · rw [pCore_two_quotient_eq_top_iff]
    intro x
    obtain ⟨k, hk⟩ := h2 x
    refine ⟨k, ?_⟩
    have hLO : L ≤ oInftyE Q := by
      rw [oInftyE_eq_cCompSpan_sup Q]
      exact (le_cCompSpan hLcC).trans le_sup_left
    exact hLO hk
  · have h1 : twoResidual (⊤ : Subgroup Q) ≤ L :=
      twoResidual_le_of_isTwoQuotient le_top (fun g _ => hnormtop g) fun y _ => h2 y
    have h3 : perfectCore (⊤ : Subgroup Q) ≤ twoResidual (⊤ : Subgroup Q) :=
      perfectCore_le_of_sup_solvable (twoResidual_le ⊤)
        (Subgroup.Normal.subgroupOf
          (Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_twoResidual ⊤))) _)
        (by rw [sup_comm]; exact (sup_twoResidual_eq hS).symm)
        (isSolvable_of_isPGroup_two hS.isPGroup)
    exact le_antisymm (h1.trans (le_perfectCore_of_perfect le_top hLperf)) h3
  · set π := QuotientGroup.mk' (CFSG.solvableRadical Q) with hπ
    have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
    have hker : Group.IsSolvable π.ker := by
      rw [QuotientGroup.ker_mk']; exact A3.solvableRadical_isSolvable
    have hLb : L.map π ∈ cComp (⊤ : Subgroup (Q ⧸ CFSG.solvableRadical Q)) :=
      map_mem_cComp_top π hπs hker hLcC
    have hLbc : CFSG.IsComponent (L.map π) :=
      isComponent_of_mem_cComp_top (A3.solvableRadical_quotient_eq_bot Q) hLb
    have hLbn : (L.map π).Normal := Subgroup.Normal.map inferInstance π hπs
    have hspan : cCompSpan (⊤ : Subgroup Q) ≤ L := by
      refine sSup_le fun K hK => ?_
      have hKc : CFSG.IsComponent K := isComponent_of_mem_cComp_top hR hK
      rcases CFSG.LocalCores.distinct_components_commute hKc hLc with h | h
      · exact h.le
      · exfalso
        have : K ≤ ⊥ := hC ▸ Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
        exact ne_bot_of_mem_cComp hK (le_bot_iff.mp this)
    have hlayer : CFSG.layer (Q ⧸ CFSG.solvableRadical Q) = L.map π := by
      refine le_antisymm ?_ (CFSG.LocalCores.component_le_layer hLbc)
      rw [← map_cCompSpan_eq_layer]
      exact Subgroup.map_mono hspan
    have hLB : ⁅L, B⁆ = L := by
      rcases cComp_commutator_dichotomy hLcC B with ⟨h, -⟩ | h
      · exfalso
        have h0 : ⁅L, B⁆ = ⊥ := le_bot_iff.mp (hR ▸ h)
        rw [Subgroup.commutator_comm] at h0
        exact hB (le_bot_iff.mp (hC ▸ Subgroup.commutator_eq_bot_iff_le_centralizer.mp h0))
      · rw [h]
        exact le_antisymm (conjClosure_le fun h' _ z hz => by
            have := Subgroup.Normal.conj_mem inferInstance z hz h'
            exact this) (le_conjClosure L B)
    refine ⟨L.map π, hLbc, ?_, Or.inl ?_⟩
    · rw [hlayer]
      refine le_antisymm ?_ ?_
      · refine le_iSup₂_of_le (1 : Q ⧸ CFSG.solvableRadical Q) (Subgroup.one_mem _) ?_
        rw [conjSub_one]
      · refine iSup₂_le fun t _ => ?_
        exact (conjSub_eq_iff_mem_normalizer.mpr (by
          rw [Subgroup.normalizer_eq_top_iff.mpr hLbn]; exact Subgroup.mem_top t)).le
    · show L.map π = ⁅L.map π, B.map π⁆
      rw [← Subgroup.map_commutator, hLB]

theorem isE_one_top_of_almostSimple {G : Type*} [Group G] [Finite G]
    (L T A : Subgroup G) [L.Normal] [IsSimpleGroup L] (hnc : ∃ a b : L, a * b ≠ b * a)
    (hC : Subgroup.centralizer (L : Set G) = ⊥) (hT : IsSylowIn 2 T ⊤) (hLT : L ⊔ T = ⊤)
    (hAT : A ≤ T) (hA : Nat.card A = 2) : IsE 1 ⊤ T A ⊤ := by
  have hAbot : A ≠ ⊥ := by
    rintro rfl
    simp at hA
  have hR : CFSG.solvableRadical G = ⊥ := solvableRadical_eq_bot_of_normal_simple L hnc hC
  have he : (Subgroup.topEquiv (G := G)).toMonoidHom = (⊤ : Subgroup G).subtype := rfl
  have hS : ((T ⊓ ⊤).subgroupOf (⊤ : Subgroup G)).map
      (Subgroup.topEquiv (G := G)).toMonoidHom = T := by
    rw [he, inf_top_eq]
    exact Subgroup.map_subgroupOf_eq_of_le le_top
  have hB : (A.subgroupOf (⊤ : Subgroup G)).map (Subgroup.topEquiv (G := G)).toMonoidHom = A := by
    rw [he]
    exact Subgroup.map_subgroupOf_eq_of_le le_top
  refine ⟨le_rfl, (tauOf_le ⊤ T A).trans (by rw [inf_top_eq]), by rwa [inf_top_eq],
    Or.inr ⟨?_, ?_⟩⟩
  · rw [eTwo_map (Subgroup.topEquiv (G := G)), hS, hB]
    exact eTwo_of_normal_simple L T A hnc hC hT hLT hAbot
  · have h1 := card_barRad_map (Subgroup.topEquiv (G := G)) (A.subgroupOf (⊤ : Subgroup G))
    rw [hB] at h1
    rw [← h1]
    have hinj : Function.Injective (QuotientGroup.mk' (CFSG.solvableRadical G)) :=
      (MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk', hR])
    have : Nat.card (barRad G A) = Nat.card A := Subgroup.card_map_of_injective hinj
    rw [this, hA]
    norm_num

theorem isE_one_top_of_fstar_simple {G : Type*} [Group G] [Finite G] (T A : Subgroup G)
    [IsSimpleGroup ↥(CFSG.generalizedFitting G)]
    (hnc : ∃ a b : ↥(CFSG.generalizedFitting G), a * b ≠ b * a)
    (hT : IsSylowIn 2 T ⊤) (hLT : CFSG.generalizedFitting G ⊔ T = ⊤)
    (hAT : A ≤ T) (hA : Nat.card A = 2) : IsE 1 ⊤ T A ⊤ := by
  have : (CFSG.generalizedFitting G).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := G)).2
  have hZ : Subgroup.center ↥(CFSG.generalizedFitting G) = ⊥ :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).2
  have hC : Subgroup.centralizer (CFSG.generalizedFitting G : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxY : x ∈ CFSG.generalizedFitting G := CFSG.centralizer_generalizedFitting_le G hx
    have hxc : (⟨x, hxY⟩ : ↥(CFSG.generalizedFitting G)) ∈
        Subgroup.center ↥(CFSG.generalizedFitting G) := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx y y.2)
    rw [hZ, Subgroup.mem_bot] at hxc
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hxc
  exact isE_one_top_of_almostSimple _ T A hnc hC hT hLT hAT hA

theorem isE_one_top_of_fstar_simple' {G : Type*} [Group G] [Finite G] (T A : Subgroup G)
    [IsSimpleGroup ↥(CFSG.generalizedFitting G)]
    (hnc : ∃ a b : ↥(CFSG.generalizedFitting G), a * b ≠ b * a)
    (hT : quasithinIsSylowTwo T) (hLT : CFSG.generalizedFitting G ⊔ T = ⊤)
    (hAT : A ≤ T) (hA : Nat.card A = 2) : IsE 1 ⊤ T A ⊤ :=
  isE_one_top_of_fstar_simple T A hnc (isSylowIn_top_of_quasithinIsSylowTwo hT) hLT hAT hA

theorem pCore_two_eq_bot_of_normal_simple {Q : Type*} [Group Q] [Finite Q]
    (L : Subgroup Q) [L.Normal] [IsSimpleGroup L] (hnc : ∃ a b : L, a * b ≠ b * a)
    (hC : Subgroup.centralizer (L : Set Q) = ⊥) : CFSG.Open.pCore 2 Q = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR := solvableRadical_eq_bot_of_normal_simple L hnc hC
  have hP2 : IsPGroup 2 ↥(CFSG.Open.pCore 2 Q) := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hsolv : Group.IsSolvable ↥(CFSG.Open.pCore 2 Q) := by
    have := hP2.isNilpotent
    infer_instance
  have hle : CFSG.Open.pCore 2 Q ≤ CFSG.solvableRadical Q :=
    le_sSup ⟨CFSG.LieType.BorelTits.pCore_normal 2, hsolv⟩
  rw [hR] at hle
  exact le_bot_iff.mp hle

theorem pCoreOf_top_eq_bot_of_normal_simple {Q : Type*} [Group Q] [Finite Q]
    (L : Subgroup Q) [L.Normal] [IsSimpleGroup L] (hnc : ∃ a b : L, a * b ≠ b * a)
    (hC : Subgroup.centralizer (L : Set Q) = ⊥) : pCoreOf 2 (⊤ : Subgroup Q) = ⊥ := by
  rw [pCoreOf_top_eq]
  exact pCore_two_eq_bot_of_normal_simple L hnc hC

end E1

end CFSG.Quasithin

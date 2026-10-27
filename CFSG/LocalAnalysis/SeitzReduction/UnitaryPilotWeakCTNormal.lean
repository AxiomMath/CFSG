module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotWeakCTNormalDescent
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotNeighbourParamNormal
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotGlobalNormalQuotient
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotHR8
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotWeakCTGlobal

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Quasithin (perfectCore)
open CFSG.EvenSmallLie (StandardSetting)
open CFSG.SeitzReduction.F4Pilot (centerQuotientAut)

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {n : ℕ}

section Model

theorem isQuasisimple_unitaryPSU (hn : 3 ≤ n) (hnq : (n, 2 ^ f) ≠ (3, 2)) :
    CFSG.IsQuasisimple (unitaryPSU h n) :=
  (CFSG.LocalCores.quasisimple_central_quotient (isQuasisimple_unitarySU h hn hnq)
    (unitaryScalars h n) (center_unitarySU_eq_unitaryScalars h n).ge).1

theorem center_unitaryPSU_eq_bot (hn : 3 ≤ n) (hnq : (n, 2 ^ f) ≠ (3, 2)) :
    center (unitaryPSU h n) = ⊥ := by
  rw [(CFSG.LocalCores.quasisimple_central_quotient (isQuasisimple_unitarySU h hn hnq)
    (unitaryScalars h n) (center_unitarySU_eq_unitaryScalars h n).ge).2.2,
    center_unitarySU_eq_unitaryScalars h n, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']

theorem commutator_unitaryPSU_eq_top (hn : 3 ≤ n) (hnq : (n, 2 ^ f) ≠ (3, 2)) :
    ⁅(⊤ : Subgroup (unitaryPSU h n)), (⊤ : Subgroup (unitaryPSU h n))⁆ = ⊤ := by
  have := (isQuasisimple_unitaryPSU h hn hnq).1
  rw [← commutator_def]
  exact Group.IsPerfect.commutator_eq_top

theorem perfectCore_fixedSubgroup_graphFieldAut (hn : 3 ≤ n) (hnq : (n, 2 ^ f) ≠ (3, 2)) :
    perfectCore (fixedSubgroup (graphFieldAut h n)) = (toPSL h n).range := by
  have := h.finite
  refine le_antisymm (le_range_toPSL_of_le_fixedSubgroup h (CFSG.Quasithin.perfectCore_perfect _)
    (CFSG.Quasithin.perfectCore_le _))
    (CFSG.Quasithin.le_perfectCore_of_perfect (range_toPSL_le_fixedSubgroup h) ?_)
  rw [MonoidHom.range_eq_map, ← map_commutator, commutator_unitaryPSU_eq_top h hn hnq]

theorem isComponent_perfectCore_of_range_eq (hn : 3 ≤ n) (hnq : (n, 2 ^ f) ≠ (3, 2)) {M : Type}
    [Group M] {τ : MulAut M} (ε : unitaryPSU h n →* M) (hε : Function.Injective ε)
    (hεr : ε.range = perfectCore (fixedSubgroup τ)) :
    IsComponent ((perfectCore (fixedSubgroup τ)).subgroupOf (fixedSubgroup τ)) ∧
      LieModel ((perfectCore (fixedSubgroup τ)).subgroupOf (fixedSubgroup τ)) .PSU n 2 f := by
  have hD₀F : perfectCore (fixedSubgroup τ) ≤ fixedSubgroup τ := CFSG.Quasithin.perfectCore_le _
  let eD₀ : unitaryPSU h n ≃* (perfectCore (fixedSubgroup τ)).subgroupOf (fixedSubgroup τ) :=
    ((MonoidHom.ofInjective hε).trans (MulEquiv.subgroupCongr hεr)).trans
      (subgroupOfEquivOfLe hD₀F).symm
  exact ⟨⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv eD₀ (isQuasisimple_unitaryPSU h hn hnq),
      (CFSG.Quasithin.perfectCore_normal _).isSubnormal⟩,
    lieModel_PSU_of_mulEquiv_unitaryPSU h hn hnq eD₀.symm⟩

theorem graphFieldAut_not_mem_range_conj (hn : 3 ≤ n) (hnq : (n, 2 ^ f) ≠ (3, 2)) :
    graphFieldAut h n ∉
      (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range := by
  have := h.finite
  obtain ⟨hC, hCm⟩ := isComponent_perfectCore_of_range_eq h hn hnq (toPSL h n) (toPSL_injective h)
    (perfectCore_fixedSubgroup_graphFieldAut h hn hnq).symm
  exact not_mem_range_conj_of_isComponent_PSU hn h.one_le (by rw [h.card])
    (graphFieldAut_mul_self h) hC hCm

end Model

section Normalize

theorem exists_mulEquiv_toPSL_eq_of_perfectCore (hn : 3 ≤ n) (hnq : (n, 2 ^ f) ≠ (3, 2))
    {M : Type} [Group M] (ψ₀ : M ≃* projectiveSL n K) {τ : MulAut M} (hτ : τ * τ = 1)
    (ε : unitaryPSU h n →* M) (hε : Function.Injective ε)
    (hεr : ε.range = perfectCore (fixedSubgroup τ)) :
    ∃ ψ : M ≃* projectiveSL n K, (∀ x, ψ (ε x) = toPSL h n x) ∧
      ∀ y, ψ (τ y) = graphFieldAut h n (ψ y) := by
  set β₀ := MulAut.congr ψ₀ τ with hβ₀def
  have hβ₀ : β₀ * β₀ = 1 := by rw [hβ₀def, ← map_mul, hτ, map_one]
  obtain ⟨hcomp, hm⟩ := isComponent_perfectCore_of_range_eq h hn hnq ε hε hεr
  let Ψ := fixedSubgroupCongrEquiv ψ₀ τ
  obtain ⟨H, hH⟩ := eq_conj_graphFieldAut_conj_inv_of_isComponent h hn hβ₀
    (CFSG.LocalCores.isComponent_map_mulEquiv Ψ hcomp)
    (LieType.CurtisTits.lieModel_of_mulEquiv
      (((perfectCore (fixedSubgroup τ)).subgroupOf (fixedSubgroup τ)).equivMapOfInjective
        Ψ.toMonoidHom Ψ.injective) hm)
  set ψ₁ : M ≃* projectiveSL n K := ψ₀.trans (conjAut n K H)⁻¹ with hψ₁
  have h1 : MulAut.congr ψ₁ τ = (conjAut n K H)⁻¹ * β₀ * conjAut n K H :=
    MulEquiv.ext fun _ => rfl
  have hτ₁ : MulAut.congr ψ₁ τ = graphFieldAut h n := by
    rw [h1, hH]
    group
  exact exists_mulEquiv_toPSL_eq h hn (fun h' => hnq (by rw [h'.1, h'.2])) ψ₁ hτ₁ ε hε
    (hεr.le.trans (CFSG.Quasithin.perfectCore_le _))

end Normalize

theorem injective_mk_inclusion_of_center_eq_bot {G : Type*} [Group G] {L G₀ : Subgroup G}
    (hZ : center L = ⊥) (hLG₀ : L ≤ G₀) :
    Function.Injective ((QuotientGroup.mk' (center G₀)).comp (inclusion hLG₀)) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
  have hxZ : x ∈ center L := mem_center_iff.mpr fun y => by
    have h' := mem_center_iff.mp hx (inclusion hLG₀ y)
    exact inclusion_injective hLG₀ (by rw [map_mul, map_mul]; exact h')
  rw [hZ, mem_bot] at hxZ
  exact hxZ

section Global

variable {G : Type} [Group G] [Finite G] {L G₀ : Subgroup G}

theorem exists_mulEquiv_globalGraphField_center (hn : 3 ≤ n) (hnq : (n, 2 ^ f) ≠ (3, 2))
    (e : L ≃* unitaryPSU h n) (ψ₀ : G₀ ⧸ center G₀ ≃* projectiveSL n K) (hLG₀ : L ≤ G₀) {t : G}
    (ht : t ^ 2 = 1) (htG₀ : t ∈ normalizer (G₀ : Set G))
    (hCt : perfectCore (G₀ ⊓ centralizer ({t} : Set G)) = L) :
    ∃ ψ : G₀ ⧸ center G₀ ≃* projectiveSL n K,
      (∀ x : L, ψ ((inclusion hLG₀ x : G₀) : G₀ ⧸ center G₀) = toPSL h n (e x)) ∧
      ∀ x : G₀, ψ ((G₀.normalizerMonoidHom ⟨t, htG₀⟩ x : G₀) : G₀ ⧸ center G₀) =
        graphFieldAut h n (ψ (x : G₀ ⧸ center G₀)) := by
  set θ := G₀.normalizerMonoidHom ⟨t, htG₀⟩ with hθdef
  have hθ : θ * θ = 1 := by
    rw [← sq]
    exact F4Pilot.normalizerMonoidHom_sq_eq_one G₀ htG₀ ht
  have hθ' : centerQuotientAut θ * centerQuotientAut θ = 1 := by
    rw [← LinearPilot.centerQuotientAut_mul, hθ, LinearPilot.centerQuotientAut_one]
  set q := (QuotientGroup.mk' (center G₀)).comp (inclusion hLG₀) with hqdef
  set ε : unitaryPSU h n →* G₀ ⧸ center G₀ := q.comp e.symm.toMonoidHom with hεdef
  have hZL : center L = ⊥ := by
    rw [← map_center_eq e.symm, center_unitaryPSU_eq_bot h hn hnq, Subgroup.map_bot]
  have hε : Function.Injective ε :=
    (injective_mk_inclusion_of_center_eq_bot hZL hLG₀).comp e.symm.injective
  have hcore : perfectCore (fixedSubgroup θ) = L.subgroupOf G₀ := by
    rw [hθdef, F4Pilot.fixedSubgroup_normalizerMonoidHom]
    apply Subgroup.map_injective G₀.subtype_injective
    rw [CFSG.Quasithin.map_perfectCore, subgroupOf_map_subtype, inf_comm, hCt,
      subgroupOf_map_subtype, inf_eq_left.mpr hLG₀]
  have hεr : ε.range = perfectCore (fixedSubgroup (centerQuotientAut θ)) := by
    rw [LinearPilot.perfectCore_fixedSubgroup_centerQuotientAut, hcore, hεdef,
      MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.symm.surjective,
      ← MonoidHom.range_eq_map, hqdef, MonoidHom.range_comp, Subgroup.inclusion_range]
  obtain ⟨ψ, hψε, hψθ⟩ := exists_mulEquiv_toPSL_eq_of_perfectCore h hn hnq ψ₀ hθ' ε hε hεr
  refine ⟨ψ, fun x => ?_, fun x => ?_⟩
  · have hx : ε (e x) = ((inclusion hLG₀ x : G₀) : G₀ ⧸ center G₀) := by
      rw [hεdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
      rfl
    rw [← hx, hψε]
  · rw [← hψθ, LinearPilot.centerQuotientAut_coe]

omit [Finite G] in
theorem not_mem_of_globalGraphField (hn : 3 ≤ n) (hnq : (n, 2 ^ f) ≠ (3, 2)) {t : G}
    (htG₀ : t ∈ normalizer (G₀ : Set G)) (ψ : G₀ ⧸ center G₀ ≃* projectiveSL n K)
    (hψt : ∀ x : G₀, ψ ((G₀.normalizerMonoidHom ⟨t, htG₀⟩ x : G₀) : G₀ ⧸ center G₀) =
      graphFieldAut h n (ψ (x : G₀ ⧸ center G₀))) : t ∉ G₀ := by
  intro htG
  apply graphFieldAut_not_mem_range_conj h hn hnq
  refine ⟨ψ ((⟨t, htG⟩ : G₀) : G₀ ⧸ center G₀), ?_⟩
  ext z
  obtain ⟨q, rfl⟩ := ψ.surjective z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  rw [MulAut.conj_apply, ← hψt x, ← map_inv, ← map_mul, ← map_mul]
  congr 1

end Global

theorem commutator_eq_self_of_mulEquiv_unitaryPSU {G : Type*} [Group G] {L : Subgroup G}
    (hn : 3 ≤ n) (hnq : (n, 2 ^ f) ≠ (3, 2)) (e : L ≃* unitaryPSU h n) : ⁅L, L⁆ = L := by
  have htop : ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆ = ⊤ := by
    have h' := congrArg (Subgroup.map (e.symm : unitaryPSU h n →* L))
      (commutator_unitaryPSU_eq_top h hn hnq)
    rwa [map_commutator, map_top_of_surjective _ e.symm.surjective] at h'
  have hL : (⊤ : Subgroup L).map L.subtype = L := by
    rw [← MonoidHom.range_eq_map, range_subtype]
  rw [← hL, ← map_commutator, htop]

section Standard

variable {G : Type} [Group G] [Finite G] {L G₀ : Subgroup G}

theorem perfectCore_inf_centralizer_eq_of_standardSetting_unitary (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) (hn : 3 ≤ n) (hnq : (n, 2 ^ f) ≠ (3, 2))
    (e : L ≃* unitaryPSU h n) (hLG₀ : L ≤ G₀) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) : perfectCore (G₀ ⊓ centralizer ({t} : Set G)) = L := by
  refine le_antisymm (std_perfect_le hset hOut htC ht (CFSG.Quasithin.perfectCore_perfect _)
    ((CFSG.Quasithin.perfectCore_le _).trans inf_le_right))
    (CFSG.Quasithin.le_perfectCore_of_perfect (le_inf hLG₀ fun x hx => ?_)
      (commutator_eq_self_of_mulEquiv_unitaryPSU h hn hnq e))
  rw [mem_centralizer_singleton_iff]
  exact mem_centralizer_iff.mp htC x hx

theorem exists_globalGraphField_center_of_standardSetting (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) (hn : 3 ≤ n) (hnq : (n, 2 ^ f) ≠ (3, 2))
    (e : L ≃* unitaryPSU h n) (ψ₀ : G₀ ⧸ center G₀ ≃* projectiveSL n K) (hLG₀ : L ≤ G₀) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (htG₀ : t ∈ normalizer (G₀ : Set G)) :
    ∃ ψ : G₀ ⧸ center G₀ ≃* projectiveSL n K,
      (∀ x : L, ψ ((inclusion hLG₀ x : G₀) : G₀ ⧸ center G₀) = toPSL h n (e x)) ∧
      ∀ x : G₀, ψ ((G₀.normalizerMonoidHom ⟨t, htG₀⟩ x : G₀) : G₀ ⧸ center G₀) =
        graphFieldAut h n (ψ (x : G₀ ⧸ center G₀)) :=
  exists_mulEquiv_globalGraphField_center h hn hnq e ψ₀ hLG₀
    (by rw [← ht]; exact pow_orderOf_eq_one t) htG₀
    (perfectCore_inf_centralizer_eq_of_standardSetting_unitary h hset hOut hn hnq e hLG₀ htC ht)

end Standard

section Seitz

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {m : ℕ}

omit h in
theorem exists_globalGraphField_unitaryRootTorus {h : UnitaryFieldData 2 f K}
    (hset : SeitzSetting G L) (e : L ≃* unitaryPSU h (m + 1)) (hm : 5 ≤ m) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hparam : ∀ (a b : Fin (m + 1)) (hab : a ≠ b),
      Nonempty (GraphFieldNeighbourParam e t (modelToG e (unitaryRootTorus h hab))
        ({a, b}ᶜ : Finset (Fin (m + 1)))))
    {G₀ : Subgroup G}
    (hG₀ : G₀ = ⨆ i : Fin m, pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1)))) :
    ∃ (hLG₀ : L ≤ G₀) (htG₀ : t ∈ normalizer (G₀ : Set G)), CFSG.IsQuasisimple G₀ ∧ t ∉ G₀ ∧
      ∃ ψ : G₀ ⧸ center G₀ ≃* projectiveSL (m + 1) K,
        (∀ x : L, ψ ((inclusion hLG₀ x : G₀) : G₀ ⧸ center G₀) = toPSL h (m + 1) (e x)) ∧
        ∀ x : G₀, ψ ((G₀.normalizerMonoidHom ⟨t, htG₀⟩ x : G₀) : G₀ ⧸ center G₀) =
          graphFieldAut h (m + 1) (ψ (x : G₀ ⧸ center G₀)) := by
  have hn : 3 ≤ m + 1 := by omega
  have hnq : (m + 1, 2 ^ f) ≠ (3, 2) := fun h' => by
    have := congrArg Prod.fst h'
    simp only at this
    omega
  obtain ⟨hLG₀, htG₀, hqs, -, ⟨ψ₀⟩, -⟩ := exists_globalField_unitaryRootTorus hm htC hparam hG₀
  obtain ⟨ψ, hψL, hψt⟩ := exists_globalGraphField_center_of_standardSetting h
    hset.standardSetting (isSolvable_outer_of_mulEquiv h hn hnq e) hn hnq e ψ₀ hLG₀ htC ht htG₀
  exact ⟨hLG₀, htG₀, hqs, not_mem_of_globalGraphField h hn hnq htG₀ ψ hψt, ψ, hψL, hψt⟩

end Seitz

end CFSG.SeitzReduction.UnitaryPilot

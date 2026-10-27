module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentNbrDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSThreeNbr
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsExcBasic
public import CFSG.Adapters.QiuzhenLegacy.FeitThompson.GroupAction.Quotient

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Layer

variable {G : Type} [Group G]

theorem ggRCSStructNbrConcl_of_concl {p : ℕ} {G₀ M : Subgroup G} {r : G}
    (h : GGRCSStructConcl p G₀ M r) (hN : p = 3 → GGRCSNbr M r) : GGRCSStructNbrConcl p G₀ M r := by
  obtain ⟨𝒮, h𝒮, hcov⟩ := h
  refine ⟨𝒮, fun S hS => ?_, hcov⟩
  rcases h𝒮 S hS with h | ⟨hp, hT⟩
  · exact Or.inl h
  · exact Or.inr ⟨hp, hT, hN hp⟩

end Layer

section Excluding

variable {G : Type} [Group G]

theorem GGRootCentDerivedAt.toQ_of_not_isSolvable [Finite G] {p : ℕ} {G₀ : Subgroup G} {r : G}
    (h : GGRootCentDerivedAt p G₀ r) (hX : ¬ IsSolvable ↥(ggRCSX G₀ r)) :
    GGRootCentDerivedAtQ p G₀ r := by
  rcases h with h | ⟨hp, hQ, hcov⟩ | ⟨Q, -, hQ2, hQn, he⟩
  · exact Or.inl h
  · exact Or.inr ⟨hp, hQ, hcov⟩
  · exfalso
    apply hX
    letI := hQn
    obtain ⟨e⟩ := he
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hQ2X : IsPGroup 2 (Q.subgroupOf (ggRCSX G₀ r)) :=
      hQ2.comap_of_injective (ggRCSX G₀ r).subtype (Subgroup.subtype_injective _)
    haveI : Group.IsSolvable (Q.subgroupOf (ggRCSX G₀ r)) :=
      @IsNilpotent.to_isSolvable _ _ hQ2X.isNilpotent
    haveI : Group.IsSolvable (Equiv.Perm (Fin 3)) := Equiv.Perm.isSolvable (by simp)
    haveI : Group.IsSolvable (↥(ggRCSX G₀ r) ⧸ Q.subgroupOf (ggRCSX G₀ r)) :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact Group.isSolvable_of_ker_le_range (Q.subgroupOf (ggRCSX G₀ r)).subtype
      (QuotientGroup.mk' (Q.subgroupOf (ggRCSX G₀ r)))
      (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem ggRCSX_not_isSolvable_of_le {G₀ : Subgroup G} {r : G} {L₀ : Subgroup G}
    (hL₀ : CFSG.IsQuasisimple L₀) (hL₀X : L₀ ≤ ggRCSX G₀ r) : ¬ IsSolvable ↥(ggRCSX G₀ r) := by
  haveI : Nontrivial ↥L₀ := CFSG.LocalCores.isQuasisimple_nontrivial hL₀
  haveI : Group.IsPerfect ↥L₀ := hL₀.1
  intro hsol
  haveI : Group.IsSolvable ↥(ggRCSX G₀ r) := hsol
  haveI : Group.IsSolvable ↥(L₀.subgroupOf (ggRCSX G₀ r)) :=
    CFSG.subgroup_solvable_of_solvable _
  have hsolL : Group.IsSolvable ↥L₀ :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hL₀X).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hL₀X).symm.injective
  exact Group.IsPerfect.not_isSolvable ↥L₀ hsolL

end Excluding

section ProducersFinite

variable {G : Type} [Group G] [Finite G]

theorem ggRootCentDerivedAtQ_of_not_dvd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {G₀ : Subgroup G}
    {r : G} {Q L₀ : Subgroup G} (hQ2 : IsPGroup 2 Q) (hL₀Q : L₀ ≤ Subgroup.normalizer (Q : Set G))
    (hX : ggRCSX G₀ r ≤ Q ⊔ L₀) (hpL : ¬ p ∣ Nat.card L₀) : GGRootCentDerivedAtQ p G₀ r :=
  Or.inl fun _ hy hyp =>
    ggRCS_eq_one_of_not_dvd hp (ggRCST_not_dvd_card_sup hp hp2 hQ2 hL₀Q hpL) (hX hy) hyp

theorem ggRootCentDerivedAtQ_of_quasisimple {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {G₀ : Subgroup G} {r : G} {Q L₀ : Subgroup G} (hQX : Q ≤ ggRCSX G₀ r) (hQ2 : IsPGroup 2 Q)
    (hXQ : ggRCSX G₀ r ≤ Subgroup.normalizer (Q : Set G)) (hL₀X : L₀ ≤ ggRCSX G₀ r)
    (hL₀ : CFSG.IsQuasisimple L₀) (hY : ggRCSXd G₀ r ≤ Q ⊔ L₀)
    (hcov : ∀ y ∈ ggRCSX G₀ r, y ^ p = 1 → y ∈ Q ⊔ L₀) : GGRootCentDerivedAtQ p G₀ r :=
  (ggRootCentDerivedAt_of_quasisimple hp hp2 hQX hQ2 hXQ hL₀X hL₀ hY hcov).toQ_of_not_isSolvable
    (ggRCSX_not_isSolvable_of_le hL₀ hL₀X)

theorem ggRootCentDerivedAtQ_of_sup_eq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {G₀ : Subgroup G} {r : G} {Q L : Subgroup G} (hQ2 : IsPGroup 2 Q)
    (hQL : Q ⊔ L = G₀ ⊓ Subgroup.centralizer {r}) (hLQ : L ≤ Subgroup.normalizer (Q : Set G))
    (hL : CFSG.IsQuasisimple L) (hL2 : L ≤ ggOTwoPrime (G₀ ⊓ Subgroup.centralizer {r})) :
    GGRootCentDerivedAtQ p G₀ r := by
  have hXC : ggRCSX G₀ r ≤ Q ⊔ L := (ggOTwoPrime_le _).trans hQL.ge
  exact ggRootCentDerivedAtQ_of_quasisimple hp hp2
    (OTwoGen.le_ggOTwoPrime_of_isPGroup ((le_sup_left : Q ≤ Q ⊔ L).trans hQL.le) hQ2) hQ2
    (hXC.trans (sup_le Subgroup.le_normalizer hLQ)) hL2 hL
    ((CFSG.Quasithin.perfectCore_le _).trans hXC) fun _ hy _ => hXC hy

theorem ggRootCentDerivedAtQ_of_model {U C : Type*} [Group U] [Group C]
    {ψ : U →* G} {π : U →* C} (hπ : Function.Surjective π) (hker : π.ker = ψ.ker) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {w : U} (hw : GGRootCentQL (π w)) :
    GGRootCentDerivedAtQ p ψ.range (ψ w) := by
  set Θ := AutSt.modelEquiv ψ π hπ hker with hΘ
  let Θ' : C →* G := ψ.range.subtype.comp Θ.toMonoidHom
  have hΘ' : Θ' (π w) = ψ w := AutSt.modelEquiv_apply ψ π hπ hker w
  have hinj : Function.Injective Θ' := Subtype.val_injective.comp Θ.injective
  have hrange : Θ'.range = ψ.range := by
    ext x
    constructor
    · rintro ⟨c, rfl⟩
      exact (Θ c).2
    · intro hx
      exact ⟨Θ.symm ⟨x, hx⟩, by simp [Θ']⟩
  obtain ⟨Q, L, hQ2, hQL, hLQ, hL, hL2⟩ := hw
  have hC := ggRCQL_range_inf_centralizer hinj (π w)
  rw [hrange, hΘ'] at hC
  refine ggRootCentDerivedAtQ_of_sup_eq hp hp2 (hQ2.map Θ') ?_
    (ggRCST_map_le_normalizer Θ' hLQ)
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv (L.equivMapOfInjective Θ' hinj) hL) ?_
  · rw [hC, ← hQL, Subgroup.map_sup]
  · rw [hC]
    exact (Subgroup.map_mono hL2).trans (LinFusion.map_ggOTwoPrime_le Θ' _)

theorem ggRootCentDerivedAtQ_of_perfect {p : ℕ} (hp : p.Prime) {G₀ : Subgroup G} {r : G}
    (hperf : ⁅ggRCSX G₀ r, ggRCSX G₀ r⁆ = ggRCSX G₀ r) {Q : Subgroup G}
    (hQX : Q ≤ ggRCSX G₀ r) (hQ2 : IsPGroup 2 Q) [hQn : (Q.subgroupOf (ggRCSX G₀ r)).Normal]
    (hq : p ∣ Nat.card (ggRCSX G₀ r) →
      CFSG.IsQuasisimple (↥(ggRCSX G₀ r) ⧸ Q.subgroupOf (ggRCSX G₀ r))) :
    GGRootCentDerivedAtQ p G₀ r := by
  have hc : ggRCSXd G₀ r = ggRCSX G₀ r := CFSG.Quasithin.perfectCore_eq_self_of_perfect hperf
  by_cases hpX : p ∣ Nat.card (ggRCSX G₀ r)
  · refine Or.inr ?_
    rw [hc]
    refine ⟨hpX, ⟨Q, hQX, hQ2, hQn, ?_⟩, fun y hy _ => hy⟩
    intro _
    exact hq hpX
  · exact Or.inl fun y hy hyp => ggRCS_eq_one_of_not_dvd hp hpX hy hyp

end ProducersFinite

section LayersQ

variable {G : Type} [Group G] [Finite G]

theorem ggRCSLayerQ_of_derivedAtQ {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {G₀ M : Subgroup G}
    (hG₀M : G₀ ≤ M) (hM : M ≤ Subgroup.normalizer (G₀ : Set G)) {r : G}
    (h : GGRootCentDerivedAtQ p G₀ r) : GGRCSLayerQ p G₀ M r := by
  set X := ggRCSX G₀ r with hX
  set V := M ⊓ Subgroup.centralizer ({r} : Set G) with hV
  have hXV : X ≤ V := (ggOTwoPrime_le _).trans (inf_le_inf_right _ hG₀M)
  have hVX : V ≤ Subgroup.normalizer (X : Set G) := fun c hc =>
    ggMem_normalizer_oTwoPrime_inf_centralizer (hM hc.1) hc.2
  have hVXd : V ≤ Subgroup.normalizer (ggRCSXd G₀ r : Set G) :=
    hVX.trans (CFSG.Quasithin.normalizer_le_normalizer_perfectCore X)
  have hXdV : ggRCSXd G₀ r ≤ V := (CFSG.Quasithin.perfectCore_le X).trans hXV
  have hperf : ⁅ggRCSXd G₀ r, ggRCSXd G₀ r⁆ = ggRCSXd G₀ r :=
    CFSG.Quasithin.perfectCore_perfect _
  rcases h with h1 | ⟨hpXd, ⟨Q₁, -, hQ₁2, hQ₁n, hq⟩, hcov⟩
  · refine ⟨∅, fun S hS => hS.elim, fun y hy hyp => ?_⟩
    rw [h1 y hy hyp]
    exact one_mem _
  · refine ⟨{ggRCSXd G₀ r}, ?_, fun y hy hyp => ?_⟩
    · rintro S rfl
      refine ⟨CFSG.Assembly.pCoreOf 2 (ggRCSXd G₀ r), hXdV, ?_, hperf, hpXd,
        Subgroup.map_subtype_le _, ggIsPGroup_pCoreOf 2 _,
        hVXd.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _), ?_⟩
      · exact ggIsSubnormal_of_normal hXdV
          ((Subgroup.normal_subgroupOf_iff_le_normalizer hXdV).mpr hVXd)
      · intro _
        exact ggRCS_quasisimple_pCoreOf hp hp2 hQ₁2 (@hq hQ₁n) hpXd
    · rw [sSup_singleton]
      exact hcov y hy hyp

theorem ggRCSLayerNbr_of_derivedAtQ {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {G₀ M : Subgroup G}
    (hG₀M : G₀ ≤ M) (hM : M ≤ Subgroup.normalizer (G₀ : Set G)) {r : G}
    (h : GGRootCentDerivedAtQ p G₀ r) : GGRCSLayerNbr p G₀ M r :=
  Or.inl (ggRCSLayerQ_of_derivedAtQ hp hp2 hG₀M hM h)

theorem ggRCSLayerQ_of_two_summands {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {G₀ M : Subgroup G}
    (hG₀M : G₀ ≤ M) (hM : M ≤ Subgroup.normalizer (G₀ : Set G)) {r : G} {Q L₁ L₂ : Subgroup G}
    (hQ2 : IsPGroup 2 Q) (hO2 : CFSG.Assembly.pCoreOf 2 (ggRCSX G₀ r) = Q)
    (hX : ggRCSX G₀ r = Q ⊔ L₁ ⊔ L₂) (hL₁Q : L₁ ≤ Subgroup.normalizer (Q : Set G))
    (hL₂Q : L₂ ≤ Subgroup.normalizer (Q : Set G))
    (hcomm : L₁ ≤ Subgroup.centralizer (L₂ : Set G)) (hL₁ : CFSG.IsQuasisimple L₁)
    (hL₂ : CFSG.IsQuasisimple L₂) (hQ₁ : Q ≤ ⁅Q ⊔ L₁, Q ⊔ L₁⁆) (hQ₂ : Q ≤ ⁅Q ⊔ L₂, Q ⊔ L₂⁆) :
    GGRCSLayerQ p G₀ M r := by
  set X := ggRCSX G₀ r with hXdef
  set V := M ⊓ Subgroup.centralizer ({r} : Set G) with hV
  have hXV : X ≤ V := (ggOTwoPrime_le _).trans (inf_le_inf_right _ hG₀M)
  have hVX : V ≤ Subgroup.normalizer (X : Set G) := fun c hc =>
    ggMem_normalizer_oTwoPrime_inf_centralizer (hM hc.1) hc.2
  have hVQ : V ≤ Subgroup.normalizer (Q : Set G) := by
    rw [← hO2]
    exact hVX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  have hQX : Q ≤ X := by rw [hX]; exact le_sup_left.trans le_sup_left
  have hL₁X : L₁ ≤ X := by rw [hX]; exact le_sup_right.trans le_sup_left
  have hL₂X : L₂ ≤ X := by rw [hX]; exact le_sup_right
  have hXsn : IsSubnormal X V :=
    ggIsSubnormal_of_normal hXV ((Subgroup.normal_subgroupOf_iff_le_normalizer hXV).mpr hVX)
  have hcomm' : L₂ ≤ Subgroup.centralizer (L₁ : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact ((Subgroup.mem_centralizer_iff.mp (hcomm ha)) b hb).symm
  have piece : ∀ L L' : Subgroup G, L ≤ Subgroup.normalizer (Q : Set G) →
      L' ≤ Subgroup.normalizer (Q : Set G) → L' ≤ Subgroup.centralizer (L : Set G) →
      L ≤ X → CFSG.IsQuasisimple L → Q ≤ ⁅Q ⊔ L, Q ⊔ L⁆ → X ≤ Q ⊔ L ⊔ L' → p ∣ Nat.card L →
      GGRCSLayerQuasi p V (Q ⊔ L) Q := by
    intro L L' hLQ hL'Q hL'L hLX hLq hQL hXL hpL
    have hYX : Q ⊔ L ≤ X := sup_le hQX hLX
    have hXN : X ≤ Subgroup.normalizer ((Q ⊔ L : Subgroup G) : Set G) := by
      refine hXL.trans (sup_le (sup_le ?_ ?_) ?_)
      · exact le_sup_left.trans Subgroup.le_normalizer
      · exact le_sup_right.trans Subgroup.le_normalizer
      · intro g hg
        exact ggRCST_mem_normalizer_sup (hL'Q hg)
          (Subgroup.centralizer_le_normalizer _ (hL'L hg))
    have hperfL : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hLq.1
    refine ⟨hYX.trans hXV, ?_, ?_, ?_, le_sup_left, hQ2, hVQ, ?_⟩
    · exact ggIsSubnormal_trans
        (ggIsSubnormal_of_normal hYX ((Subgroup.normal_subgroupOf_iff_le_normalizer hYX).mpr hXN))
        hXsn
    · refine le_antisymm (CFSG.Quasithin.A3.commutator_self_le _) (sup_le hQL ?_)
      calc L = ⁅L, L⁆ := hperfL.symm
        _ ≤ ⁅Q ⊔ L, Q ⊔ L⁆ := Subgroup.commutator_mono le_sup_right le_sup_right
    · exact dvd_trans hpL (Subgroup.card_dvd_of_le le_sup_right)
    · intro _
      exact ggRCST_isQuasisimple_quot hp hp2 hLQ le_sup_right le_rfl hQ2 inf_le_right hLq hpL
  have hX₁ : X ≤ Q ⊔ L₁ ⊔ L₂ := hX.le
  have hX₂ : X ≤ Q ⊔ L₂ ⊔ L₁ := by rw [hX, sup_right_comm]
  refine ⟨{Y | (Y = Q ⊔ L₁ ∧ p ∣ Nat.card L₁) ∨ (Y = Q ⊔ L₂ ∧ p ∣ Nat.card L₂)}, ?_, ?_⟩
  · rintro Y (⟨rfl, hp1⟩ | ⟨rfl, hp1⟩)
    · exact ⟨Q, piece L₁ L₂ hL₁Q hL₂Q hcomm' hL₁X hL₁ hQ₁ hX₁ hp1⟩
    · exact ⟨Q, piece L₂ L₁ hL₂Q hL₁Q hcomm hL₂X hL₂ hQ₂ hX₂ hp1⟩
  · intro y hy hyp
    have hmem₁ : p ∣ Nat.card L₁ → Q ⊔ L₁ ≤ sSup {Y | (Y = Q ⊔ L₁ ∧ p ∣ Nat.card L₁) ∨
        (Y = Q ⊔ L₂ ∧ p ∣ Nat.card L₂)} := fun h => le_sSup (Or.inl ⟨rfl, h⟩)
    have hmem₂ : p ∣ Nat.card L₂ → Q ⊔ L₂ ≤ sSup {Y | (Y = Q ⊔ L₁ ∧ p ∣ Nat.card L₁) ∨
        (Y = Q ⊔ L₂ ∧ p ∣ Nat.card L₂)} := fun h => le_sSup (Or.inr ⟨rfl, h⟩)
    have hN₁ : L₂ ≤ Subgroup.normalizer ((Q ⊔ L₁ : Subgroup G) : Set G) := fun g hg =>
      ggRCST_mem_normalizer_sup (hL₂Q hg) (Subgroup.centralizer_le_normalizer _ (hcomm' hg))
    have hN₂ : L₁ ≤ Subgroup.normalizer ((Q ⊔ L₂ : Subgroup G) : Set G) := fun g hg =>
      ggRCST_mem_normalizer_sup (hL₁Q hg) (Subgroup.centralizer_le_normalizer _ (hcomm hg))
    have hy₁ : y ∈ L₂ ⊔ (Q ⊔ L₁) := by rw [sup_comm]; exact hX₁ hy
    have hy₂ : y ∈ L₁ ⊔ (Q ⊔ L₂) := by rw [sup_comm]; exact hX₂ hy
    by_cases hp1 : p ∣ Nat.card L₁ <;> by_cases hp2' : p ∣ Nat.card L₂
    · exact sup_le (sup_le ((hmem₁ hp1).trans' le_sup_left) ((hmem₁ hp1).trans' le_sup_right))
        ((hmem₂ hp2').trans' le_sup_right) (hX₁ hy)
    · exact hmem₁ hp1 (ggRCST_mem_of_mem_sup_coprime hp hp2' hN₁ hy₁ hyp)
    · exact hmem₂ hp2' (ggRCST_mem_of_mem_sup_coprime hp hp1 hN₂ hy₂ hyp)
    · have h1 := ggRCST_mem_of_mem_sup_coprime hp hp2' hN₁ hy₁ hyp
      rw [ggRCS_eq_one_of_not_dvd hp (ggRCST_not_dvd_card_sup hp hp2 hQ2 hL₁Q hp1) h1 hyp]
      exact one_mem _

namespace RCSTOm

open Subgroup

theorem piece_of_summandQ {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X V Q L : Subgroup G}
    (hXV : X ≤ V) (hVX : V ≤ normalizer (X : Set G)) (hVQ : V ≤ normalizer (Q : Set G))
    (hQ2 : IsPGroup 2 Q) (hQX : Q ≤ X) (hLX : L ≤ X) (hLQ : L ≤ normalizer (Q : Set G))
    (hXN : X ≤ normalizer ((Q ⊔ L : Subgroup G) : Set G)) (hLq : CFSG.IsQuasisimple L)
    (hQL : Q ≤ ⁅Q ⊔ L, Q ⊔ L⁆) (hpL : p ∣ Nat.card L) : GGRCSLayerQuasi p V (Q ⊔ L) Q := by
  have hXsn :=
    ggIsSubnormal_of_normal hXV ((Subgroup.normal_subgroupOf_iff_le_normalizer hXV).mpr hVX)
  have hYX : Q ⊔ L ≤ X := sup_le hQX hLX
  have hperfL : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hLq.1
  refine ⟨hYX.trans hXV, ?_, ?_, ?_, le_sup_left, hQ2, hVQ, ?_⟩
  · exact ggIsSubnormal_trans
      (ggIsSubnormal_of_normal hYX ((Subgroup.normal_subgroupOf_iff_le_normalizer hYX).mpr hXN))
      hXsn
  · refine le_antisymm (CFSG.Quasithin.A3.commutator_self_le _) (sup_le hQL ?_)
    calc L = ⁅L, L⁆ := hperfL.symm
      _ ≤ ⁅Q ⊔ L, Q ⊔ L⁆ := Subgroup.commutator_mono le_sup_right le_sup_right
  · exact dvd_trans hpL (Subgroup.card_dvd_of_le le_sup_right)
  · intro _
    exact ggRCST_isQuasisimple_quot hp hp2 hLQ le_sup_right le_rfl hQ2 inf_le_right hLq hpL

theorem ggRCSLayerQ_of_three_summands {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {G₀ M : Subgroup G}
    (hG₀M : G₀ ≤ M) (hM : M ≤ normalizer (G₀ : Set G)) {r : G} {Q L₁ L₂ L₃ : Subgroup G}
    (hQ2 : IsPGroup 2 Q) (hO2 : CFSG.Assembly.pCoreOf 2 (ggRCSX G₀ r) = Q)
    (hX : ggRCSX G₀ r = Q ⊔ L₁ ⊔ L₂ ⊔ L₃) (h1Q : L₁ ≤ normalizer (Q : Set G))
    (h2Q : L₂ ≤ normalizer (Q : Set G)) (h3Q : L₃ ≤ normalizer (Q : Set G))
    (h12 : L₁ ≤ centralizer (L₂ : Set G)) (h13 : L₁ ≤ centralizer (L₃ : Set G))
    (h23 : L₂ ≤ centralizer (L₃ : Set G)) (hL₁ : GGRCSOmQuasiSummand p Q L₁)
    (hL₂ : GGRCSOmQuasiSummand p Q L₂) (hL₃ : GGRCSOmQuasiSummand p Q L₃) :
    GGRCSLayerQ p G₀ M r := by
  set X := ggRCSX G₀ r with hXdef
  set V := M ⊓ centralizer ({r} : Set G) with hV
  have hXV : X ≤ V := (ggOTwoPrime_le _).trans (inf_le_inf_right _ hG₀M)
  have hVX : V ≤ normalizer (X : Set G) := fun c hc =>
    ggMem_normalizer_oTwoPrime_inf_centralizer (hM hc.1) hc.2
  have hVQ : V ≤ normalizer (Q : Set G) := by
    rw [← hO2]
    exact hVX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  have h21 : L₂ ≤ centralizer (L₁ : Set G) := Subgroup.le_centralizer_iff.mp h12
  have h31 : L₃ ≤ centralizer (L₁ : Set G) := Subgroup.le_centralizer_iff.mp h13
  have h32 : L₃ ≤ centralizer (L₂ : Set G) := Subgroup.le_centralizer_iff.mp h23
  have hQX : Q ≤ X := by rw [hX]; exact le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hL₁X : L₁ ≤ X := by rw [hX]; exact le_sup_right.trans (le_sup_left.trans le_sup_left)
  have hL₂X : L₂ ≤ X := by rw [hX]; exact le_sup_right.trans le_sup_left
  have hL₃X : L₃ ≤ X := by rw [hX]; exact le_sup_right
  have hQN : ∀ L : Subgroup G, Q ≤ normalizer ((Q ⊔ L : Subgroup G) : Set G) := fun L =>
    le_sup_left.trans le_normalizer
  have hLN : ∀ L : Subgroup G, L ≤ normalizer ((Q ⊔ L : Subgroup G) : Set G) := fun L =>
    le_sup_right.trans le_normalizer
  have hX₁ : X ≤ normalizer ((Q ⊔ L₁ : Subgroup G) : Set G) := by
    rw [hX]
    exact sup_le (sup_le (sup_le (hQN _) (hLN _)) (le_normalizer_sup_of_centralizer h2Q h21))
      (le_normalizer_sup_of_centralizer h3Q h31)
  have hX₂ : X ≤ normalizer ((Q ⊔ L₂ : Subgroup G) : Set G) := by
    rw [hX]
    exact sup_le (sup_le (sup_le (hQN _) (le_normalizer_sup_of_centralizer h1Q h12)) (hLN _))
      (le_normalizer_sup_of_centralizer h3Q h32)
  have hX₃ : X ≤ normalizer ((Q ⊔ L₃ : Subgroup G) : Set G) := by
    rw [hX]
    exact sup_le (sup_le (sup_le (hQN _) (le_normalizer_sup_of_centralizer h1Q h13))
      (le_normalizer_sup_of_centralizer h2Q h23)) (hLN _)
  set 𝒮 : Set (Subgroup G) := {Y | (Y = Q ⊔ L₁ ∧ p ∣ Nat.card L₁) ∨
    (Y = Q ⊔ L₂ ∧ p ∣ Nat.card L₂) ∨ (Y = Q ⊔ L₃ ∧ p ∣ Nat.card L₃)} with h𝒮
  refine ⟨𝒮, ?_, fun y hy hyp => ?_⟩
  · rintro Y (⟨rfl, hpL⟩ | ⟨rfl, hpL⟩ | ⟨rfl, hpL⟩)
    · exact ⟨Q, piece_of_summandQ hp hp2 hXV hVX hVQ hQ2 hQX hL₁X h1Q hX₁
        (hL₁ hpL).1 (hL₁ hpL).2 hpL⟩
    · exact ⟨Q, piece_of_summandQ hp hp2 hXV hVX hVQ hQ2 hQX hL₂X h2Q hX₂
        (hL₂ hpL).1 (hL₂ hpL).2 hpL⟩
    · exact ⟨Q, piece_of_summandQ hp hp2 hXV hVX hVQ hQ2 hQX hL₃X h3Q hX₃
        (hL₃ hpL).1 (hL₃ hpL).2 hpL⟩
  have hy₀ : y ∈ (Q ⊔ L₂ ⊔ L₃) ⊔ L₁ := by
    have e : X = (Q ⊔ L₂ ⊔ L₃) ⊔ L₁ := by rw [hX]; ac_rfl
    rw [← e]; exact hy
  obtain ⟨B₁, hB₁, hy₁⟩ := exists_mem_sup_of_coprime hp
    (le_normalizer_sup_of_centralizer (le_normalizer_sup_of_centralizer h1Q h12) h13) hy₀ hyp
  have hB₁c : ∀ C : Subgroup G, C ≤ centralizer (L₁ : Set G) → C ≤ centralizer (B₁ : Set G) :=
    fun C hC => le_centralizer_of_eq_or_bot (hB₁.imp And.left id) hC
  have hy₁' : y ∈ (Q ⊔ B₁ ⊔ L₃) ⊔ L₂ := by
    have e : (Q ⊔ L₂ ⊔ L₃) ⊔ B₁ = (Q ⊔ B₁ ⊔ L₃) ⊔ L₂ := by ac_rfl
    rw [← e]; exact hy₁
  obtain ⟨B₂, hB₂, hy₂⟩ := exists_mem_sup_of_coprime hp
    (le_normalizer_sup_of_centralizer (le_normalizer_sup_of_centralizer h2Q (hB₁c _ h21)) h23)
    hy₁' hyp
  have hB₂c : ∀ C : Subgroup G, C ≤ centralizer (L₂ : Set G) → C ≤ centralizer (B₂ : Set G) :=
    fun C hC => le_centralizer_of_eq_or_bot (hB₂.imp And.left id) hC
  have hy₂' : y ∈ (Q ⊔ B₁ ⊔ B₂) ⊔ L₃ := by
    have e : (Q ⊔ B₁ ⊔ L₃) ⊔ B₂ = (Q ⊔ B₁ ⊔ B₂) ⊔ L₃ := by ac_rfl
    rw [← e]; exact hy₂
  obtain ⟨B₃, hB₃, hy₃⟩ := exists_mem_sup_of_coprime hp
    (le_normalizer_sup_of_centralizer (le_normalizer_sup_of_centralizer h3Q (hB₁c _ h31))
      (hB₂c _ h32)) hy₂' hyp
  have hmem : ∀ (L B : Subgroup G), Q ⊔ L ∈ 𝒮 ∨ ¬ p ∣ Nat.card L →
      ((B = L ∧ p ∣ Nat.card L) ∨ B = ⊥) → B ≤ sSup 𝒮 := by
    rintro L B hL (⟨rfl, hpL⟩ | rfl)
    · rcases hL with hL | hL
      · exact le_sup_right.trans (le_sSup hL)
      · exact absurd hpL hL
    · exact bot_le
  have h1S : Q ⊔ L₁ ∈ 𝒮 ∨ ¬ p ∣ Nat.card L₁ := by
    by_cases h : p ∣ Nat.card L₁
    · exact Or.inl (Or.inl ⟨rfl, h⟩)
    · exact Or.inr h
  have h2S : Q ⊔ L₂ ∈ 𝒮 ∨ ¬ p ∣ Nat.card L₂ := by
    by_cases h : p ∣ Nat.card L₂
    · exact Or.inl (Or.inr (Or.inl ⟨rfl, h⟩))
    · exact Or.inr h
  have h3S : Q ⊔ L₃ ∈ 𝒮 ∨ ¬ p ∣ Nat.card L₃ := by
    by_cases h : p ∣ Nat.card L₃
    · exact Or.inl (Or.inr (Or.inr ⟨rfl, h⟩))
    · exact Or.inr h
  have hBS : B₁ ⊔ B₂ ⊔ B₃ ≤ sSup 𝒮 :=
    sup_le (sup_le (hmem _ _ h1S hB₁) (hmem _ _ h2S hB₂)) (hmem _ _ h3S hB₃)
  by_cases hne : 𝒮.Nonempty
  · obtain ⟨Y, hY⟩ := hne
    have hQS : Q ≤ sSup 𝒮 := by
      have hYS : Y ≤ sSup 𝒮 := le_sSup hY
      rcases hY with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> exact le_sup_left.trans hYS
    have e : Q ⊔ B₁ ⊔ B₂ ⊔ B₃ = Q ⊔ (B₁ ⊔ B₂ ⊔ B₃) := by ac_rfl
    rw [e] at hy₃
    exact sup_le hQS hBS hy₃
  ·
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have hbot : ∀ (L B : Subgroup G), Q ⊔ L ∈ 𝒮 ∨ ¬ p ∣ Nat.card L →
        ((B = L ∧ p ∣ Nat.card L) ∨ B = ⊥) → B = ⊥ := by
      rintro L B hL (⟨rfl, hpL⟩ | rfl)
      · rcases hL with hL | hL
        · rw [hne] at hL; exact absurd hL (Set.notMem_empty _)
        · exact absurd hpL hL
      · rfl
    rw [hbot _ _ h1S hB₁, hbot _ _ h2S hB₂, hbot _ _ h3S hB₃, sup_bot_eq, sup_bot_eq,
      sup_bot_eq] at hy₃
    rw [ggRCS_eq_one_of_mem_two hp hp2 hQ2 hy₃ hyp]
    exact one_mem _

end RCSTOm

end LayersQ

section PiecesQ

variable {G : Type} [Group G] [Finite G]

theorem ggRCSStructNbrConcl_of_layerQ {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {G₀ M : Subgroup G}
    {r : G} (h : GGRCSLayerQ p G₀ M r) : GGRCSStructNbrConcl p G₀ M r := by
  obtain ⟨𝒮₀, h𝒮₀, hcov⟩ := h
  refine ⟨ggRCSImg r '' 𝒮₀, ?_, ?_⟩
  · rintro _ ⟨S₀, hS₀, rfl⟩
    obtain ⟨Q, hQ⟩ := h𝒮₀ S₀ hS₀
    exact Or.inl ⟨_, ggRCSPiece_of_layer hp hp2 hQ⟩
  · intro y hyX hyp
    have hle : sSup 𝒮₀ ≤ ((sSup (ggRCSImg r '' 𝒮₀)).comap (QuotientGroup.mk'
        (CFSG.Assembly.pCore 2 ↥(Subgroup.centralizer ({r} : Set G))))).map
          (Subgroup.centralizer ({r} : Set G)).subtype := by
      refine sSup_le fun S₀ hS₀ s hs => ?_
      obtain ⟨Q, hQ⟩ := h𝒮₀ S₀ hS₀
      have hS₀C : S₀ ≤ Subgroup.centralizer ({r} : Set G) := hQ.1.trans inf_le_right
      refine ⟨⟨s, hS₀C hs⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      have hmemS : ggRCSImg r S₀ ∈ ggRCSImg r '' 𝒮₀ := ⟨S₀, hS₀, rfl⟩
      exact (le_sSup hmemS : ggRCSImg r S₀ ≤ sSup (ggRCSImg r '' 𝒮₀))
        (mem_ggRCSImg r (y := ⟨s, hS₀C hs⟩) hs)
    obtain ⟨c, hc, hcy⟩ := hle (hcov _ hyX hyp)
    have hcy' : c = y := Subtype.ext hcy
    rw [← hcy']
    exact hc

end PiecesQ

section PiecesThree

variable {G : Type} [Group G] [Finite G]

theorem GGRCSSThreeSetting.structNbrConcl {G₀ : Subgroup G} {r : G}
    {Q S T : Subgroup G} (h : GGRCSSThreeSetting G₀ r Q S T) {M : Subgroup G} (hG₀M : G₀ ≤ M)
    (hM : M ≤ Subgroup.normalizer (G₀ : Set G)) {E : Subgroup G} (hE : IsElemAbelian 3 E)
    (hE9 : 9 ≤ Nat.card E) (hEX : E ≤ G₀ ⊓ Subgroup.centralizer {r})
    (hEM : ∀ e ∈ E, e ≠ 1 → Subgroup.centralizer {e} ≤ M) : GGRCSStructNbrConcl 3 G₀ M r := by
  refine ggRCSStructNbrConcl_of_concl
    (ggRCSStructConcl_of_layer Nat.prime_three (by norm_num) (h.layer hG₀M hM)) ?_
  intro _
  exact h.nbr hG₀M hM hE hE9 hEX hEM

end PiecesThree

end CFSG.StandardType

module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentNbr
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSThreeNbrTags
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsSp
public import CFSG.LocalAnalysis.StandardType.GGPRankBoundsSpEight

public section

namespace CFSG.StandardType

namespace RCSTSp

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.SeitzReduction.SymplecticPilot OTwoGen RootCentSp
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective elt mat_elt E)
open CFSG.RankThree.PartOne.KFCL.Sp (Hp permSp cj)
open scoped commutatorElement

section Transport

variable {G : Type} [Group G] {U : Type*} [Group U]

theorem derivedAtQ_congr {p : ℕ} {G₀ : Subgroup G} {r r' : G}
    (h : G₀ ⊓ centralizer {r} = G₀ ⊓ centralizer {r'}) :
    GGRootCentDerivedAtQ p G₀ r ↔ GGRootCentDerivedAtQ p G₀ r' := by
  unfold GGRootCentDerivedAtQ
  rw [show ggRCSX G₀ r = ggRCSX G₀ r' by rw [ggRCSX, ggRCSX, h],
    show ggRCSXd G₀ r = ggRCSXd G₀ r' by rw [ggRCSXd, ggRCSXd, ggRCSX, ggRCSX, h]]

end Transport

section Derived

variable {G : Type} [Group G] [Finite G]

theorem derivedAtQ_of_sup {U : Type*} [Group U] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {G₀ : Subgroup G} {r : G} (ψ : U →* G) (hψ : Function.Injective ψ)
    {QU LU L₀ : Subgroup U} (hX : ggRCSX G₀ r = (QU ⊔ LU).map ψ) (hQ2 : IsPGroup 2 QU)
    (hLQ : LU ≤ normalizer (QU : Set U)) (hL₀L : L₀ ≤ LU) (hL₀ : CFSG.IsQuasisimple L₀)
    (hY : ⁅LU, LU⁆ ≤ L₀) (hcov : ∀ c ∈ QU ⊔ LU, c ^ p = 1 → c ∈ QU ⊔ L₀) :
    GGRootCentDerivedAtQ p G₀ r := by
  have hXQ : ggRCSX G₀ r ≤ normalizer ((QU.map ψ : Subgroup G) : Set G) := by
    rw [hX]
    exact ggRCST_map_le_normalizer ψ (sup_le le_normalizer hLQ)
  have hsup : (QU ⊔ L₀).map ψ = QU.map ψ ⊔ L₀.map ψ := map_sup _ _ _
  refine ggRootCentDerivedAtQ_of_quasisimple hp hp2 (by rw [hX]; exact map_mono le_sup_left)
    (hQ2.map ψ) hXQ (by rw [hX]; exact map_mono (hL₀L.trans le_sup_right))
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv (L₀.equivMapOfInjective ψ hψ) hL₀) ?_ ?_
  · refine (CFSG.Quasithin.perfectCore_le_derivedSeriesOf _ 1).trans ?_
    change ⁅ggRCSX G₀ r, ggRCSX G₀ r⁆ ≤ _
    rw [hX, ← map_commutator, ← hsup]
    exact map_mono ((commutator_sup_le_sup_commutator_of_le_normalizer hLQ).trans
      (sup_le_sup_left hY QU))
  · intro y hy hyp
    rw [hX] at hy
    obtain ⟨c, hc, rfl⟩ := hy
    rw [← hsup]
    exact mem_map_of_mem ψ (hcov c hc (hψ (by rw [map_pow, hyp, map_one])))

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem derivedAtQ_long {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {m : ℕ}
    (hm : (1 ≤ m ∧ 4 ≤ Nat.card F) ∨ 3 ≤ m) (ψ : StatedSp (m + 1) F →* G)
    (hψ : Function.Injective ψ) (i : Fin (m + 1)) :
    GGRootCentDerivedAtQ p ψ.range (ψ (siegDiag F i 1)) := by
  have hX : ggRCSX ψ.range (ψ (siegDiag F i 1)) = (transvRadical F i ⊔ complSp F i).map ψ := by
    rw [ggRCSX_eq_map_centralizer ψ hψ (centralizer_siegDiag_le_ggOTwoPrime i),
      centralizer_siegDiag_eq_sup]
  have hq2 : 2 ≤ Nat.card F := Finite.one_lt_card
  have hSp : CFSG.IsQuasisimple (StatedSp m F) := by
    refine CFSG.LieType.Universal.Symplectic.isQuasisimple m F (by omega) ?_
    rcases hm with ⟨-, h4⟩ | h3
    · exact Or.inl (Or.inr h4)
    · rcases Nat.lt_or_ge (Nat.card F) 4 with h | h
      · have hF2 : Nat.card F = 2 := by
          have : Fintype F := Fintype.ofFinite F
          obtain ⟨k, -, hk⟩ := FiniteField.card F 2
          rw [Nat.card_eq_fintype_card] at h hq2 ⊢
          rw [hk] at h hq2 ⊢
          have hk1 : (k : ℕ) < 2 := by
            by_contra hk2
            push Not at hk2
            have : 2 ^ 2 ≤ 2 ^ (k : ℕ) := Nat.pow_le_pow_right (by norm_num) hk2
            omega
          have : (k : ℕ) = 1 := by have := k.ne_zero; omega
          rw [this, pow_one]
        exact Or.inr (Or.inr ⟨hF2, h3⟩)
      · exact Or.inl (Or.inr h)
  exact derivedAtQ_of_sup hp hp2 ψ hψ hX isPGroup_transvRadical complSp_le_normalizer_transvRadical
    le_rfl (CFSG.LocalCores.isQuasisimple_of_mulEquiv (complSpEquiv i) hSp)
    (CFSG.Quasithin.A3.commutator_self_le _) fun c hc _ => hc

theorem derivedAtQ_long_six {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = 2)
    (ψ : StatedSp (2 + 1) F →* G) (hψ : Function.Injective ψ) (i : Fin (2 + 1)) :
    GGRootCentDerivedAtQ p ψ.range (ψ (siegDiag F i 1)) := by
  have hX : ggRCSX ψ.range (ψ (siegDiag F i 1)) = (transvRadical F i ⊔ complSp F i).map ψ := by
    rw [ggRCSX_eq_map_centralizer ψ hψ (centralizer_siegDiag_le_ggOTwoPrime i),
      centralizer_siegDiag_eq_sup]
  set e : ↥(complSp F i) ≃* CFSG.ComponentClassification.PresentationLocal.sympFour :=
    (complSpEquiv i).symm.trans (CFSG.SeitzReduction.F4Pilot.sp4EquivSympFour hF) with he
  obtain ⟨hq, hodd⟩ := CFSG.RankThree.PartOne.derived_of_mulEquiv_sympFour e
  have hmap : (commutator ↥(complSp F i)).map (complSp F i).subtype =
      ⁅complSp F i, complSp F i⁆ := Subgroup.map_subtype_commutator _
  have hL₀ : CFSG.IsQuasisimple ↥⁅complSp F i, complSp F i⁆ :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (((commutator ↥(complSp F i)).equivMapOfInjective (complSp F i).subtype
        (Subgroup.subtype_injective _)).trans (MulEquiv.subgroupCongr hmap)) hq
  refine derivedAtQ_of_sup hp hp2 ψ hψ hX isPGroup_transvRadical
    complSp_le_normalizer_transvRadical (CFSG.Quasithin.A3.commutator_self_le _) hL₀ le_rfl ?_
  intro c hc hcp
  have hc' : c ∈ ((transvRadical F i ⊔ complSp F i : Subgroup (StatedSp (2 + 1) F)) :
      Set (StatedSp (2 + 1) F)) := hc
  rw [coe_mul_of_right_le_normalizer_left _ _ complSp_le_normalizer_transvRadical] at hc'
  obtain ⟨q, hq, l, hl, rfl⟩ := hc'
  have hlp := pow_eq_one_of_mul complSp_le_normalizer_transvRadical
    disjoint_transvRadical_complSp hq hl hcp
  have hl' := hodd hp hp2 ⟨l, hl⟩ (Subtype.ext (by simpa using hlp))
  rw [← hmap]
  exact mul_mem (mem_sup_left hq) (mem_sup_right ⟨⟨l, hl⟩, hl', rfl⟩)

theorem derivedAtQ_short_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hF4 : 4 ≤ Nat.card F)
    (ψ : StatedSp 2 F →* G) (hψ : Function.Injective ψ) {i j : Fin 2} (hij : i ≠ j) :
    GGRootCentDerivedAtQ p ψ.range (ψ (twoCentralElt 2 i j 0 1)) := by
  have hC : centralizer ({twoCentralElt 2 i j (0 : F) 1} : Set (StatedSp 2 F)) =
      wRadical F i j ⊔ (shortBlock F hij).range := by
    refine le_antisymm ?_ (sup_le (wRadical_le_centralizer_twoCentralElt 0 1) ?_)
    · have h := centralizer_a2_le_of_ne (K := F) hij
      rwa [suppGroup_offPQ_two hij, sup_bot_eq] at h
    · rintro _ ⟨A, rfl⟩
      exact shortBlock_mem_centralizer hij A 1
  have hX : ggRCSX ψ.range (ψ (twoCentralElt 2 i j 0 1)) =
      (wRadical F i j ⊔ (shortBlock F hij).range).map ψ := by
    rw [ggRCSX_eq_map_centralizer ψ hψ (centralizer_twoCentralElt_le_ggOTwoPrime hij), hC]
  have hCN : centralizer ({twoCentralElt 2 i j (0 : F) 1} : Set (StatedSp 2 F)) ≤
      normalizer (wRadical F i j : Set (StatedSp 2 F)) := by
    rw [centralizer_twoCentralElt_eq_sup hij (one_ne_zero (α := F))]
    exact sup_le le_normalizer (range_leviHom_le_normalizer_wRadical hij one_ne_zero)
  have hLQ : (shortBlock F hij).range ≤ normalizer (wRadical F i j : Set (StatedSp 2 F)) := by
    rw [hC] at hCN
    exact le_sup_right.trans hCN
  have hSL : CFSG.IsQuasisimple (shortBlock F hij).range :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective (shortBlock_injective hij))
      (CFSG.SeitzReduction.LinearPilot.isQuasisimple_specialLinearGroup_of_le le_rfl
        (Or.inr hF4))
  exact derivedAtQ_of_sup hp hp2 ψ hψ hX (isPGroup_wRadical hij) hLQ le_rfl hSL
    (CFSG.Quasithin.A3.commutator_self_le _) fun c hc _ => hc

theorem derivedAtQ_long_all {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {n f : ℕ}
    (hF : Nat.card F = 2 ^ f) (hn : 2 ≤ n) (hnf : (n, 2 ^ f) ≠ (2, 2))
    (ψ : StatedSp n F →* G) (hψ : Function.Injective ψ) (i : Fin n) :
    GGRootCentDerivedAtQ p ψ.range (ψ (siegDiag F i 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · have := Finite.one_lt_card (α := F)
      rw [hF] at this
      norm_num at this
    · exact h
  by_cases hq : 4 ≤ Nat.card F ∨ 3 ≤ m
  · refine derivedAtQ_long hp hp2 ?_ ψ hψ i
    rcases hq with h | h
    · exact Or.inl ⟨by omega, h⟩
    · exact Or.inr h
  · push Not at hq
    have hF2 : Nat.card F = 2 := by
      rw [hF] at hq ⊢
      have : f < 2 := by
        by_contra hf2
        push Not at hf2
        have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
        omega
      have : f = 1 := by omega
      rw [this, pow_one]
    have hm2 : m = 2 := by
      have h1 : m ≠ 1 := by
        rintro rfl
        have h2f : 2 ^ f = 2 := hF.symm.trans hF2
        rw [h2f] at hnf
        exact hnf rfl
      omega
    subst hm2
    exact derivedAtQ_long_six hp hp2 hF2 ψ hψ i

end Derived

section Short

variable {F : Type} [Field F] {n : ℕ}
variable [Finite F] [CharP F 2] {G : Type} [Group G] [Finite G]

theorem layerQ_short_std (hK : 4 ≤ Nat.card F) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ψ : StatedSp (n + 3) F →* G) (hψ : Function.Injective ψ) {M : Subgroup G}
    (hG₀M : ψ.range ≤ M) (hM : M ≤ normalizer (ψ.range : Set G)) {r : G}
    (hr : ψ.range ⊓ centralizer {r} =
      ψ.range ⊓ centralizer {ψ (twoCentralElt (n + 3) 1 2 (0 : F) 1)}) :
    GGRCSLayerQ p ψ.range M r := by
  have h12 := one_ne_two_fin (n := n)
  set QW := wRadical F (1 : Fin (n + 3)) 2 with hQW
  set S := (shortBlock F h12).range with hS
  set T := spCompl12 F n with hT
  have hC : centralizer ({twoCentralElt (n + 3) 1 2 (0 : F) 1} : Set (StatedSp (n + 3) F)) =
      QW ⊔ (S ⊔ T) := (perfectCore_centralizer_a2 hK).2
  have hX : ggRCSX ψ.range r = (QW ⊔ (S ⊔ T)).map ψ := by
    change ggOTwoPrime (ψ.range ⊓ centralizer {r}) = _
    rw [hr]
    change ggRCSX ψ.range (ψ (twoCentralElt (n + 3) 1 2 0 1)) = _
    rw [ggRCSX_eq_map_centralizer ψ hψ (centralizer_twoCentralElt_le_ggOTwoPrime h12), hC]
  have hCN : centralizer ({twoCentralElt (n + 3) 1 2 (0 : F) 1} : Set (StatedSp (n + 3) F)) ≤
      normalizer (QW : Set (StatedSp (n + 3) F)) := by
    rw [centralizer_twoCentralElt_eq_sup h12 (one_ne_zero (α := F))]
    exact sup_le le_normalizer (range_leviHom_le_normalizer_wRadical h12 one_ne_zero)
  have hSQ : S ≤ normalizer (QW : Set (StatedSp (n + 3) F)) :=
    (hC ▸ (le_sup_left.trans le_sup_right : S ≤ QW ⊔ (S ⊔ T))).trans hCN
  have hTQ : T ≤ normalizer (QW : Set (StatedSp (n + 3) F)) :=
    (hC ▸ (le_sup_right.trans le_sup_right : T ≤ QW ⊔ (S ⊔ T))).trans hCN
  have hQ2 : IsPGroup 2 (QW.map ψ) := (isPGroup_wRadical h12).map ψ
  have hO2 : CFSG.Assembly.pCoreOf 2 (ggRCSX ψ.range r) = QW.map ψ := by
    rw [hX, Subgroup.map_sup]
    refine ggRCST_pCoreOf_eq rfl hQ2 (ggRCST_map_le_normalizer ψ (sup_le hSQ hTQ)) ?_
    intro N hNM hN2 hMN
    set N' : Subgroup ↥(a2Levi F n) := (N.comap ψ).subgroupOf (a2Levi F n) with hN'
    have hN'n : N'.Normal := by
      refine ⟨fun x hx g => ?_⟩
      rw [hN', Subgroup.mem_subgroupOf, Subgroup.mem_comap] at hx ⊢
      have hg : ψ (g : StatedSp (n + 3) F) ∈ (S ⊔ T).map ψ := ⟨g, g.2, rfl⟩
      have := (Subgroup.mem_normalizer_iff.mp (hMN hg) (ψ x)).mp hx
      simpa using this
    have hN'2 : IsPGroup 2 N' := by
      rintro ⟨x, hx⟩
      rw [hN', Subgroup.mem_subgroupOf, Subgroup.mem_comap] at hx
      obtain ⟨k, hk⟩ := hN2 ⟨_, hx⟩
      refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
      apply hψ
      have := congrArg Subtype.val hk
      simpa using this
    have hbot := eq_bot_of_normal_of_isPGroup_a2Levi hK N' hN'2
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨a, ha, rfl⟩ := hNM hy
    have haN : (⟨a, ha⟩ : ↥(a2Levi F n)) ∈ N' := by
      rw [hN', Subgroup.mem_subgroupOf, Subgroup.mem_comap]
      exact hy
    rw [hbot, Subgroup.mem_bot] at haN
    have : a = 1 := congrArg Subtype.val haN
    rw [this, map_one]
    exact one_mem _
  have hcomm : S.map ψ ≤ centralizer ((T.map ψ : Subgroup G) : Set G) := by
    rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨t, ht, rfl⟩
    have ht' : t ∈ suppGroup {t : Fin (n + 3) ⊕ Fin (n + 3) | ¬ OffPQ 1 2 t}ᶜ := by
      have : {t : Fin (n + 3) ⊕ Fin (n + 3) | ¬ OffPQ 1 2 t}ᶜ = {t | OffPQ 1 2 t} := by
        ext t
        simp
      rw [this, ← spCompl12_eq_suppGroup]
      exact ht
    have hc := (commute_suppGroup_compl (shortBlock_mem_suppGroup (n := n) A) ht').eq
    rw [← map_mul, ← map_mul, hc]
  have hSq : CFSG.IsQuasisimple (S.map ψ) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((MonoidHom.ofInjective (shortBlock_injective h12)).trans (S.equivMapOfInjective ψ hψ))
      (CFSG.SeitzReduction.LinearPilot.isQuasisimple_specialLinearGroup_of_le le_rfl (Or.inr hK))
  have hTq : CFSG.IsQuasisimple (T.map ψ) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((spCompl12Equiv F n).trans (T.equivMapOfInjective ψ hψ))
      (CFSG.LieType.Universal.Symplectic.isQuasisimple (n + 1) F (by omega) (Or.inl (Or.inr hK)))
  refine ggRCSLayerQ_of_two_summands hp hp2 hG₀M hM hQ2 hO2
    (by rw [hX, Subgroup.map_sup, Subgroup.map_sup, sup_assoc]) (ggRCST_map_le_normalizer ψ hSQ)
    (ggRCST_map_le_normalizer ψ hTQ) hcomm hSq hTq ?_ ?_
  · rw [← Subgroup.map_sup, ← map_commutator]
    exact map_mono wRadical_le_commutator_shortBlock
  · rw [← Subgroup.map_sup, ← map_commutator, commutator_wRadical_sup_spCompl12 hK]
    exact map_mono le_sup_left

theorem layerQ_short (hK : 4 ≤ Nat.card F) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ψ : StatedSp (n + 3) F →* G) (hψ : Function.Injective ψ) {M : Subgroup G}
    (hG₀M : ψ.range ≤ M) (hM : M ≤ normalizer (ψ.range : Set G)) {r : G}
    {h : StatedSp (n + 3) F} {i j : Fin (n + 3)} (hij : i ≠ j)
    (hr : ψ.range ⊓ centralizer {r} =
      ψ.range ⊓ centralizer {ψ (h * twoCentralElt (n + 3) i j (0 : F) 1 * h⁻¹)}) :
    GGRCSLayerQ p ψ.range M r := by
  obtain ⟨g, hg⟩ := exists_conj_one_two (F := F) hij
  have hrange : (ψ.comp (MulAut.conj (h * g)).toMonoidHom).range = ψ.range :=
    range_comp_conj ψ (h * g)
  have h1 : ψ (h * twoCentralElt (n + 3) i j (0 : F) 1 * h⁻¹) =
      (ψ.comp (MulAut.conj (h * g)).toMonoidHom) (twoCentralElt (n + 3) 1 2 0 1) := by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hg]
    congr 1
    group
  have key := layerQ_short_std hK hp hp2 (ψ.comp (MulAut.conj (h * g)).toMonoidHom)
    (comp_conj_injective hψ _) (M := M) (by rw [hrange]; exact hG₀M) (by rw [hrange]; exact hM)
    (r := r) (by rw [hrange, ← h1]; exact hr)
  rwa [hrange] at key

end Short

end RCSTSp

section LayerNbr

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.SeitzReduction.SymplecticPilot RootCentSp
open CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras

theorem ggRCSLayerNbr_sp {G : Type} [Group G] [Finite G] {n f : ℕ}
    (ψ : StatedSp n (GaloisField 2 f) →* G) (hadm : StatedLieAdmissible .PSp n 2 f)
    (hψ : Function.Injective ψ) (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥)
    (h4 : GGTwoLocalRankFour 3 (Subgroup.normalizer (ψ.range : Set G))) {r : G}
    (hr : GGRootInvolution (Symplectic.rootDatum n (GaloisField 2 f)) .PSp ψ r) :
    GGRCSLayerNbr 3 ψ.range (Subgroup.normalizer (ψ.range : Set G)) r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f :=
    GaloisField.card 2 f (by have := hadm.2.1; omega)
  obtain ⟨-, -, hn, hnf⟩ := id hadm
  have hr' := hr
  obtain ⟨hr2, γ, ⟨hγ, -⟩, u, hru⟩ := hr'
  obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hru
  have hx1 : x ≠ 1 := by
    rintro rfl
    simp at hr2
  obtain ⟨ρ, hρ⟩ := exists_stdVec_of_mem_roots hγ
  obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hρ).1 hx
  have hc : c ≠ 0 := by
    rintro rfl
    exact hx1 (elt_zero ρ)
  have key : ∀ y : StatedSp n (GaloisField 2 f),
      Subgroup.centralizer ({y} : Set (StatedSp n (GaloisField 2 f))) =
        Subgroup.centralizer ({elt ρ (1 : GaloisField 2 f)} : Set (StatedSp n (GaloisField 2 f))) →
      ψ.range ⊓ Subgroup.centralizer {ψ ((MulAut.conj u).toMonoidHom (elt ρ c))} =
        ψ.range ⊓ Subgroup.centralizer {ψ (u * y * u⁻¹)} := by
    intro y hy
    rw [RCSTSp.range_inf_centralizer_of_injective hψ, RCSTSp.range_inf_centralizer_of_injective hψ]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [OTwoGen.centralizer_conj_eq_map, OTwoGen.centralizer_conj_eq_map,
      centralizer_elt_eq ρ hc, hy]
  have hconj : ∀ (g y : StatedSp n (GaloisField 2 f)),
      ψ (u * (g * y * g⁻¹) * u⁻¹) = (ψ.comp (MulAut.conj (u * g)).toMonoidHom) y := by
    intro g y
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    congr 1
    group
  rcases RCSTSp.elt_one_eq_conj (F := GaloisField 2 f) ρ with ⟨g, i, hg⟩ | ⟨g, i, j, hij, hg⟩
  ·
    refine ggRCSLayerNbr_of_derivedAtQ Nat.prime_three (by norm_num) Subgroup.le_normalizer
      le_rfl ?_
    rw [RCSTSp.derivedAtQ_congr (key _ (by rw [hg])), hconj,
      ← RCSTSp.range_comp_conj ψ (u * g)]
    exact RCSTSp.derivedAtQ_long_all Nat.prime_three (by norm_num) hF hn hnf _
      (RCSTSp.comp_conj_injective hψ _) i
  · by_cases hn3 : 3 ≤ n
    ·
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      have hrc : ψ.range ⊓ Subgroup.centralizer
            {ψ ((MulEquiv.toMonoidHom (MulAut.conj u)) (elt ρ c))} =
          ψ.range ⊓ Subgroup.centralizer
            {ψ ((u * g) * twoCentralElt (m + 3) i j (0 : GaloisField 2 f) 1 * (u * g)⁻¹)} := by
        rw [key _ (by rw [hg])]
        congr 3
        group
      by_cases hf : f = 1
      ·
        subst hf
        by_cases hm : m ≤ 1
        ·
          exact absurd h4 (ggSpSixEightRankInput_holds G (m + 3) ψ (by omega) hψ hC)
        ·
          have hK : Nat.card (GaloisField 2 1) = 2 := by
            rw [GaloisField.card 2 1 one_ne_zero, pow_one]
          exact Or.inr ⟨rfl, RCSTSp2.sThreeSetting_short_two_three_gen hK (by omega) ψ hψ
            hij hrc⟩
      ·
        have hK : 4 ≤ Nat.card (GaloisField 2 f) := by
          rw [hF]
          have h2f : 2 ≤ f := by
            by_contra h
            have h1 : f = 1 := by have := hadm.2.1; omega
            exact hf h1
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h2f
        exact Or.inl (RCSTSp.layerQ_short hK Nat.prime_three (by norm_num) ψ hψ
          Subgroup.le_normalizer le_rfl hij hrc)
    ·
      obtain rfl : n = 2 := by omega
      have hF4 : 4 ≤ Nat.card (GaloisField 2 f) := by
        rw [hF]
        have hf2 : 2 ^ f ≠ 2 := fun h => hnf (by rw [h])
        have : 2 ≤ f := by
          by_contra h
          have : f = 1 := by have := hadm.2.1; omega
          exact hf2 (by rw [this, pow_one])
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) this
      refine ggRCSLayerNbr_of_derivedAtQ Nat.prime_three (by norm_num) Subgroup.le_normalizer
        le_rfl ?_
      rw [RCSTSp.derivedAtQ_congr (key _ (by rw [hg])), hconj,
        ← RCSTSp.range_comp_conj ψ (u * g)]
      exact RCSTSp.derivedAtQ_short_two Nat.prime_three (by norm_num) hF4 _
        (RCSTSp.comp_conj_injective hψ _) hij

end LayerNbr

section Tag

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.SeitzReduction.SymplecticPilot RootCentSp
open CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras

theorem ggRootCentLayerNbrTag_PSp : GGRootCentLayerNbrTag .PSp := by
  intro G _ _ n f ψ hadm _ hker hC h4 _ r hr
  have hψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (center_statedSp_eq_bot (K := GaloisField 2 f) n).le
  exact ggRCSLayerNbr_sp ψ hadm hψ hC h4 hr

end Tag

end CFSG.StandardType

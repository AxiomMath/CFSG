module

public import CFSG.Timmesfeld.ARS.ExclNSRoots
public import Certificates.Certificate43
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate123

public section

namespace CFSG.Timmesfeld.ARS.ExclNS

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.TitsSimplicity
open scoped commutatorElement

section Frame

variable {G' : Type} [Group G'] {R' : Set (Subgroup G')}

@[expose] def memberRoots (F : NSLFrameData G' R') : Set (Fin F.D.rank → ℤ) :=
  {γ | ∃ w, γ = weylAction F.D.isFiniteType w (Pi.single F.i₀ 1)}

variable (F : NSLFrameData G' R')

theorem memberRoots_subset {γ : Fin F.D.rank → ℤ} (hγ : γ ∈ memberRoots F) : γ ∈ F.D.roots := by
  obtain ⟨w, rfl⟩ := hγ
  exact Or.inl ⟨w, F.i₀, rfl⟩

theorem weylAction_mem_memberRoots {γ : Fin F.D.rank → ℤ} (hγ : γ ∈ memberRoots F)
    (w : (coxeterMatrix F.D.isFiniteType).Group) :
    weylAction F.D.isFiniteType w γ ∈ memberRoots F := by
  obtain ⟨w', rfl⟩ := hγ
  exact ⟨w * w', by rw [weylAction_mul_apply]⟩

theorem neg_mem_memberRoots {γ : Fin F.D.rank → ℤ} (hγ : γ ∈ memberRoots F) :
    -γ ∈ memberRoots F := by
  obtain ⟨w, rfl⟩ := hγ
  refine ⟨w * (coxeterMatrix F.D.isFiniteType).toCoxeterSystem.simple F.i₀, ?_⟩
  rw [weylAction_mul_apply, weylAction_simple_single, map_neg]

theorem map_rootGroup_weylAction (w : (coxeterMatrix F.D.isFiniteType).Group)
    {γ : Fin F.D.rank → ℤ} (hγ : γ ∈ F.D.roots) :
    (F.D.rootGroup (weylAction F.D.isFiniteType w γ)).map F.Ψ =
      conjSub ((F.D.rootGroup γ).map F.Ψ) (F.Ψ (nrep F.hct w)) := by
  rw [map_conjSub_eq, actsAs_nrep F.hct w γ hγ]

theorem map_rootGroup_mem (hR : IsRootClass R') {γ : Fin F.D.rank → ℤ}
    (hγ : γ ∈ memberRoots F) : (F.D.rootGroup γ).map F.Ψ ∈ R' := by
  obtain ⟨w, rfl⟩ := hγ
  rw [map_rootGroup_weylAction F w ((RootSystem.ofCartan F.D.isFiniteType F.D.divisible).single_mem
    F.i₀)]
  exact hR.conjSub_mem F.mem _

theorem opposite_map_rootGroup {γ : Fin F.D.rank → ℤ} (hγ : γ ∈ memberRoots F) :
    Opposite ((F.D.rootGroup γ).map F.Ψ) ((F.D.rootGroup (-γ)).map F.Ψ) := by
  obtain ⟨w, rfl⟩ := hγ
  have hα := (RootSystem.ofCartan F.D.isFiniteType F.D.divisible).single_mem F.i₀
  have hα' := (RootSystem.ofCartan F.D.isFiniteType F.D.divisible).neg_mem _ hα
  rw [← map_neg, map_rootGroup_weylAction F w hα, map_rootGroup_weylAction F w hα']
  exact F.opp.conj _

theorem isPGroup_map_negUnipotent : IsPGroup 2 ↥((negUnipotent F.D).map F.Ψ) :=
  (isPGroup_negUnipotent F.hext F.pgroup).map F.Ψ

theorem iSup_le_normalizer_negUnipotent :
    (⨆ i, F.H i) ≤ Subgroup.normalizer ((negUnipotent F.D : Subgroup F.K) : Set F.K) :=
  le_normalizer_iSup₂ fun _ htT γ hγ _ hy =>
    (le_iSup₂ (f := fun γ (_ : γ ∈ {γ | γ ∈ F.D.roots ∧ ht γ < 0}) => F.D.rootGroup γ) γ hγ)
      ((Subgroup.mem_normalizer_iff.1 (iSup_le_normalizer_rootGroup F.hct hγ.1 htT) _).1 hy)

theorem commuting_of_commuting_map {β β' : Fin F.D.rank → ℤ} (hβ : β ∈ F.D.roots)
    (hβ0 : ht β < 0) (hβ' : β' ∈ F.D.roots) (hβ'0 : ht β' < 0)
    (h : Commuting ((F.D.rootGroup β).map F.Ψ) ((F.D.rootGroup β').map F.Ψ)) :
    Commuting (F.D.rootGroup β) (F.D.rootGroup β') := by
  intro x hx y hy
  have hc := h _ (Subgroup.mem_map_of_mem F.Ψ hx) _ (Subgroup.mem_map_of_mem F.Ψ hy)
  have h1 : ⁅x, y⁆ ∈ F.Ψ.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.2 hc
  have h2 : ⁅x, y⁆ ∈ negUnipotent F.D := by
    have hxU := rootGroup_le_negUnipotent hβ hβ0 hx
    have hyU := rootGroup_le_negUnipotent hβ' hβ'0 hy
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hxU hyU) (inv_mem hxU)) (inv_mem hyU)
  exact commutatorElement_eq_one_iff_commute.1
    (eq_one_of_mem_negUnipotent_of_mem_center F.hct F.hext h2 (F.ker h1))

end Frame

variable {G : Type} [Group G] {R : Set (Subgroup G)} {A A₀ : Subgroup G}

abbrev LeviBar (R : Set (Subgroup G)) (A A₀ : Subgroup G) : Type :=
  ↥(levi R A A₀) ⧸ Subgroup.center ↥(levi R A A₀)

theorem exists_mem_leviSet_of_mem_quotClass {X' : Subgroup (LeviBar R A A₀)}
    (h : X' ∈ quotClass (levi R A A₀) (leviSet R A A₀)) :
    ∃ X ∈ leviSet R A A₀, quotMap (levi R A A₀) X = X' := h

theorem opposite_of_quot (hS : Sec13 R A A₀) {X Y : Subgroup G} (hX : X ∈ leviSet R A A₀)
    (hY : Y ∈ leviSet R A A₀)
    (h : Opposite (quotMap (levi R A A₀) X) (quotMap (levi R A A₀) Y)) : Opposite X Y := by
  obtain ⟨E₀, hE₀, -⟩ := hS.nondeg
  have key := Levi.quot_hopp hS.hyp hS.mem hS.sec8.2 hS.opp hE₀
  rw [comp_eq hS hE₀] at key
  exact key X hX Y hY h

variable (F : NSLFrameData (LeviBar R A A₀) (quotClass (levi R A A₀) (leviSet R A A₀)))

structure LowMember (B : Subgroup G) : Prop where
  mem : B ∈ lambdaStar R A A₀
  le : (negUnipotent F.D).map F.Ψ ≤ stabBar R A A₀ B

@[expose] def lowSet (B : Subgroup G) : Set (Fin F.D.rank → ℤ) :=
  {β | β ∈ memberRoots F ∧
    ∃ X ∈ deltaSet R A A₀ B, quotMap (levi R A A₀) X = (F.D.rootGroup β).map F.Ψ}

theorem exists_lowMember (hS : Sec13 R A A₀) : ∃ B, LowMember F B := by
  obtain ⟨B, hB, hle⟩ := exists_le_stabBar_of_isPGroup hS (isPGroup_map_negUnipotent F)
  exact ⟨B, hB, hle⟩

variable {F}

namespace LowMember

variable (hS : Sec13 R A A₀) {B : Subgroup G} (hB : LowMember F B)
include hS hB

theorem commuting_of_le {X : Subgroup G} (hX : X ∈ leviSet R A A₀)
    (hle : quotMap (levi R A A₀) X ≤ (negUnipotent F.D).map F.Ψ) : Commuting X B :=
  (commuting_iff_quotMap_le_stabBar hS hB.mem hX).2 (hle.trans hB.le)

theorem conjSub_mem_deltaSet {X : Subgroup G} (hX : X ∈ deltaSet R A A₀ B) (v : ↥(levi R A A₀))
    (hv : QuotientGroup.mk' (Subgroup.center ↥(levi R A A₀)) v ∈ stabBar R A A₀ B) :
    conjSub X (v : G) ∈ deltaSet R A A₀ B := by
  have hvB := conjSub_eq_self_iff.2 ((mk_mem_stabBar_iff hS hB.mem v).1 hv)
  rw [← hvB, ← conjSet_deltaSet hS.hyp.root v.2]
  exact conjSub_mem_conjSet hX _

theorem exists_eq_conjSub {γ₁ : Fin F.D.rank → ℤ} (hγ₁ : γ₁ ∈ memberRoots F)
    (hγ₁U : negUnipotent F.D ≤ Subgroup.normalizer (F.D.rootGroup γ₁ : Set F.K))
    {X : Subgroup G} (hX : X ∈ deltaSet R A A₀ B) :
    ∃ β ∈ lowSet F B, ∃ u ∈ negUnipotent F.D,
      quotMap (levi R A A₀) X = conjSub ((F.D.rootGroup β).map F.Ψ) (F.Ψ u) := by
  have hq := quotHyp hS
  have hγ₁R := memberRoots_subset F hγ₁
  obtain ⟨g, hg⟩ := hq.root.exists_conjSub_eq (map_rootGroup_mem F hq.root hγ₁)
    (⟨X, hX.1, rfl⟩ : quotMap (levi R A A₀) X ∈ quotClass (levi R A A₀) (leviSet R A A₀))
  obtain ⟨k, rfl⟩ := F.surj g
  obtain ⟨b, hb, y, hy, b', hb', rfl⟩ := exists_eq_mul_mul_negBorel F.hct F.hext k
  obtain ⟨w, hw⟩ := exists_actsAs F.hct hy
  have hTN : (⨆ i, F.H i) ≤ Subgroup.normalizer (F.D.rootGroup γ₁ : Set F.K) :=
    iSup_le_normalizer_rootGroup F.hct hγ₁R
  have hb'N : b' ∈ Subgroup.normalizer (F.D.rootGroup γ₁ : Set F.K) := sup_le hTN hγ₁U hb'
  have hb2 : b ∈ ((negUnipotent F.D ⊔ ⨆ i, F.H i : Subgroup F.K) : Set F.K) := by
    rw [sup_comm]
    exact hb
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (iSup_le_normalizer_negUnipotent F)]
    at hb2
  obtain ⟨u, hu, t, ht, rfl⟩ := Set.mem_mul.1 hb2
  have hwR : weylAction F.D.isFiniteType w γ₁ ∈ F.D.roots :=
    weylAction_mem_roots _ _ hγ₁R
  have hconj : conjSub ((F.D.rootGroup γ₁).map F.Ψ) (F.Ψ (u * t * y * b')) =
      conjSub ((F.D.rootGroup (weylAction F.D.isFiniteType w γ₁)).map F.Ψ) (F.Ψ u) := by
    rw [map_mul, map_mul, map_mul, conjSub_mul, conjSub_mul, conjSub_mul, map_conjSub_eq F.Ψ _ b',
      (RankOne.map_conj_eq_self_iff).2 hb'N, map_conjSub_eq F.Ψ _ y, hw γ₁ hγ₁R,
      map_conjSub_eq F.Ψ _ t,
      (RankOne.map_conj_eq_self_iff).2 (iSup_le_normalizer_rootGroup F.hct hwR ht)]
  rw [hconj] at hg
  refine ⟨_, ⟨weylAction_mem_memberRoots F hγ₁ w, ?_⟩, u, hu, hg.symm⟩
  obtain ⟨v, hv⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥(levi R A A₀)) (F.Ψ u⁻¹)
  have hvB : QuotientGroup.mk' (Subgroup.center ↥(levi R A A₀)) v ∈ stabBar R A A₀ B := by
    rw [hv]
    exact hB.le (Subgroup.mem_map_of_mem F.Ψ (inv_mem hu))
  refine ⟨conjSub X (v : G), conjSub_mem_deltaSet hS hB hX v hvB, ?_⟩
  rw [LeviQuot.quotMap_conjSub X v.2]
  have e : QuotientGroup.mk' (Subgroup.center ↥(levi R A A₀)) ⟨(v : G), v.2⟩ = F.Ψ u⁻¹ := hv
  rw [e, ← hg, map_inv, conjSub_conjSub_inv]

theorem ht_lt_zero {β : Fin F.D.rank → ℤ} (hβ : β ∈ lowSet F B) : ht β < 0 := by
  have := hS.hyp.finite
  have hq := quotHyp hS
  have hβR := memberRoots_subset F hβ.1
  rcases ht_pos_or_neg hβR with ⟨-, hpos⟩ | ⟨-, hneg⟩
  · exfalso
    obtain ⟨Y, hY, hYβ⟩ := hβ.2
    have hβ' := neg_mem_memberRoots F hβ.1
    obtain ⟨Y', hY', hY'β⟩ := exists_mem_leviSet_of_mem_quotClass
      (map_rootGroup_mem F hq.root hβ')
    have hopp : Opposite Y' Y := by
      refine opposite_of_quot hS hY' hY.1 ?_
      rw [hY'β, hYβ]
      exact (opposite_map_rootGroup F hβ.1).symm
    have hc : Commuting Y' B := commuting_of_le hS hB hY' (by
      rw [hY'β]
      exact Subgroup.map_mono (rootGroup_le_negUnipotent (memberRoots_subset F hβ')
        (by rw [ht_neg]; omega)))
    exact not_commuting_of_opposite_of_mem_lambdaSet hS.hyp.root hY'.1.1 hopp
      (mem_lambdaSet_comm hB.mem.1.1.1 hY.2) hc
  · exact hneg

theorem nonpos {β : Fin F.D.rank → ℤ} (hβ : β ∈ lowSet F B) : β ≤ 0 := by
  rcases ht_pos_or_neg (memberRoots_subset F hβ.1) with ⟨-, h⟩ | ⟨h, -⟩
  · exact absurd (ht_lt_zero hS hB hβ) (not_lt.2 h.le)
  · exact h

theorem quotMap_le_lower {γ₁ : Fin F.D.rank → ℤ} (hγ₁ : γ₁ ∈ memberRoots F)
    (hγ₁U : negUnipotent F.D ≤ Subgroup.normalizer (F.D.rootGroup γ₁ : Set F.K))
    {X : Subgroup G} (hX : X ∈ deltaSet R A A₀ B) :
    quotMap (levi R A A₀) X ≤ (⨆ δ ∈ lowerRoots F.D (lowSet F B), F.D.rootGroup δ).map F.Ψ := by
  obtain ⟨β, hβ, u, hu, he⟩ := exists_eq_conjSub hS hB hγ₁ hγ₁U hX
  rw [he, map_conjSub_eq]
  refine Subgroup.map_mono ?_
  have hN := negUnipotent_le_normalizer_lower F.hext F.hdiv (fun β hβ => nonpos hS hB hβ) hu
  rw [← (RankOne.map_conj_eq_self_iff).2 hN]
  exact Subgroup.map_mono (le_iSup₂_of_le (f := fun δ (_ : δ ∈ lowerRoots F.D (lowSet F B)) =>
    F.D.rootGroup δ) β ⟨memberRoots_subset F hβ.1, β, hβ, le_rfl⟩ le_rfl)

theorem mem_stabBar_n {γ₁ : Fin F.D.rank → ℤ} (hγ₁ : γ₁ ∈ memberRoots F)
    (hγ₁U : negUnipotent F.D ≤ Subgroup.normalizer (F.D.rootGroup γ₁ : Set F.K))
    {s : Fin F.D.rank} (hs : -Pi.single s 1 ∉ lowSet F B) :
    F.Ψ (F.n s) ∈ stabBar R A A₀ B := by
  have hR := hS.hyp.root
  obtain ⟨v, hv⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥(levi R A A₀)) (F.Ψ (F.n s))
  have hB' : conjSub B (v : G) ∈ lambdaStar R A A₀ :=
    conjSub_mem_lambdaStar_of_mem_levi hR hB.mem v.2
  have hL : (⨆ δ ∈ lowerRoots F.D (lowSet F B), F.D.rootGroup δ).map F.Ψ ≤
      stabBar R A A₀ (conjSub B (v : G)) := by
    rw [stabBar_conjSub hS hB.mem v, hv, Subgroup.map_iSup]
    refine iSup_le fun δ => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hδ => ?_
    obtain ⟨β, hβS, hδβ⟩ := hδ.2
    have hδne : δ ≠ -Pi.single s 1 := fun e => hs (by
      rw [eq_neg_single_of_le (memberRoots_subset F hβS.1) (nonpos hS hB hβS) (e ▸ hδβ)] at hβS
      exact hβS)
    have hδ0 : ht δ < 0 := ht_neg_of_nonpos hδ.1 (hδβ.trans (nonpos hS hB hβS))
    obtain ⟨hsδ, -⟩ := ht_neg_reflection F.hdiv hδ.1 hδ0 hδne
    have hsδR := weylAction_mem_roots F.D.isFiniteType
      ((coxeterMatrix F.D.isFiniteType).toCoxeterSystem.simple s) hδ.1
    have e := actsAs_n F.hct s _ hsδR
    rw [← weylAction_mul_apply, CoxeterSystem.simple_mul_simple_self, map_one,
      Module.End.one_apply] at e
    rw [← e, ← map_conjSub_eq]
    exact Subgroup.map_mono (Subgroup.map_mono (rootGroup_le_negUnipotent hsδR hsδ)) |>.trans
      (Subgroup.map_mono hB.le)
  have hBv : conjSub B (v : G) = B := by
    refine (eq_of_forall_quotMap_le_stabBar hS hB' hB.mem fun X hX => ?_).symm
    exact (quotMap_le_lower hS hB hγ₁ hγ₁U hX).trans hL
  rw [← hv]
  exact (mk_mem_stabBar_iff hS hB.mem v).2 (conjSub_eq_self_iff.1 hBv)

theorem exists_neg_single_mem {γ₁ : Fin F.D.rank → ℤ} (hγ₁ : γ₁ ∈ memberRoots F)
    (hγ₁U : negUnipotent F.D ≤ Subgroup.normalizer (F.D.rootGroup γ₁ : Set F.K)) :
    ∃ s, -Pi.single s 1 ∈ lowSet F B := by
  by_contra! hall
  apply stabBar_ne_top hS hB.mem
  have htop := eq_top_of_negUnipotent_le F.hct (P := (stabBar R A A₀ B).comap F.Ψ)
    (Subgroup.map_le_iff_le_comap.1 hB.le) fun s => mem_stabBar_n hS hB hγ₁ hγ₁U (hall s)
  rw [eq_top_iff]
  intro g _
  obtain ⟨k, rfl⟩ := F.surj g
  exact (htop ▸ Subgroup.mem_top k : k ∈ (stabBar R A A₀ B).comap F.Ψ)

theorem weylAction_mem {γ₁ : Fin F.D.rank → ℤ} (hγ₁ : γ₁ ∈ memberRoots F)
    (hγ₁U : negUnipotent F.D ≤ Subgroup.normalizer (F.D.rootGroup γ₁ : Set F.K))
    {t : Fin F.D.rank} (ht : -Pi.single t 1 ∉ lowSet F B) {β : Fin F.D.rank → ℤ}
    (hβ : β ∈ lowSet F B) :
    weylAction F.D.isFiniteType ((coxeterMatrix F.D.isFiniteType).toCoxeterSystem.simple t) β ∈
      lowSet F B := by
  obtain ⟨Y, hY, hYβ⟩ := hβ.2
  obtain ⟨v, hv⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥(levi R A A₀)) (F.Ψ (F.n t))
  have hvB : QuotientGroup.mk' (Subgroup.center ↥(levi R A A₀)) v ∈ stabBar R A A₀ B := by
    rw [hv]
    exact mem_stabBar_n hS hB hγ₁ hγ₁U ht
  refine ⟨weylAction_mem_memberRoots F hβ.1 _, conjSub Y (v : G),
    conjSub_mem_deltaSet hS hB hY v hvB, ?_⟩
  rw [LeviQuot.quotMap_conjSub Y v.2]
  have e : QuotientGroup.mk' (Subgroup.center ↥(levi R A A₀)) ⟨(v : G), v.2⟩ = F.Ψ (F.n t) := hv
  rw [e, hYβ, map_conjSub_eq, actsAs_n F.hct t β (memberRoots_subset F hβ.1)]

theorem commuting_rootGroup {β β' : Fin F.D.rank → ℤ} (hβ : β ∈ lowSet F B)
    (hβ' : β' ∈ lowSet F B) : Commuting (F.D.rootGroup β) (F.D.rootGroup β') := by
  obtain ⟨Y, hY, hYβ⟩ := hβ.2
  obtain ⟨Y', hY', hY'β⟩ := hβ'.2
  have hc := LeviQuot.commuting_quotMap (V := levi R A A₀)
    (commuting_of_mem_deltaSet hS.hyp hS.mem hS.opp hB.mem hY hY')
  rw [hYβ, hY'β] at hc
  exact commuting_of_commuting_map F (memberRoots_subset F hβ.1) (ht_lt_zero hS hB hβ)
    (memberRoots_subset F hβ'.1) (ht_lt_zero hS hB hβ') hc

theorem exists_mem_openCone {β β' : Fin F.D.rank → ℤ} (hβ : β ∈ lowSet F B)
    (hβ' : β' ∈ lowSet F B) (w : (coxeterMatrix F.D.isFiniteType).Group)
    (hw : weylAction F.D.isFiniteType w (Pi.single F.i₀ 1) = β)
    (hind : LinIndepPair β' (-β))
    (hne : weylAction F.D.isFiniteType
        ((coxeterMatrix F.D.isFiniteType).toCoxeterSystem.simple F.i₀)
        (weylAction F.D.isFiniteType w⁻¹ β') ≠ weylAction F.D.isFiniteType w⁻¹ β') :
    ∃ ε ∈ F.D.roots, ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ ε = a • β' + b • (-β) := by
  by_contra! hcone
  exact false_of_commuting F.hct F.hext F.hdiv (memberRoots_subset F hβ.1)
    (memberRoots_subset F hβ'.1) (commuting_rootGroup hS hB hβ hβ') hind
    (fun ε hε ⟨a, b, ha, hb, he⟩ => hcone ε hε a b ha hb he) hw hne

end LowMember

end CFSG.Timmesfeld.ARS.ExclNS

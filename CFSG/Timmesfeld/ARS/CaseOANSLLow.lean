module

public import CFSG.Timmesfeld.ARS.CaseOANSLStab
public import CFSG.Timmesfeld.ARS.ExclNSLowest
public import CFSG.Timmesfeld.ARS.ExclNSExceptional

public section

open scoped commutatorElement
open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.TitsSimplicity

namespace CFSG.Timmesfeld.ARS

variable {G : Type} [Group G] {R : Set (Subgroup G)}

namespace CaseOANSL

open ExclNS (memberRoots memberRoots_subset weylAction_mem_memberRoots neg_mem_memberRoots
  map_rootGroup_mem opposite_map_rootGroup isPGroup_map_negUnipotent
  iSup_le_normalizer_negUnipotent commuting_of_commuting_map)

section Quot

variable (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
  (hA₀ : A₀ ∈ omegaSet R A) {Δ₁ : Set (Subgroup G)} (hΔ₁ : Δ₁ ∈ leviComps R A A₀)
include h hA hAne hA₀ hΔ₁

theorem isRootClass_quot₁ : IsRootClass (quotClass (gen Δ₁) Δ₁) := by
  obtain ⟨E₀, hE₀, rfl⟩ := hΔ₁
  exact Levi.isRootClass_quot h hA hAne hA₀ hE₀

theorem quot_injOn₁ : Set.InjOn (quotMap (gen Δ₁)) Δ₁ := by
  obtain ⟨E₀, hE₀, rfl⟩ := hΔ₁
  exact Levi.quot_hinj h hA hAne hA₀ hE₀

theorem opposite_of_quot₁ {X Y : Subgroup G} (hX : X ∈ Δ₁) (hY : Y ∈ Δ₁)
    (hXY : Opposite (quotMap (gen Δ₁) X) (quotMap (gen Δ₁) Y)) : Opposite X Y := by
  obtain ⟨E₀, hE₀, rfl⟩ := hΔ₁
  exact Levi.quot_hopp h hA hAne hA₀ hE₀ X hX Y hY hXY

end Quot

section Member

variable {G' : Type} [Group G'] {R' : Set (Subgroup G')} {F : NSLFrameData G' R'}

theorem exists_member_normalizer_of_ht_le
    (hlow : ∃ w : (coxeterMatrix F.D.isFiniteType).Group, ∀ ε ∈ roots F.D.isFiniteType ∅,
      ht (weylAction F.D.isFiniteType w (Pi.single F.i₀ 1)) ≤ ht ε) :
    ∃ γ₁ ∈ memberRoots F,
      negUnipotent F.D ≤ Subgroup.normalizer (F.D.rootGroup γ₁ : Set F.K) := by
  obtain ⟨w, hw⟩ := hlow
  refine ⟨_, ⟨w, rfl⟩, ExclNS.negUnipotent_le_normalizer_of_forall_ht_le F.hext F.hdiv
    (memberRoots_subset F ⟨w, rfl⟩) fun ε hε => hw ε ?_⟩
  have : ε ∈ roots F.D.isFiniteType F.D.divisible := hε
  rwa [F.hdiv] at this

theorem exists_member_normalizer_cartanC (hC : F.D.cartan = Symplectic.cartanC F.D.rank)
    (hn : 3 ≤ F.D.rank) (hi₀ : F.i₀.val + 1 < F.D.rank) :
    ∃ γ₁ ∈ memberRoots F,
      negUnipotent F.D ≤ Subgroup.normalizer (F.D.rootGroup γ₁ : Set F.K) := by
  obtain ⟨w, w', h1, h2, hneg, hcone⟩ := ExclNS.exists_lowest_cartanC F.D.isFiniteType hC hn hi₀
  set γ₁ := weylAction F.D.isFiniteType w (Pi.single F.i₀ 1) with hγ₁def
  have hγ₁R : γ₁ ∈ F.D.roots := memberRoots_subset F ⟨w, rfl⟩
  refine ⟨γ₁, ⟨w, rfl⟩, ExclNS.negUnipotent_le_normalizer_rootGroup fun δ hδ hδ0 hne => ?_⟩
  by_cases hδα : δ = -Pi.single (⟨0, by omega⟩ : Fin F.D.rank) 1
  · rw [hδα]
    set i : Fin F.D.rank := ⟨F.D.rank - 2, by omega⟩
    set j : Fin F.D.rank := ⟨F.D.rank - 1, by omega⟩
    have hij : F.D.cartan i j = -2 := by
      rw [hC]
      simp only [Symplectic.cartanC, Matrix.of_apply, i, j, Fin.mk.injEq]
      split_ifs <;> omega
    have hα : (Pi.single i 1 : Fin F.D.rank → ℤ) ∈ F.D.roots :=
      (RootSystem.ofCartan F.D.isFiniteType F.D.divisible).single_mem i
    have hsum : (Pi.single i 1 + Pi.single j 1 : Fin F.D.rank → ℤ) ∈ F.D.roots := by
      have e : (Pi.single i 1 + Pi.single j 1 : Fin F.D.rank → ℤ) =
          weylAction F.D.isFiniteType w'⁻¹ (-Pi.single (⟨0, by omega⟩ : Fin F.D.rank) 1) := by
        rw [← h2, weylAction_inv_apply_apply]
      rw [e]
      exact weylAction_mem_roots _ _ ((RootSystem.ofCartan F.D.isFiniteType
        F.D.divisible).neg_mem _ ((RootSystem.ofCartan F.D.isFiniteType
          F.D.divisible).single_mem _))
    have hc := (F.comm hC i j hij).conjSub (nrep F.hct w')
    have e1 : conjSub (F.D.rootGroup (Pi.single i 1)) (nrep F.hct w') =
        F.D.rootGroup (weylAction F.D.isFiniteType w' (Pi.single i 1)) :=
      actsAs_nrep F.hct w' _ hα
    have e2 : conjSub (F.D.rootGroup (Pi.single i 1 + Pi.single j 1)) (nrep F.hct w') =
        F.D.rootGroup (weylAction F.D.isFiniteType w' (Pi.single i 1 + Pi.single j 1)) :=
      actsAs_nrep F.hct w' _ hsum
    rw [e1, e2, h1, h2] at hc
    exact hc
  · refine ExclNS.commuting_of_forall_notMem_openCone F.hext hγ₁R hδ
      (ExclNS.linIndepPair_of_ht_neg F.hdiv hγ₁R hneg hδ hδ0 (Ne.symm hne)) ?_
    rintro ε hε ⟨a, b, ha, hb, he⟩
    have hε' : ε ∈ roots F.D.isFiniteType ∅ := by
      have : ε ∈ roots F.D.isFiniteType F.D.divisible := hε
      rwa [F.hdiv] at this
    exact hδα (hcone δ hδ0 ε hε' a b ha hb he)

end Member

variable {A A₀ : Subgroup G} {Δ₁ Δ₂ : Set (Subgroup G)}

structure LowMember₁ (R : Set (Subgroup G)) (A A₀ : Subgroup G) (Δ₁ : Set (Subgroup G))
    (F : NSLFrameData (CompBar Δ₁) (quotClass (gen Δ₁) Δ₁)) (B : Subgroup G) : Prop where
  mem : B ∈ lambdaStar R A A₀
  le : (negUnipotent F.D).map F.Ψ ≤ stabBar₁ Δ₁ B

@[expose] def lowSet₁ (R : Set (Subgroup G)) (A A₀ : Subgroup G) (Δ₁ : Set (Subgroup G))
    (F : NSLFrameData (CompBar Δ₁) (quotClass (gen Δ₁) Δ₁)) (B : Subgroup G) :
    Set (Fin F.D.rank → ℤ) :=
  {β | β ∈ memberRoots F ∧ ∃ X ∈ Δ₁, X ∈ deltaSet R A A₀ B ∧
    quotMap (gen Δ₁) X = (F.D.rootGroup β).map F.Ψ}

theorem quotMap_sup₁ {X Y : Subgroup G} (hX : X ≤ gen Δ₁) (hY : Y ≤ gen Δ₁) :
    quotMap (gen Δ₁) (X ⊔ Y) = quotMap (gen Δ₁) X ⊔ quotMap (gen Δ₁) Y := by
  rw [quotMap, quotMap, quotMap, Subgroup.subgroupOf_sup hX hY, Subgroup.map_sup]

section Low

variable (h : Hyp G R) (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
  (hmax : IsSigmaMaximal R (centralGroup R A)) (hA₀ : A₀ ∈ omegaSet R A)
  (h2 : Nat.card (leviComps R A A₀) = 2)
  (hΔ₁ : Δ₁ ∈ leviComps R A A₀) (hΔ₂ : Δ₂ ∈ leviComps R A A₀) (hne : Δ₁ ≠ Δ₂)
  (F : NSLFrameData (CompBar Δ₁) (quotClass (gen Δ₁) Δ₁))
include h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne

theorem exists_lowMember₁ : ∃ B, LowMember₁ R A A₀ Δ₁ F B := by
  obtain ⟨B, hB, hle⟩ := exists_le_stabBar₁_of_isPGroup h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne
    (isPGroup_map_negUnipotent F)
  exact ⟨B, hB, hle⟩

variable {F} {B : Subgroup G} (hB : LowMember₁ R A A₀ Δ₁ F B)
include hB

theorem LowMember₁.commuting_of_le {X : Subgroup G} (hX : X ∈ Δ₁)
    (hle : quotMap (gen Δ₁) X ≤ (negUnipotent F.D).map F.Ψ) : Commuting X B :=
  (commuting_iff_quotMap_le_stabBar₁ h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hB.mem hX).2
    (hle.trans hB.le)

theorem LowMember₁.conjSub_mem {X : Subgroup G} (hX₁ : X ∈ Δ₁)
    (hX : X ∈ deltaSet R A A₀ B) (v : ↥(gen Δ₁))
    (hv : QuotientGroup.mk' (Subgroup.center ↥(gen Δ₁)) v ∈ stabBar₁ Δ₁ B) :
    conjSub X (v : G) ∈ Δ₁ ∧ conjSub X (v : G) ∈ deltaSet R A A₀ B := by
  have hvV := gen_le_levi h hA hAne hA₀ hΔ₁ v.2
  have hvB := conjSub_eq_self_iff.2
    ((mk_mem_stabBar₁_iff h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hB.mem v).1 hv)
  refine ⟨Sec9.conjSub_mem h hA hAne hA₀ hΔ₁ hX₁ hvV, ?_⟩
  rw [← hvB, ← conjSet_deltaSet h.root hvV]
  exact conjSub_mem_conjSet hX _

theorem LowMember₁.exists_eq_conjSub {γ₁ : Fin F.D.rank → ℤ} (hγ₁ : γ₁ ∈ memberRoots F)
    (hγ₁U : negUnipotent F.D ≤ Subgroup.normalizer (F.D.rootGroup γ₁ : Set F.K))
    {X : Subgroup G} (hX₁ : X ∈ Δ₁) (hX : X ∈ deltaSet R A A₀ B) :
    ∃ β ∈ lowSet₁ R A A₀ Δ₁ F B, ∃ u ∈ negUnipotent F.D,
      quotMap (gen Δ₁) X = conjSub ((F.D.rootGroup β).map F.Ψ) (F.Ψ u) := by
  have hq := isRootClass_quot₁ h hA hAne hA₀ hΔ₁
  have hγ₁R := memberRoots_subset F hγ₁
  obtain ⟨g, hg⟩ := hq.exists_conjSub_eq (map_rootGroup_mem F hq hγ₁)
    (⟨X, hX₁, rfl⟩ : quotMap (gen Δ₁) X ∈ quotClass (gen Δ₁) Δ₁)
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
  obtain ⟨v, hv⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥(gen Δ₁)) (F.Ψ u⁻¹)
  have hvB : QuotientGroup.mk' (Subgroup.center ↥(gen Δ₁)) v ∈ stabBar₁ Δ₁ B := by
    rw [hv]
    exact hB.le (Subgroup.mem_map_of_mem F.Ψ (inv_mem hu))
  obtain ⟨h1, h2'⟩ := hB.conjSub_mem h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hX₁ hX v hvB
  refine ⟨conjSub X (v : G), h1, h2', ?_⟩
  rw [LeviQuot.quotMap_conjSub X v.2]
  have e : QuotientGroup.mk' (Subgroup.center ↥(gen Δ₁)) ⟨(v : G), v.2⟩ = F.Ψ u⁻¹ := hv
  rw [e, ← hg, map_inv, ExclNS.conjSub_conjSub_inv]

theorem LowMember₁.ht_lt_zero {β : Fin F.D.rank → ℤ} (hβ : β ∈ lowSet₁ R A A₀ Δ₁ F B) :
    ht β < 0 := by
  have := h.finite
  have hq := isRootClass_quot₁ h hA hAne hA₀ hΔ₁
  have hβR := memberRoots_subset F hβ.1
  rcases ExclNS.ht_pos_or_neg hβR with ⟨-, hpos⟩ | ⟨-, hneg⟩
  · exfalso
    obtain ⟨Y, hY₁, hY, hYβ⟩ := hβ.2
    have hβ' := neg_mem_memberRoots F hβ.1
    obtain ⟨Y', hY'₁, hY'β⟩ := map_rootGroup_mem F hq hβ'
    have hopp : Opposite Y' Y := by
      refine opposite_of_quot₁ h hA hAne hA₀ hΔ₁ hY'₁ hY₁ ?_
      rw [hY'β, hYβ]
      exact (opposite_map_rootGroup F hβ.1).symm
    have hc : Commuting Y' B := hB.commuting_of_le h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hY'₁ (by
      rw [hY'β]
      exact Subgroup.map_mono (rootGroup_le_negUnipotent (memberRoots_subset F hβ')
        (by rw [ht_neg]; omega)))
    exact not_commuting_of_opposite_of_mem_lambdaSet h.root
      (Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₁ hY'₁).1.1 hopp
      (mem_lambdaSet_comm hB.mem.1.1.1 hY.2) hc
  · exact hneg

theorem LowMember₁.nonpos {β : Fin F.D.rank → ℤ} (hβ : β ∈ lowSet₁ R A A₀ Δ₁ F B) : β ≤ 0 := by
  rcases ExclNS.ht_pos_or_neg (memberRoots_subset F hβ.1) with ⟨-, h'⟩ | ⟨h', -⟩
  · exact absurd (hB.ht_lt_zero h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hβ) (not_lt.2 h'.le)
  · exact h'

theorem LowMember₁.quotMap_le_lower {γ₁ : Fin F.D.rank → ℤ} (hγ₁ : γ₁ ∈ memberRoots F)
    (hγ₁U : negUnipotent F.D ≤ Subgroup.normalizer (F.D.rootGroup γ₁ : Set F.K))
    {X : Subgroup G} (hX₁ : X ∈ Δ₁) (hX : X ∈ deltaSet R A A₀ B) :
    quotMap (gen Δ₁) X ≤
      (⨆ δ ∈ ExclNS.lowerRoots F.D (lowSet₁ R A A₀ Δ₁ F B), F.D.rootGroup δ).map F.Ψ := by
  obtain ⟨β, hβ, u, hu, he⟩ :=
    hB.exists_eq_conjSub h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hγ₁ hγ₁U hX₁ hX
  rw [he, map_conjSub_eq]
  refine Subgroup.map_mono ?_
  have hN := ExclNS.negUnipotent_le_normalizer_lower F.hext F.hdiv
    (fun β hβ => hB.nonpos h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hβ) hu
  rw [← (RankOne.map_conj_eq_self_iff).2 hN]
  exact Subgroup.map_mono (le_iSup₂_of_le (f := fun δ (_ : δ ∈ ExclNS.lowerRoots F.D
    (lowSet₁ R A A₀ Δ₁ F B)) => F.D.rootGroup δ) β ⟨memberRoots_subset F hβ.1, β, hβ, le_rfl⟩
    le_rfl)

theorem LowMember₁.mem_stabBar_n {γ₁ : Fin F.D.rank → ℤ} (hγ₁ : γ₁ ∈ memberRoots F)
    (hγ₁U : negUnipotent F.D ≤ Subgroup.normalizer (F.D.rootGroup γ₁ : Set F.K))
    {s : Fin F.D.rank} (hs : -Pi.single s 1 ∉ lowSet₁ R A A₀ Δ₁ F B) :
    F.Ψ (F.n s) ∈ stabBar₁ Δ₁ B := by
  have hR := h.root
  obtain ⟨v, hv⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥(gen Δ₁)) (F.Ψ (F.n s))
  have hvV := gen_le_levi h hA hAne hA₀ hΔ₁ v.2
  have hB' : conjSub B (v : G) ∈ lambdaStar R A A₀ :=
    conjSub_mem_lambdaStar_of_mem_levi hR hB.mem hvV
  have hL : (⨆ δ ∈ ExclNS.lowerRoots F.D (lowSet₁ R A A₀ Δ₁ F B), F.D.rootGroup δ).map F.Ψ ≤
      stabBar₁ Δ₁ (conjSub B (v : G)) := by
    rw [stabBar₁_conjSub h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hB.mem v, hv, Subgroup.map_iSup]
    refine iSup_le fun δ => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hδ => ?_
    obtain ⟨β, hβS, hδβ⟩ := hδ.2
    have hδne : δ ≠ -Pi.single s 1 := fun e => hs (by
      rw [ExclNS.eq_neg_single_of_le (memberRoots_subset F hβS.1)
        (hB.nonpos h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hβS) (e ▸ hδβ)] at hβS
      exact hβS)
    have hδ0 : ht δ < 0 := ht_neg_of_nonpos hδ.1
      (hδβ.trans (hB.nonpos h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hβS))
    obtain ⟨hsδ, -⟩ := ExclNS.ht_neg_reflection F.hdiv hδ.1 hδ0 hδne
    have hsδR := weylAction_mem_roots F.D.isFiniteType
      ((coxeterMatrix F.D.isFiniteType).toCoxeterSystem.simple s) hδ.1
    have e := actsAs_n F.hct s _ hsδR
    rw [← weylAction_mul_apply, CoxeterSystem.simple_mul_simple_self, map_one,
      Module.End.one_apply] at e
    rw [← e, ← map_conjSub_eq]
    exact Subgroup.map_mono (Subgroup.map_mono (rootGroup_le_negUnipotent hsδR hsδ)) |>.trans
      (Subgroup.map_mono hB.le)
  have hBv : B = conjSub B (v : G) := by
    refine eq_of_forall_quotMap_le_stabBar₁ h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hB' hB.mem
      (fun X hX₁ hX => ?_) fun X hX₂ hX => ?_
    · exact (hB.quotMap_le_lower h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hγ₁ hγ₁U hX₁ hX).trans hL
    · have hXv : conjSub X (v : G) = X := conjSub_eq_of_mem_comp₂ h hA hAne hA₀ hΔ₁ hΔ₂ hne hX₂ v.2
      have := hX.2.1.2.2.conjSub (v : G)
      rw [hXv] at this
      exact this.symm
  rw [← hv]
  exact (mk_mem_stabBar₁_iff h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hB.mem v).2
    (conjSub_eq_self_iff.1 hBv.symm)

theorem LowMember₁.exists_neg_single_mem {γ₁ : Fin F.D.rank → ℤ} (hγ₁ : γ₁ ∈ memberRoots F)
    (hγ₁U : negUnipotent F.D ≤ Subgroup.normalizer (F.D.rootGroup γ₁ : Set F.K)) :
    ∃ s, -Pi.single s 1 ∈ lowSet₁ R A A₀ Δ₁ F B := by
  by_contra! hall
  apply stabBar₁_ne_top h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hB.mem
  have htop := ExclNS.eq_top_of_negUnipotent_le F.hct (P := (stabBar₁ Δ₁ B).comap F.Ψ)
    (Subgroup.map_le_iff_le_comap.1 hB.le) fun s =>
      hB.mem_stabBar_n h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hγ₁ hγ₁U (hall s)
  rw [eq_top_iff]
  intro g _
  obtain ⟨k, rfl⟩ := F.surj g
  exact (htop ▸ Subgroup.mem_top k : k ∈ (stabBar₁ Δ₁ B).comap F.Ψ)

theorem LowMember₁.weylAction_mem {γ₁ : Fin F.D.rank → ℤ} (hγ₁ : γ₁ ∈ memberRoots F)
    (hγ₁U : negUnipotent F.D ≤ Subgroup.normalizer (F.D.rootGroup γ₁ : Set F.K))
    {t : Fin F.D.rank} (ht : -Pi.single t 1 ∉ lowSet₁ R A A₀ Δ₁ F B) {β : Fin F.D.rank → ℤ}
    (hβ : β ∈ lowSet₁ R A A₀ Δ₁ F B) :
    weylAction F.D.isFiniteType ((coxeterMatrix F.D.isFiniteType).toCoxeterSystem.simple t) β ∈
      lowSet₁ R A A₀ Δ₁ F B := by
  obtain ⟨Y, hY₁, hY, hYβ⟩ := hβ.2
  obtain ⟨v, hv⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥(gen Δ₁)) (F.Ψ (F.n t))
  have hvB : QuotientGroup.mk' (Subgroup.center ↥(gen Δ₁)) v ∈ stabBar₁ Δ₁ B := by
    rw [hv]
    exact hB.mem_stabBar_n h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hγ₁ hγ₁U ht
  obtain ⟨h1, h2'⟩ := hB.conjSub_mem h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hY₁ hY v hvB
  refine ⟨weylAction_mem_memberRoots F hβ.1 _, conjSub Y (v : G), h1, h2', ?_⟩
  rw [LeviQuot.quotMap_conjSub Y v.2]
  have e : QuotientGroup.mk' (Subgroup.center ↥(gen Δ₁)) ⟨(v : G), v.2⟩ = F.Ψ (F.n t) := hv
  rw [e, hYβ, map_conjSub_eq, actsAs_n F.hct t β (memberRoots_subset F hβ.1)]

theorem LowMember₁.commuting_rootGroup {β β' : Fin F.D.rank → ℤ}
    (hβ : β ∈ lowSet₁ R A A₀ Δ₁ F B) (hβ' : β' ∈ lowSet₁ R A A₀ Δ₁ F B) :
    Commuting (F.D.rootGroup β) (F.D.rootGroup β') := by
  obtain ⟨Y, -, hY, hYβ⟩ := hβ.2
  obtain ⟨Y', -, hY', hY'β⟩ := hβ'.2
  have hc := LeviQuot.commuting_quotMap (V := gen Δ₁)
    (commuting_of_mem_deltaSet h hA hA₀ hB.mem hY hY')
  rw [hYβ, hY'β] at hc
  exact commuting_of_commuting_map F (memberRoots_subset F hβ.1)
    (hB.ht_lt_zero h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hβ) (memberRoots_subset F hβ'.1)
    (hB.ht_lt_zero h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hβ') hc

theorem LowMember₁.exists_mem_openCone {β β' : Fin F.D.rank → ℤ}
    (hβ : β ∈ lowSet₁ R A A₀ Δ₁ F B) (hβ' : β' ∈ lowSet₁ R A A₀ Δ₁ F B)
    (w : (coxeterMatrix F.D.isFiniteType).Group)
    (hw : weylAction F.D.isFiniteType w (Pi.single F.i₀ 1) = β)
    (hind : LinIndepPair β' (-β))
    (hrefl : weylAction F.D.isFiniteType
        ((coxeterMatrix F.D.isFiniteType).toCoxeterSystem.simple F.i₀)
        (weylAction F.D.isFiniteType w⁻¹ β') ≠ weylAction F.D.isFiniteType w⁻¹ β') :
    ∃ ε ∈ F.D.roots, ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ ε = a • β' + b • (-β) := by
  by_contra! hcone
  exact ExclNS.false_of_commuting F.hct F.hext F.hdiv (memberRoots_subset F hβ.1)
    (memberRoots_subset F hβ'.1)
    (hB.commuting_rootGroup h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hβ hβ') hind
    (fun ε hε ⟨a, b, ha, hb, he⟩ => hcone ε hε a b ha hb he) hw hrefl

theorem LowMember₁.form_nonneg (Q : ExclNS.InvForm F.D.cartan)
    (hM : ∀ i, Q.Q (Pi.single i 1) (Pi.single i 1) ≤
      2 * Q.Q (Pi.single F.i₀ 1) (Pi.single F.i₀ 1))
    {β β' : Fin F.D.rank → ℤ} (hβ : β ∈ lowSet₁ R A A₀ Δ₁ F B)
    (hβ' : β' ∈ lowSet₁ R A A₀ Δ₁ F B) : 0 ≤ Q.Q β' β := by
  by_contra hneg'
  have hneg : Q.Q β' β < 0 := not_le.1 hneg'
  have hnorm : ∀ {γ}, γ ∈ memberRoots F →
      Q.Q γ γ = Q.Q (Pi.single F.i₀ 1) (Pi.single F.i₀ 1) := by
    rintro _ ⟨w, rfl⟩
    exact Q.weylAction F.D.isFiniteType w _ _
  have hNβ := hnorm hβ.1
  have hNβ' := hnorm hβ'.1
  have hββ' : β ≠ β' := by
    rintro rfl
    have h1 := hM F.i₀
    rw [← hNβ] at h1
    linarith
  obtain ⟨w, hw⟩ := hβ.1
  have hβR := memberRoots_subset F hβ.1
  have hβ'R := memberRoots_subset F hβ'.1
  have hind : LinIndepPair β' (-β) := ExclNS.linIndepPair_neg_right
    (ExclNS.linIndepPair_of_ht_neg F.hdiv hβ'R
      (hB.ht_lt_zero h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hβ') hβR
      (hB.ht_lt_zero h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hβ) (Ne.symm hββ'))
  obtain ⟨ε, hε, a, b, ha, hb, he⟩ :=
    hB.exists_mem_openCone h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hβ hβ' w hw.symm hind
      (Q.reflection_ne F.D.isFiniteType (by rw [← hw]; exact hneg.ne))
  have hε' : ε ∈ roots F.D.isFiniteType ∅ := by
    have : ε ∈ roots F.D.isFiniteType F.D.divisible := hε
    rwa [F.hdiv] at this
  have hN0 : 0 ≤ Q.Q β β := by
    have h1 := hM F.i₀
    rw [← hNβ] at h1
    linarith
  exact Q.forall_notMem_openCone F.D.isFiniteType (hNβ'.trans hNβ.symm) hN0 hneg
    (fun i => (hM i).trans_eq (by rw [hNβ])) ε hε' ⟨a, b, ha, hb, he⟩

theorem LowMember₁.reflection_mem {γ₁ : Fin F.D.rank → ℤ} (hγ₁ : γ₁ ∈ memberRoots F)
    (hγ₁U : negUnipotent F.D ≤ Subgroup.normalizer (F.D.rootGroup γ₁ : Set F.K))
    (t : Fin F.D.rank) (ht : -Pi.single t 1 ∉ lowSet₁ R A A₀ Δ₁ F B) {β : Fin F.D.rank → ℤ}
    (hβ : β ∈ lowSet₁ R A A₀ Δ₁ F B) : reflection F.D.cartan t β ∈ lowSet₁ R A A₀ Δ₁ F B := by
  have := hB.weylAction_mem h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hγ₁ hγ₁U ht hβ
  rwa [weylAction_simple] at this

theorem LowMember₁.map_iSup_le_stabBar {i0 : Fin F.D.rank}
    (h0 : -Pi.single i0 1 ∈ lowSet₁ R A A₀ Δ₁ F B)
    (hn : ∀ s, s ≠ i0 → F.Ψ (F.n s) ∈ stabBar₁ Δ₁ B) :
    (⨆ i, F.H i).map F.Ψ ≤ stabBar₁ Δ₁ B := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hq := isRootClass_quot₁ h hA hAne hA₀ hΔ₁
  have hl₁ := fun {X : Subgroup G} (hX : X ∈ Δ₁) =>
    Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₁ hX
  rw [Subgroup.map_iSup]
  refine iSup_le fun i => ?_
  have hα : (Pi.single i 1 : Fin F.D.rank → ℤ) ∈ F.D.roots :=
    (RootSystem.ofCartan F.D.isFiniteType F.D.divisible).single_mem i
  have hα' : (-Pi.single i 1 : Fin F.D.rank → ℤ) ∈ F.D.roots :=
    (RootSystem.ofCartan F.D.isFiniteType F.D.divisible).neg_mem _ hα
  have hHle : (F.H i).map F.Ψ ≤ (F.D.rootGroup (Pi.single i 1)).map F.Ψ ⊔
      (F.D.rootGroup (-Pi.single i 1)).map F.Ψ := by
    rw [← Subgroup.map_sup]
    exact Subgroup.map_mono (F.hct.H_le i)
  have hneg : (F.D.rootGroup (-Pi.single i 1)).map F.Ψ ≤ stabBar₁ Δ₁ B :=
    (Subgroup.map_mono (rootGroup_le_negUnipotent hα' (by rw [ht_neg, ht_single]; omega))).trans
      hB.le
  by_cases hi : i = i0
  · subst hi
    obtain ⟨Y, hY₁, hY, hYq⟩ := h0.2
    have hαO : Pi.single i 1 ∈ memberRoots F := by
      have := neg_mem_memberRoots F h0.1
      rwa [neg_neg] at this
    obtain ⟨P, hP₁, hPq⟩ := map_rootGroup_mem F hq hαO
    have hopp : Opposite Y P := by
      refine opposite_of_quot₁ h hA hAne hA₀ hΔ₁ hY₁ hP₁ ?_
      rw [hYq, hPq]
      exact (opposite_map_rootGroup F hαO).symm
    have hYB : Commuting B Y := hY.2.1.2.2
    by_cases hc : Commuting P B
    · refine hHle.trans (sup_le ?_ hneg)
      rw [← hPq]
      exact (commuting_iff_quotMap_le_stabBar₁ h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hB.mem hP₁).1 hc
    · have hs : Special R P B := (special_of_not_commuting_of_mem_leviSet h hA hB.mem (hl₁ hP₁)
        fun h' => hc h'.symm).symm
      have hl : B ∈ lambdaSet R Y := mem_lambdaSet_comm hB.mem.1.1.1 hY.2
      have hψ : B ∈ psiSet R P := ⟨hB.mem.1.1.1, hs⟩
      rintro _ ⟨x, hx, rfl⟩
      have hmem : F.Ψ x ∈ quotMap (gen Δ₁) (Y ⊔ P) := by
        have := hHle ⟨x, hx, rfl⟩
        rw [← hPq, ← hYq, sup_comm, ← quotMap_sup₁ (le_gen hY₁)
          (le_gen hP₁)] at this
        exact this
      obtain ⟨t, ht, hte⟩ := LeviQuot.exists_of_mem_quotMap hmem
      have htY : conjSub Y (t : G) = Y := by
        refine quot_injOn₁ h hA hAne hA₀ hΔ₁
          (Sec9.conjSub_mem h hA hAne hA₀ hΔ₁ hY₁ (gen_le_levi h hA hAne hA₀ hΔ₁ t.2)) hY₁ ?_
        rw [LeviQuot.quotMap_conjSub Y t.2]
        have e : QuotientGroup.mk' (Subgroup.center ↥(gen Δ₁)) ⟨(t : G), t.2⟩ = F.Ψ x := hte
        rw [e, hYq, map_conjSub_eq,
          (RankOne.map_conj_eq_self_iff).2
            (iSup_le_normalizer_rootGroup F.hct hα' ((le_iSup F.H i) hx))]
      have hinv := Sec3.conjSub_sup_commutator_eq hR hiso hY.1.1.1 (hl₁ hP₁).1.1 hopp hl hψ ht
      have hBt : conjSub B (t : G) ≤ B := by
        intro y hy
        refine Sec3.mem_of_forall_commute_of_mem_sup hR hiso hY.1.1.1 (hl₁ hP₁).1.1 hopp hl hψ
          ?_ ?_
        · rw [← hinv]
          exact Subgroup.map_mono le_sup_left hy
        · intro a ha
          have h1 := hYB.conjSub (t : G)
          rw [htY] at h1
          exact (h1 y hy a ha).symm
      have hBt' : conjSub B (t : G) = B := Subgroup.eq_of_le_of_card_ge hBt
        (Subgroup.card_map_of_injective (MulAut.conj (t : G)).injective).ge
      rw [← hte]
      exact (mk_mem_stabBar₁_iff h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hB.mem t).2
        (conjSub_eq_self_iff.1 hBt')
  · refine hHle.trans (sup_le ?_ hneg)
    have e := actsAs_n F.hct i _ hα'
    rw [map_neg, weylAction_simple_single, neg_neg] at e
    rw [← e, ← map_conjSub_eq]
    have h1 := Subgroup.map_mono (f := (MulAut.conj (F.Ψ (F.n i))).toMonoidHom) hneg
    exact h1.trans (le_of_eq (conjSub_of_mem (hn i hi)))

theorem LowMember₁.attach_of_epsCoords {γ₁ : Fin F.D.rank → ℤ} (hγ₁ : γ₁ ∈ memberRoots F)
    (hγ₁U : negUnipotent F.D ≤ Subgroup.normalizer (F.D.rootGroup γ₁ : Set F.K))
    (P : ExclNS.EpsCoords F.D.cartan) (hn : 3 ≤ F.D.rank) (hi₀ : F.i₀.val + 1 < F.D.rank) :
    -Pi.single (⟨0, by omega⟩ : Fin F.D.rank) 1 ∈ lowSet₁ R A A₀ Δ₁ F B ∧
      (∀ s : Fin F.D.rank, s.val ≠ 0 → F.Ψ (F.n s) ∈ stabBar₁ Δ₁ B) ∧
      (⨆ i, F.H i).map F.Ψ ≤ stabBar₁ Δ₁ B := by
  have hnorm : ∀ β ∈ lowSet₁ R A A₀ Δ₁ F B, P.invForm.Q β β = 2 := by
    rintro β ⟨⟨w, rfl⟩, -⟩
    exact (P.invForm.weylAction F.D.isFiniteType w _ _).trans (P.invForm_single_of_lt hi₀)
  have hM : ∀ i, P.invForm.Q (Pi.single i 1) (Pi.single i 1) ≤
      2 * P.invForm.Q (Pi.single F.i₀ 1) (Pi.single F.i₀ 1) := by
    intro i
    rw [P.invForm_single_of_lt hi₀]
    linarith [P.invForm_single_le i]
  have hzero : ∀ s, -Pi.single s 1 ∈ lowSet₁ R A A₀ Δ₁ F B → s.val = 0 := fun s hs =>
    ExclNS.val_eq_zero_of_neg_single_mem P hnorm
      (hB.reflection_mem h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hγ₁ hγ₁U)
      (fun β hβ β' hβ' => hB.form_nonneg h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne P.invForm hM hβ hβ')
      hs
  obtain ⟨s, hs⟩ := hB.exists_neg_single_mem h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hγ₁ hγ₁U
  have hs0 := hzero s hs
  have hs' : s = ⟨0, by omega⟩ := Fin.ext hs0
  have hns : ∀ s : Fin F.D.rank, s.val ≠ 0 → F.Ψ (F.n s) ∈ stabBar₁ Δ₁ B := fun s' hs'' =>
    hB.mem_stabBar_n h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hγ₁ hγ₁U fun h' => hs'' (hzero s' h')
  refine ⟨hs' ▸ hs, hns, ?_⟩
  exact hB.map_iSup_le_stabBar h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hs fun s' hs'' =>
    hns s' fun h' => hs'' (Fin.ext (h'.trans hs0.symm))

end Low

section Attach

variable (h : Hyp G R) (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
  (hmax : IsSigmaMaximal R (centralGroup R A)) (hA₀ : A₀ ∈ omegaSet R A)
  (h2 : Nat.card (leviComps R A A₀) = 2)
  (hΔ₁ : Δ₁ ∈ leviComps R A A₀) (hΔ₂ : Δ₂ ∈ leviComps R A A₀) (hne : Δ₁ ≠ Δ₂)
include h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne

theorem exists_attach (F : NSLFrameData (CompBar Δ₁) (quotClass (gen Δ₁) Δ₁)) :
    (F.D.cartan = Spin.cartanB F.D.rank ∨ F.D.cartan = Symplectic.cartanC F.D.rank) ∧
      ∃ (hn : 3 ≤ F.D.rank), F.i₀.val + 1 < F.D.rank ∧ ∃ B, LowMember₁ R A A₀ Δ₁ F B ∧
        -Pi.single (⟨0, by omega⟩ : Fin F.D.rank) 1 ∈ lowSet₁ R A A₀ Δ₁ F B ∧
        (∀ s : Fin F.D.rank, s.val ≠ 0 → F.Ψ (F.n s) ∈ stabBar₁ Δ₁ B) ∧
        (⨆ i, F.H i).map F.Ψ ≤ stabBar₁ Δ₁ B := by
  obtain ⟨B, hB⟩ := exists_lowMember₁ h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne F
  rcases ExclNS.NSLType.elim F.type with ⟨hn, hi₀, hC⟩ | ⟨hn, hi₀, hC⟩ | ⟨hr, hi₀, hC⟩ |
    ⟨hr, hi₀, hC⟩
  · obtain ⟨γ₁, hγ₁, hγ₁U⟩ := exists_member_normalizer_cartanC hC hn hi₀
    exact ⟨Or.inr hC, hn, hi₀, B, hB, hB.attach_of_epsCoords h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne
      hγ₁ hγ₁U (hC ▸ ExclNS.epsC F.D.rank) hn hi₀⟩
  · obtain ⟨γ₁, hγ₁, hγ₁U⟩ := exists_member_normalizer_of_ht_le
      (ExclNS.exists_ht_le_cartanB F.D.isFiniteType hC (by omega) hi₀)
    exact ⟨Or.inl hC, hn, hi₀, B, hB, hB.attach_of_epsCoords h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne
      hγ₁ hγ₁U (hC ▸ ExclNS.epsB F.D.rank) hn hi₀⟩
  · exfalso
    obtain ⟨γ₁, hγ₁, hγ₁U⟩ :=
      exists_member_normalizer_of_ht_le (ExclNS.exists_ht_le_g2 F.D.isFiniteType hr hC hi₀)
    set q : Fin F.D.rank → ℤ := fun i => if i.val = 0 then 3 else 1 with hqdef
    have hq : ∀ k, 0 < q k := fun k => by simp only [hqdef]; split_ifs <;> norm_num
    have key : ∀ a < 2, ∀ b < 2,
        (if a = 0 then (3 : ℤ) else 1) * ExclNS.g2e a b =
          (if b = 0 then 3 else 1) * ExclNS.g2e b a := by
      decide
    have hsymm : ∀ i j, q i * F.D.cartan i j = q j * F.D.cartan j i := fun i j => by
      rw [hC, hC]
      exact key _ (hr ▸ i.isLt) _ (hr ▸ j.isLt)
    set Q := ExclNS.InvForm.ofSymmetrizer F.D.isFiniteType q hq hsymm
    have hM : ∀ i, Q.Q (Pi.single i 1) (Pi.single i 1) ≤
        2 * Q.Q (Pi.single F.i₀ 1) (Pi.single F.i₀ 1) := by
      intro i
      change ExclNS.symForm q _ _ _ ≤ 2 * ExclNS.symForm q _ _ _
      rw [ExclNS.symForm_single_single F.D.isFiniteType hsymm,
        ExclNS.symForm_single_single F.D.isFiniteType hsymm]
      simp only [hqdef, hi₀, ite_true]
      split_ifs <;> norm_num
    exact ExclNS.false_of_g2 hr hC hi₀ (q := q) (fun _ => rfl)
      (fun β hβ => by obtain ⟨⟨w, rfl⟩, -⟩ := hβ; exact Q.weylAction F.D.isFiniteType w _ _)
      (hB.exists_neg_single_mem h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hγ₁ hγ₁U)
      (hB.reflection_mem h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hγ₁ hγ₁U)
      (fun β hβ β' hβ' => hB.form_nonneg h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne Q hM hβ hβ')
  · exfalso
    obtain ⟨γ₁, hγ₁, hγ₁U⟩ :=
      exists_member_normalizer_of_ht_le (ExclNS.exists_ht_le_f4 F.D.isFiniteType hr hC hi₀)
    set q : Fin F.D.rank → ℤ := fun i => if i.val < 2 then 2 else 1 with hqdef
    have hq : ∀ k, 0 < q k := fun k => by simp only [hqdef]; split_ifs <;> norm_num
    have key : ∀ a < 4, ∀ b < 4,
        (if a < 2 then (2 : ℤ) else 1) * ExclNS.f4e a b =
          (if b < 2 then 2 else 1) * ExclNS.f4e b a := by
      decide
    have hsymm : ∀ i j, q i * F.D.cartan i j = q j * F.D.cartan j i := fun i j => by
      rw [hC, hC]
      exact key _ (hr ▸ i.isLt) _ (hr ▸ j.isLt)
    set Q := ExclNS.InvForm.ofSymmetrizer F.D.isFiniteType q hq hsymm
    have hM : ∀ i, Q.Q (Pi.single i 1) (Pi.single i 1) ≤
        2 * Q.Q (Pi.single F.i₀ 1) (Pi.single F.i₀ 1) := by
      intro i
      change ExclNS.symForm q _ _ _ ≤ 2 * ExclNS.symForm q _ _ _
      rw [ExclNS.symForm_single_single F.D.isFiniteType hsymm,
        ExclNS.symForm_single_single F.D.isFiniteType hsymm]
      simp only [hqdef, hi₀, ite_true]
      split_ifs <;> norm_num
    exact ExclNS.false_of_f4 hr hC hi₀ (q := q) (fun _ => rfl)
      (fun β hβ => by obtain ⟨⟨w, rfl⟩, -⟩ := hβ; exact Q.weylAction F.D.isFiniteType w _ _)
      (hB.exists_neg_single_mem h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hγ₁ hγ₁U)
      (hB.reflection_mem h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hγ₁ hγ₁U)
      (fun β hβ β' hβ' => hB.form_nonneg h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne Q hM hβ hβ')

end Attach

end CaseOANSL

end CFSG.Timmesfeld.ARS

module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSpCompBlock
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSLCompParts

public section

open Matrix Multiplicative CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped commutatorElement

namespace CFSG.StandardType

namespace CoordSp

section Setup

variable {G : Type} [Group G] {F : Type} [Field F] {n p : ℕ}

@[expose] noncomputable def frameConj (ψ : StatedSp n F →* G) (A₀ : StatedSp n F) :
    StatedSp n F →* G :=
  ψ.comp (MulAut.conj A₀).toMonoidHom

theorem frameConj_apply (ψ : StatedSp n F →* G) (A₀ x : StatedSp n F) :
    frameConj ψ A₀ x = ψ (A₀ * x * A₀⁻¹) :=
  rfl

theorem frameConj_injective {ψ : StatedSp n F →* G} (hψ : Function.Injective ψ)
    (A₀ : StatedSp n F) : Function.Injective (frameConj ψ A₀) :=
  hψ.comp (MulAut.conj A₀).injective

theorem range_frameConj (ψ : StatedSp n F →* G) (A₀ : StatedSp n F) :
    (frameConj ψ A₀).range = ψ.range := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨y, rfl⟩
    refine ⟨A₀⁻¹ * y * A₀, ?_⟩
    rw [frameConj_apply]
    congr 1
    group

theorem frameHom_eq_frameConj [NeZero p] (ψ : StatedSp n F →* G) (A₀ : StatedSp n F)
    {ζ : Fˣ} (hζ : ζ ^ p = 1) (t : Fin n → ZMod p) :
    frameHom ψ A₀ hζ (ofAdd t) = frameConj ψ A₀ (torusElt ζ t) :=
  rfl

theorem centralizer_eq_map {ψ : StatedSp n F →* G} (hψ : Function.Injective ψ)
    (A₀ : StatedSp n F) (ζ : Fˣ) (β : Fin n → ZMod p) :
    ψ.range ⊓ Subgroup.centralizer {frameConj ψ A₀ (torusElt ζ β)} =
      (Subgroup.centralizer {torusElt ζ β}).map (frameConj ψ A₀) := by
  rw [← range_frameConj ψ A₀]
  ext x
  simp only [Subgroup.mem_inf, MonoidHom.mem_range, Subgroup.mem_map,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨⟨y, rfl⟩, hy⟩
    exact ⟨y, frameConj_injective hψ A₀ (by rw [map_mul, map_mul, hy]), rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, rfl⟩, by rw [← map_mul, ← map_mul, hy]⟩

theorem wtPres_of_mem_zeroBlock {β : Fin n → ZMod p} {M : StatedSp n F}
    (hM : M ∈ suppGroup (planeSet (spClass β 0))) : WtPres β (mat n F M) := by
  intro a b hab
  by_cases hin : a ∈ planeSet (spClass β 0) ∧ b ∈ planeSet (spClass β 0)
  · exact absurd ((mem_planeSet_zero_iff.mp hin.1).trans (mem_planeSet_zero_iff.mp hin.2).symm) hab
  · rw [(mem_suppGroup.mp hM) a b hin, Matrix.one_apply_ne fun h => hab (congrArg (spWt β) h)]

theorem statedSp_comm_of_eq_zero {m : ℕ} (hm : m = 0) (X Z : StatedSp m F) : X * Z = Z * X := by
  subst hm
  apply mat_injective
  ext a b
  rcases a with a | a <;> exact a.elim0

end Setup

section Clauses

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] {n p : ℕ} [Fact p.Prime]
  {ψ : StatedSp n F →* G} {A₀ : StatedSp n F} {ζ : Fˣ} {hζ : ζ ^ p = 1}

theorem clause_zero (hinj : Function.Injective (frameHom ψ A₀ hζ)) {β : Fin n → ZMod p}
    (hβ : β ≠ 0) {L₁ : Subgroup G}
    (hL₁ : L₁ = (suppGroup (planeSet (spClass β 0))).map (frameConj ψ A₀))
    (hcard : Nat.card ((frameHom ψ A₀ hζ).range ⊓ Subgroup.centralizer (L₁ : Set G) :
      Subgroup G) ≤ p ^ 2) :
    ∃ j j' : Fin n, (∀ i, i ≠ j → i ≠ j' → β i = 0) ∧
      ∀ t : Fin n → ZMod p, t j = 0 → t j' = 0 → frameHom ψ A₀ hζ (ofAdd t) ∈ L₁ := by
  have hp : p.Prime := Fact.out
  have hcomm_t : ∀ t : Fin n → ZMod p, (∀ i, β i = 0 → t i = 0) →
      frameHom ψ A₀ hζ (ofAdd t) ∈ Subgroup.centralizer (L₁ : Set G) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [hL₁] at hx
    obtain ⟨M, hM, rfl⟩ := hx
    rw [frameHom_eq_frameConj, ← map_mul, ← map_mul, torusElt_comm_zeroBlock hζ ht hM]
  have hthree : ∀ i₁ i₂ i₃ : Fin n, i₁ ≠ i₂ → i₁ ≠ i₃ → i₂ ≠ i₃ → β i₁ ≠ 0 → β i₂ ≠ 0 →
      β i₃ ≠ 0 → False := by
    intro i₁ i₂ i₃ h12 h13 h23 h1 h2 h3
    set v : ZMod p × ZMod p × ZMod p → (Fin n → ZMod p) := fun a =>
      Pi.single i₁ a.1 + Pi.single i₂ a.2.1 + Pi.single i₃ a.2.2 with hvdef
    have hv : Function.Injective v := by
      intro a b hab
      have e1 := congrFun hab i₁
      have e2 := congrFun hab i₂
      have e3 := congrFun hab i₃
      simp only [hvdef, Pi.add_apply, Pi.single_apply, h12, h13, h23, Ne.symm h12, Ne.symm h13,
        Ne.symm h23, ↓reduceIte, add_zero, zero_add] at e1 e2 e3
      exact Prod.ext e1 (Prod.ext e2 e3)
    have hle := CoordSL.pow_three_le_natCard
      (H := (frameHom ψ A₀ hζ).range ⊓ Subgroup.centralizer (L₁ : Set G))
      (fun a => frameHom ψ A₀ hζ (ofAdd (v a)))
      (hinj.comp (ofAdd.injective.comp hv)) fun a => Subgroup.mem_inf.mpr ⟨⟨_, rfl⟩,
        hcomm_t (v a) fun i hi => by
          have hi1 : i ≠ i₁ := fun h => h1 (h ▸ hi)
          have hi2 : i ≠ i₂ := fun h => h2 (h ▸ hi)
          have hi3 : i ≠ i₃ := fun h => h3 (h ▸ hi)
          simp [hvdef, hi1, hi2, hi3]⟩
    exact absurd (hle.trans hcard) (not_le.mpr (Nat.pow_lt_pow_right hp.one_lt (by norm_num)))
  obtain ⟨j, hj⟩ : ∃ j, β j ≠ 0 := by
    by_contra h
    push Not at h
    exact hβ (funext h)
  have hmem : ∀ t : Fin n → ZMod p, (∀ i, β i ≠ 0 → t i = 0) →
      frameHom ψ A₀ hζ (ofAdd t) ∈ L₁ := by
    intro t ht
    rw [hL₁, frameHom_eq_frameConj]
    exact Subgroup.mem_map_of_mem _
      (torusElt_mem_suppGroup hζ fun i hi => ht i fun h => hi (mem_spClass.mpr h))
  by_cases hj' : ∃ j', j' ≠ j ∧ β j' ≠ 0
  · obtain ⟨j', hj'j, hj'0⟩ := hj'
    refine ⟨j, j', fun i hij hij' => ?_, fun t ht ht' => hmem t fun i hi => ?_⟩
    · by_contra hi
      exact hthree j j' i (Ne.symm hj'j) (Ne.symm hij) (Ne.symm hij') hj hj'0 hi
    · by_cases hij : i = j
      · rw [hij]
        exact ht
      · by_cases hij' : i = j'
        · rw [hij']
          exact ht'
        · exact (hthree j j' i (Ne.symm hj'j) (Ne.symm hij) (Ne.symm hij') hj hj'0 hi).elim
  · push Not at hj'
    refine ⟨j, j, fun i hij _ => hj' i hij, fun t ht _ => hmem t fun i hi => ?_⟩
    by_cases hij : i = j
    · rw [hij]
      exact ht
    · exact absurd (hj' i hij) hi

theorem clause_class (hp2 : p ≠ 2) (hinj : Function.Injective (frameHom ψ A₀ hζ))
    {β : Fin n → ZMod p} {c : ZMod p} (hc : c ≠ 0) (hS : (spClass β c).Nonempty)
    {L₁ : Subgroup G}
    (hL₁ : L₁ = (classHom (F := F) (spClass β c)).range.map (frameConj ψ A₀))
    (hcard : Nat.card ((frameHom ψ A₀ hζ).range ⊓ Subgroup.centralizer (L₁ : Set G) :
      Subgroup G) ≤ p ^ 2) :
    ∃ (k : Fin n) (c' : ZMod p), c' ≠ 0 ∧ (∀ i, i ≠ k → β i = c') ∧
      ∀ t : Fin n → ZMod p, t k = 0 → ∑ i, t i = 0 → frameHom ψ A₀ hζ (ofAdd t) ∈ L₁ := by
  have hp : p.Prime := Fact.out
  have hcomm_t : ∀ t : Fin n → ZMod p, (∀ i j, β i = c → β j = c → t i = t j) →
      frameHom ψ A₀ hζ (ofAdd t) ∈ Subgroup.centralizer (L₁ : Set G) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [hL₁] at hx
    obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := hx
    rw [frameHom_eq_frameConj, ← map_mul, ← map_mul,
      torusElt_comm_classBlock hp2 hζ hc ht (wtPres_classHom β c A) (classHom_mem_suppGroup _ A)]
  obtain ⟨i₀, hi₀⟩ := hS
  have hi₀' : β i₀ = c := mem_spClass.mp hi₀
  have hout : ∀ k₁ k₂ : Fin n, k₁ ≠ k₂ → β k₁ ≠ c → β k₂ ≠ c → False := by
    intro k₁ k₂ h12 h1 h2
    have h01 : i₀ ≠ k₁ := fun h => h1 (h ▸ hi₀')
    have h02 : i₀ ≠ k₂ := fun h => h2 (h ▸ hi₀')
    set v : ZMod p × ZMod p × ZMod p → (Fin n → ZMod p) := fun a =>
      Pi.single k₁ a.1 + Pi.single k₂ a.2.1 + fun i => if β i = c then a.2.2 else 0 with hvdef
    have hv : Function.Injective v := by
      intro a b hab
      have e1 := congrFun hab k₁
      have e2 := congrFun hab k₂
      have e3 := congrFun hab i₀
      simp only [hvdef, Pi.add_apply, Pi.single_apply, h12, Ne.symm h12, h01, h02, h1, h2, hi₀',
        ↓reduceIte, add_zero, zero_add] at e1 e2 e3
      exact Prod.ext e1 (Prod.ext e2 e3)
    have hle := CoordSL.pow_three_le_natCard
      (H := (frameHom ψ A₀ hζ).range ⊓ Subgroup.centralizer (L₁ : Set G))
      (fun a => frameHom ψ A₀ hζ (ofAdd (v a)))
      (hinj.comp (ofAdd.injective.comp hv)) fun a => Subgroup.mem_inf.mpr ⟨⟨_, rfl⟩,
        hcomm_t (v a) fun i j hi hj => by
          have hi1 : i ≠ k₁ := fun h => h1 (h ▸ hi)
          have hi2 : i ≠ k₂ := fun h => h2 (h ▸ hi)
          have hj1 : j ≠ k₁ := fun h => h1 (h ▸ hj)
          have hj2 : j ≠ k₂ := fun h => h2 (h ▸ hj)
          simp [hvdef, hi1, hi2, hj1, hj2, hi, hj]⟩
    exact absurd (hle.trans hcard) (not_le.mpr (Nat.pow_lt_pow_right hp.one_lt (by norm_num)))
  have hmem : ∀ t : Fin n → ZMod p, (∀ i, β i ≠ c → t i = 0) → ∑ i, t i = 0 →
      frameHom ψ A₀ hζ (ofAdd t) ∈ L₁ := by
    intro t ht hsum
    rw [hL₁, frameHom_eq_frameConj]
    exact Subgroup.mem_map_of_mem _ (torusElt_mem_range_classHom hp2 hζ hc ht hsum)
  by_cases hk : ∃ k, β k ≠ c
  · obtain ⟨k, hk⟩ := hk
    refine ⟨k, c, hc, fun i hik => ?_, fun t htk hsum => hmem t (fun i hi => ?_) hsum⟩
    · by_contra hi
      exact hout k i (Ne.symm hik) hk hi
    · by_cases hik : i = k
      · rw [hik]
        exact htk
      · exact (hout k i (Ne.symm hik) hk hi).elim
  · push Not at hk
    exact ⟨i₀, c, hc, fun i _ => hk i, fun t _ hsum => hmem t (fun i hi => absurd (hk i) hi) hsum⟩

end Clauses

section Aligned

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F] [CharP F 2] {n p : ℕ}
  [Fact p.Prime] {ψ : StatedSp n F →* G} {A₀ : StatedSp n F} {ζ : Fˣ} {hζ : ζ ^ p = 1}

theorem comp_of_aligned (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F - 1) (hψ : Function.Injective ψ)
    (hζo : orderOf ζ = p) {β : Fin n → ZMod p} (hal : SpAligned β) {L₁ : Subgroup G}
    (hb1 : frameHom ψ A₀ hζ (ofAdd β) ≠ 1)
    (hcomp : CFSG.Assembly.IsComponentOf L₁
      (ψ.range ⊓ Subgroup.centralizer {frameHom ψ A₀ hζ (ofAdd β)}))
    (hcard : Nat.card ((frameHom ψ A₀ hζ).range ⊓ Subgroup.centralizer (L₁ : Set G) :
      Subgroup G) ≤ p ^ 2) :
    (∃ j j' : Fin n, (∀ i, i ≠ j → i ≠ j' → β i = 0) ∧
      ∀ t : Fin n → ZMod p, t j = 0 → t j' = 0 → frameHom ψ A₀ hζ (ofAdd t) ∈ L₁) ∨
    (∃ (k : Fin n) (c : ZMod p), c ≠ 0 ∧ (∀ i, i ≠ k → β i = c) ∧
      ∀ t : Fin n → ZMod p, t k = 0 → ∑ i, t i = 0 → frameHom ψ A₀ hζ (ofAdd t) ∈ L₁) := by
  classical
  have hp : p.Prime := Fact.out
  have hinj : Function.Injective (frameHom ψ A₀ hζ) := frameHom_injective ψ A₀ hζ hψ hζo
  have hβ0 : β ≠ 0 := fun h => hb1 (by rw [h, ofAdd_zero, map_one])
  have h4 : 4 ≤ Nat.card F := by
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    have h2 := Nat.le_of_dvd (by omega) hpF
    have h3 := hp.two_le
    omega
  have hb : frameHom ψ A₀ hζ (ofAdd β) = frameConj ψ A₀ (torusElt ζ β) := rfl
  rw [hb, centralizer_eq_map hψ A₀ ζ β] at hcomp
  have hφinj : Function.Injective (frameConj ψ A₀) := frameConj_injective hψ A₀
  have hmemC₀ : ∀ u, u ∈ Subgroup.centralizer ({torusElt ζ β} : Set (StatedSp n F)) ↔
      WtPres β (mat n F u) := fun u =>
    Subgroup.mem_centralizer_singleton_iff.trans (commute_torusElt_iff hζ hζo β u)
  set φ := frameConj ψ A₀ with hφdef
  set C₀ := Subgroup.centralizer ({torusElt ζ β} : Set (StatedSp n F)) with hC₀
  set KZ := suppGroup (n := n) (K := F) (planeSet (spClass β 0)) with hKZ
  set KC : ZMod p → Subgroup (StatedSp n F) := fun c => (classHom (F := F) (spClass β c)).range
    with hKC
  have hKZC : KZ ≤ C₀ := fun M hM => (hmemC₀ M).mpr (wtPres_of_mem_zeroBlock hM)
  have hKCC : ∀ c, KC c ≤ C₀ := by
    rintro c _ ⟨A, rfl⟩
    exact (hmemC₀ _).mpr (wtPres_classHom β c A)
  have hcommY : ∀ u ∈ C₀, u * torusElt ζ β = torusElt ζ β * u := fun u hu =>
    Subgroup.mem_centralizer_singleton_iff.mp hu
  have hKZn : ((KZ.map φ).subgroupOf (C₀.map φ)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono hKZC)]
    rintro _ _ ⟨M, hM, rfl⟩ ⟨u, hu, rfl⟩
    exact ⟨u * M * u⁻¹, conj_mem_suppGroup hζ hζo (planeSet_zero_union β) (hcommY u hu) hM,
      by rw [map_mul, map_mul, map_inv]⟩
  have hKCn : ∀ c, c ≠ 0 → (((KC c).map φ).subgroupOf (C₀.map φ)).Normal := by
    intro c hc
    rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono (hKCC c))]
    rintro _ _ ⟨M, hM, rfl⟩ ⟨u, hu, rfl⟩
    exact ⟨u * M * u⁻¹, conj_mem_range_classHom hp2 hζ hζo hal hc (hcommY u hu) hM,
      by rw [map_mul, map_mul, map_inv]⟩
  have hq := hcomp.2.2
  by_cases hZ : L₁ ≤ KZ.map φ
  ·
    left
    have hrange : KZ.map φ = (φ.comp (blockSp (F := F) (spClass β 0))).range := by
      rw [MonoidHom.range_comp, range_blockSp]
    have hZ1 : 1 ≤ (spClass β 0).card := by
      by_contra h0
      refine LinSemisimple.false_of_isQuasisimple_of_commute hq fun x hx y hy => ?_
      rw [hrange] at hZ
      obtain ⟨X, rfl⟩ := hZ hx
      obtain ⟨Z, rfl⟩ := hZ hy
      rw [← map_mul, ← map_mul, statedSp_comm_of_eq_zero (by omega) X Z]
    have hQ : CFSG.IsQuasisimple (StatedSp (spClass β 0).card F) :=
      CFSG.LieType.Universal.Symplectic.isQuasisimple _ F hZ1 (Or.inl (Or.inr h4))
    have hL₁ : L₁ = KZ.map φ := by
      have hc' :=
        CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hcomp hZ (Subgroup.map_mono hKZC)
      rw [hrange] at hc' ⊢
      exact CoordSL.eq_of_isComponentOf_range hQ _ hc'
    exact clause_zero hinj hβ0 hL₁ hcard
  · by_cases hCex : ∃ c, c ≠ 0 ∧ L₁ ≤ (KC c).map φ
    ·
      right
      obtain ⟨c, hc, hLc⟩ := hCex
      have hrange : (KC c).map φ = (φ.comp (classHom (F := F) (spClass β c))).range :=
        (MonoidHom.range_comp _ _).symm
      rw [hrange] at hLc
      have hS2 : 2 ≤ (spClass β c).card := by
        by_contra h1
        refine LinSemisimple.false_of_isQuasisimple_of_commute hq fun x hx y hy => ?_
        obtain ⟨X, rfl⟩ := hLc hx
        obtain ⟨Z, rfl⟩ := hLc hy
        rw [← map_mul, ← map_mul, CoordSL.specialLinear_comm_of_le_one (by omega) X Z]
      have hQ : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin (spClass β c).card) F) :=
        CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple _ F hS2
          (Or.inr (by omega)) (Or.inr LinSemisimple.natCard_ne_three)
      have hL₁ : L₁ = (KC c).map φ := by
        have hc' := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hcomp hLc
          (by rw [← hrange]; exact Subgroup.map_mono (hKCC c))
        rw [hrange]
        exact CoordSL.eq_of_isComponentOf_range hQ _ hc'
      have hS : (spClass β c).Nonempty := Finset.card_pos.mp (by omega)
      exact clause_class hp2 hinj hc hS hL₁ hcard
    ·
      exfalso
      push Not at hCex
      have hZb : ⁅L₁, KZ.map φ⁆ = ⊥ :=
        (CoordSL.le_or_commutator_eq_bot_of_normal hcomp (Subgroup.map_mono hKZC)
          hKZn).resolve_left hZ
      have hCb : ∀ c, c ≠ 0 → ⁅L₁, (KC c).map φ⁆ = ⊥ := fun c hc =>
        (CoordSL.le_or_commutator_eq_bot_of_normal hcomp (Subgroup.map_mono (hKCC c))
          (hKCn c hc)).resolve_left (hCex c hc)
      have hcommN : ∀ {N : Subgroup G}, ⁅L₁, N⁆ = ⊥ → ∀ x ∈ L₁, ∀ y ∈ N, x * y = y * x := by
        intro N hN x hx y hy
        have h1 := Subgroup.commutator_mem_commutator hx hy
        rw [hN, Subgroup.mem_bot] at h1
        exact commutatorElement_eq_one_iff_mul_comm.mp h1
      have hlift : ∀ w, φ w ∈ L₁ → (∀ M ∈ KZ, w * M = M * w) ∧
          ∀ c, c ≠ 0 → ∀ M ∈ KC c, w * M = M * w := by
        intro w hw
        refine ⟨fun M hM => hφinj ?_, fun c hc M hM => hφinj ?_⟩
        · rw [map_mul, map_mul]
          exact hcommN hZb _ hw _ (Subgroup.mem_map_of_mem φ hM)
        · rw [map_mul, map_mul]
          exact hcommN (hCb c hc) _ hw _ (Subgroup.mem_map_of_mem φ hM)
      refine LinSemisimple.false_of_isQuasisimple_of_commute hq fun x hx y hy => ?_
      obtain ⟨u, hu, rfl⟩ := hcomp.1 hx
      obtain ⟨v, hv, rfl⟩ := hcomp.1 hy
      rw [← map_mul, ← map_mul, commute_of_comm_blocks hp2 hal ((hmemC₀ u).mp hu)
        ((hmemC₀ v).mp hv) (hlift u hx).1 (hlift v hy).1 (hlift u hx).2 (hlift v hy).2]

end Aligned

section Align

variable {n p : ℕ}

@[expose] def alignFlip (β : Fin n → ZMod p) : Fin n → Bool :=
  fun i => decide (p / 2 < (β i).val)

@[expose] def alignSign (β : Fin n → ZMod p) (i : Fin n) : (ZMod p)ˣ :=
  if alignFlip β i then -1 else 1

theorem alignSign_mem (β : Fin n → ZMod p) (i : Fin n) : alignSign β i ∈ signs p := by
  unfold alignSign
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem alignSign_mul_self (β : Fin n → ZMod p) (i : Fin n) :
    alignSign β i * alignSign β i = 1 := by
  unfold alignSign
  split_ifs <;> simp

theorem alignSign_inv (β : Fin n → ZMod p) (i : Fin n) : (alignSign β i)⁻¹ = alignSign β i :=
  inv_eq_of_mul_eq_one_right (alignSign_mul_self β i)

theorem coe_alignSign_mul_self (β : Fin n → ZMod p) (i : Fin n) :
    (alignSign β i : ZMod p) * (alignSign β i : ZMod p) = 1 := by
  rw [← Units.val_mul, alignSign_mul_self, Units.val_one]

theorem alignSign_mul_eq (β : Fin n → ZMod p) (i : Fin n) :
    (alignSign β i : ZMod p) * β i = if p / 2 < (β i).val then -β i else β i := by
  unfold alignSign alignFlip
  by_cases h : p / 2 < (β i).val <;> simp [h]

theorem spAligned_align [NeZero p] (hp : p % 2 = 1) (β : Fin n → ZMod p) :
    SpAligned fun i => (alignSign β i : ZMod p) * β i := by
  have hlow : ∀ i, ((alignSign β i : ZMod p) * β i).val ≤ p / 2 := by
    intro i
    rw [alignSign_mul_eq]
    by_cases h : p / 2 < (β i).val
    · rw [ite_eq_left h]
      have hβ : β i ≠ 0 := by
        intro h0
        rw [h0, ZMod.val_zero] at h
        omega
      rw [ZMod.neg_val, ite_eq_right hβ]
      have := ZMod.val_lt (β i)
      omega
    · rw [ite_eq_right h]
      omega
  intro i j hij
  change (alignSign β i : ZMod p) * β i = -((alignSign β j : ZMod p) * β j) at hij
  change (alignSign β i : ZMod p) * β i = 0
  by_contra hne
  have hj : (alignSign β j : ZMod p) * β j ≠ 0 := by
    intro h0
    rw [h0, neg_zero] at hij
    exact hne hij
  have h1 := hlow i
  have h2 := hlow j
  rw [hij, ZMod.neg_val, ite_eq_right hj] at h1
  omega

end Align

section FlipFrame

variable {G : Type} [Group G] {F : Type} [Field F] [CharP F 2] {n p : ℕ} [NeZero p] {ζ : Fˣ}

theorem frameHom_flip (ψ : StatedSp n F →* G) (A₀ : StatedSp n F) (hζ : ζ ^ p = 1)
    (β t : Fin n → ZMod p) :
    frameHom ψ (A₀ * (spPerm (alignFlip β) (Equiv.refl (Fin n)))⁻¹) hζ
        (ofAdd fun i => (alignSign β i : ZMod p) * t i) = frameHom ψ A₀ hζ (ofAdd t) := by
  set P := spPerm (F := F) (alignFlip β) (Equiv.refl (Fin n)) with hP
  have key : P⁻¹ * spDiag (fun i => ζ ^ ((alignSign β i : ZMod p) * t i).val) * P =
      spDiag fun i => ζ ^ (t i).val := by
    rw [hP, spPerm_conj_spDiag]
    congr 1
    funext i
    simp only [Equiv.refl_apply]
    by_cases h : alignFlip β i = true
    · have hη : (alignSign β i : ZMod p) * t i = -t i := by simp [alignSign, h]
      rw [ite_eq_left h, hη, pow_val_neg hζ, inv_inv]
    · have hη : (alignSign β i : ZMod p) * t i = t i := by simp [alignSign, h]
      rw [ite_eq_right h, hη]
  change ψ ((A₀ * P⁻¹) * spDiag (fun i => ζ ^ ((alignSign β i : ZMod p) * t i).val) *
      (A₀ * P⁻¹)⁻¹) = ψ (A₀ * spDiag (fun i => ζ ^ (t i).val) * A₀⁻¹)
  rw [← key]
  congr 1
  group

end FlipFrame

section General

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F] [CharP F 2] {n p : ℕ}
  [Fact p.Prime] {ψ : StatedSp n F →* G} {A₀ : StatedSp n F} {ζ : Fˣ} {hζ : ζ ^ p = 1}

theorem comp_of_frame (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F - 1) (hψ : Function.Injective ψ)
    (hζo : orderOf ζ = p) {β : Fin n → ZMod p} {L₁ : Subgroup G}
    (hb1 : frameHom ψ A₀ hζ (ofAdd β) ≠ 1)
    (hcomp : CFSG.Assembly.IsComponentOf L₁
      (ψ.range ⊓ Subgroup.centralizer {frameHom ψ A₀ hζ (ofAdd β)}))
    (hcard : Nat.card ((frameHom ψ A₀ hζ).range ⊓ Subgroup.centralizer (L₁ : Set G) :
      Subgroup G) ≤ p ^ 2) :
    (∃ j j' : Fin n, (∀ i, i ≠ j → i ≠ j' → β i = 0) ∧
      ∀ t : Fin n → ZMod p, t j = 0 → t j' = 0 → frameHom ψ A₀ hζ (ofAdd t) ∈ L₁) ∨
    (∃ (k : Fin n) (c : ZMod p) (ε : Fin n → (ZMod p)ˣ), c ≠ 0 ∧
      (∀ i, ε i ∈ signs p) ∧ (∀ i, i ≠ k → β i = (ε i : ZMod p) * c) ∧
      ∀ t : Fin n → ZMod p, t k = 0 → ∑ i, (↑(ε i)⁻¹ : ZMod p) * t i = 0 →
        frameHom ψ A₀ hζ (ofAdd t) ∈ L₁) := by
  have hp : p.Prime := Fact.out
  have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  have hι' : ∀ t : Fin n → ZMod p,
      frameHom ψ (A₀ * (spPerm (alignFlip β) (Equiv.refl (Fin n)))⁻¹) hζ
        (ofAdd fun i => (alignSign β i : ZMod p) * t i) = frameHom ψ A₀ hζ (ofAdd t) :=
    frameHom_flip ψ A₀ hζ β
  have hηη : ∀ i, (alignSign β i : ZMod p) * (alignSign β i : ZMod p) = 1 :=
    coe_alignSign_mul_self β
  have hrange : (frameHom ψ (A₀ * (spPerm (alignFlip β) (Equiv.refl (Fin n)))⁻¹) hζ).range =
      (frameHom ψ A₀ hζ).range := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      refine ⟨ofAdd fun i => (alignSign β i : ZMod p) * toAdd u i, ?_⟩
      rw [← hι']
      congr 1
      apply toAdd.injective
      funext i
      simp only [toAdd_ofAdd]
      rw [← mul_assoc, hηη, one_mul]
    · rintro ⟨u, rfl⟩
      exact ⟨_, hι' (toAdd u)⟩
  have hal := spAligned_align hodd β
  have hb' := hι' β
  rw [← hb'] at hb1 hcomp
  rw [← hrange] at hcard
  rcases comp_of_aligned hp2 hpF hψ hζo hal hb1 hcomp hcard with
    ⟨j, j', hjj', hmem⟩ | ⟨k, c, hc, hβ'k, hmem⟩
  · left
    refine ⟨j, j', fun i hij hij' => ?_, fun t ht ht' => ?_⟩
    · have h1 : (alignSign β i : ZMod p) * β i = 0 := hjj' i hij hij'
      exact ((alignSign β i).isUnit.mul_right_eq_zero).mp h1
    · rw [← hι' t]
      refine hmem _ ?_ ?_
      · rw [ht, mul_zero]
      · rw [ht', mul_zero]
  · right
    refine ⟨k, c, alignSign β, hc, alignSign_mem β, fun i hik => ?_, fun t htk hsum => ?_⟩
    · have h1 : (alignSign β i : ZMod p) * β i = c := hβ'k i hik
      calc β i = (alignSign β i : ZMod p) * ((alignSign β i : ZMod p) * β i) := by
            rw [← mul_assoc, hηη, one_mul]
        _ = (alignSign β i : ZMod p) * c := by rw [h1]
    · rw [← hι' t]
      refine hmem _ ?_ ?_
      · rw [htk, mul_zero]
      · have hinv : ∀ i, (↑(alignSign β i)⁻¹ : ZMod p) = (alignSign β i : ZMod p) := fun i => by
          rw [alignSign_inv]
        change ∑ i, (alignSign β i : ZMod p) * t i = 0
        simpa only [hinv] using hsum

end General

end CoordSp

open CoordSp Multiplicative

theorem ggSpCoordCompInput_holds : GGSpCoordCompInput := by
  intro G _ _ F _ _ _ n p _ hp2 hpF ψ hψ A₀ ζ hζ hζo b L₁ _ hb1 hcomp hcard β hβ
  subst hβ
  exact comp_of_frame hp2 hpF hψ hζo hb1 hcomp hcard

section Model

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

theorem ggStepTwoCoordModelOn_PSp_of_contrary (hcontr : GGSpCoordContraryInput)
    (hns : GGSpCoordModelNonsplitInput) : GGStepTwoCoordModelOn .PSp :=
  ggStepTwoCoordModelOn_PSp_of_inputs ggSpCoordCompInput_holds hcontr hns

end Model

end CFSG.StandardType

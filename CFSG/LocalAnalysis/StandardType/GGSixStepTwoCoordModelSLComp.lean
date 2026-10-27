module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSLCompParts

public section

open Polynomial Module Matrix CFSG.RankThree.CALinearPlane
open scoped commutatorElement

namespace CFSG.StandardType

namespace CoordSL

open Multiplicative

section Setup

variable {G : Type} [Group G] {K : Type} [Field K] [Finite K] {g : K[X]} [Fact (Irreducible g)]
  {n s r p : ℕ} [NeZero p] {ψ : Matrix.SpecialLinearGroup (Fin n) K →* G}
  {A₀ : Matrix.SpecialLinearGroup (Fin n) K} {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r}
  {hC : (rootMat g).det = 1} {hCp : rootMat g ^ p = 1}

omit [Finite K] in
theorem frameHom_eq_ggFrame (t : Fin s → ZMod p) :
    frameHom ψ A₀ ε hC hCp (ofAdd t) =
      SLRep.ggFrame ψ A₀ (SLNS.nsSL ε hC (fun i => (t i).val)) :=
  rfl

omit [Finite K] in
theorem centralizer_eq_map (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
    (hnsplit : ∀ c : K, c ^ p = 1 → c = 1) (β : Fin s → ZMod p) :
    ψ.range ⊓ Subgroup.centralizer {frameHom ψ A₀ ε hC hCp (ofAdd β)} =
      (Subgroup.centralizer {SLNS.nsSL ε hC (fun i => (β i).val)}).map (SLRep.ggFrame ψ A₀) := by
  rw [frameHom_eq_ggFrame, ← SLRep.range_ggFrame ψ A₀]
  ext x
  simp only [Subgroup.mem_inf, MonoidHom.mem_range, Subgroup.mem_map,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨⟨h, rfl⟩, hgc⟩
    exact ⟨h, (SLNS.commute_nsSL_of_map_commute ε hC (SLRep.ker_ggFrame_le hker A₀) hnsplit hCp _
      hgc.symm).symm, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨⟨h, rfl⟩, by rw [← map_mul, ← map_mul, hh]⟩

end Setup

section Clauses

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K] [CharP K 2]
  {g : K[X]} [Fact (Irreducible g)] {n s r p : ℕ} [Fact p.Prime]
  {ψ : Matrix.SpecialLinearGroup (Fin n) K →* G} {A₀ : Matrix.SpecialLinearGroup (Fin n) K}
  {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r} {hC : (rootMat g).det = 1}
  {hCp : rootMat g ^ p = 1}

omit [Finite K] [CharP K 2] in
theorem clause_zero (hinj : Function.Injective (frameHom ψ A₀ ε hC hCp)) {β : Fin s → ZMod p}
    (hβ : β ≠ 0) {L₁ : Subgroup G}
    (hL₁ : L₁ = (coordBlockSL K (zeroCoords ε β)).map (SLRep.ggFrame ψ A₀))
    (hcard : Nat.card ((frameHom ψ A₀ ε hC hCp).range ⊓ Subgroup.centralizer (L₁ : Set G) :
      Subgroup G) ≤ p ^ 2) :
    ∃ j j' : Fin s, (∀ i, i ≠ j → i ≠ j' → β i = 0) ∧
      ∀ t : Fin s → ZMod p, t j = 0 → t j' = 0 → frameHom ψ A₀ ε hC hCp (ofAdd t) ∈ L₁ := by
  have hp : p.Prime := Fact.out
  have hcomm_t : ∀ t : Fin s → ZMod p, (∀ i, β i = 0 → t i = 0) →
      frameHom ψ A₀ ε hC hCp (ofAdd t) ∈ Subgroup.centralizer (L₁ : Set G) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [hL₁] at hx
    obtain ⟨M, hM, rfl⟩ := hx
    rw [frameHom_eq_ggFrame, ← map_mul, ← map_mul,
      comm_zeroBlock_of_torus (fun i hi => by rw [ht i hi, ZMod.val_zero]) hM]
  have hthree : ∀ i₁ i₂ i₃ : Fin s, i₁ ≠ i₂ → i₁ ≠ i₃ → i₂ ≠ i₃ → β i₁ ≠ 0 → β i₂ ≠ 0 →
      β i₃ ≠ 0 → False := by
    intro i₁ i₂ i₃ h12 h13 h23 h1 h2 h3
    set v : ZMod p × ZMod p × ZMod p → (Fin s → ZMod p) := fun a =>
      Pi.single i₁ a.1 + Pi.single i₂ a.2.1 + Pi.single i₃ a.2.2 with hvdef
    have hv : Function.Injective v := by
      intro a b hab
      have e1 := congrFun hab i₁
      have e2 := congrFun hab i₂
      have e3 := congrFun hab i₃
      simp only [hvdef, Pi.add_apply, Pi.single_apply, h12, h13, h23, Ne.symm h12, Ne.symm h13,
        Ne.symm h23, ↓reduceIte, add_zero, zero_add] at e1 e2 e3
      exact Prod.ext e1 (Prod.ext e2 e3)
    have hle := pow_three_le_natCard
      (H := (frameHom ψ A₀ ε hC hCp).range ⊓ Subgroup.centralizer (L₁ : Set G))
      (fun a => frameHom ψ A₀ ε hC hCp (ofAdd (v a)))
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
  have hmem : ∀ t : Fin s → ZMod p, (∀ i, β i ≠ 0 → t i = 0) →
      frameHom ψ A₀ ε hC hCp (ofAdd t) ∈ L₁ := by
    intro t ht
    rw [hL₁, frameHom_eq_ggFrame]
    exact Subgroup.mem_map_of_mem _ (nsSL_mem_zeroBlock fun i hi => by rw [ht i hi, ZMod.val_zero])
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


omit [Finite K] [CharP K 2] in
theorem clause_class (hinj : Function.Injective (frameHom ψ A₀ ε hC hCp))
    (hζ : AdjoinRoot.root g ^ p = 1) {β : Fin s → ZMod p} {c : ZMod p} (hc : c ≠ 0)
    (hS : (classSet β c).Nonempty) {L₁ : Subgroup G}
    (hL₁ : L₁ = ((coordBlockSL (AdjoinRoot g) (classSet β c)).map (theta g ε)).map
      (SLRep.ggFrame ψ A₀))
    (hcard : Nat.card ((frameHom ψ A₀ ε hC hCp).range ⊓ Subgroup.centralizer (L₁ : Set G) :
      Subgroup G) ≤ p ^ 2) :
    ∃ (k : Fin s) (c' : ZMod p), c' ≠ 0 ∧ (∀ i, i ≠ k → β i = c') ∧
      ∀ t : Fin s → ZMod p, t k = 0 → ∑ i, t i = 0 → frameHom ψ A₀ ε hC hCp (ofAdd t) ∈ L₁ := by
  have hp : p.Prime := Fact.out
  have hcomm_t : ∀ t : Fin s → ZMod p, (∀ i j, β i = c → β j = c → t i = t j) →
      frameHom ψ A₀ ε hC hCp (ofAdd t) ∈ Subgroup.centralizer (L₁ : Set G) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [hL₁] at hx
    obtain ⟨_, ⟨M, hM, rfl⟩, rfl⟩ := hx
    rw [frameHom_eq_ggFrame, ← map_mul, ← map_mul,
      comm_classBlock_of_torus (fun i j hi hj => by rw [ht i j hi hj]) hM]
  obtain ⟨i₀, hi₀⟩ := hS
  have hi₀' : β i₀ = c := mem_classSet.mp hi₀
  have hout : ∀ k₁ k₂ : Fin s, k₁ ≠ k₂ → β k₁ ≠ c → β k₂ ≠ c → False := by
    intro k₁ k₂ h12 h1 h2
    have h01 : i₀ ≠ k₁ := fun h => h1 (h ▸ hi₀')
    have h02 : i₀ ≠ k₂ := fun h => h2 (h ▸ hi₀')
    set v : ZMod p × ZMod p × ZMod p → (Fin s → ZMod p) := fun a =>
      Pi.single k₁ a.1 + Pi.single k₂ a.2.1 + fun i => if β i = c then a.2.2 else 0 with hvdef
    have hv : Function.Injective v := by
      intro a b hab
      have e1 := congrFun hab k₁
      have e2 := congrFun hab k₂
      have e3 := congrFun hab i₀
      simp only [hvdef, Pi.add_apply, Pi.single_apply, h12, Ne.symm h12, h01, h02, h1, h2, hi₀',
        ↓reduceIte, add_zero, zero_add] at e1 e2 e3
      exact Prod.ext e1 (Prod.ext e2 e3)
    have hle := pow_three_le_natCard
      (H := (frameHom ψ A₀ ε hC hCp).range ⊓ Subgroup.centralizer (L₁ : Set G))
      (fun a => frameHom ψ A₀ ε hC hCp (ofAdd (v a)))
      (hinj.comp (ofAdd.injective.comp hv)) fun a => Subgroup.mem_inf.mpr ⟨⟨_, rfl⟩,
        hcomm_t (v a) fun i j hi hj => by
          have hi1 : i ≠ k₁ := fun h => h1 (h ▸ hi)
          have hi2 : i ≠ k₂ := fun h => h2 (h ▸ hi)
          have hj1 : j ≠ k₁ := fun h => h1 (h ▸ hj)
          have hj2 : j ≠ k₂ := fun h => h2 (h ▸ hj)
          simp [hvdef, hi1, hi2, hj1, hj2, hi, hj]⟩
    exact absurd (hle.trans hcard) (not_le.mpr (Nat.pow_lt_pow_right hp.one_lt (by norm_num)))
  have hmem : ∀ t : Fin s → ZMod p, (∀ i, β i ≠ c → t i = 0) → ∑ i, t i = 0 →
      frameHom ψ A₀ ε hC hCp (ofAdd t) ∈ L₁ := by
    intro t ht hsum
    obtain ⟨D, hD, hθD⟩ := diag_mem_classBlock (ε := ε) (hC := hC) hζ ht hsum
    rw [hL₁, frameHom_eq_ggFrame, ← hθD]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hD)
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

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K] [CharP K 2]
  {g : K[X]} [Fact (Irreducible g)] {n s r p : ℕ} [Fact p.Prime]
  {ψ : Matrix.SpecialLinearGroup (Fin n) K →* G} {A₀ : Matrix.SpecialLinearGroup (Fin n) K}
  {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r} {hC : (rootMat g).det = 1}
  {hCp : rootMat g ^ p = 1}

omit [Finite G] in
theorem two_le_card_of_le_map_coordBlockSL {k : Type} [Field k] {m : ℕ}
    (φ : Matrix.SpecialLinearGroup (Fin m) k →* G) {J : Finset (Fin m)} {L₁ : Subgroup G}
    (hq : CFSG.Assembly.IsQuasisimple L₁) (hL : L₁ ≤ (coordBlockSL k J).map φ) : 2 ≤ J.card := by
  have hrange : (coordBlockSL k J).map φ = (φ.comp (blockSLOn k J)).range := by
    rw [MonoidHom.range_comp, range_blockSLOn]
  rw [hrange] at hL
  by_contra h1
  refine LinSemisimple.false_of_isQuasisimple_of_commute hq fun x hx y hy => ?_
  obtain ⟨X, rfl⟩ := hL hx
  obtain ⟨Y, rfl⟩ := hL hy
  rw [← map_mul, ← map_mul, specialLinear_comm_of_le_one (by omega) X Y]

theorem eq_of_aligned (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K - 1)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
    (hgd : g ∣ cyclotomic p K) {hζ : AdjoinRoot.root g ^ p = 1} {β : Fin s → ZMod p}
    (hal : Aligned hζ β) {L₁ : Subgroup G} (hb1 : frameHom ψ A₀ ε hC hCp (ofAdd β) ≠ 1)
    (hcomp : CFSG.Assembly.IsComponentOf L₁
      (ψ.range ⊓ Subgroup.centralizer {frameHom ψ A₀ ε hC hCp (ofAdd β)}))
    (hcard : Nat.card ((frameHom ψ A₀ ε hC hCp).range ⊓ Subgroup.centralizer (L₁ : Set G) :
      Subgroup G) ≤ p ^ 2) :
    (∃ j j' : Fin s, (∀ i, i ≠ j → i ≠ j' → β i = 0) ∧
      L₁ = (coordBlockSL K (zeroCoords ε β)).map (SLRep.ggFrame ψ A₀)) ∨
    (∃ (k : Fin s) (c : ZMod p), c ≠ 0 ∧ (∀ i, i ≠ k → β i = c) ∧
      L₁ = (coordBlockSL (AdjoinRoot g) (classSet β c)).map
        ((SLRep.ggFrame ψ A₀).comp (theta g ε))) := by
  classical
  have hp : p.Prime := Fact.out
  have hpK' : (p : K) ≠ 0 := OrdPNS.natCast_ne_zero_of_charTwo hp hp2
  have hprim := root_isPrimitiveRoot hp hpK' hgd
  have hinj : Function.Injective (frameHom ψ A₀ ε hC hCp) :=
    frameHom_injective ψ A₀ ε hC hCp hker (rootPB_dim_pos g)
      (isUnit_rootMat_pow_sub hp hpK hpK' hgd)
  have hnsplit : ∀ c : K, c ^ p = 1 → c = 1 := fun c hc => OrdPNS.eq_one_of_pow_eq_one hp hpK hc
  have hβ0 : β ≠ 0 := fun h => hb1 (by rw [h, ofAdd_zero, map_one])
  set φ := SLRep.ggFrame ψ A₀ with hφdef
  have hkerφ : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) :=
    SLRep.ker_ggFrame_le hker A₀
  set Y := SLNS.nsSL ε hC (fun i => (β i).val) with hY
  set C₀ := Subgroup.centralizer ({Y} : Set (Matrix.SpecialLinearGroup (Fin n) K)) with hC₀
  rw [centralizer_eq_map hker hnsplit β] at hcomp
  have hmemC₀ : ∀ u, u ∈ C₀ ↔ u * Y = Y * u := fun u => Subgroup.mem_centralizer_singleton_iff
  set J := zeroCoords ε β with hJ
  set KC : ZMod p → Subgroup (Matrix.SpecialLinearGroup (Fin n) K) := fun c =>
    (coordBlockSL (AdjoinRoot g) (classSet β c)).map (theta g ε) with hKC
  have hKZC : coordBlockSL K J ≤ C₀ := fun M hM => (hmemC₀ M).mpr
    (comm_zeroBlock_of_torus (k := fun i => (β i).val)
      (fun i hi => by rw [hi, ZMod.val_zero]) hM).symm
  have hKCC : ∀ c, KC c ≤ C₀ := by
    rintro c _ ⟨M, hM, rfl⟩
    exact (hmemC₀ _).mpr (comm_classBlock_of_torus (fun i j hi hj => by rw [hi, hj]) hM)
  have hKZn : (((coordBlockSL K J).map φ).subgroupOf (C₀.map φ)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono hKZC)]
    rintro _ _ ⟨M, hM, rfl⟩ ⟨u, hu, rfl⟩
    exact ⟨u * M * u⁻¹, conj_mem_zeroBlock hprim hal ((hmemC₀ u).mp hu) hM,
      by rw [map_mul, map_mul, map_inv]⟩
  have hKCn : ∀ c, c ≠ 0 → (((KC c).map φ).subgroupOf (C₀.map φ)).Normal := by
    intro c hc
    rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono (hKCC c))]
    rintro _ _ ⟨_, ⟨M, hM, rfl⟩, rfl⟩ ⟨u, hu, rfl⟩
    obtain ⟨M', hM', hM'eq⟩ := conj_mem_classBlock hprim hal hc ((hmemC₀ u).mp hu) hM
    exact ⟨theta g ε M', ⟨M', hM', rfl⟩, by rw [hM'eq, map_mul, map_mul, map_inv]⟩
  have hq := hcomp.2.2
  have hdZ := le_or_commutator_eq_bot_of_normal hcomp (Subgroup.map_mono hKZC) hKZn
  by_cases hZ : L₁ ≤ (coordBlockSL K J).map φ
  ·
    left
    have hQ := quasisimple_of_le_map_coordBlockSL φ hq hZ
    have hrange : (coordBlockSL K J).map φ = (φ.comp (blockSLOn K J)).range := by
      rw [MonoidHom.range_comp, range_blockSLOn]
    have hL₁ : L₁ = (coordBlockSL K J).map φ := by
      have hc' :=
        CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hcomp hZ (Subgroup.map_mono hKZC)
      rw [hrange] at hc' ⊢
      exact eq_of_isComponentOf_range hQ _ hc'
    obtain ⟨j, j', hjj', _⟩ := clause_zero hinj hβ0 hL₁ hcard
    exact ⟨j, j', hjj', hL₁⟩
  · by_cases hCex : ∃ c, c ≠ 0 ∧ L₁ ≤ (KC c).map φ
    ·
      right
      obtain ⟨c, hc, hLc⟩ := hCex
      have : CharP (AdjoinRoot g) 2 :=
        charP_of_injective_algebraMap (algebraMap K (AdjoinRoot g)).injective 2
      have : Finite (AdjoinRoot g) := finite_adjoinRoot
      have hmap : (KC c).map φ =
          (coordBlockSL (AdjoinRoot g) (classSet β c)).map (φ.comp (theta g ε)) :=
        Subgroup.map_map _ _ _
      rw [hmap] at hLc
      have hQ := quasisimple_of_le_map_coordBlockSL (φ.comp (theta g ε)) hq hLc
      have hS2 := two_le_card_of_le_map_coordBlockSL (φ.comp (theta g ε)) hq hLc
      have hS : (classSet β c).Nonempty := Finset.card_pos.mp (by omega)
      have hrange : (coordBlockSL (AdjoinRoot g) (classSet β c)).map (φ.comp (theta g ε)) =
          ((φ.comp (theta g ε)).comp (blockSLOn (AdjoinRoot g) (classSet β c))).range := by
        rw [MonoidHom.range_comp, range_blockSLOn]
      have hL₁ : L₁ = (KC c).map φ := by
        have hc' := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hcomp hLc
          (hmap ▸ Subgroup.map_mono (hKCC c))
        rw [hmap, hrange]
        rw [hrange] at hc'
        exact eq_of_isComponentOf_range hQ _ hc'
      obtain ⟨k, c', hc', hβ'k, _⟩ := clause_class hinj hζ hc hS hL₁ hcard
      have hc'eq : c' = c := by
        have hex : ∃ i, i ∈ classSet β c ∧ i ≠ k := by
          by_contra h
          push Not at h
          have hsub : classSet β c ⊆ {k} := fun i hi => by
            simpa using h i hi
          have hle := Finset.card_le_card hsub
          simp at hle
          omega
        obtain ⟨i, hi, hik⟩ := hex
        exact (hβ'k i hik).symm.trans (mem_classSet.mp hi)
      have hmap' : (KC c).map φ =
          (coordBlockSL (AdjoinRoot g) (classSet β c)).map
            ((SLRep.ggFrame ψ A₀).comp (theta g ε)) := by
        rw [hmap, hφdef]
      exact ⟨k, c, hc, fun i hik => (hβ'k i hik).trans hc'eq, hL₁.trans hmap'⟩
    ·
      exfalso
      push Not at hCex
      have hZb : ⁅L₁, (coordBlockSL K J).map φ⁆ = ⊥ := hdZ.resolve_left hZ
      have hCb : ∀ c, c ≠ 0 → ⁅L₁, (KC c).map φ⁆ = ⊥ := fun c hc =>
        (le_or_commutator_eq_bot_of_normal hcomp (Subgroup.map_mono (hKCC c))
          (hKCn c hc)).resolve_left (hCex c hc)
      have hcommN : ∀ {N : Subgroup G}, ⁅L₁, N⁆ = ⊥ → ∀ x ∈ L₁, ∀ y ∈ N, x * y = y * x := by
        intro N hN x hx y hy
        have h1 := Subgroup.commutator_mem_commutator hx hy
        rw [hN, Subgroup.mem_bot] at h1
        exact commutatorElement_eq_one_iff_mul_comm.mp h1
      have hZw : ∀ w, φ w ∈ L₁ → ∀ x y (hxy : x ≠ y), x ∈ J → y ∈ J →
          w * Matrix.SpecialLinearGroup.transvection hxy (1 : K) =
            Matrix.SpecialLinearGroup.transvection hxy 1 * w := by
        intro w hw x y hxy hx hy
        have ht := SLRep.transvection_mem_coordBlockSL hx hy hxy (1 : K)
        exact commute_of_map_commute_of_mul_self hkerφ (LinSemisimple.transvection_one_mul_self hxy)
          (hcommN hZb _ hw _ (Subgroup.mem_map_of_mem φ ht))
      have hcw : ∀ w, φ w ∈ L₁ → ∀ i j (hij : i ≠ j), β i = β j → β i ≠ 0 →
          ∀ c' : AdjoinRoot g, w * theta g ε (Matrix.SpecialLinearGroup.transvection hij c') =
            theta g ε (Matrix.SpecialLinearGroup.transvection hij c') * w := by
        intro w hw i j hij hβij hβi c'
        have hT := SLRep.transvection_mem_coordBlockSL (mem_classSet.mpr rfl)
          (mem_classSet.mpr hβij.symm) hij c'
        have hθT : theta g ε (Matrix.SpecialLinearGroup.transvection hij c') ∈ KC (β i) :=
          ⟨_, hT, rfl⟩
        exact commute_of_map_commute_of_mul_self hkerφ (theta_transvection_mul_self ε hij c')
          (hcommN (hCb (β i) hβi) _ hw _ (Subgroup.mem_map_of_mem φ hθT))
      refine LinSemisimple.false_of_isQuasisimple_of_commute hq fun x hx y hy => ?_
      obtain ⟨u, hu, rfl⟩ := hcomp.1 hx
      obtain ⟨v, hv, rfl⟩ := hcomp.1 hy
      rw [← map_mul, ← map_mul, commute_of_comm_blocks hprim hal ((hmemC₀ u).mp hu)
        ((hmemC₀ v).mp hv) (hZw u hx) (hZw v hy) (hcw u hx) (hcw v hy)]

theorem comp_of_aligned (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K - 1)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
    (hgd : g ∣ cyclotomic p K) {hζ : AdjoinRoot.root g ^ p = 1} {β : Fin s → ZMod p}
    (hal : Aligned hζ β) {L₁ : Subgroup G} (hb1 : frameHom ψ A₀ ε hC hCp (ofAdd β) ≠ 1)
    (hcomp : CFSG.Assembly.IsComponentOf L₁
      (ψ.range ⊓ Subgroup.centralizer {frameHom ψ A₀ ε hC hCp (ofAdd β)}))
    (hcard : Nat.card ((frameHom ψ A₀ ε hC hCp).range ⊓ Subgroup.centralizer (L₁ : Set G) :
      Subgroup G) ≤ p ^ 2) :
    (∃ j j' : Fin s, (∀ i, i ≠ j → i ≠ j' → β i = 0) ∧
      ∀ t : Fin s → ZMod p, t j = 0 → t j' = 0 → frameHom ψ A₀ ε hC hCp (ofAdd t) ∈ L₁) ∨
    (∃ (k : Fin s) (c : ZMod p), c ≠ 0 ∧ (∀ i, i ≠ k → β i = c) ∧
      ∀ t : Fin s → ZMod p, t k = 0 → ∑ i, t i = 0 → frameHom ψ A₀ ε hC hCp (ofAdd t) ∈ L₁) := by
  classical
  have hp : p.Prime := Fact.out
  have hpK' : (p : K) ≠ 0 := OrdPNS.natCast_ne_zero_of_charTwo hp hp2
  have hinj : Function.Injective (frameHom ψ A₀ ε hC hCp) :=
    frameHom_injective ψ A₀ ε hC hCp hker (rootPB_dim_pos g)
      (isUnit_rootMat_pow_sub hp hpK hpK' hgd)
  have hβ0 : β ≠ 0 := fun h => hb1 (by rw [h, ofAdd_zero, map_one])
  rcases eq_of_aligned hp2 hpK hker hgd hal hb1 hcomp hcard with
    ⟨-, -, -, hL₁⟩ | ⟨-, c, hc, -, hL₁⟩
  · left
    obtain ⟨j, j', hjj', hmem⟩ := clause_zero hinj hβ0 hL₁ hcard
    exact ⟨j, j', hjj', hmem⟩
  · right
    have hL₁' : L₁ = ((coordBlockSL (AdjoinRoot g) (classSet β c)).map (theta g ε)).map
        (SLRep.ggFrame ψ A₀) := by
      rw [hL₁, Subgroup.map_map]
    have hq : CFSG.Assembly.IsQuasisimple L₁ := hcomp.2.2
    have hLc : L₁ ≤ (coordBlockSL (AdjoinRoot g) (classSet β c)).map
        ((SLRep.ggFrame ψ A₀).comp (theta g ε)) := by
      rw [hL₁]
    have hS2 := two_le_card_of_le_map_coordBlockSL
      ((SLRep.ggFrame ψ A₀).comp (theta g ε)) hq hLc
    have hS : (classSet β c).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨k, c', hc', hβ'k, hmem⟩ := clause_class hinj hζ hc hS hL₁' hcard
    exact ⟨k, c', hc', hβ'k, hmem⟩

end Aligned

section Align

variable {K : Type} [Field K] {g : K[X]} [Fact (Irreducible g)] {s p : ℕ} [Fact p.Prime]

theorem exists_aligned (hζ : AdjoinRoot.root g ^ p = 1) (β : Fin s → ZMod p) :
    ∃ η : Fin s → (ZMod p)ˣ, (∀ i, η i ∈ galExp g hζ) ∧
      Aligned hζ (fun i => (η i : ZMod p) * β i) := by
  classical
  set O := galExp g hζ with hO
  set orb : Fin s → Finset (Fin s) := fun i =>
    Finset.univ.filter fun j => ∃ u ∈ O, β j = (u : ZMod p) * β i with horb
  have hself : ∀ i, i ∈ orb i := fun i => by
    simp only [horb, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨1, O.one_mem, by rw [Units.val_one, one_mul]⟩
  set f : Fin s → Fin s := fun i => (orb i).min' ⟨i, hself i⟩ with hf
  have hfmem : ∀ i, ∃ u ∈ O, β (f i) = (u : ZMod p) * β i := fun i => by
    have h := Finset.min'_mem (orb i) ⟨i, hself i⟩
    simp only [horb, Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact h
  choose η hηO hη using hfmem
  have hforb : ∀ i j, (∃ w ∈ O, β i = (w : ZMod p) * β j) → f i = f j := by
    intro i j ⟨w, hwO, hw⟩
    have horbeq : orb i = orb j := by
      ext k
      simp only [horb, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨v, hvO, hv⟩
        exact ⟨v * w, O.mul_mem hvO hwO, by rw [hv, hw, Units.val_mul, mul_assoc]⟩
      · rintro ⟨v, hvO, hv⟩
        refine ⟨v * w⁻¹, O.mul_mem hvO (O.inv_mem hwO), ?_⟩
        rw [hv, hw, Units.val_mul, mul_assoc, ← mul_assoc ((w⁻¹ : (ZMod p)ˣ) : ZMod p),
          ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    simp only [hf, horbeq]
  refine ⟨η, hηO, fun i j _ u huO hij => ?_⟩
  simp only at hij ⊢
  rw [← hη i, ← hη j] at hij ⊢
  have hrel : ∃ w ∈ O, β i = (w : ZMod p) * β j := by
    refine ⟨(η i)⁻¹ * u * η j, O.mul_mem (O.mul_mem (O.inv_mem (hηO i)) huO) (hηO j), ?_⟩
    rw [Units.val_mul, Units.val_mul, mul_assoc, mul_assoc, ← hη j, ← hij, hη i, ← mul_assoc,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  rw [hforb i j hrel]

end Align

section General

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K] [CharP K 2]
  {g : K[X]} [Fact (Irreducible g)] {n s r p : ℕ} [Fact p.Prime]
  {ψ : Matrix.SpecialLinearGroup (Fin n) K →* G} {A₀ : Matrix.SpecialLinearGroup (Fin n) K}
  {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r} {hC : (rootMat g).det = 1}
  {hCp : rootMat g ^ p = 1}

omit [Finite G] [CharP K 2] in
private theorem exists_aligned_frame_aux (hζ : AdjoinRoot.root g ^ p = 1)
    (β : Fin s → ZMod p) :
    ∃ (η : Fin s → (ZMod p)ˣ) (M : Matrix.SpecialLinearGroup (Fin n) K),
      (∀ i, η i ∈ galExp g hζ) ∧ Aligned hζ (fun i => (η i : ZMod p) * β i) ∧
      (∀ t : Fin s → ZMod p,
        frameHom ψ (A₀ * M) ε hC hCp (ofAdd fun i => (η i : ZMod p) * t i) =
          frameHom ψ A₀ ε hC hCp (ofAdd t)) ∧
      (frameHom ψ (A₀ * M) ε hC hCp).range = (frameHom ψ A₀ ε hC hCp).range := by
  obtain ⟨η, hηO, hal⟩ := exists_aligned hζ β
  obtain ⟨M, hM⟩ := exists_conj_frameHom g ψ A₀ ε hC hCp hζ (Equiv.refl _) η hηO
  set w := SLRep.ggFrame ψ A₀ M with hwdef
  have hw : ∀ u : Fin s → ZMod p, frameHom ψ (A₀ * M) ε hC hCp (ofAdd u) =
      w * frameHom ψ A₀ ε hC hCp (ofAdd u) * w⁻¹ := by
    intro u
    simp only [hwdef, frameHom_apply, SLRep.ggFrame_apply, ← map_inv, ← map_mul]
    congr 1
    group
  have hι' : ∀ t : Fin s → ZMod p,
      frameHom ψ (A₀ * M) ε hC hCp (ofAdd fun i => (η i : ZMod p) * t i) =
        frameHom ψ A₀ ε hC hCp (ofAdd t) := by
    intro t
    have h := hM t
    simp only [Equiv.refl_apply] at h
    rw [hw, ← h]
    group
  have hrange : (frameHom ψ (A₀ * M) ε hC hCp).range = (frameHom ψ A₀ ε hC hCp).range := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      refine ⟨ofAdd fun i => ((η i)⁻¹ : (ZMod p)ˣ) * toAdd u i, ?_⟩
      rw [← hι']
      congr 1
      apply toAdd.injective
      funext i
      simp only [toAdd_ofAdd]
      rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    · rintro ⟨u, rfl⟩
      exact ⟨_, hι' (toAdd u)⟩
  exact ⟨η, M, hηO, hal, hι', hrange⟩

theorem comp_of_frame (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K - 1)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
    (hgd : g ∣ cyclotomic p K) (hζ : AdjoinRoot.root g ^ p = 1) {β : Fin s → ZMod p}
    {L₁ : Subgroup G} (hb1 : frameHom ψ A₀ ε hC hCp (ofAdd β) ≠ 1)
    (hcomp : CFSG.Assembly.IsComponentOf L₁
      (ψ.range ⊓ Subgroup.centralizer {frameHom ψ A₀ ε hC hCp (ofAdd β)}))
    (hcard : Nat.card ((frameHom ψ A₀ ε hC hCp).range ⊓ Subgroup.centralizer (L₁ : Set G) :
      Subgroup G) ≤ p ^ 2) :
    (∃ j j' : Fin s, (∀ i, i ≠ j → i ≠ j' → β i = 0) ∧
      ∀ t : Fin s → ZMod p, t j = 0 → t j' = 0 → frameHom ψ A₀ ε hC hCp (ofAdd t) ∈ L₁) ∨
    (∃ (k : Fin s) (c : ZMod p) (ε' : Fin s → (ZMod p)ˣ), c ≠ 0 ∧
      (∀ i, ε' i ∈ galExp g hζ) ∧ (∀ i, i ≠ k → β i = (ε' i : ZMod p) * c) ∧
      ∀ t : Fin s → ZMod p, t k = 0 → ∑ i, (↑(ε' i)⁻¹ : ZMod p) * t i = 0 →
        frameHom ψ A₀ ε hC hCp (ofAdd t) ∈ L₁) := by
  obtain ⟨η, M, hηO, hal, hι', hrange⟩ := exists_aligned_frame_aux (ψ := ψ) (A₀ := A₀)
    (ε := ε) (hC := hC) (hCp := hCp) hζ β
  have hb' := hι' β
  rw [← hb'] at hb1 hcomp
  rw [← hrange] at hcard
  rcases comp_of_aligned hp2 hpK hker hgd hal hb1 hcomp hcard with
    ⟨j, j', hjj', hmem⟩ | ⟨k, c, hc, hβ'k, hmem⟩
  · left
    refine ⟨j, j', fun i hij hij' => ?_, fun t ht ht' => ?_⟩
    · have h1 := hjj' i hij hij'
      exact ((η i).isUnit.mul_right_eq_zero).mp h1
    · rw [← hι' t]
      exact hmem _ (by simp [ht]) (by simp [ht'])
  · right
    refine ⟨k, c, fun i => (η i)⁻¹, hc, fun i => (galExp g hζ).inv_mem (hηO i),
      fun i hik => ?_, fun t htk hsum => ?_⟩
    · have h1 := hβ'k i hik
      rw [← h1, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    · rw [← hι' t]
      refine hmem _ (by simp [htk]) ?_
      simpa only [inv_inv] using hsum

theorem comp_eq_of_frame (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K - 1)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
    (hgd : g ∣ cyclotomic p K) (hζ : AdjoinRoot.root g ^ p = 1) {β : Fin s → ZMod p}
    {L₁ : Subgroup G} (hb1 : frameHom ψ A₀ ε hC hCp (ofAdd β) ≠ 1)
    (hcomp : CFSG.Assembly.IsComponentOf L₁
      (ψ.range ⊓ Subgroup.centralizer {frameHom ψ A₀ ε hC hCp (ofAdd β)}))
    (hcard : Nat.card ((frameHom ψ A₀ ε hC hCp).range ⊓ Subgroup.centralizer (L₁ : Set G) :
      Subgroup G) ≤ p ^ 2) :
    ∃ (A₁ : Matrix.SpecialLinearGroup (Fin n) K) (β₁ : Fin s → ZMod p),
      (frameHom ψ A₁ ε hC hCp).range = (frameHom ψ A₀ ε hC hCp).range ∧
      frameHom ψ A₁ ε hC hCp (ofAdd β₁) = frameHom ψ A₀ ε hC hCp (ofAdd β) ∧
      ((∃ j j' : Fin s, (∀ i, i ≠ j → i ≠ j' → β₁ i = 0) ∧
          L₁ = (coordBlockSL K (zeroCoords ε β₁)).map (SLRep.ggFrame ψ A₁)) ∨
        (∃ (k : Fin s) (c : ZMod p), c ≠ 0 ∧ (∀ i, i ≠ k → β₁ i = c) ∧
          L₁ = (coordBlockSL (AdjoinRoot g) (classSet β₁ c)).map
            ((SLRep.ggFrame ψ A₁).comp (theta g ε)))) := by
  obtain ⟨η, M, -, hal, hι', hrange⟩ := exists_aligned_frame_aux (ψ := ψ) (A₀ := A₀)
    (ε := ε) (hC := hC) (hCp := hCp) hζ β
  have hb' := hι' β
  rw [← hb'] at hb1 hcomp
  rw [← hrange] at hcard
  refine ⟨A₀ * M, fun i => (η i : ZMod p) * β i, hrange, hι' β, ?_⟩
  exact eq_of_aligned hp2 hpK hker hgd hal hb1 hcomp hcard

end General

end CoordSL

open CoordSL Multiplicative

theorem ggSLCoordCompInput_holds : GGSLCoordCompInput := by
  intro G _ _ F _ _ _ n p _ hp2 hpF ψ hker g _ hgd s r ε A₀ hC hCp hζ b L₁ _ hb1 hcomp hcard β hβ
  subst hβ
  exact comp_of_frame hp2 hpF hker hgd hζ hb1 hcomp hcard


section Model

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

theorem ggStepTwoCoordModelOn_PSL_of_contrary (hcontr : GGSLCoordContraryInput) :
    GGStepTwoCoordModelOn .PSL :=
  ggStepTwoCoordModelOn_PSL_of_inputs ggSLCoordCompInput_holds hcontr

end Model

end CFSG.StandardType

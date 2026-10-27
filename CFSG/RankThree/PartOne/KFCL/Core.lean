module

public import CFSG.RankThree.PartOne.KFCL.GenDefs
public import CFSG.RankThree.PartOne.S15K.KtData
public import CFSG.RankThree.PartOne.S12.Sec1511Tools
public import CFSG.RankThree.PartOne.S12.Sec1322Reflect

public section

namespace CFSG.RankThree.PartOne.KFCL

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne
open scoped commutatorElement

section Transfer

variable {G : Type*} [Group G]

theorem commutator_subgroupOf_eq' {C Q : Subgroup G} (hQC : Q ≤ C) (hQ : ⁅Q, Q⁆ = Q) :
    ⁅Q.subgroupOf C, Q.subgroupOf C⁆ = Q.subgroupOf C := by
  apply Subgroup.map_injective C.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hQC, hQ]

theorem commutator_eq_of_subgroupOf' {C Q : Subgroup G} (hQC : Q ≤ C)
    (hQ : ⁅Q.subgroupOf C, Q.subgroupOf C⁆ = Q.subgroupOf C) : ⁅Q, Q⁆ = Q := by
  have := congrArg (Subgroup.map C.subtype) hQ
  rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hQC] at this

theorem subgroupOf_iSup {ι : Sort*} {C : Subgroup G} (X : ι → Subgroup G) (hX : ∀ i, X i ≤ C) :
    (⨆ i, X i).subgroupOf C = ⨆ i, (X i).subgroupOf C := by
  apply Subgroup.map_injective C.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le (iSup_le hX), Subgroup.map_iSup]
  exact iSup_congr fun i => (Subgroup.map_subgroupOf_eq_of_le (hX i)).symm

end Transfer

theorem conjBy_subgroupOf {G : Type} [Group G] {I K : Subgroup G} (w : ↥I) :
    (conjBy (w : G) K).subgroupOf I = (K.subgroupOf I).map (MulAut.conj w).toMonoidHom := by
  ext x
  rw [Subgroup.mem_subgroupOf, Equivariance.mem_conjBy, Subgroup.mem_map_equiv,
    MulAut.conj_symm_apply, Subgroup.mem_subgroupOf]
  rfl

structure RootData (p : ℕ) {Γ : Type*} [Group Γ] (T : Subgroup Γ) where
  ι : Type
  block : ι → Subgroup Γ
  hyp : ι → Subgroup Γ
  W : Subgroup Γ
  W_le : W ≤ Subgroup.normalizer (T : Set Γ)
  hyp_le : ∀ i, hyp i ≤ T
  hyp_ne : ∀ i, hyp i ≠ T
  hyp_inj : Function.Injective hyp
  block_le : ∀ i, block i ≤ Subgroup.centralizer (hyp i : Set Γ)
  block_simple : ∀ (i : ι) (N : Subgroup Γ), N ≤ block i → (N.subgroupOf (block i)).Normal →
    N = ⊥ ∨ N = block i
  derived_le : ∀ S : Subgroup Γ, S ≤ T →
    (S.relIndex T = p ∨ ∃ e : Γ, e ∈ T ∧ e ≠ 1 ∧ S = Subgroup.zpowers e) →
    ⁅Subgroup.centralizer (S : Set Γ), Subgroup.centralizer (S : Set Γ)⁆ ≤
      ⨆ i : {i : ι // S ≤ hyp i}, block i.1
  weyl : ∀ w ∈ W, ∀ i : ι, ∃ j : ι, (block i).map (MulAut.conj w).toMonoidHom = block j ∧
    (hyp i).map (MulAut.conj w).toMonoidHom = hyp j

namespace RootData

variable {p : ℕ} {Γ : Type*} [Group Γ] {T : Subgroup Γ}

@[expose] def WStable (R : RootData p T) (J : Set R.ι) : Prop :=
  ∀ w ∈ R.W, ∀ i ∈ J, ∃ j ∈ J, (R.block i).map (MulAut.conj w).toMonoidHom = R.block j ∧
    (R.hyp i).map (MulAut.conj w).toMonoidHom = R.hyp j

@[expose] def GenBlocks (R : RootData p T) : Prop :=
  ∀ J : Set R.ι, R.WStable J → (⨆ i ∈ J, R.block i) = ⊤ → J = Set.univ

structure ReflData (R : RootData p T) (N : ℕ) where
  Tblock_card : ∀ i, Nat.card ↥(T ⊓ R.block i) = p
  hyp_inf : ∀ i, R.hyp i ⊓ (T ⊓ R.block i) = ⊥
  hyp_sup : ∀ i, R.hyp i ⊔ (T ⊓ R.block i) = T
  refl : R.ι → MulAut ↥T
  refl_fix : ∀ i (x : ↥T), (x : Γ) ∈ R.hyp i → refl i x = x
  refl_inv : ∀ i (x : ↥T), (x : Γ) ∈ R.block i → refl i x = x⁻¹
  weyl_card : Nat.card ↥(Subgroup.closure (Set.range refl)) ≤ N
  gen : ∀ J : Set R.ι, R.WStable J →
    Subgroup.closure (refl '' J) = Subgroup.closure (Set.range refl) → J = Set.univ

end RootData

section Map

variable {p : ℕ} {Γ Γ' : Type*} [Group Γ] [Group Γ']

theorem map_centralizer_equiv (φ : Γ ≃* Γ') (S : Subgroup Γ) :
    (Subgroup.centralizer (S : Set Γ)).map φ.toMonoidHom =
      Subgroup.centralizer ((S.map φ.toMonoidHom : Subgroup Γ') : Set Γ') := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h s' hs'
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hs'
    have := h s hs
    have h2 := congrArg φ this
    simpa using h2
  · intro h s hs
    have := h (φ s) (Subgroup.mem_map_of_mem φ.toMonoidHom hs)
    apply φ.injective
    simpa using this

theorem map_conj_map (φ : Γ ≃* Γ') (w : Γ) (H : Subgroup Γ) :
    (H.map φ.toMonoidHom).map (MulAut.conj (φ w)).toMonoidHom =
      (H.map (MulAut.conj w).toMonoidHom).map φ.toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp

theorem map_top_equiv (φ : Γ ≃* Γ') : (⊤ : Subgroup Γ).map φ.toMonoidHom = ⊤ := by
  rw [← MonoidHom.range_eq_map]
  exact MonoidHom.range_eq_top.2 φ.surjective

@[expose] def RootData.map {T : Subgroup Γ} (R : RootData p T) (φ : Γ ≃* Γ') :
    RootData p (T.map φ.toMonoidHom) where
  ι := R.ι
  block i := (R.block i).map φ.toMonoidHom
  hyp i := (R.hyp i).map φ.toMonoidHom
  W := R.W.map φ.toMonoidHom
  W_le := by
    rintro _ ⟨w, hw, rfl⟩
    have hwn := R.W_le hw
    rw [Subgroup.mem_normalizer_iff] at hwn ⊢
    intro x'
    obtain ⟨x, rfl⟩ := φ.surjective x'
    constructor
    · intro hx'
      have hx : x ∈ T := by
        obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx'
        exact φ.injective hyx ▸ hy
      have := (hwn x).1 hx
      refine Subgroup.mem_map.2 ⟨_, this, ?_⟩
      simp
    · intro hx'
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx'
      have hy' : y = w * x * w⁻¹ := φ.injective (by simpa using hyx)
      have hxT : x ∈ T := (hwn x).2 (hy' ▸ hy)
      exact Subgroup.mem_map_of_mem φ.toMonoidHom hxT
  hyp_le i := Subgroup.map_mono (R.hyp_le i)
  hyp_ne i := fun h => R.hyp_ne i (Subgroup.map_injective (f := φ.toMonoidHom) φ.injective h)
  hyp_inj i j hij := R.hyp_inj (Subgroup.map_injective (f := φ.toMonoidHom) φ.injective hij)
  block_le i := by
    rw [← map_centralizer_equiv]
    exact Subgroup.map_mono (R.block_le i)
  block_simple i N' hN' hnorm := by
    set N : Subgroup Γ := N'.map φ.symm.toMonoidHom with hN
    have hNb : N ≤ R.block i := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨b, hb, hby⟩ := Subgroup.mem_map.1 (hN' hy)
      have : φ.symm y = b := by rw [← hby]; simp
      simpa [this] using hb
    have hmapN : N.map φ.toMonoidHom = N' := by
      rw [hN, Subgroup.map_map]
      have : φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id Γ' := by ext x; simp
      rw [this, Subgroup.map_id]
    have hNnorm : (N.subgroupOf (R.block i)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hNb]
      intro n g hn hg
      have hn' : φ n ∈ N' := by rw [← hmapN]; exact Subgroup.mem_map_of_mem _ hn
      have hg' : φ g ∈ (R.block i).map φ.toMonoidHom := Subgroup.mem_map_of_mem _ hg
      have := (Subgroup.normal_subgroupOf_iff hN').1 hnorm (φ n) (φ g) hn' hg'
      have h2 : φ (g * n * g⁻¹) ∈ N' := by simpa using this
      rw [← hmapN] at h2
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 h2
      exact φ.injective hyx ▸ hy
    rcases R.block_simple i N hNb hNnorm with h0 | h0
    · left
      rw [← hmapN, h0, Subgroup.map_bot]
    · right
      rw [← hmapN, h0]
  derived_le S' hS' hshape' := by
    set S : Subgroup Γ := S'.map φ.symm.toMonoidHom with hS
    have hSS' : S.map φ.toMonoidHom = S' := by
      rw [hS, Subgroup.map_map]
      have : φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id Γ' := by ext x; simp
      rw [this, Subgroup.map_id]
    have hST : S ≤ T := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨t, ht, hty⟩ := Subgroup.mem_map.1 (hS' hy)
      have : φ.symm y = t := by rw [← hty]; simp
      simpa [this] using ht
    have hshape : S.relIndex T = p ∨ ∃ e : Γ, e ∈ T ∧ e ≠ 1 ∧ S = Subgroup.zpowers e := by
      rcases hshape' with hidx | ⟨e', he'T, he'1, rfl⟩
      · left
        rw [← hidx, ← Subgroup.relIndex_map_map_of_injective (f := φ.toMonoidHom) S T φ.injective, hSS']
      · right
        obtain ⟨e, heT, rfl⟩ := Subgroup.mem_map.1 he'T
        refine ⟨e, heT, fun h => he'1 (by simp [h]), ?_⟩
        apply Subgroup.map_injective (f := φ.toMonoidHom) φ.injective
        rw [hSS', MonoidHom.map_zpowers]
    have h1 := R.derived_le S hST hshape
    have h2 := Subgroup.map_mono (f := φ.toMonoidHom) h1
    rw [Subgroup.map_commutator, map_centralizer_equiv, hSS', Subgroup.map_iSup] at h2
    refine h2.trans (iSup_le fun i => ?_)
    refine le_iSup_of_le ⟨i.1, ?_⟩ le_rfl
    rw [← hSS']
    exact Subgroup.map_mono i.2
  weyl w' hw' i := by
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hw'
    obtain ⟨j, hjb, hjh⟩ := R.weyl w hw i
    refine ⟨j, ?_, ?_⟩
    · show ((R.block i).map φ.toMonoidHom).map (MulAut.conj (φ w)).toMonoidHom =
        (R.block j).map φ.toMonoidHom
      rw [map_conj_map, hjb]
    · show ((R.hyp i).map φ.toMonoidHom).map (MulAut.conj (φ w)).toMonoidHom =
        (R.hyp j).map φ.toMonoidHom
      rw [map_conj_map, hjh]

theorem RootData.WStable.of_map {T : Subgroup Γ} {R : RootData p T} {φ : Γ ≃* Γ'} {J : Set R.ι}
    (h : (R.map φ).WStable J) : R.WStable J := by
  intro w hw i hi
  obtain ⟨j, hjJ, hjb, hjh⟩ := h (φ w) (Subgroup.mem_map_of_mem _ hw) i hi
  refine ⟨j, hjJ, ?_, ?_⟩
  · apply Subgroup.map_injective (f := φ.toMonoidHom) φ.injective
    rw [← map_conj_map]
    exact hjb
  · apply Subgroup.map_injective (f := φ.toMonoidHom) φ.injective
    rw [← map_conj_map]
    exact hjh

theorem RootData.GenBlocks.map {T : Subgroup Γ} {R : RootData p T} (hR : R.GenBlocks)
    (φ : Γ ≃* Γ') : (R.map φ).GenBlocks := by
  intro J hJ htop
  refine hR J hJ.of_map ?_
  have h1 : (⨆ i ∈ J, R.block i).map φ.toMonoidHom = ⊤ := by
    rw [Subgroup.map_iSup]
    simp only [Subgroup.map_iSup]
    exact htop
  exact Subgroup.map_injective (f := φ.toMonoidHom) φ.injective (h1.trans (map_top_equiv φ).symm)

noncomputable abbrev tEquiv (φ : Γ ≃* Γ') (T : Subgroup Γ) : ↥T ≃* ↥(T.map φ.toMonoidHom) :=
  Subgroup.equivMapOfInjective T φ.toMonoidHom φ.injective

@[expose] noncomputable def RootData.ReflData.map {T : Subgroup Γ} {R : RootData p T} {N : ℕ}
    (rd : R.ReflData N) (φ : Γ ≃* Γ') : (R.map φ).ReflData N where
  Tblock_card (i : R.ι) := by
    show Nat.card ↥((T.map φ.toMonoidHom) ⊓ (R.block i).map φ.toMonoidHom) = p
    rw [← Subgroup.map_inf _ _ φ.toMonoidHom φ.injective, Subgroup.card_map_of_injective φ.injective]
    exact rd.Tblock_card i
  hyp_inf (i : R.ι) := by
    show (R.hyp i).map φ.toMonoidHom ⊓ ((T.map φ.toMonoidHom) ⊓ (R.block i).map φ.toMonoidHom) = ⊥
    rw [← Subgroup.map_inf _ _ φ.toMonoidHom φ.injective, ← Subgroup.map_inf _ _ φ.toMonoidHom φ.injective, rd.hyp_inf i,
      Subgroup.map_bot]
  hyp_sup (i : R.ι) := by
    show (R.hyp i).map φ.toMonoidHom ⊔ ((T.map φ.toMonoidHom) ⊓ (R.block i).map φ.toMonoidHom) =
      T.map φ.toMonoidHom
    rw [← Subgroup.map_inf _ _ φ.toMonoidHom φ.injective, ← Subgroup.map_sup, rd.hyp_sup i]
  refl (i : R.ι) := MulAut.congr (tEquiv φ T) (rd.refl i)
  refl_fix (i : R.ι) x hx := by
    have hx' : (x : Γ') ∈ (R.hyp i).map φ.toMonoidHom := hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx'
    have hxy : x = tEquiv φ T ⟨y, (R.hyp_le i) hy⟩ := Subtype.ext hyx.symm
    subst hxy
    show tEquiv φ T (rd.refl i ((tEquiv φ T).symm (tEquiv φ T ⟨y, _⟩))) = _
    rw [MulEquiv.symm_apply_apply, rd.refl_fix i _ hy]
  refl_inv (i : R.ι) x hx := by
    have hx' : (x : Γ') ∈ (R.block i).map φ.toMonoidHom := hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx'
    have hyT : y ∈ T := by
      have := x.2
      obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.1 this
      exact φ.injective (hzx.trans hyx.symm) ▸ hz
    have hxy : x = tEquiv φ T ⟨y, hyT⟩ := Subtype.ext hyx.symm
    subst hxy
    show tEquiv φ T (rd.refl i ((tEquiv φ T).symm (tEquiv φ T ⟨y, _⟩))) = _
    rw [MulEquiv.symm_apply_apply, rd.refl_inv i _ hy, map_inv]
  weyl_card := by
    have h1 : Subgroup.closure (Set.range fun i : R.ι => (MulAut.congr (tEquiv φ T)) (rd.refl i)) =
        (Subgroup.closure (Set.range rd.refl)).map (MulAut.congr (tEquiv φ T)).toMonoidHom := by
      rw [MonoidHom.map_closure, ← Set.range_comp]
      rfl
    show Nat.card ↥(Subgroup.closure
      (Set.range fun i : R.ι => (MulAut.congr (tEquiv φ T)) (rd.refl i))) ≤ N
    rw [h1, Subgroup.card_map_of_injective (MulAut.congr (tEquiv φ T)).injective]
    exact rd.weyl_card
  gen J hJ hcl := by
    refine rd.gen J hJ.of_map ?_
    have h1 : ∀ S : Set R.ι,
        Subgroup.closure ((fun i : R.ι => (MulAut.congr (tEquiv φ T)) (rd.refl i)) '' S) =
        (Subgroup.closure (rd.refl '' S)).map (MulAut.congr (tEquiv φ T)).toMonoidHom := fun S => by
      rw [MonoidHom.map_closure, ← Set.image_comp]
      rfl
    have h2 : Subgroup.closure
        (Set.range fun i : R.ι => (MulAut.congr (tEquiv φ T)) (rd.refl i)) =
        (Subgroup.closure (Set.range rd.refl)).map (MulAut.congr (tEquiv φ T)).toMonoidHom := by
      rw [← Set.image_univ, h1 Set.univ, Set.image_univ]
    have hcl' : Subgroup.closure
        ((fun i : R.ι => (MulAut.congr (tEquiv φ T)) (rd.refl i)) '' J) =
        Subgroup.closure (Set.range fun i : R.ι => (MulAut.congr (tEquiv φ T)) (rd.refl i)) := hcl
    rw [h1 J, h2] at hcl'
    exact Subgroup.map_injective (MulAut.congr (tEquiv φ T)).injective hcl'

end Map

@[expose] def weylOrder (r : ℕ) : ℕ := if r = 1 then 24 else 48

theorem OutcomeEven.card_reflectionGroup {G : Type} [Group G] {p : ℕ} {E A I : Subgroup G} {r : ℕ}
    (h : OutcomeEven r p E A I) (hr1 : 1 ≤ r) (hr4 : r ≤ 4) :
    Nat.card ↥(reflectionGroup p E) = weylOrder r := by
  interval_cases r
  · obtain ⟨f, -, -, -, ⟨σ⟩, -⟩ := h
    rw [Nat.card_congr σ.toEquiv, Nat.card_eq_fintype_card]
    simp [weylOrder, Fintype.card_perm, Nat.factorial]
  · obtain ⟨f, -, -, -, ⟨σ⟩, -⟩ := h
    rw [Nat.card_congr σ.toEquiv, Nat.card_eq_fintype_card]
    simp [weylOrder, Fintype.card_perm, Fintype.card_prod, Nat.factorial]
  · obtain ⟨f, -, -, -, ⟨σ⟩, -⟩ := h
    rw [Nat.card_congr σ.toEquiv, Nat.card_eq_fintype_card]
    simp [weylOrder, Fintype.card_perm, Fintype.card_prod, Nat.factorial]
  · obtain ⟨f, -, -, -, ⟨σ⟩, -⟩ := h
    rw [Nat.card_congr σ.toEquiv, Nat.card_eq_fintype_card]
    simp [weylOrder, Fintype.card_perm, Fintype.card_prod, Nat.factorial]

@[expose] def RootModelRow (r : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    OutcomeEven r p E A (lieGenerated p E) → E ≤ lieGenerated p E →
    ∃ R : RootData p (E.subgroupOf (lieGenerated p E)),
      R.GenBlocks ∨ Nonempty (R.ReflData (weylOrder r))

section Glue

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

omit [Finite G] in
theorem kt_facts {t : MulAut E} (ht : t ∈ reflectionSet p E) {g : ℕ} (hKF : KFAt p E g t) :
    CFSG.IsQuasisimple ↥(kZero p E t) ∧ IsKt p E t (kZero p E t) ∧ kZero p E t ≤ lieGenerated p E := by
  obtain ⟨hne, hmod, -, -, -⟩ := hKF
  have hKt : IsKt p E t (kZero p E t) := ⟨fun f hf => absurd ⟨f, hf⟩ hne, fun _ => rfl⟩
  exact ⟨S15K.isQuasisimple_of_model hmod, hKt, le_sSup ⟨t, ht, hKt⟩⟩

theorem relIndex_fixed (h : Sec12Hyp G p A c L E) {t : MulAut E} (ht : t ∈ reflectionSet p E) :
    (autFixedInG E t).relIndex E = p := by
  obtain ⟨-, -, -, hcard⟩ := Sec13Base.reflection_facts h ht
  have hDE : autFixedInG E t ≤ E := Subgroup.map_subtype_le _
  have hcD : Nat.card ↥(autFixedInG E t) = Nat.card ↥(autFixed E t) := by
    unfold autFixedInG
    exact Subgroup.card_map_of_injective E.subtype_injective
  have h1 := Subgroup.relIndex_mul_card (H := autFixedInG E t) (K := E)
  rw [inf_eq_left.2 hDE, hcD] at h1
  have hpos : 0 < Nat.card ↥(autFixed E t) := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h1, hcard, mul_comm]

theorem kt_block {I : Subgroup G} (h : Sec12Hyp G p A c L E) (hEI : E ≤ I)
    (R : RootData p (E.subgroupOf I)) {t : MulAut E} (ht : t ∈ reflectionSet p E)
    (hq : CFSG.IsQuasisimple ↥(kZero p E t)) (hKI : kZero p E t ≤ I) :
    ∃ i : R.ι, (autFixedInG E t).subgroupOf I = R.hyp i ∧
      (kZero p E t).subgroupOf I = R.block i := by
  classical
  have hp : p.Prime := h.prime
  have hDE : autFixedInG E t ≤ E := Subgroup.map_subtype_le _
  have hDI : autFixedInG E t ≤ I := hDE.trans hEI
  have hperf : ⁅kZero p E t, kZero p E t⁆ = kZero p E t := Subgroup.isPerfect_iff.1 hq.1
  have hKhperf := commutator_subgroupOf_eq' hKI hperf
  have hDhT : (autFixedInG E t).subgroupOf I ≤ E.subgroupOf I := fun x hx =>
    Subgroup.mem_subgroupOf.2 (hDE (Subgroup.mem_subgroupOf.1 hx))
  have hidx : ((autFixedInG E t).subgroupOf I).relIndex (E.subgroupOf I) = p := by
    rw [Subgroup.relIndex_subgroupOf hEI]
    exact relIndex_fixed h ht
  have hKC : (kZero p E t).subgroupOf I ≤
      Subgroup.centralizer (((autFixedInG E t).subgroupOf I : Subgroup ↥I) : Set ↥I) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.1 (S15K.kZero_le_centralizer p E t
      (Subgroup.mem_subgroupOf.1 hy)) (d : G) (Subgroup.mem_subgroupOf.1 hd)
  have hle : (kZero p E t).subgroupOf I ≤
      ⨆ i : {i : R.ι // (autFixedInG E t).subgroupOf I ≤ R.hyp i}, R.block i.1 :=
    calc (kZero p E t).subgroupOf I = ⁅(kZero p E t).subgroupOf I, (kZero p E t).subgroupOf I⁆ :=
          hKhperf.symm
      _ ≤ ⁅Subgroup.centralizer (((autFixedInG E t).subgroupOf I : Subgroup ↥I) : Set ↥I),
          Subgroup.centralizer (((autFixedInG E t).subgroupOf I : Subgroup ↥I) : Set ↥I)⁆ :=
        Subgroup.commutator_mono hKC hKC
      _ ≤ _ := R.derived_le _ hDhT (Or.inl hidx)
  have hKne : (kZero p E t).subgroupOf I ≠ ⊥ := by
    intro hbot
    have hbot' : kZero p E t = ⊥ := by
      have := congrArg (Subgroup.map I.subtype) hbot
      rwa [Subgroup.map_subgroupOf_eq_of_le hKI, Subgroup.map_bot] at this
    have : Subsingleton ↥(kZero p E t) := by rw [hbot']; infer_instance
    obtain ⟨a, b, hab⟩ := hq.2.2
    exact hab (Subsingleton.elim _ _)
  have key : ∀ j : R.ι, (autFixedInG E t).subgroupOf I ≤ R.hyp j →
      (autFixedInG E t).subgroupOf I = R.hyp j := by
    intro j hj
    have h1 := Subgroup.relIndex_mul_relIndex ((autFixedInG E t).subgroupOf I) (R.hyp j)
      (E.subgroupOf I) hj (R.hyp_le j)
    rw [hidx] at h1
    rcases (Nat.dvd_prime hp).1 (Dvd.intro _ h1) with h2 | h2
    · exact le_antisymm hj (Subgroup.relIndex_eq_one.1 h2)
    · have h3 : (R.hyp j).relIndex (E.subgroupOf I) = 1 := by
        rw [h2] at h1
        exact Nat.eq_of_mul_eq_mul_left hp.pos (by simpa using h1)
      exact absurd (le_antisymm (R.hyp_le j) (Subgroup.relIndex_eq_one.1 h3)) (R.hyp_ne j)
  have hex : ∃ i : R.ι, (autFixedInG E t).subgroupOf I ≤ R.hyp i := by
    by_contra hcon
    push Not at hcon
    have : IsEmpty {i : R.ι // (autFixedInG E t).subgroupOf I ≤ R.hyp i} :=
      ⟨fun i => hcon i.1 i.2⟩
    rw [iSup_of_empty] at hle
    exact hKne (le_bot_iff.1 hle)
  obtain ⟨i, hi⟩ := hex
  have hDeq : (autFixedInG E t).subgroupOf I = R.hyp i := key i hi
  have hsub : ∀ j : {j : R.ι // (autFixedInG E t).subgroupOf I ≤ R.hyp j}, j.1 = i := fun j =>
    R.hyp_inj ((key j.1 j.2).symm.trans hDeq)
  have hKb : (kZero p E t).subgroupOf I ≤ R.block i :=
    hle.trans (iSup_le fun j => by rw [hsub j])
  have hnorm : (((kZero p E t).subgroupOf I).subgroupOf (R.block i)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hgC : (g : ↥I) ∈ Subgroup.centralizer
        (((autFixedInG E t).subgroupOf I : Subgroup ↥I) : Set ↥I) := hDeq ▸ R.block_le i g.2
    have hgC' : ((g : ↥I) : G) ∈ Subgroup.centralizer (autFixedInG E t : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have := Subgroup.mem_centralizer_iff.1 hgC ⟨d, hDI hd⟩ (Subgroup.mem_subgroupOf.2 hd)
      exact congrArg Subtype.val this
    have hnormal := S15K.kZero_normalized p E t hgC'
    rw [Subgroup.mem_normalizer_iff] at hnormal
    have hn' : (((n : ↥(R.block i)) : ↥I) : G) ∈ kZero p E t := Subgroup.mem_subgroupOf.1 hn
    exact (hnormal _).1 hn'
  have hKeq : (kZero p E t).subgroupOf I = R.block i := by
    rcases R.block_simple i _ hKb hnorm with h0 | h0
    · exact absurd h0 hKne
    · exact h0
  exact ⟨i, hDeq, hKeq⟩

@[expose] def rootsOfKt (I : Subgroup G) (R : RootData p (E.subgroupOf I)) : Set R.ι :=
  {i | ∃ t ∈ reflectionSet p E, (autFixedInG E t).subgroupOf I = R.hyp i ∧
    (kZero p E t).subgroupOf I = R.block i}

omit [Finite G] in
theorem kt_facts_all {I : Subgroup G} (hI : I = lieGenerated p E)
    (hAt : ∀ t ∈ reflectionSet p E, ∃ g : ℕ, KFAt p E g t) :
    ∀ t ∈ reflectionSet p E, CFSG.IsQuasisimple ↥(kZero p E t) ∧
      IsKt p E t (kZero p E t) ∧ kZero p E t ≤ I := by
  intro t ht
  obtain ⟨hq, hKt, hKI⟩ := kt_facts ht (hAt t ht).choose_spec
  exact ⟨hq, hKt, hI ▸ hKI⟩

theorem exists_root_of_kt {I : Subgroup G} (h : Sec12Hyp G p A c L E) (hEI : E ≤ I)
    (hI : I = lieGenerated p E) (hAt : ∀ t ∈ reflectionSet p E, ∃ g : ℕ, KFAt p E g t)
    (R : RootData p (E.subgroupOf I)) {t : MulAut E} (ht : t ∈ reflectionSet p E) :
    ∃ i : R.ι, (autFixedInG E t).subgroupOf I = R.hyp i ∧ (kZero p E t).subgroupOf I = R.block i :=
  kt_block h hEI R ht (kt_facts_all hI hAt t ht).1 (kt_facts_all hI hAt t ht).2.2

theorem rootsOfKt_wstable {I : Subgroup G} (h : Sec12Hyp G p A c L E) (hEI : E ≤ I)
    (hI : I = lieGenerated p E) (hAt : ∀ t ∈ reflectionSet p E, ∃ g : ℕ, KFAt p E g t)
    (R : RootData p (E.subgroupOf I)) : R.WStable (rootsOfKt I R) := by
  classical
  have hp : p.Prime := h.prime
  intro w hw i hi
  obtain ⟨t, ht, hDt, hKt⟩ := hi
  have hwN : (w : G) ∈ Subgroup.normalizer (E : Set G) := by
    have hwn := R.W_le hw
    rw [Subgroup.mem_normalizer_iff] at hwn ⊢
    intro x
    constructor
    · intro hx
      have hxI : x ∈ I := hEI hx
      have := (hwn ⟨x, hxI⟩).1 (Subgroup.mem_subgroupOf.2 hx)
      exact Subgroup.mem_subgroupOf.1 this
    · intro hx
      have hxI : (w : G) * x * (w : G)⁻¹ ∈ I := hEI hx
      have hxI' : x ∈ I := by
        have := I.mul_mem (I.mul_mem (I.inv_mem w.2) hxI) w.2
        simpa [mul_assoc] using this
      have := (hwn ⟨x, hxI'⟩).2 (Subgroup.mem_subgroupOf.2 (by simpa using hx))
      exact Subgroup.mem_subgroupOf.1 this
  have ht'D : conjAut E (w : G) hwN * t * (conjAut E (w : G) hwN)⁻¹ ∈ reflectionSet p E :=
    conj_mem_reflectionSet hp ht hwN
  obtain ⟨i', hDi', hKi'⟩ := exists_root_of_kt h hEI hI hAt R ht'D
  obtain ⟨j, hjb, hjh⟩ := R.weyl w hw i
  have hD' : (autFixedInG E (conjAut E (w : G) hwN * t * (conjAut E (w : G) hwN)⁻¹)).subgroupOf I =
      (R.hyp i).map (MulAut.conj w).toMonoidHom := by
    rw [Equivariance.autFixedInG_conj t hwN, conjBy_subgroupOf, hDt]
  have hK' : (kZero p E (conjAut E (w : G) hwN * t * (conjAut E (w : G) hwN)⁻¹)).subgroupOf I =
      (R.block i).map (MulAut.conj w).toMonoidHom := by
    rw [kZero_conj p t hwN, conjBy_subgroupOf, hKt]
  have hji : j = i' := R.hyp_inj (hjh.symm.trans (hD'.symm.trans hDi'))
  refine ⟨i', ⟨_, ht'D, hDi', hKi'⟩, ?_, ?_⟩
  · rw [← hKi', hK']
  · rw [← hDi', hD']

theorem rootsOfKt_top {I : Subgroup G} (h : Sec12Hyp G p A c L E) (hEI : E ≤ I)
    (hI : I = lieGenerated p E) (hAt : ∀ t ∈ reflectionSet p E, ∃ g : ℕ, KFAt p E g t)
    (R : RootData p (E.subgroupOf I)) : (⨆ i ∈ rootsOfKt I R, R.block i) = ⊤ := by
  classical
  have hfacts := kt_facts_all hI hAt
  have hblock := fun t ht => exists_root_of_kt h hEI hI hAt R (t := t) ht
  have hI_eq : I = ⨆ t : {t : MulAut E // t ∈ reflectionSet p E}, kZero p E t.1 := by
    apply le_antisymm
    · rw [hI]
      refine sSup_le ?_
      rintro K ⟨t, ht, hKt⟩
      have hKeq : K = kZero p E t := hKt.2 (hAt t ht).choose_spec.1
      rw [hKeq]
      exact le_iSup (fun t : {t : MulAut E // t ∈ reflectionSet p E} => kZero p E t.1) ⟨t, ht⟩
    · exact iSup_le fun t => (hfacts t.1 t.2).2.2
  have hKI : ∀ t : {t : MulAut E // t ∈ reflectionSet p E}, kZero p E t.1 ≤ I := fun t =>
    (hfacts t.1 t.2).2.2
  have htop : (⊤ : Subgroup ↥I) = ⨆ t : {t : MulAut E // t ∈ reflectionSet p E},
      (kZero p E t.1).subgroupOf I := by
    rw [← subgroupOf_iSup _ hKI, ← hI_eq]
    exact (Subgroup.subgroupOf_self I).symm
  rw [eq_top_iff, htop]
  refine iSup_le fun t => ?_
  obtain ⟨i', hDi', hKi'⟩ := hblock t.1 t.2
  rw [hKi']
  exact le_iSup₂_of_le i' ⟨t.1, t.2, hDi', hKi'⟩ le_rfl

theorem rootsOfKt_eq_univ_of_blocks {I : Subgroup G} (h : Sec12Hyp G p A c L E) (hEI : E ≤ I)
    (hI : I = lieGenerated p E) (hAt : ∀ t ∈ reflectionSet p E, ∃ g : ℕ, KFAt p E g t)
    (R : RootData p (E.subgroupOf I)) (hgen : R.GenBlocks) : rootsOfKt I R = Set.univ :=
  hgen _ (rootsOfKt_wstable h hEI hI hAt R) (rootsOfKt_top h hEI hI hAt R)

theorem involution_eq_inv {H : Type*} [Group H] {R : Subgroup H} {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card ↥R = p) (t : MulAut H) (htt : t * t = 1) (hinv : ∀ r ∈ R, t r ∈ R)
    (hfix : ∀ r ∈ R, t r = r → r = 1) : ∀ r ∈ R, t r = r⁻¹ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hcyc : IsCyclic ↥R := isCyclic_of_prime_card hcard
  obtain ⟨g, hg⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top R).1 hcyc
  have hgR : g ∈ R := hg ▸ Subgroup.mem_zpowers g
  have hRg : ∀ r ∈ R, ∃ k : ℤ, g ^ k = r := by
    intro r hr
    have : r ∈ Subgroup.zpowers g := hg ▸ hr
    exact Subgroup.mem_zpowers_iff.1 this
  have hord : orderOf g = p := by
    rw [← Nat.card_zpowers, hg]
    exact hcard
  obtain ⟨m, hm⟩ := hRg (t g) (hinv g hgR)
  have htt' : ∀ x, t (t x) = x := fun x => by
    have := congrArg (fun f : MulAut H => f x) htt
    simpa using this
  have hg2 : g ^ (m * m) = g :=
    calc g ^ (m * m) = (g ^ m) ^ m := zpow_mul _ _ _
      _ = (t g) ^ m := by rw [hm]
      _ = t (g ^ m) := (map_zpow t g m).symm
      _ = t (t g) := by rw [hm]
      _ = g := htt' g
  have hgm1 : ∀ n : ℤ, (p : ℤ) ∣ n → g ^ n = 1 := fun n hn =>
    orderOf_dvd_iff_zpow_eq_one.1 (by rw [hord]; exact hn)
  have hdvd : (p : ℤ) ∣ (m - 1) * (m + 1) := by
    have h3 : g ^ (m * m - 1) = 1 := by
      rw [zpow_sub, hg2, zpow_one, mul_inv_cancel]
    have := orderOf_dvd_iff_zpow_eq_one.2 h3
    rw [hord] at this
    have hfac : m * m - 1 = (m - 1) * (m + 1) := by ring
    rwa [hfac] at this
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  rcases hpz.dvd_or_dvd hdvd with h1 | h1
  · exfalso
    have h2 : g ^ (m - 1) = 1 := hgm1 _ h1
    have h3 : g ^ m = g := by
      have : g ^ m = g ^ (m - 1) * g := by
        rw [← zpow_add_one]
        congr 1
        ring
      rw [this, h2, one_mul]
    have h4 : t g = g := by rw [← hm, h3]
    have h5 := hfix g hgR h4
    have h6 : orderOf g = 1 := by rw [h5]; exact orderOf_one
    rw [hord] at h6
    exact hp.ne_one h6
  · intro r hr
    obtain ⟨k, rfl⟩ := hRg r hr
    have h2 : g ^ (m + 1) = 1 := hgm1 _ h1
    have h3 : g ^ m = g⁻¹ := by
      have : g ^ (m + 1) = g ^ m * g := zpow_add_one _ _
      rw [this] at h2
      exact eq_inv_of_mul_eq_one_left h2
    have h4 : t g = g⁻¹ := by rw [← hm, h3]
    rw [map_zpow, h4, inv_zpow]

omit [Finite G] in
theorem mem_autFixedInG_iff {t : MulAut E} {e : G} :
    e ∈ autFixedInG E t ↔ ∃ he : e ∈ E, t ⟨e, he⟩ = ⟨e, he⟩ := by
  unfold autFixedInG autFixed
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨he, h⟩
    exact ⟨⟨e, he⟩, h, rfl⟩

theorem theta_eq_refl {I : Subgroup G} (h : Sec12Hyp G p A c L E) (hEI : E ≤ I)
    (R : RootData p (E.subgroupOf I)) {N : ℕ} (rd : R.ReflData N) {t : MulAut E}
    (ht : t ∈ reflectionSet p E) {i : R.ι} (hD : (autFixedInG E t).subgroupOf I = R.hyp i)
    (hK : (kZero p E t).subgroupOf I = R.block i) :
    MulAut.congr (Subgroup.subgroupOfEquivOfLe hEI).symm t = rd.refl i := by
  classical
  have hp : p.Prime := h.prime
  obtain ⟨⟨w, hw⟩, hwt⟩ := Sec1322.reflectionSet_subset_torusWeyl t ht
  have hwt' : conjAut E w hw = t := hwt
  have hKconj : conjBy w (kZero p E t) = kZero p E t := by
    have := kZero_conj p t hw
    rw [hwt', mul_inv_cancel_right] at this
    exact this.symm
  have htt : t * t = 1 := by
    have h2 : t ^ 2 = 1 := ht.1.1 ▸ pow_orderOf_eq_one t
    rwa [pow_two] at h2
  let Θ : MulAut ↥E ≃* MulAut ↥(E.subgroupOf I) :=
    MulAut.congr (Subgroup.subgroupOfEquivOfLe hEI).symm
  have hΘcoe : ∀ x : ↥(E.subgroupOf I), (((Θ t x : ↥(E.subgroupOf I)) : ↥I) : G) = w * (x : G) * w⁻¹ := by
    intro x
    have := Equivariance.coe_conjAut hw ⟨(x : G), Subgroup.mem_subgroupOf.1 x.2⟩
    rw [hwt'] at this
    exact this
  have hΘfix : ∀ x : ↥(E.subgroupOf I), (x : ↥I) ∈ R.hyp i → Θ t x = x := by
    intro x hx
    rw [← hD] at hx
    obtain ⟨he, hfix⟩ := mem_autFixedInG_iff.1 (Subgroup.mem_subgroupOf.1 hx)
    apply Subtype.ext
    apply Subtype.ext
    rw [hΘcoe]
    have := congrArg (fun y : ↥E => (y : G)) hfix
    simp only [Equivariance.coe_conjAut hw, hwt'.symm] at this
    exact this
  have hΘ1 : (Θ t) * (Θ t) = 1 := by rw [← map_mul, htt, map_one]
  have hΘinv : ∀ x : ↥(E.subgroupOf I), (x : ↥I) ∈ R.block i → Θ t x = x⁻¹ := by
    let R₁ : Subgroup ↥(E.subgroupOf I) := (R.block i).subgroupOf (E.subgroupOf I)
    have hcard : Nat.card ↥R₁ = p := by
      have h1 := rd.Tblock_card i
      have h2 : R₁.map (E.subgroupOf I).subtype = (E.subgroupOf I) ⊓ R.block i :=
        (Subgroup.subgroupOf_map_subtype (R.block i) (E.subgroupOf I)).trans (inf_comm _ _)
      rw [← h1, ← h2]
      exact (Subgroup.card_map_of_injective (E.subgroupOf I).subtype_injective).symm
    have hinv : ∀ r ∈ R₁, Θ t r ∈ R₁ := by
      intro r hr
      have hr1 : (r : ↥I) ∈ R.block i := hr
      rw [← hK] at hr1
      have hr' : (((r : ↥I) : G)) ∈ kZero p E t := hr1
      refine Subgroup.mem_subgroupOf.2 ?_
      rw [← hK]
      refine Subgroup.mem_subgroupOf.2 ?_
      rw [hΘcoe]
      have : (w * ((r : ↥I) : G) * w⁻¹) ∈ conjBy w (kZero p E t) := by
        rw [Equivariance.mem_conjBy]
        simpa [mul_assoc] using hr'
      rwa [hKconj] at this
    have hfix : ∀ r ∈ R₁, Θ t r = r → r = 1 := by
      intro r hr hfixr
      have hrb : (r : ↥I) ∈ R.block i := hr
      have hre : ((r : ↥I) : G) ∈ E := Subgroup.mem_subgroupOf.1 r.2
      have hco := congrArg (fun y : ↥(E.subgroupOf I) => (((y : ↥(E.subgroupOf I)) : ↥I) : G)) hfixr
      simp only [hΘcoe] at hco
      have hrh : (r : ↥I) ∈ R.hyp i := by
        rw [← hD]
        refine Subgroup.mem_subgroupOf.2 (mem_autFixedInG_iff.2 ⟨hre, ?_⟩)
        apply Subtype.ext
        have := Equivariance.coe_conjAut hw ⟨((r : ↥I) : G), hre⟩
        rw [hwt'] at this
        rw [this]
        exact hco
      have hmem : (r : ↥I) ∈ R.hyp i ⊓ ((E.subgroupOf I) ⊓ R.block i) := ⟨hrh, r.2, hrb⟩
      rw [rd.hyp_inf i, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    exact involution_eq_inv hp hcard (Θ t) hΘ1 hinv hfix
  have hΘeq : ∀ x : ↥(E.subgroupOf I), Θ t x = rd.refl i x := by
    let f₁ : ↥(E.subgroupOf I) →* ↥(E.subgroupOf I) := (Θ t).toMonoidHom
    let f₂ : ↥(E.subgroupOf I) →* ↥(E.subgroupOf I) := (rd.refl i).toMonoidHom
    have hA : (R.hyp i).subgroupOf (E.subgroupOf I) ≤ MonoidHom.eqLocus f₁ f₂ := fun x hx => by
      have hx' : (x : ↥I) ∈ R.hyp i := hx
      show Θ t x = rd.refl i x
      rw [hΘfix x hx', rd.refl_fix i x hx']
    have hB : ((E.subgroupOf I) ⊓ R.block i).subgroupOf (E.subgroupOf I) ≤
        MonoidHom.eqLocus f₁ f₂ := fun x hx => by
      have hx' : (x : ↥I) ∈ R.block i := (Subgroup.mem_inf.1 hx).2
      show Θ t x = rd.refl i x
      rw [hΘinv x hx', rd.refl_inv i x hx']
    have hsup : (R.hyp i).subgroupOf (E.subgroupOf I) ⊔
        ((E.subgroupOf I) ⊓ R.block i).subgroupOf (E.subgroupOf I) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup (R.hyp_le i) inf_le_left, rd.hyp_sup i]
      exact Subgroup.subgroupOf_self _
    intro x
    have hx : x ∈ (⊤ : Subgroup ↥(E.subgroupOf I)) := Subgroup.mem_top x
    rw [← hsup] at hx
    exact (sup_le hA hB) hx
  exact MulEquiv.ext hΘeq

theorem rootsOfKt_eq_univ_of_refl {I : Subgroup G} (h : Sec12Hyp G p A c L E) (hEI : E ≤ I)
    (hI : I = lieGenerated p E) (hAt : ∀ t ∈ reflectionSet p E, ∃ g : ℕ, KFAt p E g t)
    (R : RootData p (E.subgroupOf I)) {N : ℕ} (rd : R.ReflData N)
    (hN : Nat.card ↥(reflectionGroup p E) = N) : rootsOfKt I R = Set.univ := by
  classical
  refine rd.gen _ (rootsOfKt_wstable h hEI hI hAt R) ?_
  let Θ : MulAut ↥E ≃* MulAut ↥(E.subgroupOf I) :=
    MulAut.congr (Subgroup.subgroupOfEquivOfLe hEI).symm
  have himg : Θ.toMonoidHom '' reflectionSet p E = rd.refl '' rootsOfKt I R := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨i, hDi, hKi⟩ := exists_root_of_kt h hEI hI hAt R ht
      exact ⟨i, ⟨t, ht, hDi, hKi⟩, (theta_eq_refl h hEI R rd ht hDi hKi).symm⟩
    · rintro ⟨i, ⟨t, ht, hDi, hKi⟩, rfl⟩
      exact ⟨t, ht, theta_eq_refl h hEI R rd ht hDi hKi⟩
  have hcl : (reflectionGroup p E).map Θ.toMonoidHom = Subgroup.closure (rd.refl '' rootsOfKt I R) := by
    unfold reflectionGroup
    rw [MonoidHom.map_closure, himg]
  have hle : Subgroup.closure (rd.refl '' rootsOfKt I R) ≤ Subgroup.closure (Set.range rd.refl) :=
    Subgroup.closure_mono (Set.image_subset_range _ _)
  have hcard1 : Nat.card ↥(Subgroup.closure (rd.refl '' rootsOfKt I R)) = N := by
    rw [← hcl, Subgroup.card_map_of_injective Θ.injective]
    exact hN
  have hfin : Finite ↥(Subgroup.closure (Set.range rd.refl)) := inferInstance
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard1]; exact rd.weyl_card)

theorem kfCompGenRow_of_rootModel {r : ℕ} (hr1 : 1 ≤ r) (hr4 : r ≤ 4) (hEI : Sec1511.KFEI)
    (hAt : KFAtRow r) (hRM : RootModelRow r) : KFCompGenRow r := by
  classical
  intro G _ _ p A c L E h15 hF hF13 hout e he he1 Q hQle hQc
  have h := h15.h12
  have hEIle : E ≤ lieGenerated p E :=
    hEI G p A c L E h15 hF (hout.outcome152 hr1 hr4) (hout.not_five hr1 hr4)
  obtain ⟨R, hR⟩ := hRM G p A c L E h15 hF hF13 hout hEIle
  have hAt' : ∀ t ∈ reflectionSet p E, ∃ g : ℕ, KFAt p E g t := hAt G p A c L E h15 hF hF13 hout
  have huniv : rootsOfKt (lieGenerated p E) R = Set.univ := by
    rcases hR with hgen | ⟨⟨rd⟩⟩
    · exact rootsOfKt_eq_univ_of_blocks h hEIle rfl hAt' R hgen
    · exact rootsOfKt_eq_univ_of_refl h hEIle rfl hAt' R rd (hout.card_reflectionGroup hr1 hr4)
  have hQI : Q ≤ lieGenerated p E := hQle.trans inf_le_left
  have hQperf : ⁅Q, Q⁆ = Q :=
    commutator_eq_of_subgroupOf' hQle (Subgroup.isPerfect_iff.1 hQc.1.1)
  have hQhperf := commutator_subgroupOf_eq' hQI hQperf
  let eh : ↥(lieGenerated p E) := ⟨e, hEIle he⟩
  have hST : Subgroup.zpowers eh ≤ E.subgroupOf (lieGenerated p E) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_subgroupOf.2 he
  have hehne : eh ≠ 1 := fun h => he1 (congrArg Subtype.val h)
  have hQC : Q.subgroupOf (lieGenerated p E) ≤
      Subgroup.centralizer ((Subgroup.zpowers eh : Subgroup ↥(lieGenerated p E)) : Set _) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
    have hyc : Commute (y : G) e := by
      have := (Subgroup.mem_inf.1 (hQle (Subgroup.mem_subgroupOf.1 hy))).2
      exact (Subgroup.mem_centralizer_singleton_iff.1 this)
    have hc : Commute y eh := Subtype.ext hyc
    exact (hc.symm.zpow_left k).eq
  have hle : Q.subgroupOf (lieGenerated p E) ≤
      ⨆ i : {i : R.ι // Subgroup.zpowers eh ≤ R.hyp i}, R.block i.1 :=
    calc Q.subgroupOf (lieGenerated p E) =
          ⁅Q.subgroupOf (lieGenerated p E), Q.subgroupOf (lieGenerated p E)⁆ := hQhperf.symm
      _ ≤ ⁅Subgroup.centralizer ((Subgroup.zpowers eh : Subgroup ↥(lieGenerated p E)) : Set _),
          Subgroup.centralizer ((Subgroup.zpowers eh : Subgroup ↥(lieGenerated p E)) : Set _)⁆ :=
        Subgroup.commutator_mono hQC hQC
      _ ≤ _ := R.derived_le _ hST (Or.inr ⟨eh, hST (Subgroup.mem_zpowers eh), hehne, rfl⟩)
  have hmap : Q ≤ ⨆ i : {i : R.ι // Subgroup.zpowers eh ≤ R.hyp i},
      (R.block i.1).map (lieGenerated p E).subtype := by
    have h1 := Subgroup.map_mono (f := (lieGenerated p E).subtype) hle
    rw [Subgroup.map_subgroupOf_eq_of_le hQI, Subgroup.map_iSup] at h1
    exact h1
  refine hmap.trans (iSup_le fun i => ?_)
  obtain ⟨t, ht, hDt, hKt⟩ : i.1 ∈ rootsOfKt (lieGenerated p E) R := huniv ▸ Set.mem_univ _
  obtain ⟨g', hKF'⟩ := hAt' t ht
  obtain ⟨hq, hKtt, hKI⟩ := kt_facts ht hKF'
  have het : e ∈ autFixedInG E t := by
    have h1 : eh ∈ R.hyp i.1 := i.2 (Subgroup.mem_zpowers eh)
    rw [← hDt] at h1
    exact Subgroup.mem_subgroupOf.1 h1
  have hmapK : (R.block i.1).map (lieGenerated p E).subtype = kZero p E t := by
    rw [← hKt, Subgroup.map_subgroupOf_eq_of_le hKI]
  rw [hmapK]
  intro x hx
  exact Subgroup.subset_closure ⟨t, ht, het, kZero p E t, hKtt, hx⟩

end Glue

end CFSG.RankThree.PartOne.KFCL

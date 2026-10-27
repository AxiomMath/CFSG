module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotNeighbourParamLift
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelL39Out

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.EvenSmallLie.Child3.SelL39 (projectiveSLCongr slCongr)

section Transport

variable {m : ℕ} {K' K : Type*} [Field K'] [Field K]

theorem projectiveSLCongr_proj (r : K' ≃+* K) (x : SpecialLinearGroup (Fin m) K') :
    projectiveSLCongr r (LinearFlag.proj m K' x) =
      LinearFlag.proj m K (SpecialLinearGroup.map r.toRingHom x) :=
  QuotientGroup.congr_mk' _ _ _ _ x

theorem projectiveSLCongr_symm_proj (r : K' ≃+* K) (x : SpecialLinearGroup (Fin m) K) :
    (projectiveSLCongr r).symm (LinearFlag.proj m K x) =
      LinearFlag.proj m K' (SpecialLinearGroup.map r.symm.toRingHom x) := by
  rw [MulEquiv.symm_apply_eq, projectiveSLCongr_proj]
  congr 1
  ext i j
  simp

theorem congr_projectiveSLCongr_fieldAut_mul_dualAut (r : K' ≃+* K) (φ : K' ≃+* K') :
    MulAut.congr (projectiveSLCongr (n := m) r) (LinearFlag.fieldAut m K' φ * LinearFlag.dualAut m K') =
      LinearFlag.fieldAut m K (r.symm.trans (φ.trans r)) * LinearFlag.dualAut m K := by
  ext y
  obtain ⟨g, rfl⟩ := LinearFlag.proj_surjective m K y
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, projectiveSLCongr_symm_proj,
    MulAut.mul_apply, LinearFlag.dualAut_proj,
    LinearFlag.fieldAut_proj, projectiveSLCongr_proj, MulAut.mul_apply, LinearFlag.dualAut_proj,
    LinearFlag.fieldAut_proj]
  congr 1
  have hinv : (SpecialLinearGroup.map r.symm.toRingHom g)⁻¹ =
      SpecialLinearGroup.map r.symm.toRingHom g⁻¹ := (map_inv _ g).symm
  rw [hinv]
  ext i j
  simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    SpecialLinearGroup.coe_transpose, transpose_apply, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe]
  rfl

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {K' : Type} [Field K']

theorem congr_projectiveSLCongr_eq_graphFieldAut (r : K' ≃+* K) {φ : K' ≃+* K'}
    (hφ : ∀ x, φ x = x ^ 2 ^ f) :
    MulAut.congr (projectiveSLCongr (n := m) r) (LinearFlag.fieldAut m K' φ * LinearFlag.dualAut m K') =
      graphFieldAut h m := by
  rw [congr_projectiveSLCongr_fieldAut_mul_dualAut, graphFieldAut]
  congr 2
  ext x
  change r (φ (r.symm x)) = h.bar x
  rw [hφ, map_pow, RingEquiv.apply_symm_apply, h.bar_apply]

end Transport

section Normalize

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {m : ℕ}

theorem exists_mulEquiv_toPSL_eq (hm : 3 ≤ m) (hmq : ¬(m = 3 ∧ 2 ^ f = 2)) {M : Type*}
    [Group M] (ψ₀ : M ≃* LinearFlag.projectiveSL m K) {τ : MulAut M}
    (hτ : MulAut.congr ψ₀ τ = graphFieldAut h m) (ε : unitaryPSU h m →* M)
    (hε : Function.Injective ε) (hετ : ε.range ≤ fixedSubgroup τ) :
    ∃ ψ : M ≃* LinearFlag.projectiveSL m K, (∀ x, ψ (ε x) = toPSL h m x) ∧
      ∀ y, ψ (τ y) = graphFieldAut h m (ψ y) := by
  have hψ₀τ : ∀ y, ψ₀ (τ y) = graphFieldAut h m (ψ₀ y) := fun y => by
    rw [← hτ, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
  have hperf : Group.IsPerfect (unitarySU 2 f K m) :=
    (isQuasisimple_unitarySU h hm (fun h' => hmq ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩)).1
  have hinj₁ : Function.Injective (ψ₀.toMonoidHom.comp ε) := ψ₀.injective.comp hε
  have hinj₂ : Function.Injective (toPSL h m) := toPSL_injective h
  have hrange₁ : (ψ₀.toMonoidHom.comp ε).range =
      ((ψ₀.toMonoidHom.comp ε).comp (unitaryProj h m)).range := by
    symm
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (unitaryProj_surjective h m),
      ← MonoidHom.range_eq_map]
  have hle : (ψ₀.toMonoidHom.comp ε).range ≤ (toPSL h m).range := by
    refine le_range_toPSL_of_le_fixedSubgroup h ?_ ?_
    · rw [hrange₁, MonoidHom.range_eq_map, ← map_commutator, ← _root_.commutator_def,
        Group.IsPerfect.commutator_eq_top]
    · rintro _ ⟨x, rfl⟩
      change graphFieldAut h m (ψ₀ (ε x)) = ψ₀ (ε x)
      rw [← hψ₀τ]
      exact congrArg ψ₀ (hετ ⟨x, rfl⟩)
  have hrange : (ψ₀.toMonoidHom.comp ε).range = (toPSL h m).range := by
    have := h.finite
    have : Finite (unitaryPSU h m) := inferInstance
    refine eq_of_le_of_card_ge hle ?_
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj₂).toEquiv,
      ← Nat.card_congr (MonoidHom.ofInjective hinj₁).toEquiv]
  set δ : MulAut (unitaryPSU h m) := ((MonoidHom.ofInjective hinj₁).trans
    (MulEquiv.subgroupCongr hrange)).trans (MonoidHom.ofInjective hinj₂).symm with hδdef
  have hδ : ∀ x, toPSL h m (δ x) = ψ₀ (ε x) := by
    intro x
    have h1 := (MonoidHom.ofInjective hinj₂).apply_symm_apply
      (MulEquiv.subgroupCongr hrange (MonoidHom.ofInjective hinj₁ x))
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  obtain ⟨δ', hδ', hcomm⟩ := exists_mulAut_toPSL_comm h hm hmq δ
  refine ⟨ψ₀.trans δ'⁻¹, fun x => ?_, fun y => ?_⟩
  · rw [MulEquiv.trans_apply, ← hδ, ← hδ']
    exact MulAut.inv_apply_self _ _ _
  · show δ'⁻¹ (ψ₀ (τ y)) = graphFieldAut h m (δ'⁻¹ (ψ₀ y))
    rw [hψ₀τ]
    exact congrArg (fun φ : MulAut (LinearFlag.projectiveSL m K) => φ (ψ₀ y)) hcomm.inv_left.eq

end Normalize

section Embed

variable {G : Type*} [Group G] {L : Subgroup G} {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {n : ℕ} (e : L ≃* unitaryPSU h n) {a b : Fin n} (hab : a ≠ b)
  {m : ℕ} (eN : ({a, b}ᶜ : Finset (Fin n)) ≃ Fin m)

@[expose] noncomputable def neighbourBlockHomU :
    unitarySU 2 f K m →* centralizer (modelToG e (unitaryRootTorus h hab) : Set G) :=
  MonoidHom.codRestrict (L.subtype.comp (e.symm.toMonoidHom.comp ((unitaryProj h n).comp
      (unitaryBlockSLHom h eN)))) _
    fun x => modelToG_le_centralizer e (blockSU_compl_le_centralizer_unitaryRootTorus h hab)
      (symm_mem_modelToG e (unitaryProj_mem_blockSU h (unitaryBlockSLHom_mem h eN x)))

theorem coe_neighbourBlockHomU (x : unitarySU 2 f K m) :
    ((neighbourBlockHomU e hab eN x : centralizer (modelToG e (unitaryRootTorus h hab) : Set G)) :
      G) = ((e.symm (unitaryProj h n (unitaryBlockSLHom h eN x)) : L) : G) :=
  rfl

theorem range_neighbourBlockHomU :
    (neighbourBlockHomU e hab eN).range =
      (modelToG e (blockSU h ({a, b}ᶜ : Finset (Fin n)))).subgroupOf
        (centralizer (modelToG e (unitaryRootTorus h hab) : Set G)) := by
  ext ⟨g, hg⟩
  rw [mem_subgroupOf, MonoidHom.mem_range]
  change (∃ x, neighbourBlockHomU e hab eN x = ⟨g, hg⟩) ↔ g ∈ modelToG e (blockSU h _)
  constructor
  · rintro ⟨x, hx⟩
    have hgx : ((e.symm (unitaryProj h n (unitaryBlockSLHom h eN x)) : L) : G) = g := by
      rw [← coe_neighbourBlockHomU e hab eN x, hx]
    rw [← hgx]
    exact symm_mem_modelToG e (unitaryProj_mem_blockSU h (unitaryBlockSLHom_mem h eN x))
  · intro hgD
    obtain ⟨y, hy, rfl⟩ := (mem_modelToG e).1 hgD
    obtain ⟨A, hA, rfl⟩ := (mem_blockSU h).1 hy
    obtain ⟨x, rfl⟩ := exists_unitaryBlockSLHom_eq h eN hA
    exact ⟨x, Subtype.ext rfl⟩

@[expose] noncomputable def neighbourBarHomU :
    unitarySU 2 f K m →* centralizer (modelToG e (unitaryRootTorus h hab) : Set G) ⧸
      oddCore (centralizer (modelToG e (unitaryRootTorus h hab) : Set G)) :=
  (QuotientGroup.mk' (oddCore (centralizer (modelToG e (unitaryRootTorus h hab) : Set G)))).comp
    (neighbourBlockHomU e hab eN)

theorem range_neighbourBarHomU :
    (neighbourBarHomU e hab eN).range =
      ((modelToG e (blockSU h ({a, b}ᶜ : Finset (Fin n)))).subgroupOf
        (centralizer (modelToG e (unitaryRootTorus h hab) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e (unitaryRootTorus h hab) : Set G)))) := by
  rw [neighbourBarHomU, MonoidHom.range_comp, range_neighbourBlockHomU]

theorem ker_neighbourBarHomU (hm : 4 ≤ m)
    (hne : ((modelToG e (blockSU h ({a, b}ᶜ : Finset (Fin n)))).subgroupOf
        (centralizer (modelToG e (unitaryRootTorus h hab) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e (unitaryRootTorus h hab) :
            Set G)))) ≠ ⊥)
    (hZ : center (((modelToG e (blockSU h ({a, b}ᶜ : Finset (Fin n)))).subgroupOf
        (centralizer (modelToG e (unitaryRootTorus h hab) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e (unitaryRootTorus h hab) :
            Set G))))) = ⊥) :
    (neighbourBarHomU e hab eN).ker = center (unitarySU 2 f K m) := by
  set φ := neighbourBarHomU e hab eN with hφ
  refine le_antisymm (LieType.CurtisTits.ker_le_center_of_isQuasisimple
    (isQuasisimple_unitarySU h (by omega) (fun h' => by
      have := congrArg Prod.fst h'
      simp only at this
      omega)) ?_) ?_
  · by_contra hc
    push Not at hc
    apply hne
    rw [← range_neighbourBarHomU, eq_bot_iff]
    rintro _ ⟨x, rfl⟩
    exact (mem_bot).mpr (hc x)
  · intro z hz
    have hZ' : center φ.range = ⊥ := by
      rw [hφ, range_neighbourBarHomU]
      exact hZ
    have hzc : (⟨φ z, z, rfl⟩ : φ.range) ∈ center φ.range := by
      rw [mem_center_iff]
      rintro ⟨_, x, rfl⟩
      apply Subtype.ext
      change φ x * φ z = φ z * φ x
      rw [← map_mul, ← map_mul, (mem_center_iff.mp hz x)]
    rw [hZ', mem_bot] at hzc
    exact congrArg Subtype.val hzc

theorem exists_unitaryPSU_embedding (hm : 4 ≤ m)
    (hne : ((modelToG e (blockSU h ({a, b}ᶜ : Finset (Fin n)))).subgroupOf
        (centralizer (modelToG e (unitaryRootTorus h hab) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e (unitaryRootTorus h hab) :
            Set G)))) ≠ ⊥)
    (hZ : center (((modelToG e (blockSU h ({a, b}ᶜ : Finset (Fin n)))).subgroupOf
        (centralizer (modelToG e (unitaryRootTorus h hab) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e (unitaryRootTorus h hab) :
            Set G))))) = ⊥)
    {Kc : Subgroup (centralizer (modelToG e (unitaryRootTorus h hab) : Set G) ⧸
      oddCore (centralizer (modelToG e (unitaryRootTorus h hab) : Set G)))}
    (hDK : ((modelToG e (blockSU h ({a, b}ᶜ : Finset (Fin n)))).subgroupOf
        (centralizer (modelToG e (unitaryRootTorus h hab) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e (unitaryRootTorus h hab) :
            Set G)))) ≤ Kc) :
    ∃ ε : unitaryPSU h m →* Kc, Function.Injective ε ∧
      ε.range = (((modelToG e (blockSU h ({a, b}ᶜ : Finset (Fin n)))).subgroupOf
        (centralizer (modelToG e (unitaryRootTorus h hab) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e (unitaryRootTorus h hab) :
            Set G))))).subgroupOf Kc ∧
      ∀ x, ((ε (unitaryProj h m x) : Kc) : centralizer (modelToG e (unitaryRootTorus h hab) :
        Set G) ⧸ oddCore (centralizer (modelToG e (unitaryRootTorus h hab) : Set G))) =
          neighbourBarHomU e hab eN x := by
  have hker := ker_neighbourBarHomU e hab eN hm hne hZ
  have hsc : unitaryScalars h m ≤ (neighbourBarHomU e hab eN).ker := by
    rw [hker, center_unitarySU_eq_unitaryScalars h m]
  set ε₀ := QuotientGroup.lift (unitaryScalars h m) (neighbourBarHomU e hab eN) hsc with hε₀
  have hε₀app : ∀ x, ε₀ (unitaryProj h m x) = neighbourBarHomU e hab eN x := fun x =>
    QuotientGroup.lift_mk' _ hsc x
  have hmem : ∀ y, ε₀ y ∈ Kc := by
    intro y
    obtain ⟨x, rfl⟩ := unitaryProj_surjective h m y
    rw [hε₀app]
    exact hDK (by rw [← range_neighbourBarHomU]; exact ⟨x, rfl⟩)
  refine ⟨ε₀.codRestrict Kc hmem, ?_, ?_, fun x => hε₀app x⟩
  · rw [injective_iff_map_eq_one]
    intro y hy
    obtain ⟨x, rfl⟩ := unitaryProj_surjective h m y
    have h1 : neighbourBarHomU e hab eN x = 1 := by
      rw [← hε₀app]
      exact congrArg Subtype.val hy
    have h2 : x ∈ (neighbourBarHomU e hab eN).ker := h1
    rw [hker, center_unitarySU_eq_unitaryScalars h m] at h2
    rw [← MonoidHom.mem_ker, ker_unitaryProj]
    exact h2
  · ext ⟨k, hk⟩
    rw [mem_subgroupOf, MonoidHom.mem_range, ← range_neighbourBarHomU]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := unitaryProj_surjective h m y
      have h1 : neighbourBarHomU e hab eN x = k := by
        rw [← hε₀app]
        exact congrArg Subtype.val hy
      exact ⟨x, h1⟩
    · rintro ⟨x, hx⟩
      exact ⟨unitaryProj h m x, Subtype.ext (by
        change ε₀ (unitaryProj h m x) = k
        rw [hε₀app, hx])⟩

end Embed

end CFSG.SeitzReduction.UnitaryPilot

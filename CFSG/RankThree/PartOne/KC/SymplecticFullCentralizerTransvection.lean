module

public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerSemi
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneDefs
public import CFSG.RankThree.PartOne.KC.SymplecticIsotypicFixed

public section

namespace CFSG.RankThree.PartOne.KCSpFull

open Module Polynomial CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary
  CFSG.ClassicalGroups.Alternating CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open scoped commutatorElement

variable {r : ℕ} {K : Type} [Field K]

theorem exists_spTransvection (u : Fin r ⊕ Fin r → K) (t : K) :
    ∃ g : StatedSp r K,
      spLin r K g = symplecticTransvection (spForm r K) spForm_isAlt u t := by
  have h : symplecticTransvection (spForm r K) spForm_isAlt u t ∈ (spLin r K).range := by
    rw [range_spLin, ← KCSpIsotypic.bilinIsometryGroup_eq_sesqUnitaryGroup]
    exact symplecticTransvection_mem_bilinIsometryGroup spForm_isAlt u t
  exact h

@[expose] noncomputable def spTransvection (u : Fin r ⊕ Fin r → K) (t : K) : StatedSp r K :=
  Classical.choose (exists_spTransvection u t)

theorem spLin_spTransvection (u : Fin r ⊕ Fin r → K) (t : K) :
    spLin r K (spTransvection u t) = symplecticTransvection (spForm r K) spForm_isAlt u t :=
  Classical.choose_spec (exists_spTransvection u t)

theorem spEnd_spTransvection (u : Fin r ⊕ Fin r → K) (t : K) (y : Fin r ⊕ Fin r → K) :
    spEnd (spTransvection u t) y = y + (t * spForm r K y u) • u := by
  change ((spLin r K (spTransvection u t) : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
    Module.End K (Fin r ⊕ Fin r → K)) y = _
  rw [spLin_spTransvection, symplecticTransvection_apply]

theorem spTransvection_inv (u : Fin r ⊕ Fin r → K) (t : K) :
    (spTransvection u t)⁻¹ = spTransvection u (-t) := by
  apply spLin_injective
  rw [map_inv, spLin_spTransvection, spLin_spTransvection, symplecticTransvection_inv]

theorem spEnd_mul (a b : StatedSp r K) : spEnd (a * b) = spEnd a * spEnd b := by
  change ((spLin r K (a * b) : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
    Module.End K (Fin r ⊕ Fin r → K)) = _
  rw [map_mul, Units.val_mul]

theorem spEnd_one : spEnd (1 : StatedSp r K) = 1 := by
  change ((spLin r K 1 : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
    Module.End K (Fin r ⊕ Fin r → K)) = _
  rw [map_one, Units.val_one]


omit [Field K] in
theorem exists_sub_one_apply_eq_of_mem_primaryComponent [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] (T : Module.End K V) {k : K[X]} (hk : Irreducible k) (hkm : k.Monic)
    (hk1 : k ≠ X - 1) {w : V} (hw : w ∈ primaryComponent T k) : ∃ w' : V, (T - 1) w' = w := by
  have hnd : ¬ k ∣ (X - C 1 : K[X]) := by
    intro hd
    have hass : Associated k (X - C 1 : K[X]) := hk.associated_of_dvd (irreducible_X_sub_C 1) hd
    exact hk1 (by rw [eq_of_monic_of_associated hkm (monic_X_sub_C 1) hass, map_one])
  obtain ⟨a, b, hab⟩ := hk.coprime_iff_not_dvd.mpr hnd
  refine ⟨aeval T b w, ?_⟩
  have h1 : aeval T (a * k + b * (X - C 1)) w = w := by rw [hab, map_one]; rfl
  rw [map_add, LinearMap.add_apply, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
    mem_primaryComponent.mp hw, map_zero, zero_add] at h1
  have h2 : (T - 1 : Module.End K V) = aeval T (X - C 1 : K[X]) := by
    rw [map_sub, aeval_X, aeval_C, map_one]
  rw [h2, ← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply, h1]

theorem spForm_eq_zero_of_mem_primaryComponent (x : StatedSp r K) {k : K[X]}
    (hk : k ∈ primaryFactors (spEnd x)) (hk1 : k ≠ X - 1) {u w : Fin r ⊕ Fin r → K}
    (hu : spEnd x u = u) (hw : w ∈ primaryComponent (spEnd x) k) : spForm r K w u = 0 := by
  obtain ⟨w', rfl⟩ := exists_sub_one_apply_eq_of_mem_primaryComponent (spEnd x)
    (irreducible_of_mem_primaryFactors hk) (monic_of_mem_primaryFactors hk) hk1 hw
  have hiso := mem_sesqUnitaryGroup.mp (spLin_mem x) w' u
  change spForm r K (spEnd x w') (spEnd x u) = spForm r K w' u at hiso
  rw [hu] at hiso
  rw [LinearMap.sub_apply, Module.End.one_apply, map_sub, LinearMap.sub_apply, hiso, sub_self]

theorem spTransvection_mem_spFixedFactor {x : StatedSp r K} {u : Fin r ⊕ Fin r → K}
    (hu : spEnd x u = u) (t : K) : spTransvection u t ∈ spFixedFactor x := by
  rw [spFixedFactor, mem_spSupported]
  have hiso : ∀ y, spForm r K (spEnd x y) u = spForm r K y u := fun y => by
    have := mem_sesqUnitaryGroup.mp (spLin_mem x) y u
    change spForm r K (spEnd x y) (spEnd x u) = spForm r K y u at this
    rwa [hu] at this
  refine ⟨?_, fun k hk hk1 v hv => ?_⟩
  · apply spLin_injective
    rw [map_mul, map_mul]
    refine Units.ext (LinearMap.ext fun y => ?_)
    simp only [Units.val_mul, Module.End.mul_apply]
    change spEnd (spTransvection u t) (spEnd x y) = spEnd x (spEnd (spTransvection u t) y)
    rw [spEnd_spTransvection, spEnd_spTransvection, map_add, map_smul, hu, hiso]
  · have hk1' : k ≠ X - 1 := fun h => hk1 (by rw [h]; exact Set.mem_singleton _)
    rw [spEnd_spTransvection, spForm_eq_zero_of_mem_primaryComponent x hk hk1' hu hv, mul_zero,
      zero_smul, add_zero]

section Abstract

variable {V : Type*} [AddCommGroup V] [Module K V] {B : LinearMap.BilinForm K V}

theorem eq_refl_of_commute_transvections (hnd : B.Nondegenerate) {σ : K ≃+* K} {F : V → V}
    (hadd : ∀ u v, F (u + v) = F u + F v) (hsmul : ∀ (c : K) v, F (c • v) = σ c • F v)
    (hinj : Function.Injective F) {u : V} (hu : u ≠ 0)
    (hcomm : ∀ (t : K) (y : V), F (y + (t * B y u) • u) = F y + (t * B (F y) u) • u) :
    σ = RingEquiv.refl K ∧ ∃ c : K, c ≠ 0 ∧ F u = c • u := by
  obtain ⟨y₁, hy₁⟩ : ∃ y, B y u ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hu (hnd.2 u hcon)
  obtain ⟨y₀, hB⟩ : ∃ y, B y u = 1 :=
    ⟨(B y₁ u)⁻¹ • y₁, by rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hy₁]⟩
  have hF0 : F 0 = 0 := by
    have := hadd 0 0
    simpa using this
  have key : ∀ t : K, σ t • F u = (t * B (F y₀) u) • u := by
    intro t
    have := hcomm t y₀
    rw [hB, mul_one, hadd, hsmul] at this
    exact add_left_cancel this
  set c₀ := B (F y₀) u with hc₀def
  have hFu : F u = c₀ • u := by
    have := key 1
    simpa using this
  have hFu0 : F u ≠ 0 := fun h => hu (hinj (h.trans hF0.symm))
  have hc₀ : c₀ ≠ 0 := fun h => hFu0 (by rw [hFu, h, zero_smul])
  refine ⟨RingEquiv.ext fun t => ?_, c₀, hc₀, hFu⟩
  have h1 := key t
  rw [hFu, smul_smul] at h1
  have h2 : (σ t * c₀ - t * c₀) • u = 0 := by rw [sub_smul, h1, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · have h4 : σ t * c₀ = t * c₀ := sub_eq_zero.mp h3
    simpa using mul_right_cancel₀ hc₀ h4
  · exact absurd h3 hu

theorem exists_scalar_of_forall_eigenvector {W : Submodule K V} {F : V →ₗ[K] V}
    (h : ∀ u ∈ W, ∃ c : K, F u = c • u) : ∃ l : K, ∀ u ∈ W, F u = l • u := by
  have hW : ∀ u ∈ W, F u ∈ W := fun u hu => by
    obtain ⟨c, hc⟩ := h u hu
    rw [hc]
    exact W.smul_mem c hu
  let γ : W →ₗ[K] W := F.restrict hW
  have hnl : ∀ w : W, ¬ LinearIndependent K ![w, γ w] := by
    intro w hli
    obtain ⟨c, hc⟩ := h w w.2
    have hγ : γ w = c • w := Subtype.ext (by simpa [γ] using hc)
    have := (LinearIndependent.pair_iff.mp hli) (-c) 1 (by
      simp only [one_smul, neg_smul, hγ]
      exact neg_add_cancel _)
    exact one_ne_zero this.2
  obtain ⟨l, hl⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent hnl
  refine ⟨l, fun u hu => ?_⟩
  have := congrArg (fun f : W →ₗ[K] W => (f ⟨u, hu⟩ : V)) hl
  simpa [γ] using this

end Abstract

section Lines

theorem sq_eq_multiplier_of_scalar [NeZero r] {A : gsp r K} {σ : K ≃+* K}
    (hσ : σ = RingEquiv.refl K)
    {W : Submodule K (Fin r ⊕ Fin r → K)} (hW : ((spForm r K).restrict W).Nondegenerate)
    (hne : W ≠ ⊥) {l : K} (hl : ∀ u ∈ W, semilinMap A σ u = l • u) :
    l * l = (multiplier r K A : K) := by
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨w, hw⟩ : ∃ w : W, (spForm r K).restrict W w ⟨u, hu⟩ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hu0 (congrArg Subtype.val (hW.2 ⟨u, hu⟩ hcon))
  have h1 : spForm r K (w : Fin r ⊕ Fin r → K) u ≠ 0 := hw
  have h2 := semilinMap_spForm A σ w u
  rw [hl w w.2, hl u hu, hσ] at h2
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h2
  have h3 : (l * l) * spForm r K (w : Fin r ⊕ Fin r → K) u =
      (multiplier r K A : K) * spForm r K (w : Fin r ⊕ Fin r → K) u := by
    rw [mul_assoc, h2]
    rfl
  exact mul_right_cancel₀ h1 h3


theorem semilinMap_comm_transvection (A : gsp r K) (σ : K ≃+* K) {x : StatedSp r K}
    (hfix : ∀ g ∈ spFixedFactor x, semiConj A σ g = g) {u : Fin r ⊕ Fin r → K}
    (hu : spEnd x u = u) (t : K) (y : Fin r ⊕ Fin r → K) :
    semilinMap A σ (y + (t * spForm r K y u) • u) =
      semilinMap A σ y + (t * spForm r K (semilinMap A σ y) u) • u := by
  have h := semilinMap_comm A σ (hfix _ (spTransvection_mem_spFixedFactor hu t)) y
  rw [spEnd_spTransvection, spEnd_spTransvection] at h
  exact h

theorem mem_ker_sub_one_iff {x : StatedSp r K} {u : Fin r ⊕ Fin r → K} :
    u ∈ LinearMap.ker (spEnd x - 1) ↔ spEnd x u = u := by
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]

theorem line_scalar_of_fixedFactor [NeZero r] (A : gsp r K) (σ : K ≃+* K) {x : StatedSp r K}
    (hfix : ∀ g ∈ spFixedFactor x, semiConj A σ g = g)
    (hW : ((spForm r K).restrict (LinearMap.ker (spEnd x - 1))).Nondegenerate)
    (hne : LinearMap.ker (spEnd x - 1) ≠ ⊥) :
    σ = RingEquiv.refl K ∧ ∃ l : K,
      (∀ u ∈ LinearMap.ker (spEnd x - 1), semilinMap A σ u = l • u) ∧
        l * l = (multiplier r K A : K) := by
  have heig : ∀ u ∈ LinearMap.ker (spEnd x - 1), u ≠ 0 →
      σ = RingEquiv.refl K ∧ ∃ c : K, c ≠ 0 ∧ semilinMap A σ u = c • u := fun u hu hu0 =>
    eq_refl_of_commute_transvections spForm_nondegenerate (semilinMap_add A σ)
      (semilinMap_smul A σ) (semilinMap_injective A σ) hu0
      (fun t y => semilinMap_comm_transvection A σ hfix (mem_ker_sub_one_iff.mp hu) t y)
  obtain ⟨u₀, hu₀, hu₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hσ : σ = RingEquiv.refl K := (heig u₀ hu₀ hu₀0).1
  refine ⟨hσ, ?_⟩
  subst hσ
  let Fl : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K) :=
    { toFun := semilinMap A (RingEquiv.refl K)
      map_add' := semilinMap_add A _
      map_smul' := fun c v => by rw [semilinMap_smul]; rfl }
  obtain ⟨l, hl⟩ := exists_scalar_of_forall_eigenvector (W := LinearMap.ker (spEnd x - 1))
    (F := Fl) (fun u hu => by
      by_cases hu0 : u = 0
      · exact ⟨0, by simp [hu0, Fl, semilinMap_zero]⟩
      · obtain ⟨-, c, -, hc⟩ := heig u hu hu0
        exact ⟨c, hc⟩)
  exact ⟨l, hl, sq_eq_multiplier_of_scalar rfl hW hne hl⟩

theorem ringEquiv_eq_refl_of_card_two (hK : Nat.card K = 2) (σ : K ≃+* K) :
    σ = RingEquiv.refl K := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  have h01 : ∀ c : K, c = 0 ∨ c = 1 := by
    intro c
    by_contra hcon
    push Not at hcon
    have h3 : ({0, 1, c} : Finset K).card = 3 :=
      Finset.card_eq_three.mpr ⟨0, 1, c, zero_ne_one, hcon.1.symm, hcon.2.symm, rfl⟩
    have := Finset.card_le_univ ({0, 1, c} : Finset K)
    omega
  refine RingEquiv.ext fun c => ?_
  rcases h01 c with rfl | rfl
  · simp
  · simp

@[expose] def spanMoving (U : Submodule K (Fin r ⊕ Fin r → K)) : Subgroup (StatedSp r K) where
  carrier := {g | ∀ y, spEnd g y - y ∈ U}
  one_mem' := fun y => by simp [spEnd_one]
  mul_mem' := fun {a b} ha hb y => by
    have : spEnd (a * b) y - y = (spEnd a (spEnd b y) - spEnd b y) + (spEnd b y - y) := by
      rw [spEnd_mul, Module.End.mul_apply]
      abel
    rw [this]
    exact U.add_mem (ha _) (hb y)
  inv_mem' := fun {a} ha y => by
    have h1 := ha (spEnd a⁻¹ y)
    have h2 : spEnd a (spEnd a⁻¹ y) = y := by
      rw [← Module.End.mul_apply, ← spEnd_mul, mul_inv_cancel, spEnd_one]
      rfl
    rw [h2] at h1
    have : spEnd a⁻¹ y - y = -(y - spEnd a⁻¹ y) := by abel
    rw [this]
    exact U.neg_mem h1

theorem spTransvection_mem_spanMoving {U : Submodule K (Fin r ⊕ Fin r → K)}
    {w : Fin r ⊕ Fin r → K} (hw : w ∈ U) (t : K) : spTransvection w t ∈ spanMoving U := by
  intro y
  rw [spEnd_spTransvection, add_sub_cancel_left]
  exact U.smul_mem _ hw


theorem spEnd_commutator_transvection_left {u v : Fin r ⊕ Fin r → K}
    (huv : spForm r K u v = 1) :
    spEnd ⁅spTransvection u 1, spTransvection v 1⁆ u = u - v := by
  have h1 : spForm r K u u = 0 := spForm_isAlt.self_eq_zero u
  have h2 : spForm r K v v = 0 := spForm_isAlt.self_eq_zero v
  have h3 : spForm r K v u = -1 := by rw [← spForm_isAlt.neg_eq u v, huv]
  rw [commutatorElement_def, spEnd_mul, spEnd_mul, spEnd_mul, spTransvection_inv,
    spTransvection_inv]
  simp only [Module.End.mul_apply, spEnd_spTransvection, map_add, map_smul, huv, h1, h2, h3]
  module

theorem semilinMap_mem_span_of_derived [NeZero r] (A : gsp r K) {x : StatedSp r K}
    (hfix : ∀ g ∈ ⁅spFixedFactor x, spFixedFactor x⁆,
      semiConj A (RingEquiv.refl K) g = g)
    {u v : Fin r ⊕ Fin r → K} (hu : u ∈ LinearMap.ker (spEnd x - 1))
    (hv : v ∈ LinearMap.ker (spEnd x - 1)) (huv : spForm r K u v = 1) :
    semilinMap A (RingEquiv.refl K) v ∈ Submodule.span K {u, v} := by
  have hu' : spEnd x u = u := mem_ker_sub_one_iff.mp hu
  have hv' : spEnd x v = v := mem_ker_sub_one_iff.mp hv
  have hg₁ : spTransvection u 1 ∈ spFixedFactor x := spTransvection_mem_spFixedFactor hu' 1
  have hg₂ : spTransvection v 1 ∈ spFixedFactor x := spTransvection_mem_spFixedFactor hv' 1
  have hc := Subgroup.commutator_mem_commutator hg₁ hg₂
  have hcomm := semilinMap_comm A (RingEquiv.refl K) (hfix _ hc) u
  rw [spEnd_commutator_transvection_left huv] at hcomm
  have hmov : ⁅spTransvection u 1, spTransvection v 1⁆ ∈
      spanMoving (Submodule.span K {u, v}) := by
    have h1 : spTransvection u 1 ∈ spanMoving (Submodule.span K {u, v}) :=
      spTransvection_mem_spanMoving (Submodule.subset_span (by simp)) 1
    have h2 : spTransvection v 1 ∈ spanMoving (Submodule.span K {u, v}) :=
      spTransvection_mem_spanMoving (Submodule.subset_span (by simp)) 1
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h1 h2) (inv_mem h1)) (inv_mem h2)
  have h3 := hmov (semilinMap A (RingEquiv.refl K) u)
  rw [← hcomm] at h3
  let Fl : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K) :=
    { toFun := semilinMap A (RingEquiv.refl K)
      map_add' := semilinMap_add A _
      map_smul' := fun c v => by rw [semilinMap_smul]; rfl }
  have h4 : semilinMap A (RingEquiv.refl K) (u - v) =
      semilinMap A (RingEquiv.refl K) u - semilinMap A (RingEquiv.refl K) v :=
    map_sub Fl u v
  rw [h4, sub_sub_cancel_left] at h3
  exact (Submodule.neg_mem_iff _).mp h3


theorem line_scalar_of_derived [NeZero r] (hK : Nat.card K = 2) (A : gsp r K) (σ : K ≃+* K)
    {x : StatedSp r K}
    (hfix : ∀ g ∈ ⁅spFixedFactor x, spFixedFactor x⁆, semiConj A σ g = g)
    (hW : ((spForm r K).restrict (LinearMap.ker (spEnd x - 1))).Nondegenerate)
    (h4 : 4 ≤ Module.finrank K (LinearMap.ker (spEnd x - 1))) :
    σ = RingEquiv.refl K ∧ ∃ l : K,
      (∀ u ∈ LinearMap.ker (spEnd x - 1), semilinMap A σ u = l • u) ∧
        l * l = (multiplier r K A : K) := by
  classical
  have hσ := ringEquiv_eq_refl_of_card_two hK σ
  refine ⟨hσ, ?_⟩
  subst hσ
  have hne : LinearMap.ker (spEnd x - 1) ≠ ⊥ := by
    intro h
    have h0 : Module.finrank K (LinearMap.ker (spEnd x - 1)) = 0 := by
      rw [h]
      exact finrank_bot K _
    omega
  let Fl : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K) :=
    { toFun := semilinMap A (RingEquiv.refl K)
      map_add' := semilinMap_add A _
      map_smul' := fun c v => by rw [semilinMap_smul]; rfl }
  have heig : ∀ w ∈ LinearMap.ker (spEnd x - 1), ∃ c : K, Fl w = c • w := by
    intro w hw
    by_cases hw0 : w = 0
    · exact ⟨0, by simp [hw0]⟩
    obtain ⟨u, hu, huw⟩ : ∃ u ∈ LinearMap.ker (spEnd x - 1), spForm r K u w = 1 := by
      obtain ⟨u₁, hu₁⟩ : ∃ u₁ : LinearMap.ker (spEnd x - 1),
          (spForm r K).restrict (LinearMap.ker (spEnd x - 1)) u₁ ⟨w, hw⟩ ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hw0 (congrArg Subtype.val (hW.2 ⟨w, hw⟩ hcon))
      have hu₁' : spForm r K (u₁ : Fin r ⊕ Fin r → K) w ≠ 0 := hu₁
      refine ⟨(spForm r K (u₁ : Fin r ⊕ Fin r → K) w)⁻¹ • (u₁ : Fin r ⊕ Fin r → K),
        Submodule.smul_mem _ _ u₁.2, ?_⟩
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hu₁']
    obtain ⟨u', hu', hu'w, hu'span⟩ : ∃ u' ∈ LinearMap.ker (spEnd x - 1), spForm r K u' w = 1 ∧
        u' ∉ Submodule.span K {u, w} := by
      obtain ⟨u'', hu'', hu''span⟩ : ∃ u'' ∈ LinearMap.ker (spEnd x - 1),
          u'' ∉ Submodule.span K {u, w} := by
        by_contra hcon
        push Not at hcon
        have hle : LinearMap.ker (spEnd x - 1) ≤ Submodule.span K {u, w} := hcon
        have h1 := Submodule.finrank_mono hle
        have h2 : Module.finrank K (Submodule.span K {u, w}) ≤ 2 := by
          have := finrank_span_finset_le_card (R := K) ({u, w} : Finset (Fin r ⊕ Fin r → K))
          rw [Set.finrank, Finset.coe_pair] at this
          exact this.trans (Finset.card_le_two)
        omega
      by_cases hb : spForm r K u'' w = 0
      · refine ⟨u + u'', Submodule.add_mem _ hu hu'', ?_, ?_⟩
        · rw [map_add, LinearMap.add_apply, huw, hb, add_zero]
        · intro hmem
          apply hu''span
          have := Submodule.sub_mem _ hmem (Submodule.subset_span (by simp : u ∈ ({u, w} : Set _)))
          simpa using this
      · refine ⟨(spForm r K u'' w)⁻¹ • u'', Submodule.smul_mem _ _ hu'', ?_, ?_⟩
        · rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hb]
        · intro hmem
          apply hu''span
          have := Submodule.smul_mem _ (spForm r K u'' w) hmem
          rwa [smul_smul, mul_inv_cancel₀ hb, one_smul] at this
    have hFu := semilinMap_mem_span_of_derived A hfix hu hw huw
    have hFu' := semilinMap_mem_span_of_derived A hfix hu' hw hu'w
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hFu
    obtain ⟨a', b', hab'⟩ := Submodule.mem_span_pair.mp hFu'
    by_cases ha' : a' = 0
    · refine ⟨b', ?_⟩
      show semilinMap A (RingEquiv.refl K) w = b' • w
      rw [← hab', ha', zero_smul, zero_add]
    · exfalso
      apply hu'span
      have h1 : a' • u' = a • u + (b - b') • w := by
        have h2 : a' • u' + b' • w = a • u + b • w := hab'.trans hab.symm
        calc a' • u' = (a' • u' + b' • w) - b' • w := by rw [add_sub_cancel_right]
          _ = (a • u + b • w) - b' • w := by rw [h2]
          _ = a • u + (b - b') • w := by module
      have h3 : u' = a'⁻¹ • (a • u + (b - b') • w) := by
        rw [← h1, smul_smul, inv_mul_cancel₀ ha', one_smul]
      rw [h3]
      exact Submodule.smul_mem _ _ (Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
  obtain ⟨l, hl⟩ := exists_scalar_of_forall_eigenvector (W := LinearMap.ker (spEnd x - 1))
    (F := Fl) heig
  exact ⟨l, hl, sq_eq_multiplier_of_scalar rfl hW hne hl⟩

end Lines

end CFSG.RankThree.PartOne.KCSpFull

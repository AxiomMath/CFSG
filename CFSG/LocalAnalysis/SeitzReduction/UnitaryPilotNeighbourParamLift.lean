module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotNeighbourParamFixed
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourParamTorus
import CFSG.LieType.Steinberg.CentralExt.SLMilnor
import CFSG.LieType.Steinberg.CentralExt.PerfectCover
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourStandard

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear blockSLEquiv eq_of_comp_eq_of_ker_le_center)
open scoped commutatorElement

section Schur

theorem exists_section_specialLinear_of_five_le {F : Type} [Field F] [Finite F] {m : ℕ}
    (hm : 3 ≤ m) (hF : 5 ≤ Nat.card F ∨ 5 ≤ m) {E : Type*} [Group E]
    {π : E →* SpecialLinearGroup (Fin m) F} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ center E) :
    ∃ s : SpecialLinearGroup (Fin m) F →* E, ∀ g, π (s g) = g := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rcases hF with hF | hk
  · exact CFSG.LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_central (by omega) hF
      hπ hcen
  · exact CFSG.LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_four_le (by omega) hπ
      hcen

theorem exists_surjective_lift_of_ker_le_center' {F : Type} [Field F] [Finite F] {m : ℕ}
    (hm : 3 ≤ m) (hF : 5 ≤ Nat.card F ∨ 5 ≤ m) {E : Type*} [Group E] [Group.IsPerfect E]
    {p : E →* LinearFlag.projectiveSL m F} (hp : Function.Surjective p)
    (hpker : p.ker ≤ center E) :
    ∃ Φ : SpecialLinearGroup (Fin m) F →* E, (∀ x, p (Φ x) = LinearFlag.proj m F x) ∧
      Function.Surjective Φ ∧ Φ.ker ≤ center (SpecialLinearGroup (Fin m) F) := by
  obtain ⟨s, hs⟩ := exists_section_specialLinear_of_five_le hm hF
    (CFSG.LieType.Steinberg.pullbackFst_surjective (β := LinearFlag.proj m F) hp)
    (CFSG.LieType.Steinberg.ker_pullbackFst_le_center hpker)
  let Φ : SpecialLinearGroup (Fin m) F →* E :=
    ((MonoidHom.snd _ E).comp
      (CFSG.LieType.Steinberg.pullback (LinearFlag.proj m F) p).subtype).comp s
  have hΦ : ∀ x, p (Φ x) = LinearFlag.proj m F x := fun x => by
    have hmem := CFSG.LieType.Steinberg.mem_pullback.1 (s x).2
    have h1 : ((s x : CFSG.LieType.Steinberg.pullback (LinearFlag.proj m F) p) :
        SpecialLinearGroup (Fin m) F × E).1 = x := hs x
    change p ((s x : CFSG.LieType.Steinberg.pullback (LinearFlag.proj m F) p) :
      SpecialLinearGroup (Fin m) F × E).2 = _
    rw [← hmem, h1]
  refine ⟨Φ, hΦ, ?_, ?_⟩
  · have hdecomp : ∀ y : E, ∃ x, y * (Φ x)⁻¹ ∈ center E := fun y => by
      obtain ⟨x, hx⟩ := LinearFlag.proj_surjective m F (p y)
      exact ⟨x, hpker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hΦ, hx, mul_inv_cancel])⟩
    have hcomm : commutator E ≤ Φ.range := by
      rw [commutator_def, Subgroup.commutator_le]
      intro y _ z _
      obtain ⟨x, hx⟩ := hdecomp y
      obtain ⟨x', hx'⟩ := hdecomp z
      have e : ⁅y, z⁆ = ⁅Φ x, Φ x'⁆ := by
        have h := CFSG.LieType.Steinberg.commutatorElement_mul_mul_of_mem_center hx hx' (Φ x)
          (Φ x')
        rwa [inv_mul_cancel_right, inv_mul_cancel_right] at h
      rw [e, ← map_commutatorElement]
      exact ⟨_, rfl⟩
    intro y
    exact hcomm (by rw [Group.IsPerfect.commutator_eq_top]; exact mem_top y)
  · intro x hx
    have h1 : LinearFlag.proj m F x = 1 := by rw [← hΦ, MonoidHom.mem_ker.1 hx, map_one]
    rw [LinearFlag.proj_eq_one_iff, LinearFlag.scalars_eq_center] at h1
    exact h1

end Schur

section Block

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}
  {N : Finset (Fin n)} {m : ℕ} (eN : N ≃ Fin m)

include h in
theorem unitary_blockSLEquiv {x : SpecialLinearGroup (Fin m) K}
    (hx : ((x : Matrix (Fin m) (Fin m) K).map h.bar)ᵀ * (x : Matrix (Fin m) (Fin m) K) = 1) :
    ((((blockSLEquiv N eN x : blockSpecialLinear (K := K) N) : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
      (((blockSLEquiv N eN x : blockSpecialLinear (K := K) N) : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = 1 := by
  rw [LinearPilot.coe_blockSLEquiv, LinearPilot.coe_blockEmbed]
  exact blockMatrix_unitary h N (reindex_unitary h eN.symm hx)

include h in
theorem unitary_of_unitary_blockSLEquiv {x : SpecialLinearGroup (Fin m) K}
    (hx : ((((blockSLEquiv N eN x : blockSpecialLinear (K := K) N) : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
      (((blockSLEquiv N eN x : blockSpecialLinear (K := K) N) : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = 1) :
    ((x : Matrix (Fin m) (Fin m) K).map h.bar)ᵀ * (x : Matrix (Fin m) (Fin m) K) = 1 := by
  rw [LinearPilot.coe_blockSLEquiv, LinearPilot.coe_blockEmbed] at hx
  exact unitary_of_reindex_unitary h eN.symm (unitary_of_blockMatrix_unitary h N hx)

@[expose] noncomputable def unitaryBlockSLHom : unitarySU p f K m →* unitarySU p f K n where
  toFun x := ofSL h (blockSLEquiv N eN (toSL h m x) : SpecialLinearGroup (Fin n) K)
    (unitary_blockSLEquiv h eN (unitary_toSL h x))
  map_one' := toSL_injective h (by rw [toSL_ofSL, map_one, map_one]; rfl)
  map_mul' x y := toSL_injective h (by
    rw [toSL_ofSL, map_mul, map_mul, map_mul, toSL_ofSL, toSL_ofSL, Subgroup.coe_mul])

theorem toSL_unitaryBlockSLHom (x : unitarySU p f K m) :
    toSL h n (unitaryBlockSLHom h eN x) =
      (blockSLEquiv N eN (toSL h m x) : SpecialLinearGroup (Fin n) K) :=
  rfl

theorem unitaryBlockSLHom_mem (x : unitarySU p f K m) : unitaryBlockSLHom h eN x ∈ unitaryBlock h N :=
  (mem_unitaryBlock_iff_toSL h).2 (blockSLEquiv N eN (toSL h m x)).2

theorem exists_unitaryBlockSLHom_eq {y : unitarySU p f K n} (hy : y ∈ unitaryBlock h N) :
    ∃ x : unitarySU p f K m, unitaryBlockSLHom h eN x = y := by
  set z := (blockSLEquiv N eN).symm ⟨toSL h n y, (mem_unitaryBlock_iff_toSL h).1 hy⟩ with hz
  have hεz : (blockSLEquiv N eN z : SpecialLinearGroup (Fin n) K) = toSL h n y := by
    rw [hz, MulEquiv.apply_symm_apply]
  have hzu := unitary_of_unitary_blockSLEquiv h eN (x := z) (by rw [hεz]; exact unitary_toSL h y)
  refine ⟨ofSL h z hzu, toSL_injective h ?_⟩
  rw [toSL_unitaryBlockSLHom, toSL_ofSL, hεz]

end Block

section BlockTau

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}
  {N : Finset (Fin n)} {m : ℕ} (eN : N ≃ Fin m)

omit [Field K] in
theorem blockSLEquiv_transpose [Field K] (x : SpecialLinearGroup (Fin m) K) :
    (blockSLEquiv N eN x.transpose : SpecialLinearGroup (Fin n) K) =
      (blockSLEquiv N eN x : SpecialLinearGroup (Fin n) K).transpose := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [SpecialLinearGroup.coe_transpose, transpose_apply, LinearPilot.coe_blockSLEquiv_apply,
    LinearPilot.coe_blockSLEquiv_apply, SpecialLinearGroup.coe_transpose]
  by_cases hij : i ∈ N ∧ j ∈ N
  · rw [dite_eq_left hij, dite_eq_left ⟨hij.2, hij.1⟩, transpose_apply]
  · rw [dite_eq_right hij, dite_eq_right (fun h' => hij ⟨h'.2, h'.1⟩)]
    by_cases e : i = j
    · subst e
      rfl
    · rw [one_apply_ne e, one_apply_ne (Ne.symm e)]

theorem graphFieldBlock_blockSLEquiv (x : SpecialLinearGroup (Fin m) K) :
    graphFieldBlock h N (blockSLEquiv N eN x) = blockSLEquiv N eN (graphFieldSL h m x) := by
  apply Subtype.ext
  rw [coe_graphFieldBlock_apply, graphFieldSL_apply, graphFieldSL_apply,
    LinearPilot.blockSLEquiv_map, blockSLEquiv_transpose, map_inv, Subgroup.coe_inv]

variable {f : ℕ} {h : UnitaryFieldData 2 f K}

@[expose] noncomputable def unitaryTorusBlockGL (c : unitaryTorusParam h (∅ : Finset (Fin n))) :
    GL (Fin m) K :=
  LinearPilot.unitDiagGL (LinearPilot.torusBlockUnits (RingHom.id K) eN
    ⟨c.1, unitaryTorusParam_le_blockTorusParam h ∅ c.2⟩)

theorem unitary_unitaryTorusBlockGL (c : unitaryTorusParam h (∅ : Finset (Fin n))) :
    (((unitaryTorusBlockGL eN c : GL (Fin m) K) : Matrix (Fin m) (Fin m) K).map h.bar)ᵀ *
      ((unitaryTorusBlockGL eN c : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = 1 := by
  rw [unitaryTorusBlockGL, LinearPilot.coe_unitDiagGL, diagonal_map (map_zero _),
    diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext a
  have hc := c.2.1 ((eN.symm a : N) : Fin n)
  rw [UnitaryFieldData.norm] at hc
  simp only [LinearPilot.torusBlockUnits, Units.coe_map]
  rw [mul_comm]
  exact hc

end BlockTau

section Torus

variable {G : Type*} [Group G] {L : Subgroup G} {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {n : ℕ}

theorem proj_normalizerMonoidHom_torus_eq_unitary [Finite G] (e : L ≃* unitaryPSU h n)
    {X : Subgroup G} {N : Finset (Fin n)} {m : ℕ} (eN : N ≃ Fin m) (hm : 3 ≤ m)
    (p : centralizerPerfectCore X →* LinearFlag.projectiveSL m K) (hp : Function.Surjective p)
    (hpker : p.ker ≤ center (centralizerPerfectCore X))
    (hD : modelToG e (blockSU h N) ≤ centralizerPerfectCore X)
    (h1 : ∀ x : unitarySU 2 f K m,
      p ⟨((e.symm (unitaryProj h n (unitaryBlockSLHom h eN x)) : L) : G),
        hD (symm_mem_modelToG e (unitaryProj_mem_blockSU h (unitaryBlockSLHom_mem h eN x)))⟩ =
        LinearFlag.proj m K (toSL h m x))
    (c : unitaryTorusParam h (∅ : Finset (Fin n)))
    (hg : ((e.symm (unitaryProj h n (torusDiagSU h c)) : L) : G) ∈
      normalizer (centralizerPerfectCore X : Set G))
    (y : centralizerPerfectCore X) :
    p ((centralizerPerfectCore X).normalizerMonoidHom ⟨_, hg⟩ y) =
      LinearFlag.conjAut m K (unitaryTorusBlockGL eN c) (p y) := by
  have := h.finite
  have := h.charP
  set gc : G := ((e.symm (unitaryProj h n (torusDiagSU h c)) : L) : G) with hgc
  have hker : p.ker = center (centralizerPerfectCore X) :=
    LinearPilot.ker_eq_center_of_surjective_of_center_eq_bot hp hpker
      (CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot hm)
  set γ := (centralizerPerfectCore X).normalizerMonoidHom ⟨gc, hg⟩ with hγ
  set γb := LinearPilot.descendCenterMulAut p hp hker γ with hγb
  set β := LinearFlag.conjAut m K (unitaryTorusBlockGL eN c) with hβ
  have hagree : ∀ x : unitaryPSU h m, γb (toPSL h m x) = β (toPSL h m x) := by
    intro x
    obtain ⟨g, rfl⟩ := unitaryProj_surjective h m x
    set z := torusDiagSU h c * unitaryBlockSLHom h eN g * (torusDiagSU h c)⁻¹ with hz
    have hzSL : toSL h n z = (blockSLEquiv N eN
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation m K
          (unitaryTorusBlockGL eN c) (toSL h m g)) : SpecialLinearGroup (Fin n) K) := by
      rw [hz, map_mul, map_mul, map_inv, toSL_unitaryBlockSLHom, toSL_torusDiagSU]
      exact LinearPilot.torusDiagSL_mul_blockSLEquiv_mul_inv N eN _ (toSL h m g)
    have hzN : z ∈ unitaryBlock h N := by
      rw [mem_unitaryBlock_iff_toSL, hzSL]
      exact (blockSLEquiv N eN _).2
    obtain ⟨g', hg'⟩ := exists_unitaryBlockSLHom_eq h eN hzN
    have hg'SL : toSL h m g' =
        CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation m K
          (unitaryTorusBlockGL eN c) (toSL h m g) := by
      apply (blockSLEquiv N eN).injective
      apply Subtype.ext
      rw [← toSL_unitaryBlockSLHom, hg', hzSL]
    have hγg : γ ⟨((e.symm (unitaryProj h n (unitaryBlockSLHom h eN g)) : L) : G),
        hD (symm_mem_modelToG e (unitaryProj_mem_blockSU h (unitaryBlockSLHom_mem h eN g)))⟩ =
        ⟨((e.symm (unitaryProj h n (unitaryBlockSLHom h eN g')) : L) : G),
          hD (symm_mem_modelToG e (unitaryProj_mem_blockSU h (unitaryBlockSLHom_mem h eN g')))⟩ := by
      apply Subtype.ext
      rw [hγ, Subgroup.normalizerMonoidHom_apply_apply_coe]
      change gc * ((e.symm (unitaryProj h n (unitaryBlockSLHom h eN g)) : L) : G) * gc⁻¹ =
        ((e.symm (unitaryProj h n (unitaryBlockSLHom h eN g')) : L) : G)
      rw [hg', hz, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
      simp only [hgc, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [toPSL_unitaryProj, ← h1 g, hγb, LinearPilot.descendCenterMulAut_apply, hγg, h1 g', hg'SL,
      hβ, h1 g, LinearFlag.conjAut_proj]
  set r := Nat.card Kˣ with hr
  have hrodd : Odd r := by
    rw [hr, Nat.card_units]
    exact LinearPilot.odd_natCard_sub_one
  have hcr : c ^ r = 1 := by
    apply Subtype.ext
    funext i
    change (c.1 i) ^ r = 1
    exact pow_card_eq_one'
  have hγr : γb ^ r = 1 := by
    have hgr : (⟨gc, hg⟩ : normalizer (centralizerPerfectCore X : Set G)) ^ r = 1 := by
      apply Subtype.ext
      rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
      change gc ^ r = 1
      rw [hgc, ← Subgroup.coe_pow, ← map_pow, ← map_pow, ← map_pow, hcr, map_one, map_one,
        map_one, OneMemClass.coe_one]
    rw [hγb, ← map_pow, hγ, ← map_pow, hgr, map_one, map_one]
  have hβr : β ^ r = 1 := by
    have hu : LinearPilot.torusBlockUnits (RingHom.id K) eN
        ⟨c.1, unitaryTorusParam_le_blockTorusParam h ∅ c.2⟩ ^ r = 1 := by
      funext a
      change (Units.map (RingHom.id K).toMonoidHom (c.1 ((eN.symm a : N) : Fin n))) ^ r = 1
      rw [← map_pow, pow_card_eq_one', map_one]
    rw [hβ, ← map_pow, unitaryTorusBlockGL, LinearPilot.unitDiagGL_pow, hu,
      LinearPilot.unitDiagGL_one, map_one]
  have hβθ : Commute β (graphFieldAut h m) :=
    commute_conjAut_graphFieldAut h (unitary_unitaryTorusBlockGL eN c)
  have hγβ := eq_of_forall_toPSL_of_pow h hm hβθ hrodd hβr hγr hagree
  rw [← LinearPilot.descendCenterMulAut_apply p hp hker γ y, ← hγb, hγβ]

end Torus

section FromProj

variable {G : Type*} [Group G] {L : Subgroup G} {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {n : ℕ}

theorem nonempty_graphFieldNeighbourParam_of_proj [Finite G] (e : L ≃* unitaryPSU h n) (t : G)
    {X : Subgroup G} {N : Finset (Fin n)} {m : ℕ} (eN : N ≃ Fin m) (hm : 4 ≤ m)
    (hsplit : 5 ≤ Nat.card K ∨ 5 ≤ m)
    (p : centralizerPerfectCore X →* LinearFlag.projectiveSL m K) (hp : Function.Surjective p)
    (hpker : p.ker ≤ center (centralizerPerfectCore X))
    (hD : modelToG e (blockSU h N) ≤ centralizerPerfectCore X)
    (h1 : ∀ x : unitarySU 2 f K m,
      p ⟨((e.symm (unitaryProj h n (unitaryBlockSLHom h eN x)) : L) : G),
        hD (symm_mem_modelToG e (unitaryProj_mem_blockSU h (unitaryBlockSLHom_mem h eN x)))⟩ =
        LinearFlag.proj m K (toSL h m x))
    (ht : t ∈ normalizer (centralizerPerfectCore X : Set G))
    (h3 : ∀ y, p ((centralizerPerfectCore X).normalizerMonoidHom ⟨t, ht⟩ y) =
      graphFieldAut h m (p y))
    (hg : ∀ c : unitaryTorusParam h (∅ : Finset (Fin n)),
      ((e.symm (unitaryProj h n (torusDiagSU h c)) : L) : G) ∈
        normalizer (centralizerPerfectCore X : Set G)) :
    Nonempty (GraphFieldNeighbourParam e t X N) := by
  have := h.finite
  have : Group.IsPerfect (centralizerPerfectCore X) :=
    Subgroup.isPerfect_iff.mpr (F4Pilot.commutator_centralizerPerfectCore X)
  have : Group.IsPerfect (SpecialLinearGroup (Fin m) K) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by omega)
  have : Group.IsPerfect (unitarySU 2 f K m) :=
    (isQuasisimple_unitarySU h (by omega) (fun h' => by
      have := congrArg Prod.fst h'
      simp only at this
      omega)).1
  obtain ⟨Φ₀, hΦ₀, hsurj, hker⟩ := exists_surjective_lift_of_ker_le_center' (by omega) hsplit hp
    hpker
  let ψ₁ : unitarySU 2 f K m →* centralizerPerfectCore X :=
    MonoidHom.codRestrict (L.subtype.comp (e.symm.toMonoidHom.comp ((unitaryProj h n).comp
      (unitaryBlockSLHom h eN)))) (centralizerPerfectCore X)
      (fun x => hD (symm_mem_modelToG e (unitaryProj_mem_blockSU h (unitaryBlockSLHom_mem h eN x))))
  have hN1 : Φ₀.comp (toSL h m) = ψ₁ :=
    eq_of_comp_eq_of_ker_le_center hpker fun x => by
      rw [MonoidHom.comp_apply, hΦ₀]
      exact (h1 x).symm
  have hN3 : ((centralizerPerfectCore X).normalizerMonoidHom ⟨t, ht⟩).toMonoidHom.comp Φ₀ =
      Φ₀.comp (graphFieldSL h m).toMonoidHom :=
    eq_of_comp_eq_of_ker_le_center hpker fun x => by
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h3, hΦ₀, hΦ₀,
        MulEquiv.coe_toMonoidHom, graphFieldAut_proj]
  have hN2 : ∀ c, ((centralizerPerfectCore X).normalizerMonoidHom ⟨_, hg c⟩).toMonoidHom.comp Φ₀ =
      Φ₀.comp (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation m K
        (unitaryTorusBlockGL eN c)).toMonoidHom := fun c =>
    eq_of_comp_eq_of_ker_le_center hpker fun x => by
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.coe_toMonoidHom,
        proj_normalizerMonoidHom_torus_eq_unitary e eN (by omega) p hp hpker hD h1 c (hg c), hΦ₀,
        hΦ₀, LinearFlag.conjAut_proj]
  let Φ : blockSpecialLinear (K := K) N →* G :=
    (centralizerPerfectCore X).subtype.comp (Φ₀.comp (blockSLEquiv N eN).symm.toMonoidHom)
  have hΦ : ∀ x', Φ (blockSLEquiv N eN x') = (Φ₀ x' : G) := fun x' => by
    change ((Φ₀ ((blockSLEquiv N eN).symm (blockSLEquiv N eN x')) : centralizerPerfectCore X) :
      G) = _
    rw [MulEquiv.symm_apply_apply]
  refine ⟨⟨Φ, ?_, ?_, ?_, ?_, ?_⟩⟩
  ·
    have hs : Function.Surjective (Φ₀.comp (blockSLEquiv N eN).symm.toMonoidHom) := fun y => by
      obtain ⟨x, rfl⟩ := hsurj y
      exact ⟨blockSLEquiv N eN x, by simp⟩
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hs, ← MonoidHom.range_eq_map,
      range_subtype]
  ·
    intro x hx
    obtain ⟨x', rfl⟩ := (blockSLEquiv N eN).surjective x
    have hx' : Φ₀ x' = 1 := by
      apply Subtype.ext
      rw [← hΦ]
      exact hx
    have hz := hker hx'
    rw [mem_center_iff] at hz ⊢
    intro y
    obtain ⟨y', rfl⟩ := (blockSLEquiv N eN).surjective y
    rw [← map_mul, ← map_mul, hz y']
  ·
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := exists_unitaryBlockSLHom_eq h eN hy
    have hx : (⟨toSL h n (unitaryBlockSLHom h eN x), (mem_unitaryBlock_iff_toSL h).1
        (Subtype.mk (unitaryBlockSLHom h eN x) hy).2⟩ : blockSpecialLinear (K := K) N) =
        blockSLEquiv N eN (toSL h m x) := Subtype.ext rfl
    rw [hx, hΦ]
    have := congrArg (fun φ : unitarySU 2 f K m →* centralizerPerfectCore X => (φ x : G)) hN1
    exact this
  ·
    intro c _ x
    obtain ⟨x', rfl⟩ := (blockSLEquiv N eN).surjective x
    rw [conjTorus_eq_conjDiag, LinearPilot.conjDiag_blockSLEquiv, hΦ, hΦ]
    have := congrArg (fun φ : SpecialLinearGroup (Fin m) K →* centralizerPerfectCore X => (φ x' : G)) (hN2 c)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      Subgroup.normalizerMonoidHom_apply_apply_coe] at this
    exact this.symm
  ·
    intro x
    obtain ⟨x', rfl⟩ := (blockSLEquiv N eN).surjective x
    rw [graphFieldBlock_blockSLEquiv, hΦ, hΦ]
    have := congrArg (fun φ : SpecialLinearGroup (Fin m) K →* centralizerPerfectCore X => (φ x' : G)) hN3
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      Subgroup.normalizerMonoidHom_apply_apply_coe] at this
    exact this

end FromProj

section Root

variable {G : Type*} [Group G] {L : Subgroup G} {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {n : ℕ}

theorem unitaryProj_torusDiagSU_mem_normalizer_unitaryRootTorus {a b : Fin n} (hab : a ≠ b)
    (c : unitaryTorusParam h (∅ : Finset (Fin n))) :
    unitaryProj h n (torusDiagSU h c) ∈
      normalizer (unitaryRootTorus h hab : Set (unitaryPSU h n)) := by
  refine centralizer_le_normalizer _ (mem_centralizer_iff.2 fun x hx => ?_)
  obtain ⟨c', -, rfl⟩ := (mem_unitaryBlockTorus h).1
    (unitaryRootTorus_le_unitaryBlockTorus_of_subset h hab (Finset.empty_subset _) hx)
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, mul_comm c' c]

end Root

end CFSG.SeitzReduction.UnitaryPilot

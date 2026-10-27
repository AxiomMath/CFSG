module

public import CFSG.LocalAnalysis.StandardType.GGQ2OrthBlocksExt2

public section

namespace CFSG.StandardType.GGQ2Frame.OrthBlocks

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.SpJoin
  CFSG.StandardType.ClassicalPosition Matrix
open CFSG.Open (StatedSp)
open CFSG.ClassicalGroups.Symplectic

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (δ : Fin 2)

theorem oYcode_extension_map_eq (hK : Nat.card K = 2) (hζ : Function.Injective ζ)
    (e : PlaneRaw.V t) (he : PlaneRaw.admissible (.orthogonal δ) (.extension e : PlaneRaw.Code t)) :
    (oYcode ζ t δ (.extension e)).map (omegaQ (K := K) t δ).subtype =
      (SpBlocks.Ycode ζ (t + δ.val) (.extension (liftV t δ e))).map
        (StatedSp (t + δ.val) K).subtype := by
  let S : Finset (Fin (t + δ.val)) := PlaneRaw.Code.extSupport (liftV t δ e)
  let B : Subgroup ↥(StatedSp (t + δ.val) K) :=
    SpBlocks.blockGroup ζ (t + δ.val) (.extension (liftV t δ e))
  let B' : Subgroup (GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :=
    B.map (StatedSp (t + δ.val) K).subtype
  let Y : Subgroup ↥(StatedSp (t + δ.val) K) :=
    SpBlocks.Ycode ζ (t + δ.val) (.extension (liftV t δ e))
  have hB'leO : B' ≤ LargeEvenOrthGroup (planeQ (K := K) t δ) :=
    blockGroup_extension_map_le_orth ζ t δ hK hζ e
  have hcomp_le_Omega : ⁅B', B'⁆ ≤ omegaQ (K := K) t δ := by
    rw [show omegaQ (K := K) t δ = LargeEvenOmega (planeQ (K := K) t δ) from rfl,
      largeEvenOmega_def]
    exact Subgroup.commutator_mono hB'leO hB'leO
  have he' : PlaneRaw.admissible .symplectic
      (.extension (liftV t δ e) : PlaneRaw.Code (t + δ.val)) :=
    admissible_symplectic_lift t δ he
  have hYq : IsQuasisimple ↥Y := SpBlocks.spIsQuasisimpleYcode_holds ζ (t + δ.val) hK hζ
    (.extension (liftV t δ e)) he'
  have hYself : ⁅Y, Y⁆ = Y := by
    rw [← Subgroup.map_subtype_commutator Y, hYq.1.commutator_eq_top, Subgroup.map_top,
      Subgroup.range_subtype]
  have hperfect : ⁅B', B'⁆ = ⁅⁅B', B'⁆, ⁅B', B'⁆⁆ := by
    have hB'' : ⁅B', B'⁆ = Y.map (StatedSp (t + δ.val) K).subtype := by
      change ⁅B.map (StatedSp (t + δ.val) K).subtype,
          B.map (StatedSp (t + δ.val) K).subtype⁆ =
        (SpBlocks.Ycode ζ (t + δ.val) (.extension (liftV t δ e))).map
          (StatedSp (t + δ.val) K).subtype
      rw [SpBlocks.Ycode, Subgroup.map_commutator]
    rw [hB'', ← Subgroup.map_commutator, hYself]
  have hB''le : ⁅B', B'⁆ ≤ B' ⊓ omegaQ (K := K) t δ :=
    le_inf (Subgroup.commutator_le_self B') hcomp_le_Omega
  have hEq : ⁅B' ⊓ omegaQ (K := K) t δ, B' ⊓ omegaQ (K := K) t δ⁆ = ⁅B', B'⁆ := by
    refine le_antisymm (Subgroup.commutator_mono inf_le_left inf_le_left) ?_
    calc ⁅B', B'⁆ = ⁅⁅B', B'⁆, ⁅B', B'⁆⁆ := hperfect
      _ ≤ ⁅B' ⊓ omegaQ (K := K) t δ, B' ⊓ omegaQ (K := K) t δ⁆ :=
          Subgroup.commutator_mono hB''le hB''le
  have hLHS : (oYcode ζ t δ (.extension e)).map (omegaQ (K := K) t δ).subtype =
      ⁅B' ⊓ omegaQ (K := K) t δ, B' ⊓ omegaQ (K := K) t δ⁆ := by
    rw [oYcode, Subgroup.map_commutator, oBlockGroup_map_eq]
    change ⁅B' ⊓ omegaQ (K := K) t δ, B' ⊓ omegaQ (K := K) t δ⁆ =
      ⁅B' ⊓ omegaQ (K := K) t δ, B' ⊓ omegaQ (K := K) t δ⁆
    rfl
  have hRHS : (SpBlocks.Ycode ζ (t + δ.val) (.extension (liftV t δ e))).map
        (StatedSp (t + δ.val) K).subtype = ⁅B', B'⁆ := by
    rw [SpBlocks.Ycode, Subgroup.map_commutator]
  rw [hLHS, hRHS, hEq]

private noncomputable def oYcodeEquivSpYcode (hK : Nat.card K = 2)
    (hζ : Function.Injective ζ) (e : PlaneRaw.V t)
    (he : PlaneRaw.admissible (.orthogonal δ) (.extension e : PlaneRaw.Code t)) :
    ↥(oYcode ζ t δ (.extension e)) ≃*
      ↥(SpBlocks.Ycode ζ (t + δ.val) (.extension (liftV t δ e))) :=
  ((oYcode ζ t δ (.extension e)).equivMapOfInjective (omegaQ (K := K) t δ).subtype
      (Subgroup.subtype_injective _)).trans
    ((MulEquiv.subgroupCongr (oYcode_extension_map_eq ζ t δ hK hζ e he)).trans
      ((SpBlocks.Ycode ζ (t + δ.val) (.extension (liftV t δ e))).equivMapOfInjective
        (StatedSp (t + δ.val) K).subtype (Subgroup.subtype_injective _)).symm)

theorem orthIsQuasisimpleYcode_extension (hK : Nat.card K = 2) (hζ : Function.Injective ζ)
    (e : PlaneRaw.V t) (he : PlaneRaw.admissible (.orthogonal δ) (.extension e : PlaneRaw.Code t)) :
    IsQuasisimple ↥(oYcode ζ t δ (.extension e)) := by
  have he' : PlaneRaw.admissible .symplectic
      (.extension (liftV t δ e) : PlaneRaw.Code (t + δ.val)) :=
    admissible_symplectic_lift t δ he
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (oYcodeEquivSpYcode ζ t δ hK hζ e he).symm
    (SpBlocks.spIsQuasisimpleYcode_holds ζ (t + δ.val) hK hζ
      (.extension (liftV t δ e)) he')

theorem orthMarkedYcode_extension (hK : Nat.card K = 2) (hζ : Function.Injective ζ)
    (e : PlaneRaw.V t) (he : PlaneRaw.admissible (.orthogonal δ) (.extension e : PlaneRaw.Code t)) :
    LargeEvenMarking ↥(oYcode ζ t δ (.extension e))
      (fun lab _ _ _ _ _ => lab =
        PlaneRaw.label (.orthogonal δ) (.extension e : PlaneRaw.Code t)) := by
  have he' : PlaneRaw.admissible .symplectic
      (.extension (liftV t δ e) : PlaneRaw.Code (t + δ.val)) :=
    admissible_symplectic_lift t δ he
  have hmark : LargeEvenMarking
      ↥(SpBlocks.Ycode ζ (t + δ.val) (.extension (liftV t δ e)))
      (fun lab _ _ _ _ _ => lab = PlaneRaw.label .symplectic
        (.extension (liftV t δ e) : PlaneRaw.Code (t + δ.val))) :=
    SpBlocks.spMarkedYcode_holds ζ (t + δ.val) hK hζ (.extension (liftV t δ e)) he'
  have hlab : PlaneRaw.label (.orthogonal δ) (.extension e : PlaneRaw.Code t) =
      PlaneRaw.label .symplectic
        (.extension (liftV t δ e) : PlaneRaw.Code (t + δ.val)) := by
    simp [PlaneRaw.label, card_extSupport_liftV t δ e]
  refine largeEvenMarking_congr (oYcodeEquivSpYcode ζ t δ hK hζ e he) ?_ hmark
  intro lab R _ I F θ hθ
  exact hθ.trans hlab.symm

theorem orthTauMemYcodeIff_extension (hK : Nat.card K = 2) (hζ : Function.Injective ζ)
    (e : PlaneRaw.V t) (he : PlaneRaw.admissible (.orthogonal δ) (.extension e : PlaneRaw.Code t))
    (u : PlaneRaw.V t) :
    otau ζ t δ u ∈ (oYcode ζ t δ (.extension e)).map (omegaQ (K := K) t δ).subtype ↔
      u ∈ PlaneRaw.inside (.orthogonal δ) (.extension e : PlaneRaw.Code t) := by
  have he' : PlaneRaw.admissible .symplectic
      (.extension (liftV t δ e) : PlaneRaw.Code (t + δ.val)) :=
    admissible_symplectic_lift t δ he
  rw [oYcode_extension_map_eq ζ t δ hK hζ e he]
  have hmem : (otau ζ t δ u ∈
      (SpBlocks.Ycode ζ (t + δ.val) (.extension (liftV t δ e))).map
        (StatedSp (t + δ.val) K).subtype) ↔
      SpBlocks.tau ζ (t + δ.val) (liftV t δ u) ∈
        SpBlocks.Ycode ζ (t + δ.val) (.extension (liftV t δ e)) := by
    change ((SpBlocks.tau ζ (t + δ.val) (liftV t δ u) :
      ↥(StatedSp (t + δ.val) K)) : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) ∈ _ ↔ _
    exact mem_map_subtype_iff _ _
  rw [hmem, SpBlocks.spTauMemYcodeIff_holds ζ (t + δ.val) hK hζ
    (.extension (liftV t δ e)) he' (liftV t δ u)]
  exact mem_inside_liftV_iff t δ .symplectic (.orthogonal δ) e u

theorem orthTauCommuteYcodeIff_extension (hK : Nat.card K = 2) (hζ : Function.Injective ζ)
    (e : PlaneRaw.V t) (he : PlaneRaw.admissible (.orthogonal δ) (.extension e : PlaneRaw.Code t))
    (u : PlaneRaw.V t) :
    (∀ g ∈ oYcode ζ t δ (.extension e),
        otau ζ t δ u * (g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) =
          (g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) * otau ζ t δ u) ↔
      u ∈ PlaneRaw.cent (.orthogonal δ) (.extension e : PlaneRaw.Code t) := by
  have he' : PlaneRaw.admissible .symplectic
      (.extension (liftV t δ e) : PlaneRaw.Code (t + δ.val)) :=
    admissible_symplectic_lift t δ he
  have hcent := mem_cent_liftV_iff t δ .symplectic (.orthogonal δ) e u
  rw [← hcent]
  rw [← SpBlocks.spTauCommuteYcodeIff_holds ζ (t + δ.val) hK hζ
    (.extension (liftV t δ e)) he' (liftV t δ u)]
  have hE := oYcode_extension_map_eq ζ t δ hK hζ e he
  constructor
  · intro h y hy
    have hy' : (y : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) ∈
        (SpBlocks.Ycode ζ (t + δ.val) (.extension (liftV t δ e))).map
          (StatedSp (t + δ.val) K).subtype :=
      Subgroup.mem_map_of_mem _ hy
    rw [← hE] at hy'
    obtain ⟨g, hg, hgy⟩ := Subgroup.mem_map.mp hy'
    have hg' := h g hg
    have hgy' : (g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) =
        (y : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) := hgy
    rw [hgy'] at hg'
    apply (StatedSp (t + δ.val) K).subtype_injective
    change ((SpBlocks.tau ζ (t + δ.val) (liftV t δ u) :
        ↥(StatedSp (t + δ.val) K)) : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) *
        (y : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) =
      (y : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) *
        ((SpBlocks.tau ζ (t + δ.val) (liftV t δ u) :
          ↥(StatedSp (t + δ.val) K)) : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K)
    simpa only [otau] using hg'
  · intro h g hg
    have hg' : (g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) ∈
        (oYcode ζ t δ (.extension e)).map (omegaQ (K := K) t δ).subtype :=
      Subgroup.mem_map_of_mem _ hg
    rw [hE] at hg'
    obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp hg'
    have hy' := h y hy
    have hy'' := congrArg (fun z : ↥(StatedSp (t + δ.val) K) =>
      (z : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K)) hy'
    simp only [Subgroup.coe_mul] at hy''
    have hyg' : (y : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) =
        (g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) := hyg
    simpa only [otau, hyg'] using hy''

theorem orthNotIsComponentOfYcode_extension (hK : Nat.card K = 2) (hζ : Function.Injective ζ)
    (e : PlaneRaw.V t)
    (he : ¬ PlaneRaw.admissible (.orthogonal δ) (.extension e : PlaneRaw.Code t))
    (X : Subgroup ↥(omegaQ (K := K) t δ)) :
    ¬ IsComponentOf X (oYcode ζ t δ (.extension e)) := by
  by_cases hzero : e = 0
  · subst e
    have hzero' : (liftV t δ (0 : PlaneRaw.V t) :
        PlaneRaw.V (t + δ.val)) = 0 := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
        simp [liftV, Fin.append_left, Fin.append_right]
    have hB : SpBlocks.blockGroup ζ (t + δ.val)
        (.extension (liftV t δ (0 : PlaneRaw.V t))) = ⊥ := by
      rw [hzero', SpBlocks.blockGroup_extension_zero]
    have hoB : oBlockGroup ζ t δ (.extension (0 : PlaneRaw.V t)) = ⊥ := by
      have hmap : (oBlockGroup ζ t δ (.extension (0 : PlaneRaw.V t))).map
          (omegaQ (K := K) t δ).subtype = ⊥ := by
        rw [show oBlockGroup ζ t δ (.extension (0 : PlaneRaw.V t)) =
          ((SpBlocks.blockGroup ζ (t + δ.val)
            (.extension (liftV t δ (0 : PlaneRaw.V t)))).map
              (StatedSp (t + δ.val) K).subtype).comap
                (omegaQ (K := K) t δ).subtype from rfl, hB]
        simp
      exact (Subgroup.map_eq_bot_iff_of_injective
        (oBlockGroup ζ t δ (.extension (0 : PlaneRaw.V t)))
        (f := (omegaQ (K := K) t δ).subtype)
        (Subgroup.subtype_injective (omegaQ (K := K) t δ))).mp hmap
    have hoY : oYcode ζ t δ (.extension (0 : PlaneRaw.V t)) = ⊥ := by
      rw [oYcode, hoB, Subgroup.commutator_bot_left]
    rw [hoY]
    simpa using SpBlocks.not_isComponentOf_commutator_bot X
  · have hcard : (PlaneRaw.Code.extSupport e).card ≤ 3 := by
      by_contra h
      exact he ⟨hzero, by omega⟩
    have hcard' : (PlaneRaw.Code.extSupport (liftV t δ e)).card ≤ 3 := by
      rwa [card_extSupport_liftV]
    have he' : liftV t δ e ≠ 0 := by
      intro h0
      have hzero0 : liftV t δ (0 : PlaneRaw.V t) = 0 := by
        funext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
          simp [liftV, Fin.append_left, Fin.append_right]
      exact hzero (liftV_injective t δ (h0.trans hzero0.symm))
    obtain ⟨E, _, _, _, hE, ⟨φ⟩⟩ :=
      SpBlocks.exists_blockGroup_extension_mulEquiv ζ (t + δ.val) hK hζ he'
    let B : Subgroup ↥(StatedSp (t + δ.val) K) :=
      SpBlocks.blockGroup ζ (t + δ.val) (.extension (liftV t δ e))
    have hBsolv : Group.IsSolvable ↥B :=
      SpBlocks.isSolvable_of_mulEquiv_guFull hE hcard' φ
    have hB'solv : Group.IsSolvable
        ↥(B.map (StatedSp (t + δ.val) K).subtype) :=
      @Group.isSolvable_of_isSolvable_injective
        ↥(B.map (StatedSp (t + δ.val) K).subtype) ↥B _ _
        (B.equivMapOfInjective (StatedSp (t + δ.val) K).subtype
          (Subgroup.subtype_injective _)).symm.toMonoidHom
        (B.equivMapOfInjective (StatedSp (t + δ.val) K).subtype
          (Subgroup.subtype_injective _)).symm.injective hBsolv
    have hmapB : (oBlockGroup ζ t δ (.extension e)).map
        (omegaQ (K := K) t δ).subtype = B.map (StatedSp (t + δ.val) K).subtype ⊓
          omegaQ (K := K) t δ := by
      rw [oBlockGroup_map_eq]
      rfl
    have hle : (oBlockGroup ζ t δ (.extension e)).map
        (omegaQ (K := K) t δ).subtype ≤ B.map (StatedSp (t + δ.val) K).subtype := by
      rw [hmapB]
      exact inf_le_left
    let ψ : ↥(oBlockGroup ζ t δ (.extension e)) →*
        ↥(B.map (StatedSp (t + δ.val) K).subtype) :=
      ((omegaQ (K := K) t δ).subtype.comp
        (oBlockGroup ζ t δ (.extension e)).subtype).codRestrict _ fun x =>
          hle ⟨x, x.2, rfl⟩
    have hψ : Function.Injective ψ := by
      intro x y hxy
      apply Subtype.ext
      apply (Subgroup.subtype_injective (omegaQ (K := K) t δ))
      exact congrArg (fun z : ↥(B.map (StatedSp (t + δ.val) K).subtype) =>
        (z : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K)) hxy
    have hoBsolv : Group.IsSolvable ↥(oBlockGroup ζ t δ (.extension e)) :=
      @Group.isSolvable_of_isSolvable_injective
        ↥(oBlockGroup ζ t δ (.extension e))
        ↥(B.map (StatedSp (t + δ.val) K).subtype) _ _ ψ hψ hB'solv
    have hoYsolv : Group.IsSolvable ↥(oYcode ζ t δ (.extension e)) :=
      @Group.isSolvable_of_isSolvable_injective
        ↥(oYcode ζ t δ (.extension e)) ↥(oBlockGroup ζ t δ (.extension e)) _ _
        (Subgroup.inclusion (Subgroup.commutator_le_self
          (oBlockGroup ζ t δ (.extension e))))
        (Subgroup.inclusion_injective (Subgroup.commutator_le_self
          (oBlockGroup ζ t δ (.extension e)))) hoBsolv
    exact CFSG.StandardType.ResU3Three.not_isComponentOf_of_isSolvable hoYsolv

end CFSG.StandardType.GGQ2Frame.OrthBlocks

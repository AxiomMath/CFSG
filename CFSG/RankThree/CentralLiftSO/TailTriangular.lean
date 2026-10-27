module

public import CFSG.RankThree.CentralLiftSO.TailWeyl
public import CFSG.RankThree.CentralLiftSO.SplitTriangular
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailParameterKernels

public section

namespace CFSG.RankThree.CentralLiftSO.TailO

open QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal CFSG.LieType.CentralExt
open CFSG.RankThree.CentralLift
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.LocalAnalysis.ComponentInitial.NormTail
open CFSG.LocalAnalysis.ComponentInitial.NormTail renaming torusMap → tMap
open CFSG.LocalAnalysis.ComponentInitial (orthElementaryGroup)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (sl2W sl2Diag)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit (ne_succ_of_lt eps roots
  posRoots_subset_roots neg_mem_roots)
open CFSG.LieType.Chevalley (uSL vSL coe_uSL coe_vSL)
open CFSG.RankThree.CentralLiftSO.Lift
open scoped Pointwise

variable {K L : Type} [Field K] [Field L] [Algebra K L]

section Defs

variable (T : NormTailData K L) (r : ℕ)

@[expose] noncomputable def unipG : Subgroup (G0 T r) :=
  (tailUnipotent r (normForm T)).subgroupOf (orthElementaryGroup (quadTail r (normForm T)))

@[expose] noncomputable def unipExceptG (i : Fin r) : Subgroup (G0 T r) :=
  (tailUnipotentExcept r (normForm T) i).subgroupOf
    (orthElementaryGroup (quadTail r (normForm T)))

variable {T r} {E : Type*} [Group E] (π : E →* G0 T r)

@[expose] noncomputable def liftUnip : Subgroup E :=
  liftSubgroup (ringChar K) π (unipG T r)

@[expose] noncomputable def liftUnipExcept (i : Fin r) : Subgroup E :=
  liftSubgroup (ringChar K) π (unipExceptG T r i)

@[expose] noncomputable def liftBorel : Subgroup E :=
  liftUnip π ⊔ liftTorus T π

@[expose] noncomputable def xPlusLong {i : Fin r} (h : i.val + 1 < r) (t : K) : E :=
  etaLift T π (ne_succ_of_lt h) (uSL t)

@[expose] noncomputable def xMinusLong {i : Fin r} (h : i.val + 1 < r) (t : K) : E :=
  etaLift T π (ne_succ_of_lt h) (vSL t)

@[expose] noncomputable def xPlusShort (i : Fin r) (t : L) : E :=
  rhoLift T π i (uSL t)

@[expose] noncomputable def xMinusShort (i : Fin r) (t : L) : E :=
  rhoLift T π i (vSL t)

theorem xPlusLong_mul_sLift {i : Fin r} (h : i.val + 1 < r) {t : K} (ht : t ≠ 0) :
    xPlusLong π h t * sLift T π i =
      xMinusLong π h t⁻¹ * hLift T π (ne_succ_of_lt h) (Units.mk0 t ht) *
        xPlusLong π h (-t⁻¹) := by
  rw [xPlusLong, sLift_of_lt h, ← map_mul, uSL_mul_sl2W ht, map_mul, map_mul]
  rfl

theorem xPlusShort_mul_sLift {i : Fin r} (h : ¬i.val + 1 < r) {t : L} (ht : t ≠ 0) :
    xPlusShort π i t * sLift T π i =
      xMinusShort π i t⁻¹ * tauLift T π i (Units.mk0 t ht) * xPlusShort π i (-t⁻¹) := by
  rw [xPlusShort, sLift_of_not_lt h, wLift, ← map_mul, uSL_mul_sl2W ht, map_mul, map_mul]
  rfl

end Defs

section Matrices

variable (T : NormTailData K L) {r : ℕ}

theorem eta_uSL_of_lt {i : Fin r} (h : i.val + 1 < r) (t : K) :
    eta L (ne_succ_of_lt h) (uSL t) = tailLongElt r (normForm T) (simpleRootB r i) t := by
  rw [eta_eq_prodHom T, MonoidHom.comp_apply, SplitO.etaLin_uSL_of_lt h, prodHom_apply,
    tailLongElt_eq_prodCongr, simpleRootB_eq_simpleRoot h]

theorem eta_vSL_of_lt {i : Fin r} (h : i.val + 1 < r) (t : K) :
    eta L (ne_succ_of_lt h) (vSL t) = tailLongElt r (normForm T) (-simpleRootB r i) t := by
  rw [eta_eq_prodHom T, MonoidHom.comp_apply, SplitO.etaLin_vSL_of_lt h, prodHom_apply,
    tailLongElt_eq_prodCongr, simpleRootB_eq_simpleRoot h]

theorem rhoO_uSL (i : Fin r) (t : L) :
    rhoO T i (uSL t) = tailShortElt r (normForm T) (eps r i) (-t) := by
  rw [show uSL t = upperSL L t from rfl, rhoO_upperSL, tailShortElt_eps]

theorem rhoO_vSL (i : Fin r) (t : L) :
    rhoO T i (vSL t) = tailShortElt r (normForm T) (-eps r i) (T.bar t) := by
  rw [show vSL t = lowerSL L t from rfl, rhoO_lowerSL, tailShortElt_neg_eps]

theorem simpleRootB_mem_rootsB (i : Fin r) : simpleRootB r i ∈ rootsB r :=
  posRootsB_subset_rootsB (simpleRootB_mem_posRootsB i)

theorem tailLongElt_mem_tailRootGroup {α : Fin r → ℤ} (hα : α ∈ roots r) (t : K) :
    tailLongElt r (normForm T) α t ∈ tailRootGroup r (normForm T) α :=
  (mem_tailRootGroup_long hα).2 ⟨t, rfl⟩

theorem tailShortElt_eps_mem (i : Fin r) (a : L) :
    tailShortElt r (normForm T) (eps r i) a ∈ tailRootGroup r (normForm T) (eps r i) := by
  rw [tailShortElt_eps]
  exact mem_tailRootGroup_eps.2 ⟨a, rfl⟩

theorem tailShortElt_neg_eps_mem (i : Fin r) (a : L) :
    tailShortElt r (normForm T) (-eps r i) a ∈ tailRootGroup r (normForm T) (-eps r i) := by
  rw [tailShortElt_neg_eps]
  exact mem_tailRootGroup_neg_eps.2 ⟨a, rfl⟩

theorem map_conj_tailWeylElt_unipExcept_le (i : Fin r) :
    (tailUnipotentExcept r (normForm T) i).map
        (MulAut.conj (tailWeylElt r (normForm T) 1 i)).toMonoidHom ≤
      tailUnipotent r (normForm T) := by
  rw [tailUnipotentExcept, Subgroup.map_iSup]
  refine iSup_le fun β => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hβ => ?_
  have h := map_conj_tailRootGroup (normForm_anisotropic T) (one_ne_zero (α := L))
    ⟨tailWeylElt r (normForm T) 1 i, tailWeylElt_mem_tailTorusWeyl 1 i⟩
    (posRootsB_subset_rootsB hβ.1)
  rw [tailTorusWeylNu_tailWeylElt (normForm_anisotropic T) (one_ne_zero (α := L)) i] at h
  change (tailRootGroup r (normForm T) β).map
    (MulAut.conj (tailWeylElt r (normForm T) 1 i)).toMonoidHom = _ at h
  rw [h]
  exact tailRootGroup_le_tailUnipotent ((bijOn_simpleReflB i).mapsTo hβ).1

theorem tailWeylElt_last_inv {i : Fin r} (h : ¬i.val + 1 < r) :
    (tailWeylElt r (normForm T) 1 i)⁻¹ = tailWeylElt r (normForm T) 1 i := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [tailWeylElt_of_not_lt 1 h]
  exact shortWeyl_mul_self _ (tail_mem_perp_hypPairT _ 1)
    (by rw [quadTail_tail, normForm_one]; exact one_ne_zero)

variable [FiniteDimensional K L]

theorem conj_mem_tailUnipotent_of_mem_tailTorus
    {t u : ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × L)}
    (ht : t ∈ tailTorus r (normForm T)) (hu : u ∈ tailUnipotent r (normForm T)) :
    t * u * t⁻¹ ∈ tailUnipotent r (normForm T) := by
  have hN := tailUnipotent_normal (normForm_anisotropic T) (r := r)
  have hu' : (⟨u, tailUnipotent_le_tailBorel (normForm_anisotropic T) hu⟩ :
      tailBorel r (normForm T)) ∈ (tailUnipotent r (normForm T)).subgroupOf
        (tailBorel r (normForm T)) := hu
  exact hN.conj_mem _ hu' ⟨t, tailTorus_le_tailBorel ht⟩

theorem le_normalizer_tailUnipotent
    {S : Subgroup (((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × L))}
    (hS : S ≤ tailTorus r (normForm T)) :
    S ≤ Subgroup.normalizer (tailUnipotent r (normForm T) : Set _) := fun t ht =>
  mem_normalizer_of_conj (fun _ hu => conj_mem_tailUnipotent_of_mem_tailTorus T (hS ht) hu)
    (fun _ hu => by
      simpa using conj_mem_tailUnipotent_of_mem_tailTorus T (hS (inv_mem ht)) hu)

theorem coe_tailUnipotent_eq_mul (i : Fin r) :
    (tailUnipotent r (normForm T) :
      Set (((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × L))) =
      (tailRootGroup r (normForm T) (simpleRootB r i) :
        Set (((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × L))) *
        (tailUnipotentExcept r (normForm T) i :
          Set (((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × L))) :=
  ((orthogonal_geometry_tail_simple_positive_parameter_kernels (normForm_anisotropic T)
    (r := r)).2.2 i).2.2.2

end Matrices

variable {T : NormTailData K L} {r : ℕ} {E : Type*} [Group E] {π : E →* G0 T r}

section Images

variable [Finite E] (hS : TailHyp T π)
include hS

theorem coe_map_xPlusLong {i : Fin r} (h : i.val + 1 < r) (t : K) :
    ((π (xPlusLong π h t) : G0 T r) :
      ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × L)) =
        tailLongElt r (normForm T) (simpleRootB r i) t := by
  rw [xPlusLong, hS.coe_map_etaLift, eta_uSL_of_lt T h]

theorem coe_map_xMinusLong {i : Fin r} (h : i.val + 1 < r) (t : K) :
    ((π (xMinusLong π h t) : G0 T r) :
      ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × L)) =
        tailLongElt r (normForm T) (-simpleRootB r i) t := by
  rw [xMinusLong, hS.coe_map_etaLift, eta_vSL_of_lt T h]

theorem coe_map_xPlusShort (i : Fin r) (t : L) :
    ((π (xPlusShort π i t) : G0 T r) :
      ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × L)) =
        eichler (quadTail r (normForm T)) (hypVec K L (.inl i)) (0, -t) := by
  rw [xPlusShort, hS.coe_map_rhoLift, show uSL t = upperSL L t from rfl, rhoO_upperSL]

theorem coe_map_xMinusShort (i : Fin r) (t : L) :
    ((π (xMinusShort π i t) : G0 T r) :
      ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × L)) =
        eichler (quadTail r (normForm T)) (hypVec K L (.inr i)) (0, T.bar t) := by
  rw [xMinusShort, hS.coe_map_rhoLift, show vSL t = lowerSL L t from rfl, rhoO_lowerSL]

theorem coe_map_xPlusShort_eq_tailShortElt (i : Fin r) (t : L) :
    ((π (xPlusShort π i t) : G0 T r) :
      ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × L)) =
        tailShortElt r (normForm T) (eps r i) (-t) := by
  rw [xPlusShort, hS.coe_map_rhoLift, rhoO_uSL]

theorem coe_map_xMinusShort_eq_tailShortElt (i : Fin r) (t : L) :
    ((π (xMinusShort π i t) : G0 T r) :
      ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × L)) =
        tailShortElt r (normForm T) (-eps r i) (T.bar t) := by
  rw [xMinusShort, hS.coe_map_rhoLift, rhoO_vSL]

theorem coe_map_sLift_eq_inv (i : Fin r) :
    ((π (sLift T π i) : G0 T r) :
      ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × L)) =
        (tailWeylElt r (normForm T) 1 i)⁻¹ := by
  by_cases h : i.val + 1 < r
  · exact coe_map_sLift_of_lt hS h
  · rw [coe_map_sLift_of_not_lt hS h, tailWeylElt_last_inv T h]

end Images

section Lifts

variable [Finite K] [FiniteDimensional K L] [Finite E] [Fact (ringChar K).Prime]

omit [Fact (ringChar K).Prime] in
theorem isPGroup_unipG : IsPGroup (ringChar K) (unipG T r) := by
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K (ringChar K)
  refine IsPGroup.of_card (n := n * (r * (r - 1) + r * Module.finrank K L)) ?_
  rw [unipG, Nat.card_congr (Subgroup.subgroupOfEquivOfLe tailUnipotent_le).toEquiv,
    card_tailUnipotent (normForm_anisotropic T), Nat.card_eq_fintype_card, hn, ← pow_mul]

omit [Finite K] [FiniteDimensional K L] [Finite E] [Fact (ringChar K).Prime] in
theorem unipExceptG_le_unipG (i : Fin r) : unipExceptG T r i ≤ unipG T r :=
  fun _ hx => tailUnipotentExcept_le i hx

omit [Fact (ringChar K).Prime] in
theorem isPGroup_unipExceptG (i : Fin r) : IsPGroup (ringChar K) (unipExceptG T r i) :=
  isPGroup_unipG.to_le (unipExceptG_le_unipG i)

omit [Finite K] [FiniteDimensional K L] [Finite E] in
theorem exists_orderOf_map_uSL_L (φ : SpecialLinearGroup (Fin 2) L →* E) (t : L) :
    ∃ n : ℕ, orderOf (φ (uSL t)) = ringChar K ^ n := by
  have : Fact (ringChar L).Prime := ⟨by rw [← Algebra.ringChar_eq K L]; exact Fact.out⟩
  rw [Algebra.ringChar_eq K L]
  exact exists_orderOf_map_uSL φ t

omit [Finite K] [FiniteDimensional K L] [Finite E] in
theorem exists_orderOf_map_vSL_L (φ : SpecialLinearGroup (Fin 2) L →* E) (t : L) :
    ∃ n : ℕ, orderOf (φ (vSL t)) = ringChar K ^ n := by
  have : Fact (ringChar L).Prime := ⟨by rw [← Algebra.ringChar_eq K L]; exact Fact.out⟩
  rw [Algebra.ringChar_eq K L]
  exact exists_orderOf_map_vSL φ t

variable (hS : TailHyp T π)
include hS

theorem mem_liftUnip_of {x : E}
    (hx : ((π x : G0 T r) : ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × L)) ∈
      tailUnipotent r (normForm T))
    (hn : ∃ n : ℕ, orderOf x = ringChar K ^ n) : x ∈ liftUnip π :=
  mem_liftSubgroup_of hS.ext.cen isPGroup_unipG hx hn

theorem xPlusLong_mem_liftUnip {i : Fin r} (h : i.val + 1 < r) (t : K) :
    xPlusLong π h t ∈ liftUnip π := by
  refine mem_liftUnip_of hS ?_ (exists_orderOf_map_uSL _ t)
  rw [coe_map_xPlusLong hS h]
  exact tailRootGroup_le_tailUnipotent (simpleRootB_mem_posRootsB i)
    (tailLongElt_mem_tailRootGroup T (posRoots_subset_roots (simpleRootB_mem_posRoots_of_lt h)) t)

theorem xPlusShort_mem_liftUnip {i : Fin r} (h : ¬i.val + 1 < r) (t : L) :
    xPlusShort π i t ∈ liftUnip π := by
  refine mem_liftUnip_of hS ?_ (exists_orderOf_map_uSL_L _ t)
  rw [coe_map_xPlusShort_eq_tailShortElt hS]
  have hα := simpleRootB_mem_posRootsB (r := r) i
  rw [simpleRootB_of_not_lt h] at hα
  exact tailRootGroup_le_tailUnipotent hα (tailShortElt_eps_mem T i _)

theorem liftTorus_le_normalizer_liftUnip :
    liftTorus T π ≤ Subgroup.normalizer (liftUnip π : Set E) := by
  have key : ∀ e ∈ liftTorus T π, ∀ x ∈ liftUnip π, e * x * e⁻¹ ∈ liftUnip π :=
    fun e he x hx => conj_mem_liftSubgroup hS.ext.cen isPGroup_unipG isPGroup_unipG
      (fun u hu => by
        change ((π e * u * (π e)⁻¹ : G0 T r) :
          ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × L)) ∈
            tailUnipotent r (normForm T)
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
        exact conj_mem_tailUnipotent_of_mem_tailTorus T (coe_map_mem_tailTorus hS he) hu) hx
  exact fun h hh => mem_normalizer_of_conj (key h hh) (fun x hx => by
    simpa using key h⁻¹ (inv_mem hh) x hx)

theorem coe_liftBorel :
    (liftBorel π : Set E) = (liftUnip π : Set E) * (liftTorus T π : Set E) :=
  Subgroup.coe_mul_of_right_le_normalizer_left _ _ (liftTorus_le_normalizer_liftUnip hS)

theorem mem_liftBorel_iff {x : E} :
    x ∈ liftBorel π ↔ ∃ u ∈ liftUnip π, ∃ h ∈ liftTorus T π, x = u * h := by
  rw [← SetLike.mem_coe, coe_liftBorel hS, Set.mem_mul]
  exact ⟨fun ⟨u, hu, h, hh, e⟩ => ⟨u, hu, h, hh, e.symm⟩,
    fun ⟨u, hu, h, hh, e⟩ => ⟨u, hu, h, hh, e.symm⟩⟩

theorem sLift_inv_conj_mem_liftUnip (i : Fin r) {x : E} (hx : x ∈ liftUnipExcept π i) :
    (sLift T π i)⁻¹ * x * sLift T π i ∈ liftUnip π := by
  have h := conj_mem_liftSubgroup hS.ext.cen (isPGroup_unipExceptG i) isPGroup_unipG
    (e := (sLift T π i)⁻¹) (fun u hu => by
      change (((π (sLift T π i)⁻¹ * u * (π (sLift T π i)⁻¹)⁻¹ : G0 T r)) :
        ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × L)) ∈
          tailUnipotent r (normForm T)
      simp only [Subgroup.coe_mul, map_inv, Subgroup.coe_inv, inv_inv]
      rw [coe_map_sLift_eq_inv hS i, inv_inv]
      exact map_conj_tailWeylElt_unipExcept_le T i ⟨_, hu, rfl⟩) hx
  rwa [inv_inv] at h

theorem conj_mem_liftUnip_of_root {v : E} (hv : v ∈ liftWeyl T π) {β : Fin r → ℤ}
    (hβ : β ∈ rootsB r) {y : E}
    (hy : ((π y : G0 T r) : ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × L)) ∈
      tailRootGroup r (normForm T) β)
    (hn : ∃ n : ℕ, orderOf y = ringChar K ^ n)
    (hpos : ((weylHom hS ⟨v, hv⟩ : weylGroupB r) : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) β ∈
      posRootsB r) :
    v * y * v⁻¹ ∈ liftUnip π := by
  refine mem_liftUnip_of hS ?_ (exists_orderOf_conj v hn)
  have h := map_conj_tailRootGroup_weylHom hS ⟨v, hv⟩ hβ
  refine tailRootGroup_le_tailUnipotent hpos ?_
  rw [← h]
  refine ⟨_, hy, ?_⟩
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_mul, map_inv, Subgroup.coe_mul,
    Subgroup.coe_mul, Subgroup.coe_inv]

theorem conj_xLong_mem {v : E} (hv : v ∈ liftWeyl T π) {i : Fin r} (h : i.val + 1 < r) :
    (∀ t : K, v * xPlusLong π h t * v⁻¹ ∈ liftUnip π) ∨
      ∀ t : K, v * xMinusLong π h t * v⁻¹ ∈ liftUnip π := by
  have hα := simpleRootB_mem_rootsB (r := r) i
  have hlong : simpleRootB r i ∈ roots r :=
    posRoots_subset_roots (simpleRootB_mem_posRoots_of_lt h)
  set w := weylHom hS ⟨v, hv⟩
  rcases (mem_posRootsB_or_neg_mem_posRootsB (apply_mem_rootsB w.2 hα)).1 with hpos | hneg
  · left
    intro t
    refine conj_mem_liftUnip_of_root hS hv hα ?_ (exists_orderOf_map_uSL _ t) hpos
    rw [coe_map_xPlusLong hS h]
    exact tailLongElt_mem_tailRootGroup T hlong t
  · right
    intro t
    refine conj_mem_liftUnip_of_root hS hv (neg_mem_rootsB hα) ?_
      (exists_orderOf_map_vSL _ t) (by rw [map_neg]; exact hneg)
    rw [coe_map_xMinusLong hS h]
    exact tailLongElt_mem_tailRootGroup T (neg_mem_roots hlong) t

theorem conj_xShort_mem {v : E} (hv : v ∈ liftWeyl T π) {i : Fin r} (h : ¬i.val + 1 < r) :
    (∀ t : L, v * xPlusShort π i t * v⁻¹ ∈ liftUnip π) ∨
      ∀ t : L, v * xMinusShort π i t * v⁻¹ ∈ liftUnip π := by
  have hα := simpleRootB_mem_rootsB (r := r) i
  rw [simpleRootB_of_not_lt h] at hα
  set w := weylHom hS ⟨v, hv⟩
  rcases (mem_posRootsB_or_neg_mem_posRootsB (apply_mem_rootsB w.2 hα)).1 with hpos | hneg
  · left
    intro t
    refine conj_mem_liftUnip_of_root hS hv hα ?_ (exists_orderOf_map_uSL_L _ t) hpos
    rw [coe_map_xPlusShort_eq_tailShortElt hS]
    exact tailShortElt_eps_mem T i _
  · right
    intro t
    refine conj_mem_liftUnip_of_root hS hv (neg_mem_rootsB hα) ?_
      (exists_orderOf_map_vSL_L _ t) (by rw [map_neg]; exact hneg)
    rw [coe_map_xMinusShort_eq_tailShortElt hS]
    exact tailShortElt_neg_eps_mem T i _

theorem mem_liftUnipExcept_of {i : Fin r} {x u : E} (hx : x ∈ liftUnip π) (hu : u ∈ liftUnip π)
    (hxu : ((π (x⁻¹ * u) : G0 T r) :
      ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × L)) ∈
        tailUnipotentExcept r (normForm T) i) : x⁻¹ * u ∈ liftUnipExcept π i := by
  have hmem : x⁻¹ * u ∈ liftUnip π := mul_mem (inv_mem hx) hu
  obtain ⟨-, hn⟩ := (mem_liftSubgroup_iff hS.ext.cen isPGroup_unipG).1 hmem
  exact mem_liftSubgroup_of hS.ext.cen (isPGroup_unipExceptG i) hxu hn

theorem mem_liftBorel_iff_xPlusLong {i : Fin r} (h : i.val + 1 < r) {x : E} :
    x ∈ liftBorel π ↔
      ∃ t : K, ∃ u ∈ liftUnipExcept π i, ∃ g ∈ liftTorus T π, x = xPlusLong π h t * u * g := by
  constructor
  · intro hx
    obtain ⟨u, hu, g, hg, rfl⟩ := (mem_liftBorel_iff hS).1 hx
    have huU : ((π u : G0 T r) :
        ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × L)) ∈
          tailUnipotent r (normForm T) :=
      liftSubgroup_le_comap hS.ext.cen isPGroup_unipG hu
    rw [← SetLike.mem_coe, coe_tailUnipotent_eq_mul T i, Set.mem_mul] at huU
    obtain ⟨y, hy, u', hu', hyu⟩ := huU
    obtain ⟨t, rfl⟩ := (mem_tailRootGroup_long
      (posRoots_subset_roots (simpleRootB_mem_posRoots_of_lt h))).1 hy
    refine ⟨t, (xPlusLong π h t)⁻¹ * u, mem_liftUnipExcept_of hS
      (xPlusLong_mem_liftUnip hS h t) hu ?_, g, hg, by group⟩
    rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, coe_map_xPlusLong hS h, ← hyu,
      inv_mul_cancel_left]
    exact hu'
  · rintro ⟨t, u, hu, g, hg, rfl⟩
    refine mul_mem (mul_mem (Subgroup.mem_sup_left (xPlusLong_mem_liftUnip hS h t))
      (Subgroup.mem_sup_left ?_)) (Subgroup.mem_sup_right hg)
    exact liftSubgroup_mono hS.ext.cen isPGroup_unipG (unipExceptG_le_unipG i) hu

theorem mem_liftBorel_iff_xPlusShort {i : Fin r} (h : ¬i.val + 1 < r) {x : E} :
    x ∈ liftBorel π ↔
      ∃ t : L, ∃ u ∈ liftUnipExcept π i, ∃ g ∈ liftTorus T π, x = xPlusShort π i t * u * g := by
  constructor
  · intro hx
    obtain ⟨u, hu, g, hg, rfl⟩ := (mem_liftBorel_iff hS).1 hx
    have huU : ((π u : G0 T r) :
        ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × L)) ∈
          tailUnipotent r (normForm T) :=
      liftSubgroup_le_comap hS.ext.cen isPGroup_unipG hu
    rw [← SetLike.mem_coe, coe_tailUnipotent_eq_mul T i, Set.mem_mul,
      simpleRootB_of_not_lt h] at huU
    obtain ⟨y, hy, u', hu', hyu⟩ := huU
    obtain ⟨a, rfl⟩ := mem_tailRootGroup_eps.1 hy
    refine ⟨-a, (xPlusShort π i (-a))⁻¹ * u, mem_liftUnipExcept_of hS
      (xPlusShort_mem_liftUnip hS h _) hu ?_, g, hg, by group⟩
    rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, coe_map_xPlusShort hS, neg_neg,
      ← hyu, inv_mul_cancel_left]
    exact hu'
  · rintro ⟨t, u, hu, g, hg, rfl⟩
    refine mul_mem (mul_mem (Subgroup.mem_sup_left (xPlusShort_mem_liftUnip hS h t))
      (Subgroup.mem_sup_left ?_)) (Subgroup.mem_sup_right hg)
    exact liftSubgroup_mono hS.ext.cen isPGroup_unipG (unipExceptG_le_unipG i) hu

variable (hC : ¬ringChar K ∣ Nat.card π.ker)
include hC

theorem coe_map_liftBorel :
    ((liftBorel π).map ((orthElementaryGroup (quadTail r (normForm T))).subtype.comp π) :
      Set (((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × L))) =
      (tailUnipotent r (normForm T) : Set _) *
        ((liftTorus T π).map ((orthElementaryGroup (quadTail r (normForm T))).subtype.comp π) :
          Set _) := by
  have h1 : (liftUnip π).map ((orthElementaryGroup (quadTail r (normForm T))).subtype.comp π) =
      tailUnipotent r (normForm T) := by
    rw [← Subgroup.map_map, liftUnip, map_liftSubgroup hS.ext.cen hS.ext.surj hC isPGroup_unipG,
      unipG, Subgroup.subgroupOf_map_subtype, inf_of_le_left tailUnipotent_le]
  rw [liftBorel, Subgroup.map_sup, h1]
  refine Subgroup.coe_mul_of_right_le_normalizer_left _ _ (le_normalizer_tailUnipotent T ?_)
  rintro _ ⟨x, hx, rfl⟩
  exact coe_map_mem_tailTorus hS hx

omit hC in
theorem map_liftBorel_le :
    (liftBorel π).map ((orthElementaryGroup (quadTail r (normForm T))).subtype.comp π) ≤
      tailBorel r (normForm T) := by
  rw [liftBorel, Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact tailUnipotent_le_tailBorel (normForm_anisotropic T)
      (liftSubgroup_le_comap hS.ext.cen isPGroup_unipG hx)
  · rintro _ ⟨x, hx, rfl⟩
    exact tailTorus_le_tailBorel (coe_map_mem_tailTorus hS hx)

theorem liftBorel_inf_ker (hr : 2 ≤ r) :
    liftBorel π ⊓ π.ker = Subgroup.zpowers (tauLift T π ⟨r - 1, by omega⟩ (-1)) := by
  rw [← liftTorus_inf_ker hS hr]
  refine le_antisymm (fun x hx => ?_) (inf_le_inf_right _ le_sup_right)
  obtain ⟨hxB, hxK⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨u, hu, h, hh, rfl⟩ := (mem_liftBorel_iff hS).1 hxB
  have h1 : π u = (π h)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← map_mul]; exact hxK)
  have hmem : ((π u : G0 T r) :
      ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × L)) ∈
        tailTorus r (normForm T) ⊓ tailUnipotent r (normForm T) := by
    refine Subgroup.mem_inf.2 ⟨?_, liftSubgroup_le_comap hS.ext.cen isPGroup_unipG hu⟩
    rw [h1, Subgroup.coe_inv]
    exact inv_mem (coe_map_mem_tailTorus hS hh)
  rw [tailTorus_inf_tailUnipotent (normForm_anisotropic T), Subgroup.mem_bot] at hmem
  have hu1 : u = 1 := eq_one_of_mem_liftSubgroup_of_mem_ker hS.ext.cen hC isPGroup_unipG hu
    (Subtype.ext hmem)
  rw [hu1, one_mul] at hxK ⊢
  exact Subgroup.mem_inf.2 ⟨hh, hxK⟩

theorem injective_pi_liftBorel (hr : 2 ≤ r) :
    Function.Injective (π.comp (liftBorel π).subtype) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hmem : (x : E) ∈ liftBorel π ⊓ π.ker := Subgroup.mem_inf.2 ⟨x.2, hx⟩
  rw [liftBorel_inf_ker hS hC hr, tauLift_neg_one_eq_one hS, Subgroup.zpowers_one_eq_bot,
    Subgroup.mem_bot] at hmem
  exact Subtype.ext hmem

end Lifts


theorem odd_orthogonal_tail_cross_characteristic_central_prime_triangular_factorization
    {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L] (hK : ringChar K ≠ 2)
    (T : NormTailData K L) (hm : Module.finrank K L = 1 ∨ Module.finrank K L = 2) {r : ℕ}
    (hr : 3 ≤ r) {E : Type*} [Group E] [Finite E] {π : E →* G0 T r} {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpℓ : p ≠ ringChar K) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hpk : IsPGroup p π.ker) :
    (∀ P : Sylow (ringChar K) ((unipG T r).comap π),
      (P : Subgroup ((unipG T r).comap π)).map ((unipG T r).comap π).subtype = liftUnip π) ∧
    liftTorus T π ≤ Subgroup.normalizer (liftUnip π : Set E) ∧
    (liftBorel π : Set E) = (liftUnip π : Set E) * (liftTorus T π : Set E) ∧
    ((liftBorel π).map ((orthElementaryGroup (quadTail r (normForm T))).subtype.comp π) :
      Set (((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × L))) =
      (tailUnipotent r (normForm T) : Set _) *
        ((liftTorus T π).map ((orthElementaryGroup (quadTail r (normForm T))).subtype.comp π) :
          Set _) ∧
    (liftBorel π).map ((orthElementaryGroup (quadTail r (normForm T))).subtype.comp π) ≤
      tailBorel r (normForm T) ∧
    liftBorel π ⊓ π.ker = Subgroup.zpowers (tauLift T π ⟨r - 1, by omega⟩ (-1)) ∧
    tauLift T π ⟨r - 1, by omega⟩ (-1) = 1 ∧
    Function.Injective (π.comp (liftBorel π).subtype) ∧
    (∀ i : Fin r, ∀ P : Sylow (ringChar K) ((unipExceptG T r i).comap π),
      (P : Subgroup ((unipExceptG T r i).comap π)).map ((unipExceptG T r i).comap π).subtype =
        liftUnipExcept π i) ∧
    (∀ i : Fin r, ∀ x ∈ liftUnipExcept π i, (sLift T π i)⁻¹ * x * sLift T π i ∈ liftUnip π) ∧
    (∀ (i : Fin r) (h : i.val + 1 < r),
      (∀ t : K, ((π (xPlusLong π h t) : G0 T r) :
        ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × L)) =
          tailLongElt r (normForm T) (simpleRootB r i) t) ∧
      (∀ t : K, ((π (xMinusLong π h t) : G0 T r) :
        ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × L)) =
          tailLongElt r (normForm T) (-simpleRootB r i) t) ∧
      (∀ x : E, x ∈ liftBorel π ↔ ∃ t : K, ∃ u ∈ liftUnipExcept π i, ∃ g ∈ liftTorus T π,
        x = xPlusLong π h t * u * g) ∧
      (∀ (t : K) (ht : t ≠ 0), xPlusLong π h t * sLift T π i =
          xMinusLong π h t⁻¹ * etaLift T π (ne_succ_of_lt h) (sl2Diag (Units.mk0 t ht)) *
            xPlusLong π h (-t⁻¹) ∧
        etaLift T π (ne_succ_of_lt h) (sl2Diag (Units.mk0 t ht)) ∈ liftTorus T π) ∧
      ∀ v ∈ liftWeyl T π, (∀ t : K, v * xPlusLong π h t * v⁻¹ ∈ liftUnip π) ∨
        ∀ t : K, v * xMinusLong π h t * v⁻¹ ∈ liftUnip π) ∧
    (∀ t : L, ((π (xPlusShort π ⟨r - 1, by omega⟩ t) : G0 T r) :
      ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × L)) =
        eichler (quadTail r (normForm T)) (hypVec K L (.inl ⟨r - 1, by omega⟩)) (0, -t)) ∧
    (∀ t : L, ((π (xMinusShort π ⟨r - 1, by omega⟩ t) : G0 T r) :
      ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × L)) =
        eichler (quadTail r (normForm T)) (hypVec K L (.inr ⟨r - 1, by omega⟩)) (0, T.bar t)) ∧
    (∀ x : E, x ∈ liftBorel π ↔ ∃ t : L, ∃ u ∈ liftUnipExcept π ⟨r - 1, by omega⟩,
      ∃ g ∈ liftTorus T π, x = xPlusShort π ⟨r - 1, by omega⟩ t * u * g) ∧
    (∀ (t : L) (ht : t ≠ 0), xPlusShort π ⟨r - 1, by omega⟩ t * sLift T π ⟨r - 1, by omega⟩ =
        xMinusShort π ⟨r - 1, by omega⟩ t⁻¹ *
          rhoLift T π ⟨r - 1, by omega⟩ (sl2Diag (Units.mk0 t ht)) *
          xPlusShort π ⟨r - 1, by omega⟩ (-t⁻¹) ∧
      rhoLift T π ⟨r - 1, by omega⟩ (sl2Diag (Units.mk0 t ht)) ∈ liftTorus T π) ∧
    ∀ v ∈ liftWeyl T π, (∀ t : L, v * xPlusShort π ⟨r - 1, by omega⟩ t * v⁻¹ ∈ liftUnip π) ∨
      ∀ t : L, v * xMinusShort π ⟨r - 1, by omega⟩ t * v⁻¹ ∈ liftUnip π := by
  have hpos : 0 < Module.finrank K L := by rcases hm with h | h <;> omega
  have : Module.Finite K L := Module.finite_of_finrank_pos hpos
  have hL : Finite L := Module.finite_of_finite K
  have := Fintype.ofFinite K
  obtain ⟨n, hℓ, -⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hr2 : 2 ≤ r := by omega
  have hS : TailHyp T π := ⟨hK, ⟨hπ, hcen, ⟨p, hp, hp3, hpk⟩⟩, inferInstance, hL⟩
  have hC : ¬ringChar K ∣ Nat.card π.ker := by
    obtain ⟨m, hm⟩ := hpk.exists_card_dvd_pow
    intro hdvd
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).1 (hℓ.dvd_of_dvd_pow (hdvd.trans hm))).symm
  have hlast : ¬(⟨r - 1, by omega⟩ : Fin r).val + 1 < r := by simp only; omega
  refine ⟨sylow_map_eq_liftSubgroup hcen isPGroup_unipG, liftTorus_le_normalizer_liftUnip hS,
    coe_liftBorel hS, coe_map_liftBorel hS hC, map_liftBorel_le hS, liftBorel_inf_ker hS hC hr2,
    tauLift_neg_one_eq_one hS _, injective_pi_liftBorel hS hC hr2,
    fun i => sylow_map_eq_liftSubgroup hcen (isPGroup_unipExceptG i),
    fun i x hx => sLift_inv_conj_mem_liftUnip hS i hx, fun i h =>
      ⟨coe_map_xPlusLong hS h, coe_map_xMinusLong hS h, fun x => mem_liftBorel_iff_xPlusLong hS h,
        fun t ht => ⟨xPlusLong_mul_sLift π h ht, hLift_mem T π _ _⟩,
        fun v hv => conj_xLong_mem hS hv h⟩,
    coe_map_xPlusShort hS _, coe_map_xMinusShort hS _,
    fun x => mem_liftBorel_iff_xPlusShort hS hlast,
    fun t ht => ⟨xPlusShort_mul_sLift π hlast ht, tauLift_mem T π _ _⟩,
    fun v hv => conj_xShort_mem hS hv hlast⟩

end CFSG.RankThree.CentralLiftSO.TailO

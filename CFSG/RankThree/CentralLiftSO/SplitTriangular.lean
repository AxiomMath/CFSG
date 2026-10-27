module

public import CFSG.RankThree.CentralLiftSO.CanonicalLift
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryPositive
public import CFSG.RankThree.CentralLiftSO.SplitWeyl

public section

namespace CFSG.RankThree.CentralLiftSO.SplitO

open Matrix CFSG.LieType.CentralExt CFSG.LieType.Universal.Spin CFSG.RankThree.CentralLift
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.LocalAnalysis.ComponentInitial (orthElementaryGroup)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (sl2Diag sl2W)
open CFSG.LieType.Chevalley (uSL vSL coe_uSL coe_vSL)
open CFSG.RankThree.CentralLiftSO.Lift
open scoped Pointwise

section Defs

variable (r : ℕ) (k : Type) [Field k]

@[expose] noncomputable def unipG : Subgroup (orthElementaryGroup (quadPlus r k)) :=
  (unipotent r k).subgroupOf (orthElementaryGroup (quadPlus r k))

@[expose] noncomputable def unipExceptG (i : Fin r) :
    Subgroup (orthElementaryGroup (quadPlus r k)) :=
  (unipotentExcept r k i).subgroupOf (orthElementaryGroup (quadPlus r k))

variable {r k} {E : Type*} [Group E] (π : E →* orthElementaryGroup (quadPlus r k))

@[expose] noncomputable def liftUnip : Subgroup E := liftSubgroup (ringChar k) π (unipG r k)

@[expose] noncomputable def liftUnipExcept (i : Fin r) : Subgroup E :=
  liftSubgroup (ringChar k) π (unipExceptG r k i)

@[expose] noncomputable def liftBorel : Subgroup E := liftUnip π ⊔ liftTorus π

@[expose] noncomputable def xPlus (i : Fin r) (t : k) : E := simpleLift π i (uSL t)

@[expose] noncomputable def xMinus (i : Fin r) (t : k) : E := simpleLift π i (vSL t)

theorem xPlus_mul_sLift (i : Fin r) {t : k} (ht : t ≠ 0) :
    xPlus π i t * sLift π i =
      xMinus π i t⁻¹ * hSimple π i (Units.mk0 t ht) * xPlus π i (-t⁻¹) := by
  rw [xPlus, sLift, ← map_mul, uSL_mul_sl2W ht, map_mul, map_mul]
  rfl

end Defs

section Matrices

variable {r : ℕ} {k : Type} [Field k]

theorem conj_mem_unipotent_of_mem_posBorel {t u : (Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k)}
    (ht : t ∈ posBorel r k) (hu : u ∈ unipotent r k) : t * u * t⁻¹ ∈ unipotent r k := by
  rw [unipotent_eq_posUnip] at hu ⊢
  exact (posUnip_normal (r := r) (K := k)).conj_mem ⟨u, posUnip_le_posBorel hu⟩ hu ⟨t, ht⟩

theorem torus_le_posBorel : torus r k ≤ posBorel r k :=
  fun _ ht => borel_le_posBorel (torus_le_borel ht)

theorem sqTorus_le_posBorel : sqTorus r k ≤ posBorel r k := by
  rintro _ ⟨a, rfl, -⟩
  exact torusElt_mem_posBorel a

theorem le_normalizer_unipotent {T : Subgroup ((Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k))}
    (hT : T ≤ posBorel r k) : T ≤ Subgroup.normalizer (unipotent r k : Set _) := fun t ht =>
  mem_normalizer_of_conj (fun _ hu => conj_mem_unipotent_of_mem_posBorel (hT ht) hu)
    (fun _ hu => by
      simpa using conj_mem_unipotent_of_mem_posBorel (hT (inv_mem ht)) hu)

theorem unipotent_inf_torus : unipotent r k ⊓ torus r k = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hU, -, d, rfl⟩
  rw [unipotent_eq_posUnip] at hU
  have hd := (mem_posUnip.1 hU).2
  have h1 : d = 1 := by
    funext i
    apply Units.ext
    have := hd i
    rw [LinearMap.toMatrix'_apply, LinearEquiv.coe_coe, torusElt_apply] at this
    simpa using this
  rw [h1, map_one]
  exact one_mem _

theorem simpleRoot_mem_roots (hr : 2 ≤ r) (i : Fin r) : simpleRoot r i ∈ roots r :=
  posRoots_subset_roots (simpleRoot_mem_posRoots hr i)

theorem etaLin_uSL_of_lt {i : Fin r} (h : i.val + 1 < r) (t : k) :
    etaLin (coordIdx_inl_ne (ne_succ_of_lt h)) (uSL t) = rootElt r k (simpleRoot r i) t := by
  have hlt : i < ⟨i.val + 1, h⟩ := Fin.lt_def.2 (by simp)
  rw [simpleRoot, dite_eq_left h, rootElt_eps_sub_eps' hlt, etaLin_of_upper _ (coe_uSL t)]
  rfl

theorem etaLin_vSL_of_lt {i : Fin r} (h : i.val + 1 < r) (t : k) :
    etaLin (coordIdx_inl_ne (ne_succ_of_lt h)) (vSL t) = rootElt r k (-simpleRoot r i) t := by
  have hlt : i < ⟨i.val + 1, h⟩ := Fin.lt_def.2 (by simp)
  have hneg : -(eps r i - eps r ⟨i.val + 1, h⟩) = -eps r i + eps r ⟨i.val + 1, h⟩ := by abel
  rw [simpleRoot, dite_eq_left h, hneg, rootElt_neg_eps_add_eps' hlt,
    etaLin_of_lower _ (coe_vSL t)]
  rfl

theorem etaLin_uSL_of_not_lt {i : Fin r} (h : ¬i.val + 1 < r) (h' : 1 ≤ i.val) (t : k) :
    etaLin (coordIdx_inl_inr_ne (pred_ne_of_one_le h')) (uSL t) =
      rootElt r k (simpleRoot r i) t := by
  have hlt : (⟨r - 2, by omega⟩ : Fin r) < i := Fin.lt_def.2 (by simp; omega)
  have hp : (⟨i.val - 1, by omega⟩ : Fin r) = ⟨r - 2, by omega⟩ := Fin.ext (by simp; omega)
  rw [simpleRoot, dite_eq_right h, rootElt_eps_add_eps' hlt, etaLin_of_upper _ (coe_uSL t), hp]
  rfl

theorem etaLin_vSL_of_not_lt {i : Fin r} (h : ¬i.val + 1 < r) (h' : 1 ≤ i.val) (t : k) :
    etaLin (coordIdx_inl_inr_ne (pred_ne_of_one_le h')) (vSL t) =
      rootElt r k (-simpleRoot r i) t := by
  have hlt : (⟨r - 2, by omega⟩ : Fin r) < i := Fin.lt_def.2 (by simp; omega)
  have hp : (⟨i.val - 1, by omega⟩ : Fin r) = ⟨r - 2, by omega⟩ := Fin.ext (by simp; omega)
  have hneg : -(eps r ⟨r - 2, by omega⟩ + eps r i) = -eps r ⟨r - 2, by omega⟩ - eps r i := by
    abel
  rw [simpleRoot, dite_eq_right h, hneg, rootElt_neg_eps_sub_eps' hlt,
    etaLin_of_lower _ (coe_vSL t), hp]
  rfl

end Matrices

variable {r : ℕ} {k : Type} [Field k] {E : Type*} [Group E]
  {π : E →* orthElementaryGroup (quadPlus r k)}

theorem simpleLift_of_lt {i : Fin r} (h : i.val + 1 < r) :
    simpleLift π i = sl2Lift π (eta (k := k) (coordIdx_inl_ne (ne_succ_of_lt h))) := by
  rw [simpleLift, dite_eq_left h]
  rfl

theorem simpleLift_of_not_lt {i : Fin r} (h : ¬i.val + 1 < r) (h' : 1 ≤ i.val) :
    simpleLift π i = sl2Lift π (eta (k := k) (coordIdx_inl_inr_ne (pred_ne_of_one_le h'))) := by
  rw [simpleLift, dite_eq_right h, dite_eq_left h', etaPlusLift, etaPlus_eq]

theorem epsilon_eq_hSimple (hr : 3 ≤ r) :
    hMinus π ⟨r - 2, by omega⟩ ⟨r - 1, by omega⟩ (Fin.ne_of_val_ne (by simp; omega)) (-1) *
      hPlus π ⟨r - 2, by omega⟩ ⟨r - 1, by omega⟩ (Fin.ne_of_val_ne (by simp; omega)) (-1) =
    hSimple π ⟨r - 2, by omega⟩ (-1) * hSimple π ⟨r - 1, by omega⟩ (-1) := by
  have e1 : hSimple π ⟨r - 2, by omega⟩ (-1) =
      hMinus π ⟨r - 2, by omega⟩ ⟨r - 1, by omega⟩ (Fin.ne_of_val_ne (by simp; omega)) (-1) := by
    rw [hSimple_of_lt (by simp; omega)]
    congr 1
    exact Fin.ext (by simp; omega)
  have e2 : hSimple π ⟨r - 1, by omega⟩ (-1) =
      hPlus π ⟨r - 2, by omega⟩ ⟨r - 1, by omega⟩ (Fin.ne_of_val_ne (by simp; omega)) (-1) := by
    rw [hSimple_of_not_lt (by simp; omega) (by simp; omega)]
    exact hPlus_congr_left (Fin.ext (by simp; omega)) _ _ _
  rw [e1, e2]

variable [Finite k] [Finite E]

section Images

variable (hS : LargeHyp π)
include hS

theorem coe_pi_xPlus (hr : 2 ≤ r) (i : Fin r) (t : k) :
    ((π (xPlus π i t) : orthElementaryGroup (quadPlus r k)) :
      (Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k)) = rootElt r k (simpleRoot r i) t := by
  by_cases h : i.val + 1 < r
  · rw [xPlus, simpleLift_of_lt h, hS.map_lift, coe_eta, etaLin_uSL_of_lt h]
  · rw [xPlus, simpleLift_of_not_lt h (by omega), hS.map_lift, coe_eta,
      etaLin_uSL_of_not_lt h (by omega)]

theorem coe_pi_xMinus (hr : 2 ≤ r) (i : Fin r) (t : k) :
    ((π (xMinus π i t) : orthElementaryGroup (quadPlus r k)) :
      (Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k)) = rootElt r k (-simpleRoot r i) t := by
  by_cases h : i.val + 1 < r
  · rw [xMinus, simpleLift_of_lt h, hS.map_lift, coe_eta, etaLin_vSL_of_lt h]
  · rw [xMinus, simpleLift_of_not_lt h (by omega), hS.map_lift, coe_eta,
      etaLin_vSL_of_not_lt h (by omega)]

end Images

section Lifts

theorem isPGroup_unipG : IsPGroup (ringChar k) (unipG r k) := by
  have := Fintype.ofFinite k
  obtain ⟨n, -, hn⟩ := FiniteField.card k (ringChar k)
  refine IsPGroup.of_card (n := n * (r * (r - 1))) ?_
  rw [unipG, Nat.card_congr (Subgroup.subgroupOfEquivOfLe unipotent_le).toEquiv,
    unipotent_eq_posUnip, card_posUnip, Nat.card_eq_fintype_card, hn, ← pow_mul]

omit [Finite k] in
theorem unipExceptG_le_unipG (i : Fin r) : unipExceptG r k i ≤ unipG r k :=
  fun _ hx => unipotentExcept_le_unipotent i hx

theorem isPGroup_unipExceptG (i : Fin r) : IsPGroup (ringChar k) (unipExceptG r k i) :=
  isPGroup_unipG.to_le (unipExceptG_le_unipG i)

variable [Fact (ringChar k).Prime] (hS : LargeHyp π)
include hS

theorem xPlus_mem_liftUnip (hr : 2 ≤ r) (i : Fin r) (t : k) : xPlus π i t ∈ liftUnip π := by
  refine mem_liftSubgroup_of hS.ext.cen isPGroup_unipG ?_ (exists_orderOf_map_uSL _ t)
  change ((π (xPlus π i t) : orthElementaryGroup (quadPlus r k)) :
    (Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k)) ∈ unipotent r k
  rw [coe_pi_xPlus hS hr]
  exact rootSubgroup_le_unipotent (simpleRoot_mem_posRoots hr i) (rootElt_mem_rootSubgroup _ t)

theorem liftTorus_le_normalizer_liftUnip :
    liftTorus π ≤ Subgroup.normalizer (liftUnip π : Set E) := by
  have key : ∀ e ∈ liftTorus π, ∀ x ∈ liftUnip π, e * x * e⁻¹ ∈ liftUnip π :=
    fun e he x hx => conj_mem_liftSubgroup hS.ext.cen isPGroup_unipG isPGroup_unipG
      (fun u hu => by
        change ((π e * u * (π e)⁻¹ : orthElementaryGroup (quadPlus r k)) :
          (Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k)) ∈ unipotent r k
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
        exact conj_mem_unipotent_of_mem_posBorel
          (torus_le_posBorel (coe_pi_mem_torus hS he)) hu) hx
  exact fun h hh => mem_normalizer_of_conj (key h hh) (fun x hx => by
    simpa using key h⁻¹ (inv_mem hh) x hx)

theorem coe_liftBorel :
    (liftBorel π : Set E) = (liftUnip π : Set E) * (liftTorus π : Set E) :=
  Subgroup.coe_mul_of_right_le_normalizer_left _ _ (liftTorus_le_normalizer_liftUnip hS)

theorem mem_liftBorel_iff {x : E} :
    x ∈ liftBorel π ↔ ∃ u ∈ liftUnip π, ∃ h ∈ liftTorus π, x = u * h := by
  rw [← SetLike.mem_coe, coe_liftBorel hS, Set.mem_mul]
  exact ⟨fun ⟨u, hu, h, hh, e⟩ => ⟨u, hu, h, hh, e.symm⟩,
    fun ⟨u, hu, h, hh, e⟩ => ⟨u, hu, h, hh, e.symm⟩⟩

theorem sLift_inv_conj_mem_liftUnip (hr : 2 ≤ r) (i : Fin r) {x : E}
    (hx : x ∈ liftUnipExcept π i) : (sLift π i)⁻¹ * x * sLift π i ∈ liftUnip π := by
  have h := conj_mem_liftSubgroup hS.ext.cen (isPGroup_unipExceptG i) isPGroup_unipG
    (e := (sLift π i)⁻¹) (fun u hu => by
      change ((π (sLift π i)⁻¹ * u * (π (sLift π i)⁻¹)⁻¹ :
        orthElementaryGroup (quadPlus r k)) :
          (Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k)) ∈ unipotent r k
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_inv, Subgroup.coe_inv,
        coe_pi_sLift hS hr, inv_inv]
      exact map_conj_weylElt_unipotentExcept_le hr i ⟨_, hu, rfl⟩) hx
  rwa [inv_inv] at h

theorem conj_xPlus_or_xMinus_mem (hr : 2 ≤ r) {v : E} (hv : v ∈ liftWeyl π) (i : Fin r) :
    (∀ t : k, v * xPlus π i t * v⁻¹ ∈ liftUnip π) ∨
      ∀ t : k, v * xMinus π i t * v⁻¹ ∈ liftUnip π := by
  set n : torusWeyl r k := ⟨_, coe_pi_mem_torusWeyl hS hr hv⟩
  set w := torusWeylNu r k hr n
  have hα := simpleRoot_mem_roots hr i
  have hconj : ∀ {β : Fin r → ℤ}, β ∈ roots r → ∀ y : E, ∀ t : k,
      ((π y : orthElementaryGroup (quadPlus r k)) :
        (Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k)) = rootElt r k β t →
      ((π (v * y * v⁻¹) : orthElementaryGroup (quadPlus r k)) :
        (Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k)) ∈
          rootSubgroup r k ((w : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) β) := by
    intro β hβ y t hy
    rw [← map_conj_rootSubgroup_torusWeyl hr n hβ]
    refine ⟨rootElt r k β t, rootElt_mem_rootSubgroup _ t, ?_⟩
    rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hy]
    rfl
  rcases (mem_posRoots_or_neg_mem_posRoots (apply_mem_roots w.2 hα)).1 with hpos | hneg
  · left
    intro t
    refine mem_liftSubgroup_of hS.ext.cen isPGroup_unipG ?_
      (exists_orderOf_conj v (exists_orderOf_map_uSL _ t))
    exact rootSubgroup_le_unipotent hpos (hconj hα _ t (coe_pi_xPlus hS hr i t))
  · right
    intro t
    refine mem_liftSubgroup_of hS.ext.cen isPGroup_unipG ?_
      (exists_orderOf_conj v (exists_orderOf_map_vSL _ t))
    have h := hconj (neg_mem_roots hα) _ t (coe_pi_xMinus hS hr i t)
    rw [map_neg] at h
    exact rootSubgroup_le_unipotent hneg h

variable (hC : ¬ringChar k ∣ Nat.card π.ker)
include hC

omit hC in
theorem mem_liftBorel_iff_xPlus (hr : 3 ≤ r) (i : Fin r) {x : E} :
    x ∈ liftBorel π ↔
      ∃ t : k, ∃ u ∈ liftUnipExcept π i, ∃ h ∈ liftTorus π, x = xPlus π i t * u * h := by
  have hr2 : 2 ≤ r := by omega
  constructor
  · intro hx
    obtain ⟨u, hu, h, hh, rfl⟩ := (mem_liftBorel_iff hS).1 hx
    have huU : ((π u : orthElementaryGroup (quadPlus r k)) :
        (Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k)) ∈ unipotent r k :=
      liftSubgroup_le_comap hS.ext.cen isPGroup_unipG hu
    have hfac := ((orthogonal_geometry_split_positive_root_factorization (K := k) hr).2.2.2
      i).2.2.2.1
    rw [← SetLike.mem_coe, hfac, Set.mem_mul] at huU
    obtain ⟨_, ⟨t, rfl⟩, u', hu', hutu⟩ := huU
    refine ⟨t, (xPlus π i t)⁻¹ * u, ?_, h, hh, by group⟩
    have hmem : (xPlus π i t)⁻¹ * u ∈ liftUnip π :=
      mul_mem (inv_mem (xPlus_mem_liftUnip hS hr2 i t)) hu
    obtain ⟨-, hn⟩ := (mem_liftSubgroup_iff hS.ext.cen isPGroup_unipG).1 hmem
    refine mem_liftSubgroup_of hS.ext.cen (isPGroup_unipExceptG i) ?_ hn
    change ((π ((xPlus π i t)⁻¹ * u) : orthElementaryGroup (quadPlus r k)) :
      (Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k)) ∈ unipotentExcept r k i
    rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, coe_pi_xPlus hS hr2, ← hutu,
      inv_mul_cancel_left]
    exact hu'
  · rintro ⟨t, u, hu, h, hh, rfl⟩
    refine mul_mem (mul_mem (Subgroup.mem_sup_left (xPlus_mem_liftUnip hS hr2 i t))
      (Subgroup.mem_sup_left ?_)) (Subgroup.mem_sup_right hh)
    exact liftSubgroup_mono hS.ext.cen isPGroup_unipG (unipExceptG_le_unipG i) hu

theorem coe_map_liftBorel (hr : 2 ≤ r) :
    ((liftBorel π).map ((orthElementaryGroup (quadPlus r k)).subtype.comp π) :
      Set ((Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k))) =
      (unipotent r k : Set _) * (sqTorus r k : Set _) := by
  have h1 : (liftUnip π).map ((orthElementaryGroup (quadPlus r k)).subtype.comp π) =
      unipotent r k := by
    rw [← Subgroup.map_map, liftUnip, map_liftSubgroup hS.ext.cen hS.ext.surj hC isPGroup_unipG,
      unipG, Subgroup.subgroupOf_map_subtype, inf_of_le_left unipotent_le]
  have h2 : (liftTorus π).map ((orthElementaryGroup (quadPlus r k)).subtype.comp π) =
      sqTorus r k := by
    rw [← range_thetaHom hS hr, MonoidHom.map_range, ← range_pi_thetaHom hS hr]
    rfl
  rw [liftBorel, Subgroup.map_sup, h1, h2]
  exact Subgroup.coe_mul_of_right_le_normalizer_left _ _
    (le_normalizer_unipotent sqTorus_le_posBorel)

theorem liftBorel_inf_ker (hr : 3 ≤ r) :
    liftBorel π ⊓ π.ker =
      Subgroup.zpowers (hMinus π ⟨r - 2, by omega⟩ ⟨r - 1, by omega⟩
        (Fin.ne_of_val_ne (by simp; omega)) (-1) *
      hPlus π ⟨r - 2, by omega⟩ ⟨r - 1, by omega⟩ (Fin.ne_of_val_ne (by simp; omega)) (-1)) := by
  rw [epsilon_eq_hSimple (π := π) hr, ← liftTorus_inf_ker hS hr]
  refine le_antisymm (fun x hx => ?_) (inf_le_inf_right _ le_sup_right)
  obtain ⟨hxB, hxK⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨u, hu, h, hh, rfl⟩ := (mem_liftBorel_iff hS).1 hxB
  have h1 : π u = (π h)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← map_mul]; exact hxK)
  have hmem : ((π u : orthElementaryGroup (quadPlus r k)) :
      (Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k)) ∈ unipotent r k ⊓ torus r k := by
    refine Subgroup.mem_inf.2 ⟨liftSubgroup_le_comap hS.ext.cen isPGroup_unipG hu, ?_⟩
    rw [h1, Subgroup.coe_inv]
    exact inv_mem (coe_pi_mem_torus hS hh)
  rw [unipotent_inf_torus, Subgroup.mem_bot] at hmem
  have hu1 : u = 1 := eq_one_of_mem_liftSubgroup_of_mem_ker hS.ext.cen hC isPGroup_unipG hu
    (Subtype.ext hmem)
  rw [hu1, one_mul] at hxK ⊢
  exact Subgroup.mem_inf.2 ⟨hh, hxK⟩

theorem injective_pi_liftBorel (hr : 3 ≤ r) :
    Function.Injective (π.comp (liftBorel π).subtype) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hmem : (x : E) ∈ liftBorel π ⊓ π.ker := Subgroup.mem_inf.2 ⟨x.2, hx⟩
  rw [liftBorel_inf_ker hS hC hr, epsilon_eq_hSimple (π := π) hr, epsilon_eq_one hS hr,
    Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hmem
  exact Subtype.ext hmem

end Lifts

omit [Finite k] [Finite E] in
theorem etaPlusLift_congr_left {i i' j : Fin r} (h : i = i') (hij : i ≠ j) (hij' : i' ≠ j) :
    etaPlusLift π i j hij = etaPlusLift π i' j hij' := by
  subst h
  rfl

theorem odd_split_orthogonal_cross_characteristic_central_prime_triangular_factorization
    {k : Type} [Field k] [Finite k] (hk : ringChar k ≠ 2) {r : ℕ} (hr : 3 ≤ r) {E : Type*}
    [Group E] [Finite E] {π : E →* orthElementaryGroup (quadPlus r k)} {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpℓ : p ≠ ringChar k) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hpk : IsPGroup p π.ker) :
    (∀ P : Sylow (ringChar k) ((unipG r k).comap π),
      (P : Subgroup ((unipG r k).comap π)).map ((unipG r k).comap π).subtype = liftUnip π) ∧
    liftTorus π ≤ Subgroup.normalizer (liftUnip π : Set E) ∧
    (liftBorel π : Set E) = (liftUnip π : Set E) * (liftTorus π : Set E) ∧
    ((liftBorel π).map ((orthElementaryGroup (quadPlus r k)).subtype.comp π) :
      Set ((Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k))) =
      (unipotent r k : Set _) * (sqTorus r k : Set _) ∧
    liftBorel π ⊓ π.ker =
      Subgroup.zpowers (hMinus π ⟨r - 2, by omega⟩ ⟨r - 1, by omega⟩
        (Fin.ne_of_val_ne (by simp; omega)) (-1) *
      hPlus π ⟨r - 2, by omega⟩ ⟨r - 1, by omega⟩ (Fin.ne_of_val_ne (by simp; omega)) (-1)) ∧
    Nat.card (liftBorel π ⊓ π.ker : Subgroup E) ≤ 2 ∧
    hMinus π ⟨r - 2, by omega⟩ ⟨r - 1, by omega⟩ (Fin.ne_of_val_ne (by simp; omega)) (-1) *
      hPlus π ⟨r - 2, by omega⟩ ⟨r - 1, by omega⟩ (Fin.ne_of_val_ne (by simp; omega)) (-1) = 1 ∧
    Function.Injective (π.comp (liftBorel π).subtype) ∧
    (∀ (i : Fin r) (h : i.val + 1 < r),
      simpleLift π i = etaMinusLift π i ⟨i.val + 1, h⟩ (ne_succ_of_lt h)) ∧
    simpleLift π ⟨r - 1, by omega⟩ =
      etaPlusLift π ⟨r - 2, by omega⟩ ⟨r - 1, by omega⟩ (Fin.ne_of_val_ne (by simp; omega)) ∧
    ∀ i : Fin r,
      (∀ P : Sylow (ringChar k) ((unipExceptG r k i).comap π),
        (P : Subgroup ((unipExceptG r k i).comap π)).map
          ((unipExceptG r k i).comap π).subtype = liftUnipExcept π i) ∧
      (∀ t : k, ((π (xPlus π i t) : orthElementaryGroup (quadPlus r k)) :
        (Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k)) = rootElt r k (simpleRoot r i) t) ∧
      (∀ t : k, ((π (xMinus π i t) : orthElementaryGroup (quadPlus r k)) :
        (Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k)) = rootElt r k (-simpleRoot r i) t) ∧
      (∀ x : E, x ∈ liftBorel π ↔
        ∃ t : k, ∃ u ∈ liftUnipExcept π i, ∃ h ∈ liftTorus π, x = xPlus π i t * u * h) ∧
      (∀ x ∈ liftUnipExcept π i, (sLift π i)⁻¹ * x * sLift π i ∈ liftUnip π) ∧
      (∀ (t : k) (ht : t ≠ 0), xPlus π i t * sLift π i =
        xMinus π i t⁻¹ * hSimple π i (Units.mk0 t ht) * xPlus π i (-t⁻¹)) ∧
      ∀ v ∈ liftWeyl π,
        (∀ t : k, v * xPlus π i t * v⁻¹ ∈ liftUnip π) ∨
        ∀ t : k, v * xMinus π i t * v⁻¹ ∈ liftUnip π := by
  have := Fintype.ofFinite k
  obtain ⟨n, hℓ, -⟩ := FiniteField.card k (ringChar k)
  have : Fact (ringChar k).Prime := ⟨hℓ⟩
  have hr2 : 2 ≤ r := by omega
  have hS : LargeHyp π := ⟨hk, ⟨hπ, hcen, ⟨p, hp, hp3, hpk⟩⟩⟩
  have hC : ¬ringChar k ∣ Nat.card π.ker := by
    obtain ⟨m, hm⟩ := hpk.exists_card_dvd_pow
    intro hdvd
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).1 (hℓ.dvd_of_dvd_pow (hdvd.trans hm))).symm
  have hε : hMinus π ⟨r - 2, by omega⟩ ⟨r - 1, by omega⟩ (Fin.ne_of_val_ne (by simp; omega)) (-1) *
      hPlus π ⟨r - 2, by omega⟩ ⟨r - 1, by omega⟩ (Fin.ne_of_val_ne (by simp; omega)) (-1) = 1 := by
    rw [epsilon_eq_hSimple hr]
    exact epsilon_eq_one hS hr
  refine ⟨sylow_map_eq_liftSubgroup hcen isPGroup_unipG, liftTorus_le_normalizer_liftUnip hS,
    coe_liftBorel hS, coe_map_liftBorel hS hC hr2, liftBorel_inf_ker hS hC hr, ?_, hε,
    injective_pi_liftBorel hS hC hr, fun i h => ?_, ?_, fun i =>
      ⟨sylow_map_eq_liftSubgroup hcen (isPGroup_unipExceptG i), coe_pi_xPlus hS hr2 i,
        coe_pi_xMinus hS hr2 i, fun x => mem_liftBorel_iff_xPlus hS hr i,
        fun x hx => sLift_inv_conj_mem_liftUnip hS hr2 i hx, fun t ht => xPlus_mul_sLift π i ht,
        fun v hv => conj_xPlus_or_xMinus_mem hS hr2 hv i⟩⟩
  · rw [liftBorel_inf_ker hS hC hr, hε, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot]
    norm_num
  · rw [simpleLift, dite_eq_left h]
  · rw [simpleLift, dite_eq_right (by simp; omega), dite_eq_left (by simp; omega)]
    exact etaPlusLift_congr_left (Fin.ext (by simp; omega)) _ _

end CFSG.RankThree.CentralLiftSO.SplitO

module

public import CFSG.RankThree.CentralLiftSO.TailLift
import all CFSG.LieType.Universal.SymplecticRoots
import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylQuotient
import CFSG.RankThree.CentralLiftSO.CanonicalLift
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailWeylLift

public section

namespace CFSG.RankThree.CentralLiftSO.TailO

open QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal CFSG.LieType.CentralExt
open CFSG.RankThree.CentralLift
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.LocalAnalysis.ComponentInitial.NormTail
open CFSG.LocalAnalysis.ComponentInitial.NormTail renaming torusMap → tMap
open CFSG.LocalAnalysis.ComponentInitial (orthElementaryGroup)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (sl2W sl2ConjDiag sl2Diag
  sl2W_mul_sl2W sl2ConjDiag_inv_sl2W sl2ConjDiag_neg_one_sl2W conj_comp_eq)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit (ne_succ_of_lt coordWt)

variable {K L : Type} [Field K] [Field L] [Algebra K L] (T : NormTailData K L) {r : ℕ}
  {E : Type*} [Group E]

section Defs

variable (π : E →* G0 T r)

@[expose] noncomputable def sLift (i : Fin r) : E :=
  if h : i.val + 1 < r then etaLift T π (ne_succ_of_lt h) sl2W else wLift T π i

@[expose] noncomputable def liftWeyl : Subgroup E :=
  Subgroup.closure ((liftTorus T π : Set E) ∪ Set.range (sLift T π))

end Defs

variable {T} {π : E →* G0 T r}

theorem sLift_of_lt {i : Fin r} (h : i.val + 1 < r) :
    sLift T π i = etaLift T π (ne_succ_of_lt h) sl2W := by
  rw [sLift, dite_eq_left h]

theorem sLift_of_not_lt {i : Fin r} (h : ¬i.val + 1 < r) : sLift T π i = wLift T π i := by
  rw [sLift, dite_eq_right h]

theorem liftTorus_le_liftWeyl : liftTorus T π ≤ liftWeyl T π :=
  fun _ hx => Subgroup.subset_closure (Or.inl hx)

theorem sLift_mem (i : Fin r) : sLift T π i ∈ liftWeyl T π :=
  Subgroup.subset_closure (Or.inr ⟨i, rfl⟩)

theorem sLift_mul_self (i : Fin r) : sLift T π i * sLift T π i ∈ liftTorus T π := by
  by_cases h : i.val + 1 < r
  · rw [sLift_of_lt h, ← map_mul, sl2W_mul_sl2W]
    exact hLift_mem T π _ (-1)
  · rw [sLift_of_not_lt h, wLift_mul_self]
    exact tauLift_mem T π _ _

theorem sLift_sq_mem (i : Fin r) : sLift T π i ^ 2 ∈ liftTorus T π := by
  rw [pow_two]
  exact sLift_mul_self i

variable [Finite E]

section Images

variable (hS : TailHyp T π)
include hS

theorem coe_map_sLift_of_lt {i : Fin r} (h : i.val + 1 < r) :
    ((π (sLift T π i) : G0 T r) : ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] _) =
      (tailWeylElt r (normForm T) 1 i)⁻¹ := by
  rw [sLift_of_lt h, hS.coe_map_etaLift, eta_sl2W_eq_tailWeylElt_inv T h]

theorem coe_map_sLift_of_not_lt {i : Fin r} (h : ¬i.val + 1 < r) :
    ((π (sLift T π i) : G0 T r) : ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] _) =
      tailWeylElt r (normForm T) 1 i := by
  rw [sLift_of_not_lt h, coe_map_wLift hS, rhoO_sl2W_eq_tailWeylElt T h]

theorem coe_map_mem_tailTorusWeyl {v : E} (hv : v ∈ liftWeyl T π) :
    ((π v : G0 T r) : ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] _) ∈ tailTorusWeyl r (normForm T) 1 := by
  have hle : liftWeyl T π ≤ (tailTorusWeyl r (normForm T) 1).comap
      ((orthElementaryGroup (quadTail r (normForm T))).subtype.comp π) := by
    rw [liftWeyl, Subgroup.closure_le]
    rintro x (hx | ⟨i, rfl⟩)
    · exact tailTorus_le_tailTorusWeyl 1 (coe_map_mem_tailTorus hS hx)
    · change ((π (sLift T π i) : G0 T r) :
        ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × L)) ∈
          tailTorusWeyl r (normForm T) 1
      by_cases h : i.val + 1 < r
      · rw [coe_map_sLift_of_lt hS h]
        exact inv_mem (tailWeylElt_mem_tailTorusWeyl 1 i)
      · rw [coe_map_sLift_of_not_lt hS h]
        exact tailWeylElt_mem_tailTorusWeyl 1 i
  exact hle hv

end Images

section Normalizer

omit [Finite E] in
theorem conj_eq_inv_mul_of_conj {x s h : E} (hx : x * s * x⁻¹ = h * s) :
    s * x * s⁻¹ = h⁻¹ * x := by
  have h1 : x * s = h * s * x := mul_inv_eq_iff_eq_mul.1 hx
  calc s * x * s⁻¹ = h⁻¹ * (h * s * x) * s⁻¹ := by group
    _ = h⁻¹ * (x * s) * s⁻¹ := by rw [h1]
    _ = h⁻¹ * x := by group

omit [Field L] [Algebra K L] [Finite E] in
theorem sl2ConjDiag_sl2W {F : Type} [Field F] (u : Fˣ) :
    sl2ConjDiag u (sl2W : SpecialLinearGroup (Fin 2) F) = sl2Diag u⁻¹ * sl2W := by
  rw [← sl2ConjDiag_inv_sl2W, inv_inv]

variable (hS : TailHyp T π)
include hS

theorem sLift_conj_mem {x : E} (hx : x ∈ liftTorus T π) (i : Fin r) :
    sLift T π i * x * (sLift T π i)⁻¹ ∈ liftTorus T π := by
  obtain ⟨a, c, hc, hxa⟩ := exists_torusMap_of_mem hS hx
  by_cases h : i.val + 1 < r
  · have h1 := conj_etaLift_of_torusMap hS hxa (ne_succ_of_lt h) rfl sl2W
    rw [sl2ConjDiag_sl2W, map_mul, ← sLift_of_lt h] at h1
    rw [conj_eq_inv_mul_of_conj h1]
    exact mul_mem (inv_mem (hLift_mem T π _ _)) hx
  · have h1 := conj_rhoLift_of_torusMap hS hc hxa i rfl sl2W
    rw [sl2ConjDiag_sl2W, map_mul, show rhoLift T π i sl2W = sLift T π i by
      rw [sLift_of_not_lt h]; rfl] at h1
    rw [conj_eq_inv_mul_of_conj h1]
    exact mul_mem (inv_mem (tauLift_mem T π _ _)) hx

theorem sLift_mem_normalizer (i : Fin r) :
    sLift T π i ∈ Subgroup.normalizer (liftTorus T π : Set E) := by
  refine Lift.mem_normalizer_of_conj (fun x hx => sLift_conj_mem hS hx i) fun x hx => ?_
  have h2 := sLift_mul_self (π := π) i
  have hy : (sLift T π i * sLift T π i)⁻¹ * x * (sLift T π i * sLift T π i) ∈ liftTorus T π :=
    mul_mem (mul_mem (inv_mem h2) hx) h2
  have he : (sLift T π i)⁻¹ * x * sLift T π i = sLift T π i *
      ((sLift T π i * sLift T π i)⁻¹ * x * (sLift T π i * sLift T π i)) * (sLift T π i)⁻¹ := by
    group
  rw [he]
  exact sLift_conj_mem hS hy i

theorem liftWeyl_le_normalizer :
    liftWeyl T π ≤ Subgroup.normalizer (liftTorus T π : Set E) := by
  rw [liftWeyl, Subgroup.closure_le]
  rintro x (hx | ⟨i, rfl⟩)
  · exact Subgroup.le_normalizer hx
  · exact sLift_mem_normalizer hS i

theorem normal_liftTorus_subgroupOf : ((liftTorus T π).subgroupOf (liftWeyl T π)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer liftTorus_le_liftWeyl).2
    (liftWeyl_le_normalizer hS)

theorem wLift_mem_liftWeyl (i : Fin r) : wLift T π i ∈ liftWeyl T π := by
  suffices h : ∀ m : ℕ, ∀ i : Fin r, i.val + 1 + m = r → wLift T π i ∈ liftWeyl T π from
    h (r - 1 - i.val) i (by have := i.isLt; omega)
  intro m
  induction m with
  | zero =>
    intro i hi
    rw [← sLift_of_not_lt (by omega)]
    exact sLift_mem i
  | succ m ih =>
    intro i hi
    have hlt : i.val + 1 < r := by omega
    have h1 := vLift_conj_wLift hS (ne_succ_of_lt hlt)
    rw [← sLift_of_lt hlt] at h1
    have h2 : (wLift T π i)⁻¹ ∈ liftWeyl T π := by
      rw [← h1]
      exact mul_mem (mul_mem (sLift_mem i) (ih ⟨i.val + 1, hlt⟩ (by simp; omega)))
        (inv_mem (sLift_mem i))
    simpa using inv_mem h2

end Normalizer

section WeylHom

variable (hS : TailHyp T π)
include hS

@[expose] noncomputable def piWeyl : liftWeyl T π →* tailTorusWeyl r (normForm T) 1 :=
  ((orthElementaryGroup (quadTail r (normForm T))).subtype.comp
    (π.comp (liftWeyl T π).subtype)).codRestrict _ fun v => coe_map_mem_tailTorusWeyl hS v.2

@[expose] noncomputable def weylHom : liftWeyl T π →* weylGroupB r :=
  (tailTorusWeylNu r (normForm T) (normForm_anisotropic T) (one_ne_zero (α := L))).comp
    (piWeyl hS)

theorem weylHom_apply (v : liftWeyl T π) :
    weylHom hS v =
      tailTorusWeylNu r (normForm T) (normForm_anisotropic T) (one_ne_zero (α := L))
        (piWeyl hS v) :=
  rfl

theorem weylHom_sLift (i : Fin r) :
    weylHom hS ⟨sLift T π i, sLift_mem i⟩ = ⟨simpleReflB r i, simpleReflB_mem i⟩ := by
  rw [weylHom_apply]
  by_cases h : i.val + 1 < r
  · have hp : piWeyl hS ⟨sLift T π i, sLift_mem i⟩ =
        (⟨tailWeylElt r (normForm T) 1 i, tailWeylElt_mem_tailTorusWeyl 1 i⟩ :
          tailTorusWeyl r (normForm T) 1)⁻¹ :=
      Subtype.ext (coe_map_sLift_of_lt hS h)
    rw [hp, map_inv, tailTorusWeylNu_tailWeylElt]
    exact inv_eq_of_mul_eq_one_right (Subtype.ext (simpleReflB_mul_self i))
  · have hp : piWeyl hS ⟨sLift T π i, sLift_mem i⟩ =
        ⟨tailWeylElt r (normForm T) 1 i, tailWeylElt_mem_tailTorusWeyl 1 i⟩ :=
      Subtype.ext (coe_map_sLift_of_not_lt hS h)
    rw [hp, tailTorusWeylNu_tailWeylElt]

theorem weylHom_eq_one_of_mem {v : liftWeyl T π} (hv : (v : E) ∈ liftTorus T π) :
    weylHom hS v = 1 := by
  rw [weylHom_apply, ← MonoidHom.mem_ker, tailTorusWeylNu_ker, Subgroup.mem_subgroupOf]
  exact coe_map_mem_tailTorus hS hv

theorem liftTorus_le_ker_weylHom :
    (liftTorus T π).subgroupOf (liftWeyl T π) ≤ (weylHom hS).ker :=
  fun _ hv => weylHom_eq_one_of_mem hS (Subgroup.mem_subgroupOf.1 hv)

theorem weylHom_surjective : Function.Surjective (weylHom hS) := by
  rintro ⟨w, hw⟩
  have hle : Subgroup.closure (Set.range (simpleReflB r)) ≤
      (weylHom hS).range.map (weylGroupB r).subtype := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨_, ⟨⟨sLift T π i, sLift_mem i⟩, rfl⟩, by rw [weylHom_sLift]; rfl⟩
  obtain ⟨_, ⟨n, rfl⟩, hn⟩ := hle ((closure_simpleReflB (r := r)).ge hw)
  exact ⟨n, Subtype.ext hn⟩

theorem apply_hypVec_weylHom (v : liftWeyl T π) (c : Fin r ⊕ Fin r) :
    ∃ (μ : Kˣ) (c' : Fin r ⊕ Fin r),
      ((π v : G0 T r) : ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] _) (hypVec K L c) =
          (μ : K) • hypVec K L c' ∧
        coordWt c' = ((weylHom hS v : weylGroupB r) : (Fin r → ℤ) ≃ₗ[ℤ] _) (coordWt c) :=
  apply_hypVec_tailTorusWeylNu (normForm_anisotropic T) (one_ne_zero (α := L)) (piWeyl hS v) c

theorem map_conj_tailRootGroup_weylHom (v : liftWeyl T π) {α : Fin r → ℤ} (hα : α ∈ rootsB r) :
    (tailRootGroup r (normForm T) α).map (MulAut.conj ((π v : G0 T r) :
        ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] _)).toMonoidHom =
      tailRootGroup r (normForm T)
        (((weylHom hS v : weylGroupB r) : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) α) :=
  map_conj_tailRootGroup (normForm_anisotropic T) (one_ne_zero (α := L)) (piWeyl hS v) hα

end WeylHom

section Relations

variable (hS : TailHyp T π)
include hS

theorem etaLift_symm_sl2W {i j : Fin r} (hij : i ≠ j) :
    etaLift T π hij.symm sl2W = (etaLift T π hij sl2W)⁻¹ := by
  rw [etaLift, etaG_symm, ← hS.liftOf_comp_K, MonoidHom.comp_apply, SplitO.sl2Swap_sl2W, map_inv]
  rfl

theorem vLift_braid {a b c : Fin r} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    etaLift T π hbc sl2W * etaLift T π hab sl2W * etaLift T π hbc sl2W =
      etaLift T π hab sl2W * etaLift T π hbc sl2W * etaLift T π hab sl2W := by
  have hba : Sum.inl b ≠ (Sum.inl a : Fin r ⊕ Fin r) := fun h => hab (Sum.inl_injective h).symm
  have hcb : Sum.inl c ≠ (Sum.inl b : Fin r ⊕ Fin r) := fun h => hbc (Sum.inl_injective h).symm
  have h1 := vLift_conj_etaLift hS hab (a := b) (b := c) hbc hac
    (by simp [Equiv.swap_apply_of_ne_of_ne])
    (by simp [Equiv.swap_apply_of_ne_of_ne, hbc.symm, hac.symm])
    (u := -1) (by rw [SplitO.wSign_of_eq rfl, SplitO.wSign_of_ne hcb (by simp)]; simp) sl2W
  have h2 := vLift_conj_etaLift hS hbc.symm (a := a) (b := b) hab hac
    (by simp [Equiv.swap_apply_def, hab, hac])
    (by simp [Equiv.swap_apply_def])
    (u := -1) (by rw [SplitO.wSign_of_ne hba.symm (by simp), SplitO.wSign_of_eq rfl]; simp) sl2W
  rw [etaLift_symm_sl2W hS hbc, inv_inv] at h2
  have h := h1.trans h2.symm
  have h' := congrArg (fun x => etaLift T π hbc sl2W * x * etaLift T π hab sl2W) h
  simp only [mul_assoc, inv_mul_cancel, mul_inv_cancel_left, mul_one] at h'
  simpa only [mul_assoc] using h'

theorem commute_vLift_etaLift {a b c d : Fin r} (hab : a ≠ b) (hcd : c ≠ d) (hca : c ≠ a)
    (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b) (g : SpecialLinearGroup (Fin 2) K) :
    Commute (etaLift T π hab sl2W) (etaLift T π hcd g) := by
  have h1 := vLift_conj_etaLift hS hab (a := c) (b := d) hcd hcd
    (SplitO.swap_mul_swap_apply_of_ne (by simpa using hca) (by simpa using hcb) (by simp)
      (by simp))
    (SplitO.swap_mul_swap_apply_of_ne (by simpa using hda) (by simpa using hdb) (by simp)
      (by simp))
    (u := 1) (by rw [SplitO.wSign_of_ne (by simpa using hcb) (by simp),
      SplitO.wSign_of_ne (by simpa using hdb) (by simp)]; simp) g
  rw [SplitO.sl2ConjDiag_one] at h1
  exact mul_inv_eq_iff_eq_mul.1 h1

theorem commute_vLift_rhoLift {i a b : Fin r} (hab : a ≠ b) (hia : i ≠ a) (hib : i ≠ b)
    (g : SpecialLinearGroup (Fin 2) K) (A : SpecialLinearGroup (Fin 2) L) :
    Commute (etaLift T π hab g) (rhoLift T π i A) :=
  hS.commute_liftOf_KL _ _ (fun g A => Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_etaG, coe_rhoOG]
    exact eta_mul_rhoO_of_ne T hab hia hib g A)) g A

end Relations

section Coxeter

variable (T π) in
@[expose] noncomputable def sClass (i : Fin r) :
    liftWeyl T π ⧸ (liftTorus T π).subgroupOf (liftWeyl T π) :=
  QuotientGroup.mk ⟨sLift T π i, sLift_mem i⟩

omit [Finite E] in
theorem qmk_congr {x y : E} (hx : x ∈ liftWeyl T π) (hy : y ∈ liftWeyl T π) (h : x = y) :
    (QuotientGroup.mk ⟨x, hx⟩ : liftWeyl T π ⧸ (liftTorus T π).subgroupOf (liftWeyl T π)) =
      QuotientGroup.mk ⟨y, hy⟩ := by
  subst h
  rfl

variable [((liftTorus T π).subgroupOf (liftWeyl T π)).Normal]

omit [Finite E] in
theorem qmk_mul {x y : E} (hx : x ∈ liftWeyl T π) (hy : y ∈ liftWeyl T π) :
    (QuotientGroup.mk ⟨x, hx⟩ : liftWeyl T π ⧸ (liftTorus T π).subgroupOf (liftWeyl T π)) *
      QuotientGroup.mk ⟨y, hy⟩ = QuotientGroup.mk ⟨x * y, mul_mem hx hy⟩ := rfl

omit [Finite E] in
theorem qmk_inv {x : E} (hx : x ∈ liftWeyl T π) :
    (QuotientGroup.mk ⟨x, hx⟩ : liftWeyl T π ⧸ (liftTorus T π).subgroupOf (liftWeyl T π))⁻¹ =
      QuotientGroup.mk ⟨x⁻¹, inv_mem hx⟩ := rfl

omit [Finite E] in
theorem qmk_eq_one_iff {x : E} (hx : x ∈ liftWeyl T π) :
    (QuotientGroup.mk ⟨x, hx⟩ : liftWeyl T π ⧸ (liftTorus T π).subgroupOf (liftWeyl T π)) = 1 ↔
      x ∈ liftTorus T π := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

omit [Finite E] in
theorem sClass_mul_self (i : Fin r) : sClass T π i * sClass T π i = 1 := by
  rw [sClass, qmk_mul, qmk_eq_one_iff]
  exact sLift_mul_self i

variable (hS : TailHyp T π)
include hS

theorem sClass_braid {i j : Fin r} (hij : i.val + 1 = j.val) (hj : j.val + 1 < r) :
    sClass T π j * sClass T π i * sClass T π j = sClass T π i * sClass T π j * sClass T π i := by
  have hi : i.val + 1 < r := by omega
  simp only [sClass, qmk_mul]
  apply qmk_congr
  obtain rfl : j = ⟨i.val + 1, hi⟩ := Fin.ext hij.symm
  rw [sLift_of_lt hi, sLift_of_lt hj]
  exact vLift_braid hS (ne_succ_of_lt hi) (ne_succ_of_lt hj)
    (Fin.ne_of_val_ne (by simp only; omega))

theorem sClass_comm {i j : Fin r} (hij : i.val + 1 < j.val) :
    sClass T π i * sClass T π j = sClass T π j * sClass T π i := by
  have hi : i.val + 1 < r := by omega
  simp only [sClass, qmk_mul]
  apply qmk_congr
  rw [sLift_of_lt hi]
  by_cases hj : j.val + 1 < r
  · rw [sLift_of_lt hj]
    exact (commute_vLift_etaLift hS _ _ (Fin.ne_of_val_ne (by omega))
      (Fin.ne_of_val_ne (by simp only; omega)) (Fin.ne_of_val_ne (by simp only; omega))
      (Fin.ne_of_val_ne (by simp only; omega)) sl2W).eq
  · rw [sLift_of_not_lt hj]
    exact (commute_vLift_rhoLift hS _ (Fin.ne_of_val_ne (by omega))
      (Fin.ne_of_val_ne (by simp only; omega)) sl2W sl2W).eq

theorem sClass_long {i j : Fin r} (hij : i.val + 1 = j.val) (hj : ¬j.val + 1 < r) :
    sClass T π i * sClass T π j * sClass T π i * (sClass T π i * sClass T π j * sClass T π i) =
        1 ∧
      sClass T π i * sClass T π j * sClass T π i * sClass T π j =
        sClass T π j * (sClass T π i * sClass T π j * sClass T π i) := by
  have hi : i.val + 1 < r := by omega
  have hji : j ≠ i := Fin.ne_of_val_ne (by omega)
  have hinv : (sClass T π i)⁻¹ = sClass T π i :=
    inv_eq_of_mul_eq_one_right (sClass_mul_self i)
  have hv : sClass T π i * sClass T π j * sClass T π i =
      (QuotientGroup.mk ⟨wLift T π i, wLift_mem_liftWeyl hS i⟩ :
        liftWeyl T π ⧸ (liftTorus T π).subgroupOf (liftWeyl T π))⁻¹ := by
    have h3 : sClass T π i * sClass T π j * sClass T π i =
        sClass T π i * sClass T π j * (sClass T π i)⁻¹ := by rw [hinv]
    rw [h3]
    simp only [sClass, qmk_mul, qmk_inv]
    apply qmk_congr
    obtain rfl : j = ⟨i.val + 1, hi⟩ := Fin.ext hij.symm
    rw [sLift_of_lt hi, sLift_of_not_lt hj]
    exact vLift_conj_wLift hS (ne_succ_of_lt hi)
  have hsj : sClass T π j = QuotientGroup.mk ⟨wLift T π j, wLift_mem_liftWeyl hS j⟩ := by
    rw [sClass]
    exact qmk_congr _ _ (sLift_of_not_lt hj)
  have hcomm : (QuotientGroup.mk ⟨wLift T π j, wLift_mem_liftWeyl hS j⟩ :
      liftWeyl T π ⧸ (liftTorus T π).subgroupOf (liftWeyl T π)) *
        QuotientGroup.mk ⟨wLift T π i, wLift_mem_liftWeyl hS i⟩ *
        (QuotientGroup.mk ⟨wLift T π j, wLift_mem_liftWeyl hS j⟩)⁻¹ =
      QuotientGroup.mk ⟨wLift T π i, wLift_mem_liftWeyl hS i⟩ := by
    have hτ : rhoLift T π i (-1) ∈ liftWeyl T π := by
      rw [CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.neg_one_eq_sl2Diag]
      exact liftTorus_le_liftWeyl (tauLift_mem T π i (-1))
    rw [qmk_inv, qmk_mul, qmk_mul, qmk_congr _ (mul_mem hτ (wLift_mem_liftWeyl hS i))
      (wLift_conj_wLift hS hji), ← qmk_mul hτ, (qmk_eq_one_iff hτ).2, one_mul]
    rw [CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.neg_one_eq_sl2Diag]
    exact tauLift_mem T π i (-1)
  have hc : Commute (QuotientGroup.mk ⟨wLift T π i, wLift_mem_liftWeyl hS i⟩ :
      liftWeyl T π ⧸ (liftTorus T π).subgroupOf (liftWeyl T π))
      (QuotientGroup.mk ⟨wLift T π j, wLift_mem_liftWeyl hS j⟩) :=
    (mul_inv_eq_iff_eq_mul.1 hcomm).symm
  rw [hv, hsj]
  refine ⟨?_, hc.inv_left.eq⟩
  rw [← _root_.mul_inv_rev, inv_eq_one, qmk_mul, qmk_eq_one_iff, wLift_mul_self]
  exact tauLift_mem T π i (-1)

private theorem isLiftable_sClass :
    (CFSG.LieType.RootSystem.coxeterMatrix
      (CFSG.LieType.Universal.Symplectic.isFiniteType_cartanC r)).IsLiftable (sClass T π) := by
  have key : ∀ i j : Fin r, i < j → (sClass T π i * sClass T π j) ^
      (CFSG.LieType.RootSystem.coxeterMatrix
        (CFSG.LieType.Universal.Symplectic.isFiniteType_cartanC r)) i j = 1 := by
    intro i j hij
    have hij' : i.val < j.val := hij
    by_cases hadj : i.val + 1 = j.val
    · by_cases hj : j.val + 1 < r
      · rw [CFSG.LieType.Universal.Symplectic.coxeterMatrix_of_succ_short r hadj hj]
        exact CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.pow_three_eq_one
          (sClass_mul_self i) (sClass_mul_self j) (sClass_braid hS hadj hj)
      · rw [CFSG.LieType.Universal.Symplectic.coxeterMatrix_of_succ_long r hadj hj]
        exact CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.pow_four_eq_one
          (sClass_mul_self j) (sClass_long hS hadj hj).1 (sClass_long hS hadj hj).2
    · rw [CFSG.LieType.Universal.Symplectic.coxeterMatrix_of_far r hij.ne hadj (by omega)]
      exact CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.pow_two_eq_one_of_commute
        (sClass_mul_self i) (sClass_mul_self j) (sClass_comm hS (by omega))
  intro i j
  rcases lt_trichotomy i j with h | rfl | h
  · exact key i j h
  · rw [CoxeterMatrix.diagonal, pow_one]
    exact sClass_mul_self i
  · rw [CoxeterMatrix.symmetric]
    exact CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.pow_eq_one_comm (key j i h)

end Coxeter

section Kernel

omit [Finite E] in
private theorem simpleReflB_apply_eq_stdRefl (i : Fin r) (e : Fin r → ℤ) :
    simpleReflB r i e = CFSG.LieType.Universal.Symplectic.stdRefl r i e := by
  by_cases h : i.val + 1 < r
  · rw [simpleReflB_of_lt h, CFSG.LieType.Universal.Symplectic.stdRefl_of_lt r h]
    funext j
    rw [CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.signedPermAut_apply, Equiv.swap_inv,
      Pi.one_apply, Units.val_one, one_mul, Function.comp_apply]
  · rw [simpleReflB_of_not_lt h, CFSG.LieType.Universal.Symplectic.stdRefl_of_not_lt r h]
    funext j
    rw [CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.signedPermAut_apply, inv_one,
      Equiv.Perm.one_apply]
    by_cases hj : j = i
    · rw [hj, signAt_self, ite_eq_left rfl]
    · rw [signAt_of_ne hj, ite_eq_right hj]

variable (hS : TailHyp T π)
include hS

theorem ker_weylHom_le : (weylHom hS).ker ≤ (liftTorus T π).subgroupOf (liftWeyl T π) := by
  have := normal_liftTorus_subgroupOf hS
  set hA := CFSG.LieType.Universal.Symplectic.isFiniteType_cartanC r
  set cs := (CFSG.LieType.RootSystem.coxeterMatrix hA).toCoxeterSystem
  set Lc := cs.lift ⟨sClass T π, isLiftable_sClass hS⟩ with hL
  set φbar := QuotientGroup.lift _ (weylHom hS) (liftTorus_le_ker_weylHom hS) with hφbar
  have hsimple : ∀ i, ((φbar (Lc (cs.simple i)) : weylGroupB r) :
      (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) = simpleReflB r i := by
    intro i
    rw [hL, CoxeterSystem.lift_apply_simple, sClass, hφbar, QuotientGroup.lift_mk, weylHom_sLift]
  have hact : ∀ w v, CFSG.LieType.Universal.Symplectic.toStd r
      (CFSG.LieType.RootSystem.weylAction hA w v) =
        ((φbar (Lc w) : weylGroupB r) : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ))
          (CFSG.LieType.Universal.Symplectic.toStd r v) := by
    intro w
    refine cs.simple_induction_left (p := fun w => ∀ v,
      CFSG.LieType.Universal.Symplectic.toStd r (CFSG.LieType.RootSystem.weylAction hA w v) =
        ((φbar (Lc w) : weylGroupB r) : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ))
          (CFSG.LieType.Universal.Symplectic.toStd r v)) w ?_ ?_
    · intro v
      rw [map_one, map_one, map_one]
      rfl
    · intro w i ih v
      rw [CFSG.LieType.RootSystem.weylAction_mul_apply,
        CFSG.LieType.RootSystem.weylAction_simple,
        CFSG.LieType.Universal.Symplectic.toStd_reflection, ih, map_mul, map_mul,
        Subgroup.coe_mul, LinearEquiv.mul_apply, hsimple, simpleReflB_apply_eq_stdRefl]
  have hinj : ∀ w, φbar (Lc w) = 1 → w = 1 := by
    intro w hw
    apply CFSG.LieType.RootSystem.weylAction_injective hA
    rw [map_one]
    refine LinearMap.ext fun v => CFSG.LieType.Universal.Symplectic.toStd_injective r ?_
    rw [hact, hw, Module.End.one_apply]
    rfl
  have hsurj : Function.Surjective Lc := by
    have key : ∀ x (hx : x ∈ liftWeyl T π),
        (QuotientGroup.mk ⟨x, hx⟩ : liftWeyl T π ⧸ (liftTorus T π).subgroupOf (liftWeyl T π)) ∈
          Lc.range := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
        rcases hx with hx | ⟨i, rfl⟩
        · exact ⟨1, by rw [map_one]; exact ((qmk_eq_one_iff _).2 hx).symm⟩
        · exact ⟨cs.simple i, CoxeterSystem.lift_apply_simple _ _ i⟩
      | one => exact Lc.range.one_mem
      | mul x y hx hy ihx ihy => exact mul_mem ihx ihy
      | inv x hx ihx => exact inv_mem ihx
    intro q
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective q
    exact key x hx
  intro n hn
  obtain ⟨w, hw⟩ := hsurj (QuotientGroup.mk n)
  have h1 : φbar (Lc w) = 1 := by
    rw [hw, hφbar, QuotientGroup.lift_mk]
    exact hn
  rw [hinj w h1, map_one] at hw
  exact (QuotientGroup.eq_one_iff n).1 hw.symm

theorem ker_weylHom : (weylHom hS).ker = (liftTorus T π).subgroupOf (liftWeyl T π) :=
  le_antisymm (ker_weylHom_le hS) (liftTorus_le_ker_weylHom hS)

end Kernel

end CFSG.RankThree.CentralLiftSO.TailO

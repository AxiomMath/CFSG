module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylBFrame
import all CFSG.LieType.Universal.SymplecticRoots

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits CoxeterSystem
  CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras
  CFSG.Assembly.LowTwoRank TauCeti.GLSymplecticFin

variable {n : ℕ}

theorem toStd_single_eq_zero {j c : Fin (n + 1)} (hcj : c ≠ j)
    (hc : ∀ h : j.val + 1 < n + 1, c ≠ ⟨j.val + 1, h⟩) :
    toStd (n + 1) (Pi.single j 1) c = 0 := by
  by_cases h : j.val + 1 < n + 1
  · rw [toStd_single_of_lt' h]
    simp [hcj, hc h]
  · rw [toStd_single_of_not_lt' h]
    simp [hcj]

theorem spLevi_orbit (F : Type) [Field F] (hn : 4 ≤ n) :
    GGOrbit (Symplectic.rootDatum (n + 1) F)
      (fun _ : Unit => ggSupp (Symplectic.rootDatum (n + 1) F) (spLeviJ n)) := by
  refine ggOrbit_of_pairs (fun _ => ggSuppLattice (Symplectic.rootDatum (n + 1) F) (spLeviJ n))
    (fun _ γ hγ hγM => ⟨hγ, hγM⟩) ?_
  intro J hJ
  let J' : Finset (Fin (n + 1)) := J
  have hJ' : J'.card ≤ 2 := hJ
  let nx : Fin (n + 1) → Fin (n + 1) := fun j => if h : j.val + 1 < n + 1 then ⟨j.val + 1, h⟩ else j
  obtain ⟨E, hEdef⟩ : ∃ E : Finset (Fin (n + 1)), E = J' ∪ J'.image nx := ⟨_, rfl⟩
  have hE : E.card < (Finset.univ : Finset (Fin (n + 1))).card := by
    have h1 := Finset.card_union_le J' (J'.image nx)
    have h2 := Finset.card_image_le (s := J') (f := nx)
    rw [Finset.card_univ, Fintype.card_fin, hEdef]
    omega
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hE
  have hcj : ∀ j ∈ J', c ≠ j := fun j hj e => hc (hEdef ▸ Finset.mem_union_left _ (e ▸ hj))
  have hcn : ∀ j ∈ J', ∀ h : j.val + 1 < n + 1, c ≠ ⟨j.val + 1, h⟩ := fun j hj h e =>
    hc (hEdef ▸ Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, hj, by
      simp only [nx]
      rw [dite_eq_left h, e]⟩))
  have hlat : ∀ v : Fin (n + 1) → ℤ, toStd (n + 1) v 0 = 0 →
      v ∈ ggSuppLattice (Symplectic.rootDatum (n + 1) F) (spLeviJ n) := by
    intro v hv i hi
    have hi0 : (i : Fin (n + 1)).val = 0 := by have := mt mem_spLeviJ.mpr hi; omega
    have : i = (0 : Fin (n + 1)) := Fin.ext hi0
    subst this
    rw [← toStd_succ_apply_zero (n := n) (by omega) v]
    exact hv
  by_cases hc0 : c = 0
  · refine ⟨1, (), fun j hj => hlat _ ?_⟩
    rw [map_one, Module.End.one_apply, ← hc0]
    exact toStd_single_eq_zero (hcj j hj) (hcn j hj)
  · have hc1 : 1 ≤ c.val := by
      have := Fin.val_ne_of_ne hc0
      simp only [Fin.val_zero] at this
      omega
    obtain ⟨v, -, -, hu⟩ := exists_spZeroSwap (by omega) c hc1
    refine ⟨v * (coxeterMatrix (isFiniteType_cartanC (n + 1))).toCoxeterSystem.simple 0 * v⁻¹, (),
      fun j hj => hlat _ ?_⟩
    refine (congrFun (hu (Pi.single j 1)) 0).trans ?_
    change 1 * toStd (n + 1) (Pi.single j 1) ((Equiv.swap 0 c).symm 0) = 0
    rw [Equiv.symm_swap, Equiv.swap_apply_left, one_mul]
    exact toStd_single_eq_zero (hcj j hj) (hcn j hj)

theorem spLevi_transitive {F : Type} [Field F] (hn : 1 ≤ n)
    (w : (coxeterMatrix (isFiniteType_cartanC (n + 1))).Group) {α : Fin (n + 1) → ℤ}
    (hα : α ∈ ggSupp (Symplectic.rootDatum (n + 1) F) (spLeviJ n))
    (hβ : weylAction (isFiniteType_cartanC (n + 1)) w α ∈
      ggSupp (Symplectic.rootDatum (n + 1) F) (spLeviJ n)) :
    ∃ v ∈ spLeviWeyl n, weylAction (isFiniteType_cartanC (n + 1)) v α =
      weylAction (isFiniteType_cartanC (n + 1)) w α := by
  obtain ⟨π, s, hs, hw⟩ := exists_spRealizes w
  obtain ⟨u, z₀, hu, hz₀, hv⟩ := spLevi_decomp hn hs hw
  set β := weylAction (isFiniteType_cartanC (n + 1)) w α with hβdef
  have hα0 : toStd (n + 1) α 0 = 0 := by
    rw [toStd_succ_apply_zero hn]
    exact (mem_ggSupp_spLeviJ_iff.mp hα).2
  have hβ0 : toStd (n + 1) β 0 = 0 := by
    rw [toStd_succ_apply_zero hn]
    exact (mem_ggSupp_spLeviJ_iff.mp hβ).2
  have hβπ : toStd (n + 1) β (π 0) = 0 := by
    have := congrFun (hw α) (π 0)
    rw [Equiv.symm_apply_apply, hα0, mul_zero] at this
    exact this
  have hufix : weylAction (isFiniteType_cartanC (n + 1)) u β = β := by
    rcases hu with rfl | hu
    · rw [map_one, Module.End.one_apply]
    · refine hu.fix fun b => ?_
      simp only [Pi.one_apply, one_mul, Equiv.symm_swap]
      rcases eq_or_ne b 0 with rfl | hb0
      · rw [Equiv.swap_apply_left, hβπ, hβ0]
      rcases eq_or_ne b (π 0) with rfl | hbc
      · rw [Equiv.swap_apply_right, hβ0, hβπ]
      · rw [Equiv.swap_apply_of_ne_of_ne hb0 hbc]
  have hzfix : weylAction (isFiniteType_cartanC (n + 1)) z₀ β = β := by
    rcases hz₀ with rfl | hz₀
    · rw [map_one, Module.End.one_apply]
    · refine hz₀.fix fun b => ?_
      change spSgn 0 b * toStd (n + 1) β b = toStd (n + 1) β b
      unfold spSgn
      split_ifs with hb
      · subst hb
        rw [hβ0]
        ring
      · ring
  refine ⟨z₀ * u * w, hv, ?_⟩
  rw [weylAction_mul_apply, weylAction_mul_apply, ← hβdef, hufix, hzfix]

@[expose] def spTwoEpsZero (n : ℕ) : Fin (n + 1) → ℤ := fun i => if i = Fin.last n then 1 else 2

theorem toStd_spTwoEpsZero (hn : 1 ≤ n) :
    toStd (n + 1) (spTwoEpsZero n) = Pi.single 0 2 := by
  funext a
  rw [toStd_apply_eq]
  by_cases ha0 : a.val = 0
  · have : a = 0 := Fin.ext ha0
    subst this
    have h1 : ¬ (0 < (0 : Fin (n + 1)).val) := by simp
    have h2 : ¬ ((0 : Fin (n + 1)).val + 1 = n + 1) := by simp; omega
    have h3 : (0 : Fin (n + 1)) ≠ Fin.last n := fun e => by
      have := congrArg Fin.val e
      simp at this
      omega
    rw [dite_eq_right h1, ite_eq_right h2]
    simp [spTwoEpsZero, h3]
  · have hpos : 0 < a.val := by omega
    rw [dite_eq_left hpos, Pi.single_eq_of_ne (fun e => ha0 (by rw [e]; rfl))]
    have hprev : (⟨a.val - 1, by omega⟩ : Fin (n + 1)) ≠ Fin.last n := fun e => by
      have := congrArg Fin.val e
      simp at this
      omega
    simp only [spTwoEpsZero, hprev, ite_false]
    by_cases hal : a = Fin.last n
    · subst hal
      simp
    · have hal' : ¬ (a.val = n) := fun e => hal (Fin.ext (by simp; omega))
      simp [hal, hal']

theorem spLevi_refl_mem {F : Type} [Field F] (hn : 1 ≤ n)
    (w : (coxeterMatrix (isFiniteType_cartanC (n + 1))).Group) (j : Fin (n + 1))
    (hj : weylAction (isFiniteType_cartanC (n + 1)) w (Pi.single j 1) ∈
      ggSupp (Symplectic.rootDatum (n + 1) F) (spLeviJ n)) :
    w * (coxeterMatrix (isFiniteType_cartanC (n + 1))).toCoxeterSystem.simple j * w⁻¹ ∈
      spLeviWeyl n := by
  obtain ⟨π, s, hs, hx⟩ := exists_spRealizes
    (w * (coxeterMatrix (isFiniteType_cartanC (n + 1))).toCoxeterSystem.simple j * w⁻¹)
  have hc : weylAction (isFiniteType_cartanC (n + 1))
      (w * (coxeterMatrix (isFiniteType_cartanC (n + 1))).toCoxeterSystem.simple j * w⁻¹)
        (spTwoEpsZero n) = spTwoEpsZero n -
          coroot (cartanC (n + 1)) j (weylAction (isFiniteType_cartanC (n + 1)) w⁻¹
            (spTwoEpsZero n)) •
            weylAction (isFiniteType_cartanC (n + 1)) w (Pi.single j 1) := by
    rw [weylAction_mul_apply, weylAction_mul_apply, weylAction_simple, reflection_apply_coroot,
      map_sub, map_zsmul, weylAction_apply_inv_apply]
  have hβ0 : toStd (n + 1) (weylAction (isFiniteType_cartanC (n + 1)) w (Pi.single j 1)) 0 = 0 := by
    rw [toStd_succ_apply_zero hn]
    exact (mem_ggSupp_spLeviJ_iff.mp hj).2
  have h0 := congrFun (hx (spTwoEpsZero n)) 0
  rw [hc, sub_eq_add_neg, toStd_add', toStd_neg', toStd_zsmul', Pi.add_apply, Pi.neg_apply,
    Pi.smul_apply, hβ0, smul_zero, neg_zero, add_zero, toStd_spTwoEpsZero hn,
    Pi.single_eq_same] at h0
  have hπ0 : π.symm 0 = 0 := by
    by_contra hne
    rw [Pi.single_eq_of_ne hne, mul_zero] at h0
    norm_num at h0
  rw [hπ0, Pi.single_eq_same] at h0
  have hs0 : s 0 = 1 := by
    rcases hs 0 with h | h
    · exact h
    · rw [h] at h0
      norm_num at h0
  have hπ : π 0 = 0 := by
    rw [← hπ0, Equiv.apply_symm_apply]
    exact hπ0.symm
  obtain ⟨v, hv, hvr⟩ := exists_spLeviW_of_fix hn hs hπ hs0
  rw [hx.inj hvr]
  exact hv

theorem spLevi_hnt {F : Type} [Field F] {X : Type*} [Group X] {φ₁ : StatedSp n F →* X}
    (hφ : Function.Injective φ₁) (hn : 1 ≤ n) :
    ∃ γ ∈ ggSupp (Symplectic.rootDatum (n + 1) F) (spLeviJ n),
      ∃ z ∈ rootGroup (n + 1) F γ, ggExt (spLeviHom φ₁) z ≠ 1 := by
  have hlast : ¬ (Fin.last n).val + 1 < n + 1 := by simp
  have hl0 : (0 : Fin (n + 1)) ≠ Fin.last n := fun e => by
    have := congrArg Fin.val e
    simp at this
    omega
  have hr : stdVec (RootSubgroupIndex.positiveLong (Fin.last n)) =
      toStd (n + 1) (Pi.single (Fin.last n) 1) := by
    rw [toStd_single_of_not_lt' hlast]
    rfl
  have hα : (Pi.single (Fin.last n) 1 : Fin (n + 1) → ℤ) ∈
      ggSupp (Symplectic.rootDatum (n + 1) F) (spLeviJ n) :=
    mem_ggSupp_spLeviJ_iff.mpr ⟨mem_roots_of_stdVec hr, Pi.single_eq_of_ne hl0 _⟩
  refine ⟨_, hα, elt (.positiveLong (Fin.last n)) 1, elt_mem_rootGroup hr 1, fun h1 => ?_⟩
  have hzL := rootGroup_le_ggSub (D := Symplectic.rootDatum (n + 1) F) hα (elt_mem_rootGroup hr 1)
  have key := ggExt_spLeviHom_injective hφ hzL (one_mem _) (h1.trans (ggExt_one _).symm)
  rw [← elt_zero (.positiveLong (Fin.last n))] at key
  exact one_ne_zero (elt_injective _ key)

end CFSG.StandardType

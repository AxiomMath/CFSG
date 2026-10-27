module

public import CFSG.RankThree.CentralLiftU.UnitaryWeyl
public import CFSG.RankThree.CentralLiftU.UnitaryTorus

public section

namespace CFSG.RankThree.CentralLiftU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (IsLinePerm)

variable {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) {r : ℕ}

theorem prod_cum_telescope (a : Fin r → K) (ha : ∀ l, a l ≠ 0) (x : Fin r) :
    (∏ m : Fin r, (if x = m then ∏ l ∈ Finset.Iic m, a l else 1) *
      (if x.val = m.val + 1 then (∏ l ∈ Finset.Iic m, a l)⁻¹ else 1)) = a x := by
  rw [Finset.prod_mul_distrib, Finset.prod_ite_eq, ite_eq_left (Finset.mem_univ _)]
  by_cases hx : x.val = 0
  · rw [Finset.prod_eq_one fun m _ => ite_eq_right (by omega), mul_one]
    have hI : Finset.Iic x = {x} := by
      ext l
      simp only [Finset.mem_Iic, Finset.mem_singleton, Fin.le_def, Fin.ext_iff]
      omega
    rw [hI, Finset.prod_singleton]
  · have hx1 : x.val - 1 < r := by omega
    set m₀ : Fin r := ⟨x.val - 1, hx1⟩ with hm₀
    rw [Finset.prod_eq_single m₀ (fun m _ hm => ite_eq_right fun e => hm (Fin.ext (by
      simp only [hm₀]
      omega))) (by simp), ite_eq_left (by simp only [hm₀]; omega)]
    have hI : Finset.Iic x = insert x (Finset.Iic m₀) := by
      ext l
      simp only [Finset.mem_Iic, Finset.mem_insert, Fin.le_def, Fin.ext_iff, hm₀]
      omega
    have hx' : x ∉ Finset.Iic m₀ := by
      simp only [Finset.mem_Iic, Fin.le_def, hm₀]
      omega
    have hP : ∏ l ∈ Finset.Iic m₀, a l ≠ 0 := Finset.prod_ne_zero_iff.2 fun l _ => ha l
    rw [hI, Finset.prod_insert hx', mul_assoc, mul_inv_cancel₀ hP, mul_one]

section Full

theorem prod_tcoord_mem (t : hypTorus h r 0) :
    (∏ l, ((tcoord h l t : Kˣ) : K)) ∈ h.fixedField := by
  obtain ⟨a, d, -, hp, hm⟩ := t.2
  have ha : ∀ l, ((tcoord h l t : Kˣ) : K) = a l := fun l => by
    rw [coe_tcoord_of_diag h l hm]
    rfl
  simp only [ha]
  rw [h.mem_fixedField, map_prod]
  have hp' : ∏ i, (a i : K) / h.bar (a i) = 1 := by simpa [torusRatio] using hp
  rw [Finset.prod_div_distrib] at hp'
  have hne : ∏ i, h.bar (a i : K) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => (map_ne_zero _).2 (a i).ne_zero
  exact ((div_eq_one_iff_eq hne).1 hp').symm

@[expose] noncomputable def fullCoord : hypTorus h r 0 →* h.fixedFieldˣ where
  toFun t := Units.mk0 ⟨∏ l, ((tcoord h l t : Kˣ) : K), prod_tcoord_mem h t⟩ (by
    intro h0
    have h1 : (∏ l, ((tcoord h l t : Kˣ) : K)) = 0 := congrArg Subtype.val h0
    exact (Finset.prod_ne_zero_iff.2 fun l _ => (tcoord h l t).ne_zero) h1)
  map_one' := by
    ext
    simp
  map_mul' t t' := by
    ext
    simp [Finset.prod_mul_distrib]

theorem coe_fullCoord (t : hypTorus h r 0) :
    (((fullCoord h t : h.fixedFieldˣ) : h.fixedField) : K) = ∏ l, ((tcoord h l t : Kˣ) : K) :=
  rfl

end Full

section Defs

variable {R : Type*} [Group R] (π : R →* hypSU h r 0) {c : K} (hc : c ∈ h.traceZero)
  (hc0 : c ≠ 0)

@[expose] def torusEvenGens : Set R :=
  {x | ∃ (i j : Fin r) (hij : i ≠ j) (t : Kˣ), hRho h π hij t = x} ∪
    {x | ∃ (k : Fin r) (b : h.fixedFieldˣ), hIota h π hc hc0 k b = x}

@[expose] noncomputable def torusEven : Subgroup R :=
  Subgroup.closure (torusEvenGens h π hc hc0)

theorem hRho_mem_torusEven {i j : Fin r} (hij : i ≠ j) (t : Kˣ) :
    hRho h π hij t ∈ torusEven h π hc hc0 :=
  Subgroup.subset_closure (Or.inl ⟨i, j, hij, t, rfl⟩)

theorem hIota_mem_torusEven (k : Fin r) (b : h.fixedFieldˣ) :
    hIota h π hc hc0 k b ∈ torusEven h π hc hc0 :=
  Subgroup.subset_closure (Or.inr ⟨k, b, rfl⟩)

@[expose] noncomputable def thetaEvenFactor (m : Fin r) : hypTorus h r 0 →* R :=
  if hm : m.val + 1 < r then (hRho h π (ne_succ_of_lt hm)).comp (cumCoord h m)
  else (hIota h π hc hc0 m).comp (fullCoord h)

theorem thetaEvenFactor_of_lt {m : Fin r} (hm : m.val + 1 < r) (t : hypTorus h r 0) :
    thetaEvenFactor h π hc hc0 m t = hRho h π (ne_succ_of_lt hm) (cumCoord h m t) := by
  rw [thetaEvenFactor, dite_eq_left hm]
  rfl

theorem thetaEvenFactor_of_not_lt {m : Fin r} (hm : ¬m.val + 1 < r) (t : hypTorus h r 0) :
    thetaEvenFactor h π hc hc0 m t = hIota h π hc hc0 m (fullCoord h t) := by
  rw [thetaEvenFactor, dite_eq_right hm]
  rfl

theorem thetaEvenFactor_mem (m : Fin r) (t : hypTorus h r 0) :
    thetaEvenFactor h π hc hc0 m t ∈ torusEven h π hc hc0 := by
  by_cases hm : m.val + 1 < r
  · rw [thetaEvenFactor_of_lt h π hc hc0 hm]
    exact hRho_mem_torusEven h π hc hc0 _ _
  · rw [thetaEvenFactor_of_not_lt h π hc hc0 hm]
    exact hIota_mem_torusEven h π hc hc0 _ _

end Defs

section Torus

variable {R : Type*} [Group R] [Finite R] {π : R →* hypSU h r 0} (hS : UHyp h π)
  {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0)
include hS

theorem gens_mem_hypTorus {x : R} (hx : x ∈ torusEvenGens h π hc hc0) :
    π x ∈ hypTorus h r 0 := by
  rcases hx with ⟨i, j, hij, t, rfl⟩ | ⟨k, b, rfl⟩
  · exact mem_hypTorus_of_diag h (coe_pi_hRho h hS hij t)
  · exact mem_hypTorus_of_diag h (coe_pi_hIota h hS hc hc0 k b)

theorem commute_gens_of_diag {x g : R} (hx : π x ∈ hypTorus h r 0)
    (hg : g ∈ torusEvenGens h π hc hc0) : Commute x g := by
  obtain ⟨a, d, -, -, hm⟩ := hx
  rcases hg with ⟨i, j, hij, t, rfl⟩ | ⟨k, b, rfl⟩
  · exact commute_of_conj_eq (conj_hRho_of_diag h hS hm hij t)
  · exact commute_of_conj_eq (conj_hIota_of_diag h hS hc hc0 hm k b)

theorem torusEven_commute {x y : R} (hx : x ∈ torusEven h π hc hc0)
    (hy : y ∈ torusEven h π hc hc0) : Commute x y := by
  have hcomm := Subgroup.isMulCommutative_closure (k := torusEvenGens h π hc hc0)
    (fun g hg g' hg' _ => commute_gens_of_diag h hS hc hc0 (gens_mem_hypTorus h hS hc hc0 hg) hg')
  exact congrArg Subtype.val (hcomm.is_comm.comm (⟨x, hx⟩ : torusEven h π hc hc0) ⟨y, hy⟩)

theorem torusEven_le : torusEven h π hc hc0 ≤ (hypTorus h r 0).comap π := by
  rw [torusEven, Subgroup.closure_le]
  intro x hx
  exact gens_mem_hypTorus h hS hc hc0 hx

theorem torusHyp_even : TorusHyp h π hc hc0 (torusEven h π hc hc0) where
  diag := torusEven_le h hS hc hc0
  rho _ _ hij t := hRho_mem_torusEven h π hc hc0 hij t
  iota k b := hIota_mem_torusEven h π hc hc0 k b

@[expose] noncomputable def thetaEven : hypTorus h r 0 →* R :=
  prodHom (thetaEvenFactor h π hc hc0) (fun i j _ x y =>
    torusEven_commute h hS hc hc0 (thetaEvenFactor_mem h π hc hc0 i x)
      (thetaEvenFactor_mem h π hc hc0 j y))

theorem thetaEven_apply (t : hypTorus h r 0) :
    thetaEven h hS hc hc0 t = (List.ofFn fun m => thetaEvenFactor h π hc hc0 m t).prod :=
  prodHom_apply _ _ t

theorem thetaEven_mem (t : hypTorus h r 0) : thetaEven h hS hc hc0 t ∈ torusEven h π hc hc0 := by
  rw [thetaEven_apply]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hx
  exact thetaEvenFactor_mem h π hc hc0 m t

theorem coe_pi_thetaEvenFactor (m : Fin r) (t : hypTorus h r 0) :
    ((π (thetaEvenFactor h π hc hc0 m t) : GL (HypIndex r 0) K) :
      Matrix (HypIndex r 0) (HypIndex r 0) K) =
      diagonal (if hm : m.val + 1 < r then rhoDiag h m ⟨m.val + 1, hm⟩ (cumCoord h m t)
        else iotaDiag h m (fullCoord h t)) := by
  by_cases hm : m.val + 1 < r
  · rw [thetaEvenFactor_of_lt h π hc hc0 hm, coe_pi_hRho h hS, dite_eq_left hm]
  · rw [thetaEvenFactor_of_not_lt h π hc hc0 hm, coe_pi_hIota h hS hc hc0, dite_eq_right hm]

theorem pi_thetaEven (t : hypTorus h r 0) : π (thetaEven h hS hc hc0 t) = t := by
  obtain ⟨a, d, -, -, hm⟩ := t.2
  have ha : ∀ l, ((tcoord h l t : Kˣ) : K) = a l := fun l => by
    rw [coe_tcoord_of_diag h l hm]
    rfl
  have hcum : ∀ m, ((cumCoord h m t : Kˣ) : K) = ∏ l ∈ Finset.Iic m, (a l : K) := fun m => by
    rw [cumCoord_apply, Units.coe_prod]
    exact Finset.prod_congr rfl fun l _ => ha l
  rw [thetaEven_apply, map_list_prod, List.map_ofFn]
  refine hypSU_eq_of_diag h (coe_prod_ofFn_of_diag h _ _
    fun m => coe_pi_thetaEvenFactor h hS hc hc0 m t) hm (fun x => ?_) (fun k => k.elim0)
  have key : ∀ m : Fin r,
      (if hm : m.val + 1 < r then rhoDiag (ε := 0) h m ⟨m.val + 1, hm⟩ (cumCoord h m t)
        else iotaDiag (ε := 0) h m (fullCoord h t)) (.inl x) =
      (if x = m then ∏ l ∈ Finset.Iic m, (a l : K) else 1) *
        (if x.val = m.val + 1 then (∏ l ∈ Finset.Iic m, (a l : K))⁻¹ else 1) := by
    intro m
    by_cases hm : m.val + 1 < r
    · rw [dite_eq_left hm]
      simp only [rhoDiag, Units.val_inv_eq_inv_val, hcum]
      by_cases hxm : x = m
      · have h1 : x.val ≠ m.val + 1 := by rw [hxm]; omega
        rw [ite_eq_left hxm, ite_eq_left hxm, ite_eq_right h1, mul_one]
      · by_cases hxm' : x.val = m.val + 1
        · rw [ite_eq_right hxm, ite_eq_left (Fin.ext hxm' : x = ⟨m.val + 1, hm⟩), ite_eq_right hxm,
            ite_eq_left hxm', one_mul]
        · have h2 : x ≠ ⟨m.val + 1, hm⟩ := fun e => hxm' (by rw [e])
          rw [ite_eq_right hxm, ite_eq_right h2, ite_eq_right hxm, ite_eq_right hxm', mul_one]
    · rw [dite_eq_right hm]
      have hxm' : x.val ≠ m.val + 1 := by
        have := x.isLt
        omega
      have hI : Finset.Iic m = Finset.univ := by
        ext l
        simp only [Finset.mem_Iic, Finset.mem_univ, iff_true, Fin.le_def]
        have := l.isLt
        omega
      simp only [iotaDiag, coe_fullCoord, ha, hI, ite_eq_right hxm', mul_one]
  simp only [key]
  exact prod_cum_telescope (fun l => (a l : K)) (fun l => (a l).ne_zero) x

theorem thetaEven_injective : Function.Injective (thetaEven h hS hc hc0) := fun t t' htt' =>
  Subtype.ext (by rw [← pi_thetaEven h hS hc hc0 t, ← pi_thetaEven h hS hc hc0 t', htt'])

theorem thetaEven_pi_hRho {i : Fin r} (hi : i.val + 1 < r) (s : Kˣ) :
    thetaEven h hS hc hc0 ⟨π (hRho h π (ne_succ_of_lt hi) s),
      mem_hypTorus_of_diag h (coe_pi_hRho h hS (ne_succ_of_lt hi) s)⟩ =
      hRho h π (ne_succ_of_lt hi) s := by
  have hii' : i ≠ ⟨i.val + 1, hi⟩ := ne_succ_of_lt hi
  have hco : ∀ l, tcoord h l ⟨π (hRho h π (ne_succ_of_lt hi) s),
      mem_hypTorus_of_diag h (coe_pi_hRho h hS (ne_succ_of_lt hi) s)⟩ =
      (Pi.mulSingle i s : Fin r → Kˣ) l *
        (Pi.mulSingle ⟨i.val + 1, hi⟩ s⁻¹ : Fin r → Kˣ) l := fun l => by
    ext
    rw [coe_tcoord_of_diag h l (coe_pi_hRho h hS (ne_succ_of_lt hi) s)]
    simp only [rhoDiag, Units.val_mul, Pi.mulSingle_apply]
    by_cases hl : l = i
    · rw [hl]
      simp [hii']
    · by_cases hl' : l = ⟨i.val + 1, hi⟩
      · rw [hl']
        simp [hii'.symm]
      · simp [hl, hl']
  have hle : ∀ m : Fin r, (⟨i.val + 1, hi⟩ : Fin r) ≤ m ↔ i.val + 1 ≤ m.val := fun m => Iff.rfl
  have hle' : ∀ m : Fin r, i ≤ m ↔ i.val ≤ m.val := fun m => Iff.rfl
  have hcum : ∀ m, cumCoord h m ⟨π (hRho h π (ne_succ_of_lt hi) s),
      mem_hypTorus_of_diag h (coe_pi_hRho h hS (ne_succ_of_lt hi) s)⟩ =
      if m = i then s else 1 := fun m => by
    rw [cumCoord_apply]
    simp only [hco]
    rw [Finset.prod_mul_distrib, Finset.prod_pi_mulSingle', Finset.prod_pi_mulSingle']
    simp only [Finset.mem_Iic]
    rcases lt_trichotomy m.val i.val with hlt | heq | hgt
    · have hm : m ≠ i := fun e => by rw [e] at hlt; omega
      rw [ite_eq_right (by rw [hle']; omega), ite_eq_right (by rw [hle]; omega),
        ite_eq_right hm, mul_one]
    · have hm : m = i := Fin.ext heq
      rw [ite_eq_left (by rw [hle']; omega), ite_eq_right (by rw [hle]; omega),
        ite_eq_left hm, mul_one]
    · have hm : m ≠ i := fun e => by rw [e] at hgt; omega
      rw [ite_eq_left (by rw [hle']; omega), ite_eq_left (by rw [hle]; omega),
        ite_eq_right hm, mul_inv_cancel]
  have hfull : fullCoord h ⟨π (hRho h π (ne_succ_of_lt hi) s),
      mem_hypTorus_of_diag h (coe_pi_hRho h hS (ne_succ_of_lt hi) s)⟩ = 1 := by
    ext
    rw [coe_fullCoord]
    simp only [hco, Units.val_mul, Finset.prod_mul_distrib]
    have e1 : ∏ x : Fin r, (((Pi.mulSingle i s : Fin r → Kˣ) x : Kˣ) : K) = s := by
      rw [← Units.coe_prod, Finset.prod_pi_mulSingle', ite_eq_left (Finset.mem_univ _)]
    have e2 : ∏ x : Fin r, (((Pi.mulSingle (⟨i.val + 1, hi⟩ : Fin r) s⁻¹ : Fin r → Kˣ) x : Kˣ) :
        K) =
        ((s⁻¹ : Kˣ) : K) := by
      rw [← Units.coe_prod, Finset.prod_pi_mulSingle', ite_eq_left (Finset.mem_univ _)]
    rw [e1, e2, Units.mul_inv]
    rfl
  rw [thetaEven_apply, prod_ofFn_eq_single _ i]
  · rw [thetaEvenFactor_of_lt h π hc hc0 hi, hcum, ite_eq_left rfl]
  · intro m hm
    by_cases hm' : m.val + 1 < r
    · rw [thetaEvenFactor_of_lt h π hc hc0 hm', hcum, ite_eq_right hm, map_one]
    · rw [thetaEvenFactor_of_not_lt h π hc hc0 hm', hfull, map_one]

theorem thetaEven_pi_hIota {k : Fin r} (hk : ¬k.val + 1 < r) (b : h.fixedFieldˣ) :
    thetaEven h hS hc hc0 ⟨π (hIota h π hc hc0 k b),
      mem_hypTorus_of_diag h (coe_pi_hIota h hS hc hc0 k b)⟩ = hIota h π hc hc0 k b := by
  set t₁ : hypTorus h r 0 := ⟨π (hIota h π hc hc0 k b),
    mem_hypTorus_of_diag h (coe_pi_hIota h hS hc hc0 k b)⟩
  have hco : ∀ l, tcoord h l t₁ = (Pi.mulSingle k (fcoe h b) : Fin r → Kˣ) l := fun l => by
    ext
    rw [coe_tcoord_of_diag h l (coe_pi_hIota h hS hc hc0 k b)]
    simp only [iotaDiag, Pi.mulSingle_apply]
    by_cases hl : l = k
    · rw [hl]
      simp [coe_fcoe]
    · simp [hl]
  have hfull : fullCoord h t₁ = b := by
    ext
    rw [coe_fullCoord]
    simp only [hco]
    rw [← Units.coe_prod, Finset.prod_pi_mulSingle', ite_eq_left (Finset.mem_univ _), coe_fcoe]
  rw [thetaEven_apply, prod_ofFn_eq_single _ k]
  · rw [thetaEvenFactor_of_not_lt h π hc hc0 hk, hfull]
  · intro m hm
    have hm' : m.val + 1 < r := by
      by_contra hc'
      have := m.isLt
      have := k.isLt
      exact hm (Fin.ext (by omega))
    have hcum : cumCoord h m t₁ = 1 := by
      rw [cumCoord_apply]
      simp only [hco]
      rw [Finset.prod_pi_mulSingle', ite_eq_right]
      simp only [Finset.mem_Iic, Fin.le_def]
      omega
    rw [thetaEvenFactor_of_lt h π hc hc0 hm', hcum, map_one]

theorem hRho_mem_range_of_lt {i j : Fin r} (hij : i ≠ j) (hlt : i.val < j.val) (s : Kˣ) :
    hRho h π hij s ∈ (thetaEven h hS hc hc0).range := by
  suffices key : ∀ d : ℕ, ∀ (i j : Fin r) (hij : i ≠ j), j.val = i.val + d + 1 →
      ∀ s, hRho h π hij s ∈ (thetaEven h hS hc hc0).range from
    key (j.val - i.val - 1) i j hij (by omega) s
  intro d
  induction d with
  | zero =>
    intro i j hij hj s
    have hi : i.val + 1 < r := by omega
    obtain rfl : j = ⟨i.val + 1, hi⟩ := Fin.ext (by simp only; omega)
    exact ⟨_, thetaEven_pi_hRho h hS hc hc0 hi s⟩
  | succ d ih =>
    intro i j hij hj s
    have hi : i.val + 1 < r := by omega
    set i' : Fin r := ⟨i.val + 1, hi⟩
    have hi'j : i' ≠ j := Fin.ne_of_val_ne (by simp only [i']; omega)
    rw [hRho_trans h hS (ne_succ_of_lt hi) hi'j hij]
    exact mul_mem ⟨_, thetaEven_pi_hRho h hS hc hc0 hi s⟩
      (ih i' j hi'j (by simp only [i']; omega) s)

theorem range_thetaEven : (thetaEven h hS hc hc0).range = torusEven h π hc hc0 := by
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    exact thetaEven_mem h hS hc hc0 t
  · have hrho : ∀ (i j : Fin r) (hij : i ≠ j) (s : Kˣ),
        hRho h π hij s ∈ (thetaEven h hS hc hc0).range := by
      intro i j hij s
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hlt
      · exact hRho_mem_range_of_lt h hS hc hc0 hij hlt s
      · rw [show hRho h π hij s = hRho h π hij.symm s⁻¹ from hRho_swap h hS hij.symm s]
        exact hRho_mem_range_of_lt h hS hc hc0 hij.symm hlt s⁻¹
    rw [torusEven, Subgroup.closure_le]
    rintro _ (⟨i, j, hij, s, rfl⟩ | ⟨k, b, rfl⟩)
    · exact hrho i j hij s
    · have hr : 0 < r := Nat.lt_of_le_of_lt (Nat.zero_le _) k.isLt
      set k₀ : Fin r := ⟨r - 1, by omega⟩
      have hk₀ : ¬k₀.val + 1 < r := by simp only [k₀]; omega
      by_cases hk : k = k₀
      · subst hk
        exact ⟨_, thetaEven_pi_hIota h hS hc hc0 hk₀ b⟩
      · rw [hIota_eq_hRho_mul h hS hc hc0 hk b]
        exact mul_mem (hrho _ _ hk _) ⟨_, thetaEven_pi_hIota h hS hc hc0 hk₀ b⟩

@[expose] noncomputable def thetaEvenEquiv : hypTorus h r 0 ≃* torusEven h π hc hc0 :=
  (MonoidHom.ofInjective (thetaEven_injective h hS hc hc0)).trans
    (MulEquiv.subgroupCongr (range_thetaEven h hS hc hc0))

theorem coe_thetaEvenEquiv (t : hypTorus h r 0) :
    ((thetaEvenEquiv h hS hc hc0 t : torusEven h π hc hc0) : R) = thetaEven h hS hc hc0 t := by
  rw [thetaEvenEquiv, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    MonoidHom.ofInjective_apply]

theorem injOn_pi_torusEven : Set.InjOn π (torusEven h π hc hc0) := by
  intro y hy y' hy' hyy'
  rw [SetLike.mem_coe, ← range_thetaEven h hS hc hc0] at hy hy'
  obtain ⟨t, rfl⟩ := hy
  obtain ⟨t', rfl⟩ := hy'
  rw [pi_thetaEven, pi_thetaEven] at hyy'
  rw [Subtype.ext hyy']

end Torus

theorem odd_unitary_higher_central_large_prime_lifted_torus_and_weyl_even {ℓ f : ℕ} {K : Type}
    [Field K] (h : UnitaryFieldData ℓ f K) (hℓ : Odd ℓ) {r : ℕ} (_hr : 2 ≤ r) {c : K}
    (hc : c ∈ h.traceZero) (hc0 : c ≠ 0) {R : Type*} [Group R] [Finite R]
    (π : R →* hypSU h r 0) (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center R)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpk : IsPGroup p π.ker) :
    (∀ (i j : Fin r) (hij : i ≠ j), π.comp (rhoLift h π hij) = rhoU h hij ∧
      ∀ ψ : SpecialLinearGroup (Fin 2) K →* R, π.comp ψ = rhoU h hij → ψ = rhoLift h π hij) ∧
    (∀ k : Fin r, π.comp (iotaLift h π hc hc0 k) = iotaU h hc hc0 k ∧
      ∀ ψ : SpecialLinearGroup (Fin 2) h.fixedField →* R, π.comp ψ = iotaU h hc hc0 k →
        ψ = iotaLift h π hc hc0 k) ∧
    IsMulCommutative (torusEven h π hc hc0) ∧
    (∀ (i j : Fin r) (hij : i ≠ j) (t : Kˣ), hRho h π hij t ∈ torusEven h π hc hc0) ∧
    (∃ θ : hypTorus h r 0 ≃* torusEven h π hc hc0, (∀ x, π (θ x) = x) ∧
      ∀ (x : hypTorus h r 0) (a : Fin r → Kˣ) (d : Fin 0 → Kˣ),
        (((x : hypSU h r 0) : GL (HypIndex r 0) K) : Matrix (HypIndex r 0) (HypIndex r 0) K) =
          diagonal (torusEntries h a d) →
        ∀ b : h.fixedFieldˣ, ((b : h.fixedField) : K) = ∏ i, (a i : K) →
        (θ x : R) = (List.ofFn fun i : Fin r => if hi : i.val + 1 < r then
          hRho h π (ne_succ_of_lt hi) (∏ l ∈ Finset.Iic i, a l) else hIota h π hc hc0 i b).prod) ∧
    torusEven h π hc hc0 ≤ liftWeylU h π hc hc0 (torusEven h π hc hc0) ∧
    liftWeylU h π hc hc0 (torusEven h π hc hc0) ≤
      Subgroup.normalizer (torusEven h π hc hc0 : Set R) ∧
    (∀ k : Fin r, vIota h π hc hc0 k ∈ liftWeylU h π hc hc0 (torusEven h π hc hc0)) ∧
    (∃ φ : liftWeylU h π hc hc0 (torusEven h π hc hc0) →* hypWeyl r,
      (∀ (n : liftWeylU h π hc hc0 (torusEven h π hc hc0)) (x y : HypIndex r 0),
        (((π n : hypSU h r 0) : GL (HypIndex r 0) K) : Matrix (HypIndex r 0) (HypIndex r 0) K)
          y x ≠ 0 ↔ y = weylPerm (φ n : Equiv.Perm (Fin r ⊕ Fin r)) x) ∧
      Function.Surjective φ ∧
      φ.ker = (torusEven h π hc hc0).subgroupOf (liftWeylU h π hc hc0 (torusEven h π hc hc0)) ∧
      ∃ _ : ((torusEven h π hc hc0).subgroupOf
          (liftWeylU h π hc hc0 (torusEven h π hc hc0))).Normal,
        ∃ e : liftWeylU h π hc hc0 (torusEven h π hc hc0) ⧸
            (torusEven h π hc hc0).subgroupOf (liftWeylU h π hc hc0 (torusEven h π hc hc0)) ≃*
              hypWeyl r,
          ∀ n : liftWeylU h π hc hc0 (torusEven h π hc hc0), e n = φ n) ∧
    Function.Injective (π.comp (liftWeylU h π hc hc0 (torusEven h π hc hc0)).subtype) ∧
    ∀ i : Fin r, sLift h π hc hc0 i ^ 2 ∈ torusEven h π hc hc0 := by
  have hℓ2 : ℓ ≠ 2 := fun e => by
    rw [e] at hℓ
    exact absurd hℓ (by decide)
  have hS : UHyp h π := ⟨hℓ2, ⟨hπ, hcen, ⟨p, hp, hp3, hpk⟩⟩⟩
  have hT := torusHyp_even h hS hc hc0
  have hN := normal_subgroupOf_liftWeylU h hS hc hc0 hT
  have := h.finite
  refine ⟨fun i j hij => ⟨?_, fun ψ hψ => ?_⟩, fun k => ⟨?_, fun ψ hψ => ?_⟩,
    ⟨⟨fun x y => Subtype.ext (torusEven_commute h hS hc hc0 x.2 y.2).eq⟩⟩,
    fun i j hij t => hRho_mem_torusEven h π hc hc0 hij t,
    ⟨thetaEvenEquiv h hS hc hc0, fun x => by rw [coe_thetaEvenEquiv, pi_thetaEven],
      fun x a d hx b hb => ?_⟩,
    le_liftWeylU h π hc hc0 _, liftWeylU_le_normalizer h hS hc hc0 hT,
    fun k => vIota_mem_liftWeylU h hS hc hc0 k,
    ⟨weylHomU h hS hc hc0 hT, fun n x y => isLinePerm_weylHomU h hS hc hc0 hT n x y,
      weylHomU_surjective h hS hc hc0 hT, ker_weylHomU h hS hc hc0 hT, hN,
      weylQuotEquivU h hS hc hc0 hT, weylQuotEquivU_mk h hS hc hc0 hT⟩,
    injective_pi_liftWeylU h hS hc hc0 hT (injOn_pi_torusEven h hS hc hc0),
    fun i => by rw [sq]; exact sLift_mul_self_mem h hc hc0 hT i⟩
  · exact CFSG.RankThree.CentralLift.comp_sl2Lift_large hS.charK hS.large _
  · exact CFSG.RankThree.CentralLift.eq_sl2Lift_large hS.charK hS.large hψ
  · exact CFSG.RankThree.CentralLift.comp_sl2Lift_large hS.charF hS.large _
  · exact CFSG.RankThree.CentralLift.eq_sl2Lift_large hS.charF hS.large hψ
  · have ha : ∀ l, tcoord h l x = a l := fun l => by
      ext
      rw [coe_tcoord_of_diag h l hx]
      rfl
    rw [coe_thetaEvenEquiv, thetaEven_apply]
    congr 1
    refine List.ofFn_inj.2 (funext fun m => ?_)
    by_cases hm : m.val + 1 < r
    · rw [thetaEvenFactor_of_lt h π hc hc0 hm, dite_eq_left hm, cumCoord_apply]
      simp only [ha]
    · rw [thetaEvenFactor_of_not_lt h π hc hc0 hm, dite_eq_right hm]
      congr 1
      ext
      rw [coe_fullCoord, hb]
      simp only [ha]

end CFSG.RankThree.CentralLiftU

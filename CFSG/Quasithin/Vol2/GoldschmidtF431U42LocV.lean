module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Pair4

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin U42F431

@[expose] def fixL0 (g : PL) : Bool := L0.all fun p => g.getD p 0 == p

@[expose] def subProdL : List ℕ → ℕ → PL
  | [], _ => idL
  | p :: l, s => if s % 2 = 1 then comp (tpTab.getD p []) (subProdL l (s / 2))
      else subProdL l (s / 2)

@[expose] def chkVprod : Bool := (List.range 64).all fun i =>
  !fixL0 (Tl.getD i []) || (List.range 32).any fun s => subProdL L0 s == Tl.getD i []

@[expose] def chkVgen : Bool := L0.all fun p => fixL0 (tpTab.getD p []) &&
  L0.all fun q => comp (tpTab.getD p []) (tpTab.getD q []) ==
    comp (tpTab.getD q []) (tpTab.getD p [])

@[expose] def vFin : Finset ℕ := (Finset.range 64).filter fun i => fixL0 (Tl.getD i []) = true

theorem chkVprod_true : chkVprod = true := by decide +kernel

theorem chkVgen_true : chkVgen = true := by decide +kernel

theorem card_vFin : vFin.card = 16 := by decide +kernel

theorem fixL0_iff {l : PL} {g : P45} (h : RepL l g) :
    fixL0 l = true ↔ ∀ p : Fin 45, p ∈ L0S → g p = p := by
  simp only [fixL0, List.all_eq_true, beq_iff_eq]
  constructor
  · intro hf p hp
    have h1 := hf p.val hp
    apply Fin.ext
    rw [← h.2 p]
    exact h1
  · intro hf p hp
    have hp45 : p < 45 := L0_lt p hp
    have h2 := hf ⟨p, hp45⟩ hp
    rw [h.2 ⟨p, hp45⟩]
    exact congrArg Fin.val h2

theorem repL_sY (p : Fin 45) :
    RepL (tpTab.getD p []) ((sY p : Y) : P45) := by
  rw [tpTab_getD _ p.2]
  exact repL_sT p

theorem exists_conj_xY (p : Fin 45) :
    ∃ c : Y, (c : P45) 0 = p ∧ c * xY * c⁻¹ = sY p := by
  refine ⟨⟨wordP (wpW.getD p []), wordP_mem _⟩, point_move p, ?_⟩
  have h := sY_conj (⟨wordP (wpW.getD p []), wordP_mem _⟩ : Y) 0
  rw [sY_zero] at h
  rw [h]
  exact congrArg sY (point_move p)

theorem sY_sq (p : Fin 45) : sY p * sY p = 1 := by
  obtain ⟨c, -, hc⟩ := exists_conj_xY p
  rw [← hc]
  calc c * xY * c⁻¹ * (c * xY * c⁻¹) = c * (xY * xY) * c⁻¹ := by group
    _ = 1 := by rw [xY_sq]; group

theorem isConj_xY_sY (p : Fin 45) : IsConj xY (sY p) := by
  obtain ⟨c, -, hc⟩ := exists_conj_xY p
  exact isConj_iff.2 ⟨c, hc⟩

theorem exists_sY_of_isConj {a : Y} (h : IsConj xY a) :
    ∃ q : Fin 45, a = sY q := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  refine ⟨(c : P45) 0, ?_⟩
  rw [← hc, ← sY_zero, sY_conj]

theorem sY_comm {p q : Fin 45} (hp : p ∈ L0S) (hq : q ∈ L0S) :
    sY p * sY q = sY q * sY p := by
  have h := chkVgen_true
  simp only [chkVgen, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  have h2 := (h p.val hp).2 q.val hq
  refine Subtype.ext (eq_of_repL (l := comp (tpTab.getD p []) (tpTab.getD q []))
    (repL_mul (repL_sY p) (repL_sY q)) ?_)
  rw [h2]
  exact repL_mul (repL_sY q) (repL_sY p)

theorem sY_fix {p q : Fin 45} (hp : p ∈ L0S) (hq : q ∈ L0S) :
    ((sY p : Y) : P45) q = q := by
  have h := chkVgen_true
  simp only [chkVgen, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  exact (fixL0_iff (repL_sY p)).1 (h p.val hp).1 q hq

theorem Vsub_gen_comm :
    ∀ x ∈ {g : Y | ∃ p : Fin 45, p ∈ L0S ∧ g = sY p},
      ∀ y ∈ {g : Y | ∃ p : Fin 45, p ∈ L0S ∧ g = sY p}, x * y = y * x := by
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
  exact sY_comm hp hq

theorem Vsub_comm {a b : Y} (ha : a ∈ Vsub) (hb : b ∈ Vsub) :
    a * b = b * a := by
  have hpair : ({g : Y | ∃ p : Fin 45, p ∈ L0S ∧ g = sY p}).Pairwise Commute :=
    fun x hx y hy _ => Vsub_gen_comm x hx y hy
  have : IsMulCommutative ↥Vsub := Subgroup.isMulCommutative_closure hpair
  exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨a, ha⟩ : Vsub) ⟨b, hb⟩)

theorem Vsub_sq {a : Y} (ha : a ∈ Vsub) : a * a = 1 := by
  refine Subgroup.closure_induction (p := fun x _ => x * x = 1) ?_ ?_ ?_ ?_ ha
  · rintro _ ⟨p, hp, rfl⟩
    exact sY_sq p
  · simp
  · intro x y hx hy hx2 hy2
    have hc : x * y = y * x := Vsub_comm hx hy
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hc]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hx2, hy2]; group
  · intro x _ hx
    calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
      _ = 1 := by rw [hx]; simp

theorem Vsub_fix {v : Y} (hv : v ∈ Vsub) :
    ∀ p : Fin 45, p ∈ L0S → (v : P45) p = p := by
  refine Subgroup.closure_induction (p := fun (x : Y) _ => ∀ p : Fin 45, p ∈ L0S → (x : P45) p = p)
    ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨q, hq, rfl⟩ p hp
    exact sY_fix hq hp
  · intro p _
    rfl
  · intro x y _ _ hx hy p hp
    show (x : P45) ((y : P45) p) = p
    rw [hy p hp, hx p hp]
  · intro x _ hx p hp
    show ((x : P45)⁻¹) p = p
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact (hx p hp).symm

@[expose] def sYn (p : ℕ) : Y := if h : p < 45 then sY ⟨p, h⟩ else 1

@[expose] def subProdY : List ℕ → ℕ → Y
  | [], _ => 1
  | p :: l, s => if s % 2 = 1 then sYn p * subProdY l (s / 2) else subProdY l (s / 2)

theorem repL_subProdY {l : List ℕ} (hl : ∀ p ∈ l, p < 45) (s : ℕ) :
    RepL (subProdL l s) ((subProdY l s : Y) : P45) := by
  induction l generalizing s with
  | nil => exact repL_one 45
  | cons p l ih =>
    have hp : p < 45 := hl p (by simp)
    have hl' : ∀ q ∈ l, q < 45 := fun q hq => hl q (by simp [hq])
    simp only [subProdL, subProdY]
    split_ifs
    · have h1 : RepL (tpTab.getD p []) ((sYn p : Y) : P45) := by
        simp only [sYn, hp, ↓reduceDIte]
        exact repL_sY ⟨p, hp⟩
      exact repL_mul h1 (ih hl' _)
    · exact ih hl' _

theorem subProdY_mem {l : List ℕ} (hl : ∀ p ∈ l, p ∈ L0) (s : ℕ) :
    subProdY l s ∈ Vsub := by
  induction l generalizing s with
  | nil => exact Vsub.one_mem
  | cons p l ih =>
    have hp : p ∈ L0 := hl p (by simp)
    have hl' : ∀ q ∈ l, q ∈ L0 := fun q hq => hl q (by simp [hq])
    simp only [subProdY]
    split_ifs
    · refine Vsub.mul_mem ?_ (ih hl' _)
      have hp45 : p < 45 := L0_lt p hp
      simp only [sYn, hp45, ↓reduceDIte]
      exact Subgroup.subset_closure ⟨⟨p, hp45⟩, hp, rfl⟩
    · exact ih hl' _

theorem mem_Vsub_of_fix {g : Y} (hgT : g ∈ T)
    (hg : ∀ p : Fin 45, p ∈ L0S → (g : P45) p = p) : g ∈ Vsub := by
  obtain ⟨i, hi, hrep⟩ := (mem_T_iff g).1 hgT
  have hf : fixL0 (Tl.getD i []) = true := (fixL0_iff hrep).2 hg
  have h := chkVprod_true
  simp only [chkVprod, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    List.any_eq_true, beq_iff_eq] at h
  rcases h i hi with h1 | ⟨s, -, hs⟩
  · rw [hf] at h1
    exact absurd h1 (by simp)
  · have hl : ∀ p ∈ L0, p < 45 := fun p hp => L0_lt p hp
    have hrep' := repL_subProdY hl s
    rw [hs] at hrep'
    have : g = subProdY L0 s := Subtype.ext (eq_of_repL hrep hrep')
    rw [this]
    exact subProdY_mem (fun p hp => hp) s

theorem mem_Vsub_iff {g : Y} :
    g ∈ Vsub ↔ g ∈ T ∧ ∀ p : Fin 45, p ∈ L0S → (g : P45) p = p :=
  ⟨fun h => ⟨Vsub_le_T h, Vsub_fix h⟩, fun h => mem_Vsub_of_fix h.1 h.2⟩

theorem card_Vsub_ge : 16 ≤ Nat.card Vsub := by
  choose! Tel hTel using fun (i : ℕ) (hi : i < 64) => exists_Tel (i := i) hi
  have hmem : ∀ i ∈ vFin, Tel i ∈ Vsub := by
    intro i hi
    simp only [vFin, Finset.mem_filter, Finset.mem_range] at hi
    have h := hTel i hi.1
    exact mem_Vsub_of_fix h.1 ((fixL0_iff h.2).1 hi.2)
  let f : vFin → Vsub := fun i => ⟨Tel i, hmem i i.2⟩
  have hinj : Function.Injective f := by
    intro i j hij
    have hi : (i : ℕ) < 64 := by
      have := i.2
      simp only [vFin, Finset.mem_filter, Finset.mem_range] at this
      exact this.1
    have hj : (j : ℕ) < 64 := by
      have := j.2
      simp only [vFin, Finset.mem_filter, Finset.mem_range] at this
      exact this.1
    have h1 := hTel i hi
    have h2 := hTel j hj
    have hij' : Tel i = Tel j := congrArg Subtype.val hij
    have hl : Tl.getD i [] = Tl.getD j [] := repL_unique h1.2 (hij' ▸ h2.2)
    rcases chkT_spec.2.2.2.2.2.1 i hi j hj with h | h
    · exact Subtype.ext h
    · exact absurd hl h
  have := Nat.card_le_card_of_injective f hinj
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, card_vFin] at this
  exact this

end CFSG.Quasithin.H13.F431.U42

module

public import CFSG.Quasithin.Background.HSL
public import CFSG.Quasithin.Background.HPair

public section

namespace CFSG.Quasithin

namespace H

namespace SL3Pair

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix
open scoped Matrix

variable {K : Type} [Field K]

@[expose] def dualGL (g : GL (Fin 3) K) : GL (Fin 3) K where
  val := ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ
  inv := (g : Matrix (Fin 3) (Fin 3) K)ᵀ
  val_inv := by rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.transpose_one]
  inv_val := by rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.transpose_one]

theorem coe_dualGL (g : GL (Fin 3) K) :
    ((dualGL g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ := rfl

@[expose] def dualHom : GL (Fin 3) K →* GL (Fin 3) K where
  toFun := dualGL
  map_one' := Units.ext (by rw [coe_dualGL, inv_one, Units.val_one, Matrix.transpose_one])
  map_mul' g h := Units.ext (by
    rw [coe_dualGL, Units.val_mul, coe_dualGL, coe_dualGL, _root_.mul_inv_rev, Units.val_mul,
      Matrix.transpose_mul])

theorem dualHom_apply (g : GL (Fin 3) K) : dualHom g = dualGL g := rfl

theorem dualGL_dualGL (g : GL (Fin 3) K) : dualGL (dualGL g) = g := by
  apply Units.ext
  rw [coe_dualGL]
  have : ((dualGL g)⁻¹ : GL (Fin 3) K) = dualGL g⁻¹ := by
    rw [← dualHom_apply, ← dualHom_apply, map_inv]
  rw [this, coe_dualGL, inv_inv, Matrix.transpose_transpose]

theorem det_dualGL (g : GL (Fin 3) K) :
    ((dualGL g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det =
      ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det := by
  rw [coe_dualGL, Matrix.det_transpose]

theorem mem_statedSL_iff {g : GL (Fin 3) K} :
    g ∈ StatedSL 3 K ↔ (g : Matrix (Fin 3) (Fin 3) K).det = 1 :=
  CFSG.Open.StatedAPI.mem_statedSL_iff

theorem dualGL_mem {g : GL (Fin 3) K} (hg : g ∈ StatedSL 3 K) : dualGL g ∈ StatedSL 3 K := by
  rw [mem_statedSL_iff] at hg ⊢
  rw [det_dualGL]
  have h1 : ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det *
      (g : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
  rw [hg, mul_one] at h1
  exact h1

abbrev PairMod (K : Type) [Field K] := StdMod (Fin 3) K × StdMod (Fin 3) K

@[expose] def pairAut (a b : MulAut (StdMod (Fin 3) K)) : MulAut (PairMod K) :=
  MulEquiv.prodCongr a b

@[simp] theorem pairAut_apply (a b : MulAut (StdMod (Fin 3) K)) (x : PairMod K) :
    pairAut a b x = (a x.1, b x.2) := rfl

theorem pairAut_mul (a b a' b' : MulAut (StdMod (Fin 3) K)) :
    pairAut a b * pairAut a' b' = pairAut (a * a') (b * b') := rfl

theorem pairAut_one : pairAut (1 : MulAut (StdMod (Fin 3) K)) 1 = 1 := rfl

theorem pairAut_inv (a b : MulAut (StdMod (Fin 3) K)) :
    (pairAut a b)⁻¹ = pairAut a⁻¹ b⁻¹ := rfl

@[expose] def pairHom : GL (Fin 3) K →* MulAut (PairMod K) where
  toFun g := pairAut (matAut g) (matAut (dualGL g))
  map_one' := by
    rw [← dualHom_apply, map_one, ← matHom_apply, map_one]
    rfl
  map_mul' g h := by
    rw [← dualHom_apply, ← dualHom_apply, ← dualHom_apply, map_mul, ← matHom_apply,
      ← matHom_apply, ← matHom_apply, ← matHom_apply, ← matHom_apply, ← matHom_apply, map_mul,
      map_mul, pairAut_mul]

theorem pairHom_apply (g : GL (Fin 3) K) :
    pairHom g = pairAut (matAut g) (matAut (dualGL g)) := rfl

@[expose] noncomputable def pairSL (K : Type) [Field K] : Subgroup (MulAut (PairMod K)) :=
  (StatedSL 3 K).map pairHom

@[expose] def V₁ (K : Type) [Field K] : Subgroup (PairMod K) := (⊤ : Subgroup _).prod ⊥

@[expose] def V₂ (K : Type) [Field K] : Subgroup (PairMod K) := (⊥ : Subgroup _).prod ⊤

theorem mem_V₁ {x : PairMod K} : x ∈ V₁ K ↔ x.2 = 1 := by
  simp [V₁, Subgroup.mem_prod]

theorem mem_V₂ {x : PairMod K} : x ∈ V₂ K ↔ x.1 = 1 := by
  simp [V₂, Subgroup.mem_prod]

theorem V₁_inf_V₂ : V₁ K ⊓ V₂ K = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hx
  rw [mem_V₁] at h1
  rw [mem_V₂] at h2
  exact Prod.ext h2 h1

theorem V₁_sup_V₂ : V₁ K ⊔ V₂ K = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨a, b⟩ -
  refine Subgroup.mem_sup.mpr ⟨(a, 1), mem_V₁.mpr rfl, (1, b), mem_V₂.mpr rfl, ?_⟩
  simp

theorem transvection_inv' {d : ℕ} (i j : Fin d) (h : i ≠ j) (c : K) :
    (Matrix.transvection i j c)⁻¹ = Matrix.transvection i j (-c) := by
  apply Matrix.inv_eq_left_inv
  have := transvection_mul_transvection_same (i := i) (j := j) (R := K) h (-c) c
  rw [this, neg_add_cancel, transvection_zero]

theorem transvection_transpose' {d : ℕ} (i j : Fin d) (c : K) :
    (Matrix.transvection i j c)ᵀ = Matrix.transvection j i c := by
  ext a b
  simp only [transvection, transpose_apply, Matrix.add_apply, one_apply, single_apply]
  by_cases h1 : b = a <;> by_cases h2 : i = b <;> by_cases h3 : j = a <;> simp_all [eq_comm]

@[expose] noncomputable def tGL (i j : Fin 3) (h : i ≠ j) (c : K) : GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection i j c)
    (by rw [Matrix.det_transvection_of_ne i j h c]; exact one_ne_zero)

theorem coe_tGL (i j : Fin 3) (h : i ≠ j) (c : K) :
    ((tGL i j h c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.transvection i j c := rfl

theorem tGL_mem (i j : Fin 3) (h : i ≠ j) (c : K) : tGL i j h c ∈ StatedSL 3 K :=
  mem_statedSL_iff.mpr (Matrix.det_transvection_of_ne i j h c)

theorem coe_dualGL_tGL (i j : Fin 3) (h : i ≠ j) (c : K) :
    ((dualGL (tGL i j h c) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.transvection j i (-c) := by
  rw [coe_dualGL, Matrix.coe_units_inv, coe_tGL, transvection_inv' i j h c,
    transvection_transpose']

theorem isInv_V₁ : Pair.IsInv (pairSL K) (V₁ K) := by
  rintro _ ⟨g, -, rfl⟩ x hx
  rw [mem_V₁] at hx ⊢
  rw [pairHom_apply, pairAut_apply, hx, map_one]

theorem isInv_V₂ : Pair.IsInv (pairSL K) (V₂ K) := by
  rintro _ ⟨g, -, rfl⟩ x hx
  rw [mem_V₂] at hx ⊢
  rw [pairHom_apply, pairAut_apply, hx, map_one]

theorem isIrr_V₁ : Pair.IsIrr (pairSL K) (V₁ K) := by
  refine ⟨?_, fun U hUV hU => ?_⟩
  · intro h
    have h1 : ((Multiplicative.ofAdd (Pi.single (0 : Fin 3) (1 : K)), 1) : PairMod K) ∈ V₁ K :=
      mem_V₁.mpr rfl
    rw [h, Subgroup.mem_bot] at h1
    have := congrArg (fun x : PairMod K => Multiplicative.toAdd x.1 0) h1
    simp at this
  · let U' : AddSubgroup (Fin 3 → K) :=
      { carrier := {v | ((Multiplicative.ofAdd v, 1) : PairMod K) ∈ U}
        add_mem' := fun {a b} ha hb => by
          have := U.mul_mem ha hb
          simpa using this
        zero_mem' := U.one_mem
        neg_mem' := fun {a} ha => by
          have := U.inv_mem ha
          simpa using this }
    have hU' : ∀ i j : Fin 3, i ≠ j → ∀ c : K, ∀ u ∈ U',
        Matrix.transvection i j c *ᵥ u ∈ U' := by
      intro i j hij c u hu
      have := hU _ ⟨tGL i j hij c, tGL_mem i j hij c, rfl⟩ _ hu
      have e : pairHom (tGL i j hij c) ((Multiplicative.ofAdd u, 1) : PairMod K) =
          (Multiplicative.ofAdd (Matrix.transvection i j c *ᵥ u), 1) := by
        rw [pairHom_apply, pairAut_apply, map_one]
        rfl
      rw [e] at this
      exact this
    rcases eq_bot_or_eq_top_of_transvection_inv (by norm_num) U' hU' with h | h
    · left
      rw [eq_bot_iff]
      intro x hx
      have hx2 : x.2 = 1 := mem_V₁.mp (hUV hx)
      have hx' : Multiplicative.toAdd x.1 ∈ U' := by
        change ((Multiplicative.ofAdd (Multiplicative.toAdd x.1), 1) : PairMod K) ∈ U
        rw [ofAdd_toAdd, ← hx2]
        exact hx
      rw [h, AddSubgroup.mem_bot] at hx'
      rw [Subgroup.mem_bot]
      exact Prod.ext (by simpa using congrArg Multiplicative.ofAdd hx') hx2
    · right
      apply le_antisymm hUV
      intro x hx
      have hx2 : x.2 = 1 := mem_V₁.mp hx
      have hx' : Multiplicative.toAdd x.1 ∈ U' := by rw [h]; trivial
      change ((Multiplicative.ofAdd (Multiplicative.toAdd x.1), 1) : PairMod K) ∈ U at hx'
      rw [ofAdd_toAdd, ← hx2] at hx'
      exact hx'

theorem isIrr_V₂ : Pair.IsIrr (pairSL K) (V₂ K) := by
  refine ⟨?_, fun U hUV hU => ?_⟩
  · intro h
    have h1 : ((1, Multiplicative.ofAdd (Pi.single (0 : Fin 3) (1 : K))) : PairMod K) ∈ V₂ K :=
      mem_V₂.mpr rfl
    rw [h, Subgroup.mem_bot] at h1
    have := congrArg (fun x : PairMod K => Multiplicative.toAdd x.2 0) h1
    simp at this
  · let U' : AddSubgroup (Fin 3 → K) :=
      { carrier := {v | ((1, Multiplicative.ofAdd v) : PairMod K) ∈ U}
        add_mem' := fun {a b} ha hb => by
          have := U.mul_mem ha hb
          simpa using this
        zero_mem' := U.one_mem
        neg_mem' := fun {a} ha => by
          have := U.inv_mem ha
          simpa using this }
    have hU' : ∀ i j : Fin 3, i ≠ j → ∀ c : K, ∀ u ∈ U',
        Matrix.transvection i j c *ᵥ u ∈ U' := by
      intro i j hij c u hu
      have := hU _ ⟨dualGL (tGL i j hij c), dualGL_mem (tGL_mem i j hij c), rfl⟩ _ hu
      have e : pairHom (dualGL (tGL i j hij c)) ((1, Multiplicative.ofAdd u) : PairMod K) =
          (1, Multiplicative.ofAdd (Matrix.transvection i j c *ᵥ u)) := by
        rw [pairHom_apply, pairAut_apply, map_one, dualGL_dualGL]
        rfl
      rw [e] at this
      exact this
    rcases eq_bot_or_eq_top_of_transvection_inv (by norm_num) U' hU' with h | h
    · left
      rw [eq_bot_iff]
      intro x hx
      have hx1 : x.1 = 1 := mem_V₂.mp (hUV hx)
      have hx' : Multiplicative.toAdd x.2 ∈ U' := by
        change ((1, Multiplicative.ofAdd (Multiplicative.toAdd x.2)) : PairMod K) ∈ U
        rw [ofAdd_toAdd, ← hx1]
        exact hx
      rw [h, AddSubgroup.mem_bot] at hx'
      rw [Subgroup.mem_bot]
      exact Prod.ext hx1 (by simpa using congrArg Multiplicative.ofAdd hx')
    · right
      apply le_antisymm hUV
      intro x hx
      have hx1 : x.1 = 1 := mem_V₂.mp hx
      have hx' : Multiplicative.toAdd x.2 ∈ U' := by rw [h]; trivial
      change ((1, Multiplicative.ofAdd (Multiplicative.toAdd x.2)) : PairMod K) ∈ U at hx'
      rw [ofAdd_toAdd, ← hx1] at hx'
      exact hx'

theorem not_isoMod [Finite K] : ¬ Pair.IsoMod (pairSL K) (V₁ K) (V₂ K) := by
  rintro ⟨e, he⟩
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  set l₁ := pairHom (tGL 0 2 h02 (1 : K)) with hl₁
  set l₂ := pairHom (tGL 1 2 h12 (1 : K)) with hl₂
  have hl₁m : l₁ ∈ pairSL K := ⟨_, tGL_mem _ _ _ _, rfl⟩
  have hl₂m : l₂ ∈ pairSL K := ⟨_, tGL_mem _ _ _ _, rfl⟩
  have a₁ : ∀ u : Fin 3 → K, l₁ ((Multiplicative.ofAdd u, 1) : PairMod K) =
      (Multiplicative.ofAdd (u + Pi.single 0 (1 * u 2)), 1) := by
    intro u
    rw [hl₁, pairHom_apply, pairAut_apply, map_one, ← transvection_mulVec]
    rfl
  have a₂ : ∀ u : Fin 3 → K, l₂ ((Multiplicative.ofAdd u, 1) : PairMod K) =
      (Multiplicative.ofAdd (u + Pi.single 1 (1 * u 2)), 1) := by
    intro u
    rw [hl₂, pairHom_apply, pairAut_apply, map_one, ← transvection_mulVec]
    rfl
  have b₁ : ∀ w : Fin 3 → K, l₁ ((1, Multiplicative.ofAdd w) : PairMod K) =
      (1, Multiplicative.ofAdd (w + Pi.single 2 (-1 * w 0))) := by
    intro w
    rw [hl₁, pairHom_apply, pairAut_apply, map_one, ← transvection_mulVec, ← coe_dualGL_tGL]
    rfl
  have b₂ : ∀ w : Fin 3 → K, l₂ ((1, Multiplicative.ofAdd w) : PairMod K) =
      (1, Multiplicative.ofAdd (w + Pi.single 2 (-1 * w 1))) := by
    intro w
    rw [hl₂, pairHom_apply, pairAut_apply, map_one, ← transvection_mulVec, ← coe_dualGL_tGL]
    rfl
  let F₁ := {v : V₁ K // l₁ v = v ∧ l₂ v = v}
  let F₂ := {w : V₂ K // l₁ w = w ∧ l₂ w = w}
  have hfix : ∀ v : V₁ K, l₁ v = v → l₂ v = v → l₁ (e v) = e v ∧ l₂ (e v) = e v := by
    intro v h1 h2
    have e1 := he l₁ hl₁m v (by rw [h1]; exact v.2)
    have e2 := he l₂ hl₂m v (by rw [h2]; exact v.2)
    have v1 : (⟨l₁ v, by rw [h1]; exact v.2⟩ : V₁ K) = v := Subtype.ext h1
    have v2 : (⟨l₂ v, by rw [h2]; exact v.2⟩ : V₁ K) = v := Subtype.ext h2
    rw [v1] at e1
    rw [v2] at e2
    exact ⟨e1.symm, e2.symm⟩
  have hinj : Nat.card F₁ ≤ Nat.card F₂ := by
    refine Nat.card_le_card_of_injective (fun v => ⟨e v.1, hfix v.1 v.2.1 v.2.2⟩) ?_
    intro v w h
    have := congrArg (fun z : F₂ => z.1) h
    exact Subtype.ext (e.injective this)
  have h1 : Nat.card (K × K) ≤ Nat.card F₁ := by
    refine Nat.card_le_card_of_injective (fun p => ⟨⟨(Multiplicative.ofAdd ![p.1, p.2, 0], 1),
      mem_V₁.mpr rfl⟩, ?_, ?_⟩) ?_
    · change l₁ ((Multiplicative.ofAdd ![p.1, p.2, 0], 1) : PairMod K) = _
      rw [a₁]
      simp
    · change l₂ ((Multiplicative.ofAdd ![p.1, p.2, 0], 1) : PairMod K) = _
      rw [a₂]
      simp
    · intro p q hpq
      have := congrArg (fun z : F₁ => Multiplicative.toAdd (z.1 : PairMod K).1) hpq
      simp only [toAdd_ofAdd] at this
      exact Prod.ext (congrFun this 0) (congrFun this 1)
  have h2 : Nat.card F₂ ≤ Nat.card K := by
    refine Nat.card_le_card_of_injective
      (fun w => Multiplicative.toAdd (w.1 : PairMod K).2 2) ?_
    intro w w' hww'
    have hw := w.2
    have hw' := w'.2
    have hw1 : (w.1 : PairMod K).1 = 1 := mem_V₂.mp w.1.2
    have hw1' : (w'.1 : PairMod K).1 = 1 := mem_V₂.mp w'.1.2
    have eq0 : ∀ z : F₂, Multiplicative.toAdd (z.1 : PairMod K).2 0 = 0 ∧
        Multiplicative.toAdd (z.1 : PairMod K).2 1 = 0 := by
      intro z
      have hz1 : (z.1 : PairMod K).1 = 1 := mem_V₂.mp z.1.2
      have hzeq : (z.1 : PairMod K) = (1, Multiplicative.ofAdd (Multiplicative.toAdd
          (z.1 : PairMod K).2)) := Prod.ext hz1 rfl
      have k1 := z.2.1
      have k2 := z.2.2
      rw [hzeq, b₁] at k1
      rw [hzeq, b₂] at k2
      have k1' := congrFun (congrArg (fun x : PairMod K => Multiplicative.toAdd x.2) k1) 2
      have k2' := congrFun (congrArg (fun x : PairMod K => Multiplicative.toAdd x.2) k2) 2
      simp at k1' k2'
      exact ⟨k1', k2'⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext (hw1.trans hw1'.symm)
    apply funext
    intro i
    fin_cases i
    · exact (eq0 w).1.trans (eq0 w').1.symm
    · exact (eq0 w).2.trans (eq0 w').2.symm
    · exact hww'
  have hK : 1 < Nat.card K := Finite.one_lt_card
  have := (h1.trans hinj).trans h2
  rw [Nat.card_prod] at this
  nlinarith

theorem V₁_ne_V₂ : V₁ K ≠ V₂ K := by
  intro h
  have h1 : ((Multiplicative.ofAdd (Pi.single (0 : Fin 3) (1 : K)), 1) : PairMod K) ∈ V₁ K :=
    mem_V₁.mpr rfl
  rw [h, mem_V₂] at h1
  have := congrArg (fun x : StdMod (Fin 3) K => Multiplicative.toAdd x 0) h1
  simp at this

theorem map_V₁_eq_or [Finite K] {x : MulAut (PairMod K)}
    (hx : x ∈ Subgroup.normalizer (pairSL K : Set (MulAut (PairMod K)))) :
    (V₁ K).map x.toMonoidHom = V₁ K ∨ (V₁ K).map x.toMonoidHom = V₂ K :=
  Pair.map_eq_or_map_eq V₁_inf_V₂ V₁_sup_V₂ isInv_V₁ isInv_V₂ isIrr_V₁ isIrr_V₂ not_isoMod hx

theorem map_V₂_eq [Finite K] {x : MulAut (PairMod K)}
    (hx : x ∈ Subgroup.normalizer (pairSL K : Set (MulAut (PairMod K))))
    (h1 : (V₁ K).map x.toMonoidHom = V₁ K) : (V₂ K).map x.toMonoidHom = V₂ K := by
  have hinf : V₂ K ⊓ V₁ K = ⊥ := by rw [inf_comm]; exact V₁_inf_V₂
  have hsup : V₂ K ⊔ V₁ K = ⊤ := by rw [sup_comm]; exact V₁_sup_V₂
  rcases Pair.map_eq_or_map_eq hinf hsup isInv_V₂ isInv_V₁ isIrr_V₂ isIrr_V₁
    (fun h => not_isoMod (h.symm isInv_V₂)) hx with h | h
  · exact h
  · exfalso
    apply V₁_ne_V₂ (K := K)
    have := h.trans h1.symm
    exact (Subgroup.map_injective (f := x.toMonoidHom) x.injective this).symm

theorem mem_natNorm_of {a : MulAut (StdMod (Fin 3) K)}
    (h₁ : ∀ γ ∈ StatedSL 3 K, ∃ δ ∈ StatedSL 3 K, a * matAut γ * a⁻¹ = matAut δ)
    (h₂ : ∀ γ ∈ StatedSL 3 K, ∃ δ ∈ StatedSL 3 K, a⁻¹ * matAut γ * a = matAut δ) :
    a ∈ natNorm (StatedSL 3 K) := by
  rw [natNorm, Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨γ, rfl⟩
    obtain ⟨δ, hδ, h⟩ := h₁ γ.1 γ.2
    exact ⟨⟨δ, hδ⟩, h.symm⟩
  · rintro ⟨δ, hδ⟩
    obtain ⟨γ, hγ, h⟩ := h₂ δ.1 δ.2
    refine ⟨⟨γ, hγ⟩, ?_⟩
    change matAut γ = y
    rw [← h]
    change a⁻¹ * natAut (StatedSL 3 K) δ * a = y
    rw [hδ]
    group

theorem exists_pairAut [Finite K] {x : MulAut (PairMod K)}
    (hx : x ∈ Subgroup.normalizer (pairSL K : Set (MulAut (PairMod K))))
    (h1 : (V₁ K).map x.toMonoidHom = V₁ K) :
    ∃ x₁ x₂ : MulAut (StdMod (Fin 3) K), x = pairAut x₁ x₂ ∧
      x₁ ∈ natNorm (StatedSL 3 K) ∧ x₂ ∈ natNorm (StatedSL 3 K) := by
  have h2 := map_V₂_eq hx h1
  have hid : x⁻¹.toMonoidHom.comp x.toMonoidHom = MonoidHom.id (PairMod K) :=
    MonoidHom.ext fun v => by simp
  have hinv1 : (V₁ K).map x⁻¹.toMonoidHom = V₁ K := by
    conv_lhs => rw [← h1]
    rw [Subgroup.map_map, hid, Subgroup.map_id]
  have hinv2 : (V₂ K).map x⁻¹.toMonoidHom = V₂ K := by
    conv_lhs => rw [← h2]
    rw [Subgroup.map_map, hid, Subgroup.map_id]
  have m1 : ∀ (y : MulAut (PairMod K)), (V₁ K).map y.toMonoidHom = V₁ K →
      ∀ v : StdMod (Fin 3) K, y (v, 1) = ((y (v, 1)).1, 1) := by
    intro y hy v
    have : y (v, 1) ∈ V₁ K := by rw [← hy]; exact ⟨(v, 1), mem_V₁.mpr rfl, rfl⟩
    exact Prod.ext rfl (mem_V₁.mp this)
  have m2 : ∀ (y : MulAut (PairMod K)), (V₂ K).map y.toMonoidHom = V₂ K →
      ∀ w : StdMod (Fin 3) K, y (1, w) = (1, (y (1, w)).2) := by
    intro y hy w
    have : y (1, w) ∈ V₂ K := by rw [← hy]; exact ⟨(1, w), mem_V₂.mpr rfl, rfl⟩
    exact Prod.ext (mem_V₂.mp this) rfl
  let x₁ : MulAut (StdMod (Fin 3) K) :=
    { toFun := fun v => (x (v, 1)).1
      invFun := fun v => (x⁻¹ (v, 1)).1
      left_inv := fun v => by
        change (x⁻¹ ((x (v, 1)).1, 1)).1 = v
        rw [← m1 x h1 v]
        simp
      right_inv := fun v => by
        change (x ((x⁻¹ (v, 1)).1, 1)).1 = v
        rw [← m1 x⁻¹ hinv1 v]
        simp
      map_mul' := fun v w => by
        rw [show ((v * w, 1) : PairMod K) = (v, 1) * (w, 1) by simp, map_mul]
        rfl }
  let x₂ : MulAut (StdMod (Fin 3) K) :=
    { toFun := fun w => (x (1, w)).2
      invFun := fun w => (x⁻¹ (1, w)).2
      left_inv := fun w => by
        change (x⁻¹ (1, (x (1, w)).2)).2 = w
        rw [← m2 x h2 w]
        simp
      right_inv := fun w => by
        change (x (1, (x⁻¹ (1, w)).2)).2 = w
        rw [← m2 x⁻¹ hinv2 w]
        simp
      map_mul' := fun v w => by
        rw [show ((1, v * w) : PairMod K) = (1, v) * (1, w) by simp, map_mul]
        rfl }
  have hxe : x = pairAut x₁ x₂ := by
    refine MulEquiv.ext fun ⟨v, w⟩ => Prod.ext ?_ ?_
    · change (x (v, w)).1 = (x (v, 1)).1
      rw [show ((v, w) : PairMod K) = (v, 1) * (1, w) by simp, map_mul, Prod.fst_mul,
        m2 x h2 w, mul_one]
    · change (x (v, w)).2 = (x (1, w)).2
      rw [show ((v, w) : PairMod K) = (v, 1) * (1, w) by simp, map_mul, Prod.snd_mul,
        m1 x h1 v, one_mul]
  refine ⟨x₁, x₂, hxe, ?_, ?_⟩
  ·
    have key : ∀ (y : MulAut (PairMod K)) (y₁ y₂ : MulAut (StdMod (Fin 3) K)),
        y ∈ Subgroup.normalizer (pairSL K : Set (MulAut (PairMod K))) → y = pairAut y₁ y₂ →
        ∀ γ ∈ StatedSL 3 K, ∃ δ ∈ StatedSL 3 K, y₁ * matAut γ * y₁⁻¹ = matAut δ := by
      intro y y₁ y₂ hy hye γ hγ
      have hm := (Subgroup.mem_normalizer_iff.mp hy (pairHom γ)).mp ⟨γ, hγ, rfl⟩
      obtain ⟨δ, hδ, hδe⟩ := hm
      refine ⟨δ, hδ, MulEquiv.ext fun v => ?_⟩
      have := congrArg (fun z : MulAut (PairMod K) => (z (v, 1)).1) hδe
      simp only [hye, pairHom_apply, pairAut_inv, pairAut_mul] at this
      exact this.symm
    refine mem_natNorm_of (key x x₁ x₂ hx hxe) ?_
    have hx' : x⁻¹ ∈ Subgroup.normalizer (pairSL K : Set (MulAut (PairMod K))) :=
      Subgroup.inv_mem _ hx
    intro γ hγ
    obtain ⟨δ, hδ, h⟩ := key x⁻¹ x₁⁻¹ x₂⁻¹ hx' (by rw [hxe, pairAut_inv]) γ hγ
    exact ⟨δ, hδ, by rw [← h, inv_inv]⟩
  ·
    have key : ∀ (y : MulAut (PairMod K)) (y₁ y₂ : MulAut (StdMod (Fin 3) K)),
        y ∈ Subgroup.normalizer (pairSL K : Set (MulAut (PairMod K))) → y = pairAut y₁ y₂ →
        ∀ γ ∈ StatedSL 3 K, ∃ δ ∈ StatedSL 3 K, y₂ * matAut γ * y₂⁻¹ = matAut δ := by
      intro y y₁ y₂ hy hye γ hγ
      have hγ' := dualGL_mem hγ
      have hm := (Subgroup.mem_normalizer_iff.mp hy (pairHom (dualGL γ))).mp ⟨_, hγ', rfl⟩
      obtain ⟨δ, hδ, hδe⟩ := hm
      refine ⟨dualGL δ, dualGL_mem hδ, MulEquiv.ext fun w => ?_⟩
      have := congrArg (fun z : MulAut (PairMod K) => (z (1, w)).2) hδe
      simp only [hye, pairHom_apply, pairAut_inv, pairAut_mul, dualGL_dualGL] at this
      exact this.symm
    refine mem_natNorm_of (key x x₁ x₂ hx hxe) ?_
    have hx' : x⁻¹ ∈ Subgroup.normalizer (pairSL K : Set (MulAut (PairMod K))) :=
      Subgroup.inv_mem _ hx
    intro γ hγ
    obtain ⟨δ, hδ, h⟩ := key x⁻¹ x₁⁻¹ x₂⁻¹ hx' (by rw [hxe, pairAut_inv]) γ hγ
    exact ⟨δ, hδ, by rw [← h, inv_inv]⟩

end SL3Pair

end H

end CFSG.Quasithin

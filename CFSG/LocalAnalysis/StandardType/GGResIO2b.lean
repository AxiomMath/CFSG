module

public import CFSG.LocalAnalysis.StandardType.GGResICellSound

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def ggO2bInt (ver : Bool) : Fin 5 → Fin 5 → ℤ :=
  ![![2, -1, 0, 0, if ver then -1 else -2],
    ![-1, 2, -1, -1, 0],
    ![0, -1, 2, 0, 0],
    ![0, -1, 0, 2, if ver then 2 else 1],
    ![if ver then -2 else -1, 0, 0, if ver then 1 else 2, 2]]

@[expose] def ggO2bT (ver : Bool) : Fin 5 → Vector (ZMod 3) 6 := fun k =>
  Vector.ofFn fun l => if hl : l.val < 5 then (ggO2bInt ver k ⟨l.val, hl⟩ : ZMod 3) else 0

@[expose] def ggO2bβ : Fin 4 → Fin 5 := ![0, 1, 2, 4]

@[expose] def ggO2bE (ver : Bool) : Fin 4 → Vector (ZMod 3) 6 :=
  if ver then ![ggFVec [0, 0, 0, 0, 1], ggFVec [1, 0, 0, 0, 1], ggFVec [1, 1, 0, 0, 1],
      ggFVec [1, 1, 1, 0, 1]]
  else ![ggFVec [0, 0, 0, 0, 1], ggFVec [1, 0, 0, 0, 2], ggFVec [1, 1, 0, 0, 2],
      ggFVec [1, 1, 1, 0, 2]]

@[expose] def ggO2bLT (ver : Bool) : Fin 4 → Fin 4 → Fin 4 × ℕ :=
  if ver then ![![(1, 1), (0, 1), (2, 1), (3, 1)], ![(0, 1), (2, 1), (1, 1), (3, 1)],
      ![(0, 1), (1, 1), (3, 1), (2, 1)], ![(0, 2), (1, 1), (2, 1), (3, 1)]]
  else ![![(1, 2), (0, 2), (2, 1), (3, 1)], ![(0, 1), (2, 1), (1, 1), (3, 1)],
      ![(0, 1), (1, 1), (3, 1), (2, 1)], ![(0, 2), (1, 1), (2, 1), (3, 1)]]

@[expose] def ggO2bY : Vector (ZMod 3) 6 := ggFVec [1, 2, 1, 2, 0]

@[expose] def ggO2bW : List (Fin 5) := [3, 1, 2, 0, 1, 3, 4, 3, 1, 2, 0, 1, 3]

@[expose] def ggO2bRx (ver : Bool) : Fin 5 → Fin 5 → ZMod 3 := fun s l =>
  if hs : s.val < 4 then (ggO2bT ver (ggO2bβ ⟨s.val, hs⟩)).get l.castSucc
  else if l = 0 then 1 else 0

@[expose] def ggO2bM (ver : Bool) : Fin 5 → Fin 5 → ZMod 3 :=
  if ver then ![![0, 0, 0, 0, 1], ![2, 1, 2, 1, 2], ![1, 2, 0, 2, 1], ![0, 2, 1, 0, 2],
      ![0, 2, 1, 2, 0]]
  else ![![0, 0, 0, 0, 1], ![2, 1, 2, 2, 2], ![1, 2, 0, 1, 1], ![0, 2, 1, 0, 2],
      ![0, 1, 2, 2, 0]]

theorem ggO2b_inv (ver : Bool) (m l : Fin 5) :
    ∑ s : Fin 5, ggO2bM ver m s * ggO2bRx ver s l = if m = l then 1 else 0 := by
  revert ver m l
  decide

theorem ggO2b_rows_y (ver : Bool) (a : Fin 4) :
    ∑ l : Fin 5, (ggO2bT ver (ggO2bβ a)).get l.castSucc * ggO2bY.get l.castSucc = 0 := by
  revert ver a
  decide

theorem ggO2b_lines (ver : Bool) (a i : Fin 4) (l : Fin 6) :
    (ggFRefl (ggO2bT ver) (ggO2bβ a) (ggO2bE ver i)).get l =
      ((ggO2bLT ver a i).2 : ZMod 3) * (ggO2bE ver (ggO2bLT ver a i).1).get l := by
  revert ver a i l
  decide

theorem ggO2b_word_fix (ver : Bool) : ggFWord (ggO2bT ver) ggO2bW ggO2bY = ggO2bY := by
  revert ver
  decide

theorem ggO2b_notProp (ver : Bool) (j : Fin 4) :
    ggFNotProp (ggFWord (ggO2bT ver) (ggConjWord ((4 : Fin 5), ggO2bW)) (ggO2bE ver 0))
      (ggO2bE ver j) = true := by
  revert ver j
  decide

theorem ggO2b_diag (ver : Bool) (k : Fin 5) : (ggO2bT ver k).get k.castSucc = 2 := by
  revert ver k
  decide

section Lin

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]

theorem ggF_fixLine {N r : ℕ} {T : Fin N → Vector (ZMod p) (N + 1)} {h : Fin N → V}
    {α : Fin N → Module.Dual (ZMod p) V} (hT : GGFTable (RingHom.id (ZMod p)) T h 0 α)
    (hspan : Submodule.span (ZMod p) (Set.range h) = ⊤) (β : Fin r → Fin N) (l₀ : Fin N)
    (Rx : Fin (r + 1) → Fin N → ZMod p) (M : Fin N → Fin (r + 1) → ZMod p)
    (hM : ∀ m l, ∑ s, M m s * Rx s l = if m = l then 1 else 0)
    (hRx : ∀ (s : Fin r) l, Rx s.castSucc l = (T (β s)).get l.castSucc)
    (hRl : ∀ l, Rx (Fin.last r) l = if l = l₀ then 1 else 0) (y₀ : Vector (ZMod p) (N + 1))
    (hy : ∀ s : Fin r, ∑ l : Fin N, (T (β s)).get l.castSucc * y₀.get l.castSucc = 0)
    (hy0 : y₀.get l₀.castSucc = 1) (v : V) (hv : ∀ s, α (β s) v = 0) :
    ∃ c : ZMod p, v = c • ggFPi (RingHom.id (ZMod p)) h 0 y₀ := by
  have hv' : v ∈ Submodule.span (ZMod p) (Set.range h) := hspan ▸ Submodule.mem_top
  obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod p)).mp hv'
  refine ⟨z l₀, ?_⟩
  have hαv : ∀ s, ∑ l, (T (β s)).get l.castSucc * z l = 0 := by
    intro s
    have h1 := hv s
    rw [← hz, map_sum] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, hT.1, RingHom.id_apply, smul_eq_mul, mul_comm]
  set w : Fin N → ZMod p := fun l => z l - z l₀ * y₀.get l.castSucc with hw
  have hRw : ∀ s, ∑ l, Rx s l * w l = 0 := by
    intro s
    induction s using Fin.lastCases with
    | last =>
      simp only [hRl, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
        hw, hy0, mul_one, sub_self]
    | cast s =>
      simp only [hRx, hw, mul_sub, Finset.sum_sub_distrib, hαv s, zero_sub, neg_eq_zero]
      calc ∑ l : Fin N, (T (β s)).get l.castSucc * (z l₀ * y₀.get l.castSucc)
          = z l₀ * ∑ l : Fin N, (T (β s)).get l.castSucc * y₀.get l.castSucc := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun l _ => by ring
        _ = 0 := by rw [hy s, mul_zero]
  have hw0 : ∀ m, w m = 0 := by
    intro m
    calc w m = ∑ l, (if m = l then 1 else 0) * w l := by simp
      _ = ∑ l, (∑ s, M m s * Rx s l) * w l := by simp only [hM]
      _ = ∑ s, M m s * ∑ l, Rx s l * w l := by
          simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
          exact Finset.sum_comm
      _ = 0 := by simp [hRw]
  rw [← hz, ggFPi_zero, Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  have h1 := hw0 l
  simp only [hw, sub_eq_zero] at h1
  rw [h1, RingHom.id_apply, smul_smul]

end Lin

section O2b

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V]

@[expose] def ggO2bP (h : Fin 5 → V) : V := ggFPi (RingHom.id (ZMod 3)) h 0 ggO2bY

@[expose] def ggO2bL (h : Fin 5 → V) (ver : Bool) (i : Fin 4) : V :=
  ggFPi (RingHom.id (ZMod 3)) h 0 (ggO2bE ver i)

theorem ggResIO2b_linear (ver : Bool) {g : Fin 5 → (V ≃ₗ[ZMod 3] V)} {h : Fin 5 → V}
    {α : Fin 5 → Module.Dual (ZMod 3) V} (hT : GGFTable (RingHom.id (ZMod 3)) (ggO2bT ver) h 0 α)
    (hg : ∀ k w, g k w = w - α k w • h k) (h2 : ∀ k, α k (h k) = 2)
    (hspan : Submodule.span (ZMod 3) (Set.range h) = ⊤) (hind : LinearIndependent (ZMod 3) h) :
    (∀ v : V, (∀ a : Fin 4, α (ggO2bβ a) v = 0) → ∃ c : ZMod 3, v = c • ggO2bP h) ∧
    (∀ a i : Fin 4, ∃ j : Fin 4, ∃ s : ZMod 3,
      g (ggO2bβ a) (ggO2bL h ver i) = s • ggO2bL h ver j) ∧
    (ggO2bW.map g).prod (ggO2bP h) = ggO2bP h ∧
    ∀ j : Fin 4, ∀ s : ZMod 3,
      ((ggO2bW.map g).prod * g 4 * ((ggO2bW.map g).prod)⁻¹) (ggO2bL h ver 0) ≠
        s • ggO2bL h ver j := by
  refine ⟨fun v hv => ggF_fixLine hT hspan ggO2bβ 0 (ggO2bRx ver) (ggO2bM ver) (ggO2b_inv ver)
    (fun s l => ?_) (fun l => ?_) ggO2bY (ggO2b_rows_y ver) (by decide) v hv,
    fun a i => ⟨(ggO2bLT ver a i).1, ((ggO2bLT ver a i).2 : ZMod 3), ?_⟩, ?_, fun j s => ?_⟩
  · simp [ggO2bRx, s.isLt]
  · simp [ggO2bRx]
  · rw [ggO2bL, ggFPi_refl hT hg]
    exact ggFPi_smul_of _ (ggO2b_lines ver a i)
  · rw [ggO2bP, ggFPi_word hT hg, ggO2b_word_fix ver]
  · rw [← ggF_conjWord_prod hg h2 ((4 : Fin 5), ggO2bW), ggO2bL, ggFPi_word hT hg]
    exact ggFNotProp_spec hind (ggO2b_notProp ver j) s

end O2b

end CFSG.StandardType

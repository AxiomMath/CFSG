module

public import CFSG.LocalAnalysis.StandardType.GGResIO2b

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def ggO2aInt (c ver : Bool) : Fin 4 → Fin 4 → ℤ :=
  ![![2, -1, -1, if c then (if ver then -1 else -2) else 0],
    ![-1, 2, 0, if c then 0 else (if ver then -1 else -2)],
    ![-1, 0, 2, if ver then 2 else 1],
    ![if c then (if ver then -2 else -1) else 0, if c then 0 else (if ver then -2 else -1),
      if ver then 1 else 2, 2]]

@[expose] def ggO2aT (c ver : Bool) : Fin 4 → Vector (ZMod 3) 5 := fun k =>
  Vector.ofFn fun l => if hl : l.val < 4 then (ggO2aInt c ver k ⟨l.val, hl⟩ : ZMod 3) else 0

@[expose] def ggO2aβ : Fin 3 → Fin 4 := ![0, 1, 3]

@[expose] def ggO2aY (c ver : Bool) : Vector (ZMod 3) 5 :=
  if c then (if ver then ggFVec [1, 2, 1, 2] else ggFVec [1, 2, 1, 1])
  else (if ver then ggFVec [1, 0, 2, 2] else ggFVec [1, 0, 2, 1])

@[expose] def ggO2aH : List (Fin 4) := [2, 3, 2]

@[expose] def ggO2aW5 (c : Bool) : List (Fin 4) := if c then [3, 0, 3, 2, 1, 0] else [3, 1, 3, 2, 1, 0]

@[expose] def ggO2aRx (c ver : Bool) : Fin 4 → Fin 4 → ZMod 3 := fun s l =>
  if hs : s.val < 3 then (ggO2aT c ver (ggO2aβ ⟨s.val, hs⟩)).get l.castSucc
  else if l = 0 then 1 else 0

@[expose] def ggO2aM (c ver : Bool) : Fin 4 → Fin 4 → ZMod 3 :=
  if c then (if ver then ![![0, 0, 0, 1], ![0, 2, 0, 2], ![1, 2, 2, 1], ![1, 2, 1, 2]]
      else ![![0, 0, 0, 1], ![0, 2, 0, 2], ![1, 2, 1, 1], ![2, 1, 1, 1]])
  else (if ver then ![![0, 0, 0, 1], ![1, 2, 1, 0], ![1, 1, 2, 2], ![2, 0, 2, 2]]
      else ![![0, 0, 0, 1], ![1, 2, 2, 0], ![1, 1, 1, 2], ![1, 0, 2, 1]])

theorem ggO2a_inv (c ver : Bool) (m l : Fin 4) :
    ∑ s : Fin 4, ggO2aM c ver m s * ggO2aRx c ver s l = if m = l then 1 else 0 := by
  revert c ver m l
  decide

theorem ggO2a_rows_y (c ver : Bool) (a : Fin 3) :
    ∑ l : Fin 4, (ggO2aT c ver (ggO2aβ a)).get l.castSucc * (ggO2aY c ver).get l.castSucc = 0 := by
  revert c ver a
  decide

theorem ggO2a_y0 (c ver : Bool) : (ggO2aY c ver).get 0 = 1 := by
  revert c ver
  decide

theorem ggO2a_fusion (c ver : Bool) (l : Fin 4) (hl : ∀ a, ggO2aβ a ≠ l) :
    (ggFWord (ggO2aT c ver) ggO2aH (ggO2aY c ver)).get l.castSucc = 0 := by
  revert c ver l
  decide

theorem ggO2a_cartanK (c ver : Bool) (e : Fin 3 → ZMod 3)
    (he : ∀ k : Fin 3, ∑ a : Fin 3, e a * (ggO2aT c ver (ggO2aβ k)).get (ggO2aβ a).castSucc = 0) :
    e = 0 := by
  revert c ver e
  decide

theorem ggO2a_order5 (c ver : Bool) :
    ggFMat (ggO2aT c ver) (ggO2aW5 c ++ ggO2aW5 c ++ ggO2aW5 c ++ ggO2aW5 c ++ ggO2aW5 c) =
      ggFMat (ggO2aT c ver) [] ∧
    ggFMat (ggO2aT c ver) (ggO2aW5 c) ≠ ggFMat (ggO2aT c ver) [] := by
  revert c ver
  decide

theorem ggO2a_diag (c ver : Bool) (k : Fin 4) : (ggO2aT c ver k).get k.castSucc = 2 := by
  revert c ver k
  decide

section O2a

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V]

theorem ggFPi_mem_span {N r : ℕ} {h : Fin N → V} (β : Fin r → Fin N) (z : Vector (ZMod 3) (N + 1))
    (hz : ∀ l : Fin N, (∀ a, β a ≠ l) → z.get l.castSucc = 0) :
    ggFPi (RingHom.id (ZMod 3)) h 0 z ∈ Submodule.span (ZMod 3) (Set.range (h ∘ β)) := by
  rw [ggFPi, smul_zero, add_zero]
  refine Submodule.sum_mem _ fun l _ => ?_
  by_cases hl : ∃ a, β a = l
  · obtain ⟨a, rfl⟩ := hl
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · push Not at hl
    rw [hz l hl, map_zero, zero_smul]
    exact Submodule.zero_mem _

theorem ggResIO2a_linear (c ver : Bool) {g : Fin 4 → (V ≃ₗ[ZMod 3] V)} {h : Fin 4 → V}
    {α : Fin 4 → Module.Dual (ZMod 3) V}
    (hT : GGFTable (RingHom.id (ZMod 3)) (ggO2aT c ver) h 0 α)
    (hg : ∀ k w, g k w = w - α k w • h k)
    (hspan : Submodule.span (ZMod 3) (Set.range h) = ⊤) (hind : LinearIndependent (ZMod 3) h) :
    (∀ v : V, (∀ a : Fin 3, α (ggO2aβ a) v = 0) →
      ∃ e : ZMod 3, v = e • ggFPi (RingHom.id (ZMod 3)) h 0 (ggO2aY c ver)) ∧
    (ggO2aH.map g).prod (ggFPi (RingHom.id (ZMod 3)) h 0 (ggO2aY c ver)) ∈
      Submodule.span (ZMod 3) (Set.range (h ∘ ggO2aβ)) ∧
    ((ggO2aW5 c).map g).prod ^ 5 = 1 ∧ ((ggO2aW5 c).map g).prod ≠ 1 := by
  obtain ⟨h5, h1⟩ := ggO2a_order5 c ver
  refine ⟨fun v hv => ggF_fixLine hT hspan ggO2aβ 0 (ggO2aRx c ver) (ggO2aM c ver)
    (ggO2a_inv c ver) (fun s l => ?_) (fun l => ?_) (ggO2aY c ver) (ggO2a_rows_y c ver)
    (ggO2a_y0 c ver) v hv,
    by rw [ggFPi_word hT hg]; exact ggFPi_mem_span ggO2aβ _ (ggO2a_fusion c ver), ?_, ?_⟩
  · simp [ggO2aRx, s.isLt]
  · simp [ggO2aRx]
  · have hw := (ggFMat_eq_iff hT hg hspan hind).mp h5
    simpa [List.map_append, List.prod_append, pow_succ, mul_assoc] using hw
  · intro h1'
    apply h1
    rw [ggFMat_eq_iff hT hg hspan hind]
    simpa using h1'

end O2a

end CFSG.StandardType

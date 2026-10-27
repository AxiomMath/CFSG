module

public import CFSG.Sporadic.Recognition.PresentedWords
public import CFSG.Certificates.WordSubgroup
public import CFSG.Sporadic.Bridge.Common
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.Sporadic.Recognition.PresentedWords

open CFSG.CosetTable

section Wprod

variable {G : Type*} [Group G]

theorem wprod_invRev {n : ℕ} (y : Fin n → G) (w : List (Fin n × Bool)) :
    wprod y (FreeGroup.invRev w) = (wprod y w)⁻¹ := by
  rw [← lift_mk y (FreeGroup.invRev w), ← lift_mk y w, ← FreeGroup.inv_mk, map_inv]

theorem wprod_substWord {m n : ℕ} (y : Fin m → G)
    (hs : List (List (Fin m × Bool))) (r : List (Fin n × Bool)) :
    wprod y (substWord hs r) =
      wprod (fun i : Fin n => wprod y (hs.getD i [])) r := by
  induction r with
  | nil => rfl
  | cons l r ih =>
    obtain ⟨i, b⟩ := l
    have hsub : substWord hs ((i, b) :: r) =
        (if b then hs.getD i [] else FreeGroup.invRev (hs.getD i [])) ++ substWord hs r := rfl
    rw [hsub, wprod_append, ih, wprod_cons]
    cases b <;> simp [wprod_invRev]

@[expose] def commWord {m : ℕ} (x w : List (Fin m × Bool)) : List (Fin m × Bool) :=
  FreeGroup.invRev x ++ FreeGroup.invRev w ++ x ++ w

theorem wprod_commWord {m : ℕ} (y : Fin m → G) (x w : List (Fin m × Bool)) :
    wprod y (commWord x w) =
      (wprod y x)⁻¹ * (wprod y w)⁻¹ * wprod y x * wprod y w := by
  simp [commWord, wprod_append, wprod_invRev, mul_assoc]

end Wprod

section Collapse

variable {m : ℕ}

theorem mem_closure_of_subsetCheckCC (ws : List (List (Fin m × Bool))) (S : List ℕ)
    {cap : ℕ} (h : subsetCheckCC ws S cap 1 = true) {G : Type*} [Group G] (y : Fin m → G)
    (hy : ∀ w ∈ ws, wprod y w = 1) (i : Fin m) :
    y i ∈ Subgroup.closure (y '' {j | j ∈ subsetOf m S}) := by
  set rels := {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
  obtain ⟨hfi, hle⟩ := index_le_of_subsetCheckCC ws S h
  have htop : genSub rels (subsetOf m S) = ⊤ :=
    Subgroup.index_eq_one.mp (Nat.le_antisymm hle (Nat.pos_of_ne_zero hfi.index_ne_zero))
  have hmem : (PresentedGroup.of i : PG m ws) ∈ genSub rels (subsetOf m S) := by
    rw [htop]
    exact Subgroup.mem_top _
  have hmap := Subgroup.mem_map_of_mem (pgHom y hy) hmem
  rw [MonoidHom.map_closure, pgHom_of] at hmap
  refine Subgroup.closure_mono ?_ hmap
  rintro _ ⟨x, ⟨j, hj, rfl⟩, rfl⟩
  rw [pgHom_of]
  exact Set.mem_image_of_mem y hj

end Collapse

section Bridge

theorem wordProd_map_fin {G : Type*} [Group G] {m : ℕ} (x : Fin m → G)
    (w : List (Fin m × Bool)) :
    CFSG.Sporadic.Bridge.wordProd (fun i => if h : i < m then x ⟨i, h⟩ else 1)
        (w.map fun l => (l.1.val, l.2)) = wprod x w := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    obtain ⟨i, b⟩ := l
    simp only [List.map_cons, CFSG.Sporadic.Bridge.wordProd, wprod, List.prod_cons] at ih ⊢
    rw [ih]
    cases b <;> simp [i.isLt]

theorem th_relatorLetters_iff {G : Type*} [Group G] (x : Fin 8 → G) :
    (∀ v ∈ TauCeti.SporadicName.Th.presentation.relatorLetters,
      CFSG.Sporadic.Bridge.wordProd (fun i => if h : i < 8 then x ⟨i, h⟩ else 1) v = 1) ↔
    ∀ w : List (Fin 8 × Bool),
      w ∈ (TauCeti.Sporadic.Thompson.presentation.relators :
        List (List (Fin 8 × Bool))) → wprod x w = 1 := by
  have hpres : TauCeti.SporadicName.Th.presentation =
      TauCeti.Sporadic.Thompson.presentation := rfl
  constructor
  · intro h w hw
    have hwT : w ∈ (TauCeti.Sporadic.Thompson.presentation.relators :
        List (List (Fin 8 × Bool))) := hw
    have hm : w.map (fun l => (l.1.val, l.2)) ∈
        TauCeti.SporadicName.Th.presentation.relatorLetters := by
      rw [TauCeti.GroupPresentation.relatorLetters_def, hpres]
      exact List.mem_map_of_mem hwT
    have h1 := h _ hm
    simpa [wordProd_map_fin] using h1
  · intro h v hv
    rw [TauCeti.GroupPresentation.relatorLetters_def, hpres, List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    let w8 : List (Fin 8 × Bool) := w
    have hw8 : w8 ∈ (TauCeti.Sporadic.Thompson.presentation.relators :
        List (List (Fin 8 × Bool))) := hw
    have h1 := h w8 hw8
    change CFSG.Sporadic.Bridge.wordProd
      (fun i => if h : i < 8 then x ⟨i, h⟩ else 1)
      (w8.map fun l => (l.1.val, l.2)) = 1
    rwa [wordProd_map_fin]

end Bridge

end CFSG.Sporadic.Recognition.PresentedWords

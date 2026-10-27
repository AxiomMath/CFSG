module

public import CFSG.Certificates.CosetTableCompactColumns

public section

namespace CFSG.Sporadic.Recognition.PresentedWords

open CFSG.CosetTable

section Wprod

variable {G : Type*} [Group G]

@[expose] def wprod {n : ℕ} (y : Fin n → G) (w : List (Fin n × Bool)) : G :=
  (w.map fun l => if l.2 then y l.1 else (y l.1)⁻¹).prod

@[simp] theorem wprod_nil {n : ℕ} (y : Fin n → G) : wprod y [] = 1 := rfl

theorem wprod_cons {n : ℕ} (y : Fin n → G) (l : Fin n × Bool) (w : List (Fin n × Bool)) :
    wprod y (l :: w) = (if l.2 then y l.1 else (y l.1)⁻¹) * wprod y w := by
  simp [wprod]

theorem wprod_append {n : ℕ} (y : Fin n → G) (u v : List (Fin n × Bool)) :
    wprod y (u ++ v) = wprod y u * wprod y v := by
  simp [wprod, List.prod_append]

theorem lift_mk {n : ℕ} (y : Fin n → G) (w : List (Fin n × Bool)) :
    FreeGroup.lift y (FreeGroup.mk w) = wprod y w := by
  rw [FreeGroup.lift_mk]
  simp [wprod, Bool.cond_eq_ite]

theorem map_wprod {H : Type*} [Group H] (φ : G →* H) {n : ℕ} (y : Fin n → G)
    (w : List (Fin n × Bool)) : φ (wprod y w) = wprod (fun i => φ (y i)) w := by
  induction w with
  | nil => simp
  | cons l w ih =>
    rw [wprod_cons, wprod_cons, map_mul, ih]
    split_ifs <;> simp

theorem wprod_comp_letters {m n : ℕ} (g : Fin m → Fin n) (y : Fin n → G)
    (w : List (Fin m × Bool)) :
    wprod y (w.map fun l => (g l.1, l.2)) = wprod (fun i => y (g i)) w := by
  induction w with
  | nil => rfl
  | cons l w ih => rw [List.map_cons, wprod_cons, wprod_cons, ih]

end Wprod

section Presented

variable {G : Type*} [Group G] {n : ℕ} {ws : List (List (Fin n × Bool))}

theorem mk_eq_wprod (w : List (Fin n × Bool)) :
    PresentedGroup.mk {r : FreeGroup (Fin n) | r ∈ ws.map FreeGroup.mk} (FreeGroup.mk w) =
      wprod (fun i => (PresentedGroup.of i : PG n ws)) w := by
  have h : (PresentedGroup.mk {r : FreeGroup (Fin n) | r ∈ ws.map FreeGroup.mk} :
      FreeGroup (Fin n) →* PG n ws) = FreeGroup.lift (fun i => PresentedGroup.of i) :=
    FreeGroup.ext_hom _ _ fun i => by rw [FreeGroup.lift_apply_of]; rfl
  rw [h, lift_mk]

theorem wprod_of_relator {w : List (Fin n × Bool)} (hw : w ∈ ws) :
    wprod (fun i => (PresentedGroup.of i : PG n ws)) w = 1 := by
  rw [← mk_eq_wprod]
  exact PresentedGroup.one_of_mem (List.mem_map_of_mem hw)

@[expose] def pgHom (y : Fin n → G) (h : ∀ w ∈ ws, wprod y w = 1) : PG n ws →* G :=
  PresentedGroup.toGroup (f := y) (by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    rw [lift_mk]
    exact h w hw)

theorem pgHom_of (y : Fin n → G) (h : ∀ w ∈ ws, wprod y w = 1) (i : Fin n) :
    pgHom y h (PresentedGroup.of i) = y i :=
  PresentedGroup.toGroup.of _

theorem pgHom_mk (y : Fin n → G) (h : ∀ w ∈ ws, wprod y w = 1) (w : List (Fin n × Bool)) :
    pgHom y h (PresentedGroup.mk {r : FreeGroup (Fin n) | r ∈ ws.map FreeGroup.mk}
      (FreeGroup.mk w)) = wprod y w := by
  show FreeGroup.lift y (FreeGroup.mk w) = _
  exact lift_mk y w

theorem pg_hom_ext {φ ψ : PG n ws →* G}
    (h : ∀ i, φ (PresentedGroup.of i) = ψ (PresentedGroup.of i)) : φ = ψ :=
  PresentedGroup.ext h

end Presented

section Restrict

variable {m : ℕ}

@[expose] noncomputable def restrictHom (ws : List (List (Fin m × Bool))) (S : List (Fin m)) :
    PG S.length (restrictWords S ws) →* PG m ws :=
  pgHom (fun j => (PresentedGroup.of (S.get j) : PG m ws)) (by
    intro w hw
    obtain ⟨v, hv, hren⟩ := List.mem_filterMap.1 hw
    rw [← wprod_comp_letters (fun j => S.get j) (fun i => (PresentedGroup.of i : PG m ws)) w,
      map_renumber S v w hren]
    exact wprod_of_relator hv)

theorem restrictHom_of (ws : List (List (Fin m × Bool))) (S : List (Fin m)) (j : Fin S.length) :
    restrictHom ws S (PresentedGroup.of j) = PresentedGroup.of (S.get j) :=
  pgHom_of _ _ j

end Restrict

section Index

variable {m : ℕ}

theorem index_le_of_subsetCheckCC (ws : List (List (Fin m × Bool))) (S : List ℕ) {cap n : ℕ}
    (h : subsetCheckCC ws S cap n = true) :
    (genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (subsetOf m S)).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (subsetOf m S)).index ≤ n :=
  index_le_of_check (goodColParams ws _ _ (genSub_words_mem ws (subsetOf m S)))
    (by simpa [colParams, mkParams] using closure_colLetter ws)
    (subsetCheckC_of_subsetCheckCC ws S h)

end Index

end CFSG.Sporadic.Recognition.PresentedWords

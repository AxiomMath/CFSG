module

public import CFSG.Quasithin.H13.L32NSp4Code

public section

namespace CFSG.Quasithin.H13.Sp4Cert

open KGCert CFSG.ComponentClassification.PresentationLocal Matrix

theorem foldl_step_mem (a : List ℕ) (gens gs : List (List ℕ)) (hgs : ∀ g ∈ gs, g ∈ gens)
    (p : List (List ℕ) × ℕ) (hp : ∀ y ∈ p.1, ∃ g ∈ gens, y = mulC a g) :
    ∀ y ∈ (gs.foldl (fun (p : List (List ℕ) × ℕ) g =>
      let b := mulC a g
      if memM p.2 b then p else (b :: p.1, addM p.2 b)) p).1, ∃ g ∈ gens, y = mulC a g := by
  induction gs generalizing p with
  | nil => simpa using hp
  | cons g gs ih =>
    rw [List.foldl_cons]
    refine ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _ ?_
    dsimp only
    split
    · exact hp
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨g, hgs g (List.mem_cons_self), rfl⟩
      · exact hp y hy

theorem bfs_sound (P : List ℕ → Prop) (gens : List (List ℕ))
    (hstep : ∀ a, P a → ∀ g ∈ gens, P (mulC a g)) :
    ∀ (n : ℕ) (fr : List (List ℕ)) (m : ℕ) (acc : List (List ℕ)), (∀ x ∈ fr, P x) →
      (∀ x ∈ acc, P x) → ∀ x ∈ (bfs gens n fr m acc).1, P x := by
  intro n
  induction n with
  | zero => intro fr m acc _ hacc x hx; exact hacc x hx
  | succ n ih =>
    intro fr m acc hfr hacc x hx
    match fr, hfr, hx with
    | [], _, hx => exact hacc x hx
    | a :: fr, hfr, hx =>
      have hnew := foldl_step_mem a gens gens (fun g hg => hg) ([], m) (by simp)
      have hnewP : ∀ y ∈ (gens.foldl (fun (p : List (List ℕ) × ℕ) g =>
          let b := mulC a g
          if memM p.2 b then p else (b :: p.1, addM p.2 b)) ([], m)).1, P y := by
        intro y hy
        obtain ⟨g, hg, rfl⟩ := hnew y hy
        exact hstep a (hfr a List.mem_cons_self) g hg
      refine ih _ _ _ ?_ ?_ x hx
      · intro y hy
        rcases List.mem_append.mp hy with hy | hy
        · exact hfr y (List.mem_cons_of_mem _ hy)
        · exact hnewP y hy
      · intro y hy
        rcases List.mem_append.mp hy with hy | hy
        · exact hnewP y hy
        · exact hacc y hy

theorem closeC_sound (P : List ℕ → Prop) (gens : List (List ℕ)) (h1 : P oneC4)
    (hstep : ∀ a, P a → ∀ g ∈ gens, P (mulC a g)) : ∀ x ∈ (closeC gens).1, P x :=
  bfs_sound P gens hstep 2000 [oneC4] _ [oneC4] (by simpa using h1) (by simpa using h1)

@[expose] def InD (Δ : Subgroup (GL (Fin 4) (ZMod 2))) (x : List ℕ) : Prop :=
  ValidC4 x ∧ ∃ g ∈ Δ, (g : Mat4) = decodeC4 x

theorem inD_oneC4 (Δ : Subgroup (GL (Fin 4) (ZMod 2))) : InD Δ oneC4 :=
  ⟨validC4_oneC4, 1, Δ.one_mem, by rw [decodeC4_oneC4]; rfl⟩

theorem inD_mulC {Δ : Subgroup (GL (Fin 4) (ZMod 2))} {a b : List ℕ} (ha : InD Δ a)
    (hb : InD Δ b) : InD Δ (mulC a b) := by
  obtain ⟨hav, g, hg, hga⟩ := ha
  obtain ⟨hbv, k, hk, hkb⟩ := hb
  refine ⟨validC4_mulC hav hbv, g * k, Δ.mul_mem hg hk, ?_⟩
  rw [decodeC4_mulC hav.1 hbv.1, Units.val_mul, hga, hkb]

theorem inD_colsOf4 {Δ : Subgroup (GL (Fin 4) (ZMod 2))} {g : GL (Fin 4) (ZMod 2)}
    (hg : g ∈ Δ) : InD Δ (colsOf4 (g : Mat4)) :=
  ⟨validC4_colsOf4 _, g, hg, (decodeC4_colsOf4 _).symm⟩

theorem validB_iff {x : List ℕ} : validB x = true ↔ ValidC4 x := by
  simp only [validB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq, ValidC4]

theorem inD_of_mul_eq {Δ : Subgroup (GL (Fin 4) (ZMod 2))} {ri a x b : List ℕ}
    (hri : ValidC4 ri) (ha : InD Δ a) (hx : ValidC4 x) (hb : InD Δ b)
    (hab : mulC (mulC ri a) x = b) {r : List ℕ} (hr : ValidC4 r) (hrr : mulC ri r = oneC4)
    (hxD : InD Δ x) : InD Δ r := by
  have hav := ha.1
  obtain ⟨-, ga, hga, hgaa⟩ := ha
  obtain ⟨-, gb, hgb, hgbb⟩ := hb
  obtain ⟨-, gx, hgx, hgxx⟩ := hxD
  have h1 : decodeC4 ri * decodeC4 r = 1 := by
    rw [← decodeC4_mulC hri.1 hr.1, hrr, decodeC4_oneC4]
  have h2 : decodeC4 ri * decodeC4 a * decodeC4 x = decodeC4 b := by
    rw [← hab, decodeC4_mulC (validC4_mulC hri hav).1 hx.1, decodeC4_mulC hri.1 hav.1]
  have h3 : decodeC4 r * decodeC4 ri = 1 := mul_eq_one_comm.mp h1
  refine ⟨hr, ga * gx * gb⁻¹, Δ.mul_mem (Δ.mul_mem hga hgx) (Δ.inv_mem hgb), ?_⟩
  have hgbinv : ((gb⁻¹ : GL (Fin 4) (ZMod 2)) : Mat4) * decodeC4 b = 1 := by
    rw [← hgbb, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc ((ga * gx * gb⁻¹ : GL (Fin 4) (ZMod 2)) : Mat4)
      = decodeC4 a * decodeC4 x * ((gb⁻¹ : GL (Fin 4) (ZMod 2)) : Mat4) := by
        rw [Units.val_mul, Units.val_mul, hgaa, hgxx]
    _ = decodeC4 r * (decodeC4 ri * decodeC4 a * decodeC4 x) *
          ((gb⁻¹ : GL (Fin 4) (ZMod 2)) : Mat4) := by
        rw [← Matrix.mul_assoc (decodeC4 r), ← Matrix.mul_assoc (decodeC4 r), h3,
          Matrix.one_mul, Matrix.mul_assoc]
    _ = decodeC4 r := by
        rw [h2, Matrix.mul_assoc, ← hgbb, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.mul_one]

theorem inD_of_mem_closeC {Δ : Subgroup (GL (Fin 4) (ZMod 2))} {gens : List (List ℕ)}
    (hg : ∀ g ∈ gens, InD Δ g) : ∀ x ∈ (closeC gens).1, InD Δ x :=
  closeC_sound (InD Δ) gens (inD_oneC4 Δ) fun _ ha g hgm => inD_mulC ha (hg g hgm)

@[expose] def nodeCard (s : Node) : ℕ := (s.els.map codeC).toFinset.card

class Sp4Data : Type where
  ov5K : List Node
  ov9K : List Node
  specK : Spec
  node5 : ∀ {Δ : Subgroup (GL (Fin 4) (ZMod 2))}, Δ ≤ sympFour → InD Δ x5C →
    ∃ s ∈ ov5K, (∀ x ∈ s.els, InD Δ x) ∧ ∀ g ∈ Δ, colsOf4 (g : Mat4) ∈ s.els
  node9 : ∀ {Δ : Subgroup (GL (Fin 4) (ZMod 2))}, Δ ≤ sympFour → InD Δ a9C → InD Δ b9C →
    ∃ s ∈ ov9K, (∀ x ∈ s.els, InD Δ x) ∧ ∀ g ∈ Δ, colsOf4 (g : Mat4) ∈ s.els
  facts : ∀ s, s ∈ ov5K ∨ s ∈ ov9K →
    s.mask = maskOf s.els ∧ (∀ x ∈ s.els, ValidC4 x) ∧ s.els.Nodup
  line5 : lineOk specK ov5K = true
  line9 : lineOk specK ov9K = true
  quad5 : quadOk specK ov5K = true
  quad9 : quadOk specK ov9K = true
  special : specialOk specK = true

export Sp4Data (ov5K ov9K specK)

theorem exists_node_eq_5 [Sp4Data] {Δ : Subgroup (GL (Fin 4) (ZMod 2))}
    (hΔ : Δ ≤ sympFour) (hP : InD Δ x5C) :
    ∃ s ∈ ov5K, (∀ x ∈ s.els, InD Δ x) ∧ ∀ g ∈ Δ, colsOf4 (g : Mat4) ∈ s.els :=
  Sp4Data.node5 hΔ hP

theorem exists_node_eq_9 [Sp4Data] {Δ : Subgroup (GL (Fin 4) (ZMod 2))}
    (hΔ : Δ ≤ sympFour) (hP : InD Δ a9C) (hP' : InD Δ b9C) :
    ∃ s ∈ ov9K, (∀ x ∈ s.els, InD Δ x) ∧ ∀ g ∈ Δ, colsOf4 (g : Mat4) ∈ s.els :=
  Sp4Data.node9 hΔ hP hP'

end CFSG.Quasithin.H13.Sp4Cert

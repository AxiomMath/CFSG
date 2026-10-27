module

public import CFSG.Walter.Ree.Thompson2.BaseRel.Card
public import CFSG.Walter.Ree.Thompson2.BaseRel.Enum

public section

namespace CFSG.Walter.Ree.T2.BaseRel

open CFSG.Walter.J1Recog Word

section Ev

variable {H : Type*} [Group H]

@[expose] def evList {n : ℕ} (f : Fin n → H) (w : Word n) : H :=
  (w.map fun x => cond x.2 (f x.1) (f x.1)⁻¹).prod

theorem ev_cons {n : ℕ} (f : Fin n → H) (x : Fin n × Bool) (w : Word n) :
    ev f (x :: w) = cond x.2 (f x.1) (f x.1)⁻¹ * ev f w := by
  obtain ⟨i, b⟩ := x
  have h : ((i, b) :: w : Word n) = cond b (gen i) (inv (gen i)) ++ w := by cases b <;> rfl
  rw [h, ev_append]
  cases b <;> simp

theorem ev_eq_evList {n : ℕ} (f : Fin n → H) (w : Word n) : ev f w = evList f w := by
  induction w with
  | nil => simp [evList]
  | cons x w ih =>
    rw [ev_cons, ih]
    simp [evList]

theorem range_lift {n : ℕ} (l : List (Word n)) (f : Fin n → H) (hf : ∀ w ∈ l, ev f w = 1) :
    (lift l f hf).range = Subgroup.closure (Set.range f) := by
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
    ← Set.range_comp]
  congr 1
  ext x
  simp

theorem lift_ev {n : ℕ} (l : List (Word n)) (f : Fin n → H) (hf : ∀ w ∈ l, ev f w = 1)
    (w : Word n) : lift l f hf (ev PresentedGroup.of w) = ev f w := by
  rw [map_ev]
  simp

end Ev

@[expose] def pglGen : Fin 4 → Equiv.Perm (Fin 9) := ![pglJ, pglK, pglT, pglY]

theorem range_pglGen : Set.range pglGen = {pglJ, pglK, pglT, pglY} := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [pglGen]
  · rintro (rfl | rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]

theorem pglGen_rels1512 : ∀ w ∈ rels1512, ev pglGen w = 1 := by
  intro w hw
  rw [ev_eq_evList]
  revert w
  decide +kernel

noncomputable def toPerm1512 : Pres1512 →* Equiv.Perm (Fin 9) :=
  lift rels1512 pglGen pglGen_rels1512

theorem range_toPerm1512 : toPerm1512.range = PGammaL28 := by
  rw [toPerm1512, range_lift, range_pglGen]
  rfl

noncomputable def toPGL1512 : Pres1512 →* PGammaL28 :=
  toPerm1512.codRestrict PGammaL28 fun x => range_toPerm1512 ▸ ⟨x, rfl⟩

theorem toPGL1512_bijective : Function.Bijective toPGL1512 := by
  have hsurj : Function.Surjective toPGL1512 := by
    rintro ⟨g, hg⟩
    rw [← range_toPerm1512] at hg
    obtain ⟨x, rfl⟩ := hg
    exact ⟨x, rfl⟩
  have := card_pres1512_le.1
  exact hsurj.bijective_of_nat_card_le (by rw [card_PGammaL28]; exact card_pres1512_le.2)

noncomputable def iso1512 : Pres1512 ≃* PGammaL28 :=
  MulEquiv.ofBijective toPGL1512 toPGL1512_bijective

theorem iso1512_of (i : Fin 4) :
    ((iso1512 (PresentedGroup.of i) : PGammaL28) : Equiv.Perm (Fin 9)) = pglGen i := by
  change toPerm1512 (PresentedGroup.of i) = pglGen i
  rw [toPerm1512, lift_of]

theorem iso1512_symm_j : iso1512.symm PGammaL28.j = PresentedGroup.of 0 :=
  iso1512.symm_apply_eq.mpr (Subtype.ext (iso1512_of 0).symm)

theorem iso1512_symm_k : iso1512.symm PGammaL28.k = PresentedGroup.of 1 :=
  iso1512.symm_apply_eq.mpr (Subtype.ext (iso1512_of 1).symm)

theorem iso1512_symm_t : iso1512.symm PGammaL28.t = PresentedGroup.of 2 :=
  iso1512.symm_apply_eq.mpr (Subtype.ext (iso1512_of 2).symm)

theorem iso1512_symm_y : iso1512.symm PGammaL28.y = PresentedGroup.of 3 :=
  iso1512.symm_apply_eq.mpr (Subtype.ext (iso1512_of 3).symm)

abbrev C2 := Multiplicative (ZMod 2)

@[expose] def c2Gen : Fin 4 → C2 × Equiv.Perm (Fin 9) :=
  ![(Multiplicative.ofAdd 1, pglJ), (Multiplicative.ofAdd 1, pglK), (1, pglT), (1, pglY)]

theorem c2Gen_rels3024 : ∀ w ∈ rels3024, ev c2Gen w = 1 := by
  intro w hw
  rw [ev_eq_evList]
  revert w
  decide +kernel

noncomputable def toC2 : Pres3024 →* C2 × Equiv.Perm (Fin 9) := lift rels3024 c2Gen c2Gen_rels3024

theorem pglGen_rels3024 : ∀ w ∈ rels3024, ev pglGen w = 1 := by
  intro w hw
  apply pglGen_rels1512 w
  simp only [rels3024, rels1512, List.mem_append, List.mem_cons] at hw ⊢
  tauto

theorem snd_comp_toC2 : (MonoidHom.snd _ _).comp toC2 = lift rels3024 pglGen pglGen_rels3024 := by
  apply PresentedGroup.ext
  intro i
  simp only [MonoidHom.comp_apply, toC2, lift_of, MonoidHom.coe_snd]
  fin_cases i <;> rfl

theorem toC2_kt3 : toC2 (ev PresentedGroup.of kt3) = (Multiplicative.ofAdd 1, 1) := by
  rw [toC2, lift_ev, ev_eq_evList]
  decide +kernel

theorem mem_range_toC2 (c : C2) {g : Equiv.Perm (Fin 9)} (hg : g ∈ PGammaL28) :
    (c, g) ∈ toC2.range := by
  have hg' : g ∈ ((MonoidHom.snd _ _).comp toC2).range := by
    rw [snd_comp_toC2, range_lift, range_pglGen]
    exact hg
  obtain ⟨x, hx⟩ := hg'
  simp only [MonoidHom.comp_apply, MonoidHom.coe_snd] at hx
  have hc : ∀ a b : C2, a = b ∨ a * Multiplicative.ofAdd 1 = b := by decide
  rcases hc (toC2 x).1 c with h | h
  · exact ⟨x, Prod.ext h hx⟩
  · refine ⟨x * ev PresentedGroup.of kt3, ?_⟩
    rw [map_mul, toC2_kt3]
    exact Prod.ext h (by simp [hx])

theorem toC2_injective : Function.Injective toC2 := by
  have := card_pres3024_le.1
  have hsurj : Function.Surjective toC2.rangeRestrict := MonoidHom.rangeRestrict_surjective _
  have hcard : 3024 ≤ Nat.card toC2.range := by
    let f : C2 × PGammaL28 → toC2.range := fun x => ⟨(x.1, x.2), mem_range_toC2 x.1 x.2.2⟩
    have hf : Function.Injective f := fun a b h => by
      have h' := congrArg Subtype.val h
      simp only [f, Prod.mk.injEq] at h'
      exact Prod.ext h'.1 (Subtype.ext h'.2)
    have := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_prod, card_PGammaL28, Nat.card_eq_fintype_card (α := C2),
      show Fintype.card C2 = 2 from rfl] at this
  have hb := hsurj.bijective_of_nat_card_le (card_pres3024_le.2.trans hcard)
  exact MonoidHom.rangeRestrict_injective_iff.mp hb.1

theorem ev_eq_of_c2 {H : Type*} [Group H] (f : Fin 4 → H) (hf : ∀ w ∈ rels3024, ev f w = 1)
    {w₁ w₂ : Word 4} (h : evList c2Gen w₁ = evList c2Gen w₂) : ev f w₁ = ev f w₂ := by
  have h' : ev (PresentedGroup.of (rels := relSet rels3024)) w₁ =
      ev (PresentedGroup.of (rels := relSet rels3024)) w₂ := by
    apply toC2_injective
    rw [toC2, lift_ev, lift_ev, ev_eq_evList, ev_eq_evList, h]
  rw [← lift_ev rels3024 f hf, ← lift_ev rels3024 f hf, h']

theorem ev_kt3_sq {H : Type*} [Group H] (f : Fin 4 → H) (hf : ∀ w ∈ rels3024, ev f w = 1) :
    ev f (kt3 ++ kt3) = 1 := by
  rw [← ev_nil f]
  exact ev_eq_of_c2 f hf (by decide +kernel)

theorem ev_kt3_comm {H : Type*} [Group H] (f : Fin 4 → H) (hf : ∀ w ∈ rels3024, ev f w = 1) :
    ev f (kt3 ++ wy) = ev f (wy ++ kt3) :=
  ev_eq_of_c2 f hf (by decide +kernel)

end CFSG.Walter.Ree.T2.BaseRel

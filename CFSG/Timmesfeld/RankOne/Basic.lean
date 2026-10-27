module

public import CFSG.Timmesfeld.RankOne.Defs
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Timmesfeld

variable {X : Type*} [Group X]

namespace RankOne

theorem mem_map_conj {H : Subgroup X} {g x : X} :
    x ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ H := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem conj_mem_map_conj {H : Subgroup X} (g : X) {x : X} (hx : x ∈ H) :
    g * x * g⁻¹ ∈ H.map (MulAut.conj g).toMonoidHom := by
  rw [mem_map_conj]
  simpa [mul_assoc] using hx

theorem map_conj_mul (H : Subgroup X) (g g' : X) :
    H.map (MulAut.conj (g * g')).toMonoidHom =
      (H.map (MulAut.conj g').toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  ext x
  simp only [mem_map_conj]
  rw [show (g * g')⁻¹ * x * (g * g') = g'⁻¹ * (g⁻¹ * x * g) * g' by group]

@[simp] theorem map_conj_one (H : Subgroup X) :
    H.map (MulAut.conj (1 : X)).toMonoidHom = H := by
  ext x
  simp

theorem map_conj_of_mem {H : Subgroup X} {g : X} (hg : g ∈ H) :
    H.map (MulAut.conj g).toMonoidHom = H := by
  ext x
  rw [mem_map_conj]
  constructor
  · intro hx
    have := H.mul_mem (H.mul_mem hg hx) (H.inv_mem hg)
    simpa [mul_assoc] using this
  · intro hx
    exact H.mul_mem (H.mul_mem (H.inv_mem hg) hx) hg

theorem map_conj_eq_self_iff {H : Subgroup X} {g : X} :
    H.map (MulAut.conj g).toMonoidHom = H ↔ g ∈ Subgroup.normalizer (H : Set X) := by
  rw [Subgroup.mem_normalizer_iff'']
  constructor
  · intro heq x
    rw [← mem_map_conj, heq]
  · intro hn
    ext x
    rw [mem_map_conj, ← hn]

theorem map_conj_inj {H K : Subgroup X} {g : X} :
    H.map (MulAut.conj g).toMonoidHom = K.map (MulAut.conj g).toMonoidHom ↔ H = K :=
  (Subgroup.map_injective (MulAut.conj g).injective).eq_iff

@[simp] theorem map_conj_inv_map_conj (H : Subgroup X) (g : X) :
    (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = H := by
  rw [← map_conj_mul, inv_mul_cancel, map_conj_one]

@[simp] theorem map_conj_map_conj_inv (H : Subgroup X) (g : X) :
    (H.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = H := by
  rw [← map_conj_mul, mul_inv_cancel, map_conj_one]

theorem map_conj_eq_iff {H K : Subgroup X} {g : X} :
    H.map (MulAut.conj g).toMonoidHom = K ↔ H = K.map (MulAut.conj g⁻¹).toMonoidHom := by
  constructor
  · rintro rfl
    exact (map_conj_inv_map_conj H g).symm
  · rintro rfl
    exact map_conj_map_conj_inv K g

end RankOne

open RankOne

namespace IsElemAbRankOne

variable {A B : Subgroup X} (h : IsElemAbRankOne A B)
include h

theorem inv_eq_self {a : X} (ha : a ∈ A) : a⁻¹ = a :=
  inv_eq_of_mul_eq_one_right (h.sq a ha)

theorem exists_ne_one : ∃ a ∈ A, a ≠ 1 := by
  by_contra hA'
  have hA : ∀ a ∈ A, a = 1 := fun a ha => by_contra fun ha1 => hA' ⟨a, ha, ha1⟩
  apply h.ne
  have hAbot : A = ⊥ := (Subgroup.eq_bot_iff_forall A).2 hA
  have hBbot : B = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall B).2 fun b hb => ?_
    by_contra hb1
    obtain ⟨a, ha, ha1, -⟩ := h.moufang' b hb hb1
    exact ha1 (hA a ha)
  rw [hAbot, hBbot]

theorem exists_eq_map_conj : ∃ g : X, B = A.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨a, ha, ha1⟩ := h.exists_ne_one
  obtain ⟨b, -, -, hab⟩ := h.moufang a ha ha1
  refine ⟨a⁻¹ * b, ?_⟩
  rw [map_conj_mul, hab, map_conj_inv_map_conj]

theorem mul_self_of_mem_map_conj {g x : X} (hx : x ∈ A.map (MulAut.conj g).toMonoidHom) :
    x * x = 1 := by
  rw [mem_map_conj] at hx
  have := h.sq _ hx
  have h2 : g⁻¹ * (x * x) * g = 1 := by
    rw [← this]
    group
  have h3 : x * x = g * (g⁻¹ * (x * x) * g) * g⁻¹ := by group
  rw [h3, h2]
  group

theorem commute_of_mem_map_conj {g x y : X} (hx : x ∈ A.map (MulAut.conj g).toMonoidHom)
    (hy : y ∈ A.map (MulAut.conj g).toMonoidHom) : Commute x y := by
  rw [mem_map_conj] at hx hy
  have hc := h.comm _ hx _ hy
  have hxy : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
  have hyy : y = g * (g⁻¹ * y * g) * g⁻¹ := by group
  rw [hxy, hyy]
  exact (hc.conj g)

theorem symm : IsElemAbRankOne B A := by
  obtain ⟨g, hg⟩ := h.exists_eq_map_conj
  exact
    { gen := by rw [sup_comm]; exact h.gen
      ne := h.ne.symm
      comm := fun x hx y hy => h.commute_of_mem_map_conj (hg ▸ hx) (hg ▸ hy)
      sq := fun x hx => h.mul_self_of_mem_map_conj (hg ▸ hx)
      moufang := h.moufang'
      moufang' := h.moufang }

theorem eq_one_of_map_conj_eq {a : X} (ha : a ∈ A)
    (hB : B.map (MulAut.conj a).toMonoidHom = B) : a = 1 := by
  by_contra ha1
  obtain ⟨b, hb, -, hab⟩ := h.moufang a ha ha1
  rw [hB, map_conj_eq_iff, map_conj_of_mem (B.inv_mem hb)] at hab
  exact h.ne hab

theorem inf_eq_bot : A ⊓ B = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  exact h.eq_one_of_map_conj_eq hx.1 (map_conj_of_mem hx.2)

theorem map_conj_injOn {a a' : X} (ha : a ∈ A) (ha' : a' ∈ A)
    (heq : B.map (MulAut.conj a).toMonoidHom = B.map (MulAut.conj a').toMonoidHom) :
    a = a' := by
  have h1 : B.map (MulAut.conj (a'⁻¹ * a)).toMonoidHom = B := by
    rw [map_conj_mul, heq, map_conj_inv_map_conj]
  have := h.eq_one_of_map_conj_eq (A.mul_mem (A.inv_mem ha') ha) h1
  rw [inv_mul_eq_one] at this
  exact this.symm

theorem map_conj_ne {a : X} (ha : a ∈ A) : B.map (MulAut.conj a).toMonoidHom ≠ A := by
  intro hBA
  rw [map_conj_eq_iff, map_conj_of_mem (A.inv_mem ha)] at hBA
  exact h.ne hBA.symm

theorem map_conj_cases (g : X) :
    A.map (MulAut.conj g).toMonoidHom = A ∨
      ∃ a ∈ A, A.map (MulAut.conj g).toMonoidHom = B.map (MulAut.conj a).toMonoidHom := by
  let S : Subgroup X → Prop := fun C =>
    C = A ∨ ∃ a ∈ A, C = B.map (MulAut.conj a).toMonoidHom
  have hBA : ∀ b ∈ B, S (A.map (MulAut.conj b).toMonoidHom) := by
    intro b hb
    by_cases hb1 : b = 1
    · subst hb1
      left
      exact map_conj_one A
    obtain ⟨a, ha, -, hab⟩ := h.moufang' b hb hb1
    exact Or.inr ⟨a, ha, hab.symm⟩
  have hgen : ∀ x ∈ (A : Set X) ∪ B, ∀ C, S C → S (C.map (MulAut.conj x).toMonoidHom) := by
    rintro x (hx | hx) C (rfl | ⟨a, ha, rfl⟩)
    · exact Or.inl (map_conj_of_mem hx)
    · refine Or.inr ⟨x * a, A.mul_mem hx ha, ?_⟩
      rw [map_conj_mul]
    · exact hBA x hx
    · by_cases ha1 : a = 1
      · subst ha1
        refine Or.inr ⟨1, A.one_mem, ?_⟩
        rw [map_conj_one, map_conj_of_mem hx]
      obtain ⟨b, hb, -, hab⟩ := h.moufang a ha ha1
      rw [← hab, ← map_conj_mul]
      exact hBA _ (B.mul_mem hx hb)
  have hall : ∀ x : X, ∀ C, S C → S (C.map (MulAut.conj x).toMonoidHom) := by
    intro x
    have hx : x ∈ Subgroup.closure ((A : Set X) ∪ B) := by
      rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq, h.gen]
      trivial
    induction hx using Subgroup.closure_induction'' with
    | mem x hx => exact hgen x hx
    | inv_mem x hx =>
      have hx' : x⁻¹ ∈ (A : Set X) ∪ B := by
        rcases hx with hx | hx
        · exact Or.inl (A.inv_mem hx)
        · exact Or.inr (B.inv_mem hx)
      exact hgen _ hx'
    | one => intro C hC; rwa [map_conj_one]
    | mul x y _ _ hx hy =>
      intro C hC
      rw [map_conj_mul]
      exact hx _ (hy C hC)
  exact hall g A (Or.inl rfl)

theorem exists_eq_of_map_conj_ne {g : X} (hg : A.map (MulAut.conj g).toMonoidHom ≠ A) :
    ∃ a ∈ A, A.map (MulAut.conj g).toMonoidHom = B.map (MulAut.conj a).toMonoidHom :=
  (h.map_conj_cases g).resolve_left hg

theorem eq_of_map_conj_eq {a g : X} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hfix : (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      A.map (MulAut.conj g).toMonoidHom) :
    A.map (MulAut.conj g).toMonoidHom = A := by
  by_contra hne
  obtain ⟨a', ha', ha'eq⟩ := h.exists_eq_of_map_conj_ne hne
  rw [ha'eq, ← map_conj_mul] at hfix
  have := h.map_conj_injOn (A.mul_mem ha ha') ha' hfix
  exact ha1 (by simpa using this)

theorem eq_of_mem_of_map_conj_eq {x u g : X} (hu : u ∈ A.map (MulAut.conj x).toMonoidHom)
    (hu1 : u ≠ 1)
    (hfix : (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj u).toMonoidHom =
      A.map (MulAut.conj g).toMonoidHom) :
    A.map (MulAut.conj g).toMonoidHom = A.map (MulAut.conj x).toMonoidHom := by
  rw [mem_map_conj] at hu
  have ha1 : x⁻¹ * u * x ≠ 1 := by
    intro h1
    apply hu1
    have : u = x * (x⁻¹ * u * x) * x⁻¹ := by group
    rw [this, h1]
    group
  have hfix' : (A.map (MulAut.conj (x⁻¹ * g)).toMonoidHom).map
      (MulAut.conj (x⁻¹ * u * x)).toMonoidHom = A.map (MulAut.conj (x⁻¹ * g)).toMonoidHom := by
    rw [← map_conj_mul, show x⁻¹ * u * x * (x⁻¹ * g) = x⁻¹ * (u * g) by group, map_conj_mul,
      map_conj_mul A u g, hfix, ← map_conj_mul]
  have := h.eq_of_map_conj_eq hu ha1 hfix'
  rw [map_conj_mul, map_conj_eq_iff, inv_inv] at this
  exact this

theorem map_conj_inf_eq_bot {x y : X}
    (hne : A.map (MulAut.conj x).toMonoidHom ≠ A.map (MulAut.conj y).toMonoidHom) :
    A.map (MulAut.conj x).toMonoidHom ⊓ A.map (MulAut.conj y).toMonoidHom = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun u hu => ?_
  by_contra hu1
  exact hne (h.eq_of_mem_of_map_conj_eq hu.1 hu1 (map_conj_of_mem hu.2)).symm

theorem exists_mul_of_mem_normalizer {g : X} (hg : g ∈ Subgroup.normalizer (A : Set X)) :
    ∃ a ∈ A, ∃ k ∈ Subgroup.normalizer (A : Set X) ⊓ Subgroup.normalizer (B : Set X),
      g = a * k := by
  obtain ⟨g₀, hg₀⟩ := h.exists_eq_map_conj
  have hne : A.map (MulAut.conj (g * g₀)).toMonoidHom ≠ A := by
    intro heq
    rw [map_conj_mul, ← hg₀, map_conj_eq_iff, map_conj_eq_self_iff.2 (Subgroup.inv_mem _ hg)]
      at heq
    exact h.ne heq.symm
  obtain ⟨a, ha, haeq⟩ := h.exists_eq_of_map_conj_ne hne
  have hBg : B.map (MulAut.conj g).toMonoidHom = B.map (MulAut.conj a).toMonoidHom :=
    calc B.map (MulAut.conj g).toMonoidHom
        = (A.map (MulAut.conj g₀).toMonoidHom).map (MulAut.conj g).toMonoidHom := by rw [← hg₀]
      _ = A.map (MulAut.conj (g * g₀)).toMonoidHom := (map_conj_mul A g g₀).symm
      _ = B.map (MulAut.conj a).toMonoidHom := haeq
  refine ⟨a, ha, a⁻¹ * g, Subgroup.mem_inf.2 ⟨?_, ?_⟩, by group⟩
  · exact Subgroup.mul_mem _ (map_conj_eq_self_iff.1 (map_conj_of_mem (A.inv_mem ha))) hg
  · rw [← map_conj_eq_self_iff, map_conj_mul, hBg, map_conj_inv_map_conj]

end IsElemAbRankOne

end CFSG.Timmesfeld

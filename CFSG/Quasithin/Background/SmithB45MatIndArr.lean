module

public import CFSG.Quasithin.Background.SmithB45MatIndDefs
public import CFSG.Quasithin.Background.SmithB45MatSpin

public section

namespace CFSG.Quasithin.B45Mat.Ind

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.A5.M22Hat

theorem getElem!_id24_of_lt {i : ℕ} (hi : i < 24) : id24[i]! = i := by
  rw [id24, getElem!_pos _ i (by simpa using hi), Array.getElem_range]

theorem getElem!_comp24_of_lt (a b : Array ℕ) {i : ℕ} (hi : i < 24) :
    (comp24 a b)[i]! = a[b[i]!]! := by
  rw [comp24, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem hasArr_id24 : HasArr (1 : Equiv.Perm (Fin 24)) id24 := fun i => by
  rw [getElem!_id24_of_lt i.2]
  rfl

theorem hasArr_comp24 {σ τ : Equiv.Perm (Fin 24)} {a b : Array ℕ} (hσ : HasArr σ a)
    (hτ : HasArr τ b) : HasArr (σ * τ) (comp24 a b) := fun i => by
  rw [getElem!_comp24_of_lt a b i.2, Equiv.Perm.mul_apply, hσ, hτ]

theorem hasArr_wordArr {σ τ : Equiv.Perm (Fin 24)} {a b : Array ℕ} (hσ : HasArr σ a)
    (hτ : HasArr τ b) : ∀ w : List Bool, HasArr (wordG σ τ w) (wordArr a b w)
  | [] => hasArr_id24
  | z :: w => by
    rw [wordG, wordArr]
    refine hasArr_comp24 ?_ (hasArr_wordArr hσ hτ w)
    cases z
    · exact hσ
    · exact hτ

theorem map_wordG {G H : Type*} [Group G] [Group H] (f : G →* H) (x y : G) :
    ∀ w : List Bool, f (wordG x y w) = wordG (f x) (f y) w
  | [] => by rw [wordG, wordG, map_one]
  | z :: w => by
    rw [wordG, wordG, map_mul, map_wordG f x y w]
    cases z <;> rfl

theorem hasArr_inv_of {σ : Equiv.Perm (Fin 24)} {a : Array ℕ} (hσ : HasArr σ a)
    (h : ∀ j < 24, (invArr a)[a[j]!]! = j) : HasArr σ⁻¹ (invArr a) := fun i => by
  have h1 := h (σ⁻¹ i : Fin 24) (σ⁻¹ i).2
  have h2 : σ (σ⁻¹ i) = i := by simp
  rw [← hσ, h2] at h1
  exact h1.symm

structure CosetFacts (ts : Array (Array ℕ)) (m p : ℕ) (g : Array ℕ) : Prop where
  size_eq : ts.size = m
  pi_lt : ∀ k < m, (piArr ts g p)[k]! < m
  pi_point : ∀ k < m, (ts[(piArr ts g p)[k]!]!)[p]! = (comp24 g ts[k]!)[p]!
  point_inj : ∀ k < m, ∀ k' < m, (ts[k]!)[p]! = (ts[k']!)[p]! → k = k'
  inv_ok : ∀ k < m, ∀ j < 24, (invArr ts[k]!)[(ts[k]!)[j]!]! = j

theorem cosetFacts_of_cosetOK {a b : Array ℕ} {ts : Array (Array ℕ)} {m p : ℕ}
    (h : cosetOK a b ts m p = true) : CosetFacts ts m p a ∧ CosetFacts ts m p b := by
  simp only [cosetOK, piOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hm, hinj⟩, ha⟩, hb⟩, hinv⟩ := h
  have hinj' : ∀ k < m, ∀ k' < m, (ts[k]!)[p]! = (ts[k']!)[p]! → k = k' := by
    intro k hk k' hk' he
    rcases hinj k hk k' hk' with h1 | h1
    · exact h1
    · exact absurd he h1
  refine ⟨⟨hm, fun k hk => ?_, fun k hk => ?_, hinj', hinv⟩,
    ⟨hm, fun k hk => ?_, fun k hk => ?_, hinj', hinv⟩⟩
  · exact (ha k (hm ▸ hk)).1.trans_eq hm
  · exact (ha k (hm ▸ hk)).2
  · exact (hb k (hm ▸ hk)).1.trans_eq hm
  · exact (hb k (hm ▸ hk)).2

end CFSG.Quasithin.B45Mat.Ind

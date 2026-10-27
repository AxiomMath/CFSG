module

public import CFSG.Quasithin.EmptyFaithful.SzF53MUni

public section

namespace CFSG.Quasithin.F53Mod

open Equiv

variable {n : ℕ}

theorem fidx_conj (M : Model n) (g : Perm (Fin n)) (B : Subgroup (Perm (Fin n))) :
    (fixW M (B.map (MulAut.conj g).toMonoidHom)).index = (fixW M B).index := by
  have h1 := Subgroup.card_mul_index (fixW M (B.map (MulAut.conj g).toMonoidHom))
  have h2 := Subgroup.card_mul_index (fixW M B)
  rw [card_fixW_conj] at h1
  have hpos : 0 < Nat.card (fixW M B) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)

theorem idx_conj (M : Model n) (g a : Perm (Fin n)) : idx M (g * a * g⁻¹) = idx M a := by
  have : Subgroup.zpowers (g * a * g⁻¹) = (Subgroup.zpowers a).map (MulAut.conj g).toMonoidHom := by
    rw [MonoidHom.map_zpowers]
    simp [MulAut.conj_apply]
  unfold idx
  rw [this]
  exact fidx_conj M g _

theorem fixW_sup (M : Model n) (B C : Subgroup (Perm (Fin n))) :
    fixW M (B ⊔ C) = fixW M B ⊓ fixW M C := by
  apply le_antisymm
  · exact le_inf (fun w hw b hb => hw b (Subgroup.mem_sup_left hb))
      (fun w hw b hb => hw b (Subgroup.mem_sup_right hb))
  · intro w hw
    rw [Subgroup.mem_inf] at hw
    rw [Subgroup.sup_eq_closure, mem_fixW_closure]
    rintro s (hs | hs)
    · exact hw.1 s hs
    · exact hw.2 s hs

theorem fixW_antitone (M : Model n) {B C : Subgroup (Perm (Fin n))} (h : B ≤ C) :
    fixW M C ≤ fixW M B := fun _ hw b hb => hw b (h hb)

theorem index_fixW_sup_le (M : Model n) (B C : Subgroup (Perm (Fin n))) :
    (fixW M (B ⊔ C)).index ≤ (fixW M B).index * (fixW M C).index := by
  rw [fixW_sup]
  exact Subgroup.index_inf_le

theorem card_le_fidx_sq (M : Model n) {H B : Subgroup (Perm (Fin n))} (g : Perm (Fin n))
    (hgen : H ≤ B ⊔ B.map (MulAut.conj g).toMonoidHom) (hfix : fixW M H = ⊥) :
    Nat.card M.W ≤ (fixW M B).index ^ 2 := by
  have h1 : fixW M (B ⊔ B.map (MulAut.conj g).toMonoidHom) = ⊥ :=
    eq_bot_iff.mpr (hfix ▸ fixW_antitone M hgen)
  have h2 := index_fixW_sup_le M B (B.map (MulAut.conj g).toMonoidHom)
  rw [h1, Subgroup.index_bot, fidx_conj, ← sq] at h2
  exact h2

@[expose] def threeCyc012 : Perm (Fin 5) := swap 0 1 * swap 1 2

@[expose] def threeCyc234 : Perm (Fin 5) := swap 2 3 * swap 3 4

@[expose, irreducible] def alt5Words : Finset (Perm (Fin 5)) := wordSet [threeCyc012, threeCyc234] 6

set_option maxRecDepth 100000 in
private theorem alt5_wordSet : ∀ σ : Perm (Fin 5), Perm.sign σ = 1 → σ ∈ alt5Words := by
  unfold alt5Words
  decide +kernel

private theorem alt5Words_subset : ∀ x ∈ alt5Words, x ∈ Subgroup.closure {threeCyc012, threeCyc234} := by
  unfold alt5Words
  have e : {g | g ∈ [threeCyc012, threeCyc234]} = ({threeCyc012, threeCyc234} : Set (Perm (Fin 5))) := by
    ext g; simp
  rw [← e]
  exact wordSet_subset_closure [threeCyc012, threeCyc234] 6

theorem alt5_le_closure_threeCycles :
    alternatingGroup (Fin 5) ≤ Subgroup.closure {threeCyc012, threeCyc234} := fun σ hσ =>
  alt5Words_subset σ (alt5_wordSet σ (Perm.mem_alternatingGroup.mp hσ))

theorem eq_top_of_path_swaps {M : Subgroup (Perm (Fin 5))} (h01 : swap (0 : Fin 5) 1 ∈ M)
    (h12 : swap (1 : Fin 5) 2 ∈ M) (h23 : swap (2 : Fin 5) 3 ∈ M) (h34 : swap (3 : Fin 5) 4 ∈ M) :
    M = ⊤ := by
  have h02 := SubmonoidClass.swap_mem_trans M h01 h12
  have h03 := SubmonoidClass.swap_mem_trans M h02 h23
  have h04 := SubmonoidClass.swap_mem_trans M h03 h34
  have h13 := SubmonoidClass.swap_mem_trans M h12 h23
  have h14 := SubmonoidClass.swap_mem_trans M h13 h34
  have h24 := SubmonoidClass.swap_mem_trans M h23 h34
  rw [eq_top_iff, ← Equiv.Perm.closure_isSwap, Subgroup.closure_le]
  rintro _ ⟨a, b, hab, rfl⟩
  fin_cases a <;> fin_cases b <;> simp at hab <;>
    first | assumption | rwa [swap_comm]

theorem eq_top_of_that_swaps {M : Subgroup (Perm (Fin 5))} (h02 : swap (0 : Fin 5) 2 ∈ M)
    (h13 : swap (1 : Fin 5) 3 ∈ M) (h03 : swap (0 : Fin 5) 3 ∈ M) (h14 : swap (1 : Fin 5) 4 ∈ M) :
    M = ⊤ := by
  have h20 : swap (2 : Fin 5) 0 ∈ M := by rwa [swap_comm]
  have h31 : swap (3 : Fin 5) 1 ∈ M := by rwa [swap_comm]
  have h23 := SubmonoidClass.swap_mem_trans M h20 h03
  have h32 : swap (3 : Fin 5) 2 ∈ M := by rwa [swap_comm]
  have h01 := SubmonoidClass.swap_mem_trans M h03 h31
  have h04 := SubmonoidClass.swap_mem_trans M h01 h14
  have h12 := SubmonoidClass.swap_mem_trans M h13 h32
  have h24 := SubmonoidClass.swap_mem_trans M h20 h04
  have h34 := SubmonoidClass.swap_mem_trans M h31 h14
  rw [eq_top_iff, ← Equiv.Perm.closure_isSwap, Subgroup.closure_le]
  rintro _ ⟨a, b, hab, rfl⟩
  fin_cases a <;> fin_cases b <;> simp at hab <;>
    first | assumption | rwa [swap_comm]

theorem fixW_closure_four (M : Model n) (a b c d : Perm (Fin n)) :
    fixW M (Subgroup.closure {a, b, c, d}) =
      fixW M (Subgroup.zpowers a) ⊓ fixW M (Subgroup.zpowers b) ⊓ fixW M (Subgroup.zpowers c) ⊓
        fixW M (Subgroup.zpowers d) := by
  ext w
  simp only [mem_fixW_closure, Subgroup.mem_inf, mem_fixW_zpowers, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  tauto

theorem card_le_idx_pow_four (M : Model 5) {t : Perm (Fin 5)} (ht : t.IsSwap)
    (hfix : fixW M ⊤ = ⊥) : Nat.card M.W ≤ idx M t ^ 4 := by
  obtain ⟨x, y, hxy, rfl⟩ := ht
  have key : ∀ a b : Fin 5, a ≠ b → idx M (swap a b) = idx M (swap x y) := by
    intro a b hab
    obtain ⟨c, hc⟩ := isConj_iff.mp (Perm.isConj_swap hxy hab)
    rw [← hc, idx_conj]
  have h0 : fixW M (Subgroup.closure {swap (0 : Fin 5) 1, swap 1 2, swap 2 3, swap 3 4}) = ⊥ := by
    have : Subgroup.closure {swap (0 : Fin 5) 1, swap 1 2, swap 2 3, swap 3 4} = ⊤ :=
      eq_top_of_path_swaps (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
    rw [this, hfix]
  rw [fixW_closure_four] at h0
  have h1 := Subgroup.index_inf_le (H := fixW M (Subgroup.zpowers (swap (0 : Fin 5) 1)) ⊓
      fixW M (Subgroup.zpowers (swap 1 2)) ⊓ fixW M (Subgroup.zpowers (swap 2 3)))
    (K := fixW M (Subgroup.zpowers (swap 3 4)))
  have h2 := Subgroup.index_inf_le (H := fixW M (Subgroup.zpowers (swap (0 : Fin 5) 1)) ⊓
      fixW M (Subgroup.zpowers (swap 1 2))) (K := fixW M (Subgroup.zpowers (swap 2 3)))
  have h3 := Subgroup.index_inf_le (H := fixW M (Subgroup.zpowers (swap (0 : Fin 5) 1)))
    (K := fixW M (Subgroup.zpowers (swap 1 2)))
  rw [h0, Subgroup.index_bot] at h1
  have e01 : (fixW M (Subgroup.zpowers (swap (0 : Fin 5) 1))).index = idx M (swap x y) :=
    key 0 1 (by decide)
  have e12 : (fixW M (Subgroup.zpowers (swap (1 : Fin 5) 2))).index = idx M (swap x y) :=
    key 1 2 (by decide)
  have e23 : (fixW M (Subgroup.zpowers (swap (2 : Fin 5) 3))).index = idx M (swap x y) :=
    key 2 3 (by decide)
  have e34 : (fixW M (Subgroup.zpowers (swap (3 : Fin 5) 4))).index = idx M (swap x y) :=
    key 3 4 (by decide)
  rw [e34] at h1
  rw [e23] at h2
  rw [e01, e12] at h3
  calc Nat.card M.W ≤ _ := h1
    _ ≤ (_ * idx M (swap x y)) * idx M (swap x y) := Nat.mul_le_mul_right _ h2
    _ ≤ ((idx M (swap x y) * idx M (swap x y)) * idx M (swap x y)) * idx M (swap x y) := by
        gcongr
    _ = idx M (swap x y) ^ 4 := by ring

@[expose] def conjT34 : Perm (Fin 5) := swap 3 4

@[expose] def conjThat234 : Perm (Fin 5) := swap 2 3 * swap 3 4

@[expose] def altTGens : List (Perm (Fin 5)) :=
  [swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2, swap 0 1 * swap 2 4,
    swap 0 2 * swap 1 4, swap 0 4 * swap 1 2]

@[expose, irreducible] def altTWords : Finset (Perm (Fin 5)) := wordSet altTGens 4

set_option maxRecDepth 100000 in
private theorem altT_wordSet : ∀ σ : Perm (Fin 5), Perm.sign σ = 1 → σ ∈ altTWords := by
  unfold altTWords altTGens
  decide +kernel

private theorem altTWords_subset : ∀ x ∈ altTWords, x ∈ Subgroup.closure {g | g ∈ altTGens} := by
  unfold altTWords
  exact wordSet_subset_closure altTGens 4

private theorem altTGens_mem : ∀ x ∈ altTGens, x ∈ S5T ∨ x ∈ S5T.map (MulAut.conj conjT34).toMonoidHom := by
  intro x hx
  have hT : ∀ y, y ∈ S5T ↔ y ∈ S5TF := mem_S5T_iff
  have hg : ∀ y : Perm (Fin 5), y ∈ S5T.map (MulAut.conj conjT34).toMonoidHom ↔ conjT34⁻¹ * y * conjT34 ∈ S5T :=
    mem_map_conj S5T conjT34
  simp only [hg, hT]
  revert x
  unfold altTGens S5TF conjT34
  decide +kernel

theorem alt5_le_syl_sup :
    alternatingGroup (Fin 5) ≤ S5T ⊔ S5T.map (MulAut.conj conjT34).toMonoidHom := by
  intro σ hσ
  have h := altTWords_subset σ (altT_wordSet σ (Perm.mem_alternatingGroup.mp hσ))
  refine (Subgroup.closure_le _).mpr (fun x hx => ?_) h
  rcases altTGens_mem x hx with h1 | h1
  · exact Subgroup.mem_sup_left h1
  · exact Subgroup.mem_sup_right h1

theorem top_le_that_sup :
    (⊤ : Subgroup (Perm (Fin 5))) ≤ S5That ⊔ S5That.map (MulAut.conj conjThat234).toMonoidHom := by
  have hm : ∀ x ∈ S5That, conjThat234 * x * conjThat234⁻¹ ∈ S5That.map (MulAut.conj conjThat234).toMonoidHom :=
    fun x hx => ⟨x, hx, by simp [MulAut.conj_apply]⟩
  have h02 : swap (0 : Fin 5) 2 ∈ S5That := Subgroup.subset_closure (by simp)
  have h13 : swap (1 : Fin 5) 3 ∈ S5That := Subgroup.subset_closure (by simp)
  have e03 : conjThat234 * swap (0 : Fin 5) 2 * conjThat234⁻¹ = swap 0 3 := by unfold conjThat234; decide +kernel
  have e14 : conjThat234 * swap (1 : Fin 5) 3 * conjThat234⁻¹ = swap 1 4 := by unfold conjThat234; decide +kernel
  have h03 := hm _ h02
  have h14 := hm _ h13
  rw [e03] at h03
  rw [e14] at h14
  exact (eq_top_of_that_swaps (M := S5That ⊔ S5That.map (MulAut.conj conjThat234).toMonoidHom)
    (Subgroup.mem_sup_left h02) (Subgroup.mem_sup_left h13) (Subgroup.mem_sup_right h03)
    (Subgroup.mem_sup_right h14)).ge

end CFSG.Quasithin.F53Mod

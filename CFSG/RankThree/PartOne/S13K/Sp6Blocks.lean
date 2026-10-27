module

public import CFSG.RankThree.PartOne.S13K.Sp6Supp

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartOne.S13K

open CFSG CFSG.Assembly CFSG.RankThree.PartOne.KFQ CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne

variable {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}

@[expose] def suppB (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool) (j : Fin 3) : Bool :=
  decide (π j ≠ j) || ε j

@[expose] noncomputable def cj (m : ↥(M10 K)) (B : Subgroup ↥(M10 K)) : Subgroup ↥(M10 K) :=
  B.map (MulAut.conj m).toMonoidHom

theorem mem_cj {m x : ↥(M10 K)} {B : Subgroup ↥(M10 K)} : x ∈ cj m B ↔ ∃ b ∈ B, m * b * m⁻¹ = x := by
  unfold cj
  rw [Subgroup.mem_map]
  simp [MulAut.conj_apply]

theorem fixCoord_of_mem_cj {σ : Equiv.Perm (Fin 3)} {τ : Fin 3 → Bool} {B : Subgroup ↥(M10 K)}
    {j : Fin 3} (hB : ∀ b ∈ B, FixCoord b.1 j) {g : ↥(M10 K)} (hg : g ∈ cj (sg10 σ τ) B) :
    FixCoord g.1 (σ j) := by
  obtain ⟨b, hb, rfl⟩ := mem_cj.mp hg
  exact fixCoord_conj (hB b hb)

theorem sBlk_fix {b : ↥(M10 K)} (hb : b ∈ sBlk K) {j : Fin 3} (hj : j ≠ 0) : FixCoord b.1 j := by
  intro a
  fin_cases j
  · exact absurd rfl hj
  · exact (hb a).1
  · exact (hb a).2

theorem dBlk_fix {b : ↥(M10 K)} (hb : b ∈ dBlk K) : FixCoord b.1 2 := fun a => hb.1 a

namespace Sp6Ctx

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L E : Subgroup G} {f : ℕ}
  (C : Sp6Ctx p A c L E f K)

theorem tSgn_eq_conj (σ : Equiv.Perm (Fin 3)) (τ : Fin 3 → Bool) {π π' : Equiv.Perm (Fin 3)}
    {s s' : Fin 3 → Bool}
    (hconj : sg10 σ τ * sg10 π' s' * (sg10 σ τ)⁻¹ = (sg10 π s : ↥(M10 K))) :
    C.tSgn π s = conjAut E (C.phi (sg10 σ τ))
      (C.mem_normalizer (sg10_hg1 C.hpq' σ τ) (C.hg2_of_hg1 (sg10_hg1 C.hpq' σ τ))) * C.tSgn π' s' *
      (conjAut E (C.phi (sg10 σ τ))
        (C.mem_normalizer (sg10_hg1 C.hpq' σ τ) (C.hg2_of_hg1 (sg10_hg1 C.hpq' σ τ))))⁻¹ := by
  unfold conjAut tSgn
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  change C.phi (sg10 π s) = C.phi (sg10 σ τ) * C.phi (sg10 π' s') * (C.phi (sg10 σ τ))⁻¹
  rw [← hconj, map_mul, map_mul, map_inv]

theorem kZero_tSgn_conj (σ : Equiv.Perm (Fin 3)) (τ : Fin 3 → Bool) {π π' : Equiv.Perm (Fin 3)}
    {s s' : Fin 3 → Bool}
    (hconj : sg10 σ τ * sg10 π' s' * (sg10 σ τ)⁻¹ = (sg10 π s : ↥(M10 K)))
    {B : Subgroup ↥(M10 K)} (h : kZero p E (C.tSgn π' s') = B.map C.phi) :
    kZero p E (C.tSgn π s) = (cj (sg10 σ τ) B).map C.phi := by
  rw [C.tSgn_eq_conj σ τ hconj, kZero_conj, h]
  unfold conjBy cj
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext b
  simp [MulAut.conj_apply, map_mul, map_inv]

theorem kZero_gS : kZero p E (C.tSgn 1 ![true, false, false]) = (sBlk K).map C.phi :=
  C.kfAtBlock_gS.2

theorem kZero_gD : kZero p E (C.tSgn (Equiv.swap 0 1) ![false, false, false]) =
    (dBlk K).map C.phi := C.kfAtBlock_gD.2

theorem exists_blk_S (i : Fin 3) :
    ∃ B : Subgroup ↥(M10 K), kZero p E (C.tSgn 1 (fun j => decide (j = i))) = B.map C.phi ∧
      ∀ g ∈ B, ∀ j, j ≠ i → FixCoord g.1 j := by
  have hconj : sg10 (Equiv.swap 0 i) (fun _ => false) * sg10 1 ![true, false, false] *
      (sg10 (Equiv.swap 0 i) (fun _ => false))⁻¹ = (sg10 1 (fun j => decide (j = i)) : ↥(M10 K)) := by
    rw [sg10_conj_perm, sact_fun_swap i]
    congr 1
    simp
  refine ⟨cj (sg10 (Equiv.swap 0 i) (fun _ => false)) (sBlk K),
    C.kZero_tSgn_conj _ _ hconj C.kZero_gS, fun g hg j hj => ?_⟩
  have hj' : Equiv.swap 0 i j ≠ 0 := by
    intro h0
    apply hj
    have := congrArg (Equiv.swap (0 : Fin 3) i) h0
    simpa using this
  have := fixCoord_of_mem_cj (σ := Equiv.swap 0 i) (τ := fun _ => false)
    (fun b hb => sBlk_fix hb hj') hg
  simpa using this

theorem kZero_D0 {a b : Fin 3} {σ : Equiv.Perm (Fin 3)} (h0 : σ 0 = a) (h1 : σ 1 = b) :
    kZero p E (C.tSgn (Equiv.swap a b) (fun _ => false)) =
      (cj (sg10 σ (fun _ => false)) (dBlk K)).map C.phi := by
  have hconj : sg10 σ (fun _ => false) * sg10 (Equiv.swap 0 1) ![false, false, false] *
      (sg10 σ (fun _ => false))⁻¹ = (sg10 (Equiv.swap a b) (fun _ => false) : ↥(M10 K)) := by
    rw [sg10_conj_perm]
    have hperm : σ * Equiv.swap 0 1 * σ⁻¹ = Equiv.swap a b := by
      rw [Equiv.mul_swap_eq_swap_mul, mul_inv_cancel_right, h0, h1]
    have hfun : (fun j => (![false, false, false] : Fin 3 → Bool) (σ.symm j)) = fun _ => false := by
      funext j
      exact bool_false_vec _
    rw [hperm, hfun]
  exact C.kZero_tSgn_conj _ _ hconj C.kZero_gD

theorem kZero_D1 {a b : Fin 3} {σ : Equiv.Perm (Fin 3)} (hab : a ≠ b) (h0 : σ 0 = a) (h1 : σ 1 = b) :
    kZero p E (C.tSgn (Equiv.swap a b) (fun j => decide (j = a ∨ j = b))) =
      (cj (sg10 1 (fun j => decide (j = b))) (cj (sg10 σ (fun _ => false)) (dBlk K))).map C.phi :=
  C.kZero_tSgn_conj _ _ (sg10_conj_sign hab) (C.kZero_D0 h0 h1)

end Sp6Ctx

theorem fixCoord_cj_dBlk {a b : Fin 3} {σ : Equiv.Perm (Fin 3)} (h0 : σ 0 = a) (h1 : σ 1 = b)
    {g : ↥(M10 K)} (hg : g ∈ cj (sg10 σ (fun _ => false)) (dBlk K)) {j : Fin 3} (hja : j ≠ a)
    (hjb : j ≠ b) : FixCoord g.1 j := by
  have hj2 : σ.symm j = 2 := by
    have h0' : σ.symm j ≠ 0 := fun h => hja (by rw [← h0, ← h]; simp)
    have h1' : σ.symm j ≠ 1 := fun h => hjb (by rw [← h1, ← h]; simp)
    revert h0' h1'
    generalize σ.symm j = k
    revert k
    decide
  have h2 : σ 2 = j := by rw [← hj2]; simp
  have := fixCoord_of_mem_cj (σ := σ) (τ := fun _ => false) (j := 2) (fun b hb => dBlk_fix hb) hg
  rw [h2] at this
  exact this

namespace Sp6Ctx

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L E : Subgroup G} {f : ℕ}
  (C : Sp6Ctx p A c L E f K)

theorem exists_blk_D0 {a b : Fin 3} (hab : a ≠ b) :
    ∃ B : Subgroup ↥(M10 K), kZero p E (C.tSgn (Equiv.swap a b) (fun _ => false)) = B.map C.phi ∧
      ∀ g ∈ B, ∀ j, j ≠ a → j ≠ b → FixCoord g.1 j := by
  obtain ⟨σ, h0, h1⟩ := exists_perm_of_ne a b hab
  exact ⟨cj (sg10 σ (fun _ => false)) (dBlk K), C.kZero_D0 h0 h1,
    fun g hg j hja hjb => fixCoord_cj_dBlk h0 h1 hg hja hjb⟩

theorem exists_blk_D1 {a b : Fin 3} (hab : a ≠ b) :
    ∃ B : Subgroup ↥(M10 K), kZero p E (C.tSgn (Equiv.swap a b)
        (fun j => decide (j = a ∨ j = b))) = B.map C.phi ∧
      ∀ g ∈ B, ∀ j, j ≠ a → j ≠ b → FixCoord g.1 j := by
  obtain ⟨σ, h0, h1⟩ := exists_perm_of_ne a b hab
  refine ⟨cj (sg10 1 (fun j => decide (j = b))) (cj (sg10 σ (fun _ => false)) (dBlk K)),
    C.kZero_D1 hab h0 h1, fun g hg j hja hjb => ?_⟩
  have := fixCoord_of_mem_cj (σ := 1) (τ := fun j => decide (j = b))
    (fun g hg => fixCoord_cj_dBlk h0 h1 hg hja hjb) hg
  simpa using this

end Sp6Ctx

end CFSG.RankThree.PartOne.S13K

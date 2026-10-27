module

public import CFSG.LocalAnalysis.StandardType.FS81.E7RowA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81.E7Row

open scoped Matrix

theorem spMat_injective {σ σ' : Equiv.Perm (Fin 8)} {s s' : Fin 8 → ZMod 3} (hs : IsSign s)
    (h : spMat σ s = spMat σ' s') : σ = σ' ∧ s = s' := by
  have key : ∀ j, σ j = σ' j ∧ s j = s' j := by
    intro j
    have e := congrFun (congrFun h (σ j)) j
    simp only [spMat_apply] at e
    by_cases hj : σ j = σ' j
    · rw [if_pos hj] at e
      exact ⟨hj, e⟩
    · rw [if_neg hj] at e
      exfalso
      rcases hs j with h1 | h1 <;> rw [h1] at e <;> exact absurd e (by decide)
  exact ⟨Equiv.ext fun j => (key j).1, funext fun j => (key j).2⟩

set_option maxRecDepth 100000 in
theorem card_signs_hSix :
    (Finset.univ.filter fun s : Fin 8 → ZMod 3 =>
      (∀ i, s i = 1 ∨ s i = -1) ∧ s 0 = 1 ∧ s 1 = 1 ∧ ∏ i : Fin 6, s i.succ.succ = 1).card = 32 := by
  decide +kernel

theorem card_hSix : Nat.card ↥hSix = 23040 := by
  let P := {f : Equiv.Perm (Fin 8) // ∀ a, ¬ (a ≠ 0 ∧ a ≠ 1) → f a = a}
  let S := {s : Fin 8 → ZMod 3 //
    (∀ i, s i = 1 ∨ s i = -1) ∧ s 0 = 1 ∧ s 1 = 1 ∧ ∏ i : Fin 6, s i.succ.succ = 1}
  let F : P × S → Matrix (Fin 8) (Fin 8) (ZMod 3) := fun q => spMat q.1.1 q.2.1
  have hF : Function.Injective F := by
    rintro ⟨⟨σ, hσ⟩, ⟨s, hs⟩⟩ ⟨⟨σ', hσ'⟩, ⟨s', hs'⟩⟩ h
    obtain ⟨h1, h2⟩ := spMat_injective hs.1 h
    subst h1
    subst h2
    rfl
  have hrange : Set.range F = hSix := by
    ext A
    constructor
    · rintro ⟨⟨⟨σ, hσ⟩, ⟨s, hs, hs0, hs1, hp⟩⟩, rfl⟩
      exact ⟨σ, s, hs, ⟨hσ 0 (by simp), hs0, hσ 1 (by simp), hs1, hp⟩, rfl⟩
    · rintro ⟨σ, s, hs, ⟨h0, hs0, h1, hs1, hp⟩, rfl⟩
      refine ⟨(⟨σ, fun a ha => ?_⟩, ⟨s, hs, hs0, hs1, hp⟩), rfl⟩
      rw [not_and_or, not_not, not_not] at ha
      rcases ha with rfl | rfl
      · exact h0
      · exact h1
  have hP : Nat.card P = 720 := by
    rw [← Nat.card_congr (Equiv.Perm.subtypeEquivSubtypePerm fun a : Fin 8 => a ≠ 0 ∧ a ≠ 1),
      Nat.card_perm, Nat.card_eq_fintype_card]
    rfl
  have hS : Nat.card S = 32 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact card_signs_hSix
  rw [← hrange, Nat.card_range_of_injective hF, Nat.card_prod, hP, hS]

theorem mem_hSix_of_mem_hSeven {A : Matrix (Fin 8) (Fin 8) (ZMod 3)} (hA : A ∈ hSeven)
    (he : A *ᵥ Pi.single 1 1 = Pi.single 1 1) : A ∈ hSix := by
  obtain ⟨σ, s, hs, ⟨h0, hs0, h1, hp⟩, rfl⟩ := hA
  refine ⟨σ, s, hs, ⟨h0, hs0, h1, ?_, hp⟩, rfl⟩
  have e := congrFun he 1
  rw [spMat_mulVec] at e
  have : σ.symm 1 = 1 := by rw [Equiv.symm_apply_eq, h1]
  simpa [this] using e

@[expose, reducible] def glAct : MulAction (GL (Fin 8) (ZMod 3)) (Coords 8) where
  smul g v := (g : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ v
  one_smul v := by
    show ((1 : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ v = v
    rw [Units.val_one, Matrix.one_mulVec]
  mul_smul g h v := by
    show ((g * h : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ v =
      (g : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ ((h : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ v)
    rw [Units.val_mul, Matrix.mulVec_mulVec]

variable {X : Subgroup (GL (Fin 8) (ZMod 3))}

attribute [local instance] glAct in
theorem ncard_orb1 (h : CoreHyp X) : (orb1 X).ncard = 126 := by
  have horb : MulAction.orbit ↥(X ⊓ fixE0 7) (Pi.single 1 1 : Coords 8) = orb1 X := by
    ext v
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hstab : Nat.card ↥(MulAction.stabilizer ↥(X ⊓ fixE0 7) (Pi.single 1 1 : Coords 8)) =
      23040 := by
    rw [← card_hSix]
    have hmem : ∀ x : ↥(MulAction.stabilizer ↥(X ⊓ fixE0 7) (Pi.single 1 1 : Coords 8)),
        (((x : ↥(X ⊓ fixE0 7)) : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) ∈ hSix := by
      rintro ⟨⟨x, hxX, hxF⟩, hx⟩
      have he : (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 1 1 = Pi.single 1 1 := hx
      exact mem_hSix_of_mem_hSeven (h.hstab x hxX (mem_fixE0.mp hxF) ⟨1, by rw [he, one_smul]⟩) he
    refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨_, hmem x⟩) ⟨?_, ?_⟩)
    · intro a b e
      apply Subtype.ext
      apply Subtype.ext
      apply Units.ext
      exact congrArg Subtype.val e
    · rintro ⟨A, hA⟩
      obtain ⟨x, hx, rfl⟩ := h.exists_fix (hSix_subset_hSeven hA)
      obtain ⟨σ, s, -, ⟨-, -, h1, hs1, -⟩, hAeq⟩ := hA
      have he : (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 1 1 = Pi.single 1 1 := by
        rw [hAeq, spMat_mulVec]
        funext i
        by_cases hi : i = 1
        · subst hi
          have : σ.symm 1 = 1 := by rw [Equiv.symm_apply_eq, h1]
          simp [this, hs1]
        · have : σ.symm i ≠ 1 := fun e => hi (by rw [← h1, ← e, Equiv.apply_symm_apply])
          simp [this, hi]
      exact ⟨⟨⟨x, hx⟩, he⟩, rfl⟩
  have hidx := MulAction.index_stabilizer ↥(X ⊓ fixE0 7) (Pi.single 1 1 : Coords 8)
  have hmul := Subgroup.index_mul_card
    (MulAction.stabilizer ↥(X ⊓ fixE0 7) (Pi.single 1 1 : Coords 8))
  rw [hidx, horb, hstab, h.hcard] at hmul
  omega

@[expose] def cvec (a : ZMod 3) (k : ℕ) (p : ZMod 3) : Coords 8 := fun i =>
  if i = 0 then 0 else if i = 1 then a else
    if i.val - 1 ≤ k then (if k = 6 ∧ i = 7 then p else 1) else 0

@[expose] def cand (n : Fin 16) : Coords 8 :=
  if n.val < 6 then cvec 0 n.val 1 else if n.val = 6 then cvec 0 6 1 else if n.val = 7 then cvec 0 6 2
    else if n.val < 14 then cvec 1 (n.val - 8) 1 else if n.val = 14 then cvec 1 6 1 else cvec 1 6 2

@[expose] def candSize (n : Fin 16) : ℕ :=
  [1, 12, 60, 160, 240, 192, 32, 32, 2, 24, 120, 320, 480, 384, 64, 64].getD n.val 0

set_option maxRecDepth 100000 in
theorem nf_mem_cand : ∀ v : Coords 8, v 0 = 0 → ∃ n : Fin 16, nf v = cand n := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem card_cls : ∀ n : Fin 16,
    (Finset.univ.filter fun v : Coords 8 => v 0 = 0 ∧ nf v = cand n).card = candSize n := by
  decide +kernel

theorem cand_injective : Function.Injective cand := by
  decide

theorem nf_cand : ∀ n : Fin 16, nf (cand n) = cand n ∧ cand n 0 = 0 := by
  decide

theorem cand_not_supp_two : ∀ n : Fin 16, 3 ≤ n.val → n.val ≤ 7 →
    ¬ ∃ j k : Fin 8, ∀ i, i ≠ j → i ≠ k → cand n i = 0 := by
  decide

theorem cand_one_zero : ∀ n : Fin 16, n.val ≤ 7 → cand n 1 = 0 := by
  decide

theorem cand_eight : cand 8 = Pi.single 1 1 := by
  decide

theorem cand_zero : cand 0 = 0 := by
  decide


theorem mem_orb1_iff (h : CoreHyp X) (v : Coords 8) : v ∈ orb1 X ↔ v 0 = 0 ∧ nf v ∈ orb1 X := by
  have hinv : ∀ g : Gen, g.Valid → ∀ v ∈ orb1 X, g.act v ∈ orb1 X := fun _ hg _ hv => orb1_gen h hg hv
  constructor
  · intro hv
    exact ⟨orb1_zero h hv, (mem_iff_nf_mem hinv v).mp hv⟩
  · rintro ⟨-, hv⟩
    exact (mem_iff_nf_mem hinv v).mpr hv

open Classical in
@[irreducible] noncomputable def bit (X : Subgroup (GL (Fin 8) (ZMod 3))) (n : Fin 16) : ℕ :=
  if cand n ∈ orb1 X then 1 else 0

theorem bit_le (n : Fin 16) : bit X n ≤ 1 := by
  unfold bit
  split_ifs <;> omega

theorem sum_fin16 (f : Fin 16 → ℕ) : ∑ n, f n = f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 +
    (f 7 + (f 8 + (f 9 + (f 10 + (f 11 + (f 12 + (f 13 + (f 14 + f 15)))))))))))))) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  rfl

theorem ncard_orb1_eq_sum (h : CoreHyp X) : (orb1 X).ncard = ∑ n : Fin 16, bit X n * candSize n := by
  classical
  set S : Finset (Coords 8) := Finset.univ.filter (· ∈ orb1 X) with hS
  have hSo : (S : Set (Coords 8)) = orb1 X := by
    ext v
    simp [hS]
  rw [← hSo, Set.ncard_coe_finset]
  have hmaps : ∀ v ∈ S, nf v ∈ Finset.univ.image cand := by
    intro v hv
    have hv' : v ∈ orb1 X := (Finset.mem_filter.mp hv).2
    obtain ⟨n, hn⟩ := nf_mem_cand v (orb1_zero h hv')
    exact Finset.mem_image.mpr ⟨n, Finset.mem_univ _, hn.symm⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps,
    Finset.sum_image (fun a _ b _ e => cand_injective e)]
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold bit
  by_cases hc : cand n ∈ orb1 X
  · rw [if_pos hc, one_mul, ← card_cls n]
    congr 1
    ext v
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hv, hn⟩
      exact ⟨orb1_zero h hv, hn⟩
    · rintro ⟨h0, hn⟩
      exact ⟨(mem_orb1_iff h v).mpr ⟨h0, hn ▸ hc⟩, hn⟩
  · rw [if_neg hc, zero_mul, Finset.card_eq_zero]
    ext v
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
      not_and]
    intro hv hn
    exact hc (hn ▸ ((mem_orb1_iff h v).mp hv).2)

theorem bit_zero : bit X 0 = 0 := by
  unfold bit
  rw [if_neg]
  rintro ⟨x, -, hx⟩
  rw [cand_zero] at hx
  have e := congrFun (mulVec_inv_mulVec x (Pi.single 1 1)) 1
  rw [hx, Matrix.mulVec_zero] at e
  simp at e

theorem bit_eight : bit X 8 = 1 := by
  unfold bit
  rw [if_pos (by rw [cand_eight]; exact e1_mem_orb1)]

theorem bit_small (h : CoreHyp X) (n : Fin 16) (h3 : 3 ≤ n.val) (h7 : n.val ≤ 7) : bit X n = 0 := by
  unfold bit
  rw [if_neg]
  intro hc
  have h1 : cand n 1 = 0 := cand_one_zero n h7
  exact cand_not_supp_two n h3 h7 (supp_two_of_mem_orb1 h hc h1)

theorem bits_arith : ∀ b : Fin 9 → Fin 2,
    (b 0).val * 12 + ((b 1).val * 60 + (2 + ((b 2).val * 24 + ((b 3).val * 120 + ((b 4).val * 320 +
      ((b 5).val * 480 + ((b 6).val * 384 + ((b 7).val * 64 + (b 8).val * 64)))))))) = 126 →
    (b 1).val = 1 ∧ (b 7).val + (b 8).val = 1 ∧ (b 0).val = 0 ∧ (b 2).val = 0 ∧ (b 3).val = 0 ∧
      (b 4).val = 0 ∧ (b 5).val = 0 ∧ (b 6).val = 0 := by
  decide +kernel

theorem orb1_bits (h : CoreHyp X) :
    bit X 2 = 1 ∧ bit X 14 + bit X 15 = 1 ∧ bit X 1 = 0 ∧ bit X 9 = 0 ∧ bit X 10 = 0 ∧
      bit X 11 = 0 ∧ bit X 12 = 0 ∧ bit X 13 = 0 := by
  have hsum := (ncard_orb1_eq_sum h).symm.trans (ncard_orb1 h)
  rw [sum_fin16] at hsum
  have s0 : candSize 0 = 1 := rfl
  have s1 : candSize 1 = 12 := rfl
  have s2 : candSize 2 = 60 := rfl
  have s3 : candSize 3 = 160 := rfl
  have s4 : candSize 4 = 240 := rfl
  have s5 : candSize 5 = 192 := rfl
  have s6 : candSize 6 = 32 := rfl
  have s7 : candSize 7 = 32 := rfl
  have s8 : candSize 8 = 2 := rfl
  have s9 : candSize 9 = 24 := rfl
  have s10 : candSize 10 = 120 := rfl
  have s11 : candSize 11 = 320 := rfl
  have s12 : candSize 12 = 480 := rfl
  have s13 : candSize 13 = 384 := rfl
  have s14 : candSize 14 = 64 := rfl
  have s15 : candSize 15 = 64 := rfl
  rw [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, bit_zero,
    bit_small h 3 (by decide) (by decide), bit_small h 4 (by decide) (by decide),
    bit_small h 5 (by decide) (by decide), bit_small h 6 (by decide) (by decide),
    bit_small h 7 (by decide) (by decide), bit_eight] at hsum
  simp only [zero_mul, zero_add, one_mul] at hsum
  let b : Fin 9 → Fin 2 := ![⟨bit X 1, Nat.lt_succ_of_le (bit_le 1)⟩,
    ⟨bit X 2, Nat.lt_succ_of_le (bit_le 2)⟩, ⟨bit X 9, Nat.lt_succ_of_le (bit_le 9)⟩,
    ⟨bit X 10, Nat.lt_succ_of_le (bit_le 10)⟩, ⟨bit X 11, Nat.lt_succ_of_le (bit_le 11)⟩,
    ⟨bit X 12, Nat.lt_succ_of_le (bit_le 12)⟩, ⟨bit X 13, Nat.lt_succ_of_le (bit_le 13)⟩,
    ⟨bit X 14, Nat.lt_succ_of_le (bit_le 14)⟩, ⟨bit X 15, Nat.lt_succ_of_le (bit_le 15)⟩]
  exact bits_arith b hsum

@[expose] def IsRoot7 (δ : ZMod 3) (v : Coords 8) : Prop :=
  v 0 = 0 ∧ (nf v = cand 8 ∨ nf v = cand 2 ∨ nf v = cvec 1 6 δ)

instance (δ : ZMod 3) (v : Coords 8) : Decidable (IsRoot7 δ v) := by
  unfold IsRoot7
  infer_instance

theorem mem_bit {n : Fin 16} : cand n ∈ orb1 X ↔ bit X n = 1 := by
  unfold bit
  split_ifs with hc <;> simp [hc]

theorem orb1_eq (h : CoreHyp X) : ∃ δ : ZMod 3, (δ = 1 ∨ δ = -1) ∧ ∀ v, v ∈ orb1 X ↔ IsRoot7 δ v := by
  obtain ⟨b2, b1415, b1, b9, b10, b11, b12, b13⟩ := orb1_bits h
  have b0 : bit X 0 = 0 := bit_zero
  have b8 : bit X 8 = 1 := bit_eight
  have bs : ∀ n : Fin 16, 3 ≤ n.val → n.val ≤ 7 → bit X n = 0 := fun n h3 h7 => bit_small h n h3 h7
  have l14 := bit_le (X := X) 14
  have l15 := bit_le (X := X) 15
  have hc15 : cand 15 = cvec 1 6 (-1) := by decide
  have hc14 : cand 14 = cvec 1 6 1 := by decide
  by_cases h14 : bit X 14 = 1
  · refine ⟨1, Or.inl rfl, fun v => ?_⟩
    rw [mem_orb1_iff h v]
    constructor
    · rintro ⟨h0, hv⟩
      obtain ⟨n, hn⟩ := nf_mem_cand v h0
      rw [hn, mem_bit] at hv
      refine ⟨h0, ?_⟩
      rw [hn, ← hc14]
      fin_cases n <;> simp_all
    · rintro ⟨h0, h8 | h2 | h6⟩
      · exact ⟨h0, by rw [h8, mem_bit]; exact b8⟩
      · exact ⟨h0, by rw [h2, mem_bit]; exact b2⟩
      · exact ⟨h0, by rw [h6, ← hc14, mem_bit]; exact h14⟩
  · have h15 : bit X 15 = 1 := by omega
    have h14' : bit X 14 = 0 := by omega
    refine ⟨-1, Or.inr rfl, fun v => ?_⟩
    rw [mem_orb1_iff h v]
    constructor
    · rintro ⟨h0, hv⟩
      obtain ⟨n, hn⟩ := nf_mem_cand v h0
      rw [hn, mem_bit] at hv
      refine ⟨h0, ?_⟩
      rw [hn, ← hc15]
      fin_cases n <;> simp_all
    · rintro ⟨h0, h8 | h2 | h6⟩
      · exact ⟨h0, by rw [h8, mem_bit]; exact b8⟩
      · exact ⟨h0, by rw [h2, mem_bit]; exact b2⟩
      · exact ⟨h0, by rw [h6, ← hc15, mem_bit]; exact h15⟩

end CFSG.StandardType.FrameRoute.FS81.E7Row

end

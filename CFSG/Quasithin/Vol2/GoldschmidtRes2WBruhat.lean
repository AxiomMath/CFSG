module

public import CFSG.Quasithin.Vol2.Ch3E215MB

public section

namespace CFSG.Quasithin.Res2

open CFSG.Open CFSG.QuasithinUnique B6 Ch3E215M

variable {G : Type} [Group G] {X T M V : Subgroup G} {g : G}

theorem inf_conjSub_B_of_normalized [Finite G] (h : E2.Pair X T M V g)
    (hBN : ∀ m ∈ M, conjSub m (kerIn M X ⊓ V) = kerIn M X ⊓ V)
    (hBru : ∀ x ∈ X, x ∈ M ∨ ∃ m₁ ∈ M, ∃ m₂ ∈ M, x = m₁ * g * m₂) {u : G} (hu : u ∈ X)
    (huM : u ∉ M) : kerIn M X ⊓ V ⊓ conjSub u (kerIn M X ⊓ V) = V ⊓ conjSub g V := by
  obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := (hBru u hu).resolve_left huM
  have e1 := hBN m₁ hm₁
  rw [conjSub_mul, conjSub_mul, hBN m₂ hm₂]
  calc kerIn M X ⊓ V ⊓ conjSub m₁ (conjSub g (kerIn M X ⊓ V))
      = conjSub m₁ (kerIn M X ⊓ V) ⊓ conjSub m₁ (conjSub g (kerIn M X ⊓ V)) := by rw [e1]
    _ = conjSub m₁ (kerIn M X ⊓ V ⊓ conjSub g (kerIn M X ⊓ V)) :=
        ((conjSub m₁).map_inf _ _).symm
    _ = V ⊓ conjSub g V := by rw [h.B_inf_A, h.conjSub_inf_conj (h.le_X hm₁)]

theorem conjSub_inf_conjSub_B_of_normalized [Finite G] (h : E2.Pair X T M V g)
    (hBN : ∀ m ∈ M, conjSub m (kerIn M X ⊓ V) = kerIn M X ⊓ V)
    (hBru : ∀ x ∈ X, x ∈ M ∨ ∃ m₁ ∈ M, ∃ m₂ ∈ M, x = m₁ * g * m₂) {x y : G} (hx : x ∈ X)
    (hy : y ∈ X) (hxy : x⁻¹ * y ∉ M) :
    conjSub x (kerIn M X ⊓ V) ⊓ conjSub y (kerIn M X ⊓ V) = V ⊓ conjSub g V := by
  have e1 : conjSub y (kerIn M X ⊓ V) = conjSub x (conjSub (x⁻¹ * y) (kerIn M X ⊓ V)) := by
    rw [← conjSub_mul, mul_inv_cancel_left]
  rw [e1, ← (conjSub x).map_inf,
    inf_conjSub_B_of_normalized h hBN hBru (X.mul_mem (X.inv_mem hx) hy) hxy,
    h.conjSub_inf_conj hx]

theorem commutator_eq_bot_of_bruhat_of_normalized [Finite G] (h : E2.Pair X T M V g)
    (hBN : ∀ m ∈ M, conjSub m (kerIn M X ⊓ V) = kerIn M X ⊓ V)
    (hBru : ∀ x ∈ X, x ∈ M ∨ ∃ m₁ ∈ M, ∃ m₂ ∈ M, x = m₁ * g * m₂)
    (hidx : M.relIndex X = (V ⊓ conjSub g V).relIndex (kerIn M X ⊓ V) + 1) :
    ⁅kerIn M X ⊓ V, conjSub g (kerIn M X ⊓ V)⁆ = ⊥ := by
  classical
  have := Fintype.ofFinite G
  have hZB : V ⊓ conjSub g V ≤ kerIn M X ⊓ V := h.inf_conj_le_kerIn_inf
  have hPX := h.le_normalizer_P
  have hZX : ∀ x ∈ X, conjSub x (V ⊓ conjSub g V) = V ⊓ conjSub g V :=
    fun x hx => h.conjSub_inf_conj hx
  have hcov : ∀ x ∈ X, ∀ y ∈ X, x⁻¹ * y ∉ M →
      conjSub x (kerIn M X ⊓ V) ⊓ conjSub y (kerIn M X ⊓ V) = V ⊓ conjSub g V :=
    fun x hx y hy => conjSub_inf_conjSub_B_of_normalized h hBN hBru hx hy
  have hP2 := Ch3E213M.relIndex_P_eq h
  have hsqB : ∀ x p, p ∈ conjSub x (kerIn M X ⊓ V) → p * p = 1 :=
    fun x p hp => mul_self_of_mem_conjSub h hp
  set B := kerIn M X ⊓ V with hB
  set A := conjSub g B with hA
  set Z := V ⊓ conjSub g V with hZ
  set P := B ⊔ A with hP
  have hBP : B ≤ P := le_sup_left
  have hBZ : Nat.card B = Z.relIndex B * Nat.card Z := by
    have h1 := Subgroup.relIndex_mul_card Z B
    rw [inf_eq_left.2 hZB] at h1
    exact h1.symm
  have hPZ : Nat.card P = (Z.relIndex B) ^ 2 * Nat.card Z := by
    have h1 := Subgroup.relIndex_mul_card Z P
    rw [inf_eq_left.2 (hZB.trans hBP), hP2] at h1
    exact h1.symm
  have hb1 : 1 ≤ Z.relIndex B := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  set b := Z.relIndex B with hb
  set Q := ↥X ⧸ M.subgroupOf X with hQ
  have : Fintype Q := Fintype.ofFinite Q
  have hcardQ : Fintype.card Q = b + 1 := by
    rw [← Nat.card_eq_fintype_card, ← hidx]
    rfl
  let r : Q → G := fun q => ((Quotient.out q : ↥X) : G)
  have hrX : ∀ q, r q ∈ X := fun q => (Quotient.out q).2
  have hr : ∀ q q', q ≠ q' → (r q)⁻¹ * r q' ∉ M := by
    intro q q' hqq' hM
    apply hqq'
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    simpa [r] using hM
  let D : Q → Finset G := fun q => fs (conjSub (r q) B) \ fs Z
  have hZS : ∀ q, Z ≤ conjSub (r q) B := fun q =>
    calc Z = conjSub (r q) Z := (hZX _ (hrX q)).symm
      _ ≤ conjSub (r q) B := (conjSub (r q)).monotone hZB
  have hdisj : Set.PairwiseDisjoint (Finset.univ : Finset Q) D := by
    intro q _ q' _ hqq'
    rw [Function.onFun, Finset.disjoint_left]
    intro p hp hp'
    simp only [D, Finset.mem_sdiff, mem_fs] at hp hp'
    have h1 : p ∈ conjSub (r q) B ⊓ conjSub (r q') B := ⟨hp.1, hp'.1⟩
    rw [hcov _ (hrX q) _ (hrX q') (hr q q' hqq')] at h1
    exact hp.2 h1
  have hcardD : ∀ q, (D q).card = Nat.card B - Nat.card Z := fun q => by
    rw [Finset.card_sdiff_of_subset (fun p hp => mem_fs.2 (hZS q (mem_fs.1 hp))), card_fs,
      card_fs]
    congr 1
    exact Subgroup.card_map_of_injective (MulAut.conj (r q)).injective
  set U := fs Z ∪ Finset.univ.biUnion D with hU
  have hUP : U ⊆ fs P := by
    intro p hp
    rw [hU, Finset.mem_union, Finset.mem_biUnion] at hp
    rw [mem_fs]
    rcases hp with hp | ⟨q, -, hq⟩
    · exact hBP (hZB (mem_fs.1 hp))
    · have hqS : p ∈ conjSub (r q) B := mem_fs.1 (Finset.mem_sdiff.1 hq).1
      rw [mem_conjSub] at hqS
      have h1 := (Subgroup.mem_normalizer_iff.mp (hPX (hrX q)) _).mp (hBP hqS)
      simpa [mul_assoc] using h1
  have hcardU : U.card = Nat.card P := by
    have hd : Disjoint (fs Z) (Finset.univ.biUnion D) := by
      rw [Finset.disjoint_left]
      intro p hp hp'
      obtain ⟨q, -, hq⟩ := Finset.mem_biUnion.1 hp'
      exact (Finset.mem_sdiff.1 hq).2 hp
    rw [hU, Finset.card_union_of_disjoint hd, Finset.card_biUnion hdisj, card_fs]
    simp only [hcardD, Finset.sum_const, Finset.card_univ, hcardQ, smul_eq_mul, hBZ, hPZ]
    exact card_cover_arith hb1
  have hUeq : U = fs P := Finset.eq_of_subset_of_card_le hUP (by rw [hcardU, card_fs])
  refine commutator_eq_bot_of_mul_self fun p hp => ?_
  have hpU : p ∈ U := hUeq ▸ mem_fs.2 hp
  rw [hU, Finset.mem_union, Finset.mem_biUnion] at hpU
  rcases hpU with hp' | ⟨q, -, hq⟩
  · exact hsqB 1 p (by rw [conjSub_one]; exact hZB (mem_fs.1 hp'))
  · exact hsqB _ p (mem_fs.1 (Finset.mem_sdiff.1 hq).1)

end CFSG.Quasithin.Res2

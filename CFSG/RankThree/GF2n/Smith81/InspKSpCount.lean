module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCentralizerA2

public section

namespace CFSG.RankThree.GF2n.Smith81.Insp.KFact

open CFSG.SeitzReduction.SymplecticPilot Subgroup Matrix
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective elt)
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.Open (StatedSp)

private theorem cardWR_card_offPQ {n : ℕ} {p q : Fin n} (hpq : p ≠ q) :
    Nat.card {t : Fin n ⊕ Fin n // OffPQ p q t} = 2 * n - 4 := by
  have hS : ({Sum.inl p, Sum.inr p, Sum.inl q, Sum.inr q} :
      Finset (Fin n ⊕ Fin n)).card = 4 := by
    simp [Finset.card_insert_of_notMem, hpq, Ne.symm hpq]
  have hmem : ∀ t : Fin n ⊕ Fin n,
      t ∈ (Finset.univ \ {Sum.inl p, Sum.inr p, Sum.inl q, Sum.inr q} :
        Finset (Fin n ⊕ Fin n)) ↔ OffPQ p q t := by
    intro t
    simp [OffPQ, mem_coords, not_or, and_assoc]
  rw [Nat.subtype_card _ hmem, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, Fintype.card_sum, Fintype.card_fin, hS]
  omega

private theorem cardWR_mat_mul {K : Type} [Field K] {n : ℕ} {p q : Fin n} (hpq : p ≠ q)
    {z : StatedSp n K} (hz : z ∈ wRadical K p q) (g : StatedSp n K)
    (x t : Fin n ⊕ Fin n) (ht : OffPQ p q t) :
    mat n K (g * z) x t = mat n K g x t + mat n K g x (Sum.inl p) * mat n K z (Sum.inl p) t +
      mat n K g x (Sum.inl q) * mat n K z (Sum.inl q) t := by
  have hz3 := (mem_wRadical.1 hz).2.2
  have htp : t ≠ Sum.inl p := fun h => ht.1 (h ▸ inl_mem_coords p)
  have htq : t ≠ Sum.inl q := fun h => ht.2 (h ▸ inl_mem_coords q)
  have hpt : ∀ u : Fin n ⊕ Fin n, mat n K g x u * mat n K z u t =
      (if u = t then mat n K g x t else 0) +
      (if u = Sum.inl p then mat n K g x (Sum.inl p) * mat n K z (Sum.inl p) t else 0) +
      (if u = Sum.inl q then mat n K g x (Sum.inl q) * mat n K z (Sum.inl q) t else 0) := by
    intro u
    by_cases hut : u = t
    · have hup : u ≠ Sum.inl p := fun h => htp (hut.symm.trans h)
      have huq : u ≠ Sum.inl q := fun h => htq (hut.symm.trans h)
      rw [if_pos hut, if_neg hup, if_neg huq, hz3 t ht u hup huq, hut, Matrix.one_apply_eq]
      simp
    · by_cases hup : u = Sum.inl p
      · have huq : u ≠ Sum.inl q := fun h => hpq (Sum.inl_injective (hup.symm.trans h))
        rw [if_neg hut, if_pos hup, if_neg huq, hup]
        simp
      · by_cases huq : u = Sum.inl q
        · rw [if_neg hut, if_neg hup, if_pos huq, huq]
          simp
        · rw [if_neg hut, if_neg hup, if_neg huq, hz3 t ht u hup huq, Matrix.one_apply_ne hut]
          simp
  rw [map_mul, Matrix.mul_apply, Finset.sum_congr rfl fun u _ => hpt u,
    Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp

private theorem cardWR_mat_mul_inl_p {K : Type} [Field K] {n : ℕ} {p q : Fin n} (hpq : p ≠ q)
    {g z : StatedSp n K} (hg : g ∈ wRadical K p q) (hz : z ∈ wRadical K p q)
    (t : Fin n ⊕ Fin n) (ht : OffPQ p q t) :
    mat n K (g * z) (Sum.inl p) t = mat n K g (Sum.inl p) t + mat n K z (Sum.inl p) t := by
  have hg' := mem_wRadical.1 hg
  rw [cardWR_mat_mul hpq hz g (Sum.inl p) t ht, hg'.1 (Sum.inl p), hg'.2.1 (Sum.inl p),
    Matrix.one_apply_eq,
    Matrix.one_apply_ne (show Sum.inl p ≠ Sum.inl q from fun h => hpq (Sum.inl_injective h))]
  simp

private theorem cardWR_mat_mul_inl_q {K : Type} [Field K] {n : ℕ} {p q : Fin n} (hpq : p ≠ q)
    {g z : StatedSp n K} (hg : g ∈ wRadical K p q) (hz : z ∈ wRadical K p q)
    (t : Fin n ⊕ Fin n) (ht : OffPQ p q t) :
    mat n K (g * z) (Sum.inl q) t = mat n K g (Sum.inl q) t + mat n K z (Sum.inl q) t := by
  have hg' := mem_wRadical.1 hg
  rw [cardWR_mat_mul hpq hz g (Sum.inl q) t ht, hg'.1 (Sum.inl q), hg'.2.1 (Sum.inl q),
    Matrix.one_apply_eq,
    Matrix.one_apply_ne (show Sum.inl q ≠ Sum.inl p from fun h => hpq (Sum.inl_injective h).symm)]
  simp

private theorem cardWR_map_mul {K : Type} [Field K] {n : ℕ} {p q : Fin n} (hpq : p ≠ q)
    (g z : wRadical K p q) :
    Multiplicative.ofAdd (fun bt : Bool × {t : Fin n ⊕ Fin n // OffPQ p q t} =>
        mat n K (g * z).1 (if bt.1 then Sum.inl p else Sum.inl q) bt.2.1) =
      Multiplicative.ofAdd (fun bt : Bool × {t : Fin n ⊕ Fin n // OffPQ p q t} =>
        mat n K g.1 (if bt.1 then Sum.inl p else Sum.inl q) bt.2.1) *
      Multiplicative.ofAdd (fun bt : Bool × {t : Fin n ⊕ Fin n // OffPQ p q t} =>
        mat n K z.1 (if bt.1 then Sum.inl p else Sum.inl q) bt.2.1) := by
  rw [← ofAdd_add, Subgroup.coe_mul]
  congr 1
  funext bt
  obtain ⟨b, t⟩ := bt
  cases b
  · simpa using cardWR_mat_mul_inl_q hpq g.2 z.2 t.1 t.2
  · simpa using cardWR_mat_mul_inl_p hpq g.2 z.2 t.1 t.2

private noncomputable def cardWRHom (K : Type) [Field K] {n : ℕ} {p q : Fin n} (hpq : p ≠ q) :
    wRadical K p q →* Multiplicative (Bool × {t : Fin n ⊕ Fin n // OffPQ p q t} → K) :=
  MonoidHom.mk'
    (fun g => Multiplicative.ofAdd fun bt : Bool × {t : Fin n ⊕ Fin n // OffPQ p q t} =>
      mat n K g.1 (if bt.1 then Sum.inl p else Sum.inl q) bt.2.1)
    (cardWR_map_mul hpq)

private theorem cardWRHom_apply {K : Type} [Field K] {n : ℕ} {p q : Fin n} (hpq : p ≠ q)
    (g : wRadical K p q) :
    cardWRHom K hpq g = Multiplicative.ofAdd fun bt : Bool × {t : Fin n ⊕ Fin n // OffPQ p q t} =>
      mat n K g.1 (if bt.1 then Sum.inl p else Sum.inl q) bt.2.1 := by
  simp [cardWRHom]

private theorem cardWR_ker_card_le {K : Type} [Field K] [Finite K] {n : ℕ} {p q : Fin n}
    (hpq : p ≠ q) : Nat.card (cardWRHom K hpq).ker ≤ Nat.card K ^ 3 := by
  have hv : ∀ z : (cardWRHom K hpq).ker, ∀ t : Fin n ⊕ Fin n, OffPQ p q t →
      mat n K z.1.1 (Sum.inl p) t = 0 ∧ mat n K z.1.1 (Sum.inl q) t = 0 := by
    intro z t ht
    have h1 := MonoidHom.mem_ker.1 z.2
    rw [cardWRHom_apply] at h1
    have h2 := ofAdd_eq_one.1 h1
    exact ⟨by simpa using congrFun h2 (true, ⟨t, ht⟩),
      by simpa using congrFun h2 (false, ⟨t, ht⟩)⟩
  have hinj : Function.Injective (fun z : (cardWRHom K hpq).ker =>
      (mat n K z.1.1 (Sum.inl p) (Sum.inr p), mat n K z.1.1 (Sum.inl q) (Sum.inr q),
        mat n K z.1.1 (Sum.inl p) (Sum.inr q))) := by
    rintro z w h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    apply Subtype.ext
    apply Subtype.ext
    rw [eq_siegel_of_mem_wRadical hpq z.1.2 (hv z), eq_siegel_of_mem_wRadical hpq w.1.2 (hv w),
      h1, h2, h3]
  calc Nat.card (cardWRHom K hpq).ker ≤ Nat.card (K × K × K) :=
        Nat.card_le_card_of_injective _ hinj
    _ = Nat.card K ^ 3 := by rw [Nat.card_prod, Nat.card_prod]; ring

private theorem cardWR_range_card_le {K : Type} [Field K] [Finite K] {n : ℕ} {p q : Fin n}
    (hpq : p ≠ q) :
    Nat.card (cardWRHom K hpq).range ≤
      Nat.card K ^ (2 * Nat.card {t : Fin n ⊕ Fin n // OffPQ p q t}) := by
  have h1 : Nat.card (cardWRHom K hpq).range ≤
      Nat.card (Bool × {t : Fin n ⊕ Fin n // OffPQ p q t} → K) :=
    Nat.card_le_card_of_injective
      (fun z => Multiplicative.toAdd
        (z : Multiplicative (Bool × {t : Fin n ⊕ Fin n // OffPQ p q t} → K)))
      (fun z w h => Subtype.ext (Multiplicative.toAdd.injective h))
  have hBool : Nat.card Bool = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_bool]
  rw [Nat.card_fun, Nat.card_prod, hBool] at h1
  exact h1

theorem card_wRadical_le {K : Type} [Field K] [Finite K] {n : ℕ} {p q : Fin n} (hpq : p ≠ q) :
    Nat.card (wRadical K p q) ≤ Nat.card K ^ (4 * n - 5) := by
  have hn : 2 ≤ n := by
    have h1 : (p : ℕ) < n := p.isLt
    have h2 : (q : ℕ) < n := q.isLt
    have h3 : (p : ℕ) ≠ (q : ℕ) := fun h => hpq (Fin.ext h)
    omega
  have hT := cardWR_card_offPQ hpq
  rw [← Subgroup.card_ker_mul_card_range (cardWRHom K hpq)]
  have hK : 0 < Nat.card K := Nat.card_pos
  calc Nat.card (cardWRHom K hpq).ker * Nat.card (cardWRHom K hpq).range
      ≤ Nat.card K ^ 3 * Nat.card K ^ (2 * Nat.card {t : Fin n ⊕ Fin n // OffPQ p q t}) :=
        Nat.mul_le_mul (cardWR_ker_card_le hpq) (cardWR_range_card_le hpq)
    _ = Nat.card K ^ (3 + 2 * Nat.card {t : Fin n ⊕ Fin n // OffPQ p q t}) := by
        rw [pow_add]
    _ ≤ Nat.card K ^ (4 * n - 5) := Nat.pow_le_pow_right hK (by rw [hT]; omega)

end CFSG.RankThree.GF2n.Smith81.Insp.KFact

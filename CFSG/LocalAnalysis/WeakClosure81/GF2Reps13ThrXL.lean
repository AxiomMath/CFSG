module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXLB

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]
variable {A X Q : Subgroup (MulAut W)} {t : MulAut W}

theorem s13_three_case_three (h : HAb A X Q t 3)
    (hH0 : ∀ y ∈ X, y ≠ 1 → (s13Supp X (Subgroup.zpowers y)).ncard ≠ 1)
    (hQ9 : Nat.card ↥Q = 9) (he : (s13Supp X Q).ncard = 3) :
    ∃ L : Subgroup (MulAut W), L ≤ X ∧ Conc4_133 A t L ∧
      L = s13XSupp X (s13Supp X L) := by
  have hp3 : Nat.Prime 3 := by norm_num
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  have hQeq := w16g_three_Q_eq_XSupp h hH0 hQ9 he
  have hrk := w16g_three_rk_eq_six h he
  have hinv := w16g_three_inv_ne_bot h
  have hblocks := w16g_three_blocks h hH0 hQ9 he
  have hcomm : ∀ a b : ↥Q, a * b = b * a := fun a b =>
    Subtype.ext (by
      have h' := (h.hXe.1.is_comm).comm (⟨(a : MulAut W), h.hQX a.2⟩ : ↥X)
        (⟨(b : MulAut W), h.hQX b.2⟩ : ↥X)
      simpa using congrArg Subtype.val h')
  have hQrank : IsElemAbelianOfRank 3 2 ↥Q :=
    w16g_isElemAbelianOfRank_of_card (p := 3) (n := 2) hcomm
      (fun a => Subtype.ext (h.hXe.2 (a : MulAut W) (h.hQX a.2))) hQ9
  have hind : sSupIndep (conjSubs A (commSub ⊤ Q)) :=
    sSupIndep_conjSubs_of_s13Supp h.hW hp3 (by norm_num) h.hXe h.hXA h.hQX hblocks
  refine ⟨Q, h.hQX, ?_, hQeq⟩
  exact ⟨3, hp3, h.hQX.trans h.hXO, hinv, hind,
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hQrank, hrk, h.hQinv⟩)))))⟩

theorem s13_three_orthogonal (h : HAb A X Q t 3)
    (hH0 : ∀ y ∈ X, y ≠ 1 → (s13Supp X (Subgroup.zpowers y)).ncard ≠ 1)
    (hQ3 : Nat.card ↥Q = 3) (he : (s13Supp X Q).ncard = 3)
    {lam : s13IsoComps X → Additive ↥X →+ ZMod 3} (hl : IsCoord X 3 lam) :
    ∀ a ∈ A, ∀ q : ↥X, (q : MulAut W) ∈ Q.map (MulAut.conj a).toMonoidHom → ∀ x : ↥X,
      ∑ᶠ U : ↥(s13IsoComps X), lam U (Additive.ofMul q) * lam U (Additive.ofMul x) = 0 := by
  intro a ha q hq x
  have h' : HAb A X (Q.map (MulAut.conj a).toMonoidHom) (a * t * a⁻¹) 3 := h.conj ha
  have hQ3' : Nat.card ↥(Q.map (MulAut.conj a).toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj a).injective, hQ3]
  have he' : (s13Supp X (Q.map (MulAut.conj a).toMonoidHom)).ncard = 3 := by
    have h1 := s13Supp_conj (X := X) (L := Q) (g := a)
      (h.hXA a ha) (by simpa using h.hXA a⁻¹ (A.inv_mem ha))
    rw [h1, Set.ncard_image_of_injective _ (Subgroup.map_injective a.injective), he]
  exact w16g_three_orth_core h' hH0 hQ3' he' hl q hq x

theorem s13_three_case_two_supports (h : HAb A X Q t 3)
    (hH0 : ∀ y ∈ X, y ≠ 1 → (s13Supp X (Subgroup.zpowers y)).ncard ≠ 1)
    (hQ3 : Nat.card ↥Q = 3) (he : (s13Supp X Q).ncard = 3) :
    (∀ a ∈ A, (s13Supp X (Q.map (MulAut.conj a).toMonoidHom) ∩ s13Supp X Q).ncard ≠ 1) ∧
      ((∀ a ∈ A, (s13Supp X (Q.map (MulAut.conj a).toMonoidHom) ∩ s13Supp X Q).ncard ≠ 2) →
        ∀ a ∈ A, s13Supp X (Q.map (MulAut.conj a).toMonoidHom) = s13Supp X Q ∨
          Disjoint (s13Supp X (Q.map (MulAut.conj a).toMonoidHom)) (s13Supp X Q)) := by
  classical
  have hp3 : Nat.Prime 3 := by norm_num
  have hp32 : 3 ≠ 2 := by norm_num
  haveI : Finite (Subgroup W) :=
    Finite.of_injective (fun S : Subgroup W => (S : Set W)) SetLike.coe_injective
  haveI : Fintype ↥(s13IsoComps X) := Fintype.ofFinite _
  obtain ⟨lam, hl⟩ := exists_coord h.hW hp3 hp32 h.hXe
  have horth := s13_three_orthogonal h hH0 hQ3 he hl
  have hle3 : ∀ a ∈ A, (s13Supp X (Q.map (MulAut.conj a).toMonoidHom)).ncard ≤ 3 := by
    intro a ha
    rcases s13_three_shape (h.conj ha) hH0 with ⟨h2, -⟩ | ⟨h3, -⟩ | ⟨h3, -⟩ <;> omega
  have hno1 : ∀ a ∈ A,
      (s13Supp X (Q.map (MulAut.conj a).toMonoidHom) ∩ s13Supp X Q).ncard ≠ 1 := by
    intro a ha h1
    obtain ⟨U, hUeq⟩ := Set.ncard_eq_one.mp h1
    have hUinter : U ∈ s13Supp X (Q.map (MulAut.conj a).toMonoidHom) ∩ s13Supp X Q := by
      rw [hUeq]; exact Set.mem_singleton U
    have hUmem : U ∈ s13IsoComps X := (hUinter.1).1
    let U' : s13IsoComps X := ⟨U, hUmem⟩
    have hUe : U ∈ s13Supp X Q := hUinter.2
    have hUe' : U ∈ s13Supp X (Q.map (MulAut.conj a).toMonoidHom) := hUinter.1
    have hQX' : Q.map (MulAut.conj a).toMonoidHom ≤ X := by
      intro q hq
      obtain ⟨q₀, hq₀, rfl⟩ := Subgroup.mem_map.mp hq
      simpa [MulAut.conj_apply] using h.hXA a ha q₀ (h.hQX hq₀)
    obtain ⟨x, hxL, hx0⟩ := (mem_s13Supp_iff_coord hl hQX' U').mp hUe'
    obtain ⟨y, hyL, hy0⟩ := (mem_s13Supp_iff_coord hl h.hQX U').mp hUe
    have hsum : (∑ᶠ V : ↥(s13IsoComps X),
        lam V (Additive.ofMul x) * lam V (Additive.ofMul y)) =
        lam U' (Additive.ofMul x) * lam U' (Additive.ofMul y) := by
      rw [finsum_eq_sum_of_fintype]
      refine Finset.sum_eq_single U' ?_ ?_
      · intro V _ hVne
        have hzero : lam V (Additive.ofMul x) = 0 ∨ lam V (Additive.ofMul y) = 0 := by
          by_contra hc
          push Not at hc
          have hVE' : (V : Subgroup W) ∈ s13Supp X (Q.map (MulAut.conj a).toMonoidHom) :=
            (mem_s13Supp_iff_coord hl hQX' V).mpr ⟨x, hxL, hc.1⟩
          have hVe : (V : Subgroup W) ∈ s13Supp X Q :=
            (mem_s13Supp_iff_coord hl h.hQX V).mpr ⟨y, hyL, hc.2⟩
          have hVmem : (V : Subgroup W) ∈ s13Supp X (Q.map (MulAut.conj a).toMonoidHom) ∩
              s13Supp X Q := ⟨hVE', hVe⟩
          rw [hUeq] at hVmem
          exact hVne (Subtype.ext (Set.mem_singleton_iff.mp hVmem))
        rcases hzero with h0 | h0 <;> simp [h0]
      · intro hnot
        simp at hnot
    have hne0 : lam U' (Additive.ofMul x) * lam U' (Additive.ofMul y) ≠ 0 :=
      mul_ne_zero hx0 hy0
    have hz := horth a ha x hxL y
    rw [hsum] at hz
    exact hne0 hz
  have hno2 : (∀ a ∈ A,
      (s13Supp X (Q.map (MulAut.conj a).toMonoidHom) ∩ s13Supp X Q).ncard ≠ 2) →
      ∀ a ∈ A, s13Supp X (Q.map (MulAut.conj a).toMonoidHom) = s13Supp X Q ∨
        Disjoint (s13Supp X (Q.map (MulAut.conj a).toMonoidHom)) (s13Supp X Q) := by
    intro hno2 a ha
    set E' : Set (Subgroup W) := s13Supp X (Q.map (MulAut.conj a).toMonoidHom) with hE'def
    have hint3 : (E' ∩ s13Supp X Q).ncard ≤ 3 := by
      calc (E' ∩ s13Supp X Q).ncard ≤ E'.ncard := Set.ncard_le_ncard Set.inter_subset_left
        _ ≤ 3 := hle3 a ha
    have hcases : (E' ∩ s13Supp X Q).ncard = 0 ∨ (E' ∩ s13Supp X Q).ncard = 3 := by
      rcases Nat.eq_zero_or_pos (E' ∩ s13Supp X Q).ncard with h0 | hpos
      · exact Or.inl h0
      · exact Or.inr (by
          have h1 := hno1 a ha
          have h2 := hno2 a ha
          rw [← hE'def] at h1 h2
          omega)
    rcases hcases with h0 | h3
    · right
      exact Set.disjoint_iff_inter_eq_empty.mpr
        ((Set.ncard_eq_zero (s := E' ∩ s13Supp X Q)).mp h0)
    · left
      have hint_eq_e : E' ∩ s13Supp X Q = s13Supp X Q :=
        Set.eq_of_subset_of_ncard_le Set.inter_subset_right (by rw [he, h3])
      have hesub : s13Supp X Q ⊆ E' := by
        rw [← hint_eq_e]
        exact Set.inter_subset_left
      exact (Set.eq_of_subset_of_ncard_le hesub (by rw [he]; exact hle3 a ha)).symm
  exact ⟨hno1, hno2⟩

theorem s13_three_case_two_blocks (h : HAb A X Q t 3)
    (hH0 : ∀ y ∈ X, y ≠ 1 → (s13Supp X (Subgroup.zpowers y)).ncard ≠ 1)
    (hQ3 : Nat.card ↥Q = 3) (he : (s13Supp X Q).ncard = 3)
    (hblk : ∀ a ∈ A, s13Supp X (Q.map (MulAut.conj a).toMonoidHom) = s13Supp X Q ∨
      Disjoint (s13Supp X (Q.map (MulAut.conj a).toMonoidHom)) (s13Supp X Q)) :
    ∃ L : Subgroup (MulAut W), L ≤ X ∧ Conc4_133 A t L ∧
      L = s13XSupp X (s13Supp X L) := by
  have hp3 : Nat.Prime 3 := by norm_num
  have hQeq := w16g_three_plane_eq h hH0 hQ3 he hblk
  have hrk := w16g_three_rk_eq_six h he
  have hinv := w16g_three_inv_ne_bot h
  have hcyc : IsCyclicOrd ↥Q 3 := ⟨isCyclic_of_prime_card hQ3, hQ3⟩
  have hind : sSupIndep (conjSubs A (commSub ⊤ Q)) :=
    sSupIndep_conjSubs_of_s13Supp h.hW hp3 (by norm_num) h.hXe h.hXA h.hQX hblk
  refine ⟨Q, h.hQX, ?_, hQeq⟩
  exact ⟨3, hp3, h.hQX.trans h.hXO, hinv, hind,
    Or.inl ⟨hcyc, Or.inr (Or.inr hrk)⟩⟩

end CFSG.LocalAnalysis.WeakClosure81

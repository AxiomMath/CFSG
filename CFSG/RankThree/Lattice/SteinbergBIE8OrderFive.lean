module

public import CFSG.RankThree.Lattice.SteinbergBIE8OrderFiveTransportA
public import CFSG.RankThree.Lattice.SteinbergBIE8OrderFiveTransportB

public noncomputable section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 Polynomial Matrix

theorem peval_phi5 {K : Type*} [CommRing K] (r : K) :
    peval phi5 r = r ^ 4 + r ^ 3 + r ^ 2 + r + 1 := by
  simp only [phi5, peval_cons, peval_nil, Int.cast_one]
  ring

theorem e8F5_transport {i : ℕ} (hi : i < 12) :
    ∃ a : WeylGroup Tag.E8, (a • ·) '' e8F5ClassSet i = parabolicRoots Tag.E8 e8F5J ∧
      (∃ π : Equiv.Perm (Fin 5), orderOf π = 5 ∧ ∀ k l,
        (a * e8F5U * a⁻¹) • chainRoot e8F5Chain k l = chainRoot e8F5Chain (π k) (π l)) ∧
      IsNegativeTransition (fun x => (a * e8F5C ^ 21 * a⁻¹) • x) e8F5Chain e8F5Chain := by
  interval_cases i
  exacts [e8F5_transport_0, e8F5_transport_1, e8F5_transport_2, e8F5_transport_3,
    e8F5_transport_4, e8F5_transport_5, e8F5_transport_6, e8F5_transport_7, e8F5_transport_8,
    e8F5_transport_9, e8F5_transport_10, e8F5_transport_11]

theorem classSet_nonempty {i : ℕ} (hi : i < 12) : (e8F5ClassSet i).Nonempty :=
  Set.nonempty_of_ncard_ne_zero (by rw [ncard_classSet hi]; norm_num)

theorem E8_order_five_twelve_cyclotomic_lines_and_full_A4_root_kernels :
    e8F5U ^ 5 = 1 ∧ weylMatrix (e8F5C ^ 15) = -1 ∧
    (weylMatrix e8F5U).charpoly = (X ^ 4 + X ^ 3 + X ^ 2 + X + 1) ^ 2 ∧ e8F5B.det = 1 ∧
    weylMatrix (e8F5C ^ 21) = -weylMatrix e8F5U ∧
    (Matrix.of fun i j : Fin 4 => Tag.E8.cartan (e8F5Chain i) (e8F5Chain j)) =
      !![2, -1, 0, 0; -1, 2, -1, 0; 0, -1, 2, -1; 0, 0, -1, 2] ∧
    ∀ (p : ℕ) [Fact p.Prime], 5 < p → ∀ r : ZMod p, r ^ 4 + r ^ 3 + r ^ 2 + r + 1 = 0 →
      (∀ a b : ZMod p, (dualMatrix (ZMod p) e8F5U).mulVec (e8F5Z r a b) = r • e8F5Z r a b) ∧
      (∀ z : Fin Tag.E8.rank → ZMod p, z ≠ 0 → (dualMatrix (ZMod p) e8F5U).mulVec z = r • z →
        ∃! ab : ZMod p × ZMod p, ab ≠ 0 ∧ z = e8F5Z r ab.1 ab.2) ∧
      (∀ α, IsRoot Tag.E8 α → ∃ fg : ZMod p × ZMod p, fg ≠ 0 ∧
        {ab : ZMod p × ZMod p | charVal (e8F5Z r ab.1 ab.2) α = 0} =
          {ab | fg.1 * ab.1 + fg.2 * ab.2 = 0}) ∧
      {L : Set (ZMod p × ZMod p) | ∃ α, IsRoot Tag.E8 α ∧
        L = {ab | charVal (e8F5Z r ab.1 ab.2) α = 0}}.ncard = 12 ∧
      {K : Set (Fin Tag.E8.rank → ℤ) | ∃ ab : ZMod p × ZMod p, ab ≠ 0 ∧
        K = e8RootKernel (e8F5Z r ab.1 ab.2) ∧ K.Nonempty}.ncard = 12 ∧
      (∀ α, IsRoot Tag.E8 α → ∃! K : Set (Fin Tag.E8.rank → ℤ),
        (∃ ab : ZMod p × ZMod p, ab ≠ 0 ∧ K = e8RootKernel (e8F5Z r ab.1 ab.2) ∧ K.Nonempty) ∧
          α ∈ K) ∧
      ∀ ab : ZMod p × ZMod p, ab ≠ 0 →
        e8RootKernel (e8F5Z r ab.1 ab.2) = ∅ ∨
        ((e8RootKernel (e8F5Z r ab.1 ab.2)).ncard = 20 ∧
          ∃ a : WeylGroup Tag.E8,
            (a • ·) '' e8RootKernel (e8F5Z r ab.1 ab.2) = parabolicRoots Tag.E8 e8F5J ∧
            (∃ π : Equiv.Perm (Fin 5), orderOf π = 5 ∧ ∀ k l,
              (a * e8F5U * a⁻¹) • chainRoot e8F5Chain k l = chainRoot e8F5Chain (π k) (π l)) ∧
            IsNegativeTransition (fun x => (a * e8F5C ^ 21 * a⁻¹) • x) e8F5Chain e8F5Chain) := by
  refine ⟨e8F5U_pow_five, weylMatrix_e8F5C_15, e8F5_charpoly, e8F5B_det, weylMatrix_e8F5C_21,
    by decide +kernel, fun p _ hp5 r hr => ?_⟩
  have hr' : peval phi5 r = 0 := by rw [peval_phi5, hr]
  have hzero : ∀ {i : ℕ}, i < 12 → ∀ {α}, α ∈ e8F5ClassSet i →
      {ab : ZMod p × ZMod p | charVal (e8F5Z r ab.1 ab.2) α = 0} = e8F5Line r i := by
    intro i hi α hα
    ext ab
    obtain ⟨μ, hμ, h⟩ := charVal_classSet hp5 hr' ab.1 ab.2 hi hα
    simp only [Set.mem_ofPred_eq, e8F5Line, h, mul_eq_zero, hμ, false_or]
  have hline_inj : ∀ {i j : ℕ}, i < 12 → j < 12 → e8F5Line r i = e8F5Line r j → i = j :=
    fun hi hj h => e8F5_line_unique hp5 hr' hi hj (e8F5Pt_ne_zero hp5 hr' hi) (e8F5Pt_mem r _)
      (h ▸ e8F5Pt_mem r _)
  have hker : ∀ ab : ZMod p × ZMod p, ab ≠ 0 →
      e8RootKernel (e8F5Z r ab.1 ab.2) = ∅ ∨
        ∃ i < 12, ab ∈ e8F5Line r i ∧ e8RootKernel (e8F5Z r ab.1 ab.2) = e8F5ClassSet i := by
    intro ab hab
    by_cases h : ∃ i < 12, ab ∈ e8F5Line r i
    · obtain ⟨i, hi, hl⟩ := h
      exact Or.inr ⟨i, hi, hl, e8RootKernel_eq_classSet hp5 hr' hab hi hl⟩
    · push Not at h
      exact Or.inl (e8RootKernel_eq_empty hp5 hr' h)
  have hfam : {K : Set (Fin Tag.E8.rank → ℤ) | ∃ ab : ZMod p × ZMod p, ab ≠ 0 ∧
      K = e8RootKernel (e8F5Z r ab.1 ab.2) ∧ K.Nonempty} =
      Set.range fun i : Fin 12 => e8F5ClassSet i := by
    ext K
    simp only [Set.mem_ofPred_eq, Set.mem_range]
    constructor
    · rintro ⟨ab, hab, rfl, hne⟩
      rcases hker ab hab with h | ⟨i, hi, -, h⟩
      · rw [h] at hne
        exact absurd hne Set.not_nonempty_empty
      · exact ⟨⟨i, hi⟩, h.symm⟩
    · rintro ⟨i, rfl⟩
      refine ⟨e8F5Pt r i, e8F5Pt_ne_zero hp5 hr' i.2,
        (e8RootKernel_eq_classSet hp5 hr' (e8F5Pt_ne_zero hp5 hr' i.2) i.2
          (e8F5Pt_mem r i)).symm, classSet_nonempty i.2⟩
  refine ⟨e8F5_eigen_of hr, fun z hz0 hz => ?_, fun α hα => ?_, ?_, ?_, fun α hα => ?_,
    fun ab hab => ?_⟩
  ·
    have h := e8F5_eigen_eq hz
    refine ⟨(charVal z (e8F5E 0), charVal z (e8F5E 1)), ⟨fun h0 => hz0 ?_, h⟩, ?_⟩
    · have h1 := congrArg Prod.fst h0
      have h2 := congrArg Prod.snd h0
      simp only [Prod.fst_zero, Prod.snd_zero] at h1 h2
      rw [h, h1, h2, e8F5Z_zero]
    · rintro ⟨a', b'⟩ ⟨-, h'⟩
      obtain ⟨ha, hb⟩ := e8F5Z_coords r a' b'
      rw [← h'] at ha hb
      rw [ha, hb]
  ·
    obtain ⟨i, hi, hαi⟩ := exists_classSet hα
    refine ⟨(e8F5F r i, e8F5G r i), fun h0 => ?_, hzero hi hαi⟩
    have h1 := congrArg Prod.fst h0
    have h2 := congrArg Prod.snd h0
    simp only [Prod.fst_zero, Prod.snd_zero] at h1 h2
    rcases e8F5_rep_ne_zero hp5 hr' hi with h | h
    · exact h h1
    · exact h h2
  ·
    have e : {L : Set (ZMod p × ZMod p) | ∃ α, IsRoot Tag.E8 α ∧
        L = {ab | charVal (e8F5Z r ab.1 ab.2) α = 0}} =
        Set.range fun i : Fin 12 => e8F5Line r i := by
      ext L
      simp only [Set.mem_ofPred_eq, Set.mem_range]
      constructor
      · rintro ⟨α, hα, rfl⟩
        obtain ⟨i, hi, hαi⟩ := exists_classSet hα
        exact ⟨⟨i, hi⟩, (hzero hi hαi).symm⟩
      · rintro ⟨i, rfl⟩
        obtain ⟨α, hα⟩ := classSet_nonempty i.2
        exact ⟨α, isRoot_of_mem_classSet i.2 hα, (hzero i.2 hα).symm⟩
    rw [e, Set.ncard_range_of_injective, Nat.card_eq_fintype_card, Fintype.card_fin]
    intro i j h
    exact Fin.ext (hline_inj i.2 j.2 h)
  ·
    rw [hfam, Set.ncard_range_of_injective, Nat.card_eq_fintype_card, Fintype.card_fin]
    intro i j h
    obtain ⟨α, hα⟩ := classSet_nonempty i.2
    have h' : e8F5ClassSet i = e8F5ClassSet j := h
    have hα' : α ∈ e8F5ClassSet j := h' ▸ hα
    exact Fin.ext (classSet_unique i.2 j.2 hα hα')
  ·
    obtain ⟨i, hi, hαi⟩ := exists_classSet hα
    have hmem : ∀ K, (∃ ab : ZMod p × ZMod p, ab ≠ 0 ∧ K = e8RootKernel (e8F5Z r ab.1 ab.2) ∧
        K.Nonempty) ↔ K ∈ Set.range fun i : Fin 12 => e8F5ClassSet i := fun K => by
      rw [← hfam]
      rfl
    refine ⟨e8F5ClassSet i, ⟨(hmem _).2 ⟨⟨i, hi⟩, rfl⟩, hαi⟩, ?_⟩
    rintro K ⟨hK, hαK⟩
    obtain ⟨j, rfl⟩ := (hmem K).1 hK
    show e8F5ClassSet j = e8F5ClassSet i
    rw [classSet_unique j.2 hi hαK hαi]
  ·
    rcases hker ab hab with h | ⟨i, hi, -, h⟩
    · exact Or.inl h
    · right
      rw [h]
      exact ⟨ncard_classSet hi, e8F5_transport hi⟩

end CFSG.RankThree.Lattice

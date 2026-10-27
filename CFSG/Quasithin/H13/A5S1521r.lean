module

public import CFSG.Quasithin.H13.A5Facts1321
public import CFSG.Quasithin.Background.HMathieuStatements
public import CFSG.Quasithin.Background.D2Involutions
public import CFSG.Quasithin.Background.D2Misc
public import CFSG.Quasithin.Background.A1aFStar

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank

structure Facts1321 : Prop where
  b45 : AsB45
  h144 : H.Mathieu.StmtH14_4
  lie : FactLieRows1321
  m12 : FactM12Row1321
  m22 : FactM22HatRow1321
  j2 : FactJ2Row1321
  a5 : FactA5Rows1321
  sym : FactSymRows1321
  a7four : FactA7FourRow1321
  a6three : FactTripleA6Row1321
  lnat : FactLNatRow1321
  l5ten : FactL5TenRow1321

section Rows

variable {V : Type} [CommGroup V] [Finite V]

@[expose] def Outcome1321 (G L : Subgroup (MulAut V)) : Prop :=
  (∃ π : ↥(alternatingGroup (Fin 7)) →* ↥L, Function.Surjective π) ∨
  (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ∧
    ∃ π : ↥(StatedSL 3 F) →* ↥L, Function.Surjective π) ∨
  ∃ A : Subgroup (MulAut V), Rows1321Remaining G L A

theorem card_field_ne_one (K : Type) [Field K] [Finite K] : Nat.card K ≠ 1 := by
  intro h
  have := Finite.one_lt_card (α := K)
  omega

omit [Finite V] in
theorem not_binaryNaturalSp4_zero (H : Subgroup (MulAut V)) : ¬ BinaryNaturalSp4 H ⊤ ⊥ 0 := by
  rintro ⟨K, _, _, hK, -⟩
  exact card_field_ne_one K (by simpa using hK)

omit [Finite V] in
theorem not_g2Natural_zero (H : Subgroup (MulAut V)) : ¬ G2Natural H ⊤ ⊥ 0 := by
  rintro ⟨K, _, _, hK, -⟩
  exact card_field_ne_one K (by simpa using hK)

theorem B4Hyp.isOver {G L : Subgroup (MulAut V)} (h : B4Hyp G L) :
    L ≤ G ∧ G ≤ Subgroup.normalizer (L : Set (MulAut V)) := by
  obtain ⟨-, hL, -, -⟩ := h
  rw [hL]
  exact ⟨quasithinGenFitting_le G, le_normalizer_quasithinGenFitting G⟩

omit [Finite V] in
theorem le_rkIdx_of_le_mParam {G : Subgroup (MulAut V)} {v : MulAut V} (hvG : v ∈ G)
    (hord : orderOf v = 2) {n : ℕ} (h : n ≤ E3.mParam G) :
    n ≤ rkIdx (fixV (Subgroup.zpowers v)) := by
  have heven : Even (Nat.card G) := by
    have h1 : orderOf (⟨v, hvG⟩ : ↥G) ∣ Nat.card G := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hord] at h1
    exact even_iff_two_dvd.mpr h1
  unfold E3.mParam at h
  simp only [heven, ↓reduceIte] at h
  exact h.trans (Nat.sInf_le ⟨v, hvG, hord, rfl⟩)

theorem Cond1321.qhatOf_le_two (hV : ∀ w : V, w ^ 2 = 1) {G L : Subgroup (MulAut V)}
    {v : MulAut V} (h : Cond1321 G L v) : qhatOf G ≤ ((2 : ℚ) : WithTop ℚ) := by
  have hvG := h.mem
  have hsq : v ^ 2 = 1 := by rw [pow_two]; exact h.sq
  have hord : orderOf v = 2 := orderOf_eq_prime hsq h.ne_one
  refine (qhatOf_le_qOf G).trans (qOf_le_iff.mpr ⟨Subgroup.zpowers v, ⟨?_, ?_, ?_⟩,
    isQuadratic_zpowers hV hsq, ?_⟩)
  · exact Subgroup.zpowers_le.mpr hvG
  · intro h0
    apply h.ne_one
    have := Subgroup.mem_zpowers v
    rw [h0, Subgroup.mem_bot] at this
    exact this
  · refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact (Commute.refl v).zpow_zpow i j
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hsq, one_zpow]
  · have hrk1 : rk ↥(Subgroup.zpowers v) = 1 := by
      unfold rk
      rw [Nat.card_zpowers, hord]
      simp
    unfold rAV
    rw [hrk1]
    simp only [Nat.cast_one, div_one]
    exact_mod_cast h.rank

theorem rows1321 (hF : Facts1321) (hV : ∀ w : V, w ^ 2 = 1) {G L : Subgroup (MulAut V)}
    {v : MulAut V} (hB4 : B4Hyp G L) (hc : Cond1321 G L v) : Outcome1321 G L := by
  have hvG := hc.mem
  have hord : orderOf v = 2 := orderOf_eq_prime (by rw [pow_two]; exact hc.sq) hc.ne_one
  have hrk := hc.rank
  have hm3 : 3 ≤ rkIdx (fixV (Subgroup.zpowers v)) → False := fun h => by omega
  have hover := B4Hyp.isOver hB4
  rcases hF.b45 V hV G L hB4 (hc.qhatOf_le_two hV) with ⟨-, ⟨A, hA⟩, hall⟩ | ⟨-, htab⟩ | hp3
  ·
    rcases hall A hA with c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8 | c9 | c10 | c11
    · obtain ⟨-, ⟨n, hn⟩, -⟩ := c1
      by_cases h2 : n = 2
      · subst h2
        exact absurd (Or.inl hn) (hF.a5 V hV G L v hB4 hc)
      · exact absurd (Or.inl ⟨n, h2, hn⟩) (hF.lie V hV G L v hB4 hc)
    · obtain ⟨-, ⟨n, hn⟩, -⟩ := c2
      by_cases h1 : n = 1
      · subst h1
        obtain ⟨K, hKf, hKfin, hK, π, hπ, -⟩ := hn
        exact Or.inr (Or.inl ⟨K, hKf, hKfin, by simpa using hK, π, hπ⟩)
      · exact absurd (Or.inr (Or.inl ⟨n, h1, hn⟩)) (hF.lie V hV G L v hB4 hc)
    · obtain ⟨⟨n, hn, hnL⟩, -⟩ := c3
      rcases Nat.lt_trichotomy n 1 with h | h | h
      · obtain rfl : n = 0 := by omega
        exact absurd hn (not_binaryNaturalSp4_zero _)
      · subst h
        exact Or.inr (Or.inr ⟨A, Or.inr (Or.inl hn)⟩)
      · have hL := hnL h
        rw [hL] at hn
        exact absurd (Or.inr (Or.inr (Or.inl ⟨n, h, hn⟩))) (hF.lie V hV G L v hB4 hc)
    · obtain ⟨⟨n, hn, -, hnL⟩, -⟩ := c4
      rcases Nat.lt_trichotomy n 1 with h | h | h
      · obtain rfl : n = 0 := by omega
        exact absurd hn (not_g2Natural_zero _)
      · subst h
        exact Or.inr (Or.inr ⟨A, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))⟩)
      · have hL := hnL h
        rw [hL] at hn
        exact absurd (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, h, hn⟩)))) (hF.lie V hV G L v hB4 hc)
    · exact Or.inl (hF.sym V hV G L A v hB4 hc c5)
    · exact Or.inr (Or.inr ⟨A, Or.inl c6⟩)
    · exact absurd c7 (hF.a7four V hV G L A v hB4 hc)
    · exact absurd c8 (hF.a6three V hV G L A v hB4 hc)
    · exact Or.inr (Or.inr ⟨A, Or.inr (Or.inr (Or.inl c9))⟩)
    · exact Or.inr (Or.inr ⟨A, Or.inr (Or.inr (Or.inr (Or.inl c10)))⟩)
    · exact absurd c11 (hF.l5ten V hV G L A v hB4 hc)
  ·
    rcases htab with ⟨hA7, -⟩ | ⟨m, hm, hm4, -⟩ | ⟨m, hmU, -⟩ | ⟨f, hf, -⟩ | ⟨m, hm, hm9, -⟩ |
        ⟨hG2, -⟩ | ⟨hM12, -⟩ | ⟨hM22, -⟩ | ⟨hC22, -⟩ | ⟨hD22, -⟩ | ⟨hM, -⟩
    · obtain ⟨π, hπ, -⟩ := hA7
      exact Or.inl ⟨π, hπ⟩
    · by_cases h1 : m = 1
      · subst h1
        exact absurd (Or.inr hm4) (hF.a5 V hV G L v hB4 hc)
      · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, by omega, hm4⟩)))))
          (hF.lie V hV G L v hB4 hc)
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, hmU⟩))))))
        (hF.lie V hV G L v hB4 hc)
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f, hf⟩)))))))
        (hF.lie V hV G L v hB4 hc)
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨m, hm, hm9⟩))))))))
        (hF.lie V hV G L v hB4 hc)
    · exact Or.inr (Or.inr ⟨⊥, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hG2))))⟩)
    · exact (hm3 (hF.m12 V G L hover.1 hover.2 hM12 v hvG hord)).elim
    · exact (hm3 (hF.m22 V G L hover.1 hover.2 hM22 v hvG hord)).elim
    · exact (hm3 (le_rkIdx_of_le_mParam hvG hord ((hF.h144 V L G ⟨hover.1, hover.2⟩).2
        (Or.inl hC22)))).elim
    · exact (hm3 (le_rkIdx_of_le_mParam hvG hord ((hF.h144 V L G ⟨hover.1, hover.2⟩).2
        (Or.inr hD22)))).elim
    · have hM' : MathieuCocode24 L ⊤ ⊥ ∨ MathieuCode24 L ⊤ ⊥ ∨ MathieuCocode23 L ⊤ ⊥ ∨
          MathieuCode23 L ⊤ ⊥ := by
        rcases hM with h | h | h | h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      have h4 := (hF.h144 V L G ⟨hover.1, hover.2⟩).1 hM'
      exact (hm3 (le_rkIdx_of_le_mParam hvG hord (n := 3) (by omega))).elim
  ·
    obtain ⟨-, -, ⟨a, ha, hT⟩ | ⟨hJ2, -, hJ2V⟩⟩ := hp3
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr ⟨a, ha, hT⟩)))))))) (hF.lie V hV G L v hB4 hc)
    · exact (hm3 (hF.j2 V G L hover.1 hover.2 hJ2 hJ2V v hvG hord)).elim

end Rows

end CFSG.Quasithin.H13.A5

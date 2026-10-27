module

public import CFSG.Quasithin.EmptyFaithful.SBd8Mod

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace SBd8

section Trio

@[expose] def TrioShape (X : Type) [Group X] (U : Subgroup X) : Prop :=
  Subgroup.normalizer (U : Set X) = U ∧
  ∃ P₀ P₁ : Subgroup X, P₀ ≠ P₁ ∧ P₀ ≠ ⊤ ∧ P₁ ≠ ⊤ ∧ U < P₀ ∧ U < P₁ ∧
    Nat.card ↥P₀ = 3 * Nat.card ↥U ∧ Nat.card ↥P₁ = 3 * Nat.card ↥U ∧
    ∀ Y : Subgroup X, U ≤ Y → Y = U ∨ Y = P₀ ∨ Y = P₁ ∨ Y = ⊤

variable {X : Type} [Group X] [Finite X]

theorem eq_of_le_of_card_eq' {P Q : Subgroup X} (h : P ≤ Q) (hc : Nat.card ↥P = Nat.card ↥Q) : P = Q :=
  Subgroup.eq_of_le_of_card_ge h (le_of_eq hc.symm)

theorem eq_of_isSylowTwoOf_le {T U : Subgroup X} (hT : IsSylowTwoOf T ⊤) (hU : IsPGroup 2 ↥U)
    (hTU : T ≤ U) : T = U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmul := Subgroup.relIndex_mul_relIndex T U ⊤ hTU le_top
  have hodd : ¬ 2 ∣ T.relIndex ⊤ := by
    have := hT.2.2
    rwa [show (T.subgroupOf (⊤ : Subgroup X)).index = T.relIndex ⊤ from rfl] at this
  obtain ⟨k, hk⟩ := hU.index (T.subgroupOf U)
  have h2 : T.relIndex U = (T.subgroupOf U).index := rfl
  have hk0 : k = 0 := by
    by_contra hne
    apply hodd
    rw [← hmul, h2, hk]
    exact Dvd.dvd.mul_right (dvd_pow_self 2 hne) _
  have : T.relIndex U = 1 := by rw [h2, hk, hk0, pow_zero]
  exact le_antisymm hTU (Subgroup.relIndex_eq_one.1 this)

theorem trioConcl_of_shape {A : Subgroup (MulAut X)} {U K : Subgroup X} (d : OvgData X A U K)
    (h : TrioShape X U) :
    IsMinParabolicOf (⊤ : Subgroup X) K ∧
      ∀ P : Subgroup X, IsMinParabolicOf (⊤ : Subgroup X) P → Subgroup.normalizer (U : Set X) ≤ P →
        ∀ α ∈ A, P.map α.toMonoidHom = P := by
  obtain ⟨hN, P₀, P₁, hne, hP₀t, hP₁t, hUP₀, hUP₁, hc₀, hc₁, hlat⟩ := h
  have hUp : IsPGroup 2 ↥U := d.U_syl.2.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2)).1 hUp
  have h3U : ¬ 3 ∣ Nat.card ↥U := by
    rw [ha]
    intro h3
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  have hKm : K = P₀ ∨ K = P₁ := by
    rcases hlat K d.U_le with h | h | h | h
    · exfalso
      apply h3U
      rw [← h]
      exact d.three_dvd
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h d.K_ne
  have hPQ : ∀ Q : Subgroup X, (Q = P₀ ∨ Q = P₁) →
      (Q ≠ ⊤ ∧ U < Q ∧ Nat.card ↥Q = 3 * Nat.card ↥U) := by
    rintro Q (rfl | rfl)
    · exact ⟨hP₀t, hUP₀, hc₀⟩
    · exact ⟨hP₁t, hUP₁, hc₁⟩
  have hPP : ∀ Q R : Subgroup X, (Q = P₀ ∨ Q = P₁) → (R = P₀ ∨ R = P₁) → Q ≤ R → Q = R := by
    intro Q R hQ hR hle
    exact eq_of_le_of_card_eq' hle ((hPQ Q hQ).2.2.trans (hPQ R hR).2.2.symm)
  have hmaxOver : ∀ Q : Subgroup X, (Q = P₀ ∨ Q = P₁) → maxOver Q U = {U} := by
    intro Q hQ
    obtain ⟨hQt, hUQ, hQc⟩ := hPQ Q hQ
    ext M
    simp only [Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨hMQ, hmax⟩, hUM⟩
      rcases hlat M hUM with h | h | h | h
      · exact h
      · exact absurd (hPP M Q (Or.inl h) hQ hMQ.le) hMQ.ne
      · exact absurd (hPP M Q (Or.inr h) hQ hMQ.le) hMQ.ne
      · exact absurd (top_le_iff.1 (h ▸ hMQ.le)) hQt
    · rintro rfl
      refine ⟨⟨hUQ, fun K' hK' hK'Q => ?_⟩, le_rfl⟩
      rcases hlat K' hK'.le with h | h | h | h
      · exact absurd h hK'.ne'
      · exact hPP K' Q (Or.inl h) hQ hK'Q
      · exact hPP K' Q (Or.inr h) hQ hK'Q
      · exact absurd (top_le_iff.1 (h ▸ hK'Q)) hQt
  have hmin : ∀ Q : Subgroup X, (Q = P₀ ∨ Q = P₁) → IsMinParabolicOf (⊤ : Subgroup X) Q := by
    intro Q hQ
    refine ⟨U, d.U_syl, ⟨⟨le_top, (hPQ Q hQ).2.1, ?_⟩, ?_⟩⟩
    · rw [hmaxOver Q hQ]
      exact Set.ncard_singleton U
    · intro hle
      rw [hN] at hle
      exact (hPQ Q hQ).2.1.not_ge hle
  have hperm : ∀ Q : Subgroup X, (Q = P₀ ∨ Q = P₁) → ∀ α ∈ A,
      (Q.map α.toMonoidHom = P₀ ∨ Q.map α.toMonoidHom = P₁) := by
    intro Q hQ α hα
    obtain ⟨hQt, hUQ, hQc⟩ := hPQ Q hQ
    have hUQα : U ≤ Q.map α.toMonoidHom := by
      rw [← d.A_U α hα]
      exact Subgroup.map_mono hUQ.le
    have hcardα : Nat.card ↥(Q.map α.toMonoidHom) = Nat.card ↥Q :=
      Subgroup.card_map_of_injective α.injective
    rcases hlat _ hUQα with h | h | h | h
    · exfalso
      have h1 : Nat.card ↥(Q.map α.toMonoidHom) = Nat.card ↥U := by rw [h]
      rw [hcardα, hQc] at h1
      have : 0 < Nat.card ↥U := Nat.card_pos
      omega
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      apply hQt
      have := Subgroup.map_injective α.injective (h.trans (Subgroup.map_top_of_surjective _ α.surjective).symm)
      exact this
  refine ⟨hmin K hKm, ?_⟩
  intro P hP hNP α hα
  have hmin' := hP
  obtain ⟨T', hT', ⟨⟨-, hT'P, -⟩, -⟩⟩ := hP
  have hUP : U ≤ P := Subgroup.le_normalizer.trans hNP
  have hPcases : (P = P₀ ∨ P = P₁) ∨ P = ⊤ := by
    rcases hlat P hUP with h | h | h | h
    · exfalso
      exact absurd (eq_of_isSylowTwoOf_le hT' hUp (le_of_lt (h ▸ hT'P))) (ne_of_lt (h ▸ hT'P))
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  rcases hPcases with hP' | hPt
  · by_cases hPK : P = K
    · rw [hPK]
      exact d.A_K α hα
    · have hαP := hperm P hP' α hα
      have hαK : K.map α.toMonoidHom = K := d.A_K α hα
      have hne' : P.map α.toMonoidHom ≠ K := by
        intro h
        apply hPK
        rw [← hαK] at h
        exact Subgroup.map_injective α.injective h
      rcases hP' with hP0 | hP1
      · have hK1 : K = P₁ := hKm.resolve_left (fun hK0 => hPK (hP0.trans hK0.symm))
        rcases hαP with h0 | h1
        · rw [h0, hP0]
        · exact absurd (h1.trans hK1.symm) hne'
      · have hK0 : K = P₀ := hKm.resolve_right (fun hK1 => hPK (hP1.trans hK1.symm))
        rcases hαP with h0 | h1
        · exact absurd (h0.trans hK0.symm) hne'
        · rw [h1, hP1]
  · rw [hPt]
    exact Subgroup.map_top_of_surjective _ α.surjective

omit [Finite X] in
theorem TrioShape.map {Y : Type} [Group Y] [Finite Y] (e : X ≃* Y) {U : Subgroup X}
    (h : TrioShape X U) : TrioShape Y (U.map e.toMonoidHom) := by
  obtain ⟨hN, P₀, P₁, hne, hP₀t, hP₁t, hUP₀, hUP₁, hc₀, hc₁, hlat⟩ := h
  have hinj : Function.Injective e.toMonoidHom := e.injective
  have hmaptop : ∀ Q : Subgroup X, Q.map e.toMonoidHom = ⊤ ↔ Q = ⊤ := fun Q => by
    constructor
    · intro h
      apply Subgroup.map_injective hinj
      rw [h, Subgroup.map_top_of_surjective _ e.surjective]
    · rintro rfl
      exact Subgroup.map_top_of_surjective _ e.surjective
  have hcard : ∀ Q : Subgroup X, Nat.card ↥(Q.map e.toMonoidHom) = Nat.card ↥Q := fun Q =>
    Subgroup.card_map_of_injective hinj
  refine ⟨?_, P₀.map e.toMonoidHom, P₁.map e.toMonoidHom, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_equiv_normalizer_eq U e, hN]
  · exact fun h => hne (Subgroup.map_injective hinj h)
  · exact fun h => hP₀t ((hmaptop _).1 h)
  · exact fun h => hP₁t ((hmaptop _).1 h)
  · exact (Subgroup.map_lt_map_iff_of_injective hinj).2 hUP₀
  · exact (Subgroup.map_lt_map_iff_of_injective hinj).2 hUP₁
  · rw [hcard, hcard, hc₀]
  · rw [hcard, hcard, hc₁]
  · intro Y' hY'
    set Z := Y'.map e.symm.toMonoidHom with hZ
    have hZe : Z.map e.toMonoidHom = Y' := by
      rw [hZ, Subgroup.map_map]
      have : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id Y := by ext x; simp
      rw [this, Subgroup.map_id]
    have hUZ : U ≤ Z := by
      intro u hu
      refine ⟨e u, hY' ⟨u, hu, rfl⟩, by simp⟩
    rcases hlat Z hUZ with h | h | h | h
    · left; rw [← hZe, h]
    · right; left; rw [← hZe, h]
    · right; right; left; rw [← hZe, h]
    · right; right; right; rw [← hZe, h, Subgroup.map_top_of_surjective _ e.surjective]

theorem TrioShape.of_equiv_sylow {Y : Type} [Group Y] [Finite Y] (e : X ≃* Y) {U₀ : Subgroup X}
    (hU₀ : IsSylowTwoOf U₀ ⊤) (h : TrioShape X U₀) {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) :
    TrioShape Y U := by
  have h1 : IsSylowTwoOf (U₀.map e.toMonoidHom) ⊤ := by
    have := isSylowTwoOf_map' hU₀ e.toMonoidHom
    rwa [Subgroup.map_top_of_surjective _ e.surjective] at this
  obtain ⟨g, -, hg⟩ := B6.isSylowTwoOf_exists_conj h1 hU
  rw [hg]
  exact (h.map e).map (MulAut.conj g)

end Trio

end SBd8

end CFSG.Quasithin

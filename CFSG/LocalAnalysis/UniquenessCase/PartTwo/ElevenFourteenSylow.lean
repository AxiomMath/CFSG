module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qr
public import CFSG.LocalAnalysis.UniquenessCase.UC6Syl
import CFSG.LocalAnalysis.EvenBN.Tits.N.P3Frob

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.ABGLocalTools Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace ElevenFourteen

theorem exists_isSylowOf_inf {p : ℕ} [Fact p.Prime] {M X : Subgroup G} (hXM : X ≤ M) :
    ∃ P : Subgroup G, IsSylowOf p P M ∧ IsSylowOf p (P ⊓ X) X := by
  obtain ⟨Y, hY⟩ := exists_isSylowOf p X
  obtain ⟨P, hP, hYP⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC6.exists_isSylowOf_ge (hY.le.trans hXM) hY.isPGroup
  refine ⟨P, hP, ?_⟩
  have h : P ⊓ X = Y := hY.eq_of_le (le_inf hYP hY.le) inf_le_right hP.isPGroup.to_inf_left
  rw [h]
  exact hY

theorem eq_sup_inf_of_mul_eq {p : ℕ} [Fact p.Prime] {M X C P : Subgroup G} (hXM : X ≤ M)
    (hCM : C ≤ M) (hMC : M ≤ normalizer (C : Set G))
    (hXC : (X : Set G) * (C : Set G) = (M : Set G)) (hP : IsSylowOf p P M)
    (hPX : IsSylowOf p (P ⊓ X) X) : P = (P ⊓ C) ⊔ (P ⊓ X) := by
  have hXn : X ≤ normalizer (C : Set G) := hXM.trans hMC
  have hPM : P ≤ M := hP.le
  have hPn : P ≤ normalizer (C : Set G) := hPM.trans hMC
  have hQ : IsSylowOf p (P ⊓ C) C := hP.inf_of_le_normalizer hCM hMC
  have hXCn : X ≤ normalizer ((X ⊓ C : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · rintro ⟨hz1, hz2⟩
      exact ⟨X.mul_mem (X.mul_mem hx hz1) (X.inv_mem hx),
        (mem_normalizer_iff.1 (hXn hx) z).1 hz2⟩
    · rintro ⟨hz1, hz2⟩
      refine ⟨?_, (mem_normalizer_iff.1 (hXn hx) z).2 hz2⟩
      have := X.mul_mem (X.mul_mem (X.inv_mem hx) hz1) hx
      simpa [mul_assoc] using this
  have hYC : IsSylowOf p ((P ⊓ X) ⊓ (X ⊓ C)) (X ⊓ C) :=
    hPX.inf_of_le_normalizer inf_le_left hXCn
  have hYQ : (P ⊓ X) ⊓ (X ⊓ C) = (P ⊓ X) ⊓ (P ⊓ C) := by
    ext z
    simp only [mem_inf]
    tauto
  rw [hYQ] at hYC
  have hMeq : X ⊔ C = M := by
    apply SetLike.coe_injective
    rw [coe_mul_of_left_le_normalizer_right X C hXn]
    exact hXC
  have hprod1 : Nat.card M * Nat.card (X ⊓ C : Subgroup G) = Nat.card X * Nat.card C := by
    have := CFSG.LocalAnalysis.EvenBN.Tits.N.card_sup_mul_card_inf' hXn
    rwa [hMeq] at this
  have hYn : (P ⊓ X) ≤ normalizer ((P ⊓ C : Subgroup G) : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · rintro ⟨hz1, hz2⟩
      exact ⟨P.mul_mem (P.mul_mem hy.1 hz1) (P.inv_mem hy.1),
        (mem_normalizer_iff.1 (hPn hy.1) z).1 hz2⟩
    · rintro ⟨hz1, hz2⟩
      refine ⟨?_, (mem_normalizer_iff.1 (hPn hy.1) z).2 hz2⟩
      have := P.mul_mem (P.mul_mem (P.inv_mem hy.1) hz1) hy.1
      simpa [mul_assoc] using this
  have hprod2 := CFSG.LocalAnalysis.EvenBN.Tits.N.card_sup_mul_card_inf' hYn
  have hPcard : Nat.card P = p ^ (Nat.card M).factorization p := hP.card_eq
  have hYcard : Nat.card (P ⊓ X : Subgroup G) = p ^ (Nat.card X).factorization p := hPX.card_eq
  have hQcard : Nat.card (P ⊓ C : Subgroup G) = p ^ (Nat.card C).factorization p := hQ.card_eq
  have hIcard : Nat.card ((P ⊓ X) ⊓ (P ⊓ C) : Subgroup G) =
      p ^ (Nat.card (X ⊓ C : Subgroup G)).factorization p := hYC.card_eq
  have hfac : (Nat.card M).factorization p + (Nat.card (X ⊓ C : Subgroup G)).factorization p =
      (Nat.card X).factorization p + (Nat.card C).factorization p := by
    have h : (Nat.card M * Nat.card (X ⊓ C : Subgroup G)).factorization p =
        (Nat.card X * Nat.card C).factorization p := by rw [hprod1]
    rwa [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
      Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
      Finsupp.add_apply] at h
  have hsupcard : Nat.card ((P ⊓ X) ⊔ (P ⊓ C) : Subgroup G) = Nat.card P := by
    apply Nat.eq_of_mul_eq_mul_right
      (show 0 < p ^ (Nat.card (X ⊓ C : Subgroup G)).factorization p from
        pow_pos (Fact.out : p.Prime).pos _)
    rw [← hIcard, hprod2, hYcard, hQcard, hPcard, hIcard, ← pow_add, ← pow_add, hfac]
  have hle : (P ⊓ X) ⊔ (P ⊓ C) ≤ P := sup_le inf_le_left inf_le_left
  have heq : (P ⊓ X) ⊔ (P ⊓ C) = P :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq hsupcard.symm)
  rw [sup_comm]
  exact heq.symm

theorem conj_eq_of_pow_eq_one_of_odd {n : ℕ} (hn : Odd n) {V₀ : Subgroup G}
    (hV₀exp : ∀ d ∈ V₀, d ^ 2 = 1) {e v : G} (hen : e ^ n = 1)
    (he0 : ∀ d ∈ V₀, e * d * e⁻¹ = d) (hv : e * v * e⁻¹ * v⁻¹ ∈ V₀) :
    e * v * e⁻¹ = v := by
  set f : G := e * v * e⁻¹ * v⁻¹ with hf
  have hfv : e * v * e⁻¹ = f * v := by simp [hf]
  have hf2 : f ^ 2 = 1 := hV₀exp f hv
  have hfe : e * f * e⁻¹ = f := he0 f hv
  have key : ∀ k : ℕ, e ^ k * v * (e ^ k)⁻¹ = f ^ k * v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc e ^ (k + 1) * v * (e ^ (k + 1))⁻¹ = e * (e ^ k * v * (e ^ k)⁻¹) * e⁻¹ := by group
        _ = e * (f ^ k * v) * e⁻¹ := by rw [ih]
        _ = (e * f * e⁻¹) ^ k * (e * v * e⁻¹) := by rw [conj_pow]; group
        _ = f ^ (k + 1) * v := by rw [hfe, hfv, pow_succ']; group
  have hfn : f ^ n = 1 := by
    have h := key n
    rw [hen] at h
    simp only [inv_one, mul_one, one_mul] at h
    exact (mul_eq_right.1 h.symm)
  obtain ⟨m, hm⟩ := hn
  have hf1 : f = 1 := by
    have : f ^ n = f := by
      rw [hm, pow_succ, pow_mul, hf2, one_pow, one_mul]
    rw [← this]
    exact hfn
  rw [hfv, hf1, one_mul]

theorem inf_ctilde_inf_centralizer_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M V₀ V P : Subgroup G}
    (hP : IsPGroup p P) (hV₀exp : ∀ d ∈ V₀, d ^ 2 = 1) :
    P ⊓ F11.CTilde M V₀ V ⊓ centralizer (V₀ : Set G) ≤ centralizer (V : Set G) := by
  rintro e ⟨⟨heP, heC⟩, heV₀⟩
  obtain ⟨k, hk⟩ := hP ⟨e, heP⟩
  have hek : e ^ (p ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hodd : Odd (p ^ k) := (hp.odd_of_ne_two hp2).pow
  obtain ⟨-, -, hv⟩ := uc22p22q_mem_ctilde.1 heC
  have he0 : ∀ d ∈ V₀, e * d * e⁻¹ = d := by
    intro d hd
    have h1 : d * e = e * d := Subgroup.mem_centralizer_iff.1 heV₀ d hd
    calc e * d * e⁻¹ = d * e * e⁻¹ := by rw [h1]
      _ = d := by group
  rw [Subgroup.mem_centralizer_iff]
  intro v hv'
  have h2 := conj_eq_of_pow_eq_one_of_odd hodd hV₀exp hek he0 (hv v hv')
  calc v * e = (e * v * e⁻¹) * e := by rw [h2]
    _ = e * v := by group

theorem normal_inf_centralizer_subgroupOf {X V₀ : Subgroup G}
    (hX : X ≤ normalizer (V₀ : Set G)) :
    ((X ⊓ centralizer (V₀ : Set G)).subgroupOf X).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).2
    (uc22p22nc_le_normalizer_inf_centralizer hX)

theorem uniqueMax_of_le {M Y X : Subgroup G} (hM : rankThreeIsMaxTwoLocal M)
    (hU : UniqueMax M Y) (hYX : Y ≤ X) (hXM : X ≤ M) : UniqueMax M X := by
  unfold UniqueMax calMOf at *
  ext N
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hN, hXN⟩
    have hmem : N ∈ {N | rankThreeIsMaxTwoLocal N ∧ Y ≤ N} := ⟨hN, hYX.trans hXN⟩
    rw [hU] at hmem
    exact hmem
  · rintro rfl
    exact ⟨hM, hXM⟩

end ElevenFourteen

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

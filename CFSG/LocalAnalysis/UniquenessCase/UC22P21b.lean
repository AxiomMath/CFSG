module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P21a
public import CFSG.LocalAnalysis.UniquenessCase.UC6Pgrp
public import CFSG.LocalAnalysis.UniquenessCase.UC6Syl

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

theorem uc22p21b_conj_mem_centralizer {Z : Subgroup G} {n k : G}
    (hn : n ∈ normalizer (Z : Set G)) (hk : k ∈ centralizer (Z : Set G)) :
    n * k * n⁻¹ ∈ centralizer (Z : Set G) := by
  rw [mem_centralizer_iff] at hk ⊢
  intro z hz
  have hz' : n⁻¹ * z * n ∈ Z := (mem_normalizer_iff''.1 hn z).1 hz
  have h := hk _ hz'
  calc z * (n * k * n⁻¹) = n * ((n⁻¹ * z * n) * k) * n⁻¹ := by group
    _ = n * (k * (n⁻¹ * z * n)) * n⁻¹ := by rw [h]
    _ = (n * k * n⁻¹) * z := by group

theorem uc22p21b_comm_mem {A : Subgroup G} {t u : G} (ht : ∀ a ∈ A, t * a * t⁻¹ = a⁻¹)
    (hu : u ∈ normalizer (A : Set G)) : t * u * t⁻¹ * u⁻¹ ∈ centralizer (A : Set G) := by
  rw [mem_centralizer_iff]
  intro a ha
  have ha1 : u⁻¹ * a * u ∈ A := (mem_normalizer_iff''.1 hu a).1 ha
  have e1 : t⁻¹ * (u⁻¹ * a * u) * t = (u⁻¹ * a * u)⁻¹ := by
    have h := ht _ (A.inv_mem ha1)
    rw [inv_inv] at h
    calc t⁻¹ * (u⁻¹ * a * u) * t = t⁻¹ * (t * (u⁻¹ * a * u)⁻¹ * t⁻¹) * t := by rw [h]
      _ = (u⁻¹ * a * u)⁻¹ := by group
  have h2 : t * a⁻¹ * t⁻¹ = a := by simpa using ht _ (A.inv_mem ha)
  have h3 : t * u * t⁻¹ * u⁻¹ * a * (t * u * t⁻¹ * u⁻¹)⁻¹ = a := by
    calc t * u * t⁻¹ * u⁻¹ * a * (t * u * t⁻¹ * u⁻¹)⁻¹
        = t * u * (t⁻¹ * (u⁻¹ * a * u) * t) * u⁻¹ * t⁻¹ := by group
      _ = t * u * (u⁻¹ * a * u)⁻¹ * u⁻¹ * t⁻¹ := by rw [e1]
      _ = t * a⁻¹ * t⁻¹ := by group
      _ = a := h2
  exact (mul_inv_eq_iff_eq_mul.1 h3).symm

theorem uc22p21b_conj_mem_iff {Q : Subgroup G} {u z : G} (hu : u ∈ Q) :
    u⁻¹ * z * u ∈ Q ↔ z ∈ Q := by
  constructor
  · intro h
    have := Q.mul_mem (Q.mul_mem hu h) (Q.inv_mem hu)
    simpa [mul_assoc] using this
  · intro h
    exact Q.mul_mem (Q.mul_mem (Q.inv_mem hu) h) hu

theorem uc22p21b_exists_prod (C Q : Subgroup G) (h : ∀ u ∈ Q, ∀ c ∈ C, u * c * u⁻¹ ∈ C) :
    ∃ H : Subgroup G, C ≤ H ∧ Q ≤ H ∧ ∀ g ∈ H, ∃ c ∈ C, ∃ u ∈ Q, g = c * u := by
  refine ⟨{ carrier := {g | ∃ c ∈ C, ∃ u ∈ Q, g = c * u}
            one_mem' := ⟨1, C.one_mem, 1, Q.one_mem, (mul_one 1).symm⟩
            mul_mem' := ?_
            inv_mem' := ?_ }, ?_, ?_, fun g hg => hg⟩
  · rintro _ _ ⟨c₁, hc₁, u₁, hu₁, rfl⟩ ⟨c₂, hc₂, u₂, hu₂, rfl⟩
    refine ⟨c₁ * (u₁ * c₂ * u₁⁻¹), C.mul_mem hc₁ (h u₁ hu₁ c₂ hc₂), u₁ * u₂,
      Q.mul_mem hu₁ hu₂, ?_⟩
    group
  · rintro _ ⟨c, hc, u, hu, rfl⟩
    refine ⟨u⁻¹ * c⁻¹ * u, ?_, u⁻¹, Q.inv_mem hu, ?_⟩
    · simpa using h u⁻¹ (Q.inv_mem hu) c⁻¹ (C.inv_mem hc)
    · group
  · intro c hc
    exact ⟨c, hc, 1, Q.one_mem, (mul_one c).symm⟩
  · intro u hu
    exact ⟨1, C.one_mem, u, hu, (one_mul u).symm⟩

theorem uc22p21b_core {M A X : Subgroup G} (hMs : normalizer (M : Set G) = M) {q : ℕ}
    (hq : q.Prime) (hXq : IsPGroup q X) (hXA : X ≤ normalizer (A : Set G))
    (hXU : UC6.InU M X) {t : G} (ht : ∀ a ∈ A, t * a * t⁻¹ = a⁻¹) :
    ∃ m ∈ M, ∀ a ∈ A, m * a * m⁻¹ = a⁻¹ := by
  haveI : Fact q.Prime := ⟨hq⟩
  have htN : t ∈ normalizer (A : Set G) := mem_normalizer_of_inverts le_rfl ht
  obtain ⟨Q, hQN, hXQ⟩ := UC6.exists_isSylowOf_ge hXA hXq
  have hQU : UC6.InU M Q :=
    UC6.InU.of_subnormal hMs (UC6.isSubnormal_of_isPGroup hq hQN.isPGroup hXQ) hXU
  have hNQ : normalizer (Q : Set G) ≤ M := hQU.normalizer_le hMs
  have hCN : centralizer (A : Set G) ≤ normalizer (A : Set G) := centralizer_le_normalizer _
  obtain ⟨H, hCH, hQH, hHdec⟩ := uc22p21b_exists_prod (centralizer (A : Set G)) Q
    fun u hu c hc => uc22p21b_conj_mem_centralizer (hQN.le hu) hc
  have hHN : H ≤ normalizer (A : Set G) := by
    intro g hg
    obtain ⟨c, hc, u, hu, rfl⟩ := hHdec g hg
    exact (normalizer (A : Set G)).mul_mem (hCN hc) (hQN.le hu)
  have hQH' : IsSylowOf q Q H := hQN.of_le hQH hHN
  have hQ'H : Q.map (MulAut.conj t).toMonoidHom ≤ H := by
    rintro _ ⟨u, hu, rfl⟩
    have hc : t * u * t⁻¹ * u⁻¹ ∈ centralizer (A : Set G) :=
      uc22p21b_comm_mem ht (hQN.le hu)
    have e : (MulAut.conj t).toMonoidHom u = (t * u * t⁻¹ * u⁻¹) * u := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    exact H.mul_mem (hCH hc) (hQH hu)
  have hQ'S : IsSylowOf q (Q.map (MulAut.conj t).toMonoidHom) H := by
    refine isSylowOf_of_card hQ'H ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj t).injective, hQH'.card_eq]
  obtain ⟨k, hkH, hk⟩ := hQH'.exists_mem_conj hQ'S
  obtain ⟨c, hc, u, hu, rfl⟩ := hHdec k hkH
  have hn : c⁻¹ * t ∈ normalizer (Q : Set G) := by
    rw [mem_normalizer_iff]
    intro y
    have h1 : y ∈ Q ↔ t * y * t⁻¹ ∈ Q.map (MulAut.conj t).toMonoidHom := by
      have := Subgroup.mem_map_iff_mem (f := (MulAut.conj t).toMonoidHom)
        (MulAut.conj t).injective (K := Q) (x := y)
      simpa [MulAut.conj_apply] using this.symm
    rw [h1, hk]
    have e : (c * u)⁻¹ * (t * y * t⁻¹) * (c * u) = u⁻¹ * (c⁻¹ * (t * y * t⁻¹) * c) * u := by
      group
    have e' : c⁻¹ * t * y * (c⁻¹ * t)⁻¹ = c⁻¹ * (t * y * t⁻¹) * c := by group
    rw [e, e']
    exact uc22p21b_conj_mem_iff hu
  refine ⟨c⁻¹ * t, hNQ hn, fun a ha => ?_⟩
  have hca : a⁻¹ * c = c * a⁻¹ := mem_centralizer_iff.1 hc a⁻¹ (A.inv_mem ha)
  calc c⁻¹ * t * a * (c⁻¹ * t)⁻¹ = c⁻¹ * (t * a * t⁻¹) * c := by group
    _ = c⁻¹ * a⁻¹ * c := by rw [ht a ha]
    _ = c⁻¹ * (a⁻¹ * c) := by group
    _ = a⁻¹ := by rw [hca]; group

theorem s21_10 (D : Data G) (Ch : Choice2011 G) :
    H1930 D → ∀ c : Ctx21 D Ch, ∀ A : Subgroup G, A ≠ ⊥ → A ≤ c.B →
      ∀ X : Subgroup G, X ≠ ⊥ → (∃ q : ℕ, q.Prime ∧ IsPGroup q ↥X) → X ≤ normalizer (A : Set G) →
        X ∈ uniqueSet D.M → InvertedIn D.M A := by
  intro _ c A _ hAB X _ ⟨q, hq, hXq⟩ hXA hXU
  obtain ⟨_, _, B', C', _, _, _, _, _, _, ⟨t, _, _, _, htinv⟩, _⟩ := c.hB
  have hMs : normalizer (D.M : Set G) = D.M := UC6.normalizer_eq_of_isMaxTwoLocal D.maxLocal
  exact uc22p21b_core hMs hq hXq hXA ⟨hXU.1, fun g hg => hXU.2 g⁻¹ hg⟩
    fun a ha => htinv a (hAB ha)

end CFSG.LocalAnalysis.UniquenessCase.UC22

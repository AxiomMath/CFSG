module

public import CFSG.RankThree.PartOne.S11c.PlaneLines
public import CFSG.RankThree.PartOne.S11c.SporadicResidual

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Sporadic.SmallOddCore
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem card_le_of_isPGroup_two_of_le {G : Type*} [Group G] [Finite G] {C R2 : Subgroup G}
    {a m : ℕ} (hC : Nat.card C = 2 ^ a * m) (hm : ¬ 2 ∣ m) (hR2 : IsPGroup 2 R2) (hle : R2 ≤ C) :
    Nat.card R2 ≤ 2 ^ a := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hR2
  have hdvd : Nat.card R2 ∣ Nat.card C := Subgroup.card_dvd_of_le hle
  rw [hn, hC] at hdvd
  have hcop : Nat.Coprime (2 ^ n) m :=
    Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hm)
  have h2 : 2 ^ n ∣ 2 ^ a := hcop.dvd_of_dvd_mul_right hdvd
  rw [hn]
  exact Nat.le_of_dvd (by positivity) h2

section Model

variable {M : Type*} [Group M] [Finite M] {P R : Subgroup M}

theorem mem_of_pow_eq_one_of_autModel (h : AutModel P R) (hidx : Nat.card R ≤ 2 * Nat.card P)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {r : M} (hr : r ∈ R) (hrp : r ^ p = 1) : r ∈ P := by
  have hPnorm : (P.subgroupOf R).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact h.conj_mem g g.2 n hn⟩
  have hRP : Nat.card R ≤ 2 * Nat.card (P.subgroupOf R) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le).toEquiv]
    exact hidx
  have hodd : Odd (Nat.card (Subgroup.zpowers (⟨r, hr⟩ : R))) := by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk]
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hrp) with h1 | h1
    · rw [h1]
      exact odd_one
    · rw [h1]
      exact hp.odd_of_ne_two hp2
  have hle := odd_card_map_le_of_index_le_two (P.subgroupOf R) hRP hodd
  exact hle (Subgroup.mem_zpowers _)

theorem exists_inner_of_pow_eq_one (h : AutModel P R) (hidx : Nat.card R ≤ 2 * Nat.card P)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {T : Type*} [Group T] (θ : T ≃* P) (α : MulAut T)
    (hα : α ^ p = 1) : ∃ b : T, MulAut.conj b = α := by
  let α' : MulAut P := MulAut.congr θ α
  have hα'p : α' ^ p = 1 := by
    show (MulAut.congr θ α) ^ p = 1
    rw [← map_pow, hα, map_one]
  let r : M := h.elt α'
  have hrR : r ∈ R := h.elt_mem α'
  have hrp : r ^ p = 1 := by
    have : h.hom (α' ^ p) = r ^ p := by rw [map_pow]; rfl
    rw [← this, hα'p, map_one]
  have hrP : r ∈ P := mem_of_pow_eq_one_of_autModel h hidx hp hp2 hrR hrp
  refine ⟨θ.symm ⟨r, hrP⟩, ?_⟩
  ext t
  apply θ.injective
  apply Subtype.ext
  have key : ((θ (α t) : P) : M) = r * ((θ t : P) : M) * r⁻¹ := by
    have h1 := h.elt_spec α' (θ t)
    have h2 : α' (θ t) = θ (α t) := by
      show (MulAut.congr θ α) (θ t) = θ (α t)
      simp [MulAut.congr_apply]
    rw [h2] at h1
    exact h1
  rw [key]
  simp [MulAut.conj_apply]

omit [Finite M] in
theorem card_mulAut_dvd_card_of_autModel (h : AutModel P R) {T : Type*} [Group T] (θ : T ≃* P) :
    Nat.card (MulAut T) ∣ Nat.card R := by
  let φ : MulAut T →* M := h.hom.comp (MulAut.congr θ).toMonoidHom
  have hinj : Function.Injective φ := h.hom_injective.comp (MulAut.congr θ).injective
  have hle : φ.range ≤ R := by
    rintro _ ⟨α, rfl⟩
    exact h.elt_mem _
  have h1 : Nat.card (MulAut T) = Nat.card φ.range :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  rw [h1]
  exact Subgroup.card_dvd_of_le hle

omit [Finite M] in
theorem moveBound_of_plain {p k : ℕ}
    (h : ∀ y ∈ P, orderOf y = p → ∀ R2 : Subgroup M, IsPGroup 2 R2 →
      R2 ≤ R ⊓ centralizer ({y} : Set M) → Nat.card R2 ≤ k) :
    ∀ y ∈ P, orderOf y = p → ∀ f ∈ P, orderOf f = p → f * y = y * f →
      ∀ R2 : Subgroup M, IsPGroup 2 R2 → R2 ≤ R ⊓ centralizer ({y} : Set M) →
        (∀ r ∈ R2, f * r * f⁻¹ ∈ R2) → (∃ r ∈ R2, f * r * f⁻¹ ≠ r) → Nat.card R2 ≤ k :=
  fun y hy hord _ _ _ _ R2 hR2 hle _ _ => h y hy hord R2 hR2 hle

omit [Finite M] in
theorem sporadicPlanesCentralize_of_data_abel {A : Type} [Group A] (hPR : P ≤ R) (e : A ≃* P)
    {S : Finset ℕ}
    (hS : ∀ (T : Type) [Group T] [Finite T], IsSimpleGroup T → (∃ a b : T, a * b ≠ b * a) →
      Nonempty (T ≃* A) → ∀ p : ℕ, p.Prime → 3 < p → p ∈ S ∨ ¬ p ^ 2 ∣ Nat.card (MulAut T))
    (hinner : ∀ p ∈ S, ∀ (T : Type) [Group T] [Finite T], T ≃* A → ∀ α : MulAut T, α ^ p = 1 →
      ∃ b : T, MulAut.conj b = α)
    (hbound : ∀ p ∈ S, ∃ k : ℕ, ((p = 5 ∧ k < 16) ∨ (p = 7 ∧ k < 8)) ∧
      ∀ y ∈ P, orderOf y = p → ∀ f ∈ P, orderOf f = p → f * y = y * f →
        ∀ R2 : Subgroup M, IsPGroup 2 R2 → R2 ≤ R ⊓ centralizer ({y} : Set M) →
          (∀ r ∈ R2, f * r * f⁻¹ ∈ R2) → (∃ r ∈ R2, f * r * f⁻¹ ≠ r) →
          (p = 7 → Nat.card R2 = 8 → IsElementaryAbelian 2 R2) → Nat.card R2 ≤ k) :
    SporadicPlanesCentralize A := by
  intro T _ _ hs hnab ⟨eT⟩ p E U hpl
  have := hs
  let θ : T ≃* P := eT.trans e
  rcases hS T hs hnab ⟨eT⟩ p hpl.prime hpl.three_lt with hpS | hpAut
  · obtain ⟨k, hk, hb⟩ := hbound p hpS
    have hcenter : Subgroup.center T = ⊥ := center_eq_bot_of_simple hnab
    have hk' : (p = 5 ∧ k < 16) ∨ (p = 7 ∧ k < 8) ∨ (p = 11 ∧ k < 1024) := by
      rcases hk with h5 | h7
      · exact Or.inl h5
      · exact Or.inr (Or.inl h7)
    refine planeCentralizes_of_planeRBoundMove hcenter hk'
      (fun α hα => hinner p hpS T eT α hα) ?_ hpl
    exact planeRBoundMove_of_native_abel (φ := P.subtype.comp θ.toMonoidHom)
      (P.subtype_injective.comp θ.injective) (fun t => (θ t).2) hPR hb
  · exfalso
    have h1 : p ^ 2 ∣ Nat.card (MulAut T) := by
      have := Subgroup.card_subgroup_dvd_card E
      rwa [hpl.card] at this
    exact hpAut h1

omit [Finite M] in
theorem sporadicPlanesCentralize_of_data {A : Type} [Group A] (hPR : P ≤ R) (e : A ≃* P)
    {S : Finset ℕ}
    (hS : ∀ (T : Type) [Group T] [Finite T], IsSimpleGroup T → (∃ a b : T, a * b ≠ b * a) →
      Nonempty (T ≃* A) → ∀ p : ℕ, p.Prime → 3 < p → p ∈ S ∨ ¬ p ^ 2 ∣ Nat.card (MulAut T))
    (hinner : ∀ p ∈ S, ∀ (T : Type) [Group T] [Finite T], T ≃* A → ∀ α : MulAut T, α ^ p = 1 →
      ∃ b : T, MulAut.conj b = α)
    (hbound : ∀ p ∈ S, ∃ k : ℕ, ((p = 5 ∧ k < 16) ∨ (p = 7 ∧ k < 8)) ∧
      ∀ y ∈ P, orderOf y = p → ∀ f ∈ P, orderOf f = p → f * y = y * f →
        ∀ R2 : Subgroup M, IsPGroup 2 R2 → R2 ≤ R ⊓ centralizer ({y} : Set M) →
          (∀ r ∈ R2, f * r * f⁻¹ ∈ R2) → (∃ r ∈ R2, f * r * f⁻¹ ≠ r) → Nat.card R2 ≤ k) :
    SporadicPlanesCentralize A :=
  sporadicPlanesCentralize_of_data_abel hPR e hS hinner fun p hp => by
    obtain ⟨k, hk, hb⟩ := hbound p hp
    exact ⟨k, hk, fun y hy hord f hf hfo hfy R2 h2 hle hn hm _ =>
      hb y hy hord f hf hfo hfy R2 h2 hle hn hm⟩

theorem sporadicPlanesCentralize_of_model {A : Type} [Group A] (h : AutModel P R)
    (hidx : Nat.card R ≤ 2 * Nat.card P) (e : A ≃* P) {S : Finset ℕ}
    (hS : ∀ p : ℕ, p.Prime → 3 < p → p ∈ S ∨ ¬ p ^ 2 ∣ Nat.card R)
    (hbound : ∀ p ∈ S, ∃ k : ℕ, ((p = 5 ∧ k < 16) ∨ (p = 7 ∧ k < 8)) ∧
      ∀ y ∈ P, orderOf y = p → ∀ f ∈ P, orderOf f = p → f * y = y * f →
        ∀ R2 : Subgroup M, IsPGroup 2 R2 → R2 ≤ R ⊓ centralizer ({y} : Set M) →
          (∀ r ∈ R2, f * r * f⁻¹ ∈ R2) → (∃ r ∈ R2, f * r * f⁻¹ ≠ r) → Nat.card R2 ≤ k) :
    SporadicPlanesCentralize A := by
  refine sporadicPlanesCentralize_of_data h.le e (S := S) ?_ ?_ hbound
  · intro T _ _ _ _ ⟨eT⟩ p hp hp3
    rcases hS p hp hp3 with hpS | hpR
    · exact Or.inl hpS
    · exact Or.inr fun hdvd => hpR (hdvd.trans (card_mulAut_dvd_card_of_autModel h (eT.trans e)))
  · intro p hpS T _ _ eT α hα
    obtain ⟨k, hk, -⟩ := hbound p hpS
    have hp57 : p = 5 ∨ p = 7 := by
      rcases hk with ⟨h5, -⟩ | ⟨h7, -⟩
      · exact Or.inl h5
      · exact Or.inr h7
    have hp : p.Prime := by rcases hp57 with rfl | rfl <;> norm_num
    have hp2 : p ≠ 2 := by rcases hp57 with rfl | rfl <;> norm_num
    exact exists_inner_of_pow_eq_one h hidx hp hp2 (eT.trans e) α hα

end Model

end CFSG.RankThree.PartOne

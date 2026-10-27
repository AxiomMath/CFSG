module

public import CFSG.SignalizerFunctorTheorem.McBride.Models.Assembly
public import CFSG.SignalizerFunctorTheorem.McBride.Models.UnitaryC1
public import CFSG.SignalizerFunctorTheorem.McBride.Models.UnitaryOut
public import CFSG.SignalizerFunctorTheorem.McBride.Models.FrameItems

public section

open CFSG.Open
open scoped MatrixGroups

namespace CFSG.SignalizerFunctorTheorem.McBride

variable {X Y : Type*} [Group X] [Group Y]

namespace Extra

@[expose] def OuterPerfect (X : Type*) [Group X] : Prop :=
  ∀ P : Subgroup (MulAut X), Group.IsPerfect P → P ≤ (MulAut.conj : X →* MulAut X).range

@[expose] def OuterCoprimeSix (p : ℕ) (X : Type*) [Group X] : Prop :=
  ∀ g : MulAut X, Nat.Coprime p (orderOf g) → g ^ 6 ∈ (MulAut.conj : X →* MulAut X).range

theorem congr_conj (e : X ≃* Y) (x : X) :
    MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) := by
  ext y
  simp

theorem OuterPerfect.of_equiv (e : X ≃* Y) (h : OuterPerfect Y) : OuterPerfect X := by
  intro P hP g hg
  have hP' : Group.IsPerfect (P.map (MulAut.congr e).toMonoidHom) := by
    rw [Subgroup.isPerfect_iff] at hP ⊢
    rw [← Subgroup.map_commutator, hP]
  obtain ⟨y, hy⟩ := h _ hP' (Subgroup.mem_map_of_mem _ hg)
  refine ⟨e.symm y, (MulAut.congr e).injective ?_⟩
  rw [congr_conj, MulEquiv.apply_symm_apply]
  exact hy

theorem OuterCoprimeSix.of_equiv {p : ℕ} (e : X ≃* Y) (h : OuterCoprimeSix p Y) :
    OuterCoprimeSix p X := by
  intro g hg
  have hg' : Nat.Coprime p (orderOf (MulAut.congr e g)) := by
    rwa [orderOf_congr]
  obtain ⟨y, hy⟩ := h (MulAut.congr e g) hg'
  refine ⟨e.symm y, (MulAut.congr e).injective ?_⟩
  rw [congr_conj, MulEquiv.apply_symm_apply, map_pow]
  exact hy

theorem fixedCore1_eq_of_congr (e : X ≃* Y) {f : MulAut X}
    (h : fixedCore1 (MulAut.congr e f) = signalizerFixedSubgroup (MulAut.congr e f)) :
    fixedCore1 f = signalizerFixedSubgroup f := by
  rw [fixedCore1_congr, signalizerFixedSubgroup_congr] at h
  exact Subgroup.map_injective e.injective h

theorem exists_prime_overgroup_of_fixedCore1_eq {p ℓ : ℕ} [Finite X] {f : MulAut X}
    (hF : Frame p ℓ f) (hO : ItemO f) (hC1 : fixedCore1 f = signalizerFixedSubgroup f) :
    ∃ r : ℕ, r.Prime ∧ r ∣ Nat.card X ∧ ¬ r ∣ Nat.card (fixedNormalizer f) ∧
      ∀ Y : Subgroup X, fixedCore1 f ≤ Y → (∃ y ∈ Y, orderOf y = r) → Y = ⊤ := by
  obtain ⟨r, hr, hrX, hrM⟩ := hO.1
  refine ⟨r, hr, hrX, hrM, fun Z hZ ⟨y, hyZ, hyr⟩ => ?_⟩
  by_contra hne
  have hle := (hF.unique_maximal).2.2.2 Z (hC1 ▸ hZ) hne
  have hy : y ∈ fixedNormalizer f := hle hyZ
  have := (Subgroup.orderOf_dvd_natCard (fixedNormalizer f) hy)
  rw [hyr] at this
  exact hrM this

theorem exists_prime_overgroup_of_equiv (e : X ≃* Y) {f : MulAut X}
    (h : ∃ r : ℕ, r.Prime ∧ r ∣ Nat.card Y ∧
      ¬ r ∣ Nat.card (fixedNormalizer (MulAut.congr e f)) ∧
      ∀ H : Subgroup Y, fixedCore1 (MulAut.congr e f) ≤ H → (∃ y ∈ H, orderOf y = r) →
        H = ⊤) :
    ∃ r : ℕ, r.Prime ∧ r ∣ Nat.card X ∧ ¬ r ∣ Nat.card (fixedNormalizer f) ∧
      ∀ H : Subgroup X, fixedCore1 f ≤ H → (∃ y ∈ H, orderOf y = r) → H = ⊤ := by
  obtain ⟨r, hr, hrY, hrM, hall⟩ := h
  refine ⟨r, hr, ?_, ?_, fun H hH ⟨y, hyH, hyr⟩ => ?_⟩
  · rwa [Nat.card_congr e.toEquiv]
  · rwa [fixedNormalizer_congr, Subgroup.card_map_of_injective e.injective] at hrM
  · have h1 : H.map e.toMonoidHom = ⊤ :=
      hall _ (by rw [fixedCore1_congr]; exact Subgroup.map_mono hH)
        ⟨e y, Subgroup.mem_map_of_mem _ hyH, by rw [MulEquiv.orderOf_eq]; exact hyr⟩
    exact Subgroup.map_injective e.injective
      (h1.trans (Subgroup.map_top_of_surjective _ e.surjective).symm)

end Extra

open Extra

variable {p : ℕ} [Finite X]

omit [Finite X] in
theorem NearSimple.outer_perfect_le_inner'
    (h : NearSimple p X) (P : Subgroup (MulAut X))
    (hP : Group.IsPerfect P) : P ≤ (MulAut.conj : X →* MulAut X).range := by
  rcases h.model with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨n, rfl, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  · have hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 2 p)) := by
      rw [← Nat.card_congr e.toEquiv]; exact h.coprime
    exact OuterPerfect.of_equiv e (outer_perfect_psl2Even h.prime hcop) P hP
  · have hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 3 p)) := by
      rw [← Nat.card_congr e.toEquiv]; exact h.coprime
    exact OuterPerfect.of_equiv e (outer_perfect_psl2Three h.prime hcop) P hP
  · exact OuterPerfect.of_equiv e (outer_perfect_sz h.prime) P hP
  · have hcop : Nat.Coprime p (Nat.card (PSU3 2 p)) := by
      rw [← Nat.card_congr e.toEquiv]; exact h.coprime
    exact OuterPerfect.of_equiv e (outer_perfect_psu3 h.prime
      (UnitaryFrame.five_le_of_coprime h.prime hcop)) P hP

omit [Finite X] in
theorem NearSimple.outer_coprime_pow_six_mem_inner'
    (h : NearSimple p X) (g : MulAut X)
    (hg : Nat.Coprime p (orderOf g)) : g ^ 6 ∈ (MulAut.conj : X →* MulAut X).range := by
  rcases h.model with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨n, rfl, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  · have hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 2 p)) := by
      rw [← Nat.card_congr e.toEquiv]; exact h.coprime
    exact OuterCoprimeSix.of_equiv e (outer_coprime_pow_six_psl2Even h.prime hcop) g hg
  · have hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 3 p)) := by
      rw [← Nat.card_congr e.toEquiv]; exact h.coprime
    exact OuterCoprimeSix.of_equiv e (outer_coprime_pow_six_psl2Three h.prime hcop) g hg
  · exact OuterCoprimeSix.of_equiv e (outer_coprime_pow_six_sz h.prime) g hg
  · have hcop : Nat.Coprime p (Nat.card (PSU3 2 p)) := by
      rw [← Nat.card_congr e.toEquiv]; exact h.coprime
    exact OuterCoprimeSix.of_equiv e (outer_coprime_pow_six_psu3 h.prime
      (UnitaryFrame.five_le_of_coprime h.prime hcop)) g hg

theorem NearSimple.exists_prime_overgroup_C₁'
    (h : NearSimple p X) {f : MulAut X}
    (hf : orderOf f = p) :
    ∃ r : ℕ, r.Prime ∧ r ∣ Nat.card X ∧ ¬ r ∣ Nat.card (fixedNormalizer f) ∧
      ∀ Y : Subgroup X, fixedCore1 f ≤ Y → (∃ y ∈ Y, orderOf y = r) → Y = ⊤ := by
  obtain ⟨ℓ, hF⟩ := frame_of_nearSimple h hf
  have hO := itemO_of_nearSimple h hf
  rcases h.model with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨n, rfl, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  · have hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 2 p)) := by
      rw [← Nat.card_congr e.toEquiv]; exact h.coprime
    exact exists_prime_overgroup_of_fixedCore1_eq hF hO
      (fixedCore1_eq_of_congr e (fixedCore1_psl2Even h.prime hcop _ (by rw [orderOf_congr, hf])))
  · have hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 3 p)) := by
      rw [← Nat.card_congr e.toEquiv]; exact h.coprime
    exact exists_prime_overgroup_of_fixedCore1_eq hF hO
      (fixedCore1_eq_of_congr e (fixedCore1_psl2Three h.prime hcop _ (by rw [orderOf_congr, hf])))
  · have hcop : Nat.Coprime (2 * n + 1) (Nat.card (Sz n)) := by
      rw [← Nat.card_congr e.toEquiv]; exact h.coprime
    exact exists_prime_overgroup_of_fixedCore1_eq hF hO
      (fixedCore1_eq_of_congr e (fixedCore1_sz h.prime hcop _ (by rw [orderOf_congr, hf])))
  · have hcop : Nat.Coprime p (Nat.card (PSU3 2 p)) := by
      rw [← Nat.card_congr e.toEquiv]; exact h.coprime
    have hY := TransportA.nearPSolvable_of_mulEquiv e h.nearPSolvable
    exact exists_prime_overgroup_of_equiv e
      (exists_prime_overgroup_psu3 h.prime hcop hY _ (by rw [orderOf_congr, hf]))

end CFSG.SignalizerFunctorTheorem.McBride

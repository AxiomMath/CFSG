module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R899C4Sc
public import CFSG.LocalAnalysis.UniquenessCase.UC22R8100BFrat
public import CFSG.Quasithin.Background.A1cRank
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCRankOneCenter

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

section Swap

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem r899_exists_shift_perm {q : ℕ} [Fact q.Prime] {K S : Fin 3 → Subgroup Γ}
    (hS : ∀ i, CFSG.ABGLocalTools.IsSylowOf q (S i) (K i))
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, x * y = y * x) (π : Equiv.Perm (Fin 3))
    {w : Γ} (hwK : ∀ i, (K i).map (MulAut.conj w).toMonoidHom = K (π i)) :
    ∃ w' : Γ, (∀ i, (K i).map (MulAut.conj w').toMonoidHom = K (π i)) ∧
      ∀ i, (S i).map (MulAut.conj w').toMonoidHom = S (π i) := by
  classical
  have hconj : ∀ (H : Subgroup Γ) (a b : Γ),
      H.map (MulAut.conj (a * b)).toMonoidHom =
        (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
    intro H a b
    ext x
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨b * y * b⁻¹, ⟨y, hy, rfl⟩, by group⟩
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z, hz, by group⟩
  have step : ∀ (j : Fin 3) (w : Γ),
      (∀ i, (K i).map (MulAut.conj w).toMonoidHom = K (π i)) →
      ∃ w' : Γ, (∀ i, (K i).map (MulAut.conj w').toMonoidHom = K (π i)) ∧
        (S j).map (MulAut.conj w').toMonoidHom = S (π j) ∧
        ∀ i, i ≠ j → (S i).map (MulAut.conj w').toMonoidHom =
          (S i).map (MulAut.conj w).toMonoidHom := by
    intro j w hw
    have hSyl : CFSG.ABGLocalTools.IsSylowOf q
        ((S j).map (MulAut.conj w).toMonoidHom) (K (π j)) := by
      rw [← hw j]
      exact CFSG.ABGLocalTools.isSylowOf_of_card (Subgroup.map_mono (hS j).le)
        (by rw [Subgroup.card_map_of_injective (MulAut.conj w).injective,
          Subgroup.card_map_of_injective (MulAut.conj w).injective, (hS j).card_eq])
    obtain ⟨k, hk, hkx⟩ := uc22r8100b_exists_conj hSyl (hS (π j))
    have hkc : ∀ m, m ≠ π j → k ∈ centralizer (K m : Set Γ) := fun m hm =>
      Subgroup.mem_centralizer_iff.2 fun y hy =>
        (hcomm (π j) m hm.symm k hk y hy).symm
    have hkN : ∀ m, k ∈ normalizer (K m : Set Γ) := by
      intro m
      by_cases hm : m = π j
      · subst hm
        exact Subgroup.le_normalizer hk
      · exact Subgroup.centralizer_le_normalizer _ (hkc m hm)
    refine ⟨k * w, fun i => ?_, ?_, fun i hij => ?_⟩
    · rw [hconj (K i) k w, hw i]
      exact Subgroup.mem_normalizer_iff_map_conj_eq.1 (hkN (π i))
    · rw [hconj (S j) k w]
      ext x
      rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, hkx]
    ·
      have hle : (S i).map (MulAut.conj w).toMonoidHom ≤ K (π i) := by
        rw [← hw i]
        exact Subgroup.map_mono (hS i).le
      have hk' : k ∈ normalizer
          (((S i).map (MulAut.conj w).toMonoidHom : Subgroup Γ) : Set Γ) :=
        Subgroup.centralizer_le_normalizer _
          (Subgroup.mem_centralizer_iff.2 fun y hy =>
            (Subgroup.mem_centralizer_iff.1
              (hkc (π i) (fun h => hij (π.injective h))) y (hle hy)))
      rw [hconj (S i) k w]
      exact Subgroup.mem_normalizer_iff_map_conj_eq.1 hk'
  obtain ⟨w₁, hK₁, hS₁, -⟩ := step 0 w hwK
  obtain ⟨w₂, hK₂, hS₂, hrest₂⟩ := step 1 w₁ hK₁
  obtain ⟨w₃, hK₃, hS₃, hrest₃⟩ := step 2 w₂ hK₂
  refine ⟨w₃, hK₃, fun i => ?_⟩
  fin_cases i
  · change (S 0).map (MulAut.conj w₃).toMonoidHom = S (π 0)
    rw [hrest₃ 0 (by decide), hrest₂ 0 (by decide), hS₁]
  · change (S 1).map (MulAut.conj w₃).toMonoidHom = S (π 1)
    rw [hrest₃ 1 (by decide), hS₂]
  · exact hS₃

theorem r899_exists_common_pow_swap {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : r.Prime)
    {K S : Fin 3 → Subgroup Γ} {t : Fin 3 → Γ} (hSc : ∀ i, IsCyclic (S i))
    (ht : ∀ i, t i ∈ S i) (hto : ∀ i, orderOf (t i) = r) {w τ : Γ}
    (hwK : ∀ i, (K i).map (MulAut.conj w).toMonoidHom = K (i + 1))
    (hwS : ∀ i, (S i).map (MulAut.conj w).toMonoidHom = S (i + 1))
    (hτK : ∀ i, (K i).map (MulAut.conj τ).toMonoidHom = K (Equiv.swap 0 1 i))
    (hτS : ∀ i, (S i).map (MulAut.conj τ).toMonoidHom = S (Equiv.swap 0 1 i)) {d : Γ}
    (hd : orderOf d = p) (hdK : ∀ i, d ∈ normalizer (K i : Set Γ))
    (hdS : ∀ i, d ∈ normalizer (S i : Set Γ)) :
    ∃ g ∈ normalizer (K 2 : Set Γ) ⊓ normalizer (S 2 : Set Γ), orderOf g = p ∧
      ∃ k : ℕ, g * t 0 * g⁻¹ = t 0 ^ k ∧ g * t 1 * g⁻¹ = t 1 ^ k := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact r.Prime := ⟨hr⟩
  choose e he using fun i => @uc22r899c4_exists_pow_of_isCyclic Γ _ _ (S i) (hSc i) d (hdS i)
  have hdp : d ^ p = 1 := hd ▸ pow_orderOf_eq_one d
  have hep : ∀ i, ((e i : ℕ) : ZMod r) ^ p = 1 := fun i =>
    uc22r899c4_cast_pow_eq_one (hto i) (he i (t i) (ht i)) hdp
  have hpow : ∀ i {a b : ℕ}, (a : ZMod r) = (b : ZMod r) → t i ^ a = t i ^ b := fun i a b h =>
    pow_eq_pow_iff_modEq.2 (by rw [hto i]; exact (ZMod.natCast_eq_natCast_iff _ _ _).1 h)
  have hdτ : ∀ i, ∀ u ∈ S (Equiv.swap 0 1 i),
      (τ * d * τ⁻¹) * u * (τ * d * τ⁻¹)⁻¹ = u ^ (e i) := by
    intro i
    rw [← hτS i]
    exact uc22r899c4_conj_pow_conj (he i) τ
  have hdτ0 : ∀ u ∈ S 0, (τ * d * τ⁻¹) * u * (τ * d * τ⁻¹)⁻¹ = u ^ (e 1) := by
    have h := hdτ 1
    rw [show (Equiv.swap 0 1) (1 : Fin 3) = 0 from by decide] at h
    exact h
  have hdτ1 : ∀ u ∈ S 1, (τ * d * τ⁻¹) * u * (τ * d * τ⁻¹)⁻¹ = u ^ (e 0) := by
    have h := hdτ 0
    rw [show (Equiv.swap 0 1) (0 : Fin 3) = 1 from by decide] at h
    exact h
  have hdτ2 : ∀ u ∈ S 2, (τ * d * τ⁻¹) * u * (τ * d * τ⁻¹)⁻¹ = u ^ (e 2) := by
    have h := hdτ 2
    rw [show (Equiv.swap 0 1) (2 : Fin 3) = 2 from by decide] at h
    exact h
  have hS0 : ∀ u ∈ S 0, (d * (τ * d * τ⁻¹)) * u * (d * (τ * d * τ⁻¹))⁻¹ =
      u ^ (e 0 * e 1) := uc22r899c4_conj_pow_mul (he 0) hdτ0
  have hS1 : ∀ u ∈ S 1, (d * (τ * d * τ⁻¹)) * u * (d * (τ * d * τ⁻¹))⁻¹ =
      u ^ (e 0 * e 1) := by
    have h := uc22r899c4_conj_pow_mul (he 1) hdτ1
    rw [Nat.mul_comm (e 1) (e 0)] at h
    exact h
  have hS2 : ∀ u ∈ S 2, (d * (τ * d * τ⁻¹)) * u * (d * (τ * d * τ⁻¹))⁻¹ =
      u ^ (e 2 * e 2) := uc22r899c4_conj_pow_mul (he 2) hdτ2
  have hτK2 : (K 2).map (MulAut.conj τ).toMonoidHom = K 2 := by
    have h := hτK 2
    rw [show (Equiv.swap 0 1) (2 : Fin 3) = 2 from by decide] at h
    exact h
  have hτS2 : (S 2).map (MulAut.conj τ).toMonoidHom = S 2 := by
    have h := hτS 2
    rw [show (Equiv.swap 0 1) (2 : Fin 3) = 2 from by decide] at h
    exact h
  have hdτK : (τ * d * τ⁻¹) ∈ normalizer (K 2 : Set Γ) := by
    rw [← hτK2, ← Subgroup.map_equiv_normalizer_eq]
    exact ⟨d, hdK 2, rfl⟩
  have hdτS : (τ * d * τ⁻¹) ∈ normalizer (S 2 : Set Γ) := by
    rw [← hτS2, ← Subgroup.map_equiv_normalizer_eq]
    exact ⟨d, hdS 2, rfl⟩
  have hhK : d * (τ * d * τ⁻¹) ∈ normalizer (K 2 : Set Γ) :=
    (normalizer (K 2 : Set Γ)).mul_mem (hdK 2) hdτK
  have hhS : d * (τ * d * τ⁻¹) ∈ normalizer (S 2 : Set Γ) :=
    (normalizer (S 2 : Set Γ)).mul_mem (hdS 2) hdτS
  have hαp : ((e 0 * e 1 : ℕ) : ZMod r) ^ p = 1 := by
    rw [Nat.cast_mul, mul_pow, hep 0, hep 1, one_mul]
  have hβp : ((e 2 * e 2 : ℕ) : ZMod r) ^ p = 1 := by
    rw [Nat.cast_mul, mul_pow, hep 2, one_mul]
  by_cases hα : ((e 0 * e 1 : ℕ) : ZMod r) = 1
  · by_cases hβ : ((e 2 * e 2 : ℕ) : ZMod r) = 1
    ·
      have hβ' : (e 2 : ZMod r) * (e 2 : ZMod r) = 1 := by
        rw [← Nat.cast_mul]
        exact hβ
      have he2sq : (e 2 : ZMod r) ^ 2 = 1 := by
        rw [pow_two]
        exact hβ'
      have he2 : (e 2 : ZMod r) = 1 := by
        rcases sq_eq_one_iff.mp he2sq with h | h
        · exact h
        · have h2 := hep 2
          rw [h] at h2
          rw [Odd.neg_one_pow (hp.odd_of_ne_two hp2)] at h2
          rw [h, h2]
      by_cases he0 : (e 0 : ZMod r) = 1
      ·
        have he1 : (e 1 : ZMod r) = (e 0 : ZMod r) := by
          have h := hα
          rw [Nat.cast_mul, he0, one_mul] at h
          rw [h, he0]
        refine ⟨d, ⟨hdK 2, hdS 2⟩, hd, e 0, he 0 (t 0) (ht 0), ?_⟩
        rw [he 1 (t 1) (ht 1)]
        exact hpow 1 he1
      ·
        have hw1K : (K 1).map (MulAut.conj w).toMonoidHom = K 2 := by
          have h := hwK 1
          rw [show (1 : Fin 3) + 1 = 2 from by decide] at h
          exact h
        have hw1S : (S 1).map (MulAut.conj w).toMonoidHom = S 2 := by
          have h := hwS 1
          rw [show (1 : Fin 3) + 1 = 2 from by decide] at h
          exact h
        have hd''K : (w * d * w⁻¹) ∈ normalizer (K 2 : Set Γ) := by
          rw [← hw1K, ← Subgroup.map_equiv_normalizer_eq]
          exact ⟨d, hdK 1, rfl⟩
        have hd''S : (w * d * w⁻¹) ∈ normalizer (S 2 : Set Γ) := by
          rw [← hw1S, ← Subgroup.map_equiv_normalizer_eq]
          exact ⟨d, hdS 1, rfl⟩
        have hτd''K : (τ * (w * d * w⁻¹) * τ⁻¹) ∈ normalizer (K 2 : Set Γ) := by
          rw [← hτK2, ← Subgroup.map_equiv_normalizer_eq]
          exact ⟨_, hd''K, rfl⟩
        have hτd''S : (τ * (w * d * w⁻¹) * τ⁻¹) ∈ normalizer (S 2 : Set Γ) := by
          rw [← hτS2, ← Subgroup.map_equiv_normalizer_eq]
          exact ⟨_, hd''S, rfl⟩
        have hh''K : (w * d * w⁻¹) * (τ * (w * d * w⁻¹) * τ⁻¹) ∈
            normalizer (K 2 : Set Γ) :=
          (normalizer (K 2 : Set Γ)).mul_mem hd''K hτd''K
        have hh''S : (w * d * w⁻¹) * (τ * (w * d * w⁻¹) * τ⁻¹) ∈
            normalizer (S 2 : Set Γ) :=
          (normalizer (S 2 : Set Γ)).mul_mem hd''S hτd''S
        have hd''act : ∀ i, ∀ u ∈ S (i + 1),
            (w * d * w⁻¹) * u * (w * d * w⁻¹)⁻¹ = u ^ (e i) := by
          intro i
          rw [← hwS i]
          exact uc22r899c4_conj_pow_conj (he i) w
        have hd''0 : ∀ u ∈ S 0, (w * d * w⁻¹) * u * (w * d * w⁻¹)⁻¹ = u ^ (e 2) := by
          have h := hd''act 2
          rw [show (2 : Fin 3) + 1 = 0 from by decide] at h
          exact h
        have hd''1 : ∀ u ∈ S 1, (w * d * w⁻¹) * u * (w * d * w⁻¹)⁻¹ = u ^ (e 0) := by
          have h := hd''act 0
          rw [show (0 : Fin 3) + 1 = 1 from by decide] at h
          exact h
        have hτd''0 : ∀ u ∈ S 0, (τ * (w * d * w⁻¹) * τ⁻¹) * u *
            (τ * (w * d * w⁻¹) * τ⁻¹)⁻¹ = u ^ (e 0) := by
          have h := uc22r899c4_conj_pow_conj hd''1 τ
          rw [hτS 1, show (Equiv.swap 0 1) (1 : Fin 3) = 0 from by decide] at h
          exact h
        have hτd''1 : ∀ u ∈ S 1, (τ * (w * d * w⁻¹) * τ⁻¹) * u *
            (τ * (w * d * w⁻¹) * τ⁻¹)⁻¹ = u ^ (e 2) := by
          have h := uc22r899c4_conj_pow_conj hd''0 τ
          rw [hτS 0, show (Equiv.swap 0 1) (0 : Fin 3) = 1 from by decide] at h
          exact h
        have hh''0 : ∀ u ∈ S 0, ((w * d * w⁻¹) * (τ * (w * d * w⁻¹) * τ⁻¹)) * u *
            ((w * d * w⁻¹) * (τ * (w * d * w⁻¹) * τ⁻¹))⁻¹ = u ^ (e 2 * e 0) :=
          uc22r899c4_conj_pow_mul hd''0 hτd''0
        have hh''1 : ∀ u ∈ S 1, ((w * d * w⁻¹) * (τ * (w * d * w⁻¹) * τ⁻¹)) * u *
            ((w * d * w⁻¹) * (τ * (w * d * w⁻¹) * τ⁻¹))⁻¹ = u ^ (e 0 * e 2) :=
          uc22r899c4_conj_pow_mul hd''1 hτd''1
        have hζo : orderOf (((e 0 : ℕ)) : ZMod r) = p := orderOf_eq_prime (hep 0) he0
        have hζe : (((e 2 * e 0 : ℕ)) : ZMod r) = (((e 0 : ℕ)) : ZMod r) ^ 1 := by
          rw [pow_one, Nat.cast_mul, he2, one_mul]
        have hpdvd : p ∣ orderOf ((w * d * w⁻¹) * (τ * (w * d * w⁻¹) * τ⁻¹)) :=
          uc22r899c4_dvd_orderOf hp (hto 0) (hh''0 (t 0) (ht 0)) hζo (m := 1) hζe
            hp.not_dvd_one
        refine ⟨((w * d * w⁻¹) * (τ * (w * d * w⁻¹) * τ⁻¹)) ^
            (orderOf ((w * d * w⁻¹) * (τ * (w * d * w⁻¹) * τ⁻¹)) / p), ?_, ?_, ?_⟩
        · exact ⟨(normalizer (K 2 : Set Γ)).pow_mem hh''K _,
            (normalizer (S 2 : Set Γ)).pow_mem hh''S _⟩
        · exact orderOf_pow_orderOf_div (orderOf_pos _).ne' hpdvd
        · refine ⟨(e 2 * e 0) ^
              (orderOf ((w * d * w⁻¹) * (τ * (w * d * w⁻¹) * τ⁻¹)) / p), ?_, ?_⟩
          · rw [uc22r899c4_conj_pow_pow hh''0 _ (t 0) (ht 0)]
          · rw [uc22r899c4_conj_pow_pow hh''1 _ (t 1) (ht 1), Nat.mul_comm (e 0) (e 2)]
    ·
      have hζo : orderOf (((e 2 * e 2 : ℕ)) : ZMod r) = p := orderOf_eq_prime hβp hβ
      have hpdvd : p ∣ orderOf (d * (τ * d * τ⁻¹)) :=
        uc22r899c4_dvd_orderOf hp (hto 2) (hS2 (t 2) (ht 2)) hζo (m := 1) (by simp)
          hp.not_dvd_one
      refine ⟨(d * (τ * d * τ⁻¹)) ^ (orderOf (d * (τ * d * τ⁻¹)) / p), ?_, ?_, ?_⟩
      · exact ⟨(normalizer (K 2 : Set Γ)).pow_mem hhK _,
          (normalizer (S 2 : Set Γ)).pow_mem hhS _⟩
      · exact orderOf_pow_orderOf_div (orderOf_pos _).ne' hpdvd
      · exact ⟨(e 0 * e 1) ^ (orderOf (d * (τ * d * τ⁻¹)) / p),
          uc22r899c4_conj_pow_pow hS0 _ (t 0) (ht 0),
          uc22r899c4_conj_pow_pow hS1 _ (t 1) (ht 1)⟩
  ·
    have hζo : orderOf (((e 0 * e 1 : ℕ)) : ZMod r) = p := orderOf_eq_prime hαp hα
    have hpdvd : p ∣ orderOf (d * (τ * d * τ⁻¹)) :=
      uc22r899c4_dvd_orderOf hp (hto 0) (hS0 (t 0) (ht 0)) hζo (m := 1) (by simp)
        hp.not_dvd_one
    refine ⟨(d * (τ * d * τ⁻¹)) ^ (orderOf (d * (τ * d * τ⁻¹)) / p), ?_, ?_, ?_⟩
    · exact ⟨(normalizer (K 2 : Set Γ)).pow_mem hhK _,
        (normalizer (S 2 : Set Γ)).pow_mem hhS _⟩
    · exact orderOf_pow_orderOf_div (orderOf_pos _).ne' hpdvd
    · exact ⟨(e 0 * e 1) ^ (orderOf (d * (τ * d * τ⁻¹)) / p),
        uc22r899c4_conj_pow_pow hS0 _ (t 0) (ht 0),
        uc22r899c4_conj_pow_pow hS1 _ (t 1) (ht 1)⟩

theorem r899_exists_scalar_of_common_pow {p : ℕ} (hp : p.Prime) {K S : Fin 3 → Subgroup Γ}
    {t : Fin 3 → Γ} (hSK : ∀ i, S i ≤ K i) (ht : ∀ i, t i ∈ S i)
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, x * y = y * x)
    (hKS : ∀ y ∈ K 2, y ∈ normalizer (S 2 : Set Γ) → orderOf y ≠ p) (hpK : p ∣ Nat.card (K 2))
    {g : Γ} (hg : g ∈ normalizer (K 2 : Set Γ) ⊓ normalizer (S 2 : Set Γ)) (hgo : orderOf g = p)
    {k : ℕ} (hk0 : g * t 0 * g⁻¹ = t 0 ^ k) (hk1 : g * t 1 * g⁻¹ = t 1 ^ k) :
    ∃ B : Subgroup Γ, IsElemAbelian p B ∧ Nat.card B = p ^ 2 ∧
      (∀ b ∈ B, ∃ k : ℕ, ∀ u ∈ zpowers (t 0) ⊔ zpowers (t 1), b * u * b⁻¹ = u ^ k) ∧
      ∃ z ∈ B, z ≠ 1 ∧ ∀ u ∈ zpowers (t 0) ⊔ zpowers (t 1), z * u = u * z := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hgK : g ∉ K 2 := fun h => hKS g h hg.2 hgo
  have hgP : IsPGroup p (zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hgo, pow_one])
  obtain ⟨z, hzK, hzo, hzc⟩ :=
    CFSG.Quasithin.exists_orderOf_eq_of_isPGroup_normalizer hgP (zpowers_le.2 hg.1) hpK
  have hgz : g * z = z * g := Subgroup.mem_centralizer_iff.1 hzc g (mem_zpowers g)
  have hzg : z ∉ zpowers g := by
    intro hz
    have heq : zpowers z = zpowers g :=
      Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hz)
        (le_of_eq (by rw [Nat.card_zpowers, Nat.card_zpowers, hgo, hzo]))
    have hgz' : g ∈ zpowers z := by
      rw [heq]
      exact mem_zpowers g
    exact hgK (zpowers_le.2 hzK hgz')
  obtain ⟨hBel, hBc⟩ :=
    CFSG.ComponentClassification.UnbalancedGS.RankOneCenter.pair_isElementaryAbelian_card hgo
      hzo hgz hzg
  have ht01 : t 0 * t 1 = t 1 * t 0 :=
    hcomm 0 1 (by decide) (t 0) (hSK 0 (ht 0)) (t 1) (hSK 1 (ht 1))
  have hzU : zpowers (t 0) ⊔ zpowers (t 1) ≤ centralizer ({z} : Set Γ) :=
    sup_le (zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2
        (hcomm 2 0 (by decide) z hzK (t 0) (hSK 0 (ht 0))).symm))
      (zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2
        (hcomm 2 1 (by decide) z hzK (t 1) (hSK 1 (ht 1))).symm))
  have hzc' : ∀ u ∈ zpowers (t 0) ⊔ zpowers (t 1), z * u = u * z := fun u hu =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hzU hu)).symm
  have hBp : zpowers g ⊔ zpowers z ≤ uc22r899c4_powSub (zpowers (t 0) ⊔ zpowers (t 1)) :=
    sup_le (zpowers_le.2 (uc22r899c4_mem_powSub.2
        ⟨k, uc22r899c4_conj_pow_sup ht01 hk0 hk1⟩))
      (zpowers_le.2 (uc22r899c4_mem_powSub.2
        ⟨1, fun u hu => by rw [pow_one, hzc' u hu, mul_inv_cancel_right]⟩))
  refine ⟨zpowers g ⊔ zpowers z, (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).1
    hBel, hBc, fun b hb => uc22r899c4_mem_powSub.1 (hBp hb), z,
    Subgroup.mem_sup_right (mem_zpowers z), fun h1 => ?_, hzc'⟩
  rw [h1, orderOf_one] at hzo
  exact hp.one_lt.ne hzo

end Swap

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

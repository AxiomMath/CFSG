module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoToralCoord

public section

namespace CFSG.StandardType

namespace StepTwoToral

open Multiplicative

variable {G : Type} [Group G] {p r : ℕ}

@[expose] def GGStepTwoCoordShape (p r : ℕ) (O : Subgroup (ZMod p)ˣ)
    (ι : Multiplicative (Fin r → ZMod p) →* G) (C : Subgroup G) : Prop :=
  (∃ k : Fin r, ∀ s : Fin r → ZMod p, ι (ofAdd s) ∈ C → s k = 0) ∨
    ∃ (j j' : Fin r) (ε : Fin r → (ZMod p)ˣ), (∀ i, ε i ∈ O) ∧
      ∀ s : Fin r → ZMod p, ι (ofAdd s) ∈ C → ∃ c : ZMod p, ∀ i, i ≠ j → i ≠ j' → s i = ε i * c

theorem exists_sum_eq_of_ne_one [Fact p.Prime] {O : Subgroup (ZMod p)ˣ} {u : (ZMod p)ˣ}
    (huO : u ∈ O) (hu1 : u ≠ 1) {ι' : Type*} (S : Finset ι') (hS : p - 1 ≤ S.card)
    (σ : ZMod p) : ∃ w : ι' → (ZMod p)ˣ, (∀ i, w i ∈ O) ∧ ∑ i ∈ S, (w i : ZMod p) = σ := by
  classical
  set a : ZMod p := (u : ZMod p) - 1 with ha
  have ha0 : a ≠ 0 := by
    intro h
    apply hu1
    ext
    rw [Units.val_one]
    exact sub_eq_zero.mp h
  set j₀ : ℕ := ((σ - (S.card : ZMod p)) / a).val with hj₀
  have hj₀le : j₀ ≤ S.card := by
    have := ZMod.val_lt ((σ - (S.card : ZMod p)) / a)
    omega
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hj₀le
  refine ⟨fun i => if i ∈ T then u else 1, fun i => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact huO
    · exact O.one_mem
  · have h1 : ∀ i, ((if i ∈ T then u else 1 : (ZMod p)ˣ) : ZMod p) =
        1 + if i ∈ T then a else 0 := by
      intro i
      split_ifs <;> simp [ha]
    simp only [h1]
    rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.inter_eq_right.mpr hTS,
      Finset.sum_const, Finset.sum_const, hTcard, nsmul_eq_mul, nsmul_eq_mul, mul_one, hj₀,
      ZMod.natCast_zmod_val, div_mul_cancel₀ _ ha0]
    ring

theorem exists_balanced [Fact p.Prime] {O : Subgroup (ZMod p)ˣ} {u : (ZMod p)ˣ} (huO : u ∈ O)
    (hu1 : u ≠ 1) (S : Finset (Fin r)) (hS : p - 1 ≤ S.card) {ε : Fin r → (ZMod p)ˣ}
    (hε : ∀ i, ε i ∈ O) {t : Fin r → ZMod p} {c : ZMod p} (hc : c ≠ 0)
    (ht : ∀ i ∈ S, t i = ε i * c) :
    ∃ o : Fin r → (ZMod p)ˣ, (∀ i, o i ∈ O) ∧ ∑ i, (o i : ZMod p) * t i = 0 := by
  classical
  obtain ⟨w, hwO, hw⟩ := exists_sum_eq_of_ne_one huO hu1 S hS (-(∑ i ∈ Sᶜ, t i) / c)
  refine ⟨fun i => if i ∈ S then w i * (ε i)⁻¹ else 1, fun i => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact O.mul_mem (hwO i) (O.inv_mem (hε i))
    · exact O.one_mem
  · rw [← Finset.sum_add_sum_compl S]
    have h1 : ∑ i ∈ S, ((if i ∈ S then w i * (ε i)⁻¹ else 1 : (ZMod p)ˣ) : ZMod p) * t i =
        c * ∑ i ∈ S, (w i : ZMod p) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      simp only [hi, ↓reduceIte]
      rw [ht i hi, Units.val_mul, mul_assoc, ← mul_assoc ((ε i)⁻¹ : (ZMod p)ˣ).val,
        Units.inv_mul, one_mul, mul_comm]
    have h2 : ∑ i ∈ Sᶜ, ((if i ∈ S then w i * (ε i)⁻¹ else 1 : (ZMod p)ˣ) : ZMod p) * t i =
        ∑ i ∈ Sᶜ, t i := by
      refine Finset.sum_congr rfl fun i hi => ?_
      simp only [Finset.mem_compl.mp hi, ↓reduceIte, Units.val_one, one_mul]
    rw [h1, h2, hw, mul_div_cancel₀ _ hc, neg_add_cancel]

theorem exists_ne_zero_mem_ker [Fact p.Prime] {ι : Multiplicative (Fin r → ZMod p) →* G}
    {D : Subgroup G} (hD : D ≤ ι.range) (hDcard : Nat.card D = p ^ 2)
    (g : (Fin r → ZMod p) →+ ZMod p) :
    ∃ t : Fin r → ZMod p, t ≠ 0 ∧ g t = 0 ∧ ι (ofAdd t) ∈ D := by
  have hp : p.Prime := Fact.out
  have hfin : Finite D :=
    Nat.finite_of_card_ne_zero (by rw [hDcard]; exact pow_ne_zero 2 hp.ne_zero)
  have hcoord : ∀ d : D, ∃ t : Fin r → ZMod p, ι (ofAdd t) = d := fun d => by
    obtain ⟨y, hy⟩ := hD d.2
    exact ⟨toAdd y, by simpa using hy⟩
  choose c hc using hcoord
  have hlt : Nat.card (ZMod p) < Nat.card D := by
    rw [Nat.card_zmod, hDcard]
    exact lt_self_pow₀ hp.one_lt (by norm_num)
  have hni : ¬ Function.Injective (fun d : D => g (c d)) := fun hinj =>
    absurd (Nat.card_le_card_of_injective _ hinj) (not_le.mpr hlt)
  obtain ⟨d₁, d₂, heq, hne⟩ := Function.not_injective_iff.mp hni
  have heq' : g (c d₁) = g (c d₂) := heq
  refine ⟨c d₂ - c d₁, fun h0 => hne ?_, by rw [map_sub, heq', sub_self], ?_⟩
  · apply Subtype.ext
    rw [← hc d₁, ← hc d₂, sub_eq_zero.mp h0]
  · rw [ofAdd_sub, map_div, hc, hc]
    exact D.div_mem d₂.2 d₁.2

theorem ofAdd_smul_mem [NeZero p] {ι : Multiplicative (Fin r → ZMod p) →* G} {D : Subgroup G}
    {t : Fin r → ZMod p} (ht : ι (ofAdd t) ∈ D) (a : ZMod p) : ι (ofAdd (a • t)) ∈ D := by
  have h : a • t = a.val • t := by
    funext i
    rw [Pi.smul_apply, Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_zmod_val, smul_eq_mul]
  rw [h, ofAdd_nsmul, map_pow]
  exact D.pow_mem ht _

theorem contrary_of_vanish [Fact p.Prime] {O : Subgroup (ZMod p)ˣ}
    {ι : Multiplicative (Fin r → ZMod p) →* G} {D : Subgroup G} (hD : D ≤ ι.range)
    (hDcard : Nat.card D = p ^ 2) {k : Fin r}
    (hk : ∀ t : Fin r → ZMod p, ι (ofAdd t) ∈ D → t k = 0) :
    ∃ (k : Fin r) (o : Fin r → (ZMod p)ˣ) (s : Fin r → ZMod p),
      (∀ i, o i ∈ O) ∧ s ≠ 0 ∧ s k = 0 ∧ ∑ i, (o i : ZMod p) * s i = 0 ∧ ι (ofAdd s) ∈ D := by
  obtain ⟨t, ht0, hsum, htD⟩ := exists_ne_zero_mem_ker hD hDcard
    (AddMonoidHom.mk' (fun s => ∑ i, s i) fun x y => by
      simp only [Pi.add_apply, Finset.sum_add_distrib])
  refine ⟨k, 1, t, fun _ => O.one_mem, ht0, hk t htD, ?_, htD⟩
  simpa using hsum

theorem contrary_of_aligned [Fact p.Prime] {O : Subgroup (ZMod p)ˣ}
    {ι : Multiplicative (Fin r → ZMod p) →* G} {D : Subgroup G} (hD : D ≤ ι.range)
    (hDcard : Nat.card D = p ^ 2) {u : (ZMod p)ˣ} (huO : u ∈ O) (hu1 : u ≠ 1) (hr : p + 1 ≤ r)
    {j j' : Fin r} {ε : Fin r → (ZMod p)ˣ} (hε : ∀ i, ε i ∈ O)
    (hal : ∀ t : Fin r → ZMod p, ι (ofAdd t) ∈ D →
      ∃ c : ZMod p, ∀ i, i ≠ j → i ≠ j' → t i = ε i * c) :
    ∃ (k : Fin r) (o : Fin r → (ZMod p)ˣ) (s : Fin r → ZMod p),
      (∀ i, o i ∈ O) ∧ s ≠ 0 ∧ s k = 0 ∧ ∑ i, (o i : ZMod p) * s i = 0 ∧ ι (ofAdd s) ∈ D := by
  classical
  set S : Finset (Fin r) := (Finset.univ.erase j).erase j' with hSdef
  have hmemS : ∀ i, i ∈ S ↔ i ≠ j ∧ i ≠ j' := by
    intro i
    simp only [hSdef, Finset.mem_erase, Finset.mem_univ, and_true]
    exact and_comm
  have hScard : p - 1 ≤ S.card := by
    have h1 : (Finset.univ.erase j).card - 1 ≤ S.card := Finset.pred_card_le_card_erase
    have h2 : (Finset.univ : Finset (Fin r)).card - 1 ≤ (Finset.univ.erase j).card :=
      Finset.pred_card_le_card_erase
    rw [Finset.card_univ, Fintype.card_fin] at h2
    omega
  have hbal : ∀ (j₀ : Fin r) (t : Fin r → ZMod p), t ≠ 0 → t j₀ = 0 → ι (ofAdd t) ∈ D →
      ∀ c : ZMod p, c ≠ 0 → (∀ i, i ≠ j → i ≠ j' → t i = ε i * c) →
        ∃ (k : Fin r) (o : Fin r → (ZMod p)ˣ) (s : Fin r → ZMod p), (∀ i, o i ∈ O) ∧ s ≠ 0 ∧
          s k = 0 ∧ ∑ i, (o i : ZMod p) * s i = 0 ∧ ι (ofAdd s) ∈ D := by
    intro j₀ t ht0 htj htD c hc htc
    obtain ⟨o, hoO, hsum⟩ := exists_balanced huO hu1 S hScard hε hc fun i hi =>
      htc i ((hmemS i).mp hi).1 ((hmemS i).mp hi).2
    exact ⟨j₀, o, t, hoO, ht0, htj, hsum, htD⟩
  have hcase : ∀ j₀ j₁ : Fin r, (j₀ = j ∧ j₁ = j' ∨ j₀ = j' ∧ j₁ = j) →
      (∃ (k : Fin r) (o : Fin r → (ZMod p)ˣ) (s : Fin r → ZMod p), (∀ i, o i ∈ O) ∧ s ≠ 0 ∧
          s k = 0 ∧ ∑ i, (o i : ZMod p) * s i = 0 ∧ ι (ofAdd s) ∈ D) ∨
        ∃ t : Fin r → ZMod p, ι (ofAdd t) ∈ D ∧ t j₀ = 0 ∧ t j₁ ≠ 0 ∧ ∀ i, i ≠ j₁ → t i = 0 := by
    intro j₀ j₁ hj
    obtain ⟨t, ht0, htj, htD⟩ :=
      exists_ne_zero_mem_ker hD hDcard (Pi.evalAddMonoidHom (fun _ => ZMod p) j₀)
    rw [Pi.evalAddMonoidHom_apply] at htj
    obtain ⟨c, hc⟩ := hal t htD
    by_cases hc0 : c = 0
    · right
      have hsupp : ∀ i, i ≠ j₁ → t i = 0 := by
        intro i hi
        by_cases hij₀ : i = j₀
        · rw [hij₀]
          exact htj
        · rcases hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rw [hc i hij₀ hi, hc0, mul_zero]
          · rw [hc i hi hij₀, hc0, mul_zero]
      refine ⟨t, htD, htj, fun h1 => ht0 (funext fun i => ?_), hsupp⟩
      by_cases hi : i = j₁
      · rw [hi, h1]
        rfl
      · exact hsupp i hi
    · left
      exact hbal j₀ t ht0 htj htD c hc0 hc
  rcases hcase j j' (Or.inl ⟨rfl, rfl⟩) with h | ⟨t, htD, htj, htj', htsupp⟩
  · exact h
  rcases hcase j' j (Or.inr ⟨rfl, rfl⟩) with h | ⟨t', ht'D, ht'j', ht'j, ht'supp⟩
  · exact h
  have hjj' : j ≠ j' := fun h => htj' (h ▸ htj)
  obtain ⟨k, hk⟩ : S.Nonempty := Finset.card_pos.mp (by have := (Fact.out : p.Prime).two_le; omega)
  obtain ⟨hkj, hkj'⟩ := (hmemS k).mp hk
  refine ⟨k, 1, t j' • t' - t' j • t, fun _ => O.one_mem, fun h0 => ?_, ?_, ?_, ?_⟩
  · have h := congrFun h0 j
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, htsupp j hjj',
      mul_zero, sub_zero] at h
    exact mul_ne_zero htj' ht'j h
  · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, htsupp k hkj', ht'supp k hkj, mul_zero,
      sub_zero]
  · have hs1 : ∑ i, t i = t j' := Finset.sum_eq_single j' (fun i _ hi => htsupp i hi)
      (fun h => absurd (Finset.mem_univ j') h)
    have hs2 : ∑ i, t' i = t' j := Finset.sum_eq_single j (fun i _ hi => ht'supp i hi)
      (fun h => absurd (Finset.mem_univ j) h)
    simp only [Pi.one_apply, Units.val_one, one_mul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_sub_distrib, ← Finset.mul_sum, hs1, hs2]
    ring
  · rw [ofAdd_sub, map_div]
    exact D.div_mem (ofAdd_smul_mem ht'D _) (ofAdd_smul_mem htD _)

theorem contrary_of_coordShape [Fact p.Prime] {O : Subgroup (ZMod p)ˣ}
    {ι : Multiplicative (Fin r → ZMod p) →* G} {D C : Subgroup G} (hD : D ≤ ι.range)
    (hDcard : Nat.card D = p ^ 2) (hDC : D ≤ C) {u : (ZMod p)ˣ} (huO : u ∈ O) (hu1 : u ≠ 1)
    (hr : p + 1 ≤ r) (hC : GGStepTwoCoordShape p r O ι C) :
    ∃ (k : Fin r) (o : Fin r → (ZMod p)ˣ) (s : Fin r → ZMod p),
      (∀ i, o i ∈ O) ∧ s ≠ 0 ∧ s k = 0 ∧ ∑ i, (o i : ZMod p) * s i = 0 ∧ ι (ofAdd s) ∈ D := by
  rcases hC with ⟨k, hk⟩ | ⟨j, j', ε, hε, hal⟩
  · exact contrary_of_vanish hD hDcard fun t ht => hk t (hDC ht)
  · exact contrary_of_aligned hD hDcard huO hu1 hr hε fun t ht => hal t (hDC ht)

theorem succ_le_of_natCast_sub_one_eq_zero [Fact p.Prime] (hr : (r : ZMod p) - 1 = 0)
    (h2 : 2 ≤ r) : p + 1 ≤ r := by
  have h : ((r - 1 : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
    exact hr
  have hdvd := (ZMod.natCast_eq_zero_iff _ _).mp h
  have := Nat.le_of_dvd (by omega) hdvd
  omega

end StepTwoToral

end CFSG.StandardType

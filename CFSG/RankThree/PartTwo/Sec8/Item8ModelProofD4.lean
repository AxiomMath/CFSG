module

public import CFSG.RankThree.PartTwo.Sec8.Item8KFactsProofD4
import CFSG.RankThree.PartTwo.Sec8.Item82OneProofTransport
public import CFSG.RankThree.PartTwo.Sec4.Item47CoreClosed

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


@[expose] def KF82D4LangCoset : Prop :=
  ∀ (n : ℕ) (K : Type) [Field K] [Finite K] (σ : K ≃+* K),
    Nat.card K = (2 ^ n) ^ 3 → (∀ c, σ c = c ^ 2 ^ n) →
    ∀ g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (MulAut.conj g * fieldActor σ σ) ^ 3 = 1 →
        ∃ (β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
          (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
          fieldActor σ σ y = y ∧ y ^ 3 = 1 ∧
            MulAut.conj g * fieldActor σ σ = β * (MulAut.conj y * fieldActor σ σ) * β⁻¹

@[expose] def KF82D4SecondCent : Prop :=
  ∀ n : ℕ, Odd n → ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K),
    Nat.card K = (2 ^ n) ^ 3 → (∀ c, σ c = c ^ 2 ^ n) →
    ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      fieldActor σ σ y = y → orderOf y = 3 →
      ¬ Sec4.IsStdGraphFieldConj σ (MulAut.conj y * fieldActor σ σ) →
        IsoPGUThree (Sec4.autFix (MulAut.conj y * fieldActor σ σ)) (2 ^ n)

namespace Item8ModelProof

theorem eq_or_eq_inv_of_pow_three {G : Type*} [Group G] [Finite G] [IsCyclic G] {a b : G}
    (ha : orderOf a = 3) (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1) : b = a ∨ b = a⁻¹ := by
  classical
  have := Fintype.ofFinite G
  by_contra hne
  push Not at hne
  obtain ⟨hba, hbai⟩ := hne
  have ha3 : a ^ 3 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ha
    omega
  have haa : a ≠ a⁻¹ := by
    intro h
    have h2 : a ^ 2 = 1 := by rw [pow_two]; nth_rewrite 2 [h]; exact mul_inv_cancel a
    have := orderOf_dvd_of_pow_eq_one h2
    rw [ha] at this
    omega
  have hsub : ({1, a, a⁻¹, b} : Finset G) ⊆ Finset.univ.filter (fun x : G => x ^ 3 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl | rfl
    · exact one_pow 3
    · exact ha3
    · rw [inv_pow, ha3, inv_one]
    · exact hb3
  have hcard : ({1, a, a⁻¹, b} : Finset G).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair]
    · exact fun h => hbai h.symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨haa, fun h => hba h.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨fun h => ha1 h.symm, fun h => ha1 (inv_eq_one.mp h.symm), fun h => hb1 h.symm⟩
  have hle := Finset.card_le_card hsub
  have h3 := IsCyclic.card_pow_eq_one_le (α := G) (n := 3) (by norm_num)
  omega

variable {n : ℕ} {K : Type} [Field K] [Finite K] {σ : K ≃+* K}

theorem orderOf_sigma (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ n) :
    orderOf σ = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : σ ^ 3 = 1 := by
    ext c
    rw [pow_three, RingAut.mul_apply, RingAut.mul_apply]
    exact ringEquiv_cube_apply_eq hK hσ c
  have h1 : σ ≠ 1 := by
    rintro rfl
    have h := card_fixSubfield_of_cube hn hK hσ
    have htop : Nat.card (fixSubfield (1 : K ≃+* K)) = Nat.card K :=
      Nat.card_congr ((Equiv.subtypeEquivRight fun c => by
        simp).trans (Equiv.Set.univ K))
    rw [htop, hK] at h
    have h2 : 2 ≤ 2 ^ n := le_trans (by norm_num) (Nat.le_self_pow (by omega) 2)
    have : 2 ^ n < (2 ^ n) ^ 3 :=
      calc 2 ^ n < 2 ^ n * 4 := by omega
        _ ≤ 2 ^ n * (2 ^ n) ^ 2 := Nat.mul_le_mul_left _ (by nlinarith)
        _ = (2 ^ n) ^ 3 := by ring
    omega
  exact orderOf_eq_prime h3 h1

theorem exists_conj_mul_sigma (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 3)
    (hσ : ∀ c, σ c = c ^ 2 ^ n) {α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hα3 : α ^ 3 = 1) (hαin : ¬ IsInnerAut α) :
    ∃ g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      α = MulAut.conj g * fieldActor σ σ ∨ α = MulAut.conj g * (fieldActor σ σ)⁻¹ := by
  obtain ⟨g, δ, rfl⟩ := exists_conj_mul_fieldActor hn hK hσ α
  set I := (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
    MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range with hI
  have hIn : I.Normal := ⟨fun d hd β => by
    obtain ⟨y, rfl⟩ := hd
    exact ⟨β y, (mul_mulAutConj_mul_inv β y).symm⟩⟩
  have hgI : MulAut.conj g ∈ I := ⟨g, rfl⟩
  have hδ1 : δ ≠ 1 := by
    rintro rfl
    rw [fieldActor_one, mul_one] at hαin
    exact hαin hgI
  have hδ3I : fieldActor (t := TwistTag.D4) σ δ ^ 3 ∈ I := by
    have hmk : ((MulAut.conj g * fieldActor σ δ :
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
          MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ⧸ I) =
        ((fieldActor (t := TwistTag.D4) σ δ :
          MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
            MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ⧸ I) := by
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr hgI, one_mul]
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hmk, ← QuotientGroup.mk_pow, hα3,
      QuotientGroup.mk_one]
  have hδ3 : δ ^ 3 = 1 := by
    rw [← isInnerAut_fieldActor_iff hn hK hσ]
    have h1 : fieldActor (t := TwistTag.D4) σ (δ ^ 3) = fieldActor σ δ ^ 3 :=
      map_pow (fieldActorHom (t := TwistTag.D4) σ) δ 3
    rw [h1]
    exact hδ3I
  obtain ⟨-, -, -, hcyc, -⟩ := even_triality_exact_automorphism_normal_form hn K hK σ hσ
  have : IsCyclic (K ≃+* K) := hcyc
  refine ⟨g, ?_⟩
  rcases eq_or_eq_inv_of_pow_three (orderOf_sigma hn hK hσ) hδ3 hδ1 with rfl | rfl
  · exact Or.inl rfl
  · right
    rw [show fieldActor (t := TwistTag.D4) σ σ⁻¹ = (fieldActor σ σ)⁻¹ from
      map_inv (fieldActorHom (t := TwistTag.D4) σ) σ]

theorem conj_normal_form {X : Type*} [Group X] {ρ β : MulAut X} {y : X} (hy : ρ y = y) :
    (β * (MulAut.conj y * ρ) * β⁻¹ = β * ρ * β⁻¹ * MulAut.conj (β y) ∧
      (β * ρ * β⁻¹) (β y) = β y) ∧
    ((β * (MulAut.conj y * ρ) * β⁻¹)⁻¹ = β * ρ⁻¹ * β⁻¹ * MulAut.conj (β y⁻¹) ∧
      (β * ρ⁻¹ * β⁻¹) (β y⁻¹) = β y⁻¹) := by
  have hyi : ρ⁻¹ y = y := by
    rw [MulAut.inv_apply, MulEquiv.symm_apply_eq]
    exact hy.symm
  have hfix1 : (β * ρ * β⁻¹) (β y) = β y := by
    simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply, hy]
  have hfix2 : (β * ρ⁻¹ * β⁻¹) (β y⁻¹) = β y⁻¹ := by
    simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply, map_inv]
    rw [← MulAut.inv_apply, hyi]
  have hcomm : ∀ (γ : MulAut X) (z : X), γ z = z → γ * MulAut.conj z = MulAut.conj z * γ := by
    intro γ z hz
    have h := mul_mulAutConj_mul_inv γ z
    rw [hz] at h
    calc γ * MulAut.conj z = γ * MulAut.conj z * γ⁻¹ * γ := by group
      _ = MulAut.conj z * γ := by rw [h]
  refine ⟨⟨?_, hfix1⟩, ⟨?_, hfix2⟩⟩
  · rw [hcomm _ _ hfix1, ← mul_mulAutConj_mul_inv β y]
    group
  · rw [← mul_mulAutConj_mul_inv β y⁻¹, map_inv]
    group

theorem autFix_inv {X : Type*} [Group X] (α : MulAut X) : Sec4.autFix α⁻¹ = Sec4.autFix α := by
  ext x
  rw [Sec4.mem_autFix, Sec4.mem_autFix, MulAut.inv_apply, MulEquiv.symm_apply_eq, eq_comm]

theorem lang_cases (hL : KF82D4LangCoset) (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 3)
    (hσ : ∀ c, σ c = c ^ 2 ^ n) {α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hα3 : α ^ 3 = 1) (hαin : ¬ IsInnerAut α) :
    Sec4.IsStdGraphFieldConj σ α ∨
      ∃ (β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
        (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
        fieldActor σ σ y = y ∧ orderOf y = 3 ∧
          (α = β * (MulAut.conj y * fieldActor σ σ) * β⁻¹ ∨
            α⁻¹ = β * (MulAut.conj y * fieldActor σ σ) * β⁻¹) := by
  have hfin : ∀ (β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
      (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom), fieldActor σ σ y = y → y ^ 3 = 1 →
      (α = β * (MulAut.conj y * fieldActor σ σ) * β⁻¹ ∨
        α⁻¹ = β * (MulAut.conj y * fieldActor σ σ) * β⁻¹) →
      Sec4.IsStdGraphFieldConj σ α ∨
        ∃ (β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
          (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
          fieldActor σ σ y = y ∧ orderOf y = 3 ∧
            (α = β * (MulAut.conj y * fieldActor σ σ) * β⁻¹ ∨
              α⁻¹ = β * (MulAut.conj y * fieldActor σ σ) * β⁻¹) := by
    intro β y hy hy3 hαβ
    by_cases hy1 : y = 1
    · subst hy1
      left
      rcases hαβ with h | h
      · exact ⟨β, Or.inl (by rw [h, map_one, one_mul])⟩
      · refine ⟨β, Or.inr ?_⟩
        rw [← inv_inv α, h, map_one, one_mul]
        group
    · exact Or.inr ⟨β, y, hy, orderOf_eq_prime hy3 hy1, hαβ⟩
  obtain ⟨g, hg | hg⟩ := exists_conj_mul_sigma hn hK hσ hα3 hαin
  · obtain ⟨β, y, hy, hy3, hβ⟩ := hL n K σ hK hσ g (hg ▸ hα3)
    exact hfin β y hy hy3 (Or.inl (hg.trans hβ))
  · have hinv : α⁻¹ = MulAut.conj (fieldActor σ σ g⁻¹) * fieldActor σ σ := by
      rw [hg, mul_inv_rev, inv_inv, ← mul_mulAutConj_mul_inv (fieldActor σ σ) g⁻¹, map_inv]
      group
    have h3 : (MulAut.conj (fieldActor σ σ g⁻¹) * fieldActor σ σ) ^ 3 = 1 := by
      rw [← hinv, inv_pow, hα3, inv_one]
    obtain ⟨β, y, hy, hy3, hβ⟩ := hL n K σ hK hσ _ h3
    exact hfin β y hy hy3 (Or.inr (hinv.trans hβ))

end Item8ModelProof

open Item8ModelProof

theorem kF82D4OuterClasses_of_lang (hL : KF82D4LangCoset) : KF82D4OuterClasses := by
  intro n K _ _ σ hK hσ α hα3 hαin
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · have : 2 ≤ Nat.card K := Finite.one_lt_card
      rw [hK] at this
      norm_num at this
    · exact h
  rcases lang_cases hL hn hK hσ hα3 hαin with hstd | ⟨β, y, hy, hy3, hαβ | hαβ⟩
  · exact Or.inl hstd
  · obtain ⟨⟨h1, h2⟩, -⟩ := conj_normal_form (β := β) hy
    exact Or.inr ⟨β * fieldActor σ σ * β⁻¹, β y, ⟨β, Or.inl rfl⟩, h2,
      by rw [MulEquiv.orderOf_eq]; exact hy3, hαβ.trans h1⟩
  · obtain ⟨-, ⟨h1, h2⟩⟩ := conj_normal_form (β := β) hy
    refine Or.inr ⟨β * (fieldActor σ σ)⁻¹ * β⁻¹, β y⁻¹, ⟨β, Or.inr rfl⟩, h2,
      by rw [MulEquiv.orderOf_eq, orderOf_inv]; exact hy3, ?_⟩
    rw [← inv_inv α, hαβ, h1]

theorem kF82E9TrialityD4_of_lang (hL : KF82D4LangCoset) : KF82E9TrialityD4 :=
  kF82E9TrialityD4_of (kF82D4OuterClasses_of_lang hL)

theorem inputs47ClassesD4_of_lang (hL : KF82D4LangCoset) (hC : KF82D4SecondCent) :
    Sec4.Inputs47ClassesD4 := by
  intro n hnodd K _ _ σ hK hσ α hα3 hαin
  have hn : 1 ≤ n := hnodd.pos
  by_cases hstd : Sec4.IsStdGraphFieldConj σ α
  · exact Or.inl hstd
  right
  rcases lang_cases hL hn hK hσ hα3 hαin with hstd' | ⟨β, y, hy, hy3, hαβ | hαβ⟩
  · exact (hstd hstd').elim
  ·
    have hcongr : β * (MulAut.conj y * fieldActor σ σ) * β⁻¹ =
        MulAut.congr β (MulAut.conj y * fieldActor σ σ) := by
      ext x
      rfl
    have hnstd : ¬ Sec4.IsStdGraphFieldConj σ (MulAut.conj y * fieldActor σ σ) := by
      rintro ⟨β', h | h⟩
      · exact hstd ⟨β * β', Or.inl (by rw [hαβ, h]; group)⟩
      · exact hstd ⟨β * β', Or.inr (by rw [hαβ, h]; group)⟩
    have hPGU := hC n hnodd K σ hK hσ y hy hy3 hnstd
    obtain ⟨⟨h1, h2⟩, -⟩ := conj_normal_form (β := β) hy
    refine ⟨β * fieldActor σ σ * β⁻¹, β y, ⟨β, Or.inl rfl⟩, h2,
      by rw [MulEquiv.orderOf_eq]; exact hy3, hαβ.trans h1, ?_⟩
    rw [hαβ, hcongr]
    exact Item82OneProof.isoPGUThree_of_mulEquiv (Sec4.autFixCongrEquiv β _) hPGU
  ·
    have hcongr : β * (MulAut.conj y * fieldActor σ σ) * β⁻¹ =
        MulAut.congr β (MulAut.conj y * fieldActor σ σ) := by
      ext x
      rfl
    have hnstd : ¬ Sec4.IsStdGraphFieldConj σ (MulAut.conj y * fieldActor σ σ) := by
      rintro ⟨β', h | h⟩
      · refine hstd ⟨β * β', Or.inr ?_⟩
        rw [← inv_inv α, hαβ, h]
        group
      · refine hstd ⟨β * β', Or.inl ?_⟩
        rw [← inv_inv α, hαβ, h]
        group
    have hPGU := hC n hnodd K σ hK hσ y hy hy3 hnstd
    obtain ⟨-, ⟨h1, h2⟩⟩ := conj_normal_form (β := β) hy
    refine ⟨β * (fieldActor σ σ)⁻¹ * β⁻¹, β y⁻¹, ⟨β, Or.inr rfl⟩, h2,
      by rw [MulEquiv.orderOf_eq, orderOf_inv]; exact hy3, by rw [← inv_inv α, hαβ, h1], ?_⟩
    rw [← autFix_inv, hαβ, hcongr]
    exact Item82OneProof.isoPGUThree_of_mulEquiv (Sec4.autFixCongrEquiv β _) hPGU

end CFSG.RankThree.PartTwo.Sec8

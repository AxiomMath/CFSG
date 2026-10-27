module

public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.Quasithin.EmptyFaithful.S146F6

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

section Cases

variable {G : Type} [Group G]

@[expose] def Stage14614C1 (T H : Subgroup G) (p : ℕ) : Prop :=
  conjClosure (oTwoUpper H) (mcOf T) = oTwoUpper H ∧
    (p = 3 → ∀ r : ℕ, r.Prime → r ∣ Nat.card (mcOf T) → r = 2 ∨ r = 3)

@[expose] def Stage14614C2 (T H : Subgroup G) (p : ℕ) : Prop :=
  p = 3 ∧ conjClosure (oTwoUpper H) (mcOf T) ∈ cComp (mcOf T) ∧
    ∃ n : ℕ, (n = 4 ∨ n = 5) ∧
      Nonempty (OTwoQuot (mcOf T) ≃* MulAut (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)))

@[expose] def Stage14614C3 (T H : Subgroup G) (p : ℕ) : Prop :=
  p = 3 ∧ ∃ (K₁ : Subgroup G) (s : G), K₁ ∈ cComp (mcOf T) ∧ s ∈ T ∧
    s ∉ Subgroup.normalizer (K₁ : Set G) ∧
    conjClosure (oTwoUpper H) (mcOf T) = K₁ ⊔ conjSub s K₁ ∧
    (Nonempty (OTwoQuot (mcOf T) ≃* (Equiv.Perm (Fin 5) ≀ᵣ Multiplicative (ZMod 2))) ∨
      Nonempty (OTwoQuot (mcOf T) ≃*
        (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ≀ᵣ Multiplicative (ZMod 2))))

@[expose] def Stage14614C4 (T H : Subgroup G) (p : ℕ) : Prop :=
  p = 5 ∧ ∃ (K₁ : Subgroup G) (s : G), K₁ ∈ cComp (mcOf T) ∧ s ∈ T ∧
    s ∉ Subgroup.normalizer (K₁ : Set G) ∧
    conjClosure (oTwoUpper H) (mcOf T) = K₁ ⊔ conjSub s K₁ ∧
    mcOf T = conjClosure (oTwoUpper H) (mcOf T) ⊔ T ∧
    (imageOTwoQuot (mcOf T) (conjClosure (oTwoUpper H) (mcOf T))).index ∣ 32 ∧
    Nonempty (OTwoQuot K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4))

theorem stage14614At_iff (T H : Subgroup G) (p : ℕ) :
    Stage14614At T H p ↔
      Stage14614C1 T H p ∨ Stage14614C2 T H p ∨ Stage14614C3 T H p ∨ Stage14614C4 T H p :=
  Iff.rfl

end Cases

@[expose] def Input14616Norm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p →
      ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDec12 T M H p H₀ H₁ H₂ t →
        Subgroup.normalizer ((T ⊓ Subgroup.normalizer (H₁ : Set G) : Subgroup G) : Set G) ⊓ H = T

@[expose] def Input14616Weak : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → p = 3 →
      (Stage14614C2 T H p ∨ Stage14614C3 T H p) →
        ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDec12 T M H p H₀ H₁ H₂ t →
          Subgroup.normalizer ((T ⊓ Subgroup.normalizer (H₁ : Set G) : Subgroup G) : Set G) ⊓
            mcOf T ≤ H

@[expose] def Input14616One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → p = 3 → Stage14614C1 T H p →
      ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDec12 T M H p H₀ H₁ H₂ t →
        ¬ 3 ∣ Nat.card (oTwoUpper (Subgroup.normalizer
          ((T ⊓ Subgroup.normalizer (H₁ : Set G) : Subgroup G) : Set G) ⊓ mcOf T))

section Steps

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem IsDec12.relIndex_inf_normalizer_eq_two {PQ : Subgroup G} (hred : IsRedCE T M H PQ p)
    (h : IsDec12 T M H p H₀ H₁ H₂ t) :
    (T ⊓ Subgroup.normalizer (H₁ : Set G)).relIndex T = 2 := by
  have hTH : T ≤ H := hred.isHTM.1.1
  rw [h.inf_normalizer_eq hTH, inf_comm, Subgroup.inf_relIndex_right]
  have hle : H₀.relIndex T ≤ H₀.relIndex H :=
    Subgroup.relIndex_le_of_le_right hTH Subgroup.index_ne_zero_of_finite
  have h2 : H₀.relIndex H = 2 := h.index
  have hne0 : H₀.relIndex T ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hne1 : H₀.relIndex T ≠ 1 := fun h1 => by
    have hTH₀ : T ≤ H₀ := Subgroup.relIndex_eq_one.mp h1
    exact h.t_not (h.H₀_le_normalizer_H₁ (hTH₀ h.t_mem))
  omega

omit [Finite G] in
theorem IsDec12.le_normalizer_inf {PQ : Subgroup G} (hred : IsRedCE T M H PQ p)
    (h : IsDec12 T M H p H₀ H₁ H₂ t) :
    T ≤ Subgroup.normalizer ((T ⊓ Subgroup.normalizer (H₁ : Set G) : Subgroup G) : Set G) := by
  have hTH : T ≤ H := hred.isHTM.1.1
  rw [h.inf_normalizer_eq hTH]
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hxH₀ : x ∈ Subgroup.normalizer (H₀ : Set G) := h.le_normalizer_H₀ (hTH hx)
  constructor
  · rintro ⟨hyT, hyH₀⟩
    exact ⟨T.mul_mem (T.mul_mem hx hyT) (T.inv_mem hx),
      (Subgroup.mem_normalizer_iff.mp hxH₀ y).mp hyH₀⟩
  · rintro ⟨hyT, hyH₀⟩
    refine ⟨?_, (Subgroup.mem_normalizer_iff.mp hxH₀ y).mpr hyH₀⟩
    have := T.mul_mem (T.mul_mem (T.inv_mem hx) hyT) hx
    simpa [mul_assoc] using this

end Steps

section Final

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem IsDec12.normalizer_eq_of_case_one (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (hp3 : p = 3) (h1 : Stage14614C1 T H p)
    (h : IsDec12 T M H p H₀ H₁ H₂ t)
    (hX : ¬ 3 ∣ Nat.card (oTwoUpper (Subgroup.normalizer
      ((T ⊓ Subgroup.normalizer (H₁ : Set G) : Subgroup G) : Set G) ⊓ mcOf T))) :
    Subgroup.normalizer ((T ⊓ Subgroup.normalizer (H₁ : Set G) : Subgroup G) : Set G) ⊓ mcOf T = T := by
  have hTG : T ≤ mcOf T := le_centralizer_quasithinOmegaOneCenter T
  set N := Subgroup.normalizer ((T ⊓ Subgroup.normalizer (H₁ : Set G) : Subgroup G) : Set G) ⊓ mcOf T
    with hN
  have hTN : T ≤ N := le_inf (h.le_normalizer_inf hred) hTG
  have hNG : N ≤ mcOf T := inf_le_right
  have hTsyl : IsSylowTwoOf T (mcOf T) := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hTG
  have hXN : oTwoUpper N ≤ N := oTwoUpper_le N
  have hX2 : IsPGroup 2 (oTwoUpper N) := by
    refine isPGroup_two_of_forall fun x hx => ?_
    have hdvd : orderOf x ∣ Nat.card (oTwoUpper N) := by
      rw [← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hx)
    have h3 : ¬ 3 ∣ orderOf x := fun h3 => hX (h3.trans hdvd)
    have hpos : 0 < orderOf x := orderOf_pos x
    have hpr : ∀ {d : ℕ}, d.Prime → d ∣ orderOf x → d = 2 := by
      intro d hd hdd
      have hdG : d ∣ Nat.card (mcOf T) := by
        refine hdd.trans (hdvd.trans ?_)
        exact Subgroup.card_dvd_of_le (hXN.trans hNG)
      rcases h1.2 hp3 d hd hdG with h2 | h3'
      · exact h2
      · exact absurd (h3' ▸ hdd) h3
    have hord : orderOf x = 2 ^ (orderOf x).primeFactorsList.length :=
      Nat.eq_prime_pow_of_unique_prime_dvd hpos.ne' hpr
    exact ⟨(orderOf x).primeFactorsList.length, by rw [← hord]; exact pow_orderOf_eq_one x⟩
  have hXbot : oTwoUpper N = ⊥ := by
    refine le_antisymm ?_ bot_le
    refine (Subgroup.closure_le ⊥).mpr fun x hx => ?_
    obtain ⟨hxN, hxodd⟩ := hx
    have hxX : x ∈ oTwoUpper N := mem_oTwoUpper_of_odd hxN hxodd
    obtain ⟨k, hk⟩ := hX2 ⟨x, hxX⟩
    have hk' : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hdvd : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hcop : Nat.Coprime (orderOf x) (2 ^ k) := (Odd.coprime_two_right hxodd).pow_right k
    have h1 : orderOf x = 1 := Nat.Coprime.eq_one_of_dvd hcop hdvd
    exact orderOf_eq_one_iff.mp h1
  have hN2 : IsPGroup 2 N := by
    refine isPGroup_two_of_forall fun x hx => ?_
    obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper N hx
    rw [hXbot] at hk
    exact ⟨k, Subgroup.mem_bot.mp hk⟩
  exact hTsyl.eq_of_le hTN hNG hN2

theorem stage14616_of_named_inputs (h14 : Stage14614) (h15 : Stage14615) (iNorm : Input14616Norm)
    (iWeak : Input14616Weak) (iOne : Input14616One) : Stage14616 := by
  intro G _ _ T M S H PQ p hred hmax H₀ H₁ H₂ t hdec
  have hp3 : p = 3 := h15 G T M S H PQ p hred hmax
  refine ⟨hdec.relIndex_inf_normalizer_eq_two hred, ?_⟩
  have hAt := (stage14614At_iff T H p).mp (stage14614At_of h14 S hred hmax)
  have hTG : T ≤ mcOf T := le_centralizer_quasithinOmegaOneCenter T
  have hTN := hdec.le_normalizer_inf hred
  rcases hAt with c1 | c2 | c3 | c4
  · exact hdec.normalizer_eq_of_case_one S hred hp3 c1
      (iOne G T M S H PQ p hred hp3 c1 H₀ H₁ H₂ t hdec)
  · refine le_antisymm ?_ (le_inf hTN hTG)
    have hH := iWeak G T M S H PQ p hred hp3 (Or.inl c2) H₀ H₁ H₂ t hdec
    have hNH := iNorm G T M S H PQ p hred H₀ H₁ H₂ t hdec
    exact fun x hx => hNH.le ⟨hx.1, hH hx⟩
  · refine le_antisymm ?_ (le_inf hTN hTG)
    have hH := iWeak G T M S H PQ p hred hp3 (Or.inr c3) H₀ H₁ H₂ t hdec
    have hNH := iNorm G T M S H PQ p hred H₀ H₁ H₂ t hdec
    exact fun x hx => hNH.le ⟨hx.1, hH hx⟩
  · exact absurd c4.1 (by omega)

end Final

end CFSG.Quasithin

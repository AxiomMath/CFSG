module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorusOmega

public section

open Module Multiplicative QuadraticMap

namespace CFSG.StandardType

namespace OrthTorus

open CFSG.Assembly

section Cong

theorem one_not_modEq_neg_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ (1 : ℤ) ≡ -1 [ZMOD p] := by
  intro h
  have h1 := Int.modEq_iff_dvd.mp h
  have h2 : (p : ℤ) ∣ 2 := by
    have e : (-1 - 1 : ℤ) = -2 := by norm_num
    rwa [e, dvd_neg] at h1
  have h3 : p ∣ 2 := by exact_mod_cast h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)

theorem neg_one_not_modEq_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ (-1 : ℤ) ≡ 1 [ZMOD p] := fun h => one_not_modEq_neg_one hp hp2 h.symm

theorem modEq_neg_one_of_dvd {p q : ℕ} (h : p ∣ q + 1) : (q : ℤ) ≡ -1 [ZMOD p] := by
  rw [Int.modEq_iff_dvd]
  have e : (-1 - (q : ℤ)) = -((q + 1 : ℕ) : ℤ) := by
    push_cast
    ring
  rw [e, dvd_neg]
  exact_mod_cast h

theorem modEq_one_of_dvd {p q : ℕ} (hq : 1 ≤ q) (h : p ∣ q - 1) : (q : ℤ) ≡ 1 [ZMOD p] := by
  rw [Int.modEq_iff_dvd]
  have e : (1 - (q : ℤ)) = -((q - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub hq]
    push_cast
    ring
  rw [e, dvd_neg]
  exact_mod_cast h

theorem ne_two_of_dvd_card_sub_one {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hpq : p ∣ Nat.card K - 1) : p ≠ 2 := by
  rintro rfl
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  rw [Nat.card_eq_fintype_card, hn] at hpq
  have h2 : 2 ∣ 2 ^ (n : ℕ) := dvd_pow_self 2 n.ne_zero
  have h1 : 1 ≤ 2 ^ (n : ℕ) := Nat.one_le_two_pow
  omega

end Cong

section Plus

variable {K : Type} [Field K]

theorem isFrame_qPlusForm (n : ℕ) (c₀ : K) :
    OrdPNsOm.IsFrame (TableBOrth.qPlusForm K (n + 1)) c₀ false
      (fun i => Pi.single (Sum.inl i.castSucc) 1) (fun i => Pi.single (Sum.inr i.castSucc) 1)
      (Pi.single (Sum.inl (Fin.last n)) 1) (Pi.single (Sum.inr (Fin.last n)) 1) where
  hyp := TableBOrth.isHypFamily_single (fun k => TableBOrth.isHypCoord_qPlusForm _)
    (fun i j h => Fin.castSucc_injective _ (Sum.inr_injective h)) (fun i j => Sum.inl_ne_inr)
  pea i := by
    rw [(TableBOrth.isHypCoord_qPlusForm _).polar_left]
    simp
  peb i := by
    rw [(TableBOrth.isHypCoord_qPlusForm _).polar_left, Pi.single_apply]
    simp [(Fin.castSucc_lt_last i).ne]
  pfa i := by
    rw [(TableBOrth.isHypCoord_qPlusForm _).polar_right, Pi.single_apply]
    simp [(Fin.castSucc_lt_last i).ne]
  pfb i := by
    rw [(TableBOrth.isHypCoord_qPlusForm _).polar_right]
    simp
  pab := by
    rw [(TableBOrth.isHypCoord_qPlusForm _).polar_left]
    simp
  qa := by simpa using (TableBOrth.isHypCoord_qPlusForm (K := K) (Fin.last n)).map_left
  qb := by simpa using (TableBOrth.isHypCoord_qPlusForm (K := K) (Fin.last n)).map_right

variable [Finite K] [CharP K 2]

theorem charSum_qPlusForm (n : ℕ) :
    OrdPNsOm.charSum (TableBOrth.qPlusForm K (n + 1)) ⊤ = (Nat.card K : ℤ) ^ (n + 1) := by
  classical
  obtain ⟨c₀, hc₀⟩ := OrdPNsOm.exists_not_mem_range_wp (K := K)
  have hF := isFrame_qPlusForm (K := K) n c₀
  have hspan := hF.span_eq (U := ⊤) (fun _ => Submodule.mem_top) (by
    rw [finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring)
  rw [← hspan, OrdPFieldNsOm.charSum_span_frame hc₀ hF]
  simp [OrdPNsOm.tailSum, pow_succ]

omit [Finite K] in
theorem exists_totallySingular_qPlusForm {n : ℕ} (hn : 3 ≤ n) :
    ∃ T : Submodule K (Fin (n + 1) ⊕ Fin (n + 1) → K), finrank K T = 3 ∧
      ∀ v ∈ T, TableBOrth.qPlusForm K (n + 1) v = 0 :=
  OrdPFieldNsOm.exists_totallySingular_of_frame hn (isFrame_qPlusForm (K := K) n 0)

end Plus

section Minus

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem charSum_qMinusForm (m : ℕ) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    OrdPNsOm.charSum (TableBOrth.qMinusForm K m b c) ⊤ = -(Nat.card K : ℤ) ^ (m + 1) ∧
      (3 ≤ m → ∃ T : Submodule K (LargeEvenMinusIdx m → K), finrank K T = 3 ∧
        ∀ v ∈ T, TableBOrth.qMinusForm K m b c v = 0) := by
  classical
  obtain ⟨c₀, hc₀⟩ := OrdPNsOm.exists_not_mem_range_wp (K := K)
  set Q := TableBOrth.qMinusForm K m b c with hQdef
  have hnd := TableBOrth.nondegenerate_qMinusForm m hirr
  have hnd' : SUTB.NondegOn (polarBilin Q) ⊤ := fun x _ hx =>
    hnd.2 x fun y => hx y Submodule.mem_top
  have hdim : finrank K (⊤ : Submodule K (LargeEvenMinusIdx m → K)) = 2 * m + 2 := by
    rw [finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin]
    ring
  obtain ⟨τ, e, f, a, b', -, hF, hS⟩ := OrdPNsOm.exists_frame hc₀ m ⊤ hnd' hdim
  have hτ : τ = true := by
    by_contra hτ
    have hτf : τ = false := by simpa using hτ
    subst hτf
    set ι : Fin m ⊕ Fin 1 → OrdPNsOm.FrIdx m :=
      Sum.elim (fun i => .inl i) (fun _ => .inr (.inr 0)) with hι
    have hιinj : Function.Injective ι := by
      rintro (i | i) (j | j) h
      · simp only [hι, Sum.elim_inl, Sum.inl.injEq] at h
        rw [h]
      · simp [hι] at h
      · simp [hι] at h
      · rw [Subsingleton.elim i j]
    have hli := hF.linearIndependent.comp ι hιinj
    set T := Submodule.span K (Set.range (OrdPNsOm.fvec e f a b' ∘ ι)) with hT
    have hTdim : finrank K T = m + 1 := by
      rw [hT, finrank_span_eq_card hli, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
    have hsing : ∀ v ∈ T, Q v = 0 := TableBOrth.eq_zero_on_span (by
        rintro _ ⟨x, rfl⟩
        rcases x with i | i
        · exact hF.hyp.map_e i
        · simpa [hι] using hF.qa)
      (by
        rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
        rcases x with i | i <;> rcases y with j | j
        · exact hF.hyp.polar_ee i j
        · exact hF.pea i
        · change polar Q a (e j) = 0
          rw [polar_comm]
          exact hF.pea j
        · exact OrdPNsOm.polar_self_charTwo _)
    have := TableBOrth.finrank_le_of_singular_qMinus hirr T hsing
    omega
  subst hτ
  refine ⟨?_, fun hm => OrdPFieldNsOm.exists_totallySingular_of_frame hm hF⟩
  rw [hS]
  simp [OrdPNsOm.tailSum, pow_succ]

end Minus

end OrthTorus

end CFSG.StandardType

end

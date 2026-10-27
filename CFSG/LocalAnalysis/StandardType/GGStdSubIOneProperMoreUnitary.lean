module

public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperMoreOrthEnd
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeThree
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenVac

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace IOneMore

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag TableBUE

variable {K : Type} [Field K] [Finite K] {n d p : ℕ}

theorem card_le_unitary_of_coprime (h : UnitaryFieldData 2 n K)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hd : 3 ≤ d) (hdq : (d, 2 ^ n) ≠ (3, 2)) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ d)
    {X : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))}
    (hX : IsElemAbelian p X)
    (hXI : (X : Set (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))) ⊆
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) :
    Nat.card X ≤ p ^ (d - 1) := by
  classical
  have hN := gu_subset_normalizer (d := d) h
  have hpK : p ∣ Nat.card K - 1 := by
    have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have he : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
      obtain ⟨k, hk⟩ : ∃ k, 2 ^ n = k + 1 := ⟨2 ^ n - 1, by omega⟩
      rw [hk, Nat.add_sub_cancel]
      apply Nat.sub_eq_of_eq_add
      ring
    rw [hK, he]
    exact Dvd.dvd.mul_right hpq _
  set ρ := TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ n)) with hρ
  set N₀ : Subgroup
      (Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ n) : Set (GL (Fin d) K))) :=
    X.comap ρ with hN₀
  set χ : Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ n) : Set (GL (Fin d) K)) →*
      MulAut (projectiveSL d K) :=
    (conjAut d K).comp
      (Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ n) : Set (GL (Fin d) K))).subtype
    with hχ
  set Y := N₀.map χ with hY
  have hscal : ∀ M, ρ M = 1 → χ M = 1 := by
    intro M hM
    obtain ⟨c, hc⟩ := mem_scalars_of_projConj_eq_one h hK hd hdq hp hpq hM
    rw [hχ, MonoidHom.comp_apply, Subgroup.coe_subtype, ← hc, conjAut_scalar]
  have hYab : IsElemAbelian p Y := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, M, hM, rfl⟩ ⟨_, M', hM', rfl⟩
      apply Subtype.ext
      show χ M * χ M' = χ M' * χ M
      have hc : ρ (M * M' * M⁻¹ * M'⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv,
          TableB.IsElemAbelian.comm hX hM hM', mul_inv_cancel_right, mul_inv_cancel]
      have h1 := hscal _ hc
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      calc χ M * χ M' = χ M * χ M' * (χ M)⁻¹ * (χ M')⁻¹ * (χ M' * χ M) := by group
        _ = χ M' * χ M := by rw [h1, one_mul]
    · rintro _ ⟨M, hM, rfl⟩
      rw [← map_pow]
      exact hscal _ (by rw [map_pow]; exact hX.2 _ hM)
  have hYI : (Y : Set (MulAut (projectiveSL d K))) ⊆ Set.range (conjAut d K) := by
    rintro _ ⟨M, -, rfl⟩
    exact ⟨M, rfl⟩
  have hlift : ∀ x : X, ∃ M : Subgroup.normalizer
      (LargeEvenSUGroup (Fin d) K (2 ^ n) : Set (GL (Fin d) K)), ρ M = x := by
    intro x
    obtain ⟨M, hMgu, hMeq⟩ := TableB.exists_eq_projConj hN (hXI x.2)
    exact ⟨⟨M, hN hMgu⟩, hMeq.symm⟩
  choose Mf hMf using hlift
  have hMN : ∀ x : X, Mf x ∈ N₀ := fun x => by
    show ρ (Mf x) ∈ X
    rw [hMf x]
    exact x.2
  let f : X → Y := fun x => ⟨χ (Mf x), Mf x, hMN x, rfl⟩
  have hf : Function.Injective f := by
    intro a b hab'
    have h1 : χ ((Mf a)⁻¹ * Mf b) = 1 := by
      have := congrArg Subtype.val hab'
      simp only [f] at this
      rw [map_mul, map_inv, this, inv_mul_cancel]
    obtain ⟨c, hc⟩ := TypeA.exists_scalar_of_conjAut_eq_one h1
    have hz := mem_scalars_of_eq_scalar hc
    have h2 : ρ ((Mf a)⁻¹ * Mf b) = 1 := by
      have he : (Mf a)⁻¹ * Mf b = ⟨_, TableB.scalar_mem_normalizer _ hz⟩ := Subtype.ext rfl
      rw [he]
      exact TableB.projConj_of_scalar _ hz
    have h3 : ρ (Mf a) = ρ (Mf b) := by
      rw [map_mul, map_inv, inv_mul_eq_one] at h2
      exact h2
    apply Subtype.ext
    rw [← hMf a, ← hMf b, h3]
  have hle := Nat.card_le_card_of_injective f hf
  have hpd' : Nat.Coprime p d := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpd
  exact hle.trans (TypeA.card_le_of_subset_conjAut hp hpK (by omega) hpd' hYab hYI)

end IOneMore

open IOneMore

@[expose] def GGIOneMoreUnitaryFourLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .twA ∨ lab.tag = .twD) ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n + 1 ∧ ¬ p ∣ lab.n

section Certs

open CorFourTwoOpen in
theorem largeEvenLabelAll_bstarEq_twAThree {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n)
    (hpq : p ∣ 2 ^ n + 1) (hpn : ¬ p ∣ n) :
    LargeEvenLabelAll ⟨.twA, 3, n⟩ fun R _ I _ =>
      (∃ r, GGTorusLift p r R ∧ GGInnerDiagBound p r R I) ∧
        ∃ r, GGTorusLift p r R ∧ GGIRankLe p r R I := by
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpq
  have hpd : ¬ p ∣ 3 + 1 := by
    intro h4
    have h1 : p ∣ 2 ^ 2 := by norm_num; exact h4
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h1))
  have hlab : LargeEvenInLambda2 ⟨.twA, 3, n⟩ := ⟨hn, by norm_num, by norm_num⟩
  have h1 := largeEvenLabelAll_torusLift_twA hlab rfl hp hpq
  have h2 : LargeEvenLabelAll ⟨.twA, 3, n⟩ fun R _ I _ =>
      (∀ φ : MulAut R, φ ^ p = 1 → φ ∈ I) ∧
        ∀ X : Subgroup (MulAut R), (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X →
          Nat.card X < p ^ 4 := by
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    have hQ' := recipeUnitary_pow_mem (by norm_num) hn (by omega) hp hp2 hpn hQ
    obtain ⟨K, i1, i2, hK, hq, hpow⟩ := hQ'
    have h := TableBU.unitaryFieldData_of_card hK hn
    refine ⟨K, i1, i2, hK, hq, hpow, fun X hXI hX => ?_⟩
    have hdq : (3 + 1, 2 ^ n) ≠ (3, 2) := by
      intro he
      simp only [Prod.mk.injEq] at he
      omega
    have hle := card_le_unitary_of_coprime h hK (d := 3 + 1) (by norm_num) hdq hp hpq hpd hX hXI
    calc Nat.card X ≤ p ^ (3 + 1 - 1) := hle
      _ < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  refine (h1.and h2).mono fun R _ I _ ⟨hlift, hpow, hlt⟩ => ⟨⟨_, hlift,
    ggInnerDiagBound_of_forall_mem hpow⟩, _, hlift, fun X hXI hX h4 => ?_⟩
  exact absurd h4 (not_le.mpr (hlt X hXI hX))

theorem largeEvenLabelAll_bstarEq_unitaryFour {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGIOneMoreUnitaryFourLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => (∃ r, GGTorusLift p r R ∧ GGInnerDiagBound p r R I) ∧
      ∃ r, GGTorusLift p r R ∧ GGIRankLe p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hl, hpq, hpn⟩ := h
  dsimp only at htag hl hpq hpn
  subst hl
  have hn : 1 ≤ n := hlab.1
  rcases htag with rfl | rfl
  · exact largeEvenLabelAll_bstarEq_twAThree hp hn hpq hpn
  · exact largeEvenLabelAll_twDThree_of_twA (largeEvenLabelAll_bstarEq_twAThree hp hn hpq hpn)

theorem ggStdSubIOneProperInputOn_unitaryFour (ha₀ : GGLNoncyclicInput) :
    GGStdSubIOneProperInputOn GGIOneMoreUnitaryFourLabel :=
  ggStdSubIOneProperInputOn_of_bstarEq ha₀ fun _ _ hp hlab h _ =>
    largeEvenLabelAll_bstarEq_unitaryFour hp hlab h

end Certs

@[expose] def GGIOneMoreUnitaryRestLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twA ∧ 3 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1 ∧ (p ∣ lab.rank + 1 ∨ p = 3) ∧
    (lab.rank = 3 → p ∣ lab.n)

@[expose] def GGIOneMoreTwDThreeFieldLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twD ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n + 1 ∧ p = 3 ∧ p ∣ lab.n

@[expose] def GGIOneProperRestFourLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGIOneMoreUnitaryRestLabel p lab ∨ GGIOneMoreTwDThreeFieldLabel p lab ∨
    GGIOneMoreSpTwoLabel p lab ∨ GGIOneMoreOrthPlusFourLabel p lab ∨
      GGIOneMoreOrthMinusOddFieldLabel p lab ∨ GGIOneMoreExcTwoLabel p lab ∨
        GGIOneMoreTwE6Label p lab ∨ GGIOneMoreE6ThreeLabel p lab

theorem ggIOneProperRestThreeLabel_cover {p : ℕ} {lab : LargeEvenLabel}
    (h : GGIOneProperRestThreeLabel p lab) :
    GGIOneMoreUnitaryFourLabel p lab ∨ GGIOneProperRestFourLabel p lab := by
  rcases h with ⟨ht, hl, hpq, hc⟩ | ⟨ht, hl, hpq, hp3⟩ | hS | hP | hM | hX | hE6 | hE3
  · by_cases h3 : lab.rank = 3 ∧ ¬ p ∣ lab.n
    · exact Or.inl ⟨Or.inl ht, h3.1, hpq, h3.2⟩
    · refine Or.inr (Or.inl ⟨ht, hl, hpq, hc, fun hl3 => ?_⟩)
      by_contra hpn
      exact h3 ⟨hl3, hpn⟩
  · by_cases hpn : p ∣ lab.n
    · exact Or.inr (Or.inr (Or.inl ⟨ht, hl, hpq, hp3, hpn⟩))
    · exact Or.inl ⟨Or.inr ht, hl, hpq, hpn⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inl hS)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hP))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hM)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hX))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hE6)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hE3)))))))

end CFSG.StandardType

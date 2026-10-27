module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.Quasithin.Background.B5Part3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

section NaturalModules

variable {V : Type} [CommGroup V]

theorem s16c1610_card_of_realizes_nat {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} {H : Subgroup (MulAut V)} {U : Subgroup V}
    (h : (FFModel.nat Γ).Realizes H U ⊥) : Nat.card U = Nat.card K ^ Fintype.card ι := by
  obtain ⟨π, -, -, -, -, -, -, -, β, hβs, hβk, -⟩ := h
  have hinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have := (hβk u).1 hu
    exact Subtype.ext (by simpa using this)
  calc Nat.card U
      = Nat.card (↥(⊤ : Subgroup (Multiplicative (ι → K))) ⧸
          ((⊥ : Subgroup (Multiplicative (ι → K))).subgroupOf ⊤)) :=
        Nat.card_congr (Equiv.ofBijective β ⟨hinj, hβs⟩)
    _ = Nat.card (Multiplicative (ι → K)) :=
        Nat.card_congr (CFSG.Quasithin.B5.natQuotEquiv (Multiplicative (ι → K))).toEquiv
    _ = Nat.card (ι → K) := Nat.card_congr Multiplicative.toAdd
    _ = Nat.card K ^ Nat.card ι := Nat.card_fun
    _ = Nat.card K ^ Fintype.card ι := by rw [Nat.card_eq_fintype_card (α := ι)]

theorem s16c1610_rk_of_card_two_pow {A : Type*} [Group A] {e : ℕ} (h : Nat.card A = 2 ^ e) :
    rk A = e := by
  unfold rk
  rw [h, padicValNat.prime_pow]

theorem s16c1610_rk_natOmegaPlus {H : Subgroup (MulAut V)} {U : Subgroup V} {n a : ℕ}
    (h : NatOmegaPlus H U ⊥ n a) : rk ↥U = a * n := by
  obtain ⟨⟨r, hr⟩, K, _, _, hK, hreal⟩ := h
  have hn : n / 2 = r := by omega
  rw [hn] at hreal
  have hcard := s16c1610_card_of_realizes_nat hreal
  rw [Fintype.card_sum, Fintype.card_fin, hK, ← pow_mul] at hcard
  exact s16c1610_rk_of_card_two_pow (hcard.trans (by rw [show r + r = n by omega]))

theorem s16c1610_rk_natOmegaMinus {H : Subgroup (MulAut V)} {U : Subgroup V} {n a : ℕ}
    (hn2 : 2 ≤ n) (h : NatOmegaMinus H U ⊥ n a) : rk ↥U = a * n := by
  obtain ⟨⟨r, hr⟩, K, _, _, b, c, hK, -, hreal⟩ := h
  have hn : n / 2 = r := by omega
  rw [hn] at hreal
  have hcard := s16c1610_card_of_realizes_nat hreal
  rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, hK,
    ← pow_mul] at hcard
  exact s16c1610_rk_of_card_two_pow (hcard.trans (by rw [show r - 1 + (r - 1 + 2) = n by omega]))

theorem s16c1610_rk_natSpn {H : Subgroup (MulAut V)} {U : Subgroup V} {n a : ℕ}
    (h : NatSpn H U ⊥ n a) : rk ↥U = a * n := by
  obtain ⟨⟨r, hr⟩, K, _, _, hK, hreal⟩ := h
  have hn : n / 2 = r := by omega
  rw [hn] at hreal
  have hcard := s16c1610_card_of_realizes_nat hreal
  rw [Fintype.card_sum, Fintype.card_fin, hK, ← pow_mul] at hcard
  exact s16c1610_rk_of_card_two_pow (hcard.trans (by rw [show r + r = n by omega]))

theorem s16c1610_rk_binaryNaturalSL {H : Subgroup (MulAut V)} {U : Subgroup V} {n a : ℕ}
    (h : BinaryNaturalSL H U ⊥ n a) : rk ↥U = a * n := by
  obtain ⟨K, _, _, hK, hreal⟩ := h
  have hcard := s16c1610_card_of_realizes_nat hreal
  rw [Fintype.card_fin, hK, ← pow_mul] at hcard
  exact s16c1610_rk_of_card_two_pow hcard

end NaturalModules

section Alternating

open CFSG.Quasithin.G6

private noncomputable def weightSum (n : ℕ) : PermMod n →* Multiplicative (ZMod 2) where
  toFun x := Multiplicative.ofAdd (∑ i, Multiplicative.toAdd x i)
  map_one' := by simp
  map_mul' x y := by simp [Finset.sum_add_distrib]

private theorem ker_weightSum (n : ℕ) : (weightSum n).ker = coreMod n := by
  ext x
  rw [MonoidHom.mem_ker, mem_coreMod]
  exact ofAdd_eq_one

private theorem weightSum_surjective {n : ℕ} (hn : 1 ≤ n) : Function.Surjective (weightSum n) := by
  intro y
  refine ⟨Multiplicative.ofAdd (Pi.single (⟨0, hn⟩ : Fin n) (Multiplicative.toAdd y)), ?_⟩
  show Multiplicative.ofAdd (∑ i, Multiplicative.toAdd (Multiplicative.ofAdd
    (Pi.single (⟨0, hn⟩ : Fin n) (Multiplicative.toAdd y))) i) = y
  simp

theorem s16c1610_card_coreMod (n : ℕ) (hn : 1 ≤ n) : Nat.card (coreMod n) = 2 ^ (n - 1) := by
  have h := Subgroup.card_ker_mul_card_range (weightSum n)
  rw [MonoidHom.range_eq_top.mpr (weightSum_surjective hn), Subgroup.card_top, ker_weightSum,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod,
    Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin] at h
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [pow_succ] at h
  rw [Nat.add_sub_cancel]
  omega

private theorem allOnes_sq (n : ℕ) : allOnes n ^ 2 = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  simp only [allOnes, toAdd_pow, toAdd_ofAdd, toAdd_one, Pi.smul_apply, Pi.zero_apply]
  decide

private theorem zpow_of_mul_self_eq_one {A : Type*} [Group A] {g : A} (hg : g * g = 1) (k : ℤ) :
    g ^ k = 1 ∨ g ^ k = g := by
  have hinv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  refine Int.induction_on k (Or.inl (zpow_zero _)) ?_ ?_
  · intro i ih
    rw [zpow_add_one]
    rcases ih with h | h
    · right
      rw [h, one_mul]
    · left
      rw [h, hg]
  · intro i ih
    rw [zpow_sub_one, hinv]
    rcases ih with h | h
    · right
      rw [h, one_mul]
    · left
      rw [h, hg]

private theorem zpow_allOnes (n : ℕ) (k : ℤ) : allOnes n ^ k = 1 ∨ allOnes n ^ k = allOnes n :=
  zpow_of_mul_self_eq_one (by rw [← sq]; exact allOnes_sq n) k

private theorem card_altKer_le (n : ℕ) :
    Nat.card ↥(Subgroup.zpowers (allOnes n) ⊓ coreMod n) ≤ 2 :=
  calc Nat.card ↥(Subgroup.zpowers (allOnes n) ⊓ coreMod n)
      ≤ Nat.card ↥(Subgroup.zpowers (allOnes n)) := Subgroup.card_le_of_le inf_le_left
    _ = orderOf (allOnes n) := Nat.card_zpowers _
    _ ≤ 2 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (allOnes_sq n))

private theorem altKer_eq_bot_of_odd {n : ℕ} (hn : Odd n) :
    Subgroup.zpowers (allOnes n) ⊓ coreMod n = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx1, hx2⟩
  rw [Subgroup.mem_bot]
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx1
  rcases zpow_allOnes n k with h | h
  · exact h
  · exfalso
    have hx3 : allOnes n ∈ coreMod n := h ▸ hx2
    rw [mem_coreMod] at hx3
    simp only [allOnes, toAdd_ofAdd, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at hx3
    have h2 : ((n : ℕ) : ZMod 2) = 0 := by simpa using hx3
    rw [ZMod.natCast_eq_zero_iff_even] at h2
    exact (Nat.not_even_iff_odd.mpr hn) h2

variable {V : Type} [CommGroup V]

theorem s16c1610_card_alternatingNatural_mul {H : Subgroup (MulAut V)} {U : Subgroup V} {n : ℕ}
    (hn : 1 ≤ n) (h : AlternatingNatural H U ⊥ n) :
    Nat.card U * Nat.card ↥(Subgroup.zpowers (allOnes n) ⊓ coreMod n) = 2 ^ (n - 1) := by
  obtain ⟨π, -, -, -, -, -, -, -, β, hβs, hβk, -⟩ := h
  have hinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have := (hβk u).1 hu
    exact Subtype.ext (by simpa using this)
  have h1 : Nat.card U = Nat.card (↥(coreMod n) ⧸
      (Subgroup.zpowers (allOnes n) ⊓ coreMod n).subgroupOf (coreMod n)) :=
    Nat.card_congr (Equiv.ofBijective β ⟨hinj, hβs⟩)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((Subgroup.zpowers (allOnes n) ⊓ coreMod n).subgroupOf (coreMod n))
  have h3 : Nat.card ((Subgroup.zpowers (allOnes n) ⊓ coreMod n).subgroupOf (coreMod n)) =
      Nat.card ↥(Subgroup.zpowers (allOnes n) ⊓ coreMod n) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  rw [h1, ← h3, ← h2, s16c1610_card_coreMod n hn]

theorem s16c1610_card_alternatingNatural_odd {H : Subgroup (MulAut V)} {U : Subgroup V} {n : ℕ}
    (hn : Odd n) (h : AlternatingNatural H U ⊥ n) : Nat.card U = 2 ^ (n - 1) := by
  have h1 := s16c1610_card_alternatingNatural_mul (by obtain ⟨k, rfl⟩ := hn; omega) h
  rwa [altKer_eq_bot_of_odd hn, Subgroup.card_bot, mul_one] at h1

theorem s16c1610_two_pow_le_card_alternatingNatural {H : Subgroup (MulAut V)} {U : Subgroup V}
    {n : ℕ} (hn : 2 ≤ n) (h : AlternatingNatural H U ⊥ n) : 2 ^ (n - 2) ≤ Nat.card U := by
  have h1 := s16c1610_card_alternatingNatural_mul (by omega) h
  have h2 := card_altKer_le n
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rw [show k + 2 - 1 = k + 1 by omega, pow_succ] at h1
  rw [show k + 2 - 2 = k by omega]
  exact Nat.le_of_mul_le_mul_right
    (calc 2 ^ k * 2 = Nat.card U * Nat.card ↥(Subgroup.zpowers (allOnes (k + 2)) ⊓
            coreMod (k + 2)) := h1.symm
      _ ≤ Nat.card U * 2 := Nat.mul_le_mul_left _ h2) (by norm_num)

end Alternating

section SumOfTwo

variable {W : Type} [CommGroup W] [Finite W]

theorem s16c1610_rk_sumOfNat_two {N : Subgroup (MulAut W) → Subgroup W → Subgroup W → Prop}
    {H : Subgroup (MulAut W)} {U : Subgroup W} {r : ℕ}
    (hN : ∀ I : Subgroup W, N H I ⊥ → rk ↥I = r) (h : SumOfNat N H U ⊥ 2) : rk ↥U = 2 * r := by
  obtain ⟨I, -, hind, hsup, hnat⟩ := h
  have h01 : I 0 ⊓ I 1 = ⊥ := by
    have h0 := hind 0
    have h1 : I 1 ≤ ⊥ ⊔ ⨆ (j : Fin 2) (_ : j ≠ 0), I j :=
      le_sup_of_le_right (le_iSup₂_of_le (1 : Fin 2) (by decide) le_rfl)
    exact le_bot_iff.mp (le_trans (inf_le_inf_left _ h1) h0)
  have hU : I 0 ⊔ I 1 = U := by
    rw [← hsup, bot_sup_eq]
    apply le_antisymm
    · exact sup_le (le_iSup I 0) (le_iSup I 1)
    · exact iSup_le fun i => by fin_cases i <;> simp
  have h := rk_sup_add_rk_inf (I 0) (I 1)
  rw [h01, hU, rk_bot, hN _ (hnat 0), hN _ (hnat 1)] at h
  omega

end SumOfTwo



end CFSG.LocalAnalysis.UniquenessCase.PartTwo

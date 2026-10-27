module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcDefs
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3ExcRank

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
  CFSG.StandardType.RCKC1 CFSG.StandardType.GGFinModel CFSG.StandardType.LieCore
open CFSG.Open (StatedLieTag StatedLieAdmissible)

theorem rckExc_five_dvd_pred_or_succ {f : ℕ}
    (h : orderOf ((2 ^ f : ℕ) : ZMod 5) ≠ 4) : 5 ∣ 2 ^ f - 1 ∨ 5 ∣ 2 ^ f + 1 := by
  have hmod : ∀ k : ℕ, 2 ^ k % 5 = 1 ∨ 2 ^ k % 5 = 2 ∨ 2 ^ k % 5 = 3 ∨ 2 ^ k % 5 = 4 := by
    intro k
    induction k with
    | zero => left; norm_num
    | succ k ih => rw [pow_succ]; omega
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hpos : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have hne : 2 ^ f % 5 = 2 ∨ 2 ^ f % 5 = 3 := by
    rcases hmod f with h | h | h | h <;> omega
  apply h
  rcases hne with h2' | h3'
  · have hc : ((2 ^ f : ℕ) : ZMod 5) = 2 := by
      rw [← ZMod.natCast_mod, h2']
      rfl
    rw [hc]
    exact (orderOf_eq_iff (by norm_num)).2 ⟨by decide, by decide⟩
  · have hc : ((2 ^ f : ℕ) : ZMod 5) = 3 := by
      rw [← ZMod.natCast_mod, h3']
      rfl
    rw [hc]
    exact (orderOf_eq_iff (by norm_num)).2 ⟨by decide, by decide⟩

theorem rckExc_exists_corestrict_injective {X : Type} [Group X] {U : Type} [Group U]
    {ψ : U →* X} {G₀ : Subgroup X} (A : Subgroup X) (hrange : ψ.range = G₀)
    (hinj : Function.Injective ψ) :
    ∃ χ : U →* ↥(A ⊔ G₀), Function.Injective χ := by
  have hmem : ∀ u : U, ψ u ∈ A ⊔ G₀ := fun u => by
    have h1 : ψ u ∈ ψ.range := MonoidHom.mem_range.2 ⟨u, rfl⟩
    rw [hrange] at h1
    exact Subgroup.mem_sup_right h1
  refine ⟨ψ.codRestrict (A ⊔ G₀) hmem, fun u v huv => hinj ?_⟩
  exact congrArg Subtype.val huv

theorem rckExc_E8_floor
    {X : Type} [Group X] [Finite X] {n f : ℕ} {ψ : (ggU .E8 n f).K →* X} {p : ℕ}
    {G₀ A B₁ D J L R Rm K : Subgroup X} {e : X}
    (h : RCKRPConfig .E8 n f ψ p G₀ A B₁ D J L R Rm K e)
    (hp35 : p = 3 ∨ (p = 5 ∧ orderOf ((2 ^ f : ℕ) : ZMod 5) ≠ 4)) :
    p ^ 7 ≤ Nat.card A := by
  unfold RCKRPConfig at h
  rcases h with
    ⟨hGG, hOddG0, hp, hp2, hAel, hB1A, hDB1, hDcard, hAnorm, hMarkG0, hB1J, hB1Jc,
      hp4, hA2, hrank2, -⟩
  have := Fact.mk hp
  have hf : 1 ≤ f := hGG.1.1.2.1
  have hker : ψ.ker ≤ Subgroup.center (ggU .E8 n f).K := hGG.2.1.2
  have hrange : ψ.range = G₀ := hGG.2.1.1
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hZ : Subgroup.center (adjointGroup .E8 (GaloisField 2 f)) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans hZ.le
  obtain ⟨χ, hχ⟩ := rckExc_exists_corestrict_injective A hrange hinj
  have hp35' : p = 3 ∨ p = 5 := by
    rcases hp35 with h3 | ⟨h5, -⟩
    · exact Or.inl h3
    · exact Or.inr h5
  have hpq : p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1 := by
    rcases hp35 with h3 | ⟨h5, hord⟩
    · rw [h3]
      exact three_dvd_two_pow_pred_or_succ f
    · rw [h5]
      exact rckExc_five_dvd_pred_or_succ hord
  have h7 : 7 ≤ LargeEvenTwoLocalRank p ↥(A ⊔ G₀) := by
    rcases hpq with h | h
    · have hpK : p ∣ Nat.card (GaloisField 2 f) - 1 := by rw [hK]; exact h
      have h8 := ExcFrames.rank_le_twoLocalRank (τ := .E8) (by decide) hp hpK
        (TableBExc.isUnit_det_cartan_of_eq hp CFSG.LieType.Chevalley.det_cartan_E8
          (Nat.coprime_one_left p)) χ hχ
      exact le_trans (by decide) h8
    · have hpK : p ∣ Nat.card (GaloisField 2 f) + 1 := by rw [hK]; exact h
      have h8 := rank_pred_le_twoLocalRank_of_half (τ := .E8) hp χ hχ
        (ExcFramesHalf.ggExcHalfTwoLocalInput_E8 (GaloisField 2 f) p hp hp2 hpK hp35')
      exact le_trans (by decide) h8
  calc p ^ 7 ≤ p ^ LargeEvenTwoLocalRank p ↥(A ⊔ G₀) := Nat.pow_le_pow_right hp.pos h7
    _ ≤ Nat.card A := hrank2

theorem rckExc_E7_floor
    {X : Type} [Group X] [Finite X] {n f : ℕ} {ψ : (ggU .E7 n f).K →* X} {p : ℕ}
    {G₀ A B₁ D J L R Rm K : Subgroup X} {e : X}
    (h : RCKRPConfig .E7 n f ψ p G₀ A B₁ D J L R Rm K e) (hp3 : p = 3) :
    3 ^ 6 ≤ Nat.card A := by
  unfold RCKRPConfig at h
  rcases h with
    ⟨hGG, hOddG0, hp, hp2, hAel, hB1A, hDB1, hDcard, hAnorm, hMarkG0, hB1J, hB1Jc,
      hp4, hA2, hrank2, -⟩
  have := Fact.mk hp
  have hf : 1 ≤ f := hGG.1.1.2.1
  have hker : ψ.ker ≤ Subgroup.center (ggU .E7 n f).K := hGG.2.1.2
  have hrange : ψ.range = G₀ := hGG.2.1.1
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hZ : Subgroup.center
      ↥(CFSG.LieType.Steinberg.Minuscule.e7Data_valid.minGroup (GaloisField 2 f)) = ⊥ :=
    CFSG.SeitzReduction.E8Pilot.center_minGroup_e7_eq_bot
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans hZ.le
  obtain ⟨χ₀, hχ₀⟩ := rckExc_exists_corestrict_injective A hrange hinj
  set e7e := CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint (GaloisField 2 f) with he7e
  set χ : adjointGroup .E7 (GaloisField 2 f) →* ↥(A ⊔ G₀) := χ₀.comp e7e.symm.toMonoidHom with hχdef
  have hχ : Function.Injective χ := hχ₀.comp e7e.symm.injective
  have h6 : 6 ≤ LargeEvenTwoLocalRank p ↥(A ⊔ G₀) := by
    rcases three_dvd_two_pow_pred_or_succ f with h | h
    · have hpK : p ∣ Nat.card (GaloisField 2 f) - 1 := by rw [hK, hp3]; exact h
      have h7 := ExcFrames.rank_le_twoLocalRank (τ := .E7) (by decide) hp hpK
        (TableBExc.isUnit_det_cartan_of_eq hp CFSG.LieType.Chevalley.det_cartan_E7
          ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))) χ hχ
      exact le_trans (by decide) h7
    · have hpK : p ∣ Nat.card (GaloisField 2 f) + 1 := by rw [hK, hp3]; exact h
      have h7 := rank_pred_le_twoLocalRank_of_half (τ := .E7) hp χ hχ
        (ExcFramesHalf.ggExcHalfTwoLocalInput_E7 (GaloisField 2 f) p hp hp2 hpK (Or.inl hp3))
      exact le_trans (by decide) h7
  calc 3 ^ 6 = p ^ 6 := by rw [hp3]
    _ ≤ p ^ LargeEvenTwoLocalRank p ↥(A ⊔ G₀) := Nat.pow_le_pow_right hp.pos h6
    _ ≤ Nat.card A := hrank2

end CFSG.StandardType.RCKRP

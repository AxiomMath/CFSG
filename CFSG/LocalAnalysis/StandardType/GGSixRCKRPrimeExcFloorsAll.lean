module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcFloorsE
import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfTwoLocal

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
  CFSG.StandardType.RCKC1 CFSG.StandardType.GGFinModel CFSG.StandardType.LieCore
open CFSG.Open (StatedLieTag StatedLieAdmissible)

private theorem rckExc_E8_floor_data
    {X : Type} [Group X] [Finite X] {n f : ℕ} {ψ : (ggU .E8 n f).K →* X} {p : ℕ}
    {G₀ A B₁ D J L R Rm K : Subgroup X} {e : X}
    (h : RCKRPConfig .E8 n f ψ p G₀ A B₁ D J L R Rm K e) :
    p.Prime ∧ p ≠ 2 ∧ Nat.card (GaloisField 2 f) = 2 ^ f ∧
      (∃ χ : adjointGroup .E8 (GaloisField 2 f) →* ↥(A ⊔ G₀), Function.Injective χ) ∧
      p ^ LargeEvenTwoLocalRank p ↥(A ⊔ G₀) ≤ Nat.card A := by
  unfold RCKRPConfig at h
  rcases h with
    ⟨hGG, hOddG0, hp, hp2, hAel, hB1A, hDB1, hDcard, hAnorm, hMarkG0, hB1J, hB1Jc,
      hp4, hA2, hrank2, -⟩
  have hf : 1 ≤ f := hGG.1.1.2.1
  have hker : ψ.ker ≤ Subgroup.center (ggU .E8 n f).K := hGG.2.1.2
  have hrange : ψ.range = G₀ := hGG.2.1.1
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hZ : Subgroup.center (adjointGroup .E8 (GaloisField 2 f)) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans hZ.le
  exact ⟨hp, hp2, hK, rckExc_exists_corestrict_injective A hrange hinj, hrank2⟩

theorem rckExc_E8_floor_split
    {X : Type} [Group X] [Finite X] {n f : ℕ} {ψ : (ggU .E8 n f).K →* X} {p : ℕ}
    {G₀ A B₁ D J L R Rm K : Subgroup X} {e : X}
    (h : RCKRPConfig .E8 n f ψ p G₀ A B₁ D J L R Rm K e) (hpq : p ∣ 2 ^ f - 1) :
    p ^ 8 ≤ Nat.card A := by
  obtain ⟨hp, hp2, hK, ⟨χ, hχ⟩, hrank2⟩ := rckExc_E8_floor_data h
  have := Fact.mk hp
  have hpK : p ∣ Nat.card (GaloisField 2 f) - 1 := by rw [hK]; exact hpq
  have h8 := ExcFrames.rank_le_twoLocalRank (τ := .E8) (by decide) hp hpK
    (TableBExc.isUnit_det_cartan_of_eq hp CFSG.LieType.Chevalley.det_cartan_E8
      (Nat.coprime_one_left p)) χ hχ
  calc p ^ 8 ≤ p ^ LargeEvenTwoLocalRank p ↥(A ⊔ G₀) :=
        Nat.pow_le_pow_right hp.pos (le_trans (by decide) h8)
    _ ≤ Nat.card A := hrank2

theorem rckExc_E8_floor_half
    {X : Type} [Group X] [Finite X] {n f : ℕ} {ψ : (ggU .E8 n f).K →* X} {p : ℕ}
    {G₀ A B₁ D J L R Rm K : Subgroup X} {e : X}
    (h : RCKRPConfig .E8 n f ψ p G₀ A B₁ D J L R Rm K e) (hpq : p ∣ 2 ^ f + 1) :
    p ^ 7 ≤ Nat.card A := by
  obtain ⟨hp, hp2, hK, ⟨χ, hχ⟩, hrank2⟩ := rckExc_E8_floor_data h
  have := Fact.mk hp
  have hpK : p ∣ Nat.card (GaloisField 2 f) + 1 := by rw [hK]; exact hpq
  have h8 := rank_pred_le_twoLocalRank_of_half (τ := .E8) hp χ hχ
    (ExcFramesHalf.exists_twoLocal_of_frame TableBExcTwo.frameE8 hp hp2 hpK)
  calc p ^ 7 ≤ p ^ LargeEvenTwoLocalRank p ↥(A ⊔ G₀) :=
        Nat.pow_le_pow_right hp.pos (le_trans (by decide) h8)
    _ ≤ Nat.card A := hrank2

private theorem rckExc_E7_floor_data
    {X : Type} [Group X] [Finite X] {n f : ℕ} {ψ : (ggU .E7 n f).K →* X} {p : ℕ}
    {G₀ A B₁ D J L R Rm K : Subgroup X} {e : X}
    (h : RCKRPConfig .E7 n f ψ p G₀ A B₁ D J L R Rm K e) :
    p.Prime ∧ p ≠ 2 ∧ Nat.card (GaloisField 2 f) = 2 ^ f ∧
      (∃ χ : adjointGroup .E7 (GaloisField 2 f) →* ↥(A ⊔ G₀), Function.Injective χ) ∧
      p ^ LargeEvenTwoLocalRank p ↥(A ⊔ G₀) ≤ Nat.card A := by
  unfold RCKRPConfig at h
  rcases h with
    ⟨hGG, hOddG0, hp, hp2, hAel, hB1A, hDB1, hDcard, hAnorm, hMarkG0, hB1J, hB1Jc,
      hp4, hA2, hrank2, -⟩
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
  exact ⟨hp, hp2, hK, ⟨χ₀.comp e7e.symm.toMonoidHom, hχ₀.comp e7e.symm.injective⟩, hrank2⟩

theorem rckExc_E7_floor_split
    {X : Type} [Group X] [Finite X] {n f : ℕ} {ψ : (ggU .E7 n f).K →* X} {p : ℕ}
    {G₀ A B₁ D J L R Rm K : Subgroup X} {e : X}
    (h : RCKRPConfig .E7 n f ψ p G₀ A B₁ D J L R Rm K e) (hpq : p ∣ 2 ^ f - 1) :
    p ^ 7 ≤ Nat.card A := by
  obtain ⟨hp, hp2, hK, ⟨χ, hχ⟩, hrank2⟩ := rckExc_E7_floor_data h
  have := Fact.mk hp
  have hpK : p ∣ Nat.card (GaloisField 2 f) - 1 := by rw [hK]; exact hpq
  have h7 := ExcFrames.rank_le_twoLocalRank (τ := .E7) (by decide) hp hpK
    (TableBExc.isUnit_det_cartan_of_eq hp CFSG.LieType.Chevalley.det_cartan_E7
      ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))) χ hχ
  calc p ^ 7 ≤ p ^ LargeEvenTwoLocalRank p ↥(A ⊔ G₀) :=
        Nat.pow_le_pow_right hp.pos (le_trans (by decide) h7)
    _ ≤ Nat.card A := hrank2

theorem rckExc_E7_floor_half
    {X : Type} [Group X] [Finite X] {n f : ℕ} {ψ : (ggU .E7 n f).K →* X} {p : ℕ}
    {G₀ A B₁ D J L R Rm K : Subgroup X} {e : X}
    (h : RCKRPConfig .E7 n f ψ p G₀ A B₁ D J L R Rm K e) (hpq : p ∣ 2 ^ f + 1) :
    p ^ 6 ≤ Nat.card A := by
  obtain ⟨hp, hp2, hK, ⟨χ, hχ⟩, hrank2⟩ := rckExc_E7_floor_data h
  have := Fact.mk hp
  have hpK : p ∣ Nat.card (GaloisField 2 f) + 1 := by rw [hK]; exact hpq
  have h7 := rank_pred_le_twoLocalRank_of_half (τ := .E7) hp χ hχ
    (ExcFramesHalf.exists_twoLocal_of_frame TableBExcTwo.frameE7 hp hp2 hpK)
  calc p ^ 6 ≤ p ^ LargeEvenTwoLocalRank p ↥(A ⊔ G₀) :=
        Nat.pow_le_pow_right hp.pos (le_trans (by decide) h7)
    _ ≤ Nat.card A := hrank2

end CFSG.StandardType.RCKRP

module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusDefs
import CFSG.LocalAnalysis.StandardType.GGTableBExc
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusLift
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcToralRank

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley


theorem q2c_E8_rank {p d : ℕ} {lab : LargeEvenLabel} (hlab : lab.tag = .E8) (hp : p.Prime)
    (hp2 : p ≠ 2) (hsplit : LargeEvenSplit p lab) (hpd : p ∣ d) :
    LargeEvenLabelAll lab (fun R _ I _ =>
      ∀ A : Subgroup (MulAut R), IsElemAbelian p A → (∀ a ∈ A, a ∈ I) →
      (∀ r : ℕ, GGTorusLift p r R → p ^ r ≤ Nat.card A) →
      p ^ (d - 1) ≤ Nat.card A → Nat.card A ≤ p ^ d → p = 3 ∧ d = 9) := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at hlab
  subst hlab
  have hsplt : p ∣ 2 ^ n - 1 ∨ (n = 1 ∧ p = 3) :=
    (largeEvenSplit_E_iff (lab := ⟨.E8, l, n⟩) (Or.inr (Or.inr rfl))).mp hsplit
  haveI : Fact p.Prime := ⟨hp⟩
  intro Q hQ
  obtain ⟨K, _, _, hKcard, hQ'⟩ := hQ
  haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card hKcard
  refine ⟨K, inferInstance, inferInstance, hKcard, hQ', ?_⟩
  intro A hA hAI hbig hlo hup
  have hZ : Subgroup.center (TableBExc.RecipeGroup .E8 K) = ⊥ :=
    TableBExc.center_recipeGroup_eq_bot .E8 K
  let f : TableBExc.RecipeGroup .E8 K →* MulAut (TableBExc.RecipeGroup .E8 K) := MulAut.conj
  have hf : Function.Injective f :=
    CFSG.ComponentClassification.SmallLocal.mulAut_conj_injective hZ
  have hArange : A ≤ f.range := fun a ha => TableBExc.idImage_subset_inn_E8 K (hAI a ha)
  let A₀ : Subgroup (TableBExc.RecipeGroup .E8 K) := A.comap f
  have hcardA₀ : Nat.card A₀ = Nat.card A := by
    have hmap : A₀.map f = A := Subgroup.map_comap_eq_self hArange
    calc Nat.card A₀ = Nat.card (A₀.map f) := (Subgroup.card_map_of_injective hf).symm
      _ = Nat.card A :=
        congrArg (fun H : Subgroup (MulAut (TableBExc.RecipeGroup .E8 K)) => Nat.card ↥H) hmap
  have hA₀ : IsElemAbelian p A₀ := hA.comap hf
  let e : TableBExc.RecipeGroup .E8 K ≃* adjointGroup .E8 K := TableBExc.recipeEquiv .E8 K
  let A₁ : Subgroup (adjointGroup .E8 K) := A₀.map e.toMonoidHom
  have hA₁ : IsElemAbelian p A₁ := CFSG.SectionRank.isElemAbelian_map hA₀ e.toMonoidHom
  have hcardA₁ : Nat.card A₁ = Nat.card A₀ := Subgroup.card_map_of_injective e.injective
  have hcard_le : Nat.card A ≤ p ^ 8 := by
    have hrank : Tag.E8.rank = 8 := rfl
    rw [← hcardA₀, ← hcardA₁]
    rcases hsplt with hpq | ⟨hn1, hp3⟩
    · have hpq' : p ∣ Nat.card K - 1 := by rw [hKcard]; exact hpq
      have h := CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.card_le_pow_rank_of_E7_or_E8
        (Or.inr rfl) (K := K) hp hp2 hpq' hA₁
      rwa [hrank] at h
    · have hpqsq : p ∣ Nat.card K ^ 2 - 1 := by rw [hKcard, hn1, hp3]; norm_num
      have h :=
        CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.card_le_pow_rank_of_E7_or_E8_of_dvd_sq
        (Or.inr rfl) (K := K) hp hp2 hpqsq hA₁
      rwa [hrank] at h
  rcases hsplt with hpq | ⟨hn1, hp3⟩
  · have hpq' : p ∣ Nat.card K - 1 := by rw [hKcard]; exact hpq
    have hlower : p ^ 8 ≤ Nat.card A :=
      hbig 8 (TableBExc.ggTorusLift_E8 (K := K) hp hp2 hpq')
    have hd_ge : 8 ≤ d := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hlower.trans hup)
    have hd_le : d - 1 ≤ 8 := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hlo.trans hcard_le)
    have hd : d = 8 ∨ d = 9 := by omega
    rcases hd with rfl | rfl
    · exfalso
      have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (m := 2) (n := 3)
        (by rw [show (2 : ℕ) ^ 3 = 8 by norm_num]; exact hpd)
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
    · exact ⟨(Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
        (hp.dvd_of_dvd_pow (m := 3) (n := 2)
          (by rw [show (3 : ℕ) ^ 2 = 9 by norm_num]; exact hpd)), rfl⟩
  · have hpqPlus : p ∣ Nat.card K + 1 := by rw [hKcard, hn1, hp3]; norm_num
    have hlower : p ^ 7 ≤ Nat.card A :=
      hbig 7 (ggTorusLift_E8Plus (K := K) hp hp2 hpqPlus)
    have hd_ge : 7 ≤ d := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hlower.trans hup)
    have hd_le : d - 1 ≤ 8 := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hlo.trans hcard_le)
    have hd : d = 9 := by
      have hcases : d = 7 ∨ d = 8 ∨ d = 9 := by omega
      rcases hcases with rfl | rfl | rfl
      · rw [hp3] at hpd; exact absurd hpd (by norm_num)
      · rw [hp3] at hpd; exact absurd hpd (by norm_num)
      · rfl
    exact ⟨hp3, hd⟩

end CFSG.StandardType

module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusDefs
import CFSG.LocalAnalysis.StandardType.GGTableBExc
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusLift
import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.ExcE7
import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011LabUniq

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley


private theorem q2cE7_conj_injective {R : Type*} [Group R] (hZ : Subgroup.center R = ⊥) :
    Function.Injective (MulAut.conj : R →* MulAut R) := by
  intro x y hxy
  have h1 : MulAut.conj (x⁻¹ * y) = 1 := by
    rw [map_mul, map_inv, hxy, inv_mul_cancel]
  have hmem : x⁻¹ * y ∈ Subgroup.center R := by
    rw [Subgroup.mem_center_iff]
    intro r
    have h2 : MulAut.conj (x⁻¹ * y) r = r := by
      rw [h1]; rfl
    rw [MulAut.conj_apply] at h2
    calc r * (x⁻¹ * y) = ((x⁻¹ * y) * r * (x⁻¹ * y)⁻¹) * (x⁻¹ * y) := by rw [h2]
      _ = (x⁻¹ * y) * r := by group
  rw [hZ, Subgroup.mem_bot] at hmem
  have hyx : y = x := by
    calc y = x * (x⁻¹ * y) := by group
      _ = x := by rw [hmem, mul_one]
  exact hyx.symm

theorem q2c_E7_rank {p d : ℕ} {lab : LargeEvenLabel} (hlab : lab.tag = .E7) (hp : p.Prime)
    (hp2 : p ≠ 2) (hsplit : LargeEvenSplit p lab) (hpd : p ∣ d) :
    LargeEvenLabelAll lab (fun R _ I _ =>
      ∀ A : Subgroup (MulAut R), IsElemAbelian p A → (∀ a ∈ A, a ∈ I) →
      (∀ r : ℕ, GGTorusLift p r R → p ^ r ≤ Nat.card A) →
      p ^ (d - 1) ≤ Nat.card A → Nat.card A ≤ p ^ d →
      (p = 7 ∧ d = 7) ∨ (lab.n = 1 ∧ p = 3 ∧ d = 6)) := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at hlab
  subst hlab
  have hsplt : p ∣ 2 ^ n - 1 ∨ (n = 1 ∧ p = 3) :=
    (largeEvenSplit_E_iff (lab := ⟨.E7, l, n⟩) (Or.inr (Or.inl rfl))).mp hsplit
  haveI : Fact p.Prime := ⟨hp⟩
  intro Q hQ
  obtain ⟨K, _, _, hKcard, hQ'⟩ := hQ
  haveI : CharP K 2 := charP_two_of_card hKcard
  refine ⟨K, inferInstance, inferInstance, hKcard, hQ', ?_⟩
  intro A hA hAI hbig hlo hup
  have hZ : Subgroup.center (TableBExc.RecipeGroup .E7 K) = ⊥ :=
    TableBExc.center_recipeGroup_eq_bot .E7 K
  let f : TableBExc.RecipeGroup .E7 K →* MulAut (TableBExc.RecipeGroup .E7 K) := MulAut.conj
  have hf : Function.Injective f := q2cE7_conj_injective hZ
  have hArange : A ≤ f.range := fun a ha => TableBExc.idImage_subset_inn_E7 K (hAI a ha)
  let A₀ : Subgroup (TableBExc.RecipeGroup .E7 K) := A.comap f
  have hcardA₀ : Nat.card A₀ = Nat.card A := by
    have hmap : A₀.map f = A := Subgroup.map_comap_eq_self hArange
    calc Nat.card A₀ = Nat.card (A₀.map f) := (Subgroup.card_map_of_injective hf).symm
      _ = Nat.card A :=
        congrArg (fun H : Subgroup (MulAut (TableBExc.RecipeGroup .E7 K)) => Nat.card ↥H) hmap
  have hA₀ : IsElemAbelian p A₀ := hA.comap hf
  let e : TableBExc.RecipeGroup .E7 K ≃* adjointGroup Tag.E7 K := TableBExc.recipeEquiv .E7 K
  let A₁ : Subgroup (adjointGroup Tag.E7 K) := A₀.map e.toMonoidHom
  have hA₁ : IsElemAbelian p A₁ := CFSG.SectionRank.isElemAbelian_map hA₀ e.toMonoidHom
  have hcardA₁ : Nat.card A₁ = Nat.card A₀ := Subgroup.card_map_of_injective e.injective
  haveI : Finite (adjointGroup Tag.E7 K) :=
    CFSG.LieType.Chevalley.generated_group_finite Tag.E7 K
  have hcard_le : Nat.card A ≤ p ^ 7 := by
    obtain ⟨k, hk⟩ := hA₁.isPGroup.exists_card_eq
    have hk_le : k ≤ CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup Tag.E7 K)) :=
      CFSG.SectionRank.le_pRank hp.one_lt (H := ⊤) le_top hA₁ hk
    have hprank : CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup Tag.E7 K)) ≤ 7 := by
      rcases hsplt with hpq | ⟨hn1, hp3⟩
      · exact CFSG.LocalAnalysis.GLTheoremA.pRank_adjointGroup_E7_le_seven_of_dvd_sub_one K hp hp2
          (by rw [hKcard]; exact hpq)
      · have hcard2 : Nat.card K = 2 ^ 1 := by rw [hKcard, hn1]
        have hpqPlus : p ∣ Nat.card K + 1 := by rw [hKcard, hn1, hp3]; norm_num
        exact CFSG.LocalAnalysis.GLTheoremA.pRank_adjointGroup_E7_le_seven_of_dvd_add_one K 1
          hcard2 le_rfl hp hp2 hpqPlus
    rw [← hcardA₀, ← hcardA₁, hk]
    exact Nat.pow_le_pow_right hp.pos (hk_le.trans hprank)
  have hd_le : d - 1 ≤ 7 := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hlo.trans hcard_le)
  rcases hsplt with hpq | ⟨hn1, hp3⟩
  · have hpq' : p ∣ Nat.card K - 1 := by rw [hKcard]; exact hpq
    have hlower : p ^ 7 ≤ Nat.card A := hbig 7 (TableBExc.ggTorusLift_E7 hp hp2 hpq')
    have hd_ge : 7 ≤ d := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hlower.trans hup)
    have hd : d = 7 ∨ d = 8 := by omega
    rcases hd with rfl | rfl
    · left
      exact ⟨(Nat.prime_dvd_prime_iff_eq hp Nat.prime_seven).mp hpd, rfl⟩
    · exfalso
      have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (m := 2) (n := 3)
        (by rw [show (2 : ℕ) ^ 3 = 8 by norm_num]; exact hpd)
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  · have hpqPlus : p ∣ Nat.card K + 1 := by rw [hKcard, hn1, hp3]; norm_num
    have hlower : p ^ 6 ≤ Nat.card A := hbig 6 (ggTorusLift_E7Plus hp hp2 hpqPlus)
    have hd_ge : 6 ≤ d := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hlower.trans hup)
    have hd_cases : d = 6 ∨ d = 7 ∨ d = 8 := by omega
    rcases hd_cases with rfl | rfl | rfl
    · exact Or.inr ⟨hn1, hp3, rfl⟩
    · exfalso; rw [hp3] at hpd; exact (by norm_num : ¬ (3 ∣ 7)) hpd
    · exfalso; rw [hp3] at hpd; exact (by norm_num : ¬ (3 ∣ 8)) hpd

end CFSG.StandardType

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsOmegaK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOm.Isometry
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOm.Pull
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.OmegaMinusFour
public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
public import CFSG.LieType.Universal.SpinCenterMinus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOm.MinusCoords
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOm.MinusSylow
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOm.RootGroupGL
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdNatural.Pow3OmegaMinus
public import CFSG.ClassicalGroups.Orthogonal.RootGroupFixedCard
public import CFSG.GroupTheory.GL52.Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsComponents
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsSL3
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21b
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07
public import CFSG.Quasithin.Background.RealizesFaithful

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KOm

open CFSG.Open Matrix
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.ClassicalGroups.Orthogonal (rootGroupGL)
open CFSG.LieType.Universal.Spin (quadMinus)

local notation "ιM" => Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2

private lemma factorization_two_pow_mul_sub_one {n : ℕ} (hn : 2 ≤ n) :
    (((2 : ℕ) ^ n) ^ 2 * (((2 : ℕ) ^ n) ^ 4 - 1)).factorization 2 = 2 * n := by
  have h4ne : (2 : ℕ) ^ (n * 4) - 1 ≠ 0 := by
    have h1 : 1 < 2 ^ (n * 4) := Nat.one_lt_pow (by omega) (by norm_num)
    omega
  have hodd : Odd ((2 : ℕ) ^ (n * 4) - 1) := by
    have heven : Even ((2 : ℕ) ^ (n * 4)) := by
      rw [Nat.even_pow]
      exact ⟨by norm_num, by omega⟩
    exact Nat.Even.sub_odd Nat.one_le_two_pow heven (by norm_num)
  have hnotdvd : ¬ 2 ∣ (2 : ℕ) ^ (n * 4) - 1 := by
    rw [Nat.dvd_iff_mod_eq_zero]
    have h1 := hodd
    rw [Nat.odd_iff] at h1
    omega
  rw [← pow_mul, ← pow_mul]
  rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num)) h4ne]
  rw [Nat.factorization_pow]
  rw [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [Nat.factorization_eq_zero_of_not_dvd hnotdvd, Nat.prime_two.factorization_self]
  simp only [Nat.mul_one, Nat.add_zero]
  ring

theorem exists_minusModel {W : Type} [CommGroup W] [Finite W] {H : Subgroup (MulAut W)} {n : ℕ}
    {S : Sylow 2 ↥H} {Tstar : Subgroup (MulAut W)} (hF : OmegaMinusFrame H n S Tstar) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (b c : K),
      Nat.card K = 2 ^ n ∧ (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧
      ∃ (e : W ≃* Multiplicative (ιM → K)) (T : Subgroup (GL ιM K)),
        H = (StatedOmega (StatedQuadMinus 2 K b c)).map (glPull e) ∧
        Tstar = T.map (glPull e) ∧
        T ≤ isoFix (StatedQuadMinus 2 K b c) (KTabC.e1M K) ∧ IsPGroup 2 ↥T ∧
        rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K) ≤ T ∧
        CFSG.Quasithin.fixV ((S : Subgroup ↥H).map H.subtype) = linePull e (KTabC.e1M K) := by
  classical
  obtain ⟨K, hKfield, hKfin, hKchar, b, c, hKcard, hirr, e, hH, hT, hfixEq⟩ :=
    exists_minusCoords hF
  letI : Field K := hKfield
  letI : Finite K := hKfin
  letI : CharP K 2 := hKchar
  obtain ⟨hn, -, -, hT2, hST, hTfix⟩ := hF
  have hHeq : H = (StatedOmega (StatedQuadMinus 2 K b c)).map (glPull e) :=
    (eq_map_glPull_iff e).mp hH
  have hTrange : Tstar ≤ MonoidHom.range (glPull e) := by
    intro x hx
    have hx' : MulAut.congr e x ∈ Tstar.map (MulAut.congr e).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.congr e).toMonoidHom hx
    obtain ⟨A, -, hA⟩ := Subgroup.mem_map.mp (hT hx')
    exact ⟨A, (MulAut.congr e).injective (by rw [congr_glPull, hA])⟩
  let T : Subgroup (GL ιM K) := Tstar.comap (glPull e)
  have hTmap : T.map (glPull e) = Tstar := Subgroup.map_comap_eq_self hTrange
  have hTleIso : T ≤ isoFix (StatedQuadMinus 2 K b c) (KTabC.e1M K) := by
    intro A hA
    have h1 : s16gNatHom ιM K A ∈
        (isoFix (StatedQuadMinus 2 K b c) (KTabC.e1M K) ⊓
          Subgroup.normalizer
            ((StatedOmega (StatedQuadMinus 2 K b c) : Subgroup (GL ιM K)) :
              Set (GL ιM K))).map (s16gNatHom ιM K) := by
      have h2 : MulAut.congr e (glPull e A) ∈ Tstar.map (MulAut.congr e).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hA
      rw [congr_glPull] at h2
      exact hT h2
    exact ((Subgroup.mem_map_iff_mem s16gNatHom_injective).mp h1).1
  have hTiso : ↥T ≃* ↥Tstar :=
    (T.equivMapOfInjective (glPull e) (glPull_injective e)).trans
      (MulEquiv.subgroupCongr hTmap)
  have hT2' : IsPGroup 2 ↥T := IsPGroup.of_equiv hT2 hTiso.symm
  have hℓ : CFSG.Quasithin.fixV ((S : Subgroup ↥H).map H.subtype) =
      linePull e (KTabC.e1M K) := by
    apply Subgroup.ext
    intro w
    exact (hfixEq w).trans mem_linePull.symm
  have hUT : rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K) ≤ T := by
    let P : Subgroup (MulAut W) := (S : Subgroup ↥H).map H.subtype
    let S' : Subgroup (GL ιM K) := P.comap (glPull e)
    have hPleH : P ≤ H := Subgroup.map_subtype_le (S : Subgroup ↥H)
    have hS'T : S' ≤ T := fun A hA => hST hA
    have hS'Γ : S' ≤ StatedOmega (StatedQuadMinus 2 K b c) := by
      intro A hA
      have hmemH : glPull e A ∈ H := hPleH hA
      rw [hHeq] at hmemH
      obtain ⟨B, hB, hBA⟩ := Subgroup.mem_map.mp hmemH
      rw [glPull_injective e hBA] at hB
      exact hB
    have hS'fix : ∀ A ∈ S', (A : Matrix ιM ιM K) *ᵥ KTabC.e1M K = KTabC.e1M K := by
      intro A hA
      let w₁ : W := e.symm (Multiplicative.ofAdd (KTabC.e1M K))
      have hw₁ : w₁ ∈ CFSG.Quasithin.fixV ((S : Subgroup ↥H).map H.subtype) := by
        rw [hℓ]
        exact mem_linePull.mpr ⟨1, by rw [MulEquiv.apply_symm_apply, toAdd_ofAdd, one_smul]⟩
      have hfx : glPull e A w₁ = w₁ := hTfix (glPull e A) (hST hA) w₁ hw₁
      have h1 := toAdd_glPull_apply e A w₁
      rw [hfx] at h1
      have h2 : Multiplicative.toAdd (e w₁) = KTabC.e1M K := by
        rw [MulEquiv.apply_symm_apply, toAdd_ofAdd]
      rw [h2] at h1
      exact h1.symm
    have hP_range : P ≤ MonoidHom.range (glPull e) := by
      intro p hp
      have hpΓ : p ∈ (StatedOmega (StatedQuadMinus 2 K b c)).map (glPull e) := by
        rw [← hHeq]
        exact hPleH hp
      obtain ⟨A, -, hAp⟩ := Subgroup.mem_map.mp hpΓ
      exact ⟨A, hAp⟩
    have hS'map : S'.map (glPull e) = P := Subgroup.map_comap_eq_self hP_range
    have hcardS'P : Nat.card ↥S' = Nat.card ↥P := by
      rw [← hS'map]
      exact (Subgroup.card_map_of_injective (glPull_injective e)).symm
    have hcardPS : Nat.card ↥P = Nat.card ↥S :=
      Subgroup.card_map_of_injective H.subtype_injective
    have hHcard : Nat.card ↥H = Nat.card K ^ 2 * (Nat.card K ^ 4 - 1) := by
      rw [hHeq, Subgroup.card_map_of_injective (glPull_injective e)]
      exact KOrdNat.card_statedOmega_quadMinus_two_eq hirr
    have hq : Nat.card K = 2 ^ n := hKcard
    have hfac : (Nat.card ↥H).factorization 2 = 2 * n := by
      rw [hHcard, hq]
      exact factorization_two_pow_mul_sub_one hn
    have hSfac : Nat.card (S : Subgroup ↥H) = 2 ^ (2 * n) := by
      have h := S.card_eq_multiplicity
      rw [hfac] at h
      exact h
    have hS'card2 : Nat.card ↥S' = 2 ^ (2 * n) := by
      rw [hcardS'P]
      exact hcardPS.trans hSfac
    have hS'2 : IsPGroup 2 ↥S' := IsPGroup.iff_card.mpr ⟨2 * n, hS'card2⟩
    have hQ : (QuadraticMap.polarBilin (quadMinus 2 K b c)).Nondegenerate :=
      CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 2 K hirr
    have hS'U : S' ≤ rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K) :=
      le_rootGroupGL_of_le_statedOmega hirr hS'Γ hS'fix hS'2
    have hUcard : Nat.card ↥(rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K)) =
        Nat.card K ^ 2 := by
      have h := card_rootGroupGL (Q := quadMinus 2 K b c) hQ
        (quadMinus_e1M b c) e1M_ne_zero
      rw [show Fintype.card ιM = 4 by simp] at h
      simpa using h
    have hUcard2 : Nat.card ↥(rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K)) =
        Nat.card ↥S' := by
      rw [hUcard, hq, hS'card2, ← pow_mul]
      congr 1
      ring
    have hS'eqU : S' = rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K) :=
      Subgroup.eq_of_le_of_card_ge hS'U (le_of_eq hUcard2)
    rw [← hS'eqU]
    exact hS'T
  refine ⟨K, hKfield, hKfin, hKchar, b, c, hKcard, hirr, ?_⟩
  exact ⟨e, T, hHeq, hTmap.symm, hTleIso, hT2', hUT, hℓ⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.KOm

end

module

public import CFSG.Quasithin.AppendixH.H9.H93.Theta
public import CFSG.Quasithin.AppendixH.H9.H92.Part2
public import CFSG.Quasithin.AppendixH.H9.H92.RadConj
public import CFSG.Quasithin.AppendixH.H9.H92.CoreRad
public import CFSG.Quasithin.AppendixH.H9.H92.Classify
public import CFSG.Quasithin.AppendixH.H9.H92.FixComm
public import CFSG.Quasithin.AppendixH.H9.H92.Gamma

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

private theorem card_eq_two_pow_rk_of_isElemAbelian2 (A : Subgroup (MulAut (PairN 5)))
    (hab : IsElemAbelian2 A) : Nat.card A = 2 ^ rk ↥A := by
  have hP : IsPGroup 2 A := isPGroup_two_of_sq_eq_one (fun a : A =>
    Subtype.ext (hab.2 (a : MulAut (PairN 5)) a.2))
  exact card_eq_two_pow_of_isPGroup hP

private theorem conjAut_le_Mg {g : MulAut (PairN 5)} (hg : g ∈ Mg 5)
    {A : Subgroup (MulAut (PairN 5))} (hA : A ≤ Mg 5) : conjAut g A ≤ Mg 5 := by
  intro (x : MulAut (PairN 5)) hx
  have h1 : g⁻¹ * x * g ∈ A := mem_conjAut.mp hx
  have h2 : g * (g⁻¹ * x * g) * g⁻¹ ∈ Mg 5 :=
    (Mg 5).mul_mem ((Mg 5).mul_mem hg (hA h1)) ((Mg 5).inv_mem hg)
  have h3 : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
  rwa [h3] at h2

private theorem conjAut_inv_conjAut' {V : Type*} [CommGroup V] (g : MulAut V)
    (A : Subgroup (MulAut V)) : conjAut g⁻¹ (conjAut g A) = A := by
  rw [← conjAut_mul, inv_mul_cancel, conjAut_one]

private theorem part345 (U : Subgroup (PairN 5)) (hU : U ≤ V1n 5) (hrk : rk ↥U = 3)
    (A₀ : Subgroup (MulAut (PairN 5))) (hA₀ : A₀ = RadV1 5 U) :
    ((∀ B : Subgroup (MulAut (PairN 5)),
          (∃ g ∈ Mg 5, B = conjAut g A₀) ↔
            (B ≤ Mg 5 ∧ IsElemAbelian2 B ∧ Nat.card B = 64)) ∧
        (∀ A : Subgroup (MulAut (PairN 5)), A ≤ Mg 5 → IsElemAbelian2 A → rk ↥A = 5 →
          ∃ g ∈ Mg 5, conjAut g A ≤ A₀ ∧ Nat.card (conjAut g A) * 2 = Nat.card A₀)) ∧
      (∀ A : Subgroup (MulAut (PairN 5)), A ≤ A₀ → Nat.card A * 2 = Nat.card A₀ →
          fixV A = commV A ∧ commV A = fixV A₀ ∧ fixV A₀ = commV A₀ ∧
          commV A₀ = U ⊔ (V2n 5 ⊓ perpN 5 U) ∧ rk ↥(U ⊔ (V2n 5 ⊓ perpN 5 U)) = 5) ∧
      (∀ A : Subgroup (MulAut (PairN 5)), A ≤ Mg 5 → IsElemAbelian2 A → 5 ≤ rk ↥A →
        E3.gammaCheck 3 A = ⊤) := by
  subst hA₀
  have hRc : Nat.card (RadV1 5 U) = 64 := card_radV1 U hU (Or.inr hrk)
  have hRab : IsElemAbelian2 (RadV1 5 U) := isElemAbelian2_radV1 5 U
  have hRM : RadV1 5 U ≤ Mg 5 := (RadV1_le_Lg 5 U).trans Lg_le_Mg
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  ·
    intro B
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨conjAut_le_Mg hg hRM, (isElemAbelian2_conjAut_iff g _).mpr hRab,
        (card_conjAut g _).trans hRc⟩
    · rintro ⟨hBM, hBab, hBc⟩
      have hpow : 2 ^ rk ↥B = 2 ^ 6 := by
        rw [← card_eq_two_pow_rk_of_isElemAbelian2 B hBab, hBc]
        norm_num
      have hr6 : rk ↥B = 6 := Nat.pow_right_injective le_rfl hpow
      have hBL : B ≤ Lg 5 := le_Lg_of_five_le_rk B hBM hBab (by omega)
      obtain ⟨D, hD, hDr, hBD⟩ := exists_radV1_of_card_ge B hBL hBab (by omega)
      have hDc : Nat.card (RadV1 5 D) = 64 := card_radV1 D hD hDr
      have hBeq : B = RadV1 5 D := Subgroup.eq_of_le_of_card_ge hBD (by omega)
      obtain ⟨g, hg, hgc⟩ := exists_conj_radV1 U D hU hD hrk hDr
      exact ⟨g⁻¹, (Mg 5).inv_mem hg,
        hBeq.trans ((conjAut_inv_conjAut' g (RadV1 5 D)).symm.trans
          (congrArg (conjAut g⁻¹) hgc))⟩
  ·
    intro A hAM hAab hr5
    have hAc : Nat.card A = 32 := by
      rw [card_eq_two_pow_rk_of_isElemAbelian2 A hAab, hr5]
      norm_num
    have hAL : A ≤ Lg 5 := le_Lg_of_five_le_rk A hAM hAab (by omega)
    obtain ⟨D, hD, hDr, hAD⟩ := exists_radV1_of_card_ge A hAL hAab (by omega)
    obtain ⟨g, hg, hgc⟩ := exists_conj_radV1 U D hU hD hrk hDr
    refine ⟨g, hg, (conjAut_mono g hAD).trans (le_of_eq hgc), ?_⟩
    have h1 : Nat.card ↥(conjAut g A) = Nat.card A := card_conjAut g A
    omega
  ·
    intro A hA hcard
    exact fixV_commV_radV1_hyperplane U hU hrk A hA hcard
  ·
    intro A hAM hAab h5
    have hAL : A ≤ Lg 5 := le_Lg_of_five_le_rk A hAM hAab h5
    have hAc : 32 ≤ Nat.card A := by
      rw [card_eq_two_pow_rk_of_isElemAbelian2 A hAab]
      calc 32 = 2 ^ 5 := by norm_num
        _ ≤ 2 ^ rk ↥A := Nat.pow_le_pow_right (by norm_num) h5
    obtain ⟨D, hD, hDr, hAD⟩ := exists_radV1_of_card_ge A hAL hAab hAc
    exact gammaCheck_three_eq_top_of_le_radV1 D hD hDr A hAD

theorem h92_main :
  ((∀ t ∈ Mg 5, ∀ t' ∈ Mg 5, t ∉ Lg 5 → t' ∉ Lg 5 → orderOf t = 2 → orderOf t' = 2 →
      IsConjIn (Mg 5) t t') ∧
    (∀ t ∈ Mg 5, t ∉ Lg 5 → orderOf t = 2 →
      ThetaIso 5 t ∧
      G6.IsSymNatural (Lg 5 ⊓ Subgroup.centralizer ({t} : Set (MulAut (PairN 5))))
        (commOn (fixV (Subgroup.zpowers t))
          (Lg 5 ⊓ Subgroup.centralizer ({t} : Set (MulAut (PairN 5))))) 6 ∧
      ∃ v ∈ fixV (Subgroup.zpowers t), pairQn 5 v = 1 ∧
        (∀ g ∈ Lg 5 ⊓ Subgroup.centralizer ({t} : Set (MulAut (PairN 5))), g v = v) ∧
        fixV (Subgroup.zpowers t) =
          Subgroup.zpowers v ⊔ commOn (fixV (Subgroup.zpowers t))
            (Lg 5 ⊓ Subgroup.centralizer ({t} : Set (MulAut (PairN 5)))) ∧
        Subgroup.zpowers v ⊓ commOn (fixV (Subgroup.zpowers t))
            (Lg 5 ⊓ Subgroup.centralizer ({t} : Set (MulAut (PairN 5)))) = ⊥)) ∧
  (∀ A : Subgroup (MulAut (PairN 5)), A ≤ Mg 5 → IsElemAbelian2 A → 5 ≤ rk ↥A → A ≤ Lg 5) ∧
  ∀ T : Subgroup (MulAut (PairN 5)), IsSylowIn 2 T (Mg 5) →
  ∀ U : Subgroup (PairN 5), U ≤ V1n 5 → rk ↥U = 3 →
    (∀ g ∈ T ⊓ stabSub (V1n 5), ∀ u ∈ U, g u ∈ U) →
      ((∀ B : Subgroup (MulAut (PairN 5)),
          (∃ g ∈ Mg 5, B = conjAut g (CFSG.Open.pCoreOf 2 (Lg 5 ⊓ stabSub U))) ↔
            (B ≤ Mg 5 ∧ IsElemAbelian2 B ∧ Nat.card B = 64)) ∧
        (∀ A : Subgroup (MulAut (PairN 5)), A ≤ Mg 5 → IsElemAbelian2 A → rk ↥A = 5 →
          ∃ g ∈ Mg 5, conjAut g A ≤ CFSG.Open.pCoreOf 2 (Lg 5 ⊓ stabSub U) ∧
            Nat.card (conjAut g A) * 2 = Nat.card (CFSG.Open.pCoreOf 2 (Lg 5 ⊓ stabSub U)))) ∧
      (∀ A : Subgroup (MulAut (PairN 5)), A ≤ CFSG.Open.pCoreOf 2 (Lg 5 ⊓ stabSub U) →
        Nat.card A * 2 = Nat.card (CFSG.Open.pCoreOf 2 (Lg 5 ⊓ stabSub U)) →
          fixV A = commV A ∧ commV A = fixV (CFSG.Open.pCoreOf 2 (Lg 5 ⊓ stabSub U)) ∧
          fixV (CFSG.Open.pCoreOf 2 (Lg 5 ⊓ stabSub U)) = commV (CFSG.Open.pCoreOf 2 (Lg 5 ⊓ stabSub U)) ∧
          commV (CFSG.Open.pCoreOf 2 (Lg 5 ⊓ stabSub U)) = U ⊔ (V2n 5 ⊓ perpN 5 U) ∧
          rk ↥(U ⊔ (V2n 5 ⊓ perpN 5 U)) = 5) ∧
      (∀ A : Subgroup (MulAut (PairN 5)), A ≤ Mg 5 → IsElemAbelian2 A → 5 ≤ rk ↥A →
        E3.gammaCheck 3 A = ⊤) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  ·
    intro t ht t' ht' htL ht'L ht2 ht'2
    obtain ⟨g, hg, hgt⟩ := isConjIn_swap_of_outer_involution t ht htL ht2
    obtain ⟨g', hg', hgt'⟩ := isConjIn_swap_of_outer_involution t' ht' ht'L ht'2
    refine ⟨g' * g⁻¹, (Mg 5).mul_mem hg' ((Mg 5).inv_mem hg), ?_⟩
    rw [← hgt, ← hgt']
    group
  ·
    intro t ht htL ht2
    exact ⟨thetaIso_of_outer_involution 5 t ht htL ht2,
      isSymNatural_of_outer_involution t ht htL ht2,
      exists_nonsingular_vec_of_outer_involution t ht htL ht2⟩
  ·
    exact fun A hA hab h5 => le_Lg_of_five_le_rk A hA hab h5
  · intro T hT U hU hrk hinv
    exact part345 U hU hrk _ (pCoreOf_stabSub_eq_radV1 U hU hrk)

end CFSG.ASVolI.ChH

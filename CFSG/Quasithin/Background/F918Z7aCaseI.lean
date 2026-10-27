module

public import CFSG.Quasithin.Background.F918Z7aTwo
public import CFSG.Quasithin.Background.F918Z7aRank
public import CFSG.Quasithin.Background.F918Z7aTypes
public import CFSG.Quasithin.Background.F918Z2Swap
public import CFSG.Quasithin.Background.F918Z4a
public import CFSG.Quasithin.Background.F918Z4bL2
public import CFSG.Quasithin.Background.F918Z4bSz
public import CFSG.Quasithin.Background.F918Z4bJ1
public import CFSG.Quasithin.Background.F918Z4bPrime

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank

theorem caseI_concl
    {V : Type} [CommGroup V] [Finite V] {D X G T' : Subgroup (MulAut V)} {s : MulAut V}
    (hZ : Z37 D X G T' s) {A : Subgroup (MulAut V)} (hA : A ∈ QhatStar G) (hAT : A ≤ T')
    {t : MulAut V} (htA : t ∈ A) (htD : ¬ D.map (MulAut.conj t).toMonoidHom = D) :
    Z37Concl D X := by
  obtain ⟨r, -, hr2, hAr, -⟩ := QhatStar_spec hA
  have hA2 : IsA2 G A := hAr.1.1
  have hAe : IsElemAbelian2 A := hA2.isElemAbelian2
  have hAV : rkIdx (fixV A) ≤ 2 * rk A := by
    have h1 : rAV A * (rk A : ℚ) = (rkIdx (fixV A) : ℚ) := hA2.rAV_mul
    have h2 : rAV A = r := hAr.1.2
    rw [h2] at h1
    have h3 : (rkIdx (fixV A) : ℚ) ≤ 2 * (rk A : ℚ) := by
      rw [← h1]
      exact mul_le_mul_of_nonneg_right hr2 (Nat.cast_nonneg _)
    exact_mod_cast h3
  have ht2 : t * t = 1 := by
    have := hAe.2 t htA
    rwa [pow_two] at this
  have htT : t ∈ T' := hAT htA
  have hperm : ∀ a ∈ A, D.map (MulAut.conj a).toMonoidHom = D ∨
      D.map (MulAut.conj a).toMonoidHom = X := fun a ha => hZ.T_perm a (hAT ha)
  have htX : D.map (MulAut.conj t).toMonoidHom = X := (hZ.T_perm t htT).resolve_left htD
  have hZt : Z37 D X G T' t := Z7a.z37_of_swap hZ htT ht2 htX
  have := hZt.nontrivial
  obtain ⟨F, _, _, _, d, β, ρ, σ, ϑ, Q, R, hd, hM, hQ, hR, hform⟩ :=
    hasSqModel_swap_form hZt.exp hZt.comm hZt.irr hZt.swapDX hZt.swapXD
  rcases Nat.lt_or_ge d 3 with hlt | hd3
  ·
    have hd12 : d = 1 ∨ d = 2 := by omega
    rcases hd12 with rfl | rfl
    · exact (z37_dim_ne_one hZ β ρ σ hM).elim
    · exact z37Concl_of_sqModel_two hZ β ρ σ hM
  obtain ⟨e, he1, hF⟩ := Z4e.exists_card_eq_two_pow (K := F)
  have hrk : d * (d - 1) * e / 2 ≤ rkIdx (fixV (Subgroup.zpowers t)) :=
    rkIdx_fixV_swap_ge hF β ϑ Q R hQ hR hform ht2
  have key : ∀ m : ℕ, 1 ≤ m → AutRankLe ↥D m → d * (d - 1) * e ≤ 4 * m + 2 := by
    intro m hm hAut
    have h := Z7a.le_two_mul_add_one_of_swap hZt ht2 hAe htA hperm hAV hm hAut hrk
    have := Z7a.mul_pred_mul_le_of_div_le d e h
    omega
  have hρ := hM.rho_injective
  rcases Z7a.a38_cases hZ.typeD with ⟨n, hn, hL⟩ | ⟨n, hn, hL⟩ | hL | ⟨p, hp, hp7, hL⟩
  · exact (Z7a.false_of_psl2_two hn hL hF ρ hρ hd3
      (key n (by omega) (autRankLe_psl2_two hn hL))).elim
  · exact (Z7a.false_of_sz hn hL hF ρ hρ hd3
      (key (2 * n - 1) (by omega) (autRankLe_sz hn hL))).elim
  · exact (Z7a.false_of_j1 hL hF ρ hρ hd3 (key 3 (by omega) (autRankLe_j1 hL))).elim
  · have hKI := key 2 (by omega) (autRankLe_psl2_prime hp hp7 hL)
    obtain ⟨rfl, rfl⟩ := Z7a.numeric_Lp hd3 he1 hKI
    have hF2 : Nat.card F = 2 := by simpa using hF
    have hDpsl : IsPSL 3 2 1 ↥D := Z7a.isPSL_three_two_of_psl2_prime hp hp7 hL hF2 ρ hρ
    have hXpsl : IsPSL 3 2 1 ↥X := isPSL_congr (conjEquivOfEq hZ.swapDX) hDpsl
    exact Or.inr ⟨hDpsl, tensorNatL32_of_sqModel_three hZ.comm hF2 β ρ σ hM hDpsl hXpsl⟩

end CFSG.Quasithin

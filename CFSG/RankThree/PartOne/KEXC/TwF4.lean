module

public import CFSG.RankThree.PartOne.KEXC.SectorKey
public import CFSG.RankThree.PartOne.KEXC.RootTable
public import CFSG.RankThree.PartOne.KF.ClsExcRank
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.RankThree.PartOne.KLR.SectorOrder
public import CFSG.RankThree.PartOne.KLR.SectorSixTwelve

public section

namespace CFSG.RankThree.PartOne.KEXC

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.RF4 CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KLR CFSG.RankThree.LargeReeOrder CFSG

section Odd

theorem odd_mPhi2 (a : ℕ) : Odd (mPhi2 a) := by
  unfold mPhi2
  exact Even.add_one (Nat.even_pow.2 ⟨even_two, by omega⟩)

theorem odd_mPhi4m (a : ℕ) : Odd (mPhi4m a) := by
  unfold mPhi4m
  have h2 : 2 ∣ 2 ^ (2 * a + 1) := dvd_pow_self 2 (by omega)
  have h2' : 2 ∣ 2 ^ (a + 1) := dvd_pow_self 2 (by omega)
  have hle : 2 ^ (a + 1) ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [Nat.odd_iff]
  omega

theorem odd_mPhi4p (a : ℕ) : Odd (mPhi4p a) := by
  unfold mPhi4p
  have h2 : 2 ∣ 2 ^ (2 * a + 1) := dvd_pow_self 2 (by omega)
  have h2' : 2 ∣ 2 ^ (a + 1) := dvd_pow_self 2 (by omega)
  rw [Nat.odd_iff]
  omega

end Odd

section NoPlane

variable
  {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}

theorem no_plane_reeGamma (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : ¬ p ∣ 2 ^ (2 * a + 1) - 1)
    {U E : Subgroup (ReeTag.F4.reeGamma K a)} (hU2 : IsPGroup 2 U) (hU0 : U ≠ ⊥)
    (hE : IsElementaryAbelian p E) (hEc : Nat.card E = p ^ 2)
    (hEU : E ≤ Subgroup.normalizer (U : Set (ReeTag.F4.reeGamma K a))) : False := by
  classical
  have hp3 : 3 < p := by omega
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have hpq' : ¬ p ∣ Nat.card K - 1 := by rw [hK]; exact hpq
  have hdvd : p ∣ Nat.card (ReeTag.F4.reeGamma K a) :=
    (dvd_pow_self p two_ne_zero).trans (hEc ▸ Subgroup.card_subgroup_dvd_card E)
  obtain ⟨e, he, he1, t, htU, ht1, ht2, het⟩ :=
    exists_centralizing_involution hp hp2 hU2 hU0 hE hEc hEU
  have hsix : (p ∣ (2 ^ (2 * a + 1)) ^ 2 - 2 ^ (2 * a + 1) + 1 ∨
      p ∣ (2 ^ (2 * a + 1)) ^ 4 - (2 ^ (2 * a + 1)) ^ 2 + 1) → False := by
    intro h
    have hep : orderOf e = p := orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian e he) he1
    have h2 := not_two_dvd_card_centralizer_of_sixTwelve ha hK hp hp3 h e hep
    apply h2
    have htc : t ∈ Subgroup.centralizer ({e} : Set (ReeTag.F4.reeGamma K a)) :=
      Subgroup.mem_centralizer_singleton_iff.2 het.symm
    have ht2' : orderOf t = 2 := orderOf_eq_prime ht2 ht1
    have := Subgroup.orderOf_dvd_natCard _ htc
    rw [ht2'] at this
    exact this
  obtain ⟨D⟩ := reeFrameData_nonempty (K := K) (L := AlgebraicClosure K) hK
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  rcases (large_Ree_exact_native_order_and_prime_factor_exhaustion a K hK).2 p hp hp3 hdvd with
    h1 | h2 | h3 | h4 | h5
  · exact hpq h1
  · exact sector_no_plane D ha hK (odd_mPhi2 a) (torusParam_phi2 D.isFrob) hp hp3 hpq' h2
      (pow_factorization_card_reeGamma_dvd_phi2 hK hp hp3 h2)
      (fun α hα => hroots_phi2 a hp h2 hα) hU2 hU0 hE hEc hEU
  · rcases dvd_phi4_cases hp hp3 h3 with ⟨hpp, -⟩ | ⟨hpm, -⟩
    · exact sector_no_plane D ha hK (odd_mPhi4p a) (torusParam_phi4p D.isFrob) hp hp3 hpq' hpp
        (pow_factorization_card_reeGamma_dvd_phi4p hK hp hp3 hpp)
        (fun α hα => hroots_phi4p a hp hpp hα) hU2 hU0 hE hEc hEU
    · exact sector_no_plane D ha hK (odd_mPhi4m a) (torusParam_phi4m D.isFrob) hp hp3 hpq' hpm
        (pow_factorization_card_reeGamma_dvd_phi4m hK hp hp3 hpm)
        (fun α hα => hroots_phi4m a hp hpm hα) hU2 hU0 hE hEc hEU
  · exact hsix (Or.inl h4)
  · exact hsix (Or.inr h5)

end NoPlane

theorem kf123ExcTwF4NoRankTwo_holds :
    CFSG.RankThree.PartOne.KF123ExcTwF4NoRankTwo := by
  intro X _ _ f hX p hp hp5 hpq
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, K, _, _, _, ha, hfa, hK, ⟨e⟩⟩ := exists_gamma_of_model hX
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  have hpq' : ¬ p ∣ 2 ^ (2 * a + 1) - 1 := by rw [← hfa]; exact hpq
  refine localRank_le_one_of_no_plane hp ?_
  intro U hU2 hU0 E hEU hE hEc
  have : IsElementaryAbelian p E := hE
  exact no_plane_reeGamma ha hK' hp hp5 hpq' (U := U.map e.toMonoidHom) (E := E.map e.toMonoidHom)
    (hU2.map _) (fun h => hU0 ((Subgroup.map_eq_bot_iff_of_injective U e.injective).1 h))
    (IsElementaryAbelian.map _) (by rw [Subgroup.card_map_of_injective e.injective]; exact hEc)
    (by rw [← Subgroup.map_equiv_normalizer_eq]; exact Subgroup.map_mono hEU)

end CFSG.RankThree.PartOne.KEXC

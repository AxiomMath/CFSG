module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2Defs
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2FinGen
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2FinInv
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2FinL3
public import CFSG.Quasithin.EmptyFaithful.S152He4Layer
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSylowNormalizer

public section

namespace CFSG.Quasithin.E9P2.FinInst

open CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

theorem upperTriangular_eq_unitriangular (n : ℕ) :
    upperTriangular n (ZMod 2) = unitriangular n (ZMod 2) := by
  apply le_antisymm
  · intro A hA
    refine ⟨hA, fun i => ?_⟩
    have hdet : (A : Matrix (Fin n) (Fin n) (ZMod 2)).det =
        ∏ i, (A : Matrix (Fin n) (Fin n) (ZMod 2)) i i :=
      det_of_isUpperTriangular (mem_upperTriangular_iff_isUpperTriangular.1 hA)
    rw [A.prop] at hdet
    have hne : (A : Matrix (Fin n) (Fin n) (ZMod 2)) i i ≠ 0 := by
      intro h0
      rw [Finset.prod_eq_zero (f := fun j => (A : Matrix (Fin n) (Fin n) (ZMod 2)) j j)
        (Finset.mem_univ i) h0] at hdet
      exact one_ne_zero hdet
    revert hne
    generalize (A : Matrix (Fin n) (Fin n) (ZMod 2)) i i = x
    revert x
    decide
  · exact fun A hA => hA.1

theorem isSylowTwoOf_unitriangular {n : ℕ} (hn : 1 ≤ n) :
    IsSylowTwoOf (unitriangular n (ZMod 2)) ⊤ := by
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := ZMod 2) 2 hn
  rw [← hP]
  exact E9P2.FinInv.isSylowTwoOf_top_of_sylow P

theorem normalizer_unitriangular_eq (n : ℕ) :
    Subgroup.normalizer (unitriangular n (ZMod 2) : Set (SpecialLinearGroup (Fin n) (ZMod 2))) =
      unitriangular n (ZMod 2) := by
  rw [normalizer_unitriangular, upperTriangular_eq_unitriangular]

theorem card_eq_of_isSylowTwoOf {n : ℕ} (hn : 1 ≤ n)
    {U : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))} (hU : IsSylowTwoOf U ⊤) :
    Nat.card U = 2 ^ (n * (n - 1) / 2) := by
  rw [hU.card_eq, ← (isSylowTwoOf_unitriangular hn).card_eq, card_unitriangular, Nat.card_zmod]

theorem normalizer_eq_of_isSylowTwoOf_sl {n : ℕ} (hn : 1 ≤ n)
    {U : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))} (hU : IsSylowTwoOf U ⊤) :
    Subgroup.normalizer (U : Set (SpecialLinearGroup (Fin n) (ZMod 2))) = U :=
  E9P2.FinInv.normalizer_eq_of_isSylowTwoOf hU (isSylowTwoOf_unitriangular hn)
    (normalizer_unitriangular_eq n)

theorem binCrit_sl_binary (n : ℕ) (hn : n = 4 ∨ n = 5) :
    BinCrit (SpecialLinearGroup (Fin n) (ZMod 2)) where
  card_sylow U hU := by
    rw [card_eq_of_isSylowTwoOf (by omega) hU]
    rcases hn with rfl | rfl
    · exact ⟨3, by norm_num⟩
    · exact ⟨5, by norm_num⟩
  gen_invol U hU := sl2_sylow_gen_involutions n U hU
  no_invol E hE _ _ z hz hc :=
    He4.NoInvCommNine.of_injective SpecialLinearGroup.toGL SpecialLinearGroup.toGL_injective
      (He4.noInvCommNine_gl n (by omega)) E hE z hz fun p hp => (hc p hp).symm
  no_normalizer U hU x hx h3 :=
    E9P2.FinInv.eq_one_of_mem_normalizer_of_pow_three hU.isPGroup
      (normalizer_eq_of_isSylowTwoOf_sl (by omega) hU) hx h3

end CFSG.Quasithin.E9P2.FinInst

namespace CFSG.Quasithin

open E9P2.FinInv E9P2.FinInst CFSG.QuasithinUnique

theorem binCrit_sl4 : BinCrit (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) :=
  binCrit_sl_binary 4 (Or.inl rfl)

theorem binCrit_sl5 : BinCrit (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :=
  binCrit_sl_binary 5 (Or.inr rfl)

theorem binCrit_sl3_prod : BinCrit (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ×
    Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) where
  card_sylow U hU := by
    rw [eq_prod_map hU, card_prod,
      card_eq_of_isSylowTwoOf (by omega) (isSylowTwoOf_map_fst hU),
      card_eq_of_isSylowTwoOf (by omega) (isSylowTwoOf_map_snd hU)]
    exact ⟨3, by norm_num⟩
  gen_invol U hU := by
    have h := closure_involutions_prod
      (sl2_sylow_gen_involutions 3 _ (isSylowTwoOf_map_fst hU))
      (sl2_sylow_gen_involutions 3 _ (isSylowTwoOf_map_snd hU))
    rwa [← eq_prod_map hU] at h
  no_invol E hE hE3 _ z hz hc :=
    eq_one_of_commute_prod E9P2.FinL3.not_nine_dvd_card_sl3 E9P2.FinL3.not_nine_dvd_card_sl3
      (fun _ _ ha ha3 hz hc => E9P2.FinL3.eq_one_of_commute_of_order_three ha ha3 hz hc)
      (fun _ _ ha ha3 hz hc => E9P2.FinL3.eq_one_of_commute_of_order_three ha ha3 hz hc)
      hE hE3 hz hc
  no_normalizer U hU x hx h3 := by
    rw [eq_prod_map hU] at hx
    exact eq_one_of_mem_normalizer_prod (isSylowTwoOf_map_fst hU).isPGroup
      (isSylowTwoOf_map_snd hU).isPGroup
      (normalizer_eq_of_isSylowTwoOf_sl (by omega) (isSylowTwoOf_map_fst hU))
      (normalizer_eq_of_isSylowTwoOf_sl (by omega) (isSylowTwoOf_map_snd hU)) hx h3

end CFSG.Quasithin

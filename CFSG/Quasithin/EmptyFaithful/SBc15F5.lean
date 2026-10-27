module

public import CFSG.Quasithin.EmptyFaithful.SBc15F5W
public import CFSG.Quasithin.EmptyFaithful.SBc15F5Prod
public import CFSG.Quasithin.EmptyFaithful.SBc15F5A
public import CFSG.LieType.BorelTits.CentralQuotient
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits Equiv

namespace SBc15

namespace F5

theorem card_perm_five : Nat.card (Perm (Fin 5)) = 120 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

theorem card_wrPerf_five : Nat.card (wrPerf (alternatingGroup (Fin 5))) = 3600 := by
  rw [wrPerf_eq_map, Subgroup.card_map_of_injective wrEmb_injective, card_prod_subgroup,
    AltFive.a5Facts.card_A]

theorem index_wrPerf_five : (wrPerf (alternatingGroup (Fin 5))).index = 8 := by
  have h := Subgroup.card_mul_index (wrPerf (alternatingGroup (Fin 5)))
  rw [card_wrPerf_five, card_wr card_perm_five] at h
  omega

theorem factorization_two_3600 : (3600 : ℕ).factorization 2 = 4 := by
  have h : (3600 : ℕ) = 2 ^ 4 * 225 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

end F5

open F5

theorem weakW_five_cover (T : Subgroup (Perm (Fin 5) ≀ᵣ Multiplicative (ZMod 2)))
    (hT : IsSylowTwoOf T ⊤) (g : Perm (Fin 5) ≀ᵣ Multiplicative (ZMod 2)) :
    ∃ k ∈ wrPerf (alternatingGroup (Fin 5)), ∃ y ∈ T, g = k * y := by
  have hPn : (wrPerf (alternatingGroup (Fin 5))).Normal := wrPerf_normal inferInstance
  have hTodd : ¬ 2 ∣ T.index := by
    have h := hT.2.2
    rwa [show (T.subgroupOf ⊤).index = T.index from Subgroup.relIndex_top_right T] at h
  have hdvd1 : (T ⊔ wrPerf (alternatingGroup (Fin 5))).index ∣ T.index :=
    Subgroup.index_dvd_of_le le_sup_left
  have hdvd2 : (T ⊔ wrPerf (alternatingGroup (Fin 5))).index ∣ 8 := by
    rw [← index_wrPerf_five]
    exact Subgroup.index_dvd_of_le le_sup_right
  have hodd : ¬ 2 ∣ (T ⊔ wrPerf (alternatingGroup (Fin 5))).index := fun h => hTodd (h.trans hdvd1)
  have h1 : (T ⊔ wrPerf (alternatingGroup (Fin 5))).index = 1 := by
    generalize (T ⊔ wrPerf (alternatingGroup (Fin 5))).index = n at hodd hdvd2 ⊢
    have hn8 : n ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd2
    interval_cases n <;> omega
  have htop : T ⊔ wrPerf (alternatingGroup (Fin 5)) = ⊤ := Subgroup.index_eq_one.mp h1
  have hg : g ∈ ((wrPerf (alternatingGroup (Fin 5)) ⊔ T : Subgroup _) : Set _) := by
    rw [sup_comm, htop]
    trivial
  rw [Subgroup.normal_mul] at hg
  obtain ⟨k, hk, y, hy, hky⟩ := Set.mem_mul.mp hg
  exact ⟨k, hk, y, hy, hky.symm⟩

theorem weakW_five_closure :
    ∀ T X : Subgroup (Perm (Fin 5) ≀ᵣ Multiplicative (ZMod 2)), IsSylowTwoOf T ⊤ →
      X ≤ wrPerf (alternatingGroup (Fin 5)) →
      T ≤ Subgroup.normalizer (X : Set (Perm (Fin 5) ≀ᵣ Multiplicative (ZMod 2))) →
      oTwoUpper X = X → (∃ a : ℕ, Nat.card X = 9 * 2 ^ a) →
        ∀ k ∈ wrPerf (alternatingGroup (Fin 5)),
          (∀ w ∈ pCoreOf 2 (X ⊔ T ⊓ wrPerf (alternatingGroup (Fin 5))),
            k * w * k⁻¹ ∈ T ⊓ wrPerf (alternatingGroup (Fin 5))) →
          k ∈ X ⊔ T ⊓ wrPerf (alternatingGroup (Fin 5)) := by
  intro T X hT hXP hTX hO h9 k hk hkU
  set A : Subgroup (Perm (Fin 5)) := alternatingGroup (Fin 5) with hA
  set P := wrPerf A with hP
  set U := T ⊓ P with hU
  have hPn : P.Normal := wrPerf_normal inferInstance
  have hUsyl : IsSylowTwoOf U P :=
    A4.isSylowTwoOf_inf_normal hT le_top (Subgroup.normalizer_eq_top (H := P)).ge
  have hU16 : Nat.card U = 16 := by
    rw [hUsyl.card_eq, twoPart, hP, hA, card_wrPerf_five, factorization_two_3600]
    norm_num
  have hUP : U ≤ P := inf_le_right
  set ι := wrEmb (Perm (Fin 5)) with hι
  have hinj : Function.Injective ι := wrEmb_injective
  have hXm : (X.comap ι).map ι = X := map_comap_wrEmb hXP
  have hUm : (U.comap ι).map ι = U := map_comap_wrEmb hUP
  have hXA : X.comap ι ≤ A.prod A := comap_wrEmb_le hXP
  have hUA : U.comap ι ≤ A.prod A := comap_wrEmb_le hUP
  have hUcard : Nat.card (U.comap ι) = 16 := by
    have h := Subgroup.card_map_of_injective hinj (K := U.comap ι)
    rw [hUm] at h
    rw [← h, hU16]
  have hXcard : Nat.card (X.comap ι) = Nat.card X := by
    have h := Subgroup.card_map_of_injective hinj (K := X.comap ι)
    rw [hXm] at h
    exact h.symm
  have hO' : oTwoUpper (X.comap ι) = X.comap ι := by
    apply Subgroup.map_injective hinj
    rw [← oTwoUpper_map, hXm, hO]
  have h9' : ∃ a : ℕ, Nat.card (X.comap ι) = 9 * 2 ^ a := by
    obtain ⟨a, ha⟩ := h9
    exact ⟨a, hXcard.trans ha⟩
  have hUX' : ∀ u ∈ U.comap ι, ∀ x ∈ X.comap ι, u * x * u⁻¹ ∈ X.comap ι := by
    intro u hu x hx
    rw [Subgroup.mem_comap] at hu hx ⊢
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hTX hu.1) (ι x)).mp hx
  obtain ⟨k', hk', hk'k⟩ : ∃ k' ∈ A.prod A, ι k' = k := by
    have h : k ∈ (A.prod A).map ι := by
      rw [← wrPerf_eq_map]
      exact hk
    exact Subgroup.mem_map.mp h
  have hkU' : ∀ w ∈ pCoreOf 2 (X.comap ι ⊔ U.comap ι), k' * w * k'⁻¹ ∈ U.comap ι := by
    intro w hw
    have hw' : ι w ∈ pCoreOf 2 (X ⊔ U) := by
      have h1 : ι w ∈ (pCoreOf 2 (X.comap ι ⊔ U.comap ι)).map ι := Subgroup.mem_map_of_mem ι hw
      have h2 := map_pCoreOf_le (r := 2) ι (X.comap ι ⊔ U.comap ι) h1
      rwa [Subgroup.map_sup, hXm, hUm] at h2
    have h3 := hkU (ι w) hw'
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv, hk'k]
    exact h3
  have key := weakClosure_prod AltFive.a5Facts hUA
    (IsPGroup.of_card_dvd_pow (n := 4) (by rw [hUcard]; norm_num)) hUcard hXA hUX' hO' h9' hk'
    hkU'
  have hmem : ι k' ∈ (X.comap ι ⊔ U.comap ι).map ι := Subgroup.mem_map_of_mem ι key
  rw [Subgroup.map_sup, hXm, hUm, hk'k] at hmem
  exact hmem

theorem weakW_five : WeakW (Equiv.Perm (Fin 5)) (alternatingGroup (Fin 5)) := by
  unfold WeakW
  exact ⟨weakW_five_cover, weakW_five_closure⟩

end SBc15

end CFSG.Quasithin

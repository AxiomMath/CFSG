module

public import CFSG.Permutation.FiveTransitive.Degree24SevenRSixCentralizer
public import CFSG.Permutation.FiveTransitive.Degree24FixedSetSeven

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

theorem stabilizer_card_ne_rSix_cases
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (hCases :
      Nat.card (fixingSubgroup P s) = 13608 ∨
      Nat.card (fixingSubgroup P s) = 13063680) :
    False := by
  classical
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let H : Subgroup P := fixingSubgroup P s
  have hSevenDvdH : 7 ∣ Nat.card H := by
    rcases hCases with hH | hH
    · simpa only [H, hH] using (show 7 ∣ 13608 by norm_num)
    · simpa only [H, hH] using
        (show 7 ∣ 13063680 by norm_num)
  obtain ⟨u, hu⟩ :=
    exists_prime_orderOf_dvd_card' 7 hSevenDvdH
  let uP : P := u
  let g : Equiv.Perm X := uP
  let D : Subgroup P :=
    Subgroup.centralizer ({uP} : Set P)
  let F := Function.fixedPoints g
  let ρ : D →* Equiv.Perm F :=
    subgroupCentralizerToFixedPoints P uP
  letI : MulAction D F :=
    MulAction.compHom F ρ
  have huP : orderOf uP = 7 := by
    calc
      orderOf uP = orderOf u :=
        Subgroup.orderOf_coe _
      _ = 7 := hu
  have hg : orderOf g = 7 := by
    calc
      orderOf g = orderOf uP :=
        Subgroup.orderOf_coe _
      _ = 7 := huP
  have hgSupport : g.support.card = 14 :=
    order_seven_mem_five_stabilizer_support_eq_fourteen
      X P hcard h5 hnotAlt s hs u hu
  have hFcard : Fintype.card F = 10 := by
    rw [Equiv.Perm.card_fixedPoints,
      Equiv.Perm.sum_cycleType, hcard, hgSupport]
  have hD5 :
      ∀ a b : Fin 5 → F, Function.Injective a →
        Function.Injective b →
        ∃ q : D, ∀ i, q • a i = b i := by
    intro a b ha hb
    obtain ⟨q, hq⟩ :=
      rSix_centralizer_five_transitive
        X P hcard h5 hnotAlt s hs hCases u hu
          a b ha hb
    refine ⟨q, ?_⟩
    intro i
    change ρ q (a i) = b i
    exact hq i
  have hDfive :
      MulAction.IsMultiplyPretransitive D F 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨q, hq⟩ :=
      hD5 a b a.injective b.injective
    refine ⟨q, ?_⟩
    ext i
    exact congrArg Subtype.val (hq i)
  let eX : Fin 5 ↪ X :=
    fiveEmbeddingOfSet X s hs
  have heXrange : Set.range eX = s :=
    range_fiveEmbeddingOfSet X s hs
  have heFixed (i : Fin 5) : g (eX i) = eX i := by
    change uP • eX i = eX i
    exact
      (mem_fixingSubgroup_iff P).mp u.prop
        (eX i) (by
          rw [← heXrange]
          exact ⟨i, rfl⟩)
  let eF : Fin 5 ↪ F := {
    toFun := fun i => ⟨eX i, heFixed i⟩
    inj' := fun i j hij =>
      eX.injective
        (congrArg (fun z : F => (z : X)) hij) }
  let sF : Set F := Set.range eF
  have hsF : sF.ncard = 5 := by
    rw [Set.ncard_range_of_injective eF.injective,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  let K : Subgroup D := fixingSubgroup D sF
  have hKindexRaw :=
    hDfive.index_of_fixingSubgroup_mul hsF
  rw [Nat.card_eq_fintype_card, hFcard] at hKindexRaw
  norm_num at hKindexRaw
  have hKindex : K.index = 30240 := by
    change (fixingSubgroup D sF).index = 30240
    omega
  have hDcardEq : Nat.card D = 30240 * Nat.card K := by
    have hproduct := K.index_mul_card
    rw [hKindex] at hproduct
    exact hproduct.symm
  let R : Subgroup H := Subgroup.zpowers u
  have hRcard : Nat.card R = 7 := by
    rw [Nat.card_zpowers, hu]
  have hRisP : IsPGroup 7 R := by
    apply IsPGroup.of_card (n := 1)
    rw [hRcard]
    norm_num
  obtain ⟨S, hRleS⟩ := hRisP.exists_le_sylow
  have hScard : Nat.card S = 7 := by
    rcases hCases with hH | hH
    · exact
        sylow_card_eq_prime_of_card_eq_prime_mul
          H 7 1944 (by norm_num) (by norm_num)
            (by simpa only [H] using hH) S
    · exact
        sylow_card_eq_prime_of_card_eq_prime_mul
          H 7 1866240 (by norm_num) (by norm_num)
            (by simpa only [H] using hH) S
  have hRS : R = (S : Subgroup H) := by
    apply Subgroup.eq_of_le_of_card_ge hRleS
    rw [hRcard, hScard]
  let C : Subgroup H :=
    Subgroup.centralizer (S : Set H)
  have hCcard : Nat.card C = 14 := by
    simpa only [H, C] using
      (rSix_sylowSeven_local_data
        X P hcard h5 hnotAlt s hs hCases S).1
  have hcentEq :
      Subgroup.centralizer ({u} : Set H) = C := by
    apply le_antisymm
    · intro q hq
      rw [Subgroup.mem_centralizer_iff] at hq ⊢
      intro x hx
      have hxR : x ∈ R := by
        rw [hRS]
        exact hx
      obtain ⟨z, hz⟩ :=
        Subgroup.mem_zpowers_iff.mp hxR
      have huq : Commute u q :=
        hq u (by simp)
      rw [← hz]
      exact (huq.zpow_left z).eq
    · change
        Subgroup.centralizer (S : Set H) ≤
          Subgroup.centralizer ({u} : Set H)
      apply Subgroup.centralizer_le
      rw [Set.singleton_subset_iff]
      have huR : u ∈ R :=
        Subgroup.mem_zpowers u
      rw [hRS] at huR
      exact huR
  let C₁ : Subgroup H :=
    Subgroup.centralizer ({u} : Set H)
  have hC₁card : Nat.card C₁ = 14 := by
    rw [show C₁ = C from hcentEq]
    exact hCcard
  let baseMap : K →* P :=
    D.subtype.comp K.subtype
  have hbaseMapMemH :
      ∀ q : K, baseMap q ∈ H := by
    intro q
    rw [mem_fixingSubgroup_iff]
    intro x hx
    have hxi : x ∈ Set.range eX := by
      simpa only [heXrange] using hx
    obtain ⟨i, rfl⟩ := hxi
    have hqfix :=
      (mem_fixingSubgroup_iff D).mp q.prop
        (eF i) ⟨i, rfl⟩
    exact congrArg Subtype.val hqfix
  let localMap : K →* H :=
    baseMap.codRestrict H hbaseMapMemH
  have hlocalMapMemC₁ :
      ∀ q : K, localMap q ∈ C₁ := by
    intro q
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcommP : Commute (baseMap q) uP :=
      Subgroup.mem_centralizer_singleton_iff.mp
        (q.1.prop)
    show localMap q * u = u * localMap q
    apply Subtype.ext
    exact hcommP.eq
  let centMap : K →* C₁ :=
    localMap.codRestrict C₁ hlocalMapMemC₁
  have hcentMapInjective :
      Function.Injective centMap := by
    intro a b hab
    apply K.subtype_injective
    apply D.subtype_injective
    exact
      congrArg
        (fun q : C₁ => ((q : H) : P)) hab
  have hKdvdFourteen : Nat.card K ∣ 14 := by
    rw [← hC₁card]
    exact
      Subgroup.card_dvd_of_injective
        centMap hcentMapInjective
  have hKle : Nat.card K ≤ 14 :=
    Nat.le_of_dvd (by norm_num) hKdvdFourteen
  have hDupper : Nat.card D ≤ 423360 := by
    rw [hDcardEq]
    omega
  let J : Subgroup (Equiv.Perm F) := ρ.range
  have hJ5 :
      ∀ a b : Fin 5 → F, Function.Injective a →
        Function.Injective b →
        ∃ q : J, ∀ i, q • a i = b i := by
    intro a b ha hb
    obtain ⟨q, hq⟩ := hD5 a b ha hb
    let qJ : J := ⟨ρ q, ⟨q, rfl⟩⟩
    refine ⟨qJ, ?_⟩
    intro i
    change ρ q (a i) = b i
    exact hq i
  have hAlt :
      alternatingGroup F ≤
        (MulAction.toPermHom J F).range :=
    FiveTransitive.Helpers.alternatingGroup_le_of_five_transitive_of_card_eq_ten
        J F hFcard hJ5
  have hAltDvdRange :
      Nat.card (alternatingGroup F) ∣
        Nat.card (MulAction.toPermHom J F).range :=
    Subgroup.card_dvd_of_le hAlt
  have hAltDvdJ :
      Nat.card (alternatingGroup F) ∣ Nat.card J :=
    hAltDvdRange.trans
      (Subgroup.card_range_dvd
        (MulAction.toPermHom J F))
  have hAltDvdD :
      Nat.card (alternatingGroup F) ∣ Nat.card D :=
    hAltDvdJ.trans
      (by
        simpa only [J] using
          Subgroup.card_range_dvd ρ)
  have hAltCard :
      Nat.card (alternatingGroup F) = 1814400 := by
    letI : Nontrivial F :=
      Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    rw [Nat.card_eq_fintype_card,
      card_alternatingGroup, hFcard]
    norm_num
  have hDlower : 1814400 ≤ Nat.card D := by
    rw [← hAltCard]
    exact Nat.le_of_dvd Nat.card_pos hAltDvdD
  omega

end FiveTransitive.Degree24

end CFSG

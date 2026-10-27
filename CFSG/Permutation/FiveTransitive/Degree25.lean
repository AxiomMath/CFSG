module

public import CFSG.Permutation.FiveTransitive.LongPrimeArithmetic
public import CFSG.Permutation.FiveTransitive.Degree19LongPrimeNormalizers
public import CFSG.Permutation.FiveTransitive.OrbitBounds
public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG

namespace FiveTransitive.Degree25

open MulAction SubMulAction Subgroup

private theorem transfer_contradiction
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b → ∃ g : P, ∀ i, g • a i = b i)
    (h : ℕ) (hnotTwentyThree : ¬23 ∣ h)
    (e : Fin 2 ↪ X)
    (hJcard : Nat.card (fixingSubgroup P (Set.range e)) = 10626 * h)
    (T : Sylow 23 (fixingSubgroup P (Set.range e)))
    (hTcard : Nat.card T = 23)
    (hnormalizer : Subgroup.normalizer (T : Set (fixingSubgroup P (Set.range e))) ≤
      Subgroup.centralizer (T : Set (fixingSubgroup P (Set.range e)))) : False := by
  classical
  letI : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  let J := fixingSubgroup P (Set.range e)
  have hh : h ≠ 0 := by
    rintro rfl
    exact hnotTwentyThree (dvd_zero 23)
  have hecard : (Set.range e).ncard = 2 := by
    rw [Set.ncard_range_of_injective e.injective,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨g, hg⟩ := h5 a b a.injective b.injective
    refine ⟨g, ?_⟩
    ext i
    exact hg i
  let transfer : J →* T :=
    MonoidHom.transferSylow T hnormalizer
  let Q : Subgroup J := transfer.ker
  letI : Q.Normal := by
    dsimp only [Q, transfer]
    infer_instance
  have hcomplement : IsComplement' Q T := by
    simpa only [Q, transfer] using
      MonoidHom.ker_transferSylow_isComplement'
        T hnormalizer
  have hcardMul := hcomplement.card_mul
  have hQcard : Nat.card Q = 462 * h := by
    rw [hTcard, hJcard] at hcardMul
    nlinarith only [hcardMul]
  let Z :=
    SubMulAction.ofFixingSubgroup P (Set.range e)
  have hZcard : Nat.card Z = 23 := by
    change Nat.card ↥((Set.range e)ᶜ : Set X) = 23
    rw [Nat.card_coe_set_eq]
    have htotal :=
      Set.ncard_add_ncard_compl (Set.range e)
    rw [Nat.card_eq_fintype_card, hcard,
      hecard] at htotal
    omega
  have hJ3 :
      MulAction.IsMultiplyPretransitive J Z 3 := by
    letI : MulAction.IsMultiplyPretransitive P X 5 :=
      hP5
    change
      MulAction.IsMultiplyPretransitive
        (fixingSubgroup P (Set.range e))
        (SubMulAction.ofFixingSubgroup P (Set.range e)) 3
    apply SubMulAction.ofFixingSubgroup.isMultiplyPretransitive
      (m := 3) (n := 5) P (Set.range e)
    omega
  have hJ2 :
      MulAction.IsMultiplyPretransitive J Z 2 := by
    letI : MulAction.IsMultiplyPretransitive J Z 3 := hJ3
    exact MulAction.isMultiplyPretransitive_of_le
      (G := J) (α := Z) (m := 2) (n := 3)
        (by omega) (by
          rw [hZcard]
          omega)
  letI : MulAction.IsPreprimitive J Z :=
    MulAction.isPreprimitive_of_is_two_pretransitive hJ2
  letI : Nonempty Z :=
    Fintype.card_pos_iff.mp (by
      rw [← Nat.card_eq_fintype_card, hZcard]
      norm_num)
  have hfaithfulJ :
      ∀ j : J, (∀ z : Z, j • z = z) → j = 1 := by
    intro j hj
    apply Subtype.ext
    apply P.subtype_injective
    ext x
    by_cases hx : x ∈ Set.range e
    · have hfix :=
        (mem_fixingSubgroup_iff P).mp j.prop x hx
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def]
        using hfix
    · let z : Z := ⟨x, hx⟩
      have hz := hj z
      have hz' := congrArg Subtype.val hz
      simpa [z, Subgroup.smul_def, Equiv.Perm.smul_def]
        using hz'
  have hnormalCases :=
    OrbitBounds.normal_subgroup_card_eq_one_or_degree_dvd
      J Z hfaithfulJ Q
  have hQneOne : Nat.card Q ≠ 1 := by
    rw [hQcard]
    omega
  have htwentyThreeQ : 23 ∣ Nat.card Q := by
    rcases hnormalCases with hQone | hZdvd
    · exact (hQneOne hQone).elim
    · rwa [hZcard] at hZdvd
  rw [hQcard] at htwentyThreeQ
  rcases (show Nat.Prime 23 by norm_num).dvd_mul.mp
      htwentyThreeQ with htwentyThree | htwentyThree
  · norm_num at htwentyThree
  · exact (hnotTwentyThree htwentyThree).elim

theorem five_point_stabilizer_card_mod_twentyThree
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) % 23 = 17 := by
  classical
  let H : Subgroup P := fixingSubgroup P s
  let h := Nat.card H
  have hh : h ≠ 0 := Nat.ne_of_gt Nat.card_pos
  let Y := SubMulAction.ofFixingSubgroup P s
  have hYcard : Nat.card Y = 20 := by
    change Nat.card ↥(sᶜ : Set X) = 20
    rw [Nat.card_coe_set_eq]
    have htotal := Set.ncard_add_ncard_compl s
    rw [Nat.card_eq_fintype_card, hcard, hs] at htotal
    omega
  have hfaithfulH :
      Function.Injective (MulAction.toPermHom H Y) := by
    intro a b hab
    apply Subtype.ext
    apply P.subtype_injective
    ext x
    by_cases hx : x ∈ s
    · have ha :=
        (mem_fixingSubgroup_iff P).mp a.prop x hx
      have hb :=
        (mem_fixingSubgroup_iff P).mp b.prop x hx
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using
        ha.trans hb.symm
    · let y : Y := ⟨x, hx⟩
      have hy :=
        congrArg (fun q : Equiv.Perm Y => q y) hab
      have hy' := congrArg Subtype.val hy
      simpa [y, Subgroup.smul_def, Equiv.Perm.smul_def] using
        hy'
  have hHdvdFactorial : h ∣ (20 : ℕ).factorial := by
    have hdvd :=
      Subgroup.card_dvd_of_injective
        (MulAction.toPermHom H Y) hfaithfulH
    rw [Nat.card_perm, Nat.card_eq_fintype_card,
      ← Nat.card_eq_fintype_card, hYcard] at hdvd
    exact hdvd
  have hnotTwentyThree : ¬23 ∣ h := by
    intro hdvd
    have : 23 ∣ (20 : ℕ).factorial :=
      hdvd.trans hHdvdFactorial
    norm_num at this
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨g, hg⟩ :=
      h5 a b a.injective b.injective
    refine ⟨g, ?_⟩
    ext i
    exact hg i
  have hP2 : MulAction.IsMultiplyPretransitive P X 2 := by
    letI : MulAction.IsMultiplyPretransitive P X 5 := hP5
    exact MulAction.isMultiplyPretransitive_of_le
      (G := P) (α := X) (m := 2) (n := 5)
        (by omega) (by
          rw [Nat.card_eq_fintype_card, hcard]
          omega)
  have hHindexRaw :=
    hP5.index_of_fixingSubgroup_mul hs
  rw [Nat.card_eq_fintype_card, hcard] at hHindexRaw
  norm_num at hHindexRaw
  have hHindex : H.index = 6375600 := by
    change (fixingSubgroup P s).index = 6375600
    omega
  have hHindexCard := H.index_mul_card
  have hPcard : Nat.card P = 6375600 * h := by
    rw [hHindex] at hHindexCard
    exact hHindexCard.symm
  letI : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  have hPfactorization :
      (6375600 * h).factorization 23 = 1 := by
    have hf := LongPrimeArithmetic.factorization_prime_mul_once 23 277200 h
      (by decide) (by norm_num) hnotTwentyThree
    simpa only [show 23 * 277200 = 6375600 by norm_num] using hf
  let S : Sylow 23 P := Sylow.nonempty.some
  have hScard : Nat.card S = 23 := by
    rw [S.card_eq_multiplicity, hPcard,
      hPfactorization]
    norm_num
  let C : Subgroup P :=
    Subgroup.centralizer (S : Set P)
  let N : Subgroup P :=
    Subgroup.normalizer (S : Set P)
  let rG := C.relIndex N
  have hglobal :
      rG ∣ 22 ∧
        0 < rG ∧
        N.index % 23 = 1 ∧
        rG * N.index * 23 = Nat.card P := by
    simpa only [C, N, rG] using
      Degree19.long_prime_normalizer_constraints
        X P h5 hnotAlt (p := 23) (f := 2)
          (by norm_num) (by norm_num) (by norm_num)
          (by omega) S hScard
  have hglobalDivided :
      rG * N.index = 277200 * h := by
    rw [hPcard] at hglobal
    nlinarith only [hglobal.2.2.2]
  have hglobalMod :
      (4 * h) % 23 = rG % 23 := by
    calc
      (4 * h) % 23 = (277200 * h) % 23 := by
        simp [Nat.mul_mod]
      _ = (rG * N.index) % 23 :=
        congrArg (fun n => n % 23)
          hglobalDivided.symm
      _ = rG % 23 := by
        rw [Nat.mul_mod, hglobal.2.2.1]
        simp
  have heNonempty : Nonempty (Fin 2 ↪ X) :=
    Fintype.card_pos_iff.mp (by
      rw [Fintype.card_embedding_eq,
        Fintype.card_fin, hcard]
      norm_num)
  let e : Fin 2 ↪ X := Classical.choice heNonempty
  let J : Subgroup P :=
    fixingSubgroup P (Set.range e)
  have hecard : (Set.range e).ncard = 2 := by
    rw [Set.ncard_range_of_injective e.injective,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have hJindexRaw :=
    hP2.index_of_fixingSubgroup_mul hecard
  rw [Nat.card_eq_fintype_card, hcard] at hJindexRaw
  norm_num at hJindexRaw
  have hJindex : J.index = 600 := by
    change
      (fixingSubgroup P (Set.range e)).index = 600
    omega
  have hJindexCard := J.index_mul_card
  have hJcard : Nat.card J = 10626 * h := by
    rw [hJindex, hPcard] at hJindexCard
    omega
  have hJfactorization :
      (10626 * h).factorization 23 = 1 := by
    have hf := LongPrimeArithmetic.factorization_prime_mul_once 23 462 h
      (by decide) (by norm_num) hnotTwentyThree
    simpa only [show 23 * 462 = 10626 by norm_num] using hf
  let T : Sylow 23 J := Sylow.nonempty.some
  have hTcard : Nat.card T = 23 := by
    rw [T.card_eq_multiplicity, hJcard,
      hJfactorization]
    norm_num
  letI : IsCyclic T :=
    isCyclic_of_prime_card hTcard
  letI : IsMulCommutative T :=
    IsCyclic.isMulCommutative
  obtain ⟨u, huorder⟩ :=
    IsCyclic.exists_ofOrder_eq_natCard (α := T)
  have huorderT : orderOf u = 23 :=
    huorder.trans hTcard
  have huorderJ : orderOf (u : J) = 23 := by
    calc
      orderOf (u : J) = orderOf u :=
        Subgroup.orderOf_coe _
      _ = 23 := huorderT
  have huorderP : orderOf ((u : J) : P) = 23 := by
    calc
      orderOf ((u : J) : P) = orderOf (u : J) :=
        Subgroup.orderOf_coe _
      _ = 23 := huorderJ
  let CJ : Subgroup J :=
    Subgroup.centralizer (T : Set J)
  let NJ : Subgroup J :=
    Subgroup.normalizer (T : Set J)
  have hTleCJ : (T : Subgroup J) ≤ CJ := by
    intro a ha b hb
    exact congrArg Subtype.val
      (mul_comm' (⟨b, hb⟩ : T) (⟨a, ha⟩ : T))
  let globalC : Subgroup P :=
    Subgroup.centralizer
      ({((u : J) : P)} : Set P)
  have hglobalCcard : Nat.card globalC = 23 := by
    simpa only [globalC] using
      FewFixedPrimeCycle.centralizer_card_eq_prime_of_not_alternating
        X P (p := 23) (f := 2)
          (by norm_num) (by norm_num) (by norm_num)
          (by omega) h5 hnotAlt ((u : J) : P) huorderP
  let baseMap : CJ →* P :=
    J.subtype.comp CJ.subtype
  have hbaseMapMem :
      ∀ c : CJ, baseMap c ∈ globalC := by
    intro c
    change ((c.1 : J) : P) ∈
      Subgroup.centralizer
        ({((u : J) : P)} : Set P)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val
      (c.prop (u : J) u.prop).symm
  let centMap : CJ →* globalC :=
    baseMap.codRestrict globalC hbaseMapMem
  have hcentMapInjective : Function.Injective centMap := by
    intro a b hab
    have hab' := congrArg Subtype.val hab
    change baseMap a = baseMap b at hab'
    exact CJ.subtype_injective
      (J.subtype_injective hab')
  have hCJdiv : Nat.card CJ ∣ 23 := by
    rw [← hglobalCcard]
    exact Subgroup.card_dvd_of_injective
      centMap hcentMapInjective
  have hTwentyThreeDvdCJ : 23 ∣ Nat.card CJ := by
    rw [← hTcard]
    exact Subgroup.card_dvd_of_le hTleCJ
  have hCJcard : Nat.card CJ = 23 :=
    Nat.dvd_antisymm hCJdiv hTwentyThreeDvdCJ
  have hAutCard : Nat.card (MulAut T) = 22 := by
    rw [IsCyclic.card_mulAut T, hTcard,
      Nat.totient_prime (show Nat.Prime 23 by norm_num)]
  have hrangeDvd :
      Nat.card T.normalizerMonoidHom.range ∣ 22 := by
    rw [← hAutCard]
    exact Subgroup.card_subgroup_dvd_card _
  have hrJEq :
      CJ.relIndex NJ =
        Nat.card T.normalizerMonoidHom.range := by
    change
      (Subgroup.centralizer (T : Set J)).relIndex
          (Subgroup.normalizer (T : Set J)) =
        Nat.card T.normalizerMonoidHom.range
    rw [Subgroup.relIndex, ← Subgroup.index_ker,
      T.normalizerMonoidHom_ker]
    simp only [T.coe_coe]
  have hrJDvd : CJ.relIndex NJ ∣ 22 := by
    rwa [hrJEq]
  letI : CJ.IsFiniteRelIndex NJ :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  have hNJmod : NJ.index % 23 = 1 := by
    change
      (Subgroup.normalizer (T : Set J)).index % 23 = 1
    have hsylow :
        (Subgroup.normalizer (T : Set J)).index ≡
          1 [MOD 23] := by
      rw [← T.card_eq_index_normalizer]
      exact card_sylow_modEq_one 23 J
    change
      (Subgroup.normalizer (T : Set J)).index % 23 =
        1 % 23 at hsylow
    norm_num at hsylow
    exact hsylow
  have hrel :
      CJ.relIndex NJ * NJ.index = CJ.index := by
    simpa only [CJ, NJ] using
      Subgroup.relIndex_mul_index
        (Subgroup.centralizer_le_normalizer (T : Set J))
  have hCJindex := CJ.index_mul_card
  have hlocalProduct :
      CJ.relIndex NJ * NJ.index * 23 = Nat.card J := by
    rw [hCJcard, ← hrel] at hCJindex
    exact hCJindex
  have hlocalDivided :
      CJ.relIndex NJ * NJ.index = 462 * h := by
    rw [hJcard] at hlocalProduct
    nlinarith only [hlocalProduct]
  have hlocalMod :
      (2 * h) % 23 = (CJ.relIndex NJ) % 23 := by
    calc
      (2 * h) % 23 = (462 * h) % 23 := by
        simp [Nat.mul_mod]
      _ = (CJ.relIndex NJ * NJ.index) % 23 :=
        congrArg (fun n => n % 23)
          hlocalDivided.symm
      _ = (CJ.relIndex NJ) % 23 := by
        rw [Nat.mul_mod, hNJmod]
        simp
  have hpairCases :
      (CJ.relIndex NJ = 1 ∧ rG = 2) ∨
        (CJ.relIndex NJ = 11 ∧ rG = 22) :=
    LongPrimeArithmetic.degree_twenty_five_residue_pairs
      h (CJ.relIndex NJ) rG hrJDvd hglobal.1 hlocalMod hglobalMod
  rcases hpairCases with hpair | hpair
  · have hnormalizer :
        Subgroup.normalizer (T : Set J) ≤
          Subgroup.centralizer (T : Set J) := by
      exact Subgroup.relIndex_eq_one.mp
        (show CJ.relIndex NJ = 1 by
          simpa only [CJ, NJ] using hpair.1)
    exact (transfer_contradiction X P hcard h5 h hnotTwentyThree e
      hJcard T hTcard hnormalizer).elim
  · have hlocalMod' := hlocalMod
    rw [hpair.1] at hlocalMod'
    norm_num at hlocalMod'
    have hm : h % 23 = 17 := by omega
    simpa only [H, h] using hm

end FiveTransitive.Degree25

end CFSG

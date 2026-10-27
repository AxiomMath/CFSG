module

public import CFSG.Permutation.FiveTransitive.Degree24StabilizerOneBelow
public import CFSG.Permutation.FiveTransitive.Degree19LongPrimeNormalizers

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

private theorem twentyThree_dvd_card_of_large_normal_subgroup
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (Q : Subgroup P) [Q.Normal]
    (hQlarge : 24 < Nat.card Q) :
    23 ∣ Nat.card Q := by
  classical
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨q, hq⟩ :=
      h5 a b a.injective b.injective
    refine ⟨q, ?_⟩
    ext i
    exact hq i
  have hP2 : MulAction.IsMultiplyPretransitive P X 2 := by
    letI : MulAction.IsMultiplyPretransitive P X 5 := hP5
    exact MulAction.isMultiplyPretransitive_of_le
      (G := P) (α := X) (m := 2) (n := 5)
        (by omega) (by
          rw [Nat.card_eq_fintype_card, hcard]
          omega)
  letI : MulAction.IsPreprimitive P X :=
    MulAction.isPreprimitive_of_is_two_pretransitive hP2
  have hQfixedNe :
      MulAction.fixedPoints Q X ≠ Set.univ := by
    intro hfixed
    have hsubsingleton : Subsingleton Q := by
      constructor
      intro a b
      apply Subtype.ext
      apply P.subtype_injective
      ext z
      have ha :
          a • z = z :=
        MulAction.mem_fixedPoints.mp
          ((Set.eq_univ_iff_forall.mp hfixed) z) a
      have hb :
          b • z = z :=
        MulAction.mem_fixedPoints.mp
          ((Set.eq_univ_iff_forall.mp hfixed) z) b
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def]
        using ha.trans hb.symm
    have hQcardOne : Nat.card Q = 1 :=
      @Nat.card_unique Q inferInstance hsubsingleton
    omega
  have hQtrans :
      MulAction.IsPretransitive Q X :=
    MulAction.IsQuasiPreprimitive.isPretransitive_of_normal
      hQfixedNe
  letI : MulAction.IsPretransitive Q X := hQtrans
  have hxNonempty : Nonempty X :=
    Fintype.card_pos_iff.mp (by omega)
  let x : X := Classical.choice hxNonempty
  let K : Subgroup P := MulAction.stabilizer P x
  let Y := SubMulAction.ofStabilizer P x
  have hP3 : MulAction.IsMultiplyPretransitive P X 3 := by
    letI : MulAction.IsMultiplyPretransitive P X 5 := hP5
    exact MulAction.isMultiplyPretransitive_of_le
      (G := P) (α := X) (m := 3) (n := 5)
        (by omega) (by
          rw [Nat.card_eq_fintype_card, hcard]
          omega)
  have hK2 :
      MulAction.IsMultiplyPretransitive K Y 2 := by
    simpa only [K, Y] using
      (SubMulAction.ofStabilizer.isMultiplyPretransitive
        (G := P) (α := X) (a := x) (n := 2)).mp hP3
  letI : MulAction.IsPreprimitive K Y :=
    MulAction.isPreprimitive_of_is_two_pretransitive hK2
  let L : Subgroup K := Subgroup.comap K.subtype Q
  letI : L.Normal :=
    Subgroup.Normal.comap (inferInstance : Q.Normal) K.subtype
  have hLfixedNe :
      MulAction.fixedPoints L Y ≠ Set.univ := by
    intro hfixed
    have hLsubsingleton : Subsingleton L := by
      constructor
      intro a b
      apply Subtype.ext
      apply Subtype.ext
      apply P.subtype_injective
      ext z
      by_cases hz : z = x
      · subst z
        have ha :
            a.1.1 • x = x :=
          MulAction.mem_stabilizer_iff.mp a.1.prop
        have hb :
            b.1.1 • x = x :=
          MulAction.mem_stabilizer_iff.mp b.1.prop
        simpa [Subgroup.smul_def, Equiv.Perm.smul_def]
          using ha.trans hb.symm
      · let y : Y := ⟨z, by
          simpa only [Y,
            SubMulAction.mem_ofStabilizer_iff] using hz⟩
        have ha :
            a • y = y :=
          MulAction.mem_fixedPoints.mp
            ((Set.eq_univ_iff_forall.mp hfixed) y) a
        have hb :
            b • y = y :=
          MulAction.mem_fixedPoints.mp
            ((Set.eq_univ_iff_forall.mp hfixed) y) b
        have ha' := congrArg Subtype.val ha
        have hb' := congrArg Subtype.val hb
        change ((a.1.1 : P) : Equiv.Perm X) z = z at ha'
        change ((b.1.1 : P) : Equiv.Perm X) z = z at hb'
        exact ha'.trans hb'.symm
    let stabilizerToL :
        MulAction.stabilizer Q x → L :=
      fun q =>
        ⟨⟨q.1.1, by
            exact MulAction.mem_stabilizer_iff.mpr
              (MulAction.mem_stabilizer_iff.mp q.prop)⟩,
          q.1.prop⟩
    have hstabilizerSubsingleton :
        Subsingleton (MulAction.stabilizer Q x) := by
      constructor
      intro a b
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun q : L => q.1.1)
        (hLsubsingleton.elim
          (stabilizerToL a) (stabilizerToL b))
    letI : Subsingleton (MulAction.stabilizer Q x) :=
      hstabilizerSubsingleton
    have hstabilizerCard :
        Nat.card (MulAction.stabilizer Q x) = 1 :=
      Nat.card_unique
    have hindex :
        (MulAction.stabilizer Q x).index = 24 := by
      rw [MulAction.index_stabilizer_of_transitive,
        Nat.card_eq_fintype_card, hcard]
    have hindexCard :=
      (MulAction.stabilizer Q x).index_mul_card
    have hQcard : Nat.card Q = 24 := by
      calc
        Nat.card Q =
            (MulAction.stabilizer Q x).index *
              Nat.card (MulAction.stabilizer Q x) :=
          hindexCard.symm
        _ = 24 := by
          rw [hindex, hstabilizerCard]
    exact (Nat.ne_of_gt hQlarge) hQcard
  have hLtrans :
      MulAction.IsPretransitive L Y :=
    MulAction.IsQuasiPreprimitive.isPretransitive_of_normal
      hLfixedNe
  letI : MulAction.IsPretransitive L Y := hLtrans
  have hYcard : Nat.card Y = 23 := by
    rw [SubMulAction.nat_card_ofStabilizer_eq P x,
      Nat.card_eq_fintype_card, hcard]
  have hyNonempty : Nonempty Y :=
    (Nat.card_pos_iff.mp (by
      rw [hYcard]
      norm_num)).1
  let y : Y := Classical.choice hyNonempty
  have hLindex :
      (MulAction.stabilizer L y).index = 23 := by
    rw [MulAction.index_stabilizer_of_transitive,
      hYcard]
  have hLindexCard :=
    (MulAction.stabilizer L y).index_mul_card
  have htwentyThreeL : 23 ∣ Nat.card L := by
    rw [hLindex] at hLindexCard
    exact ⟨Nat.card (MulAction.stabilizer L y),
      hLindexCard.symm⟩
  let inclusion : L →* Q := {
    toFun := fun q => ⟨q.1.1, by exact q.prop⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hinclusion : Function.Injective inclusion := by
    intro a b hab
    exact Subtype.ext (Subtype.ext
      (congrArg (fun q : Q => (q : P)) hab))
  exact htwentyThreeL.trans
    (Subgroup.card_dvd_of_injective inclusion hinclusion)

theorem five_point_stabilizer_card_mod_twentyThree_ne_nineteen
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) % 23 ≠ 19 := by
  classical
  let H : Subgroup P := fixingSubgroup P s
  let h := Nat.card H
  have hh : h ≠ 0 := Nat.ne_of_gt Nat.card_pos
  have hdiv : h ∣ 522547200 := by
    simpa only [H, h] using
      five_point_stabilizer_card_dvd_without_two_thirteenth
        X P hcard h5 hnotAlt s hs
  have hnotTwentyThree : ¬23 ∣ h := by
    intro hdvd
    have : 23 ∣ 522547200 := hdvd.trans hdiv
    norm_num at this
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨g, hg⟩ :=
      h5 a b a.injective b.injective
    refine ⟨g, ?_⟩
    ext i
    exact hg i
  have hHindexRaw :=
    hP5.index_of_fixingSubgroup_mul hs
  rw [Nat.card_eq_fintype_card, hcard] at hHindexRaw
  norm_num at hHindexRaw
  have hHindex : H.index = 5100480 := by
    change (fixingSubgroup P s).index = 5100480
    omega
  have hHindexCard := H.index_mul_card
  have hPcard : Nat.card P = 5100480 * h := by
    rw [hHindex] at hHindexCard
    exact hHindexCard.symm
  letI : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  have hPfactorization :
      (5100480 * h).factorization 23 = 1 := by
    rw [show 5100480 = 23 * 221760 by norm_num,
      Nat.mul_assoc,
      Nat.factorization_mul (by norm_num)
        (Nat.mul_ne_zero (by norm_num) hh),
      Finsupp.add_apply,
      (show Nat.Prime 23 by norm_num).factorization,
      Finsupp.single_eq_same,
      Nat.factorization_mul (by norm_num) hh,
      Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd hnotTwentyThree]
    norm_num
  let S : Sylow 23 P := Sylow.nonempty.some
  have hScard : Nat.card S = 23 := by
    rw [S.card_eq_multiplicity, hPcard,
      hPfactorization]
    norm_num
  let C : Subgroup P :=
    Subgroup.centralizer (S : Set P)
  let N : Subgroup P :=
    Subgroup.normalizer (S : Set P)
  let r := C.relIndex N
  have hnormalizerData :
      r ∣ 22 ∧
        0 < r ∧
        N.index % 23 = 1 ∧
        r * N.index * 23 = Nat.card P := by
    simpa only [C, N, r] using
      Degree19.long_prime_normalizer_constraints
        X P h5 hnotAlt (p := 23) (f := 1)
          (by norm_num) (by norm_num) (by norm_num)
          (by omega) S hScard
  have hdivided :
      r * N.index = 221760 * h := by
    rw [hPcard] at hnormalizerData
    nlinarith [hnormalizerData.2.2.2]
  have hmod :
      (17 * h) % 23 = r % 23 := by
    calc
      (17 * h) % 23 = (221760 * h) % 23 := by
        simp [Nat.mul_mod]
      _ = (r * N.index) % 23 :=
        congrArg (fun n => n % 23) hdivided.symm
      _ = r % 23 := by
        rw [Nat.mul_mod, hnormalizerData.2.2.1]
        simp
  change h % 23 ≠ 19
  intro hmodNineteen
  have hrmod : r % 23 = 1 := by
    rw [← hmod, Nat.mul_mod, hmodNineteen]
  have hrle : r ≤ 22 :=
    Nat.le_of_dvd (by norm_num) hnormalizerData.1
  have hr : r = 1 := by omega
  have hnormalizer :
      Subgroup.normalizer (S : Set P) ≤
        Subgroup.centralizer (S : Set P) := by
    exact Subgroup.relIndex_eq_one.mp
      (show C.relIndex N = 1 by simpa only [r] using hr)
  let transfer : P →* S :=
    MonoidHom.transferSylow S hnormalizer
  let Q : Subgroup P := transfer.ker
  letI : Q.Normal := by
    dsimp only [Q, transfer]
    infer_instance
  have hcomplement : IsComplement' Q S := by
    simpa only [Q, transfer] using
      MonoidHom.ker_transferSylow_isComplement'
        S hnormalizer
  have hcardMul := hcomplement.card_mul
  have hQcard : Nat.card Q = 221760 * h := by
    rw [hScard, hPcard] at hcardMul
    nlinarith
  have hQlarge : 24 < Nat.card Q := by
    rw [hQcard]
    nlinarith [Nat.card_pos (α := H)]
  have htwentyThreeQ : 23 ∣ Nat.card Q :=
    twentyThree_dvd_card_of_large_normal_subgroup
      X P hcard h5 Q hQlarge
  rw [hQcard] at htwentyThreeQ
  rcases (show Nat.Prime 23 by norm_num).dvd_mul.mp
      htwentyThreeQ with htwentyThree | htwentyThree
  · norm_num at htwentyThree
  · exact hnotTwentyThree htwentyThree

end FiveTransitive.Degree24

end CFSG

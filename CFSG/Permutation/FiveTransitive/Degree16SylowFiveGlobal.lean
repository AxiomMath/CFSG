module

public import CFSG.Permutation.FiveTransitive.Degree16DoubleFiveCentralizer
public import CFSG.Permutation.FiveTransitive.Degree15FourTuples
public import Mathlib.Algebra.Group.Equiv.Finite

public section

namespace CFSG

namespace FiveTransitive.Degree16

open MulAction SubMulAction Subgroup

private theorem sylow_five_normalizer_card_le_seven_thousand_two_hundred
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 16)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (hPcard : Nat.card P = 94348800)
    (S : Sylow 5 P) (hScard : Nat.card S = 25) :
    Nat.card (Subgroup.normalizer (S : Set P)) ≤ 7200 := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let D := DoubleFiveElements X P S
  have hDcard : Fintype.card D = 12 :=
    card_doubleFiveElements_eq_twelve
      X P hcard h5 hnotAlt S hScard
  have hDnonempty : Nonempty D :=
    Fintype.card_pos_iff.mp (by omega)
  let u : D := Classical.choice hDnonempty
  have huOrder : orderOf u.1 = 5 :=
    sylow_five_nonidentity_order
      X P hcard S hScard u.2.1
  have hvExists :
      ∃ v : D, v.1 ∉ Subgroup.zpowers u.1 := by
    by_contra h
    push Not at h
    let f : D → Subgroup.zpowers u.1 :=
      fun v => ⟨v.1, h v⟩
    have hfInjective : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      change a.1 = b.1
      exact congrArg
        (fun z : Subgroup.zpowers u.1 => (z : S)) hab
    have hcardLe :=
      Fintype.card_le_of_injective f hfInjective
    rw [hDcard, Fintype.card_zpowers, huOrder] at hcardLe
    omega
  obtain ⟨v, hvNotZPowers⟩ := hvExists
  let H : Subgroup S :=
    Subgroup.closure ({u.1, v.1} : Set S)
  have huH : u.1 ∈ H :=
    Subgroup.subset_closure (by simp)
  have hvH : v.1 ∈ H :=
    Subgroup.subset_closure (by simp)
  have hzpowersLe : Subgroup.zpowers u.1 ≤ H :=
    Subgroup.zpowers_le.mpr huH
  have hzpowersCard :
      Nat.card (Subgroup.zpowers u.1) = 5 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_zpowers,
      huOrder]
  have hHcardDvd : Nat.card H ∣ 25 := by
    rw [← hScard]
    exact Subgroup.card_subgroup_dvd_card H
  have hHcardGe : 5 ≤ Nat.card H := by
    calc
      5 = Nat.card (Subgroup.zpowers u.1) :=
        hzpowersCard.symm
      _ ≤ Nat.card H :=
        Nat.card_le_card_of_injective
          (Subgroup.inclusion hzpowersLe)
          (Subgroup.inclusion_injective hzpowersLe)
  have hHcardNeFive : Nat.card H ≠ 5 := by
    intro hHcard
    have heq : Subgroup.zpowers u.1 = H :=
      Subgroup.eq_of_le_of_card_ge hzpowersLe
        (hHcard.trans hzpowersCard.symm).le
    exact hvNotZPowers (by
      rw [heq]
      exact hvH)
  have hHcard : Nat.card H = 25 := by
    have hHcardLe := Nat.le_of_dvd (by norm_num) hHcardDvd
    let k : Fin 26 := ⟨Nat.card H, by omega⟩
    have hfinite :
        ∀ k : Fin 26, k.val ∣ 25 → 5 ≤ k.val →
          k.val ≠ 5 → k.val = 25 := by
      decide
    exact hfinite k hHcardDvd hHcardGe hHcardNeFive
  have hclosure : H = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hHcard, hScard]
  let N : Subgroup P :=
    Subgroup.normalizer (S : Set P)
  let C : Subgroup P :=
    Subgroup.centralizer (S : Set P)
  let R : Subgroup (MulAut S) :=
    S.normalizerMonoidHom.range
  have hmapsDoubleFive (r : R) (a : D) :
      r.1 a.1 ≠ 1 ∧
        Fintype.card
          (MulAction.fixedBy X ((r.1 a.1 : S) : P)) = 6 := by
    have hne : r.1 a.1 ≠ 1 := by
      intro h
      apply a.2.1
      apply r.1.injective
      simpa using h
    obtain ⟨n, hn⟩ := r.2
    have hconjS :
        S.normalizerMonoidHom n a.1 = r.1 a.1 :=
      congrArg (fun e : MulAut S => e a.1) hn
    have hconjP :
        ((r.1 a.1 : S) : P) =
          (n : P) * (a.1 : P) * (n : P)⁻¹ := by
      exact congrArg Subtype.val hconjS.symm
    have hconjPerm :
        (((r.1 a.1 : S) : P) : Equiv.Perm X) =
          ((n : P) : Equiv.Perm X) *
            (((a.1 : S) : P) : Equiv.Perm X) *
            ((n : P) : Equiv.Perm X)⁻¹ :=
      congrArg Subtype.val hconjP
    refine ⟨hne, ?_⟩
    calc
      Fintype.card
          (MulAction.fixedBy X ((r.1 a.1 : S) : P)) =
          Fintype.card X -
            (((r.1 a.1 : S) : P) :
              Equiv.Perm X).support.card :=
        Degree15.card_fixedBy_subgroup_perm P _
      _ = Fintype.card X -
            (((a.1 : S) : P) :
              Equiv.Perm X).support.card := by
        rw [hconjPerm, Equiv.Perm.card_support_conj]
      _ = Fintype.card
          (MulAction.fixedBy X ((a.1 : S) : P)) :=
        (Degree15.card_fixedBy_subgroup_perm P _).symm
      _ = 6 := a.2.2
  let pairMap : R → D × D :=
    fun r =>
      (⟨r.1 u.1, hmapsDoubleFive r u⟩,
        ⟨r.1 v.1, hmapsDoubleFive r v⟩)
  have hpairMapInjective : Function.Injective pairMap := by
    intro r t hrt
    apply Subtype.ext
    apply MulEquiv.toMonoidHom_injective
    apply MonoidHom.eq_of_eqOn_dense hclosure
    intro x hx
    rcases hx with rfl | hx
    · exact congrArg (fun z : D × D => z.1.1) hrt
    · have hxv : x = v.1 := by simpa using hx
      subst x
      exact congrArg (fun z : D × D => z.2.1) hrt
  have hRcardLe : Nat.card R ≤ 144 := by
    rw [Nat.card_eq_fintype_card]
    calc
      Fintype.card R ≤ Fintype.card (D × D) :=
        Fintype.card_le_of_injective
          pairMap hpairMapInjective
      _ = 12 * 12 := by
        rw [Fintype.card_prod, hDcard]
      _ = 144 := by norm_num
  have hrEq : C.relIndex N = Nat.card R := by
    change
      (Subgroup.centralizer (S : Set P)).relIndex
          (Subgroup.normalizer (S : Set P)) =
        Nat.card S.normalizerMonoidHom.range
    rw [Subgroup.relIndex, ← Subgroup.index_ker,
      S.normalizerMonoidHom_ker]
    simp only [S.coe_coe]
  have hCle :
      C ≤ Subgroup.centralizer
        ({((u.1 : S) : P)} : Set P) := by
    intro q hq
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hq ((u.1 : S) : P) u.1.prop).symm
  have hCcardLe : Nat.card C ≤ 50 := by
    have hdiv := Subgroup.card_dvd_of_le hCle
    exact (Nat.le_of_dvd Nat.card_pos hdiv).trans
      (double_five_centralizer_card_le_fifty
        X P hcard h5 hnotAlt hPcard S hScard u)
  have hrel :
      C.relIndex N * N.index = C.index :=
    Subgroup.relIndex_mul_index
      (Subgroup.centralizer_le_normalizer (S : Set P))
  have hNcardEq :
      Nat.card N = C.relIndex N * Nat.card C := by
    have hprod :
        N.index * (C.relIndex N * Nat.card C) =
          N.index * Nat.card N := by
      calc
        N.index * (C.relIndex N * Nat.card C) =
            C.index * Nat.card C := by
          rw [← hrel]
          ac_rfl
        _ = Nat.card P := C.index_mul_card
        _ = N.index * Nat.card N := N.index_mul_card.symm
    exact (Nat.mul_left_cancel
      (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      hprod).symm
  rw [hNcardEq, hrEq]
  exact (Nat.mul_le_mul hRcardLe hCcardLe).trans (by norm_num)

abbrev DoubleFiveIncidences
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) :=
  Σ S : Sylow 5 P, DoubleFiveElements X P S

noncomputable instance doubleFiveIncidencesFintype
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) :
    Fintype (DoubleFiveIncidences X P) := by
  classical
  infer_instance

private def doubleFiveIncidenceVal
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) :
    DoubleFiveIncidences X P → P
  | ⟨_, u⟩ => u.1

theorem five_transitive_order_ninety_four_million_impossible
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 16)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (hPcard : Nat.card P = 94348800) :
    False := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let S : Sylow 5 P := Sylow.nonempty.some
  have hScard : Nat.card S = 25 := by
    rw [S.card_eq_multiplicity, hPcard]
    rw [show 94348800 = 5 * (5 * 3773952) by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply,
      (show Nat.Prime 5 by norm_num).factorization,
      Finsupp.single_eq_same,
      Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply,
      (show Nat.Prime 5 by norm_num).factorization,
      Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    norm_num
  let N : Subgroup P :=
    Subgroup.normalizer (S : Set P)
  have hNcardLe : Nat.card N ≤ 7200 := by
    simpa only [N] using
      sylow_five_normalizer_card_le_seven_thousand_two_hundred
        X P hcard h5 hnotAlt hPcard S hScard
  have hNindexLower : 13104 ≤ N.index := by
    have hscaled : 94348800 ≤ N.index * 7200 := by
      calc
        94348800 = Nat.card P := hPcard.symm
        _ = N.index * Nat.card N := N.index_mul_card.symm
        _ ≤ N.index * 7200 :=
          Nat.mul_le_mul_left N.index hNcardLe
    omega
  let A := DoubleFiveIncidences X P
  let val : A → P :=
    doubleFiveIncidenceVal X P
  have hvalInjective : Function.Injective val := by
    rintro ⟨T, u⟩ ⟨U, v⟩ huv
    have hTcard : Nat.card T = 25 := by
      calc
        Nat.card T = Nat.card S :=
          Nat.card_congr (Sylow.equiv T S).toEquiv
        _ = 25 := hScard
    have huU : ((u.1 : T) : P) ∈ U := by
      have huvP : ((u.1 : T) : P) = ((v.1 : U) : P) := by
        simpa [val, doubleFiveIncidenceVal] using huv
      rw [huvP]
      exact v.1.prop
    have hTU : T = U :=
      sylow_five_eq_of_double_five_mem
        X P hcard h5 hnotAlt hPcard T U hTcard u huU
    subst U
    have huvP : ((u.1 : T) : P) = ((v.1 : T) : P) := by
      simpa [val, doubleFiveIncidenceVal] using huv
    have huvT : u.1 = v.1 :=
      Subtype.ext huvP
    have huvD : u = v :=
      Subtype.ext huvT
    subst v
    rfl
  have hfiber (T : Sylow 5 P) :
      Fintype.card (DoubleFiveElements X P T) = 12 := by
    have hTcard : Nat.card T = 25 := by
      calc
        Nat.card T = Nat.card S :=
          Nat.card_congr (Sylow.equiv T S).toEquiv
        _ = 25 := hScard
    exact card_doubleFiveElements_eq_twelve
      X P hcard h5 hnotAlt T hTcard
  have hSylowCard :
      Fintype.card (Sylow 5 P) = N.index := by
    rw [← Nat.card_eq_fintype_card,
      S.card_eq_index_normalizer]
  have hAcard : Fintype.card A = N.index * 12 := by
    change
      Fintype.card
          (Σ T : Sylow 5 P,
            DoubleFiveElements X P T) =
        N.index * 12
    rw [Fintype.card_sigma]
    simp_rw [hfiber]
    simp [hSylowCard]
  let E := Fin 5 ↪ X
  have hfixed (a : A) :
      Fintype.card (MulAction.fixedBy E (val a)) = 720 := by
    rcases a with ⟨T, u⟩
    change
      Fintype.card
          (MulAction.fixedBy (Fin 5 ↪ X) ((u.1 : T) : P)) =
        720
    calc
      Fintype.card
          (MulAction.fixedBy (Fin 5 ↪ X) ((u.1 : T) : P)) =
          (Fintype.card
            (MulAction.fixedBy X ((u.1 : T) : P))).descFactorial
              (Fintype.card (Fin 5)) :=
        Degree15.card_fixedBy_embedding ((u.1 : T) : P)
      _ = 720 := by
        rw [u.2.2, Fintype.card_fin]
        norm_num
  have hselectedSum :
      (∑ a : A,
          Fintype.card (MulAction.fixedBy E (val a))) =
        N.index * 12 * 720 := by
    simp_rw [hfixed]
    simp [hAcard]
  have hselectedLe :
      (∑ a : A,
          Fintype.card (MulAction.fixedBy E (val a))) ≤
        ∑ q : P,
          Fintype.card (MulAction.fixedBy E q) := by
    calc
      (∑ a : A,
          Fintype.card (MulAction.fixedBy E (val a))) =
          ∑ q ∈ Finset.univ.image val,
            Fintype.card (MulAction.fixedBy E q) := by
        rw [Finset.sum_image hvalInjective.injOn]
      _ ≤ ∑ q ∈ (Finset.univ : Finset P),
          Fintype.card (MulAction.fixedBy E q) :=
        Finset.sum_le_sum_of_subset (by simp)
      _ = ∑ q : P,
          Fintype.card (MulAction.fixedBy E q) := by
        simp
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨g, hg⟩ := h5 a b a.injective b.injective
    refine ⟨g, ?_⟩
    ext i
    exact hg i
  letI : MulAction.IsPretransitive P E := by
    change MulAction.IsMultiplyPretransitive P X 5
    exact hP5
  letI : Nonempty E := Fintype.card_pos_iff.mp (by
    change 0 < Fintype.card (Fin 5 ↪ X)
    rw [Fintype.card_embedding_eq, Fintype.card_fin, hcard]
    norm_num)
  letI : Unique (MulAction.orbitRel.Quotient P E) :=
    Classical.choice
      ((MulAction.pretransitive_iff_unique_quotient_of_nonempty
        P E).mp hP5)
  have hburnside :=
    MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group P E
  have hburnside' :
      (∑ q : P,
          Fintype.card (MulAction.fixedBy E q)) =
        Nat.card P := by
    rw [Fintype.card_unique, one_mul,
      ← Nat.card_eq_fintype_card] at hburnside
    exact hburnside
  have hupper :
      N.index * 12 * 720 ≤ 94348800 := by
    calc
      N.index * 12 * 720 =
          ∑ a : A,
            Fintype.card (MulAction.fixedBy E (val a)) :=
        hselectedSum.symm
      _ ≤ ∑ q : P,
          Fintype.card (MulAction.fixedBy E q) :=
        hselectedLe
      _ = Nat.card P := hburnside'
      _ = 94348800 := hPcard
  omega

end FiveTransitive.Degree16

end CFSG

module

public import CFSG.RankThree.PartTwo.Sec21.Item223PrintProofOne
public import CFSG.RankThree.PartTwo.Sec21.Item223KFactsProofInsp
import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.RankThree.PartTwo.Sec21.Commute33
public import CFSG.RankThree.PartTwo.Sec21.Item223PrintProofFour
public import CFSG.RankThree.PartTwo.Sec21.Item233OneProofHull

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.Assembly (IsElemAbelian)
open Item223PrintProof

variable {G : Type} [Group G]


theorem item223Print_one_of_list [Finite G] (h45 : Sec4.Item4_5) (h46 : Sec4.Item4_6)
    (h47 : Sec4.Item4_7W) (h66 : Sec6.Item6_6) (h1134 : Item1134Four)
    (hList : Inspection223List) (hθ : Item223ThetaTrivial) (h222 : Item222)
    (hKW : KOfWellDefinedAll) {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L)
    (hA81 : Nat.card A = 3 ^ 4) {φ : MulAut A} (hφ : φ ∈ dStar A) {X : Subgroup G}
    (hX : X ∈ lStar A) (hKX : kOf A φ ≤ X) : ∃ m : ℕ, OneData A φ X m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hst := hpair.standing
  have hG := hst.toTheoremFourHyp
  have hAF := hpair.mem_S.1
  have hAe : IsElemAbelian 3 A := hAF.1
  have hAc : ∀ a b : A, a * b = b * a := hAe.1.is_comm.comm
  have hAmax : Maximal (fun B : Subgroup G => IsElemAbelian 3 B) A :=
    ⟨hAe, fun B hB hAB => (hAF.2.1 B hB hAB).le⟩
  have hK := hKW G A E U c L hpair
  obtain ⟨a, haA, ha1, hXa⟩ := mem_thetaComponentFamily_iff.mp hX.1
  have ha3 : a ^ 3 = 1 := hAe.2 a haA
  have hXC := Sec6.le_centralizer_of_mem_thetaComponentsAt hXa
  have hAX : A ≤ Subgroup.normalizer (X : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG hAe haA ha1 X hXa
  have hcomA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAc ⟨x, hx⟩ ⟨y, hy⟩)
  have haC : a ∈ Sec4.thetaQuotCentralizer X := by
    refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨hAX haA, fun l hl => ?_⟩
    have hla : l * a = a * l := Subgroup.mem_centralizer_singleton_iff.mp (hXC hl)
    rw [← hla, mul_inv_cancel_right, inv_mul_cancel]
    exact Subgroup.one_mem _
  have hD : A ⊓ Sec4.thetaQuotCentralizer X = Subgroup.zpowers a := by
    have hcyc := h66 G hst A hpair.mem_S X hX
    have hle : Subgroup.zpowers a ≤ A ⊓ Sec4.thetaQuotCentralizer X :=
      Subgroup.zpowers_le.mpr ⟨haA, haC⟩
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [Nat.card_zpowers, orderOf_eq_prime ha3 ha1]
    have hexp : Monoid.exponent (A ⊓ Sec4.thetaQuotCentralizer X : Subgroup G) ∣ 3 :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact hAe.2 x x.2.1)
    rw [IsCyclic.exponent_eq_card] at hexp
    exact Nat.le_of_dvd (by norm_num) hexp
  have hcard3 : Nat.card (A ⊓ Sec4.thetaQuotCentralizer X : Subgroup G) = 3 := by
    rw [hD, Nat.card_zpowers, orderOf_eq_prime ha3 ha1]
  have hsec : Late.sectionCentralizer A X ((aschbacherSolvableCore 3 X).map X.subtype) =
      (Subgroup.zpowers a : Set G) := by
    rw [Sec13.sectionCentralizer_eq_inf hAX, hD]
  obtain ⟨n, hn1, hno, ⟨eK⟩⟩ := exists_mulEquiv_kOf_odd h222 hpair hA81 hφ
  have hn2 : n ≠ 2 := fun h => by
    rw [h] at hno
    exact (Nat.not_odd_iff_even.mpr even_two) hno
  have hKeq : kOf A φ = kZero A φ := kOf_eq_kZero_of_mulEquiv hK hφ (by omega) hn2 eK
  have := isSimpleGroup_projSL_two (by omega : 2 ≤ n)
  have : IsSimpleGroup (kOf A φ) := eK.isSimpleGroup
  have hKp : Group.IsPerfect (kOf A φ) := isPerfect_of_mulEquiv_projSL (by omega) eK
  have hKB : kOf A φ ≤ Subgroup.centralizer (fixedInG A φ : Set G) :=
    (kOf_le_kZero hK hφ).trans (kZero_le_centralizer A φ)
  obtain ⟨EK, hEKK, hEK, hEK4⟩ :=
    Commute33Steps.exists_fourGroup_of_mulEquiv_projSL (by omega) eK
  have hEK2 : IsPGroup 2 EK := IsPGroup.of_card (n := 2) (by rw [hEK4]; norm_num)
  have hEK1 : EK ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hEK4
    omega
  have hEKcomm : ∀ e ∈ fixedInG A φ, ∀ q ∈ EK, e * q * e⁻¹ = q := fun e he q hq => by
    rw [Subgroup.mem_centralizer_iff.mp (hKB (hEKK hq)) e he, mul_inv_cancel_right]
  have hEmem : fixedInG A φ ∈ partTwoE G := by
    refine ⟨Sec5.isElemAbelian_of_le hAe (Subgroup.map_subtype_le _), ?_, EK, hEK1, hEK2,
      le_normalizer_of_forall_mul_mem fun e he q hq => ?_⟩
    · rw [card_fixedInG_eq hAc hA81 hφ.1]
      norm_num
    · rw [hEKcomm e he q hq]
      exact hq
  have hbar : Sec8.InvTwoBarNontrivial (fixedInG A φ) X :=
    invTwoBarNontrivial_of (hEKK.trans hKX) hEK2 hEK1
      (le_bot_iff.mp ((inf_le_inf_right _ hEKK).trans
        (inf_inSubgroup_theta_eq_bot hKX hKp).le)) hEKcomm
  have hnf := h1134 G A a X hst hAF hA81 haA ha1 ⟨hX, hXa⟩ hsec
    ⟨fixedInG A φ, hEmem, Subgroup.map_subtype_le _, hbar⟩
  have hdiag : ∀ x ∈ A, Sec4.InducesOuterTheta x X → KFacts.InducesStdKind X x .diagonal := by
    intro x hxA hout
    have hx1 : x ≠ 1 := by
      rintro rfl
      exact KFacts.not_inducesOuterTheta_one X hout
    exact inducesStdKind_diagonal_of h47 hG ha3 ha1 hXa (hcomA x hxA a haA)
      (orderOf_eq_prime (hAe.2 x hxA) hx1) hout (hnf x hxA).1 (hnf x hxA).2
  have hnorm : ∀ y ∈ X ⊓ Subgroup.centralizer (fixedInG A φ : Set G), ∀ k ∈ kOf A φ,
      y * k * y⁻¹ ∈ kOf A φ := by
    intro y hy k hk
    rw [hKeq] at hk ⊢
    exact (Subgroup.mem_normalizer_iff.mp
      (Item233One.centralizer_le_normalizer_kZero A φ hy.2) k).mp hk
  obtain ⟨eX⟩ := nonempty_mulEquiv_projSU_of_list hList
    (isList46_of_mem_thetaComponentsAt h46 hG ha3 ha1 hXa) hAe hA81 hAX hcard3 hdiag
    (Subgroup.map_subtype_le _) (card_fixedInG_eq hAc hA81 hφ.1) hKX hKB hnorm ⟨eK⟩ hn1 hno
    fun k hk ⟨eXk⟩ x hxA => not_inducesOuterTheta_of_mem_thetaComponentsAt hG ha3 ha1 hXa hk
      eXk (hcomA x hxA a haA) (hAe.2 x hxA)
  have hθX := hθ G A E U c L hpair hA81 φ hφ X hX hKX n hn1 ⟨eX⟩
  have hθX' : aschbacherSolvableCore 3 X = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).mp hθX
  have eXU : X ≃* projSU 4 2 n := (mulEquiv_lBar_of_theta_eq_bot hθX).trans eX
  have : IsSimpleGroup (projSU 4 2 n) := isSimpleGroup_projSU le_rfl (by omega)
  have : IsSimpleGroup X := eXU.isSimpleGroup
  have hZX : Subgroup.center X = ⊥ :=
    center_eq_bot_of_isSimpleGroup_of_isPerfect (Sec6.isPerfect_of_mem_thetaComponentsAt hXa)
  have hinner : ∀ x ∈ A, ¬ Sec4.InducesOuterTheta x X := fun x hxA =>
    not_inducesOuterTheta_of_mem_thetaComponentsAt hG ha3 ha1 hXa (by omega) eX
      (hcomA x hxA a haA) (hAe.2 x hxA)
  have hdecomp : ∀ b ∈ A, ∃ y ∈ A ⊓ X, y⁻¹ * b ∈ Subgroup.centralizer (X : Set G) := by
    intro b hb
    obtain ⟨y, hyX, hby⟩ := exists_conj_eq_of_not_inducesOuterTheta hθX' (hAX hb) (hinner b hb)
    refine ⟨y, ⟨mem_of_conj_eq hAmax hAX hZX hb hyX hby, hyX⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 := hby l hl
    calc l * (y⁻¹ * b) = y⁻¹ * (y * l * y⁻¹) * b := by group
      _ = y⁻¹ * (b * l * b⁻¹) * b := by rw [h1]
      _ = y⁻¹ * b * l := by group
  have hCA : A ⊓ Subgroup.centralizer (X : Set G) = Subgroup.zpowers a := by
    apply le_antisymm
    · rw [← hD]
      rintro x ⟨hxA, hxC⟩
      refine ⟨hxA, Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨hAX hxA, fun l hl => ?_⟩⟩
      rw [← Subgroup.mem_centralizer_iff.mp hxC l hl, mul_inv_cancel_right, inv_mul_cancel]
      exact Subgroup.one_mem _
    · rw [Subgroup.zpowers_le]
      exact ⟨haA, Subgroup.mem_centralizer_iff.mpr fun l hl =>
        Subgroup.mem_centralizer_singleton_iff.mp (hXC hl)⟩
  have hcardC : Nat.card (A ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) = 3 := by
    rw [hCA, Nat.card_zpowers, orderOf_eq_prime ha3 ha1]
  have hbij : Function.Bijective (fun p : (A ⊓ X : Subgroup G) ×
      (A ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) =>
        (⟨(p.1 : G) * p.2, A.mul_mem p.1.2.1 p.2.2.1⟩ : A)) := by
    constructor
    · rintro ⟨y, z⟩ ⟨y', z'⟩ h
      have h1 : (y : G) * z = y' * z' := congrArg Subtype.val h
      have h2 : (y' : G)⁻¹ * y = z' * (z : G)⁻¹ := by
        calc (y' : G)⁻¹ * y = (y' : G)⁻¹ * (y * z) * (z : G)⁻¹ := by group
          _ = (y' : G)⁻¹ * (y' * z') * (z : G)⁻¹ := by rw [h1]
          _ = z' * (z : G)⁻¹ := by group
      have hm : (y' : G)⁻¹ * y ∈ X := X.mul_mem (X.inv_mem y'.2.2) y.2.2
      have hc : ∀ l ∈ X, ((y' : G)⁻¹ * y) * l * ((y' : G)⁻¹ * y)⁻¹ = l := by
        intro l hl
        rw [h2]
        have hz : (z' : G) * (z : G)⁻¹ ∈ Subgroup.centralizer (X : Set G) :=
          Subgroup.mul_mem _ z'.2.2 (Subgroup.inv_mem _ z.2.2)
        rw [(Subgroup.mem_centralizer_iff.mp hz l hl).symm, mul_inv_cancel_right]
      have h3 := eq_one_of_forall_conj_eq hZX hm hc
      have hyy : (y : G) = y' := by
        rw [inv_mul_eq_one] at h3
        exact h3.symm
      have hzz : (z : G) = z' := by
        rw [hyy] at h1
        exact mul_left_cancel h1
      exact Prod.ext (Subtype.ext hyy) (Subtype.ext hzz)
    · rintro ⟨b, hb⟩
      obtain ⟨y, hy, hyb⟩ := hdecomp b hb
      exact ⟨(⟨y, hy⟩, ⟨y⁻¹ * b, A.mul_mem (A.inv_mem hy.1) hb, hyb⟩),
        Subtype.ext (by simp)⟩
  have hcardA := Nat.card_eq_of_bijective _ hbij
  rw [Nat.card_prod, hcardC, hA81] at hcardA
  exact ⟨n, ⟨hn1, hno, ⟨eXU⟩, ⟨eK⟩, hθX, hZX, hAX, ⟨a, haA, ha1, hXa, hCA⟩, hinner, hdecomp,
    by omega⟩⟩

theorem item223OneInner_of_list (h45 : Sec4.Item4_5) (h46 : Sec4.Item4_6) (h47 : Sec4.Item4_7W)
    (h66 : Sec6.Item6_6) (h1134 : Item1134Four) (hList : Inspection223List)
    (hθ : Item223ThetaTrivial) (h222 : Item222) (hKW : KOfWellDefinedAll) :
    Item223OneInner := by
  intro G _ _ A E U c L hpair hA81 φ hφ X hX hKX
  obtain ⟨m, hm⟩ :=
    item223Print_one_of_list h45 h46 h47 h66 h1134 hList hθ h222 hKW hpair hA81 hφ hX hKX
  obtain ⟨a, haA, ha1, -, hCA⟩ := hm.center
  have hC3 : Nat.card (A ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) = 3 := by
    rw [hCA, Nat.card_zpowers]
    exact orderOf_eq_prime (hpair.mem_S.1.1.2 a haA) ha1
  exact ⟨m, hm.one_lt, hm.odd, hm.equiv, hm.kOf_equiv, hm.theta_eq_bot, hm.inner, hm.card_inf,
    hC3⟩

end CFSG.RankThree.PartTwo.Sec21

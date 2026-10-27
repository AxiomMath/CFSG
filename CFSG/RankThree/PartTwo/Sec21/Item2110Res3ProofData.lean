module

public import CFSG.RankThree.PartTwo.Sec21.Item2110Res2ProofTheta
public import CFSG.RankThree.PartTwo.Sec21.Item2113Res3ProofRankCases
import CFSG.RankThree.PartTwo.Sec21.Item2113Res3ProofRankTools
import CFSG.RankThree.PartOne.S11.SecTenEight
import CFSG.RankThree.Native.MathieuRealThree

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2110Res3Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint
open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem card_center_quot_dvd {P : Type*} [Group P] [Finite P] (hP : IsQuasisimple P) :
    Nat.card (center (P ⧸ aschbacherSolvableCore 3 P)) ∣ Nat.card (center P) := by
  have hθZ := PartOne.theta_le_center_of_quasisimple Nat.prime_three hP
  obtain ⟨-, -, hc⟩ := LocalCores.quasisimple_central_quotient hP _ hθZ
  rw [hc]
  exact card_map_dvd _ _

theorem not_two_dvd_card_center_quot {P : Type*} [Group P] [Finite P] :
    ¬ 2 ∣ Nat.card (center (P ⧸ aschbacherSolvableCore 3 P)) := by
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2
  set X := P ⧸ aschbacherSolvableCore 3 P
  have hX : aschbacherSolvableCore 3 X = ⊥ := theta_quotient_core_and_ranks.1
  have hT : zpowers (t : X) ≤ aschbacherSolvableCore 3 X := by
    obtain ⟨-, -, -, hmax, -⟩ := solvable_prime_complement_core_characterization (H := X)
      Nat.prime_three
    refine hmax _ ?_ ?_ ?_
    · refine ⟨fun x hx g => ?_⟩
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
      have hc : g * (t : X) ^ k * g⁻¹ = (t : X) ^ k := by
        rw [(Commute.zpow_right (mem_center_iff.mp t.2 g) k).eq, mul_inv_cancel_right]
      rw [hc]
      exact zpow_mem (mem_zpowers _) k
    · refine Group.isSolvable_of_comm fun a b => ?_
      obtain ⟨i, hi⟩ := mem_zpowers_iff.mp a.2
      obtain ⟨j, hj⟩ := mem_zpowers_iff.mp b.2
      apply Subtype.ext
      rw [coe_mul, coe_mul, ← hi, ← hj]
      exact (Commute.zpow_zpow_self (t : X) i j).eq
    · rw [Nat.card_zpowers, Subgroup.orderOf_coe, ht]
      norm_num
  rw [hX] at hT
  have h1 : (t : X) = 1 := mem_bot.mp (hT (mem_zpowers (t : X)))
  have h1' : orderOf t = 1 := by rw [← Subgroup.orderOf_coe, h1, orderOf_one]
  rw [h1'] at ht
  norm_num at ht

theorem isTripleCover_lBar_of {S : Type*} [Group S] {I : Subgroup G} (hq : IsQuasisimple I)
    (h6 : Nat.card (center I) ∣ 6) (e : I ⧸ center I ≃* S) {d : G} (hdI : d ∈ I)
    (hdc : ∀ x ∈ I, x * d = d * x) (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) :
    Sec4.IsTripleCover (lBar I) S := by
  set θ := aschbacherSolvableCore 3 I with hθ
  have hθZ : θ ≤ center I := PartOne.theta_le_center_of_quasisimple Nat.prime_three hq
  obtain ⟨-, -, hc⟩ := LocalCores.quasisimple_central_quotient hq θ hθZ
  refine ⟨?_, ⟨((QuotientGroup.quotientMulEquivOfEq hc).trans
    (QuotientGroup.quotientQuotientEquivQuotient θ (center I) hθZ)).trans e⟩⟩
  have hdvd : Nat.card (center (lBar I)) ∣ 6 := (card_center_quot_dvd hq).trans h6
  have h2 : ¬ 2 ∣ Nat.card (center (lBar I)) := not_two_dvd_card_center_quot
  set d₀ : I := ⟨d, hdI⟩
  have hd₀ : d₀ ∈ center I := mem_center_iff.mpr fun g => Subtype.ext (hdc g g.2)
  set db := QuotientGroup.mk' θ d₀ with hdb
  have hdbZ : db ∈ center (lBar I) := by
    rw [hc]
    exact mem_map_of_mem _ hd₀
  have hdb1 : db ≠ 1 := by
    intro h1
    rw [hdb, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hord : orderOf d₀ = 3 :=
      orderOf_eq_prime (Subtype.ext hd3) fun h => hd1 (congrArg Subtype.val h)
    have hdv : orderOf d₀ ∣ Nat.card θ := Subgroup.orderOf_dvd_natCard θ h1
    rw [hord] at hdv
    exact three_not_dvd_card_aschbacherSolvableCore hdv
  have hdb3 : db ^ 3 = 1 := by
    rw [hdb, ← map_pow]
    have : d₀ ^ 3 = 1 := Subtype.ext hd3
    rw [this, map_one]
  have h3 : 3 ∣ Nat.card (center (lBar I)) := by
    have hord : orderOf (⟨db, hdbZ⟩ : center (lBar I)) = 3 := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact orderOf_eq_prime (Subtype.ext hdb3) fun h => hdb1 (congrArg Subtype.val h)
    have h := orderOf_dvd_natCard (⟨db, hdbZ⟩ : center (lBar I))
    rwa [hord] at h
  have hpos : 0 < Nat.card (center (lBar I)) := Nat.card_pos
  have hle : Nat.card (center (lBar I)) ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases h : Nat.card (center (lBar I)) <;> omega

theorem lBar_cases {K : Subgroup G} {d : G} (hdI : d ∈ iOf218 K d)
    (hdc : ∀ x ∈ iOf218 K d, x * d = d * x) (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1)
    (h : (Nonempty (K ≃* NativeSporadic.He) ∧
            Sec4.IsTripleCover (iOf218 K d) (alternatingGroup (Fin 7))) ∨
          ((Nonempty (lBar K ≃* NativeSporadic.M24) ∨ Nonempty (lBar K ≃* NativeSporadic.J2) ∨
              Nonempty (lBar K ≃* NativeSporadic.Ru)) ∧
            Sec4.IsTripleCover (lBar (iOf218 K d)) (alternatingGroup (Fin 6))) ∨
          (Nonempty (K ≃* NativeSporadic.J4) ∧
            Nat.card (Subgroup.center (iOf218 K d)) = 6 ∧
            Nonempty (iOf218 K d ⧸ Subgroup.center (iOf218 K d) ≃* NativeSporadic.M22)) ∨
          (∃ n : ℕ, 0 < n ∧ Even n ∧
            (ChevalleyExceptionalModel (lBar K) .G2 2 n ∨
              ChevalleyExceptionalModel (lBar K) .trialityD4 2 n) ∧
            Nonempty (lBar (iOf218 K d) ≃* SL3 n))) :
    (Sec4.IsTripleCover (lBar (iOf218 K d)) (alternatingGroup (Fin 6)) ∨
        Sec4.IsTripleCover (lBar (iOf218 K d)) (alternatingGroup (Fin 7)) ∨
        Sec4.IsTripleCover (lBar (iOf218 K d)) NativeSporadic.M22) ∨
      ∃ n : ℕ, 0 < n ∧ Even n ∧ Nonempty (lBar (iOf218 K d) ≃* SL3 n) := by
  have hIp := Item2113Res3Proof.isPerfect_iOf218 K d
  rcases h with ⟨-, hcard, ⟨e⟩⟩ | ⟨-, hA6⟩ | ⟨-, hcard, ⟨e⟩⟩ | ⟨n, hn, hev, -, he⟩
  · have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
    obtain ⟨s, m, hs3, hs1, hm⟩ := Item2113Res3Proof.alternating_seven_real
    obtain ⟨hq, -⟩ := Item2113Res3Proof.isQuasisimple_and_exists_of_real hIp e hs3 hs1 hm
    exact Or.inl (Or.inr (Or.inl (isTripleCover_lBar_of hq (by rw [hcard]; norm_num) e hdI hdc
      hd3 hd1)))
  · exact Or.inl (Or.inl hA6)
  · have : IsSimpleGroup NativeSporadic.M22 := CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
    obtain ⟨s, -, m, hs, -, -, hm⟩ := Native.m22_witness
    have hs3 : s ^ 3 = 1 := hs ▸ pow_orderOf_eq_one s
    have hs1 : s ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hs; norm_num at hs
    obtain ⟨hq, -⟩ := Item2113Res3Proof.isQuasisimple_and_exists_of_real hIp e hs3 hs1 hm
    exact Or.inl (Or.inr (Or.inr (isTripleCover_lBar_of hq (by simp [hcard]) e hdI hdc hd3
      hd1)))
  · exact Or.inr ⟨n, hn, hev, he⟩

theorem card_le_three_of_le_center {X : Type} [Group X] [Finite X]
    (h : (Sec4.IsTripleCover X (alternatingGroup (Fin 6)) ∨
        Sec4.IsTripleCover X (alternatingGroup (Fin 7)) ∨
        Sec4.IsTripleCover X NativeSporadic.M22) ∨
      ∃ n : ℕ, 0 < n ∧ Even n ∧ Nonempty (X ≃* SL3 n))
    {H : Subgroup X} (hH : H ≤ center X) : Nat.card H ≤ 3 := by
  have hle : Nat.card H ≤ Nat.card (center X) := card_le_of_le hH
  refine hle.trans ?_
  rcases h with (⟨hc, -⟩ | ⟨hc, -⟩ | ⟨hc, -⟩) | ⟨n, -, -, ⟨e⟩⟩
  · exact hc.le
  · exact hc.le
  · exact hc.le
  · rw [← map_center_eq e.symm, card_map_of_injective e.symm.injective,
      Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (0 : Fin 3)).toEquiv]
    have h3 := card_rootsOfUnity (R := GaloisField 2 n) (k := Fintype.card (Fin 3))
    simpa using h3

theorem isType_of_lBar_cases {X : Type} [Group X]
    (h : (Sec4.IsTripleCover X (alternatingGroup (Fin 6)) ∨
        Sec4.IsTripleCover X (alternatingGroup (Fin 7)) ∨
        Sec4.IsTripleCover X NativeSporadic.M22) ∨
      ∃ n : ℕ, 0 < n ∧ Even n ∧ Nonempty (X ≃* SL3 n)) :
    Sec4.IsTripleCover X (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover X (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover X NativeSporadic.M22 ∨ Sec4.IsSLThreePi X := by
  rcases h with (h | h | h) | ⟨n, hn, ⟨k, hk⟩, ⟨e⟩⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · refine Or.inr (Or.inr (Or.inr ⟨2 ^ n, GaloisField 2 n, inferInstance, inferInstance,
      Or.inl ⟨GaloisField.card 2 n (by omega), ?_,
        ⟨e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 _)⟩⟩⟩))
    rw [hk, ← two_mul, pow_mul, Nat.pow_mod]
    norm_num

theorem mem_thetaComponentsIn_closure {L : Subgroup G} {c d : G}
    (hLc : L ∈ thetaComponentsAt 3 c) (hq : IsQuasisimple (lBar (iOf218 L d))) :
    iOf218 L d ∈ thetaComponentsIn
      (centralizer ((closure {c, d} : Subgroup G) : Set G)) := by
  set H := centralizer ((closure {c, d} : Subgroup G) : Set G) with hH
  set X := L ⊓ centralizer ({d} : Set G) with hX
  set I := iOf218 L d with hI
  obtain ⟨hLC, hL₀⟩ := mem_thetaComponentsIn_iff.mp hLc
  have hmemH : ∀ x : G, x ∈ H ↔ x * c = c * x ∧ x * d = d * x := by
    intro x
    rw [hH, centralizer_closure, mem_centralizer_iff]
    constructor
    · intro h
      exact ⟨(h c (Set.mem_insert c {d})).symm,
        (h d (Set.mem_insert_of_mem c (Set.mem_singleton d))).symm⟩
    · rintro ⟨h1, h2⟩ y hy
      rcases hy with rfl | rfl
      · exact h1.symm
      · exact h2.symm
  have hIX : I ≤ X := map_subtype_le _
  have hHc : H ≤ centralizer ({c} : Set G) := fun x hx =>
    mem_centralizer_singleton_iff.mpr ((hmemH x).mp hx).1
  have hIH : I ≤ H := by
    intro x hx
    obtain ⟨hxL, hxd⟩ := hIX hx
    exact (hmemH x).mpr ⟨mem_centralizer_singleton_iff.mp (hLC hxL),
      mem_centralizer_singleton_iff.mp hxd⟩
  have hXN : X ≤ normalizer (I : Set G) := by
    have h1 := le_normalizer_map (H := layer ↥X) X.subtype
    have htop : normalizer ((layer ↥X : Subgroup ↥X) : Set ↥X) = ⊤ := by
      have := LocalCores.layer_characteristic (G := ↥X)
      exact normalizer_eq_top_iff.mpr inferInstance
    rw [htop, ← MonoidHom.range_eq_map, range_subtype] at h1
    exact h1
  refine mem_thetaComponentsIn_iff.mpr ⟨hIH, ?_, ?_, ?_⟩
  ·
    have := Item2113Res3Proof.isPerfect_iOf218 L d
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hIH).symm.toMonoidHom)
      (MulEquiv.surjective _)
  ·
    have hM : (L.subgroupOf H).IsSubnormal := by
      have h1 := hL₀.2.1.comap (Subgroup.inclusion hHc)
      convert h1 using 1
      ext y
      simp [mem_subgroupOf]
    have hle : I.subgroupOf H ≤ L.subgroupOf H := fun y hy =>
      mem_subgroupOf.mpr (hIX (mem_subgroupOf.mp hy)).1
    refine IsSubnormal.step _ (L.subgroupOf H) hle hM ?_
    rw [normal_subgroupOf_iff hle]
    intro y k hy hk
    rw [mem_subgroupOf] at hy hk ⊢
    have hkX : (k : G) ∈ X := ⟨hk, mem_centralizer_singleton_iff.mpr
      ((hmemH k).mp k.2).2⟩
    simp only [coe_mul, coe_inv]
    exact (mem_normalizer_iff.mp (hXN hkX) _).mp hy
  ·
    set e₀ := subgroupOfEquivOfLe hIH
    exact LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.congr _ _ e₀ (aschbacherSolvableCore_map_mulEquiv Nat.prime_three e₀)).symm
      hq

theorem pCore_center_eq {I : Subgroup G} {d : G} (hdI : d ∈ I) (hdc : ∀ x ∈ I, x * d = d * x)
    (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1)
    (hZ : ∀ H : Subgroup (lBar I), H ≤ center (lBar I) → Nat.card H ≤ 3) :
    inSubgroup (CFSG.pCore 3) (I ⊓ centralizer (I : Set G)) = zpowers d := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z := I ⊓ centralizer (I : Set G) with hZdef
  have hdZ : d ∈ Z := ⟨hdI, mem_centralizer_iff.mpr fun x hx => hdc x hx⟩
  have hZcomm : ∀ a b : Z, a * b = b * a := fun a b => Subtype.ext
    (mem_centralizer_iff.mp (b.2.2) a a.2.1)
  set d₀ : Z := ⟨d, hdZ⟩
  have hd₀3 : d₀ ^ 3 = 1 := Subtype.ext hd3
  have hcard3 : Nat.card (zpowers d) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hd3 hd1]
  have hle : zpowers d ≤ inSubgroup (CFSG.pCore 3) Z := by
    rw [zpowers_le]
    refine ⟨d₀, ?_, rfl⟩
    refine le_sSup (s := {K : Subgroup Z | K.Normal ∧ IsPGroup 3 K}) ⟨?_, ?_⟩ (mem_zpowers d₀)
    · refine ⟨fun x _ g => ?_⟩
      rwa [hZcomm g x, mul_inv_cancel_right]
    · have hdvd : Nat.card (zpowers d₀) ∣ 3 ^ 1 := by
        rw [Nat.card_zpowers, pow_one]
        exact orderOf_dvd_of_pow_eq_one hd₀3
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
      exact IsPGroup.of_card hj
  set P := CFSG.pCore 3 Z with hP
  have hP3 : IsPGroup 3 P := CFSG.pCore_isPGroup (p := 3) (G := Z)
  have hZI : Z ≤ I := inf_le_left
  set P' : Subgroup I := P.map (inclusion hZI) with hP'
  have hP'3 : IsPGroup 3 P' := hP3.map _
  have hcardP' : Nat.card P' = Nat.card P := card_map_of_injective (inclusion_injective hZI)
  set Pb := P'.map (QuotientGroup.mk' (aschbacherSolvableCore 3 I)) with hPb
  have hcardPb : Nat.card Pb = Nat.card P' :=
    Nat.card_image_of_injOn (injOn_mk_of_isPGroup Nat.prime_three hP'3)
  have hPbZ : Pb ≤ center (lBar I) := by
    rintro _ ⟨p, ⟨q, hq, rfl⟩, rfl⟩
    rw [mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 I) g
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact mem_centralizer_iff.mp (q : Z).2.2 g' g'.2
  have hcardP : Nat.card P ≤ 3 := by
    rw [← hcardP', ← hcardPb]
    exact hZ Pb hPbZ
  have hcardIn : Nat.card (inSubgroup (CFSG.pCore 3) Z) ≤ 3 := by
    rw [inSubgroup, card_map_of_injective Z.subtype_injective]
    exact hcardP
  exact (eq_of_le_of_card_ge hle (by rw [hcard3]; exact hcardIn)).symm

theorem item2110IData_of (h219 : Item219) : Item2110IData := by
  intro G _ _ A E U c L hpair hL d hdA hd1 hdcen
  obtain ⟨hdI, hcases⟩ := h219 G A E U c L hpair hL d hdA hd1 hdcen
  obtain ⟨hq, -⟩ := Item2113Res3Proof.lBar_facts_of_item219 hcases
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hpairs.2.2.1
  have hAe := hpair.mem_S.1.1
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  have hIC : iOf218 L d ≤ centralizer ({d} : Set G) := (map_subtype_le _).trans inf_le_right
  have hdc : ∀ x ∈ iOf218 L d, x * d = d * x := fun x hx =>
    mem_centralizer_singleton_iff.mp (hIC hx)
  have hcl := lBar_cases hdI hdc hd3 hd1 hcases
  exact ⟨hdI, mem_thetaComponentsIn_closure hLc hq,
    pCore_center_eq hdI hdc hd3 hd1 fun H hH => card_le_three_of_le_center hcl hH,
    isType_of_lBar_cases hcl⟩

end CFSG.RankThree.PartTwo.Sec21.Item2110Res3Proof

module

public import CFSG.RankThree.PartTwo.Sec21.Item21Res6ProofNoField
import CFSG.RankThree.PartTwo.Sec21.Item2130Res5ProofCube
import CFSG.RankThree.PartTwo.Sec11.FieldCentRigid82
import CFSG.RankThree.PartTwo.Sec8.Item86ResProofKinds
import CFSG.RankThree.PartOne.S10.FiveSuccessorTheta
public import CFSG.RankThree.PartOne.S10.AmbientTheta
public import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
public import CFSG.RankThree.PartTwo.KFacts.K71Lift
public import CFSG.RankThree.PartTwo.Sec21.Item2110Res3ProofAL

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint

namespace Item21Res8Proof

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem mem_zpowers_of_acts_trivially_on {A I J : Subgroup G}
    (hAe : CFSG.Assembly.IsElemAbelian 3 A) (hIJ : I ≤ J) {a d : G} (haA : a ∈ A)
    (haI : a ∈ I) (hdA : d ∈ A) (hdI : d ∈ I) (hdc : ∀ x ∈ I, x * d = d * x) (hd1 : d ≠ 1)
    (haJ : ∀ l ∈ I, l⁻¹ * (a * l * a⁻¹) ∈ inSubgroup (aschbacherSolvableCore 3) J)
    (hZ : ∀ H : Subgroup (lBar I), H ≤ center (lBar I) → Nat.card H ≤ 3) : a ∈ zpowers d := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ := aschbacherSolvableCore 3 ↥I with hθ
  set π := QuotientGroup.mk' θ with hπ
  set a₀ : I := ⟨a, haI⟩
  set d₀ : I := ⟨d, hdI⟩
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  have haZ : π a₀ ∈ center (lBar I) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective θ g
    have hx : (x : G)⁻¹ * (a * x * a⁻¹) ∈ inSubgroup (aschbacherSolvableCore 3) I :=
      Item2110Res3Proof.inSubgroup_theta_inf_le hIJ (Subgroup.mem_inf.mpr ⟨haJ x x.2, I.mul_mem
        (I.inv_mem x.2) (I.mul_mem (I.mul_mem haI x.2) (I.inv_mem haI))⟩)
    obtain ⟨y, hy, hyx⟩ := hx
    have hy' : x⁻¹ * (a₀ * x * a₀⁻¹) ∈ θ := by
      have : y = x⁻¹ * (a₀ * x * a₀⁻¹) := Subtype.ext hyx
      rwa [← this]
    have h1 : π x = π (a₀ * x * a₀⁻¹) := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      exact hy'
    have h2 := congrArg (· * π a₀) h1
    simp only [map_mul, map_inv, inv_mul_cancel_right] at h2
    exact h2
  have hd₀Z : d₀ ∈ center I := mem_center_iff.mpr fun g => Subtype.ext (hdc g g.2)
  have hdZ : π d₀ ∈ center (lBar I) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective θ g
    rw [← map_mul, ← map_mul, mem_center_iff.mp hd₀Z x]
  set P : Subgroup I := A.subgroupOf I with hP
  have hP3 : IsPGroup 3 P := fun x => ⟨1, by
    have hx : ((x : I) : G) ^ 3 = 1 := hAe.2 _ (mem_subgroupOf.mp x.2)
    apply Subtype.ext
    apply Subtype.ext
    simpa using hx⟩
  have hinj := injOn_mk_of_isPGroup Nat.prime_three hP3
  have hd₀P : d₀ ∈ P := mem_subgroupOf.mpr hdA
  have hd₀1 : π d₀ ≠ 1 := by
    intro h
    have h' : π d₀ = π 1 := by rw [h, map_one]
    have := hinj hd₀P (one_mem P) h'
    exact hd1 (congrArg Subtype.val this)
  have hd₀3 : π d₀ ^ 3 = 1 := by
    rw [← map_pow]
    have : d₀ ^ 3 = 1 := Subtype.ext hd3
    rw [this, map_one]
  set H := closure ({π a₀, π d₀} : Set (lBar I)) with hH
  have hHZ : H ≤ center (lBar I) := by
    rw [hH, closure_le]
    rintro x (rfl | rfl)
    · exact haZ
    · exact hdZ
  have hdH : zpowers (π d₀) ≤ H := zpowers_le.mpr (subset_closure (Set.mem_insert_of_mem _ rfl))
  have hcard : Nat.card (zpowers (π d₀)) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hd₀3 hd₀1]
  have hHeq : zpowers (π d₀) = H :=
    eq_of_le_of_card_ge hdH (by rw [hcard]; exact hZ H hHZ)
  have haH : π a₀ ∈ zpowers (π d₀) := hHeq ▸ subset_closure (Set.mem_insert _ _)
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp haH
  have hk' : π (d₀ ^ k) = π a₀ := by rw [map_zpow, hk]
  have heq : d₀ ^ k = a₀ := hinj (zpow_mem hd₀P k) (mem_subgroupOf.mpr haA) hk'
  have : d ^ k = a := congrArg Subtype.val heq
  exact this ▸ zpow_mem (mem_zpowers d) k

section Certs

theorem not_mem_thetaQuotCentralizer_of_field {J : Subgroup G} {x : G}
    (hx : KFacts.InducesStdKind J x .field) : x ∉ Sec4.thetaQuotCentralizer J := by
  intro hxC
  obtain ⟨hxN, hxJ⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp hxC
  have h1N : (1 : G) ∈ normalizer (J : Set G) := one_mem _
  have hx1 : Sec4.thetaQuotMulAut J (Sec4.compAction J ⟨x, hxN⟩) = 1 := by
    refine KFacts.thetaQuotMulAut_compAction_eq_one_of_forall hxN fun y hy => ?_
    have h2 : x * y * x⁻¹ * y⁻¹ = y * (y⁻¹ * (x * y * x⁻¹)) * y⁻¹ := by group
    rw [h2]
    exact (mem_normalizer_iff.mp (Sec6.le_normalizer_theta J hy) _).mp (hxJ y hy)
  have h11 : Sec4.thetaQuotMulAut J (Sec4.compAction J ⟨1, h1N⟩) = 1 :=
    KFacts.thetaQuotMulAut_compAction_eq_one h1N fun y _ => by rw [one_mul, mul_one]
  exact KFacts.not_inducesStdKind_one_field J
    (Sec8.Item86ResProof.inducesStdKind_of_thetaQuotMulAut_eq hx h1N fun hx' => by
      rw [h11, show (⟨x, hx'⟩ : normalizer (J : Set G)) = ⟨x, hxN⟩ from rfl, hx1])

end Certs

theorem two_pow_dvd_card_of_isSLThreePiAt {X : Type} [Group X] {m : ℕ} (hm : 2 ≤ m)
    (hX : Sec4.IsSLThreePiAt X (2 ^ (3 * m))) : 2 ^ 18 ∣ Nat.card X := by
  have hq : (2 ^ (3 * m)) ^ 3 = 2 ^ (9 * m) := by
    rw [← pow_mul]
    ring_nf
  have hdvd : (2 ^ (3 * m)) ^ 3 ∣ Nat.card X := by
    rcases Item2130Res5Proof.card_of_isSLThreePiAt_two_pow (by omega) hX with
        ⟨-, h⟩ | ⟨-, h⟩ <;>
      · rw [h]
        exact Dvd.dvd.mul_right (Dvd.dvd.mul_right dvd_rfl _) _
  rw [hq] at hdvd
  exact (pow_dvd_pow 2 (by omega)).trans hdvd

theorem not_nonempty_projSL_two_eight {X : Type} [Group X] {m : ℕ} (hm : 2 ≤ m)
    (hX : Sec4.IsSLThreePiAt X (2 ^ (3 * m))) :
    ¬ Nonempty (X ≃* CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 3)) := by
  rintro ⟨e⟩
  have h1 := Nat.card_congr e.toEquiv
  rw [Sec21.card_projSL_two 3 (by norm_num)] at h1
  have h2 := two_pow_dvd_card_of_isSLThreePiAt hm hX
  rw [h1] at h2
  norm_num at h2

theorem not_isSLThreePiAt_eight {X : Type} [Group X] {m : ℕ} (hm : 2 ≤ m)
    (hX : Sec4.IsSLThreePiAt X (2 ^ (3 * m))) : ¬ Sec4.IsSLThreePiAt X 8 := by
  intro h8
  have h8' : Sec4.IsSLThreePiAt X (2 ^ 3) := h8
  have h2 := two_pow_dvd_card_of_isSLThreePiAt hm hX
  rcases Item2130Res5Proof.card_of_isSLThreePiAt_two_pow (by norm_num) h8' with ⟨h, -⟩ | ⟨-, h⟩
  · norm_num at h
  · rw [h] at h2
    norm_num at h2

section Main

theorem item2110JField_of_res8 (h211 : Item211) (h45 : Sec4.Item4_5) (h219 : Item219)
    (hAL : Item2110ALInI) (hST : Item1134E27ST) (hN : Sec11.Item1134E27N) :
    Item2110JField := by
  intro G _ _ A E U c L hpair hL d hdA hd1 hdcen J hJ hIJ m hm hIm hJm
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hcA, hc1, hLc, -, hcL⟩ := Item2113Res2Proof.pair_data h45 hpair hL
  have hAe := hpair.mem_S.1.1
  have hG := hpair.standing.toTheoremFourHyp
  have h27' : Nat.card A = 3 ^ 3 := Item2113Proof.card_eq_of_isList218 h211 hpair hL
  have h27 : Nat.card A = 27 := by rw [h27']; norm_num
  have h9 : Nat.card (A ⊓ L : Subgroup G) = 9 :=
    Item2113Res3Proof.card_inf_eq_nine h211 h45 hpair hL
  obtain ⟨hdI, hcases⟩ := h219 G A E U c L hpair hL d hdA hd1 hdcen
  obtain ⟨hq, -⟩ := Item2113Res3Proof.lBar_facts_of_item219 hcases
  have hIL : iOf218 L d ≤ L := (map_subtype_le _).trans inf_le_left
  have hIC : iOf218 L d ≤ centralizer ({d} : Set G) := (map_subtype_le _).trans inf_le_right
  have hdc : ∀ x ∈ iOf218 L d, x * d = d * x := fun x hx =>
    mem_centralizer_singleton_iff.mp (hIC hx)
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  have hcl := Item2110Res3Proof.lBar_cases hdI hdc hd3 hd1 hcases
  have hZ : ∀ H : Subgroup (lBar (iOf218 L d)), H ≤ center (lBar (iOf218 L d)) →
      Nat.card H ≤ 3 := fun H hH => Item2110Res3Proof.card_le_three_of_le_center hcl hH
  have hALI : A ⊓ L ≤ iOf218 L d := hAL G A E U c L hpair hL d hdA hd1 hdcen
  have hm2 : 2 ≤ m := by
    by_contra h
    have hm1 : m = 1 := by omega
    rw [hm1] at hIm
    have hq' := hq
    obtain ⟨hperf, hsimple, -⟩ := hq'
    have : Nontrivial (lBar (iOf218 L d) ⧸ center (lBar (iOf218 L d))) :=
      hsimple.toNontrivial
    have : Nontrivial (lBar (iOf218 L d)) :=
      (QuotientGroup.mk_surjective (s := center (lBar (iOf218 L d)))).nontrivial
    exact Group.IsPerfect.not_isSolvable _
      (Sec11.FieldCentRigid82.isSolvable_of_isSLThreePiAt_two hIm)
  have hAJ : A ≤ normalizer (J : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG hAe hdA hd1 J hJ
  have hJd : J ≤ centralizer ({d} : Set G) := Sec6.le_centralizer_of_mem_thetaComponentsAt hJ
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hLcomp : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hpairs.2.2.1
  have hIin := Item2110Res3Proof.mem_thetaComponentsIn_closure (d := d) hLcomp hq
  have hcI : iOf218 L d ≤ centralizer ({c} : Set G) := hIL.trans hLc
  have hIJc : iOf218 L d ∈ thetaComponentsIn (J ⊓ centralizer ({c} : Set G)) := by
    obtain ⟨hICB, hIθ⟩ := mem_thetaComponentsIn_iff.mp hIin
    have hle1 : iOf218 L d ≤ J ⊓ centralizer ({c} : Set G) := le_inf hIJ hcI
    have hle2 : J ⊓ centralizer ({c} : Set G) ≤
        centralizer ((closure {c, d} : Subgroup G) : Set G) := by
      rintro y ⟨hyJ, hyc⟩
      rw [centralizer_closure, mem_centralizer_iff]
      intro g hg
      rcases hg with rfl | rfl
      · exact (mem_centralizer_singleton_iff.mp hyc).symm
      · exact (mem_centralizer_singleton_iff.mp (hJd hyJ)).symm
    exact mem_thetaComponentsIn_iff.mpr
      ⟨hle1, PartOne.subgroupOf_mem_thetaComponents_of_le Nat.prime_three hle1 hle2 hIθ⟩
  have hc3' : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hfield : KFacts.InducesStdKind J c .field :=
    kSL3PiCubeField_holds G J c (iOf218 L d) m hm hc3' (hAJ hcA) hIJc hJm hIm
  have hcD : c ∉ Sec4.thetaQuotCentralizer J := not_mem_thetaQuotCentralizer_of_field hfield
  have hdJ : d ∈ Sec4.thetaQuotCentralizer J := by
    refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨hAJ hdA, fun l hl => ?_⟩
    have : d * l * d⁻¹ = l := by
      rw [← mem_centralizer_singleton_iff.mp (hJd hl), mul_inv_cancel_right]
    rw [this, inv_mul_cancel]
    exact one_mem _
  have hAcL : zpowers c ⊔ (A ⊓ L) = A := by
    have hle : zpowers c ⊔ (A ⊓ L) ≤ A := sup_le (zpowers_le.mpr hcA) inf_le_left
    have hlt : A ⊓ L < zpowers c ⊔ (A ⊓ L) := by
      refine lt_of_le_of_ne le_sup_right fun h => hcL ?_
      have hc' : c ∈ zpowers c ⊔ (A ⊓ L) := mem_sup_left (mem_zpowers c)
      rw [← h] at hc'
      exact hc'.2
    have hdvd : Nat.card (zpowers c ⊔ (A ⊓ L) : Subgroup G) ∣ 3 ^ 3 := by
      rw [← h27']
      exact card_dvd_of_le hle
    obtain ⟨j, hj, hjc⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    have hgt : 9 < Nat.card (zpowers c ⊔ (A ⊓ L) : Subgroup G) := by
      rw [← h9]
      exact card_lt_of_lt hlt
    have hj3 : j = 3 := by
      rcases j with _ | _ | _ | _ | j
      · rw [hjc] at hgt; norm_num at hgt
      · rw [hjc] at hgt; norm_num at hgt
      · rw [hjc] at hgt; norm_num at hgt
      · rfl
      · omega
    exact eq_of_le_of_card_ge hle (by rw [hjc, hj3, h27'])
  have hθN : A ≤ normalizer (inSubgroup (aschbacherSolvableCore 3) J : Set G) :=
    PartOne.le_normalizer_theta_of_le_normalizer Nat.prime_three hAJ
  have hDd : A ⊓ Sec4.thetaQuotCentralizer J ≤ zpowers d := by
    intro x hx
    obtain ⟨i, hi, b, hb, rfl⟩ := Sec13.exists_pow_mul_of_mem hAe hcA hAcL.symm hx.1
    have hxJ := (Sec6.mem_thetaQuotCentralizer_iff.mp hx.2).2
    have hgA : (c ^ i)⁻¹ ∈ A := A.inv_mem (A.pow_mem hcA i)
    have hbact : ∀ l ∈ iOf218 L d,
        l⁻¹ * (b * l * b⁻¹) ∈ inSubgroup (aschbacherSolvableCore 3) J := by
      intro l hl
      have hlc : l * c = c * l := mem_centralizer_singleton_iff.mp (hcI hl)
      have hgl : c ^ i * l⁻¹ = l⁻¹ * c ^ i := by
        have h1 : Commute l c := hlc
        exact (h1.inv_left.pow_right i).eq.symm
      have e : l⁻¹ * (b * l * b⁻¹) =
          (c ^ i)⁻¹ * (l⁻¹ * (c ^ i * b * l * (c ^ i * b)⁻¹)) * ((c ^ i)⁻¹)⁻¹ := by
        calc l⁻¹ * (b * l * b⁻¹) = (c ^ i)⁻¹ * (c ^ i * l⁻¹) * (b * l * b⁻¹) * c ^ i * (c ^ i)⁻¹ :=
              by group
          _ = (c ^ i)⁻¹ * (l⁻¹ * c ^ i) * (b * l * b⁻¹) * c ^ i * (c ^ i)⁻¹ := by rw [hgl]
          _ = (c ^ i)⁻¹ * (l⁻¹ * (c ^ i * b * l * (c ^ i * b)⁻¹)) * ((c ^ i)⁻¹)⁻¹ := by
              group
      rw [e]
      exact (mem_normalizer_iff.mp (hθN hgA) _).mp (hxJ l (hIJ hl))
    have hbd : b ∈ zpowers d :=
      mem_zpowers_of_acts_trivially_on hAe hIJ hb.1 (hALI hb) hdA hdI hdc hd1 hbact hZ
    have hbD : b ∈ Sec4.thetaQuotCentralizer J := (zpowers_le.mpr hdJ) hbd
    have hgD : c ^ i ∈ Sec4.thetaQuotCentralizer J := by
      have := (Sec4.thetaQuotCentralizer J).mul_mem hx.2
        ((Sec4.thetaQuotCentralizer J).inv_mem hbD)
      rwa [mul_inv_cancel_right] at this
    interval_cases i
    · rwa [pow_zero, one_mul]
    · exact absurd (by simpa using hgD) hcD
    · exfalso
      apply hcD
      have := (Sec4.thetaQuotCentralizer J).pow_mem hgD 2
      rwa [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, hc3, one_mul] at this
  have hJs : J ∈ lStar A := Sec6.mem_lStar_of_inf_le_zpowers hAe hdA hd1 hJ hAJ hDd
  have hDeq : A ⊓ Sec4.thetaQuotCentralizer J = zpowers d :=
    le_antisymm hDd (zpowers_le.mpr ⟨hdA, hdJ⟩)
  have hsc : Late.sectionCentralizer A J ((aschbacherSolvableCore 3 J).map J.subtype) =
      (zpowers d : Set G) := by
    rw [Sec13.sectionCentralizer_eq_inf hAJ, hDeq]
  have hJ8 := not_nonempty_projSL_two_eight hm2 hJm
  have hJU8 := not_isSLThreePiAt_eight hm2 hJm
  have hEF : partTwoE G = partTwoF G := hpair.side (mem_partTwoE_of_card hpair h27')
  by_cases hT : A ∈ partTwoT G
  · exact (hST G A d J hpair.standing hpair.mem_S hT h27 hdA hd1 ⟨hJs, hJ⟩ hsc
      (Or.inr (Or.inr ⟨hJ8, hJU8⟩)) hEF c hcA).1 hfield
  · exact (hN G A d J hpair.standing hpair.mem_S.1 hT h27 hdA hd1 ⟨hJs, hJ⟩ hsc hJ8 hJU8
      (fun _ => hEF) c hcA).1 hfield

theorem item2110JField_of_res8' (h211 : Item211) (h45 : Sec4.Item4_5) (h219 : Item219)
    (hD4 : KF2110ALInID4) (hST : Item1134E27ST) (hN : Sec11.Item1134E27N) :
    Item2110JField :=
  item2110JField_of_res8 h211 h45 h219 (Item2110Res3Proof.item2110ALInI_of h211 h219 hD4) hST hN

end Main

end Item21Res8Proof

end CFSG.RankThree.PartTwo.Sec21

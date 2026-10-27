module

public import CFSG.RankThree.PartTwo.Sec14.Item148Steps
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofSub
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKType
import CFSG.RankThree.PartTwo.Sec14.Item148StepOne
import CFSG.RankThree.PartTwo.Sec14.Concrete
import CFSG.RankThree.PartTwo.Sec4.T444.Lift
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.Sporadic.J2
public import CFSG.GroupTheory.LocalCores.Components
import CFSG.Sporadic.Mathieu.M12
import CFSG.Sporadic.Mathieu.M22

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL projSU)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Main148

section Quot

variable {A Y : Subgroup G} [(ker148 A Y).Normal]

theorem alpha148_ne_one {e : G} (he : e ∈ A) (he1 : e ≠ 1) (he3 : e ^ 3 = 1) :
    alpha148 A Y e he ≠ 1 := by
  intro h
  rw [alpha148_eq_mk', mk'_ker148_eq_one_iff] at h
  exact he1 (eq_one_of_pow_three_pow_eq_one148 (coprime_card_pPrimeCoreOf 3 Y) h (k := 1)
    (by rw [pow_one]; exact he3))

theorem img148_inf_centralizer_alpha148 (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    {J : Subgroup G} (hJM : J ≤ Y ⊔ A) (hAJ : A ≤ Subgroup.normalizer (J : Set G)) {e : G}
    (he : e ∈ A) (he3 : e ^ 3 = 1) :
    img148 A Y J ⊓ Subgroup.centralizer {alpha148 A Y e he} =
      img148 A Y (J ⊓ Subgroup.centralizer {e}) := by
  set N := pPrimeCoreOf 3 Y with hNdef
  have hAN : A ≤ Subgroup.normalizer (N : Set G) :=
    hAY.trans (normalizer_le_normalizer_pPrimeCoreOf 3 Y)
  have hZA : Subgroup.zpowers e ≤ A := Subgroup.zpowers_le.mpr he
  apply le_antisymm
  · rintro x ⟨hxJ, hxc⟩
    obtain ⟨j, hjM, hjJ, rfl⟩ := mem_img148_iff.mp hxJ
    have hxc' := Subgroup.mem_centralizer_singleton_iff.mp hxc
    have hk : ∀ b ∈ Subgroup.zpowers e, j⁻¹ * (b * j * b⁻¹) ∈ N ⊓ J := by
      intro b hb
      have hbA : b ∈ A := hZA hb
      have hbjJ : b * j * b⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp (hAJ hbA) j).mp hjJ
      refine ⟨?_, J.mul_mem (J.inv_mem hjJ) hbjJ⟩
      have hbjM : b * j * b⁻¹ ∈ Y ⊔ A := hJM hbjJ
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      have hcomm : alpha148 A Y e he ^ n *
          QuotientGroup.mk' (ker148 A Y) ⟨j, hjM⟩ * (alpha148 A Y e he ^ n)⁻¹ =
          QuotientGroup.mk' (ker148 A Y) ⟨j, hjM⟩ := by
        have hc : Commute (alpha148 A Y e he) (QuotientGroup.mk' (ker148 A Y) ⟨j, hjM⟩) :=
          hxc'.symm
        rw [(hc.zpow_left n).eq, mul_inv_cancel_right]
      have hmk : QuotientGroup.mk' (ker148 A Y) ⟨j, hjM⟩ =
          QuotientGroup.mk' (ker148 A Y) ⟨e ^ n * j * (e ^ n)⁻¹, hbjM⟩ := by
        rw [← hcomm, alpha148_eq_mk', ← map_zpow, ← map_inv, ← map_mul, ← map_mul]
        rfl
      exact (mk'_ker148_eq_iff.mp hmk)
    have hB3 : IsPGroup 3 (Subgroup.zpowers e) := isPGroup_three_of_pow148 fun b hb => by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, he3, one_zpow]
    have hN3 : Nat.Coprime 3 (Nat.card ↥(N ⊓ J)) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
        (coprime_card_pPrimeCoreOf 3 Y)
    have hBN : Subgroup.zpowers e ≤ Subgroup.normalizer ((N ⊓ J : Subgroup G) : Set G) :=
      fun b hb => Subgroup.inf_normalizer_le_normalizer_inf ⟨hAN (hZA hb), hAJ (hZA hb)⟩
    obtain ⟨y, hy, hyc⟩ := exists_commute_mem_coset148 hB3 hN3 hBN hk
    have hyJ : y ∈ J := by
      have := J.mul_mem hjJ hy.2
      rwa [mul_inv_cancel_left] at this
    have hyM : y ∈ Y ⊔ A := hJM hyJ
    refine mem_img148_iff.mpr ⟨y, hyM, ⟨hyJ, ?_⟩, ?_⟩
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hyc e (Subgroup.mem_zpowers e)).symm
    · exact (mk'_ker148_eq_iff.mpr hy.1).symm
  · rintro x hx
    obtain ⟨d, hdM, ⟨hdJ, hdc⟩, rfl⟩ := mem_img148_iff.mp hx
    refine Subgroup.mem_inf.mpr ⟨mem_img148_iff.mpr ⟨d, hdM, hdJ, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff, alpha148_eq_mk', ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hdc)

omit [Finite G] in
theorem isSubnormal_img148 {K D : Subgroup G} (hKD : K ≤ D) (hDM : D ≤ Y ⊔ A)
    (hK : (K.subgroupOf D).IsSubnormal) :
    ((img148 A Y K).subgroupOf (img148 A Y D)).IsSubnormal := by
  set f : ↥D →* ↥(Y ⊔ A) ⧸ ker148 A Y :=
    (QuotientGroup.mk' (ker148 A Y)).comp (Subgroup.inclusion hDM) with hf
  have hrange : f.range = img148 A Y D := by
    rw [hf, MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have h1 := hK.map (f := f.rangeRestrict) f.rangeRestrict_surjective
  have h2 : (K.subgroupOf D).map f.rangeRestrict = (img148 A Y K).subgroupOf f.range := by
    ext ⟨x, hx⟩
    rw [Subgroup.mem_map, Subgroup.mem_subgroupOf, mem_img148_iff]
    constructor
    · rintro ⟨d, hdK, hdx⟩
      refine ⟨d, hDM d.2, hdK, ?_⟩
      exact congrArg Subtype.val hdx
    · rintro ⟨g, hg, hgK, rfl⟩
      exact ⟨⟨g, hKD hgK⟩, hgK, Subtype.ext rfl⟩
  rw [h2] at h1
  rwa [← hrange]

end Quot

theorem img148_isQuasisimple {A Y J : Subgroup G} [(ker148 A Y).Normal]
    (hJ : J ∈ thetaComponentsIn Y) (h3 : 3 ∣ Nat.card J) :
    IsQuasisimple ↥(img148 A Y J) ∧ aschbacherSolvableCore 3 ↥(img148 A Y J) = ⊥ := by
  obtain ⟨hJY, hJ'⟩ := mem_thetaComponentsIn_iff.mp hJ
  set J' := J.subgroupOf Y with hJ'def
  have h3' : 3 ∣ Nat.card J' := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJY).toEquiv]
  have heq := Sec4.inf_pPrimeCore_eq_of_mem_thetaComponents hJ' h3'
  set φ : ↥Y →* ↥(Y ⊔ A) ⧸ ker148 A Y :=
    (QuotientGroup.mk' (ker148 A Y)).comp (Subgroup.inclusion le_sup_left) with hφ
  have hker : ∀ y : ↥Y, φ y = 1 ↔ y ∈ CFSG.pPrimeCore 3 ↥Y := by
    intro y
    change QuotientGroup.mk' (ker148 A Y) (Subgroup.inclusion le_sup_left y) = 1 ↔ _
    rw [mk'_ker148_eq_one_iff, Subgroup.coe_inclusion, pPrimeCoreOf, Subgroup.mem_map]
    constructor
    · rintro ⟨z, hz, hzy⟩
      have : z = y := Subtype.ext hzy
      exact this ▸ hz
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hM : ∀ l : ↥J', l ∈ aschbacherSolvableCore 3 ↥J' ↔ φ (l : ↥Y) = 1 := by
    intro l
    rw [hker]
    constructor
    · intro hl
      have h1 : (l : ↥Y) ∈ inSubgroup (aschbacherSolvableCore 3) J' := ⟨l, hl, rfl⟩
      rw [← heq] at h1
      exact h1.2
    · intro hl
      have h1 : (l : ↥Y) ∈ J' ⊓ CFSG.pPrimeCore 3 ↥Y := ⟨l.2, hl⟩
      rw [heq] at h1
      obtain ⟨l', hl', he⟩ := h1
      rwa [← Subtype.ext he]
  obtain ⟨η, -⟩ := exists_quotient_mulEquiv_map φ J' (aschbacherSolvableCore 3 ↥J') hM
  have hmap : J'.map φ = img148 A Y J := by
    ext x
    rw [Subgroup.mem_map, mem_img148_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, (le_sup_left : Y ≤ Y ⊔ A) y.2, hy, rfl⟩
    · rintro ⟨g, hg, hgJ, rfl⟩
      exact ⟨⟨g, hJY hgJ⟩, hgJ, rfl⟩
  let η' : ↥J' ⧸ aschbacherSolvableCore 3 ↥J' ≃* ↥(img148 A Y J) :=
    η.trans (MulEquiv.subgroupCongr hmap)
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv η' hJ'.2.2, ?_⟩
  rw [← aschbacherSolvableCore_map_mulEquiv Nat.prime_three η',
    (theta_quotient_core_and_ranks (G := ↥J')).1, Subgroup.map_bot]

theorem mem_zpowers_pow_three {Γ : Type*} [Group Γ] [Finite Γ] {r : Γ}
    (hr : Nat.Coprime 3 (orderOf r)) : r ∈ Subgroup.zpowers (r ^ 3) := by
  rcases Nat.lt_or_ge 1 (orderOf r) with h1 | h1
  · obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime hr h1
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    rw [zpow_natCast, ← pow_mul, ← pow_mod_orderOf, hk, pow_one]
  · have : orderOf r = 1 := le_antisymm h1 (Nat.one_le_iff_ne_zero.mpr (orderOf_pos r).ne')
    rw [orderOf_eq_one_iff.mp this]
    exact Subgroup.one_mem _

theorem aschbacherSolvableCore_sup_eq_bot {Γ : Type*} [Group Γ] [Finite Γ] {L Â : Subgroup Γ}
    (hÂL : Â ≤ Subgroup.normalizer (L : Set Γ)) (hÂ3 : ∀ a ∈ Â, a ^ 3 = 1)
    (hL : aschbacherSolvableCore 3 ↥L = ⊥) : aschbacherSolvableCore 3 ↥(L ⊔ Â) = ⊥ := by
  set C := L ⊔ Â with hCdef
  obtain ⟨hRs, hRc, hR3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥C) Nat.prime_three
  set R := aschbacherSolvableCore 3 ↥C with hRdef
  have hRn : R.Normal := by
    have := hRc
    exact Subgroup.normal_of_characteristic R
  have hLC : L ≤ C := le_sup_left
  have hRL : R.map C.subtype ≤ L := by
    rintro _ ⟨r, hr, rfl⟩
    have hrC : (r : Γ) ∈ (L : Set Γ) * (Â : Set Γ) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left L Â hÂL]
      exact r.2
    obtain ⟨l, hl, a, ha, hla⟩ := hrC
    have hr3 : (r : Γ) ^ 3 ∈ L := by
      have hla' : l * a = (r : Γ) := hla
      have e1 : (r : Γ) ^ 3 = l * (a * l * a⁻¹) * (a * a * l * a⁻¹ * a⁻¹) * (a ^ 3) := by
        rw [← hla', pow_succ, pow_succ, pow_succ, pow_zero, one_mul, pow_succ, pow_succ, pow_succ,
          pow_zero, one_mul]
        group
      rw [e1, hÂ3 a ha, mul_one]
      have h1 : a * l * a⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hÂL ha) l).mp hl
      have h2 : a * a * l * a⁻¹ * a⁻¹ ∈ L := by
        have := (Subgroup.mem_normalizer_iff.mp (hÂL ha) _).mp h1
        simpa [mul_assoc] using this
      exact L.mul_mem (L.mul_mem hl h1) h2
    have hcop : Nat.Coprime 3 (orderOf (r : Γ)) := by
      rw [Subgroup.orderOf_coe]
      have hdvd : orderOf r ∣ Nat.card ↥R := by
        rw [← Subgroup.orderOf_mk r hr]
        exact orderOf_dvd_natCard _
      exact Nat.Coprime.coprime_dvd_right hdvd
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hR3)
    exact (Subgroup.zpowers_le.mpr hr3) (mem_zpowers_pow_three hcop)
  set R' : Subgroup ↥L := (R.map C.subtype).subgroupOf L with hR'def
  have hR'n : R'.Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨r, hr, hrx⟩ := hx
    have hgC : (g : Γ) ∈ C := hLC g.2
    have hrx' : (r : Γ) = (x : Γ) := hrx
    refine ⟨⟨g, hgC⟩ * r * ⟨g, hgC⟩⁻¹, hRn.conj_mem r hr _, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, hrx']
  have hR'iso : ↥R' ≃* ↥R :=
    (Subgroup.subgroupOfEquivOfLe hRL).trans (R.equivMapOfInjective C.subtype
      C.subtype_injective).symm
  have hR's : Group.IsSolvable ↥R' :=
    Group.isSolvable_of_surjective (f := hR'iso.symm.toMonoidHom) hR'iso.symm.surjective
  have hR'3 : ¬ 3 ∣ Nat.card ↥R' := by
    rw [Nat.card_congr hR'iso.toEquiv]
    exact hR3
  have hle := (solvable_prime_complement_core_characterization (H := ↥L)
    Nat.prime_three).2.2.2.1 R' hR'n hR's hR'3
  rw [hL, le_bot_iff] at hle
  rw [eq_bot_iff]
  intro r hr
  have hrL : (r : Γ) ∈ L := hRL ⟨r, hr, rfl⟩
  have : (⟨r, hrL⟩ : ↥L) ∈ R' := ⟨r, hr, rfl⟩
  rw [hle, Subgroup.mem_bot] at this
  have h1 : (r : Γ) = 1 := congrArg Subtype.val this
  exact Subgroup.mem_bot.mpr (Subtype.ext h1)

theorem exists_ne_comm_of_isPerfect {X : Type*} [Group X] [Nontrivial X] (hX : Group.IsPerfect X) :
    ∃ a b : X, a * b ≠ b * a := by
  by_contra h
  push Not at h
  exact Group.IsPerfect.not_isSolvable X (Group.isSolvable_of_comm h)

@[expose] def Type429 (X : Type) [Group X] : Prop :=
  (∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧ Sec4.IsoLThreePi X p e) ∨
    Nonempty (X ≃* alternatingGroup (Fin 7)) ∨
    Nonempty (X ≃* Blueprint.NativeSporadic.M12) ∨
    Nonempty (X ≃* Blueprint.NativeSporadic.M22) ∨
    Nonempty (X ≃* Blueprint.NativeSporadic.J2)

theorem isSimpleGroup_of_type429
    {X : Type} [Group X] (hXp : Group.IsPerfect X)
    (ht : Type429 X) : IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a := by
  have hs : IsSimpleGroup X := by
    rcases ht with ⟨p, e, hp, he, ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
    · have := Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field (GaloisField p e)
      exact MulEquiv.isSimpleGroup φ
    · by_cases hq : p ^ e = 2
      · exfalso
        have hpd : p ∣ 2 := hq ▸ dvd_pow_self p (by omega : e ≠ 0)
        have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp hpd
        subst hp2
        have he1 : e = 1 := Nat.pow_right_injective (le_refl 2) (hq.trans (pow_one 2).symm)
        subst he1
        have hsU := Sec13.isSolvable_projSU_two
        have hsol : Group.IsSolvable X :=
          Group.isSolvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective
        have hcard := KFacts.KS14.card_projSU_three_mul_gcd 2 1 le_rfl
        norm_num at hcard
        have hcX : Nat.card X = 72 := by
          rw [Nat.card_congr φ.toEquiv]
          omega
        have : Finite X := Nat.finite_of_card_ne_zero (by omega)
        have hnt : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
        exact Group.IsPerfect.not_isSolvable X hsol
      · have := Sec19.Step1914TriProof.isSimpleGroup_projSU_three_of_ne_two p e he hq
        exact MulEquiv.isSimpleGroup φ
    · have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
        alternatingGroup.isSimpleGroup (by simp)
      exact MulEquiv.isSimpleGroup φ
    · have := Sporadic.Mathieu.fam_m12_simplicity.2.2
      exact MulEquiv.isSimpleGroup φ
    · have := Sporadic.Mathieu.fam_m22_simplicity.2.2
      exact MulEquiv.isSimpleGroup φ
    · have := Sporadic.J2.fam_j2_simplicity.2.2
      exact MulEquiv.isSimpleGroup φ
  have : Nontrivial X := hs.toNontrivial
  exact ⟨hs, exists_ne_comm_of_isPerfect hXp⟩

theorem three_dvd_card_of_type429 {X : Type} [Group X] (ht : Type429 X) : 3 ∣ Nat.card X := by
  rcases ht with ⟨p, e, hp, he, hiso⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · exact three_dvd_card_of_isoLThreePi148 he hiso
  · rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]
    norm_num
  · rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeM12]
    norm_num
  · rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeM22]
    norm_num
  · rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeJ2]
    norm_num

theorem type429_of_type148 {X : Type} [Group X] (h : Type148 X)
    (hE : ¬ ∃ (p f : ℕ) (_ : Fact p.Prime), p ≠ 3 ∧ 1 ≤ f ∧
      ((p ^ f % 3 = 2 ∧ Nonempty (X ≃* projSL 3 (GaloisField p f))) ∨
        (p ^ f % 3 = 1 ∧ 2 < p ^ f ∧ Nonempty (X ≃* projSU 3 p f)))) : Type429 X := by
  rcases h with ⟨p, e, hp, he, hiso⟩ | ⟨p, f, hp, hp3, hf, hL⟩ | hA7 | hM12 | hM22 | hJ2
  · exact Or.inl ⟨p, e, hp, he, hiso⟩
  · have h3 : ¬ 3 ∣ p ^ f := fun h3 => hp3
      ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp.out).mp
        (Nat.prime_three.dvd_of_dvd_pow h3)).symm
    have hmod : p ^ f % 3 = 1 ∨ p ^ f % 3 = 2 := by omega
    rcases hL with ⟨⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
    · rcases hmod with h1 | h2
      · exact Or.inl ⟨p, f, hp, hf, Or.inl ⟨h1, ⟨φ⟩⟩⟩
      · exact absurd ⟨p, f, hp, hp3, hf, Or.inl ⟨h2, ⟨φ⟩⟩⟩ hE
    · rcases hmod with h1 | h2
      · exact absurd ⟨p, f, hp, hp3, hf, Or.inr ⟨h1, hq, ⟨φ⟩⟩⟩ hE
      · exact Or.inl ⟨p, f, hp, hf, Or.inr ⟨h2, ⟨φ⟩⟩⟩
  · exact Or.inr (Or.inl hA7)
  · exact Or.inr (Or.inr (Or.inl hM12))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hM22)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hJ2)))

end Main148

open Main148

@[expose] def Hyp429In148 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
      ∀ J ∈ thetaComponentsIn Y, A ≤ Subgroup.normalizer (J : Set G) → 3 ∣ Nat.card J →
        letI := ker148_normal hY.2
        SectionFourHyp ↥(img148 A Y (J ⊔ A)) ∧
          partTwoE ↥(img148 A Y (J ⊔ A)) = partTwoF ↥(img148 A Y (J ⊔ A))

section Certificates


@[expose] def Step148Lift429Eps : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
      ∀ (e : G) (he : e ∈ A), e ≠ 1 →
      ∀ K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({e} : Set G)),
      A ≤ Subgroup.normalizer (K : Set G) →
      Late.sectionCentralizer A K (pPrimeCoreOf 3 Y) = (Subgroup.zpowers e : Set G) →
      (letI := ker148_normal hY.2;
        ∃ (p f : ℕ) (_ : Fact p.Prime), p ≠ 3 ∧ 1 ≤ f ∧
          ((p ^ f % 3 = 2 ∧ Nonempty (↥(img148 A Y K) ≃* projSL 3 (GaloisField p f))) ∨
            (p ^ f % 3 = 1 ∧ 2 < p ^ f ∧ Nonempty (↥(img148 A Y K) ≃* projSU 3 p f)))) →
      ∀ J ∈ thetaComponentsIn Y, K ≤ J → A ≤ Subgroup.normalizer (J : Set G) →
        letI := ker148_normal hY.2
        Lift148Eq A Y K J ∨ Lift148Ten A Y K J ∨ Lift148Field A Y e he K J ∨
          Lift148D4 A Y e he K J

theorem step148Lift429_of
    (h429 : Sec4.Item4_29) (hT : Hyp429In148)
    (hEps : Step148Lift429Eps) : Step148Lift429 := by
  intro G _ _ A c L h Y hY hs e he he1 K hK hAK hsec htype J hJ hKJ hAJ
  let := ker148_normal hY.2
  by_cases hE : ∃ (p f : ℕ) (_ : Fact p.Prime), p ≠ 3 ∧ 1 ≤ f ∧
      ((p ^ f % 3 = 2 ∧ Nonempty (↥(img148 A Y K) ≃* projSL 3 (GaloisField p f))) ∨
        (p ^ f % 3 = 1 ∧ 2 < p ^ f ∧ Nonempty (↥(img148 A Y K) ≃* projSU 3 p f)))
  · exact hEps G A c L h Y hY hs e he he1 K hK hAK hsec hE J hJ hKJ hAJ
  have ht := type429_of_type148 htype hE
  have hA : Late.IsE27 A := h.isE27
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  have hKYe : K ≤ Y ⊓ Subgroup.centralizer ({e} : Set G) := le_of_mem_thetaComponentsIn hK
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have hKM : K ≤ Y ⊔ A := hKJ.trans hJM
  have hKe : K ≤ Subgroup.centralizer {e} := hKYe.trans inf_le_right
  have hKp : Group.IsPerfect K := isPerfect_of_mem_thetaComponentsIn hK
  have hKαp : Group.IsPerfect ↥(img148 A Y K) := isPerfect_img148 hKM
  obtain ⟨hKαs, hKαnc⟩ := isSimpleGroup_of_type429 hKαp ht
  have h3J : 3 ∣ Nat.card J := ((three_dvd_card_of_type429 ht).trans
    (card_img148_dvd hKM)).trans (Subgroup.card_dvd_of_le hKJ)
  obtain ⟨hJq, hJθ⟩ := img148_isQuasisimple (A := A) (Y := Y) hJ h3J
  obtain ⟨hC4, hCE⟩ := hT G A c L h Y hY hs J hJ hAJ h3J
  have hCeq : img148 A Y (J ⊔ A) = img148 A Y J ⊔ img148 A Y A := img148_sup hJM le_sup_right
  have hAαJα : img148 A Y A ≤ Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer hAJ
  have hAα3 : ∀ a ∈ img148 A Y A, a ^ 3 = 1 := (img148_isE27 hA).1.2
  have hCθ : aschbacherSolvableCore 3 ↥(img148 A Y (J ⊔ A)) = ⊥ := by
    rw [hCeq]
    exact aschbacherSolvableCore_sup_eq_bot hAαJα hAα3 hJθ
  have hAC : img148 A Y A ≤ img148 A Y (J ⊔ A) := img148_mono le_sup_right
  have hLC : img148 A Y J ≤ img148 A Y (J ⊔ A) := img148_mono le_sup_left
  have hLn : img148 A Y (J ⊔ A) ≤
      Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    rw [hCeq]
    exact sup_le Subgroup.le_normalizer hAαJα
  have hcent := img148_inf_centralizer_eq (A := A) (Y := Y) (J := K) hKM he hKe hsec rfl
  have hCJ := img148_inf_centralizer_alpha148 hY.2 hJM hAJ he (hA3 e he)
  have hKL : img148 A Y K ≤ img148 A Y J ⊓ Subgroup.centralizer {alpha148 A Y e he} := by
    rw [hCJ]
    exact img148_mono (le_inf hKJ hKe)
  have hKsubJ : (K.subgroupOf (J ⊓ Subgroup.centralizer {e})).IsSubnormal := by
    have h1 := (mem_thetaComponentsIn_iff.mp hK).2.2.1
    have hle : J ⊓ Subgroup.centralizer {e} ≤ Y ⊓ Subgroup.centralizer ({e} : Set G) :=
      inf_le_inf_right _ hJY
    have h2 := h1.comap (Subgroup.inclusion hle)
    have heq : (K.subgroupOf (Y ⊓ Subgroup.centralizer ({e} : Set G))).comap
        (Subgroup.inclusion hle) = K.subgroupOf (J ⊓ Subgroup.centralizer {e}) := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rwa [heq] at h2
  have hKsub : ((img148 A Y K).subgroupOf
      (img148 A Y J ⊓ Subgroup.centralizer {alpha148 A Y e he})).IsSubnormal := by
    rw [hCJ]
    exact isSubnormal_img148 (le_inf hKJ hKe) (inf_le_left.trans hJM) hKsubJ
  rcases item4_29_of_le h429 (img148 A Y (J ⊔ A)) hC4 hCθ hCE hAC hLC (img148_isE27 hA)
      (alpha148_mem_img148 he) (alpha148_ne_one he he1 (hA3 e he)) hJq hLn hKL hKαs hKαnc
      hKsub ht hcent.symm with h1 | h2 | h3 | h4
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact Or.inr (Or.inr (Or.inr h4))

theorem step148Lift429Eps_of_step148Lift429 (h : Step148Lift429) : Step148Lift429Eps := by
  intro G _ _ A c L hS Y hY hs e he he1 K hK hAK hsec hE J hJ hKJ hAJ
  let := ker148_normal hY.2
  obtain ⟨p, f, hp, hp3, hf, hcase⟩ := hE
  have htype : Type148 ↥(img148 A Y K) := by
    refine Or.inr (Or.inl ⟨p, f, hp, hp3, hf, ?_⟩)
    rcases hcase with ⟨-, hφ⟩ | ⟨-, hq, hφ⟩
    · exact Or.inl hφ
    · exact Or.inr ⟨hq, hφ⟩
  exact h G A c L hS Y hY hs e he he1 K hK hAK hsec htype J hJ hKJ hAJ

end Certificates

end CFSG.RankThree.PartTwo.Sec14

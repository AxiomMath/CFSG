module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.lemma_10_12_b
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection5.lemma_5_2_b
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection5.theorem_5_3
import Mathlib.GroupTheory.Schreier
import Mathlib.LinearAlgebra.Projectivization.Cardinality

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Statements from BG Section 10

This file records a statement-only scaffold for Section 10 of
`Local Analysis for the Odd Order Theorem`.

The local PDF extraction mangles the Greek letters used in the book. This
module imports the shared Section 10 notation from `FeitThompson.BGsection10.Defs`.
-/

section Section10

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

omit [Finite G] [IsMinCE G] in
/- Lemma 10.13(a). -/
private theorem CFSG.section10_omegaOneCenter_le_rankTwoMaximal
    {p : Nat.Primes} {A P : Subgroup G}
    (hA : A ∈ section10RankTwoMaximalElementaryAbelianSubgroups p G)
    (hAleP : A ≤ P) :
    section10OmegaOneCenter p P ≤ A := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  let Z0 : Subgroup G := section10OmegaOneCenter p P
  have hZ0centA : Z0 ≤ Subgroup.centralizer (A : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact
      Subgroup.mem_centralizer_iff.mp
        (section10_omegaOneCenter_le_centralizer (G := G) (p := p) P
          (by simpa [Z0] using hz)) a (hAleP ha)
  have hZ0elem : IsElementaryAbelian p.val Z0 := by
    have hΩelem : IsElementaryAbelian p.val (Ω₁Z p.val P) :=
      section10_omega1Z_isElementaryAbelian_pre (p := p.val) P
    letI : IsElementaryAbelian p.val (Ω₁Z p.val P) := hΩelem
    change IsElementaryAbelian p.val ((Ω₁Z p.val P).map P.subtype)
    exact section10_isElementaryAbelian_map_pre
      (G := P) (p := p.val) (A := Ω₁Z p.val P) (G' := G) P.subtype
  have hsupElem : IsElementaryAbelian p.val (A ⊔ Z0 : Subgroup G) := by
    letI : IsElementaryAbelian p.val A := hA.1.2
    letI : IsElementaryAbelian p.val Z0 := hZ0elem
    exact section10_isElementaryAbelian_sup_of_le_centralizer
      (G := G) (p := p.val) (E := A) (D := Z0) hZ0centA
  have hAeq : A = A ⊔ Z0 := hA.2.2 (A ⊔ Z0) le_sup_left hsupElem
  intro z hz
  have hzSup : z ∈ A ⊔ Z0 := Subgroup.mem_sup_right (by simpa [Z0] using hz)
  rw [hAeq]
  exact hzSup

private theorem CFSG.section10_omegaOneCenter_card_eq_prime_of_high_rank_pSubgroup
    {p : Nat.Primes} {A P : Subgroup G}
    (hpG : p ∈ subgroupPrimeSet (⊤ : Subgroup G))
    (hA : A ∈ section10RankTwoMaximalElementaryAbelianSubgroups p G)
    (hPp : IsPGroup p.val P) (hAleP : A ≤ P)
    (hPrank : 3 ≤ groupRank P) :
    Nat.card (section10OmegaOneCenter p P) = p.val := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  have hp_dvd_G : p.val ∣ Nat.card G := by
    simpa [subgroupPrimeSet] using hpG
  have hpodd : p.val ≠ 2 := Odd.ne_two_of_dvd_nat IsMinCE.odd_order hp_dvd_G
  have hAsub :
      A.subgroupOf P ∈ section10RankTwoMaximalElementaryAbelianSubgroups p P :=
    section10_rankTwoMaximal_subgroupOf_of_le_pre
      (G := G) (p := p) (A := A) (S := P) hAleP hA.1 hA.2
  have hΩcard :
      Nat.card (Ω₁Z p.val P) = p.val :=
    (lemma_5_2_b (p := p.val) hpodd (R := P) hPp hPrank
      (hE := hAsub.1) (hEmax := hAsub.2)).1
  calc
    Nat.card (section10OmegaOneCenter p P) = Nat.card (Ω₁Z p.val P) := by
      simpa [section10OmegaOneCenter] using
        (Subgroup.card_map_of_injective
          (K := Ω₁Z p.val P) (f := P.subtype) P.subtype_injective)
    _ = p.val := hΩcard

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section10_rankTwoMaximal_ne_bot
    {p : Nat.Primes} {A : Subgroup G}
    (hA : A ∈ section10RankTwoMaximalElementaryAbelianSubgroups p G) :
    A ≠ ⊥ := by
  intro hbot
  have hcard_one : Nat.card A = 1 := (Subgroup.card_eq_one (H := A)).2 hbot
  have hp_dvd_one : p.val ∣ 1 := by
    rw [← hcard_one, hA.1.1]
    simp [pow_two]
  exact p.property.not_dvd_one hp_dvd_one

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section10_nontrivial_of_rankTwoMaximal_le
    {p : Nat.Primes} {A P : Subgroup G}
    (hA : A ∈ section10RankTwoMaximalElementaryAbelianSubgroups p G)
    (hAleP : A ≤ P) :
    Nontrivial P := by
  have hAne : A ≠ ⊥ := section10_rankTwoMaximal_ne_bot (G := G) hA
  have hPne : P ≠ ⊥ := by
    intro hPbot
    exact hAne (le_bot_iff.mp (by simpa [hPbot] using hAleP))
  exact (Subgroup.nontrivial_iff_ne_bot P).2 hPne

omit [IsMinCE G] in
public theorem CFSG.section10_omegaOneCenter_ne_bot_of_nontrivial_pSubgroup
    {p : Nat.Primes} {P : Subgroup G}
    (hPp : IsPGroup p.val P) [Nontrivial P] :
    section10OmegaOneCenter p P ≠ ⊥ := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  have hZ_nontrivial : Nontrivial (Subgroup.center P) := hPp.center_nontrivial
  have hpdvd_center : p.val ∣ Nat.card (Subgroup.center P) := by
    have hcenter_p : IsPGroup p.val (Subgroup.center P) :=
      hPp.to_subgroup (Subgroup.center P)
    rcases (IsPGroup.nontrivial_iff_card
        (p := p.val) (G := Subgroup.center P) (hG := hcenter_p)).1 hZ_nontrivial with
      ⟨n, hn, hcard⟩
    rw [hcard]
    exact dvd_pow_self p.val (Nat.ne_of_gt hn)
  have hΩlocal_ne_bot : Ω₁Z p.val P ≠ ⊥ := by
    simpa [Ω₁Z] using
      omega₁_map_subtype_ne_bot (M := Subgroup.center P) (p := p.val) hpdvd_center
  simpa [section10OmegaOneCenter] using
    section10_map_subtype_ne_bot_of_ne_bot (G := G) (M := P) hΩlocal_ne_bot

omit [IsMinCE G] in
private theorem CFSG.section10_omegaOneCenter_card_eq_prime_or_prime_sq_of_le_rankTwoMaximal
    {p : Nat.Primes} {A P : Subgroup G}
    (hA : A ∈ section10RankTwoMaximalElementaryAbelianSubgroups p G)
    (hPp : IsPGroup p.val P) (hAleP : A ≤ P) :
    Nat.card (section10OmegaOneCenter p P) = p.val ∨
      Nat.card (section10OmegaOneCenter p P) = p.val ^ 2 := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  haveI : Nontrivial P := section10_nontrivial_of_rankTwoMaximal_le (G := G) hA hAleP
  let Z : Subgroup G := section10OmegaOneCenter p P
  have hZne : Z ≠ ⊥ :=
    section10_omegaOneCenter_ne_bot_of_nontrivial_pSubgroup (G := G) (p := p) hPp
  have hZleA : Z ≤ A := section10_omegaOneCenter_le_rankTwoMaximal (G := G) hA hAleP
  have hZelem : IsElementaryAbelian p.val Z := by
    have hΩelem : IsElementaryAbelian p.val (Ω₁Z p.val P) :=
      section10_omega1Z_isElementaryAbelian_pre (p := p.val) P
    letI : IsElementaryAbelian p.val (Ω₁Z p.val P) := hΩelem
    change IsElementaryAbelian p.val ((Ω₁Z p.val P).map P.subtype)
    exact section10_isElementaryAbelian_map_pre
      (G := P) (p := p.val) (A := Ω₁Z p.val P) (G' := G) P.subtype
  have hZp : IsPGroup p.val Z := by
    letI : IsElementaryAbelian p.val Z := hZelem
    exact IsElementaryAbelian.isPGroup p.val Z
  rcases hZp.exists_card_eq with ⟨k, hk⟩
  have hk_pos : 0 < k := by
    by_contra hk_not
    have hk0 : k = 0 := by omega
    have hZcard_one : Nat.card Z = 1 := by simpa [hk0] using hk
    exact hZne ((Subgroup.card_eq_one (H := Z)).1 hZcard_one)
  have hk_le_two : k ≤ 2 := by
    have hcard_le : Nat.card Z ≤ p.val ^ 2 := by
      simpa [Z, hA.1.1] using Subgroup.card_le_of_le hZleA
    rw [hk] at hcard_le
    exact (Nat.pow_le_pow_iff_right p.property.one_lt).1 hcard_le
  have hk_cases : k = 1 ∨ k = 2 := by omega
  rcases hk_cases with hk1 | hk2
  · left
    simpa [hk1] using hk
  · right
    simpa [hk2] using hk

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section10_omegaOneCenter_mem_primeOrder_of_card
    {p : Nat.Primes} {A P : Subgroup G}
    (hA : A ∈ section10RankTwoMaximalElementaryAbelianSubgroups p G)
    (hAleP : A ≤ P)
    (hZcard : Nat.card (section10OmegaOneCenter p P) = p.val) :
    section10OmegaOneCenter p P ∈ section10PrimeOrderSubgroupsIn p A := by
  exact ⟨section10_omegaOneCenter_le_rankTwoMaximal (G := G) hA hAleP, hZcard⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section10_exists_sylow_over_pSubgroup
    {p : Nat.Primes} {P : Subgroup G} (hPp : IsPGroup p.val P) :
    ∃ S : Sylow p.val G, P ≤ (S : Subgroup G) := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  exact IsPGroup.exists_le_sylow (G := G) (p := p.val) hPp

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section10_omegaOneCenter_le_of_le_rankTwoMaximal
    {p : Nat.Primes} {A P S : Subgroup G}
    (hA : A ∈ section10RankTwoMaximalElementaryAbelianSubgroups p G)
    (hAleP : A ≤ P) (hPleS : P ≤ S) (hAleS : A ≤ S) :
    section10OmegaOneCenter p S ≤ section10OmegaOneCenter p P := by
  classical
  intro x hx
  change x ∈ (Ω₁Z p.val S).map S.subtype at hx
  rcases Subgroup.mem_map.mp hx with ⟨xS, hxSΩ, hx_eq⟩
  have hxS_center : xS ∈ Subgroup.center S :=
    section10_omega1Z_le_center_pre p.val S hxSΩ
  have hxP : x ∈ P := by
    exact hAleP
      (section10_omegaOneCenter_le_rankTwoMaximal (G := G) hA hAleS (by
        simpa [section10OmegaOneCenter] using hx))
  let xP : P := ⟨x, hxP⟩
  have hxP_center : xP ∈ Subgroup.center P := by
    rw [Subgroup.mem_center_iff]
    intro yP
    let yS : S := ⟨(yP : G), hPleS yP.property⟩
    have hcommS : xS * yS = yS * xS :=
      (Subgroup.mem_center_iff.mp hxS_center yS).symm
    apply Subtype.ext
    simpa [xP, yS, ← hx_eq] using (congrArg (fun z : S => (z : G)) hcommS).symm
  have hxPpow : xP ^ p.val = 1 := by
    have hxSpow : xS ^ p.val = 1 := by
      haveI : Fact p.val.Prime := ⟨p.property⟩
      have hΩelem : IsElementaryAbelian p.val (Ω₁Z p.val S) :=
        section10_omega1Z_isElementaryAbelian_pre (p := p.val) S
      letI : IsElementaryAbelian p.val (Ω₁Z p.val S) := hΩelem
      exact elemPow_eq_one_of_isElementaryAbelian xS hxSΩ
    apply Subtype.ext
    simpa [xP, ← hx_eq] using congrArg (fun z : S => (z : G)) hxSpow
  have hxPΩ : xP ∈ Ω₁Z p.val P := by
    change xP ∈ (omega₁ (G := Subgroup.center P) (p := p.val)).map
      (Subgroup.center P).subtype
    let xC : Subgroup.center P := ⟨xP, hxP_center⟩
    have hxCΩ : xC ∈ omega₁ (G := Subgroup.center P) (p := p.val) := by
      change xC ∈ Subgroup.closure {y : Subgroup.center P | y ^ (p.val ^ 1) = 1}
      refine Subgroup.subset_closure ?_
      apply Subtype.ext
      simpa [pow_one, xC] using hxPpow
    exact Subgroup.mem_map_of_mem (Subgroup.center P).subtype hxCΩ
  change x ∈ (Ω₁Z p.val P).map P.subtype
  exact Subgroup.mem_map.mpr ⟨xP, hxPΩ, rfl⟩

omit [IsMinCE G] in
private theorem CFSG.section10_omegaOneCenter_eq_of_le_card_prime
    {p : Nat.Primes} {P S : Subgroup G}
    (hle : section10OmegaOneCenter p S ≤ section10OmegaOneCenter p P)
    (hPcard : Nat.card (section10OmegaOneCenter p P) = p.val)
    (hScard : Nat.card (section10OmegaOneCenter p S) = p.val) :
    section10OmegaOneCenter p P = section10OmegaOneCenter p S := by
  exact
    (Subgroup.eq_of_le_of_card_ge hle (by rw [hPcard, hScard])).symm

private theorem CFSG.section10_sylow_omegaOneCenter_card_eq_prime_of_high_rank
    {p : Nat.Primes} {A : Subgroup G} (S : Sylow p.val G)
    (hpG : p ∈ subgroupPrimeSet (⊤ : Subgroup G))
    (hA : A ∈ section10RankTwoMaximalElementaryAbelianSubgroups p G)
    (hAleS : A ≤ (S : Subgroup G)) (hSrank : 3 ≤ groupRank (S : Subgroup G)) :
    Nat.card (section10OmegaOneCenter p (S : Subgroup G)) = p.val := by
  exact
    section10_omegaOneCenter_card_eq_prime_of_high_rank_pSubgroup
      (G := G) (p := p) (A := A) (P := (S : Subgroup G))
      hpG hA S.isPGroup' hAleS hSrank

omit [IsMinCE G] in
private theorem CFSG.section10_prime_order_subgroups_disjoint_of_ne
    {p : Nat.Primes} {A X Y : Subgroup G}
    (_hA : A ∈ section10RankTwoMaximalElementaryAbelianSubgroups p G)
    (hX : X ∈ section10PrimeOrderSubgroupsIn p A)
    (hY : Y ∈ section10PrimeOrderSubgroupsIn p A) (hXY : X ≠ Y) :
    Disjoint X Y := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  rw [Subgroup.disjoint_def]
  intro z hzX hzY
  by_contra hz_ne
  have hXsubY_top : X.subgroupOf Y = ⊤ := by
    haveI : Fact (Nat.card Y).Prime := ⟨by simpa [hY.2] using p.property⟩
    have hsub_ne_bot : X.subgroupOf Y ≠ ⊥ := by
      intro hbot
      have hzsub : (⟨z, hzY⟩ : Y) ∈ X.subgroupOf Y := hzX
      have hzbot : (⟨z, hzY⟩ : Y) ∈ (⊥ : Subgroup Y) := by
        simpa [hbot] using hzsub
      exact hz_ne (by simpa using congrArg Subtype.val (Subgroup.mem_bot.mp hzbot))
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card (X.subgroupOf Y) with hbot | htop
    · exact False.elim (hsub_ne_bot hbot)
    · exact htop
  have hYleX : Y ≤ X := by
    intro y hy
    have hy_top : (⟨y, hy⟩ : Y) ∈ (⊤ : Subgroup Y) := by simp
    rw [← hXsubY_top] at hy_top
    change y ∈ X at hy_top
    exact hy_top
  have hXYcard : Nat.card X ≤ Nat.card Y := by
    rw [hX.2, hY.2]
  have hYX' : Y = X :=
    Subgroup.eq_of_le_of_card_ge hYleX hXYcard
  have hYX : X = Y := hYX'.symm
  exact hXY hYX

omit [IsMinCE G] in
private theorem CFSG.section10_rankTwo_eq_sup_of_distinct_prime_order
    {p : Nat.Primes} {A X Y : Subgroup G}
    (hA : A ∈ section10RankTwoMaximalElementaryAbelianSubgroups p G)
    (hX : X ∈ section10PrimeOrderSubgroupsIn p A)
    (hY : Y ∈ section10PrimeOrderSubgroupsIn p A) (hXY : X ≠ Y) :
    A = X ⊔ Y := by
  classical
  have hdisj : Disjoint X Y :=
    section10_prime_order_subgroups_disjoint_of_ne (G := G) hA hX hY hXY
  have hsup_le_A : X ⊔ Y ≤ A := sup_le hX.1 hY.1
  have hX_norm : (X.subgroupOf (X ⊔ Y : Subgroup G)).Normal := by
    have hXYcomm : IsMulCommutative (X ⊔ Y : Subgroup G) := by
      letI : IsElementaryAbelian p.val A := hA.1.2
      refine ⟨⟨fun x y => ?_⟩⟩
      apply Subtype.ext
      exact setLike_mul_comm (s := A)
        (hsup_le_A x.property) (hsup_le_A y.property)
    letI : IsMulCommutative (X ⊔ Y : Subgroup G) := hXYcomm
    letI : CommGroup (X ⊔ Y : Subgroup G) := IsMulCommutative.instCommGroup
    infer_instance
  have hcomp :
      (X.subgroupOf (X ⊔ Y : Subgroup G)).IsComplement'
        (Y.subgroupOf (X ⊔ Y : Subgroup G)) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    ·
        rw [Subgroup.disjoint_def]
        intro z hzX hzY
        apply Subtype.ext
        exact Subgroup.disjoint_def.mp hdisj hzX hzY
    · rw [Set.eq_univ_iff_forall]
      intro z
      let XD : Subgroup (X ⊔ Y : Subgroup G) := X.subgroupOf (X ⊔ Y : Subgroup G)
      let YD : Subgroup (X ⊔ Y : Subgroup G) := Y.subgroupOf (X ⊔ Y : Subgroup G)
      haveI : XD.Normal := by simpa [XD] using hX_norm
      have hsup_top : XD ⊔ YD = ⊤ := by
        simpa [XD, YD] using
          (Subgroup.subgroupOf_sup (A := X) (A' := Y) (B := X ⊔ Y)
            le_sup_left le_sup_right).symm
      have hz : z ∈ XD ⊔ YD := by simp [hsup_top]
      rcases (Subgroup.mem_sup_of_normal_left
          (x := z) (s := XD) (t := YD)).1 hz with
        ⟨x, hxX, y, hyY, hxy⟩
      exact ⟨x, hxX, y, hyY, hxy⟩
  have hsup_card : Nat.card (X ⊔ Y : Subgroup G) = p.val ^ 2 := by
    have hmul := hcomp.card_mul
    rw [natCard_subgroupOf_eq X (X ⊔ Y : Subgroup G) le_sup_left,
      natCard_subgroupOf_eq Y (X ⊔ Y : Subgroup G) le_sup_right,
      hX.2, hY.2] at hmul
    simpa [pow_two] using hmul.symm
  exact
    (Subgroup.eq_of_le_of_card_ge hsup_le_A (by rw [hA.1.1, hsup_card])).symm

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section10_isMulCommutative_sup_of_le_centralizer
    {A Y : Subgroup G}
    (hAcomm : IsMulCommutative A) (hYcomm : IsMulCommutative Y)
    (hYleCentA : Y ≤ Subgroup.centralizer (A : Set G)) :
    IsMulCommutative (A ⊔ Y : Subgroup G) := by
  classical
  let D : Subgroup G := A ⊔ Y
  let AD : Subgroup D := A.subgroupOf D
  let YD : Subgroup D := Y.subgroupOf D
  have hA_norm_Y : A ≤ Subgroup.normalizer (Y : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have hcomm : a * y = y * a :=
        Subgroup.mem_centralizer_iff.mp (hYleCentA hy) a ha
      have hconj : a * y * a⁻¹ = y := by
        calc
          a * y * a⁻¹ = y * a * a⁻¹ := by rw [hcomm]
          _ = y := by simp [mul_assoc]
      simpa [hconj] using hy
    · intro hy
      let y' : G := a * y * a⁻¹
      have hy'Y : y' ∈ Y := by simpa [y'] using hy
      have hcomm' : a * y' = y' * a :=
        Subgroup.mem_centralizer_iff.mp (hYleCentA hy'Y) a ha
      have hconj : a⁻¹ * y' * a = y' := by
        have h := congrArg (fun t : G => a⁻¹ * t) hcomm'
        simpa [mul_assoc] using h.symm
      have hy_eq : y = y' := by
        calc
          y = a⁻¹ * y' * a := by simp [y', mul_assoc]
          _ = y' := hconj
      simpa [hy_eq] using hy'Y
  haveI : YD.Normal := by
    simpa [D, YD] using
      (Subgroup.normal_subgroupOf_sup_of_le_normalizer
        (H := A) (N := Y) hA_norm_Y)
  have hAD_YD_top : AD ⊔ YD = ⊤ := by
    calc
      AD ⊔ YD = D.subgroupOf D := by
        symm
        exact Subgroup.subgroupOf_sup
          (A := A) (A' := Y) (B := D)
          (by simp [D])
          (by simp [D])
      _ = ⊤ := by simp
  refine ⟨⟨fun x y => ?_⟩⟩
  have hxTop : x ∈ AD ⊔ YD := by simp [hAD_YD_top]
  have hyTop : y ∈ AD ⊔ YD := by simp [hAD_YD_top]
  rcases (Subgroup.mem_sup_of_normal_right (s := AD) (t := YD) (x := x)).1 hxTop with
    ⟨aD, haD, bD, hbD, hxab⟩
  rcases (Subgroup.mem_sup_of_normal_right (s := AD) (t := YD) (x := y)).1 hyTop with
    ⟨cD, hcD, dD, hdD, hycd⟩
  let a : G := aD
  let b : G := bD
  let c : G := cD
  let d : G := dD
  have haA : a ∈ A := by simpa [a, AD, Subgroup.mem_subgroupOf] using haD
  have hbY : b ∈ Y := by simpa [b, YD, Subgroup.mem_subgroupOf] using hbD
  have hcA : c ∈ A := by simpa [c, AD, Subgroup.mem_subgroupOf] using hcD
  have hdY : d ∈ Y := by simpa [d, YD, Subgroup.mem_subgroupOf] using hdD
  have hx_eq : (x : G) = a * b := by
    have hval := congrArg (fun z : D => (z : G)) hxab
    simpa [a, b] using hval.symm
  have hy_eq : (y : G) = c * d := by
    have hval := congrArg (fun z : D => (z : G)) hycd
    simpa [c, d] using hval.symm
  have hac : a * c = c * a :=
    setLike_mul_comm (s := A) haA hcA
  have hbd : b * d = d * b :=
    setLike_mul_comm (s := Y) hbY hdY
  have hbc : b * c = c * b :=
    (Subgroup.mem_centralizer_iff.mp (hYleCentA hbY) c hcA).symm
  have had : a * d = d * a :=
    Subgroup.mem_centralizer_iff.mp (hYleCentA hdY) a haA
  apply Subtype.ext
  change (x : G) * (y : G) = (y : G) * (x : G)
  rw [hx_eq, hy_eq]
  calc
    (a * b) * (c * d) = a * (b * c) * d := by simp [mul_assoc]
    _ = a * (c * b) * d := by rw [hbc]
    _ = (a * c) * (b * d) := by simp [mul_assoc]
    _ = (c * a) * (d * b) := by rw [hac, hbd]
    _ = c * (a * d) * b := by simp [mul_assoc]
    _ = c * (d * a) * b := by rw [had]
    _ = (c * d) * (a * b) := by simp [mul_assoc]

omit [IsMinCE G] in
private theorem CFSG.section10_omegaOneCenter_card_eq_prime_of_nonabelian_le_abelian_centralizer
    {p : Nat.Primes} {A P S : Subgroup G}
    (hA : A ∈ section10RankTwoMaximalElementaryAbelianSubgroups p G)
    (hPp : IsPGroup p.val P) (hPnonab : ¬ IsMulCommutative P)
    (hAleP : A ≤ P) (hPleS : P ≤ S)
    (hCScomm : IsMulCommutative (subgroupCentralizerIn S A)) :
    Nat.card (section10OmegaOneCenter p P) = p.val := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  have hZ₀small :=
    section10_omegaOneCenter_card_eq_prime_or_prime_sq_of_le_rankTwoMaximal
      (G := G) (p := p) (A := A) (P := P) hA hPp hAleP
  rcases hZ₀small with hprime | hsquare
  · exact hprime
  · have hZ₀eqA : section10OmegaOneCenter p P = A :=
      Subgroup.eq_of_le_of_card_ge
        (section10_omegaOneCenter_le_rankTwoMaximal (G := G) hA hAleP)
        (by rw [hA.1.1, hsquare])
    have hAleCenterP : A ≤ Subgroup.centralizer (P : Set G) := by
      intro a ha
      have haZ : a ∈ section10OmegaOneCenter p P := by simpa [hZ₀eqA] using ha
      exact section10_omegaOneCenter_le_centralizer (G := G) (p := p) P haZ
    have hPleCS : P ≤ subgroupCentralizerIn S A := by
      intro x hx
      refine ⟨hPleS hx, ?_⟩
      change x ∈ Subgroup.centralizer (A : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact (Subgroup.mem_centralizer_iff.mp (hAleCenterP ha) x hx).symm
    have hPcomm : IsMulCommutative P := by
      letI : IsMulCommutative (subgroupCentralizerIn S A) := hCScomm
      refine ⟨⟨fun x y => ?_⟩⟩
      let xC : subgroupCentralizerIn S A := ⟨(x : G), hPleCS x.property⟩
      let yC : subgroupCentralizerIn S A := ⟨(y : G), hPleCS y.property⟩
      have hcomm : xC * yC = yC * xC :=
        (IsMulCommutative.is_comm (M := subgroupCentralizerIn S A)).comm xC yC
      apply Subtype.ext
      simpa [xC, yC] using congrArg Subtype.val hcomm
    exact False.elim (hPnonab hPcomm)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section10_centralizerIn_isMulCommutative_of_eq_prime_cyclic_sup
    {p : Nat.Primes} {A S A₀ Y : Subgroup G}
    (hA : A ∈ section10RankTwoMaximalElementaryAbelianSubgroups p G)
    (hA₀ : A₀ ∈ section10PrimeOrderSubgroupsIn p A)
    (hYleC : Y ≤ subgroupCentralizerIn S A)
    (hYcyc : IsCyclic Y)
    (hCeq : subgroupCentralizerIn S A = A₀ ⊔ Y) :
    IsMulCommutative (subgroupCentralizerIn S A) := by
  classical
  have hA₀comm : IsMulCommutative A₀ := by
    letI : IsElementaryAbelian p.val A := hA.1.2
    refine ⟨⟨fun x y => ?_⟩⟩
    apply Subtype.ext
    exact setLike_mul_comm (s := A)
      (hA₀.1 x.property) (hA₀.1 y.property)
  have hYcomm : IsMulCommutative Y := by
    letI : CommGroup Y := IsCyclic.commGroup
    infer_instance
  have hYleCentA₀ : Y ≤ Subgroup.centralizer (A₀ : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact Subgroup.mem_centralizer_iff.mp (hYleC hy).2 a (hA₀.1 ha)
  have hSupComm : IsMulCommutative (A₀ ⊔ Y : Subgroup G) :=
    section10_isMulCommutative_sup_of_le_centralizer
      (G := G) hA₀comm hYcomm hYleCentA₀
  rw [hCeq]
  exact hSupComm

omit [IsMinCE G] in
private theorem CFSG.section10_exists_prime_order_complement_to_prime_order_in_rank_two
    {p : Nat.Primes} {A Z : Subgroup G}
    (hA : A ∈ section10RankTwoMaximalElementaryAbelianSubgroups p G)
    (hZ : Z ∈ section10PrimeOrderSubgroupsIn p A) :
    ∃ A₁ : Subgroup G,
      A₁ ∈ section10PrimeOrderSubgroupsIn p A ∧ A₁ ≠ Z ∧ A = A₁ ⊔ Z := by
  classical
  letI : IsElementaryAbelian p.val A := hA.1.2
  have hZsub_card : Nat.card (Z.subgroupOf A) = p.val := by
    simpa using natCard_subgroupOf_eq Z A hZ.1 |>.trans hZ.2
  obtain ⟨z, hzZ, hzne⟩ : ∃ z : G, z ∈ Z ∧ z ≠ 1 := by
    by_contra h
    have hZbot : Z = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro z hz
      by_contra hz_ne
      exact h ⟨z, hz, hz_ne⟩
    have hcard_one : Nat.card Z = 1 := (Subgroup.card_eq_one (H := Z)).2 hZbot
    have hp_one : p.val ∣ 1 := by
      rw [← hcard_one, hZ.2]
    exact p.property.not_dvd_one hp_one
  let zA : A := ⟨z, hZ.1 hzZ⟩
  have hzA_ne : zA ≠ 1 := by
    intro h
    exact hzne (by simpa [zA] using congrArg Subtype.val h)
  obtain ⟨wA, hwA_ne, hlin⟩ :
      ∃ w : A, w ≠ 1 ∧ w ∉ Z.subgroupOf A := by
    by_contra h
    have htop : Z.subgroupOf A = ⊤ := by
      rw [Subgroup.eq_top_iff']
      intro a
      by_cases ha : a = 1
      · simp [ha]
      · exact by
          by_contra hanot
          exact h ⟨a, ha, hanot⟩
    have hAcard_eq_Zsub : Nat.card A = Nat.card (Z.subgroupOf A) := by
      rw [htop]
      exact (Subgroup.card_top (G := A)).symm
    have hpow_ne : p.val ^ 2 ≠ p.val := by
      exact ne_of_gt <| by
        calc
          p.val = p.val * 1 := by rw [mul_one]
          _ < p.val * p.val :=
            Nat.mul_lt_mul_of_pos_left p.property.one_lt p.property.pos
          _ = p.val ^ 2 := by rw [pow_two]
    exact hpow_ne (by rw [← hA.1.1, hAcard_eq_Zsub, hZsub_card])
  let A₁ : Subgroup G := Subgroup.zpowers (wA : G)
  have hwA_pow : wA ^ p.val = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p.val A) wA
  have hw_pow : ((wA : G) ^ p.val = 1) := by
    simpa using congrArg Subtype.val hwA_pow
  have hA₁card : Nat.card A₁ = p.val := by
    calc
      Nat.card A₁ = orderOf (wA : G) := by simp [A₁]
      _ = p.val := by
        haveI : Fact p.val.Prime := ⟨p.property⟩
        exact orderOf_eq_prime hw_pow (by
          intro h
          exact hwA_ne (Subtype.ext h))
  have hA₁leA : A₁ ≤ A := by
    exact (Subgroup.zpowers_le).2 wA.property
  have hA₁mem : A₁ ∈ section10PrimeOrderSubgroupsIn p A := ⟨hA₁leA, hA₁card⟩
  have hA₁neZ : A₁ ≠ Z := by
    intro h
    exact hlin (by
      change (wA : G) ∈ Z
      rw [← h]
      exact Subgroup.mem_zpowers (wA : G))
  exact ⟨A₁, hA₁mem, hA₁neZ,
    section10_rankTwo_eq_sup_of_distinct_prime_order
      (G := G) (p := p) (A := A) (X := A₁) (Y := Z)
      hA hA₁mem hZ hA₁neZ⟩

private theorem CFSG.section10_high_rank_sylow_centralizer_split_of_prime_order
    {p : Nat.Primes} {A B : Subgroup G} (S : Sylow p.val G)
    (hpG : p ∈ subgroupPrimeSet (⊤ : Subgroup G))
    (hA : A ∈ section10RankTwoMaximalElementaryAbelianSubgroups p G)
    (hAleS : A ≤ (S : Subgroup G)) (hSrank : 3 ≤ groupRank (S : Subgroup G))
    (hB : B ∈ section10PrimeOrderSubgroupsIn p A)
    (hBneZ : B ≠ section10OmegaOneCenter p (S : Subgroup G)) :
    ∃ Y : Subgroup G,
      section10OmegaOneCenter p (S : Subgroup G) ≤ Y ∧
        Y ≤ subgroupCentralizerIn (S : Subgroup G) A ∧
        IsCyclic Y ∧
        Disjoint B Y ∧
        subgroupCentralizerIn (S : Subgroup G) A = B ⊔ Y := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  have hp_dvd_G : p.val ∣ Nat.card G := by
    simpa [subgroupPrimeSet] using hpG
  have hpodd : p.val ≠ 2 :=
    Odd.ne_two_of_dvd_nat IsMinCE.odd_order hp_dvd_G
  have hAsubS :
      A.subgroupOf (S : Subgroup G) ∈ section10RankTwoMaximalElementaryAbelianSubgroups p S :=
    section10_rankTwoMaximal_subgroupOf_of_le_pre
      (G := G) (p := p) (A := A) (S := (S : Subgroup G)) hAleS hA.1 hA.2
  have hZ₁card :
      Nat.card (section10OmegaOneCenter p (S : Subgroup G)) = p.val :=
    section10_sylow_omegaOneCenter_card_eq_prime_of_high_rank
      (G := G) (p := p) (A := A) S hpG hA hAleS hSrank
  have hZmemS :
      section10OmegaOneCenter p (S : Subgroup G) ∈ section10PrimeOrderSubgroupsIn p A :=
    section10_omegaOneCenter_mem_primeOrder_of_card
      (G := G) (p := p) (A := A) (P := (S : Subgroup G))
      hA hAleS hZ₁card
  have hAeq : A = B ⊔ section10OmegaOneCenter p (S : Subgroup G) :=
    section10_rankTwo_eq_sup_of_distinct_prime_order
      (G := G) (p := p) (A := A) (X := B)
      (Y := section10OmegaOneCenter p (S : Subgroup G))
      hA hB hZmemS hBneZ
  obtain ⟨hnarrowS, _hnot_le_T, _hZ₁local_card, _hWmem, _hTchar, _hTindex⟩ :
      IsNarrowPGroup p.val S ∧
        ¬ A.subgroupOf (S : Subgroup G) ≤ CΩ₁Z₂ p.val S ∧
        Nat.card (Ω₁Z p.val S) = p.val ∧
        Ω₁Z₂ p.val S ∈ elementaryAbelianSubgroupsOfRank p.val 2 S ∧
        (CΩ₁Z₂ p.val S).Characteristic ∧
        (CΩ₁Z₂ p.val S).index = p.val := by
    have hnarrowS :
        IsNarrowPGroup p.val S :=
      (theorem_5_3 (p := p.val) hpodd (R := S) S.isPGroup' hSrank).mpr
        ⟨A.subgroupOf (S : Subgroup G), hAsubS.1, hAsubS.2⟩
    refine ⟨hnarrowS, ?_, ?_, ?_, ?_, ?_⟩
    · exact theorem_5_3_a
        (p := p.val) hpodd (R := S) hnarrowS hSrank hAsubS.1 hAsubS.2
    · exact (theorem_5_3_b (p := p.val) hpodd (R := S) hnarrowS hSrank).1
    · exact (theorem_5_3_b (p := p.val) hpodd (R := S) hnarrowS hSrank).2
    · exact (theorem_5_3_c (p := p.val) hpodd (R := S) hnarrowS hSrank).1
    · exact (theorem_5_3_c (p := p.val) hpodd (R := S) hnarrowS hSrank).2
  let BS : Subgroup S := B.subgroupOf (S : Subgroup G)
  have hBS_card : Nat.card BS = p.val := by
    simpa [BS] using
      natCard_subgroupOf_eq B (S : Subgroup G) (hB.1.trans hAleS)
        |>.trans hB.2
  have hcentBS_rank_le :
      groupRank (Subgroup.centralizer (BS : Set S)) ≤ 2 := by
    have hAeqS :
        A.subgroupOf (S : Subgroup G) = Ω₁Z p.val S ⊔ BS := by
      have hBleS : B ≤ (S : Subgroup G) := hB.1.trans hAleS
      have hZleS :
          section10OmegaOneCenter p (S : Subgroup G) ≤ (S : Subgroup G) :=
        section10_omegaOneCenter_le (G := G) (p := p) (P := (S : Subgroup G))
      have hZsub :
          (section10OmegaOneCenter p (S : Subgroup G)).subgroupOf (S : Subgroup G) =
            Ω₁Z p.val S := by
        simpa [section10OmegaOneCenter] using
          (subgroupOf_map_subtype_eq (K := (S : Subgroup G)) (Ω₁Z p.val S))
      calc
        A.subgroupOf (S : Subgroup G) =
            (B ⊔ section10OmegaOneCenter p (S : Subgroup G)).subgroupOf
              (S : Subgroup G) := by
          rw [hAeq]
        _ = BS ⊔
            (section10OmegaOneCenter p (S : Subgroup G)).subgroupOf
              (S : Subgroup G) := by
          simpa [BS] using
            Subgroup.subgroupOf_sup
              (A := B) (A' := section10OmegaOneCenter p (S : Subgroup G))
              (B := (S : Subgroup G)) hBleS hZleS
        _ = BS ⊔ Ω₁Z p.val S := by
          rw [hZsub]
        _ = Ω₁Z p.val S ⊔ BS := by
          rw [sup_comm]
    exact
      groupRank_centralizer_le_two_of_rank_two_maximal
        (p := p.val) hpodd (R := S) S.isPGroup'
        hAsubS.1 hAsubS.2 hAeqS
  obtain ⟨hYlocal_cyc, _hB_der_bot, hB_T_bot, hcentB_eq⟩ :=
    theorem_5_3_d (p := p.val) hpodd (R := S) hnarrowS hSrank
      (S := BS) hBS_card hcentBS_rank_le
  let YS : Subgroup S := subgroupCentralizerIn (CΩ₁Z₂ p.val S) BS
  let Y : Subgroup G := YS.map (S : Subgroup G).subtype
  have hYcyc : IsCyclic Y := by
    let eY : YS ≃* Y :=
      Subgroup.equivMapOfInjective (f := (S : Subgroup G).subtype) YS
        (S : Subgroup G).subtype_injective
    exact eY.isCyclic.1 hYlocal_cyc
  have hZ₁leY : section10OmegaOneCenter p (S : Subgroup G) ≤ Y := by
    intro z hz
    change z ∈ (Ω₁Z p.val S).map (S : Subgroup G).subtype at hz
    rcases Subgroup.mem_map.mp hz with ⟨zS, hzΩ, rfl⟩
    refine Subgroup.mem_map_of_mem (S : Subgroup G).subtype ?_
    refine ⟨?_, ?_⟩
    · exact
        ((section10_omega1Z_le_center_pre p.val S).trans
          (Subgroup.center_le_centralizer (Ω₁Z₂ p.val S : Set S))) hzΩ
    · change zS ∈ Subgroup.centralizer (BS : Set S)
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (Subgroup.mem_center_iff.mp
        (section10_omega1Z_le_center_pre p.val S hzΩ)) b
  have hYleC : Y ≤ subgroupCentralizerIn (S : Subgroup G) A := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨yS, hyYS, rfl⟩
    refine ⟨yS.property, ?_⟩
    change ((yS : S) : G) ∈ Subgroup.centralizer (A : Set G)
    rw [hAeq, Subgroup.sup_eq_closure, Subgroup.centralizer_closure,
      Subgroup.mem_centralizer_iff]
    intro x hx
    rcases hx with hxB | hxZ
    · let xS : S := ⟨x, hB.1.trans hAleS hxB⟩
      have hxS_B : xS ∈ BS := by
        change (xS : G) ∈ B
        exact hxB
      have hcommS := (Subgroup.mem_centralizer_iff.mp hyYS.2) xS hxS_B
      exact congrArg (fun t : S => (t : G)) hcommS
    · change x ∈ (Ω₁Z p.val S).map (S : Subgroup G).subtype at hxZ
      rcases Subgroup.mem_map.mp hxZ with ⟨zS, hzΩ, hz_eq⟩
      have hcommS :
          zS * yS = yS * zS := by
        exact (Subgroup.mem_center_iff.mp
          (section10_omega1Z_le_center_pre p.val S hzΩ) yS).symm
      rw [← hz_eq]
      exact congrArg (fun t : S => (t : G)) hcommS
  have hdisj : Disjoint B Y := by
    rw [Subgroup.disjoint_def]
    intro x hxB hxY
    rcases Subgroup.mem_map.mp hxY with ⟨xS, hxYS, rfl⟩
    have hxBS : xS ∈ BS := by
      change ((xS : S) : G) ∈ B
      exact hxB
    have hxinf : xS ∈ BS ⊓ CΩ₁Z₂ p.val S := ⟨hxBS, hxYS.1⟩
    have hxbot : xS ∈ (⊥ : Subgroup S) := by
      simpa [hB_T_bot] using hxinf
    have hxS_one : xS = 1 := Subgroup.mem_bot.mp hxbot
    exact congrArg (fun z : S => (z : G)) hxS_one
  have hCeq : subgroupCentralizerIn (S : Subgroup G) A = B ⊔ Y := by
    apply le_antisymm
    · intro x hx
      let xS : S := ⟨x, hx.1⟩
      have hx_cent_BS : xS ∈ Subgroup.centralizer (BS : Set S) := by
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        let bG : G := b
        have hbB : bG ∈ B := by
          change ((b : S) : G) ∈ B
          change ((b : S) : G) ∈ B at hb
          exact hb
        have hcommG := Subgroup.mem_centralizer_iff.mp hx.2 bG (hB.1 hbB)
        exact Subtype.ext hcommG
      have hxS_sup : xS ∈ BS ⊔ YS := by
        simpa [hcentB_eq] using hx_cent_BS
      have hx_map_sup :
          ((xS : S) : G) ∈ (BS ⊔ YS).map (S : Subgroup G).subtype :=
        Subgroup.mem_map_of_mem (S : Subgroup G).subtype hxS_sup
      rw [Subgroup.map_sup] at hx_map_sup
      change x ∈ BS.map (S : Subgroup G).subtype ⊔ Y at hx_map_sup
      have hBS_map : BS.map (S : Subgroup G).subtype = B := by
        exact Subgroup.map_subgroupOf_eq_of_le (G := G) (H := B)
          (K := (S : Subgroup G)) (hB.1.trans hAleS)
      change x ∈ B ⊔ Y
      simpa [hBS_map] using hx_map_sup
    · apply sup_le
      · intro b hb
        refine ⟨hAleS (hB.1 hb), ?_⟩
        change b ∈ Subgroup.centralizer (A : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        letI : IsElementaryAbelian p.val A := hA.1.2
        exact setLike_mul_comm (s := A)
          ha (hB.1 hb)
      · exact hYleC
  exact ⟨Y, hZ₁leY, hYleC, hYcyc, hdisj, hCeq⟩

private theorem CFSG.section10_lemma_10_13_sylow_structural_package
    {p : Nat.Primes} {A P A₀ : Subgroup G} (S : Sylow p.val G)
    (hpG : p ∈ subgroupPrimeSet (⊤ : Subgroup G))
    (hA : A ∈ section10RankTwoMaximalElementaryAbelianSubgroups p G)
    (hPp : IsPGroup p.val P) (hPnonab : ¬ IsMulCommutative P)
    (hAleP : A ≤ P) (hPleS : P ≤ (S : Subgroup G))
    (hAleS : A ≤ (S : Subgroup G))
    (hA₀ : A₀ ∈ section10PrimeOrderSubgroupsIn p A)
    (hA₀ne : A₀ ≠ section10OmegaOneCenter p P) :
    section10OmegaOneCenter p P = section10OmegaOneCenter p (S : Subgroup G) ∧
      section10OmegaOneCenter p (S : Subgroup G) ∈ section10PrimeOrderSubgroupsIn p A ∧
      ∃ Y : Subgroup G,
        section10OmegaOneCenter p (S : Subgroup G) ≤ Y ∧
          Y ≤ subgroupCentralizerIn (S : Subgroup G) A ∧
          IsCyclic Y ∧
          Disjoint A₀ Y ∧
          subgroupCentralizerIn (S : Subgroup G) A = A₀ ⊔ Y := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  have hp_dvd_G : p.val ∣ Nat.card G := by
    simpa [subgroupPrimeSet] using hpG
  have hpodd : p.val ≠ 2 :=
    Odd.ne_two_of_dvd_nat IsMinCE.odd_order hp_dvd_G
  have hZ₁leZ₀ :
      section10OmegaOneCenter p (S : Subgroup G) ≤ section10OmegaOneCenter p P :=
    section10_omegaOneCenter_le_of_le_rankTwoMaximal
      (G := G) (p := p) (A := A) (P := P) (S := (S : Subgroup G))
      hA hAleP hPleS hAleS
  have hA₀ne_symm : section10OmegaOneCenter p P ≠ A₀ := fun h => hA₀ne h.symm
  have hAsubS :
      A.subgroupOf (S : Subgroup G) ∈ section10RankTwoMaximalElementaryAbelianSubgroups p S :=
    section10_rankTwoMaximal_subgroupOf_of_le_pre
      (G := G) (p := p) (A := A) (S := (S : Subgroup G)) hAleS hA.1 hA.2
  by_cases hSrank : 3 ≤ groupRank (S : Subgroup G)
  · have hZ₁card :
        Nat.card (section10OmegaOneCenter p (S : Subgroup G)) = p.val :=
      section10_sylow_omegaOneCenter_card_eq_prime_of_high_rank
        (G := G) (p := p) (A := A) S hpG hA hAleS hSrank
    have hZ₀card :
        Nat.card (section10OmegaOneCenter p P) = p.val := by
      by_cases hPrank : 3 ≤ groupRank P
      · exact
          section10_omegaOneCenter_card_eq_prime_of_high_rank_pSubgroup
            (G := G) (p := p) (A := A) (P := P)
            hpG hA hPp hAleP hPrank
      · have hZ₀small :=
          section10_omegaOneCenter_card_eq_prime_or_prime_sq_of_le_rankTwoMaximal
            (G := G) (p := p) (A := A) (P := P) hA hPp hAleP
        rcases hZ₀small with hprime | hsquare
        · exact hprime
        · have hZmemS_pre :
              section10OmegaOneCenter p (S : Subgroup G) ∈ section10PrimeOrderSubgroupsIn p A :=
            section10_omegaOneCenter_mem_primeOrder_of_card
              (G := G) (p := p) (A := A) (P := (S : Subgroup G))
              hA hAleS hZ₁card
          obtain ⟨A₁, hA₁, hA₁neZ₁, _hAeqA₁Z₁⟩ :=
            section10_exists_prime_order_complement_to_prime_order_in_rank_two
              (G := G) (p := p) (A := A)
              (Z := section10OmegaOneCenter p (S : Subgroup G))
              hA hZmemS_pre
          obtain ⟨Y₁, _hZ₁leY₁, hY₁leC, hY₁cyc, _hdisj₁, hCeq₁⟩ :=
            section10_high_rank_sylow_centralizer_split_of_prime_order
              (G := G) (p := p) (A := A) (B := A₁) S
              hpG hA hAleS hSrank hA₁ hA₁neZ₁
          exact
            section10_omegaOneCenter_card_eq_prime_of_nonabelian_le_abelian_centralizer
              (G := G) (p := p) (A := A) (P := P) (S := (S : Subgroup G))
              hA hPp hPnonab hAleP hPleS
              (section10_centralizerIn_isMulCommutative_of_eq_prime_cyclic_sup
                (G := G) (p := p) (A := A) (S := (S : Subgroup G))
                (A₀ := A₁) (Y := Y₁) hA hA₁ hY₁leC hY₁cyc hCeq₁)
    have hZeq :
        section10OmegaOneCenter p P = section10OmegaOneCenter p (S : Subgroup G) :=
      section10_omegaOneCenter_eq_of_le_card_prime
        (G := G) (p := p) (P := P) (S := (S : Subgroup G))
        hZ₁leZ₀ hZ₀card hZ₁card
    have hZmemS :
        section10OmegaOneCenter p (S : Subgroup G) ∈ section10PrimeOrderSubgroupsIn p A :=
      section10_omegaOneCenter_mem_primeOrder_of_card
        (G := G) (p := p) (A := A) (P := (S : Subgroup G))
        hA hAleS hZ₁card
    have hAeq : A = A₀ ⊔ section10OmegaOneCenter p (S : Subgroup G) := by
      have hA₀neZ₁ : A₀ ≠ section10OmegaOneCenter p (S : Subgroup G) := by
        intro h
        exact hA₀ne (by simp [hZeq, h])
      exact
        section10_rankTwo_eq_sup_of_distinct_prime_order
          (G := G) (p := p) (A := A) (X := A₀)
          (Y := section10OmegaOneCenter p (S : Subgroup G))
          hA hA₀ hZmemS hA₀neZ₁
    obtain ⟨hnarrowS, hnot_le_T, hZ₁local_card, hWmem, hTchar, hTindex⟩ :
        IsNarrowPGroup p.val S ∧
          ¬ A.subgroupOf (S : Subgroup G) ≤ CΩ₁Z₂ p.val S ∧
          Nat.card (Ω₁Z p.val S) = p.val ∧
          Ω₁Z₂ p.val S ∈ elementaryAbelianSubgroupsOfRank p.val 2 S ∧
          (CΩ₁Z₂ p.val S).Characteristic ∧
          (CΩ₁Z₂ p.val S).index = p.val := by
      have hnarrowS :
          IsNarrowPGroup p.val S :=
        (theorem_5_3 (p := p.val) hpodd (R := S) S.isPGroup' hSrank).mpr
          ⟨A.subgroupOf (S : Subgroup G), hAsubS.1, hAsubS.2⟩
      refine ⟨hnarrowS, ?_, ?_, ?_, ?_, ?_⟩
      · exact theorem_5_3_a
          (p := p.val) hpodd (R := S) hnarrowS hSrank hAsubS.1 hAsubS.2
      · exact (theorem_5_3_b (p := p.val) hpodd (R := S) hnarrowS hSrank).1
      · exact (theorem_5_3_b (p := p.val) hpodd (R := S) hnarrowS hSrank).2
      · exact (theorem_5_3_c (p := p.val) hpodd (R := S) hnarrowS hSrank).1
      · exact (theorem_5_3_c (p := p.val) hpodd (R := S) hnarrowS hSrank).2
    let A₀S : Subgroup S := A₀.subgroupOf (S : Subgroup G)
    have hA₀S_card : Nat.card A₀S = p.val := by
      simpa [A₀S] using
        natCard_subgroupOf_eq A₀ (S : Subgroup G) (hA₀.1.trans hAleS)
          |>.trans hA₀.2
    have hcentA₀S_rank_le :
        groupRank (Subgroup.centralizer (A₀S : Set S)) ≤ 2 := by
      have hAeqS :
          A.subgroupOf (S : Subgroup G) = Ω₁Z p.val S ⊔ A₀S := by
        have hA₀leS : A₀ ≤ (S : Subgroup G) := hA₀.1.trans hAleS
        have hZleS :
            section10OmegaOneCenter p (S : Subgroup G) ≤ (S : Subgroup G) :=
          section10_omegaOneCenter_le (G := G) (p := p) (P := (S : Subgroup G))
        have hZsub :
            (section10OmegaOneCenter p (S : Subgroup G)).subgroupOf (S : Subgroup G) =
              Ω₁Z p.val S := by
          simpa [section10OmegaOneCenter] using
            (subgroupOf_map_subtype_eq (K := (S : Subgroup G)) (Ω₁Z p.val S))
        calc
          A.subgroupOf (S : Subgroup G) =
              (A₀ ⊔ section10OmegaOneCenter p (S : Subgroup G)).subgroupOf
                (S : Subgroup G) := by
            rw [hAeq]
          _ = A₀S ⊔
              (section10OmegaOneCenter p (S : Subgroup G)).subgroupOf
                (S : Subgroup G) := by
            simpa [A₀S] using
              Subgroup.subgroupOf_sup
                (A := A₀) (A' := section10OmegaOneCenter p (S : Subgroup G))
                (B := (S : Subgroup G)) hA₀leS hZleS
          _ = A₀S ⊔ Ω₁Z p.val S := by
            rw [hZsub]
          _ = Ω₁Z p.val S ⊔ A₀S := by
            rw [sup_comm]
      exact
        groupRank_centralizer_le_two_of_rank_two_maximal
          (p := p.val) hpodd (R := S) S.isPGroup'
          hAsubS.1 hAsubS.2 hAeqS
    obtain ⟨hYlocal_cyc, _hA₀_der_bot, hA₀_T_bot, hcentA₀_eq⟩ :=
      theorem_5_3_d (p := p.val) hpodd (R := S) hnarrowS hSrank
        (S := A₀S) hA₀S_card hcentA₀S_rank_le
    let YS : Subgroup S := subgroupCentralizerIn (CΩ₁Z₂ p.val S) A₀S
    let Y : Subgroup G := YS.map (S : Subgroup G).subtype
    have hYcyc : IsCyclic Y := by
      let eY : YS ≃* Y :=
        Subgroup.equivMapOfInjective (f := (S : Subgroup G).subtype) YS
          (S : Subgroup G).subtype_injective
      exact eY.isCyclic.1 hYlocal_cyc
    have hZ₁leY : section10OmegaOneCenter p (S : Subgroup G) ≤ Y := by
      intro z hz
      change z ∈ (Ω₁Z p.val S).map (S : Subgroup G).subtype at hz
      rcases Subgroup.mem_map.mp hz with ⟨zS, hzΩ, rfl⟩
      refine Subgroup.mem_map_of_mem (S : Subgroup G).subtype ?_
      refine ⟨?_, ?_⟩
      · exact
          ((section10_omega1Z_le_center_pre p.val S).trans
            (Subgroup.center_le_centralizer (Ω₁Z₂ p.val S : Set S))) hzΩ
      · change zS ∈ Subgroup.centralizer (A₀S : Set S)
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        exact (Subgroup.mem_center_iff.mp
          (section10_omega1Z_le_center_pre p.val S hzΩ)) a
    have hYleC : Y ≤ subgroupCentralizerIn (S : Subgroup G) A := by
      intro y hy
      rcases Subgroup.mem_map.mp hy with ⟨yS, hyYS, rfl⟩
      refine ⟨yS.property, ?_⟩
      change ((yS : S) : G) ∈ Subgroup.centralizer (A : Set G)
      rw [hAeq, Subgroup.sup_eq_closure, Subgroup.centralizer_closure,
        Subgroup.mem_centralizer_iff]
      intro x hx
      rcases hx with hxA₀ | hxZ
      · let xS : S := ⟨x, hA₀.1.trans hAleS hxA₀⟩
        have hxS_A₀ : xS ∈ A₀S := by
          change (xS : G) ∈ A₀
          exact hxA₀
        have hcommS := (Subgroup.mem_centralizer_iff.mp hyYS.2) xS hxS_A₀
        exact congrArg (fun t : S => (t : G)) hcommS
      · change x ∈ (Ω₁Z p.val S).map (S : Subgroup G).subtype at hxZ
        rcases Subgroup.mem_map.mp hxZ with ⟨zS, hzΩ, hz_eq⟩
        have hcommS :
            zS * yS = yS * zS := by
          exact (Subgroup.mem_center_iff.mp
            (section10_omega1Z_le_center_pre p.val S hzΩ) yS).symm
        rw [← hz_eq]
        exact congrArg (fun t : S => (t : G)) hcommS
    have hdisj : Disjoint A₀ Y := by
      rw [Subgroup.disjoint_def]
      intro x hxA₀ hxY
      rcases Subgroup.mem_map.mp hxY with ⟨xS, hxYS, rfl⟩
      have hxA₀S : xS ∈ A₀S := by
        change ((xS : S) : G) ∈ A₀
        exact hxA₀
      have hxinf : xS ∈ A₀S ⊓ CΩ₁Z₂ p.val S := ⟨hxA₀S, hxYS.1⟩
      have hxbot : xS ∈ (⊥ : Subgroup S) := by
        simpa [hA₀_T_bot] using hxinf
      have hxS_one : xS = 1 := Subgroup.mem_bot.mp hxbot
      exact congrArg (fun z : S => (z : G)) hxS_one
    have hCeq : subgroupCentralizerIn (S : Subgroup G) A = A₀ ⊔ Y := by
      apply le_antisymm
      · intro x hx
        let xS : S := ⟨x, hx.1⟩
        have hx_cent_A₀S : xS ∈ Subgroup.centralizer (A₀S : Set S) := by
          rw [Subgroup.mem_centralizer_iff]
          intro a ha
          let aG : G := a
          have haA₀ : aG ∈ A₀ := by
            change ((a : S) : G) ∈ A₀
            change ((a : S) : G) ∈ A₀ at ha
            exact ha
          have hcommG := Subgroup.mem_centralizer_iff.mp hx.2 aG (hA₀.1 haA₀)
          exact Subtype.ext hcommG
        have hxS_sup : xS ∈ A₀S ⊔ YS := by
          simpa [hcentA₀_eq] using hx_cent_A₀S
        have hx_map_sup :
            ((xS : S) : G) ∈ (A₀S ⊔ YS).map (S : Subgroup G).subtype :=
          Subgroup.mem_map_of_mem (S : Subgroup G).subtype hxS_sup
        rw [Subgroup.map_sup] at hx_map_sup
        change x ∈ A₀S.map (S : Subgroup G).subtype ⊔ Y at hx_map_sup
        have hA₀S_map : A₀S.map (S : Subgroup G).subtype = A₀ := by
          exact Subgroup.map_subgroupOf_eq_of_le (G := G) (H := A₀)
            (K := (S : Subgroup G)) (hA₀.1.trans hAleS)
        change x ∈ A₀ ⊔ Y
        simpa [hA₀S_map] using hx_map_sup
      · apply sup_le
        · intro a ha
          refine ⟨hAleS (hA₀.1 ha), ?_⟩
          change a ∈ Subgroup.centralizer (A : Set G)
          rw [Subgroup.mem_centralizer_iff]
          intro b hb
          letI : IsElementaryAbelian p.val A := hA.1.2
          exact setLike_mul_comm (s := A)
            hb (hA₀.1 ha)
        · exact hYleC
    exact ⟨hZeq, hZmemS, Y, hZ₁leY, hYleC, hYcyc, hdisj, hCeq⟩
  · have hSrank_le : groupRank (S : Subgroup G) ≤ 2 := by omega
    rcases corollary_10_7_b (G := G) S hSrank_le with hScomm | hshape
    · have hPcomm : IsMulCommutative P := by
        letI : IsMulCommutative (S : Subgroup G) := hScomm
        letI : CommGroup (S : Subgroup G) := IsMulCommutative.instCommGroup
        refine ⟨⟨fun x y => ?_⟩⟩
        have hxy : (⟨(x : G), hPleS x.property⟩ : S) *
            (⟨(y : G), hPleS y.property⟩ : S) =
            (⟨(y : G), hPleS y.property⟩ : S) *
            (⟨(x : G), hPleS x.property⟩ : S) :=
          mul_comm _ _
        exact Subtype.ext (congrArg (fun z : S => (z : G)) hxy)
      exact False.elim (hPnonab hPcomm)
    · -- Low-rank Sylow branch: Corollary 10.7(b) gives
      -- `S = S₁ Z(S)` with `Z(S)` cyclic and
      -- `Z(S₁) = Ω₁(Z(S))`; the book then proves `C_S(A) = A Z(S)`.
      -- The remaining code transports that central-product split to the
      -- ambient subgroup statement.
      rcases hshape with ⟨S₁, S₂, hS₁card, hS₁noncomm, hS₁exp, hS₂cyc,
        hcentral, hΩeq⟩
      have hS₁p : IsPGroup p.val S₁ := S.isPGroup'.to_subgroup S₁
      letI : Fact (IsPGroup p.val S₁) := ⟨hS₁p⟩
      have hS₁extra : IsExtraspecial p.val S₁ :=
        section10_isExtraspecial_of_noncommutative_card_p3_exponent_p
          (K := S₁) (p := p.val) hS₁card hS₁exp hS₁noncomm
      letI : IsExtraspecial p.val S₁ := hS₁extra
      have hder_center :
          (derivedSubgroup S₁).map S₁.subtype =
            (Subgroup.center S₁).map S₁.subtype :=
        section10_derivedSubgroup_map_subtype_eq_center_map_subtype_of_isExtraspecial
          (R := S) (p := p.val) S₁
      have hΩder :
          (omega₁ (G := S₂) (p := p.val)).map S₂.subtype =
            (derivedSubgroup S₁).map S₁.subtype := by
        letI : IsCyclic S₂ := hS₂cyc
        calc
          (omega₁ (G := S₂) (p := p.val)).map S₂.subtype =
              (Ω₁Z p.val S₂).map S₂.subtype := by
            rw [section10_omega1Z_eq_omega1_of_isCyclic (R := S₂) (p := p.val)]
          _ = (Subgroup.center S₁).map S₁.subtype := hΩeq
          _ = (derivedSubgroup S₁).map S₁.subtype := hder_center.symm
      have homegaS : omega₁ (G := S) (p := p.val) = S₁ :=
        section10_omega1_eq_centralProduct_left_of_exponent
          (p := p.val) (R := S) (R₁ := S₁) (R₂ := S₂)
          hcentral hS₁exp hΩder
      have hAleS₁ : A.subgroupOf (S : Subgroup G) ≤ S₁ := by
        intro a ha
        have haA : (a : G) ∈ A := by
          simpa [Subgroup.mem_subgroupOf] using ha
        let aA : A := ⟨(a : G), haA⟩
        have ha_pow_A : aA ^ p.val = 1 := by
          letI : IsElementaryAbelian p.val A := hA.1.2
          exact
            Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
              (IsElementaryAbelian.exponent_dvd_p p.val A) aA
        have ha_pow_S : a ^ p.val = 1 := by
          apply Subtype.ext
          simpa [aA] using congrArg Subtype.val ha_pow_A
        have haOmega : a ∈ omega₁ (G := S) (p := p.val) := by
          change a ∈ Subgroup.closure {x : S | x ^ (p.val ^ 1) = 1}
          exact Subgroup.subset_closure (by simpa [pow_one] using ha_pow_S)
        simpa [homegaS] using haOmega
      have hZ₁card :
          Nat.card (section10OmegaOneCenter p (S : Subgroup G)) = p.val := by
        let Z₁G : Subgroup G := section10OmegaOneCenter p (S : Subgroup G)
        let ZS₁S : Subgroup S := (Subgroup.center S₁).map S₁.subtype
        let ZS₁G : Subgroup G := ZS₁S.map (S : Subgroup G).subtype
        have hZ₁leZS₁G : Z₁G ≤ ZS₁G := by
          intro z hz
          change z ∈ (Ω₁Z p.val S).map (S : Subgroup G).subtype at hz
          rcases Subgroup.mem_map.mp hz with ⟨zS, hzΩ, rfl⟩
          have hzS₁ : zS ∈ S₁ := by
            have hzω : zS ∈ omega₁ (G := S) (p := p.val) := by
              exact
                section10_omega1_map_subtype_le
                  (R := S) (p := p.val) (Subgroup.center S) hzΩ
            simpa [homegaS] using hzω
          have hzcenterS₁ : (⟨zS, hzS₁⟩ : S₁) ∈ Subgroup.center S₁ := by
            rw [Subgroup.mem_center_iff]
            intro y
            apply Subtype.ext
            have hzcenterS : zS ∈ Subgroup.center S :=
              section10_omega1Z_le_center_pre p.val S hzΩ
            exact Subgroup.mem_center_iff.mp hzcenterS y
          exact Subgroup.mem_map_of_mem (S : Subgroup G).subtype
            (Subgroup.mem_map_of_mem S₁.subtype hzcenterS₁)
        have hZS₁G_card : Nat.card ZS₁G = p.val := by
          have hZS₁S_card : Nat.card ZS₁S = Nat.card (Subgroup.center S₁) := by
            simpa [ZS₁S] using
              (Subgroup.card_map_of_injective
                (K := Subgroup.center S₁) (f := S₁.subtype) S₁.subtype_injective)
          calc
            Nat.card ZS₁G = Nat.card ZS₁S := by
              simpa [ZS₁G] using
                (Subgroup.card_map_of_injective
                  (K := ZS₁S) (f := (S : Subgroup G).subtype)
                  (S : Subgroup G).subtype_injective)
            _ = Nat.card (Subgroup.center S₁) := hZS₁S_card
            _ = p.val := IsExtraspecial.center_order_p p.val S₁
        have hZ₁_card_le : Nat.card Z₁G ≤ p.val := by
          simpa [hZS₁G_card] using Subgroup.card_le_of_le hZ₁leZS₁G
        haveI : Nontrivial (S : Subgroup G) :=
          section10_nontrivial_of_rankTwoMaximal_le (G := G) (p := p) hA hAleS
        have hZ₁ne : Z₁G ≠ ⊥ :=
          section10_omegaOneCenter_ne_bot_of_nontrivial_pSubgroup
            (G := G) (p := p) (P := (S : Subgroup G)) S.isPGroup'
        have hZ₁elem : IsElementaryAbelian p.val Z₁G := by
          have hΩelem : IsElementaryAbelian p.val (Ω₁Z p.val S) :=
            section10_omega1Z_isElementaryAbelian_pre (p := p.val) S
          letI : IsElementaryAbelian p.val (Ω₁Z p.val S) := hΩelem
          change IsElementaryAbelian p.val
            ((Ω₁Z p.val S).map (S : Subgroup G).subtype)
          exact section10_isElementaryAbelian_map_pre
            (G := S) (p := p.val) (A := Ω₁Z p.val S)
            (G' := G) (S : Subgroup G).subtype
        have hZ₁p : IsPGroup p.val Z₁G := by
          letI : IsElementaryAbelian p.val Z₁G := hZ₁elem
          exact IsElementaryAbelian.isPGroup p.val Z₁G
        rcases hZ₁p.exists_card_eq with ⟨n, hn⟩
        have hn_pos : 0 < n := by
          by_contra hn_not
          have hn0 : n = 0 := by omega
          have hcard_one : Nat.card Z₁G = 1 := by simpa [hn0] using hn
          exact hZ₁ne ((Subgroup.card_eq_one (H := Z₁G)).1 hcard_one)
        have hn_le_one : n ≤ 1 := by
          have hpow_le : p.val ^ n ≤ p.val := by
            simpa [hn] using hZ₁_card_le
          have hpow_le' : p.val ^ n ≤ p.val ^ 1 := by
            simpa [pow_one] using hpow_le
          simpa [pow_one] using
            (Nat.pow_le_pow_iff_right p.property.one_lt).1 hpow_le'
        have hn_eq_one : n = 1 := by omega
        simpa [Z₁G, hn_eq_one] using hn
      let Y : Subgroup G := S₂.map (S : Subgroup G).subtype
      have hZ₁leY : section10OmegaOneCenter p (S : Subgroup G) ≤ Y := by
        intro z hz
        change z ∈ (Ω₁Z p.val S).map (S : Subgroup G).subtype at hz
        rcases Subgroup.mem_map.mp hz with ⟨zS, hzΩ, rfl⟩
        have hzS₁ : zS ∈ S₁ := by
          have hzω : zS ∈ omega₁ (G := S) (p := p.val) :=
            section10_omega1_map_subtype_le
              (R := S) (p := p.val) (Subgroup.center S) hzΩ
          simpa [homegaS] using hzω
        have hzcenterS₁ :
            (⟨zS, hzS₁⟩ : S₁) ∈ Subgroup.center S₁ := by
          rw [Subgroup.mem_center_iff]
          intro y
          apply Subtype.ext
          have hzcenterS : zS ∈ Subgroup.center S :=
            section10_omega1Z_le_center_pre p.val S hzΩ
          exact Subgroup.mem_center_iff.mp hzcenterS y
        have hzS_center_map :
            zS ∈ (Subgroup.center S₁).map S₁.subtype :=
          Subgroup.mem_map_of_mem S₁.subtype hzcenterS₁
        have hzS_omegaS₂ :
            zS ∈ (Ω₁Z p.val S₂).map S₂.subtype := by
          simpa [hΩeq] using hzS_center_map
        rcases Subgroup.mem_map.mp hzS_omegaS₂ with ⟨zS₂, hzS₂, hzS_eq⟩
        refine Subgroup.mem_map.mpr ⟨zS₂, zS₂.property, ?_⟩
        exact congrArg (fun x : S => (x : G)) hzS_eq
      have hYleC : Y ≤ subgroupCentralizerIn (S : Subgroup G) A := by
        rcases hcentral with ⟨_hS₁norm, _hS₂norm, hcomm12, _hsup12⟩
        have hS₂leCentS₁ : S₂ ≤ Subgroup.centralizer (S₁ : Set S) := by
          exact
            (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := S₂) (H₂ := S₁)).1
              (by simpa [Subgroup.commutator_comm] using hcomm12)
        intro y hy
        rcases Subgroup.mem_map.mp hy with ⟨yS₂, hyS₂, rfl⟩
        refine ⟨yS₂.property, ?_⟩
        change ((yS₂ : S) : G) ∈ Subgroup.centralizer (A : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        have haS : (⟨a, hAleS ha⟩ : S) ∈ A.subgroupOf (S : Subgroup G) := by
          change a ∈ A
          exact ha
        have haS₁ : (⟨a, hAleS ha⟩ : S) ∈ S₁ := hAleS₁ haS
        have hcommS :
            (⟨a, hAleS ha⟩ : S) * yS₂ =
              yS₂ * (⟨a, hAleS ha⟩ : S) := by
          exact Subgroup.mem_centralizer_iff.mp (hS₂leCentS₁ hyS₂) _ haS₁
        exact congrArg (fun x : S => (x : G)) hcommS
      have hYcyc : IsCyclic Y := by
        let eY : S₂ ≃* Y :=
          Subgroup.equivMapOfInjective (f := (S : Subgroup G).subtype) S₂
            (S : Subgroup G).subtype_injective
        exact eY.isCyclic.1 hS₂cyc
      have hYleCentA_pre : Y ≤ Subgroup.centralizer (A : Set G) := by
        intro y hy
        exact (hYleC hy).2
      have hCSAeq : subgroupCentralizerIn (S : Subgroup G) A = A ⊔ Y := by
        rcases hcentral with ⟨hS₁norm, _hS₂norm, hcomm12, hsup12⟩
        apply le_antisymm
        · intro x hx
          let xS : S := ⟨x, hx.1⟩
          have hx_sup : xS ∈ S₁ ⊔ S₂ := by
            rw [hsup12]
            exact Subgroup.mem_top _
          rcases (Subgroup.mem_sup_of_normal_left (x := xS) (s := S₁) (t := S₂)).1 hx_sup with
            ⟨s₁, hs₁, s₂, hs₂, hs₁s₂⟩
          let s₁G : G := s₁
          let s₂G : G := s₂
          have hs₁s₂G : s₁G * s₂G = x := by
            have hval := congrArg (fun z : S => (z : G)) hs₁s₂
            simpa [xS, s₁G, s₂G] using hval
          have hs₂Y : s₂G ∈ Y := by
            exact Subgroup.mem_map_of_mem (S : Subgroup G).subtype hs₂
          have hs₂_centA : s₂G ∈ Subgroup.centralizer (A : Set G) := (hYleC hs₂Y).2
          have hs₁_centA : s₁G ∈ Subgroup.centralizer (A : Set G) := by
            rw [Subgroup.mem_centralizer_iff]
            intro a ha
            have hxcomm : x * a = a * x :=
              (Subgroup.mem_centralizer_iff.mp hx.2 a ha).symm
            have hs₂comm : s₂G * a = a * s₂G :=
              (Subgroup.mem_centralizer_iff.mp hs₂_centA a ha).symm
            have hcancel : (a * s₁G) * s₂G = (s₁G * a) * s₂G := by
              symm
              calc
                (s₁G * a) * s₂G = s₁G * (a * s₂G) := by simp [mul_assoc]
                _ = s₁G * (s₂G * a) := by rw [← hs₂comm]
                _ = (s₁G * s₂G) * a := by simp [mul_assoc]
                _ = x * a := by rw [hs₁s₂G]
                _ = a * x := hxcomm
                _ = a * (s₁G * s₂G) := by rw [hs₁s₂G]
                _ = (a * s₁G) * s₂G := by simp [mul_assoc]
            exact mul_right_cancel (b := s₂G) hcancel
          have hs₁_pow : s₁G ^ p.val = 1 := by
            have hs₁_sub_pow : (⟨s₁, hs₁⟩ : S₁) ^ p.val = 1 := by
              exact
                Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
                  (show Monoid.exponent S₁ ∣ p.val by rw [hS₁exp]) ⟨s₁, hs₁⟩
            simpa [s₁G] using congrArg (fun z : S₁ => ((z : S) : G)) hs₁_sub_pow
          let C : Subgroup G := Subgroup.zpowers s₁G
          have hCelem : IsElementaryAbelian p.val C :=
            section10_isElementaryAbelian_zpowers_of_pow_eq_one
              (G := G) (p := p.val) hs₁_pow
          have hCcentA : C ≤ Subgroup.centralizer (A : Set G) := by
            intro z hz
            rw [Subgroup.mem_centralizer_iff]
            intro a ha
            rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, rfl⟩
            have hcomm : Commute a s₁G :=
              Subgroup.mem_centralizer_iff.mp hs₁_centA a ha
            exact (hcomm.zpow_right n).eq
          have hsupElem : IsElementaryAbelian p.val (A ⊔ C : Subgroup G) := by
            letI : IsElementaryAbelian p.val A := hA.1.2
            letI : IsElementaryAbelian p.val C := hCelem
            exact section10_isElementaryAbelian_sup_of_le_centralizer
              (G := G) (p := p.val) (E := A) (D := C) hCcentA
          have hAeqSup : A = A ⊔ C := hA.2.2 (A ⊔ C) le_sup_left hsupElem
          have hs₁A : s₁G ∈ A := by
            rw [hAeqSup]
            exact Subgroup.mem_sup_right (Subgroup.mem_zpowers s₁G)
          have hs₁AY : s₁G ∈ A ⊔ Y := Subgroup.mem_sup_left hs₁A
          have hs₂AY : s₂G ∈ A ⊔ Y := Subgroup.mem_sup_right hs₂Y
          have hmul : s₁G * s₂G ∈ A ⊔ Y :=
            (A ⊔ Y).mul_mem hs₁AY hs₂AY
          simpa [hs₁s₂G] using hmul
        · apply sup_le
          · intro a ha
            refine ⟨hAleS ha, ?_⟩
            change a ∈ Subgroup.centralizer (A : Set G)
            rw [Subgroup.mem_centralizer_iff]
            intro b hb
            letI : IsElementaryAbelian p.val A := hA.1.2
            exact setLike_mul_comm (s := A) hb ha
          · exact hYleC
      have hCScomm : IsMulCommutative (subgroupCentralizerIn (S : Subgroup G) A) := by
        have hAcomm : IsMulCommutative A := by
          letI : IsElementaryAbelian p.val A := hA.1.2
          infer_instance
        have hYcomm : IsMulCommutative Y := by
          letI : CommGroup Y := IsCyclic.commGroup
          infer_instance
        have hSupComm : IsMulCommutative (A ⊔ Y : Subgroup G) :=
          section10_isMulCommutative_sup_of_le_centralizer
            (G := G) hAcomm hYcomm hYleCentA_pre
        rw [hCSAeq]
        exact hSupComm
      have hZ₀card :
          Nat.card (section10OmegaOneCenter p P) = p.val :=
        section10_omegaOneCenter_card_eq_prime_of_nonabelian_le_abelian_centralizer
          (G := G) (p := p) (A := A) (P := P) (S := (S : Subgroup G))
          hA hPp hPnonab hAleP hPleS hCScomm
      have hZeq :
          section10OmegaOneCenter p P = section10OmegaOneCenter p (S : Subgroup G) :=
        section10_omegaOneCenter_eq_of_le_card_prime
          (G := G) (p := p) (P := P) (S := (S : Subgroup G))
          hZ₁leZ₀ hZ₀card hZ₁card
      have hZmemS :
          section10OmegaOneCenter p (S : Subgroup G) ∈ section10PrimeOrderSubgroupsIn p A :=
        section10_omegaOneCenter_mem_primeOrder_of_card
          (G := G) (p := p) (A := A) (P := (S : Subgroup G))
          hA hAleS hZ₁card
      have hAeq : A = A₀ ⊔ section10OmegaOneCenter p (S : Subgroup G) := by
        have hA₀neZ₁ : A₀ ≠ section10OmegaOneCenter p (S : Subgroup G) := by
          intro h
          exact hA₀ne (by simp [hZeq, h])
        exact
          section10_rankTwo_eq_sup_of_distinct_prime_order
            (G := G) (p := p) (A := A) (X := A₀)
            (Y := section10OmegaOneCenter p (S : Subgroup G))
            hA hA₀ hZmemS hA₀neZ₁
      have hYleCentA : Y ≤ Subgroup.centralizer (A : Set G) := by
        intro y hy
        exact (hYleC hy).2
      have hA₀_le_centY : A₀ ≤ Subgroup.centralizer (Y : Set G) := by
        intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact (Subgroup.mem_centralizer_iff.mp (hYleCentA hy) a (hA₀.1 ha)).symm
      have hdisj : Disjoint A₀ Y := by
        rw [Subgroup.disjoint_def]
        intro x hxA₀ hxY
        by_contra hxne
        have hxA : x ∈ A := hA₀.1 hxA₀
        let xA : A := ⟨x, hxA⟩
        have hxpowA : xA ^ p.val = 1 := by
          letI : IsElementaryAbelian p.val A := hA.1.2
          exact
            Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
              (IsElementaryAbelian.exponent_dvd_p p.val A) xA
        have hxOmegaY :
            x ∈ ((omega₁ (G := S₂) (p := p.val)).map S₂.subtype).map
              (S : Subgroup G).subtype := by
          have hxS₂ : ∃ xS₂ : S₂, (((xS₂ : S₂) : S) : G) = x := by
            rcases Subgroup.mem_map.mp hxY with ⟨xS₂, hxS₂, hx_eq⟩
            exact ⟨⟨xS₂, hxS₂⟩, hx_eq⟩
          rcases hxS₂ with ⟨xS₂, hxS₂_eq⟩
          have hxS₂pow : xS₂ ^ p.val = 1 := by
            have hxpowG : x ^ p.val = 1 := by
              simpa [xA] using congrArg Subtype.val hxpowA
            apply S₂.subtype_injective
            apply (S : Subgroup G).subtype_injective
            simpa [← hxS₂_eq] using hxpowG
          have hxS₂omega : xS₂ ∈ omega₁ (G := S₂) (p := p.val) := by
            change xS₂ ∈ Subgroup.closure {u : S₂ | u ^ (p.val ^ 1) = 1}
            exact Subgroup.subset_closure (by simpa [pow_one] using hxS₂pow)
          simpa [hxS₂_eq] using
            Subgroup.mem_map_of_mem (S : Subgroup G).subtype
              (Subgroup.mem_map_of_mem S₂.subtype hxS₂omega)
        have hxZ₁ : x ∈ section10OmegaOneCenter p (S : Subgroup G) := by
          change x ∈ (Ω₁Z p.val S).map (S : Subgroup G).subtype
          rcases Subgroup.mem_map.mp hxOmegaY with ⟨xS, hxS, hx_eq⟩
          change xS ∈ (omega₁ (G := S₂) (p := p.val)).map S₂.subtype at hxS
          letI : IsCyclic S₂ := hS₂cyc
          have hxOmegaS₂ : xS ∈ (Ω₁Z p.val S₂).map S₂.subtype := by
            simpa [section10_omega1Z_eq_omega1_of_isCyclic (R := S₂) (p := p.val)] using hxS
          have hxS_center : xS ∈ Subgroup.center S := by
            rw [Subgroup.mem_center_iff]
            intro s
            rcases hcentral with ⟨_hS₁norm, _hS₂norm, hcomm12, hsup12⟩
            rcases Subgroup.mem_map.mp hxOmegaS₂ with ⟨xS₂, hxΩS₂, hxS₂_eq⟩
            have hs_sup : (s : S) ∈ S₁ ⊔ S₂ := by
              rw [hsup12]
              exact Subgroup.mem_top _
            rcases (Subgroup.mem_sup_of_normal_left (x := (s : S)) (s := S₁) (t := S₂)).1 hs_sup with
              ⟨s₁, hs₁, s₂, hs₂, hs_eq⟩
            have hx_s₁ : xS * s₁ = s₁ * xS := by
              rw [← hxS₂_eq]
              exact
                (Subgroup.mem_centralizer_iff.mp
                  ((Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := S₂) (H₂ := S₁)).1
                    (by simpa [Subgroup.commutator_comm] using hcomm12) xS₂.property) s₁ hs₁).symm
            have hx_s₂ : xS * s₂ = s₂ * xS := by
              rw [← hxS₂_eq]
              exact (congrArg (fun z : S₂ => (z : S))
                ((Subgroup.mem_center_iff.mp
                  (section10_omega1Z_le_center_pre p.val S₂ hxΩS₂)) ⟨s₂, hs₂⟩)).symm
            rw [← hs_eq]
            symm
            calc
              xS * (s₁ * s₂) = (xS * s₁) * s₂ := by simp [mul_assoc]
              _ = (s₁ * xS) * s₂ := by rw [hx_s₁]
              _ = s₁ * (xS * s₂) := by simp [mul_assoc]
              _ = s₁ * (s₂ * xS) := by rw [hx_s₂]
              _ = (s₁ * s₂) * xS := by simp [mul_assoc]
          have hxS_pow : xS ^ p.val = 1 := by
            apply Subtype.ext
            have hxpowG : x ^ p.val = 1 := by
              simpa [xA] using congrArg Subtype.val hxpowA
            simpa [← hx_eq] using hxpowG
          have hxΩ : xS ∈ Ω₁Z p.val S := by
            change xS ∈ (omega₁ (G := Subgroup.center S) (p := p.val)).map (Subgroup.center S).subtype
            let xC : Subgroup.center S := ⟨xS, hxS_center⟩
            have hxCω : xC ∈ omega₁ (G := Subgroup.center S) (p := p.val) := by
              change xC ∈ Subgroup.closure {u : Subgroup.center S | u ^ (p.val ^ 1) = 1}
              refine Subgroup.subset_closure ?_
              apply Subtype.ext
              simpa [pow_one, xC] using hxS_pow
            exact Subgroup.mem_map_of_mem (Subgroup.center S).subtype hxCω
          exact Subgroup.mem_map.mpr ⟨xS, hxΩ, hx_eq⟩
        have hxA₀Z : x ∈ A₀ ⊓ section10OmegaOneCenter p (S : Subgroup G) := ⟨hxA₀, hxZ₁⟩
        have hA₀disjZ₁ : Disjoint A₀ (section10OmegaOneCenter p (S : Subgroup G)) := by
          have hA₀neZ₁ : A₀ ≠ section10OmegaOneCenter p (S : Subgroup G) := by
            intro h
            exact hA₀ne (by simp [hZeq, h])
          exact section10_prime_order_subgroups_disjoint_of_ne
            (G := G) (p := p) (A := A) (X := A₀)
            (Y := section10OmegaOneCenter p (S : Subgroup G))
            hA hA₀ hZmemS hA₀neZ₁
        exact hxne (Subgroup.disjoint_def.mp hA₀disjZ₁ hxA₀ hxZ₁)
      have hCeq : subgroupCentralizerIn (S : Subgroup G) A = A₀ ⊔ Y := by
        rcases hcentral with ⟨hS₁norm, _hS₂norm, hcomm12, hsup12⟩
        apply le_antisymm
        · intro x hx
          let xS : S := ⟨x, hx.1⟩
          have hx_sup : xS ∈ S₁ ⊔ S₂ := by
            rw [hsup12]
            exact Subgroup.mem_top _
          rcases (Subgroup.mem_sup_of_normal_left (x := xS) (s := S₁) (t := S₂)).1 hx_sup with
            ⟨s₁, hs₁, s₂, hs₂, hs₁s₂⟩
          let s₁G : G := s₁
          let s₂G : G := s₂
          have hs₁s₂G : s₁G * s₂G = x := by
            have hval := congrArg (fun z : S => (z : G)) hs₁s₂
            simpa [xS, s₁G, s₂G] using hval
          have hs₂Y : s₂G ∈ Y := by
            exact Subgroup.mem_map_of_mem (S : Subgroup G).subtype hs₂
          have hs₂_centA : s₂G ∈ Subgroup.centralizer (A : Set G) := (hYleC hs₂Y).2
          have hs₁_centA : s₁G ∈ Subgroup.centralizer (A : Set G) := by
            rw [Subgroup.mem_centralizer_iff]
            intro a ha
            have hxcomm : x * a = a * x :=
              (Subgroup.mem_centralizer_iff.mp hx.2 a ha).symm
            have hs₂comm : s₂G * a = a * s₂G :=
              (Subgroup.mem_centralizer_iff.mp hs₂_centA a ha).symm
            have hcancel : (a * s₁G) * s₂G = (s₁G * a) * s₂G := by
              symm
              calc
                (s₁G * a) * s₂G = s₁G * (a * s₂G) := by simp [mul_assoc]
                _ = s₁G * (s₂G * a) := by rw [← hs₂comm]
                _ = (s₁G * s₂G) * a := by simp [mul_assoc]
                _ = x * a := by rw [hs₁s₂G]
                _ = a * x := hxcomm
                _ = a * (s₁G * s₂G) := by rw [hs₁s₂G]
                _ = (a * s₁G) * s₂G := by simp [mul_assoc]
            exact mul_right_cancel (b := s₂G) hcancel
          have hs₁_pow : s₁G ^ p.val = 1 := by
            have hs₁_sub_pow : (⟨s₁, hs₁⟩ : S₁) ^ p.val = 1 := by
              exact
                Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
                  (show Monoid.exponent S₁ ∣ p.val by rw [hS₁exp]) ⟨s₁, hs₁⟩
            simpa [s₁G] using congrArg (fun z : S₁ => ((z : S) : G)) hs₁_sub_pow
          let C : Subgroup G := Subgroup.zpowers s₁G
          have hCelem : IsElementaryAbelian p.val C :=
            section10_isElementaryAbelian_zpowers_of_pow_eq_one
              (G := G) (p := p.val) hs₁_pow
          have hCcentA : C ≤ Subgroup.centralizer (A : Set G) := by
            intro z hz
            rw [Subgroup.mem_centralizer_iff]
            intro a ha
            rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, rfl⟩
            have hcomm : Commute a s₁G :=
              Subgroup.mem_centralizer_iff.mp hs₁_centA a ha
            exact (hcomm.zpow_right n).eq
          have hsupElem : IsElementaryAbelian p.val (A ⊔ C : Subgroup G) := by
            letI : IsElementaryAbelian p.val A := hA.1.2
            letI : IsElementaryAbelian p.val C := hCelem
            exact section10_isElementaryAbelian_sup_of_le_centralizer
              (G := G) (p := p.val) (E := A) (D := C) hCcentA
          have hAeqSup : A = A ⊔ C := hA.2.2 (A ⊔ C) le_sup_left hsupElem
          have hs₁A : s₁G ∈ A := by
            rw [hAeqSup]
            exact Subgroup.mem_sup_right (Subgroup.mem_zpowers s₁G)
          have hs₁A₀Z₁ : s₁G ∈ A₀ ⊔ section10OmegaOneCenter p (S : Subgroup G) := by
            simpa [hAeq] using hs₁A
          have hs₁A₀Y : s₁G ∈ A₀ ⊔ Y := by
            exact (sup_le le_sup_left (hZ₁leY.trans le_sup_right)) hs₁A₀Z₁
          have hs₂A₀Y : s₂G ∈ A₀ ⊔ Y := Subgroup.mem_sup_right hs₂Y
          have hmul : s₁G * s₂G ∈ A₀ ⊔ Y :=
            (A₀ ⊔ Y).mul_mem hs₁A₀Y hs₂A₀Y
          simpa [hs₁s₂G] using hmul
        · apply sup_le
          · intro a ha
            refine ⟨hAleS (hA₀.1 ha), ?_⟩
            change a ∈ Subgroup.centralizer (A : Set G)
            rw [Subgroup.mem_centralizer_iff]
            intro b hb
            letI : IsElementaryAbelian p.val A := hA.1.2
            exact setLike_mul_comm (s := A)
              hb (hA₀.1 ha)
          · exact hYleC
      exact ⟨hZeq, hZmemS, Y, hZ₁leY, hYleC, hYcyc, hdisj, hCeq⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section10_lemma_10_13_restrict_structural_package
    {p : Nat.Primes} {A P A₀ Y : Subgroup G}
    (hZmem : section10OmegaOneCenter p P ∈ section10PrimeOrderSubgroupsIn p A)
    (hZleY : section10OmegaOneCenter p P ≤ Y)
    (_hYleC : Y ≤ subgroupCentralizerIn P A)
    (hYcyc : IsCyclic Y) (hdisj : Disjoint A₀ Y)
    (hCeq : subgroupCentralizerIn P A = A₀ ⊔ Y)
    (htrans :
      ConjugationActionTransitiveOn (subgroupNormalizerIn P (A : Set G))
        {X | X ∈ section10PrimeOrderSubgroupsIn p A ∧ X ≠ section10OmegaOneCenter p P}) :
    section10OmegaOneCenter p P ∈ section10PrimeOrderSubgroupsIn p A ∧
      (∃ Z : Subgroup G,
        section10OmegaOneCenter p P ≤ Z ∧
          IsCyclic Z ∧
          Disjoint A₀ Z ∧
          subgroupCentralizerIn P A = A₀ ⊔ Z) ∧
      ConjugationActionTransitiveOn (subgroupNormalizerIn P (A : Set G))
        {X | X ∈ section10PrimeOrderSubgroupsIn p A ∧ X ≠ section10OmegaOneCenter p P} := by
  exact ⟨hZmem, ⟨⟨Y, hZleY, hYcyc, hdisj, hCeq⟩, htrans⟩⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section10_centralizer_restrict_sup_inf
    {p : Nat.Primes} {A P S A₀ Y : Subgroup G}
    (hA : A ∈ section10RankTwoMaximalElementaryAbelianSubgroups p G)
    (hAleP : A ≤ P) (hPleS : P ≤ S)
    (hA₀ : A₀ ∈ section10PrimeOrderSubgroupsIn p A)
    (hYleCS : Y ≤ subgroupCentralizerIn S A)
    (hCeqS : subgroupCentralizerIn S A = A₀ ⊔ Y) :
    subgroupCentralizerIn P A = A₀ ⊔ (Y ⊓ P) := by
  classical
  letI : IsElementaryAbelian p.val A := hA.1.2
  have hA₀leA : A₀ ≤ A := hA₀.1
  have hA₀leP : A₀ ≤ P := hA₀leA.trans hAleP
  have hA₀leCS : A₀ ≤ subgroupCentralizerIn P A := by
    intro a ha
    refine ⟨hA₀leP ha, ?_⟩
    change a ∈ Subgroup.centralizer (A : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact setLike_mul_comm (s := A) hb (hA₀leA ha)
  have hYinf_le_CP : Y ⊓ P ≤ subgroupCentralizerIn P A := by
    intro y hy
    exact ⟨hy.2, (hYleCS hy.1).2⟩
  have hA₀_norm_Y : A₀ ≤ Subgroup.normalizer (Y : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have hcomm : a * y = y * a :=
        Subgroup.mem_centralizer_iff.mp (hYleCS hy).2 a (hA₀leA ha)
      have hconj : a * y * a⁻¹ = y := by
        calc
          a * y * a⁻¹ = y * a * a⁻¹ := by rw [hcomm]
          _ = y := by simp
      simpa [hconj] using hy
    · intro hy
      let y' : G := a * y * a⁻¹
      have hy'Y : y' ∈ Y := by simpa [y'] using hy
      have hcomm' : a * y' = y' * a :=
        Subgroup.mem_centralizer_iff.mp (hYleCS hy'Y).2 a (hA₀leA ha)
      have hconj : a⁻¹ * y' * a = y' := by
        have h := congrArg (fun t : G => a⁻¹ * t) hcomm'
        simpa [mul_assoc] using h.symm
      have hy_eq : y = y' := by
        calc
          y = a⁻¹ * y' * a := by simp [y', mul_assoc]
          _ = y' := hconj
      simpa [hy_eq] using hy'Y
  apply le_antisymm
  · intro x hx
    have hxCS : x ∈ subgroupCentralizerIn S A := ⟨hPleS hx.1, hx.2⟩
    have hxSup : x ∈ A₀ ⊔ Y := by simpa [hCeqS] using hxCS
    let D : Subgroup G := A₀ ⊔ Y
    let A₀D : Subgroup D := A₀.subgroupOf D
    let YD : Subgroup D := Y.subgroupOf D
    haveI : YD.Normal := by
      simpa [D, YD] using
        (Subgroup.normal_subgroupOf_sup_of_le_normalizer
          (H := A₀) (N := Y) hA₀_norm_Y)
    let xD : D := ⟨x, by simpa [D] using hxSup⟩
    have hA₀D_YD_top : A₀D ⊔ YD = ⊤ := by
      calc
        A₀D ⊔ YD = D.subgroupOf D := by
          symm
          exact Subgroup.subgroupOf_sup
            (A := A₀) (A' := Y) (B := D)
            (by simp [D])
            (by simp [D])
        _ = ⊤ := by simp
    have hxTop : xD ∈ A₀D ⊔ YD := by
      simp [hA₀D_YD_top]
    rcases (Subgroup.mem_sup_of_normal_right
        (s := A₀D) (t := YD) (x := xD)).1 hxTop with
      ⟨aD, haD, yD, hyD, hmul⟩
    let a : G := aD
    let y : G := yD
    have haA₀ : a ∈ A₀ := by
      simpa [a, A₀D, Subgroup.mem_subgroupOf] using haD
    have hyY : y ∈ Y := by
      simpa [y, YD, Subgroup.mem_subgroupOf] using hyD
    have hxy : x = a * y := by
      have hval := congrArg (fun z : D => (z : G)) hmul
      simpa [xD, a, y] using hval.symm
    have hyP : y ∈ P := by
      have hx_eq : y = a⁻¹ * x := by
        calc
          y = a⁻¹ * (a * y) := by simp
          _ = a⁻¹ * x := by rw [← hxy]
      rw [hx_eq]
      exact P.mul_mem (P.inv_mem (hA₀leP haA₀)) hx.1
    rw [hxy]
    exact (A₀ ⊔ (Y ⊓ P : Subgroup G)).mul_mem
      (Subgroup.mem_sup_left haA₀)
      (Subgroup.mem_sup_right ⟨hyY, hyP⟩)
  · exact sup_le hA₀leCS hYinf_le_CP


omit [IsMinCE G] in
private theorem CFSG.section10_local_prime_order_subgroups_card_rank_two
    {p : Nat.Primes} {A : Subgroup G}
    (hA : A ∈ section10RankTwoMaximalElementaryAbelianSubgroups p G) :
    Nat.card {X : Subgroup A // Nat.card X = p.val} = p.val + 1 := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  letI : IsElementaryAbelian p.val A := hA.1.2
  letI : CommGroup A := IsMulCommutative.instCommGroup
  letI : AddCommGroup (Additive A) := Additive.addCommGroup
  let η : Subgroup A ≃o Submodule (ZMod p.val) (Additive A) :=
    Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := p.val))
  have hcard_submodule (H : Subgroup A) :
      Nat.card (η H) = Nat.card H := by
    let eη : (η H) ≃ Subgroup.toAddSubgroup H := {
      toFun x := ⟨x.1, by
        have hx :
            x.1 ∈ AddSubgroup.toZModSubmodule (n := p.val) (Subgroup.toAddSubgroup H) :=
          x.property
        exact hx⟩
      invFun x := ⟨x.1, by
        have hx : x.1 ∈ Subgroup.toAddSubgroup H := x.property
        exact hx⟩
      left_inv x := by
        apply Subtype.ext
        rfl
      right_inv x := by
        apply Subtype.ext
        rfl }
    let eH : Subgroup.toAddSubgroup H ≃ H := {
      toFun x := ⟨Additive.toMul x.1, (Additive.mem_toAddSubgroup H x.1).1 x.property⟩
      invFun x := ⟨Additive.ofMul (x : A), (Additive.mem_toAddSubgroup H _).2 x.property⟩
      left_inv x := by
        apply Subtype.ext
        rfl
      right_inv x := by
        apply Subtype.ext
        rfl }
    exact (Nat.card_congr eη).trans (Nat.card_congr eH)
  have hfinrank_iff (H : Subgroup A) :
      Module.finrank (ZMod p.val) (η H) = 1 ↔ Nat.card H = p.val := by
    have hnat :
        Nat.card (η H) =
          p.val ^ Module.finrank (ZMod p.val) (η H) := by
      simpa [ZMod.card] using
        Module.natCard_eq_pow_finrank (K := ZMod p.val) (V := η H)
    constructor
    · intro hdim
      rw [← hcard_submodule H, hnat, hdim, pow_one]
    · intro hcard
      have hpow :
          p.val ^ Module.finrank (ZMod p.val) (η H) = p.val ^ 1 := by
        rw [← hnat, hcard_submodule H, hcard, pow_one]
      exact Nat.pow_right_injective p.property.one_lt hpow
  let eSub :
      {X : Subgroup A // Nat.card X = p.val} ≃
        {L : Submodule (ZMod p.val) (Additive A) //
          Module.finrank (ZMod p.val) L = 1} := {
    toFun X := ⟨η X.1, (hfinrank_iff X.1).2 X.2⟩
    invFun L := ⟨η.symm L.1, (hfinrank_iff (η.symm L.1)).1 (by
      rw [η.apply_symm_apply]
      exact L.2)⟩
    left_inv X := by
      apply Subtype.ext
      exact η.symm_apply_apply X.1
    right_inv L := by
      apply Subtype.ext
      exact η.apply_symm_apply L.1 }
  have hdimA : Module.finrank (ZMod p.val) (Additive A) = 2 := by
    have hnat := Module.natCard_eq_pow_finrank (K := ZMod p.val) (V := Additive A)
    have hAcard_add : Nat.card (Additive A) = p.val ^ 2 := by
      calc
        Nat.card (Additive A) = Nat.card A :=
          Nat.card_congr (Additive.toMul : Additive A ≃ A)
        _ = p.val ^ 2 := hA.1.1
    have hpow :
        p.val ^ Module.finrank (ZMod p.val) (Additive A) = p.val ^ 2 := by
      simpa [ZMod.card, hAcard_add] using hnat.symm
    exact Nat.pow_right_injective p.property.one_lt hpow
  calc
    Nat.card {X : Subgroup A // Nat.card X = p.val}
        = Nat.card
            {L : Submodule (ZMod p.val) (Additive A) //
              Module.finrank (ZMod p.val) L = 1} := Nat.card_congr eSub
    _ = Nat.card (Projectivization (ZMod p.val) (Additive A)) := by
        exact Nat.card_congr (Projectivization.equivSubmodule (ZMod p.val) (Additive A)).symm
    _ = p.val + 1 := by
        simpa [ZMod.card] using
          Projectivization.card_of_finrank_two (ZMod p.val) (Additive A) hdimA

omit [IsMinCE G] in
private theorem CFSG.section10_prime_order_subgroups_card_rank_two
    {p : Nat.Primes} {A : Subgroup G}
    (hA : A ∈ section10RankTwoMaximalElementaryAbelianSubgroups p G) :
    Nat.card {X : Subgroup G // X ∈ section10PrimeOrderSubgroupsIn p A} = p.val + 1 := by
  classical
  let e :
      {X : Subgroup G // X ∈ section10PrimeOrderSubgroupsIn p A} ≃
        {X : Subgroup A // Nat.card X = p.val} := {
    toFun X := ⟨X.1.subgroupOf A, by
      simpa using (natCard_subgroupOf_eq X.1 A X.2.1).trans X.2.2⟩
    invFun X := ⟨X.1.map A.subtype, by
      constructor
      · intro x hx
        rcases Subgroup.mem_map.mp hx with ⟨xA, _hxA, rfl⟩
        exact xA.property
      · exact (Subgroup.card_map_of_injective (K := X.1) (f := A.subtype)
          Subtype.coe_injective).trans X.2⟩
    left_inv X := by
      apply Subtype.ext
      exact Subgroup.map_subgroupOf_eq_of_le X.2.1
    right_inv X := by
      apply Subtype.ext
      exact subgroupOf_map_subtype_eq (K := A) X.1 }
  calc
    Nat.card {X : Subgroup G // X ∈ section10PrimeOrderSubgroupsIn p A}
        = Nat.card {X : Subgroup A // Nat.card X = p.val} := Nat.card_congr e
    _ = p.val + 1 := section10_local_prime_order_subgroups_card_rank_two (G := G) hA

omit [IsMinCE G] in
private theorem CFSG.section10_noncentral_prime_order_subgroups_card_rank_two
    {p : Nat.Primes} {A Z : Subgroup G}
    (hA : A ∈ section10RankTwoMaximalElementaryAbelianSubgroups p G)
    (hZ : Z ∈ section10PrimeOrderSubgroupsIn p A) :
    Nat.card {X : Subgroup G // X ∈ section10PrimeOrderSubgroupsIn p A ∧ X ≠ Z} = p.val := by
  classical
  let Ω := {X : Subgroup G // X ∈ section10PrimeOrderSubgroupsIn p A}
  have hcardΩ : Nat.card Ω = p.val + 1 := by
    simpa [Ω] using section10_prime_order_subgroups_card_rank_two (G := G) hA
  let zΩ : Ω := ⟨Z, hZ⟩
  let e :
      {X : Subgroup G // X ∈ section10PrimeOrderSubgroupsIn p A ∧ X ≠ Z} ≃
        {X : Ω // X ≠ zΩ} := {
    toFun X := ⟨⟨X.1, X.2.1⟩, by
      intro h
      exact X.2.2 (congrArg Subtype.val h)⟩
    invFun X := ⟨X.1.1, X.1.2, by
      intro h
      exact X.2 (Subtype.ext h)⟩
    left_inv X := by
      apply Subtype.ext
      rfl
    right_inv X := by
      apply Subtype.ext
      apply Subtype.ext
      rfl }
  calc
    Nat.card {X : Subgroup G // X ∈ section10PrimeOrderSubgroupsIn p A ∧ X ≠ Z}
        = Nat.card {X : Ω // X ≠ zΩ} := Nat.card_congr e
    _ = p.val := by
      haveI : Fintype Ω := Fintype.ofFinite Ω
      haveI : Fintype {X : Ω // X ≠ zΩ} := Fintype.ofFinite _
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq]
      rw [← Nat.card_eq_fintype_card, hcardΩ]
      omega

omit [IsMinCE G] in
private theorem CFSG.section10_lemma_10_13_transitivity_from_split
    {p : Nat.Primes} {A P A₀ Y : Subgroup G}
    (_hpG : p ∈ subgroupPrimeSet (⊤ : Subgroup G))
    (hA : A ∈ section10RankTwoMaximalElementaryAbelianSubgroups p G)
    (hPp : IsPGroup p.val P) (hPnonab : ¬ IsMulCommutative P) (hAleP : A ≤ P)
    (hA₀ : A₀ ∈ section10PrimeOrderSubgroupsIn p A)
    (_hA₀ne : A₀ ≠ section10OmegaOneCenter p P)
    (hZmem : section10OmegaOneCenter p P ∈ section10PrimeOrderSubgroupsIn p A)
    (_hZleY : section10OmegaOneCenter p P ≤ Y)
    (hYcyc : IsCyclic Y) (_hdisj : Disjoint A₀ Y)
    (hCeq : subgroupCentralizerIn P A = A₀ ⊔ Y) :
    ConjugationActionTransitiveOn (subgroupNormalizerIn P (A : Set G))
      {X | X ∈ section10PrimeOrderSubgroupsIn p A ∧ X ≠ section10OmegaOneCenter p P} := by
  classical
  let C : Subgroup G := subgroupCentralizerIn P A
  let Z₀ : Subgroup G := section10OmegaOneCenter p P
  have hYleC : Y ≤ C := by
    intro y hy
    have hySup : y ∈ A₀ ⊔ Y := Subgroup.mem_sup_right hy
    simpa [C, hCeq] using hySup
  have hCcomm : IsMulCommutative C := by
    simpa [C] using
      section10_centralizerIn_isMulCommutative_of_eq_prime_cyclic_sup
        (G := G) (p := p) (A := A) (S := P) (A₀ := A₀) (Y := Y)
        hA hA₀ hYleC hYcyc hCeq
  have hCleP : C ≤ P := by
    intro x hx
    exact hx.1
  have hCneP : C ≠ P := by
    intro hCP
    have hPcomm : IsMulCommutative P := by
      rw [← hCP]
      exact hCcomm
    exact hPnonab hPcomm
  have hCsubP_ne_top : C.subgroupOf P ≠ ⊤ := by
    intro htop
    have hPC : P ≤ C := Subgroup.subgroupOf_eq_top.mp htop
    exact hCneP (le_antisymm hCleP hPC)
  have hCsubP_lt_top : C.subgroupOf P < ⊤ :=
    lt_of_le_of_ne le_top hCsubP_ne_top
  haveI : Fact p.val.Prime := ⟨p.property⟩
  have hPnil : Group.IsNilpotent P :=
    IsPGroup.isNilpotent (p := p.val) (G := P) hPp
  letI : Group.IsNilpotent P := hPnil
  have hnc : NormalizerCondition P := Group.normalizerCondition_of_isNilpotent (G := P)
  let CP : Subgroup P := C.subgroupOf P
  have hCsubP_lt_norm :
      CP < Subgroup.normalizer ((CP : Subgroup P) : Set P) := by
    exact hnc CP hCsubP_lt_top
  obtain ⟨xP, hxPnorm, hxPnotC⟩ :
      ∃ x : P,
        x ∈ Subgroup.normalizer ((CP : Subgroup P) : Set P) ∧
          x ∉ CP := by
    have hproper :
        ∃ x : P,
          x ∈ Subgroup.normalizer ((CP : Subgroup P) : Set P) ∧
            x ∉ CP := by
      by_contra hnone
      have hnorm_le : Subgroup.normalizer ((CP : Subgroup P) : Set P) ≤ CP := by
        intro x hx
        by_contra hxnot
        exact hnone ⟨x, hx, hxnot⟩
      exact (not_le_of_gt hCsubP_lt_norm) hnorm_le
    exact hproper
  have hx_normC : (xP : G) ∈ Subgroup.normalizer (C : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hyC
      have hySub : (⟨y, hCleP hyC⟩ : P) ∈ CP := hyC
      have hconj := (Subgroup.mem_normalizer_iff.mp hxPnorm (⟨y, hCleP hyC⟩ : P)).1 hySub
      change ((xP : G) * y * (xP : G)⁻¹) ∈ C at hconj
      simpa using hconj
    · intro hyC
      have hxinv : xP⁻¹ ∈ Subgroup.normalizer ((CP : Subgroup P) : Set P) :=
        (Subgroup.normalizer ((CP : Subgroup P) : Set P)).inv_mem hxPnorm
      let z : P := ⟨(xP : G) * y * (xP : G)⁻¹, hCleP hyC⟩
      have hzSub : z ∈ CP := hyC
      have hconj := (Subgroup.mem_normalizer_iff.mp hxinv z).1 hzSub
      change (((xP⁻¹ : P) * z * (xP⁻¹)⁻¹ : P) : G) ∈ C at hconj
      simpa [z, mul_assoc] using hconj
  have hx_notC : (xP : G) ∉ C := by
    intro hxC
    apply hxPnotC
    change (xP : G) ∈ C
    exact hxC
  have hA_le_C : A ≤ C := by
    intro a ha
    refine ⟨hAleP ha, ?_⟩
    change a ∈ Subgroup.centralizer (A : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    letI : IsElementaryAbelian p.val A := hA.1.2
    exact setLike_mul_comm (s := A) hb ha
  have hx_normA : (xP : G) ∈ Subgroup.normalizer (A : Set G) := by
    let ΩC : Subgroup G := (omega₁ (G := C) (p := p.val)).map C.subtype
    have hnormΩ :
        (xP : G) ∈ Subgroup.normalizer (ΩC : Set G) := by
      have hΩchar : (omega₁ (G := C) (p := p.val)).Characteristic :=
        omega₁_characteristic (G := C) (p := p.val)
      letI : (omega₁ (G := C) (p := p.val)).Characteristic := hΩchar
      have hnorm_le :
          Subgroup.normalizer (C : Set G) ≤ Subgroup.normalizer (ΩC : Set G) := by
        simpa [ΩC] using
          section10_normalizer_le_normalizer_map_subtype_of_characteristic_pre
            (G := G) C (omega₁ (G := C) (p := p.val))
      exact hnorm_le hx_normC
    have hΩCelem : IsElementaryAbelian p.val ΩC := by
      have hΩelemC : IsElementaryAbelian p.val (omega₁ (G := C) (p := p.val)) := by
        letI : IsMulCommutative C := hCcomm
        exact section10_omega1_isElementaryAbelian_of_commutative_pre
          (p := p.val) C
      letI : IsElementaryAbelian p.val (omega₁ (G := C) (p := p.val)) := hΩelemC
      simpa [ΩC] using
        section10_isElementaryAbelian_map_pre
          (G := C) (p := p.val) (A := omega₁ (G := C) (p := p.val))
          (G' := G) C.subtype
    have hA_le_ΩC : A ≤ ΩC := by
      intro a ha
      let AC : Subgroup C := A.subgroupOf C
      have hACelem : IsElementaryAbelian p.val AC := by
        haveI : IsElementaryAbelian p.val A := hA.1.2
        exact IsElementaryAbelian.subgroupOf
          (G := G) (p := p.val) hA_le_C
      letI : IsElementaryAbelian p.val AC := hACelem
      let aC : C := ⟨a, hA_le_C ha⟩
      have haAC : aC ∈ AC := by
        simpa [AC, aC, Subgroup.mem_subgroupOf] using ha
      have haCΩ : aC ∈ omega₁ (G := C) (p := p.val) := by
        exact elementaryAbelian_le_omega₁ (p := p.val) (G := C) (E := AC) haAC
      exact Subgroup.mem_map_of_mem C.subtype haCΩ
    have hAeqΩC : A = ΩC := hA.2.2 ΩC hA_le_ΩC hΩCelem
    simpa [hAeqΩC] using hnormΩ
  have hx_in_NPA : (xP : G) ∈ subgroupNormalizerIn P (A : Set G) := by
    exact section10_mem_subgroupNormalizerIn.mpr ⟨hx_normA, xP.property⟩
  let xN : subgroupNormalizerIn P (A : Set G) := ⟨(xP : G), hx_in_NPA⟩
  have hx_not_centralizes_A : (xP : G) ∉ Subgroup.centralizer (A : Set G) := by
    intro hxcent
    exact hx_notC ⟨xP.property, hxcent⟩
  have hx_centralizes_Z₀ : (xP : G) ∈ Subgroup.centralizer (Z₀ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp
      (section10_omegaOneCenter_le_centralizer (G := G) (p := p) P
        (by simpa [Z₀] using hz)) (xP : G) xP.property).symm
  have hx_conj_target :
      ∀ Q : Subgroup G,
        Q ∈ section10PrimeOrderSubgroupsIn p A →
        Q.conjBy (xP : G) ∈ section10PrimeOrderSubgroupsIn p A := by
    intro Q hQ
    constructor
    · intro q hq
      rw [Subgroup.conjBy, Subgroup.mem_map] at hq
      rcases hq with ⟨q₀, hq₀, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hx_normA q₀).1 (hQ.1 hq₀)
    · exact (section10_conjBy_card Q (xP : G)).trans hQ.2
  have hx_conj_Z₀ : Z₀.conjBy (xP : G) = Z₀ := by
    exact section10_conjBy_eq_of_mem_normalizer
      ((centralizer_le_normalizer (R := Z₀)) hx_centralizes_Z₀)
  have hx_conj_target_ne_Z₀ :
      ∀ Q : Subgroup G,
        Q ∈ section10PrimeOrderSubgroupsIn p A →
        Q ≠ Z₀ →
        Q.conjBy (xP : G) ≠ Z₀ := by
    intro Q hQ hQne hQconj
    have hback : Q = Z₀ := by
      calc
        Q = (Q.conjBy (xP : G)).conjBy ((xP : G)⁻¹) := by
          exact (section10_conjBy_inv Q (xP : G)).symm
        _ = Z₀.conjBy ((xP : G)⁻¹) := by rw [hQconj]
        _ = Z₀ := by
          have hxinv_normZ :
              ((xP : G)⁻¹) ∈ Subgroup.normalizer (Z₀ : Set G) :=
            (Subgroup.normalizer (Z₀ : Set G)).inv_mem
              ((centralizer_le_normalizer (R := Z₀)) hx_centralizes_Z₀)
          exact section10_conjBy_eq_of_mem_normalizer hxinv_normZ
    exact hQne hback
  have hx_fixed_prime_order_subgroup_centralizes :
      ∀ Q : Subgroup G,
        Q ∈ section10PrimeOrderSubgroupsIn p A →
        Q.conjBy (xP : G) = Q →
        (xP : G) ∈ Subgroup.centralizer (Q : Set G) := by
    intro Q hQ hQfix
    have hx_normQ : (xP : G) ∈ Subgroup.normalizer (Q : Set G) :=
      section10_mem_normalizer_of_conjBy_eq hQfix
    let R : Subgroup G := Subgroup.zpowers (xP : G)
    have hRnormQ : R ≤ Subgroup.normalizer (Q : Set G) := by
      rw [Subgroup.zpowers_le]
      exact hx_normQ
    haveI : Subgroup.Normalizes R Q := ⟨hRnormQ⟩
    have hRp : IsPGroup p.val R := by
      exact hPp.to_le (by
        intro r hr
        rcases Subgroup.mem_zpowers_iff.mp hr with ⟨n, rfl⟩
        exact P.zpow_mem xP.property n)
    have hQcyc : IsCyclic Q := isCyclic_of_prime_card hQ.2
    have hQtriv : ActsTrivially (A := R) (G := Q) := by
      exact actsTrivially_of_isPGroup_on_cyclic_prime_order
        p.property hRp hQcyc hQ.2
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    let xR : R := ⟨(xP : G), Subgroup.mem_zpowers (xP : G)⟩
    let qQ : Q := ⟨q, hq⟩
    have htriv := hQtriv xR qQ
    have hconj :
        ((xP : G) * q * (xP : G)⁻¹) = q := by
      simpa [xR, qQ, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
        hRnormQ] using congrArg Subtype.val htriv
    have h := congrArg (fun t : G => t * (xP : G)) hconj
    simpa [mul_assoc] using h.symm
  have hx_no_fixed_prime_order_subgroup :
      ∀ Q : Subgroup G,
        Q ∈ section10PrimeOrderSubgroupsIn p A →
        Q ≠ Z₀ →
        Q.conjBy (xP : G) ≠ Q := by
    intro Q hQ hQne hQfix
    have hxcentQ :
        (xP : G) ∈ Subgroup.centralizer (Q : Set G) :=
      hx_fixed_prime_order_subgroup_centralizes Q hQ hQfix
    have hAeq : A = Q ⊔ Z₀ :=
      section10_rankTwo_eq_sup_of_distinct_prime_order
        (G := G) hA hQ hZmem hQne
    apply hx_not_centralizes_A
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have haSup : a ∈ Q ⊔ Z₀ := by simpa [hAeq] using ha
    let D : Subgroup G := Q ⊔ Z₀
    let QD : Subgroup D := Q.subgroupOf D
    let ZD : Subgroup D := Z₀.subgroupOf D
    have hQ_norm_Z : Q ≤ Subgroup.normalizer (Z₀ : Set G) := by
      intro q hq
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · intro hz
        have hcomm : q * z = z * q := by
          letI : IsElementaryAbelian p.val A := hA.1.2
          exact setLike_mul_comm (s := A)
            (hQ.1 hq) (hZmem.1 hz)
        have hconj : q * z * q⁻¹ = z := by
          calc
            q * z * q⁻¹ = z * q * q⁻¹ := by rw [hcomm]
            _ = z := by simp [mul_assoc]
        simpa [hconj] using hz
      · intro hz
        let z' : G := q * z * q⁻¹
        have hz' : z' ∈ Z₀ := by simpa [z'] using hz
        have hcomm : q * z' = z' * q := by
          letI : IsElementaryAbelian p.val A := hA.1.2
          exact setLike_mul_comm (s := A)
            (hQ.1 hq) (hZmem.1 hz')
        have hz_eq : z = q⁻¹ * z' * q := by
          simp [z', mul_assoc]
        have hconj : q⁻¹ * z' * q = z' := by
          have h := congrArg (fun t : G => q⁻¹ * t) hcomm.symm
          simpa [mul_assoc] using h
        simpa [hz_eq, hconj] using hz'
    haveI : ZD.Normal := by
      simpa [D, ZD] using
        (Subgroup.normal_subgroupOf_sup_of_le_normalizer
          (H := Q) (N := Z₀) hQ_norm_Z)
    have hQD_ZD_top : QD ⊔ ZD = ⊤ := by
      calc
        QD ⊔ ZD = D.subgroupOf D := by
          symm
          exact Subgroup.subgroupOf_sup
            (A := Q) (A' := Z₀) (B := D)
            (by simp [D])
            (by simp [D])
        _ = ⊤ := by simp
    let aD : D := ⟨a, haSup⟩
    have haTop : aD ∈ QD ⊔ ZD := by simp [hQD_ZD_top]
    rcases (Subgroup.mem_sup_of_normal_right
        (s := QD) (t := ZD) (x := aD)).1 haTop with
      ⟨qD, hqD, zD, hzD, hqz⟩
    let q : G := qD
    let z : G := zD
    have hqQ : q ∈ Q := by simpa [q, QD, Subgroup.mem_subgroupOf] using hqD
    have hzZ : z ∈ Z₀ := by simpa [z, ZD, Subgroup.mem_subgroupOf] using hzD
    have ha_eq : a = q * z := by
      have hval := congrArg (fun y : D => (y : G)) hqz
      simpa [aD, q, z] using hval.symm
    have hxq : q * (xP : G) = (xP : G) * q :=
      Subgroup.mem_centralizer_iff.mp hxcentQ q hqQ
    have hxz : z * (xP : G) = (xP : G) * z :=
      Subgroup.mem_centralizer_iff.mp hx_centralizes_Z₀ z hzZ
    rw [ha_eq]
    calc
      q * z * (xP : G) = q * (z * (xP : G)) := by simp [mul_assoc]
      _ = q * ((xP : G) * z) := by rw [hxz]
      _ = (q * (xP : G)) * z := by simp [mul_assoc]
      _ = ((xP : G) * q) * z := by rw [hxq]
      _ = (xP : G) * (q * z) := by simp [mul_assoc]
  -- It remains to count the orbit of `x` on the rank-two projective line.
  let Ωsub := {Q : Subgroup G // Q ∈ section10PrimeOrderSubgroupsIn p A ∧ Q ≠ Z₀}
  have hK_conj_mem :
      ∀ k : subgroupNormalizerIn P (A : Set G), ∀ Q : Subgroup G,
        Q ∈ section10PrimeOrderSubgroupsIn p A →
        Q.conjBy (k : G) ∈ section10PrimeOrderSubgroupsIn p A := by
    intro k Q hQ
    have hk_normA : (k : G) ∈ Subgroup.normalizer (A : Set G) :=
      (section10_mem_subgroupNormalizerIn.mp k.property).1
    constructor
    · intro q hq
      rw [Subgroup.conjBy, Subgroup.mem_map] at hq
      rcases hq with ⟨q₀, hq₀, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hk_normA q₀).1 (hQ.1 hq₀)
    · exact (section10_conjBy_card Q (k : G)).trans hQ.2
  have hK_conj_Z₀ :
      ∀ k : subgroupNormalizerIn P (A : Set G), Z₀.conjBy (k : G) = Z₀ := by
    intro k
    have hkP : (k : G) ∈ P := (section10_mem_subgroupNormalizerIn.mp k.property).2
    have hk_centZ : (k : G) ∈ Subgroup.centralizer (Z₀ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (Subgroup.mem_centralizer_iff.mp
        (section10_omegaOneCenter_le_centralizer (G := G) (p := p) P
          (by simpa [Z₀] using hz)) (k : G) hkP).symm
    exact section10_conjBy_eq_of_mem_normalizer
      ((centralizer_le_normalizer (R := Z₀)) hk_centZ)
  have hK_conj_ne_Z₀ :
      ∀ k : subgroupNormalizerIn P (A : Set G), ∀ Q : Subgroup G,
        Q ≠ Z₀ → Q.conjBy (k : G) ≠ Z₀ := by
    intro k Q hQne hQconj
    have hback : Q = Z₀ := by
      calc
        Q = (Q.conjBy (k : G)).conjBy ((k : G)⁻¹) := by
          exact (section10_conjBy_inv Q (k : G)).symm
        _ = Z₀.conjBy ((k : G)⁻¹) := by rw [hQconj]
        _ = Z₀ := by
          have hk_inv : ((k : G)⁻¹) ∈ Subgroup.normalizer (Z₀ : Set G) := by
            have hk_norm : (k : G) ∈ Subgroup.normalizer (Z₀ : Set G) :=
              section10_mem_normalizer_of_conjBy_eq (hK_conj_Z₀ k)
            exact (Subgroup.normalizer (Z₀ : Set G)).inv_mem hk_norm
          exact section10_conjBy_eq_of_mem_normalizer hk_inv
    exact hQne hback
  letI : MulAction (subgroupNormalizerIn P (A : Set G)) Ωsub := {
    smul := fun k Q =>
      ⟨Q.1.conjBy (k : G),
        hK_conj_mem k Q.1 Q.2.1,
        hK_conj_ne_Z₀ k Q.1 Q.2.2⟩
    one_smul := by
      intro Q
      apply Subtype.ext
      exact section10_conjBy_one Q.1
    mul_smul := by
      intro k₁ k₂ Q
      apply Subtype.ext
      exact section10_conjBy_mul Q.1 (k₁ : G) (k₂ : G) }
  have hKp : IsPGroup p.val (subgroupNormalizerIn P (A : Set G)) :=
    hPp.to_le (section10_subgroupNormalizerIn_le P (A : Set G))
  have hΩcard : Nat.card Ωsub = p.val := by
    simpa [Ωsub, Z₀] using
      section10_noncentral_prime_order_subgroups_card_rank_two
        (G := G) (p := p) (A := A) (Z := Z₀) hA hZmem
  have hxN_no_fixed : ∀ Q : Ωsub, xN • Q ≠ Q := by
    intro Q hfix
    have hfix_val := congrArg Subtype.val hfix
    change Q.1.conjBy (xP : G) = Q.1 at hfix_val
    exact hx_no_fixed_prime_order_subgroup Q.1 Q.2.1 Q.2.2
      hfix_val
  intro Q₁ hQ₁ Q₂ hQ₂
  let Q₁sub : Ωsub := ⟨Q₁, hQ₁⟩
  let Q₂sub : Ωsub := ⟨Q₂, hQ₂⟩
  have hQ₁_orbit_card_ne_one :
      Nat.card (MulAction.orbit (subgroupNormalizerIn P (A : Set G)) Q₁sub) ≠ 1 := by
    intro hcard_one
    haveI : Fintype (MulAction.orbit (subgroupNormalizerIn P (A : Set G)) Q₁sub) :=
      Fintype.ofFinite _
    have hfix :
        Q₁sub ∈ MulAction.fixedPoints (subgroupNormalizerIn P (A : Set G)) Ωsub := by
      rw [MulAction.mem_fixedPoints_iff_card_orbit_eq_one]
      simpa [Nat.card_eq_fintype_card] using hcard_one
    exact hxN_no_fixed Q₁sub ((MulAction.mem_fixedPoints.mp hfix) xN)
  obtain ⟨n, hn⟩ :=
    hKp.card_orbit (α := Ωsub) Q₁sub
  have hn_pos : 0 < n := by
    by_contra hnpos
    have hn0 : n = 0 := by omega
    exact hQ₁_orbit_card_ne_one (by simpa [hn0] using hn)
  have hOrbit_le_Ω :
      Nat.card (MulAction.orbit (subgroupNormalizerIn P (A : Set G)) Q₁sub) ≤
        Nat.card Ωsub :=
    Nat.card_le_card_of_injective
      (fun Q : MulAction.orbit (subgroupNormalizerIn P (A : Set G)) Q₁sub => (Q : Ωsub))
      (fun a b h => Subtype.ext h)
  have hn_le_one : n ≤ 1 := by
    have hpown_le : p.val ^ n ≤ p.val ^ 1 := by
      calc
        p.val ^ n =
            Nat.card (MulAction.orbit (subgroupNormalizerIn P (A : Set G)) Q₁sub) := hn.symm
        _ ≤ Nat.card Ωsub := hOrbit_le_Ω
        _ = p.val ^ 1 := by rw [hΩcard, pow_one]
    exact (Nat.pow_le_pow_iff_right p.property.one_lt).1 hpown_le
  have hn_eq_one : n = 1 := by omega
  have hOrbit_card :
      Nat.card (MulAction.orbit (subgroupNormalizerIn P (A : Set G)) Q₁sub) =
        Nat.card Ωsub := by
    rw [hn, hn_eq_one, pow_one, hΩcard]
  have hOrbit_univ :
      MulAction.orbit (subgroupNormalizerIn P (A : Set G)) Q₁sub = Set.univ := by
    by_contra hne
    have hproper :
        Nat.card (MulAction.orbit (subgroupNormalizerIn P (A : Set G)) Q₁sub) <
          Nat.card Ωsub := by
      classical
      haveI : Finite Ωsub := inferInstance
      have hnot_all :
          ¬ ∀ Q : Ωsub,
            Q ∈ MulAction.orbit (subgroupNormalizerIn P (A : Set G)) Q₁sub := by
        intro hall
        exact hne (Set.eq_univ_iff_forall.mpr hall)
      push Not at hnot_all
      rcases hnot_all with ⟨Q, hQnot⟩
      simpa using
        (Finite.card_subtype_lt
          (p := fun Q : Ωsub =>
            Q ∈ MulAction.orbit (subgroupNormalizerIn P (A : Set G)) Q₁sub)
          hQnot)
    exact (ne_of_lt hproper) hOrbit_card
  have hQ₂orbit : Q₂sub ∈ MulAction.orbit (subgroupNormalizerIn P (A : Set G)) Q₁sub := by
    simp [hOrbit_univ]
  rcases MulAction.mem_orbit_iff.mp hQ₂orbit with ⟨k, hk⟩
  exact ⟨k, by
    have hkval := congrArg Subtype.val hk
    change Q₁.conjBy (k : G) = Q₂ at hkval
    exact hkval.symm⟩


public theorem CFSG.section10_lemma_10_13_structural_package
    {p : Nat.Primes} {A P A₀ : Subgroup G}
    (hpG : p ∈ subgroupPrimeSet (⊤ : Subgroup G))
    (hA : A ∈ section10RankTwoMaximalElementaryAbelianSubgroups p G)
    (hPp : IsPGroup p.val P) (hPnonab : ¬ IsMulCommutative P) (hAleP : A ≤ P)
    (hA₀ : A₀ ∈ section10PrimeOrderSubgroupsIn p A)
    (hA₀ne : A₀ ≠ section10OmegaOneCenter p P) :
    section10OmegaOneCenter p P ∈ section10PrimeOrderSubgroupsIn p A ∧
      (∃ Z : Subgroup G,
        section10OmegaOneCenter p P ≤ Z ∧
          IsCyclic Z ∧
          Disjoint A₀ Z ∧
          subgroupCentralizerIn P A = A₀ ⊔ Z) ∧
      ConjugationActionTransitiveOn (subgroupNormalizerIn P (A : Set G))
        {X | X ∈ section10PrimeOrderSubgroupsIn p A ∧ X ≠ section10OmegaOneCenter p P} := by
  classical
  obtain ⟨S, hPleS⟩ := section10_exists_sylow_over_pSubgroup (G := G) (p := p) hPp
  have hAleS : A ≤ (S : Subgroup G) := hAleP.trans hPleS
  obtain ⟨hΩeq, hZmemS, Y, hZleY_S, hYleCS, hYcyc, hdisj, hCeqS⟩ :=
    section10_lemma_10_13_sylow_structural_package
      (G := G) (p := p) (A := A) (P := P) (A₀ := A₀) S
      hpG hA hPp hPnonab hAleP hPleS hAleS hA₀ hA₀ne
  have hZmem : section10OmegaOneCenter p P ∈ section10PrimeOrderSubgroupsIn p A := by
    simpa [hΩeq] using hZmemS
  let Z : Subgroup G := Y ⊓ P
  have hZleC : Z ≤ subgroupCentralizerIn P A := by
    intro z hz
    exact ⟨hz.2, (hYleCS hz.1).2⟩
  have hZleY : section10OmegaOneCenter p P ≤ Z := by
    intro z hz
    exact ⟨by simpa [← hΩeq] using hZleY_S (by simpa [hΩeq] using hz),
      section10_omegaOneCenter_le (G := G) (p := p) P hz⟩
  have hZcyc : IsCyclic Z := by
    exact Subgroup.isCyclic_of_le (H := Z) (H' := Y) inf_le_left
  have hdisjZ : Disjoint A₀ Z := hdisj.mono_right inf_le_left
  have hCeq : subgroupCentralizerIn P A = A₀ ⊔ Z := by
    simpa [Z] using
      section10_centralizer_restrict_sup_inf
        (G := G) (p := p) (A := A) (P := P) (S := (S : Subgroup G))
        (A₀ := A₀) (Y := Y) hA hAleP hPleS hA₀ hYleCS hCeqS
  have htrans :
      ConjugationActionTransitiveOn (subgroupNormalizerIn P (A : Set G))
        {X | X ∈ section10PrimeOrderSubgroupsIn p A ∧ X ≠ section10OmegaOneCenter p P} :=
    section10_lemma_10_13_transitivity_from_split
      (G := G) hpG hA hPp hPnonab hAleP hA₀ hA₀ne hZmem hZleY hZcyc hdisjZ hCeq
  exact
    section10_lemma_10_13_restrict_structural_package
      (G := G) hZmem hZleY hZleC hZcyc hdisjZ hCeq htrans


end Section10

/-!
# Lemma 10.13(a) from BG Section 10

This file contains Lemma 10.13(a) from BG Section 10.
-/

section Section10

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

/-- Lemma 10.13(a). -/
public theorem CFSG.lemma_10_13_a
    {p : Nat.Primes} {A P A₀ : Subgroup G}
    (hpG : p ∈ subgroupPrimeSet (⊤ : Subgroup G))
    (hA : A ∈ section10RankTwoMaximalElementaryAbelianSubgroups p G)
    (hPp : IsPGroup p.val P) (hPnonab : ¬ IsMulCommutative P) (hAleP : A ≤ P)
    (hA₀ : A₀ ∈ section10PrimeOrderSubgroupsIn p A)
    (hA₀ne : A₀ ≠ section10OmegaOneCenter p P) :
    section10OmegaOneCenter p P ∈ section10PrimeOrderSubgroupsIn p A := by
  exact
    (section10_lemma_10_13_structural_package
      (G := G) hpG hA hPp hPnonab hAleP hA₀ hA₀ne).1

end Section10

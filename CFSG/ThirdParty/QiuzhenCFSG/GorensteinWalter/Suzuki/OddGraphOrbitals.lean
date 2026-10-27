module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphRootBridge
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinCommutingPairs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinCosetPairDistribution
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.InvertedSetCardSmall
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.TwoCoreNormal
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

private lemma dihedralThree_centralizer_element :
    ∀ s x : DihedralGroup 3, IsInvolution s → Commute s x → x = 1 ∨ x = s := by
  intro s x hs hx
  rcases dihedralGroup_cases s with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · have hi1 : (DihedralGroup.r i : DihedralGroup 3) ≠ 1 := hs.1
    have hpow : (DihedralGroup.r i : DihedralGroup 3) ^ 3 = 1 := by
      rw [pow_succ, pow_two, DihedralGroup.r_mul_r, DihedralGroup.r_mul_r]
      congr 1
      calc
        i + i + i = (3 : ZMod 3) * i := by ring
        _ = 0 := by rw [show (3 : ZMod 3) = 0 by decide, zero_mul]
    have hord3 : orderOf (DihedralGroup.r i : DihedralGroup 3) ∣ 3 :=
      orderOf_dvd_of_pow_eq_one hpow
    have hord2 : orderOf (DihedralGroup.r i : DihedralGroup 3) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hs.2)
    have hord1 : orderOf (DihedralGroup.r i : DihedralGroup 3) = 1 := by
      have hd : orderOf (DihedralGroup.r i : DihedralGroup 3) ∣ Nat.gcd 2 3 :=
        Nat.dvd_gcd hord2 hord3
      simpa using hd
    exact False.elim (hi1 (orderOf_eq_one_iff.mp hord1))
  · rcases dihedralGroup_cases x with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · left
      have hij : i + j = i - j :=
        DihedralGroup.sr.inj (by simpa [Commute, SemiconjBy] using hx.eq)
      have h2j : (2 : ZMod 3) * j = 0 := by
        linear_combination hij
      have h2ne : (2 : ZMod 3) ≠ 0 := by decide
      have hj : j = 0 := (mul_eq_zero.mp h2j).resolve_left h2ne
      rw [hj]
      simp
    · right
      have hij : i - j = j - i :=
        DihedralGroup.r.inj (by simpa [Commute, SemiconjBy] using hx.eq.symm)
      have h2 : (2 : ZMod 3) * (i - j) = 0 := by
        calc
          (2 : ZMod 3) * (i - j) = (i - j) + (i - j) := by ring
          _ = (i - j) + (j - i) := by rw [hij]
          _ = 0 := by ring
      have h2ne : (2 : ZMod 3) ≠ 0 := by decide
      have hzero : i - j = 0 := (mul_eq_zero.mp h2).resolve_left h2ne
      exact congrArg DihedralGroup.sr (sub_eq_zero.mp hzero).symm

private lemma hhat_involution_not_twoCore_inverts_U
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    {s : G} (hsH : s ∈ c.Hhat) (hsI : IsInvolution s)
    (hsV : s ∉ twoCoreOf c.Hhat) :
    ∀ u : G, u ∈ c.U → s * u * s⁻¹ = u⁻¹ := by
  classical
  have hklein : IsKleinFour (pCore 2 c.Hhat) :=
    firstCase_twoCore_isKleinFour hmin c hfirst
  obtain ⟨_d0, K, hKHall, hKne, hKall⟩ :=
    firstCase_klein_data_complete hmin c hfirst hklein
  have hU3 : Nat.card c.U = 3 := firstCase_U_card_three hmin c hfirst d
  have hK3 : Nat.card K = 3 :=
    firstCase_klein_K_card_eq_three_of_U_card_three c hKHall hKne hU3
  have hKleU : K ≤ c.U := hKHall.1.trans (fittingSubgroupOf_le c.U)
  have hKeq : K = c.U := by
    apply Subgroup.eq_of_le_of_card_ge hKleU
    rw [hK3, hU3]
  have hKinv := (hKall s hsH hsI hsV).1
  intro u hu
  have huK : u ∈ K := by rw [hKeq]; exact hu
  have huInv : u ∈ invertedElements c.U s := by
    rw [← hKinv]
    exact huK
  exact huInv.2

private theorem hhat_centralizer_card_four
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    {s : G} (hsH : s ∈ c.Hhat) (hsI : IsInvolution s)
    (hsV : s ∉ twoCoreOf c.Hhat) :
    Nat.card {x : G // x ∈ c.Hhat ∧ Commute s x} = 4 := by
  classical
  let V : Subgroup G := twoCoreOf c.Hhat
  let H : Subgroup G := c.Hhat
  let N : Subgroup H := pCore 2 H ⊔ pPrimeCore 2 H
  let q : H →* (H ⧸ N) := QuotientGroup.mk' N
  let e : (H ⧸ N) ≃* DihedralGroup 3 :=
    (firstCase_klein_quotient_d6 hmin c hfirst
      (firstCase_twoCore_isKleinFour hmin c hfirst)).some
  let sH : H := ⟨s, hsH⟩
  let sb : DihedralGroup 3 := e (q sH)
  have hklein : IsKleinFour (pCore 2 c.Hhat) :=
    firstCase_twoCore_isKleinFour hmin c hfirst
  have hVK : IsKleinFour V := by
    simpa [V] using firstCase_klein_V_klein c hklein
  have hU3 : Nat.card c.U = 3 := firstCase_U_card_three hmin c hfirst d
  have hUeq : c.U = oddCoreOf c.Hhat := (theorem_2_6 hmin c).1
  have hNmap : N.map H.subtype = V ⊔ c.U := by
    dsimp [N, H, V]
    rw [Subgroup.map_sup]
    simp [twoCoreOf, oddCoreOf, hUeq]
  have hsbI : IsInvolution sb := by
    refine ⟨?_, ?_⟩
    · intro hb
      have hq1 : q sH = 1 := by
        apply e.injective
        simpa [sb] using hb
      have hsN : sH ∈ N := (QuotientGroup.eq_one_iff sH).mp hq1
      have hsVU : s ∈ V ⊔ c.U := by
        rw [← hNmap]
        exact Subgroup.mem_map.mpr ⟨sH, hsN, rfl⟩
      exact hsV (firstCase_klein_involution_mem_twoCore_of_mem_VU
        hmin c hklein hsVU hsI)
    · change (e (q sH)) ^ 2 = 1
      rw [← map_pow, ← map_pow]
      have hsH2 : sH ^ 2 = 1 := by
        apply Subtype.ext
        exact hsI.2
      rw [hsH2]
      simp
  have hVleH : V ≤ c.Hhat := (twoCoreOf_isNormalIn c.Hhat).1
  have hVnormal : IsNormalIn V c.Hhat := twoCoreOf_isNormalIn c.Hhat
  have hVcentU : V ≤ Subgroup.centralizer (c.U : Set G) := by
    simpa [V, hUeq] using twoCoreOf_centralizes_oddCoreOf c.Hhat
  have hVnormU : V ≤ Subgroup.normalizer (c.U : Set G) :=
    hVcentU.trans (Subgroup.centralizer_le_normalizer (c.U : Set G))
  have hdisj : Disjoint V c.U := by
    apply Subgroup.disjoint_of_coprime_natCard
    rw [hVK.card_four, hU3]
    norm_num
  have hVUset : ((V ⊔ c.U : Subgroup G) : Set G) =
      (V : Set G) * (c.U : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right V c.U hVnormU
  have hsInvU : ∀ u : G, u ∈ c.U → s * u * s⁻¹ = u⁻¹ :=
    hhat_involution_not_twoCore_inverts_U hmin c hfirst d hsH hsI hsV
  have hkernel : ∀ xH : H, Commute s (xH : G) →
      q xH = 1 → (xH : G) ∈ V := by
    intro xH hsx hxq
    let x : G := xH
    have hxH : x ∈ c.Hhat := xH.2
    have hxN : xH ∈ N := (QuotientGroup.eq_one_iff xH).mp hxq
    have hxVU : x ∈ V ⊔ c.U := by
      rw [← hNmap]
      exact Subgroup.mem_map.mpr ⟨xH, hxN, rfl⟩
    have hxprod : x ∈ (V : Set G) * (c.U : Set G) := by
      rw [← hVUset]
      exact hxVU
    rcases Set.mem_mul.mp hxprod with ⟨v, hv, u, hu, hvux⟩
    let vp : G := s * v * s⁻¹
    have hvp : vp ∈ V := hVnormal.2 s hsH v hv
    have hconjx : s * x * s⁻¹ = x := by
      calc
        s * x * s⁻¹ = (x * s) * s⁻¹ := by rw [hsx.eq]
        _ = x := by group
    have hprod : vp * u⁻¹ = v * u := by
      calc
        vp * u⁻¹ = (s * v * s⁻¹) * (s * u * s⁻¹) := by rw [hsInvU u hu]
        _ = s * (v * u) * s⁻¹ := by group
        _ = s * x * s⁻¹ := by rw [hvux]
        _ = x := hconjx
        _ = v * u := hvux.symm
    let a : V × c.U := ⟨⟨vp, hvp⟩, ⟨u⁻¹, c.U.inv_mem hu⟩⟩
    let b : V × c.U := ⟨⟨v, hv⟩, ⟨u, hu⟩⟩
    have hab : a = b := by
      apply Subgroup.mul_injective_of_disjoint hdisj
      exact hprod
    have huInvEq : u⁻¹ = u := by
      exact congrArg (fun z : V × c.U => (z.2 : G)) hab
    have hu2 : u ^ 2 = 1 := by
      rw [pow_two]
      calc
        u * u = u⁻¹ * u := congrArg (fun z : G => z * u) huInvEq.symm
        _ = 1 := inv_mul_cancel u
    have hu1 : u = 1 := by
      by_cases huone : u = 1
      · exact huone
      · exact firstCase_odd_subgroup_involution_eq_one c (by
          rw [hU3]
          norm_num) hu ⟨huone, hu2⟩
    change x ∈ V
    rw [← hvux, hu1]
    simpa using hv
  have hclass : ∀ x : G, x ∈ c.Hhat → Commute s x → x ≠ 1 →
      IsInvolution x := by
    intro x hxH hsx hxne
    let xH : H := ⟨x, hxH⟩
    have hsHxH : Commute sH xH := by
      apply Subtype.ext
      exact hsx.eq
    have hbcomm : Commute sb (e (q xH)) := (hsHxH.map q).map e
    rcases dihedralThree_centralizer_element sb (e (q xH)) hsbI hbcomm with hb1 | hbs
    · have hxq : q xH = 1 := by
        apply e.injective
        simpa using hb1
      have hxV : x ∈ V := hkernel xH hsx hxq
      exact ⟨hxne, by
        simpa [pow_two] using congrArg Subtype.val (hVK.mul_self ⟨x, hxV⟩)⟩
    · have hxq : q xH = q sH := by
        apply e.injective
        simpa [sb] using hbs
      let z : G := s * x
      have hzH : z ∈ c.Hhat := c.Hhat.mul_mem hsH hxH
      have hzs : Commute s z := by
        rw [Commute]
        dsimp [z]
        have hss : s * s = 1 := by simpa [pow_two] using hsI.2
        calc
          s * (s * x) = (s * s) * x := by group
          _ = x := by rw [hss]; simp
          _ = x * (s * s) := by rw [hss]; simp
          _ = (x * s) * s := by group
          _ = (s * x) * s := by rw [hsx.eq]
      have hzq : q (⟨z, hzH⟩ : H) = 1 := by
        change q (sH * xH) = 1
        rw [map_mul, hxq]
        have hqs2 : (q sH) ^ 2 = 1 := by
          rw [← map_pow]
          have hsH2 : sH ^ 2 = 1 := by
            apply Subtype.ext
            exact hsI.2
          rw [hsH2]
          simp
        simpa [pow_two] using hqs2
      have hzV : z ∈ V := hkernel ⟨z, hzH⟩ hzs hzq
      have hszeq : s * z = x := by
        dsimp [z]
        rw [← mul_assoc, show s * s = 1 by simpa [pow_two] using hsI.2]
        simp
      have hszcomm : Commute s z := hzs
      refine ⟨hxne, ?_⟩
      rw [← hszeq, pow_two]
      calc
        (s * z) * (s * z) = s * (z * s) * z := by group
        _ = s * (s * z) * z := by rw [hszcomm.eq]
        _ = (s * s) * (z * z) := by group
        _ = 1 := by
          rw [show s * s = 1 by simpa [pow_two] using hsI.2]
          have hz2 : z * z = 1 := by
            simpa [pow_two] using congrArg Subtype.val (hVK.mul_self ⟨z, hzV⟩)
          rw [hz2]
          simp
  let C : Type u := {x : G // x ∈ c.Hhat ∧ Commute s x}
  let J : Type u := {x : G // IsInvolution x ∧ x ∈ c.Hhat ∧ Commute s x}
  let B : Type u := {x : C // (x : G) ≠ 1}
  let eBJ : B ≃ J :=
    { toFun := fun x => ⟨(x : G), hclass x x.1.2.1 x.1.2.2 x.2,
        x.1.2.1, x.1.2.2⟩
      invFun := fun x => ⟨⟨(x : G), x.2.2.1, x.2.2.2⟩, x.2.1.1⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  let A : Type u := {x : C // (x : G) = 1}
  have hA : Nat.card A = 1 := by
    apply (Nat.card_eq_one_iff_exists).2
    let oneA : A := ⟨⟨1, c.Hhat.one_mem, by simp⟩, rfl⟩
    refine ⟨oneA, ?_⟩
    intro x
    apply Subtype.ext
    apply Subtype.ext
    exact x.2
  have hCsplit : Nat.card C = Nat.card A + Nat.card B := by
    let : Fintype C := Fintype.ofFinite C
    let : Fintype A := Fintype.ofFinite A
    let : Fintype B := Fintype.ofFinite B
    have hcomp := Fintype.card_subtype_compl
      (α := C) (p := fun x : C => (x : G) = 1)
    have hBcard : Nat.card B = Nat.card C - Nat.card A := by
      simpa [Nat.card_eq_fintype_card, A, B] using hcomp
    have hAle : Nat.card A ≤ Nat.card C := by
      simpa [Nat.card_eq_fintype_card, A] using
        (Fintype.card_subtype_le (p := fun x : C => (x : G) = 1))
    omega
  let JV : Type u := {x : J // (x : G) ∈ V}
  let JO : Type u := {x : J // (x : G) ∉ V}
  let TV : Type u := {v : G // IsInvolution v ∧ v ∈ V ∧ Commute v s}
  let TO : Type u := {x : G // IsInvolution x ∧ x ∈ c.Hhat ∧
    x ∉ V ∧ Commute s x}
  let eJV : JV ≃ TV :=
    { toFun := fun x => ⟨(x : G), x.1.2.1, x.2, x.1.2.2.2.symm⟩
      invFun := fun x => ⟨⟨(x : G), x.2.1, hVleH x.2.2.1, x.2.2.2.symm⟩,
        x.2.2.1⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  let eJO : JO ≃ TO :=
    { toFun := fun x => ⟨(x : G), x.1.2.1, x.1.2.2.1, x.2, x.1.2.2.2⟩
      invFun := fun x => ⟨⟨(x : G), x.2.1, x.2.2.1, x.2.2.2.2⟩,
        x.2.2.2.1⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  have hJV : Nat.card JV = 1 := by
    rw [Nat.card_congr eJV]
    simpa [TV, V] using firstCase_klein_fixed_V_involution_card_one
      hmin c hfirst hklein hsH hsI hsV
  have hJO : Nat.card JO = 2 := by
    rw [Nat.card_congr eJO]
    simpa [TO, V] using firstCase_klein_Hhat_outside_commuting_fiber_card_two
      hmin c hfirst hklein hsH hsI hsV
  have hJsplit : Nat.card J = Nat.card JV + Nat.card JO := by
    let : Fintype J := Fintype.ofFinite J
    let : Fintype JV := Fintype.ofFinite JV
    let : Fintype JO := Fintype.ofFinite JO
    have hcomp := Fintype.card_subtype_compl
      (α := J) (p := fun x : J => (x : G) ∈ V)
    have hJOcard : Nat.card JO = Nat.card J - Nat.card JV := by
      simpa [Nat.card_eq_fintype_card, JV, JO] using hcomp
    have hJVle : Nat.card JV ≤ Nat.card J := by
      simpa [Nat.card_eq_fintype_card, JV] using
        (Fintype.card_subtype_le (p := fun x : J => (x : G) ∈ V))
    omega
  rw [hCsplit, hA, Nat.card_congr eBJ, hJsplit, hJV, hJO]

/-- A non-base coset containing exactly two involutions has an `Ĥ`-orbit
of size eighteen. -/
public theorem firstCaseCosetLayer_two_orbit_card
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    (q : G ⧸ c.Hhat)
    (hq : q ≠ cosetInvolution_base c.Hhat ∧
      Nat.card (cosetInvolution_fiber c.Hhat q) = 2) :
    Nat.card (MulAction.orbit c.Hhat q) = 18 := by
  classical
  let F : Type u := cosetInvolution_fiber c.Hhat q
  have hFcard : Nat.card F = 2 := hq.2
  have hFpos : 0 < Nat.card F := by rw [hFcard]; norm_num
  obtain ⟨yF⟩ := (Nat.card_pos_iff.mp hFpos).1
  let y : G := yF.1
  have hyI : IsInvolution y := yF.2.1
  have hyproj : cosetInvolution_proj c.Hhat y = q := yF.2.2
  have hyH : y ∉ c.Hhat := by
    intro hyH
    apply hq.1
    rw [← hyproj]
    unfold cosetInvolution_proj cosetInvolution_base
    apply (QuotientGroup.eq (s := c.Hhat)).mpr
    have hyInv : y⁻¹ = y :=
      inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hyI.2)
    simpa [hyInv] using hyH
  have hcfcard : Nat.card (cosetFiber c y) = 2 := by
    change Nat.card {z : G // IsInvolution z ∧
      cosetInvolution_proj c.Hhat z = cosetInvolution_proj c.Hhat y} = 2
    rw [hyproj]
    exact hFcard
  let eFI : cosetFiber c y ≃
      {x : G // x ∈ invertedElements c.Hhat y} :=
    cosetFiber_equiv_inverted c hyI hyH
  have hIcard : Nat.card {x : G // x ∈ invertedElements c.Hhat y} = 2 := by
    calc
      Nat.card {x : G // x ∈ invertedElements c.Hhat y} =
          Nat.card (cosetFiber c y) := (Nat.card_congr eFI).symm
      _ = 2 := hcfcard
  let oneI : {x : G // x ∈ invertedElements c.Hhat y} :=
    ⟨1, c.Hhat.one_mem, by simp⟩
  obtain ⟨tI, htIne, _htAll⟩ := (Nat.card_eq_two_iff' oneI).mp hIcard
  let t : G := tI.1
  have htI : t ∈ invertedElements c.Hhat y := tI.2
  have htne : t ≠ 1 := by
    intro ht
    apply htIne
    apply Subtype.ext
    exact ht
  have ht2 : t * t = 1 :=
    inverted_card_two_mul_self c.Hhat hyI htI hIcard
  have htInv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hytFix : y * t * y⁻¹ = t := by
    simpa [htInv] using htI.2
  have hyt : Commute y t := by
    rw [Commute]
    exact mul_inv_eq_iff_eq_mul.mp (by simpa [mul_assoc] using hytFix)
  let z : G := t * y
  have hzI : IsInvolution z := by
    refine ⟨?_, ?_⟩
    · intro hzone
      apply hyH
      have hyEq : y = t⁻¹ := eq_inv_of_mul_eq_one_right hzone
      rw [hyEq]
      exact c.Hhat.inv_mem htI.1
    · rw [pow_two]
      dsimp [z]
      calc
        (t * y) * (t * y) = t * (y * t) * y := by group
        _ = t * (t * y) * y := by rw [hyt.eq]
        _ = (t * t) * (y * y) := by group
        _ = 1 := by
          rw [ht2, show y * y = 1 by simpa [pow_two] using hyI.2]
          simp
  have hzproj : cosetInvolution_proj c.Hhat z = q := by
    rw [← hyproj]
    unfold cosetInvolution_proj
    apply (QuotientGroup.eq (s := c.Hhat)).mpr
    have hyInv : y⁻¹ = y :=
      inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hyI.2)
    have hmain : ((t * y)⁻¹)⁻¹ * y⁻¹ = t := by
      rw [inv_inv, hyInv]
      rw [mul_assoc, show y * y = 1 by simpa [pow_two] using hyI.2]
      simp
    rw [hmain]
    exact htI.1
  let zF : F := ⟨z, hzI, hzproj⟩
  have hyz_ne : yF ≠ zF := by
    intro heq
    apply htne
    have hyz : y = z := congrArg Subtype.val heq
    calc
      t = (t * y) * y⁻¹ := by group
      _ = z * y⁻¹ := by rfl
      _ = y * y⁻¹ := by rw [← hyz]
      _ = 1 := by simp
  obtain ⟨wF, hwFne, hwFuniq⟩ := (Nat.card_eq_two_iff' yF).mp hFcard
  have hzFw : zF = wF := hwFuniq zF hyz_ne.symm
  have hFcases : ∀ a : F, a = yF ∨ a = zF := by
    intro a
    by_cases hay : a = yF
    · exact Or.inl hay
    · exact Or.inr ((hwFuniq a hay).trans hzFw.symm)
  have htyz : t = y * z := by
    dsimp [z]
    calc
      t = t * (y * y) := by rw [show y * y = 1 by simpa [pow_two] using hyI.2]; simp
      _ = (t * y) * y := by group
      _ = (y * t) * y := by rw [hyt.eq]
      _ = y * (t * y) := by group
  have hyz : Commute y z := by
    dsimp [z]
    calc
      y * (t * y) = (y * t) * y := by group
      _ = (t * y) * y := by rw [hyt.eq]
  have htV : t ∉ twoCoreOf c.Hhat := by
    intro htV
    have hyC : y ∈ Subgroup.centralizer ({t} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hyt.eq
    exact hyH (firstCase_klein_centralizer_twoCore_le_Hhat hmin c
      (firstCase_twoCore_isKleinFour hmin c hfirst) t htV htne hyC)
  have htI' : IsInvolution t := ⟨htne, by simpa [pow_two] using ht2⟩
  let C : Type u := {x : G // x ∈ c.Hhat ∧ Commute t x}
  have hCcard : Nat.card C = 4 :=
    hhat_centralizer_card_four hmin c hfirst d htI.1 htI' htV
  let conjF : ∀ h : c.Hhat, (h : G) • q = q → F → F := fun h hfix w => by
    let w' := (conjFiberEquiv c.Hhat h.2 q).symm w
    refine ⟨w'.1, w'.2.1, w'.2.2.trans ?_⟩
    have hmk : QuotientGroup.mk ((h : G) * q.out) = (h : G) • q := by
      simpa using (MulAction.Quotient.mk_smul_out (b := (h : G)) (q := q))
    exact hmk.trans hfix
  have conjF_val (h : c.Hhat) (hfix : (h : G) • q = q) (w : F) :
      (conjF h hfix w).1 = (h : G) * w.1 * (h : G)⁻¹ := by
    rfl
  have hstab_centralizes : ∀ h : MulAction.stabilizer c.Hhat q,
      Commute t (h : G) := by
    intro h
    have hfix : (h.1 : G) • q = q := MulAction.mem_stabilizer_iff.mp h.2
    let cy : F := conjF h.1 hfix yF
    let cz : F := conjF h.1 hfix zF
    have hcycz : cy ≠ cz := by
      intro heq
      apply hyz_ne
      apply Subtype.ext
      have heqG : (h.1 : G) * y * (h.1 : G)⁻¹ =
          (h.1 : G) * z * (h.1 : G)⁻¹ := by
        calc
          (h.1 : G) * y * (h.1 : G)⁻¹ = cy.1 := by
            exact (conjF_val h.1 hfix yF).symm
          _ = cz.1 := congrArg Subtype.val heq
          _ = (h.1 : G) * z * (h.1 : G)⁻¹ := by
            exact conjF_val h.1 hfix zF
      calc
        y = (h.1 : G)⁻¹ * ((h.1 : G) * y * (h.1 : G)⁻¹) * (h.1 : G) := by group
        _ = (h.1 : G)⁻¹ * ((h.1 : G) * z * (h.1 : G)⁻¹) * (h.1 : G) := by rw [heqG]
        _ = z := by group
    have hprod : cy.1 * cz.1 = y * z := by
      rcases hFcases cy with hcy | hcy <;> rcases hFcases cz with hcz | hcz
      · exact False.elim (hcycz (hcy.trans hcz.symm))
      · rw [hcy, hcz]
      · rw [hcy, hcz]
        exact hyz.eq.symm
      · exact False.elim (hcycz (hcy.trans hcz.symm))
    have hconjt : (h.1 : G) * t * (h.1 : G)⁻¹ = t := by
      calc
        (h.1 : G) * t * (h.1 : G)⁻¹ =
            (h.1 : G) * (y * z) * (h.1 : G)⁻¹ := by rw [htyz]
        _ = ((h.1 : G) * y * (h.1 : G)⁻¹) *
            ((h.1 : G) * z * (h.1 : G)⁻¹) := by group
        _ = cy.1 * cz.1 := by
          rw [conjF_val h.1 hfix yF, conjF_val h.1 hfix zF]
        _ = y * z := hprod
        _ = t := htyz.symm
    have hht : (h.1 : G) * t = t * (h.1 : G) :=
      mul_inv_eq_iff_eq_mul.mp (by simpa [mul_assoc] using hconjt)
    exact hht.symm
  let f : MulAction.stabilizer c.Hhat q → C := fun h =>
    ⟨(h : G), h.1.2, hstab_centralizes h⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : C => x.1) hab
  have hstab_le : Nat.card (MulAction.stabilizer c.Hhat q) ≤ 4 := by
    have hle := Nat.card_le_card_of_injective f hf
    rwa [hCcard] at hle
  let : Fintype ↥c.Hhat := Fintype.ofFinite _
  let : Fintype (MulAction.orbit c.Hhat q) := Fintype.ofFinite _
  let : Fintype (MulAction.stabilizer c.Hhat q) := Fintype.ofFinite _
  have horbit := MulAction.card_orbit_mul_card_stabilizer_eq_card_group c.Hhat q
  have horbit' : Nat.card (MulAction.orbit c.Hhat q) *
      Nat.card (MulAction.stabilizer c.Hhat q) = Nat.card c.Hhat := by
    simpa [Nat.card_eq_fintype_card] using horbit
  rw [firstCase_hhat_card_72 c d] at horbit'
  have hlower : 18 ≤ Nat.card (MulAction.orbit c.Hhat q) := by
    have hmul : Nat.card (MulAction.orbit c.Hhat q) *
        Nat.card (MulAction.stabilizer c.Hhat q) ≤
          Nat.card (MulAction.orbit c.Hhat q) * 4 :=
      Nat.mul_le_mul_left _ hstab_le
    rw [horbit'] at hmul
    omega
  have hsubset : MulAction.orbit c.Hhat q ⊆
      {x : G ⧸ c.Hhat | x ≠ cosetInvolution_base c.Hhat ∧
        Nat.card (cosetInvolution_fiber c.Hhat x) = 2} := by
    intro x hx
    rcases hx with ⟨h, rfl⟩
    exact ⟨smul_base_ne c.Hhat h.2 hq.1,
      (fiber_card_smul c.Hhat h.2 q).trans hq.2⟩
  have hupper : Nat.card (MulAction.orbit c.Hhat q) ≤ 18 := by
    rw [Nat.card_coe_set_eq]
    calc
      (MulAction.orbit c.Hhat q).ncard ≤
          {x : G ⧸ c.Hhat | x ≠ cosetInvolution_base c.Hhat ∧
            Nat.card (cosetInvolution_fiber c.Hhat x) = 2}.ncard :=
        Set.ncard_le_ncard hsubset
      _ = 18 := by
        change Nat.card {x : G ⧸ c.Hhat //
          x ≠ cosetInvolution_base c.Hhat ∧
            Nat.card (cosetInvolution_fiber c.Hhat x) = 2} = 18
        simpa only [firstCaseCosetLayer] using
          (firstCaseCosetLayer_card hmin c hfirst d).2.1
  omega

/-- The fibre-two layer is a single `Ĥ`-orbit. -/
public theorem firstCaseCosetLayer_two_orbit_eq
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    (q : G ⧸ c.Hhat)
    (hq : q ≠ cosetInvolution_base c.Hhat ∧
      Nat.card (cosetInvolution_fiber c.Hhat q) = 2) :
    MulAction.orbit c.Hhat q =
      {x : G ⧸ c.Hhat | x ≠ cosetInvolution_base c.Hhat ∧
        Nat.card (cosetInvolution_fiber c.Hhat x) = 2} := by
  classical
  have hsubset : MulAction.orbit c.Hhat q ⊆
      {x : G ⧸ c.Hhat | x ≠ cosetInvolution_base c.Hhat ∧
        Nat.card (cosetInvolution_fiber c.Hhat x) = 2} := by
    intro x hx
    rcases hx with ⟨h, rfl⟩
    exact ⟨smul_base_ne c.Hhat h.2 hq.1,
      (fiber_card_smul c.Hhat h.2 q).trans hq.2⟩
  have horbit : (MulAction.orbit c.Hhat q).ncard = 18 := by
    change Nat.card {x : G ⧸ c.Hhat // x ∈ MulAction.orbit c.Hhat q} = 18
    exact firstCaseCosetLayer_two_orbit_card hmin c hfirst d q hq
  have hlayer : ({x : G ⧸ c.Hhat | x ≠ cosetInvolution_base c.Hhat ∧
      Nat.card (cosetInvolution_fiber c.Hhat x) = 2} : Set (G ⧸ c.Hhat)).ncard = 18 := by
    change Nat.card {x : G ⧸ c.Hhat // x ≠ cosetInvolution_base c.Hhat ∧
      Nat.card (cosetInvolution_fiber c.Hhat x) = 2} = 18
    simpa [firstCaseCosetLayer] using
      (firstCaseCosetLayer_card hmin c hfirst d).2.1
  exact Set.eq_of_subset_of_ncard_le hsubset (by rw [hlayer, horbit])

end CFSG.GorensteinWalter

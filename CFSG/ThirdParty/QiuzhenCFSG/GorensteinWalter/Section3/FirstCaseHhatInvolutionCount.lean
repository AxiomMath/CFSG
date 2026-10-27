module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseBaseInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreFittingTI
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourFixedAutomorphism
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-! The incidence count for the involutions in `Ĥ`. -/

private theorem firstCase_card_sigma_partition
    {A : Type u} [Fintype A] (p : A → Prop) [DecidablePred p]
    (Q : A → Type u) [∀ a, Finite (Q a)]
    (n m : ℕ)
    (hp : ∀ a, p a → Nat.card (Q a) = n)
    (hm : ∀ a, ¬ p a → Nat.card (Q a) = m) :
    Nat.card (Sigma Q) =
      n * Nat.card {a : A // p a} + m * Nat.card {a : A // ¬ p a} := by
  let A1 : Type u := {a : A // p a}
  let A0 : Type u := {a : A // ¬ p a}
  let Q1 : A1 → Type u := fun a => Q a.1
  let Q0 : A0 → Type u := fun a => Q a.1
  let e : (Sigma Q1) ⊕ (Sigma Q0) ≃ Sigma Q :=
    { toFun := fun z => match z with
        | Sum.inl q => ⟨q.1, q.2⟩
        | Sum.inr q => ⟨q.1, q.2⟩
      invFun := fun q => if h : p q.1 then
        Sum.inl ⟨⟨q.1, h⟩, q.2⟩
      else Sum.inr ⟨⟨q.1, h⟩, q.2⟩
      left_inv := by
        intro z
        cases z with
        | inl q =>
          dsimp
          rw [dif_pos q.1.2]
        | inr q =>
          dsimp
          rw [dif_neg (by exact q.1.2)]
      right_inv := by
        intro q
        by_cases h : p q.1 <;> simp [h, A1, A0, Q1, Q0] }
  have hcard1 : Nat.card (Sigma Q1) = Fintype.card A1 * n := by
    rw [Nat.card_sigma]
    simp_rw [show ∀ a : A1, Nat.card (Q1 a) = n from
      fun a => hp a.1 a.2]
    simp
  have hcard0 : Nat.card (Sigma Q0) = Fintype.card A0 * m := by
    rw [Nat.card_sigma]
    simp_rw [show ∀ a : A0, Nat.card (Q0 a) = m from
      fun a => hm a.1 a.2]
    simp
  rw [← Nat.card_congr e, Nat.card_sum, hcard1, hcard0]
  dsimp [A1, A0] at hcard1 hcard0 ⊢
  simp [Nat.card_eq_fintype_card, Nat.mul_comm]

private theorem firstCase_klein_V_normal
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) :
    IsNormalIn (twoCoreOf c.Hhat) c.Hhat := by
  refine ⟨?_, ?_⟩
  · exact Subgroup.map_subtype_le (pCore 2 c.Hhat)
  · intro h hh x hx
    rcases Subgroup.mem_map.mp hx with ⟨x0, hx0, rfl⟩
    exact Subgroup.mem_map.mpr ⟨
      (⟨h, hh⟩ : c.Hhat) * x0 * (⟨h, hh⟩ : c.Hhat)⁻¹,
      (pCore_normal (p := 2) (G := c.Hhat)).conj_mem
        x0 hx0 (⟨h, hh⟩ : c.Hhat), by simp⟩

private theorem firstCase_klein_V_sq_one
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    {v : G} (hv : v ∈ twoCoreOf c.Hhat) :
    v * v = 1 := by
  have hV := firstCase_klein_V_klein c hklein
  simpa [pow_two] using
    congrArg Subtype.val (hV.mul_self (⟨v, hv⟩ : twoCoreOf c.Hhat))

private theorem firstCase_klein_V_involution
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    {v : G} (hv : v ∈ twoCoreOf c.Hhat) (hvne : v ≠ 1) :
    IsInvolution v := by
  exact ⟨hvne, by simpa [pow_two] using firstCase_klein_V_sq_one c hklein hv⟩

/- The centralizer of the Klein core inside `H` has no involution outside
`V`.  This is the only local Sylow-model argument in the incidence proof. -/
private theorem firstCase_klein_H_involution_centralizes_V_mem
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    {x : G} (hxH : x ∈ c.H) (hxI : IsInvolution x)
    (hcent : ∀ v : G, v ∈ twoCoreOf c.Hhat → v * x = x * v) :
    x ∈ twoCoreOf c.Hhat := by
  classical
  let V : Subgroup G := twoCoreOf c.Hhat
  have hVklein : IsKleinFour V := by
    simpa [V] using firstCase_klein_V_klein c hklein
  have hVleHhat : V ≤ c.Hhat := by
    dsimp [V, twoCoreOf]
    exact Subgroup.map_subtype_le (pCore 2 c.Hhat)
  have hVleS : V ≤ (c.S : Subgroup G) := by
    dsimp [V]
    rw [← (theorem_2_6 hmin c).2.1]
    exact inf_le_left
  have hS8 : Nat.card (c.S : Subgroup G) = 8 :=
    firstCase_klein_S_card hmin c hfirst hklein
  have hdecomp : ∃ s : G, s ∈ c.S ∧ ∃ u : G, u ∈ c.U ∧ s * u = x := by
    have hSU : (c.S : Subgroup G) ⊔ c.U = c.H :=
      fact_2_preamble_H_eq_SU hmin c
    have hUnorm : IsNormalIn c.U c.H := by
      change IsNormalIn (oddCoreOf c.H) c.H
      refine ⟨?_, ?_⟩
      · intro z hz
        rcases Subgroup.mem_map.mp hz with ⟨y, _hy, rfl⟩
        exact y.2
      · intro h hh z hz
        rcases Subgroup.mem_map.mp hz with ⟨y, hy, rfl⟩
        refine Subgroup.mem_map.mpr ⟨
          (⟨h, hh⟩ : c.H) * y * (⟨h, hh⟩ : c.H)⁻¹, ?_, by simp⟩
        exact (pPrimeCore_normal (p := 2) (G := c.H)).conj_mem
          y hy (⟨h, hh⟩ : c.H)
    have hSnormal : (c.S : Subgroup G) ≤
        Subgroup.normalizer (c.U : Set G) :=
      (centralizerSetup_S_le_H c).trans (le_normalizer_of_isNormalIn hUnorm)
    have hset : (c.H : Set G) = (c.S : Set G) * (c.U : Set G) := by
      rw [← hSU, Subgroup.coe_mul_of_left_le_normalizer_right c.S c.U hSnormal]
      rfl
    have hxprod : x ∈ (c.S : Set G) * (c.U : Set G) := by
      rw [← hset]
      exact hxH
    rcases Set.mem_mul.mp hxprod with ⟨s, hs, u, hu, hsu⟩
    exact ⟨s, hs, u, hu, hsu⟩
  obtain ⟨s, hsS, u, huU, hsu⟩ := hdecomp
  have hsI : IsInvolution s := by
    exact firstCase_product_involution_component hmin c hsS huU (by
      simpa [hsu] using hxI)
  have hscent : ∀ v : G, v ∈ V → v * s = s * v := by
    intro v hv
    have hvu : v * u = u * v := by
      have h26 := theorem_2_6 hmin c
      have hVc : V ≤ Subgroup.centralizer (c.U : Set G) := by
        simpa [V, h26.1] using twoCoreOf_centralizes_oddCoreOf c.Hhat
      exact (Subgroup.mem_centralizer_iff.mp (hVc hv) u huU).symm
    have hvx := hcent v hv
    have hvuC : Commute v u := hvu
    have hvu' : v * u⁻¹ = u⁻¹ * v := hvuC.inv_right.eq
    calc
      v * s = v * (x * u⁻¹) := by
        have hsx : s = x * u⁻¹ := by rw [← hsu]; group
        rw [hsx]
      _ = (v * x) * u⁻¹ := by rw [mul_assoc]
      _ = (x * v) * u⁻¹ := by rw [hvx]
      _ = x * (v * u⁻¹) := by group
      _ = x * (u⁻¹ * v) := by rw [hvu']
      _ = (x * u⁻¹) * v := by group
      _ = s * v := by
        have hsx : x * u⁻¹ = s := by rw [← hsu]; group
        rw [hsx]
  by_cases hsV : s ∈ V
  · have hsuC : Commute s u := by
      have h26 := theorem_2_6 hmin c
      have hVc : V ≤ Subgroup.centralizer (c.U : Set G) := by
        simpa [V, h26.1] using twoCoreOf_centralizes_oddCoreOf c.Hhat
      exact (Subgroup.mem_centralizer_iff.mp (hVc hsV) u huU).symm
    have huSq : u ^ 2 = 1 := by
      have hsSq : s * s = 1 := by simpa [pow_two] using hsI.2
      calc
        u ^ 2 = (s * s) * (u * u) := by simp [pow_two, hsSq]
        _ = s * (s * u) * u := by group
        _ = s * (u * s) * u := by rw [hsuC.eq]
        _ = s * u * s * u := by group
        _ = (s * u) ^ 2 := by rw [pow_two]; group
        _ = x ^ 2 := by rw [hsu]
        _ = 1 := hxI.2
    have hUcop : Nat.Coprime 2 (Nat.card c.U) := by
      have h26 := theorem_2_6 hmin c
      rw [h26.1]
      change Nat.Coprime 2 (Nat.card (oddCoreOf c.Hhat))
      rw [show Nat.card (oddCoreOf c.Hhat) = Nat.card (pPrimeCore 2 c.Hhat) by
        simpa [oddCoreOf] using
          (Subgroup.card_map_of_injective (K := pPrimeCore 2 c.Hhat)
            c.Hhat.subtype_injective)]
      exact pPrimeCore_coprime_card (p := 2) (G := c.Hhat)
    have hu1 : u = 1 := by
      by_cases hu1 : u = 1
      · exact hu1
      · exact firstCase_odd_subgroup_involution_eq_one c hUcop huU
          ⟨hu1, huSq⟩
    rw [← hsu, hu1]
    simpa using hsV
  ·
    have hZ : Nat.card (Subgroup.zpowers s) = 2 := by
      have hsord : orderOf s = 2 := orderOf_eq_prime
        (by simpa [pow_two] using hsI.2) hsI.1
      simpa [Nat.card_zpowers] using hsord
    have hdisj : Disjoint V (Subgroup.zpowers s) := by
      rw [Subgroup.disjoint_def]
      intro z hzV hzZ
      by_cases hz1 : z = 1
      · exact hz1
      have hzuniq : ∃! y, y ≠ (1 : Subgroup.zpowers s) :=
        (Nat.card_eq_two_iff' (1 : Subgroup.zpowers s)).mp hZ
      obtain ⟨y, hyne, hyuniq⟩ := hzuniq
      have hzneq : (⟨z, hzZ⟩ : Subgroup.zpowers s) ≠ 1 := by
        intro h
        exact hz1 (congrArg Subtype.val h)
      have hzs : (⟨z, hzZ⟩ : Subgroup.zpowers s) = y := hyuniq _ hzneq
      have hysne : (⟨s, Subgroup.mem_zpowers s⟩ : Subgroup.zpowers s) ≠ 1 := by
        intro h
        exact hsI.1 (congrArg Subtype.val h)
      have hys : (⟨s, Subgroup.mem_zpowers s⟩ : Subgroup.zpowers s) = y :=
        hyuniq _ hysne
      have hzEqS : z = s := by
        exact congrArg Subtype.val (hzs.trans hys.symm)
      exfalso
      exact hsV (hzEqS ▸ hzV)
    have hcross : ∀ v z : G, v ∈ V →
        z ∈ Subgroup.zpowers s → Commute v z := by
      intro v z hv hz
      rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, rfl⟩
      have hvs : Commute v s := hscent v hv
      exact hvs.zpow_right n
    have hdisj' : V ⊓ Subgroup.zpowers s = ⊥ := by
      apply le_antisymm
      · exact (disjoint_iff_inf_le.mp hdisj)
      · exact bot_le
    have hZabel : IsMulCommutative (↥(Subgroup.zpowers s)) := by
      refine ⟨⟨?_⟩⟩
      intro a b
      rcases Subgroup.mem_zpowers_iff.mp a.2 with ⟨n, hn⟩
      rcases Subgroup.mem_zpowers_iff.mp b.2 with ⟨m, hm⟩
      apply Subtype.ext
      change (a : G) * (b : G) = (b : G) * (a : G)
      rw [← hn, ← hm]
      exact (Commute.zpow_zpow_self s n m).eq
    have hjoinabel : IsMulCommutative (↥(V ⊔ Subgroup.zpowers s)) :=
      subgroup_sup_isMulCommutative_of_commute_of_disjoint V
        (Subgroup.zpowers s) hdisj' hcross hVklein.isMulCommutative hZabel
    have hjoin_le : V ⊔ Subgroup.zpowers s ≤ (c.S : Subgroup G) :=
      sup_le hVleS ((Subgroup.zpowers_le).2 hsS)
    have hjoin_card : Nat.card (↥(V ⊔ Subgroup.zpowers s)) = 8 := by
      let e := subgroup_sup_equiv_prod_of_commute_of_disjoint V
        (Subgroup.zpowers s) hdisj' hcross
      have hc := Nat.card_congr e.toEquiv
      rw [Nat.card_prod, hVklein.card_four, hZ] at hc
      norm_num at hc ⊢
      exact hc
    have hjoin_eq : (V ⊔ Subgroup.zpowers s : Subgroup G) = (c.S : Subgroup G) := by
      apply Subgroup.eq_of_le_of_card_ge hjoin_le
      rw [hS8, hjoin_card]
    have hScomm : IsMulCommutative (c.S : Subgroup G) := by
      rw [← hjoin_eq]
      exact hjoinabel
    have hmodel : IsMulCommutative (DihedralGroup 4) := by
      obtain ⟨e⟩ := c.dihedralEquiv
      have hm2 : c.m = 2 := by
        have hcard : Nat.card (c.S : Subgroup G) = 2 * 2 ^ c.m := by
          simpa using (Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card
        rw [hS8] at hcard
        have : 2 ^ c.m = 4 := by omega
        apply (Nat.pow_right_injective (a := 2) (by norm_num : 2 ≤ 2))
        simpa using this
      let e4 : (c.S : Subgroup G) ≃* DihedralGroup 4 := by
        have hpow : 2 ^ c.m = 4 := by rw [hm2]; norm_num
        rw [hpow] at e
        exact e
      refine ⟨⟨?_⟩⟩
      intro a b
      have hab := hScomm.is_comm.comm (e4.symm a) (e4.symm b)
      apply e4.symm.injective
      simpa using hab
    exact False.elim ((DihedralGroup.not_commutative (by norm_num) (by norm_num)) hmodel)

public theorem firstCase_klein_fixed_V_involution_card_one
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    {x : G} (hxHhat : x ∈ c.Hhat) (hxI : IsInvolution x)
    (hxnotV : x ∉ twoCoreOf c.Hhat) :
    Nat.card {v : G // IsInvolution v ∧ v ∈ twoCoreOf c.Hhat ∧
      Commute v x} = 1 := by
  classical
  let V : Subgroup G := twoCoreOf c.Hhat
  have hVklein : IsKleinFour V := by
    simpa [V] using firstCase_klein_V_klein c hklein
  have hVleHhat : V ≤ c.Hhat := by
    dsimp [V, twoCoreOf]
    exact Subgroup.map_subtype_le (pCore 2 c.Hhat)
  have hVnormal : IsNormalIn V c.Hhat := by
    simpa [V] using firstCase_klein_V_normal c
  have htV : c.t ∈ V := by
    dsimp [V]
    exact centralizerStructure_t_mem_twoCore c (theorem_2_6 hmin c)
  have htI : IsInvolution c.t := c.t_involution
  have hxnotcentral : ¬ (∀ v : G, v ∈ V → v * x = x * v) := by
    intro hcentral
    apply hxnotV
    have hxH : x ∈ c.H := by
      rw [c.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
      exact (hcentral c.t htV).symm
    exact firstCase_klein_H_involution_centralizes_V_mem hmin c hfirst hklein
      hxH hxI hcentral
  have hconjV : ∀ v : G, v ∈ V → x * v * x⁻¹ ∈ V := by
    intro v hv
    exact hVnormal.2 x hxHhat v hv
  have hxinv : x⁻¹ = x := by
    exact inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hxI.2)
  let tp : G := x * c.t * x⁻¹
  have htpV : tp ∈ V := by
    exact hconjV c.t htV
  have htpne : tp ≠ 1 := by
    intro h
    apply htI.1
    calc
      c.t = x⁻¹ * (x * c.t * x⁻¹) * x := by group
      _ = x⁻¹ * tp * x := by rfl
      _ = 1 := by rw [h]; simp
  have htpI : IsInvolution tp := by
    refine ⟨htpne, ?_⟩
    dsimp [tp]
    rw [pow_two]
    calc
      (x * c.t * x⁻¹) * (x * c.t * x⁻¹) =
          x * (c.t * c.t) * x⁻¹ := by group
      _ = 1 := by rw [← pow_two, htI.2]; simp
  have htpconj : x * tp * x⁻¹ = c.t := by
    dsimp [tp]
    calc
      x * (x * c.t * x⁻¹) * x⁻¹ =
          (x * x) * c.t * (x⁻¹ * x⁻¹) := by group
      _ = c.t := by
        have hxx : x * x = 1 := by simpa [pow_two] using hxI.2
        simp [hxx, hxinv]
  have hfixed_of_two : ∀ {a b : G},
      a ∈ V → b ∈ V → a ≠ 1 → b ≠ 1 → a ≠ b →
      a * x = x * a → b * x = x * b →
      ∀ z : G, z ∈ V → z * x = x * z := by
    intro a b ha hb ha1 hb1 hab hax hbx z hz
    let aV : V := ⟨a, ha⟩
    let bV : V := ⟨b, hb⟩
    let zV : V := ⟨z, hz⟩
    let : Fintype V := Fintype.ofFinite V
    have haV1 : aV ≠ 1 := by
      intro h
      exact ha1 (congrArg Subtype.val h)
    have hbV1 : bV ≠ 1 := by
      intro h
      exact hb1 (congrArg Subtype.val h)
    have habV : aV ≠ bV := by
      intro h
      exact hab (congrArg Subtype.val h)
    have hmem : zV ∈ ({aV * bV, aV, bV, (1 : V)} : Finset V) := by
      have huniv := hVklein.eq_finset_univ haV1 hbV1 habV
      rw [huniv]
      exact Finset.mem_univ zV
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with hprod | haeq | hbeq | h1
    · have hprod' : a * b * x = x * (a * b) := by
        calc
          a * b * x = a * (b * x) := by rw [mul_assoc]
          _ = a * (x * b) := by rw [hbx]
          _ = (a * x) * b := by rw [mul_assoc]
          _ = (x * a) * b := by rw [hax]
          _ = x * (a * b) := by group
      have hzEq : z = a * b := by
        exact congrArg Subtype.val hprod
      rw [hzEq]
      exact hprod'
    · have hzEq : z = a := congrArg Subtype.val haeq
      rw [hzEq]
      exact hax
    · have hzEq : z = b := congrArg Subtype.val hbeq
      rw [hzEq]
      exact hbx
    · have hzEq : z = 1 := congrArg Subtype.val h1
      rw [hzEq]
      simp
  have hex : ∃ v : G, IsInvolution v ∧ v ∈ V ∧ Commute v x := by
    by_cases hfix : tp = c.t
    · have htx : c.t * x = x * c.t := by
        have h' : x * c.t = c.t * x := by
          calc
            x * c.t = (x * c.t * x⁻¹) * x := by group
            _ = tp * x := by rfl
            _ = c.t * x := by rw [hfix]
        exact h'.symm
      exact ⟨c.t, htI, htV, htx⟩
    · let w : G := c.t * tp
      have hwV : w ∈ V := by
        dsimp [w]
        exact V.mul_mem htV htpV
      have htw : c.t * tp = tp * c.t := by
        exact congrArg Subtype.val
          (hVklein.isMulCommutative.is_comm.comm
            (⟨c.t, htV⟩ : V) (⟨tp, htpV⟩ : V))
      have hwne : w ≠ 1 := by
        intro h
        apply hfix
        have : tp = c.t := by
          calc
            tp = 1 * tp := by simp
            _ = (c.t * c.t) * tp := by
              have hct : c.t * c.t = 1 := by simpa [pow_two] using htI.2
              rw [hct]
            _ = c.t * (c.t * tp) := by group
            _ = c.t * w := by rfl
            _ = c.t := by simpa [h]
        exact this
      have hwI : IsInvolution w := by
        refine ⟨hwne, ?_⟩
        dsimp [w]
        rw [pow_two]
        calc
          (c.t * tp) * (c.t * tp) = c.t * (tp * c.t) * tp := by group
          _ = c.t * (c.t * tp) * tp := by rw [htw.symm]
          _ = c.t * c.t * (tp * tp) := by group
          _ = 1 := by rw [← pow_two, htI.2, ← pow_two, htpI.2]; simp
      have hwx : w * x = x * w := by
        have hconjW : x * w * x⁻¹ = w := by
          dsimp [w]
          calc
            x * (c.t * tp) * x⁻¹ =
                (x * c.t * x⁻¹) * (x * tp * x⁻¹) := by group
            _ = tp * c.t := by rw [show x * c.t * x⁻¹ = tp by rfl, htpconj]
            _ = c.t * tp := htw.symm
        have : x * w = w * x := by
          calc
            x * w = (x * w * x⁻¹) * x := by group
            _ = w * x := by rw [hconjW]
        exact this.symm
      exact ⟨w, hwI, hwV, hwx⟩
  obtain ⟨v0, hv0I, hv0V, hv0C⟩ := hex
  let y0 : {v : G // IsInvolution v ∧ v ∈ V ∧ Commute v x} :=
    ⟨v0, hv0I, hv0V, hv0C⟩
  apply (Nat.card_eq_one_iff_exists).2
  refine ⟨y0, ?_⟩
  intro z
  by_cases hEq : (z : G) = v0
  · exact Subtype.ext hEq
  exfalso
  apply hxnotcentral
  intro v hv
  exact hfixed_of_two (a := (z : G)) (b := v0)
    z.2.2.1 hv0V z.2.1.1 hv0I.1 hEq z.2.2.2.eq hv0C.eq v hv

public theorem firstCase_klein_commuting_fiber_card
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    {v : G} (hvI : IsInvolution v) (hvV : v ∈ twoCoreOf c.Hhat) :
    Nat.card {x : {x : G // IsInvolution x ∧ x ∈ c.Hhat} // Commute v x} =
      Nat.card {x : G // IsInvolution x ∧ x ∈ c.H} := by
  classical
  have hVne : twoCoreOf c.Hhat ≠ ⊥ := by
    intro hbot
    have hcard := (firstCase_klein_V_klein c hklein).card_four
    rw [hbot] at hcard
    simp at hcard
  have hUne : c.U ≠ ⊥ := (lemma_2_2 hmin c).2
  have hNorm : Subgroup.normalizer (c.U : Set G) = c.Hhat :=
    theorem26_normalizer_U_eq_Hhat hmin c hVne hUne
  have hVleS : twoCoreOf c.Hhat ≤ (c.S : Subgroup G) := by
    rw [← (theorem_2_6 hmin c).2.1]
    exact inf_le_left
  have hVcentU : twoCoreOf c.Hhat ≤
      Subgroup.centralizer (c.U : Set G) := by
    simpa [(theorem_2_6 hmin c).1] using
      twoCoreOf_centralizes_oddCoreOf c.Hhat
  have htV : c.t ∈ twoCoreOf c.Hhat :=
    centralizerStructure_t_mem_twoCore c (theorem_2_6 hmin c)
  have htC : c.t ∈ (c.S : Subgroup G) ⊓
      Subgroup.centralizer (c.U : Set G) := by
    exact ⟨hVleS htV, hVcentU htV⟩
  have hvC : v ∈ (c.S : Subgroup G) ⊓
      Subgroup.centralizer (c.U : Set G) :=
    ⟨hVleS hvV, hVcentU hvV⟩
  obtain ⟨g, hgHhat, hgv⟩ := theorem26_involutions_in_C_conjugate
    hmin c hNorm hvI c.t_involution hvC htC
  let A : Type u :=
    {x : {x : G // IsInvolution x ∧ x ∈ c.Hhat} // Commute v x}
  let B : Type u := {x : G // IsInvolution x ∧ x ∈ c.H}
  let f : A → B := fun z =>
    ⟨g * (z.1 : G) * g⁻¹, by
      have hzI : IsInvolution (g * (z.1 : G) * g⁻¹) := by
        refine ⟨?_, ?_⟩
        · intro h
          apply z.1.2.1.1
          calc
            (z.1 : G) = g⁻¹ * (g * (z.1 : G) * g⁻¹) * g := by group
            _ = 1 := by rw [h]; simp
        · rw [pow_two]
          calc
            (g * (z.1 : G) * g⁻¹) * (g * (z.1 : G) * g⁻¹) =
                g * ((z.1 : G) * (z.1 : G)) * g⁻¹ := by group
            _ = 1 := by rw [← pow_two, z.1.2.1.2]; simp
      refine ⟨hzI, ?_⟩
      rw [c.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
      have hcomm : Commute (g * v * g⁻¹) (g * (z.1 : G) * g⁻¹) :=
        (z.2).conj g
      simpa [hgv] using hcomm.eq.symm⟩
  let fInv : B → A := fun z =>
    ⟨⟨g⁻¹ * (z : G) * g, by
      refine ⟨?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · intro h
          apply z.2.1.1
          calc
            (z : G) = g * (g⁻¹ * (z : G) * g) * g⁻¹ := by group
            _ = 1 := by rw [h]; simp
        · rw [pow_two]
          calc
            (g⁻¹ * (z : G) * g) * (g⁻¹ * (z : G) * g) =
                g⁻¹ * ((z : G) * (z : G)) * g := by group
            _ = 1 := by rw [← pow_two, z.2.1.2]; simp
      · exact c.Hhat.mul_mem
          (c.Hhat.mul_mem (c.Hhat.inv_mem hgHhat) (c.H_le_Hhat z.2.2)) hgHhat⟩,
      by
        have hcomm : Commute (g⁻¹ * c.t * g) (g⁻¹ * (z : G) * g) := by
          have hzC : (z : G) * c.t = c.t * (z : G) := by
            simpa [c.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
              using z.2.2
          simpa [inv_inv] using (show Commute c.t (z : G) from hzC.symm).conj g⁻¹
        have hgv' : g⁻¹ * c.t * g = v := by
          calc
            g⁻¹ * c.t * g = g⁻¹ * (g * v * g⁻¹) * g := by rw [hgv]
            _ = v := by group
        simpa [hgv'] using hcomm⟩
  have hfInv : Function.LeftInverse fInv f := by
    intro z
    apply Subtype.ext
    dsimp [fInv, f]
    apply Subtype.ext
    change g⁻¹ * (g * (z.1 : G) * g⁻¹) * g = (z.1 : G)
    group
  have hfInv' : Function.RightInverse fInv f := by
    intro z
    apply Subtype.ext
    dsimp [fInv, f]
    change g * (g⁻¹ * (z : G) * g) * g⁻¹ = (z : G)
    group
  exact Nat.card_congr (Equiv.ofBijective f ⟨
    (fun a b h => by
      apply hfInv.injective
      rw [h]),
    (fun b => ⟨fInv b, hfInv' b⟩)⟩)

public theorem firstCase_klein_Hhat_involution_count_with_K
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat)) :
    ∃ K : Subgroup G, IsHallIn K c.FU ∧ K ≠ ⊥ ∧
      Nat.card {x : G // IsInvolution x ∧ x ∈ c.H} =
        3 + 2 * Nat.card K ∧
      Nat.card {x : G // IsInvolution x ∧ x ∈ c.Hhat} =
        3 + 6 * Nat.card K := by
  classical
  obtain ⟨K, hKHall, hKne, hHcount⟩ :=
    firstCase_klein_H_involution_count hmin c hfirst hklein
  let V : Subgroup G := twoCoreOf c.Hhat
  let W : Type u := {v : G // IsInvolution v ∧ v ∈ V}
  let JH : Type u := {x : G // IsInvolution x ∧ x ∈ c.Hhat}
  let Q : W → Type u := fun v =>
    {x : JH // Commute (v : G) (x : G)}
  let R : JH → Type u := fun x =>
    {v : W // Commute (v : G) (x : G)}
  let : Fintype W := Fintype.ofFinite W
  let : Fintype JH := Fintype.ofFinite JH
  have hVklein : IsKleinFour V := by
    simpa [V] using firstCase_klein_V_klein c hklein
  have hVleHhat : V ≤ c.Hhat := by
    dsimp [V, twoCoreOf]
    exact Subgroup.map_subtype_le (pCore 2 c.Hhat)
  have hWcard : Nat.card W = 3 := by
    simpa [W, V] using firstCase_klein_V_involution_count c hklein
  have hQcard : ∀ w : W, Nat.card (Q w) = 3 + 2 * Nat.card K := by
    intro w
    have hf := firstCase_klein_commuting_fiber_card hmin c hklein
      w.2.1 w.2.2
    calc
      Nat.card (Q w) =
          Nat.card {x : {x : G // IsInvolution x ∧ x ∈ c.Hhat} //
            Commute (w : G) x} := by
          rfl
      _ = Nat.card {x : G // IsInvolution x ∧ x ∈ c.H} := hf
      _ = 3 + 2 * Nat.card K := hHcount
  have hRcard_in : ∀ x : JH, (x : G) ∈ V → Nat.card (R x) = 3 := by
    intro x hx
    let e : R x ≃ W :=
      { toFun := fun z => z.1
        invFun := fun w =>
          ⟨w, by
            change (w : G) * (x : G) = (x : G) * (w : G)
            exact congrArg Subtype.val
              (hVklein.isMulCommutative.is_comm.comm
                (⟨w.1, w.2.2⟩ : V) (⟨x.1, hx⟩ : V))⟩
        left_inv := by intro z; rfl
        right_inv := by intro w; rfl }
    rw [Nat.card_congr e, hWcard]
  have hRcard_out : ∀ x : JH, (x : G) ∉ V → Nat.card (R x) = 1 := by
    intro x hx
    have hf := firstCase_klein_fixed_V_involution_card_one hmin c hfirst hklein
      x.2.2 x.2.1 hx
    let e : R x ≃
        {v : G // IsInvolution v ∧ v ∈ V ∧ Commute v (x : G)} :=
      { toFun := fun z =>
          ⟨z.1.1, z.1.2.1, z.1.2.2, z.2⟩
        invFun := fun z =>
          ⟨⟨z.1, z.2.1, z.2.2.1⟩, z.2.2.2⟩
        left_inv := by intro z; rfl
        right_inv := by intro z; rfl }
    rw [Nat.card_congr e, hf]
  let pJ : JH → Prop := fun x => (x : G) ∈ V
  have hSigmaPart :
      Nat.card (Sigma R) =
        3 * Nat.card {x : JH // pJ x} +
          Nat.card {x : JH // ¬ pJ x} := by
    simpa using firstCase_card_sigma_partition pJ R 3 1 hRcard_in hRcard_out
  let eSwap : (Sigma Q) ≃ (Sigma R) :=
    { toFun := fun z => ⟨z.2.1, ⟨z.1, z.2.2⟩⟩
      invFun := fun z => ⟨z.2.1, ⟨z.1, z.2.2⟩⟩
      left_inv := by intro z; rfl
      right_inv := by intro z; rfl }
  have hSigmaFirst :
      Nat.card (Sigma Q) =
        (3 + 2 * Nat.card K) * Nat.card W := by
    rw [Nat.card_sigma]
    simp_rw [hQcard]
    simp [Nat.mul_comm]
  have hSigmaEq :
      (3 + 2 * Nat.card K) * Nat.card W =
        3 * Nat.card {x : JH // pJ x} +
          Nat.card {x : JH // ¬ pJ x} := by
    calc
      (3 + 2 * Nat.card K) * Nat.card W = Nat.card (Sigma Q) :=
        hSigmaFirst.symm
      _ = Nat.card (Sigma R) := Nat.card_congr eSwap
      _ = 3 * Nat.card {x : JH // pJ x} +
          Nat.card {x : JH // ¬ pJ x} := hSigmaPart
  let JHin : Type u := {x : JH // pJ x}
  let JHout : Type u := {x : JH // ¬ pJ x}
  have hJHin : Nat.card JHin = 3 := by
    let e : JHin ≃ W :=
      { toFun := fun x => ⟨x.1, x.1.2.1, x.2⟩
        invFun := fun w =>
          ⟨⟨w.1, ⟨w.2.1, hVleHhat w.2.2⟩⟩, w.2.2⟩
        left_inv := by intro x; rfl
        right_inv := by intro w; rfl }
    rw [Nat.card_congr e, hWcard]
  let : Fintype JHin := Fintype.ofFinite JHin
  let : Fintype JHout := Fintype.ofFinite JHout
  have hJHsplit : Nat.card JH = 3 + Nat.card JHout := by
    have hcomp := Fintype.card_subtype_compl (α := JH) pJ
    have hle : Fintype.card JHin ≤ Fintype.card JH :=
      Fintype.card_subtype_le pJ
    have hJHin' : Fintype.card JHin = 3 := by
      simpa [Nat.card_eq_fintype_card] using hJHin
    have hJHsplit' : Fintype.card JH = 3 + Fintype.card JHout := by
      rw [hcomp, hJHin']
      omega
    simpa [Nat.card_eq_fintype_card] using hJHsplit'
  have hJHcard : Nat.card JH = 3 + 6 * Nat.card K := by
    have hEq :
        (3 + 2 * Nat.card K) * Nat.card W =
          3 * Nat.card JHin + Nat.card JHout := by
      simpa [JHin, JHout] using hSigmaEq
    rw [hWcard, hJHin] at hEq
    omega
  refine ⟨K, hKHall, hKne, hHcount, ?_⟩
  simpa [JH] using hJHcard

public theorem firstCase_klein_Hhat_involution_count
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat)) :
    ∃ K : Subgroup G, IsHallIn K c.FU ∧ K ≠ ⊥ ∧
      Nat.card {x : G // IsInvolution x ∧ x ∈ c.Hhat} =
        3 + 6 * Nat.card K := by
  rcases firstCase_klein_Hhat_involution_count_with_K hmin c hfirst hklein with
    ⟨K, hK, hKne, _hH, hHhat⟩
  exact ⟨K, hK, hKne, hHhat⟩

end CFSG.GorensteinWalter

module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseGlobalCommutingInvolutionCard
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseHhatInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinVUInvolution
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

private theorem dihedralThree_commuting_involutions_eq
    {a b : DihedralGroup 3}
    (ha : IsInvolution a) (hb : IsInvolution b)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : Commute a b) :
    a = b := by
  rcases dihedralGroup_cases a with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · have hi1 : (DihedralGroup.r i : DihedralGroup 3) ≠ 1 := by
      simpa using ha1
    have hpow : (DihedralGroup.r i : DihedralGroup 3) ^ 3 = 1 := by
      rw [pow_succ, pow_two, DihedralGroup.r_mul_r, DihedralGroup.r_mul_r]
      congr 1
      calc
        i + i + i = (3 : ZMod 3) * i := by ring
        _ = 0 := by rw [show (3 : ZMod 3) = 0 by decide, zero_mul]
    have hord : orderOf (DihedralGroup.r i : DihedralGroup 3) ∣ 3 :=
      orderOf_dvd_of_pow_eq_one hpow
    have hord2 : orderOf (DihedralGroup.r i : DihedralGroup 3) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using ha.2)
    have hord1 : orderOf (DihedralGroup.r i : DihedralGroup 3) = 1 := by
      have hd : orderOf (DihedralGroup.r i : DihedralGroup 3) ∣ Nat.gcd 2 3 :=
        Nat.dvd_gcd hord2 hord
      simpa using hd
    exact False.elim (hi1 (orderOf_eq_one_iff.mp hord1))
  · rcases dihedralGroup_cases b with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exfalso
      have hpow : (DihedralGroup.r j : DihedralGroup 3) ^ 3 = 1 := by
        rw [pow_succ, pow_two, DihedralGroup.r_mul_r, DihedralGroup.r_mul_r]
        congr 1
        calc
          j + j + j = (3 : ZMod 3) * j := by ring
          _ = 0 := by rw [show (3 : ZMod 3) = 0 by decide, zero_mul]
      have hord : orderOf (DihedralGroup.r j : DihedralGroup 3) ∣ 3 :=
        orderOf_dvd_of_pow_eq_one hpow
      have hord2 : orderOf (DihedralGroup.r j : DihedralGroup 3) ∣ 2 :=
        orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hb.2)
      have hord1 : orderOf (DihedralGroup.r j : DihedralGroup 3) = 1 := by
        have hd : orderOf (DihedralGroup.r j : DihedralGroup 3) ∣ Nat.gcd 2 3 :=
          Nat.dvd_gcd hord2 hord
        simpa using hd
      exact hb1 (orderOf_eq_one_iff.mp hord1)
    · have hcomm : DihedralGroup.sr i * DihedralGroup.sr j =
          DihedralGroup.sr j * DihedralGroup.sr i := hab.eq
      have hij : i - j = j - i := by
        exact DihedralGroup.r.inj (by simpa using hcomm.symm)
      have h2 : (2 : ZMod 3) * (i - j) = 0 := by
        calc
          (2 : ZMod 3) * (i - j) = (i - j) + (i - j) := by ring
          _ = (i - j) + (j - i) := by rw [hij]
          _ = 0 := by abel
      have h2ne : (2 : ZMod 3) ≠ 0 := by decide
      have hzero : i - j = 0 := (mul_eq_zero.mp h2).resolve_left h2ne
      exact congrArg DihedralGroup.sr (sub_eq_zero.mp hzero)

public theorem firstCase_klein_Hhat_outside_commuting_fiber_card_two
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    {s : G} (hsH : s ∈ c.Hhat) (hsI : IsInvolution s)
    (hsV : s ∉ twoCoreOf c.Hhat) :
    Nat.card {x : G // IsInvolution x ∧ x ∈ c.Hhat ∧
      x ∉ twoCoreOf c.Hhat ∧ Commute s x} = 2 := by
  classical
  let V : Subgroup G := twoCoreOf c.Hhat
  let H : Subgroup G := c.Hhat
  let N : Subgroup H := pCore 2 H ⊔ pPrimeCore 2 H
  let q : H →* (H ⧸ N) := QuotientGroup.mk' N
  obtain ⟨e⟩ := firstCase_klein_quotient_d6 hmin c hfirst hklein
  have hUeq : c.U = oddCoreOf c.Hhat := (theorem_2_6 hmin c).1
  have hmapN : N.map H.subtype = V ⊔ c.U := by
    dsimp [N, H, V]
    rw [Subgroup.map_sup]
    simp [twoCoreOf, oddCoreOf, hUeq]
  have hprod_mem_V {a b : G}
      (haH : a ∈ c.Hhat) (hbH : b ∈ c.Hhat)
      (haI : IsInvolution a) (hbI : IsInvolution b)
      (hab : Commute a b) (haV : a ∉ V) (hbV : b ∉ V) :
      a * b ∈ V := by
    let aH : H := ⟨a, haH⟩
    let bH : H := ⟨b, hbH⟩
    have haN : q aH ≠ 1 := by
      intro hqa
      have haN' : aH ∈ N := (QuotientGroup.eq_one_iff aH).mp hqa
      have haMap : a ∈ N.map H.subtype := Subgroup.mem_map.mpr ⟨aH, haN', rfl⟩
      have haVU : a ∈ V ⊔ c.U := hmapN ▸ haMap
      exact haV (firstCase_klein_involution_mem_twoCore_of_mem_VU
        hmin c hklein haVU haI)
    have hbN : q bH ≠ 1 := by
      intro hqb
      have hbN' : bH ∈ N := (QuotientGroup.eq_one_iff bH).mp hqb
      have hbMap : b ∈ N.map H.subtype := Subgroup.mem_map.mpr ⟨bH, hbN', rfl⟩
      have hbVU : b ∈ V ⊔ c.U := hmapN ▸ hbMap
      exact hbV (firstCase_klein_involution_mem_twoCore_of_mem_VU
        hmin c hklein hbVU hbI)
    have haqI : IsInvolution (q aH) := by
      refine ⟨haN, ?_⟩
      have hsq : aH * aH = (1 : H) := by
        apply Subtype.ext
        simpa [aH, pow_two] using haI.2
      simpa [pow_two] using congrArg q hsq
    have hbqI : IsInvolution (q bH) := by
      refine ⟨hbN, ?_⟩
      have hsq : bH * bH = (1 : H) := by
        apply Subtype.ext
        simpa [bH, pow_two] using hbI.2
      simpa [pow_two] using congrArg q hsq
    have habq : Commute (q aH) (q bH) := by
      have habH : Commute aH bH := by
        show aH * bH = bH * aH
        exact Subtype.ext hab.eq
      exact habH.map q
    have habq' : Commute (e (q aH)) (e (q bH)) := habq.map e
    have haqIe : IsInvolution (e (q aH)) := by
      refine ⟨?_, ?_⟩
      · intro h
        apply haqI.1
        apply e.injective
        simpa using h
      · simpa [pow_two] using congrArg e haqI.2
    have hbqIe : IsInvolution (e (q bH)) := by
      refine ⟨?_, ?_⟩
      · intro h
        apply hbqI.1
        apply e.injective
        simpa using h
      · simpa [pow_two] using congrArg e hbqI.2
    have haqIe1 : e (q aH) ≠ 1 := by
      intro h
      exact haqI.1 (by
        apply e.injective
        simpa using h)
    have hbqIe1 : e (q bH) ≠ 1 := by
      intro h
      exact hbqI.1 (by
        apply e.injective
        simpa using h)
    have heq : e (q aH) = e (q bH) :=
      dihedralThree_commuting_involutions_eq
        haqIe hbqIe haqIe1 hbqIe1 habq'
    have hqeq : q aH = q bH := e.injective heq
    have hqprod : q (aH * bH) = 1 := by
      rw [map_mul, hqeq]
      simpa [pow_two] using hbqI.2
    have hmemN : aH * bH ∈ N := (QuotientGroup.eq_one_iff _).mp hqprod
    have hmemMap : a * b ∈ N.map H.subtype :=
      Subgroup.mem_map.mpr ⟨aH * bH, hmemN, rfl⟩
    have hmemVU : a * b ∈ V ⊔ c.U := hmapN ▸ hmemMap
    by_cases hp : a * b = 1
    · rw [hp]
      exact V.one_mem
    · apply firstCase_klein_involution_mem_twoCore_of_mem_VU hmin c hklein hmemVU
      refine ⟨hp, ?_⟩
      rw [pow_two]
      calc
        (a * b) * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hab.eq]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [← pow_two, haI.2, ← pow_two, hbI.2]; simp
  let P : Type u := {x : G // IsInvolution x ∧ x ∈ c.Hhat ∧
    x ∉ V ∧ Commute s x}
  let C : Type u := {v : G // v ∈ V ∧ Commute s v}
  let f : P → C := fun x => ⟨s * (x : G), by
    refine ⟨hprod_mem_V hsH x.2.2.1 hsI x.2.1 x.2.2.2.2 hsV x.2.2.2.1, ?_⟩
    exact (Commute.refl s).mul_right x.2.2.2.2⟩
  let fInv : C → P := fun v => ⟨s * (v : G), by
    have hv2 : (v : G) * (v : G) = 1 := by
      simpa [pow_two] using congrArg Subtype.val
        ((firstCase_klein_V_klein c hklein).mul_self ⟨v, v.2.1⟩)
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · intro h
        apply hsV
        have hsEq : s = (s * (v : G)) * (v : G)⁻¹ := by group
        rw [hsEq]
        exact V.mul_mem (by simpa [h] using V.one_mem) (V.inv_mem v.2.1)
      · rw [pow_two]
        calc
          (s * (v : G)) * (s * (v : G)) = s * ((v : G) * s) * (v : G) := by group
          _ = s * (s * (v : G)) * (v : G) := by rw [v.2.2.eq]
          _ = (s * s) * ((v : G) * (v : G)) := by group
          _ = 1 := by rw [← pow_two, hsI.2, hv2]; simp
    · refine ⟨c.Hhat.mul_mem hsH (show (v : G) ∈ c.Hhat from
        (show V ≤ c.Hhat from by
          dsimp [V, twoCoreOf]
          exact Subgroup.map_subtype_le (pCore 2 c.Hhat)) v.2.1),
        ?_, ?_⟩
      · intro h
        apply hsV
        have hvH : (v : G) ∈ c.Hhat := by
          exact (show V ≤ c.Hhat from by
            dsimp [V, twoCoreOf]
            exact Subgroup.map_subtype_le (pCore 2 c.Hhat)) v.2.1
        have hv2' : (v : G)⁻¹ = (v : G) := inv_eq_of_mul_eq_one_right hv2
        have hsEq : s = (s * (v : G)) * (v : G)⁻¹ := by group
        rw [hsEq]
        exact V.mul_mem h (V.inv_mem v.2.1)
      · exact (Commute.refl s).mul_right v.2.2⟩
  have hfInv : Function.LeftInverse fInv f := by
    intro x
    have hss : s * s = 1 := by simpa [pow_two] using hsI.2
    apply Subtype.ext
    dsimp [fInv, f]
    calc
      s * (s * (x : G)) = (s * s) * (x : G) := by group
      _ = (x : G) := by rw [hss]; simp
  have hfInv' : Function.RightInverse fInv f := by
    intro v
    have hss : s * s = 1 := by simpa [pow_two] using hsI.2
    apply Subtype.ext
    dsimp [fInv, f]
    calc
      s * (s * (v : G)) = (s * s) * (v : G) := by group
      _ = (v : G) := by rw [hss]; simp
  have hPC : Nat.card P = Nat.card C := Nat.card_congr (Equiv.ofBijective f ⟨
    (fun a b h => hfInv.injective h), (fun b => ⟨fInv b, hfInv' b⟩)⟩)
  let T : Type u := {v : G // IsInvolution v ∧ v ∈ V ∧ Commute v s}
  have hTC : Nat.card T = 1 := by
    simpa [T, V] using firstCase_klein_fixed_V_involution_card_one
      hmin c hfirst hklein hsH hsI hsV
  have hCcard : Nat.card C = 2 := by
    let oneC : C := ⟨1, V.one_mem, by simp⟩
    obtain ⟨t0, ht0⟩ := (Nat.card_eq_one_iff_exists.mp (by simpa [T, V] using hTC))
    let tC : C := ⟨(t0 : G), t0.2.2.1, t0.2.2.2.symm⟩
    apply (Nat.card_eq_two_iff' oneC).2
    refine ⟨tC, ?_, ?_⟩
    · intro h
      have hval : (t0 : G) = 1 := congrArg Subtype.val h
      exact t0.2.1.1 hval
    · intro y hy
      by_cases hy1 : (y : G) = 1
      · exfalso
        apply hy
        apply Subtype.ext
        simpa [oneC] using hy1
      have hyI : IsInvolution (y : G) := by
        refine ⟨hy1, ?_⟩
        simpa [pow_two] using congrArg Subtype.val
          ((firstCase_klein_V_klein c hklein).mul_self ⟨y.1, y.2.1⟩)
      have yt : (⟨(y : G), hyI, y.2.1, y.2.2.symm⟩ : T) = t0 := ht0 _
      apply Subtype.ext
      simpa [tC] using congrArg Subtype.val yt
  change Nat.card P = 2
  rw [hPC, hCcard]

public theorem firstCase_klein_outside_commuting_involution_card_two_mul
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    {k : ℕ}
    (hHcount : Nat.card {x : G // IsInvolution x ∧ x ∈ c.H} = 3 + 2 * k)
    {s : G} (hsH : s ∈ c.Hhat) (hsI : IsInvolution s)
    (hsV : s ∉ twoCoreOf c.Hhat) :
    Nat.card {x : G // IsInvolution x ∧ x ∉ c.Hhat ∧ Commute s x} = 2 * k := by
  classical
  let V : Subgroup G := twoCoreOf c.Hhat
  let J : Type u := {x : G // IsInvolution x ∧ x ∈ c.Hhat ∧ Commute s x}
  let A : Type u := {x : J // (x : G) ∈ V}
  let B : Type u := {x : J // (x : G) ∉ V}
  let All : Type u := {x : G // IsInvolution x ∧ Commute s x}
  let Out : Type u := {x : All // (x : G) ∉ c.Hhat}
  have hA : Nat.card A = 1 := by
    let T : Type u := {v : G // IsInvolution v ∧ v ∈ V ∧ Commute v s}
    have hT : Nat.card T = 1 := by
      simpa [T, V] using firstCase_klein_fixed_V_involution_card_one
        hmin c hfirst hklein hsH hsI hsV
    let e : A ≃ T :=
      { toFun := fun x => ⟨(x.1 : G), ⟨x.1.2.1, x.2, x.1.2.2.2.symm⟩⟩
        invFun := fun x => ⟨⟨(x : G), ⟨x.2.1,
          (show V ≤ c.Hhat from by
            dsimp [V, twoCoreOf]
            exact Subgroup.map_subtype_le (pCore 2 c.Hhat)) x.2.2.1,
          x.2.2.2.symm⟩⟩, x.2.2.1⟩
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl }
    calc
      Nat.card A = Nat.card T := Nat.card_congr e
      _ = 1 := hT
  have hB : Nat.card B = 2 := by
    let e : B ≃ {x : G // IsInvolution x ∧ x ∈ c.Hhat ∧
        x ∉ V ∧ Commute s x} :=
      { toFun := fun x => ⟨x.1, x.1.2.1, x.1.2.2.1, x.2, x.1.2.2.2⟩
        invFun := fun x => ⟨⟨(x : G), ⟨x.2.1, x.2.2.1, x.2.2.2.2⟩⟩, x.2.2.2.1⟩
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl }
    calc
      Nat.card B = Nat.card {x : G // IsInvolution x ∧ x ∈ c.Hhat ∧
          x ∉ V ∧ Commute s x} := Nat.card_congr e
      _ = 2 := firstCase_klein_Hhat_outside_commuting_fiber_card_two
        hmin c hfirst hklein hsH hsI hsV
  have hJsplit : Nat.card J = Nat.card A + Nat.card B := by
    let : Fintype J := Fintype.ofFinite J
    let : Fintype A := Fintype.ofFinite A
    let : Fintype B := Fintype.ofFinite B
    have h := Fintype.card_subtype_compl (α := J) (p := fun x : J => (x : G) ∈ V)
    have h' : Nat.card B = Nat.card J - Nat.card A := by
      simpa only [Nat.card_eq_fintype_card] using h
    omega
  have hJcard : Nat.card J = 3 := by rw [hJsplit, hA, hB]
  have hAllJ : Nat.card All = Nat.card J + Nat.card Out := by
    let : Fintype All := Fintype.ofFinite All
    let : Fintype J := Fintype.ofFinite J
    let : Fintype Out := Fintype.ofFinite Out
    let eJ : J ≃ {x : All // (x : G) ∈ c.Hhat} :=
      { toFun := fun x =>
          let y : J := x
          ⟨⟨(y : G), ⟨y.2.1, y.2.2.2⟩⟩, y.2.2.1⟩
        invFun := fun x =>
          let y : All := x.1
          ⟨(y : G), ⟨y.2.1, x.2, y.2.2⟩⟩
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl }
    let eOut : Out ≃ {x : G // IsInvolution x ∧ x ∉ c.Hhat ∧ Commute s x} :=
      { toFun := fun x => ⟨x.1, x.1.2.1, x.2, x.1.2.2⟩
        invFun := fun x => ⟨⟨(x : G), ⟨x.2.1, x.2.2.2⟩⟩, x.2.2.1⟩
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl }
    have hcomp := Fintype.card_subtype_compl (α := All)
      (p := fun x : All => (x : G) ∈ c.Hhat)
    have hcompNat : Nat.card Out = Nat.card All -
        Nat.card {x : All // (x : G) ∈ c.Hhat} := by
      simpa only [Nat.card_eq_fintype_card] using hcomp
    have hJsub : Nat.card {x : All // (x : G) ∈ c.Hhat} = Nat.card J :=
      (Nat.card_congr eJ).symm
    have hle : Nat.card {x : All // (x : G) ∈ c.Hhat} ≤ Nat.card All := by
      exact Nat.card_le_card_of_injective (fun x => (x.1 : All)) (by
        intro a b h
        exact Subtype.ext h)
    rw [hJsub] at hcompNat
    omega
  have hAllcard : Nat.card All = 3 + 2 * k := by
    exact (firstCase_global_commuting_involution_card hmin c hsI).trans hHcount
  have hOutcard : Nat.card Out = 2 * k := by
    have hcomp := hAllJ
    rw [hJcard] at hcomp
    omega
  let eOut : Out ≃ {x : G // IsInvolution x ∧ x ∉ c.Hhat ∧ Commute s x} :=
    { toFun := fun x => ⟨(x.1 : G), x.1.2.1, x.2, x.1.2.2⟩
      invFun := fun x => ⟨⟨(x : G), ⟨x.2.1, x.2.2.2⟩⟩, x.2.2.1⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  exact (Nat.card_congr eOut).symm.trans hOutcard

public theorem firstCase_klein_external_commuting_pair_card
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    {k : ℕ}
    (hHcount : Nat.card {x : G // IsInvolution x ∧ x ∈ c.H} = 3 + 2 * k)
    (hHhatcount : Nat.card {x : G // IsInvolution x ∧ x ∈ c.Hhat} = 3 + 6 * k) :
    Nat.card (Sigma fun s : {s : G // IsInvolution s ∧ s ∈ c.Hhat ∧
        s ∉ twoCoreOf c.Hhat} =>
      {z : G // IsInvolution z ∧ z ∉ c.Hhat ∧ Commute (s : G) z}) =
      12 * k ^ 2 := by
  classical
  let V : Subgroup G := twoCoreOf c.Hhat
  let S : Type u := {s : G // IsInvolution s ∧ s ∈ c.Hhat ∧ s ∉ V}
  let Q : S → Type u := fun s =>
    {z : G // IsInvolution z ∧ z ∉ c.Hhat ∧ Commute (s : G) z}
  let T : Type u := {x : G // IsInvolution x ∧ x ∈ c.Hhat}
  let W : Type u := {x : G // IsInvolution x ∧ x ∈ V}
  have hW : Nat.card W = 3 := by
    simpa [W, V] using firstCase_klein_V_involution_count c hklein
  have hT : Nat.card T = 3 + 6 * k := by simpa [T] using hHhatcount
  have hS : Nat.card S = 6 * k := by
    have hsub : Nat.card {x : T // (x : G) ∈ V} = Nat.card W := by
      let e : {x : T // (x : G) ∈ V} ≃ W :=
        { toFun := fun x => ⟨(x.1 : G), ⟨x.1.2.1, x.2⟩⟩
          invFun := fun x => ⟨⟨(x : G), ⟨x.2.1,
            (show V ≤ c.Hhat from by
              dsimp [V, twoCoreOf]
              exact Subgroup.map_subtype_le (pCore 2 c.Hhat)) x.2.2⟩⟩, x.2.2⟩
          left_inv := by intro x; rfl
          right_inv := by intro x; rfl }
      exact Nat.card_congr e
    let : Fintype T := Fintype.ofFinite T
    let : Fintype S := Fintype.ofFinite S
    let : Fintype {x : T // (x : G) ∈ V} := Fintype.ofFinite _
    let : Fintype {x : T // (x : G) ∉ V} := Fintype.ofFinite _
    have hcomp := Fintype.card_subtype_compl (α := T)
      (p := fun x : T => (x : G) ∈ V)
    have hcompNat : Nat.card {x : T // (x : G) ∉ V} =
        Nat.card T - Nat.card {x : T // (x : G) ∈ V} := by
      simpa only [Nat.card_eq_fintype_card] using hcomp
    have hSsub : Nat.card {x : T // (x : G) ∉ V} = Nat.card S := by
      let e : {x : T // (x : G) ∉ V} ≃ S :=
        { toFun := fun x => ⟨(x.1 : G), ⟨x.1.2.1, x.1.2.2, x.2⟩⟩
          invFun := fun x => ⟨⟨(x : G), ⟨x.2.1, x.2.2.1⟩⟩, x.2.2.2⟩
          left_inv := by intro x; rfl
          right_inv := by intro x; rfl }
      exact Nat.card_congr e
    calc
      Nat.card S = Nat.card {x : T // (x : G) ∉ V} := hSsub.symm
      _ = Nat.card T - Nat.card {x : T // (x : G) ∈ V} := hcompNat
      _ = Nat.card T - Nat.card W := by rw [hsub]
      _ = 6 * k := by rw [hW, hT]; omega
  have hQ : ∀ s : S, Nat.card (Q s) = 2 * k := by
    intro s
    simpa [Q, S, V] using firstCase_klein_outside_commuting_involution_card_two_mul
      hmin c hfirst hklein hHcount s.2.2.1 s.2.1 s.2.2.2
  let : Fintype S := Fintype.ofFinite S
  calc
    Nat.card (Sigma Q) = ∑ s : S, Nat.card (Q s) := Nat.card_sigma
    _ = ∑ _s : S, 2 * k := by
      apply Finset.sum_congr rfl
      intro s _hs
      exact hQ s
    _ = Nat.card S * (2 * k) := by simp [Nat.card_eq_fintype_card]
    _ = 12 * k ^ 2 := by rw [hS]; ring

public theorem firstCase_klein_h8_of_coset_pair_distribution
    (k b2 b4 : ℕ)
    (hpair : 2 * (3 * b4 + b2) = 12 * k ^ 2) :
    3 * b4 + b2 = 6 * k ^ 2 := by omega

end CFSG.GorensteinWalter

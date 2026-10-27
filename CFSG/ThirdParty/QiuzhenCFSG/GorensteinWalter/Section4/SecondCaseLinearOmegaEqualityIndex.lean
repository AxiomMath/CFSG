module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationEightDefs
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddRelativeIndexBound
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PrimeOrderSubgroupIntersection
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27IndexTwo
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # The equality branch of the linear omega index argument -/

open scoped Pointwise

noncomputable section

namespace CFSG.GorensteinWalter

universe u

local instance {X : Type*} [Group X] : MulAction X (Subgroup X) :=
  MulAction.compHom (Subgroup X) (MulAut.conj : X →* MulAut X)

/-- An odd relative index bounded by `p + 1` (for odd `p`) is at most
`p`.  This is the oddness step of the equation-(8) bound: every relative
index in the odd-order group `U` is odd, and `p + 1` is even. -/
public theorem odd_relIndex_le_of_le_add_one
    {G : Type u} [Group G] [Finite G]
    (H U : Subgroup G) (hUodd : Odd (Nat.card U))
    {p : ℕ} (hpod : Odd p) (hle : H.relIndex U ≤ p + 1) :
    H.relIndex U ≤ p := by
  have hodd : Odd (H.relIndex U) :=
    Odd.of_dvd_nat hUodd (Subgroup.relIndex_dvd_card H U)
  rcases hpod with ⟨j, hj⟩
  rcases hodd with ⟨k, hk⟩
  rw [hk, hj] at hle
  omega

/-- The core equality-branch index estimate behind equation (8), generic
in the odd prime `p`.  The `U`-conjugates of the prime-order subgroup
`P` lie in the normal type-`(p,p)` subgroup `A` (`P ≤ A`, `A ⊴ U`), so
pairing each conjugate with its nonidentity elements injects into the
`p² - 1` nonidentity elements of `A`: the orbit of `P` under `U` has at
most `p + 1` elements.  The stabilizer is `U ∩ N_G(P)`, whose relative
index in `U` is therefore an odd number at most `p + 1`, hence at most
`p`; it equals `K ⊔ B`, which lies in `B ⊔ K ⊔ F(U)`. -/
public theorem linearOmega_equality_relIndex_core
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    {p : ℕ} (hp : p.Prime) (hpod : Odd p)
    (P A B K : Subgroup G)
    (hAcard : Nat.card A = p ^ 2)
    (hPcard : Nat.card P = p)
    (hPleA : P ≤ A)
    (hAnormalU : IsNormalIn A c.U)
    (hNP : c.U ⊓ Subgroup.normalizer (P : Set G) = K ⊔ B) :
    (B ⊔ K ⊔ c.FU).relIndex c.U ≤ p := by
  classical
  let U : Subgroup G := c.U
  let : MulAction U (Subgroup G) :=
    MulAction.compHom (Subgroup G) U.subtype
  have mem_smul_iff (x : U) (y : G) (T : Subgroup G) :
      y ∈ x • T ↔ (x : G)⁻¹ * y * (x : G) ∈ T := by
    change y ∈ T.map (MulAut.conj (x : G)).toMonoidHom ↔ _
    rw [Subgroup.mem_map_equiv]
    simp [MulAut.conj_symm_apply]
  let Orb := MulAction.orbit U P
  have hTcard : ∀ T : Orb, Nat.card T.1 = p := by
    intro T
    rcases T.2 with ⟨u, hu⟩
    have hcard : Nat.card ↥(u • P : Subgroup G) = Nat.card P := by
      change Nat.card (P.map (MulAut.conj (u : G)).toMonoidHom) =
        Nat.card P
      exact Subgroup.card_map_of_injective (MulAut.conj (u : G)).injective
    rw [← hu]
    exact hcard.trans hPcard
  have hTleA : ∀ T : Orb, T.1 ≤ A := by
    intro T
    rcases T.2 with ⟨u, hu⟩
    intro y hy
    have hySmul : y ∈ u • P := by
      change y ∈ (fun m : U => m • P) u
      rw [hu]
      exact hy
    have hpre : (u : G)⁻¹ * y * (u : G) ∈ P :=
      (mem_smul_iff u y P).mp hySmul
    have hpreA : (u : G)⁻¹ * y * (u : G) ∈ A := hPleA hpre
    have hconjA := hAnormalU.2 (u : G) u.2
      ((u : G)⁻¹ * y * (u : G)) hpreA
    simpa [mul_assoc] using hconjA
  let Pairs := Σ T : Orb, {x : T.1 // x ≠ 1}
  let target := {x : A // x ≠ 1}
  let f : Pairs → target := fun p =>
    ⟨⟨(p.2 : G), hTleA p.1 p.2.1.2⟩,
      by
        intro h1
        apply p.2.2
        apply Subtype.ext
        exact congrArg (fun z : A => (z : G)) h1⟩
  have hfInj : Function.Injective f := by
    rintro ⟨T, x⟩ ⟨S, y⟩ hxy
    have hvalG : (x : G) = (y : G) :=
      congrArg (fun z : target => ((z.1 : A) : G)) hxy
    have hyGne : (y : G) ≠ 1 := by
      intro h1
      apply y.2
      exact Subtype.ext h1
    have hxGne : (x : G) ≠ 1 := fun h1 =>
      hyGne (hvalG.symm.trans h1)
    have hxS : (x : G) ∈ S.1 := by
      rw [hvalG]
      exact y.1.2
    have hTS : T.1 = S.1 :=
      subgroup_eq_of_card_eq_prime_of_common_ne_one hp
        T.1 S.1 (hTcard T) (hTcard S) x.1.2 hxS hxGne
    have hOrbEq : T = S := Subtype.ext hTS
    subst S
    have hxy' : x = y := by
      apply Subtype.ext
      apply Subtype.ext
      exact hvalG
    rw [hxy']
  have htargetCard : Nat.card target = p ^ 2 - 1 := by
    let : Fintype A := Fintype.ofFinite A
    let : Fintype target := Fintype.ofFinite target
    have hAF : Fintype.card A = p ^ 2 := by
      simpa [Nat.card_eq_fintype_card] using hAcard
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    simp [hAF]
  have hpairCard : Nat.card Pairs = Nat.card Orb * (p - 1) := by
    let : Fintype Orb := Fintype.ofFinite Orb
    rw [Nat.card_sigma]
    have hfiber : ∀ T : Orb, Nat.card {x : T.1 // x ≠ 1} = p - 1 := by
      intro T
      let : Fintype T.1 := Fintype.ofFinite T.1
      let : Fintype {x : T.1 // x ≠ 1} := Fintype.ofFinite _
      have hTF : Fintype.card T.1 = p := by
        simpa [Nat.card_eq_fintype_card] using hTcard T
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
      simp [hTF]
    simp_rw [hfiber]
    simp [mul_comm]
  have hOrbLe : Nat.card Orb ≤ p + 1 := by
    have hpairsLe : Nat.card Pairs ≤ Nat.card target :=
      Nat.card_le_card_of_injective f hfInj
    rw [hpairCard, htargetCard] at hpairsLe
    have hp2 : p ^ 2 - 1 = (p + 1) * (p - 1) := by
      rw [← Nat.sq_sub_sq p 1]
    have hp1 : 0 < p - 1 := by
      have hple2 : 2 ≤ p := hp.two_le
      omega
    have hmul : Nat.card Orb * (p - 1) ≤ (p + 1) * (p - 1) := by
      simpa [hp2] using hpairsLe
    exact Nat.le_of_mul_le_mul_right hmul hp1
  let NU : Subgroup U :=
    (Subgroup.normalizer (P : Set G)).comap U.subtype
  have hstab : MulAction.stabilizer U P = NU := by
    ext u
    rw [MulAction.mem_stabilizer_iff]
    change u • P = P ↔
      (u : G) ∈ Subgroup.normalizer (P : Set G)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rfl
  have hOrbIndex : Nat.card Orb = NU.index := by
    calc
      Nat.card Orb = Nat.card (U ⧸ MulAction.stabilizer U P) :=
        Nat.card_congr (MulAction.orbitEquivQuotientStabilizer U P)
      _ = (MulAction.stabilizer U P).index :=
        (Subgroup.index_eq_card (MulAction.stabilizer U P)).symm
      _ = NU.index := by rw [hstab]
  have hNUindexLe : NU.index ≤ p + 1 := by
    rw [← hOrbIndex]
    exact hOrbLe
  let N : Subgroup G := U ⊓ Subgroup.normalizer (P : Set G)
  have hNsub : N.subgroupOf U = NU := by
    ext x
    simp [N, NU]
  have hNrel : N.relIndex U = NU.index := by
    change (N.subgroupOf U).index = NU.index
    rw [hNsub]
  have hUodd : Odd (Nat.card U) := by
    change Odd (Nat.card (oddCoreOf c.H))
    exact odd_card_oddCoreOf c.H
  have hNrelLe : N.relIndex U ≤ p := by
    apply odd_relIndex_le_of_le_add_one N U hUodd hpod
    rw [hNrel]
    exact hNUindexLe
  have hNleL : N ≤ B ⊔ K ⊔ c.FU := by
    intro x hx
    have hxKB : x ∈ K ⊔ B := by
      rw [← hNP]
      exact hx
    have hKBle : K ⊔ B ≤ B ⊔ K ⊔ c.FU :=
      sup_le
        ((le_sup_right : K ≤ B ⊔ K).trans
          (le_sup_left : B ⊔ K ≤ B ⊔ K ⊔ c.FU))
        ((le_sup_left : B ≤ B ⊔ K).trans
          (le_sup_left : B ⊔ K ≤ B ⊔ K ⊔ c.FU))
    exact hKBle hxKB
  have hNrelne : N.relIndex U ≠ 0 := by
    rw [hNrel]
    exact Nat.card_pos.ne'
  exact (Subgroup.relIndex_le_of_le_left hNleL hNrelne).trans hNrelLe

/-! ## The equality branch `A = Q` -/

/-- The equality branch of the linear equation-(8) trichotomy: when
`A = Q` (with `Q = Ω₁(Z₂(O_p(U)))` characteristic in `F(U)`), the
branch outputs needed by the equation-(8) constructor hold.  `A` is
normal in `F(U)` (indeed in `U`, being characteristic there), so
`N_U(A) = U`, `u = |U : N_U(A)| = 1`; and the index bound
`|U : B·K·F(U)| ≤ p` follows from the orbit of `P` under `U` combined
with `N_U(P) = U ∩ M = K·B` and the oddness of `p`. -/
public theorem secondCase_linear_omega_equality_index
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (od : SecondCaseLinearOmegaData c w d)
    (heq : od.A = od.Q.map c.U.subtype) :
    IsNormalIn od.A c.FU ∧
    (normalizerIn c.U od.A).relIndex c.U = 1 ∧
    (od.B ⊔ od.K ⊔ c.FU).relIndex c.U ≤ od.p := by
  classical
  have hAnormalU : IsNormalIn od.A c.U := by
    rw [heq]
    exact map_characteristic_isNormalIn_of_isNormalIn
      od.Q od.Q_characteristic
      ⟨le_rfl, by
        intro u hu x hx
        exact c.U.mul_mem (c.U.mul_mem hu hx) (c.U.inv_mem hu)⟩
  have hAneFU : IsNormalIn od.A c.FU := by
    refine ⟨od.A_le_FU, ?_⟩
    intro f hf a ha
    exact hAnormalU.2 f (fittingSubgroupOf_le c.U hf) a ha
  have hrelU : (normalizerIn c.U od.A).relIndex c.U = 1 := by
    rw [Subgroup.relIndex_eq_one]
    intro u hu
    exact ⟨hu, le_normalizer_of_isNormalIn hAnormalU hu⟩
  have hpod : Odd od.p := by
    have hFleFU : od.F ≤ c.FU := by
      intro x hx
      rw [od.F_fixed] at hx
      exact hx.1.1
    have hPleU : od.P ≤ c.U :=
      od.P_le_F.trans (hFleFU.trans (fittingSubgroupOf_le c.U))
    have hdvd : od.p ∣ Nat.card (↥c.U) := by
      rw [← od.P_card]
      exact Subgroup.card_dvd_of_le hPleU
    have hUodd : Odd (Nat.card (↥c.U)) := by
      change Odd (Nat.card (↥(oddCoreOf c.H)))
      exact odd_card_oddCoreOf c.H
    exact Odd.of_dvd_nat hUodd hdvd
  have hPleA : od.P ≤ od.A := by
    rw [od.A_eq]
    exact le_sup_left
  have hNP : c.U ⊓ Subgroup.normalizer (od.P : Set G) = od.K ⊔ od.B := by
    simpa [normalizerIn] using
      ((secondCase_linear_omega_NU_P_eq_U_inter_M c w d od).trans
        od.U_inter_M_eq.symm)
  have hrel : (od.B ⊔ od.K ⊔ c.FU).relIndex c.U ≤ od.p :=
    linearOmega_equality_relIndex_core c od.hp_prime hpod
      od.P od.A od.B od.K od.A_card od.P_card hPleA hAnormalU hNP
  exact ⟨hAneFU, hrelU, hrel⟩

end CFSG.GorensteinWalter

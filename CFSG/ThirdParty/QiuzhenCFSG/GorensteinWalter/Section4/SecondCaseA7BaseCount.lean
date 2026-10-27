module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7InvolutionsInComponent
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenInvolutionCountTransport
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 4: the A₇ base-coset involution count

The selected component has odd center and central quotient `A₇`.  The
centralizer of the distinguished involution therefore has index `105`, and
the internal fusion theorem identifies the involutions in the maximal
subgroup with the involutions in the component.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private abbrev A7 := alternatingGroup (Fin 7)

/-- In the A₇ branch, the base coset contains exactly `105` involutions. -/
public theorem secondCase_a7_base_involutions_card
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7) :
    Nat.card {x : G // IsInvolution x ∧ x ∈ w.M} = 105 := by
  classical
  let E := d.E
  let Z : Subgroup E := Subgroup.center E
  let q : E →* E ⧸ Z := QuotientGroup.mk' Z
  let tE : E := ⟨c.t, d.t_mem_E⟩
  let T : Subgroup E := Subgroup.zpowers tE
  have htE : IsInvolution tE := by
    constructor
    · intro h
      exact c.t_involution.1 (by simpa [tE] using congrArg Subtype.val h)
    · exact Subtype.ext c.t_involution.2
  have htord : orderOf tE = 2 := orderOf_eq_prime htE.2 htE.1
  have hTcard : Nat.card T = 2 := by
    simp [T, Nat.card_zpowers, htord]
  have hTp : IsPGroup 2 T := by
    apply IsPGroup.of_card (n := 1)
    simp [hTcard]
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (IsPGroup 2 T) := ⟨hTp⟩
  have hZodd : Odd (Nat.card Z) := d.center_odd
  have hZcop : Nat.Coprime 2 (Nat.card Z) := Nat.coprime_two_left.mpr hZodd
  have hTsingle : Subgroup.centralizer (T : Set E) =
      Subgroup.centralizer ({tE} : Set E) := by
    dsimp [T]
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hqT : T.map q = Subgroup.zpowers (q tE) := by
    simpa [T] using MonoidHom.map_zpowers q tE
  have hTqsingle : Subgroup.centralizer
      ((Subgroup.zpowers (q tE) : Subgroup (E ⧸ Z)) : Set (E ⧸ Z)) =
      Subgroup.centralizer ({q tE} : Set (E ⧸ Z)) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  let C : Subgroup E := Subgroup.centralizer ({tE} : Set E)
  let Cq : Subgroup (E ⧸ Z) := Subgroup.centralizer ({q tE} : Set (E ⧸ Z))
  have hcm' : Subgroup.centralizer
      ((T.map q : Subgroup (E ⧸ Z)) : Set (E ⧸ Z)) = C.map q := by
    have hh := centralizer_map_quotient_eq_map_centralizer
      (G := E) (p := 2) T Z (by infer_instance) hZcop
    rw [hTsingle] at hh
    simpa [q, C] using hh
  have hCmap : Cq = C.map q := by
    rw [hqT] at hcm'
    rw [hTqsingle] at hcm'
    exact hcm'
  have hZleC : Z ≤ C := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : y = tE := by simpa using hy
    subst y
    exact (Subgroup.mem_center_iff.mp hz) tE
  have hmapidx := Subgroup.index_map C q
  have hker : q.ker = Z := by simpa [q] using QuotientGroup.ker_mk' Z
  have hqrange : q.range = ⊤ := QuotientGroup.range_mk' Z
  have hCqidx : Cq.index = C.index := by
    have hmapidx' : Cq.index = (C ⊔ q.ker).index * q.range.index := by
      simpa [hCmap] using hmapidx
    rw [hker, hqrange, sup_eq_left.mpr hZleC, Subgroup.index_top, mul_one] at hmapidx'
    exact hmapidx'
  let eQ : (E ⧸ Z) ≃* A7 := hA7.some
  let qtA : A7 := eQ (q tE)
  have hqt_ne : q tE ≠ 1 := by
    intro hq1
    have htZ : tE ∈ Z :=
      (QuotientGroup.eq_one_iff (N := Z) tE).mp hq1
    have h2dvd : 2 ∣ Nat.card Z := by
      rw [← htord]
      exact Subgroup.orderOf_dvd_natCard Z htZ
    exact hZodd.not_two_dvd_nat h2dvd
  have hqtA : IsInvolution qtA := by
    constructor
    · intro h
      apply hqt_ne
      apply eQ.injective
      simpa [qtA] using h
    · have hh := congrArg q htE.2
      have hh2 := congrArg eQ hh
      simpa [qtA, map_pow] using hh2
  have hfuseA : ∀ x : A7, IsInvolution x →
      ∃ g : A7, g * x * g⁻¹ = qtA := by
    intro x hx
    obtain ⟨g, hg⟩ := aSeven_involutions_conjugate x qtA hx hqtA
    exact ⟨g, hg⟩
  have hidxA : (Subgroup.centralizer ({qtA} : Set A7)).index = 105 := by
    have hcount := involutions_card_eq_centralizer_index_of_fusion qtA hqtA hfuseA
    rw [aSeven_involutions_card] at hcount
    exact hcount.symm
  have hcentEq : (Cq.map eQ.toMonoidHom) =
      Subgroup.centralizer ({qtA} : Set A7) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change y ∈ Subgroup.centralizer ({q tE} : Set (E ⧸ Z)) at hy
      have hy' : y * q tE = q tE * y :=
        (Subgroup.mem_centralizer_singleton_iff.mp hy)
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      simpa [qtA] using congrArg eQ hy'
    · intro hx
      change x ∈ Subgroup.centralizer ({qtA} : Set A7) at hx
      have hx' : x * qtA = qtA * x :=
        (Subgroup.mem_centralizer_singleton_iff.mp hx)
      refine Subgroup.mem_map.mpr ⟨eQ.symm x, ?_, ?_⟩
      · apply Subgroup.mem_centralizer_singleton_iff.mpr
        apply eQ.injective
        simpa [qtA] using hx'
      · simp
  have hidxQ : Cq.index = 105 := by
    calc
      Cq.index = (Cq.map eQ.toMonoidHom).index :=
        (Subgroup.index_map_equiv Cq eQ).symm
      _ = (Subgroup.centralizer ({qtA} : Set A7)).index := by rw [hcentEq]
      _ = 105 := hidxA
  have hCidx : C.index = 105 := by exact hCqidx.symm.trans hidxQ
  have hcomp := secondCase_component_involutions_card_eq_centralizer_index c w d
  have hcomp' : Nat.card {x : G // IsInvolution x ∧ x ∈ E} = 105 := by
    rw [hcomp, hCidx]
  have hMtoE : ∀ x : G, x ∈ w.M → IsInvolution x → x ∈ E :=
    secondCase_a7_involutions_in_component hmin c w d hA7 hmodel
  let f : {x : G // IsInvolution x ∧ x ∈ w.M} ≃
      {x : G // IsInvolution x ∧ x ∈ E} :=
    { toFun := fun x => ⟨x.1, x.2.1, hMtoE x.1 x.2.2 x.2.1⟩
      invFun := fun x => ⟨x.1, x.2.1, d.E_component.1 x.2.2⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  exact (Nat.card_congr f).trans hcomp'

/-- The global single-class involution count, once the source's index relation
`[G : H] = 35 [G : M]` has been established. -/
public theorem secondCase_total_involutions_card_of_H_index
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (M : Subgroup G)
    (hindex : c.H.index = 35 * M.index) :
    Nat.card {x : G // IsInvolution x} = 35 * M.index := by
  have hcount := involutions_card_eq_centralizer_index_of_fusion
    c.t c.t_involution (fun x hx =>
      fact_2_preamble_involutions_conjugate_proved hmin x c.t hx c.t_involution)
  rw [← c.H_eq_centralizer] at hcount
  rw [hindex] at hcount
  exact hcount

end CFSG.GorensteinWalter

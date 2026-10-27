module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Hall.corollary_14_4_2

namespace CFSG
end CFSG
open CFSG

/-!
# Hall-Wielandt theorem

Book-order external theorem interface for Hall's Theorem 14.4.2, the
Hall-Wielandt theorem used in Peterfalvi, Part II, Chapter II.

Source guide: `docs/PFpart2/ref/PFpart2_external_formalization_guides.md`,
item `NearFieldHallWielandtPackage`; Hall, *The Theory of Groups*, Section
14.4, Theorem 14.4.2.
-/

namespace CFSG.BenderSuzuki
namespace External

open PFchapter1section1 PFAppendixIII
open PFchapter2

universe u

/-- If `z` lies in the `(p-1)`st upper central term, then every Hall Engel
symbol `e_p(u,z)` is trivial. This is the condition (3) to condition (1)
commutator calculation in Hall-Wielandt. -/
public theorem hallWielandt_engel_of_mem_upperCentralSeries
    {R : Type u} [Group R] (p : ℕ) [Fact p.Prime] {z : R}
    (hz : z ∈ Subgroup.upperCentralSeries R (p - 1)) :
    ∀ u : R, engelSymbol p u z = 1 := by
  have hiter_succ : ∀ (n : ℕ) (a b : R),
      iteratedInverseFirstCommutator (n + 1) a b =
        iteratedInverseFirstCommutator n (inverseFirstCommutator a b) b := by
    intro n
    induction n with
    | zero => intro a b; rfl
    | succ n ih =>
        intro a b
        change inverseFirstCommutator (iteratedInverseFirstCommutator (n + 1) a b) b =
          iteratedInverseFirstCommutator (n + 1) (inverseFirstCommutator a b) b
        rw [ih a b]
        rfl
  have hleft_desc : ∀ (n : ℕ) {x z : R},
      x ∈ Subgroup.upperCentralSeries R n → iteratedInverseFirstCommutator n x z = 1 := by
    intro n
    induction n with
    | zero =>
        intro x z hx
        simpa [iteratedInverseFirstCommutator, Subgroup.upperCentralSeries_zero] using hx
    | succ n ih =>
        intro x z hx
        have hxstep : inverseFirstCommutator x z ∈ Subgroup.upperCentralSeries R n := by
          have hxinv : x⁻¹ ∈ Subgroup.upperCentralSeries R (n + 1) :=
            (Subgroup.upperCentralSeries R (n + 1)).inv_mem hx
          simpa [inverseFirstCommutator, commutatorElement_def] using
            (Subgroup.mem_upperCentralSeries_succ_iff (G := R) (n := n) (x := x⁻¹)).1 hxinv z⁻¹
        rw [hiter_succ n x z]
        exact ih hxstep
  intro u
  have hp_two : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have hpred : p - 2 + 1 = p - 1 := by omega
  have hfirst : inverseFirstCommutator u z ∈ Subgroup.upperCentralSeries R (p - 2) := by
    have hzinv : z⁻¹ ∈ Subgroup.upperCentralSeries R (p - 1) :=
      (Subgroup.upperCentralSeries R (p - 1)).inv_mem hz
    rw [← hpred] at hzinv
    have hreverse : inverseFirstCommutator z u ∈ Subgroup.upperCentralSeries R (p - 2) := by
      simpa [inverseFirstCommutator, commutatorElement_def] using
        (Subgroup.mem_upperCentralSeries_succ_iff (G := R) (n := p - 2) (x := z⁻¹)).1 hzinv u⁻¹
    simpa [inverseFirstCommutator, mul_assoc] using
      (Subgroup.upperCentralSeries R (p - 2)).inv_mem hreverse
  unfold engelSymbol
  have hp_sub : p - 1 = p - 2 + 1 := hpred.symm
  rw [hp_sub, hiter_succ (p - 2) u z]
  exact hleft_desc (p - 2) hfirst

/-- Iterated inverse-first commutators commute with the subtype map of a
subgroup. -/
public theorem iteratedInverseFirstCommutator_subtype_coe
    {G : Type u} [Group G] (P : Subgroup G) (n : ℕ) (u z : P) :
    ((iteratedInverseFirstCommutator n u z : P) : G) =
      iteratedInverseFirstCommutator n (u : G) (z : G) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change ((inverseFirstCommutator (iteratedInverseFirstCommutator n u z) z : P) : G) =
        inverseFirstCommutator (iteratedInverseFirstCommutator n (u : G) (z : G)) (z : G)
      simp [inverseFirstCommutator, ih]

/-- Hall's Engel symbol commutes with the subtype map of a subgroup. -/
public theorem engelSymbol_subtype_coe
    {G : Type u} [Group G] (P : Subgroup G) (p : ℕ) (u z : P) :
    ((engelSymbol p u z : P) : G) = engelSymbol p (u : G) (z : G) := by
  simp [engelSymbol, iteratedInverseFirstCommutator_subtype_coe]

/-- Hall-Wielandt condition (3) implies condition (1): if `Q` lies in the
`(p-1)`st upper central series term of `P`, then `e_p(u,z)=1` for `u ∈ P` and
`z ∈ Q`. -/
public theorem hallWielandt_engel_condition_three_implies_first
    {G : Type u} [Group G] (p : ℕ) [Fact p.Prime]
    (P Q : Subgroup G) (hQ_le_P : Q ≤ P)
    (h3 : Q.subgroupOf P ≤ Subgroup.upperCentralSeries P (p - 1)) :
    ∀ u z : G, u ∈ P → z ∈ Q → engelSymbol p u z = 1 := by
  intro u z hu hz
  let up : P := ⟨u, hu⟩
  let zp : P := ⟨z, hQ_le_P hz⟩
  have hzP : zp ∈ Subgroup.upperCentralSeries P (p - 1) := h3 hz
  have hP : engelSymbol p up zp = 1 :=
    hallWielandt_engel_of_mem_upperCentralSeries (R := P) p hzP up
  have hcoe := congrArg Subtype.val hP
  simpa [engelSymbol_subtype_coe, up, zp] using hcoe
/-- Hall-Wielandt condition (2) implies condition (1): if `Q` is normal in
`P` and `e_{p-1}(u,z)=1` for `u,z ∈ Q`, then `e_p(u,z)=1` for `u ∈ P` and
`z ∈ Q`. -/
public theorem hallWielandt_engel_condition_two_implies_first
    {G : Type u} [Group G] (p : ℕ) [Fact p.Prime]
    (P Q : Subgroup G) (hQ_le_P : Q ≤ P)
    (hQnorm : (Q.subgroupOf P).Normal)
    (h2 : ∀ u z : G, u ∈ Q → z ∈ Q → engelSymbol (p - 1) u z = 1) :
    ∀ u z : G, u ∈ P → z ∈ Q → engelSymbol p u z = 1 := by
  intro u z hu hz
  have hcomm_mem_Q : inverseFirstCommutator u z ∈ Q := by
    let up : P := ⟨u, hu⟩
    let zp : P := ⟨z, hQ_le_P hz⟩
    have hz_sub : zp ∈ Q.subgroupOf P := hz
    have hconj : up⁻¹ * zp⁻¹ * up ∈ Q.subgroupOf P := by
      simpa [up, zp, mul_assoc] using
        hQnorm.conj_mem' (zp⁻¹) ((Q.subgroupOf P).inv_mem hz_sub) up
    have hz_sub' : zp ∈ Q.subgroupOf P := hz
    have hprod : up⁻¹ * zp⁻¹ * up * zp ∈ Q.subgroupOf P :=
      (Q.subgroupOf P).mul_mem hconj hz_sub'
    have hprod' : ((up⁻¹ * zp⁻¹ * up * zp : P) : G) ∈ Q :=
      Subgroup.mem_subgroupOf.mp hprod
    change inverseFirstCommutator u z ∈ Q
    simpa [inverseFirstCommutator, up, zp, mul_assoc] using hprod'
  have hiter_succ : ∀ (n : ℕ) (a b : G),
      iteratedInverseFirstCommutator (n + 1) a b =
        iteratedInverseFirstCommutator n (inverseFirstCommutator a b) b := by
    intro n
    induction n with
    | zero => intro a b; rfl
    | succ n ih =>
        intro a b
        change inverseFirstCommutator (iteratedInverseFirstCommutator (n + 1) a b) b =
          iteratedInverseFirstCommutator (n + 1) (inverseFirstCommutator a b) b
        rw [ih a b]
        rfl
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  have hp_sub_succ : p - 1 + 1 = p := Nat.sub_add_cancel hp_pos
  have hrewrite : engelSymbol p u z = engelSymbol (p - 1) (inverseFirstCommutator u z) z := by
    unfold engelSymbol
    rw [← hp_sub_succ]
    cases p with
    | zero => cases hp_pos
    | succ p' =>
        have hp_two : 2 ≤ p' + 1 := (Fact.out : Nat.Prime (p' + 1)).two_le
        cases p' with
        | zero => omega
        | succ q => simpa using hiter_succ q u z
  rw [hrewrite]
  exact h2 (inverseFirstCommutator u z) z hcomm_mem_Q hz
/--
Hall-Wielandt theorem, Hall Theorem 14.4.2. If `P` is a Sylow `p`-subgroup of
`G`, `Q` is weakly closed in `P`, and `H=N_G(Q)`, then any of the three
displayed Hall conditions gives `u_p(H)=H∩u_p(G)` and the quotient isomorphism
`G/u_p(G) ≃ H/u_p(H)`.
-/
public theorem hallWielandt_residual_intersection
    {G : Type u} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (P : Sylow p G) (Q H : Subgroup G)
    (hH : H = Subgroup.normalizer (Q : Set G))
    (hweak : WeaklyClosedIn (P : Subgroup G) Q)
    (hcondition :
      (∀ u z : G, u ∈ (P : Subgroup G) → z ∈ Q → engelSymbol p u z = 1) ∨
        (∀ u z : G, u ∈ Q → z ∈ Q → engelSymbol (p - 1) u z = 1) ∨
          Q.subgroupOf (P : Subgroup G) ≤
            Subgroup.upperCentralSeries (P : Subgroup G) (p - 1)) :
    (hallPResidual p H).map H.subtype = H ⊓ hallPResidual p G ∧
      letI : (hallPResidual p G).Normal := hallPResidual_normal p G
      letI : (hallPResidual p H).Normal := hallPResidual_normal p H
      Nonempty ((G ⧸ hallPResidual p G) ≃* (H ⧸ hallPResidual p H)) := by
  classical
  have hengel :
      ∀ u z : G, u ∈ (P : Subgroup G) → z ∈ Q →
        engelSymbol p u z = 1 := by
    rcases hcondition with h1 | h23
    · exact h1
    · rcases h23 with h2 | h3
      · exact hallWielandt_engel_condition_two_implies_first
          p (P : Subgroup G) Q hweak.1
            (weaklyClosedIn_subgroupOf_normal hweak) h2
      · exact hallWielandt_engel_condition_three_implies_first
          p (P : Subgroup G) Q hweak.1 h3
  have hN_le_H :
      Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ H := by
    rw [hH]
    exact weaklyClosedIn_normalizer_le_normalizer hweak
  let N : Subgroup G :=
    Subgroup.normalizer ((P : Subgroup G) : Set G)
  let G₀ : Subgroup G := hallPResidual p G
  let Hcap : Subgroup G := G₀ ⊓ H
  let Pcap : Subgroup G := G₀ ⊓ (P : Subgroup G)
  have hHall := hall_theorem_14_4_1_p_hall_of_weakly_closed
    (G := G) p P Q N H G₀ Hcap Pcap rfl
      (by simpa [N] using hN_le_H) hH hweak rfl rfl rfl
  have hres_le : (hallPResidual p Hcap).map Hcap.subtype ≤ Hcap :=
    Subgroup.map_subtype_le _
  have hres_eq : (hallPResidual p Hcap).map Hcap.subtype = Hcap := by
    rcases eq_or_lt_of_le hres_le with heq | hlt
    · exact heq
    · have hmod_lt : hallTransferModulus p Hcap H < Hcap :=
        hallTransferModulus_proper_of_residual_lt
          p H G₀ Hcap rfl rfl hlt
      obtain ⟨Zs, hZs, E, hE, hgenerated⟩ := hHall.2 hlt
      have hE_le : E ⊆ hallTransferModulus p Hcap H := by
        intro x hx
        obtain ⟨u, z, c, hu, hz, _hc, _hxH, rfl⟩ := hE x hx
        have huP : u ∈ (P : Subgroup G) := hu.2
        have hzQ : z ∈ Q := hZs z hz
        have heng : engelSymbol p u z = 1 := hengel u z huP hzQ
        simp [heng]
      have hclosure :
          Subgroup.closure E ≤ hallTransferModulus p Hcap H :=
        (Subgroup.closure_le _).2 hE_le
      have hHcap_le : Hcap ≤ hallTransferModulus p Hcap H :=
        hgenerated.trans (sup_le le_rfl hclosure)
      exact (not_le_of_gt hmod_lt hHcap_le).elim
  have hres :
      (hallPResidual p H).map H.subtype =
        H ⊓ hallPResidual p G := by
    calc
      (hallPResidual p H).map H.subtype =
          (hallPResidual p Hcap).map Hcap.subtype := hHall.1
      _ = Hcap := hres_eq
      _ = H ⊓ hallPResidual p G := by
        simp [Hcap, G₀, inf_comm]
  refine ⟨hres, ?_⟩
  letI : (hallPResidual p G).Normal := hallPResidual_normal p G
  letI : (hallPResidual p H).Normal := hallPResidual_normal p H
  have hP_le_H : (P : Subgroup G) ≤ H :=
    Subgroup.le_normalizer.trans hN_le_H
  have hsup : H ⊔ hallPResidual p G = ⊤ :=
    hall_sup_hallPResidual_eq_top_of_sylow_le
      (G := G) p P H hP_le_H
  have hres' :
      (hallPResidual p H).map H.subtype =
        hallPResidual p G ⊓ H := by
    simpa [inf_comm] using hres
  exact hallQuotientIsoOfMapResidualEq
    (G := G) (K := hallPResidual p G)
      (H := H) (L := hallPResidual p H) hres' hsup

end External
end CFSG.BenderSuzuki


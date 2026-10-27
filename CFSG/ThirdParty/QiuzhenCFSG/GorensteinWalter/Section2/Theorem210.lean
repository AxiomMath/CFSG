module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import Mathlib.Algebra.Group.Defs
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ReflectionQCoreCentralizerOddCore
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27Infra
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27IndexTwo
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.FittingOddCoreEquality
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PreambleInvolutions
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970API
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.FUFittingContainment
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Theorem26
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma28
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CoprimeActionNontrivialTransfer
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Theorem4
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourOfCommutingInvolutions
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.MinimalCounterexample
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.OddPCoresCentralizeFitting
import Mathlib.GroupTheory.FixedPointFree
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ExistsReflection

namespace CFSG
end CFSG
open CFSG

namespace CFSG.GorensteinWalter

universe u

noncomputable section

open scoped Pointwise

/-- Conjugating by `g` maps the centralizer of `x` onto the centralizer of
`g * x * g⁻¹`. -/
private theorem map_centralizer_singleton_conj
    {G : Type u} [Group G] (g x : G) :
    Subgroup.map (MulAut.conj g).toMonoidHom
      (Subgroup.centralizer ({x} : Set G)) =
      Subgroup.centralizer ({g * x * g⁻¹} : Set G) := by
  let e : G ≃* G := MulAut.conj g
  apply le_antisymm
  · intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨z, hz, hyz⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff.mp hw]
    have hzx : z * x = x * z :=
      (Subgroup.mem_centralizer_iff.mp hz x (by simp)).symm
    have hmap' : e z * e x = e x * e z := by
      simpa [map_mul] using congrArg e.toMonoidHom hzx
    change e z = y at hyz
    rw [hyz] at hmap'
    simpa [e, MulAut.conj_apply] using hmap'.symm
  · intro y hy
    let z : G := e.symm y
    have he_x : e x = g * x * g⁻¹ := by simp [e]
    have hzC : z ∈ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff.mp hw]
      have heq : y * e x = e x * y :=
        (Subgroup.mem_centralizer_iff.mp hy (e x) (by simpa using he_x)).symm
      have hmap' : e.symm y * e.symm (e x) = e.symm (e x) * e.symm y := by
        simpa [map_mul] using congrArg e.symm.toMonoidHom heq
      simp [e, he_x] at hmap'
      group at hmap'
      simpa [z, e, he_x, mul_assoc] using hmap'.symm
    refine Subgroup.mem_map.mpr ⟨z, hzC, ?_⟩
    change e (e.symm y) = y
    exact e.apply_symm_apply y

/-- The odd core of a conjugate centralizer is the conjugate odd core:
`O(C_G(s)) = U^g` when `s = g t g⁻¹`. -/
private theorem oddCoreOf_centralizer_conj
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) {g s : G} (hgs : g * c.t * g⁻¹ = s) :
    oddCoreOf (Subgroup.centralizer ({s} : Set G)) =
      conjugateSubgroup c.U g := by
  classical
  have hC : Subgroup.centralizer ({s} : Set G) =
      Subgroup.map (MulAut.conj g).toMonoidHom
        (Subgroup.centralizer ({c.t} : Set G)) := by
    rw [← hgs]
    exact (map_centralizer_singleton_conj g c.t).symm
  have hH : c.H = Subgroup.centralizer ({c.t} : Set G) := c.H_eq_centralizer
  have hmap : oddCoreOf (Subgroup.map (MulAut.conj g).toMonoidHom c.H) =
      Subgroup.map (MulAut.conj g).toMonoidHom (oddCoreOf c.H) := by
    let e : ↥c.H ≃* ↥(Subgroup.map (MulAut.conj g).toMonoidHom c.H) :=
      Subgroup.equivMapOfInjective c.H (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective
    have hcore : Subgroup.map e.toMonoidHom (pPrimeCore 2 (↥c.H)) =
        pPrimeCore 2 (↥(Subgroup.map (MulAut.conj g).toMonoidHom c.H)) :=
      pPrimeCore_map_iso 2 e
    have hcomp : (Subgroup.map (MulAut.conj g).toMonoidHom c.H).subtype.comp
        e.toMonoidHom = (MulAut.conj g).toMonoidHom.comp c.H.subtype := by
      ext x
      rfl
    calc
      oddCoreOf (Subgroup.map (MulAut.conj g).toMonoidHom c.H)
          = (pPrimeCore 2 (↥(Subgroup.map (MulAut.conj g).toMonoidHom c.H))).map
              (Subgroup.map (MulAut.conj g).toMonoidHom c.H).subtype := rfl
      _ = Subgroup.map (Subgroup.map (MulAut.conj g).toMonoidHom c.H).subtype
              (Subgroup.map e.toMonoidHom (pPrimeCore 2 (↥c.H))) := by
                rw [hcore]
      _ = Subgroup.map ((Subgroup.map (MulAut.conj g).toMonoidHom c.H).subtype.comp
              e.toMonoidHom) (pPrimeCore 2 (↥c.H)) := by
                rw [Subgroup.map_map]
      _ = Subgroup.map ((MulAut.conj g).toMonoidHom.comp c.H.subtype)
              (pPrimeCore 2 (↥c.H)) := by rw [hcomp]
      _ = Subgroup.map (MulAut.conj g).toMonoidHom
              (Subgroup.map c.H.subtype (pPrimeCore 2 (↥c.H))) := by
                rw [Subgroup.map_map]
      _ = Subgroup.map (MulAut.conj g).toMonoidHom (oddCoreOf c.H) := rfl
  rw [hC, ← hH, hmap]
  change Subgroup.map (MulAut.conj g).toMonoidHom (oddCoreOf c.H) =
      Subgroup.map (MulAut.conj g).toMonoidHom (oddCoreOf c.H)
  rfl

/-- `t` and a reflection `s` commute: both lie in `S ≤ H = C_G(t)`. -/
private theorem reflection_commutes_with_t
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) {s : G} (hs : c.IsReflection s) :
    Commute c.t s := by
  have hsH : s ∈ c.H := centralizerSetup_S_le_H c hs.1
  rw [c.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff] at hsH
  exact hsH.symm

/-- The `t`-invariant Sylow `p`-subgroup of `O(C_G(s))` containing
`C_{O_p(U)}(s)` supplied by Fact 1.1(ii). -/
private theorem exists_invariant_sylow_containing_fixed_core
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) {s : G} (hs : c.IsReflection s)
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p) :
    ∃ P : Subgroup G,
      BenderSuzuki.theorem4bIsSylowSubgroupOf p P
        (oddCoreOf (Subgroup.centralizer ({s} : Set G))) ∧
      centralizerIn (qCoreOf c.U p) s ≤ P ∧
      c.t ∈ Subgroup.normalizer (P : Set G) := by
  classical
  let D : Subgroup G := oddCoreOf (Subgroup.centralizer ({s} : Set G))
  let X : Subgroup G := centralizerIn (qCoreOf c.U p) s
  have hts : Commute c.t s := reflection_commutes_with_t c hs
  have htC : c.t ∈ Subgroup.centralizer ({s} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hts
  have htNormD : c.t ∈ Subgroup.normalizer (D : Set G) := by
    let C : Subgroup G := Subgroup.centralizer ({s} : Set G)
    have hchar : (pPrimeCore 2 (↥C)).Characteristic :=
      pPrimeCore_characteristic (p := 2)
    have hzNorm : ∀ z : G, z ∈ C →
        ∀ x : G, x ∈ D → z * x * z⁻¹ ∈ D := by
      intro z hz x hx
      rcases (Subgroup.mem_map).1 hx with ⟨y, hy, rfl⟩
      let e : ↥C ≃* ↥C := MulAut.conj ⟨z, hz⟩
      have hcomap : pPrimeCore 2 (↥C) ≤
          (pPrimeCore 2 (↥C)).comap e.toMonoidHom :=
        (Subgroup.characteristic_iff_le_comap.mp hchar) e
      have he : e y ∈ pPrimeCore 2 (↥C) := hcomap hy
      exact Subgroup.mem_map.mpr
        ⟨e y, he, by
          change z * (y : G) * z⁻¹ = z * (y : G) * z⁻¹
          rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hzNorm c.t htC x hx
    · intro hx
      have hy : c.t⁻¹ * (c.t * (x : G) * c.t⁻¹) * c.t ∈ D := by
        simpa using
          hzNorm c.t⁻¹ (C.inv_mem htC) (c.t * (x : G) * c.t⁻¹) hx
      simpa [mul_assoc] using hy
  have htNormX : c.t ∈ Subgroup.normalizer (X : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have htNormQ : c.t ∈ Subgroup.normalizer
        (qCoreOf c.U p : Set G) := by
      -- `t` centralizes `U`, hence its p-core.
      have htCentU : c.t ∈ Subgroup.centralizer (c.U : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro u hu
        have huH : u ∈ c.H :=
          (Subgroup.map_subtype_le (H := c.H) (pPrimeCore 2 c.H)) hu
        rw [c.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff] at huH
        exact huH
      exact (Subgroup.centralizer_le_normalizer (qCoreOf c.U p : Set G))
        (by
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          exact (Subgroup.mem_centralizer_iff.mp htCentU) y
            (qCoreOf_le c.U p hy))
    have htNormC : c.t ∈ Subgroup.normalizer
        (Subgroup.centralizer ({s} : Set G) : Set G) :=
      Subgroup.le_normalizer htC
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at htNormQ htNormC
    change (qCoreOf c.U p ⊓ Subgroup.centralizer ({s} : Set G)).map
      (MulAut.conj c.t).toMonoidHom =
      qCoreOf c.U p ⊓ Subgroup.centralizer ({s} : Set G)
    rw [Subgroup.map_inf _ _ _ (MulAut.conj c.t).injective]
    simpa [htNormQ, htNormC]
  rcases BenderSuzuki.theorem4b_exists_invariant_sylow_containing
    (D := D) (P := X) (z := c.t) (p := p)
    (odd_card_oddCoreOf (Subgroup.centralizer ({s} : Set G)))
    c.t_involution htNormD hp
    (IsPGroup.to_le (qCoreOf_isPGroup c.U p) inf_le_left)
    (reflection_qCore_centralizer_le_oddCore hmin c hs hp hpodd)
    htNormX with ⟨Q, hQ, hXQ, htQ⟩
  exact ⟨Q, hQ, hXQ, htQ⟩

/-- A `t`-invariant Sylow `p`-subgroup of `O(C_G(s))` containing a proper
fixed subgroup `C_{O_p(U)}(s)` cannot lie in `C_G(t)`.  Otherwise it would
be a Sylow `p`-subgroup of `U` as well, forcing the whole p-core into the
fixed subgroup. -/
private theorem invariant_sylow_not_le_H
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) {s : G} (hs : c.IsReflection s)
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (P : Subgroup G)
    (hPsyl : BenderSuzuki.theorem4bIsSylowSubgroupOf p P
      (oddCoreOf (Subgroup.centralizer ({s} : Set G))))
    (hXP : centralizerIn (qCoreOf c.U p) s ≤ P)
    (hXproper : centralizerIn (qCoreOf c.U p) s ≠ qCoreOf c.U p) :
    ¬ P ≤ c.H := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let X : Subgroup G := centralizerIn (qCoreOf c.U p) s
  intro hPleH
  rcases hPsyl with ⟨Q, hQeq⟩
  have hQp : IsPGroup p (Q : Subgroup (oddCoreOf (Subgroup.centralizer ({s} : Set G)))) :=
    Q.isPGroup'
  have hPp : IsPGroup p P := by
    rw [hQeq]
    exact hQp.map (oddCoreOf (Subgroup.centralizer ({s} : Set G))).subtype
  have hPodd : Nat.Coprime 2 (Nat.card P) := by
    rcases hPp.exists_card_eq with ⟨n, hn⟩
    rw [hn]
    exact (hpodd.pow).coprime_two_left
  have hPleU : P ≤ c.U := odd_order_subgroup_le_U_of_H_eq_SU hmin c hPleH hPodd
  -- `P` is a Sylow `p`-subgroup of `U`: orders agree with the conjugate
  -- odd core `O(C_G(s)) ≅ U`.
  have hPcardD : Nat.card P = p ^ (Nat.card
      (oddCoreOf (Subgroup.centralizer ({s} : Set G)))).factorization p := by
    rw [hQeq]
    calc
      Nat.card (Subgroup.map (oddCoreOf (Subgroup.centralizer ({s} : Set G))).subtype
          (Q : Subgroup (oddCoreOf (Subgroup.centralizer ({s} : Set G))))) =
          Nat.card (Q : Subgroup (oddCoreOf (Subgroup.centralizer ({s} : Set G)))) :=
            Subgroup.card_map_of_injective
              (oddCoreOf (Subgroup.centralizer ({s} : Set G))).subtype_injective
      _ = p ^ (Nat.card
          (oddCoreOf (Subgroup.centralizer ({s} : Set G)))).factorization p :=
            Q.card_eq_multiplicity
  obtain ⟨g, hgs⟩ := fact_2_preamble_involutions_conjugate_proved hmin c.t s
    c.t_involution (centralizerSetup_reflection_isInvolution c hs)
  have hUg : oddCoreOf (Subgroup.centralizer ({s} : Set G)) =
      conjugateSubgroup c.U g := oddCoreOf_centralizer_conj c hgs
  have hcardUg : Nat.card (oddCoreOf (Subgroup.centralizer ({s} : Set G))) =
      Nat.card c.U := by
    rw [hUg, conjugateSubgroup]
    exact Nat.card_congr (Subgroup.equivMapOfInjective c.U
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm.toEquiv
  have hPcardU : Nat.card P = p ^ (Nat.card c.U).factorization p := by
    rw [hPcardD, hcardUg]
  let UQ : Sylow p c.U := Sylow.ofCard (P.subgroupOf c.U) (by
    calc
      Nat.card (P.subgroupOf c.U) = Nat.card P :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPleU).toEquiv
      _ = p ^ (Nat.card c.U).factorization p := hPcardU)
  have hPleUQ : P ≤ (UQ : Subgroup c.U).map c.U.subtype := by
    intro x hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hPleU hx⟩, ?_, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr hx
  -- `O_p(U) ≤ P` since the p-core is contained in every Sylow subgroup.
  have hQcoreP : qCoreOf c.U p ≤ P := by
    have hcoreP : IsPGroup p ((qCoreOf c.U p).subgroupOf c.U) :=
      (qCoreOf_isPGroup c.U p).of_equiv
        (Subgroup.subgroupOfEquivOfLe (qCoreOf_le c.U p)).symm
    have : ((qCoreOf c.U p).subgroupOf c.U).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer (H := c.U)
        (N := qCoreOf c.U p)
        (le_normalizer_of_isNormalIn (qCoreOf_normal_in c.U p))
    have hcore_sub : (qCoreOf c.U p).subgroupOf c.U ≤
        (UQ : Subgroup c.U) := by
      exact IsPGroup.le_sylow_of_normal hcoreP UQ
    intro x hx
    have hxU : x ∈ c.U := qCoreOf_le c.U p hx
    have hxsub : (⟨x, hxU⟩ : c.U) ∈ (qCoreOf c.U p).subgroupOf c.U :=
      hx
    have hxQ : (⟨x, hxU⟩ : c.U) ∈ (UQ : Subgroup c.U) := hcore_sub hxsub
    exact (Subgroup.mem_subgroupOf.mp hxQ)
  -- `X = P ∩ O_p(U)`.
  have hXPinf : X = P ⊓ qCoreOf c.U p := by
    apply le_antisymm
    · intro x hx
      exact Subgroup.mem_inf.mpr ⟨hXP hx, hx.1⟩
    · intro x hx
      refine Subgroup.mem_inf.mpr ⟨hx.2, ?_⟩
      have hxP : x ∈ P := hx.1
      have hxO : x ∈ qCoreOf c.U p := hx.2
      have hxC : x ∈ Subgroup.centralizer ({s} : Set G) := by
        have hPleD : P ≤ oddCoreOf (Subgroup.centralizer ({s} : Set G)) := by
          rw [hQeq]
          exact Subgroup.map_subtype_le
            (H := oddCoreOf (Subgroup.centralizer ({s} : Set G)))
            (Q : Subgroup (oddCoreOf (Subgroup.centralizer ({s} : Set G))))
        have hPleC : P ≤ Subgroup.centralizer ({s} : Set G) :=
          hPleD.trans (Subgroup.map_subtype_le
            (H := Subgroup.centralizer ({s} : Set G))
            (pPrimeCore 2 (↥(Subgroup.centralizer ({s} : Set G)))))
        exact hPleC hxP
      exact hxC
  have hXeq : X = qCoreOf c.U p := by
    rw [hXPinf]
    exact inf_eq_right.mpr hQcoreP
  exact hXproper hXeq

/-- Fact 1.1(iv): if `t` does not centralize the invariant Sylow subgroup
`P`, then it acts nontrivially on the normalizer in `P` of the fixed
subgroup `X`. -/
private theorem commutator_t_normalizer_fixed_core_ne_bot
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    {s : G} (hs : c.IsReflection s)
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (P : Subgroup G) (hPp : IsPGroup p P)
    (hXP : centralizerIn (qCoreOf c.U p) s ≤ P)
    (htP : c.t ∈ Subgroup.normalizer (P : Set G))
    (hPnotCent : ¬ P ≤ c.H) :
    let X := centralizerIn (qCoreOf c.U p) s
    ⁅P ⊓ Subgroup.normalizer (X : Set G), Subgroup.zpowers c.t⁆ ≠ ⊥ := by
  classical
  let X : Subgroup G := centralizerIn (qCoreOf c.U p) s
  let N : Subgroup G := P ⊓ Subgroup.normalizer (X : Set G)
  let Q : Subgroup G := Subgroup.zpowers c.t
  have hQnormP : Q ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.zpowers_le.mpr htP
  have hNleP : N ≤ P := inf_le_left
  have hsub : (N.subgroupOf P).IsSubnormal := by
    let : Fact p.Prime := ⟨hp⟩
    have hPnil : Group.IsNilpotent (↥P) := IsPGroup.isNilpotent hPp
    exact isSubnormal_of_nilpotent hPnil N hNleP
  have hself : P ⊓ Subgroup.centralizer (N : Set G) ≤ N := by
    intro x hx
    have hxP : x ∈ P := hx.1
    have hxX : x ∈ Subgroup.centralizer (X : Set G) := by
      have hXleN : X ≤ N := le_inf hXP Subgroup.le_normalizer
      exact (Subgroup.centralizer_le (SetLike.coe_mono hXleN)) hx.2
    exact Subgroup.mem_inf.mpr ⟨hxP,
      (Subgroup.centralizer_le_normalizer (X : Set G)) hxX⟩
  have hcop : Nat.Coprime (Nat.card Q) (Nat.card P) := by
    let : Fact p.Prime := ⟨hp⟩
    have hQcard : Nat.card Q = 2 := by
      have htord : orderOf c.t = 2 :=
        orderOf_eq_prime c.t_involution.2 c.t_involution.1
      simp [Q, Nat.card_zpowers, htord]
    rcases hPp.exists_card_eq with ⟨n, hn⟩
    rw [hQcard, hn]
    exact (hpodd.pow).coprime_two_left
  have hsolv : IsSolvable P := by
    let : Fact p.Prime := ⟨hp⟩
    exact isSolvable_of_isPGroup hPp
  have hQnotCent : ¬ Q ≤ Subgroup.centralizer (P : Set G) := by
    intro hQcent
    apply hPnotCent
    intro y hy
    rw [c.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (hQcent (Subgroup.mem_zpowers c.t))
      y hy)
  exact commutator_ne_bot_of_subnormal_selfCentralizing_coprime
    Q P N hQnormP hNleP hsub hself hcop hsolv hQnotCent

/-- `t` and a reflection `s` both normalize `K = N_P(X)`: `t` normalizes
`P` and `X`, while `s` centralizes `P` and normalizes `X`. -/
private theorem t_s_normalize_normalizer_in_sylow
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) {s : G} (hs : c.IsReflection s)
    {P X : Subgroup G}
    (hXP : X ≤ P)
    (hsP : s ∈ Subgroup.centralizer (P : Set G))
    (hsX : s ∈ Subgroup.normalizer (X : Set G))
    (htP : c.t ∈ Subgroup.normalizer (P : Set G))
    (htX : c.t ∈ Subgroup.normalizer (X : Set G)) :
    s ∈ Subgroup.normalizer
        ((P ⊓ Subgroup.normalizer (X : Set G)) : Set G) ∧
      c.t ∈ Subgroup.normalizer
        ((P ⊓ Subgroup.normalizer (X : Set G)) : Set G) := by
  classical
  let K : Subgroup G := P ⊓ Subgroup.normalizer (X : Set G)
  have hsNormP : s ∈ Subgroup.normalizer (P : Set G) :=
    (Subgroup.centralizer_le_normalizer (P : Set G)) hsP
  have hsNormNX : s ∈ Subgroup.normalizer
      (Subgroup.normalizer (X : Set G) : Set G) :=
    Subgroup.le_normalizer hsX
  have htNormNX : c.t ∈ Subgroup.normalizer
      (Subgroup.normalizer (X : Set G) : Set G) :=
    Subgroup.le_normalizer htX
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hsNormP hsNormNX htP htNormNX
  constructor
  · change s ∈ Subgroup.normalizer
      ↑(P ⊓ Subgroup.normalizer (X : Set G))
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rw [Subgroup.map_inf]
    · rw [hsNormP, hsNormNX]
    · exact (MulAut.conj s).injective
  · change c.t ∈ Subgroup.normalizer
      ↑(P ⊓ Subgroup.normalizer (X : Set G))
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rw [Subgroup.map_inf]
    · rw [htP, htNormNX]
    · exact (MulAut.conj c.t).injective

/-- `t` centralizes `K` iff `[K,⟨t⟩] = 1`, in the form needed for the
branch contradictions. -/
private theorem centralizes_iff_commutator_eq_bot
    {G : Type u} [Group G] (t : G) {K : Subgroup G} :
    (∀ k : G, k ∈ K → k * t = t * k) ↔
      ⁅K, Subgroup.zpowers t⁆ = ⊥ := by
  classical
  constructor
  · intro h
    apply (Subgroup.commutator_eq_bot_iff_le_centralizer
      (H₁ := K) (H₂ := Subgroup.zpowers t)).2
    intro k hk z hz
    rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, rfl⟩
    have hkt : k * t = t * k := h k hk
    have hcomm : Commute k t := hkt
    exact (hcomm.zpow_right n).symm
  · intro h k hk
    have hle : K ≤ Subgroup.centralizer
        ((Subgroup.zpowers t : Subgroup G) : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer
        (H₁ := K) (H₂ := Subgroup.zpowers t)).1 h
    have hkC : k ∈ Subgroup.centralizer
        ((Subgroup.zpowers t : Subgroup G) : Set G) := hle hk
    exact (Subgroup.mem_centralizer_iff.mp hkC t
      (Subgroup.mem_zpowers t)).symm

/-- The two-core of `Ĥ` is a Klein four whenever the p-core quotient branch
of Theorem 2.6 holds. -/
private theorem twoCoreOf_isKleinFour_of_centralizerStructure
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (hK4 : IsKleinFour (pCore 2 c.Hhat)) :
    IsKleinFour (twoCoreOf c.Hhat) := by
  let e : pCore 2 c.Hhat ≃* twoCoreOf c.Hhat :=
    Subgroup.equivMapOfInjective (pCore 2 c.Hhat) c.Hhat.subtype
      c.Hhat.subtype_injective
  exact {
    card_four := (Nat.card_congr e.toEquiv).symm.trans hK4.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv e).symm.trans hK4.exponent_two
  }

/-- If `W ≤ S` and `U ∩ S = 1`, then `(W ⊔ U) ∩ S ≤ W`. -/
private theorem sup_inter_le_of_le_and_disjoint
    {G : Type u} [Group G] (W U S : Subgroup G)
    (hWnorm : IsNormalIn W (W ⊔ U))
    (hUnorm : IsNormalIn U (W ⊔ U))
    (hWS : W ≤ S) (hUS : Disjoint U S) :
    (W ⊔ U) ⊓ S ≤ W := by
  intro x hx
  let H : Subgroup G := W ⊔ U
  let W' : Subgroup (↥H) := W.subgroupOf H
  let U' : Subgroup (↥H) := U.subgroupOf H
  have hW'norm : W'.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (H := H) (N := W)
      (le_normalizer_of_isNormalIn hWnorm)
  have hU'norm : U'.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (H := H) (N := U)
      (le_normalizer_of_isNormalIn hUnorm)
  have htop : W' ⊔ U' = ⊤ := by
    dsimp [W', U', H]
    rw [← Subgroup.subgroupOf_sup (le_sup_left : W ≤ W ⊔ U)
      (le_sup_right : U ≤ W ⊔ U), Subgroup.subgroupOf_self]
  let : U'.Normal := hU'norm
  have hxSup : (⟨x, hx.1⟩ : ↥H) ∈ W' ⊔ U' := by
    rw [htop]
    trivial
  rcases (Subgroup.mem_sup_of_normal_right (s := W') (t := U')
      (x := (⟨x, hx.1⟩ : ↥H))).mp hxSup with ⟨w', hwW', u', huU', hwueq⟩
  have hxEq : (w' : G) * (u' : G) = x := congrArg Subtype.val hwueq
  have hwW : (w' : G) ∈ W := (Subgroup.mem_subgroupOf).mp hwW'
  have huU : (u' : G) ∈ U := (Subgroup.mem_subgroupOf).mp huU'
  have hwS : (w' : G) ∈ S := hWS hwW
  have huS : (u' : G) ∈ S := (S.mul_mem_cancel_left hwS).mp
    (by simpa [hxEq] using hx.2)
  have hu1 : (u' : G) = 1 := Subgroup.disjoint_def.mp hUS huU huS
  simpa [← hxEq, hu1] using hwW

/-- Two subgroups which are normal in their join and disjoint have trivial
commutator. -/
private theorem commutator_eq_bot_of_normal_subgroupOf_disjoint
    {G : Type u} [Group G] (W K : Subgroup G)
    (hWnorm : W ⊔ K ≤ Subgroup.normalizer (W : Set G))
    (hKnorm : W ⊔ K ≤ Subgroup.normalizer (K : Set G))
    (hdisj : Disjoint W K) :
    ⁅W, K⁆ = ⊥ := by
  let H : Subgroup G := W ⊔ K
  let W' : Subgroup (↥H) := W.subgroupOf H
  let K' : Subgroup (↥H) := K.subgroupOf H
  have hW'norm : W'.Normal := by
    dsimp [W', H]
    exact Subgroup.normal_subgroupOf_of_le_normalizer (H := W ⊔ K) (N := W) hWnorm
  have hK'norm : K'.Normal := by
    dsimp [K', H]
    exact Subgroup.normal_subgroupOf_of_le_normalizer (H := W ⊔ K) (N := K) hKnorm
  have hdisj' : Disjoint W' K' := by
    rw [Subgroup.disjoint_def] at hdisj ⊢
    intro x hxW hxK
    exact Subtype.ext (hdisj (Subgroup.mem_subgroupOf.mp hxW)
      (Subgroup.mem_subgroupOf.mp hxK))
  have hcomm' : ⁅W', K'⁆ = ⊥ := Subgroup.commutator_eq_bot_of_disjoint hdisj'
  have hmap : (⁅W', K'⁆).map H.subtype = ⁅W, K⁆ := by
    rw [Subgroup.map_commutator]
    dsimp [W', K', H]
    rw [Subgroup.map_subgroupOf_eq_of_le (le_sup_left : W ≤ W ⊔ K)]
    rw [Subgroup.map_subgroupOf_eq_of_le (le_sup_right : K ≤ W ⊔ K)]
  have hmapbot : (⁅W', K'⁆).map H.subtype = ⊥ := by
    simpa [hcomm'] using (Subgroup.map_bot H.subtype)
  exact hmap.symm.trans hmapbot

/-- An odd-order subgroup of the centralizer of a reflection in `D₆` is
trivial. -/
private theorem odd_order_subgroup_eq_bot_of_centralize_sr_dihedral_three
    {A : Subgroup (DihedralGroup 3)} (j : ZMod 3)
    (hA : A ≤ Subgroup.centralizer
      ({DihedralGroup.sr j} : Set (DihedralGroup 3)))
    (hodd : Odd (Nat.card A)) :
    A = ⊥ := by
  classical
  let C : Subgroup (DihedralGroup 3) :=
    Subgroup.centralizer ({DihedralGroup.sr j} : Set (DihedralGroup 3))
  have hCsub : (C : Set (DihedralGroup 3)) ⊆ {DihedralGroup.sr j, 1} := by
    intro x hx
    have hcomm : DihedralGroup.sr j * x = x * DihedralGroup.sr j :=
      (Subgroup.mem_centralizer_iff.mp hx) (DihedralGroup.sr j) (by simp)
    rcases x with i | i
    · have h2i : (2 : ZMod 3) * i = 0 := by
        have hji : j + i = j - i := DihedralGroup.sr.inj (by simpa using hcomm)
        calc
          (2 : ZMod 3) * i = i + i := by ring
          _ = (j + i) - j + i := by abel
          _ = (j - i) - j + i := by rw [hji]
          _ = 0 := by abel
      have h2ne : (2 : ZMod 3) ≠ 0 := by decide
      have hi : i = 0 := (mul_eq_zero.mp h2i).resolve_left h2ne
      simp [hi]
    · have h2i : (2 : ZMod 3) * (i - j) = 0 := by
        have hji : i - j = j - i := DihedralGroup.r.inj (by simpa using hcomm)
        calc
          (2 : ZMod 3) * (i - j) = (i - j) + (i - j) := by ring
          _ = (i - j) + (j - i) := by rw [hji]
          _ = 0 := by abel
      have h2ne : (2 : ZMod 3) ≠ 0 := by decide
      have hij : i - j = 0 := (mul_eq_zero.mp h2i).resolve_left h2ne
      have hi : i = j := sub_eq_zero.mp hij
      simp [hi]
  have hCcard_le2 : Nat.card C ≤ 2 := by
    calc
      Nat.card C = (C : Set (DihedralGroup 3)).ncard :=
        Nat.card_coe_set_eq (C : Set (DihedralGroup 3))
      _ ≤ ({DihedralGroup.sr j, 1} : Set (DihedralGroup 3)).ncard :=
        Set.ncard_le_ncard hCsub
      _ ≤ 2 := by
        calc
          ({DihedralGroup.sr j, 1} : Set (DihedralGroup 3)).ncard ≤
              ({1} : Set (DihedralGroup 3)).ncard + 1 :=
            Set.ncard_insert_le (DihedralGroup.sr j)
              ({1} : Set (DihedralGroup 3))
          _ ≤ 2 := by simp
  have hCcard_ge2 : 2 ≤ Nat.card C := by
    calc
      2 ≤ ({DihedralGroup.sr j, 1} : Set (DihedralGroup 3)).ncard := by
        have hncard : ({DihedralGroup.sr j, 1} : Set (DihedralGroup 3)).ncard = 2 := by
          rw [Set.ncard_insert_of_notMem]
          · simp
          · intro h
            have h' : DihedralGroup.sr j = DihedralGroup.r 0 := by simpa using h
            cases h'
        exact hncard.ge
      _ ≤ (C : Set (DihedralGroup 3)).ncard := Set.ncard_le_ncard (by
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · change DihedralGroup.sr j ∈ C
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          rw [Set.mem_singleton_iff.mp hy]
        · exact C.one_mem)
      _ = Nat.card C := (Nat.card_coe_set_eq (C : Set (DihedralGroup 3))).symm
  have hCcard : Nat.card C = 2 := Nat.le_antisymm hCcard_le2 hCcard_ge2
  rcases hodd with ⟨k, hk⟩
  have hk0 : k = 0 := by
    have hle : 2 * k + 1 ≤ 2 := by
      rw [← hk]
      exact (Subgroup.card_le_of_le (K := C) hA).trans hCcard_le2
    omega
  have hcard1 : Nat.card A = 1 := by omega
  exact (Subgroup.eq_bot_iff_card A).mpr hcard1

/-- An odd-order subgroup contained in `W ⊔ U`, where `W` is a `2`-group
commuting elementwise with `U` and disjoint from it, lies in `U`. -/
private theorem odd_order_subgroup_le_of_le_sup_of_twoPGroup
    {G : Type u} [Group G] [Finite G]
    (W U K : Subgroup G)
    (hWnorm : IsNormalIn W (W ⊔ U))
    (hUnorm : IsNormalIn U (W ⊔ U))
    (hWU : ∀ w : G, w ∈ W → ∀ u : G, u ∈ U → w * u = u * w)
    (hK : K ≤ W ⊔ U)
    (hWp : IsPGroup 2 W)
    (hKodd : Odd (Nat.card K))
    (hdisj : Disjoint W U) :
    K ≤ U := by
  intro k hk
  let H : Subgroup G := W ⊔ U
  let W' : Subgroup (↥H) := W.subgroupOf H
  let U' : Subgroup (↥H) := U.subgroupOf H
  have hW'norm : W'.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (H := H) (N := W)
      (le_normalizer_of_isNormalIn hWnorm)
  have hU'norm : U'.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (H := H) (N := U)
      (le_normalizer_of_isNormalIn hUnorm)
  have htop : W' ⊔ U' = ⊤ := by
    dsimp [W', U', H]
    rw [← Subgroup.subgroupOf_sup (le_sup_left : W ≤ W ⊔ U)
      (le_sup_right : U ≤ W ⊔ U), Subgroup.subgroupOf_self]
  let : U'.Normal := hU'norm
  have hkSup : (⟨k, hK hk⟩ : ↥H) ∈ W' ⊔ U' := by
    rw [htop]
    trivial
  rcases (Subgroup.mem_sup_of_normal_right (s := W') (t := U')
      (x := (⟨k, hK hk⟩ : ↥H))).mp hkSup with ⟨w', hwW', u', huU', hwueq⟩
  have hwW : (w' : G) ∈ W := (Subgroup.mem_subgroupOf).mp hwW'
  have huU : (u' : G) ∈ U := (Subgroup.mem_subgroupOf).mp huU'
  have hkEq : (w' : G) * (u' : G) = k := congrArg Subtype.val hwueq
  have hordKodd : Odd (orderOf k) := by
    have hsub : Subgroup.zpowers k ≤ K := Subgroup.zpowers_le.mpr hk
    have hord : orderOf k = Nat.card (Subgroup.zpowers k) :=
      (Nat.card_zpowers k).symm
    have hdvd : orderOf k ∣ Nat.card K := by
      rw [hord]
      exact Subgroup.card_dvd_of_le hsub
    exact Odd.of_dvd_nat hKodd hdvd
  let n : ℕ := orderOf k
  have hpow : k ^ n = 1 := pow_orderOf_eq_one k
  have hcomm : Commute (w' : G) (u' : G) := hWU (w' : G) hwW (u' : G) huU
  have hkpow : k ^ n = (w' : G) ^ n * (u' : G) ^ n := by
    rw [← hkEq]
    exact hcomm.mul_pow n
  have hwun : (w' : G) ^ n * (u' : G) ^ n = 1 := by
    rwa [hkpow] at hpow
  have hwn : (w' : G) ^ n = 1 := by
    have hwinW : (w' : G) ^ n ∈ W := W.pow_mem hwW n
    have huinU : (u' : G) ^ n ∈ U := U.pow_mem huU n
    have hwEqInv : (w' : G) ^ n = ((u' : G) ^ n)⁻¹ :=
      (mul_eq_one_iff_eq_inv.mp hwun)
    have hwinU : (w' : G) ^ n ∈ U := by
      rw [hwEqInv]
      exact U.inv_mem huinU
    exact Subgroup.disjoint_def.mp hdisj hwinW hwinU
  have hw1 : (w' : G) = 1 := by
    have hdvdn : orderOf (w' : G) ∣ n := orderOf_dvd_iff_pow_eq_one.mpr hwn
    rcases hWp.exists_card_eq with ⟨m, hm⟩
    have hdvd2 : orderOf (w' : G) ∣ 2 ^ m := by
      have hsub : Subgroup.zpowers (w' : G) ≤ W := Subgroup.zpowers_le.mpr hwW
      have hord : orderOf (w' : G) = Nat.card (Subgroup.zpowers (w' : G)) :=
        (Nat.card_zpowers (w' : G)).symm
      have hdvd : orderOf (w' : G) ∣ Nat.card W := by
        rw [hord]
        exact Subgroup.card_dvd_of_le hsub
      rwa [hm] at hdvd
    have hdvd1 : orderOf (w' : G) ∣ 1 := by
      have hgcd : Nat.gcd n (2 ^ m) = 1 :=
        ((Nat.coprime_two_left.mpr hordKodd).symm.pow_right m).gcd_eq_one
      rw [← hgcd]
      exact Nat.dvd_gcd hdvdn hdvd2
    have hord1 : orderOf (w' : G) = 1 := Nat.dvd_one.mp hdvd1
    exact orderOf_eq_one_iff.mp hord1
  simpa [← hkEq, hw1] using huU

/-- Fact 1.1(iv) transfer: for a proper nontrivial fixed subgroup
`X = C_{O_p(U)}(s)`, the normalizer `N_G(X)` is not contained in `Ĥ`.

If `N_G(X) ≤ Ĥ`, the invariant Sylow subgroup `P` gives
`[K, ⟨t⟩] ≠ 1` for `K = P ∩ N_G(X)`.  In the first branch of Theorem 2.6,
`Ĥ = H` centralizes `K`.  In the second branch, `W = O₂(Ĥ) ≅ V₄`: either
`s ∈ W`, so `W = ⟨t,s⟩` normalizes `K` and `[W,K] = 1`, or `s ∉ W`, so the
image of `s` in `Ĥ/WU ≅ D₆` is a reflection whose centralizer has order two,
forcing the odd-order image of `K` to be trivial and `K ≤ U`, again
centralized by `t`.  Both contradict `[K, ⟨t⟩] ≠ 1`. -/
private theorem normalizer_fixed_core_not_le_Hhat
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) {s : G} (hs : c.IsReflection s)
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (hXne : centralizerIn (qCoreOf c.U p) s ≠ ⊥)
    (hXproper : centralizerIn (qCoreOf c.U p) s ≠ qCoreOf c.U p) :
    ¬ Subgroup.normalizer (centralizerIn (qCoreOf c.U p) s : Set G) ≤ c.Hhat := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let X : Subgroup G := centralizerIn (qCoreOf c.U p) s
  obtain ⟨P, hPsyl, hXP, htP⟩ :=
    exists_invariant_sylow_containing_fixed_core hmin c hs hp hpodd
  have hPp : IsPGroup p P := by
    rcases hPsyl with ⟨Q, hQeq⟩
    have hQp : IsPGroup p
        (Q : Subgroup (oddCoreOf (Subgroup.centralizer ({s} : Set G)))) :=
      Q.isPGroup'
    rw [hQeq]
    exact hQp.map (oddCoreOf (Subgroup.centralizer ({s} : Set G))).subtype
  have hPodd : Nat.Coprime 2 (Nat.card P) := by
    rcases hPp.exists_card_eq with ⟨n, hn⟩
    rw [hn]
    exact (hpodd.pow).coprime_two_left
  have hPnotCent : ¬ P ≤ c.H :=
    invariant_sylow_not_le_H hmin c hs hp hpodd P hPsyl hXP hXproper
  have hsP : s ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hPleD : P ≤ oddCoreOf (Subgroup.centralizer ({s} : Set G)) := by
      rcases hPsyl with ⟨Q, hQeq⟩
      rw [hQeq]
      exact Subgroup.map_subtype_le
        (H := oddCoreOf (Subgroup.centralizer ({s} : Set G)))
        (Q : Subgroup (oddCoreOf (Subgroup.centralizer ({s} : Set G))))
    have hPleC : P ≤ Subgroup.centralizer ({s} : Set G) :=
      hPleD.trans (Subgroup.map_subtype_le
        (H := Subgroup.centralizer ({s} : Set G))
        (pPrimeCore 2 (↥(Subgroup.centralizer ({s} : Set G)))))
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hPleC hx))
  have hsCentX : s ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_singleton_iff.mp hx.2)
  have hsX : s ∈ Subgroup.normalizer (X : Set G) :=
    (Subgroup.centralizer_le_normalizer (X : Set G)) hsCentX
  have htCentU : c.t ∈ Subgroup.centralizer (c.U : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have huH : u ∈ c.H :=
      (Subgroup.map_subtype_le (H := c.H) (pPrimeCore 2 c.H)) hu
    rw [c.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff] at huH
    exact huH
  have htCentQ : c.t ∈ Subgroup.centralizer (qCoreOf c.U p : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp htCentU) y (qCoreOf_le c.U p hy)
  have htCentX : c.t ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp htCentQ) x hx.1
  have htX : c.t ∈ Subgroup.normalizer (X : Set G) :=
    (Subgroup.centralizer_le_normalizer (X : Set G)) htCentX
  let K : Subgroup G := P ⊓ Subgroup.normalizer (X : Set G)
  have hKleP : K ≤ P := inf_le_left
  have hKleNX : K ≤ Subgroup.normalizer (X : Set G) := inf_le_right
  have hKodd : Nat.Coprime 2 (Nat.card K) := by
    have hdvd : Nat.card K ∣ Nat.card P := Subgroup.card_dvd_of_le hKleP
    exact Nat.Coprime.of_dvd_right hdvd hPodd
  have hKoddNat : Odd (Nat.card K) := Nat.coprime_two_left.mp hKodd
  have hcommK : ⁅K, Subgroup.zpowers c.t⁆ ≠ ⊥ :=
    commutator_t_normalizer_fixed_core_ne_bot c hs hp hpodd P hPp hXP htP hPnotCent
  have htsK : s ∈ Subgroup.normalizer (K : Set G) ∧
      c.t ∈ Subgroup.normalizer (K : Set G) :=
    t_s_normalize_normalizer_in_sylow c hs hXP hsP hsX htP htX
  have h26 : CentralizerStructure c := theorem_2_6 hmin c
  intro hNleHhat
  have hKleHhat : K ≤ c.Hhat := by
    intro k hk
    exact hNleHhat (hKleNX hk)
  rcases h26.2.2 with hCase1 | hCase2
  · rcases hCase1 with ⟨_hVleS0, hHhat_eq_H⟩
    have hKleH : K ≤ c.H := by
      rw [← hHhat_eq_H]
      exact hKleHhat
    have hCentK : ∀ k : G, k ∈ K → k * c.t = c.t * k := by
      intro k hk
      have hkH : k ∈ c.H := hKleH hk
      rw [c.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff] at hkH
      exact hkH
    have hcomm : ⁅K, Subgroup.zpowers c.t⁆ = ⊥ :=
      (centralizes_iff_commutator_eq_bot c.t (K := K)).1 hCentK
    exact hcommK hcomm
  · rcases hCase2 with ⟨hK4pCore, hQuot⟩
    let W : Subgroup G := twoCoreOf c.Hhat
    have hWK4 : IsKleinFour W :=
      twoCoreOf_isKleinFour_of_centralizerStructure c hK4pCore
    let : IsKleinFour W := hWK4
    have htW : c.t ∈ W := centralizerStructure_t_mem_twoCore c h26
    have hsS : s ∈ (c.S : Subgroup G) := hs.1
    have hsHhat : s ∈ c.Hhat :=
      ((centralizerSetup_S_le_H c).trans c.H_le_Hhat) hsS
    have hWleHhat : W ≤ c.Hhat :=
      Subgroup.map_subtype_le (H := c.Hhat) (pCore 2 c.Hhat)
    have hWnormHhat : IsNormalIn W c.Hhat := by
      have hq2 : twoCoreOf c.Hhat = qCoreOf c.Hhat 2 := by
        rw [twoCoreOf_eq_piCoreOf_2,
          qCoreOf_eq_piCoreOf_singleton c.Hhat 2 Nat.prime_two]
      simpa [W, hq2] using qCoreOf_normal_in c.Hhat 2
    have hUnormHhat : IsNormalIn c.U c.Hhat := by
      have hUeq : c.U = oddCoreOf c.Hhat := h26.1
      have hO : IsNormalIn (oddCoreOf c.Hhat) c.Hhat := by
        refine ⟨?_, ?_⟩
        · intro x hx
          rcases (Subgroup.mem_map).1 hx with ⟨y, _hy, rfl⟩
          exact y.2
        · intro h hh x hx
          rcases (Subgroup.mem_map).1 hx with ⟨y, hy, rfl⟩
          refine Subgroup.mem_map.mpr
            ⟨(⟨h, hh⟩ : ↥c.Hhat) * y * (⟨h, hh⟩ : ↥c.Hhat)⁻¹, ?_, by simp⟩
          exact (pPrimeCore_normal (p := 2) (G := ↥c.Hhat)).conj_mem
            y hy (⟨h, hh⟩ : ↥c.Hhat)
      simpa [hUeq] using hO
    have hWUleHhat : W ⊔ c.U ≤ c.Hhat := sup_le hWleHhat hUnormHhat.1
    have hWnorm : IsNormalIn W (W ⊔ c.U) := by
      refine ⟨le_sup_left, ?_⟩
      intro h hh w hwW
      exact hWnormHhat.2 h (hWUleHhat hh) w hwW
    have hUnorm : IsNormalIn c.U (W ⊔ c.U) := by
      refine ⟨le_sup_right, ?_⟩
      intro h hh u huU
      exact hUnormHhat.2 h (hWUleHhat hh) u huU
    by_cases hsW : s ∈ W
    · have hWV : W = Subgroup.closure ({c.t, s} : Set G) := by
        apply le_antisymm
        · intro x hx
          let tW : ↥W := ⟨c.t, htW⟩
          let sW : ↥W := ⟨s, hsW⟩
          let xW : ↥W := ⟨x, hx⟩
          have htWne : tW ≠ 1 := by
            intro h
            apply c.t_involution.1
            exact congrArg Subtype.val h
          have hsWne : sW ≠ 1 := by
            intro h
            apply (centralizerSetup_reflection_isInvolution c hs).1
            exact congrArg Subtype.val h
          have htsWne : tW ≠ sW := by
            intro h
            have hts : c.t = s := congrArg Subtype.val h
            apply hs.2
            exact hts ▸ c.t_mem_S0
          by_cases hx1 : xW = 1
          · have hx1' : x = 1 := congrArg Subtype.val hx1
            simpa [hx1'] using (Subgroup.closure ({c.t, s} : Set G)).one_mem
          by_cases hxt : xW = tW
          · have hx : x = c.t := congrArg Subtype.val hxt
            exact Subgroup.subset_closure (by simp [hx])
          by_cases hxs : xW = sW
          · have hx : x = s := congrArg Subtype.val hxs
            exact Subgroup.subset_closure (by simp [hx])
          · have hxeq : xW = tW * sW :=
              IsKleinFour.eq_mul_of_ne_all htWne hsWne htsWne hx1
                (by intro h; exact hxt h) (by intro h; exact hxs h)
            have htV : c.t ∈ Subgroup.closure ({c.t, s} : Set G) :=
              Subgroup.subset_closure (by simp)
            have hsV : s ∈ Subgroup.closure ({c.t, s} : Set G) :=
              Subgroup.subset_closure (by simp)
            have hx : x = c.t * s := congrArg Subtype.val hxeq
            simpa [hx] using (Subgroup.mul_mem (H := Subgroup.closure ({c.t, s} : Set G)) htV hsV)
        · exact (Subgroup.closure_le W).mpr (by
            intro x hx
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
            rcases hx with rfl | rfl
            · exact htW
            · exact hsW)
      have hWleNK : W ≤ Subgroup.normalizer (K : Set G) := by
        rw [hWV]
        exact (Subgroup.closure_le (Subgroup.normalizer (K : Set G))).mpr (by
          intro x hx
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with rfl | rfl
          · exact htsK.2
          · exact htsK.1)
      have hKnorm : W ⊔ K ≤ Subgroup.normalizer (K : Set G) :=
        sup_le hWleNK Subgroup.le_normalizer
      have hWnormJoin : W ⊔ K ≤ Subgroup.normalizer (W : Set G) :=
        (sup_le hWleHhat hKleHhat).trans (le_normalizer_of_isNormalIn hWnormHhat)
      have hdisj : Disjoint W K := by
        have hWKcop : Nat.Coprime (Nat.card W) (Nat.card K) := by
          have hWcard : Nat.card W = 4 := hWK4.card_four
          rw [hWcard]
          change Nat.Coprime (2 ^ 2) (Nat.card K)
          exact hKodd.pow_left 2
        exact Subgroup.disjoint_of_coprime_natCard hWKcop
      have hcommWK : ⁅W, K⁆ = ⊥ :=
        commutator_eq_bot_of_normal_subgroupOf_disjoint W K hWnormJoin hKnorm hdisj
      have hWleCentK : W ≤ Subgroup.centralizer (K : Set G) :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer
          (H₁ := W) (H₂ := K)).1 hcommWK
      have hCentK : ∀ k : G, k ∈ K → k * c.t = c.t * k := by
        intro k hk
        exact (Subgroup.mem_centralizer_iff.mp (hWleCentK htW)) k hk
      have hcomm : ⁅K, Subgroup.zpowers c.t⁆ = ⊥ :=
        (centralizes_iff_commutator_eq_bot c.t (K := K)).1 hCentK
      exact hcommK hcomm
    · have hWp : IsPGroup 2 W := by
        have hq2 : twoCoreOf c.Hhat = qCoreOf c.Hhat 2 := by
          rw [twoCoreOf_eq_piCoreOf_2,
            qCoreOf_eq_piCoreOf_singleton c.Hhat 2 Nat.prime_two]
        change IsPGroup 2 (twoCoreOf c.Hhat)
        rw [hq2]
        exact qCoreOf_isPGroup c.Hhat 2
      have hWleS : W ≤ (c.S : Subgroup G) := by
        change twoCoreOf c.Hhat ≤ (c.S : Subgroup G)
        rw [← h26.2.1]
        exact inf_le_left
      have hUodd : Odd (Nat.card c.U) := by
        rw [h26.1]
        exact odd_card_oddCoreOf c.Hhat
      have hUdisjS : Disjoint c.U (c.S : Subgroup G) := by
        rcases (c.S.isPGroup').exists_card_eq with ⟨n, hn⟩
        have hUcop : Nat.Coprime (Nat.card c.U) (Nat.card (c.S : Subgroup G)) := by
          rw [hn]
          exact (Nat.coprime_two_right.mpr hUodd).pow_right n
        exact Subgroup.disjoint_of_coprime_natCard hUcop
      have hWUinterS : (W ⊔ c.U) ⊓ (c.S : Subgroup G) ≤ W :=
        sup_inter_le_of_le_and_disjoint W c.U (c.S : Subgroup G)
          hWnorm hUnorm hWleS hUdisjS
      have hsNotWU : s ∉ W ⊔ c.U := by
        intro hsWU
        have hsWU' : s ∈ (W ⊔ c.U) ⊓ (c.S : Subgroup G) := ⟨hsWU, hsS⟩
        exact hsW (hWUinterS hsWU')
      let N : Subgroup (↥c.Hhat) := pCore 2 c.Hhat ⊔ pPrimeCore 2 c.Hhat
      let q : ↥c.Hhat →* (↥c.Hhat ⧸ N) := QuotientGroup.mk' N
      let sH : ↥c.Hhat := ⟨s, hsHhat⟩
      let sbar : ↥c.Hhat ⧸ N := q sH
      rcases hQuot with ⟨e⟩
      let r : DihedralGroup 3 := e sbar
      have hsbar_ne_one : sbar ≠ 1 := by
        intro hsbar1
        have hsH_in_N : sH ∈ N := (QuotientGroup.eq_one_iff sH).mp hsbar1
        have hNmap : N.map c.Hhat.subtype = W ⊔ c.U := by
          rw [Subgroup.map_sup]
          simp [W, h26.1, twoCoreOf, oddCoreOf]
        have hsInWU : s ∈ W ⊔ c.U := by
          have hsN : s ∈ N.map c.Hhat.subtype :=
            Subgroup.mem_map.mpr ⟨sH, hsH_in_N, rfl⟩
          simpa [hNmap] using hsN
        exact hsNotWU hsInWU
      have hsr2 : r ^ 2 = 1 := by
        have hs2 : s ^ 2 = 1 := (centralizerSetup_reflection_isInvolution c hs).2
        have hsbar2 : sbar ^ 2 = 1 := by
          dsimp [sbar]
          change (QuotientGroup.mk' N sH) ^ 2 = 1
          rw [← map_pow]
          have hss : sH ^ 2 = 1 := by
            apply Subtype.ext
            exact hs2
          rw [hss, map_one]
        change (e.toMonoidHom sbar) ^ 2 = 1
        rw [← map_pow]
        simpa [hsbar2]
      have hrne : r ≠ 1 := by
        intro hr1
        apply hsbar_ne_one
        apply e.injective
        simpa [r] using hr1
      have hr_reflection : ∃ i : ZMod 3, r = DihedralGroup.sr i := by
        rcases r with i | i
        · have hri2 : (DihedralGroup.r i) ^ 2 = 1 := by simpa using hsr2
          have hri3 : (DihedralGroup.r i) ^ 3 = 1 := by
            rw [DihedralGroup.r_pow]
            have h3 : (3 : ZMod 3) = 0 := ZMod.natCast_self 3
            have hzero : (i * 3 : ZMod 3) = 0 := by
              rw [mul_comm, h3]
              simp
            simp [hzero]
          have hri1 : DihedralGroup.r i = 1 := by
            have hdvd2 : orderOf (DihedralGroup.r i) ∣ 2 :=
              orderOf_dvd_iff_pow_eq_one.mpr hri2
            have hdvd3 : orderOf (DihedralGroup.r i) ∣ 3 :=
              orderOf_dvd_iff_pow_eq_one.mpr hri3
            have hdvd1 : orderOf (DihedralGroup.r i) ∣ 1 := by
              have hgcd : Nat.gcd 2 3 = 1 := by norm_num
              rw [← hgcd]
              exact Nat.dvd_gcd hdvd2 hdvd3
            have hord1 : orderOf (DihedralGroup.r i) = 1 := Nat.dvd_one.mp hdvd1
            exact orderOf_eq_one_iff.mp hord1
          exact absurd hri1 hrne
        · exact ⟨i, rfl⟩
      have hsCentK : s ∈ Subgroup.centralizer (K : Set G) :=
        (Subgroup.centralizer_le (SetLike.coe_mono hKleP)) hsP
      let Ksub : Subgroup (↥c.Hhat) := K.subgroupOf c.Hhat
      let Kbar : Subgroup (↥c.Hhat ⧸ N) := Ksub.map q
      have hKbarCent : Kbar ≤ Subgroup.centralizer ({sbar} : Set (↥c.Hhat ⧸ N)) := by
        intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        rw [Set.mem_singleton_iff.mp hb]
        rcases (Subgroup.mem_map).1 ha with ⟨k, hkKsub, rfl⟩
        have hkK : (k : G) ∈ K := (Subgroup.mem_subgroupOf).mp hkKsub
        have hks : (k : G) * s = s * (k : G) :=
          (Subgroup.mem_centralizer_iff.mp hsCentK) (k : G) hkK
        change q sH * q k = q k * q sH
        rw [← map_mul, ← map_mul]
        exact (congrArg q (Subtype.ext hks)).symm
      let A : Subgroup (DihedralGroup 3) := Kbar.map e.toMonoidHom
      have hACent : A ≤ Subgroup.centralizer ({r} : Set (DihedralGroup 3)) := by
        intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        rw [Set.mem_singleton_iff.mp hb]
        rcases (Subgroup.mem_map).1 ha with ⟨x, hxKbar, rfl⟩
        have hxCent : sbar * x = x * sbar :=
          (Subgroup.mem_centralizer_iff.mp (hKbarCent hxKbar)) sbar (by simp)
        change r * e.toMonoidHom x = e.toMonoidHom x * r
        dsimp [r]
        rw [← map_mul, ← map_mul]
        exact congrArg e.toMonoidHom hxCent
      have hAodd : Odd (Nat.card A) := by
        have hAcard : Nat.card A = Nat.card Kbar := by
          dsimp [A]
          exact (Nat.card_congr
            (Subgroup.equivMapOfInjective Kbar e.toMonoidHom e.injective).toEquiv).symm
        have hdvd1 : Nat.card Kbar ∣ Nat.card Ksub := Subgroup.card_map_dvd Ksub q
        have hKsubcard : Nat.card Ksub = Nat.card K := by
          dsimp [Ksub]
          exact Nat.card_congr
            (Subgroup.subgroupOfEquivOfLe hKleHhat).toEquiv
        have hdvd : Nat.card Kbar ∣ Nat.card K := by
          rw [hKsubcard] at hdvd1
          exact hdvd1
        rw [hAcard]
        exact Odd.of_dvd_nat hKoddNat hdvd
      rcases hr_reflection with ⟨i, hri⟩
      have hAbot : A = ⊥ := by
        refine odd_order_subgroup_eq_bot_of_centralize_sr_dihedral_three
          (A := A) i ?_ hAodd
        simpa [hri] using hACent
      have hKbarBot : Kbar = ⊥ := by
        have hleKer : Kbar ≤ (e.toMonoidHom).ker :=
          (Subgroup.map_eq_bot_iff Kbar (f := e.toMonoidHom)).mp hAbot
        have hker : (e.toMonoidHom).ker = ⊥ :=
          (MonoidHom.ker_eq_bot_iff e.toMonoidHom).mpr e.injective
        have hleBot : Kbar ≤ ⊥ := by
          rw [hker] at hleKer
          exact hleKer
        exact eq_bot_iff.mpr hleBot
      have hNmap : N.map c.Hhat.subtype = W ⊔ c.U := by
        rw [Subgroup.map_sup]
        simp [W, h26.1, twoCoreOf, oddCoreOf]
      have hKleWU : K ≤ W ⊔ c.U := by
        intro k hk
        have hkH : k ∈ c.Hhat := hKleHhat hk
        have hkSub : (⟨k, hkH⟩ : ↥c.Hhat) ∈ Ksub := hk
        have hkqker : (⟨k, hkH⟩ : ↥c.Hhat) ∈ q.ker :=
          (Subgroup.map_eq_bot_iff Ksub (f := q)).mp hKbarBot hkSub
        have hkN : (⟨k, hkH⟩ : ↥c.Hhat) ∈ N := by
          rw [QuotientGroup.ker_mk'] at hkqker
          exact hkqker
        have hkNmap : k ∈ N.map c.Hhat.subtype :=
          Subgroup.mem_map.mpr ⟨⟨k, hkH⟩, hkN, rfl⟩
        simpa [hNmap] using hkNmap
      have hdisjWU : Disjoint W c.U := by
        have hcop : Nat.Coprime (Nat.card W) (Nat.card c.U) := by
          have hWcard : Nat.card W = 4 := hWK4.card_four
          rw [hWcard]
          change Nat.Coprime (2 ^ 2) (Nat.card c.U)
          exact (Nat.coprime_two_left.mpr hUodd).pow_left 2
        exact Subgroup.disjoint_of_coprime_natCard hcop
      have hWUcomm : ∀ w : G, w ∈ W → ∀ u : G, u ∈ c.U → w * u = u * w := by
        have hWnormJoin' : W ⊔ c.U ≤ Subgroup.normalizer (W : Set G) :=
          hWUleHhat.trans (le_normalizer_of_isNormalIn hWnormHhat)
        have hUnormJoin' : W ⊔ c.U ≤ Subgroup.normalizer (c.U : Set G) :=
          hWUleHhat.trans (le_normalizer_of_isNormalIn hUnormHhat)
        have hcommWU : ⁅W, c.U⁆ = ⊥ :=
          commutator_eq_bot_of_normal_subgroupOf_disjoint W c.U
            hWnormJoin' hUnormJoin' hdisjWU
        have hWleCentU : W ≤ Subgroup.centralizer (c.U : Set G) :=
          (Subgroup.commutator_eq_bot_iff_le_centralizer
            (H₁ := W) (H₂ := c.U)).1 hcommWU
        intro w hwW u huU
        exact ((Subgroup.mem_centralizer_iff.mp (hWleCentU hwW)) u huU).symm
      have hKleU : K ≤ c.U :=
        odd_order_subgroup_le_of_le_sup_of_twoPGroup W c.U K
          hWnorm hUnorm hWUcomm hKleWU hWp hKoddNat hdisjWU
      have hCentK : ∀ k : G, k ∈ K → k * c.t = c.t * k := by
        intro k hk
        exact (Subgroup.mem_centralizer_iff.mp htCentU) k (hKleU hk)
      have hcomm : ⁅K, Subgroup.zpowers c.t⁆ = ⊥ :=
        (centralizes_iff_commutator_eq_bot c.t (K := K)).1 hCentK
      exact hcommK hcomm

/-- If an involution centralizes an odd-order subgroup, the elements it
inverts inside that subgroup are trivial. -/
private theorem invertedElements_eq_singleton_one_of_centralizes
    {G : Type u} [Group G] [Finite G] (X : Subgroup G) {s : G}
    (_hs : IsInvolution s)
    (hcent : s ∈ Subgroup.centralizer (X : Set G))
    (hodd : Nat.Coprime 2 (Nat.card (↥X))) :
    invertedElements X s = ({1} : Set G) := by
  classical
  ext x
  constructor
  · intro hx
    have hxX : x ∈ X := hx.1
    have hcomm : s * x = x * s := by
      exact ((Subgroup.mem_centralizer_iff (g := s) (s := (X : Set G))).1
        hcent x hxX).symm
    have hfix : s * x * s⁻¹ = x := by
      calc
        s * x * s⁻¹ = x * s * s⁻¹ := by rw [hcomm]
        _ = x := by simp
    have hxinv : s * x * s⁻¹ = x⁻¹ := hx.2
    have hxeq : x = x⁻¹ := by
      calc
        x = s * x * s⁻¹ := hfix.symm
        _ = x⁻¹ := hxinv
    have hx2 : x * x = 1 := by
      nth_rw 1 [hxeq]
      simp
    have hxsq : x ^ 2 = 1 := by simpa [pow_two] using hx2
    have hmem : (⟨x, hxX⟩ : ↥X) ^ 2 = 1 := by
      apply Subtype.ext
      simpa using hxsq
    have hone : (⟨x, hxX⟩ : ↥X) = 1 :=
      eq_one_of_sq_eq_one_of_coprime_two (G := ↥X) hodd hmem
    exact congrArg Subtype.val hone
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    rw [invertedElements]
    exact ⟨X.one_mem, by simp⟩

/-- If a reflection's inverted set inside `U` is trivial, then `⊥` is the
subgroup witnessing the Hall clause of `FirstCase`. -/
private theorem bot_inverted_Hall_of_eq_singleton
    {G : Type u} [Group G] [Finite G] (c : CentralizerSetup G) {s : G}
    (h : invertedElements c.U s = ({1} : Set G)) :
    ∃ I : Subgroup G, IsInvertedSubgroup I c.U s ∧ IsHallIn I c.FU := by
  refine ⟨⊥, ?_, ?_⟩
  · rw [IsInvertedSubgroup]
    ext x
    simp [h]
  · exact ⟨bot_le, by simp⟩

private theorem reflection_dihedralModel_is_sr
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) {s : G} (hs : c.IsReflection s)
    (hm2 : 2 ≤ c.m) (e : c.S ≃* DihedralGroup (2 ^ c.m)) :
    ∃ i : ZMod (2 ^ c.m),
      e ⟨s, hs.1⟩ = DihedralGroup.sr i := by
  classical
  let S' : Subgroup G := c.S
  let S0' : Subgroup (↥S') := c.S0.subgroupOf S'
  let A : Subgroup (DihedralGroup (2 ^ c.m)) := S0'.map e.toMonoidHom
  have hcardS0' : Nat.card (↥S0') = 2 ^ c.m := by
    have hcardS : Nat.card (↥S') = 2 * 2 ^ c.m := by
      calc
        Nat.card (↥S') = Nat.card (DihedralGroup (2 ^ c.m)) := Nat.card_congr e.toEquiv
        _ = 2 * 2 ^ c.m := DihedralGroup.nat_card
    have hsub : Nat.card (↥S0') = Nat.card (↥c.S0) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe c.S0_le_S).toEquiv
    have h1 : Nat.card (↥S') = 2 * Nat.card (↥S0') := by
      have hraw := c.S_index_two
      change Nat.card (↥S') = 2 * Nat.card (↥c.S0) at hraw
      rw [← hsub] at hraw
      exact hraw
    rw [hcardS] at h1
    omega
  have hcardA : Nat.card (↥A) = 2 ^ c.m := by
    change Nat.card (↥(S0'.map e.toMonoidHom)) = 2 ^ c.m
    rw [Subgroup.card_map_of_injective e.injective, hcardS0']
  have hcycS0' : IsCyclic (↥S0') := by
    have e0 := Subgroup.subgroupOfEquivOfLe c.S0_le_S
    have hc0 : IsCyclic (↥(c.S0.subgroupOf (c.S : Subgroup G))) :=
      e0.isCyclic.mpr c.S0_cyclic
    simpa [S0', S'] using hc0
  have hcycA : IsCyclic (↥A) := by
    let em : (↥S0') ≃* (↥A) :=
      Subgroup.equivMapOfInjective S0' e.toMonoidHom e.injective
    exact isCyclic_of_surjective em em.surjective
  have hsnotA : e ⟨s, hs.1⟩ ∉ A := by
    intro hA
    rcases Subgroup.mem_map.mp hA with ⟨x, hx, hxe⟩
    have hxs : x = ⟨s, hs.1⟩ := by
      apply e.injective
      simpa using hxe
    have hs0 : s ∈ c.S0 := by
      have : ⟨s, hs.1⟩ ∈ S0' := hxs ▸ hx
      exact this
    exact hs.2 hs0
  have hArot : A = Subgroup.zpowers (DihedralGroup.r 1) := by
    exact dihedral_cyclic_index_two_eq_rotation hm2 A hcycA hcardA
  have hnotrot : e ⟨s, hs.1⟩ ∉ Subgroup.zpowers (DihedralGroup.r 1) := by
    intro h
    apply hsnotA
    rw [hArot]
    exact h
  rcases dihedralGroup_cases (e ⟨s, hs.1⟩) with ⟨i, hi⟩ | ⟨i, hi⟩
  · exfalso
    apply hnotrot
    rw [hi]
    exact r_mem_zpowers_r_one (n := 2 ^ c.m) i
  · exact ⟨i, hi⟩

/-- `t` centralizes every element of the fixed Sylow subgroup. -/
private theorem t_centralizes_S
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) {x : G} (hxS : x ∈ (c.S : Subgroup G)) :
    c.t * x = x * c.t := by
  have hxH : x ∈ c.H := centralizerSetup_S_le_H c hxS
  rw [c.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff] at hxH
  exact hxH.symm

/-- `U = O(H)` is normal in `H`. -/
private theorem oddCoreOf_isNormalIn
    {G : Type u} [Group G] (H : Subgroup G) :
    IsNormalIn (oddCoreOf H) H := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨y, _hy, rfl⟩
    exact y.2
  · intro h hh x hx
    rcases (Subgroup.mem_map).1 hx with ⟨y, hy, rfl⟩
    refine Subgroup.mem_map.mpr
      ⟨(⟨h, hh⟩ : ↥H) * y * (⟨h, hh⟩ : ↥H)⁻¹, ?_, by simp⟩
    exact (pPrimeCore_normal (p := 2) (G := ↥H)).conj_mem
      y hy (⟨h, hh⟩ : ↥H)

/-- Elements of `S` normalize the `p`-core of `U`. -/
private theorem conj_mem_qCoreOf_of_mem_S
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) {u y : G} {p : ℕ}
    (huS : u ∈ (c.S : Subgroup G))
    (hy : y ∈ qCoreOf c.U p) :
    u * y * u⁻¹ ∈ qCoreOf c.U p := by
  classical
  have huH : u ∈ c.H := centralizerSetup_S_le_H c huS
  have hUnormH : IsNormalIn c.U c.H := by
    change IsNormalIn (oddCoreOf c.H) c.H
    exact oddCoreOf_isNormalIn c.H
  rcases (Subgroup.mem_map).1 hy with ⟨z, hz, rfl⟩
  let U' : Subgroup (↥c.H) := c.U.subgroupOf c.H
  have hU'norm : U'.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (H := c.H) (N := c.U)
      (le_normalizer_of_isNormalIn hUnormH)
  let eU : U' ≃* c.U := Subgroup.subgroupOfEquivOfLe hUnormH.1
  let φ : MulAut U' := MulAut.conjNormal (⟨u, huH⟩ : ↥c.H)
  let ψ : MulAut (↥c.U) := (eU.symm).trans (φ.trans eU)
  have hchar : (pCore p (↥c.U)).Characteristic := inferInstance
  have hcomap : pCore p (↥c.U) ≤ (pCore p (↥c.U)).comap ψ.toMonoidHom :=
    (Subgroup.characteristic_iff_le_comap.mp hchar) ψ
  have hψz : ψ z ∈ pCore p (↥c.U) := hcomap hz
  have hψz_val : (ψ z : G) = u * (z : G) * u⁻¹ := by
    dsimp [ψ, eU, φ]
    have hφ : (φ (eU.symm z) : ↥c.H) =
        (⟨u, huH⟩ : ↥c.H) * (eU.symm z) * (⟨u, huH⟩ : ↥c.H)⁻¹ :=
      MulAut.conjNormal_apply (⟨u, huH⟩ : ↥c.H) (eU.symm z)
    calc
      (eU (φ (eU.symm z)) : G) = (φ (eU.symm z) : ↥c.H) := rfl
      _ = u * (eU.symm z : G) * u⁻¹ := congrArg Subtype.val hφ
      _ = u * (z : G) * u⁻¹ := by
        have hz : (eU.symm z : G) = (z : G) := by
          dsimp [eU]
          rfl
        rw [hz]
  exact Subgroup.mem_map.mpr ⟨ψ z, hψz, hψz_val⟩

/-- If `u ∈ S` conjugates a reflection `s` into `{s, t s}`, then
conjugation by `u` preserves the fixed subgroup `X = C_{O_p(U)}(s)`. -/
private theorem fixed_core_conj_of_conj_s_in_pair
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) {s u : G} (_hs : c.IsReflection s)
    (huS : u ∈ (c.S : Subgroup G)) {p : ℕ}
    (hpair : u * s * u⁻¹ = s ∨ u * s * u⁻¹ = c.t * s)
    {y : G} (hyX : y ∈ centralizerIn (qCoreOf c.U p) s) :
    u * y * u⁻¹ ∈ centralizerIn (qCoreOf c.U p) s := by
  classical
  have hyQ : y ∈ qCoreOf c.U p := hyX.1
  have huQ : u * y * u⁻¹ ∈ qCoreOf c.U p :=
    conj_mem_qCoreOf_of_mem_S c huS hyQ
  refine Subgroup.mem_inf.mpr ⟨huQ, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hzs : y * s = s * y :=
    (Subgroup.mem_centralizer_singleton_iff.mp hyX.2)
  have hzt : y * c.t = c.t * y := by
    have htCentQ : c.t ∈ Subgroup.centralizer (qCoreOf c.U p : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hwH : w ∈ c.H :=
        (Subgroup.map_subtype_le (H := c.H) (pPrimeCore 2 c.H))
          (qCoreOf_le c.U p hw)
      rw [c.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff] at hwH
      exact hwH
    exact (Subgroup.mem_centralizer_iff.mp htCentQ) y hyQ
  have hzfixs : s * y * s⁻¹ = y := by
    calc
      s * y * s⁻¹ = y * s * s⁻¹ := by rw [hzs]
      _ = y := by simp
  have hzfixt : c.t * y * c.t⁻¹ = y := by
    calc
      c.t * y * c.t⁻¹ = y * c.t * c.t⁻¹ := by rw [hzt]
      _ = y := by simp
  have hw : u⁻¹ * s * u = s ∨ u⁻¹ * s * u = c.t * s := by
    rcases hpair with hcase | hcase
    · left
      have huCent : u * s = s * u := by
        calc
          u * s = (u * s * u⁻¹) * u := by group
          _ = s * u := by rw [hcase]
      calc
        u⁻¹ * s * u = u⁻¹ * (s * u) := by group
        _ = u⁻¹ * (u * s) := by rw [huCent]
        _ = s := by group
    · right
      have huInvS : u⁻¹ ∈ (c.S : Subgroup G) :=
        (c.S : Subgroup G).inv_mem huS
      have htuInv : c.t * u⁻¹ = u⁻¹ * c.t := t_centralizes_S c huInvS
      have hs' : s = c.t * (u⁻¹ * s * u) := by
        calc
          s = u⁻¹ * (u * s * u⁻¹) * u := by group
          _ = u⁻¹ * (c.t * s) * u := by rw [hcase]
          _ = (u⁻¹ * c.t) * s * u := by group
          _ = (c.t * u⁻¹) * s * u := by rw [← htuInv]
          _ = c.t * (u⁻¹ * s * u) := by
            group
      have htt : c.t * c.t = 1 := by
        rw [← pow_two, c.t_involution.2]
      calc
        u⁻¹ * s * u = c.t * (c.t * (u⁻¹ * s * u)) := by
          rw [← mul_assoc, htt]
          simp
        _ = c.t * s := by rw [← hs']
  have hfix : s * (u * y * u⁻¹) * s⁻¹ = u * y * u⁻¹ := by
    rcases hw with hws | hwts
    · calc
        s * (u * y * u⁻¹) * s⁻¹ =
            u * ((u⁻¹ * s * u) * y * (u⁻¹ * s * u)⁻¹) * u⁻¹ := by
              group
        _ = u * (s * y * s⁻¹) * u⁻¹ := by rw [hws]
        _ = u * y * u⁻¹ := by rw [hzfixs]
    · calc
        s * (u * y * u⁻¹) * s⁻¹ =
            u * ((u⁻¹ * s * u) * y * (u⁻¹ * s * u)⁻¹) * u⁻¹ := by
              group
        _ = u * ((c.t * s) * y * (c.t * s)⁻¹) * u⁻¹ := by rw [hwts]
        _ = u * (c.t * (s * y * s⁻¹) * c.t⁻¹) * u⁻¹ := by group
        _ = u * (c.t * y * c.t⁻¹) * u⁻¹ := by rw [hzfixs]
        _ = u * y * u⁻¹ := by rw [hzfixt]
  have hcomm : s * (u * y * u⁻¹) = (u * y * u⁻¹) * s := by
    calc
      s * (u * y * u⁻¹) = (s * (u * y * u⁻¹) * s⁻¹) * s := by group
      _ = (u * y * u⁻¹) * s := by rw [hfix]
  exact hcomm.symm

/-- If `x ∈ S` conjugates a reflection `s` into `{s, t s}`, then `x`
normalizes the fixed subgroup `X = C_{O_p(U)}(s)`. -/
private theorem reflection_normalizes_fixed_core_of_conj_in_pair
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) {s x : G} (hs : c.IsReflection s)
    (hxS : x ∈ (c.S : Subgroup G))
    {p : ℕ}
    (hxs : x * s * x⁻¹ = s ∨ x * s * x⁻¹ = c.t * s) :
    x ∈ Subgroup.normalizer
      (centralizerIn (qCoreOf c.U p) s : Set G) := by
  classical
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hyX
    exact fixed_core_conj_of_conj_s_in_pair c hs hxS hxs hyX
  · intro hyu
    have hxInvS : x⁻¹ ∈ (c.S : Subgroup G) :=
      (c.S : Subgroup G).inv_mem hxS
    have hxs' : x⁻¹ * s * (x⁻¹)⁻¹ = s ∨ x⁻¹ * s * (x⁻¹)⁻¹ = c.t * s := by
      rcases hxs with hcase | hcase
      · left
        have hxCent : x * s = s * x := by
          calc
            x * s = (x * s * x⁻¹) * x := by group
            _ = s * x := by rw [hcase]
        calc
          x⁻¹ * s * (x⁻¹)⁻¹ = x⁻¹ * s * x := by simp
          _ = x⁻¹ * (s * x) := by group
          _ = x⁻¹ * (x * s) := by rw [hxCent]
          _ = s := by group
      · right
        have htuInv : c.t * x⁻¹ = x⁻¹ * c.t := t_centralizes_S c hxInvS
        have hs' : s = c.t * (x⁻¹ * s * x) := by
          calc
            s = x⁻¹ * (x * s * x⁻¹) * x := by group
            _ = x⁻¹ * (c.t * s) * x := by rw [hcase]
            _ = (x⁻¹ * c.t) * s * x := by group
            _ = (c.t * x⁻¹) * s * x := by rw [← htuInv]
            _ = c.t * (x⁻¹ * s * x) := by
              group
        have htt : c.t * c.t = 1 := by
          rw [← pow_two, c.t_involution.2]
        calc
          x⁻¹ * s * (x⁻¹)⁻¹ = x⁻¹ * s * x := by simp
          _ = c.t * (c.t * (x⁻¹ * s * x)) := by
            rw [← mul_assoc, htt]
            simp
          _ = c.t * s := by rw [← hs']
    have hy' : x⁻¹ * (x * y * x⁻¹) * (x⁻¹)⁻¹ ∈
        centralizerIn (qCoreOf c.U p) s :=
      fixed_core_conj_of_conj_s_in_pair c hs hxInvS hxs'
        (y := x * y * x⁻¹) hyu
    have hy'' : x⁻¹ * (x * y * x⁻¹) * x = y := by group
    simpa [hy''] using hy'

/-- In the dihedral model, the half-quarter rotation conjugates a reflection
to its product with the central rotation. -/
private theorem dihedral_model_half_rotation_conj_reflection
    {m : ℕ} (hm : 2 ≤ m) (j : ZMod (2 ^ m)) :
    (DihedralGroup.r ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m))) *
      DihedralGroup.sr j *
      (DihedralGroup.r ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)))⁻¹ =
      DihedralGroup.r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) * DihedralGroup.sr j := by
  have h2 : (2 : ZMod (2 ^ m)) * ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)) =
      ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
    have hn : 2 * 2 ^ (m - 2) = 2 ^ (m - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    change ((2 : ℕ) : ZMod (2 ^ m)) * ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)) =
      ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
    rw [← Nat.cast_mul]
    exact congrArg (fun n : ℕ => (n : ZMod (2 ^ m))) hn
  calc
    (DihedralGroup.r ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m))) * DihedralGroup.sr j *
        (DihedralGroup.r ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)))⁻¹
        = DihedralGroup.sr (j - (2 : ZMod (2 ^ m)) *
            ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m))) := by
          rw [DihedralGroup.r_mul_sr, DihedralGroup.inv_r, DihedralGroup.sr_mul_r]
          congr 1
          rw [two_mul]
          abel
    _ = DihedralGroup.sr (j - ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) := by rw [h2]
    _ = DihedralGroup.r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) * DihedralGroup.sr j := by
      rw [DihedralGroup.r_mul_sr]

/-- The order of the half-quarter rotation in `DihedralGroup (2 ^ m)` is
four. -/
private theorem orderOf_half_quarter_rotation_dihedral_two_pow
    {m : ℕ} (hm : 2 ≤ m) :
    orderOf (DihedralGroup.r ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)) :
      DihedralGroup (2 ^ m)) = 4 := by
  let : NeZero (2 ^ m) := ⟨pow_ne_zero m (by norm_num)⟩
  let i : ZMod (2 ^ m) := ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m))
  let x : DihedralGroup (2 ^ m) :=
    DihedralGroup.r i
  have hpow4 : x ^ 4 = 1 := by
    dsimp [x]
    rw [DihedralGroup.r_pow]
    have h4 : (4 : ZMod (2 ^ m)) * i = 0 := by
      have hn : 4 * 2 ^ (m - 2) = 2 ^ m := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
        congr 1
        omega
      change ((4 : ℕ) : ZMod (2 ^ m)) * ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)) = 0
      rw [← Nat.cast_mul, hn, ZMod.natCast_self]
    have hzero : i * 4 = 0 := by
      rw [mul_comm, h4]
    simpa [hzero]
  have hpow2ne : x ^ 2 ≠ 1 := by
    intro h2
    dsimp [x] at h2
    rw [DihedralGroup.r_pow] at h2
    have hne0 : ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) ≠ 0 := by
      intro h
      rw [ZMod.natCast_eq_zero_iff] at h
      have hlt : 2 ^ (m - 1) < 2 ^ m := by
        exact Nat.pow_lt_pow_right (by norm_num) (by omega : m - 1 < m)
      have hpos : 0 < 2 ^ (m - 1) := pow_pos (by norm_num) _
      exact (Nat.not_dvd_of_pos_of_lt hpos hlt) h
    have h2' : DihedralGroup.r ((2 : ZMod (2 ^ m)) * i) = 1 := by
      simpa [mul_comm] using h2
    have h2'' : (2 : ZMod (2 ^ m)) * i = 0 := by
      have : DihedralGroup.r ((2 : ZMod (2 ^ m)) * i) =
          DihedralGroup.r 0 := by
        simpa using h2'
      exact (DihedralGroup.r.injEq _ _).mp this
    have hn : 2 * 2 ^ (m - 2) = 2 ^ (m - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have h2eq : (2 : ZMod (2 ^ m)) * i =
        ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
      change ((2 : ℕ) : ZMod (2 ^ m)) * ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)) =
        ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
      rw [← Nat.cast_mul]
      exact congrArg (fun n : ℕ => (n : ZMod (2 ^ m))) hn
    exact hne0 (h2eq ▸ h2'')
  have hdvd4 : orderOf x ∣ 4 := orderOf_dvd_iff_pow_eq_one.mpr hpow4
  have hxne1 : x ≠ 1 := by
    intro h
    apply hpow2ne
    -- x = 1 → x^2 = 1
    simpa [h]
  have hord_pos : 0 < orderOf x := orderOf_pos x
  have hord_le : orderOf x ≤ 4 := Nat.le_of_dvd (by norm_num : 0 < 4) hdvd4
  have hord_cases : orderOf x = 1 ∨ orderOf x = 2 ∨ orderOf x = 3 ∨ orderOf x = 4 := by
    omega
  rcases hord_cases with h1 | h2 | h3 | h4
  · exfalso
    apply hxne1
    exact orderOf_eq_one_iff.mp h1
  · exfalso
    apply hpow2ne
    simpa [h2] using (pow_orderOf_eq_one x)
  · exfalso
    rw [h3] at hdvd4
    norm_num at hdvd4
  · exact h4

/-- For a dihedral Sylow subgroup of order at least eight, there is an
element of `S` conjugating the reflection `s` to `t s`, with order four. -/
private theorem exists_S_element_conj_s_to_ts_of_large
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) {s : G} (hs : c.IsReflection s)
    (hm2 : 2 ≤ c.m) :
    ∃ x : G, x ∈ (c.S : Subgroup G) ∧
      x * s * x⁻¹ = c.t * s ∧ orderOf x = 4 := by
  classical
  rcases c.dihedralEquiv with ⟨e⟩
  rcases reflection_dihedralModel_is_sr c hs hm2 e with ⟨j, hsj⟩
  have hss : e ⟨s, hs.1⟩ = DihedralGroup.sr j := hsj
  let xS : c.S := e.symm (DihedralGroup.r
    ((2 ^ (c.m - 2) : ℕ) : ZMod (2 ^ c.m)))
  let x : G := (xS : G)
  refine ⟨x, xS.2, ?_, ?_⟩
  · have htsS : c.t * s ∈ (c.S : Subgroup G) :=
      (c.S : Subgroup G).mul_mem (c.S0_le_S c.t_mem_S0) hs.1
    have hxS' : x * s * x⁻¹ ∈ (c.S : Subgroup G) :=
      (c.S : Subgroup G).mul_mem ((c.S : Subgroup G).mul_mem xS.2 hs.1)
        ((c.S : Subgroup G).inv_mem xS.2)
    have hxs_model : e ⟨x * s * x⁻¹, hxS'⟩ =
        DihedralGroup.r ((2 ^ (c.m - 1) : ℕ) : ZMod (2 ^ c.m)) *
          DihedralGroup.sr j := by
      change e ⟨(xS : G) * s * (xS : G)⁻¹, hxS'⟩ = _
      change e (⟨(xS : G), xS.2⟩ * ⟨s, hs.1⟩ *
        ⟨(xS : G), xS.2⟩⁻¹) = _
      rw [map_mul, map_mul, map_inv]
      have hxs : e xS = DihedralGroup.r
          ((2 ^ (c.m - 2) : ℕ) : ZMod (2 ^ c.m)) := by
        dsimp [xS]
        simp
      rw [hxs, hss]
      exact dihedral_model_half_rotation_conj_reflection hm2 j
    have ht_model : e ⟨c.t * s, htsS⟩ =
        DihedralGroup.r ((2 ^ (c.m - 1) : ℕ) : ZMod (2 ^ c.m)) *
          DihedralGroup.sr j := by
      have htc : (⟨c.t, c.S0_le_S c.t_mem_S0⟩ : c.S) * ⟨s, hs.1⟩ =
          ⟨c.t * s, htsS⟩ := by
        apply Subtype.ext
        rfl
      rw [← htc, map_mul]
      have htS : e ⟨c.t, c.S0_le_S c.t_mem_S0⟩ =
          DihedralGroup.r ((2 ^ (c.m - 1) : ℕ) : ZMod (2 ^ c.m)) := by
        have hconv : (2 ^ (c.m - 1) : ZMod (2 ^ c.m)) =
            ((2 ^ (c.m - 1) : ℕ) : ZMod (2 ^ c.m)) :=
          (Nat.cast_pow (α := ZMod (2 ^ c.m)) 2 (c.m - 1)).symm
        have htS0 : e ⟨c.t, c.S0_le_S c.t_mem_S0⟩ =
            DihedralGroup.r (2 ^ (c.m - 1) : ZMod (2 ^ c.m)) := by
          have htSub : ⟨c.t, c.S0_le_S c.t_mem_S0⟩ =
              e.symm (DihedralGroup.r (2 ^ (c.m - 1) : ZMod (2 ^ c.m))) := by
            apply Subtype.ext
            exact centralizerSetup_t_eq_dihedralCentralRotation c hm2 e
          exact (congrArg e htSub).trans (e.apply_symm_apply _)
        rw [← hconv]
        exact htS0
      rw [htS, hss]
    exact congrArg Subtype.val (e.injective (hxs_model.trans ht_model.symm))
  · change orderOf (xS : G) = 4
    have hordSub : orderOf (xS : G) = orderOf xS :=
      orderOf_injective (c.S : Subgroup G).subtype
        (c.S : Subgroup G).subtype_injective xS
    have hord : orderOf xS = orderOf (e xS) := (e.orderOf_eq xS).symm
    rw [hordSub, hord]
    have hxs : e xS = DihedralGroup.r
        ((2 ^ (c.m - 2) : ℕ) : ZMod (2 ^ c.m)) := by
      dsimp [xS]
      simp
    rw [hxs]
    exact orderOf_half_quarter_rotation_dihedral_two_pow hm2

/-- A maximal overgroup of `N_G(X)` satisfies the Lemma 2.7 hypotheses,
whenever `N_G(X) ⊄ Ĥ` and `t ∉ E(M)`. -/
private theorem lemma27Hypothesis_of_maximal_containing_normalizer
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) {s : G} (hs : c.IsReflection s)
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (M : Subgroup G) (hMmax : IsCoatom M)
    (hXne : centralizerIn (qCoreOf c.U p) s ≠ ⊥)
    (hNleM : Subgroup.normalizer
      (centralizerIn (qCoreOf c.U p) s : Set G) ≤ M)
    (hNnotHhat : ¬ Subgroup.normalizer
      (centralizerIn (qCoreOf c.U p) s : Set G) ≤ c.Hhat)
    (htnot : c.t ∉ componentLayerOf M) :
    Lemma27Hypothesis c M := by
  classical
  let X : Subgroup G := centralizerIn (qCoreOf c.U p) s
  have hXleFU : X ≤ c.FU := by
    exact (inf_le_left : X ≤ qCoreOf c.U p).trans
      (qCoreOf_le_fittingSubgroupOf c.U p hp)
  have hXleFHhat : X ≤ fittingSubgroupOf c.Hhat :=
    hXleFU.trans (FU_le_fittingSubgroupOf_Hhat_of_centralizerStructure c
      (theorem_2_6 hmin c))
  have htN : c.t ∈ Subgroup.normalizer (X : Set G) := by
    have htCentX : c.t ∈ Subgroup.centralizer (X : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have htCentQ : c.t ∈ Subgroup.centralizer (qCoreOf c.U p : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        have hwH : w ∈ c.H :=
          (Subgroup.map_subtype_le (H := c.H) (pPrimeCore 2 c.H))
            (qCoreOf_le c.U p hw)
        rw [c.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff] at hwH
        exact hwH
      exact (Subgroup.mem_centralizer_iff.mp htCentQ) y hy.1
    exact (Subgroup.centralizer_le_normalizer (X : Set G)) htCentX
  have hsN : s ∈ Subgroup.normalizer (X : Set G) := by
    apply reflection_normalizes_fixed_core_of_conj_in_pair c hs hs.1 (p := p)
    left
    group
  have htM : c.t ∈ M := hNleM htN
  have hsM : s ∈ M := hNleM hsN
  have htsComm : Commute c.t s := t_centralizes_S c hs.1
  have htsNe : c.t ≠ s := by
    intro h
    apply hs.2
    exact h ▸ c.t_mem_S0
  obtain ⟨V, hVleN, hVklein, htV, hsV⟩ :=
    exists_kleinFour_of_commuting_involutions_le
      ((c.S : Subgroup G) ⊓ M) c.t s c.t_involution
      (centralizerSetup_reflection_isInvolution c hs) htsNe htsComm
      ⟨c.S0_le_S c.t_mem_S0, htM⟩ ⟨hs.1, hsM⟩
  let : IsKleinFour V := hVklein
  have hVp : IsPGroup 2 V :=
    IsPGroup.of_card (G := V) (n := 2) (by simpa [hVklein.card_four])
  have hnoncyclic : ∀ P : Sylow 2 (↥M), ¬ IsCyclic P := by
    intro P
    by_contra hPcyc
    have hPcyc' : IsCyclic (↥(P : Subgroup (↥M))) := by simpa using hPcyc
    let V' : Subgroup (↥M) := V.subgroupOf M
    have hVleM : V ≤ M := by
      intro x hx
      exact (hVleN hx).2
    have hV'p : IsPGroup 2 V' := by
      let eV : V' ≃* V := Subgroup.subgroupOfEquivOfLe hVleM
      exact IsPGroup.of_equiv hVp eV.symm
    obtain ⟨Q, hVQ⟩ := IsPGroup.exists_le_sylow (G := ↥M) (p := 2) hV'p
    have hQcyc' : ¬ IsCyclic (↥(Q : Subgroup (↥M))) := by
      intro hQcyc
      have : IsCyclic (↥(Q : Subgroup (↥M))) := hQcyc
      have hV'cyc : IsCyclic (↥V') := Subgroup.isCyclic_of_le hVQ
      have hVcyc : IsCyclic (↥V) :=
        (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hVleM)).mp hV'cyc
      exact (IsKleinFour.not_isCyclic (G := V)) hVcyc
    obtain ⟨g, hg⟩ := @MulAction.IsPretransitive.exists_smul_eq (↥M)
      (Sylow 2 (↥M)) inferInstance inferInstance Q P
    have hQP : (Q : Subgroup (↥M)).map (MulAut.conj g).toMonoidHom =
        (P : Subgroup (↥M)) := by
      have hset : MulAut.conj g • (Q : Set (↥M)) = (P : Set (↥M)) := by
        rw [← Sylow.coe_smul, hg]
      ext x
      rw [Subgroup.mem_map]
      change (∃ y ∈ (Q : Set (↥M)), (MulAut.conj g).toMonoidHom y = x) ↔
        x ∈ (P : Set (↥M))
      rw [← hset]
      rfl
    let eQP : (↥(Q : Subgroup (↥M))) ≃* ↥(P : Subgroup (↥M)) :=
      (Subgroup.equivMapOfInjective (Q : Subgroup (↥M)) (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr hQP)
    have hQcyc : IsCyclic (↥(Q : Subgroup (↥M))) :=
      (MulEquiv.isCyclic eQP).mpr hPcyc'
    exact hQcyc' hQcyc
  by_cases hm1 : c.m = 1
  · rcases c.dihedralEquiv with ⟨e⟩
    have hScard : Nat.card (↥(c.S : Subgroup G)) = 2 * 2 ^ c.m :=
      (Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card
    have hS4 : Nat.card (c.S : Subgroup G) = 4 := by
      rw [hm1] at hScard
      norm_num at hScard ⊢
      exact hScard
    exact ⟨hMmax.ne_top, ⟨X, hXne, hXleFHhat, hNleM⟩,
      (by intro hMle; exact hNnotHhat (fun x hx => hMle (hNleM hx))),
      htnot, hnoncyclic, Or.inr (Or.inl hS4)⟩
  · have hm2 : 2 ≤ c.m := by
      have h := c.one_le_m
      omega
    obtain ⟨x, hxS, hxs, hxorder4⟩ :=
      exists_S_element_conj_s_to_ts_of_large c hs hm2
    have hxN : x ∈ Subgroup.normalizer (X : Set G) :=
      reflection_normalizes_fixed_core_of_conj_in_pair c hs hxS (p := p)
        (Or.inr hxs)
    have hxM : x ∈ M := hNleM hxN
    let N : Subgroup G := (c.S : Subgroup G) ⊓ M
    have hxN' : x ∈ N := ⟨hxS, hxM⟩
    have hxNotV : x ∉ V := by
      intro hxV
      have hx2 : x ^ 2 = 1 := by
        have h := IsKleinFour.mul_self (⟨x, hxV⟩ : V)
        simpa [pow_two] using congrArg Subtype.val h
      have hdvd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hx2
      rw [hxorder4] at hdvd
      norm_num at hdvd
    have hVltN : V < N := lt_of_le_of_ne hVleN (by
      intro hVeq
      exact hxNotV (hVeq ▸ hxN'))
    let VN : Subgroup (↥N) := V.subgroupOf N
    have hVNcard : Nat.card VN = Nat.card V :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVleN).toEquiv
    have hVNindex : 2 ≤ VN.index := by
      have hne : VN ≠ ⊤ := by
        intro htop
        have hVeqN : V = N := by
          have hmapV : VN.map N.subtype = V :=
            Subgroup.map_subgroupOf_eq_of_le hVleN
          have hmapTop : (⊤ : Subgroup (↥N)).map N.subtype = N := by
            ext x
            constructor
            · rintro ⟨y, _hy, rfl⟩
              exact y.2
            · intro hx
              exact ⟨⟨x, hx⟩, trivial, rfl⟩
          calc
            V = VN.map N.subtype := hmapV.symm
            _ = (⊤ : Subgroup (↥N)).map N.subtype := by rw [htop]
            _ = N := hmapTop
        exact hxNotV (hVeqN ▸ hxN')
      have hindex_ne : VN.index ≠ 1 := by
        intro h1
        apply hne
        exact (Subgroup.index_eq_one.mp h1)
      have hindex_ne0 : VN.index ≠ 0 :=
        Subgroup.index_ne_zero_of_finite (H := VN)
      have hpos : 0 < VN.index :=
        Nat.pos_of_ne_zero hindex_ne0
      omega
    have hNcard : Nat.card N = Nat.card VN * VN.index := by
      exact (Subgroup.card_mul_index VN).symm
    have h8 : 8 ≤ Nat.card N := by
      rw [hNcard, hVNcard, hVklein.card_four]
      nlinarith
    exact ⟨hMmax.ne_top, ⟨X, hXne, hXleFHhat, hNleM⟩,
      (by intro hMle; exact hNnotHhat (fun x hx => hMle (hNleM hx))),
      htnot, hnoncyclic, Or.inl h8⟩

/-- For a proper nontrivial fixed subgroup `X = C_{O_p(U)}(s)`, the
normalizer `N_G(X)` is a proper subgroup. -/
private theorem normalizer_fixed_core_ne_top
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) {s : G} (hs : c.IsReflection s)
    {p : ℕ} (hp : p.Prime)
    (hXne : centralizerIn (qCoreOf c.U p) s ≠ ⊥) :
    Subgroup.normalizer (centralizerIn (qCoreOf c.U p) s : Set G) ≠ ⊤ := by
  classical
  let X : Subgroup G := centralizerIn (qCoreOf c.U p) s
  intro htop
  have hXnorm : X.Normal :=
    (Subgroup.normalizer_eq_top_iff (H := X)).mp htop
  have hsimple : IsSimpleGroup G := minimalCounterexample_isSimple hmin
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hsimple X hXnorm with hXbot | hXtop
  · exact hXne hXbot
  · have hUt : c.U = ⊤ := top_unique
      (hXtop ▸ ((inf_le_left : X ≤ qCoreOf c.U p).trans (qCoreOf_le c.U p)))
    have hHt : c.H = ⊤ := top_unique
      (hUt ▸ (Subgroup.map_subtype_le (H := c.H) (pPrimeCore 2 c.H)))
    have hHhatt : c.Hhat = ⊤ := top_unique (hHt ▸ c.H_le_Hhat)
    exact c.Hhat_maximal.ne_top hHhatt

/-- Per-prime dichotomy: for a reflection `s` and an odd prime `p`, the fixed
subgroup `C_{O_p(U)}(s)` is either trivial or the whole `p`-core, in the
negative `SecondCase` branch. -/
private theorem fixed_core_bot_or_top
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) {s : G} (hs : c.IsReflection s)
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (hnotSecond : ¬ SecondCase c) :
    centralizerIn (qCoreOf c.U p) s = ⊥ ∨
      centralizerIn (qCoreOf c.U p) s = qCoreOf c.U p := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let X : Subgroup G := centralizerIn (qCoreOf c.U p) s
  by_cases hbot : X = ⊥
  · exact Or.inl hbot
  · right
    by_contra htop
    have hNnot : ¬ Subgroup.normalizer (X : Set G) ≤ c.Hhat :=
      normalizer_fixed_core_not_le_Hhat hmin c hs hp hpodd hbot htop
    have hNne_top : Subgroup.normalizer (X : Set G) ≠ ⊤ :=
      normalizer_fixed_core_ne_top hmin c hs hp hbot
    rcases eq_top_or_exists_le_coatom (Subgroup.normalizer (X : Set G)) with
      htop | ⟨M, hMmax, hNleM⟩
    · exact False.elim (hNne_top htop)
    have hXleFU : X ≤ c.FU := by
      exact (inf_le_left : X ≤ qCoreOf c.U p).trans
        (qCoreOf_le_fittingSubgroupOf c.U p hp)
    have htE : c.t ∈ componentLayerOf M := by
      by_contra htnot
      have hMhyp : Lemma27Hypothesis c M :=
        lemma27Hypothesis_of_maximal_containing_normalizer hmin c hs hp hpodd M
          hMmax hbot hNleM hNnot htnot
      let π : Set ℕ := primesOfOrder (fittingSubgroupOf c.Hhat)
      let Fπ' : Subgroup G := piCoreOf (fittingSubgroupOf M) πᶜ
      have hFle : ⁅M, Subgroup.zpowers c.t⁆ ≤ Fπ' :=
        (lemma_2_7 hmin c M hMhyp).1
      obtain ⟨P, hPsyl, hXP, htP⟩ :=
        exists_invariant_sylow_containing_fixed_core hmin c hs hp hpodd
      have hPp : IsPGroup p P := by
        rcases hPsyl with ⟨Q, hQeq⟩
        have hQp : IsPGroup p
            (Q : Subgroup (oddCoreOf (Subgroup.centralizer ({s} : Set G)))) :=
          Q.isPGroup'
        rw [hQeq]
        exact hQp.map (oddCoreOf (Subgroup.centralizer ({s} : Set G))).subtype
      have hPnotCent : ¬ P ≤ c.H :=
        invariant_sylow_not_le_H hmin c hs hp hpodd P hPsyl hXP htop
      let K : Subgroup G := P ⊓ Subgroup.normalizer (X : Set G)
      have hcommK : ⁅K, Subgroup.zpowers c.t⁆ ≠ ⊥ :=
        commutator_t_normalizer_fixed_core_ne_bot c hs hp hpodd P hPp hXP htP
          hPnotCent
      have hKleP : K ≤ P := inf_le_left
      have hKleM : K ≤ M := by
        intro k hk
        exact hNleM hk.2
      have hKcomm_le_Mcomm : ⁅K, Subgroup.zpowers c.t⁆ ≤ ⁅M, Subgroup.zpowers c.t⁆ :=
        Subgroup.commutator_mono hKleM le_rfl
      have hKcomm_le_P : ⁅K, Subgroup.zpowers c.t⁆ ≤ P := by
        have hZt_le_NP : Subgroup.zpowers c.t ≤ Subgroup.normalizer (P : Set G) :=
          Subgroup.zpowers_le.mpr htP
        have hcomm_tP : ⁅Subgroup.zpowers c.t, P⁆ ≤ P :=
          (Subgroup.le_normalizer_iff_commutator_le_right).mp hZt_le_NP
        calc
          ⁅K, Subgroup.zpowers c.t⁆ = ⁅Subgroup.zpowers c.t, K⁆ :=
            Subgroup.commutator_comm _ _
          _ ≤ ⁅Subgroup.zpowers c.t, P⁆ := Subgroup.commutator_mono le_rfl hKleP
          _ ≤ P := hcomm_tP
      let C : Subgroup G := ⁅K, Subgroup.zpowers c.t⁆
      have hCleP : C ≤ P := by
        simpa [C] using hKcomm_le_P
      have hKcomm_p : IsPGroup p (↥C) :=
        IsPGroup.to_le hPp hCleP
      have hKcomm_p_dvd : p ∣ Nat.card C := by
        rcases hKcomm_p.exists_card_eq with ⟨n, hn⟩
        have hnpos : 0 < n := by
          by_contra hnpos0
          have hn0 : n = 0 := by omega
          have hcard : Nat.card C = 1 := by
            simpa [hn0] using hn
          exact hcommK ((Subgroup.eq_bot_iff_card
            (H := C)).2 hcard)
        rw [hn]
        refine ⟨p ^ (n - 1), ?_⟩
        rw [← pow_succ']
        congr 1
        omega
      have hXp : IsPGroup p X :=
        IsPGroup.to_le (qCoreOf_isPGroup c.U p) (inf_le_left : X ≤ qCoreOf c.U p)
      have hXp_dvd : p ∣ Nat.card X := by
        rcases hXp.exists_card_eq with ⟨n, hn⟩
        have hnpos : 0 < n := by
          by_contra hnpos0
          have hn0 : n = 0 := by omega
          have hcard : Nat.card X = 1 := by simpa [hn0] using hn
          exact hbot ((Subgroup.eq_bot_iff_card (H := X)).2 hcard)
        rw [hn]
        refine ⟨p ^ (n - 1), ?_⟩
        rw [← pow_succ']
        congr 1
        omega
      have hXleFHhat : X ≤ fittingSubgroupOf c.Hhat := by
        exact hXleFU.trans (FU_le_fittingSubgroupOf_Hhat_of_centralizerStructure c
          (theorem_2_6 hmin c))
      have hpdvdF : p ∣ Nat.card (fittingSubgroupOf c.Hhat) :=
        hXp_dvd.trans (Subgroup.card_dvd_of_le hXleFHhat)
      have hpπ : p ∈ π := by
        dsimp [π, primesOfOrder]
        exact Nat.mem_primeFactors.mpr
          ⟨hp, hpdvdF, Nat.card_pos.ne'⟩
      have hKleFpi' : C ≤ Fπ' :=
        by simpa [C] using hKcomm_le_Mcomm.trans hFle
      have hpdvdFpi' : p ∣ Nat.card Fπ' :=
        hKcomm_p_dvd.trans (Subgroup.card_dvd_of_le hKleFpi')
      have hpπ' : p ∈ πᶜ := by
        have hpF : p ∈ (Nat.card Fπ').primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hp, hpdvdFpi', Nat.card_pos.ne'⟩
        exact piCoreOf_primeDivisors (fittingSubgroupOf M) πᶜ p hpF
      exact (Set.mem_compl_iff (s := π) p).1 hpπ' hpπ
    exact False.elim (hnotSecond ⟨M, hMmax,
      (by intro hMle; exact hNnot (fun x hx => hMle (hNleM hx))),
      htE, X, hbot, hXleFU, hNleM⟩)

/-- The odd core `U = O(C_G(t))` has odd order. -/
private theorem card_U_odd
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) : Odd (Nat.card (↥c.U)) := by
  change Odd (Nat.card (↥((pPrimeCore 2 c.H).map c.H.subtype)))
  rw [Subgroup.card_map_of_injective c.H.subtype_injective]
  exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := c.H))

/-- The two-core of an odd-order subgroup is trivial. -/
private theorem twoCoreOf_eq_bot_of_odd_card
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (hodd : Odd (Nat.card (↥H))) :
    twoCoreOf H = ⊥ := by
  classical
  have hq : qCoreOf H 2 = twoCoreOf H := by
    rw [qCoreOf_eq_piCoreOf_singleton H 2 Nat.prime_two, twoCoreOf_eq_piCoreOf_2]
  have h2 : IsPGroup 2 (twoCoreOf H) := by
    rw [← hq]
    exact qCoreOf_isPGroup H 2
  obtain ⟨n, hn⟩ := h2.exists_card_eq
  have hdvd : Nat.card (twoCoreOf H) ∣ Nat.card H := by
    rw [← hq]
    exact Subgroup.card_dvd_of_le (qCoreOf_le H 2)
  have hnot : ¬ 2 ∣ Nat.card H := hodd.not_two_dvd_nat
  have hn0 : n = 0 := by
    by_contra hn0
    have h2dvd : 2 ∣ 2 ^ n := ⟨2 ^ (n - 1), by
      rw [← pow_succ']
      congr 1
      omega⟩
    exact hnot (h2dvd.trans (hn ▸ hdvd))
  have hcard : Nat.card (twoCoreOf H) = 1 := by
    simpa [hn0] using hn
  exact Subgroup.eq_bot_of_card_eq (H := twoCoreOf H) hcard

/-- If a reflection has no fixed points in an odd `p`-core of `U`, it
inverts that core elementwise. -/
private theorem inverted_qCore_eq_qCore_of_centralizer_bot
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) {s : G} (hs : c.IsReflection s)
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (hbot : centralizerIn (qCoreOf c.U p) s = ⊥) :
    invertedElements (qCoreOf c.U p) s = (qCoreOf c.U p : Set G) := by
  classical
  let Q : Subgroup G := qCoreOf c.U p
  have hsN : s ∈ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact conj_mem_qCoreOf_of_mem_S c hs.1 hx
    · intro hx
      have hsInvS : s⁻¹ ∈ (c.S : Subgroup G) :=
        (c.S : Subgroup G).inv_mem hs.1
      have hx' : s⁻¹ * (s * x * s⁻¹) * (s⁻¹)⁻¹ ∈ Q :=
        conj_mem_qCoreOf_of_mem_S c hsInvS hx
      have hxsimp : s⁻¹ * (s * x * s⁻¹) * (s⁻¹)⁻¹ = x := by group
      rw [hxsimp] at hx'
      exact hx'
  let phi : MulAut Q := Q.normalizerMonoidHom ⟨s, hsN⟩
  have hsInv : IsInvolution s := centralizerSetup_reflection_isInvolution c hs
  have hss : s * s = 1 := by simpa [pow_two] using hsInv.2
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hphiInvolutive : Function.Involutive phi := by
    intro y
    apply Subtype.ext
    simp only [phi, Subgroup.normalizerMonoidHom_apply_apply_coe]
    rw [hsinv]
    calc
      s * (s * (y : G) * s) * s = (s * s) * (y : G) * (s * s) := by group
      _ = (y : G) := by rw [hss]; simp
  have hphiFixedPointFree : MonoidHom.FixedPointFree phi := by
    intro y hyfix
    apply Subtype.ext
    have hyconj : s * (y : G) * s⁻¹ = (y : G) := by
      simpa [phi, Subgroup.normalizerMonoidHom_apply_apply_coe] using
        congrArg Subtype.val hyfix
    have hycomm : s * (y : G) = (y : G) * s := by
      have hmul := congrArg (fun z : G => z * s) hyconj
      simpa [mul_assoc] using hmul
    have hyC : (y : G) ∈ centralizerIn Q s := by
      change (y : G) ∈ Q ⊓ Subgroup.centralizer ({s} : Set G)
      exact ⟨y.property, by
        exact Subgroup.mem_centralizer_singleton_iff.mpr hycomm.symm⟩
    have hybot : (y : G) ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact hyC
    exact Subgroup.mem_bot.mp hybot
  have hmem_inv : ∀ x : G, x ∈ Q → x ∈ invertedElements Q s := by
    intro x hx
    have hxinv := congrFun
      (hphiFixedPointFree.coe_eq_inv_of_involutive hphiInvolutive)
      (⟨x, hx⟩ : Q)
    change x ∈ Q ∧ s * x * s⁻¹ = x⁻¹
    exact ⟨hx, by
      simpa [phi, Subgroup.normalizerMonoidHom_apply_apply_coe] using
        congrArg Subtype.val hxinv⟩
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hx
    exact hmem_inv x hx

/-- An element inverted by a reflection centralizes every odd `p`-core of
`U`, under the per-prime centralizer dichotomy. -/
private theorem mem_centralizer_qCoreOf_of_mem_invertedElements
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) {s u : G} (hs : c.IsReflection s)
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (huU : u ∈ c.U) (huinv : s * u * s⁻¹ = u⁻¹)
    (hcase : centralizerIn (qCoreOf c.U p) s = ⊥ ∨
      centralizerIn (qCoreOf c.U p) s = qCoreOf c.U p) :
    u ∈ Subgroup.centralizer (qCoreOf c.U p : Set G) := by
  classical
  let Q : Subgroup G := qCoreOf c.U p
  have hsQall : (∀ x : G, x ∈ Q → s * x * s⁻¹ = x) ∨
      (∀ x : G, x ∈ Q → s * x * s⁻¹ = x⁻¹) := by
    rcases hcase with hbot | htop
    · right
      intro x hx
      have hxinv : x ∈ invertedElements Q s := by
        rw [inverted_qCore_eq_qCore_of_centralizer_bot c hs hp hpodd hbot]
        exact hx
      exact hxinv.2
    · left
      intro x hx
      have hxcent : x ∈ centralizerIn Q s := by
        rw [htop]
        exact hx
      have hcomm : x * s = s * x :=
        Subgroup.mem_centralizer_singleton_iff.mp hxcent.2
      calc
        s * x * s⁻¹ = x * s * s⁻¹ := by rw [hcomm]
        _ = x := by simp
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have hqQ : q ∈ Q := hq
  have huQ : u * q * u⁻¹ ∈ Q :=
    (qCoreOf_normal_in c.U p).2 u huU q hqQ
  have hsu : s * u * s⁻¹ = u⁻¹ := huinv
  have hsuinv : s * u⁻¹ * s⁻¹ = u := by
    calc
      s * u⁻¹ * s⁻¹ = (s * u * s⁻¹)⁻¹ := by group
      _ = (u⁻¹)⁻¹ := by rw [hsu]
      _ = u := by simp
  have hsq : s * (u * q * u⁻¹) * s⁻¹ = u⁻¹ * (s * q * s⁻¹) * u := by
    calc
      s * (u * q * u⁻¹) * s⁻¹ =
          (s * u * s⁻¹) * (s * q * s⁻¹) * (s * u⁻¹ * s⁻¹) := by group
      _ = u⁻¹ * (s * q * s⁻¹) * u := by rw [hsu, hsuinv]
  have hmid : u⁻¹ * q * u = u * q * u⁻¹ := by
    rcases hsQall with hfix | hinv
    · have hconj : s * (u * q * u⁻¹) * s⁻¹ = u * q * u⁻¹ :=
        hfix (u * q * u⁻¹) huQ
      calc
        u⁻¹ * q * u = u⁻¹ * (s * q * s⁻¹) * u := by rw [hfix q hqQ]
        _ = s * (u * q * u⁻¹) * s⁻¹ := hsq.symm
        _ = u * q * u⁻¹ := hconj
    · have hconj : s * (u * q * u⁻¹) * s⁻¹ = (u * q * u⁻¹)⁻¹ :=
        hinv (u * q * u⁻¹) huQ
      have hmid' : u * q⁻¹ * u⁻¹ = u⁻¹ * q⁻¹ * u := by
        calc
          u * q⁻¹ * u⁻¹ = (u * q * u⁻¹)⁻¹ := by group
          _ = s * (u * q * u⁻¹) * s⁻¹ := hconj.symm
          _ = u⁻¹ * (s * q * s⁻¹) * u := hsq
          _ = u⁻¹ * q⁻¹ * u := by rw [hinv q hqQ]
      have hinv' := congrArg (fun z : G => z⁻¹) hmid'
      have hmid'' : u * q * u⁻¹ = u⁻¹ * q * u := by
        calc
          u * q * u⁻¹ = (u * q⁻¹ * u⁻¹)⁻¹ := by group
          _ = (u⁻¹ * q⁻¹ * u)⁻¹ := by rw [hmid']
          _ = u⁻¹ * q * u := by group
      exact hmid''.symm
  have huq : u * (u * q * u⁻¹) * u⁻¹ = q := by
    calc
      u * (u * q * u⁻¹) * u⁻¹ = u * (u⁻¹ * q * u) * u⁻¹ := by rw [hmid]
      _ = q := by group
  have hUodd : Odd (Nat.card (↥c.U)) := card_U_odd c
  have hordOdd : Odd (orderOf u) :=
    hUodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard c.U huU)
  have hcop : Nat.Coprime 2 (orderOf u) := Nat.coprime_two_left.mpr hordOdd
  rcases exists_pow_eq_self_of_coprime (n := 2) hcop with ⟨m, hm⟩
  have hu_eq : u = (u ^ 2) ^ m := hm.symm
  have hcomm2 : u * u * q = q * (u * u) := by
    calc
      u * u * q = u * (u * q * u⁻¹) * u := by group
      _ = (u * (u * q * u⁻¹) * u⁻¹) * u * u := by group
      _ = q * (u * u) := by rw [huq]; group
  have hcomm2' : Commute (u ^ 2) q := by
    rw [pow_two]
    change (u * u) * q = q * (u * u)
    exact hcomm2
  have hpow_comm : (u ^ 2) ^ m * q = q * (u ^ 2) ^ m := hcomm2'.pow_left m
  have hcomm : u * q = q * u := by
    rw [hu_eq]
    exact hpow_comm
  exact hcomm.symm

/-- An element inverted by a reflection centralizes the full Fitting
subgroup `F(U)` in the negative `SecondCase` branch. -/
private theorem mem_centralizer_FU_of_mem_invertedElements
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) {s u : G} (hs : c.IsReflection s)
    (hnotSecond : ¬ SecondCase c)
    (huU : u ∈ c.U) (huinv : s * u * s⁻¹ = u⁻¹) :
    u ∈ Subgroup.centralizer (c.FU : Set G) := by
  have hO2 : twoCoreOf c.U = ⊥ :=
    twoCoreOf_eq_bot_of_odd_card c.U (card_U_odd c)
  have hcentOdd : ∀ p : ℕ, p.Prime → Odd p →
      u ∈ Subgroup.centralizer (qCoreOf c.U p : Set G) := by
    intro p hp hpodd
    exact mem_centralizer_qCoreOf_of_mem_invertedElements c hs hp hpodd
      huU huinv (fixed_core_bot_or_top hmin c hs hp hpodd hnotSecond)
  exact mem_centralizer_fittingSubgroupOf_of_mem_centralizer_odd_qCores_of_twoCoreOf_eq_bot
    c.U u hO2 hcentOdd

/-- In the negative `SecondCase` branch, every element of `U` inverted by a
reflection lies in `F(U)`. -/
private theorem inverted_U_le_FU
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) {s : G} (hs : c.IsReflection s)
    (hnotSecond : ¬ SecondCase c) :
    invertedElements c.U s ⊆ c.FU := by
  intro u hu
  have hcent :=
    mem_centralizer_FU_of_mem_invertedElements hmin c hs hnotSecond hu.1 hu.2
  have hUsolv : IsSolvable (↥c.U) :=
    odd_order_theorem (↥c.U) (card_U_odd c)
  exact fact_1_2_centralizer_fitting_le_fitting c.U hUsolv ⟨hu.1, hcent⟩

/-- `O_q(F(A)) ≤ O_q(A)`. -/
private theorem qCoreOf_fittingSubgroupOf_le_qCoreOf
    {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) (q : ℕ) (hq : q.Prime) :
    qCoreOf (fittingSubgroupOf A) q ≤ qCoreOf A q := by
  let F : Subgroup G := fittingSubgroupOf A
  have hQF : qCoreOf F q ≤ F := qCoreOf_le F q
  have hQFnormA : IsNormalIn (qCoreOf F q) A := by
    have h := map_characteristic_isNormalIn_of_isNormalIn (H := F) (N := A)
      (pCore q (↥F)) (pCore_characteristic (p := q))
      (fittingSubgroupOf_isNormalIn A)
    simpa [qCoreOf] using h
  exact le_qCoreOf_of_normal_isPGroup A (qCoreOf F q) q hQFnormA.1 (by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hQFnormA.1]
    exact le_normalizer_of_isNormalIn hQFnormA) (qCoreOf_isPGroup F q)

/-- Two subgroups whose prime divisors lie in complementary sets have
coprime orders. -/
private theorem natCard_coprime_of_primeDivisors_compl
    {G : Type u} [Group G] [Finite G] (K L : Subgroup G) (π : Set ℕ)
    (hKπ : ∀ q : ℕ, q ∈ (Nat.card (↥K)).primeFactors → q ∈ π)
    (hLπ : ∀ q : ℕ, q ∈ (Nat.card (↥L)).primeFactors → q ∈ πᶜ) :
    Nat.Coprime (Nat.card (↥K)) (Nat.card (↥L)) := by
  classical
  rw [Nat.coprime_iff_gcd_eq_one]
  apply le_antisymm
  · by_contra hnot
    have hgt : 1 < (Nat.card (↥K)).gcd (Nat.card (↥L)) := by
      have hpos : 0 < (Nat.card (↥K)).gcd (Nat.card (↥L)) :=
        Nat.gcd_pos_of_pos_left _ (Nat.card_pos (α := K))
      omega
    rcases Nat.exists_prime_and_dvd (by omega :
        (Nat.card (↥K)).gcd (Nat.card (↥L)) ≠ 1) with
      ⟨p, hp, hpdvd⟩
    have hpK : p ∣ Nat.card (↥K) := hpdvd.trans (Nat.gcd_dvd_left _ _)
    have hpL : p ∣ Nat.card (↥L) := hpdvd.trans (Nat.gcd_dvd_right _ _)
    have hpK' : p ∈ (Nat.card (↥K)).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hpK, Nat.card_pos.ne'⟩
    have hpL' : p ∈ (Nat.card (↥L)).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hpL, Nat.card_pos.ne'⟩
    exact hLπ p hpL' (hKπ p hpK')
  · have hpos : 0 < (Nat.card (↥K)).gcd (Nat.card (↥L)) :=
      Nat.gcd_pos_of_pos_left _ (Nat.card_pos (α := K))
    omega

/-- The join of two subgroups with trivial intersection, one normalizing
the other, has product cardinality. -/
private theorem card_sup_eq_mul_of_disjoint_of_le_normalizer
    {G : Type u} [Group G]
    (A B : Subgroup G)
    (hnormal : B ≤ Subgroup.normalizer (A : Set G))
    (hdisjoint : Disjoint A B) :
    Nat.card (A ⊔ B : Subgroup G) = Nat.card A * Nat.card B := by
  let toSup : A × B → ↥(A ⊔ B) := fun z =>
    ⟨(z.1 : G) * (z.2 : G), Subgroup.mul_mem_sup z.1.2 z.2.2⟩
  have hinjective : Function.Injective toSup := by
    intro x y hxy
    apply Subgroup.mul_injective_of_disjoint hdisjoint
    exact congrArg Subtype.val hxy
  have hsurjective : Function.Surjective toSup := by
    intro z
    have hz : (z : G) ∈ (A : Set G) * (B : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left A B hnormal]
      exact z.2
    rcases hz with ⟨a, ha, b, hb, hab⟩
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  calc
    Nat.card (A ⊔ B : Subgroup G) = Nat.card (A × B) :=
      Nat.card_congr (Equiv.ofBijective toSup ⟨hinjective, hsurjective⟩).symm
    _ = Nat.card A * Nat.card B := Nat.card_prod A B

/-- If every prime divisor of `O_π(H)` lies in `σ`, then
`O_π(H) ≤ O_σ(H)`. -/
private theorem piCoreOf_le_piCoreOf_of_primeDivisors
    {G : Type u} [Group G] [Finite G]
    (F : Subgroup G) (π σ : Set ℕ)
    (h : ∀ q : ℕ, q ∈ (Nat.card (↥(piCoreOf F π))).primeFactors → q ∈ σ) :
    piCoreOf F π ≤ piCoreOf F σ := by
  classical
  let N : Subgroup (↥F) := piCore π (↥F)
  have hNnorm : N.Normal := piCore_normal_local π
  have hNσ : ∀ q : ℕ, q ∈ (Nat.card (↥N)).primeFactors → q ∈ σ := by
    intro q hq
    have hcard : Nat.card (↥N) = Nat.card (↥(piCoreOf F π)) := by
      dsimp [N, piCoreOf]
      exact Nat.card_congr
        (Subgroup.equivMapOfInjective (piCore π (↥F)) F.subtype
          F.subtype_injective).toEquiv
    have hq' : q ∈ (Nat.card (↥(piCoreOf F π))).primeFactors := by
      rwa [hcard] at hq
    exact h q hq'
  have hNle : N ≤ piCore σ (↥F) := by
    exact le_sSup ⟨hNnorm, hNσ⟩
  change (piCore π (↥F)).map F.subtype ≤ (piCore σ (↥F)).map F.subtype
  exact Subgroup.map_mono (f := F.subtype) hNle

/-- In the negative `SecondCase` branch, the inverted subgroup of a
reflection inside `U` is exactly `O_π(F(U))` for the set `π` of inverted
prime cores, and it is a Hall subgroup of `F(U)`. -/
private theorem reflection_inverted_hall
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) {s : G} (hs : c.IsReflection s)
    (hnotSecond : ¬ SecondCase c) :
    ∃ I : Subgroup G, IsInvertedSubgroup I c.U s ∧ IsHallIn I c.FU := by
  classical
  let π : Set ℕ := {p | p.Prime ∧ Odd p ∧
    centralizerIn (qCoreOf c.U p) s = ⊥}
  let I0 : Subgroup G := Subgroup.closure (invertedElements c.U s)
  have hI0_le_inv : I0 ≤ invertedElements c.U s := by
    intro x hx
    refine Subgroup.closure_induction
      (k := invertedElements c.U s)
      (p := fun y _ => y ∈ invertedElements c.U s)
      (x := x) ?_ ?_ ?_ ?_ hx
    · intro y hy
      exact hy
    · rw [invertedElements]
      exact ⟨c.U.one_mem, by simp⟩
    · intro a b _ha _hb haI hbI
      have haU : a ∈ c.U := haI.1
      have hbU : b ∈ c.U := hbI.1
      have haF := mem_centralizer_FU_of_mem_invertedElements hmin c hs
        hnotSecond haU haI.2
      have hbFU : b ∈ c.FU := inverted_U_le_FU hmin c hs hnotSecond hbI
      have hab_comm : a * b = b * a :=
        ((Subgroup.mem_centralizer_iff.mp haF) b hbFU).symm
      rw [invertedElements]
      refine ⟨c.U.mul_mem haU hbU, ?_⟩
      calc
        s * (a * b) * s⁻¹ = (s * a * s⁻¹) * (s * b * s⁻¹) := by group
        _ = a⁻¹ * b⁻¹ := by rw [haI.2, hbI.2]
        _ = (a * b)⁻¹ := by
          have hinv_comm : b⁻¹ * a⁻¹ = a⁻¹ * b⁻¹ := by
            have h := congrArg (fun z : G => z⁻¹) hab_comm
            simpa using h
          have h : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by group
          rw [h]
          exact hinv_comm.symm
    · intro a _ha haI
      rw [invertedElements]
      refine ⟨c.U.inv_mem haI.1, ?_⟩
      calc
        s * a⁻¹ * s⁻¹ = (s * a * s⁻¹)⁻¹ := by group
        _ = (a⁻¹)⁻¹ := by rw [haI.2]
  have hI0eq : (I0 : Set G) = invertedElements c.U s := by
    ext x
    constructor
    · intro hx
      exact hI0_le_inv hx
    · intro hx
      exact Subgroup.subset_closure hx
  have hI0leFU : I0 ≤ c.FU := by
    intro x hx
    exact inverted_U_le_FU hmin c hs hnotSecond (hI0_le_inv hx)
  let A : Subgroup G := piCoreOf c.FU π
  let B : Subgroup G := piCoreOf c.FU πᶜ
  have hFnil : Group.IsNilpotent (↥c.FU) := fittingSubgroupOf_isNilpotent c.U
  have hsup_decomp : ∀ (τ : Set ℕ),
      piCoreOf c.FU τ ≤ ⨆ p : {p // p ∈ τ}, qCoreOf c.FU p.1 := by
    intro τ
    have h := piCoreOf_le_iSup_qCoreOf_of_isNilpotent c.FU τ hFnil
    have hEq : (⨆ p : {p // p ∈ τ}, qCoreOf c.FU p.1) =
        (⨆ p ∈ τ, qCoreOf c.FU p) :=
      (iSup_subtype' (p := fun p : ℕ => p ∈ τ)
        (f := fun p : ℕ => fun _ : p ∈ τ => qCoreOf c.FU p)).symm
    rwa [← hEq] at h
  have hQ_le_I0 : ∀ p : {p // p ∈ π}, qCoreOf c.FU p.1 ≤ I0 := by
    intro p x hx
    have hpprime : p.1.Prime := p.2.1
    have hpodd : Odd p.1 := p.2.2.1
    have hbot : centralizerIn (qCoreOf c.U p.1) s = ⊥ := p.2.2.2
    have hxQU : x ∈ qCoreOf c.U p.1 :=
      qCoreOf_fittingSubgroupOf_le_qCoreOf c.U p.1 hpprime hx
    have hxInvQ : x ∈ invertedElements (qCoreOf c.U p.1) s := by
      rw [inverted_qCore_eq_qCore_of_centralizer_bot c hs hpprime hpodd hbot]
      exact hxQU
    have hxInvU : x ∈ invertedElements c.U s :=
      ⟨qCoreOf_le c.U p.1 hxQU, hxInvQ.2⟩
    exact Subgroup.subset_closure hxInvU
  have hA_le_I0 : A ≤ I0 := by
    intro x hx
    have hxsup' : x ∈ ⨆ p : {p // p ∈ π}, qCoreOf c.FU p.1 :=
      hsup_decomp π hx
    rw [Subgroup.iSup_eq_closure] at hxsup'
    refine Subgroup.closure_induction'' ?_ ?_ ?_ ?_ hxsup'
    · intro y hy
      rcases (Set.mem_iUnion).1 hy with ⟨p, hyp⟩
      exact hQ_le_I0 p hyp
    · intro y hy
      rcases (Set.mem_iUnion).1 hy with ⟨p, hyp⟩
      exact I0.inv_mem (hQ_le_I0 p hyp)
    · exact I0.one_mem
    · intro a b _ _ ha hb
      exact I0.mul_mem ha hb
  let π' : Set ℕ := {p | p.Prime ∧ p ∈ πᶜ}
  have hB_le_B' : B ≤ piCoreOf c.FU π' := by
    exact piCoreOf_le_piCoreOf_of_primeDivisors c.FU πᶜ π' (by
      intro q hq
      exact ⟨Nat.prime_of_mem_primeFactors hq,
        piCoreOf_primeDivisors c.FU πᶜ q hq⟩)
  have hQfixed_pt : ∀ p : {p // p ∈ π'}, ∀ x : G,
      x ∈ qCoreOf c.FU p.1 → s * x * s⁻¹ = x := by
    intro p x hx
    have hpprime : p.1.Prime := p.2.1
    have hnotπ : p.1 ∉ π := (Set.mem_compl_iff (s := π) p.1).1 p.2.2
    have hxQU : x ∈ qCoreOf c.U p.1 :=
      qCoreOf_fittingSubgroupOf_le_qCoreOf c.U p.1 hpprime hx
    by_cases hbotU : qCoreOf c.U p.1 = ⊥
    · have hx1 : x = 1 := by
        have hxbot : x ∈ (⊥ : Subgroup G) := by
          rw [← hbotU]
          exact hxQU
        exact Subgroup.mem_bot.mp hxbot
      simp [hx1]
    · have hpne2 : p.1 ≠ 2 := by
        intro hp2
        have hq2 : qCoreOf c.U 2 = twoCoreOf c.U := by
          rw [qCoreOf_eq_piCoreOf_singleton c.U 2 Nat.prime_two,
            twoCoreOf_eq_piCoreOf_2]
        have hbot2 : qCoreOf c.U 2 = ⊥ := by
          rw [hq2]
          exact twoCoreOf_eq_bot_of_odd_card c.U (card_U_odd c)
        exact hbotU (by simpa [hp2] using hbot2)
      have hpodd : Odd p.1 := hpprime.odd_of_ne_two hpne2
      have hcase := fixed_core_bot_or_top hmin c hs hpprime hpodd hnotSecond
      have hnotbot : centralizerIn (qCoreOf c.U p.1) s ≠ ⊥ := by
        intro hb
        exact hnotπ ⟨hpprime, hpodd, hb⟩
      have htop : centralizerIn (qCoreOf c.U p.1) s =
          qCoreOf c.U p.1 := hcase.resolve_left hnotbot
      have hxCent : x ∈ centralizerIn (qCoreOf c.U p.1) s := by
        rw [htop]
        exact hxQU
      have hcomm : x * s = s * x :=
        Subgroup.mem_centralizer_singleton_iff.mp hxCent.2
      calc
        s * x * s⁻¹ = x * s * s⁻¹ := by rw [hcomm]
        _ = x := by simp
  have hB_fixed_pt : ∀ x : G, x ∈ B → s * x * s⁻¹ = x := by
    intro x hx
    have hxsup' : x ∈ ⨆ p : {p // p ∈ π'}, qCoreOf c.FU p.1 :=
      hsup_decomp π' (hB_le_B' hx)
    rw [Subgroup.iSup_eq_closure] at hxsup'
    refine Subgroup.closure_induction'' ?_ ?_ ?_ ?_ hxsup'
    · intro y hy
      rcases (Set.mem_iUnion).1 hy with ⟨p, hyp⟩
      exact hQfixed_pt p y hyp
    · intro y hy
      rcases (Set.mem_iUnion).1 hy with ⟨p, hyp⟩
      have hyfix : s * y * s⁻¹ = y := hQfixed_pt p y hyp
      calc
        s * y⁻¹ * s⁻¹ = (s * y * s⁻¹)⁻¹ := by group
        _ = y⁻¹ := by rw [hyfix]
    · simp
    · intro a b _ _ ha hb
      calc
        s * (a * b) * s⁻¹ = (s * a * s⁻¹) * (s * b * s⁻¹) := by group
        _ = a * b := by rw [ha, hb]
  have hIB : I0 ⊓ B = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxInv : x ∈ invertedElements c.U s := hI0_le_inv hx.1
    have hxfix : s * x * s⁻¹ = x := hB_fixed_pt x hx.2
    have hxU : x ∈ c.U := hxInv.1
    have hx2 : x * x = 1 := by
      have hxeq : x = x⁻¹ := hxfix.symm.trans hxInv.2
      calc
        x * x = x * x⁻¹ := by nth_rw 2 [hxeq]
        _ = 1 := by simp
    have hord2 : orderOf x ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr (by simpa [pow_two] using hx2)
    have hcop : Nat.Coprime 2 (Nat.card (↥c.U)) :=
      Nat.coprime_two_left.mpr (card_U_odd c)
    have hordU : orderOf x ∣ Nat.card (↥c.U) :=
      Subgroup.orderOf_dvd_natCard c.U hxU
    have hord1 : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop hord2 hordU
    have hx1 : x = 1 := orderOf_eq_one_iff.mp hord1
    rw [hx1]
    simp
  have hA_inf_B : A ⊓ B = ⊥ := piCoreOf_inf_piCoreOf_compl_eq_bot c.U π
  have hF_eq : c.FU = A ⊔ B := fittingSubgroupOf_eq_sup_piCoreOf_compl c.U π
  have hBleNA : B ≤ Subgroup.normalizer (A : Set G) :=
    (piCoreOf_compl_centralizer_piCoreOf c.U π).trans
      (Subgroup.centralizer_le_normalizer (A : Set G))
  have hI0_le_A : I0 ≤ A := by
    intro x hx
    have hxF : x ∈ c.FU := hI0leFU hx
    have hxAB : x ∈ A ⊔ B := by
      rw [← hF_eq]
      exact hxF
    have hxprod : x ∈ (A : Set G) * (B : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left A B hBleNA]
      exact hxAB
    rcases hxprod with ⟨a, ha, b, hb, rfl⟩
    have haI : a ∈ I0 := hA_le_I0 ha
    have hbI : b ∈ I0 := by
      have hb_eq : b = a⁻¹ * (a * b) := by group
      rw [hb_eq]
      exact I0.mul_mem (I0.inv_mem haI) hx
    have hbIB : b ∈ I0 ⊓ B := ⟨hbI, hb⟩
    have hbBot : b ∈ (⊥ : Subgroup G) := by
      rw [← hIB]
      exact hbIB
    have hb1 : b = 1 := Subgroup.mem_bot.mp hbBot
    have hxeq : a * b = a := by rw [hb1]; simp
    simpa [hxeq] using ha
  have hI0_eq_A : I0 = A := le_antisymm hI0_le_A hA_le_I0
  have hA_le_F : A ≤ c.FU := piCoreOf_le c.FU π
  have hdisj : Disjoint A B := disjoint_iff_inf_le.mpr (by
    rw [hA_inf_B])
  have hcardF : Nat.card (↥c.FU) = Nat.card A * Nat.card B := by
    have h := card_sup_eq_mul_of_disjoint_of_le_normalizer A B hBleNA hdisj
    rwa [← hF_eq] at h
  have hcardA' : Nat.card (↥(A.subgroupOf c.FU)) = Nat.card A := by
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA_le_F).toEquiv
  have hcardF' : Nat.card (↥c.FU) =
      Nat.card A * (A.subgroupOf c.FU).index := by
    have h := Subgroup.card_mul_index (A.subgroupOf c.FU)
    change Nat.card (↥(A.subgroupOf c.FU)) * (A.subgroupOf c.FU).index =
        Nat.card (↥c.FU) at h
    rw [hcardA'] at h
    exact h.symm
  have hindex : (A.subgroupOf c.FU).index = Nat.card B := by
    have hmul : Nat.card A * Nat.card B =
        Nat.card A * (A.subgroupOf c.FU).index := by
      rw [← hcardF, hcardF']
    exact Nat.mul_left_cancel (Nat.card_pos (α := A)) hmul.symm
  have hcopAB : Nat.Coprime (Nat.card A) (Nat.card B) :=
    natCard_coprime_of_primeDivisors_compl A B π
      (piCoreOf_primeDivisors c.FU π)
      (piCoreOf_primeDivisors c.FU πᶜ)
  have hHallA : IsHallIn A c.FU :=
    ⟨hA_le_F, by rw [hindex]; exact hcopAB⟩
  have hHall : IsHallIn I0 c.FU := by
    rw [hI0_eq_A]
    exact hHallA
  exact ⟨I0, hI0eq, hHall⟩

/-- An element normalizing a subgroup also normalizes the ambient image of
each characteristic subgroup. -/
private theorem mem_normalizer_characteristic_map_subtype
    {G : Type*} [Group G]
    (T : Subgroup G) (Y : Subgroup T) (hY : Y.Characteristic)
    {u : G} (huT : u ∈ Subgroup.normalizer (T : Set G)) :
    u ∈ Subgroup.normalizer (Y.map T.subtype : Set G) := by
  have hforward : ∀ {g : G},
      g ∈ Subgroup.normalizer (T : Set G) →
      ∀ {x : G}, x ∈ Y.map T.subtype →
        g * x * g⁻¹ ∈ Y.map T.subtype := by
    intro g hg x hx
    rcases Subgroup.mem_map.mp hx with ⟨xT, hxY, rfl⟩
    let gN : Subgroup.normalizer (T : Set G) := ⟨g, hg⟩
    let alpha : MulAut T := T.normalizerMonoidHom gN
    have hfix : Y.map alpha.toMonoidHom = Y :=
      Subgroup.characteristic_iff_map_eq.mp hY alpha
    have halpha : alpha xT ∈ Y := by
      rw [← hfix]
      exact Subgroup.mem_map_of_mem alpha.toMonoidHom hxY
    refine Subgroup.mem_map.mpr ⟨alpha xT, halpha, ?_⟩
    rfl
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hforward huT
  · intro hx
    have huInvT : u⁻¹ ∈ Subgroup.normalizer (T : Set G) :=
      (Subgroup.normalizer (T : Set G)).inv_mem huT
    have hback := hforward huInvT hx
    simpa [mul_assoc] using hback

/-- A Sylow `p`-subgroup of a nilpotent group is nontrivial when `p` divides
the order, so the ambient `p`-core is nontrivial. -/
private theorem qCoreOf_ne_bot_of_prime_dvd_of_nilpotent
    {G : Type u} [Group G] [Finite G]
    (X : Subgroup G) (hXnil : Group.IsNilpotent (↥X))
    {p : ℕ} (hp : p.Prime) (hpdvd : p ∣ Nat.card (↥X)) :
    qCoreOf X p ≠ ⊥ := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let P : Sylow p (↥X) := default
  have hPne : (P : Subgroup (↥X)) ≠ ⊥ := Sylow.ne_bot_of_dvd_card P hpdvd
  have hPnorm : (P : Subgroup (↥X)).Normal := hXnil.sylow_normal p P
  have hPleCore : (P : Subgroup (↥X)) ≤ pCore p (↥X) :=
    le_sSup ⟨hPnorm, P.isPGroup'⟩
  intro hbot
  have hcorebot : pCore p (↥X) = ⊥ := by
    apply (Subgroup.map_eq_bot_iff_of_injective (H := pCore p (↥X))
      (f := X.subtype) X.subtype_injective).mp
    simpa [qCoreOf] using hbot
  have hPbot : (P : Subgroup (↥X)) = ⊥ :=
    le_bot_iff.mp (hPleCore.trans (le_of_eq hcorebot))
  exact hPne hPbot

/-- In the negative `SecondCase` branch, the second conjunct of `FirstCase`
holds: every nontrivial subgroup of `F(U)` has normalizer in `Ĥ`. -/
private theorem firstCase_normalizer_of_not_second
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hnotSecond : ¬ SecondCase c) :
    ∀ X : Subgroup G, X ≠ ⊥ → X ≤ c.FU →
      Subgroup.normalizer (X : Set G) ≤ c.Hhat := by
  classical
  intro X hXne hXleFU
  by_contra hNnot
  obtain ⟨g, hgNX, hgnotHhat⟩ := Set.not_subset.mp hNnot
  have hFnil : Group.IsNilpotent (↥c.FU) := fittingSubgroupOf_isNilpotent c.U
  have hFUleU : c.FU ≤ c.U := (fittingSubgroupOf_isNormalIn c.U).1
  have hcardX_ne1 : Nat.card (↥X) ≠ 1 := by
    intro hc
    exact hXne ((Subgroup.eq_bot_iff_card (H := X)).2 hc)
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hcardX_ne1
  have hpdvdFU : p ∣ Nat.card (↥c.FU) :=
    hpdvd.trans (Subgroup.card_dvd_of_le hXleFU)
  have hpdvdU : p ∣ Nat.card (↥c.U) :=
    hpdvdFU.trans (Subgroup.card_dvd_of_le hFUleU)
  have hpodd : Odd p := (card_U_odd c).of_dvd_nat hpdvdU
  let : Group.IsNilpotent (↥c.FU) := hFnil
  let X' : Subgroup (↥c.FU) := X.subgroupOf c.FU
  have hXnil' : Group.IsNilpotent (↥X') := Subgroup.isNilpotent X'
  have hXnil : Group.IsNilpotent (↥X) :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hXleFU)
  let Y : Subgroup G := qCoreOf X p
  have hYne : Y ≠ ⊥ :=
    qCoreOf_ne_bot_of_prime_dvd_of_nilpotent X hXnil hp hpdvd
  have hYleFU : Y ≤ c.FU := by
    intro y hy
    exact hXleFU (qCoreOf_le X p hy)
  have hYp : IsPGroup p Y := qCoreOf_isPGroup X p
  have hYleU : Y ≤ c.U := hYleFU.trans hFUleU
  have hYsubFU : (Y.subgroupOf c.FU).IsSubnormal :=
    isSubnormal_of_nilpotent hFnil Y hYleFU
  have hYsubU : (Y.subgroupOf c.U).IsSubnormal :=
    isSubnormal_of_isNormalIn_subgroup hFUleU
      (fittingSubgroupOf_isNormalIn c.U) hYleFU hYsubFU
  have hYleQ : Y ≤ qCoreOf c.U p :=
    le_qCoreOf_of_isSubnormal_isPGroup c.U Y p hYleU hYsubU hYp
  have hNX_le_NY : Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer (Y : Set G) := by
    intro u hu
    exact mem_normalizer_characteristic_map_subtype X
      (pCore p (↥X)) inferInstance hu
  have hgNY : g ∈ Subgroup.normalizer (Y : Set G) := hNX_le_NY hgNX
  have hYleFHhat : Y ≤ fittingSubgroupOf c.Hhat :=
    hYleFU.trans (FU_le_fittingSubgroupOf_Hhat_of_centralizerStructure c
      (theorem_2_6 hmin c))
  have hS_le_NY : (c.S : Subgroup G) ≤
      Subgroup.normalizer (Y : Set G) := by
    have hRefl : ∀ r : G, c.IsReflection r →
        r ∈ Subgroup.normalizer (Y : Set G) := by
      intro r hr
      rw [Subgroup.mem_normalizer_iff]
      have hcase := fixed_core_bot_or_top hmin c hr hp hpodd hnotSecond
      have hforward : ∀ z : G, z ∈ Y → r * z * r⁻¹ ∈ Y := by
        intro z hz
        have hzQ : z ∈ qCoreOf c.U p := hYleQ hz
        rcases hcase with hbot | htop
        · have hzInvQ : z ∈ invertedElements (qCoreOf c.U p) r := by
            rw [inverted_qCore_eq_qCore_of_centralizer_bot c hr hp hpodd hbot]
            exact hzQ
          have hzr : r * z * r⁻¹ = z⁻¹ := hzInvQ.2
          rw [hzr]
          exact Y.inv_mem hz
        · have hzCent : z ∈ centralizerIn (qCoreOf c.U p) r := by
            rw [htop]
            exact hzQ
          have hcomm : z * r = r * z :=
            Subgroup.mem_centralizer_singleton_iff.mp hzCent.2
          have hzr : r * z * r⁻¹ = z := by
            calc
              r * z * r⁻¹ = z * r * r⁻¹ := by rw [hcomm]
              _ = z := by simp
          rw [hzr]
          exact hz
      intro z
      constructor
      · exact hforward z
      · intro hz
        have hr2 : r * r = 1 := by
          simpa [pow_two] using
            (centralizerSetup_reflection_isInvolution c hr).2
        have hrInv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr2
        have hback := hforward (r * z * r⁻¹) hz
        have hz_eq : r * (r * z * r⁻¹) * r⁻¹ = z := by
          rw [hrInv]
          calc
            r * (r * z * r) * r = (r * r) * z * (r * r) := by group
            _ = z := by rw [hr2]; simp
        simpa [hz_eq] using hback
    intro x hxS
    by_cases hx0 : x ∈ c.S0
    · rcases CentralizerSetup.exists_reflection c with ⟨r, hr⟩
      have hxrS : r * x ∈ (c.S : Subgroup G) :=
        (c.S : Subgroup G).mul_mem hr.1 hxS
      have hxrnot : r * x ∉ c.S0 := by
        intro h
        apply hr.2
        have hrx : r = (r * x) * x⁻¹ := by group
        rw [hrx]
        exact c.S0.mul_mem h (c.S0.inv_mem hx0)
      have hxrN : r * x ∈ Subgroup.normalizer (Y : Set G) :=
        hRefl (r * x) ⟨hxrS, hxrnot⟩
      have hrN : r ∈ Subgroup.normalizer (Y : Set G) := hRefl r hr
      have hx_eq : x = r * (r * x) := by
        have hr2 : r * r = 1 := by
          simpa [pow_two] using
            (centralizerSetup_reflection_isInvolution c hr).2
        calc
          x = (r * r) * x := by rw [hr2]; simp
          _ = r * (r * x) := by rw [mul_assoc]
      rw [hx_eq]
      exact (Subgroup.normalizer (Y : Set G)).mul_mem hrN hxrN
    · exact hRefl x ⟨hxS, hx0⟩
  have hYleHhat : Y ≤ c.Hhat :=
    hYleFHhat.trans (fittingSubgroupOf_isNormalIn c.Hhat).1
  have hNYne_top : Subgroup.normalizer (Y : Set G) ≠ ⊤ := by
    intro htop
    have hYnorm : Y.Normal := (Subgroup.normalizer_eq_top_iff (H := Y)).mp htop
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ (minimalCounterexample_isSimple hmin)
      Y hYnorm with hbot | htopY
    · exact hYne hbot
    · exact c.Hhat_maximal.ne_top (top_unique (htopY ▸ hYleHhat))
  obtain ⟨M, hMmax, hNYleM⟩ :=
    (eq_top_or_exists_le_coatom (Subgroup.normalizer (Y : Set G))).resolve_left
      hNYne_top
  have hMnotHhat : ¬ M ≤ c.Hhat := by
    intro hMle
    exact hgnotHhat (hMle (hNYleM hgNY))
  have hSleM : (c.S : Subgroup G) ≤ M := hS_le_NY.trans hNYleM
  have hinverted : ∀ s : G, c.IsReflection s →
      ∃ I : Subgroup G, IsInvertedSubgroup I c.U s := by
    intro s hs
    rcases reflection_inverted_hall hmin c hs hnotSecond with ⟨I, hI, _hHall⟩
    exact ⟨I, hI⟩
  have h28 := lemma_2_8 hmin c hinverted
  have htE : c.t ∈ componentLayerOf M :=
    h28.2 M hMmax.ne_top ⟨Y, hYne, hYleFHhat, hNYleM⟩
      hMnotHhat hSleM
  exact hnotSecond ⟨M, hMmax, hMnotHhat, htE, Y, hYne, hYleFU, hNYleM⟩

/-- Theorem 2.10: in a minimal counterexample, either the Hall/normalizer
case holds, or the component-layer case holds. -/
public theorem theorem_2_10
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) :
    FirstCase c ∨ SecondCase c := by
  by_cases hsecond : SecondCase c
  · exact Or.inr hsecond
  · left
    refine ⟨?_, ?_⟩
    · intro s hs
      exact reflection_inverted_hall hmin c hs hsecond
    · exact firstCase_normalizer_of_not_second hmin c hsecond

end

end CFSG.GorensteinWalter

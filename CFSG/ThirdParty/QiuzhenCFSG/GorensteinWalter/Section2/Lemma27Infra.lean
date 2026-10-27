module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970API
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ControlCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.MinimalCounterexample
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PreambleHSU
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralUniqueCentralInvolution
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralNormalSubgroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalDihedralIndex
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GWLemma21
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GWLemma21Trichotomy
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.NoncyclicAbelianPGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27IndexTwo
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27QuotientIndex
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27TwoResidualBranch

namespace CFSG
end CFSG
open CFSG

/-!
# Infrastructure for Lemma 2.7

This module owns the reusable facts that `Lemma27.lean` (and later
`Lemma28.lean`) consume.  The paper route needs:

1. the Bender `F*`-centralizer fact used by the `C_G(F(M)) ≤ F(M)` step;
2. the dihedral normal-subgroup step (`4 | |N|` forces `t ∈ N`), whose
   Grün/dihedral proof is the in-flight `gw-lemma21-trichotomy` landing
   (single remaining registered bridge).

The generic extension/nilpotency facts, the Klein-four fixed-point choice,
the odd-order-subgroups-of-`H`-lie-in-`U` fact, and Bender 1.1(iv) (normal
and subnormal coprime transfer) are proved here sorry-free.  The involution
fixed-points bridge and the final `[S,U] ≰ F(U)` bridge were removed as
unprovable at this stage and returned as exact gaps.
-/

namespace CFSG.GorensteinWalter

universe u

noncomputable section

open scoped Pointwise commutatorElement

/-! ## Solvability glue (sorry-free) -/

/-- Solvability is preserved by extensions: if a normal subgroup and the
quotient are solvable, so is the group. -/
public theorem isSolvable_of_normal_solvable_quotient_solvable
    {G : Type u} [Group G] (N : Subgroup G) [N.Normal]
    (hN : Group.IsSolvable N) (hQ : Group.IsSolvable (G ⧸ N)) :
    Group.IsSolvable G := by
  let : Group.IsSolvable N := hN
  let : Group.IsSolvable (G ⧸ N) := hQ
  refine Group.isSolvable_of_ker_le_range N.subtype (QuotientGroup.mk' N) ?_
  intro x hx
  rw [QuotientGroup.ker_mk'] at hx
  exact ⟨⟨x, hx⟩, rfl⟩

/-- A finite `p`-group is solvable. -/
public theorem isSolvable_of_isPGroup
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (h : IsPGroup p G) : Group.IsSolvable G :=
  letI : Group.IsNilpotent G := IsPGroup.isNilpotent h
  inferInstance

/-- The Fitting subgroup of a subgroup is nilpotent (as an ambient
subgroup). -/
public theorem fittingSubgroupOf_isNilpotent
    {G : Type u} [Group G] [Finite G] (H : Subgroup G) :
    Group.IsNilpotent (↥(fittingSubgroupOf H)) := by
  change Group.IsNilpotent (↥((fittingSubgroup (↥H)).map H.subtype))
  have : Group.IsNilpotent (fittingSubgroup (↥H)) := by infer_instance
  exact Group.nilpotent_of_mulEquiv
    (Subgroup.equivMapOfInjective (fittingSubgroup (↥H)) H.subtype H.subtype_injective)

/-- `O^p(P) ≤ K` whenever `P` is a Sylow `p`-subgroup and `K ◁ G` has
`p`-power index. -/
private theorem pResidualOf_sylow_le_of_normal_index
    {G : Type u} [Group G] [Finite G]
    (p n : ℕ) [Fact p.Prime] (P : Sylow p G) (K : Subgroup G)
    (hK : K.Normal) (hindex : K.index = p ^ n) :
    pResidualOf (P : Subgroup G) p ≤ K := by
  let KP : Subgroup (↥(P : Subgroup G)) :=
    (K ⊓ (P : Subgroup G)).subgroupOf (P : Subgroup G)
  have hPleN : (P : Subgroup G) ≤
      Subgroup.normalizer ((K ⊓ (P : Subgroup G)) : Set G) := by
    let : (K : Subgroup G).Normal := hK
    exact (le_inf (Subgroup.le_normalizer_of_normal (H := K))
      (Subgroup.le_normalizer (H := (P : Subgroup G)))).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := K) (K := (P : Subgroup G)))
  have hKP_normal : KP.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (H := (P : Subgroup G))
      (N := K ⊓ (P : Subgroup G)) hPleN
  have hKP_index : ∃ m : ℕ, KP.index = p ^ m := by
    have hrel : K.relIndex (P : Subgroup G) ∣ K.index :=
      Subgroup.relIndex_dvd_index_of_normal (H := K) (K := (P : Subgroup G))
    have hKPidx : KP.index = K.relIndex (P : Subgroup G) := by
      change ((K ⊓ (P : Subgroup G)).subgroupOf (P : Subgroup G)).index =
        K.relIndex (P : Subgroup G)
      rw [Subgroup.inf_subgroupOf_right]
      rfl
    have hdvd : KP.index ∣ p ^ n := by
      rwa [← hKPidx, hindex] at hrel
    rcases (Nat.dvd_prime_pow (inferInstance : Fact p.Prime).out).mp hdvd with
      ⟨m, _hm, hm⟩
    exact ⟨m, hm⟩
  have hres := pResidualOf_le_of_normal_index
    (H := (P : Subgroup G)) (p := p) (N := KP) hKP_normal hKP_index
  exact hres.trans (by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨z, hz, rfl⟩
    exact (Subgroup.mem_subgroupOf.mp hz).1)

/-- `O^p(P) ≤ O^p(G)` for a Sylow `p`-subgroup `P` of `G`. -/
public theorem pResidualOf_sylow_le_pResidualOf_top
    {G : Type u} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (P : Sylow p G) :
    pResidualOf (P : Subgroup G) p ≤ pResidualOf (⊤ : Subgroup G) p := by
  classical
  intro x hx
  let xTop : ↥(⊤ : Subgroup G) := ⟨x, trivial⟩
  have hxSInf : xTop ∈ sInf
      {N : Subgroup (↥(⊤ : Subgroup G)) |
        N.Normal ∧ ∃ n : ℕ, N.index = p ^ n} := by
    rw [Subgroup.mem_sInf]
    intro N hN
    rcases hN with ⟨hNnormal, n, hNindex⟩
    let K : Subgroup G := N.map (⊤ : Subgroup G).subtype
    have hKnormal : K.Normal :=
      Subgroup.Normal.map hNnormal (⊤ : Subgroup G).subtype
        (Subgroup.topEquiv.surjective)
    have hKindex : K.index = p ^ n := by
      have heq := Subgroup.index_map_equiv
        (e := (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)) (H := N)
      convert heq.trans hNindex using 1
      rfl
    have hres := pResidualOf_sylow_le_of_normal_index
      (p := p) (n := n) P K hKnormal hKindex
    have hxK : x ∈ K := hres hx
    have hxN : xTop ∈ N := by
      rcases Subgroup.mem_map.mp hxK with ⟨y, hyN, hyx⟩
      have hyx' : y = xTop := by
        apply Subtype.ext
        exact hyx
      simpa [hyx'] using hyN
    exact hxN
  exact Subgroup.mem_map.mpr ⟨xTop, hxSInf, rfl⟩

/-! ## The Bender `F*`-centralizer fact -/

/-- The classical Bender fact (proved in `Bender1970_18`):
`C_G(F*(G)) ⊓ F*(G) ≤ F(G)`.  The paper route for Lemma 2.7 uses this
together with `E(M) = 1` and the D-group classification; the full
`C_G(F(M)) ≤ F(M)` plus `IsSolvable M` step is a separate gap that needs
the minimal-counterexample context (see the task card).  The previous
registered bridge `isSolvable_of_DGroup_of_componentLayer_eq_bot` was
DELETED: the statement is false in general (`F* = F` does not imply
solvable; e.g. a faithful semidirect product `F₅³ ⋊ A₅` has dihedral
Sylow-2, trivial layer, `F* = F`, and is not solvable). -/
public theorem centralizer_generalizedFitting_intersection_le_fittingSubgroup
    {G : Type u} [Group G] [Finite G] :
    let X := generalizedFittingSubgroupOf (⊤ : Subgroup G)
    let C := Subgroup.centralizer (X : Set G)
    C ⊓ X ≤ fittingSubgroupOf (⊤ : Subgroup G) :=
  centralizer_generalizedFitting_intersection_le_fittingSubgroupOf (G := G)

/-! ## Normal subgroups of order divisible by four -/

/-- Lemma 2.7's first local claim (Bender p. 221), in the standing minimal
counterexample context: every normal subgroup `N ◁ M` whose order is
divisible by `4` contains the distinguished involution `t`.

The source-faithful statement carries `(hmin : IsMinimalCounterexample G)`:
the paper's Lemma 2.7 is stated after Theorem 2.6 and uses
`t ∈ O₂(Ĥ)` ("Theorem 2.6 mainly states that `t` lies in `O₂(Ĥ)`") together
with `Ĥ ↝ M` (`NormalizerControlledBy c.Hhat M`) to force `t ∈ M`.  The
earlier `M ≤ c.Hhat` reading was confirmed by the printed-page scan to be a
transcription error; it is *not* assumed here.

The `8 ≤ |S ∩ M|` branch is proved below
(`t_mem_N_of_card_div_four_of_S_inter_M_large`); the remaining
`|S| = 4` / `t ∈ O²(M)` disjunction needs Theorem 2.6's `t ∈ O₂(Ĥ)`
consequence, whose owner module cannot be imported here (import cycle
`Theorem26 → Lemma22 → ForbiddenConfigurationBrauerSuzukiWallHypotheses →
Lemma27Infra`). -/

public theorem fittingSubgroup_le_sup_pCore_pPrimeCore
    {G : Type u} [Group G] [Finite G] :
    fittingSubgroup G ≤ pCore 2 G ⊔ pPrimeCore 2 G := by
  classical
  rw [fitting_eq_sup_pCore G]
  refine iSup_le (fun p => ?_)
  by_cases hp2 : p.1.1 = 2
  · simpa [hp2] using (le_sup_left : pCore 2 G ≤ pCore 2 G ⊔ pPrimeCore 2 G)
  · have hpodd : Odd p.1.1 := Nat.Prime.odd_of_ne_two (Nat.prime_of_mem_primeFactors p.1.2) hp2
    have hle : pCore p.1.1 G ≤ pPrimeCore 2 G := by
      have hnorm : (pCore p.1.1 G).Normal := pCore_normal
      have hcop : Nat.Coprime 2 (Nat.card (↥(pCore p.1.1 G))) := by
        rcases (IsPGroup.iff_card (p := p.1.1) (G := ↥(pCore p.1.1 G))).mp
          (pCore_isPGroup (p := p.1.1) (G := G)) with ⟨n, hn⟩
        rw [hn]
        exact Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr hpodd).symm
      change pCore p.1.1 G ≤ sSup {K : Subgroup G | K.Normal ∧ Nat.Coprime 2 (Nat.card K)}
      exact le_sSup ⟨hnorm, hcop⟩
    exact hle.trans le_sup_right

/- helper 2 -/
public theorem centralizerStructure_t_mem_twoCore
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (h26 : CentralizerStructure c) :
    c.t ∈ twoCoreOf c.Hhat := by
  rcases h26 with ⟨hU, hSinter, _hAlt⟩
  have htS : c.t ∈ (c.S : Subgroup G) := c.S0_le_S c.t_mem_S0
  have htC : c.t ∈ Subgroup.centralizer (c.U : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzH : z ∈ c.H := (Subgroup.map_subtype_le (H := c.H) (pPrimeCore 2 c.H)) hz
    have hzCent : z ∈ Subgroup.centralizer ({c.t} : Set G) := by
      rw [← c.H_eq_centralizer]
      exact hzH
    have hcomm : c.t * z = z * c.t :=
      (Subgroup.mem_centralizer_iff (g := z) (s := ({c.t} : Set G))).1 hzCent c.t (by simp)
    exact hcomm.symm
  rw [← hSinter]
  exact ⟨htS, htC⟩

/- helper 3 -/
public theorem t_centralizes_fittingSubgroupOf_of_centralizerStructure
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (h26 : CentralizerStructure c) :
    c.t ∈ Subgroup.centralizer ((fittingSubgroupOf c.Hhat : Set G)) := by
  rcases h26 with ⟨hU, hSinter, hAlt⟩
  rcases hAlt with hCase1 | hCase2
  · rcases hCase1 with ⟨hVleS0, hHhat_eq_H⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxH : x ∈ c.H := by
      rw [← hHhat_eq_H]
      exact (Subgroup.map_subtype_le (H := c.Hhat) (fittingSubgroup c.Hhat)) hx
    have hxCent : x ∈ Subgroup.centralizer ({c.t} : Set G) := by
      rw [← c.H_eq_centralizer]
      exact hxH
    have hcomm : c.t * x = x * c.t :=
      (Subgroup.mem_centralizer_iff (g := x) (s := ({c.t} : Set G))).1 hxCent c.t (by simp)
    exact hcomm.symm
  · rcases hCase2 with ⟨hK4, hquot⟩
    let V : Subgroup (↥c.Hhat) := pCore 2 c.Hhat
    let O : Subgroup (↥c.Hhat) := pPrimeCore 2 c.Hhat
    let : IsKleinFour (↥V) := by simpa [V] using hK4
    let : IsMulCommutative (↥V) := IsKleinFour.isMulCommutative
    let : CommGroup (↥V) := IsMulCommutative.instCommGroup
    have htV : c.t ∈ V.map c.Hhat.subtype := by
      have ht2 : c.t ∈ twoCoreOf c.Hhat := centralizerStructure_t_mem_twoCore c ⟨hU, hSinter, Or.inr ⟨hK4, hquot⟩⟩
      simpa [twoCoreOf, V] using ht2
    rcases htV with ⟨v, hv, hvval⟩
    have hVcentO : V ≤ Subgroup.centralizer (O : Set (↥c.Hhat)) := by
      have hcomm_le : ⁅V, O⁆ ≤ V ⊓ O := Subgroup.commutator_le_inf V O
      have hVObot : V ⊓ O = ⊥ := by
        apply (Subgroup.card_le_one_iff_eq_bot (V ⊓ O)).mp
        have hVcard : Nat.card (↥V) = 4 := by simpa [V] using hK4.card_four
        have hOodd : Nat.Coprime 2 (Nat.card (↥O)) := by
          simpa [O] using (pPrimeCore_coprime_card (p := 2) (G := ↥c.Hhat))
        have hdvdV : Nat.card (↥(V ⊓ O)) ∣ 4 := by
          exact (Subgroup.card_dvd_of_le inf_le_left).trans (by simpa [hVcard])
        have hdvdO : Nat.Coprime 2 (Nat.card (↥(V ⊓ O))) :=
          Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le inf_le_right) hOodd
        rcases (Nat.dvd_prime_pow Nat.prime_two (m := 2)).mp hdvdV with ⟨a, _ha, hapow⟩
        have hpow : Nat.card (↥(V ⊓ O)) = 2 ^ a := hapow
        have hcop2 : ¬ 2 ∣ Nat.card (↥(V ⊓ O)) :=
          (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hdvdO
        have ha0 : a = 0 := by
          by_cases ha : a = 0
          · exact ha
          · exfalso
            apply hcop2
            rw [hpow]
            exact dvd_pow_self 2 ha
        rw [hpow, ha0]
        norm_num
      have hcomm_bot : ⁅V, O⁆ = ⊥ := by
        apply le_bot_iff.mp
        exact hcomm_le.trans (le_of_eq hVObot)
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hcomm_bot
    have hFle : fittingSubgroup (↥c.Hhat) ≤ V ⊔ O := by
      exact (fittingSubgroup_le_sup_pCore_pPrimeCore (G := ↥c.Hhat))
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rcases hx with ⟨x0, hx0, rfl⟩
    have hx0VA : x0 ∈ V ⊔ O := hFle hx0
    have hxprod : (x0 : ↥c.Hhat) ∈ (V : Set (↥c.Hhat)) * (O : Set (↥c.Hhat)) := by
      rw [← Subgroup.mul_normal V O]
      exact hx0VA
    rcases hxprod with ⟨v0, hv0, a0, ha0, hva⟩
    change v0 * a0 = x0 at hva
    have hv0val : (v : ↥c.Hhat) * (v0 : ↥c.Hhat) = (v0 : ↥c.Hhat) * (v : ↥c.Hhat) := by
      have hvV : (⟨v, hv⟩ : ↥V) * (⟨v0, hv0⟩ : ↥V) = (⟨v0, hv0⟩ : ↥V) * (⟨v, hv⟩ : ↥V) := by
        exact mul_comm (⟨v, hv⟩ : ↥V) (⟨v0, hv0⟩ : ↥V)
      exact congrArg Subtype.val hvV
    have hva0 : (v : ↥c.Hhat) * (a0 : ↥c.Hhat) = (a0 : ↥c.Hhat) * (v : ↥c.Hhat) := by
      have hvc : (v : ↥c.Hhat) ∈ Subgroup.centralizer (O : Set (↥c.Hhat)) :=
        hVcentO hv
      exact ((Subgroup.mem_centralizer_iff (g := v) (s := (O : Set (↥c.Hhat)))).1 hvc a0 ha0).symm
    have hcomm : (v : ↥c.Hhat) * (x0 : ↥c.Hhat) = (x0 : ↥c.Hhat) * (v : ↥c.Hhat) := by
      calc
        (v : ↥c.Hhat) * (x0 : ↥c.Hhat) = (v : ↥c.Hhat) * ((v0 : ↥c.Hhat) * (a0 : ↥c.Hhat)) := by rw [hva]
        _ = ((v : ↥c.Hhat) * (v0 : ↥c.Hhat)) * (a0 : ↥c.Hhat) := by rw [mul_assoc]
        _ = ((v0 : ↥c.Hhat) * (v : ↥c.Hhat)) * (a0 : ↥c.Hhat) := by rw [hv0val]
        _ = (v0 : ↥c.Hhat) * ((v : ↥c.Hhat) * (a0 : ↥c.Hhat)) := by rw [mul_assoc]
        _ = (v0 : ↥c.Hhat) * ((a0 : ↥c.Hhat) * (v : ↥c.Hhat)) := by rw [hva0]
        _ = ((v0 : ↥c.Hhat) * (a0 : ↥c.Hhat)) * (v : ↥c.Hhat) := by rw [mul_assoc]
        _ = (x0 : ↥c.Hhat) * (v : ↥c.Hhat) := by rw [hva]
    have hvG : c.t = (v : G) := by
      change c.t = c.Hhat.subtype v
      exact hvval.symm
    have hcommG : c.t * (x0 : G) = (x0 : G) * c.t := by
      calc
        c.t * (x0 : G) = (v : G) * (x0 : G) := by rw [hvG]
        _ = (x0 : G) * (v : G) := congrArg Subtype.val hcomm
        _ = (x0 : G) * c.t := by rw [← hvG]
    exact hcommG.symm

/- helper 4 -/
public theorem t_mem_M_of_centralizerStructure
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (M : Subgroup G)
    (hM : Lemma27Hypothesis c M) (h26 : CentralizerStructure c) :
    c.t ∈ M := by
  rcases hM with ⟨hMproper, hControl, hMnotle, hEt, hSylow, hBranch⟩
  rcases hControl with ⟨X, hXne, hXleF, hNXleM⟩
  have htCF : c.t ∈ Subgroup.centralizer ((fittingSubgroupOf c.Hhat : Set G)) :=
    t_centralizes_fittingSubgroupOf_of_centralizerStructure c h26
  have htCX : c.t ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' : x ∈ fittingSubgroupOf c.Hhat := hXleF hx
    have hcomm : x * c.t = c.t * x :=
      (Subgroup.mem_centralizer_iff (g := c.t) (s := (fittingSubgroupOf c.Hhat : Set G))).mp htCF x hx'
    exact hcomm
  have htNX : c.t ∈ Subgroup.normalizer (X : Set G) :=
    (Subgroup.centralizer_le_normalizer (X : Set G)) htCX
  exact hNXleM htNX

public theorem unique_involution_of_cyclic_two_group {A : Type*} [Group A] [Finite A]
    (hcyc : IsCyclic A) {m : ℕ} (hm : 1 ≤ m)
    (hcard : Nat.card A = 2 ^ m) :
    ∀ x y : A, x ≠ 1 → x ^ 2 = 1 → y ≠ 1 → y ^ 2 = 1 → x = y := by
  classical
  let : IsCyclic A := hcyc
  rcases IsCyclic.exists_monoid_generator (α := A) with ⟨g, hg⟩
  have hord : orderOf g = 2 ^ m := by
    rw [← hcard]
    apply orderOf_eq_card_of_forall_mem_zpowers
    intro x
    rcases hg x with ⟨k, rfl⟩
    exact ⟨k, zpow_natCast g k⟩
  have hmm : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have h2m : 2 * 2 ^ (m - 1) = 2 ^ m := by
    calc
      2 * 2 ^ (m - 1) = 2 ^ (m - 1) * 2 := by rw [Nat.mul_comm]
      _ = 2 ^ (m - 1 + 1) := by exact (pow_succ 2 (m - 1)).symm
      _ = 2 ^ m := by rw [hmm]
  have hgpow : g ^ (2 ^ m) = 1 := by
    exact (orderOf_dvd_iff_pow_eq_one (x := g) (n := 2 ^ m)).1 (by simp [hord])
  have h2h : (g ^ (2 ^ (m - 1))) ^ 2 = 1 := by
    calc
      (g ^ (2 ^ (m - 1))) ^ 2 = g ^ (2 ^ (m - 1) * 2) := by
        exact (pow_mul g (2 ^ (m - 1)) 2).symm
      _ = g ^ (2 * 2 ^ (m - 1)) := by rw [Nat.mul_comm]
      _ = g ^ (2 ^ m) := by rw [h2m]
      _ = 1 := hgpow
  have h_pow_odd : ∀ k : ℕ, (g ^ (2 ^ (m - 1))) ^ (2 * k + 1) = g ^ (2 ^ (m - 1)) := by
    intro k
    calc
      (g ^ (2 ^ (m - 1))) ^ (2 * k + 1) =
          (g ^ (2 ^ (m - 1))) ^ (2 * k) * g ^ (2 ^ (m - 1)) := by
        exact pow_succ (g ^ (2 ^ (m - 1))) (2 * k)
      _ = ((g ^ (2 ^ (m - 1))) ^ 2) ^ k * g ^ (2 ^ (m - 1)) := by
        exact congrArg (fun z : A => z * g ^ (2 ^ (m - 1)))
          (pow_mul (g ^ (2 ^ (m - 1))) 2 k)
      _ = 1 ^ k * g ^ (2 ^ (m - 1)) := by rw [h2h]
      _ = g ^ (2 ^ (m - 1)) := by simp
  intro x y hx1 hx2 hy1 hy2
  rcases hg x with ⟨a, rfl⟩
  rcases hg y with ⟨b, rfl⟩
  have hxa : orderOf g ∣ 2 * a := by
    apply (orderOf_dvd_iff_pow_eq_one (x := g) (n := 2 * a)).2
    simpa [pow_mul, Nat.mul_comm] using hx2
  have hya : orderOf g ∣ 2 * b := by
    apply (orderOf_dvd_iff_pow_eq_one (x := g) (n := 2 * b)).2
    simpa [pow_mul, Nat.mul_comm] using hy2
  have hdiv_a : 2 ^ (m - 1) ∣ a := by
    rw [hord] at hxa
    rw [← h2m] at hxa
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hxa
  have hdiv_b : 2 ^ (m - 1) ∣ b := by
    rw [hord] at hya
    rw [← h2m] at hya
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hya
  rcases hdiv_a with ⟨a', rfl⟩
  rcases hdiv_b with ⟨b', rfl⟩
  have hx_ne : (g ^ (2 ^ (m - 1))) ^ a' ≠ 1 := by
    simpa [pow_mul] using hx1
  have hy_ne : (g ^ (2 ^ (m - 1))) ^ b' ≠ 1 := by
    simpa [pow_mul] using hy1
  have hodd_a : Odd a' := by
    rcases Nat.even_or_odd a' with he | ho
    · exfalso
      rcases he with ⟨k, rfl⟩
      have hkk : (g ^ (2 ^ (m - 1))) ^ (k + k) = 1 := by
        calc
          (g ^ (2 ^ (m - 1))) ^ (k + k) = (g ^ (2 ^ (m - 1))) ^ (2 * k) := by
            rw [Nat.two_mul]
          _ = ((g ^ (2 ^ (m - 1))) ^ 2) ^ k := by
            exact pow_mul (g ^ (2 ^ (m - 1))) 2 k
          _ = 1 ^ k := by rw [h2h]
          _ = 1 := by simp
      exact hx_ne hkk
    · exact ho
  have hodd_b : Odd b' := by
    rcases Nat.even_or_odd b' with he | ho
    · exfalso
      rcases he with ⟨k, rfl⟩
      have hkk : (g ^ (2 ^ (m - 1))) ^ (k + k) = 1 := by
        calc
          (g ^ (2 ^ (m - 1))) ^ (k + k) = (g ^ (2 ^ (m - 1))) ^ (2 * k) := by
            rw [Nat.two_mul]
          _ = ((g ^ (2 ^ (m - 1))) ^ 2) ^ k := by
            exact pow_mul (g ^ (2 ^ (m - 1))) 2 k
          _ = 1 ^ k := by rw [h2h]
          _ = 1 := by simp
      exact hy_ne hkk
    · exact ho
  rcases hodd_a with ⟨ka, rfl⟩
  rcases hodd_b with ⟨kb, rfl⟩
  calc
    g ^ (2 ^ (m - 1) * (2 * ka + 1)) = (g ^ (2 ^ (m - 1))) ^ (2 * ka + 1) := by
      exact pow_mul g (2 ^ (m - 1)) (2 * ka + 1)
    _ = g ^ (2 ^ (m - 1)) := h_pow_odd ka
    _ = (g ^ (2 ^ (m - 1))) ^ (2 * kb + 1) := (h_pow_odd kb).symm
    _ = g ^ (2 ^ (m - 1) * (2 * kb + 1)) := by
      exact (pow_mul g (2 ^ (m - 1)) (2 * kb + 1)).symm

/-- Every subgroup of `DihedralGroup (2 ^ m)` of order at least `4` contains
the central rotation `r (2 ^ (m - 1))`. -/
public theorem subgroup_card_ge_four_contains_central_rotation
    {m : ℕ} (hm : 1 ≤ m) (D : Subgroup (DihedralGroup (2 ^ m)))
    (hcard : 4 ≤ Nat.card (↥D)) :
    DihedralGroup.r (2 ^ (m - 1) : ZMod (2 ^ m)) ∈ D := by
  classical
  let z : DihedralGroup (2 ^ m) := DihedralGroup.r (2 ^ (m - 1) : ZMod (2 ^ m))
  let R : Subgroup (DihedralGroup (2 ^ m)) := Subgroup.zpowers (DihedralGroup.r 1)
  have hzR : z ∈ R := by
    simpa [z] using (r_mem_zpowers_r_one (2 ^ (m - 1) : ZMod (2 ^ m)))
  have hRcard : Nat.card (↥R) = 2 ^ m := by
    dsimp [R]
    rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one]
  have hz2 : z ^ 2 = 1 := by
    dsimp [z]
    rw [pow_two, DihedralGroup.r_mul_r]
    have hzero : (2 ^ (m - 1) : ZMod (2 ^ m)) + (2 ^ (m - 1) : ZMod (2 ^ m)) = 0 := by
      rw [← two_mul]
      by_cases hm1 : m = 1
      · subst m
        simp
        exact ZMod.natCast_self 2
      · have hm2 : 2 ≤ m := by omega
        exact (zmod_two_mul_eq_zero_iff hm2 (2 ^ (m - 1) : ZMod (2 ^ m))).mpr (Or.inr rfl)
    rw [hzero]
    rfl
  have hzne : z ≠ 1 := by
    intro h
    have hord : orderOf z = 2 := by
      dsimp [z]
      rw [DihedralGroup.orderOf_r]
      have hpow_cast : ((2 : ℕ) : ZMod (2 ^ m)) ^ (m - 1) = ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
        exact_mod_cast (Nat.cast_pow (2 : ℕ) (m - 1) :
          ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) = ((2 : ℕ) : ZMod (2 ^ m)) ^ (m - 1)).symm
      have hval : (2 ^ (m - 1) : ZMod (2 ^ m)).val = 2 ^ (m - 1) := by
        have hconv : (2 ^ (m - 1) : ZMod (2 ^ m)) = ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
          simpa using hpow_cast
        rw [hconv]
        rw [ZMod.val_natCast]
        have hlt : 2 ^ (m - 1) < 2 ^ m := by
          exact Nat.pow_lt_pow_right (by norm_num) (Nat.sub_lt hm (by norm_num))
        rw [Nat.mod_eq_of_lt hlt]
      rw [hval]
      have hgcd : Nat.gcd (2 ^ m) (2 ^ (m - 1)) = 2 ^ (m - 1) := by
        exact Nat.gcd_eq_right (pow_dvd_pow 2 (by omega : m - 1 ≤ m))
      rw [hgcd]
      have hdiv : 2 ^ m / 2 ^ (m - 1) = 2 := by
        have hpow : 2 ^ (m - (m - 1)) * 2 ^ (m - 1) = 2 ^ m :=
          Nat.pow_sub_mul_pow 2 (by omega : m - 1 ≤ m)
        have hsub : m - (m - 1) = 1 := by omega
        rw [← hpow, hsub]
        norm_num
      exact hdiv
    rw [h] at hord
    norm_num at hord
  have huniq : ∀ x : DihedralGroup (2 ^ m), x ∈ R → x ≠ 1 → x ^ 2 = 1 → x = z := by
    intro x hxR hx1 hx2
    have hxmem : (⟨x, hxR⟩ : R) ≠ 1 := by
      intro h
      apply hx1
      exact congrArg Subtype.val h
    have hxpow : (⟨x, hxR⟩ : R) ^ 2 = 1 := by
      apply Subtype.ext
      simpa using hx2
    have hzmem : (⟨z, hzR⟩ : R) ≠ 1 := by
      intro h
      apply hzne
      exact congrArg Subtype.val h
    have hzpow : (⟨z, hzR⟩ : R) ^ 2 = 1 := by
      apply Subtype.ext
      simpa using hz2
    have heq : (⟨x, hxR⟩ : R) = (⟨z, hzR⟩ : R) :=
      unique_involution_of_cyclic_two_group (inferInstance : IsCyclic (↥R)) hm hRcard
        (⟨x, hxR⟩ : R) (⟨z, hzR⟩ : R) hxmem hxpow hzmem hzpow
    exact congrArg Subtype.val heq
  by_contra hznot
  have hz_of_ne : (D ⊓ R ≠ ⊥) → z ∈ D := by
    intro hne
    rcases (Subgroup.ne_bot_iff_exists_ne_one.mp hne) with ⟨x, hxne⟩
    let H : Subgroup (DihedralGroup (2 ^ m)) := Subgroup.zpowers (x : DihedralGroup (2 ^ m))
    have hHleD : H ≤ D := by
      intro y hy
      rcases (Subgroup.mem_zpowers_iff.mp hy) with ⟨k, rfl⟩
      exact D.zpow_mem x.2.1 k
    have hHleR : H ≤ R := by
      intro y hy
      rcases (Subgroup.mem_zpowers_iff.mp hy) with ⟨k, rfl⟩
      exact Subgroup.zpow_mem R x.2.2 k
    have h2dvd : 2 ∣ Nat.card (↥H) := by
      have hordpos : 1 < orderOf (x : DihedralGroup (2 ^ m)) := by
        by_contra hle
        have hord : orderOf (x : DihedralGroup (2 ^ m)) = 1 := by
          have hpos : 0 < orderOf (x : DihedralGroup (2 ^ m)) := orderOf_pos (x : DihedralGroup (2 ^ m))
          omega
        apply hxne
        apply Subtype.ext
        exact (orderOf_eq_one_iff.mp hord)
      have horddvd : orderOf (x : DihedralGroup (2 ^ m)) ∣ 2 ^ m := by
        have hcard : Nat.card (↥H) ∣ Nat.card (↥R) := Subgroup.card_dvd_of_le hHleR
        rwa [Nat.card_zpowers, hRcard] at hcard
      have h2dvd_ord : 2 ∣ orderOf (x : DihedralGroup (2 ^ m)) := by
        rcases (Nat.dvd_prime_pow Nat.prime_two).mp horddvd with ⟨a, ha, hapow⟩
        have ha_pos : 1 ≤ a := by
          by_contra ha0
          have hord1 : orderOf (x : DihedralGroup (2 ^ m)) = 1 := by
            simpa [show a = 0 by omega] using hapow
          omega
        exact ⟨2 ^ (a - 1), by
          rw [hapow, ← pow_succ']
          congr 1
          omega⟩
      rwa [Nat.card_zpowers]
    rcases exists_prime_orderOf_dvd_card' (G := ↥H) 2 h2dvd with ⟨y, hyord⟩
    have hyG : (y : DihedralGroup (2 ^ m)) ∈ R := hHleR y.2
    have hy1 : (y : DihedralGroup (2 ^ m)) ≠ 1 := by
      intro h
      have hyord2 : orderOf y = 2 := hyord
      have hyord1 : orderOf y = 1 := by
        exact (orderOf_eq_one_iff.mpr (by
          apply Subtype.ext
          exact h))
      omega
    have hy2 : (y : DihedralGroup (2 ^ m)) ^ 2 = 1 := by
      have hy2' : y ^ 2 = 1 := (orderOf_dvd_iff_pow_eq_one (x := y) (n := 2)).1 (by
        simpa [hyord])
      exact congrArg Subtype.val hy2'
    have heq : (y : DihedralGroup (2 ^ m)) = z := huniq (y : DihedralGroup (2 ^ m)) hyG hy1 hy2
    have hyD : (y : DihedralGroup (2 ^ m)) ∈ D := hHleD y.2
    exact heq ▸ hyD
  have hDint_bot : D ⊓ R = ⊥ := by
    by_contra hne
    exact hznot (hz_of_ne hne)
  have hDle2 : Nat.card (↥D) ≤ 2 := by
    have hRnormal : (R : Subgroup (DihedralGroup (2 ^ m))).Normal := by
      apply Subgroup.normal_of_index_eq_two
      have htot : Nat.card (DihedralGroup (2 ^ m)) = 2 * 2 ^ m := DihedralGroup.nat_card
      have hprod := Subgroup.card_mul_index R
      rw [htot, hRcard] at hprod
      have hprod' : 2 ^ m * R.index = 2 ^ m * 2 := by
        rw [hprod, mul_comm]
      exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ m) hprod'
    let : (R : Subgroup (DihedralGroup (2 ^ m))).Normal := hRnormal
    let q : DihedralGroup (2 ^ m) →* (DihedralGroup (2 ^ m)) ⧸ R := QuotientGroup.mk' R
    have hker : q.ker = R := by
      ext x
      simp [q, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
    have hinj : Function.Injective (fun x : ↥D => q (x : DihedralGroup (2 ^ m))) := by
      intro x y hxy
      change q (x : DihedralGroup (2 ^ m)) = q (y : DihedralGroup (2 ^ m)) at hxy
      apply Subtype.ext
      have hkR : (x : DihedralGroup (2 ^ m))⁻¹ * (y : DihedralGroup (2 ^ m)) ∈ R := by
        rw [← hker]
        rw [MonoidHom.mem_ker]
        rw [map_mul, map_inv, hxy]
        simp
      have hbot : (x : DihedralGroup (2 ^ m))⁻¹ * (y : DihedralGroup (2 ^ m)) ∈
          (⊥ : Subgroup (DihedralGroup (2 ^ m))) := by
        have hkD : (x : DihedralGroup (2 ^ m))⁻¹ * (y : DihedralGroup (2 ^ m)) ∈ D :=
          D.mul_mem (D.inv_mem x.2) y.2
        rw [← hDint_bot]
        exact ⟨hkD, hkR⟩
      have hxyeq : (x : DihedralGroup (2 ^ m)) = (y : DihedralGroup (2 ^ m)) := by
        have hxy1 : (x : DihedralGroup (2 ^ m))⁻¹ * (y : DihedralGroup (2 ^ m)) = 1 :=
          (Subgroup.mem_bot (x := (x : DihedralGroup (2 ^ m))⁻¹ * (y : DihedralGroup (2 ^ m)))).mp hbot
        calc
          (x : DihedralGroup (2 ^ m)) = (x : DihedralGroup (2 ^ m)) * 1 := by simp
          _ = (x : DihedralGroup (2 ^ m)) *
              ((x : DihedralGroup (2 ^ m))⁻¹ * (y : DihedralGroup (2 ^ m))) := by rw [hxy1]
          _ = (y : DihedralGroup (2 ^ m)) := by group
      exact hxyeq
    have hle : Nat.card (↥D) ≤ Nat.card ((DihedralGroup (2 ^ m)) ⧸ R) :=
      Nat.card_le_card_of_injective (fun x : ↥D => q (x : DihedralGroup (2 ^ m))) hinj
    rw [← Subgroup.index_eq_card R] at hle
    have hindex : R.index = 2 := by
      have htot : Nat.card (DihedralGroup (2 ^ m)) = 2 * 2 ^ m := DihedralGroup.nat_card
      have hprod := Subgroup.card_mul_index R
      rw [htot, hRcard] at hprod
      have hprod' : 2 ^ m * R.index = 2 ^ m * 2 := by
        rw [hprod, mul_comm]
      exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ m) hprod'
    rwa [hindex] at hle
  omega


/-- The centralizer of a reflection in a dihedral `2`-group is a Klein four
group: `{r 0, r (2^(m-1)), sr j, sr (j + 2^(m-1))}`. -/
public theorem card_centralizer_sr_eq_four
    {m : ℕ} (hm : 2 ≤ m) (j : ZMod (2 ^ m)) :
    Nat.card (↥(Subgroup.centralizer ({DihedralGroup.sr j} : Set (DihedralGroup (2 ^ m))))) = 4 := by
  classical
  let h : ZMod (2 ^ m) := 2 ^ (m - 1)
  let C : Subgroup (DihedralGroup (2 ^ m)) :=
    Subgroup.centralizer ({DihedralGroup.sr j} : Set (DihedralGroup (2 ^ m)))
  have hne0 : h ≠ 0 := by
    intro hz
    have hval0 : h.val = 0 := by rw [hz]; simp
    have hpow_cast : ((2 : ℕ) : ZMod (2 ^ m)) ^ (m - 1) = ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
      exact_mod_cast (Nat.cast_pow (2 : ℕ) (m - 1) :
        ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) = ((2 : ℕ) : ZMod (2 ^ m)) ^ (m - 1)).symm
    have hval : h.val = 2 ^ (m - 1) := by
      dsimp [h]
      have hconv : (2 ^ (m - 1) : ZMod (2 ^ m)) = ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
        simpa using hpow_cast
      rw [hconv]
      rw [ZMod.val_natCast]
      have hlt : 2 ^ (m - 1) < 2 ^ m := by
        exact Nat.pow_lt_pow_right (by norm_num) (by omega : m - 1 < m)
      rw [Nat.mod_eq_of_lt hlt]
    have hpos : 0 < 2 ^ (m - 1) := pow_pos (by norm_num) (m - 1)
    omega
  have h2h : (2 : ZMod (2 ^ m)) * h = 0 := by
    exact (zmod_two_mul_eq_zero_iff hm h).mpr (Or.inr rfl)
  have hneg : -h = h := by
    exact (neg_eq_iff_add_eq_zero).mpr (by simpa [two_mul] using h2h)
  have hset : (C : Set (DihedralGroup (2 ^ m))) = {DihedralGroup.r 0, DihedralGroup.r h, DihedralGroup.sr j, DihedralGroup.sr (j + h)} := by
    ext x
    constructor
    · intro hx
      have hxc : x ∈ Subgroup.centralizer ({DihedralGroup.sr j} : Set (DihedralGroup (2 ^ m))) := by
        simpa [C] using hx
      have hcomm : DihedralGroup.sr j * x = x * DihedralGroup.sr j :=
        (Subgroup.mem_centralizer_iff (g := x) (s := ({DihedralGroup.sr j} : Set (DihedralGroup (2 ^ m))))).1 hxc
          (DihedralGroup.sr j) (by simp)
      rcases dihedralGroup_cases x with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · have hji : j + i = j - i := by
          have hs : DihedralGroup.sr (j + i) = DihedralGroup.sr (j - i) := by
            rw [← DihedralGroup.sr_mul_r, ← DihedralGroup.r_mul_sr]
            exact hcomm
          exact (DihedralGroup.sr.injEq (j + i) (j - i)).mp hs
        have hi : i = -i := by
          calc
            i = (j + i) - j := by abel
            _ = (j - i) - j := by rw [hji]
            _ = -i := by abel
        have hi1 : i + i = (-i) + i := congrArg (fun z : ZMod (2 ^ m) => z + i) hi
        have hi' : i + i = 0 := by
          calc
            i + i = (-i) + i := hi1
            _ = 0 := by simp
        have h2i : 2 * i = 0 := by
          calc
            2 * i = i + i := by rw [two_mul]
            _ = 0 := hi'
        rcases (zmod_two_mul_eq_zero_iff hm i).mp h2i with hi0 | hih
        · simp [hi0]
        · simp [hih, h]
      · have hij : i - j = j - i := by
          have hs : DihedralGroup.r (i - j) = DihedralGroup.r (j - i) := by
            rw [← DihedralGroup.sr_mul_sr, ← DihedralGroup.sr_mul_sr]
            exact hcomm
          exact (DihedralGroup.r.injEq (i - j) (j - i)).mp hs
        have h2ij : 2 * (i - j) = 0 := by
          calc
            2 * (i - j) = (i - j) + (i - j) := by rw [two_mul]
            _ = (i - j) + (j - i) := by rw [hij]
            _ = 0 := by abel
        rcases (zmod_two_mul_eq_zero_iff hm (i - j)).mp h2ij with h0 | hh
        · have hi : i = j := sub_eq_zero.mp h0
          simp [hi]
        · have hi : i = j + h := by
            calc
              i = (i - j) + j := by abel
              _ = h + j := by rw [hh]
              _ = j + h := by rw [add_comm]
          simp [hi, h]
    · intro hx
      change x ∈ Subgroup.centralizer ({DihedralGroup.sr j} : Set (DihedralGroup (2 ^ m)))
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff.mp hy]
      have hx4 : x = DihedralGroup.r 0 ∨ x = DihedralGroup.r h ∨ x = DihedralGroup.sr j ∨
          x = DihedralGroup.sr (j + h) := by
        simpa using hx
      rcases hx4 with hx0 | hx4
      · rw [hx0]
        simp
      · rcases hx4 with hxh | hx4
        · rw [hxh]
          have hjh : j - h = j + h := by
            rw [sub_eq_add_neg, hneg]
          have hr : DihedralGroup.r h * DihedralGroup.sr j = DihedralGroup.sr j * DihedralGroup.r h := by
            rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r]
            exact congrArg DihedralGroup.sr hjh
          exact hr.symm
        · rcases hx4 with hxs | hx4
          · rw [hxs]
          · rw [hx4]
            have hs : DihedralGroup.sr j * DihedralGroup.sr (j + h) =
                DihedralGroup.sr (j + h) * DihedralGroup.sr j := by
              rw [DihedralGroup.sr_mul_sr, DihedralGroup.sr_mul_sr]
              exact congrArg DihedralGroup.r (by
                calc
                  (j + h) - j = h := by abel
                  _ = -h := hneg.symm
                  _ = j - (j + h) := by abel)
            exact hs
  have hcard_set : (C : Set (DihedralGroup (2 ^ m))).ncard = 4 := by
    rw [hset]
    have h1 : DihedralGroup.r 0 ∉ ({DihedralGroup.r h, DihedralGroup.sr j, DihedralGroup.sr (j + h)} : Set (DihedralGroup (2 ^ m))) := by
      rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
      intro h1
      rcases h1 with h1 | h1
      · exact hne0 ((DihedralGroup.r.injEq 0 h).mp h1).symm
      · rcases h1 with h1 | h1
        · cases h1
        · cases h1
    have h2 : DihedralGroup.r h ∉ ({DihedralGroup.sr j, DihedralGroup.sr (j + h)} : Set (DihedralGroup (2 ^ m))) := by
      rw [Set.mem_insert_iff, Set.mem_singleton_iff]
      intro h2
      rcases h2 with h2 | h2
      · cases h2
      · cases h2
    have h3 : DihedralGroup.sr j ∉ ({DihedralGroup.sr (j + h)} : Set (DihedralGroup (2 ^ m))) := by
      rw [Set.mem_singleton_iff]
      intro h3
      have hjh : j = j + h := (DihedralGroup.sr.injEq j (j + h)).mp h3
      apply hne0
      have h0 : h = 0 := by
        calc
          h = (j + h) - j := by abel
          _ = j - j := by rw [← hjh]
          _ = 0 := by simp
      exact h0
    rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2,
      Set.ncard_insert_of_notMem h3, Set.ncard_singleton]
  have hnat : Nat.card (↥C) = (C : Set (DihedralGroup (2 ^ m))).ncard := by
    exact Nat.card_coe_set_eq (C : Set (DihedralGroup (2 ^ m)))
  rw [hnat, hcard_set]

/-- The central rotation `r (2^(m-1))` is central in the dihedral `2`-group
of order `2^(m+1)` when `m ≥ 2`. -/
public theorem central_rotation_mem_center_dihedral_two_pow
    {m : ℕ} (hm : 2 ≤ m) :
    DihedralGroup.r (2 ^ (m - 1) : ZMod (2 ^ m)) ∈
      Subgroup.center (DihedralGroup (2 ^ m)) := by
  rw [Subgroup.mem_center_iff]
  intro x
  rcases dihedralGroup_cases x with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [DihedralGroup.r_mul_r, DihedralGroup.r_mul_r, add_comm]
  · have hzero : (2 : ZMod (2 ^ m)) * (2 ^ (m - 1) : ZMod (2 ^ m)) = 0 :=
      (zmod_two_mul_eq_zero_iff hm (2 ^ (m - 1) : ZMod (2 ^ m))).mpr (Or.inr rfl)
    have hneg : -(2 ^ (m - 1) : ZMod (2 ^ m)) = 2 ^ (m - 1) := by
      apply neg_eq_iff_add_eq_zero.mpr
      simpa [two_mul] using hzero
    rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r]
    apply congrArg DihedralGroup.sr
    rw [sub_eq_add_neg, hneg]

/-- If an involution of a dihedral `2`-group centralizes a subgroup of
order at least `8`, then it is the central rotation.  This is the branch
`8 ≤ |S ∩ M|` input for Lemma 2.7: the distinguished ambient involution
cannot be a reflection in a larger Sylow subgroup, because the centralizer
of a reflection has order exactly four. -/
public theorem involution_central_of_centralizes_large_subgroup
    {m : ℕ} (hm : 2 ≤ m)
    (t : DihedralGroup (2 ^ m))
    (ht2 : t ^ 2 = 1) (htne : t ≠ 1)
    (Q : Subgroup (DihedralGroup (2 ^ m)))
    (hQcard : 8 ≤ Nat.card (↥Q))
    (htQ : t ∈ Q)
    (htQcent : ∀ q : ↥Q,
      (⟨t, htQ⟩ : ↥Q) * q = q * (⟨t, htQ⟩ : ↥Q)) :
    t ∈ Subgroup.center (DihedralGroup (2 ^ m)) := by
  classical
  rcases dihedralGroup_cases t with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · have hsq : DihedralGroup.r (i + i) = 1 := by
      simpa [pow_two, DihedralGroup.r_mul_r] using ht2
    have hzero : i + i = 0 := by
      have h := (DihedralGroup.r.injEq (i + i) 0).mp hsq
      simpa using h
    have h2i : (2 : ZMod (2 ^ m)) * i = 0 := by
      rw [two_mul, hzero]
    rcases (zmod_two_mul_eq_zero_iff hm i).mp h2i with hi0 | hic
    · exfalso
      apply htne
      rw [hi0]
      simp
    · rw [hic]
      exact central_rotation_mem_center_dihedral_two_pow hm
  · let C : Subgroup (DihedralGroup (2 ^ m)) :=
      Subgroup.centralizer ({DihedralGroup.sr i} : Set (DihedralGroup (2 ^ m)))
    have hQleC : Q ≤ C := by
      intro q hq
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff.mp hy]
      exact congrArg Subtype.val (htQcent ⟨q, hq⟩)
    have hCcard : Nat.card (↥C) = 4 := card_centralizer_sr_eq_four hm i
    have hQcard_le : Nat.card (↥Q) ≤ 4 := by
      have hle : Nat.card (↥Q) ≤ Nat.card (↥C) := Subgroup.card_le_of_le hQleC
      rwa [hCcard] at hle
    omega

/-- Transport of `involution_central_of_centralizes_large_subgroup` along a
dihedral model equivalence. -/
public theorem central_of_centralizes_large_subgroup_of_dihedral
    {A : Type u} [Group A] [Finite A]
    (t : A) (ht2 : t ^ 2 = 1) (htne : t ≠ 1)
    {m : ℕ} (hm : 2 ≤ m) (e : A ≃* DihedralGroup (2 ^ m))
    (Q : Subgroup A) (hQcard : 8 ≤ Nat.card (↥Q))
    (htQ : t ∈ Q)
    (htQcent : ∀ q : ↥Q,
      (⟨t, htQ⟩ : ↥Q) * q = q * (⟨t, htQ⟩ : ↥Q)) :
    t ∈ Subgroup.center A := by
  classical
  let Q' : Subgroup (DihedralGroup (2 ^ m)) := Q.map e.toMonoidHom
  have hQ'card : 8 ≤ Nat.card (↥Q') := by
    have hEq : Q ≃* Q' := Q.equivMapOfInjective e.toMonoidHom e.injective
    have hcard : Nat.card (↥Q') = Nat.card (↥Q) := (Nat.card_congr hEq.toEquiv).symm
    rwa [hcard]
  have htQ' : e t ∈ Q' := Subgroup.mem_map.mpr ⟨t, htQ, rfl⟩
  have htQ'cent : ∀ q' : ↥Q',
      (⟨e t, htQ'⟩ : ↥Q') * q' = q' * (⟨e t, htQ'⟩ : ↥Q') := by
    intro q'
    rcases Subgroup.mem_map.mp q'.2 with ⟨q, hq, hqval⟩
    have hcomm : t * q = q * t := by
      have h := htQcent ⟨q, hq⟩
      exact congrArg Subtype.val h
    have hcomm' : e t * e q = e q * e t := by
      calc
        e t * e q = e (t * q) := (e.map_mul t q).symm
        _ = e (q * t) := by rw [hcomm]
        _ = e q * e t := e.map_mul q t
    apply Subtype.ext
    change e t * q' = q' * e t
    rw [← hqval]
    exact hcomm'
  have hcentral' : e t ∈ Subgroup.center (DihedralGroup (2 ^ m)) :=
    involution_central_of_centralizes_large_subgroup hm (e t)
      (by simpa using congrArg e ht2)
      (by intro h
          apply htne
          exact e.injective (by simpa using h))
      Q' hQ'card htQ' htQ'cent
  rw [Subgroup.mem_center_iff]
  intro x
  apply e.injective
  calc
    e (x * t) = e x * e t := e.map_mul x t
    _ = e t * e x := Subgroup.mem_center_iff.mp hcentral' (e x)
    _ = e (t * x) := (e.map_mul t x).symm

/-- If `N` is normal in a finite group and `P` is a Sylow `2`-subgroup,
then `N ∩ P` has the same `2`-part as `N`.  In particular, `4 ∣ |N|`
implies `4 ∣ |N ∩ P|`.  This is the standard normal-Sylow intersection
fact, proved here by comparing the Sylow orders in `G`, `N`, and `G/N`. -/
public theorem four_dvd_inf_sylow_of_normal
    {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (P : Sylow 2 G)
    (h4 : 4 ∣ Nat.card N) :
    4 ∣ Nat.card (↥(N ⊓ (P : Subgroup G))) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let qP : P →* G ⧸ N := q.comp (P : Subgroup G).subtype
  let D : Subgroup G := N ⊓ (P : Subgroup G)
  let D' : Subgroup P := D.subgroupOf P
  have hker : qP.ker = D' := by
    ext x
    simp [qP, q, D, D', QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  let Pq : Sylow 2 (G ⧸ N) := P.mapSurjective (QuotientGroup.mk'_surjective N)
  have hrange : qP.range = (Pq : Subgroup (G ⧸ N)) := by
    rw [Sylow.coe_mapSurjective]
    ext x
    constructor
    · intro hx
      rcases hx with ⟨p, rfl⟩
      exact Subgroup.mem_map.mpr ⟨(p : G), p.property, rfl⟩
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨g, hg, hx⟩
      refine ⟨⟨g, hg⟩, ?_⟩
      simpa [qP, q] using hx
  have hDindex : D'.index = Nat.card (↥(Pq : Subgroup (G ⧸ N))) := by
    rw [← hker, Subgroup.index_eq_card]
    rw [← hrange]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange qP).toEquiv
  have hprod : Nat.card (↥D') * Nat.card (↥(Pq : Subgroup (G ⧸ N))) =
      Nat.card (↥P) := by
    rw [← hDindex]
    exact D'.card_mul_index
  have hDp : IsPGroup 2 (↥D') := by
    exact P.isPGroup'.to_subgroup D'
  rcases (IsPGroup.iff_card (G := ↥D')).mp hDp with ⟨e, hDcard⟩
  have hPcard : Nat.card (↥P) = 2 ^ (Nat.card G).factorization 2 :=
    Sylow.card_eq_multiplicity P
  have hPqcard : Nat.card (↥(Pq : Subgroup (G ⧸ N))) =
      2 ^ (Nat.card (G ⧸ N)).factorization 2 :=
    Sylow.card_eq_multiplicity Pq
  have hpow : 2 ^ (e + (Nat.card (G ⧸ N)).factorization 2) =
      2 ^ (Nat.card G).factorization 2 := by
    rw [hDcard, hPqcard, hPcard] at hprod
    rw [← pow_add] at hprod
    exact hprod
  have hexp : e + (Nat.card (G ⧸ N)).factorization 2 =
      (Nat.card G).factorization 2 := by
    exact Nat.pow_right_injective (by norm_num : 1 < 2) hpow
  have hGmul : Nat.card G = Nat.card N * Nat.card (G ⧸ N) := by
    rw [← N.index_eq_card]
    exact N.card_mul_index.symm
  have hGfac : (Nat.card G).factorization 2 =
      (Nat.card N).factorization 2 + (Nat.card (G ⧸ N)).factorization 2 := by
    have hfac := Nat.factorization_mul (Nat.card_pos (α := N)).ne'
      (Nat.card_pos (α := G ⧸ N)).ne'
    rw [← hGmul] at hfac
    exact congrArg (fun f : ℕ →₀ ℕ => f 2) hfac
  have heN : e = (Nat.card N).factorization 2 := by omega
  have hNfac : 2 ≤ (Nat.card N).factorization 2 := by
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (Nat.card_pos (α := N)).ne').1
      (by simpa using h4)
  have hDfour : 4 ∣ Nat.card (↥D') := by
    rw [hDcard, heN]
    exact pow_dvd_pow 2 hNfac
  have hDcard' : Nat.card (↥D') = Nat.card (↥D) := by
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := D) (K := (P : Subgroup G)) inf_le_right).toEquiv
  rwa [← hDcard']

/-- Lemma 2.7's local dihedral core: if `t` is a central involution of a
dihedral Sylow `2`-subgroup `P` of `A`, then every normal `N ◁ A` whose
order is divisible by four contains `t`.  For `m = 1` (`|P| = 4`) the
intersection `N ∩ P` already has order four, so it is all of `P`; for
`m ≥ 2` the central involution is unique and the model lemma
`subgroup_card_ge_four_contains_central_rotation` puts it into `N ∩ P`. -/
public theorem normal_subgroup_of_card_div_four_contains_central_involution_of_dihedral
    {A : Type u} [Group A] [Finite A]
    (t : A) (ht : IsInvolution t)
    (P : Sylow 2 A) (htP : t ∈ (P : Subgroup A))
    (htcent : ∀ x : ↥(P : Subgroup A),
      (⟨t, htP⟩ : ↥(P : Subgroup A)) * x = x * (⟨t, htP⟩ : ↥(P : Subgroup A)))
    {m : ℕ} (hm : 1 ≤ m) (e : P ≃* DihedralGroup (2 ^ m))
    {N : Subgroup A} (hN : N.Normal) (h4 : 4 ∣ Nat.card N) :
    t ∈ N := by
  classical
  by_cases hm1 : m = 1
  · have hPcard : Nat.card (↥(P : Subgroup A)) = 4 := by
      rw [hm1] at e
      have hc : Nat.card (↥(P : Subgroup A)) = Nat.card (DihedralGroup (2 ^ 1)) := Nat.card_congr e.toEquiv
      rw [hc]
      norm_num [DihedralGroup.nat_card]
    let D1 : Subgroup A := N ⊓ (P : Subgroup A)
    have hD4 : 4 ∣ Nat.card (↥D1) :=
      four_dvd_inf_sylow_of_normal (G := A) N P h4
    have hDge : 4 ≤ Nat.card (↥D1) :=
      Nat.le_of_dvd (Nat.card_pos (α := D1)) hD4
    have hDP : D1 = (P : Subgroup A) := by
      apply Subgroup.eq_of_le_of_card_ge (H := D1) (K := (P : Subgroup A))
      · exact inf_le_right
      · rw [hPcard]
        exact hDge
    have htD : t ∈ D1 := by
      rw [hDP]
      exact htP
    exact (inf_le_left : D1 ≤ N) htD
  · have hm2 : 2 ≤ m := by omega
    let D : Subgroup A := N ⊓ (P : Subgroup A)
    have hD4 : 4 ∣ Nat.card (↥D) := four_dvd_inf_sylow_of_normal (G := A) N P h4
    have hDge : 4 ≤ Nat.card (↥D) := Nat.le_of_dvd (Nat.card_pos (α := D)) hD4
    let D' : Subgroup P := D.subgroupOf P
    let Dmodel : Subgroup (DihedralGroup (2 ^ m)) := D'.map e.toMonoidHom
    have hD'card : Nat.card (↥D') = Nat.card (↥D) := by
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := D) (K := (P : Subgroup A)) inf_le_right).toEquiv
    have hDmodelcard : Nat.card (↥Dmodel) = Nat.card (↥D') := by
      exact (Nat.card_congr (Subgroup.equivMapOfInjective D' e.toMonoidHom e.injective).toEquiv).symm
    have hDmodelge : 4 ≤ Nat.card (↥Dmodel) := by
      rw [hDmodelcard, hD'card]
      exact hDge
    have hrCmem : DihedralGroup.r (2 ^ (m - 1) : ZMod (2 ^ m)) ∈ Dmodel :=
      subgroup_card_ge_four_contains_central_rotation hm Dmodel hDmodelge
    rcases Subgroup.mem_map.mp hrCmem with ⟨xP, hxD', hxval⟩
    let z : A := (xP : A)
    have hzD : z ∈ D := by
      exact (Subgroup.mem_subgroupOf.mp hxD')
    have hzN : z ∈ N := (inf_le_left : D ≤ N) hzD
    let tP : P := ⟨t, htP⟩
    have htP_center : tP ∈ Subgroup.center (↥(P : Subgroup A)) :=
      Subgroup.mem_center_iff.mpr (fun x => (htcent x).symm)
    have hrCpow : (DihedralGroup.r (2 ^ (m - 1) : ZMod (2 ^ m))) ^ 2 = 1 := by
      rw [pow_two, DihedralGroup.r_mul_r]
      have hz : (2 : ZMod (2 ^ m)) * (2 ^ (m - 1) : ZMod (2 ^ m)) = 0 :=
        (zmod_two_mul_eq_zero_iff hm2 (2 ^ (m - 1) : ZMod (2 ^ m))).mpr (Or.inr rfl)
      have hsum : (2 ^ (m - 1) : ZMod (2 ^ m)) + (2 ^ (m - 1) : ZMod (2 ^ m)) = 0 := by
        simpa [two_mul] using hz
      rw [hsum]
      rfl
    have hrCne : DihedralGroup.r (2 ^ (m - 1) : ZMod (2 ^ m)) ≠ 1 := by
      intro h
      have hvalh : ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)).val = 2 ^ (m - 1) := by
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega : m - 1 < m))]
      have h0 : (2 ^ (m - 1) : ZMod (2 ^ m)) = 0 := by
        have h' := (DihedralGroup.r.injEq (2 ^ (m - 1) : ZMod (2 ^ m)) 0).mp (by simpa using h)
        exact h'
      have hdvd : 2 ^ m ∣ 2 ^ (m - 1) :=
        (ZMod.natCast_eq_zero_iff (2 ^ (m - 1)) (2 ^ m)).mp (by simpa using h0)
      have hpos : 0 < 2 ^ (m - 1) := pow_pos (by norm_num) (m - 1)
      have hle : 2 ^ m ≤ 2 ^ (m - 1) := Nat.le_of_dvd hpos hdvd
      have hlt : 2 ^ (m - 1) < 2 ^ m :=
        Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega : m - 1 < m)
      omega
    have hxval' : e xP = DihedralGroup.r (2 ^ (m - 1) : ZMod (2 ^ m)) := by simpa using hxval
    have hxP_center : xP ∈ Subgroup.center (↥(P : Subgroup A)) := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply e.injective
      calc
        e (y * xP) = e y * e xP := e.map_mul y xP
        _ = e y * DihedralGroup.r (2 ^ (m - 1) : ZMod (2 ^ m)) := by rw [hxval']
        _ = DihedralGroup.r (2 ^ (m - 1) : ZMod (2 ^ m)) * e y :=
          Subgroup.mem_center_iff.mp (central_rotation_mem_center_dihedral_two_pow hm2) (e y)
        _ = e xP * e y := by rw [hxval']
        _ = e (xP * y) := (e.map_mul xP y).symm
    have hxP_pow : xP ^ 2 = 1 := by
      apply e.injective
      calc
        e (xP ^ 2) = e xP ^ 2 := e.toMonoidHom.map_pow xP 2
        _ = (DihedralGroup.r (2 ^ (m - 1) : ZMod (2 ^ m))) ^ 2 := by rw [hxval']
        _ = 1 := hrCpow
        _ = e 1 := by simp
    have hxP_ne : xP ≠ 1 := by
      intro h
      apply hrCne
      calc
        DihedralGroup.r (2 ^ (m - 1) : ZMod (2 ^ m)) = e xP := hxval'.symm
        _ = e 1 := by rw [h]
        _ = 1 := by simp
    have hetP_center : e tP ∈ Subgroup.center (DihedralGroup (2 ^ m)) := by
      rw [Subgroup.mem_center_iff]
      intro y
      rcases e.surjective y with ⟨p, rfl⟩
      have hcomm := htcent p
      have h := congrArg e hcomm
      rw [e.map_mul, e.map_mul] at h
      exact h.symm
    have htPpow : tP ^ 2 = (1 : P) := by
      apply Subtype.ext
      exact ht.2
    have hetP_pow : (e tP) ^ 2 = 1 := by
      calc
        (e tP) ^ 2 = e (tP ^ 2) := (e.toMonoidHom.map_pow tP 2).symm
        _ = e 1 := by rw [htPpow]
        _ = 1 := by simp
    have hetP_ne : e tP ≠ 1 := by
      intro h
      have htP1 : tP = 1 := e.injective (by simpa using h)
      have ht1 : t = 1 := congrArg (fun x : P => (x : A)) htP1
      exact ht.1 ht1
    have hetP : e tP = DihedralGroup.r (2 ^ (m - 1) : ZMod (2 ^ m)) :=
      unique_central_involution_of_dihedral_two_pow hm2 (e tP) hetP_center hetP_pow hetP_ne
    have htP_eq : tP = xP := by
      apply e.injective
      calc
        e tP = DihedralGroup.r (2 ^ (m - 1) : ZMod (2 ^ m)) := hetP
        _ = e xP := hxval'.symm
    have hteq : t = z := by
      change t = (xP : A)
      exact congrArg Subtype.val htP_eq
    rwa [hteq]

/-! ## Lemma 2.7: the `8 ≤ |S ∩ M|` branch -/

/-- In the branch `8 ≤ |S ∩ M|`, the distinguished involution `t` lies in
`S ∩ M` (every subgroup of the dihedral Sylow `S` of order at least `8`
contains its unique central involution) and is central in every Sylow
`2`-subgroup of `M` containing `S ∩ M`.  The local dihedral core then forces
`t ∈ N` for every normal `N ◁ M` with `4 | |N|`. -/
private theorem t_mem_N_of_card_div_four_of_S_inter_M_large
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (M : Subgroup G)
    (hMproper : M ≠ ⊤)
    (hSylow : ∀ P : Sylow 2 (↥M), ¬ IsCyclic P)
    (h8 : 8 ≤ Nat.card ↥((c.S : Subgroup G) ⊓ M))
    {N : Subgroup (↥M)} (hN : N.Normal) (h4 : 4 ∣ Nat.card N) :
    c.t ∈ N.map M.subtype := by
  classical
  obtain ⟨e⟩ := c.dihedralEquiv
  have hScard : Nat.card (↥(c.S : Subgroup G)) = 2 * 2 ^ c.m := by
    exact (Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card
  have hm2 : 2 ≤ c.m := by
    have hSge : 8 ≤ Nat.card (↥(c.S : Subgroup G)) :=
      h8.trans (Subgroup.card_le_of_le inf_le_left)
    have hSge4 : 4 ≤ 2 ^ c.m := by
      apply Nat.le_of_mul_le_mul_left (by simpa [hScard] using hSge) (by norm_num : 0 < 2)
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hSge4
  let Dsub : Subgroup (↥(c.S : Subgroup G)) :=
    ((c.S : Subgroup G) ⊓ M).subgroupOf (c.S : Subgroup G)
  have hDsubcard : Nat.card (↥Dsub) = Nat.card ↥((c.S : Subgroup G) ⊓ M) := by
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := (c.S : Subgroup G) ⊓ M)
        (K := (c.S : Subgroup G)) inf_le_left).toEquiv
  let Dmodel : Subgroup (DihedralGroup (2 ^ c.m)) := Dsub.map e.toMonoidHom
  have hDmodelcard : Nat.card (↥Dmodel) = Nat.card (↥Dsub) := by
    exact (Nat.card_congr
      (Subgroup.equivMapOfInjective Dsub e.toMonoidHom e.injective).toEquiv).symm
  have hDmodelge : 8 ≤ Nat.card (↥Dmodel) := by
    rw [hDmodelcard, hDsubcard]
    exact h8
  have hrC : DihedralGroup.r (2 ^ (c.m - 1) : ZMod (2 ^ c.m)) ∈ Dmodel :=
    subgroup_card_ge_four_contains_central_rotation (by omega : 1 ≤ c.m) Dmodel (by omega)
  rcases Subgroup.mem_map.mp hrC with ⟨xS, hxSDsub, hxval⟩
  let x : G := (xS : G)
  have hxSM : x ∈ (c.S : Subgroup G) ⊓ M := by
    exact Subgroup.mem_subgroupOf.mp hxSDsub
  let tS : ↥(c.S : Subgroup G) := ⟨c.t, c.S0_le_S c.t_mem_S0⟩
  have htS_central : ∀ s : ↥(c.S : Subgroup G), tS * s = s * tS := by
    intro s
    apply Subtype.ext
    have hsH : (s : G) ∈ c.H := centralizerSetup_S_le_H c s.2
    have hsc : (s : G) ∈ Subgroup.centralizer ({c.t} : Set G) := by
      rw [← c.H_eq_centralizer]
      exact hsH
    have hcomm : c.t * (s : G) = (s : G) * c.t :=
      (Subgroup.mem_centralizer_iff (g := (s : G)) (s := ({c.t} : Set G))).1 hsc c.t (by simp)
    exact hcomm
  have hetS_central : e tS ∈ Subgroup.center (DihedralGroup (2 ^ c.m)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    rcases e.surjective y with ⟨s, rfl⟩
    have h := congrArg e (htS_central s)
    rw [e.map_mul, e.map_mul] at h
    exact h.symm
  have hetS_pow : (e tS) ^ 2 = 1 := by
    calc
      (e tS) ^ 2 = e (tS ^ 2) := (e.toMonoidHom.map_pow tS 2).symm
      _ = e 1 := by
        congr 1
        apply Subtype.ext
        exact c.t_involution.2
      _ = 1 := by simp
  have hetS_ne : e tS ≠ 1 := by
    intro h
    have htS1 : tS = 1 := e.injective (by simpa using h)
    apply c.t_involution.1
    exact congrArg Subtype.val htS1
  have hetS : e tS = DihedralGroup.r (2 ^ (c.m - 1) : ZMod (2 ^ c.m)) :=
    unique_central_involution_of_dihedral_two_pow hm2 (e tS) hetS_central hetS_pow hetS_ne
  have hxval' : e xS = DihedralGroup.r (2 ^ (c.m - 1) : ZMod (2 ^ c.m)) := by
    simpa using hxval
  have htS_eq : tS = xS := e.injective (by
    calc
      e tS = DihedralGroup.r (2 ^ (c.m - 1) : ZMod (2 ^ c.m)) := hetS
      _ = e xS := hxval'.symm)
  have hteq : c.t = x := by
    change c.t = (xS : G)
    exact congrArg Subtype.val htS_eq
  have htSM : c.t ∈ (c.S : Subgroup G) ⊓ M := by
    exact hteq ▸ hxSM
  let tM : ↥M := ⟨c.t, htSM.2⟩
  let SM : Subgroup (↥M) := ((c.S : Subgroup G) ⊓ M).subgroupOf M
  have htSM' : tM ∈ SM := by
    simpa [tM] using (Subgroup.mem_subgroupOf.mpr htSM)
  have hSMcard : Nat.card (↥SM) = Nat.card ↥((c.S : Subgroup G) ⊓ M) := by
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := (c.S : Subgroup G) ⊓ M)
        (K := M) inf_le_right).toEquiv
  have hDsub_p : IsPGroup 2 (↥Dsub) := c.S.isPGroup'.to_subgroup Dsub
  have hSM_p : IsPGroup 2 (↥SM) := by
    let eDsubSM : Dsub ≃* SM := by
      exact (Subgroup.subgroupOfEquivOfLe (H := (c.S : Subgroup G) ⊓ M)
        (K := (c.S : Subgroup G)) inf_le_left).trans
        (Subgroup.subgroupOfEquivOfLe (H := (c.S : Subgroup G) ⊓ M)
          (K := M) inf_le_right).symm
    exact IsPGroup.of_equiv hDsub_p eDsubSM
  obtain ⟨P, hSMP⟩ := IsPGroup.exists_le_sylow (G := ↥M) (p := 2) hSM_p
  have hPge8 : 8 ≤ Nat.card (↥(P : Subgroup (↥M))) := by
    calc
      8 ≤ Nat.card ↥((c.S : Subgroup G) ⊓ M) := h8
      _ = Nat.card (↥SM) := hSMcard.symm
      _ ≤ Nat.card (↥(P : Subgroup (↥M))) := Subgroup.card_le_of_le hSMP
  have hDM : IsDGroup (↥M) := properSubgroups_areDGroups hmin M hMproper
  have hSylowM : HasCyclicOrDihedralSylowTwo (↥M) := by
    rcases hDM with ⟨hS, _⟩ | ⟨hS, _⟩ | ⟨hS, _K, _hKp, _L, _hL, _hLidx, _hLmodel⟩
    · exact hS
    · exact hS
    · exact hS
  rcases hSylowM P with hcyc | ⟨mP, hmP, eP⟩
  · exact False.elim (hSylow P hcyc)
  · have hPcard : Nat.card (↥(P : Subgroup (↥M))) = 2 * 2 ^ mP := by
      exact (Nat.card_congr eP.some.toEquiv).trans DihedralGroup.nat_card
    have hmP2 : 2 ≤ mP := by
      have hPge4 : 4 ≤ 2 ^ mP := by
        apply Nat.le_of_mul_le_mul_left (by simpa [hPcard] using hPge8) (by norm_num : 0 < 2)
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hPge4
    have htP : tM ∈ (P : Subgroup (↥M)) := hSMP htSM'
    let tP : ↥(P : Subgroup (↥M)) := ⟨tM, htP⟩
    have htSMcent : ∀ q : ↥SM, tM * q = q * tM := by
      intro q
      apply Subtype.ext
      have hqS : (q : G) ∈ (c.S : Subgroup G) :=
        (Subgroup.mem_subgroupOf.mp q.2).1
      have hqH : (q : G) ∈ c.H := centralizerSetup_S_le_H c hqS
      have hqc : (q : G) ∈ Subgroup.centralizer ({c.t} : Set G) := by
        rw [← c.H_eq_centralizer]
        exact hqH
      have hcomm : c.t * (q : G) = (q : G) * c.t :=
        (Subgroup.mem_centralizer_iff (g := (q : G)) (s := ({c.t} : Set G))).1 hqc c.t (by simp)
      exact hcomm
    let SMonP : Subgroup (↥(P : Subgroup (↥M))) :=
      SM.subgroupOf (P : Subgroup (↥M))
    have hSMonPcard : Nat.card (↥SMonP) = Nat.card (↥SM) := by
      exact Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := SM) (K := (P : Subgroup (↥M))) hSMP).toEquiv
    have hSMonPge : 8 ≤ Nat.card (↥SMonP) := by
      rw [hSMonPcard, hSMcard]
      exact h8
    have htSMonP : tP ∈ SMonP := by
      exact Subgroup.mem_subgroupOf.mpr htSM'
    have htSMonPcent : ∀ q : ↥SMonP,
        (⟨tP, htSMonP⟩ : ↥SMonP) * q = q * (⟨tP, htSMonP⟩ : ↥SMonP) := by
      intro q
      apply Subtype.ext
      apply Subtype.ext
      have hqSM : (q : ↥M) ∈ SM := Subgroup.mem_subgroupOf.mp q.2
      change tM * (q : ↥M) = (q : ↥M) * tM
      simpa using htSMcent ⟨(q : ↥M), hqSM⟩
    have hcenterP : tP ∈ Subgroup.center (↥(P : Subgroup (↥M))) :=
      central_of_centralizes_large_subgroup_of_dihedral (A := ↥(P : Subgroup (↥M)))
        tP (by
          apply Subtype.ext
          apply Subtype.ext
          simpa [tP, tM] using c.t_involution.2)
        (by intro h
            apply c.t_involution.1
            exact congrArg Subtype.val
              (congrArg (fun x : ↥(P : Subgroup (↥M)) => (x : ↥M)) h))
        hmP2 eP.some SMonP hSMonPge htSMonP htSMonPcent
    have htcent : ∀ x : ↥(P : Subgroup (↥M)), tP * x = x * tP := by
      intro x
      exact (Subgroup.mem_center_iff.mp hcenterP x).symm
    have htM_inv : IsInvolution tM := by
      constructor
      · intro h
        apply c.t_involution.1
        exact congrArg Subtype.val h
      · apply Subtype.ext
        exact c.t_involution.2
    have htN : tM ∈ N :=
      normal_subgroup_of_card_div_four_contains_central_involution_of_dihedral
        (A := ↥M) tM htM_inv (P := P) htP htcent hmP eP.some hN h4
    exact Subgroup.mem_map.mpr ⟨tM, htN, rfl⟩

/-- In the branch `|S| = 4`, every Sylow `2`-subgroup of `M` is a Klein
four-group.  Once Theorem 2.6 supplies `t ∈ M`, a normal subgroup `N ◁ M`
with `4 | |N|` intersects every such Sylow subgroup in the whole Sylow
subgroup, so it contains `t`. -/
private theorem t_mem_N_of_card_div_four_of_S_card_four
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (M : Subgroup G)
    (hMproper : M ≠ ⊤)
    (hSylow : ∀ P : Sylow 2 (↥M), ¬ IsCyclic P)
    (hS4 : Nat.card c.S = 4)
    (htM : c.t ∈ M)
    {N : Subgroup (↥M)} (hN : N.Normal) (h4 : 4 ∣ Nat.card N) :
    c.t ∈ N.map M.subtype := by
  classical
  let tM : ↥M := ⟨c.t, htM⟩
  have htp : IsPGroup 2 (Subgroup.zpowers tM) := by
    apply IsPGroup.of_card (n := 1)
    have hord : orderOf tM = 2 := orderOf_eq_prime
      (by apply Subtype.ext; exact c.t_involution.2)
      (by
        intro h
        apply c.t_involution.1
        exact congrArg Subtype.val h)
    simp [Nat.card_zpowers, hord]
  obtain ⟨P, hTleP⟩ := IsPGroup.exists_le_sylow (G := ↥M) (p := 2) htp
  have htP : tM ∈ (P : Subgroup (↥M)) := hTleP (Subgroup.mem_zpowers tM)
  have hDM : IsDGroup (↥M) := properSubgroups_areDGroups hmin M hMproper
  have hSylowM : HasCyclicOrDihedralSylowTwo (↥M) := by
    rcases hDM with ⟨hS, _⟩ | ⟨hS, _⟩ | ⟨hS, _K, _hKp, _L, _hL, _hLidx, _hLmodel⟩
    · exact hS
    · exact hS
    · exact hS
  rcases hSylowM P with hcyc | ⟨mP, hmP, eP⟩
  · exact False.elim (hSylow P hcyc)
  · have hPcard : Nat.card (↥(P : Subgroup (↥M))) = 2 * 2 ^ mP := by
      exact (Nat.card_congr eP.some.toEquiv).trans DihedralGroup.nat_card
    let PG : Subgroup G := (P : Subgroup (↥M)).map M.subtype
    have hPGcard : Nat.card (↥PG) = Nat.card (↥(P : Subgroup (↥M))) := by
      exact Subgroup.card_map_of_injective
        (K := (P : Subgroup (↥M))) (f := M.subtype) M.subtype_injective
    have hPGp : IsPGroup 2 (↥PG) := P.isPGroup'.map M.subtype
    obtain ⟨Q, hPGQ⟩ := hPGp.exists_le_sylow (G := G)
    have hQcard : Nat.card (↥(Q : Subgroup G)) = 4 := by
      calc
        Nat.card (↥(Q : Subgroup G)) = Nat.card (↥(c.S : Subgroup G)) :=
          Nat.card_congr (Sylow.equiv Q c.S).toEquiv
        _ = 4 := hS4
    have hPGleQ : Nat.card (↥PG) ≤ Nat.card (↥(Q : Subgroup G)) :=
      Subgroup.card_le_of_le hPGQ
    have hPle4 : Nat.card (↥(P : Subgroup (↥M))) ≤ 4 := by
      calc
        Nat.card (↥(P : Subgroup (↥M))) = Nat.card (↥PG) := hPGcard.symm
        _ ≤ Nat.card (↥(Q : Subgroup G)) := hPGleQ
        _ = 4 := hQcard
    have hmP1 : mP = 1 := by
      by_contra hne
      have hmPge : 2 ≤ mP := by omega
      have hPge : 8 ≤ Nat.card (↥(P : Subgroup (↥M))) := by
        rw [hPcard]
        have hpow : 8 ≤ 2 * 2 ^ mP := by
          rw [show 2 * 2 ^ mP = 2 ^ (mP + 1) by
            rw [pow_succ, mul_comm]]
          exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 3 ≤ mP + 1)
        exact hpow
      omega
    have hPcard4 : Nat.card (↥(P : Subgroup (↥M))) = 4 := by
      rw [hPcard, hmP1]
      norm_num [DihedralGroup.nat_card]
    let N1 : Subgroup (↥M) := N ⊓ (P : Subgroup (↥M))
    have hN1_4 : 4 ∣ Nat.card (↥N1) :=
      four_dvd_inf_sylow_of_normal (G := ↥M) N P h4
    have hN1_le4 : Nat.card (↥N1) ≤ 4 := by
      exact (Subgroup.card_le_of_le inf_le_right).trans (le_of_eq hPcard4)
    have hN1_card : Nat.card (↥N1) = 4 := by
      apply Nat.le_antisymm hN1_le4
      exact Nat.le_of_dvd (Nat.card_pos (α := N1)) hN1_4
    have hN1_eq : N1 = (P : Subgroup (↥M)) := by
      apply Subgroup.eq_of_le_of_card_ge (H := N1) (K := (P : Subgroup (↥M)))
      · exact inf_le_right
      · rw [hPcard4]
        exact Nat.le_of_dvd (Nat.card_pos (α := N1)) hN1_4
    have htN1 : tM ∈ N1 := by
      rw [hN1_eq]
      exact htP
    exact Subgroup.mem_map.mpr ⟨tM, (inf_le_left : N1 ≤ N) htN1, rfl⟩

/-! ## Lemma 2.7's divisible-by-four step -/

/-- Lemma 2.7's first local claim (Bender p. 221), in the standing minimal
counterexample context: every normal subgroup `N ◁ M` whose order is
divisible by `4` contains the distinguished involution `t`. -/
public theorem normal_subgroup_of_card_div_four_contains_t
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (M : Subgroup G)
    (hM : Lemma27Hypothesis c M)
    (h26 : CentralizerStructure c)
    {N : Subgroup (↥M)} (hN : N.Normal) (h4 : 4 ∣ Nat.card N) :
    c.t ∈ N.map M.subtype := by
  classical
  rcases hM with ⟨hMproper, hControl, hMnotle, hEt, hSylow, hBranch⟩
  rcases hBranch with h8 | hrest
  · exact t_mem_N_of_card_div_four_of_S_inter_M_large hmin c M hMproper hSylow h8 hN h4
  · rcases hrest with hS4 | _htO2
    · have htM : c.t ∈ M := t_mem_M_of_centralizerStructure c M
        ⟨hMproper, hControl, hMnotle, hEt, hSylow, Or.inr (Or.inl hS4)⟩ h26
      exact t_mem_N_of_card_div_four_of_S_card_four hmin c M hMproper hSylow hS4 htM hN h4
    · exact t_mem_N_map_of_mem_twoResidualOf_of_DGroup hmin c M hMproper
        hSylow _htO2 hN h4

/-! ## Gap note: involution with nontrivial fixed points on the odd core -/

/-
REMOVED REGISTERED BRIDGE `exists_involution_centralizer_oddCore_ne_bot`
(2026-08-15T19:10:07Z): the statement is not provable from
`Lemma27Hypothesis` with the currently landed Section-1/2 infrastructure.
The naive implication `F₂'(M) ≠ ⊥ ⟹ ∃ t' ∈ C_S(t), C_{F₂'(M)}(t') ≠ ⊥`
is false: a fixed-point-free involution on `C₇` (`x ↦ x⁻¹`) has trivial
centralizer, so the fixed-point part can be trivial even when the odd core
is nontrivial.  The paper's final step
`[t, C_{F₂'(M)}(t')] = C_{F₂'(M)}(t') ≠ 1` needs the full dihedral-Sylow
inversion analysis of Lemma 2.7 (Section 1.5 facts plus the non-cyclic
dihedral structure of `S ∩ M`); it is returned as an exact gap in the task
card.
-/

/-! ## Gap note: the final `[S, U] ≰ F(U)` contradiction -/

/-
REMOVED REGISTERED BRIDGE `commutator_S_U_not_le_FU` (2026-08-15T19:10:07Z):
this statement composes the removed involution-fixed-points bridge with the
`π`-group/nilpotent structure of `F(U)` and the minimal-counterexample
involution-conjugacy facts; it cannot be discharged while the
`exists_involution_centralizer_oddCore_ne_bot` step is unavailable.  It is
returned as an exact gap in the task card.
-/

/-! ## Bender 1.1(iv) transfer (with coprimality) -/

/-- Bender's coprime-action transfer 1.1(iv), normal case: if the `p`-group
`P` acts on the `p'`-group `K` (here: coprime orders plus solvability of
`K`), centralizes a normal subgroup `K₁ ⊴ K`, and `C_K(K₁) ≤ K₁`, then
`P` centralizes `K`.

Proof (no Fitting subgroup needed): the three-subgroups lemma gives
`[K,P] ≤ K ⊓ C_G(K₁) ≤ K₁`, hence `P` centralizes `[K,P]`, i.e.
`commutatorAction₂ = ⊥`; the coprime-action identity
`[K,P] = [K,P,P]` (`commutatorAction₂_eq_commutatorAction_of_coprime`)
then forces `[K,P] = ⊥`.

The statement without coprimality is false (in `S₃`, `K = K₁ = C₃`,
`P = K₁`), and coprimality of orders alone without the action being a
`p`-group on a `p'`-group is also insufficient: `P = C₃` acting unipotently
on `K = C₃²` has `[K,P] = C_K(P) ≠ 1` while `[K,P,P] = 1`.  Hence the
hypotheses `Nat.Coprime (Nat.card P) (Nat.card K)` and `IsSolvable K` are
kept (drift recorded in the task card; the applications have `K = O₂'(N)`
of odd order, solvable by Feit--Thompson). -/
public theorem centralizes_of_normal_selfCentralizing_coprime
    {G : Type u} [Group G] [Finite G]
    (P K K₁ : Subgroup G)
    (hPK : P ≤ Subgroup.normalizer (K : Set G))
    (hK1_le_K : K₁ ≤ K)
    (hK1N : (K₁.subgroupOf K).Normal)
    (hPK₁ : P ≤ Subgroup.centralizer (K₁ : Set G))
    (hself : K ⊓ Subgroup.centralizer (K₁ : Set G) ≤ K₁)
    (hcop : Nat.Coprime (Nat.card P) (Nat.card K))
    (hsolv : IsSolvable K) :
    P ≤ Subgroup.centralizer (K : Set G) := by
  classical
  have h1 : ⁅⁅P, K₁⁆, K⁆ = ⊥ := by
    have hPK1_bot : ⁅P, K₁⁆ = ⊥ :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hPK₁
    simp [hPK1_bot]
  have hK1K_le : ⁅K₁, K⁆ ≤ K₁ := by
    exact (Subgroup.le_normalizer_iff_commutator_le_left (H := K) (K := K₁)).1
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hK1_le_K).1 hK1N)
  have hK1P_bot : ⁅K₁, P⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hPK₁
  have h2 : ⁅⁅K₁, K⁆, P⁆ = ⊥ := by
    apply le_bot_iff.mp
    exact (Subgroup.commutator_mono hK1K_le le_rfl).trans (by simpa [hK1P_bot])
  have hKPK1_bot : ⁅⁅K, P⁆, K₁⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := K) (H₂ := P) (H₃ := K₁) h1 h2
  have hKP_le_K : ⁅K, P⁆ ≤ K := (Subgroup.le_normalizer_iff_commutator_le_left).1 hPK
  have hKP_cent : ⁅K, P⁆ ≤ Subgroup.centralizer (K₁ : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hKPK1_bot
  have hKP_le_K1 : ⁅K, P⁆ ≤ K₁ := (le_inf hKP_le_K hKP_cent).trans hself
  have hKPP_bot : ⁅⁅K, P⁆, P⁆ = ⊥ := by
    apply le_bot_iff.mp
    exact (Subgroup.commutator_mono hKP_le_K1 le_rfl).trans (by simpa [hK1P_bot])
  let : P.Normalizes K := ⟨hPK⟩
  let : MulDistribMulAction (↥P) (↥K) :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer P K hPK
  let C : Subgroup (↥K) := commutatorAction (A := ↥P) (G := ↥K)
  have hCmap : C.map K.subtype = ⁅K, P⁆ := by
    simpa [C] using (commutatorAction_subgroup_conj_map_eq_commutator K P hPK)
  have hcomm₂_map_le :
      (commutatorAction₂ (A := ↥P) (G := ↥K)).map K.subtype ≤ ⁅⁅K, P⁆, P⁆ := by
    let S : Set (↥K) := {x : ↥K | ∃ a : ↥P, ∃ g : ↥K, g ∈ C ∧ x = g⁻¹ * (a • g)}
    calc
      (commutatorAction₂ (A := ↥P) (G := ↥K)).map K.subtype = (Subgroup.closure S).map K.subtype := by
        rfl
      _ = Subgroup.closure (K.subtype '' S) := by
        simpa using (MonoidHom.map_closure (f := K.subtype) S)
      _ ≤ ⁅⁅K, P⁆, P⁆ := by
        refine (Subgroup.closure_le (K := ⁅⁅K, P⁆, P⁆)).2 ?_
        rintro _ ⟨y, hy, rfl⟩
        rcases hy with ⟨a, g, hgC, rfl⟩
        have hgKP : (g : G) ∈ ⁅K, P⁆ := by
          rw [← hCmap]
          exact Subgroup.mem_map_of_mem K.subtype hgC
        have hgen : ⁅((g : ↥K) : G)⁻¹, (a : G)⁆ ∈ ⁅⁅K, P⁆, P⁆ :=
          Subgroup.commutator_mem_commutator (H₁ := ⁅K, P⁆) (H₂ := P)
            (Subgroup.inv_mem (H := ⁅K, P⁆) hgKP) a.2
        simpa [commutatorElement_def,
          Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, mul_assoc] using hgen
  have hcomm₂_bot : commutatorAction₂ (A := ↥P) (G := ↥K) = ⊥ := by
    apply (Subgroup.map_eq_bot_iff_of_injective
      (H := commutatorAction₂ (A := ↥P) (G := ↥K)) (f := K.subtype) K.subtype_injective).1
    exact le_antisymm (hcomm₂_map_le.trans (by simpa [hKPP_bot])) bot_le
  have htriv : ActsTrivially (A := ↥P) (G := ↥K) :=
    actsTrivially_of_commutatorAction₂_eq_bot_of_solvable_coprime
      (G := ↥K) (A := ↥P) hsolv hcop hcomm₂_bot
  intro p hp
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  let a : ↥P := ⟨p, hp⟩
  let kK : ↥K := ⟨k, hk⟩
  have htrivK : a • kK = kK := htriv a kK
  have hsmulK : ↑(a • kK) = p * k * p⁻¹ := by
    simpa [a, kK] using
      (Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe P K (a := a) (k := kK))
  have hconj : p * k * p⁻¹ = k :=
    hsmulK.trans (congrArg Subtype.val htrivK)
  calc
    k * p = (p * k * p⁻¹) * p := by rw [hconj]
    _ = p * k := by group

public theorem centralizes_of_subnormal_selfCentralizing_coprime
    {G : Type u} [Group G] [Finite G]
    (P K K₁ : Subgroup G)
    (hPK : P ≤ Subgroup.normalizer (K : Set G))
    (hK1_le_K : K₁ ≤ K)
    (hsub : (K₁.subgroupOf K).IsSubnormal)
    (hPK₁ : P ≤ Subgroup.centralizer (K₁ : Set G))
    (hself : K ⊓ Subgroup.centralizer (K₁ : Set G) ≤ K₁)
    (hcop : Nat.Coprime (Nat.card P) (Nat.card K))
    (hsolv : IsSolvable K) :
    P ≤ Subgroup.centralizer (K : Set G) := by
  classical
  have hmain : ∀ (n : ℕ) (K' : Subgroup G), Nat.card (↥K') = n →
      P ≤ Subgroup.normalizer (K' : Set G) →
      ∀ (H' : Subgroup (↥K')), H'.IsSubnormal →
        P ≤ Subgroup.centralizer (H'.map K'.subtype : Set G) →
        K' ⊓ Subgroup.centralizer (H'.map K'.subtype : Set G) ≤ H'.map K'.subtype →
          Nat.Coprime (Nat.card P) (Nat.card K') → IsSolvable (↥K') →
            P ≤ Subgroup.centralizer (K' : Set G) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro K' hcard hPK' H' hHsn hPH hself' hcop' hsolv'
      by_cases hnorm : H'.Normal
      · have hmap_le : H'.map K'.subtype ≤ K' := Subgroup.map_subtype_le (H := K') H'
        have hNnorm : ((H'.map K'.subtype).subgroupOf K').Normal := by
          rw [Subgroup.normal_subgroupOf_iff_le_normalizer hmap_le]
          intro y hy
          rw [Subgroup.mem_normalizer_iff]
          intro x
          constructor
          · intro hx
            rcases Subgroup.mem_map.mp hx with ⟨h, hh, rfl⟩
            exact Subgroup.mem_map.mpr
              ⟨⟨y, hy⟩ * h * (⟨y, hy⟩ : ↥K')⁻¹, hnorm.conj_mem h hh ⟨y, hy⟩, by simp⟩
          · intro hx
            rcases Subgroup.mem_map.mp hx with ⟨h, hh, hx'⟩
            have hh' : (⟨y, hy⟩ : ↥K')⁻¹ * h * (⟨y, hy⟩ : ↥K') ∈ H' := by
              simpa using (hnorm.conj_mem h hh (⟨y, hy⟩ : ↥K')⁻¹)
            have hxeq : x = (((⟨y, hy⟩ : ↥K')⁻¹ * h * (⟨y, hy⟩ : ↥K') : ↥K') : G) := by
              calc
                x = y⁻¹ * (y * x * y⁻¹) * y := by group
                _ = y⁻¹ * (h : G) * y := by rw [← hx']; rw [Subgroup.subtype_apply]
                _ = (((⟨y, hy⟩ : ↥K')⁻¹ * h * (⟨y, hy⟩ : ↥K') : ↥K') : G) := by rfl
            exact Subgroup.mem_map.mpr ⟨⟨y, hy⟩⁻¹ * h * ⟨y, hy⟩, hh', hxeq.symm⟩
        exact centralizes_of_normal_selfCentralizing_coprime P K' (H'.map K'.subtype)
          hPK' hmap_le hNnorm hPH hself' hcop' hsolv'
      · let H₀ : Subgroup (↥K') := H'
        let N0 : Subgroup (↥K') := Subgroup.normalClosure (H' : Set (↥K'))
        let N : Subgroup G := N0.map K'.subtype
        have hN_le_K' : N ≤ K' := Subgroup.map_subtype_le (H := K') N0
        have hH_le_N0 : H' ≤ N0 := Subgroup.le_normalClosure (H := H')
        have hHmap_le_N : H'.map K'.subtype ≤ N :=
          Subgroup.map_mono (f := K'.subtype) hH_le_N0
        have hH_ne_top : H' ≠ ⊤ := by
          intro hHtop
          apply hnorm
          rw [hHtop]
          infer_instance
        -- trim the subnormal chain
        obtain ⟨m, f, hfmono, hfnorm, hf0, hftop⟩ := Subgroup.IsSubnormal.exists_chain hHsn
        have htop_exists : ∃ i : ℕ, i ≤ m ∧ f i = ⊤ := ⟨m, le_rfl, hftop⟩
        let k := Nat.find htop_exists
        have hk_le_m : k ≤ m := (Nat.find_spec htop_exists).1
        have hfk_top : f k = ⊤ := (Nat.find_spec htop_exists).2
        have hkmin : ∀ j, j < k → f j ≠ ⊤ := by
          intro j hj hfj
          have hk_le_j : k ≤ j :=
            Nat.find_min' htop_exists ⟨Nat.le_trans (Nat.le_of_lt hj) hk_le_m, hfj⟩
          exact (Nat.lt_irrefl k) (lt_of_le_of_lt hk_le_j hj)
        have hk_pos : 0 < k := by
          by_contra hk0
          have hk_eq : k = 0 := Nat.eq_zero_of_not_pos hk0
          have hf0top : f 0 = ⊤ := by simpa [hk_eq] using hfk_top
          have hHtop : H' = ⊤ := by
            rw [hf0] at hf0top
            exact hf0top
          exact hH_ne_top hHtop
        have hfkm1_lt_top : f (k - 1) < ⊤ := by
          refine lt_of_le_of_ne le_top ?_
          intro hfkm1top
          exact (hkmin (k - 1) (Nat.sub_lt (Nat.pos_of_ne_zero hk_pos.ne') (by norm_num))) hfkm1top
        have hH_le_fkm1 : H' ≤ f (k - 1) := by
          rw [← hf0]
          exact hfmono (Nat.zero_le (k - 1))
        have hfkm1_normal : (f (k - 1)).Normal := by
          have hstep : k - 1 + 1 = k := Nat.sub_add_cancel hk_pos
          have hfn : ((f (k - 1)).subgroupOf (f k)).Normal := by
            have hfn0 : ((f (k - 1)).subgroupOf (f (k - 1 + 1))).Normal := hfnorm (k - 1)
            rw [hstep] at hfn0
            exact hfn0
          have hfn' : ((f (k - 1)).subgroupOf (⊤ : Subgroup (↥K'))).Normal := by
            rw [hfk_top] at hfn
            exact hfn
          rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_top] at hfn'
          rw [← Subgroup.normalizer_eq_top_iff]
          exact top_le_iff.mp hfn'
        have hN0_le_fkm1 : N0 ≤ f (k - 1) := by
          exact Subgroup.normalClosure_le_normal (s := (H' : Set (↥K')))
            (N := f (k - 1)) (by intro x hx; exact hH_le_fkm1 hx)
        have hN0_lt_top : N0 < ⊤ := lt_of_le_of_lt hN0_le_fkm1 hfkm1_lt_top
        have hN0_ne_top : N0 ≠ ⊤ := hN0_lt_top.ne
        have hN_lt_K' : N < K' := by
          refine lt_of_le_of_ne hN_le_K' ?_
          intro hNeq
          have hcardN0 : Nat.card (↥N0) < Nat.card (↥K') := by
            have hidx : 1 < N0.index := by
              exact Subgroup.one_lt_index_of_ne_top hN0_ne_top
            have hlt : Nat.card (↥N0) < Nat.card (↥N0) * N0.index :=
              lt_mul_of_one_lt_right Nat.card_pos hidx
            have hcard : Nat.card (↥K') = Nat.card (↥N0) * N0.index :=
              (N0.card_mul_index).symm
            rw [hcard]
            exact hlt
          have hcardN : Nat.card (↥N) = Nat.card (↥N0) := by
            exact Nat.card_congr
              ((Subgroup.equivMapOfInjective N0 K'.subtype K'.subtype_injective).toEquiv.symm)
          have hcardNlt : Nat.card (↥N) < Nat.card (↥K') := by
            rw [hcardN]
            exact hcardN0
          have hcardN' : Nat.card (↥N) = Nat.card (↥K') := by rw [hNeq]
          exact (ne_of_lt hcardNlt) hcardN'
        -- P normalizes N
        have hN_inv (q : G) (hqP : q ∈ P) (n : ↥K') (hn : n ∈ N0) :
            q * (n : G) * q⁻¹ ∈ N := by
          refine Subgroup.closure_induction
            (k := Group.conjugatesOfSet (H' : Set (↥K')))
            (p := fun x _ => (q : G) * (x : G) * (q : G)⁻¹ ∈ N) ?mem ?one ?mul ?inv hn
          · intro x hx
            rcases Group.mem_conjugatesOfSet_iff.mp hx with ⟨a, ha, hconj⟩
            rcases isConj_iff.mp hconj with ⟨c, hc⟩
            have hpc : (q : G) * (c : G) * (q : G)⁻¹ ∈ K' :=
              ((Subgroup.mem_normalizer_iff (H := K') (g := q)).1 (hPK' hqP) (c : G)).1 c.2
            let c' : ↥K' := ⟨(q : G) * (c : G) * (q : G)⁻¹, hpc⟩
            have hhfix : (q : G) * (a : G) * (q : G)⁻¹ = (a : G) := by
              have hcomm : (a : G) * (q : G) = (q : G) * (a : G) :=
                (Subgroup.mem_centralizer_iff (g := q)
                  (s := (H'.map K'.subtype : Set G))).1 (hPH hqP) (a : G)
                  (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩)
              calc
                (q : G) * (a : G) * (q : G)⁻¹ = (a : G) * (q : G) * (q : G)⁻¹ := by rw [hcomm]
                _ = (a : G) := by group
            have hgen : q * (x : G) * q⁻¹ =
                (((c' : ↥K') * a * (c' : ↥K')⁻¹ : ↥K') : G) := by
              calc
                q * (x : G) * q⁻¹ = q * ((c * a * c⁻¹ : ↥K') : G) * q⁻¹ := by
                  rw [← hc]
                _ = (q * (c : G) * q⁻¹) * (q * (a : G) * q⁻¹) * (q * (c : G)⁻¹ * q⁻¹) := by
                  simp [Subgroup.coe_mul, Subgroup.coe_inv]
                _ = (q * (c : G) * q⁻¹) * (a : G) * (q * (c : G)⁻¹ * q⁻¹) := by rw [hhfix]
                _ = (((c' : ↥K') * a * (c' : ↥K')⁻¹ : ↥K') : G) := by
                  simp [c', Subgroup.coe_mul]
                  group
            have hmem : (c' : ↥K') * a * (c' : ↥K')⁻¹ ∈
                Group.conjugatesOfSet (H' : Set (↥K')) := by
              exact Group.conj_mem_conjugatesOfSet (G := ↥K') (s := (H' : Set (↥K')))
                (x := a) (c := c') (Group.subset_conjugatesOfSet ha)
            have hN0mem : (c' : ↥K') * a * (c' : ↥K')⁻¹ ∈ N0 :=
              Subgroup.conjugatesOfSet_subset_normalClosure hmem
            exact Subgroup.mem_map.mpr ⟨(c' : ↥K') * a * (c' : ↥K')⁻¹, hN0mem, by simpa [hgen]⟩
          · simp [N]
          · intro x y _hx _hy ihx ihy
            have hxy : q * ((x * y : ↥K') : G) * q⁻¹ =
                (q * (x : G) * q⁻¹) * (q * (y : G) * q⁻¹) := by
              rw [Subgroup.coe_mul]
              group
            rw [hxy]
            exact N.mul_mem ihx ihy
          · intro x _hx ihx
            have hxinv : q * ((x : ↥K')⁻¹ : G) * q⁻¹ = (q * (x : G) * q⁻¹)⁻¹ := by
              group
            change q * ((x : ↥K')⁻¹ : G) * q⁻¹ ∈ N
            rw [hxinv]
            exact N.inv_mem ihx
        have hPKN : P ≤ Subgroup.normalizer (N : Set G) := by
          intro q hq
          rw [Subgroup.mem_normalizer_iff]
          intro x
          constructor
          · intro hx
            rcases Subgroup.mem_map.mp hx with ⟨n, hn, rfl⟩
            exact hN_inv q hq n hn
          · intro hx
            rcases Subgroup.mem_map.mp hx with ⟨n, hn, hx'⟩
            have hqinvP : q⁻¹ ∈ P := P.inv_mem hq
            have hn' : q⁻¹ * (n : G) * q ∈ N := by
              simpa using (hN_inv q⁻¹ hqinvP n hn)
            have hxeq : x = q⁻¹ * (n : G) * q := by
              calc
                x = q⁻¹ * (q * x * q⁻¹) * q := by group
                _ = q⁻¹ * (n : G) * q := by rw [← hx']; rw [Subgroup.subtype_apply]
            rwa [hxeq]
        -- subnormality of H' in N0
        have hsubN0 : (H'.subgroupOf N0).IsSubnormal := by
          simpa [Subgroup.mem_subgroupOf] using
            (Subgroup.IsSubnormal.comap N0.subtype hHsn)
        let e0 : ↥N0 ≃* ↥N := Subgroup.equivMapOfInjective N0 K'.subtype K'.subtype_injective
        let H0 : Subgroup (↥N) := (H'.subgroupOf N0).map e0.toMonoidHom
        have hH0sn : H0.IsSubnormal := Subgroup.IsSubnormal.map e0.surjective hsubN0
        have hH0map : H0.map N.subtype = H'.map K'.subtype := by
          calc
            H0.map N.subtype = (H'.subgroupOf N0).map (N.subtype.comp e0.toMonoidHom) := by
              simp [H0, Subgroup.map_map]
            _ = (H'.subgroupOf N0).map (K'.subtype.comp N0.subtype) := by
              apply congrArg (fun f : ↥N0 →* G => (H'.subgroupOf N0).map f)
              ext x
              change (N.subtype (e0 x) : G) = (K'.subtype (N0.subtype x) : G)
              rfl
            _ = ((H'.subgroupOf N0).map N0.subtype).map K'.subtype := by
              rw [Subgroup.map_map]
            _ = H'.map K'.subtype := by
              simp [Subgroup.map_subgroupOf_eq_of_le hH_le_N0]
        have hPH0 : P ≤ Subgroup.centralizer (H0.map N.subtype : Set G) := by
          rw [hH0map]
          exact hPH
        have hself0 : N ⊓ Subgroup.centralizer (H0.map N.subtype : Set G) ≤ H0.map N.subtype := by
          rw [hH0map]
          intro x hx
          rcases hx with ⟨hxN, hxCent⟩
          exact hself' ⟨hN_le_K' hxN, hxCent⟩
        have hcopN : Nat.Coprime (Nat.card P) (Nat.card N) :=
          Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le hN_le_K') hcop'
        have hsolvN : Group.IsSolvable (↥N) := by
          let : Group.IsSolvable (↥K') := hsolv'
          have hsub_solv : Group.IsSolvable (↥(N.subgroupOf K')) := inferInstance
          have hmapN : (N.subgroupOf K').map K'.subtype = N :=
            Subgroup.map_subgroupOf_eq_of_le hN_le_K'
          have eN : ↥(N.subgroupOf K') ≃* ↥((N.subgroupOf K').map K'.subtype) :=
            Subgroup.equivMapOfInjective (N.subgroupOf K') K'.subtype K'.subtype_injective
          have hsolvMap : Group.IsSolvable (↥((N.subgroupOf K').map K'.subtype)) :=
            Group.isSolvable_of_surjective (f := eN.toMonoidHom) eN.surjective
          exact by
            rw [hmapN] at hsolvMap
            exact hsolvMap
        have hNcard_lt : Nat.card (↥N) < n := by
          have hlt' : Nat.card (↥N) < Nat.card (↥K') := by
            have hN0card : Nat.card (↥N0) < Nat.card (↥K') := by
              have hidx : 1 < N0.index := Subgroup.one_lt_index_of_ne_top hN0_ne_top
              have hlt : Nat.card (↥N0) < Nat.card (↥N0) * N0.index :=
                lt_mul_of_one_lt_right Nat.card_pos hidx
              have hcardK' : Nat.card (↥K') = Nat.card (↥N0) * N0.index :=
                (N0.card_mul_index).symm
              rw [hcardK']
              exact hlt
            have hcardN : Nat.card (↥N) = Nat.card (↥N0) := by
              exact Nat.card_congr
                ((Subgroup.equivMapOfInjective N0 K'.subtype K'.subtype_injective).toEquiv.symm)
            rw [hcardN]
            exact hN0card
          rw [← hcard]
          exact hlt'
        have hPKN_concl : P ≤ Subgroup.centralizer (N : Set G) :=
          ih (Nat.card (↥N)) hNcard_lt N rfl hPKN H0 hH0sn hPH0 hself0 hcopN hsolvN
        have hN_normal : (N.subgroupOf K').Normal := by
          rw [Subgroup.normal_subgroupOf_iff_le_normalizer hN_le_K']
          intro y hy
          rw [Subgroup.mem_normalizer_iff]
          intro x
          constructor
          · intro hx
            rcases Subgroup.mem_map.mp hx with ⟨n, hn, rfl⟩
            have hconjN0 : (⟨y, hy⟩ : ↥K') * n * (⟨y, hy⟩ : ↥K')⁻¹ ∈ N0 :=
              (inferInstance : N0.Normal).conj_mem n hn ⟨y, hy⟩
            exact Subgroup.mem_map.mpr
              ⟨⟨y, hy⟩ * n * (⟨y, hy⟩ : ↥K')⁻¹, hconjN0, by simp⟩
          · intro hx
            rcases Subgroup.mem_map.mp hx with ⟨n, hn, hx'⟩
            have hconjN0 : (⟨y, hy⟩ : ↥K')⁻¹ * n * (⟨y, hy⟩ : ↥K') ∈ N0 := by
              simpa using ((inferInstance : N0.Normal).conj_mem n hn (⟨y, hy⟩ : ↥K')⁻¹)
            have hxeq : x = (((⟨y, hy⟩ : ↥K')⁻¹ * n * (⟨y, hy⟩ : ↥K') : ↥K') : G) := by
              calc
                x = y⁻¹ * (y * x * y⁻¹) * y := by group
                _ = y⁻¹ * (n : G) * y := by rw [← hx']; rw [Subgroup.subtype_apply]
                _ = (((⟨y, hy⟩ : ↥K')⁻¹ * n * (⟨y, hy⟩ : ↥K') : ↥K') : G) := by rfl
            exact Subgroup.mem_map.mpr ⟨⟨y, hy⟩⁻¹ * n * ⟨y, hy⟩, hconjN0, hxeq.symm⟩
        have hselfN : K' ⊓ Subgroup.centralizer (N : Set G) ≤ N := by
          intro x hx
          rcases hx with ⟨hxK', hxCent⟩
          have hxCentH : x ∈ Subgroup.centralizer (H'.map K'.subtype : Set G) :=
            (Subgroup.centralizer_le (show (H'.map K'.subtype : Set G) ⊆ (N : Set G) from
              hHmap_le_N)) hxCent
          exact hHmap_le_N (hself' ⟨hxK', hxCentH⟩)
        exact centralizes_of_normal_selfCentralizing_coprime P K' N
          hPK' hN_le_K' hN_normal hPKN_concl hselfN hcop' hsolv'
  exact hmain (Nat.card (↥K)) K rfl hPK (K₁.subgroupOf K) hsub
    (by rw [Subgroup.map_subgroupOf_eq_of_le hK1_le_K]; exact hPK₁)
    (by rw [Subgroup.map_subgroupOf_eq_of_le hK1_le_K]; exact hself) hcop hsolv


/-! ## Klein-four fixed-point choice (proved) -/

/-- The "choose `s`" step for Lemma 2.9 (proved): a Klein-four `V` acting
on a nontrivial finite odd group `A` with trivial fixed subgroup has some
nonidentity `s ∈ V` with nontrivial fixed subgroup inside `A`.  This is the
consequence of
`iSup_fixedPointSubgroup_zpowers_eq_top_of_noncyclic_abelian_pGroup_action`
instantiated with the conjugation action of `↥V` on `↥A`.  Note the theorem
gives `∃ s ≠ 1, C_A(s) ≠ ⊥`, not the stronger `[s, C_A(t)] ≠ ⊥` for a fixed
distinguished `t`; if `C_A(t) = ⊥`, Lemma 2.9 must relabel the three
involutions (drift recorded for `gw8`). -/
public theorem exists_ne_one_fixedPoints_of_kleinFour_action
    {G : Type u} [Group G] [Finite G]
    {V A : Subgroup G}
    (hV : IsKleinFour V)
    (hVA : V ≤ Subgroup.normalizer (A : Set G))
    (hAodd : Nat.Coprime 2 (Nat.card (↥A)))
    (hAne : A ≠ ⊥)
    (hfaith : A ⊓ Subgroup.centralizer (V : Set G) = ⊥) :
    ∃ s : G, s ∈ V ∧ s ≠ 1 ∧
      A ⊓ Subgroup.centralizer ({s} : Set G) ≠ ⊥ := by
  classical
  let : IsKleinFour (↥V) := hV
  let : IsMulCommutative (↥V) := IsKleinFour.isMulCommutative
  let : CommGroup (↥V) := IsMulCommutative.instCommGroup
  have hV2 : IsPGroup 2 (↥V) := IsPGroup.of_card (n := 2) (by
    simpa [IsKleinFour.card_four])
  let : Fact (IsPGroup 2 (↥V)) := ⟨hV2⟩
  let : V.Normalizes A := ⟨hVA⟩
  let : MulDistribMulAction (↥V) (↥A) :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer V A hVA
  by_contra hnone
  have hAll : ∀ a : ↥V, a ≠ 1 →
      A ⊓ Subgroup.centralizer ({(a : G)} : Set G) = ⊥ := by
    intro a ha
    by_contra hne
    have haG : (a : G) ≠ 1 := by
      intro h
      exact ha (Subtype.ext h)
    exact hnone ⟨(a : G), a.2, haG, hne⟩
  have hfixed_bot : ∀ a : ↥V, a ≠ 1 →
      fixedPointSubgroup (↥(Subgroup.zpowers a)) (↥A) = ⊥ := by
    intro a ha
    apply le_bot_iff.mp
    intro x hx
    apply Subtype.ext
    have hxA : (x : G) ∈ A := x.2
    have hxfix : a • (x : ↥A) = (x : ↥A) :=
      hx ⟨a, Subgroup.mem_zpowers a⟩
    have hsmul : ↑(a • (x : ↥A)) = (x : G) := by
      exact congrArg Subtype.val hxfix
    have hcoe : ↑(a • (x : ↥A)) = (a : G) * (x : G) * (a : G)⁻¹ := by
      simpa using (Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe V A
        (a := a) (k := x))
    have hconj : (a : G) * (x : G) * (a : G)⁻¹ = (x : G) := hcoe.symm.trans hsmul
    have hcomm : (x : G) * (a : G) = (a : G) * (x : G) := by
      calc
        (x : G) * (a : G) = ((a : G) * (x : G) * (a : G)⁻¹) * (a : G) := by rw [hconj]
        _ = (a : G) * (x : G) := by group
    have hxCent : (x : G) ∈ Subgroup.centralizer ({(a : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hza : z = (a : G) := by simpa using hz
      rw [hza]
      exact hcomm.symm
    have hxinf : (x : G) ∈ A ⊓ Subgroup.centralizer ({(a : G)} : Set G) := ⟨hxA, hxCent⟩
    have hxbot : (x : G) ∈ (⊥ : Subgroup G) := by
      rw [hAll a ha] at hxinf
      exact hxinf
    exact Subgroup.mem_bot.mp hxbot
  have htop := iSup_fixedPointSubgroup_zpowers_eq_top_of_noncyclic_abelian_pGroup_action
    (G := ↥A) (A := ↥V) (p := 2) (hG := hAodd) (hncyc := IsKleinFour.not_isCyclic)
  have hbot_top : (⊥ : Subgroup (↥A)) = ⊤ := by
    have hsum : (⨆ a : ↥V, ⨆ (_ : a ≠ 1),
        fixedPointSubgroup (↥(Subgroup.zpowers a)) (↥A)) = ⊥ := by
      rw [iSup₂_eq_bot]
      intro a ha
      exact hfixed_bot a ha
    rw [← hsum, htop]
  have hA_bot : A = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxTop : (⟨x, hx⟩ : ↥A) ∈ (⊤ : Subgroup (↥A)) := trivial
    have hxBot : (⟨x, hx⟩ : ↥A) ∈ (⊥ : Subgroup (↥A)) := by
      simpa [← hbot_top] using hxTop
    exact congrArg (fun z : ↥A => (z : G)) (Subgroup.mem_bot.mp hxBot)
  exact hAne hA_bot

/-! ## Odd-order subgroups of `H` lie in `U` -/

/-- Since `H = S·U` (preamble `fact_2_preamble_H_eq_SU_proved`), the
quotient `H/U` is a `2`-group (the image of the Sylow `2`-subgroup `S`);
every odd-order subgroup `X ≤ H` maps trivially into it, hence
`X ≤ U = O(H)`. -/
public theorem odd_order_subgroup_le_U_of_H_eq_SU
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G) (c : CentralizerSetup G)
    {X : Subgroup G} (hXH : X ≤ c.H)
    (hXodd : Nat.Coprime 2 (Nat.card X)) : X ≤ c.U := by
  classical
  have hUH : c.U ≤ c.H := Subgroup.map_subtype_le (H := c.H) (pPrimeCore 2 c.H)
  have hU_normal : (c.U.subgroupOf c.H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hUH]
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      rcases Subgroup.mem_map.mp hu with ⟨p, hp, rfl⟩
      have hnorm : (⟨h, hh⟩ : ↥c.H) * (p : ↥c.H) * (⟨h, hh⟩ : ↥c.H)⁻¹ ∈ pPrimeCore 2 c.H :=
        (pPrimeCore_normal (p := 2) (G := c.H)).conj_mem (p : ↥c.H) hp (⟨h, hh⟩ : ↥c.H)
      exact Subgroup.mem_map.mpr
        ⟨(⟨h, hh⟩ : ↥c.H) * (p : ↥c.H) * (⟨h, hh⟩ : ↥c.H)⁻¹, hnorm, by simp⟩
    · intro hu
      rcases Subgroup.mem_map.mp hu with ⟨p, hp, hpeq⟩
      have hh' : h⁻¹ ∈ c.H := c.H.inv_mem hh
      have hnorm : (⟨h⁻¹, hh'⟩ : ↥c.H) * (p : ↥c.H) * (⟨h⁻¹, hh'⟩ : ↥c.H)⁻¹ ∈ pPrimeCore 2 c.H :=
        (pPrimeCore_normal (p := 2) (G := c.H)).conj_mem (p : ↥c.H) hp (⟨h⁻¹, hh'⟩ : ↥c.H)
      have hmem : h⁻¹ * (p : G) * h ∈ c.U :=
        Subgroup.mem_map.mpr
          ⟨(⟨h⁻¹, hh'⟩ : ↥c.H) * (p : ↥c.H) * (⟨h⁻¹, hh'⟩ : ↥c.H)⁻¹, hnorm, by simp⟩
      have hu_eq : u = h⁻¹ * (p : G) * h := by
        calc
          u = h⁻¹ * (h * u * h⁻¹) * h := by group
          _ = h⁻¹ * (p : G) * h := by rw [← hpeq]; rfl
      exact hu_eq ▸ hmem
  let U' : Subgroup (↥c.H) := c.U.subgroupOf c.H
  let : U'.Normal := hU_normal
  let S' : Subgroup (↥c.H) := (c.S : Subgroup G).subgroupOf c.H
  let q : ↥c.H →* ↥c.H ⧸ U' := QuotientGroup.mk' U'
  have hSH : (c.S : Subgroup G) ≤ c.H := centralizerSetup_S_le_H c
  have hHsup : (c.S : Subgroup G) ⊔ c.U = c.H := fact_2_preamble_H_eq_SU_proved hmin c
  have hS_norm_U : (c.S : Subgroup G) ≤ Subgroup.normalizer (c.U : Set G) := by
    exact hSH.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hUH).1 hU_normal)
  have htop' : S' ⊔ U' = ⊤ := by
    refine le_antisymm le_top ?_
    intro x hx
    have hxSU : (x : G) ∈ (c.S : Subgroup G) ⊔ c.U := by
      rw [hHsup]
      exact x.2
    have hxprod : (x : G) ∈ ((c.S : Subgroup G) : Set G) * (c.U : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right (H := c.S) (N := c.U) hS_norm_U]
      exact hxSU
    rcases hxprod with ⟨s, hs, u, hu, hsmu⟩
    have hsS' : (⟨s, hSH hs⟩ : ↥c.H) ∈ S' :=
      (Subgroup.mem_subgroupOf).2 hs
    have huU' : (⟨u, hUH hu⟩ : ↥c.H) ∈ U' :=
      (Subgroup.mem_subgroupOf).2 hu
    have hxeq : x = (⟨s, hSH hs⟩ : ↥c.H) * (⟨u, hUH hu⟩ : ↥c.H) := by
      apply Subtype.ext
      exact hsmu.symm
    rw [hxeq]
    exact Subgroup.mul_mem_sup hsS' huU'
  have hS2 : IsPGroup 2 ↥(c.S : Subgroup G) := c.S.isPGroup'
  have hf : IsPGroup 2 (↥c.H ⧸ U') := by
    let f : ↥(c.S : Subgroup G) →* ↥c.H ⧸ U' := q.comp (Subgroup.inclusion hSH)
    have hf_surj : Function.Surjective f := by
      intro y
      rcases QuotientGroup.mk'_surjective U' y with ⟨h, rfl⟩
      have hhSU : h ∈ S' ⊔ U' := by
        simpa [htop'] using (Subgroup.mem_top h)
      have hhprod : (h : ↥c.H) ∈ (S' : Set (↥c.H)) * (U' : Set (↥c.H)) := by
        rw [← Subgroup.mul_normal (H := S') (N := U')]
        exact hhSU
      rcases hhprod with ⟨s, hsS', u, huU', hsmu⟩
      have hqu1 : q u = 1 := (QuotientGroup.eq_one_iff (N := U') u).2 huU'
      have hqs : q (s : ↥c.H) = q h := by
        calc
          q (s : ↥c.H) = q (s : ↥c.H) * 1 := by simp
          _ = q (s : ↥c.H) * q u := by rw [hqu1]
          _ = q ((s : ↥c.H) * u) := by rw [map_mul]
          _ = q h := by exact congrArg q hsmu
      have hsS : (s : G) ∈ (c.S : Subgroup G) := by
        simpa [S', Subgroup.mem_subgroupOf] using hsS'
      refine ⟨⟨(s : G), hsS⟩, ?_⟩
      change q (s : ↥c.H) = QuotientGroup.mk' U' h
      simpa [q, f] using hqs
    exact IsPGroup.of_surjective hS2 f hf_surj
  let X' : Subgroup (↥c.H) := X.subgroupOf c.H
  have hX2 : IsPGroup 2 ↥(X'.map q) := IsPGroup.to_subgroup hf (X'.map q)
  have hcopX' : Nat.Coprime 2 (Nat.card ↥(X'.map q)) := by
    have hdvd : Nat.card ↥(X'.map q) ∣ Nat.card X := by
      exact (Subgroup.card_map_dvd X' q).trans (by rw [natCard_subgroupOf_eq X c.H hXH])
    exact Nat.Coprime.of_dvd_right hdvd hXodd
  have hX'map_bot : X'.map q = ⊥ :=
    section8_eq_bot_of_isPGroup_of_coprime (H := X'.map q) hX2 hcopX'
  intro x hx
  have hxX' : (⟨x, hXH hx⟩ : ↥c.H) ∈ X' := by
    simpa [X', Subgroup.mem_subgroupOf] using hx
  have hqx1 : q ⟨x, hXH hx⟩ = 1 := by
    have hmem : q ⟨x, hXH hx⟩ ∈ X'.map q :=
      Subgroup.mem_map.mpr ⟨⟨x, hXH hx⟩, hxX', rfl⟩
    have hbot : q ⟨x, hXH hx⟩ ∈ (⊥ : Subgroup (↥c.H ⧸ U')) := by
      simpa [hX'map_bot] using hmem
    exact (Subgroup.mem_bot.mp hbot)
  have hxU' : (⟨x, hXH hx⟩ : ↥c.H) ∈ U' :=
    (QuotientGroup.eq_one_iff (N := U') ⟨x, hXH hx⟩).1 hqx1
  exact (Subgroup.mem_subgroupOf.mp hxU')


/-! ## Lemma 2.9: `X = [s, C_A(t)] ≤ U` -/

/-- In the Lemma 2.9 configuration (`V ≤ S ≤ H`, `V ≤ N`,
`A = oddCoreOf N`), the commutator subgroup
`X := ⁅Subgroup.zpowers s, C_A(t)⁆` has odd order and lies in `H`, hence
lies in `U = O(H)` by `odd_order_subgroup_le_U_of_H_eq_SU`. -/
public theorem commutator_centralizer_le_U
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G) (c : CentralizerSetup G)
    {N V : Subgroup G} {s : G}
    (hVN : V ≤ N) (hVS : V ≤ (c.S : Subgroup G)) (hsV : s ∈ V) :
    ⁅Subgroup.zpowers s, centralizerIn (oddCoreOf N) c.t⁆ ≤ c.U := by
  classical
  let A : Subgroup G := oddCoreOf N
  let C : Subgroup G := centralizerIn A c.t
  let X : Subgroup G := ⁅Subgroup.zpowers s, C⁆
  have hVH : V ≤ c.H := hVS.trans (centralizerSetup_S_le_H c)
  have hsH : s ∈ c.H := hVH hsV
  have hzH : Subgroup.zpowers s ≤ c.H := Subgroup.zpowers_le.2 hsH
  have hCH : C ≤ c.H := by
    intro x hx
    have hxA : x ∈ A := hx.1
    have hxCent : x ∈ Subgroup.centralizer ({c.t} : Set G) := hx.2
    rw [c.H_eq_centralizer]
    exact hxCent
  have hXH : X ≤ c.H := (Subgroup.commutator_le_sup (H₁ := Subgroup.zpowers s) (H₂ := C)).trans
    (sup_le hzH hCH)
  have hzN : Subgroup.zpowers s ≤ Subgroup.normalizer (A : Set G) := by
    apply subgroup_le_normalizer_of_conj_mem (H := A) (R := Subgroup.zpowers s)
    intro r _hr ha
    rcases Subgroup.mem_zpowers_iff.mp r.2 with ⟨n, hn⟩
    rw [← hn]
    rcases Subgroup.mem_map.mp ha with ⟨p, hp, rfl⟩
    have hrN : s ^ n ∈ N := Subgroup.zpow_mem N (hVN hsV) n
    have hconj : (⟨s ^ n, hrN⟩ : ↥N) * p * (⟨s ^ n, hrN⟩ : ↥N)⁻¹ ∈ pPrimeCore 2 N :=
      (pPrimeCore_normal (p := 2) (G := N)).conj_mem p hp (⟨s ^ n, hrN⟩ : ↥N)
    exact Subgroup.mem_map.mpr ⟨(⟨s ^ n, hrN⟩ : ↥N) * p * (⟨s ^ n, hrN⟩ : ↥N)⁻¹, hconj, by simp⟩
  have hXA : X ≤ A := by
    have hCA : C ≤ A := inf_le_left
    have hcommA : ⁅A, Subgroup.zpowers s⁆ ≤ A :=
      (Subgroup.le_normalizer_iff_commutator_le_left (H := Subgroup.zpowers s) (K := A)).1 hzN
    have hXAz : ⁅Subgroup.zpowers s, C⁆ ≤ ⁅Subgroup.zpowers s, A⁆ :=
      Subgroup.commutator_mono (H₁ := Subgroup.zpowers s) (K₁ := Subgroup.zpowers s) le_rfl
        (H₂ := C) (K₂ := A) hCA
    exact hXAz.trans (by
      rw [Subgroup.commutator_comm (H₁ := Subgroup.zpowers s) (H₂ := A)]
      exact hcommA)
  have hXodd : Nat.Coprime 2 (Nat.card X) := by
    have hcopA : Nat.Coprime 2 (Nat.card A) := by
      dsimp [A, oddCoreOf]
      rw [Subgroup.card_map_of_injective N.subtype_injective]
      exact pPrimeCore_coprime_card (p := 2) (G := N)
    have hcard : Nat.card X ∣ Nat.card A := Subgroup.card_dvd_of_le hXA
    exact hcopA.of_dvd_right hcard
  exact odd_order_subgroup_le_U_of_H_eq_SU hmin c hXH hXodd

end

end CFSG.GorensteinWalter

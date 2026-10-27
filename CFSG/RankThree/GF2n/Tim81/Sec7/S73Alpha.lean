module

public import CFSG.RankThree.GF2n.Tim81.Sec7.S73Split
import CFSG.GroupTheory.CentralSylowComplement
import CFSG.CGT.PushingUpLit.SolKNA.R4.PMArith
import CFSG.Timmesfeld.Bridge.RootStructR2ManySection
import CFSG.RankThree.OddKernel.SectionRep

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n
open CFSG.RankThree.GF2n.Tim81.Sec7 (rOf oOf yOf)
open CFSG.Timmesfeld.Bridge.RootMany
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G] {M V A B : Subgroup G} {h : G} {n f : ℕ}

theorem oOf_inf_p0Of (M V X : Subgroup G) (h : G) : oOf M h ⊓ p0Of M V X = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 (p0Of M V X) :=
    (inSubgroup_pCore_two M).1.to_le
      ((inf_le_left : p0Of M V X ≤ Pc M V).trans inf_le_left)
  obtain ⟨k, hk⟩ := h2.exists_card_eq
  refine Subgroup.inf_eq_bot_of_coprime ?_
  rw [hk]
  exact (Nat.coprime_two_left.mpr (Sec7.odd_card_oOf M h)).symm.pow_right k

namespace L2Datum

theorem commutator_oOf_p0 (hS : Sec7Hyp M V n f) (h72 : Sec7.Stmt72 M V n f)
    (hD : L2Datum M V A B h) :
    ⁅oOf M h, p0Of M V (A ⊔ B)⁆ = ⊥ := by
  obtain ⟨hS1, -, -, -, -, -, -, -, -, -⟩ := h72 A B h hD
  have hOR : oOf M h ≤ rOf M h := Subgroup.map_subtype_le _
  have hP0R : p0Of M V (A ⊔ B) ≤ rOf M h := p0_le_rOf hS.toSec6Hyp hD
  have hleO : ⁅oOf M h, p0Of M V (A ⊔ B)⁆ ≤ oOf M h :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hP0R.trans (Sec7.rOf_le_normalizer_oOf M h))
  have hleP0 : ⁅oOf M h, p0Of M V (A ⊔ B)⁆ ≤ p0Of M V (A ⊔ B) :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp
      (hOR.trans (rOf_le_normalizer_p0 hS.toSec6Hyp hD hS1))
  have hbot : oOf M h ⊓ p0Of M V (A ⊔ B) = ⊥ := oOf_inf_p0Of M V (A ⊔ B) h
  rw [eq_bot_iff]
  intro x hx
  have hx' : x ∈ oOf M h ⊓ p0Of M V (A ⊔ B) := ⟨hleO hx, hleP0 hx⟩
  rwa [hbot] at hx'

private theorem le_oOf_of_complement_odd {M V : Subgroup G} {h : G} {T OT : Subgroup G}
    (hOTR : OT ≤ rOf M h) (hOTT : OT ≤ T)
    (hRT : rOf M h ≤ Subgroup.normalizer (T : Set G))
    (hOTmem : ∀ x ∈ T, x ∈ OT ↔ Odd (orderOf x)) :
    OT ≤ oOf M h := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOTsub : (OT.subgroupOf (rOf M h)).Normal := by
    refine ⟨fun x hx r => ?_⟩
    have hxOT : (x : G) ∈ OT := Subgroup.mem_subgroupOf.mp hx
    have hxT : (x : G) ∈ T := hOTT hxOT
    have hconjT : (r : G) * (x : G) * (r : G)⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.mp (hRT r.2) (x : G)).mp hxT
    have hord : orderOf ((r : G) * (x : G) * (r : G)⁻¹) = orderOf (x : G) := by
      simpa [MulAut.conj_apply] using (MulAut.conj (r : G)).orderOf_eq (x : G)
    have hxodd : Odd (orderOf (x : G)) := (hOTmem (x : G) hxT).mp hxOT
    have hcoec : (((r * x * r⁻¹ : ↥(rOf M h)) : G)) =
        (r : G) * (x : G) * (r : G)⁻¹ := by simp [Subgroup.coe_mul]
    rw [Subgroup.mem_subgroupOf, hcoec]
    exact (hOTmem _ hconjT).mpr (by rw [hord]; exact hxodd)
  have hOTodd : Odd (Nat.card OT) := by
    by_contra hodd
    rw [Nat.not_odd_iff_even] at hodd
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥OT) 2 hodd.two_dvd
    have hzT : ((z : ↥OT) : G) ∈ T := hOTT z.2
    have hzo : Odd (orderOf ((z : ↥OT) : G)) := (hOTmem _ hzT).mp z.2
    rw [Subgroup.orderOf_coe, hz] at hzo
    exact (by norm_num : ¬ Odd 2) hzo
  have hcop : Nat.Coprime 2 (Nat.card ↥(OT.subgroupOf (rOf M h))) := by
    rw [natCard_subgroupOf_eq OT (rOf M h) hOTR]
    exact hOTodd.coprime_two_left
  have hle : OT.subgroupOf (rOf M h) ≤ pPrimeCore 2 ↥(rOf M h) :=
    CFSG.le_pPrimeCore_of_normal_coprime hOTsub hcop
  intro x hx
  have hxR : (⟨x, hOTR hx⟩ : ↥(rOf M h)) ∈ pPrimeCore 2 ↥(rOf M h) :=
    hle (Subgroup.mem_subgroupOf.mpr hx)
  exact Subgroup.mem_map_of_mem (rOf M h).subtype hxR

theorem rOf_inf_cenOf_p0Of_eq (hS : Sec7Hyp M V n f) (h72 : Sec7.Stmt72 M V n f)
    (hD : L2Datum M V A B h)
    (hT2 : ∀ y ∈ rOf M h ⊓ cenOf (p0Of M V (A ⊔ B)),
      IsPGroup 2 (Subgroup.zpowers y) → y ∈ V) :
    rOf M h ⊓ cenOf (p0Of M V (A ⊔ B)) = oOf M h ⊔ V := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hS1, -, -, -, -, -, -, -, -, -⟩ := h72 A B h hD
  set P0 : Subgroup G := p0Of M V (A ⊔ B) with hP0
  set R : Subgroup G := rOf M h with hR
  set O : Subgroup G := oOf M h with hO
  set T : Subgroup G := R ⊓ cenOf P0 with hT
  have hOR : O ≤ R := Subgroup.map_subtype_le _
  have hP0R : P0 ≤ R := p0_le_rOf hS.toSec6Hyp hD
  have hVR : V ≤ R := (V_le_p0 hS.toSec6Hyp hD).trans hP0R
  have hVP0 : V ≤ P0 := V_le_p0 hS.toSec6Hyp hD
  have hP0centV : P0 ≤ cenOf V := inf_le_left.trans inf_le_right
  have hOcent : O ≤ cenOf P0 :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (commutator_oOf_p0 hS h72 hD)
  have hVcent : V ≤ cenOf P0 := Subgroup.le_centralizer_iff.mp hP0centV
  have hRT : R ≤ Subgroup.normalizer (T : Set G) := by
    intro r hr
    exact mem_normalizer_inf (Subgroup.le_normalizer hr)
      (mem_normalizer_centralizer (rOf_le_normalizer_p0 hS.toSec6Hyp hD hS1 hr))
  have hVT : V ≤ T := le_inf hVR hVcent
  have hmax : ∀ Q : Subgroup G, Q ≤ T → IsPGroup 2 Q → V ≤ Q → Q ≤ V := by
    intro Q hQT hQ2 hVQ y hy
    exact hT2 y (hQT hy) (hQ2.to_le (Subgroup.zpowers_le.mpr hy))
  have hidx : ¬ 2 ∣ V.relIndex T :=
    CFSG.GroupTheory.relIndex_not_dvd_of_maximal (p := 2) hVT
      hS.sec5.toRootHyp.toHyp.isPGroup_V hmax
  have hcent : ∀ x ∈ T, ∀ q ∈ V, x * q = q * x := by
    intro x hx q hq
    have hxT : x ∈ cenOf P0 := (Subgroup.mem_inf.mp hx).2
    exact (Subgroup.mem_centralizer_iff.mp hxT q (hVP0 hq)).symm
  obtain ⟨OT, hOTT, hOTmem, -, hOTdecomp⟩ :=
    CFSG.GroupTheory.exists_complement_of_central_sylow_two hVT
      hS.sec5.toRootHyp.toHyp.isPGroup_V hcent hidx
  have hOTleO : OT ≤ O :=
    le_oOf_of_complement_odd (M := M) (V := V) (h := h) (T := T) (OT := OT)
      (hOTT.trans inf_le_left) hOTT hRT hOTmem
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨q, hq, o, ho, hxo⟩ := hOTdecomp x hx
    rw [hxo]
    exact (O ⊔ V).mul_mem (Subgroup.mem_sup_right hq)
      (Subgroup.mem_sup_left (hOTleO ho))
  · exact _root_.sup_le (le_inf hOR hOcent) (le_inf hVR hVcent)

private theorem exists_fixed_secMk_of_isPGroup_quotient
    {H : Type} [Group H] [Finite H] (E A O : Subgroup H) [E.Normal] [A.Normal]
    [Fact (IsElemSection E A)] (hOn : O.Normal)
    (hker : O ≤ (secRep E A).ker)
    (hpow : ∀ u : H, ∃ k : ℕ, u ^ 2 ^ k ∈ O)
    (hnt : 1 < Nat.card (CFSG.Timmesfeld.Bridge.RootMany.SecMod E A)) :
    ∃ e : E, (e : H) ∉ A ∧ ∀ u : H, secRep E A u (secMk E A e) = secMk E A e := by
  classical
  haveI : O.Normal := hOn
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q := H ⧸ O
  let ρ : Representation (ZMod 2) Q (CFSG.Timmesfeld.Bridge.RootMany.SecMod E A) :=
    QuotientGroup.lift O (secRep E A) hker
  have hρmk : ∀ u : H, ρ (QuotientGroup.mk' O u) = secRep E A u :=
    fun u => QuotientGroup.lift_mk (N := O) (φ := secRep E A) hker u
  have hQ2 : IsPGroup 2 Q := by
    rw [IsPGroup.iff_orderOf]
    intro z
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective O z
    obtain ⟨k, hk⟩ := hpow u
    have hzpow : (QuotientGroup.mk' O u) ^ 2 ^ k = 1 := by
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff (u ^ 2 ^ k)).mpr hk
    obtain ⟨i, -, hi⟩ :=
      (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hzpow)
    exact ⟨i, hi⟩
  haveI : Nontrivial (CFSG.Timmesfeld.Bridge.RootMany.SecMod E A) :=
    Finite.one_lt_card_iff_nontrivial.mp hnt
  haveI : Module.Finite (ZMod 2) (CFSG.Timmesfeld.Bridge.RootMany.SecMod E A) :=
    Module.Finite.of_finite
  obtain ⟨v, hvne, hvfix⟩ :=
    CFSG.RankThree.OddKernel.exists_ne_zero_fixed (p := 2) hQ2 ρ
  obtain ⟨e, hv⟩ := secMk_surjective E A v
  refine ⟨e, ?_, ?_⟩
  · intro heA
    have hzero : secMk E A e = 0 := (secMk_eq_zero_iff E A e).mpr heA
    rw [hv] at hzero
    exact hvne hzero
  · intro u
    have h1 := hvfix (QuotientGroup.mk' O u)
    rw [hρmk u, ← hv] at h1
    exact h1

private theorem one_lt_card_secMod_of_card {H : Type} [Group H] [Finite H]
    (E A : Subgroup H) [A.Normal] [Fact (IsElemSection E A)] {q : ℕ}
    (hcard : Nat.card E = q * Nat.card A) (hq : 2 ≤ q) :
    1 < Nat.card (CFSG.Timmesfeld.Bridge.RootMany.SecMod E A) := by
  have h := card_secMod E A
  have hmul : Nat.card (CFSG.Timmesfeld.Bridge.RootMany.SecMod E A) *
      Nat.card A = q * Nat.card A := by
    rw [h, hcard]
  have hEq : Nat.card (CFSG.Timmesfeld.Bridge.RootMany.SecMod E A) = q :=
    Nat.eq_of_mul_eq_mul_right Nat.card_pos hmul
  rw [hEq]
  exact lt_of_lt_of_le (by norm_num : 1 < 2) hq

private theorem secRep_ker_of_le_centralizer {H : Type} [Group H] (E A K : Subgroup H)
    [E.Normal] [A.Normal] [Fact (IsElemSection E A)]
    (hK : K ≤ Subgroup.centralizer (E : Set H)) : K ≤ (secRep E A).ker := by
  intro k hk
  rw [MonoidHom.mem_ker, secRep_eq_one_iff]
  intro e he
  have hke : k * e = e * k :=
    (Subgroup.mem_centralizer_iff.mp (hK hk) e he).symm
  have h1 : k * e * k⁻¹ * e⁻¹ = 1 := by rw [hke]; group
  rw [h1]
  exact A.one_mem

private theorem commutator_inv_mem_of_secRep_fixed {H : Type} [Group H] (E A : Subgroup H)
    [E.Normal] [A.Normal] [Fact (IsElemSection E A)] {e : E}
    (hfixe : ∀ u : H, secRep E A u (secMk E A e) = secMk E A e) :
    ∀ u : H, ⁅u, (e : H)⁻¹⁆ ∈ A := by
  intro u
  have h1 := hfixe u
  rw [secRep_mk, secMk_eq_secMk_iff] at h1
  have hcoe : (((secConj E u e : E) : H)) = u * (e : H) * u⁻¹ :=
    coe_secConj (E := E) u e
  rw [hcoe] at h1
  simpa [commutatorElement_def, mul_assoc] using h1

private theorem one_lt_card_secMod_p0 (hS : Sec7Hyp M V n f) (h72 : Sec7.Stmt72 M V n f)
    (hD : L2Datum M V A B h) :
    1 < Nat.card (CFSG.Timmesfeld.Bridge.RootMany.SecMod
      ((p0Of M V (A ⊔ B)).subgroupOf (inSubgroup (Op_p'p 2) (rOf M h)))
      ((V).subgroupOf (inSubgroup (Op_p'p 2) (rOf M h)))) := by
  classical
  obtain ⟨hS1, hS2, hS3, -, hS5, -, -, -, -, -⟩ := h72 A B h hD
  set P0 : Subgroup G := p0Of M V (A ⊔ B) with hP0
  set R : Subgroup G := rOf M h with hR
  set U : Subgroup G := inSubgroup (Op_p'p 2) R with hU
  have hUR : U ≤ R := Subgroup.map_subtype_le _
  have hP0R : P0 ≤ R := p0_le_rOf hS.toSec6Hyp hD
  have hVP0 : V ≤ P0 := V_le_p0 hS.toSec6Hyp hD
  have hP02 : IsPGroup 2 P0 := (inSubgroup_pCore_two M).1.to_le
    ((inf_le_left : P0 ≤ Pc M V).trans inf_le_left)
  have hP0U : P0 ≤ U :=
    Sec7.le_Op_p'p_rOf_of_normal hP0R
      (rOf_le_normalizer_p0 hS.toSec6Hyp hD hS1) hP02
  have hcardE : Nat.card ↥(P0.subgroupOf U) = Nat.card P0 :=
    natCard_subgroupOf_eq P0 U hP0U
  have hcardA : Nat.card ↥(V.subgroupOf U) = Nat.card V :=
    natCard_subgroupOf_eq V U (hVP0.trans hP0U)
  have hn4 : 4 ≤ n := hS.four_le
  have hcard : Nat.card ↥(P0.subgroupOf U) =
      Nat.card V ^ (2 * n - 4) * Nat.card ↥(V.subgroupOf U) := by
    rw [hcardE, hcardA, hS2, show 2 * n - 3 = 2 * n - 4 + 1 by omega, pow_succ]
  have hq2 : 2 ≤ Nat.card V := by
    rw [hS.card_V]
    exact Nat.pow_le_pow_right (show 0 < 2 by norm_num) hS.one_le
  have hq : 2 ≤ Nat.card V ^ (2 * n - 4) := by
    have h4 : 4 ≤ 2 * n - 4 := by omega
    refine le_trans (by norm_num : 2 ≤ 2 ^ 4) ?_
    exact (Nat.pow_le_pow_left hq2 4).trans
      (Nat.pow_le_pow_right (show 0 < Nat.card V by positivity) h4)
  haveI : (V.subgroupOf U).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hVP0.trans hP0U)).mpr
      (hUR.trans (inf_le_left.trans hS.sec5.toRootHyp.toHyp.le_normalizer))
  have hES : IsElemSection (P0.subgroupOf U) (V.subgroupOf U) :=
    { le := fun x hx => Subgroup.mem_subgroupOf.mpr (hVP0 (Subgroup.mem_subgroupOf.mp hx))
      comm := fun x hx y hy => by
        rw [Subgroup.mem_subgroupOf, ← hS3]
        exact Subgroup.commutator_mem_commutator
          (Subgroup.mem_subgroupOf.mp hx) (Subgroup.mem_subgroupOf.mp hy)
      sq := fun x hx => by
        rw [Subgroup.mem_subgroupOf]
        exact hS5 (x : G) (Subgroup.mem_subgroupOf.mp hx) }
  haveI : Fact (IsElemSection (P0.subgroupOf U) (V.subgroupOf U)) := ⟨hES⟩
  exact one_lt_card_secMod_of_card _ _ hcard hq

private theorem secHyp_Op_p'p (hS : Sec7Hyp M V n f) (h72 : Sec7.Stmt72 M V n f)
    (hD : L2Datum M V A B h) :
    SecHyp (inSubgroup (Op_p'p 2) (rOf M h)) (p0Of M V (A ⊔ B))
      (p0Of M V (A ⊔ B)) V := by
  obtain ⟨hS1, -, hS3, -, hS5, -, -, -, -, -⟩ := h72 A B h hD
  set P0 : Subgroup G := p0Of M V (A ⊔ B) with hP0
  set R : Subgroup G := rOf M h with hR
  set U : Subgroup G := inSubgroup (Op_p'p 2) R with hU
  have hUR : U ≤ R := Subgroup.map_subtype_le _
  have hP0U : P0 ≤ U :=
    Sec7.le_Op_p'p_rOf_of_normal (p0_le_rOf hS.toSec6Hyp hD)
      (rOf_le_normalizer_p0 hS.toSec6Hyp hD hS1)
      ((inSubgroup_pCore_two M).1.to_le
        ((inf_le_left : P0 ≤ Pc M V).trans inf_le_left))
  exact
    { le := V_le_p0 hS.toSec6Hyp hD, le_R := hP0U
      conj_E := fun r hr e he => (Subgroup.mem_normalizer_iff.mp
        (hUR.trans (rOf_le_normalizer_p0 hS.toSec6Hyp hD hS1) hr) e).mp he
      conj_A := fun r hr x hx => (Subgroup.mem_normalizer_iff.mp
        (hUR.trans (inf_le_left.trans hS.sec5.toRootHyp.toHyp.le_normalizer) hr) x).mp hx
      comm := fun x hx y hy => by
        rw [← hS3]; exact Subgroup.commutator_mem_commutator hx hy
      sq := fun x hx => hS5 x hx
      ker := fun k hk e he => by
        rw [← hS3]; exact Subgroup.commutator_mem_commutator hk he }

private theorem exists_fixed_secMk_Op_p'p (hS : Sec7Hyp M V n f) (h72 : Sec7.Stmt72 M V n f)
    (hD : L2Datum M V A B h) :
    ∃ e : ↥(inSubgroup (Op_p'p 2) (rOf M h)),
      e ∈ (p0Of M V (A ⊔ B)).subgroupOf (inSubgroup (Op_p'p 2) (rOf M h)) ∧
      ((e : G) ∉ V) ∧
      ∀ u : ↥(inSubgroup (Op_p'p 2) (rOf M h)), ⁅(u : G), (e : G)⁻¹⁆ ∈ V := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P0 : Subgroup G := p0Of M V (A ⊔ B) with hP0
  set R : Subgroup G := rOf M h with hR
  set O : Subgroup G := oOf M h with hO
  set U : Subgroup G := inSubgroup (Op_p'p 2) R with hU
  have hsec : SecHyp U P0 P0 V := secHyp_Op_p'p hS h72 hD
  let E : Subgroup ↥U := P0.subgroupOf U
  let A' : Subgroup ↥U := V.subgroupOf U
  haveI : E.Normal := hsec.normal_E
  haveI : A'.Normal := hsec.normal_A
  haveI : Fact (IsElemSection E A') := ⟨hsec.isElemSection⟩
  have hKcent : O.subgroupOf U ≤ Subgroup.centralizer (E : Set ↥U) := by
    intro k hk
    exact Subgroup.mem_centralizer_iff.mpr fun e he => Subtype.ext
      (Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          (commutator_oOf_p0 hS h72 hD) (Subgroup.mem_subgroupOf.mp hk))
        (e : G) (Subgroup.mem_subgroupOf.mp he))
  have hkerO : O.subgroupOf U ≤ (secRep E A').ker :=
    secRep_ker_of_le_centralizer E A' (O.subgroupOf U) hKcent
  have hpow : ∀ u : ↥U, ∃ k : ℕ, u ^ 2 ^ k ∈ O.subgroupOf U := fun u => by
    obtain ⟨k, hk⟩ := Sec7.exists_pow_mem_oOf (M := M) (h := h) (u := (u : G)) u.2
    exact ⟨k, Subgroup.mem_subgroupOf.mpr hk⟩
  have hW1 : 1 < Nat.card (CFSG.Timmesfeld.Bridge.RootMany.SecMod E A') :=
    one_lt_card_secMod_p0 hS h72 hD
  obtain ⟨e, heA, hfixe⟩ := exists_fixed_secMk_of_isPGroup_quotient E A'
    (O.subgroupOf U)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (Sec7.oOf_le_Op_p'p M h)).mpr
      ((Subgroup.map_subtype_le _ : U ≤ R).trans (Sec7.rOf_le_normalizer_oOf M h)))
    hkerO hpow hW1
  let eU : ↥U := (e : E)
  have hcommE : ∀ u : ↥U, ⁅(u : G), (eU : G)⁻¹⁆ ∈ V := fun u => by
    change ((⁅u, (eU : ↥U)⁻¹⁆ : ↥U) : G) ∈ V
    exact Subgroup.mem_subgroupOf.mp (commutator_inv_mem_of_secRep_fixed E A' hfixe u)
  exact ⟨eU, (e : E).2, fun heV => heA (Subgroup.mem_subgroupOf.mpr heV), hcommE⟩

private theorem exists_fixed_point_Op_p'p (hS : Sec7Hyp M V n f) (h72 : Sec7.Stmt72 M V n f)
    (hD : L2Datum M V A B h) :
    ∃ x ∈ p0Of M V (A ⊔ B), x ∉ V ∧
      ∀ u ∈ inSubgroup (Op_p'p 2) (rOf M h), ⁅u, x⁆ ∈ V := by
  obtain ⟨e, heE, heV, hcomm⟩ := exists_fixed_secMk_Op_p'p hS h72 hD
  have heP0 : (e : G) ∈ p0Of M V (A ⊔ B) := Subgroup.mem_subgroupOf.mp heE
  refine ⟨(e : G)⁻¹, (p0Of M V (A ⊔ B)).inv_mem heP0, ?_, ?_⟩
  · intro hx
    exact heV (by simpa using V.inv_mem hx)
  · intro u hu
    exact hcomm ⟨u, hu⟩

private theorem le_normalizer_fixedPoints_Op_p'p (hS : Sec7Hyp M V n f)
    (hD : L2Datum M V A B h)
    (hS1 : p0Of M V (Subgroup.zpowers h) = p0Of M V (A ⊔ B))
    (S : Subgroup G)
    (hSdef : S = ⨅ v : ↥(inSubgroup (Op_p'p 2) (rOf M h)),
      CFSG.GroupTheory.commMemSubgroup M V
        hS.sec5.toRootHyp.toHyp.le_normalizer (v : G)) :
    M ⊓ cenOf (A ⊔ B) ≤ Subgroup.normalizer (S : Set G) := by
  classical
  set P0 : Subgroup G := p0Of M V (A ⊔ B) with hP0
  set R : Subgroup G := rOf M h with hR
  set U : Subgroup G := inSubgroup (Op_p'p 2) R with hU
  set K : Subgroup G := M ⊓ cenOf (A ⊔ B) with hK
  have hUR : U ≤ R := Subgroup.map_subtype_le _
  have hMV : M ≤ Subgroup.normalizer (V : Set G) :=
    hS.sec5.toRootHyp.toHyp.le_normalizer
  have hKR : K ≤ R := inf_cenOf_le_rOf hD
  have hKP0 : K ≤ Subgroup.normalizer (P0 : Set G) :=
    hKR.trans (rOf_le_normalizer_p0 hS.toSec6Hyp hD hS1)
  have hKM : K ≤ Subgroup.normalizer (M : Set G) :=
    inf_le_left.trans Subgroup.le_normalizer
  have hKV : K ≤ Subgroup.normalizer (V : Set G) := inf_le_left.trans hMV
  have hKU : K ≤ Subgroup.normalizer (U : Set G) :=
    hKR.trans (Sec7.rOf_le_normalizer_Op_p'p M h)
  have hforward : ∀ k ∈ K, ∀ y : G, y ∈ S → k * y * k⁻¹ ∈ S := by
    intro k hk y hy
    rw [hSdef] at hy ⊢
    rw [Subgroup.mem_iInf] at hy ⊢
    intro v
    simp only [CFSG.GroupTheory.mem_commMemSubgroup] at hy ⊢
    have hvU : k⁻¹ * (v : G) * k ∈ U := by
      simpa using (Subgroup.mem_normalizer_iff.mp (hKU (K.inv_mem hk)) (v : G)).mp v.2
    have hyv := hy ⟨k⁻¹ * (v : G) * k, hvU⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hKM hk) y).mp hyv.1, ?_⟩
    have hconj : ⁅k * y * k⁻¹, (v : G)⁆ = k * ⁅y, k⁻¹ * (v : G) * k⁆ * k⁻¹ := by
      rw [commutatorElement_def, commutatorElement_def]
      group
    rw [hconj]
    exact (Subgroup.mem_normalizer_iff.mp (hKV hk) _).mp hyv.2
  have hKinf : K ≤ Subgroup.normalizer (S : Set G) := by
    intro k hk
    refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨hforward k hk y, fun hy => ?_⟩
    have h1 := hforward (k⁻¹) (K.inv_mem hk) (k * y * k⁻¹) hy
    simpa [mul_assoc] using h1
  intro k hk
  exact hKinf hk

private theorem v_le_inf_fixedPoints_and_ne_Op_p'p (hS : Sec7Hyp M V n f)
    (h72 : Sec7.Stmt72 M V n f) (hD : L2Datum M V A B h) (S : Subgroup G)
    (hSdef : S = ⨅ v : ↥(inSubgroup (Op_p'p 2) (rOf M h)),
      CFSG.GroupTheory.commMemSubgroup M V
        hS.sec5.toRootHyp.toHyp.le_normalizer (v : G)) :
    V ≤ p0Of M V (A ⊔ B) ⊓ S ∧ p0Of M V (A ⊔ B) ⊓ S ≠ V := by
  classical
  obtain ⟨x, hxP0, hxV, hxfix⟩ := exists_fixed_point_Op_p'p hS h72 hD
  set P0 : Subgroup G := p0Of M V (A ⊔ B) with hP0
  set R : Subgroup G := rOf M h with hR
  set U : Subgroup G := inSubgroup (Op_p'p 2) R with hU
  have hP0R : P0 ≤ R := p0_le_rOf hS.toSec6Hyp hD
  have hVP0 : V ≤ P0 := V_le_p0 hS.toSec6Hyp hD
  have hMV : M ≤ Subgroup.normalizer (V : Set G) :=
    hS.sec5.toRootHyp.toHyp.le_normalizer
  have hVN : V ≤ P0 ⊓ S := by
    intro v hv
    have hvinf : v ∈ S := by
      rw [hSdef, Subgroup.mem_iInf]
      intro w
      rw [CFSG.GroupTheory.mem_commMemSubgroup]
      refine ⟨hS.sec5.toRootHyp.toHyp.le_M hv, ?_⟩
      have hwv : ⁅(w : G), v⁆ ∈ V := by
        have hvw : (w : G) * v * (w : G)⁻¹ ∈ V :=
          (Subgroup.mem_normalizer_iff.mp
            (hMV ((inf_le_left : R ≤ M) (Subgroup.map_subtype_le _ w.2))) v).mp hv
        have := V.mul_mem hvw (V.inv_mem hv)
        simpa [commutatorElement_def, mul_assoc] using this
      rw [← commutatorElement_inv]
      exact V.inv_mem hwv
    exact ⟨hVP0 hv, hvinf⟩
  have hxN : x ∈ P0 ⊓ S := by
    have hxinf : x ∈ S := by
      rw [hSdef, Subgroup.mem_iInf]
      intro w
      rw [CFSG.GroupTheory.mem_commMemSubgroup]
      refine ⟨(inf_le_left.trans hS.sec5.toRootHyp.toHyp.Pc_le_M) hxP0, ?_⟩
      rw [← commutatorElement_inv]
      exact V.inv_mem (hxfix (w : G) w.2)
    exact ⟨hxP0, hxinf⟩
  exact ⟨hVN, fun hNV => hxV (hNV ▸ hxN)⟩

theorem commutator_mem_V_of_mem_Op_p'p (hS : Sec7Hyp M V n f) (h72 : Sec7.Stmt72 M V n f)
    (hD : L2Datum M V A B h)
    (hirr : ∀ N : Subgroup G, V ≤ N → N ≤ p0Of M V (A ⊔ B) →
      M ⊓ cenOf (A ⊔ B) ≤ Subgroup.normalizer (N : Set G) →
      N = V ∨ N = p0Of M V (A ⊔ B))
    {u : G} (hu : u ∈ inSubgroup (Op_p'p 2) (rOf M h)) {p : G}
    (hp : p ∈ p0Of M V (A ⊔ B)) : ⁅u, p⁆ ∈ V := by
  classical
  obtain ⟨hS1, -, -, -, -, -, -, -, -, -⟩ := h72 A B h hD
  set P0 : Subgroup G := p0Of M V (A ⊔ B) with hP0
  set R : Subgroup G := rOf M h with hR
  set U : Subgroup G := inSubgroup (Op_p'p 2) R with hU
  set K : Subgroup G := M ⊓ cenOf (A ⊔ B) with hK
  have hUR : U ≤ R := Subgroup.map_subtype_le _
  have hP0R : P0 ≤ R := p0_le_rOf hS.toSec6Hyp hD
  have hMV : M ≤ Subgroup.normalizer (V : Set G) :=
    hS.sec5.toRootHyp.toHyp.le_normalizer
  let S : Subgroup G := ⨅ v : ↥U, CFSG.GroupTheory.commMemSubgroup M V hMV (v : G)
  let N : Subgroup G := P0 ⊓ S
  obtain ⟨hVN, hNV⟩ := v_le_inf_fixedPoints_and_ne_Op_p'p hS h72 hD S rfl
  have hKP0 : K ≤ Subgroup.normalizer (P0 : Set G) :=
    (inf_cenOf_le_rOf hD).trans (rOf_le_normalizer_p0 hS.toSec6Hyp hD hS1)
  have hKinf : K ≤ Subgroup.normalizer (S : Set G) :=
    le_normalizer_fixedPoints_Op_p'p hS hD hS1 S rfl
  have hKN : K ≤ Subgroup.normalizer (N : Set G) := fun k hk =>
    mem_normalizer_inf (hKP0 hk) (by simpa [S, N] using hKinf hk)
  have hN_eq : N = P0 := by
    rcases hirr N hVN inf_le_left hKN with h | h
    · exact absurd h hNV
    · exact h
  have hpN : p ∈ N := hN_eq ▸ hp
  have hpu : ⁅p, u⁆ ∈ V := by
    have hpS : p ∈ S := hpN.2
    have hmem := (Subgroup.mem_iInf.mp (show p ∈ (⨅ v : ↥U,
      CFSG.GroupTheory.commMemSubgroup M V hMV (v : G)) from hpS)) ⟨u, hu⟩
    exact (CFSG.GroupTheory.mem_commMemSubgroup hMV (u : G) p).mp hmem |>.2
  rw [← commutatorElement_inv]
  exact V.inv_mem hpu

theorem Op_p'p_rOf_eq_oOf_sup_p0Of (hS : Sec7Hyp M V n f) (h72 : Sec7.Stmt72 M V n f)
    (hD : L2Datum M V A B h)
    (hU2 : ∀ y ∈ inSubgroup (Op_p'p 2) (rOf M h), IsPGroup 2 (Subgroup.zpowers y) →
      y ∈ p0Of M V (A ⊔ B)) :
    inSubgroup (Op_p'p 2) (rOf M h) = oOf M h ⊔ p0Of M V (A ⊔ B) := by
  classical
  obtain ⟨hS1, -, -, -, -, -, -, -, -, -⟩ := h72 A B h hD
  set P0 : Subgroup G := p0Of M V (A ⊔ B) with hP0
  set R : Subgroup G := rOf M h with hR
  set O : Subgroup G := oOf M h with hO
  set U : Subgroup G := inSubgroup (Op_p'p 2) R with hU
  have hUR : U ≤ R := Subgroup.map_subtype_le _
  have hP0R : P0 ≤ R := p0_le_rOf hS.toSec6Hyp hD
  have hP02 : IsPGroup 2 P0 := (inSubgroup_pCore_two M).1.to_le
    ((inf_le_left : P0 ≤ Pc M V).trans inf_le_left)
  have hP0U : P0 ≤ U :=
    Sec7.le_Op_p'p_rOf_of_normal hP0R
      (rOf_le_normalizer_p0 hS.toSec6Hyp hD hS1) hP02
  have hOU : O ≤ U := Sec7.oOf_le_Op_p'p M h
  refine le_antisymm ?_ (_root_.sup_le hOU hP0U)
  intro y hyU
  obtain ⟨a, b, hyab, ha, hb, ha2, hbo⟩ :=
    CFSG.CGT.PushingUpLit.SolKNA.R4.exists_mul_eq_isPGroup_odd y
  have hzU : Subgroup.zpowers y ≤ U := Subgroup.zpowers_le.mpr hyU
  have haU : a ∈ U := hzU ha
  have hbU : b ∈ U := hzU hb
  have haP0 : a ∈ P0 := hU2 a haU ha2
  have hbO : b ∈ O := by
    obtain ⟨k, hk⟩ := Sec7.exists_pow_mem_oOf (M := M) (h := h) hbU
    have hbzp : b ∈ Subgroup.zpowers (b ^ 2 ^ k) :=
      mem_zpowers_pow_iff.mpr (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hbo))
    exact (Subgroup.zpowers_le.mpr hk) hbzp
  rw [hyab]
  exact (O ⊔ P0).mul_mem (Subgroup.mem_sup_right haP0) (Subgroup.mem_sup_left hbO)

theorem pCore_quot_rOf_eq_map_p0Of (hS : Sec7Hyp M V n f) (h72 : Sec7.Stmt72 M V n f)
    (hD : L2Datum M V A B h)
    (hU2 : ∀ y ∈ inSubgroup (Op_p'p 2) (rOf M h), IsPGroup 2 (Subgroup.zpowers y) →
      y ∈ p0Of M V (A ⊔ B)) :
    pCore 2 (↥(rOf M h) ⧸ pPrimeCore 2 ↥(rOf M h)) =
      ((p0Of M V (A ⊔ B)).subgroupOf (rOf M h)).map (QuotientGroup.mk' _) := by
  classical
  set P0 : Subgroup G := p0Of M V (A ⊔ B) with hP0
  set R : Subgroup G := rOf M h with hR
  set O : Subgroup G := oOf M h with hO
  set U : Subgroup G := inSubgroup (Op_p'p 2) R with hU
  have hOR : O ≤ R := Subgroup.map_subtype_le _
  have hP0R : P0 ≤ R := p0_le_rOf hS.toSec6Hyp hD
  have hOsub : O.subgroupOf R = pPrimeCore 2 ↥R := by
    rw [hO, hR, oOf, inSubgroup]
    exact Subgroup.comap_map_eq_self_of_injective (rOf M h).subtype_injective
      (pPrimeCore 2 ↥(rOf M h))
  have hOp : Op_p'p 2 ↥R = U.subgroupOf R := by
    rw [hU, hR, inSubgroup]
    exact (Subgroup.comap_map_eq_self_of_injective (rOf M h).subtype_injective
      (Op_p'p 2 ↥(rOf M h))).symm
  have hOpEq : Op_p'p 2 ↥R = O.subgroupOf R ⊔ P0.subgroupOf R := by
    rw [hOp, hU, hR, Op_p'p_rOf_eq_oOf_sup_p0Of hS h72 hD hU2, Subgroup.subgroupOf_sup hOR hP0R]
  have hcore : pCore 2 (↥R ⧸ pPrimeCore 2 ↥R) =
      (Op_p'p 2 ↥R).map (QuotientGroup.mk' (pPrimeCore 2 ↥R)) := by
    rw [show Op_p'p 2 ↥R =
      (pCore 2 (↥R ⧸ pPrimeCore 2 ↥R)).comap
        (QuotientGroup.mk' (pPrimeCore 2 ↥R)) from rfl]
    exact (Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective (pPrimeCore 2 ↥R)) _).symm
  have hker : (pPrimeCore 2 ↥R).map (QuotientGroup.mk' (pPrimeCore 2 ↥R)) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨x, hx, rfl⟩
    exact (QuotientGroup.eq_one_iff x).mpr hx
  rw [hcore, hOpEq, Subgroup.map_sup, hOsub, hker, bot_sup_eq]

private theorem commutator_mem_oOf_of_mem_centralizer_pCore (hS : Sec7Hyp M V n f)
    (hD : L2Datum M V A B h) (y : ↥(rOf M h))
    (hz : QuotientGroup.mk' (pPrimeCore 2 ↥(rOf M h)) y ∈
      Subgroup.centralizer
        (((p0Of M V (A ⊔ B)).subgroupOf (rOf M h)).map
          (QuotientGroup.mk' (pPrimeCore 2 ↥(rOf M h))) :
          Set (↥(rOf M h) ⧸ pPrimeCore 2 ↥(rOf M h)))) :
    ∀ p ∈ p0Of M V (A ⊔ B), ⁅(y : G), p⁆ ∈ oOf M h := by
  classical
  set P0 : Subgroup G := p0Of M V (A ⊔ B) with hP0
  set O : Subgroup G := oOf M h with hO
  have hP0R : P0 ≤ rOf M h := p0_le_rOf hS.toSec6Hyp hD
  intro p hp
  have hpR : p ∈ rOf M h := hP0R hp
  have hmem : QuotientGroup.mk' (pPrimeCore 2 ↥(rOf M h))
      (⟨p, hpR⟩ : ↥(rOf M h)) ∈
      ((P0).subgroupOf (rOf M h)).map
        (QuotientGroup.mk' (pPrimeCore 2 ↥(rOf M h))) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hp)
  have hcomm := Subgroup.mem_centralizer_iff.mp hz _ hmem
  have hcomm' : ⁅QuotientGroup.mk' (pPrimeCore 2 ↥(rOf M h)) y,
      QuotientGroup.mk' (pPrimeCore 2 ↥(rOf M h))
        (⟨p, hpR⟩ : ↥(rOf M h))⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact hcomm.symm
  have hmap : QuotientGroup.mk' (pPrimeCore 2 ↥(rOf M h))
      ⁅y, (⟨p, hpR⟩ : ↥(rOf M h))⁆ = 1 := by
    rw [map_commutatorElement, hcomm']
  have hmemcore : ⁅y, (⟨p, hpR⟩ : ↥(rOf M h))⁆ ∈
      pPrimeCore 2 ↥(rOf M h) :=
    (QuotientGroup.eq_one_iff _).mp hmap
  have hcoe : ((⁅y, (⟨p, hpR⟩ : ↥(rOf M h))⁆ : ↥(rOf M h)) : G) =
      ⁅(y : G), p⁆ := rfl
  rw [← hcoe]
  change ((⁅y, (⟨p, hpR⟩ : ↥(rOf M h))⁆ : ↥(rOf M h)) : G) ∈
    (pPrimeCore 2 ↥(rOf M h)).map (rOf M h).subtype
  exact Subgroup.mem_map_of_mem (rOf M h).subtype hmemcore

private theorem mem_sup_oOf_V_of_mem_centralizer_pCore (hS : Sec7Hyp M V n f)
    (h72 : Sec7.Stmt72 M V n f) (hD : L2Datum M V A B h)
    (hT2 : ∀ y ∈ rOf M h ⊓ cenOf (p0Of M V (A ⊔ B)),
      IsPGroup 2 (Subgroup.zpowers y) → y ∈ V)
    (y : ↥(rOf M h))
    (hz : QuotientGroup.mk' (pPrimeCore 2 ↥(rOf M h)) y ∈
      Subgroup.centralizer
        (((p0Of M V (A ⊔ B)).subgroupOf (rOf M h)).map
          (QuotientGroup.mk' (pPrimeCore 2 ↥(rOf M h))) :
          Set (↥(rOf M h) ⧸ pPrimeCore 2 ↥(rOf M h)))) :
    (y : G) ∈ oOf M h ⊔ V := by
  classical
  obtain ⟨hS1, -, -, -, -, -, -, -, -, -⟩ := h72 A B h hD
  set P0 : Subgroup G := p0Of M V (A ⊔ B) with hP0
  set O : Subgroup G := oOf M h with hO
  have hcentP0 : ∀ p ∈ P0, ⁅(y : G), p⁆ ∈ O :=
    commutator_mem_oOf_of_mem_centralizer_pCore hS hD y hz
  have hcent : (y : G) ∈ cenOf P0 := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hmemO : ⁅(y : G), p⁆ ∈ O := hcentP0 p hp
    have hmemP0 : ⁅(y : G), p⁆ ∈ P0 := by
      have hyP0 : (y : G) * p * (y : G)⁻¹ ∈ P0 :=
        (Subgroup.mem_normalizer_iff.mp
          (rOf_le_normalizer_p0 hS.toSec6Hyp hD hS1 y.2) p).mp hp
      have := P0.mul_mem hyP0 (P0.inv_mem hp)
      simpa [commutatorElement_def, mul_assoc] using this
    have hbot : ⁅(y : G), p⁆ ∈ (⊥ : Subgroup G) := by
      have hmem : ⁅(y : G), p⁆ ∈ O ⊓ P0 := ⟨hmemO, hmemP0⟩
      rwa [oOf_inf_p0Of M V (A ⊔ B) h] at hmem
    exact (commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hbot)).symm
  rw [← rOf_inf_cenOf_p0Of_eq hS h72 hD hT2]
  exact ⟨y.2, hcent⟩

theorem generalizedFitting_quot_rOf_eq_pCore (hS : Sec7Hyp M V n f) (h72 : Sec7.Stmt72 M V n f)
    (hD : L2Datum M V A B h)
    (hU2 : ∀ y ∈ inSubgroup (Op_p'p 2) (rOf M h), IsPGroup 2 (Subgroup.zpowers y) →
      y ∈ p0Of M V (A ⊔ B))
    (hT2 : ∀ y ∈ rOf M h ⊓ cenOf (p0Of M V (A ⊔ B)),
      IsPGroup 2 (Subgroup.zpowers y) → y ∈ V) :
    generalizedFitting (↥(rOf M h) ⧸ pPrimeCore 2 ↥(rOf M h)) =
      pCore 2 (↥(rOf M h) ⧸ pPrimeCore 2 ↥(rOf M h)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hS1, -, -, -, -, -, -, -, -, -⟩ := h72 A B h hD
  set P0 : Subgroup G := p0Of M V (A ⊔ B) with hP0
  set R : Subgroup G := rOf M h with hR
  set O : Subgroup G := oOf M h with hO
  have hOR : O ≤ R := Subgroup.map_subtype_le _
  have hP0R : P0 ≤ R := p0_le_rOf hS.toSec6Hyp hD
  have hOp : pCore 2 (↥R ⧸ pPrimeCore 2 ↥R) =
      (P0.subgroupOf R).map (QuotientGroup.mk' (pPrimeCore 2 ↥R)) :=
    pCore_quot_rOf_eq_map_p0Of hS h72 hD hU2
  have hOsub : O.subgroupOf R = pPrimeCore 2 ↥R := by
    rw [hO, hR, oOf, inSubgroup]
    exact Subgroup.comap_map_eq_self_of_injective (rOf M h).subtype_injective
      (pPrimeCore 2 ↥(rOf M h))
  have hOV : R ⊓ cenOf P0 = O ⊔ V := rOf_inf_cenOf_p0Of_eq hS h72 hD hT2
  have hchar : IsCharacteristicP 2 (↥R ⧸ pPrimeCore 2 ↥R) := by
    change Subgroup.centralizer (pCore 2 (↥R ⧸ pPrimeCore 2 ↥R) :
      Set (↥R ⧸ pPrimeCore 2 ↥R)) ≤ pCore 2 (↥R ⧸ pPrimeCore 2 ↥R)
    rw [hOp]
    intro z hz
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥R) z
    have hyOV : (y : G) ∈ O ⊔ V :=
      mem_sup_oOf_V_of_mem_centralizer_pCore hS h72 hD hT2 y hz
    have hVR : V ≤ R := (V_le_p0 hS.toSec6Hyp hD).trans hP0R
    have hOn : (O.subgroupOf R).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hOR).mpr
        (Sec7.rOf_le_normalizer_oOf M h)
    have hVn : (V.subgroupOf R).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hVR).mpr
        ((inf_le_left : R ≤ M).trans (hS.sec5.toRootHyp.toHyp.le_normalizer))
    have hyOV' : y ∈ O.subgroupOf R ⊔ V.subgroupOf R := by
      rw [← Subgroup.subgroupOf_sup hOR hVR]
      exact Subgroup.mem_subgroupOf.mpr hyOV
    letI := hOn
    letI := hVn
    obtain ⟨oR, hoR, vR, hvR, hy_eqR⟩ :=
      (Subgroup.mem_sup_of_normal_left (s := O.subgroupOf R)
        (t := V.subgroupOf R)).mp hyOV'
    have hv : (vR : G) ∈ V := Subgroup.mem_subgroupOf.mp hvR
    have hy_eq : (y : G) = (oR : G) * (vR : G) := (congrArg Subtype.val hy_eqR).symm
    have hvP0 : (vR : G) ∈ P0 := V_le_p0 hS.toSec6Hyp hD hv
    have ho1 : QuotientGroup.mk' (pPrimeCore 2 ↥R) oR = 1 :=
      (QuotientGroup.eq_one_iff oR).mpr (hOsub ▸ hoR)
    have hz_eq : QuotientGroup.mk' (pPrimeCore 2 ↥R) y =
        QuotientGroup.mk' (pPrimeCore 2 ↥R) vR := by
      have hy' : y = oR * vR := Subtype.ext hy_eq
      rw [hy', map_mul, ho1, one_mul]
    rw [hz_eq]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hvP0)
  exact (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore _ 2).mp hchar

theorem maximal_V_elemAbelian_rOf (hS : Sec7Hyp M V n f) (h72 : Sec7.Stmt72 M V n f)
    (hD : L2Datum M V A B h)
    (hU2 : ∀ y ∈ inSubgroup (Op_p'p 2) (rOf M h), IsPGroup 2 (Subgroup.zpowers y) →
      y ∈ p0Of M V (A ⊔ B))
    (hirr : ∀ N : Subgroup G, V ≤ N → N ≤ p0Of M V (A ⊔ B) →
      M ⊓ cenOf (A ⊔ B) ≤ Subgroup.normalizer (N : Set G) →
      N = V ∨ N = p0Of M V (A ⊔ B)) :
    Maximal (fun U' : Subgroup G => U' ≤ rOf M h ∧
      rOf M h ≤ Subgroup.normalizer (U' : Set G) ∧ Assembly.IsElemAbelian 2 U') V := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hS1, -, hS3, -, -, -, -, -, -, -⟩ := h72 A B h hD
  set P0 : Subgroup G := p0Of M V (A ⊔ B) with hP0
  set R : Subgroup G := rOf M h with hR
  set U : Subgroup G := inSubgroup (Op_p'p 2) R with hU
  have hS3' : ⁅P0, P0⁆ = V := hS3
  have hVR : V ≤ R := (V_le_p0 hS.toSec6Hyp hD).trans (p0_le_rOf hS.toSec6Hyp hD)
  have hRV : R ≤ Subgroup.normalizer (V : Set G) :=
    inf_le_left.trans hS.sec5.toRootHyp.toHyp.le_normalizer
  refine ⟨⟨hVR, hRV, hS.sec5.toRootHyp.toHyp.elem⟩, fun W hW hVW => ?_⟩
  obtain ⟨hWR, hWN, hWelem⟩ := hW
  have hW2 : IsPGroup 2 W := by
    rw [IsPGroup.iff_orderOf]
    intro z
    have hz2 : ((z : ↥W) : G) ^ 2 = 1 := hWelem.2 (z : G) z.2
    have hdvd : orderOf ((z : ↥W) : G) ∣ 2 ^ 1 := by
      simpa using orderOf_dvd_of_pow_eq_one hz2
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨i, (Subgroup.orderOf_coe z).symm.trans hi⟩
  have hWU : W ≤ U := Sec7.le_Op_p'p_rOf_of_normal hWR hWN hW2
  have hWP0 : W ≤ P0 := by
    intro y hy
    exact hU2 y (hWU hy) (hW2.to_le (Subgroup.zpowers_le.mpr hy))
  have hKN : M ⊓ cenOf (A ⊔ B) ≤ Subgroup.normalizer (W : Set G) :=
    (inf_cenOf_le_rOf hD).trans hWN
  rcases hirr W hVW hWP0 hKN with h | h
  · rw [h]
  · exfalso
    have hcomm : ⁅P0, P0⁆ = ⊥ := by
      rw [← h]
      exact Subgroup.commutator_self_eq_bot_iff.mpr hWelem.1
    rw [hS3'] at hcomm
    exact hS.sec5.toRootHyp.toHyp.ne_bot hcomm

end L2Datum

end CFSG.RankThree.GF2n.Tim81

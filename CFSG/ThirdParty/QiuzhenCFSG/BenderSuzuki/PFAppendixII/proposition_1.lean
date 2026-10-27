module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.RightNearField
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_1_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.Basic
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Suzuki.VI.section_2_2.example_3
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_1_b
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_2_a
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_b
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem
public import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Algebra.GroupWithZero.TransferInstance

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi Appendix II, Proposition 1

The statement follows the authoritative Part II source, printed page 137.
-/

namespace CFSG.BenderSuzuki
namespace PFAppendixII

open PFchapter1section1 PFAppendixIII
open scoped Pointwise

universe u v

private theorem twoRankAtLeastTwo_of_subgroup
    {G : Type u} [Group G] [Finite G] (P : Subgroup G)
    (hP : TwoRankAtLeastTwo P) : TwoRankAtLeastTwo G := by
  rcases hP with ⟨E, hEcard, hEsq⟩
  let EG : Subgroup G := E.map P.subtype
  have hEGcard : Nat.card EG = 4 := by
    rw [Subgroup.card_map_of_injective P.subtype_injective]
    exact hEcard
  refine ⟨EG, hEGcard, ?_⟩
  rintro ⟨x, hx⟩
  rcases hx with ⟨y, hy, rfl⟩
  apply Subtype.ext
  exact congrArg (fun z : E => ((z : P) : G)) (hEsq ⟨y, hy⟩)

public theorem unique_order_two_subgroup_of_not_twoRank
    {G : Type u} [Group G] [Finite G] [Nontrivial G]
    (hGp : IsPGroup 2 G) (h2rank : ¬ TwoRankAtLeastTwo G) :
    ∃ U : Subgroup G, Nat.card U = 2 ∧
      ∀ V : Subgroup G, Nat.card V = 2 → V = U := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcenter_nontrivial : Nontrivial (Subgroup.center G) := hGp.center_nontrivial
  have hcenter_p : IsPGroup 2 (Subgroup.center G) :=
    hGp.to_subgroup (Subgroup.center G)
  obtain ⟨Zc, hZc_card⟩ :=
    Sylow.exists_subgroup_card_pow_prime_of_le_card
      (G := Subgroup.center G) (n := 1) (p := 2) Nat.prime_two hcenter_p (by
        exact Nat.succ_le_of_lt
          (Finite.one_lt_card_iff_nontrivial.mpr hcenter_nontrivial))
  let Z : Subgroup G := Zc.map (Subgroup.center G).subtype
  have hZ_card : Nat.card Z = 2 := by
    rw [Subgroup.card_map_of_injective (Subgroup.center G).subtype_injective]
    simpa using hZc_card
  have hZ_le_center : Z ≤ Subgroup.center G := by
    exact Subgroup.map_subtype_le Zc
  have hZ_normal : Z.Normal := by
    constructor
    intro z hz g
    have hcomm : g * z = z * g := Subgroup.mem_center_iff.mp (hZ_le_center hz) g
    have hconj : g * z * g⁻¹ = z := by rw [hcomm]; group
    rw [hconj]
    exact hz
  letI : Z.Normal := hZ_normal
  refine ⟨Z, hZ_card, ?_⟩
  intro V hV_card
  by_contra hV_ne_Z
  have hdis : Disjoint V Z := by
    rw [disjoint_iff]
    let I : Subgroup V := (V ⊓ Z).subgroupOf V
    haveI : Fact (Nat.Prime (Nat.card V)) := ⟨by simpa [hV_card] using Nat.prime_two⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card I with hIbot | hItop
    · calc
        V ⊓ Z = I.map V.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le (H := V ⊓ Z) (K := V) inf_le_left).symm
        _ = ⊥ := by rw [hIbot]; simp
    · exfalso
      apply hV_ne_Z
      apply Subgroup.eq_of_le_of_card_ge
      · intro v hv
        have hvI : (⟨v, hv⟩ : V) ∈ I := by simp [I, hItop]
        have hvInf : v ∈ V ⊓ Z := hvI
        exact hvInf.2
      · simp [hV_card, hZ_card]
  let E : Subgroup G := V ⊔ Z
  have hV_le_E : V ≤ E := by simp [E]
  have hZ_le_E : Z ≤ E := by simp [E]
  let VE : Subgroup E := V.subgroupOf E
  let ZE : Subgroup E := Z.subgroupOf E
  have hmul_bij : Function.Bijective
      (fun x : VE × ZE => (x.1 : E) * (x.2 : E)) := by
    constructor
    · rintro ⟨v1, z1⟩ ⟨v2, z2⟩ heq
      have heqG : (v1 : G) * (z1 : G) = (v2 : G) * (z2 : G) :=
        congrArg (fun e : E => (e : G)) heq
      have hcross : (v2 : G)⁻¹ * (v1 : G) = (z2 : G) * (z1 : G)⁻¹ := by
        calc
          (v2 : G)⁻¹ * (v1 : G) =
              (v2 : G)⁻¹ * ((v1 : G) * (z1 : G)) * (z1 : G)⁻¹ := by group
          _ = (v2 : G)⁻¹ * ((v2 : G) * (z2 : G)) * (z1 : G)⁻¹ := by rw [heqG]
          _ = (z2 : G) * (z1 : G)⁻¹ := by group
      have hcrossV : (v2 : G)⁻¹ * (v1 : G) ∈ V :=
        V.mul_mem (V.inv_mem v2.2) v1.2
      have hcrossZ : (v2 : G)⁻¹ * (v1 : G) ∈ Z := by
        rw [hcross]
        exact Z.mul_mem z2.2 (Z.inv_mem z1.2)
      have hcross_mem : (v2 : G)⁻¹ * (v1 : G) ∈ V ⊓ Z := ⟨hcrossV, hcrossZ⟩
      have hcross_one : (v2 : G)⁻¹ * (v1 : G) = 1 := by
        rw [disjoint_iff.mp hdis] at hcross_mem
        exact Subgroup.mem_bot.mp hcross_mem
      have hv : (v1 : G) = (v2 : G) := by
        calc
          (v1 : G) = (v2 : G) * ((v2 : G)⁻¹ * (v1 : G)) := by group
          _ = (v2 : G) := by rw [hcross_one]; simp
      have hz : (z1 : G) = (z2 : G) := by
        rw [hv] at heqG
        exact mul_left_cancel heqG
      apply Prod.ext
      · apply Subtype.ext
        apply Subtype.ext
        exact hv
      · apply Subtype.ext
        apply Subtype.ext
        exact hz
    · intro e
      have he_mem : (e : G) ∈ V ⊔ Z := e.2
      rcases (Subgroup.mem_sup_of_normal_right.mp he_mem) with ⟨v, hv, z, hz, hvz⟩
      let vE : VE := ⟨⟨v, hV_le_E hv⟩, hv⟩
      let zE : ZE := ⟨⟨z, hZ_le_E hz⟩, hz⟩
      refine ⟨(vE, zE), ?_⟩
      apply Subtype.ext
      exact hvz
  have hcompl : VE.IsComplement' ZE :=
    (Subgroup.isComplement_iff_bijective VE ZE).mpr hmul_bij
  have hE_card : Nat.card E = 4 := by
    have hc := hcompl.card_mul
    rw [natCard_subgroupOf_eq V E hV_le_E,
      natCard_subgroupOf_eq Z E hZ_le_E, hV_card, hZ_card] at hc
    simpa using hc.symm
  apply h2rank
  refine ⟨E, hE_card, ?_⟩
  intro e
  have he_mem : (e : G) ∈ V ⊔ Z := e.2
  rcases (Subgroup.mem_sup_of_normal_right.mp he_mem) with ⟨v, hv, z, hz, hvz⟩
  letI : Fintype V := Fintype.ofFinite V
  letI : Fintype Z := Fintype.ofFinite Z
  have hv_sq : v ^ 2 = 1 := by
    have hp := pow_card_eq_one (x := (⟨v, hv⟩ : V))
    have hpG : v ^ Fintype.card V = (1 : G) :=
      congrArg (fun x : V => (x : G)) hp
    have hcard_ft : Fintype.card V = 2 := by simpa using hV_card
    rwa [hcard_ft] at hpG
  have hz_sq : z ^ 2 = 1 := by
    have hp := pow_card_eq_one (x := (⟨z, hz⟩ : Z))
    have hpG : z ^ Fintype.card Z = (1 : G) :=
      congrArg (fun x : Z => (x : G)) hp
    have hcard_ft : Fintype.card Z = 2 := by simpa using hZ_card
    rwa [hcard_ft] at hpG
  have hvz_comm : Commute v z := by
    rw [commute_iff_eq]
    exact Subgroup.mem_center_iff.mp (hZ_le_center hz) v
  apply Subtype.ext
  change ((e : G) ^ 2) = 1
  rw [← hvz, hvz_comm.mul_pow, hv_sq, hz_sq, one_mul]

private theorem proposition_1_sylow_two_cyclic_or_generalizedQuaternion
    {G : Type u} {Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G) (hA1 : HypothesisA1 G Ω H D Q t)
    (h2rank : ¬ TwoRankAtLeastTwo G) :
    ∃ P : Sylow 2 G, (P : Subgroup G) ≤ Q ∧
      (IsCyclic P ∨
        ∃ n : ℕ, 3 ≤ n ∧ Nonempty (P ≃* QuaternionGroup (2 ^ (n - 2)))) := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP_le_Q⟩ := PFchapter1section1.proposition_1_c H D Q t hA1
  have htwo_dvd_Q : 2 ∣ Nat.card Q := even_iff_two_dvd.mp hA1.Q_even
  have htwo_dvd_G : 2 ∣ Nat.card G :=
    htwo_dvd_Q.trans (Subgroup.card_subgroup_dvd_card Q)
  have hP_ne_bot : (P : Subgroup G) ≠ ⊥ := P.ne_bot_of_dvd_card htwo_dvd_G
  letI : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot (P : Subgroup G)).mpr hP_ne_bot
  have h2rankP : ¬ TwoRankAtLeastTwo P := by
    intro hP
    exact h2rank (twoRankAtLeastTwo_of_subgroup (P : Subgroup G) hP)
  obtain ⟨U, hUcard, hUunique⟩ :=
    unique_order_two_subgroup_of_not_twoRank P.isPGroup' h2rankP
  have hclass :=
    (External.huppert_III_8_2_pgroup_unique_order_prime_subgroup
      Nat.prime_two P.isPGroup' ⟨U, hUcard, hUunique⟩).2 rfl
  exact ⟨P, hP_le_Q, hclass⟩

private theorem proposition_1_factorization_of_cyclic_sylow_two
    {G : Type*} [Group G] [Finite G] (P : Sylow 2 G) (u : G)
    (hPcyc : IsCyclic P) (huI : IsInvolution u) :
    pPrimeCore 2 G ⊔ Subgroup.centralizer ({u} : Set G) = ⊤ := by
  classical
  have huOrder : orderOf u = 2 :=
    orderOf_eq_prime huI.sq_eq_one huI.ne_one
  have htwo_dvd : 2 ∣ Nat.card G := by
    simpa [huOrder] using orderOf_dvd_natCard u
  have hmin : (Nat.card G).minFac = 2 :=
    (Nat.minFac_eq_two_iff (Nat.card G)).2 htwo_dvd
  have hzuP : IsPGroup 2 (Subgroup.zpowers u) := by
    refine IsPGroup.of_card (p := 2) (G := Subgroup.zpowers u) (n := 1) ?_
    rw [Nat.card_zpowers, huOrder, pow_one]
  obtain ⟨S, hzuS⟩ := hzuP.exists_le_sylow
  have huS : u ∈ (S : Subgroup G) := hzuS (Subgroup.mem_zpowers u)
  letI : IsCyclic P := hPcyc
  have hScyc : IsCyclic S :=
    isCyclic_of_surjective (P.equiv S) (P.equiv S).surjective
  letI : IsCyclic S := hScyc
  haveI : IsMulCommutative S := hScyc.isMulCommutative
  have hScentral : (S : Subgroup G) ≤ Subgroup.centralizer ({u} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    simp only [Set.mem_singleton_iff] at hy
    subst y
    exact congrArg Subtype.val
      (hScyc.isMulCommutative.is_comm.comm
        (⟨u, huS⟩ : (S : Subgroup G)) (⟨x, hx⟩ : (S : Subgroup G)))
  let K : Subgroup G :=
    (MonoidHom.transferSylow S (hScyc.normalizer_le_centralizer hmin)).ker
  have hcomp : K.IsComplement' (S : Subgroup G) := by
    simpa [K] using hScyc.isComplement' hmin
  have hK_notdvd : ¬ 2 ∣ Nat.card K := by
    rw [← hcomp.index_eq_card]
    exact S.not_dvd_index
  have hK_le_core : K ≤ pPrimeCore 2 G := by
    exact le_sSup ⟨(inferInstance : K.Normal),
      Nat.prime_two.coprime_iff_not_dvd.mpr hK_notdvd⟩
  apply top_unique
  rw [← hcomp.sup_eq_top]
  exact sup_le_sup hK_le_core hScentral
private lemma appendixII_quaternionGroup_eq_a_parameter_of_isInvolution
    (m : ℕ) [NeZero m] {q : QuaternionGroup m} (hq : IsInvolution q) :
    q = QuaternionGroup.a (m : ZMod (2 * m)) := by
  have hm_pos : 0 < m := NeZero.pos m
  have hm_lt : m < 2 * m := by omega
  cases q with
  | xa i =>
      have horder_two :
          orderOf (QuaternionGroup.xa i : QuaternionGroup m) = 2 :=
        orderOf_eq_prime hq.sq_eq_one hq.ne_one
      rw [QuaternionGroup.orderOf_xa] at horder_two
      omega
  | a i =>
      have horder_two :
          orderOf (QuaternionGroup.a i : QuaternionGroup m) = 2 :=
        orderOf_eq_prime hq.sq_eq_one hq.ne_one
      rw [QuaternionGroup.orderOf_a] at horder_two
      have hdiv_mul :=
        Nat.div_mul_cancel (Nat.gcd_dvd_left (2 * m) i.val)
      rw [horder_two] at hdiv_mul
      have hgcd : Nat.gcd (2 * m) i.val = m := by omega
      have hm_dvd_i : m ∣ i.val := by
        obtain ⟨k, hk⟩ := Nat.gcd_dvd_right (2 * m) i.val
        refine ⟨k, ?_⟩
        calc
          i.val = Nat.gcd (2 * m) i.val * k := hk
          _ = m * k := by rw [hgcd]
      obtain ⟨k, hk⟩ := hm_dvd_i
      have hi_lt : i.val < 2 * m := ZMod.val_lt i
      have hi_ne_zero : i.val ≠ 0 := by
        intro hi_zero
        apply hq.ne_one
        rw [QuaternionGroup.one_def]
        congr 1
        exact (ZMod.val_eq_zero i).mp hi_zero
      have hk_ne_zero : k ≠ 0 := by
        intro hk_zero
        apply hi_ne_zero
        simp [hk, hk_zero]
      have hk_lt_two : k < 2 := by
        apply (Nat.mul_lt_mul_right hm_pos).mp
        simpa [Nat.mul_comm, hk] using hi_lt
      have hk_eq : k = 1 := by omega
      congr 1
      apply ZMod.val_injective
      simp [hk, hk_eq, ZMod.val_natCast, Nat.mod_eq_of_lt hm_lt]
private lemma appendixII_isPGroup_zpowers_of_involution
    {G : Type u} [Group G] [Finite G] {x : G} (hx : IsInvolution x) :
    IsPGroup 2 (Subgroup.zpowers x) := by
  have horder : orderOf x = 2 := (orderOf_eq_prime_iff).2 ⟨hx.2, hx.1⟩
  have hcard : Nat.card (Subgroup.zpowers x) = 2 := by
    simp [Nat.card_zpowers, horder]
  exact IsPGroup.of_card (p := 2) (G := Subgroup.zpowers x) (n := 1) (by
    simp [hcard])

private lemma appendixII_sylow_involution_unique
    {G : Type u} [Group G] [Finite G]
    (Q : Sylow 2 G) {n : ℕ}
    (hQ : Nonempty (Q ≃* QuaternionGroup (2 ^ (n - 2)))) :
    ∀ x y : Q, IsInvolution x → IsInvolution y → x = y := by
  let eqv : Q ≃* QuaternionGroup (2 ^ (n - 2)) := Classical.choice hQ
  intro x y hx hy
  have hex : IsInvolution (eqv x) := by
    constructor
    · intro h
      apply hx.ne_one
      apply eqv.injective
      simpa using h
    · simpa using congrArg eqv hx.sq_eq_one
  have hey : IsInvolution (eqv y) := by
    constructor
    · intro h
      apply hy.ne_one
      apply eqv.injective
      simpa using h
    · simpa using congrArg eqv hy.sq_eq_one
  apply eqv.injective
  exact
    (appendixII_quaternionGroup_eq_a_parameter_of_isInvolution
      (2 ^ (n - 2)) hex).trans
      (appendixII_quaternionGroup_eq_a_parameter_of_isInvolution
        (2 ^ (n - 2)) hey).symm

private lemma appendixII_commuting_involutions_eq
    {G : Type u} [Group G] [Finite G]
    (Q : Sylow 2 G)
    (hunique : ∀ x y : Q, IsInvolution x → IsInvolution y → x = y)
    {u v : G} (hu : IsInvolution u) (hv : IsInvolution v) (huv : Commute u v) :
    u = v := by
  have huP : IsPGroup 2 (Subgroup.zpowers u) :=
    appendixII_isPGroup_zpowers_of_involution hu
  have hvP : IsPGroup 2 (Subgroup.zpowers v) :=
    appendixII_isPGroup_zpowers_of_involution hv
  have hnorm : Subgroup.zpowers u ≤ Subgroup.normalizer (Subgroup.zpowers v) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor <;> intro hy
    · rcases hx with ⟨m, rfl⟩
      rcases hy with ⟨n, rfl⟩
      exact ⟨n, by rw [huv.zpow_zpow m n, mul_inv_cancel_right]⟩
    · rcases hx with ⟨m, rfl⟩
      rcases hy with ⟨n, hn⟩
      refine ⟨n, ?_⟩
      change v ^ n = u ^ m * y * (u ^ m)⁻¹ at hn
      have hcomm := huv.zpow_zpow m n
      calc
        v ^ n = (u ^ m)⁻¹ * (u ^ m * v ^ n) := by group
        _ = (u ^ m)⁻¹ * (v ^ n * u ^ m) := by rw [hcomm.eq]
        _ = (u ^ m)⁻¹ * ((u ^ m * y * (u ^ m)⁻¹) * u ^ m) := by rw [hn]
        _ = y := by group
  have hsupP : IsPGroup 2
      (Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' huP hvP hnorm
  obtain ⟨S, hsup_le_S⟩ :=
    IsPGroup.exists_le_sylow (G := G) (p := 2) hsupP
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S Q
  have huS : u ∈ (S : Subgroup G) :=
    hsup_le_S ((le_sup_left :
      Subgroup.zpowers u ≤ Subgroup.zpowers u ⊔ Subgroup.zpowers v)
        (Subgroup.mem_zpowers u))
  have hvS : v ∈ (S : Subgroup G) :=
    hsup_le_S ((le_sup_right :
      Subgroup.zpowers v ≤ Subgroup.zpowers u ⊔ Subgroup.zpowers v)
        (Subgroup.mem_zpowers v))
  have hcoe : ((g • S : Sylow 2 G) : Subgroup G) = (Q : Subgroup G) :=
    congrArg (fun P : Sylow 2 G => (P : Subgroup G)) hg
  let ug : Q := ⟨g * u * g⁻¹, by
    have hmem' : g * u * g⁻¹ ∈ ((g • S : Sylow 2 G) : Subgroup G) := by
      rw [Sylow.coe_subgroup_smul]
      exact Set.mem_smul_set.mpr ⟨u, huS, rfl⟩
    have hmem : g * u * g⁻¹ ∈ (Q : Subgroup G) := by
      simpa [hcoe] using hmem'
    exact hmem⟩
  let vg : Q := ⟨g * v * g⁻¹, by
    have hmem' : g * v * g⁻¹ ∈ ((g • S : Sylow 2 G) : Subgroup G) := by
      rw [Sylow.coe_subgroup_smul]
      exact Set.mem_smul_set.mpr ⟨v, hvS, rfl⟩
    have hmem : g * v * g⁻¹ ∈ (Q : Subgroup G) := by
      simpa [hcoe] using hmem'
    exact hmem⟩
  have hugAmbient : IsInvolution (g * u * g⁻¹) := by
    simpa [rightConjugateElem] using
      isInvolution_rightConjugateElem (g := g⁻¹) hu
  have hvgAmbient : IsInvolution (g * v * g⁻¹) := by
    simpa [rightConjugateElem] using
      isInvolution_rightConjugateElem (g := g⁻¹) hv
  have hug : IsInvolution ug := by
    constructor
    · intro h
      apply hugAmbient.1
      simpa [ug] using congrArg Subtype.val h
    · apply Subtype.ext
      simpa [ug] using hugAmbient.2
  have hvg : IsInvolution vg := by
    constructor
    · intro h
      apply hvgAmbient.1
      simpa [vg] using congrArg Subtype.val h
    · apply Subtype.ext
      simpa [vg] using hvgAmbient.2
  have heq : ug = vg := hunique ug vg hug hvg
  have hcoe' : g * u * g⁻¹ = g * v * g⁻¹ := congrArg Subtype.val heq
  simpa using (mul_left_cancel (mul_right_cancel hcoe'))

private lemma appendixII_quotient_sylow
    {G : Type u} [Group G] [Finite G]
    (Q : Sylow 2 G) {n : ℕ}
    (hQ : Nonempty (Q ≃* QuaternionGroup (2 ^ (n - 2)))) :
    ∃ Qbar : Sylow 2 (G ⧸ pPrimeCore 2 G),
      Nonempty (Qbar ≃* QuaternionGroup (2 ^ (n - 2))) := by
  classical
  let N : Subgroup G := pPrimeCore 2 G
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let Qbar : Sylow 2 (G ⧸ N) :=
    Q.mapSurjective (f := q) (QuotientGroup.mk'_surjective N)
  have hqinj : Function.Injective (q.comp (Q : Subgroup G).subtype) := by
    simpa [q, N] using
      quotient_pPrimeCore_subgroupMap_injective
        (G := G) (p := 2) (H := (Q : Subgroup G)) Q.isPGroup'
  let f : Q →* Qbar :=
    (q.comp (Q : Subgroup G).subtype).codRestrict Qbar (by
      intro x
      change q (x : G) ∈ (Qbar : Subgroup (G ⧸ N))
      rw [show (Qbar : Subgroup (G ⧸ N)) = (Q : Subgroup G).map q by
        simp [Qbar, Sylow.coe_mapSurjective]]
      exact Subgroup.mem_map_of_mem q x.2)
  have hfbij : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      exact congrArg Subtype.val (hqinj (congrArg Subtype.val hxy))
    · intro y
      have hy : (y : G ⧸ N) ∈ (Q : Subgroup G).map q := by
        have htemp : (Qbar : Subgroup (G ⧸ N)) = (Q : Subgroup G).map q := by
          simp [Qbar, Sylow.coe_mapSurjective]
        rw [← htemp]
        exact y.2
      rcases Subgroup.mem_map.mp hy with ⟨x, hx, hxy⟩
      refine ⟨⟨x, hx⟩, ?_⟩
      apply Subtype.ext
      exact hxy
  let eQbar : Q ≃* Qbar := MulEquiv.ofBijective f hfbij
  refine ⟨Qbar, ?_⟩
  exact ⟨eQbar.symm.trans (Classical.choice hQ)⟩

private lemma appendixII_quotient_involution_central
    {G : Type u} [Group G] [Finite G]
    (P : Sylow 2 G) {n : ℕ} (hn : 3 ≤ n)
    (hP : Nonempty (P ≃* QuaternionGroup (2 ^ (n - 2))))
    (u : G) (huI : IsInvolution u) :
    QuotientGroup.mk' (pPrimeCore 2 G) u ∈
      Subgroup.center (G ⧸ pPrimeCore 2 G) := by
  classical
  let N : Subgroup G := pPrimeCore 2 G
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  have hcenterEven :
      2 ∣ Nat.card (Subgroup.center (G ⧸ N)) := by
    simpa [N] using
      External.Suzuki.VI.suzuki_chapter6_section2_2_example3 P hn hP
  obtain ⟨Qbar, hQbar⟩ := appendixII_quotient_sylow P hP
  have huniqueQbar :=
    appendixII_sylow_involution_unique Qbar hQbar
  obtain ⟨z, hzorder⟩ :=
    exists_prime_orderOf_dvd_card'
      (G := Subgroup.center (G ⧸ N)) 2 hcenterEven
  have hzorderAmbient : orderOf (z : G ⧸ N) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact hzorder
  have hzI : IsInvolution (z : G ⧸ N) := by
    have hz := orderOf_eq_prime_iff.mp hzorderAmbient
    exact ⟨hz.2, by simpa [pow_two] using hz.1⟩
  have huP : IsPGroup 2 (Subgroup.zpowers u) :=
    appendixII_isPGroup_zpowers_of_involution huI
  have hqinj :
      Function.Injective
        (q.comp (Subgroup.zpowers u).subtype) := by
    simpa [q, N] using
      quotient_pPrimeCore_subgroupMap_injective
        (G := G) (p := 2) (H := Subgroup.zpowers u) huP
  let uz : Subgroup.zpowers u := ⟨u, Subgroup.mem_zpowers u⟩
  have huzOrder : orderOf uz = 2 := by
    rw [← Subgroup.orderOf_coe uz]
    simpa [uz] using orderOf_eq_prime huI.sq_eq_one huI.ne_one
  have hquOrder : orderOf (q u) = 2 := by
    have horder :=
      orderOf_injective
        (q.comp (Subgroup.zpowers u).subtype) hqinj uz
    simpa [uz] using horder.trans huzOrder
  have hquI : IsInvolution (q u) := by
    have h := orderOf_eq_prime_iff.mp hquOrder
    exact ⟨h.2, by simpa [pow_two] using h.1⟩
  have hcomm : Commute (z : G ⧸ N) (q u) := by
    rw [commute_iff_eq]
    exact (Subgroup.mem_center_iff.mp z.2 (q u)).symm
  have hzu : (z : G ⧸ N) = q u :=
    appendixII_commuting_involutions_eq Qbar huniqueQbar hzI hquI hcomm
  rw [← hzu]
  exact z.2

/-- An involution is central modulo the `2'`-core when a Sylow `2`-subgroup is
generalized quaternion. This is the quotient-centrality consequence of
Peterfalvi's Appendix II argument. -/
public theorem appendixII_quotient_involution_central_public
    {G : Type u} [Group G] [Finite G]
    (P : Sylow 2 G) {n : ℕ} (hn : 3 ≤ n)
    (hP : Nonempty (P ≃* QuaternionGroup (2 ^ (n - 2))))
    (u : G) (huI : IsInvolution u) :
    QuotientGroup.mk' (pPrimeCore 2 G) u ∈
      Subgroup.center (G ⧸ pPrimeCore 2 G) := by
  exact appendixII_quotient_involution_central P hn hP u huI

private lemma appendixII_factorization_of_quotient_involution_central
    {G : Type u} [Group G] [Finite G] (u : G) (huI : IsInvolution u)
    (hcentral :
      QuotientGroup.mk' (pPrimeCore 2 G) u ∈
        Subgroup.center (G ⧸ pPrimeCore 2 G)) :
    pPrimeCore 2 G ⊔ Subgroup.centralizer ({u} : Set G) = ⊤ := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup G := pPrimeCore 2 G
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let T : Subgroup G := Subgroup.zpowers u
  have hNnormal : N.Normal := by
    dsimp [N]
    exact pPrimeCore_normal
  letI : N.Normal := hNnormal
  have huOrder : orderOf u = 2 :=
    orderOf_eq_prime huI.sq_eq_one huI.ne_one
  have hTp : IsPGroup 2 T := by
    refine IsPGroup.of_card (p := 2) (G := T) (n := 1) ?_
    simp [T, Nat.card_zpowers, huOrder]
  letI : Fact (IsPGroup 2 T) := ⟨hTp⟩
  have hcop : Nat.Coprime 2 (Nat.card N) := by
    simpa [N] using (pPrimeCore_coprime_card (G := G) (p := 2))
  have hcent_eq :
      Subgroup.centralizer
          ((T.map q : Subgroup (G ⧸ N)) : Set (G ⧸ N)) =
        (Subgroup.centralizer (T : Set G)).map q := by
    simpa [q] using
      (centralizer_map_quotient_eq_map_centralizer
        (G := G) (p := 2) (T := T) (M := N) hNnormal hcop)
  have hquCenter' : q u ∈ Subgroup.center (G ⧸ N) := by
    simpa [q, N] using hcentral
  have hTmap : T.map q = Subgroup.zpowers (q u) :=
    MonoidHom.map_zpowers q u
  apply top_unique
  intro g _
  have hqgCent :
      q g ∈ Subgroup.centralizer
        ((T.map q : Subgroup (G ⧸ N)) : Set (G ⧸ N)) := by
    rw [hTmap, Subgroup.mem_centralizer_iff]
    intro y hy
    have hyCenter : y ∈ Subgroup.center (G ⧸ N) :=
      (Subgroup.zpowers_le.mpr hquCenter') hy
    exact (Subgroup.mem_center_iff.mp hyCenter (q g)).symm
  rw [hcent_eq] at hqgCent
  rcases Subgroup.mem_map.mp hqgCent with ⟨c, hc, hqc⟩
  have hgcN : g / c ∈ N := QuotientGroup.eq_iff_div_mem.mp hqc.symm
  have hcCu : c ∈ Subgroup.centralizer ({u} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact
      (Subgroup.mem_centralizer_iff.mp hc u
        (Subgroup.mem_zpowers u)).symm
  have hprod := Subgroup.mul_mem_sup hgcN hcCu
  simpa only [div_mul_cancel] using hprod

/-- In a finite group of 2-rank one, the odd core together with the
centralizer of any involution is the whole group. -/
public theorem pPrimeCore_sup_centralizer_eq_top_of_not_twoRank
    {G : Type u} [Group G] [Finite G]
    (h2rank : ¬ TwoRankAtLeastTwo G)
    {u : G} (hu : IsInvolution u) :
    pPrimeCore 2 G ⊔ Subgroup.centralizer ({u} : Set G) = ⊤ := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : IsPGroup 2 (Subgroup.zpowers u) :=
    appendixII_isPGroup_zpowers_of_involution hu
  obtain ⟨P, hTP⟩ := hT.exists_le_sylow
  have huP : u ∈ (P : Subgroup G) := hTP (Subgroup.mem_zpowers u)
  have hPne : (P : Subgroup G) ≠ ⊥ := by
    intro hPbot
    apply hu.ne_one
    exact Subgroup.mem_bot.mp (by simpa [hPbot] using huP)
  letI : Nontrivial P :=
    ⟨⟨⟨u, huP⟩, 1, by
      intro h
      exact hu.ne_one (congrArg Subtype.val h)⟩⟩
  have hPrank : ¬ TwoRankAtLeastTwo P := by
    intro hP
    rcases hP with ⟨E, hEcard, hEsq⟩
    let EG : Subgroup G := E.map (P : Subgroup G).subtype
    have hEGcard : Nat.card EG = 4 := by
      rw [Subgroup.card_map_of_injective (P : Subgroup G).subtype_injective]
      exact hEcard
    apply h2rank
    refine ⟨EG, hEGcard, ?_⟩
    rintro ⟨x, hx⟩
    rcases hx with ⟨y, hy, rfl⟩
    apply Subtype.ext
    exact congrArg (fun z : E => ((z : P) : G)) (hEsq ⟨y, hy⟩)
  obtain ⟨U, hUcard, hUunique⟩ :=
    unique_order_two_subgroup_of_not_twoRank P.isPGroup' hPrank
  have hclass :=
    (External.huppert_III_8_2_pgroup_unique_order_prime_subgroup
      Nat.prime_two P.isPGroup' ⟨U, hUcard, hUunique⟩).2 rfl
  rcases hclass with hPcyc | hPquat
  · exact proposition_1_factorization_of_cyclic_sylow_two P u hPcyc hu
  · rcases hPquat with ⟨n, hn, hQ⟩
    exact appendixII_factorization_of_quotient_involution_central u hu
      (appendixII_quotient_involution_central P hn hQ u hu)

private theorem proposition_1_exists_regular_elementaryAbelian_normal_of_solvable_normal
    {G : Type u} {Ω : Type v} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G) (hA1 : HypothesisA1 G Ω H D Q t)
    [FaithfulSMul G Ω] (N : Subgroup G) (hNnormal : N.Normal)
    (hN_ne_bot : N ≠ ⊥) (hNsolv : Group.IsSolvable N) :
    ∃ (F : Subgroup G) (p : ℕ), F.Normal ∧ p.Prime ∧
      IsElementaryAbelian p F ∧ F ≠ ⊥ ∧ MulAction.IsPretransitive F Ω ∧
      (∀ ω : Ω, MulAction.stabilizer F ω = ⊥) ∧ Disjoint F H ∧ F ⊔ H = ⊤ := by
  classical
  obtain ⟨F, hFnorm, hF_le_N, hF_ne_bot, hFmin⟩ :=
    exists_minimal_normal_le (G := G) N hNnormal hN_ne_bot
  letI : F.Normal := hFnorm
  letI : IsMinimalNormal F := {
    minimal := by
      intro K hKnormal hKle
      by_cases hKbot : K = ⊥
      · exact Or.inl hKbot
      · exact Or.inr (hFmin K hKnormal hKle hKbot)
  }
  let FN : Subgroup N := F.subgroupOf N
  let eFN : FN ≃* F := Subgroup.subgroupOfEquivOfLe hF_le_N
  letI : Group.IsSolvable N := hNsolv
  have hFNsolv : Group.IsSolvable FN := inferInstance
  letI : Group.IsSolvable FN := hFNsolv
  have hFsolv : Group.IsSolvable F :=
    Group.isSolvable_of_surjective (f := eFN.toMonoidHom) eFN.surjective
  letI : Group.IsSolvable F := hFsolv
  obtain ⟨p, hp, hFelem⟩ := minimalNormal_solvable_exists_isElementaryAbelian F
  letI : IsElementaryAbelian p F := hFelem
  letI : MulAction.IsPreprimitive G Ω :=
    MulAction.isPreprimitive_of_is_two_pretransitive hA1.two_transitive
  letI : MulAction.IsQuasiPreprimitive G Ω :=
    MulAction.IsPreprimitive.isQuasiPreprimitive
  have hfixed_ne_univ : MulAction.fixedPoints F Ω ≠ Set.univ := by
    intro hfixed
    apply hF_ne_bot
    rw [eq_bot_iff]
    intro f hf
    have hfix_all : ∀ ω : Ω, f • ω = ω := by
      intro ω
      have hω : ω ∈ MulAction.fixedPoints F Ω := by rw [hfixed]; trivial
      exact MulAction.mem_fixedPoints.mp hω ⟨f, hf⟩
    have hf_one : f = 1 :=
      FaithfulSMul.eq_of_smul_eq_smul (m₁ := f) (m₂ := (1 : G)) (by
        intro ω
        calc
          f • ω = ω := hfix_all ω
          _ = (1 : G) • ω := (one_smul G ω).symm)
    exact Subgroup.mem_bot.mpr hf_one
  have hFtrans : MulAction.IsPretransitive F Ω :=
    MulAction.IsQuasiPreprimitive.isPretransitive_of_normal hfixed_ne_univ
  letI : MulAction.IsPretransitive F Ω := hFtrans
  have hFregular : ∀ ω : Ω, MulAction.stabilizer F ω = ⊥ := by
    intro ω
    rw [eq_bot_iff]
    intro f hf
    have hfix_all : ∀ η : Ω, f • η = η := by
      intro η
      obtain ⟨a, ha⟩ :=
        @MulAction.IsPretransitive.exists_smul_eq F Ω inferInstance inferInstance ω η
      have hcomm : f * a = a * f :=
        Std.Commutative.comm f a
      calc
        f • η = f • (a • ω) := by rw [ha]
        _ = (f * a) • ω := by rw [mul_smul]
        _ = (a * f) • ω := by rw [hcomm]
        _ = a • (f • ω) := by rw [mul_smul]
        _ = a • ω := by rw [show f • ω = ω from hf]
        _ = η := ha
    have hf_one_G : (f : G) = 1 :=
      FaithfulSMul.eq_of_smul_eq_smul (m₁ := (f : G)) (m₂ := (1 : G)) (by
        intro η
        calc
          (f : G) • η = η := hfix_all η
          _ = (1 : G) • η := (one_smul G η).symm)
    apply Subgroup.mem_bot.mpr
    exact Subtype.ext hf_one_G
  obtain ⟨base, hHbase⟩ := hA1.point_stabilizer
  have hdis : Disjoint F H := by
    rw [disjoint_iff, eq_bot_iff]
    intro g hg
    have hg_stab_G : g ∈ MulAction.stabilizer G base := by simpa [← hHbase] using hg.2
    have hg_stab_F : (⟨g, hg.1⟩ : F) ∈ MulAction.stabilizer F base := by
      simpa using hg_stab_G
    rw [hFregular base] at hg_stab_F
    have hg_one_F : (⟨g, hg.1⟩ : F) = 1 := Subgroup.mem_bot.mp hg_stab_F
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hg_one_F)
  have hsup : F ⊔ H = ⊤ := by
    rw [eq_top_iff]
    intro g _hg
    obtain ⟨f, hf⟩ :=
      @MulAction.IsPretransitive.exists_smul_eq F Ω inferInstance inferInstance base (g • base)
    have hfg_stab : (f : G)⁻¹ * g ∈ MulAction.stabilizer G base := by
      change ((f : G)⁻¹ * g) • base = base
      rw [mul_smul, inv_smul_eq_iff]
      exact hf.symm
    have hfg_H : (f : G)⁻¹ * g ∈ H := by simpa [hHbase] using hfg_stab
    have hprod : (f : G) * ((f : G)⁻¹ * g) ∈ F ⊔ H :=
      Subgroup.mul_mem_sup f.property hfg_H
    simpa using hprod
  exact ⟨F, p, hFnorm, hp, hFelem, hF_ne_bot, hFtrans, hFregular, hdis, hsup⟩

private theorem proposition_1_centralizer_involution_le_H
    {G : Type u} {Ω : Type v} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t u : G) (hA1 : HypothesisA1 G Ω H D Q t)
    (huH : u ∈ H) (huI : IsInvolution u) :
    Subgroup.centralizer ({u} : Set G) ≤ H := by
  classical
  have huQ : u ∈ Q := involution_mem_Q_of_mem_H H D Q t hA1 u huH huI
  have hzp_ne : Subgroup.zpowers u ≠ (⊥ : Subgroup G) := by
    intro hbot
    have hu_bot : u ∈ (⊥ : Subgroup G) := by rw [← hbot]; exact Subgroup.mem_zpowers u
    exact huI.ne_one (Subgroup.mem_bot.mp hu_bot)
  have hzp_le_Q : Subgroup.zpowers u ≤ Q := Subgroup.zpowers_le.mpr huQ
  intro x hx
  apply (proposition_1_b H D Q t hA1 (Subgroup.zpowers u) hzp_ne hzp_le_Q)
  apply centralizer_le_normalizer (Subgroup.zpowers u)
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, rfl⟩
  exact (((commute_iff_eq x u).mpr (Subgroup.mem_centralizer_singleton_iff.mp hx)).zpow_right n).eq.symm

private theorem proposition_1_exists_regular_elementaryAbelian_normal_of_factorization
    {G : Type u} {Ω : Type v} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t u : G) (hA1 : HypothesisA1 G Ω H D Q t)
    [FaithfulSMul G Ω] (huH : u ∈ H) (huI : IsInvolution u)
    (hfactor : pPrimeCore 2 G ⊔ Subgroup.centralizer ({u} : Set G) = ⊤) :
    ∃ (F : Subgroup G) (p : ℕ), F.Normal ∧ p.Prime ∧
      IsElementaryAbelian p F ∧ F ≠ ⊥ ∧ MulAction.IsPretransitive F Ω ∧
      (∀ ω : Ω, MulAction.stabilizer F ω = ⊥) ∧ Disjoint F H ∧ F ⊔ H = ⊤ := by
  let N : Subgroup G := pPrimeCore 2 G
  have hNnormal : N.Normal := by dsimp [N]; exact pPrimeCore_normal
  have hcent_le_H : Subgroup.centralizer ({u} : Set G) ≤ H :=
    proposition_1_centralizer_involution_le_H H D Q t u hA1 huH huI
  have hN_ne_bot : N ≠ ⊥ := by
    intro hNbot
    have hcent_top : Subgroup.centralizer ({u} : Set G) = ⊤ := by
      simpa [N, hNbot] using hfactor
    have htop_le_H : (⊤ : Subgroup G) ≤ H := by simpa [hcent_top] using hcent_le_H
    have hHtop : H = ⊤ := top_unique htop_le_H
    exact hA1.t_not_mem_H (by simp [hHtop])
  have hNodd : Odd (Nat.card N) := by
    exact Nat.coprime_two_left.mp (by simpa [N] using pPrimeCore_coprime_card (p := 2) (G := G))
  have hNsolv : Group.IsSolvable N := odd_order_theorem N hNodd
  exact proposition_1_exists_regular_elementaryAbelian_normal_of_solvable_normal
    H D Q t hA1 N hNnormal hN_ne_bot hNsolv

private theorem proposition_1_exists_regular_elementaryAbelian_normal
    {G : Type u} {Ω : Type v} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G) (hA1 : HypothesisA1 G Ω H D Q t)
    [FaithfulSMul G Ω] (h2rank : ¬ TwoRankAtLeastTwo G) :
    ∃ (F : Subgroup G) (p : ℕ), F.Normal ∧ p.Prime ∧
      IsElementaryAbelian p F ∧ F ≠ ⊥ ∧ MulAction.IsPretransitive F Ω ∧
      (∀ ω : Ω, MulAction.stabilizer F ω = ⊥) ∧ Disjoint F H ∧ F ⊔ H = ⊤ := by
  obtain ⟨P, _hP_le_Q, hPclass⟩ :=
    proposition_1_sylow_two_cyclic_or_generalizedQuaternion H D Q t hA1 h2rank
  obtain ⟨pair, hpair, _hpair_unique⟩ := proposition_4_b H D Q t hA1
  let u : G := pair.1
  have huH : u ∈ H := hpair.1
  have huI : IsInvolution u := hpair.2.1
  have hBSQuaternion :
      (∃ n : ℕ, 3 ≤ n ∧ Nonempty (P ≃* QuaternionGroup (2 ^ (n - 2)))) →
      pPrimeCore 2 G ⊔ Subgroup.centralizer ({u} : Set G) = ⊤ := by
    rintro ⟨n, hn, hP⟩
    exact appendixII_factorization_of_quotient_involution_central u huI
      (appendixII_quotient_involution_central P hn hP u huI)
  have hfactor :
      pPrimeCore 2 G ⊔ Subgroup.centralizer ({u} : Set G) = ⊤ :=
    hPclass.elim
      (fun hPcyc => proposition_1_factorization_of_cyclic_sylow_two P u hPcyc huI)
      hBSQuaternion
  exact proposition_1_exists_regular_elementaryAbelian_normal_of_factorization
    H D Q t u hA1 huH huI hfactor

/-- The explicit meaning of the semilinear decomposition in Appendix II,
Proposition 1. The three maps give the additive, unit, and automorphism factors.
The last two clauses are the two involution conclusions printed in the source. -/
@[expose] public def PropositionOneConclusion
    {G : Type u} [Group G] (H D Q : Subgroup G)
    (F : Type v) [RightNearField F] : Prop :=
  ∃ (addLift : F → G) (unitLift : Fˣ → G) (sigmaAct : D → F → F),
    Function.Bijective
        (fun x : F × Fˣ × D => addLift x.1 * unitLift x.2.1 * (x.2.2 : G)) ∧
      addLift 0 = 1 ∧
      (∀ a b : F, addLift (a + b) = addLift a * addLift b) ∧
      unitLift 1 = 1 ∧
      (∀ x y : Fˣ, unitLift (x * y) = unitLift x * unitLift y) ∧
      (∀ q : G, q ∈ Q ↔ ∃ x : Fˣ, unitLift x = q) ∧
      (∀ a : F, ∀ x : Fˣ,
        rightConjugateElem (addLift a) (unitLift x) =
          addLift (a * (x : F))) ∧
      (∀ d : D, ∀ a b : F,
        sigmaAct d (a + b) = sigmaAct d a + sigmaAct d b ∧
        sigmaAct d (a * b) = sigmaAct d a * sigmaAct d b ∧
        sigmaAct d 1 = 1) ∧
      (∀ a : F, sigmaAct 1 a = a) ∧
      (∀ d e : D, ∀ a : F,
        sigmaAct (d * e) a = sigmaAct e (sigmaAct d a)) ∧
      Function.Injective sigmaAct ∧
      (∀ d : D, ∀ a : F,
        rightConjugateElem (addLift a) (d : G) =
          addLift (sigmaAct d a)) ∧
      (∃! h : H, IsInvolution (h : G)) ∧
      ∀ s t : G, IsInvolution s → IsInvolution t → s ≠ t →
        orderOf (s * t) = addOrderOf (1 : F)

/-- The product of any two distinct involutions in a Proposition-One model
has order equal to the additive order of one in its near-field. -/
public theorem PropositionOneConclusion.involutionProductOrder
    {G : Type u} [Group G] (H D Q : Subgroup G)
    {F : Type v} [RightNearField F]
    (hPO : PropositionOneConclusion H D Q F)
    {s t : G} (hs : IsInvolution s) (ht : IsInvolution t) (hst : s ≠ t) :
    orderOf (s * t) = addOrderOf (1 : F) := by
  rcases hPO with
    ⟨_addLift, _unitLift, _sigmaAct, _hcoordinates, _hadd_zero, _hadd,
      _hunit_one, _hunit_mul, _hunit_range, _hright, _hsigma_maps,
      _hsigma_one, _hsigma_mul, _hsigma_injective, _hright_sigma,
      _hinvolution_unique, hinvolution_order⟩
  exact hinvolution_order s t hs ht hst

/-- The unit coordinate of a fixed Proposition-One near-field model identifies
its multiplicative group with the `Q` factor. -/
public theorem propositionOneConclusion_unitsEquiv
    {G : Type u} [Group G] (H D Q : Subgroup G)
    {F : Type v} [RightNearField F]
    (hPO : PropositionOneConclusion H D Q F) :
    Nonempty (Fˣ ≃* Q) := by
  classical
  rcases hPO with
    ⟨addLift, unitLift, sigmaAct, hcoordinates, hadd_zero, _hadd,
      hunit_one, hunit_mul, hunit_range, _hright, _hsigma_maps,
      _hsigma_one, _hsigma_mul, _hsigma_injective, _hright_sigma,
      _hinvolution_unique, _hinvolution_order⟩
  let unitHom : Fˣ →* G :=
    { toFun := unitLift
      map_one' := hunit_one
      map_mul' := hunit_mul }
  have hunit_mem (x : Fˣ) : unitHom x ∈ Q := by
    exact (hunit_range (unitHom x)).2 ⟨x, rfl⟩
  let unitHomQ : Fˣ →* Q := unitHom.codRestrict Q hunit_mem
  have hunit_injective : Function.Injective unitHomQ := by
    intro x y hxy
    have hxyG : unitLift x = unitLift y := by
      simpa [unitHomQ, unitHom] using congrArg Subtype.val hxy
    let tx : F × Fˣ × D := (0, x, 1)
    let ty : F × Fˣ × D := (0, y, 1)
    have htriple : tx = ty := hcoordinates.1 (by
      simpa [tx, ty, hadd_zero] using hxyG)
    exact congrArg (fun z : F × Fˣ × D => z.2.1) htriple
  have hunit_surjective : Function.Surjective unitHomQ := by
    intro q
    rcases (hunit_range (q : G)).1 q.property with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    simpa [unitHomQ, unitHom] using hx
  exact ⟨MulEquiv.ofBijective unitHomQ ⟨hunit_injective, hunit_surjective⟩⟩

/-- Peterfalvi, Appendix II, Proposition 1.

Under (A1), faithfulness (A2), and 2-rank one, the doubly transitive group is a
finite semilinear affine group over a near-field. -/
public theorem proposition_1
    {G : Type u} {Ω : Type v} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) [FaithfulSMul G Ω]
    (h2rank : ¬ TwoRankAtLeastTwo G) :
    ∃ (F : Type v) (_ : RightNearField F) (_ : Finite F) (_ : Nontrivial F),
      PropositionOneConclusion H D Q F := by
  obtain ⟨F, p, hFnorm, hp, hFelem, hF_ne_bot, hFtrans, hFregular, hFdisH, hFsupH⟩ :=
    proposition_1_exists_regular_elementaryAbelian_normal H D Q t hA1 h2rank
  classical
  letI : F.Normal := hFnorm
  letI : IsElementaryAbelian p F := hFelem
  letI : IsMulCommutative F := hFelem.toIsMulCommutative
  letI : CommGroup F :=
    { mul_comm := hFelem.toIsMulCommutative.is_comm.comm }
  letI : Nontrivial F := (Subgroup.nontrivial_iff_ne_bot F).2 hF_ne_bot
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨base, hHbase⟩ := hA1.point_stabilizer
  subst H
  let beta : Ω := t⁻¹ • base
  have hbeta_ne : beta ≠ base := by
    intro hbeta
    apply hA1.t_not_mem_H
    change t • base = base
    have htinv : t⁻¹ = t := hA1.involution_t.inv_eq_self
    simpa [beta, htinv] using hbeta
  have hD :
      D = MulAction.stabilizer G base ⊓ MulAction.stabilizer G beta := by
    dsimp [beta]
    simpa [rightConjugate_stabilizer] using hA1.D_eq
  have hQreg := hypothesisA1_Q_regular_on_complement hA1 hbeta_ne hD
  let qPointEquiv : Q ≃ {omega : Ω // omega ≠ base} :=
    (Equiv.Set.univ Q).symm.trans
      (Set.BijOn.equiv (fun q : Q => (q : G) • beta) hQreg)
  let invEquiv : Q ≃ Q :=
    Equiv.inv Q
  let qEquiv : Q ≃ {omega : Ω // omega ≠ base} :=
    invEquiv.trans qPointEquiv
  have hqEquiv_apply (q : Q) :
      (qEquiv q : Ω) = (q : G)⁻¹ • beta := by
    rfl
  letI : MulAction.IsPretransitive F Ω := hFtrans
  letI : IsCancelSMul F Ω :=
    isCancelSMul_iff_stabilizer_eq_bot.mpr hFregular
  let orbitEquiv : F ≃ Ω :=
    Equiv.ofBijective (fun f : F => f • base)
      ⟨fun _ _ => IsCancelSMul.right_cancel _ _ base,
        MulAction.surjective_smul F base⟩
  let addCoord : Ω ≃ Additive F := orbitEquiv.symm.trans Additive.ofMul
  letI : AddCommGroup Ω := addCoord.addCommGroup
  have hzero_eq_base : (0 : Ω) = base := by
    calc
      (0 : Ω) = addCoord.symm (0 : Additive F) := rfl
      _ = orbitEquiv (1 : F) := by simp [addCoord, orbitEquiv]
      _ = base := by
        change (1 : F) • base = base
        simp
  let withZeroEquiv : WithZero Q ≃ Ω :=
    (Equiv.optionCongr qEquiv).trans (Equiv.optionSubtypeNe base)
  let mulCoord : Ω ≃ WithZero Q := withZeroEquiv.symm
  have hmulCoord_zero : mulCoord 0 = 0 := by
    rw [hzero_eq_base]
    change withZeroEquiv.symm base = (0 : WithZero Q)
    rw [Equiv.symm_apply_eq]
    change base = (Equiv.optionSubtypeNe base)
      ((Equiv.optionCongr qEquiv) (none : Option Q))
    rw [Equiv.optionCongr_apply]
    rfl
  letI : One Ω := mulCoord.one
  letI : Mul Ω := mulCoord.mul
  letI : Inv Ω := mulCoord.Inv
  letI : Div Ω := mulCoord.div
  letI : Pow Ω ℕ := mulCoord.pow ℕ
  letI : Pow Ω ℤ := mulCoord.pow ℤ
  letI : GroupWithZero Ω := mulCoord.injective.groupWithZero mulCoord hmulCoord_zero
    (by simp [Equiv.one_def])
    (by intro x y; simp [Equiv.mul_def])
    (by intro x; simp [Equiv.inv_def])
    (by intro x y; simp [Equiv.div_def])
    (by intro x n; simp [Equiv.pow_def])
    (by intro x n; simp [Equiv.pow_def])
  have hmulCoord_q (x : Q) :
      mulCoord (qEquiv x : Ω) = (x : WithZero Q) := by
    change withZeroEquiv.symm (qEquiv x : Ω) = (x : WithZero Q)
    rw [Equiv.symm_apply_eq]
    change (qEquiv x : Ω) = (Equiv.optionSubtypeNe base)
      ((Equiv.optionCongr qEquiv) (some x))
    rw [Equiv.optionCongr_apply]
    rfl
  have hmul_right (a : Ω) (q : Q) :
      a * (qEquiv q : Ω) = (q : G)⁻¹ • a := by
    by_cases ha : a = 0
    · rw [ha, zero_mul, hzero_eq_base]
      have hqH : (q : G) ∈ MulAction.stabilizer G base := hA1.Q_le_H q.property
      exact ((MulAction.stabilizer G base).inv_mem hqH).symm
    · let r : Q := qEquiv.symm ⟨a, by simpa [hzero_eq_base] using ha⟩
      have ha_eq : a = (qEquiv r : Ω) := by
        exact congrArg Subtype.val
          (qEquiv.apply_symm_apply ⟨a, by simpa [hzero_eq_base] using ha⟩).symm
      rw [ha_eq]
      have htarget :
          (q : G)⁻¹ • (qEquiv r : Ω) = (qEquiv (r * q) : Ω) := by
        rw [hqEquiv_apply, hqEquiv_apply]
        simp [smul_smul]
      rw [htarget]
      apply mulCoord.injective
      rw [Equiv.mul_def, hmulCoord_q, hmulCoord_q, hmulCoord_q]
      simp
  have horbit_add (a b : Ω) :
      orbitEquiv.symm (a + b) = orbitEquiv.symm a * orbitEquiv.symm b := by
    calc
      orbitEquiv.symm (a + b) =
          orbitEquiv.symm (addCoord.symm (addCoord a + addCoord b)) := rfl
      _ = Additive.ofMul.symm (addCoord a + addCoord b) := by
        simp [addCoord, orbitEquiv]
      _ = Additive.ofMul.symm (Additive.ofMul (orbitEquiv.symm a) +
          Additive.ofMul (orbitEquiv.symm b)) := by simp [addCoord, orbitEquiv]
      _ = Additive.ofMul.symm
          (Additive.ofMul (orbitEquiv.symm a * orbitEquiv.symm b)) := by simp
      _ = orbitEquiv.symm a * orbitEquiv.symm b := by simp
  have hcoord_smul (q : Q) (a : Ω) :
      orbitEquiv.symm ((q : G)⁻¹ • a) =
        MulAut.conjNormal (H := F) (q : G)⁻¹ (orbitEquiv.symm a) := by
    apply orbitEquiv.injective
    rw [orbitEquiv.apply_symm_apply]
    have hqbase : (q : G) • base = base :=
      hA1.Q_le_H q.property
    have ha_orbit : (orbitEquiv.symm a : F) • base = a := by
      change orbitEquiv (orbitEquiv.symm a) = a
      exact orbitEquiv.apply_symm_apply a
    have hconj_val :
        ((MulAut.conjNormal (H := F) (q : G)⁻¹
          (orbitEquiv.symm a) : F) : G) =
          (q : G)⁻¹ * (orbitEquiv.symm a : G) * (q : G) :=
      (MulAut.conjNormal_symm_apply (H := F) (q : G) (orbitEquiv.symm a))
    calc
      (q : G)⁻¹ • a =
          (q : G)⁻¹ • ((orbitEquiv.symm a : F) • base) := by rw [ha_orbit]
      _ = (q : G)⁻¹ • ((orbitEquiv.symm a : G) • base) := by
            rw [Subgroup.smul_def]
      _ = ((q : G)⁻¹ * (orbitEquiv.symm a : G)) • base := by rw [mul_smul]
      _ = ((q : G)⁻¹ * (orbitEquiv.symm a : G)) • ((q : G) • base) := by
            rw [hqbase]
      _ = ((q : G)⁻¹ * (orbitEquiv.symm a : G) * (q : G)) • base :=
            (mul_smul _ _ _).symm
      _ = ((MulAut.conjNormal (H := F) (q : G)⁻¹
            (orbitEquiv.symm a) : F) : G) • base := by rw [hconj_val]
      _ = (MulAut.conjNormal (H := F) (q : G)⁻¹
            (orbitEquiv.symm a) : F) • base := by rw [Subgroup.smul_def]
  have hsmul_add (q : Q) (a b : Ω) :
      (q : G)⁻¹ • (a + b) = (q : G)⁻¹ • a + (q : G)⁻¹ • b := by
    apply orbitEquiv.symm.injective
    rw [hcoord_smul, horbit_add, horbit_add, hcoord_smul, hcoord_smul]
    exact (MulAut.conjNormal (H := F) (q : G)⁻¹).map_mul _ _
  let hNF : RightNearField Ω :=
    { (inferInstance : AddCommGroup Ω), (inferInstance : GroupWithZero Ω) with
      right_distrib := by
        intro a b c
        by_cases hc : c = 0
        · simp [hc]
        · let q : Q := qEquiv.symm ⟨c, by simpa [hzero_eq_base] using hc⟩
          have hc_eq : c = (qEquiv q : Ω) := by
            exact congrArg Subtype.val
              (qEquiv.apply_symm_apply ⟨c, by simpa [hzero_eq_base] using hc⟩).symm
          rw [hc_eq, hmul_right, hmul_right, hmul_right]
          exact hsmul_add q a b
    }
  letI : RightNearField Ω := hNF
  let addLift : Ω → G := fun a => (orbitEquiv.symm a : G)
  let mulEquiv : Ω ≃* WithZero Q := mulCoord.mulEquiv
  let unitCoord : Ωˣ ≃* Q :=
    (Units.mapEquiv mulEquiv).trans WithZero.unitsWithZeroEquiv
  let unitLift : Ωˣ → G := fun x => (unitCoord x : G)
  have hunitCoord_val (x : Ωˣ) :
      mulCoord (x : Ω) = ((unitCoord x : Q) : WithZero Q) := by
    change mulCoord (x : Ω) =
      ((WithZero.unitsWithZeroEquiv ((Units.mapEquiv mulEquiv) x) : Q) : WithZero Q)
    rw [WithZero.coe_unitsWithZeroEquiv_eq_units_val, Units.coe_mapEquiv]
    rfl
  have hunit_val (x : Ωˣ) :
      (x : Ω) = (qEquiv (unitCoord x) : Ω) := by
    apply mulCoord.injective
    rw [hunitCoord_val, hmulCoord_q]
  have hqEquiv_mul (r q : Q) :
      (qEquiv r : Ω) * (qEquiv q : Ω) = (qEquiv (r * q) : Ω) := by
    apply mulCoord.injective
    rw [Equiv.mul_def, hmulCoord_q, hmulCoord_q, hmulCoord_q]
    simp
  have hone_eq_beta : (1 : Ω) = beta := by
    have hone_q : (1 : Ω) = (qEquiv (1 : Q) : Ω) := by
      apply mulCoord.injective
      rw [Equiv.one_def, hmulCoord_q]
      simp
    rw [hone_q, hqEquiv_apply]
    simp
  have hd_base (d : D) : (d : G) • base = base :=
    hA1.D_le_H d.property
  have hd_beta (d : D) : (d : G) • beta = beta := by
    have hd :
        (d : G) ∈ MulAction.stabilizer G base ⊓ MulAction.stabilizer G beta := by
      rw [← hD]
      exact d.property
    exact hd.2
  have hcoord_smul_D (d : D) (a : Ω) :
      orbitEquiv.symm ((d : G)⁻¹ • a) =
        MulAut.conjNormal (H := F) (d : G)⁻¹ (orbitEquiv.symm a) := by
    apply orbitEquiv.injective
    rw [orbitEquiv.apply_symm_apply]
    have ha_orbit : (orbitEquiv.symm a : F) • base = a := by
      change orbitEquiv (orbitEquiv.symm a) = a
      exact orbitEquiv.apply_symm_apply a
    have hconj_val :
        ((MulAut.conjNormal (H := F) (d : G)⁻¹
          (orbitEquiv.symm a) : F) : G) =
          (d : G)⁻¹ * (orbitEquiv.symm a : G) * (d : G) :=
      (MulAut.conjNormal_symm_apply (H := F) (d : G) (orbitEquiv.symm a))
    calc
      (d : G)⁻¹ • a =
          (d : G)⁻¹ • ((orbitEquiv.symm a : F) • base) := by rw [ha_orbit]
      _ = (d : G)⁻¹ • ((orbitEquiv.symm a : G) • base) := by
            rw [Subgroup.smul_def]
      _ = ((d : G)⁻¹ * (orbitEquiv.symm a : G)) • base := by rw [mul_smul]
      _ = ((d : G)⁻¹ * (orbitEquiv.symm a : G)) • ((d : G) • base) := by
            rw [hd_base]
      _ = ((d : G)⁻¹ * (orbitEquiv.symm a : G) * (d : G)) • base :=
            (mul_smul _ _ _).symm
      _ = ((MulAut.conjNormal (H := F) (d : G)⁻¹
            (orbitEquiv.symm a) : F) : G) • base := by rw [hconj_val]
      _ = (MulAut.conjNormal (H := F) (d : G)⁻¹
            (orbitEquiv.symm a) : F) • base := by rw [Subgroup.smul_def]
  have hsmul_add_D (d : D) (a b : Ω) :
      (d : G)⁻¹ • (a + b) = (d : G)⁻¹ • a + (d : G)⁻¹ • b := by
    apply orbitEquiv.symm.injective
    rw [hcoord_smul_D, horbit_add, horbit_add, hcoord_smul_D, hcoord_smul_D]
    exact (MulAut.conjNormal (H := F) (d : G)⁻¹).map_mul _ _
  let dConjQ (d : D) (q : Q) : Q :=
    ⟨(d : G)⁻¹ * (q : G) * (d : G), by
      let dH : MulAction.stabilizer G base :=
        ⟨(d : G), hA1.D_le_H d.property⟩
      let qH : MulAction.stabilizer G base :=
        ⟨(q : G), hA1.Q_le_H q.property⟩
      have hqSub : qH ∈ Q.subgroupOf (MulAction.stabilizer G base) := q.property
      have hmem :=
        hA1.Q_normal_in_H.conj_mem qH hqSub dH⁻¹
      have hmem' : (d : G)⁻¹ * (q : G) * (d : G) ∈ Q := by
        have htemp := Subgroup.mem_subgroupOf.mp hmem
        simpa [dH, qH] using htemp
      exact hmem'⟩
  have dConjQ_mul (d : D) (q r : Q) :
      dConjQ d (q * r) = dConjQ d q * dConjQ d r := by
    apply Subtype.ext
    dsimp [dConjQ]
    group
  have hsigma_qEquiv (d : D) (q : Q) :
      (d : G)⁻¹ • (qEquiv q : Ω) = (qEquiv (dConjQ d q) : Ω) := by
    rw [hqEquiv_apply, hqEquiv_apply]
    have hconj_inv :
        ((dConjQ d q : Q) : G)⁻¹ =
          (d : G)⁻¹ * (q : G)⁻¹ * (d : G) := by
      dsimp [dConjQ]
      group
    rw [hconj_inv, mul_smul, mul_smul, hd_beta]
  have hsmul_mul_D (d : D) (a b : Ω) :
      (d : G)⁻¹ • (a * b) = ((d : G)⁻¹ • a) * ((d : G)⁻¹ • b) := by
    by_cases ha : a = 0
    · rw [ha]
      have hdInvBase : (d : G)⁻¹ • base = base :=
        ((MulAction.stabilizer G base).inv_mem (hA1.D_le_H d.property))
      calc
        (d : G)⁻¹ • (0 * b) = (d : G)⁻¹ • 0 := by rw [zero_mul]
        _ = 0 := by rw [hzero_eq_base]; exact hdInvBase
        _ = ((d : G)⁻¹ • 0) * ((d : G)⁻¹ • b) := by
          rw [hzero_eq_base, hdInvBase, ← hzero_eq_base, zero_mul]
    · by_cases hb : b = 0
      · rw [hb]
        have hdInvBase : (d : G)⁻¹ • base = base :=
          ((MulAction.stabilizer G base).inv_mem (hA1.D_le_H d.property))
        calc
          (d : G)⁻¹ • (a * 0) = (d : G)⁻¹ • 0 := by rw [mul_zero]
          _ = 0 := by rw [hzero_eq_base]; exact hdInvBase
          _ = ((d : G)⁻¹ • a) * ((d : G)⁻¹ • 0) := by
            rw [hzero_eq_base, hdInvBase, ← hzero_eq_base, mul_zero]
      · let q : Q := qEquiv.symm ⟨a, by simpa [hzero_eq_base] using ha⟩
        let r : Q := qEquiv.symm ⟨b, by simpa [hzero_eq_base] using hb⟩
        have ha_eq : a = (qEquiv q : Ω) := by
          exact congrArg Subtype.val
            (qEquiv.apply_symm_apply ⟨a, by simpa [hzero_eq_base] using ha⟩).symm
        have hb_eq : b = (qEquiv r : Ω) := by
          exact congrArg Subtype.val
            (qEquiv.apply_symm_apply ⟨b, by simpa [hzero_eq_base] using hb⟩).symm
        rw [ha_eq, hb_eq, hqEquiv_mul, hsigma_qEquiv, hsigma_qEquiv,
          hsigma_qEquiv, hqEquiv_mul, dConjQ_mul]
  let sigmaAct : D → Ω → Ω := fun d a => (d : G)⁻¹ • a
  have haddLift_zero : addLift 0 = 1 := by
    change ((orbitEquiv.symm 0 : F) : G) = ((1 : F) : G)
    apply congrArg (fun f : F => (f : G))
    apply orbitEquiv.injective
    rw [orbitEquiv.apply_symm_apply, hzero_eq_base]
    change base = (1 : F) • base
    simp
  have haddLift_add (a b : Ω) : addLift (a + b) = addLift a * addLift b := by
    change ((orbitEquiv.symm (a + b) : F) : G) =
      ((orbitEquiv.symm a : F) : G) * ((orbitEquiv.symm b : F) : G)
    rw [← Subgroup.coe_mul]
    exact congrArg (fun f : F => (f : G)) (horbit_add a b)
  have hunitLift_one : unitLift 1 = 1 := by
    change ((unitCoord 1 : Q) : G) = ((1 : Q) : G)
    rw [map_one]
  have hunitLift_mul (x y : Ωˣ) : unitLift (x * y) = unitLift x * unitLift y := by
    change ((unitCoord (x * y) : Q) : G) =
      ((unitCoord x : Q) : G) * ((unitCoord y : Q) : G)
    rw [map_mul, Subgroup.coe_mul]
  have hunitLift_range (q : G) : q ∈ Q ↔ ∃ x : Ωˣ, unitLift x = q := by
    constructor
    · intro hq
      let qQ : Q := ⟨q, hq⟩
      obtain ⟨x, hx⟩ := unitCoord.surjective qQ
      refine ⟨x, ?_⟩
      change ((unitCoord x : Q) : G) = q
      simpa [qQ] using congrArg (fun z : Q => (z : G)) hx
    · rintro ⟨x, rfl⟩
      exact (unitCoord x).property
  have hrightQ (a : Ω) (x : Ωˣ) :
      rightConjugateElem (addLift a) (unitLift x) =
        addLift (a * (x : Ω)) := by
    let q : Q := unitCoord x
    change (q : G)⁻¹ * (orbitEquiv.symm a : G) * (q : G) =
      (orbitEquiv.symm (a * (x : Ω)) : G)
    calc
      (q : G)⁻¹ * (orbitEquiv.symm a : G) * (q : G) =
          ((MulAut.conjNormal (H := F) (q : G)⁻¹
            (orbitEquiv.symm a) : F) : G) := by
            exact (MulAut.conjNormal_symm_apply (H := F) (q : G)
              (orbitEquiv.symm a)).symm
      _ = (orbitEquiv.symm ((q : G)⁻¹ • a) : G) :=
        congrArg (fun f : F => (f : G)) (hcoord_smul q a).symm
      _ = (orbitEquiv.symm (a * (x : Ω)) : G) := by
        rw [hunit_val x, hmul_right]
  have hsigma_struct (d : D) (a b : Ω) :
      sigmaAct d (a + b) = sigmaAct d a + sigmaAct d b ∧
      sigmaAct d (a * b) = sigmaAct d a * sigmaAct d b ∧
      sigmaAct d 1 = 1 := by
    refine ⟨hsmul_add_D d a b, hsmul_mul_D d a b, ?_⟩
    change (d : G)⁻¹ • (1 : Ω) = 1
    rw [hone_eq_beta]
    calc
      (d : G)⁻¹ • beta = (d : G)⁻¹ • ((d : G) • beta) := by rw [hd_beta]
      _ = beta := by simp [smul_smul]
  have hsigma_one (a : Ω) : sigmaAct 1 a = a := by
    simp [sigmaAct]
  have hsigma_mul (d e : D) (a : Ω) :
      sigmaAct (d * e) a = sigmaAct e (sigmaAct d a) := by
    simp [sigmaAct, smul_smul]
  have hsigma_injective : Function.Injective sigmaAct := by
    intro d e hde
    apply Subtype.ext
    have hinv : (d : G)⁻¹ = (e : G)⁻¹ :=
      FaithfulSMul.eq_of_smul_eq_smul (fun a => congrFun hde a)
    exact inv_injective hinv
  have hrightD (d : D) (a : Ω) :
      rightConjugateElem (addLift a) (d : G) = addLift (sigmaAct d a) := by
    change (d : G)⁻¹ * (orbitEquiv.symm a : G) * (d : G) =
      (orbitEquiv.symm ((d : G)⁻¹ • a) : G)
    calc
      (d : G)⁻¹ * (orbitEquiv.symm a : G) * (d : G) =
          ((MulAut.conjNormal (H := F) (d : G)⁻¹
            (orbitEquiv.symm a) : F) : G) :=
          (MulAut.conjNormal_symm_apply (H := F) (d : G)
            (orbitEquiv.symm a)).symm
      _ = (orbitEquiv.symm ((d : G)⁻¹ • a) : G) :=
        congrArg (fun f : F => (f : G)) (hcoord_smul_D d a).symm
  have hcoordinate_bijective : Function.Bijective
      (fun x : Ω × Ωˣ × D => addLift x.1 * unitLift x.2.1 * (x.2.2 : G)) := by
    constructor
    · rintro ⟨a₁, x₁, d₁⟩ ⟨a₂, x₂, d₂⟩ heq
      change addLift a₁ * unitLift x₁ * (d₁ : G) =
        addLift a₂ * unitLift x₂ * (d₂ : G) at heq
      have hf₁ : addLift a₁ ∈ F := (orbitEquiv.symm a₁).property
      have hf₂ : addLift a₂ ∈ F := (orbitEquiv.symm a₂).property
      have hq₁ : unitLift x₁ ∈ Q := (unitCoord x₁).property
      have hq₂ : unitLift x₂ ∈ Q := (unitCoord x₂).property
      have hh₁ : unitLift x₁ * (d₁ : G) ∈ MulAction.stabilizer G base :=
        (MulAction.stabilizer G base).mul_mem (hA1.Q_le_H hq₁) (hA1.D_le_H d₁.property)
      have hh₂ : unitLift x₂ * (d₂ : G) ∈ MulAction.stabilizer G base :=
        (MulAction.stabilizer G base).mul_mem (hA1.Q_le_H hq₂) (hA1.D_le_H d₂.property)
      have hcross : (addLift a₂)⁻¹ * addLift a₁ =
          (unitLift x₂ * (d₂ : G)) * (unitLift x₁ * (d₁ : G))⁻¹ := by
        calc
          (addLift a₂)⁻¹ * addLift a₁ =
              (addLift a₂)⁻¹ * (addLift a₁ * unitLift x₁ * (d₁ : G)) *
                (unitLift x₁ * (d₁ : G))⁻¹ := by group
          _ = (addLift a₂)⁻¹ * (addLift a₂ * unitLift x₂ * (d₂ : G)) *
                (unitLift x₁ * (d₁ : G))⁻¹ := by rw [heq]
          _ = (unitLift x₂ * (d₂ : G)) * (unitLift x₁ * (d₁ : G))⁻¹ := by group
      have hcrossF : (addLift a₂)⁻¹ * addLift a₁ ∈ F :=
        F.mul_mem (F.inv_mem hf₂) hf₁
      have hcrossH : (addLift a₂)⁻¹ * addLift a₁ ∈ MulAction.stabilizer G base := by
        rw [hcross]
        exact (MulAction.stabilizer G base).mul_mem hh₂
          ((MulAction.stabilizer G base).inv_mem hh₁)
      have hcross_one : (addLift a₂)⁻¹ * addLift a₁ = 1 := by
        exact Subgroup.mem_bot.mp (hFdisH.le_bot ⟨hcrossF, hcrossH⟩)
      have haLift : addLift a₁ = addLift a₂ := by
        calc
          addLift a₁ = addLift a₂ * ((addLift a₂)⁻¹ * addLift a₁) := by group
          _ = addLift a₂ := by rw [hcross_one]; simp
      have ha : a₁ = a₂ := by
        apply orbitEquiv.symm.injective
        apply Subtype.ext
        exact haLift
      have hqd : unitLift x₁ * (d₁ : G) = unitLift x₂ * (d₂ : G) := by
        rw [ha] at heq
        have heq' : addLift a₂ * (unitLift x₁ * (d₁ : G)) =
            addLift a₂ * (unitLift x₂ * (d₂ : G)) := by
          simpa [mul_assoc] using heq
        exact mul_left_cancel heq'
      have hQDcross : (unitLift x₂)⁻¹ * unitLift x₁ = (d₂ : G) * (d₁ : G)⁻¹ := by
        calc
          (unitLift x₂)⁻¹ * unitLift x₁ =
              (unitLift x₂)⁻¹ * (unitLift x₁ * (d₁ : G)) * (d₁ : G)⁻¹ := by group
          _ = (unitLift x₂)⁻¹ * (unitLift x₂ * (d₂ : G)) * (d₁ : G)⁻¹ := by rw [hqd]
          _ = (d₂ : G) * (d₁ : G)⁻¹ := by group
      have hQDcrossQ : (unitLift x₂)⁻¹ * unitLift x₁ ∈ Q :=
        Q.mul_mem (Q.inv_mem hq₂) hq₁
      have hQDcrossD : (unitLift x₂)⁻¹ * unitLift x₁ ∈ D := by
        rw [hQDcross]
        exact D.mul_mem d₂.property (D.inv_mem d₁.property)
      have hQDcross_one : (unitLift x₂)⁻¹ * unitLift x₁ = 1 := by
        exact Subgroup.mem_bot.mp (hA1.Q_disjoint_D.le_bot ⟨hQDcrossQ, hQDcrossD⟩)
      have hqLift : unitLift x₁ = unitLift x₂ := by
        calc
          unitLift x₁ = unitLift x₂ * ((unitLift x₂)⁻¹ * unitLift x₁) := by group
          _ = unitLift x₂ := by rw [hQDcross_one]; simp
      have hx : x₁ = x₂ := by
        apply unitCoord.injective
        apply Subtype.ext
        exact hqLift
      have hd : d₁ = d₂ := by
        apply Subtype.ext
        rw [hqLift] at hqd
        exact mul_left_cancel hqd
      subst a₂
      subst x₂
      subst d₂
      rfl
    · intro g
      have hgSup : g ∈ F ⊔ MulAction.stabilizer G base := by
        rw [hFsupH]
        simp
      rcases Subgroup.mem_sup_of_normal_left.mp hgSup with
        ⟨f, hfF, h, hhH, hfh⟩
      let hH : MulAction.stabilizer G base := ⟨h, hhH⟩
      let QH : Subgroup (MulAction.stabilizer G base) :=
        Q.subgroupOf (MulAction.stabilizer G base)
      let DH : Subgroup (MulAction.stabilizer G base) :=
        D.subgroupOf (MulAction.stabilizer G base)
      letI : QH.Normal := hA1.Q_normal_in_H
      have hQHDH : QH ⊔ DH = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hA1.Q_le_H hA1.D_le_H, hA1.Q_sup_D]
        exact Subgroup.subgroupOf_self _
      have hhSup : hH ∈ QH ⊔ DH := by rw [hQHDH]; simp
      rcases Subgroup.mem_sup_of_normal_left.mp hhSup with
        ⟨q, hqQ, d, hdD, hqd⟩
      let fF : F := ⟨f, hfF⟩
      let qQ : Q := ⟨(q : G), hqQ⟩
      let dD : D := ⟨(d : G), hdD⟩
      refine ⟨(orbitEquiv fF, unitCoord.symm qQ, dD), ?_⟩
      change ((orbitEquiv.symm (orbitEquiv fF) : F) : G) *
          ((unitCoord (unitCoord.symm qQ) : Q) : G) * (dD : G) = g
      rw [orbitEquiv.symm_apply_apply, unitCoord.apply_symm_apply]
      have hqdG : (q : G) * (d : G) = h :=
        congrArg (fun z : MulAction.stabilizer G base => (z : G)) hqd
      change f * (q : G) * (d : G) = g
      calc
        f * (q : G) * (d : G) = f * ((q : G) * (d : G)) := mul_assoc _ _ _
        _ = f * h := by rw [hqdG]
        _ = g := hfh
  have hunit_neg_one_of_involution (q : Q) (hq : IsInvolution (q : G)) :
      ((unitCoord.symm q : Ωˣ) : Ω) = -1 := by
    have hxU_sq : (unitCoord.symm q) ^ 2 = (1 : Ωˣ) := by
      apply unitCoord.injective
      rw [map_pow, map_one, unitCoord.apply_symm_apply]
      apply Subtype.ext
      exact hq.sq_eq_one
    have hx_sq : ((unitCoord.symm q : Ωˣ) : Ω) ^ 2 = 1 := by
      simpa using congrArg (fun x : Ωˣ => (x : Ω)) hxU_sq
    rcases rightNearField_eq_one_or_eq_neg_one_of_sq_eq_one hx_sq with hxone | hxneg
    · exfalso
      apply hq.ne_one
      have hxU_one : unitCoord.symm q = 1 := Units.ext hxone
      have hq_one : q = 1 := by
        calc
          q = unitCoord (unitCoord.symm q) := (unitCoord.apply_symm_apply q).symm
          _ = unitCoord 1 := by rw [hxU_one]
          _ = 1 := map_one unitCoord
      exact congrArg (fun z : Q => (z : G)) hq_one
    · exact hxneg
  have hunique_H_involution : ∃! h : MulAction.stabilizer G base, IsInvolution (h : G) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨q, hqOrder⟩ :=
      exists_prime_orderOf_dvd_card' (G := Q) 2 hA1.Q_even.two_dvd
    have hqI : IsInvolution (q : G) := by
      have hqOrderG : orderOf (q : G) = 2 := by
        rw [Subgroup.orderOf_coe, hqOrder]
      have hpow_ne := (orderOf_eq_prime_iff (x := (q : G)) (p := 2)).mp hqOrderG
      exact ⟨hpow_ne.2, hpow_ne.1⟩
    let h₀ : MulAction.stabilizer G base := ⟨(q : G), hA1.Q_le_H q.property⟩
    refine ⟨h₀, hqI, ?_⟩
    intro h hhI
    have hhQ : (h : G) ∈ Q :=
      involution_mem_Q_of_mem_H (MulAction.stabilizer G base) D Q t hA1
        (h : G) h.property hhI
    let qh : Q := ⟨(h : G), hhQ⟩
    have hqh_neg := hunit_neg_one_of_involution qh hhI
    have hq_neg := hunit_neg_one_of_involution q hqI
    have hx_eq : unitCoord.symm qh = unitCoord.symm q := by
      apply Units.ext
      exact hqh_neg.trans hq_neg.symm
    have hq_eq : qh = q := by
      calc
        qh = unitCoord (unitCoord.symm qh) := (unitCoord.apply_symm_apply qh).symm
        _ = unitCoord (unitCoord.symm q) := by rw [hx_eq]
        _ = q := unitCoord.apply_symm_apply q
    apply Subtype.ext
    exact congrArg (fun z : Q => (z : G)) hq_eq
  have hzero_coord : orbitEquiv.symm (0 : Ω) = (1 : F) := by
    apply Subtype.ext
    exact haddLift_zero
  have horbit_nsmul (n : ℕ) (a : Ω) :
      orbitEquiv.symm (n • a) = (orbitEquiv.symm a) ^ n := by
    induction n with
    | zero => rw [zero_nsmul, pow_zero, hzero_coord]
    | succ n hn => rw [succ_nsmul, pow_succ, horbit_add, hn]
  have hFpow (f : F) : f ^ p = 1 :=
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p F)) f
  have hp_smul_zero (a : Ω) : p • a = 0 := by
    apply orbitEquiv.symm.injective
    rw [horbit_nsmul, hFpow, hzero_coord]
  have haddOrder_one : addOrderOf (1 : Ω) = p :=
    addOrderOf_eq_prime (hp_smul_zero 1) one_ne_zero
  have hneg_one_ne_one : (-1 : Ω) ≠ 1 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨q, hqOrder⟩ :=
      exists_prime_orderOf_dvd_card' (G := Q) 2 hA1.Q_even.two_dvd
    have hqI : IsInvolution (q : G) := by
      have hqOrderG : orderOf (q : G) = 2 := by
        rw [Subgroup.orderOf_coe, hqOrder]
      have hpow_ne := (orderOf_eq_prime_iff (x := (q : G)) (p := 2)).mp hqOrderG
      exact ⟨hpow_ne.2, hpow_ne.1⟩
    have hxneg := hunit_neg_one_of_involution q hqI
    intro hneg
    apply hqI.ne_one
    have hxone : unitCoord.symm q = 1 := by
      apply Units.ext
      exact hxneg.trans hneg
    have hqone : q = 1 := by
      calc
        q = unitCoord (unitCoord.symm q) := (unitCoord.apply_symm_apply q).symm
        _ = unitCoord 1 := by rw [hxone]
        _ = 1 := map_one unitCoord
    exact congrArg (fun z : Q => (z : G)) hqone
  have hp_ne_two : p ≠ 2 := by
    intro hpTwo
    have htwo : (2 : ℕ) • (1 : Ω) = 0 := by
      rw [← hpTwo]
      exact hp_smul_zero 1
    have hsum : (1 : Ω) + 1 = 0 := by simpa [two_nsmul] using htwo
    exact hneg_one_ne_one (eq_neg_of_add_eq_zero_right hsum).symm
  have hinvolution_product (s t : G) (hs : IsInvolution s) (ht : IsInvolution t)
      (hne : s ≠ t) : orderOf (s * t) = addOrderOf (1 : Ω) := by
    have hmul_univ : (F : Set G) * (MulAction.stabilizer G base : Set G) = Set.univ := by
      rw [Set.eq_univ_iff_forall]
      intro g
      have hgSup : g ∈ F ⊔ MulAction.stabilizer G base := by
        rw [hFsupH]
        simp
      rcases Subgroup.mem_sup_of_normal_left.mp hgSup with ⟨f, hf, h, hh, hfh⟩
      exact ⟨f, hf, h, hh, hfh⟩
    let hFH : F.IsComplement' (MulAction.stabilizer G base) :=
      Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hFdisH hmul_univ
    let hHF : (MulAction.stabilizer G base).IsComplement' F := hFH.symm
    let proj : G →* MulAction.stabilizer G base :=
      hHF.QuotientMulEquiv.toMonoidHom.comp (QuotientGroup.mk' F)
    have hproj_ne_one (x : G) (hx : IsInvolution x) : proj x ≠ 1 := by
      intro hxproj
      have hquotOne : (QuotientGroup.mk' F) x = 1 := by
        apply (MulEquiv.map_eq_one_iff hHF.QuotientMulEquiv).mp
        exact hxproj
      have hxFmem : x ∈ F := (QuotientGroup.eq_one_iff x).mp hquotOne
      let xF : F := ⟨x, hxFmem⟩
      have hxFpow : xF ^ p = 1 := hFpow xF
      have hxForder : orderOf xF = 2 := by
        rw [← Subgroup.orderOf_coe]
        exact (orderOf_eq_prime_iff (x := x) (p := 2)).mpr
          ⟨hx.sq_eq_one, hx.ne_one⟩
      have htwoDvd : 2 ∣ p := by
        rw [← hxForder]
        exact orderOf_dvd_of_pow_eq_one hxFpow
      rcases (Nat.dvd_prime hp).mp htwoDvd with htwoOne | htwoP
      · omega
      · exact hp_ne_two htwoP.symm
    have hproj_involution (x : G) (hx : IsInvolution x) :
        IsInvolution ((proj x : MulAction.stabilizer G base) : G) := by
      have hsqH : (proj x) ^ 2 = 1 := by
        rw [← map_pow, hx.sq_eq_one, map_one]
      constructor
      · intro hcoe
        apply hproj_ne_one x hx
        apply Subtype.ext
        exact hcoe
      · exact congrArg (fun h : MulAction.stabilizer G base => (h : G)) hsqH
    have hsProjI := hproj_involution s hs
    have htProjI := hproj_involution t ht
    have hprojEq : proj s = proj t :=
      hunique_H_involution.unique hsProjI htProjI
    have hprojMul : proj (s * t) = 1 := by
      rw [map_mul, hprojEq]
      have htSqH : (proj t) ^ 2 = 1 := by
        rw [← map_pow, ht.sq_eq_one, map_one]
      simpa [pow_two] using htSqH
    have hquotMul : (QuotientGroup.mk' F) (s * t) = 1 := by
      apply (MulEquiv.map_eq_one_iff hHF.QuotientMulEquiv).mp
      exact hprojMul
    have hstF : s * t ∈ F := (QuotientGroup.eq_one_iff (s * t)).mp hquotMul
    let stF : F := ⟨s * t, hstF⟩
    have hstF_ne : stF ≠ 1 := by
      intro hstOne
      apply hne
      have hstOneG : s * t = 1 := congrArg (fun f : F => (f : G)) hstOne
      calc
        s = (s * t) * t⁻¹ := by group
        _ = t⁻¹ := by rw [hstOneG, one_mul]
        _ = t := ht.inv_eq_self
    have hstOrderF : orderOf stF = p :=
      (orderOf_eq_prime_iff (x := stF) (p := p)).mpr ⟨hFpow stF, hstF_ne⟩
    calc
      orderOf (s * t) = orderOf stF := Subgroup.orderOf_coe stF
      _ = p := hstOrderF
      _ = addOrderOf (1 : Ω) := haddOrder_one.symm
  refine ⟨Ω, inferInstance, inferInstance, inferInstance,
    addLift, unitLift, sigmaAct, hcoordinate_bijective, haddLift_zero,
    haddLift_add, hunitLift_one, hunitLift_mul, hunitLift_range, hrightQ,
    hsigma_struct, hsigma_one, hsigma_mul, hsigma_injective, hrightD,
    hunique_H_involution, hinvolution_product⟩

end PFAppendixII
end CFSG.BenderSuzuki

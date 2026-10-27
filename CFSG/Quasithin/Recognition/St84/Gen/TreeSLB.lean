module

import CFSG.Quasithin.Recognition.St84.Gen.OTwoResL2
public import CFSG.Quasithin.Recognition.St84.AppTreeSAHyp
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.Quasithin.Recognition.St84.AppTreeSAB

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R
  CFSG.Quasithin.St84 CFSG.Quasithin.Fan86 CFSG.Quasithin.Fan86.Univ
open scoped Pointwise

variable {H : Type} [Group H] [Finite H]

noncomputable def f112slNlocalB (L1 L2 S : Subgroup H) :
    Subgroup (f112Gold L1 L2 S).Universal :=
  f112saMB L1 L2 S ⊔
    pCoreOf 2 (f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofB.range)

theorem f112slMB_le_E {L1 L2 S : Subgroup H} :
    f112saMB L1 L2 S ≤ f112EOdd L1 L2 S := by
  rw [f112saMB, Subgroup.map_le_iff_le_comap]
  intro z hz
  have hzM : (z : H) ∈ oTwoRes L2 := Subgroup.mem_subgroupOf.mp hz
  have key : ∀ (w : H) (hwP : w ∈ f112P2 L1 L2 S), w ∈ oTwoRes L2 →
      (f112Gold L1 L2 S).ofB ⟨w, hwP⟩ ∈ f112EOdd L1 L2 S := by
    intro w hwP hw
    revert hwP
    induction hw using Subgroup.closure_induction with
    | mem v hv =>
        intro hvP
        refine Subgroup.subset_closure ⟨Or.inr ⟨⟨v, hvP⟩, rfl⟩, ?_⟩
        rw [orderOf_injective (f112Gold L1 L2 S).ofB
          (f112Gold L1 L2 S).ofB_injective, Subgroup.orderOf_mk]
        exact hv.2.choose_spec.1.of_dvd_nat (orderOf_dvd_of_pow_eq_one hv.2.choose_spec.2)
    | one =>
        intro h1P
        have h1 : (⟨1, h1P⟩ : ↥(f112P2 L1 L2 S)) = 1 := Subtype.ext rfl
        rw [h1, map_one]
        exact Subgroup.one_mem (f112EOdd L1 L2 S)
    | mul a b ha hb iha ihb =>
        intro habP
        have haP : a ∈ f112P2 L1 L2 S := Subgroup.mem_sup_left ((oTwoRes_le L2) ha)
        have hbP : b ∈ f112P2 L1 L2 S := Subgroup.mem_sup_left ((oTwoRes_le L2) hb)
        have heq : (⟨a * b, habP⟩ : ↥(f112P2 L1 L2 S)) =
            ⟨a, haP⟩ * ⟨b, hbP⟩ := Subtype.ext rfl
        rw [heq, map_mul]
        exact Subgroup.mul_mem (f112EOdd L1 L2 S) (iha haP) (ihb hbP)
    | inv a ha iha =>
        intro haP
        have haP' : a ∈ f112P2 L1 L2 S := Subgroup.mem_sup_left ((oTwoRes_le L2) ha)
        have heq : (⟨a⁻¹, haP⟩ : ↥(f112P2 L1 L2 S)) =
            (⟨a, haP'⟩ : ↥(f112P2 L1 L2 S))⁻¹ := Subtype.ext rfl
        rw [heq, map_inv]
        exact Subgroup.inv_mem (f112EOdd L1 L2 S) (iha haP')
  exact key z z.2 hzM

theorem f112slMB_le_Nbeta {L1 L2 S : Subgroup H} :
    f112saMB L1 L2 S ≤ f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofB.range :=
  le_inf f112slMB_le_E (f112saMB_le_range L1 L2 S)

theorem f112sl_bigB_le_normalizer_oTwoRes {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) :
    bigB L1 L2 S ≤ Subgroup.normalizer (oTwoRes L2 : Set H) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  show conjSub b (oTwoRes L2) = oTwoRes L2
  rw [conjSub_oTwoRes, F1.conjSub_eq_of_mem_normalizer (f112sa_bigB_le_normalizer_L2 hF hb)]

private theorem f112sl_ofB_range_le_normalizer_MB {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) :
    (f112Gold L1 L2 S).ofB.range ≤
      Subgroup.normalizer (f112saMB L1 L2 S : Set (f112Gold L1 L2 S).Universal) := by
  intro g hg
  obtain ⟨p, rfl⟩ := hg
  have hP2_normO2 : f112P2 L1 L2 S ≤ Subgroup.normalizer (oTwoRes L2 : Set H) :=
    sup_le (le_normalizer_oTwoRes L2) (f112sl_bigB_le_normalizer_oTwoRes hF)
  have hconj : ∀ q : ↥(f112P2 L1 L2 S), ∀ x ∈ f112saMB L1 L2 S,
      (f112Gold L1 L2 S).ofB q * x * ((f112Gold L1 L2 S).ofB q)⁻¹ ∈
        f112saMB L1 L2 S := by
    intro q x hx
    obtain ⟨m, hm, rfl⟩ := hx
    have hm' : (m : H) ∈ oTwoRes L2 := Subgroup.mem_subgroupOf.mp hm
    have hqm : (q : H) * (m : H) * (q : H)⁻¹ ∈ oTwoRes L2 :=
      (Subgroup.mem_normalizer_iff.mp (hP2_normO2 q.2) (m : H)).mp hm'
    have hqmP : (q : H) * (m : H) * (q : H)⁻¹ ∈ f112P2 L1 L2 S :=
      (f112P2 L1 L2 S).mul_mem ((f112P2 L1 L2 S).mul_mem q.2 m.2)
        ((f112P2 L1 L2 S).inv_mem q.2)
    refine Subgroup.mem_map.mpr
      ⟨⟨(q : H) * (m : H) * (q : H)⁻¹, hqmP⟩,
        Subgroup.mem_subgroupOf.mpr hqm, ?_⟩
    change (f112Gold L1 L2 S).ofB (⟨(q : H) * (m : H) * (q : H)⁻¹, hqmP⟩ :
        ↥(f112P2 L1 L2 S)) =
      (f112Gold L1 L2 S).ofB q * (f112Gold L1 L2 S).ofB m *
        ((f112Gold L1 L2 S).ofB q)⁻¹
    rw [show (⟨(q : H) * (m : H) * (q : H)⁻¹, hqmP⟩ : ↥(f112P2 L1 L2 S)) =
      q * m * q⁻¹ from Subtype.ext rfl, map_mul, map_mul, map_inv]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hconj p x
  · intro hx
    have h := hconj p⁻¹ ((f112Gold L1 L2 S).ofB p * x * ((f112Gold L1 L2 S).ofB p)⁻¹) hx
    have heq : (f112Gold L1 L2 S).ofB p⁻¹ *
        ((f112Gold L1 L2 S).ofB p * x * ((f112Gold L1 L2 S).ofB p)⁻¹) *
        ((f112Gold L1 L2 S).ofB p⁻¹)⁻¹ = x := by
      rw [map_inv, inv_inv]
      group
    rwa [heq] at h

theorem f112slMB_normal_Nbeta {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) :
    f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofB.range ≤
      Subgroup.normalizer (f112saMB L1 L2 S : Set (f112Gold L1 L2 S).Universal) :=
  (inf_le_right : f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofB.range ≤
    (f112Gold L1 L2 S).ofB.range).trans (f112sl_ofB_range_le_normalizer_MB hF)

theorem f112slNlocalB_normal_Nbeta {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) :
    f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofB.range ≤ Subgroup.normalizer
      (f112slNlocalB L1 L2 S : Set (f112Gold L1 L2 S).Universal) :=
  (le_inf (f112slMB_normal_Nbeta hF)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2
      (f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofB.range))).trans
    (Subgroup.inf_normalizer_le_normalizer_sup (f112saMB L1 L2 S)
      (pCoreOf 2 (f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofB.range)))

theorem f112slNlocalB_le_Nbeta {L1 L2 S : Subgroup H} :
    f112slNlocalB L1 L2 S ≤ f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofB.range :=
  sup_le f112slMB_le_Nbeta (CFSG.LieType.BorelTits.pCoreOf_le 2 _)

theorem f112slNlocalB_le_E {L1 L2 S : Subgroup H} :
    f112slNlocalB L1 L2 S ≤ f112EOdd L1 L2 S :=
  f112slNlocalB_le_Nbeta.trans inf_le_left

theorem f112sl_oTwoRes_quot {L : Subgroup H} {n : ℕ} (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L)) :
    Nonempty (↥(oTwoRes L) ⧸ CFSG.pCore 2 ↥(oTwoRes L) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) := by
  obtain ⟨e1⟩ := pCore_quotient_mulEquiv_of_sup_pCoreOf (M := oTwoRes L) (L := L)
    (oTwoRes_le L) (le_normalizer_oTwoRes L) (f112sl_oTwoRes_sup_pCoreOf hn h2)
  obtain ⟨e2⟩ := h2
  exact ⟨e1.trans e2⟩

theorem f112slMB_quot {L1 L2 S : Subgroup H} {n : ℕ} (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    Nonempty (↥(f112saMB L1 L2 S) ⧸ CFSG.pCore 2 ↥(f112saMB L1 L2 S) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) := by
  obtain ⟨e1⟩ := f112sl_oTwoRes_quot (L := L2) hn h2
  let e2 : ↥(oTwoRes L2) ≃* ↥(f112saMB L1 L2 S) :=
    (Subgroup.subgroupOfEquivOfLe ((oTwoRes_le L2).trans le_sup_left)).symm.trans
      (Subgroup.equivMapOfInjective
        (H := (oTwoRes L2).subgroupOf (f112P2 L1 L2 S))
        (f := (f112Gold L1 L2 S).ofB) (f112Gold L1 L2 S).ofB_injective)
  exact ⟨(pCoreQuotientMulEquiv 2 e2).symm.trans e1⟩

theorem f112slNlocalB_quot {L1 L2 S : Subgroup H} {n : ℕ}
    (hF : F112HypW L1 L2 S) (hn : 2 ≤ n) (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    Nonempty (↥(f112slNlocalB L1 L2 S) ⧸ CFSG.pCore 2 ↥(f112slNlocalB L1 L2 S) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) := by
  obtain ⟨e1⟩ := pCore_quotient_mulEquiv_of_sup_pCoreOf_of_normal
    (M := f112saMB L1 L2 S)
    (K := f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofB.range) f112slMB_le_Nbeta
    (f112slMB_normal_Nbeta hF)
  obtain ⟨e2⟩ := f112slMB_quot (L1 := L1) (L2 := L2) (S := S) hn h2
  exact ⟨e1.trans e2⟩

theorem f112slNlocalB_subgroupOf_quot {L1 L2 S : Subgroup H} {n : ℕ}
    (hF : F112HypW L1 L2 S) (hn : 2 ≤ n) (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    Nonempty (↥((f112slNlocalB L1 L2 S).subgroupOf (f112EOdd L1 L2 S)) ⧸
        CFSG.pCore 2 ↥((f112slNlocalB L1 L2 S).subgroupOf (f112EOdd L1 L2 S)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) := by
  obtain ⟨e1⟩ := f112slNlocalB_quot hF hn h2
  exact ⟨(pCoreQuotientMulEquiv 2
    (Subgroup.subgroupOfEquivOfLe f112slNlocalB_le_E)).trans e1⟩

theorem f112slMB_trans {L1 L2 S : Subgroup H} {n : ℕ}
    (hF : F112HypW L1 L2 S) (hn : 2 ≤ n) (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    ∀ a b : Vtx (f112Gold L1 L2 S),
      (f112Gold L1 L2 S).treeGraph.Adj (baseB (f112Gold L1 L2 S)) a →
      (f112Gold L1 L2 S).treeGraph.Adj (baseB (f112Gold L1 L2 S)) b →
      ∃ g ∈ f112saMB L1 L2 S, g • a = b := by
  intro a b ha hb
  let X := f112Gold L1 L2 S
  obtain ⟨p, rfl⟩ := (adj_baseB_iff X a).1 ha
  obtain ⟨p', rfl⟩ := (adj_baseB_iff X b).1 hb
  have hB_normO2 : bigB L1 L2 S ≤ Subgroup.normalizer (oTwoRes L2 : Set H) :=
    f112sl_bigB_le_normalizer_oTwoRes hF
  have hP2_normO2 : f112P2 L1 L2 S ≤ Subgroup.normalizer (oTwoRes L2 : Set H) :=
    sup_le (le_normalizer_oTwoRes L2) hB_normO2
  have hQleB : pCoreOf 2 L2 ≤ bigB L1 L2 S := by
    have h1 : pCoreOf 2 L2 ≤ borelOf L2 S :=
      (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hF.1.h2.sylow).trans
        (F1.sylow_le_borelOf L2 S)
    have h2' : borelOf L2 S ≤ borelOf L1 S ⊔ borelOf L2 S := le_sup_right
    have h3 : borelOf L1 S ⊔ borelOf L2 S ≤ bigB L1 L2 S := by
      change borelOf L1 S ⊔ borelOf L2 S ≤ borelOf L1 S ⊔ borelOf L2 S ⊔ S
      exact le_sup_left
    exact h1.trans (h2'.trans h3)
  have hL2_le : L2 ≤ oTwoRes L2 ⊔ bigB L1 L2 S := by
    calc L2 = oTwoRes L2 ⊔ pCoreOf 2 L2 := (f112sl_oTwoRes_sup_pCoreOf hn h2).symm
      _ ≤ oTwoRes L2 ⊔ bigB L1 L2 S := sup_le le_sup_left (hQleB.trans le_sup_right)
  have hP2_le : f112P2 L1 L2 S ≤ oTwoRes L2 ⊔ bigB L1 L2 S := by
    change L2 ⊔ bigB L1 L2 S ≤ oTwoRes L2 ⊔ bigB L1 L2 S
    exact sup_le hL2_le le_sup_right
  have hpP2 : (p : H) ∈ f112P2 L1 L2 S := p.2
  have hp'P2 : (p' : H) ∈ f112P2 L1 L2 S := p'.2
  have hmemP2 : (p : H)⁻¹ * (p' : H) ∈ f112P2 L1 L2 S :=
    (f112P2 L1 L2 S).mul_mem ((f112P2 L1 L2 S).inv_mem hpP2) hp'P2
  have hmemO2B : (p : H)⁻¹ * (p' : H) ∈ oTwoRes L2 ⊔ bigB L1 L2 S := hP2_le hmemP2
  have hcoe : (↑(oTwoRes L2 ⊔ bigB L1 L2 S) : Set H) =
      (oTwoRes L2 : Set H) * (bigB L1 L2 S : Set H) :=
    Subgroup.coe_mul_of_right_le_normalizer_left (N := oTwoRes L2)
      (H := bigB L1 L2 S) hB_normO2
  have hmemProd : (p : H)⁻¹ * (p' : H) ∈
      (oTwoRes L2 : Set H) * (bigB L1 L2 S : Set H) := by
    rw [← hcoe]; exact hmemO2B
  obtain ⟨m', hm', b₀, hb₀, hmb⟩ := hmemProd
  have hmb' : m' * b₀ = (p : H)⁻¹ * (p' : H) := hmb
  let mH : H := (p : H) * m' * (p : H)⁻¹
  have hmO2 : mH ∈ oTwoRes L2 := by
    dsimp [mH]
    exact (Subgroup.mem_normalizer_iff.mp (hP2_normO2 hpP2) m').mp hm'
  have hmP2 : mH ∈ f112P2 L1 L2 S := by
    dsimp [mH]
    exact (f112P2 L1 L2 S).mul_mem
      ((f112P2 L1 L2 S).mul_mem hpP2 (Subgroup.mem_sup_left ((oTwoRes_le L2) hm')))
      ((f112P2 L1 L2 S).inv_mem hpP2)
  have hp'_eq : (p' : H) = mH * (p : H) * b₀ := by
    dsimp [mH]
    calc (p' : H) = (p : H) * ((p : H)⁻¹ * (p' : H)) := by group
      _ = (p : H) * (m' * b₀) := by rw [hmb']
      _ = ((p : H) * m' * (p : H)⁻¹) * (p : H) * b₀ := by group
  have hb₀P1 : b₀ ∈ f112P1 L1 L2 S := (le_sup_right : bigB L1 L2 S ≤ f112P1 L1 L2 S) hb₀
  have hb₀P2 : b₀ ∈ f112P2 L1 L2 S := (le_sup_right : bigB L1 L2 S ≤ f112P2 L1 L2 S) hb₀
  have hXedgeB : X.edgeB =
      (f112P1 L1 L2 S ⊓ f112P2 L1 L2 S).subgroupOf (f112P2 L1 L2 S) := by
    change (Subgroup.inclusion inf_le_right).range = _
    exact Subgroup.inclusion_range inf_le_right
  have hb₀edge : (⟨b₀, hb₀P2⟩ : ↥(f112P2 L1 L2 S)) ∈ X.edgeB := by
    rw [hXedgeB]
    exact Subgroup.mem_subgroupOf.mpr ⟨hb₀P1, hb₀P2⟩
  have hb₀A : X.ofB ⟨b₀, hb₀P2⟩ ∈ X.ofA.range :=
    (ofB_mem_ofA_range_iff X ⟨b₀, hb₀P2⟩).2 hb₀edge
  have hmp_eq : p' = ⟨mH, hmP2⟩ * p * ⟨b₀, hb₀P2⟩ := by
    apply Subtype.ext
    show (p' : H) = mH * (p : H) * b₀
    exact hp'_eq
  have hcoset : (Sum.inl ((X.ofB (⟨mH, hmP2⟩ * p) : X.Universal) :
        X.Universal ⧸ X.ofA.range) : Vtx X) =
      Sum.inl ((X.ofB p' : X.Universal) : X.Universal ⧸ X.ofA.range) := by
    rw [Sum.inl.injEq, QuotientGroup.eq]
    have h : (X.ofB (⟨mH, hmP2⟩ * p))⁻¹ * X.ofB p' = X.ofB ⟨b₀, hb₀P2⟩ := by
      rw [hmp_eq, map_mul, map_mul, map_mul]
      group
    rw [h]
    exact hb₀A
  refine ⟨X.ofB ⟨mH, hmP2⟩, ?_, ?_⟩
  · exact Subgroup.mem_map_of_mem X.ofB (Subgroup.mem_subgroupOf.mpr hmO2)
  · rw [ofB_smul_inl X ⟨mH, hmP2⟩ p]
    exact hcoset

theorem f112sl_localL2_baseB {L1 L2 S : Subgroup H} {n : ℕ}
    (hF : F112HypW L1 L2 S) (hn : 2 ≤ n) (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    ∃ N : Subgroup ↥(f112EOdd L1 L2 S),
      IsLocL2 (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)
        (baseB (f112Gold L1 L2 S)) n N := by
  let E := f112EOdd L1 L2 S
  let X := f112Gold L1 L2 S
  let N : Subgroup ↥E := (f112slNlocalB L1 L2 S).subgroupOf E
  have hstab : MulAction.stabilizer ↥E (baseB X) =
      (f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofB.range).subgroupOf E := by
    rw [← MulAction.stabilizer_subgroupOf E (baseB X), stabilizer_baseB X,
      Subgroup.inf_subgroupOf_left]
  refine ⟨N, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hstab]
    exact Subgroup.subgroupOf_mono E f112slNlocalB_le_Nbeta
  · rw [hstab]
    refine Subgroup.normal_subgroupOf_of_le_normalizer ?_
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hkU : (k : X.Universal) ∈
        f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofB.range := Subgroup.mem_subgroupOf.mp hk
    constructor
    · intro hh
      rw [Subgroup.mem_subgroupOf] at hh ⊢
      exact (Subgroup.mem_normalizer_iff.mp (f112slNlocalB_normal_Nbeta hF hkU)
        (h : X.Universal)).mp hh
    · intro hh
      rw [Subgroup.mem_subgroupOf] at hh ⊢
      have hkU' : (k : X.Universal)⁻¹ ∈
          f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofB.range :=
        (f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofB.range).inv_mem hkU
      have hmem := (Subgroup.mem_normalizer_iff.mp (f112slNlocalB_normal_Nbeta hF hkU')
        ((k : X.Universal) * (h : X.Universal) * (k : X.Universal)⁻¹)).mp hh
      simpa [mul_assoc] using hmem
  · rw [hstab]
    intro y hy
    rw [Subgroup.mem_subgroupOf]
    have hpc := pCoreOf_subgroupOf_map
      (K := f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofB.range) (E := E) inf_le_left
    have hmem : (y : X.Universal) ∈
        (pCoreOf 2 ((f112EOdd L1 L2 S ⊓
          (f112Gold L1 L2 S).ofB.range).subgroupOf E)).map E.subtype :=
      Subgroup.mem_map_of_mem E.subtype hy
    rw [hpc] at hmem
    exact (show pCoreOf 2 (f112EOdd L1 L2 S ⊓
      (f112Gold L1 L2 S).ofB.range) ≤ f112slNlocalB L1 L2 S from le_sup_right) hmem
  · obtain ⟨e⟩ := f112slNlocalB_subgroupOf_quot hF hn h2
    exact ⟨e⟩
  · intro a b ha hb
    obtain ⟨g, hgMB, hgab⟩ := f112slMB_trans hF hn h2 a b ha hb
    refine ⟨⟨g, f112slMB_le_E hgMB⟩, ?_, ?_⟩
    · show (⟨g, f112slMB_le_E hgMB⟩ : ↥E) ∈ N
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_sup_left hgMB
    · show g • a = b
      exact hgab

end CFSG.Quasithin.F112R.St84

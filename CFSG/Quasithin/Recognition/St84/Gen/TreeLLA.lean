module

public import CFSG.Quasithin.Recognition.St84.Gen.TreeSLB
import CFSG.Quasithin.Recognition.St84.Gen.OTwoResL2

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R
  CFSG.Quasithin.St84 CFSG.Quasithin.Fan86 CFSG.Quasithin.Fan86.Univ
open scoped Pointwise

variable {H : Type} [Group H] [Finite H]

noncomputable abbrev f112llMA (L1 L2 S : Subgroup H) : Subgroup (f112Gold L1 L2 S).Universal :=
  ((oTwoRes L1).subgroupOf (f112P1 L1 L2 S)).map (f112Gold L1 L2 S).ofA

noncomputable def f112llNlocalA (L1 L2 S : Subgroup H) : Subgroup (f112Gold L1 L2 S).Universal :=
  f112llMA L1 L2 S ⊔ pCoreOf 2 (f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofA.range)

theorem f112llMA_le_range (L1 L2 S : Subgroup H) :
    f112llMA L1 L2 S ≤ (f112Gold L1 L2 S).ofA.range :=
  Subgroup.map_le_range _ _

theorem f112llMA_le_Nalpha {L1 L2 S : Subgroup H} :
    f112llMA L1 L2 S ≤ f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofA.range :=
  le_inf f112sa_oTwoRes_left_map_le_EOdd (f112llMA_le_range L1 L2 S)

private theorem f112ll_ofA_range_le_normalizer_MA {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) :
    (f112Gold L1 L2 S).ofA.range ≤
      Subgroup.normalizer (f112llMA L1 L2 S : Set (f112Gold L1 L2 S).Universal) := by
  intro g hg
  obtain ⟨p, rfl⟩ := hg
  have hP1_normO2 : f112P1 L1 L2 S ≤ Subgroup.normalizer (oTwoRes L1 : Set H) :=
    sup_le (le_normalizer_oTwoRes L1) (f112sa_bigB_le_normalizer_oTwoRes_left hF)
  have hconj : ∀ q : ↥(f112P1 L1 L2 S), ∀ x ∈ f112llMA L1 L2 S,
      (f112Gold L1 L2 S).ofA q * x * ((f112Gold L1 L2 S).ofA q)⁻¹ ∈
        f112llMA L1 L2 S := by
    intro q x hx
    obtain ⟨m, hm, rfl⟩ := hx
    have hm' : (m : H) ∈ oTwoRes L1 := Subgroup.mem_subgroupOf.mp hm
    have hqm : (q : H) * (m : H) * (q : H)⁻¹ ∈ oTwoRes L1 :=
      (Subgroup.mem_normalizer_iff.mp (hP1_normO2 q.2) (m : H)).mp hm'
    have hqmP : (q : H) * (m : H) * (q : H)⁻¹ ∈ f112P1 L1 L2 S :=
      (f112P1 L1 L2 S).mul_mem ((f112P1 L1 L2 S).mul_mem q.2 m.2)
        ((f112P1 L1 L2 S).inv_mem q.2)
    refine Subgroup.mem_map.mpr
      ⟨⟨(q : H) * (m : H) * (q : H)⁻¹, hqmP⟩,
        Subgroup.mem_subgroupOf.mpr hqm, ?_⟩
    change (f112Gold L1 L2 S).ofA (⟨(q : H) * (m : H) * (q : H)⁻¹, hqmP⟩ :
        ↥(f112P1 L1 L2 S)) =
      (f112Gold L1 L2 S).ofA q * (f112Gold L1 L2 S).ofA m *
        ((f112Gold L1 L2 S).ofA q)⁻¹
    rw [show (⟨(q : H) * (m : H) * (q : H)⁻¹, hqmP⟩ : ↥(f112P1 L1 L2 S)) =
      q * m * q⁻¹ from Subtype.ext rfl, map_mul, map_mul, map_inv]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hconj p x
  · intro hx
    have h := hconj p⁻¹ ((f112Gold L1 L2 S).ofA p * x * ((f112Gold L1 L2 S).ofA p)⁻¹) hx
    have heq : (f112Gold L1 L2 S).ofA p⁻¹ *
        ((f112Gold L1 L2 S).ofA p * x * ((f112Gold L1 L2 S).ofA p)⁻¹) *
        ((f112Gold L1 L2 S).ofA p⁻¹)⁻¹ = x := by
      rw [map_inv, inv_inv]
      group
    rwa [heq] at h

theorem f112llMA_normal_Nalpha {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) :
    f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofA.range ≤
      Subgroup.normalizer (f112llMA L1 L2 S : Set (f112Gold L1 L2 S).Universal) :=
  (inf_le_right : f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofA.range ≤
    (f112Gold L1 L2 S).ofA.range).trans (f112ll_ofA_range_le_normalizer_MA hF)

theorem f112llNlocalA_normal_Nalpha {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) :
    f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofA.range ≤ Subgroup.normalizer
      (f112llNlocalA L1 L2 S : Set (f112Gold L1 L2 S).Universal) :=
  (le_inf (f112llMA_normal_Nalpha hF)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2
      (f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofA.range))).trans
    (Subgroup.inf_normalizer_le_normalizer_sup (f112llMA L1 L2 S)
      (pCoreOf 2 (f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofA.range)))

theorem f112llNlocalA_le_Nalpha {L1 L2 S : Subgroup H} :
    f112llNlocalA L1 L2 S ≤ f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofA.range :=
  sup_le f112llMA_le_Nalpha (CFSG.LieType.BorelTits.pCoreOf_le 2 _)

theorem f112llNlocalA_le_E {L1 L2 S : Subgroup H} :
    f112llNlocalA L1 L2 S ≤ f112EOdd L1 L2 S :=
  f112llNlocalA_le_Nalpha.trans inf_le_left

theorem f112llMA_quot {L1 L2 S : Subgroup H} {m : ℕ} (hm : 2 ≤ m)
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) :
    Nonempty (↥(f112llMA L1 L2 S) ⧸ CFSG.pCore 2 ↥(f112llMA L1 L2 S) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 m)) := by
  obtain ⟨e1⟩ := f112sl_oTwoRes_quot (L := L1) hm h1
  let e2 : ↥(oTwoRes L1) ≃* ↥(f112llMA L1 L2 S) :=
    (Subgroup.subgroupOfEquivOfLe ((oTwoRes_le L1).trans le_sup_left)).symm.trans
      (Subgroup.equivMapOfInjective
        (H := (oTwoRes L1).subgroupOf (f112P1 L1 L2 S))
        (f := (f112Gold L1 L2 S).ofA) (f112Gold L1 L2 S).ofA_injective)
  exact ⟨(pCoreQuotientMulEquiv 2 e2).symm.trans e1⟩

theorem f112llNlocalA_quot {L1 L2 S : Subgroup H} {m : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (h1 : IsL2Quot m (oTwoQuot ↥L1)) :
    Nonempty (↥(f112llNlocalA L1 L2 S) ⧸ CFSG.pCore 2 ↥(f112llNlocalA L1 L2 S) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 m)) := by
  obtain ⟨e1⟩ := pCore_quotient_mulEquiv_of_sup_pCoreOf_of_normal
    (M := f112llMA L1 L2 S)
    (K := f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofA.range) f112llMA_le_Nalpha
    (f112llMA_normal_Nalpha hF)
  obtain ⟨e2⟩ := f112llMA_quot (L1 := L1) (L2 := L2) (S := S) hm h1
  exact ⟨e1.trans e2⟩

theorem f112llNlocalA_subgroupOf_quot {L1 L2 S : Subgroup H} {m : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (h1 : IsL2Quot m (oTwoQuot ↥L1)) :
    Nonempty (↥((f112llNlocalA L1 L2 S).subgroupOf (f112EOdd L1 L2 S)) ⧸
        CFSG.pCore 2 ↥((f112llNlocalA L1 L2 S).subgroupOf (f112EOdd L1 L2 S)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 m)) := by
  obtain ⟨e1⟩ := f112llNlocalA_quot hF hm h1
  exact ⟨(pCoreQuotientMulEquiv 2
    (Subgroup.subgroupOfEquivOfLe f112llNlocalA_le_E)).trans e1⟩

theorem f112llMA_trans {L1 L2 S : Subgroup H} {m : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (h1 : IsL2Quot m (oTwoQuot ↥L1)) :
    ∀ a b : Vtx (f112Gold L1 L2 S),
      (f112Gold L1 L2 S).treeGraph.Adj (baseA (f112Gold L1 L2 S)) a →
      (f112Gold L1 L2 S).treeGraph.Adj (baseA (f112Gold L1 L2 S)) b →
      ∃ g ∈ f112llMA L1 L2 S, g • a = b := by
  intro a b ha hb
  let X := f112Gold L1 L2 S
  obtain ⟨p, rfl⟩ := (adj_baseA_iff X a).1 ha
  obtain ⟨p', rfl⟩ := (adj_baseA_iff X b).1 hb
  have hB_normO2 : bigB L1 L2 S ≤ Subgroup.normalizer (oTwoRes L1 : Set H) :=
    f112sa_bigB_le_normalizer_oTwoRes_left hF
  have hP1_normO2 : f112P1 L1 L2 S ≤ Subgroup.normalizer (oTwoRes L1 : Set H) :=
    sup_le (le_normalizer_oTwoRes L1) hB_normO2
  have hQleB : pCoreOf 2 L1 ≤ bigB L1 L2 S := by
    have hQ1 : pCoreOf 2 L1 ≤ borelOf L1 S :=
      (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hF.1.h1.sylow).trans
        (F1.sylow_le_borelOf L1 S)
    have hQ2 : borelOf L1 S ≤ borelOf L1 S ⊔ borelOf L2 S := le_sup_left
    have hQ3 : borelOf L1 S ⊔ borelOf L2 S ≤ bigB L1 L2 S := by
      change borelOf L1 S ⊔ borelOf L2 S ≤ borelOf L1 S ⊔ borelOf L2 S ⊔ S
      exact le_sup_left
    exact hQ1.trans (hQ2.trans hQ3)
  have hL1_le : L1 ≤ oTwoRes L1 ⊔ bigB L1 L2 S := by
    calc L1 = oTwoRes L1 ⊔ pCoreOf 2 L1 := (f112sl_oTwoRes_sup_pCoreOf hm h1).symm
      _ ≤ oTwoRes L1 ⊔ bigB L1 L2 S := sup_le le_sup_left (hQleB.trans le_sup_right)
  have hP1_le : f112P1 L1 L2 S ≤ oTwoRes L1 ⊔ bigB L1 L2 S := by
    change L1 ⊔ bigB L1 L2 S ≤ oTwoRes L1 ⊔ bigB L1 L2 S
    exact sup_le hL1_le le_sup_right
  have hpP1 : (p : H) ∈ f112P1 L1 L2 S := p.2
  have hp'P1 : (p' : H) ∈ f112P1 L1 L2 S := p'.2
  have hmemP1 : (p : H)⁻¹ * (p' : H) ∈ f112P1 L1 L2 S :=
    (f112P1 L1 L2 S).mul_mem ((f112P1 L1 L2 S).inv_mem hpP1) hp'P1
  have hmemO2B : (p : H)⁻¹ * (p' : H) ∈ oTwoRes L1 ⊔ bigB L1 L2 S := hP1_le hmemP1
  have hcoe : (↑(oTwoRes L1 ⊔ bigB L1 L2 S) : Set H) =
      (oTwoRes L1 : Set H) * (bigB L1 L2 S : Set H) :=
    Subgroup.coe_mul_of_right_le_normalizer_left (N := oTwoRes L1)
      (H := bigB L1 L2 S) hB_normO2
  have hmemProd : (p : H)⁻¹ * (p' : H) ∈
      (oTwoRes L1 : Set H) * (bigB L1 L2 S : Set H) := by
    rw [← hcoe]; exact hmemO2B
  obtain ⟨m', hm', b₀, hb₀, hmb⟩ := hmemProd
  have hmb' : m' * b₀ = (p : H)⁻¹ * (p' : H) := hmb
  let mH : H := (p : H) * m' * (p : H)⁻¹
  have hmO2 : mH ∈ oTwoRes L1 := by
    dsimp [mH]
    exact (Subgroup.mem_normalizer_iff.mp (hP1_normO2 hpP1) m').mp hm'
  have hmP1 : mH ∈ f112P1 L1 L2 S := by
    dsimp [mH]
    exact (f112P1 L1 L2 S).mul_mem
      ((f112P1 L1 L2 S).mul_mem hpP1 (Subgroup.mem_sup_left ((oTwoRes_le L1) hm')))
      ((f112P1 L1 L2 S).inv_mem hpP1)
  have hp'_eq : (p' : H) = mH * (p : H) * b₀ := by
    dsimp [mH]
    calc (p' : H) = (p : H) * ((p : H)⁻¹ * (p' : H)) := by group
      _ = (p : H) * (m' * b₀) := by rw [hmb']
      _ = ((p : H) * m' * (p : H)⁻¹) * (p : H) * b₀ := by group
  have hb₀P1 : b₀ ∈ f112P1 L1 L2 S := (le_sup_right : bigB L1 L2 S ≤ f112P1 L1 L2 S) hb₀
  have hb₀P2 : b₀ ∈ f112P2 L1 L2 S := (le_sup_right : bigB L1 L2 S ≤ f112P2 L1 L2 S) hb₀
  have hXedgeA : X.edgeA =
      (f112P1 L1 L2 S ⊓ f112P2 L1 L2 S).subgroupOf (f112P1 L1 L2 S) := by
    change (Subgroup.inclusion inf_le_left).range = _
    exact Subgroup.inclusion_range inf_le_left
  have hb₀edge : (⟨b₀, hb₀P1⟩ : ↥(f112P1 L1 L2 S)) ∈ X.edgeA := by
    rw [hXedgeA]
    exact Subgroup.mem_subgroupOf.mpr ⟨hb₀P1, hb₀P2⟩
  have hb₀B : X.ofA ⟨b₀, hb₀P1⟩ ∈ X.ofB.range :=
    (ofA_mem_ofB_range_iff X ⟨b₀, hb₀P1⟩).2 hb₀edge
  have hmp_eq : p' = ⟨mH, hmP1⟩ * p * ⟨b₀, hb₀P1⟩ := by
    apply Subtype.ext
    show (p' : H) = mH * (p : H) * b₀
    exact hp'_eq
  have hcoset : (Sum.inr ((X.ofA (⟨mH, hmP1⟩ * p) : X.Universal) :
        X.Universal ⧸ X.ofB.range) : Vtx X) =
      Sum.inr ((X.ofA p' : X.Universal) : X.Universal ⧸ X.ofB.range) := by
    rw [Sum.inr.injEq, QuotientGroup.eq]
    have h : (X.ofA (⟨mH, hmP1⟩ * p))⁻¹ * X.ofA p' = X.ofA ⟨b₀, hb₀P1⟩ := by
      rw [hmp_eq, map_mul, map_mul, map_mul]
      group
    rw [h]
    exact hb₀B
  refine ⟨X.ofA ⟨mH, hmP1⟩, ?_, ?_⟩
  · exact Subgroup.mem_map_of_mem X.ofA (Subgroup.mem_subgroupOf.mpr hmO2)
  · rw [ofA_smul_inr X ⟨mH, hmP1⟩ p]
    exact hcoset

theorem f112ll_localL2_baseA {L1 L2 S : Subgroup H} {m : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (h1 : IsL2Quot m (oTwoQuot ↥L1)) :
    ∃ N : Subgroup ↥(f112EOdd L1 L2 S),
      IsLocL2 (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)
        (baseA (f112Gold L1 L2 S)) m N := by
  let E := f112EOdd L1 L2 S
  let X := f112Gold L1 L2 S
  let N : Subgroup ↥E := (f112llNlocalA L1 L2 S).subgroupOf E
  have hstab : MulAction.stabilizer ↥E (baseA X) =
      (f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofA.range).subgroupOf E := by
    rw [← MulAction.stabilizer_subgroupOf E (baseA X), stabilizer_baseA X,
      Subgroup.inf_subgroupOf_left]
  refine ⟨N, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hstab]
    exact Subgroup.subgroupOf_mono E f112llNlocalA_le_Nalpha
  · rw [hstab]
    refine Subgroup.normal_subgroupOf_of_le_normalizer ?_
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hkU : (k : X.Universal) ∈
        f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofA.range := Subgroup.mem_subgroupOf.mp hk
    constructor
    · intro hh
      rw [Subgroup.mem_subgroupOf] at hh ⊢
      exact (Subgroup.mem_normalizer_iff.mp (f112llNlocalA_normal_Nalpha hF hkU)
        (h : X.Universal)).mp hh
    · intro hh
      rw [Subgroup.mem_subgroupOf] at hh ⊢
      have hkU' : (k : X.Universal)⁻¹ ∈
          f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofA.range :=
        (f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofA.range).inv_mem hkU
      have hmem := (Subgroup.mem_normalizer_iff.mp (f112llNlocalA_normal_Nalpha hF hkU')
        ((k : X.Universal) * (h : X.Universal) * (k : X.Universal)⁻¹)).mp hh
      simpa [mul_assoc] using hmem
  · rw [hstab]
    intro y hy
    rw [Subgroup.mem_subgroupOf]
    have hpc := pCoreOf_subgroupOf_map
      (K := f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofA.range) (E := E) inf_le_left
    have hmem : (y : X.Universal) ∈
        (pCoreOf 2 ((f112EOdd L1 L2 S ⊓
          (f112Gold L1 L2 S).ofA.range).subgroupOf E)).map E.subtype :=
      Subgroup.mem_map_of_mem E.subtype hy
    rw [hpc] at hmem
    exact (show pCoreOf 2 (f112EOdd L1 L2 S ⊓
      (f112Gold L1 L2 S).ofA.range) ≤ f112llNlocalA L1 L2 S from le_sup_right) hmem
  · obtain ⟨e⟩ := f112llNlocalA_subgroupOf_quot hF hm h1
    exact ⟨e⟩
  · intro a b ha hb
    obtain ⟨g, hgMA, hgab⟩ := f112llMA_trans hF hm h1 a b ha hb
    refine ⟨⟨g, f112sa_oTwoRes_left_map_le_EOdd hgMA⟩, ?_, ?_⟩
    · show (⟨g, f112sa_oTwoRes_left_map_le_EOdd hgMA⟩ : ↥E) ∈ N
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_sup_left hgMA
    · show g • a = b
      exact hgab

end CFSG.Quasithin.F112R.St84

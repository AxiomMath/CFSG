module

public import CFSG.Quasithin.Recognition.St84.Gen.TreeLLA
import CFSG.Quasithin.Recognition.St84.Gen.OTwoResMul
import CFSG.Quasithin.Recognition.St84.Gen.L2RankOne
import CFSG.Quasithin.Recognition.St84.AppTreeE5

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Quasithin CFSG.Quasithin.Fan86 CFSG.Quasithin.Fan86.Univ
open scoped Pointwise

variable {H : Type} [Group H] [Finite H]

theorem f112ll_P1_eq_P1'_sup_S {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) :
    f112P1 L1 L2 S = f112saP1' L1 L2 S ⊔ S := by
  rw [f112sa_P1_eq_oTwoRes_sup_bigB hF, f112sa_bigB_eq_S_sup_K hF]
  have hX1 : f112saX1 L1 L2 S ≤ oTwoRes L1 := f112sa_X1_le_oTwoRes L1 L2 S
  calc oTwoRes L1 ⊔ (S ⊔ (f112saX1 L1 L2 S ⊔ f112saX2 L1 L2 S))
      = (oTwoRes L1 ⊔ S) ⊔ (f112saX1 L1 L2 S ⊔ f112saX2 L1 L2 S) :=
        (sup_assoc _ _ _).symm
    _ = ((oTwoRes L1 ⊔ S) ⊔ f112saX1 L1 L2 S) ⊔ f112saX2 L1 L2 S :=
        (sup_assoc _ _ _).symm
    _ = (oTwoRes L1 ⊔ S) ⊔ f112saX2 L1 L2 S := by
        rw [sup_eq_left.mpr (hX1.trans le_sup_left)]
    _ = oTwoRes L1 ⊔ (S ⊔ f112saX2 L1 L2 S) := sup_assoc _ _ _
    _ = oTwoRes L1 ⊔ (f112saX2 L1 L2 S ⊔ S) := by rw [sup_comm S (f112saX2 L1 L2 S)]
    _ = (oTwoRes L1 ⊔ f112saX2 L1 L2 S) ⊔ S := (sup_assoc _ _ _).symm

theorem f112ll_P2_eq_P2'_sup_S {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) :
    f112P2 L1 L2 S = f112saP2' L1 L2 S ⊔ S := by
  rw [f112sa_P2_eq_oTwoRes_sup_bigB hF, f112sa_bigB_eq_S_sup_K hF]
  have hX2 : f112saX2 L1 L2 S ≤ oTwoRes L2 := f112sa_X2_le_oTwoRes L1 L2 S
  calc oTwoRes L2 ⊔ (S ⊔ (f112saX1 L1 L2 S ⊔ f112saX2 L1 L2 S))
      = (oTwoRes L2 ⊔ S) ⊔ (f112saX1 L1 L2 S ⊔ f112saX2 L1 L2 S) :=
        (sup_assoc _ _ _).symm
    _ = (oTwoRes L2 ⊔ S) ⊔ (f112saX2 L1 L2 S ⊔ f112saX1 L1 L2 S) := by
        rw [sup_comm (f112saX1 L1 L2 S) (f112saX2 L1 L2 S)]
    _ = ((oTwoRes L2 ⊔ S) ⊔ f112saX2 L1 L2 S) ⊔ f112saX1 L1 L2 S :=
        (sup_assoc _ _ _).symm
    _ = (oTwoRes L2 ⊔ S) ⊔ f112saX1 L1 L2 S := by
        rw [sup_eq_left.mpr (hX2.trans le_sup_left)]
    _ = oTwoRes L2 ⊔ (S ⊔ f112saX1 L1 L2 S) := sup_assoc _ _ _
    _ = oTwoRes L2 ⊔ (f112saX1 L1 L2 S ⊔ S) := by rw [sup_comm S (f112saX1 L1 L2 S)]
    _ = (oTwoRes L2 ⊔ f112saX1 L1 L2 S) ⊔ S := (sup_assoc _ _ _).symm

private theorem f112ll_mem_of_odd_of_eq_sup_two {P P' T : Subgroup H}
    (hPP' : P' ≤ P) (hTP : T ≤ P) (hsup : P = P' ⊔ T) (hT : IsPGroup 2 T)
    (hPN : P ≤ Subgroup.normalizer (P' : Set H)) {x : H} (hx : x ∈ P)
    (hodd : Odd (orderOf x)) : x ∈ P' := by
  haveI hN : (P'.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPP').mpr hPN
  have hsup' : T.subgroupOf P ⊔ P'.subgroupOf P = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hTP hPP', sup_comm T P', ← hsup,
      Subgroup.subgroupOf_self]
  have hT' : IsPGroup 2 (T.subgroupOf P) :=
    hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTP).symm
  have hquot : IsPGroup 2 (↥P ⧸ P'.subgroupOf P) := by
    refine IsPGroup.of_surjective hT'
      ((QuotientGroup.mk' (P'.subgroupOf P)).comp (T.subgroupOf P).subtype) ?_
    intro y
    obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective (P'.subgroupOf P) y
    have hp : p ∈ T.subgroupOf P ⊔ P'.subgroupOf P := by
      rw [hsup']
      exact Subgroup.mem_top p
    obtain ⟨t, ht, n, hn, htn⟩ :=
      (Subgroup.mem_sup_of_normal_right (s := T.subgroupOf P)
        (t := P'.subgroupOf P)).mp hp
    refine ⟨⟨t, ht⟩, ?_⟩
    change QuotientGroup.mk' (P'.subgroupOf P) ((T.subgroupOf P).subtype ⟨t, ht⟩) =
      QuotientGroup.mk' (P'.subgroupOf P) p
    have hval : (T.subgroupOf P).subtype ⟨t, ht⟩ = t := rfl
    rw [hval, ← htn, map_mul]
    have hn1 : QuotientGroup.mk' (P'.subgroupOf P) n = 1 :=
      (QuotientGroup.eq_one_iff n).mpr hn
    rw [hn1, mul_one]
  have hmem : (⟨x, hx⟩ : ↥P) ∈ P'.subgroupOf P :=
    CFSG.QuasiDihedralFusion.mem_of_odd_orderOf_of_isPGroup_quotient _
      hquot (by rw [Subgroup.orderOf_mk]; exact hodd)
  exact Subgroup.mem_subgroupOf.mp hmem

theorem f112ll_mem_P1'_of_odd {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) {x : H}
    (hx : x ∈ f112P1 L1 L2 S) (hodd : Odd (orderOf x)) : x ∈ f112saP1' L1 L2 S :=
  f112ll_mem_of_odd_of_eq_sup_two
    (show f112saP1' L1 L2 S ≤ f112P1 L1 L2 S by
      rw [f112ll_P1_eq_P1'_sup_S hF]; exact le_sup_left)
    ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)
    (f112ll_P1_eq_P1'_sup_S hF) hF.1.h1.pgroup
    (f112sa_P1_le_normalizer_P1' hF) hx hodd

theorem f112ll_mem_P2'_of_odd {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) {x : H}
    (hx : x ∈ f112P2 L1 L2 S) (hodd : Odd (orderOf x)) : x ∈ f112saP2' L1 L2 S :=
  f112ll_mem_of_odd_of_eq_sup_two
    (show f112saP2' L1 L2 S ≤ f112P2 L1 L2 S by
      rw [f112ll_P2_eq_P2'_sup_S hF]; exact le_sup_left)
    ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)
    (f112ll_P2_eq_P2'_sup_S hF) hF.1.h1.pgroup
    (f112sa_P2_le_normalizer_P2' hF) hx hodd

private noncomputable def f112llMBpre {L1 L2 S : Subgroup H}
    (M : Subgroup ↥(f112EOdd L1 L2 S)) : Subgroup H :=
  ((((M ⊓ MulAction.stabilizer ↥(f112EOdd L1 L2 S)
        (baseB (f112Gold L1 L2 S))).map (f112EOdd L1 L2 S).subtype).comap
      (f112Gold L1 L2 S).ofB).map (f112P2 L1 L2 S).subtype)

private theorem f112llMBpre_le {L1 L2 S : Subgroup H}
    (M : Subgroup ↥(f112EOdd L1 L2 S)) :
    f112llMBpre (L1 := L1) (L2 := L2) (S := S) M ≤ f112P2 L1 L2 S :=
  Subgroup.map_subtype_le _

private theorem f112llMBpre_conj {L1 L2 S : Subgroup H}
    {M : Subgroup ↥(f112EOdd L1 L2 S)} (hMnorm : M.Normal) :
    oTwoRes L2 ≤ Subgroup.normalizer
      (f112llMBpre (L1 := L1) (L2 := L2) (S := S) M : Set H) := by
  let X := f112Gold L1 L2 S
  let E := f112EOdd L1 L2 S
  let Kβ : Subgroup ↥E := MulAction.stabilizer ↥E (baseB X)
  let Mβ : Subgroup ↥E := M ⊓ Kβ
  let Mβ' : Subgroup X.Universal := Mβ.map E.subtype
  let M₀' : Subgroup ↥(f112P2 L1 L2 S) := Mβ'.comap X.ofB
  let M₀ : Subgroup H := M₀'.map (f112P2 L1 L2 S).subtype
  have hM₀eq : f112llMBpre (L1 := L1) (L2 := L2) (S := S) M = M₀ := rfl
  rw [hM₀eq]
  have hMβ'_norm : ∀ g ∈ Kβ, ∀ u ∈ Mβ',
      (g : X.Universal) * u * (g : X.Universal)⁻¹ ∈ Mβ' := by
    intro g hg u hu
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hu
    have hconjM : g * m * g⁻¹ ∈ M := hMnorm.conj_mem m hm.1 g
    have hconjK : g * m * g⁻¹ ∈ Kβ :=
      Kβ.mul_mem (Kβ.mul_mem hg hm.2) (Kβ.inv_mem hg)
    exact Subgroup.mem_map_of_mem E.subtype (Subgroup.mem_inf.mpr ⟨hconjM, hconjK⟩)
  have hconj_gen : ∀ y ∈ oTwoRes L2, ∀ m ∈ M₀, y * m * y⁻¹ ∈ M₀ := by
    intro y hy m hm
    have hyP2 : y ∈ f112P2 L1 L2 S := Subgroup.mem_sup_left ((oTwoRes_le L2) hy)
    have hyMB : X.ofB ⟨y, hyP2⟩ ∈ f112saMB L1 L2 S :=
      Subgroup.mem_map_of_mem X.ofB (Subgroup.mem_subgroupOf.mpr hy)
    have hyE : X.ofB ⟨y, hyP2⟩ ∈ E := f112slMB_le_E hyMB
    have hyKβ : (⟨X.ofB ⟨y, hyP2⟩, hyE⟩ : ↥E) ∈ Kβ := by
      change (⟨X.ofB ⟨y, hyP2⟩, hyE⟩ : ↥E) ∈ MulAction.stabilizer ↥E (baseB X)
      rw [MulAction.mem_stabilizer_iff]
      show ((⟨X.ofB ⟨y, hyP2⟩, hyE⟩ : ↥E) : X.Universal) • baseB X = baseB X
      exact MulAction.mem_stabilizer_iff.mp (by
        rw [stabilizer_baseB X]
        exact ⟨⟨y, hyP2⟩, rfl⟩)
    obtain ⟨q, hqM₀', hqm⟩ := Subgroup.mem_map.mp hm
    have hqMβ' : X.ofB q ∈ Mβ' := Subgroup.mem_comap.mp hqM₀'
    have hconj' : X.ofB (⟨y, hyP2⟩ * q * ⟨y, hyP2⟩⁻¹) ∈ Mβ' := by
      have h := hMβ'_norm ⟨X.ofB ⟨y, hyP2⟩, hyE⟩ hyKβ (X.ofB q) hqMβ'
      have h' : X.ofB ⟨y, hyP2⟩ * X.ofB q * (X.ofB ⟨y, hyP2⟩)⁻¹ ∈ Mβ' := h
      rw [← map_inv, ← map_mul, ← map_mul] at h'
      exact h'
    have hq' : (⟨y, hyP2⟩ * q * ⟨y, hyP2⟩⁻¹) ∈ M₀' := Subgroup.mem_comap.mpr hconj'
    have hfin : ((⟨y, hyP2⟩ * q * ⟨y, hyP2⟩⁻¹ : ↥(f112P2 L1 L2 S)) : H) ∈ M₀ :=
      Subgroup.mem_map_of_mem _ hq'
    rw [← hqm]
    exact hfin
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro m
  constructor
  · exact hconj_gen y hy m
  · intro hm
    have h := hconj_gen y⁻¹ ((oTwoRes L2).inv_mem hy) (y * m * y⁻¹) hm
    simpa [mul_assoc] using h

private theorem f112llMBpre_mul {L1 L2 S : Subgroup H} (hR : Hyp111R L1 L2 S)
    {M : Subgroup ↥(f112EOdd L1 L2 S)}
    (hMtrans : EdgeTransitive (f112Gold L1 L2 S).treeGraph M) :
    ∀ x ∈ oTwoRes L2, ∃ m ∈ f112llMBpre (L1 := L1) (L2 := L2) (S := S) M,
      ∃ b ∈ bigB L1 L2 S, x = m * b := by
  let X := f112Gold L1 L2 S
  let E := f112EOdd L1 L2 S
  let Kβ : Subgroup ↥E := MulAction.stabilizer ↥E (baseB X)
  let Mβ : Subgroup ↥E := M ⊓ Kβ
  let Mβ' : Subgroup X.Universal := Mβ.map E.subtype
  let M₀' : Subgroup ↥(f112P2 L1 L2 S) := Mβ'.comap X.ofB
  let M₀ : Subgroup H := M₀'.map (f112P2 L1 L2 S).subtype
  have hM₀eq : f112llMBpre (L1 := L1) (L2 := L2) (S := S) M = M₀ := rfl
  rw [hM₀eq]
  have hMβ_transB : ∀ a b : Vtx X, X.treeGraph.Adj (baseB X) a →
      X.treeGraph.Adj (baseB X) b → ∃ g ∈ Mβ, g • a = b := by
    intro a b ha hb
    obtain ⟨g, hgM, hcase⟩ := hMtrans (baseB X) a (baseB X) b ha hb
    rcases hcase with ⟨hgβ, hgab⟩ | ⟨hgβ, hga⟩
    · exact ⟨g, ⟨hgM, MulAction.mem_stabilizer_iff.mpr hgβ⟩, hgab⟩
    · exfalso
      have hdist : X.treeGraph.dist (baseB X) (g • baseB X) = 1 := by
        rw [hgβ]
        exact SimpleGraph.dist_eq_one_iff_adj.mpr hb
      have heven := f112sa_preservesParts_E (L1 := L1) (L2 := L2) (S := S) (g := g)
        (baseB X)
      rw [hdist] at heven
      norm_num at heven
  have hXedgeB : X.edgeB =
      (f112P1 L1 L2 S ⊓ f112P2 L1 L2 S).subgroupOf (f112P2 L1 L2 S) := by
    change (Subgroup.inclusion inf_le_right).range = _
    exact Subgroup.inclusion_range inf_le_right
  intro x hx
  have hxP2 : x ∈ f112P2 L1 L2 S := Subgroup.mem_sup_left ((oTwoRes_le L2) hx)
  have hbaseA_adj : X.treeGraph.Adj (baseB X) (baseA X) := (adj_baseA_baseB X).symm
  have hxfixβ : X.ofB ⟨x, hxP2⟩ • baseB X = baseB X :=
    MulAction.mem_stabilizer_iff.mp (by
      rw [stabilizer_baseB X]
      exact ⟨⟨x, hxP2⟩, rfl⟩)
  have hxadj : X.treeGraph.Adj (baseB X) (X.ofB ⟨x, hxP2⟩ • baseA X) := by
    have h := (adj_smul X (X.ofB ⟨x, hxP2⟩) (baseB X) (baseA X)).2 hbaseA_adj
    rwa [hxfixβ] at h
  obtain ⟨g, hgMβ, hg⟩ := hMβ_transB (X.ofB ⟨x, hxP2⟩ • baseA X) (baseA X) hxadj hbaseA_adj
  have hgK : g ∈ Kβ := (Subgroup.mem_inf.mp hgMβ).2
  have hgrange : (g : X.Universal) ∈ X.ofB.range := by
    have hsub : g ∈ (MulAction.stabilizer X.Universal (baseB X)).subgroupOf E := by
      rwa [MulAction.stabilizer_subgroupOf]
    rw [stabilizer_baseB X] at hsub
    exact hsub
  obtain ⟨q, hq⟩ := hgrange
  let qx : ↥(f112P2 L1 L2 S) := q * ⟨x, hxP2⟩
  have hqx_def : qx = q * ⟨x, hxP2⟩ := rfl
  have hqx_fixA : X.ofB qx • baseA X = baseA X := by
    rw [hqx_def, map_mul, mul_smul, hq]
    exact hg
  have hqx_ofA : X.ofB qx ∈ X.ofA.range := by
    rw [← stabilizer_baseA X]
    exact MulAction.mem_stabilizer_iff.mpr hqx_fixA
  have hqx_edge : qx ∈ X.edgeB := (ofB_mem_ofA_range_iff X qx).1 hqx_ofA
  have hqx_bigB : (qx : H) ∈ bigB L1 L2 S := by
    rw [← f112_inf_eq_bigB_of_hyp111R hR]
    exact Subgroup.mem_subgroupOf.mp (hXedgeB ▸ hqx_edge)
  have hqM₀' : q ∈ M₀' := by
    rw [Subgroup.mem_comap, hq]
    exact Subgroup.mem_map_of_mem E.subtype hgMβ
  have hqM₀ : (q : H) ∈ M₀ := Subgroup.mem_map_of_mem _ hqM₀'
  refine ⟨(q : H)⁻¹, M₀.inv_mem hqM₀, (qx : H), hqx_bigB, ?_⟩
  rw [hqx_def]
  change x = (q : H)⁻¹ * ((q : H) * x)
  group

theorem f112ll_MB_le_of_edgeTransitive {L1 L2 S : Subgroup H} {n : ℕ}
    (hR : Hyp111R L1 L2 S) (hn : 2 ≤ n) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    {M : Subgroup ↥(f112EOdd L1 L2 S)} (hMnorm : M.Normal)
    (hMtrans : EdgeTransitive (f112Gold L1 L2 S).treeGraph M) :
    f112saMB L1 L2 S ≤ M.map (f112EOdd L1 L2 S).subtype := by
  let X := f112Gold L1 L2 S
  let E := f112EOdd L1 L2 S
  have hO2_le : oTwoRes L2 ≤ f112llMBpre (L1 := L1) (L2 := L2) (S := S) M :=
    f112_oTwoRes_le_of_le_mul hR hn h2 (f112llMBpre_le M) (f112llMBpre_conj hMnorm)
      (f112llMBpre_mul hR hMtrans)
  intro u hu
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hu
  have hxO2 : (x : H) ∈ oTwoRes L2 := Subgroup.mem_subgroupOf.mp hx
  have hxM₀ : (x : H) ∈ f112llMBpre (L1 := L1) (L2 := L2) (S := S) M := hO2_le hxO2
  obtain ⟨q, hq, hqx⟩ := Subgroup.mem_map.mp hxM₀
  have hq' : q = x := Subtype.ext hqx
  rw [hq'] at hq
  have hqM : X.ofB x ∈ ((M ⊓ MulAction.stabilizer ↥E (baseB X)).map E.subtype) :=
    Subgroup.mem_comap.mp hq
  exact (Subgroup.map_mono (f := E.subtype) inf_le_left) hqM

private noncomputable def f112llMApre {L1 L2 S : Subgroup H}
    (M : Subgroup ↥(f112EOdd L1 L2 S)) : Subgroup H :=
  ((((M ⊓ MulAction.stabilizer ↥(f112EOdd L1 L2 S)
        (baseA (f112Gold L1 L2 S))).map (f112EOdd L1 L2 S).subtype).comap
      (f112Gold L1 L2 S).ofA).map (f112P1 L1 L2 S).subtype)

private theorem f112llMApre_le {L1 L2 S : Subgroup H}
    (M : Subgroup ↥(f112EOdd L1 L2 S)) :
    f112llMApre (L1 := L1) (L2 := L2) (S := S) M ≤ f112P1 L1 L2 S :=
  Subgroup.map_subtype_le _

private theorem f112llMApre_conj {L1 L2 S : Subgroup H}
    {M : Subgroup ↥(f112EOdd L1 L2 S)} (hMnorm : M.Normal) :
    oTwoRes L1 ≤ Subgroup.normalizer
      (f112llMApre (L1 := L1) (L2 := L2) (S := S) M : Set H) := by
  let X := f112Gold L1 L2 S
  let E := f112EOdd L1 L2 S
  let Kα : Subgroup ↥E := MulAction.stabilizer ↥E (baseA X)
  let Mα : Subgroup ↥E := M ⊓ Kα
  let Mα' : Subgroup X.Universal := Mα.map E.subtype
  let M₀' : Subgroup ↥(f112P1 L1 L2 S) := Mα'.comap X.ofA
  let M₀ : Subgroup H := M₀'.map (f112P1 L1 L2 S).subtype
  have hM₀eq : f112llMApre (L1 := L1) (L2 := L2) (S := S) M = M₀ := rfl
  rw [hM₀eq]
  have hMα'_norm : ∀ g ∈ Kα, ∀ u ∈ Mα',
      (g : X.Universal) * u * (g : X.Universal)⁻¹ ∈ Mα' := by
    intro g hg u hu
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hu
    have hconjM : g * m * g⁻¹ ∈ M := hMnorm.conj_mem m hm.1 g
    have hconjK : g * m * g⁻¹ ∈ Kα :=
      Kα.mul_mem (Kα.mul_mem hg hm.2) (Kα.inv_mem hg)
    exact Subgroup.mem_map_of_mem E.subtype (Subgroup.mem_inf.mpr ⟨hconjM, hconjK⟩)
  have hconj_gen : ∀ y ∈ oTwoRes L1, ∀ m ∈ M₀, y * m * y⁻¹ ∈ M₀ := by
    intro y hy m hm
    have hyP1 : y ∈ f112P1 L1 L2 S := Subgroup.mem_sup_left ((oTwoRes_le L1) hy)
    have hyMA : X.ofA ⟨y, hyP1⟩ ∈ f112llMA L1 L2 S :=
      Subgroup.mem_map_of_mem X.ofA (Subgroup.mem_subgroupOf.mpr hy)
    have hyE : X.ofA ⟨y, hyP1⟩ ∈ E := f112sa_oTwoRes_left_map_le_EOdd hyMA
    have hyKα : (⟨X.ofA ⟨y, hyP1⟩, hyE⟩ : ↥E) ∈ Kα := by
      change (⟨X.ofA ⟨y, hyP1⟩, hyE⟩ : ↥E) ∈ MulAction.stabilizer ↥E (baseA X)
      rw [MulAction.mem_stabilizer_iff]
      show ((⟨X.ofA ⟨y, hyP1⟩, hyE⟩ : ↥E) : X.Universal) • baseA X = baseA X
      exact MulAction.mem_stabilizer_iff.mp (by
        rw [stabilizer_baseA X]
        exact ⟨⟨y, hyP1⟩, rfl⟩)
    obtain ⟨q, hqM₀', hqm⟩ := Subgroup.mem_map.mp hm
    have hqMα' : X.ofA q ∈ Mα' := Subgroup.mem_comap.mp hqM₀'
    have hconj' : X.ofA (⟨y, hyP1⟩ * q * ⟨y, hyP1⟩⁻¹) ∈ Mα' := by
      have h := hMα'_norm ⟨X.ofA ⟨y, hyP1⟩, hyE⟩ hyKα (X.ofA q) hqMα'
      have h' : X.ofA ⟨y, hyP1⟩ * X.ofA q * (X.ofA ⟨y, hyP1⟩)⁻¹ ∈ Mα' := h
      rw [← map_inv, ← map_mul, ← map_mul] at h'
      exact h'
    have hq' : (⟨y, hyP1⟩ * q * ⟨y, hyP1⟩⁻¹) ∈ M₀' := Subgroup.mem_comap.mpr hconj'
    have hfin : ((⟨y, hyP1⟩ * q * ⟨y, hyP1⟩⁻¹ : ↥(f112P1 L1 L2 S)) : H) ∈ M₀ :=
      Subgroup.mem_map_of_mem _ hq'
    rw [← hqm]
    exact hfin
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro m
  constructor
  · exact hconj_gen y hy m
  · intro hm
    have h := hconj_gen y⁻¹ ((oTwoRes L1).inv_mem hy) (y * m * y⁻¹) hm
    simpa [mul_assoc] using h

private theorem f112llMApre_mul {L1 L2 S : Subgroup H} (hR : Hyp111R L1 L2 S)
    {M : Subgroup ↥(f112EOdd L1 L2 S)}
    (hMtrans : EdgeTransitive (f112Gold L1 L2 S).treeGraph M) :
    ∀ x ∈ oTwoRes L1, ∃ m ∈ f112llMApre (L1 := L1) (L2 := L2) (S := S) M,
      ∃ b ∈ bigB L1 L2 S, x = m * b := by
  let X := f112Gold L1 L2 S
  let E := f112EOdd L1 L2 S
  let Kα : Subgroup ↥E := MulAction.stabilizer ↥E (baseA X)
  let Mα : Subgroup ↥E := M ⊓ Kα
  let Mα' : Subgroup X.Universal := Mα.map E.subtype
  let M₀' : Subgroup ↥(f112P1 L1 L2 S) := Mα'.comap X.ofA
  let M₀ : Subgroup H := M₀'.map (f112P1 L1 L2 S).subtype
  have hM₀eq : f112llMApre (L1 := L1) (L2 := L2) (S := S) M = M₀ := rfl
  rw [hM₀eq]
  have hMα_transA : ∀ a b : Vtx X, X.treeGraph.Adj (baseA X) a →
      X.treeGraph.Adj (baseA X) b → ∃ g ∈ Mα, g • a = b := by
    intro a b ha hb
    obtain ⟨g, hgM, hcase⟩ := hMtrans (baseA X) a (baseA X) b ha hb
    rcases hcase with ⟨hgα, hgab⟩ | ⟨hgα, hga⟩
    · exact ⟨g, ⟨hgM, MulAction.mem_stabilizer_iff.mpr hgα⟩, hgab⟩
    · exfalso
      have hdist : X.treeGraph.dist (baseA X) (g • baseA X) = 1 := by
        rw [hgα]
        exact SimpleGraph.dist_eq_one_iff_adj.mpr hb
      have heven := f112sa_preservesParts_E (L1 := L1) (L2 := L2) (S := S) (g := g)
        (baseA X)
      rw [hdist] at heven
      norm_num at heven
  have hXedgeA : X.edgeA =
      (f112P1 L1 L2 S ⊓ f112P2 L1 L2 S).subgroupOf (f112P1 L1 L2 S) := by
    change (Subgroup.inclusion inf_le_left).range = _
    exact Subgroup.inclusion_range inf_le_left
  intro x hx
  have hxP1 : x ∈ f112P1 L1 L2 S := Subgroup.mem_sup_left ((oTwoRes_le L1) hx)
  have hbaseB_adj : X.treeGraph.Adj (baseA X) (baseB X) := adj_baseA_baseB X
  have hxfixα : X.ofA ⟨x, hxP1⟩ • baseA X = baseA X :=
    MulAction.mem_stabilizer_iff.mp (by
      rw [stabilizer_baseA X]
      exact ⟨⟨x, hxP1⟩, rfl⟩)
  have hxadj : X.treeGraph.Adj (baseA X) (X.ofA ⟨x, hxP1⟩ • baseB X) := by
    have h := (adj_smul X (X.ofA ⟨x, hxP1⟩) (baseA X) (baseB X)).2 hbaseB_adj
    rwa [hxfixα] at h
  obtain ⟨g, hgMα, hg⟩ := hMα_transA (X.ofA ⟨x, hxP1⟩ • baseB X) (baseB X) hxadj hbaseB_adj
  have hgK : g ∈ Kα := (Subgroup.mem_inf.mp hgMα).2
  have hgrange : (g : X.Universal) ∈ X.ofA.range := by
    have hsub : g ∈ (MulAction.stabilizer X.Universal (baseA X)).subgroupOf E := by
      rwa [MulAction.stabilizer_subgroupOf]
    rw [stabilizer_baseA X] at hsub
    exact hsub
  obtain ⟨q, hq⟩ := hgrange
  let qx : ↥(f112P1 L1 L2 S) := q * ⟨x, hxP1⟩
  have hqx_def : qx = q * ⟨x, hxP1⟩ := rfl
  have hqx_fixB : X.ofA qx • baseB X = baseB X := by
    rw [hqx_def, map_mul, mul_smul, hq]
    exact hg
  have hqx_ofB : X.ofA qx ∈ X.ofB.range := by
    rw [← stabilizer_baseB X]
    exact MulAction.mem_stabilizer_iff.mpr hqx_fixB
  have hqx_edge : qx ∈ X.edgeA := (ofA_mem_ofB_range_iff X qx).1 hqx_ofB
  have hqx_bigB : (qx : H) ∈ bigB L1 L2 S := by
    rw [← f112_inf_eq_bigB_of_hyp111R hR]
    exact Subgroup.mem_subgroupOf.mp (hXedgeA ▸ hqx_edge)
  have hqM₀' : q ∈ M₀' := by
    rw [Subgroup.mem_comap, hq]
    exact Subgroup.mem_map_of_mem E.subtype hgMα
  have hqM₀ : (q : H) ∈ M₀ := Subgroup.mem_map_of_mem _ hqM₀'
  refine ⟨(q : H)⁻¹, M₀.inv_mem hqM₀, (qx : H), hqx_bigB, ?_⟩
  rw [hqx_def]
  change x = (q : H)⁻¹ * ((q : H) * x)
  group

theorem f112ll_MA_le_of_edgeTransitive {L1 L2 S : Subgroup H} {m : ℕ}
    (hR : Hyp111R L1 L2 S) (hm : 2 ≤ m) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    {M : Subgroup ↥(f112EOdd L1 L2 S)} (hMnorm : M.Normal)
    (hMtrans : EdgeTransitive (f112Gold L1 L2 S).treeGraph M) :
    f112llMA L1 L2 S ≤ M.map (f112EOdd L1 L2 S).subtype := by
  let X := f112Gold L1 L2 S
  let E := f112EOdd L1 L2 S
  have hM₀_le : f112llMApre (L1 := L1) (L2 := L2) (S := S) M ≤ L1 ⊔ bigB L2 L1 S := by
    rw [bigB_comm]
    exact f112llMApre_le M
  have hmul : ∀ x ∈ oTwoRes L1, ∃ mm ∈ f112llMApre (L1 := L1) (L2 := L2) (S := S) M,
      ∃ b ∈ bigB L2 L1 S, x = mm * b := by
    intro x hx
    obtain ⟨mm, hmm, b, hb, hmb⟩ := f112llMApre_mul hR hMtrans x hx
    exact ⟨mm, hmm, b, by rwa [bigB_comm], hmb⟩
  have hO2_le : oTwoRes L1 ≤ f112llMApre (L1 := L1) (L2 := L2) (S := S) M :=
    f112_oTwoRes_le_of_le_mul (L1 := L2) (L2 := L1) (S := S) hR.symm hm h1 hM₀_le
      (f112llMApre_conj hMnorm) hmul
  intro u hu
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hu
  have hxO2 : (x : H) ∈ oTwoRes L1 := Subgroup.mem_subgroupOf.mp hx
  have hxM₀ : (x : H) ∈ f112llMApre (L1 := L1) (L2 := L2) (S := S) M := hO2_le hxO2
  obtain ⟨q, hq, hqx⟩ := Subgroup.mem_map.mp hxM₀
  have hq' : q = x := Subtype.ext hqx
  rw [hq'] at hq
  have hqM : X.ofA x ∈ ((M ⊓ MulAction.stabilizer ↥E (baseA X)).map E.subtype) :=
    Subgroup.mem_comap.mp hq
  exact (Subgroup.map_mono (f := E.subtype) inf_le_left) hqM

theorem f112ll_EOdd_le_sup {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) :
    f112EOdd L1 L2 S ≤ f112llMA L1 L2 S ⊔ f112saMB L1 L2 S := by
  let X := f112Gold L1 L2 S
  rw [f112EOdd, Subgroup.closure_le]
  rintro u ⟨hu | hu, huodd⟩
  · obtain ⟨p, rfl⟩ := hu
    have hpP : (p : H) ∈ f112P1 L1 L2 S := p.2
    have hoddp : Odd (orderOf (p : H)) := by
      rw [Subgroup.orderOf_coe p, ← orderOf_injective X.ofA X.ofA_injective p]
      exact huodd
    have hp' : (p : H) ∈ f112saP1' L1 L2 S := f112ll_mem_P1'_of_odd hF hpP hoddp
    have hX2norm : f112saX2 L1 L2 S ≤ Subgroup.normalizer (oTwoRes L1 : Set H) :=
      (f112sa_X2_le_bigB L1 L2 S).trans (f112sa_bigB_le_normalizer_oTwoRes_left hF)
    have hmem : (p : H) ∈ (oTwoRes L1 : Set H) * (f112saX2 L1 L2 S : Set H) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left (oTwoRes L1)
        (f112saX2 L1 L2 S) hX2norm]
      exact hp'
    obtain ⟨a, ha, x, hx, hax⟩ := hmem
    have haP1 : a ∈ f112P1 L1 L2 S := Subgroup.mem_sup_left ((oTwoRes_le L1) ha)
    have hxP1 : x ∈ f112P1 L1 L2 S :=
      (le_sup_right : bigB L1 L2 S ≤ f112P1 L1 L2 S) (f112sa_X2_le_bigB L1 L2 S hx)
    have hxP2 : x ∈ f112P2 L1 L2 S :=
      (le_sup_right : bigB L1 L2 S ≤ f112P2 L1 L2 S) (f112sa_X2_le_bigB L1 L2 S hx)
    have hp_eq : p = ⟨a, haP1⟩ * ⟨x, hxP1⟩ := by
      apply Subtype.ext
      show (p : H) = a * x
      exact hax.symm
    have hMA : X.ofA ⟨a, haP1⟩ ∈ f112llMA L1 L2 S :=
      Subgroup.mem_map_of_mem X.ofA (Subgroup.mem_subgroupOf.mpr ha)
    have hMB : X.ofA ⟨x, hxP1⟩ ∈ f112saMB L1 L2 S := by
      have hxeq : X.ofA ⟨x, hxP1⟩ = X.ofB ⟨x, hxP2⟩ :=
        f112sa_ofA_eq_ofB_of_mem_inf L1 L2 S ⟨hxP1, hxP2⟩
      rw [hxeq]
      exact Subgroup.mem_map_of_mem X.ofB
        (Subgroup.mem_subgroupOf.mpr (f112sa_X2_le_oTwoRes L1 L2 S hx))
    rw [hp_eq, map_mul]
    exact Subgroup.mul_mem_sup hMA hMB
  · obtain ⟨p, rfl⟩ := hu
    have hpP : (p : H) ∈ f112P2 L1 L2 S := p.2
    have hoddp : Odd (orderOf (p : H)) := by
      rw [Subgroup.orderOf_coe p, ← orderOf_injective X.ofB X.ofB_injective p]
      exact huodd
    have hp' : (p : H) ∈ f112saP2' L1 L2 S := f112ll_mem_P2'_of_odd hF hpP hoddp
    have hX1norm : f112saX1 L1 L2 S ≤ Subgroup.normalizer (oTwoRes L2 : Set H) :=
      (f112sa_X1_le_bigB L1 L2 S).trans (f112sl_bigB_le_normalizer_oTwoRes hF)
    have hmem : (p : H) ∈ (oTwoRes L2 : Set H) * (f112saX1 L1 L2 S : Set H) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left (oTwoRes L2)
        (f112saX1 L1 L2 S) hX1norm]
      exact hp'
    obtain ⟨a, ha, x, hx, hax⟩ := hmem
    have haP2 : a ∈ f112P2 L1 L2 S := Subgroup.mem_sup_left ((oTwoRes_le L2) ha)
    have hxP1 : x ∈ f112P1 L1 L2 S :=
      (le_sup_right : bigB L1 L2 S ≤ f112P1 L1 L2 S) (f112sa_X1_le_bigB L1 L2 S hx)
    have hxP2 : x ∈ f112P2 L1 L2 S :=
      (le_sup_right : bigB L1 L2 S ≤ f112P2 L1 L2 S) (f112sa_X1_le_bigB L1 L2 S hx)
    have hp_eq : p = ⟨a, haP2⟩ * ⟨x, hxP2⟩ := by
      apply Subtype.ext
      show (p : H) = a * x
      exact hax.symm
    have hMB : X.ofB ⟨a, haP2⟩ ∈ f112saMB L1 L2 S :=
      Subgroup.mem_map_of_mem X.ofB (Subgroup.mem_subgroupOf.mpr ha)
    have hMA : X.ofB ⟨x, hxP2⟩ ∈ f112llMA L1 L2 S := by
      have hxeq : X.ofB ⟨x, hxP2⟩ = X.ofA ⟨x, hxP1⟩ :=
        (f112sa_ofA_eq_ofB_of_mem_inf L1 L2 S ⟨hxP1, hxP2⟩).symm
      rw [hxeq]
      exact Subgroup.mem_map_of_mem X.ofA
        (Subgroup.mem_subgroupOf.mpr (f112sa_X1_le_oTwoRes L1 L2 S hx))
    rw [hp_eq, map_mul, sup_comm]
    exact Subgroup.mul_mem_sup hMB hMA

theorem f112ll_minimality {L1 L2 S : Subgroup H} {m n : ℕ} (hF : F112HypW L1 L2 S)
    (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    ∀ M : Subgroup ↥(f112EOdd L1 L2 S), M.Normal →
      EdgeTransitive (f112Gold L1 L2 S).treeGraph M → M = ⊤ := by
  intro M hMnorm hMtrans
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  have hMA : f112llMA L1 L2 S ≤ M.map (f112EOdd L1 L2 S).subtype :=
    f112ll_MA_le_of_edgeTransitive hR hm h1 hMnorm hMtrans
  have hMB : f112saMB L1 L2 S ≤ M.map (f112EOdd L1 L2 S).subtype :=
    f112ll_MB_le_of_edgeTransitive hR hn h2 hMnorm hMtrans
  have hE : f112EOdd L1 L2 S ≤ M.map (f112EOdd L1 L2 S).subtype :=
    (f112ll_EOdd_le_sup hF).trans (sup_le hMA hMB)
  rw [eq_top_iff]
  intro m _
  have hmval : (m : (f112Gold L1 L2 S).Universal) ∈ M.map (f112EOdd L1 L2 S).subtype :=
    hE m.2
  obtain ⟨m', hm', hmm'⟩ := Subgroup.mem_map.mp hmval
  have hmeq : m' = m := Subtype.ext hmm'
  simpa [hmeq] using hm'

end CFSG.Quasithin.F112R.St84

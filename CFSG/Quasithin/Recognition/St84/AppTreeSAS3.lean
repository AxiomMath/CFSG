module

public import CFSG.Quasithin.Recognition.St84.AppTreeSA
public import CFSG.Quasithin.Recognition.St84.AppTreeL2

import CFSG.Quasithin.Background.F1VertexCore

public section

namespace CFSG.Quasithin.St84

open CFSG.Open

theorem pCoreOf_map_injective {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (hf : Function.Injective f) (X : Subgroup G) :
    pCoreOf 2 (X.map f) = (pCoreOf 2 X).map f := by
  have h := CFSG.Quasithin.Fan86.Univ.pCoreOf_range (f.comp X.subtype)
    (hf.comp X.subtype_injective)
  rw [MonoidHom.range_comp, Subgroup.range_subtype] at h
  rw [h, ← Subgroup.map_map]
  rfl

theorem pCoreOf_subgroupOf_sup_pCoreOf {G : Type*} [Group G] {M K : Subgroup G}
    (hMK : M ≤ K) (hnorm : K ≤ Subgroup.normalizer (M : Set G)) :
    pCoreOf 2 ((M ⊔ pCoreOf 2 K).subgroupOf K) = (pCoreOf 2 K).subgroupOf K := by
  have hsup : pCoreOf 2 (M ⊔ pCoreOf 2 K) = pCoreOf 2 K :=
    pCoreOf_sup_pCoreOf hMK hnorm
  have h1 : (pCoreOf 2 ((M ⊔ pCoreOf 2 K).subgroupOf K)).map K.subtype =
      pCoreOf 2 K := by
    rw [pCoreOf_subgroupOf_map (K := M ⊔ pCoreOf 2 K) (E := K)
      (sup_le hMK (CFSG.LieType.BorelTits.pCoreOf_le 2 K)), hsup]
  have h2 : ((pCoreOf 2 K).subgroupOf K).map K.subtype = pCoreOf 2 K :=
    Subgroup.map_subgroupOf_eq_of_le (CFSG.LieType.BorelTits.pCoreOf_le 2 K)
  exact (Subgroup.map_injective K.subtype_injective) (h1.trans h2.symm)

end CFSG.Quasithin.St84

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.Quasithin.St84
  CFSG.Quasithin.Fan86 CFSG.Quasithin.Fan86.Univ
open scoped Pointwise

variable {H : Type} [Group H] [Finite H]

@[expose] noncomputable def f112saNalpha (L1 L2 S : Subgroup H) :
    Subgroup (f112Gold L1 L2 S).Universal :=
  f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofA.range

@[expose] noncomputable def f112saLQ (L1 L2 S : Subgroup H) :
    Subgroup (f112Gold L1 L2 S).Universal :=
  ((L1 ⊔ pCoreOf 2 (f112P1 L1 L2 S)).subgroupOf (f112P1 L1 L2 S)).map
    (f112Gold L1 L2 S).ofA

@[expose] noncomputable def f112saQ1 (L1 L2 S : Subgroup H) :
    Subgroup (f112Gold L1 L2 S).Universal :=
  ((pCoreOf 2 (f112P1 L1 L2 S)).subgroupOf (f112P1 L1 L2 S)).map (f112Gold L1 L2 S).ofA

@[expose] noncomputable def f112saHalpha (L1 L2 S : Subgroup H) :
    Subgroup (f112Gold L1 L2 S).Universal :=
  f112saNalpha L1 L2 S ⊓ f112saLQ L1 L2 S

@[expose] noncomputable def f112saNlocalA (L1 L2 S : Subgroup H) :
    Subgroup (f112Gold L1 L2 S).Universal :=
  f112saHalpha L1 L2 S ⊔ pCoreOf 2 (f112saNalpha L1 L2 S)

theorem f112saLQ_le_range (L1 L2 S : Subgroup H) :
    f112saLQ L1 L2 S ≤ (f112Gold L1 L2 S).ofA.range :=
  Subgroup.map_le_range ((f112Gold L1 L2 S).ofA) _

theorem f112saQ1_le_LQ (L1 L2 S : Subgroup H) :
    f112saQ1 L1 L2 S ≤ f112saLQ L1 L2 S :=
  Subgroup.map_mono
    (Subgroup.subgroupOf_mono (f112P1 L1 L2 S) (le_sup_right : pCoreOf 2 _ ≤ _))

theorem f112saNalpha_le_range (L1 L2 S : Subgroup H) :
    f112saNalpha L1 L2 S ≤ (f112Gold L1 L2 S).ofA.range := inf_le_right

theorem f112saHalpha_le_Nalpha (L1 L2 S : Subgroup H) :
    f112saHalpha L1 L2 S ≤ f112saNalpha L1 L2 S := inf_le_left

theorem f112saHalpha_le_LQ (L1 L2 S : Subgroup H) :
    f112saHalpha L1 L2 S ≤ f112saLQ L1 L2 S := inf_le_right

theorem f112saNlocalA_le_Nalpha (L1 L2 S : Subgroup H) :
    f112saNlocalA L1 L2 S ≤ f112saNalpha L1 L2 S :=
  sup_le (f112saHalpha_le_Nalpha L1 L2 S) (CFSG.LieType.BorelTits.pCoreOf_le 2 _)

theorem f112saNlocalA_le_E (L1 L2 S : Subgroup H) :
    f112saNlocalA L1 L2 S ≤ f112EOdd L1 L2 S :=
  (f112saNlocalA_le_Nalpha L1 L2 S).trans inf_le_left

theorem f112sa_normal_subgroupOf {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) :
    ((L1 ⊔ pCoreOf 2 (f112P1 L1 L2 S)).subgroupOf (f112P1 L1 L2 S)).Normal := by
  have hP1L1 : f112P1 L1 L2 S ≤ Subgroup.normalizer (L1 : Set H) :=
    sup_le Subgroup.le_normalizer (bigB_le_normalizer_of_hyp111 hF.1)
  have hP1Q : f112P1 L1 L2 S ≤
      Subgroup.normalizer (pCoreOf 2 (f112P1 L1 L2 S) : Set H) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (f112P1 L1 L2 S)
  exact Subgroup.normal_subgroupOf_of_le_normalizer
    ((le_inf hP1L1 hP1Q).trans
      (Subgroup.inf_normalizer_le_normalizer_sup L1 (pCoreOf 2 (f112P1 L1 L2 S))))

theorem f112saLQ_normal_range {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) :
    ((f112saLQ L1 L2 S).subgroupOf (f112Gold L1 L2 S).ofA.range).Normal := by
  let X := f112Gold L1 L2 S
  refine ⟨fun x hx g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  show (g : X.Universal) * (x : X.Universal) * (g : X.Universal)⁻¹ ∈ f112saLQ L1 L2 S
  obtain ⟨b, hb, hxb⟩ := Subgroup.mem_map.mp hx
  obtain ⟨a, ha⟩ := g.2
  rw [← hxb, ← ha]
  have hconj : a * b * a⁻¹ ∈
      (L1 ⊔ pCoreOf 2 (f112P1 L1 L2 S)).subgroupOf (f112P1 L1 L2 S) :=
    (f112sa_normal_subgroupOf hF).conj_mem b hb a
  have heq : X.ofA a * X.ofA b * (X.ofA a)⁻¹ = X.ofA (a * b * a⁻¹) := by
    rw [map_mul, map_mul, map_inv]
  rw [heq]
  exact Subgroup.mem_map_of_mem _ hconj

theorem f112saLQ_le_normalizer_range {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) :
    (f112Gold L1 L2 S).ofA.range ≤
      Subgroup.normalizer (f112saLQ L1 L2 S : Set (f112Gold L1 L2 S).Universal) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (f112saLQ_le_range L1 L2 S)).mp
    (f112saLQ_normal_range hF)

theorem f112saQ1_normal_LQ {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) :
    ((f112saQ1 L1 L2 S).subgroupOf (f112saLQ L1 L2 S)).Normal := by
  let X := f112Gold L1 L2 S
  let P := f112P1 L1 L2 S
  let Q : Subgroup H := pCoreOf 2 P
  have hQn : P ≤ Subgroup.normalizer (Q : Set H) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P
  refine ⟨fun x hx g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  show (g : X.Universal) * (x : X.Universal) * (g : X.Universal)⁻¹ ∈ f112saQ1 L1 L2 S
  obtain ⟨b, hb, hxb⟩ := Subgroup.mem_map.mp hx
  obtain ⟨a, haK, hga⟩ := Subgroup.mem_map.mp g.2
  rw [← hxb, ← hga]
  have hconj : a * b * a⁻¹ ∈ Q.subgroupOf P := by
    rw [Subgroup.mem_subgroupOf]
    exact (Subgroup.mem_normalizer_iff.mp (hQn a.2) ((b : P) : H)).mp
      (Subgroup.mem_subgroupOf.mp hb)
  have heq : X.ofA a * X.ofA b * (X.ofA a)⁻¹ = X.ofA (a * b * a⁻¹) := by
    rw [map_mul, map_mul, map_inv]
  rw [heq]
  exact Subgroup.mem_map_of_mem _ hconj

theorem f112saLQ_le_normalizer_Q1 {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) :
    f112saLQ L1 L2 S ≤
      Subgroup.normalizer (f112saQ1 L1 L2 S : Set (f112Gold L1 L2 S).Universal) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (f112saQ1_le_LQ L1 L2 S)).mp
    (f112saQ1_normal_LQ hF)

theorem f112saHalpha_le_normalizer_Q1 {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) :
    f112saHalpha L1 L2 S ≤
      Subgroup.normalizer (f112saQ1 L1 L2 S : Set (f112Gold L1 L2 S).Universal) :=
  (f112saHalpha_le_LQ L1 L2 S).trans (f112saLQ_le_normalizer_Q1 hF)

theorem f112saNalpha_le_normalizer_Halpha {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) :
    f112saNalpha L1 L2 S ≤
      Subgroup.normalizer (f112saHalpha L1 L2 S : Set (f112Gold L1 L2 S).Universal) := by
  have hNLQ : f112saNalpha L1 L2 S ≤
      Subgroup.normalizer (f112saLQ L1 L2 S : Set (f112Gold L1 L2 S).Universal) :=
    (f112saNalpha_le_range L1 L2 S).trans (f112saLQ_le_normalizer_range hF)
  exact (le_inf Subgroup.le_normalizer hNLQ).trans
    (Subgroup.inf_normalizer_le_normalizer_inf
      (H := f112saNalpha L1 L2 S) (K := f112saLQ L1 L2 S))

theorem f112sa_pCoreOf_LQ {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) : pCoreOf 2 (f112saLQ L1 L2 S) = f112saQ1 L1 L2 S := by
  have hP1L1 : f112P1 L1 L2 S ≤ Subgroup.normalizer (L1 : Set H) :=
    sup_le Subgroup.le_normalizer (bigB_le_normalizer_of_hyp111 hF.1)
  have hbase : pCoreOf 2
      ((L1 ⊔ pCoreOf 2 (f112P1 L1 L2 S)).subgroupOf (f112P1 L1 L2 S)) =
      (pCoreOf 2 (f112P1 L1 L2 S)).subgroupOf (f112P1 L1 L2 S) :=
    pCoreOf_subgroupOf_sup_pCoreOf le_sup_left hP1L1
  have htra := pCoreOf_map_injective (f := (f112Gold L1 L2 S).ofA)
    (f112Gold L1 L2 S).ofA_injective
    ((L1 ⊔ pCoreOf 2 (f112P1 L1 L2 S)).subgroupOf (f112P1 L1 L2 S))
  change pCoreOf 2 (Subgroup.map (f112Gold L1 L2 S).ofA
    ((L1 ⊔ pCoreOf 2 (f112P1 L1 L2 S)).subgroupOf (f112P1 L1 L2 S))) = f112saQ1 L1 L2 S
  rw [htra, hbase]
  rfl

theorem f112sa_ofA_mem_Halpha {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) {y : H} (hyL : y ∈ L1) (hy3 : orderOf y = 3) :
    (f112Gold L1 L2 S).ofA ⟨y, Subgroup.mem_sup_left hyL⟩ ∈ f112saHalpha L1 L2 S := by
  let X := f112Gold L1 L2 S
  let y' : ↥(f112P1 L1 L2 S) := ⟨y, Subgroup.mem_sup_left hyL⟩
  have hy'3 : orderOf y' = 3 := by
    rw [Subgroup.orderOf_mk]
    exact hy3
  have hxE : X.ofA y' ∈ f112EOdd L1 L2 S := by
    refine Subgroup.subset_closure ⟨Or.inl ⟨y', rfl⟩, ?_⟩
    rw [orderOf_injective X.ofA X.ofA_injective y', hy'3]
    norm_num
  have hxU : X.ofA y' ∈ X.ofA.range := ⟨y', rfl⟩
  have hxLQ : X.ofA y' ∈ f112saLQ L1 L2 S :=
    Subgroup.mem_map_of_mem X.ofA
      (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hyL))
  exact Subgroup.mem_inf.mpr
    ⟨Subgroup.mem_inf.mpr ⟨hxE, hxU⟩, hxLQ⟩

theorem f112saLQ_quot_perm3 {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) :
    Nonempty (↥(f112saLQ L1 L2 S) ⧸ CFSG.pCore 2 ↥(f112saLQ L1 L2 S) ≃*
      Equiv.Perm (Fin 3)) := by
  let P := f112P1 L1 L2 S
  let Q : Subgroup H := pCoreOf 2 P
  let K : Subgroup ↥P := (L1 ⊔ Q).subgroupOf P
  have hP1L1 : P ≤ Subgroup.normalizer (L1 : Set H) :=
    sup_le Subgroup.le_normalizer (bigB_le_normalizer_of_hyp111 hF.1)
  have hKP : L1 ⊔ Q ≤ P := sup_le le_sup_left (CFSG.LieType.BorelTits.pCoreOf_le 2 P)
  obtain ⟨e1⟩ := pCore_quotient_mulEquiv_of_sup_pCoreOf_of_normal
    (M := L1) (K := P) le_sup_left hP1L1
  obtain ⟨e2⟩ := h1
  exact ⟨(pCoreQuotientMulEquiv 2
      (Subgroup.equivMapOfInjective K (f112Gold L1 L2 S).ofA
        (f112Gold L1 L2 S).ofA_injective)).symm.trans
    ((pCoreQuotientMulEquiv 2 (Subgroup.subgroupOfEquivOfLe hKP)).trans (e1.trans e2))⟩

theorem f112saQ1_relIndex_LQ {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) :
    (f112saQ1 L1 L2 S).relIndex (f112saLQ L1 L2 S) = 6 := by
  have hpc : (f112saQ1 L1 L2 S).subgroupOf (f112saLQ L1 L2 S) =
      CFSG.pCore 2 ↥(f112saLQ L1 L2 S) := by
    rw [← CFSG.openPCoreOf_subgroupOf 2 (f112saLQ L1 L2 S), f112sa_pCoreOf_LQ hF]
  rw [Subgroup.relIndex, hpc, Subgroup.index_eq_card]
  obtain ⟨e⟩ := f112saLQ_quot_perm3 hF h1
  exact (Nat.card_congr e.toEquiv).trans CFSG.Quasithin.F112W.perm3_card

end CFSG.Quasithin.F112R.St84

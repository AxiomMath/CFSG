module

public import CFSG.Quasithin.H13.GoldschmidtC137U33Ms2
public import CFSG.Quasithin.H13.GoldschmidtC137U33Ms1

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
  CFSG.LieType.BorelTits
open scoped Pointwise

variable {G : Type} [Group G]

theorem isE2_of_elemAbelian2 {W : Type} [CommGroup W] {B : Subgroup (MulAut W)}
    (hB : IsElemAbelian2 B) (hc : Nat.card ↥B = 2 ^ 3) : IsE2 3 ↥B := by
  letI : CommGroup ↥B := { (inferInstance : Group ↥B) with
    mul_comm := fun a b => Subtype.ext (hB.1 a a.2 b b.2) }
  haveI : Finite ↥B := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  exact S153E58.nonempty_mulEquiv_pi_of_sq_eq_one (fun w => Subtype.ext (hB.2 w w.2)) hc

namespace U33Cfg

variable [Finite G] {X T V L P M : Subgroup G} (h : U33Cfg X T V L P M)
  (E : Entry33 X T V L (pCoreOf 2 P) h.hVe)
  (hF : G2Facts (autI h.hVe X) (autI h.hVe L))
  {A : Subgroup (MulAut (IntMod V h.hVe))} (hA : PtA (autI h.hVe X) (autI h.hVe P) A)
include h E hF hA

theorem hPnS : P ≤ normalizer ((baum (pCoreOf 2 P) : Subgroup G) : Set G) :=
  (le_normalizer_pCoreOf 2 P).trans (normalizer_le_normalizer_baum _)

theorem A_normalized : ∀ p ∈ autI h.hVe P, ∀ a : MulAut (IntMod V h.hVe),
    a ∈ A ↔ p * a * p⁻¹ ∈ A := by
  intro p hp a
  obtain ⟨x, hxP, rfl⟩ := (mem_autI h.hVe).1 hp
  have hx := B2F.mem_normalizer_iff_cjSub_eq.1 (h.hPnS E hF hA hxP)
  have hmap := autI_cjSub h.hVe x.2 (baum (pCoreOf 2 P))
  rw [hx, autI_baum h E hA] at hmap
  constructor
  · intro ha
    have : (MulAut.conj (convI h.hVe x)).toMonoidHom a ∈ A.map
        (MulAut.conj (convI h.hVe x)).toMonoidHom := ⟨a, ha, rfl⟩
    rw [hmap] at this
    simpa using this
  · intro ha
    rw [← hmap] at ha
    obtain ⟨b, hb, hba⟩ := ha
    have : b = a := (MulAut.conj (convI h.hVe x)).injective (by simpa using hba)
    rwa [← this]

theorem phi_map_S :
    (((baum (pCoreOf 2 P)).subgroupOf (L ⊔ baum (pCoreOf 2 P))).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ baum (pCoreOf 2 P))))).map
        (h.phi E hF hA).toMonoidHom = A.subgroupOf (autI h.hVe X) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    have hgS : (g : G) ∈ baum (pCoreOf 2 P) := Subgroup.mem_subgroupOf.1 hg
    have h1 : ((h.phi E hF hA (QuotientGroup.mk g) : ↥(autI h.hVe X)) :
        MulAut (IntMod V h.hVe)) = convI h.hVe ⟨g, h.hG0N g.2⟩ := h.phi_mk E hF hA g
    show ((h.phi E hF hA (QuotientGroup.mk g) : ↥(autI h.hVe X)) :
        MulAut (IntMod V h.hVe)) ∈ A
    rw [h1, ← autI_baum h E hA]
    exact convI_mem_autI h.hVe hgS _
  · intro hy
    rw [← autI_baum h E hA] at hy
    obtain ⟨s, hsS, hsy⟩ := (mem_autI h.hVe).1 hy
    have hsG : (s : G) ∈ L ⊔ baum (pCoreOf 2 P) :=
      (le_sup_right : baum (pCoreOf 2 P) ≤ L ⊔ baum (pCoreOf 2 P)) hsS
    refine ⟨_, ⟨⟨s, hsG⟩, Subgroup.mem_subgroupOf.2 hsS, rfl⟩, ?_⟩
    refine Subtype.ext ?_
    exact (h.phi_mk E hF hA ⟨(s : G), hsG⟩).trans hsy

theorem clauseB_u33
    (hCV : IsSylowTwoOf (baum (pCoreOf 2 P) ⊓ centralizer (V : Set G))
      ((L ⊔ baum (pCoreOf 2 P)) ⊓ centralizer (V : Set G))) :
    baum (pCoreOf 2 P) ≤ L ⊔ baum (pCoreOf 2 P) ∧
      pCoreOf 2 (L ⊔ baum (pCoreOf 2 P)) ≤ baum (pCoreOf 2 P) ∧
      IsG2Two (↥(L ⊔ baum (pCoreOf 2 P)) ⧸ CFSG.pCore 2 ↥(L ⊔ baum (pCoreOf 2 P))) ∧
      ∃ P' : Subgroup (↥(L ⊔ baum (pCoreOf 2 P)) ⧸ CFSG.pCore 2 ↥(L ⊔ baum (pCoreOf 2 P))),
        IsMaxParabolic2 ⊤ P' ∧
        (((baum (pCoreOf 2 P)).subgroupOf (L ⊔ baum (pCoreOf 2 P))).map
          (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ baum (pCoreOf 2 P))))) ≤ P' ∧
        ((((baum (pCoreOf 2 P)).subgroupOf (L ⊔ baum (pCoreOf 2 P))).map
          (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ baum (pCoreOf 2 P))))).subgroupOf P').Normal ∧
        IsE2 3 ↥(((baum (pCoreOf 2 P)).subgroupOf (L ⊔ baum (pCoreOf 2 P))).map
          (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ baum (pCoreOf 2 P))))) := by
  set Φ := h.phi E hF hA with hΦ
  set SQ := ((baum (pCoreOf 2 P)).subgroupOf (L ⊔ baum (pCoreOf 2 P))).map
    (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ baum (pCoreOf 2 P)))) with hSQdef
  have hmapS : SQ.map Φ.toMonoidHom = A.subgroupOf (autI h.hVe X) := h.phi_map_S E hF hA
  have hSQ : SQ = (A.subgroupOf (autI h.hVe X)).map Φ.symm.toMonoidHom := by
    rw [← hmapS, map_map_symm]
  have hAP : A.subgroupOf (autI h.hVe X) ≤ (autI h.hVe P).subgroupOf (autI h.hVe X) := by
    intro y hy
    exact Subgroup.mem_subgroupOf.2 ((hA.le.trans (pCoreOf_le 2 _))
      (Subgroup.mem_subgroupOf.1 hy))
  refine ⟨le_sup_right, ?_, isG2Two_of_equiv Φ (h.isG2Two_Y E hF),
    ((autI h.hVe P).subgroupOf (autI h.hVe X)).map Φ.symm.toMonoidHom,
    isMaxParabolic2_of_equiv Φ (h.maxPar_Y E hF), ?_, ?_, ?_⟩
  · rw [h.pCoreOf_G0 E hF hA]
    have := eq_of_isSylowTwoOf_le hCV (inf_le_inf_right _ le_sup_right) le_rfl h.isPGroup_G0C
    rw [this]
    exact inf_le_left
  · rw [hSQ]
    exact Subgroup.map_mono hAP
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer (by rw [hSQ]; exact Subgroup.map_mono hAP)]
    intro y hy
    have hy' : Φ y ∈ (autI h.hVe P).subgroupOf (autI h.hVe X) := by
      simpa using Subgroup.mem_map_equiv.1 hy
    rw [Subgroup.mem_normalizer_iff]
    intro z
    rw [hSQ]
    simp only [Subgroup.mem_map_equiv, MulEquiv.symm_symm, map_mul, map_inv,
      Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact (h.A_normalized E hF hA (Φ y : MulAut (IntMod V h.hVe)) (Subgroup.mem_subgroupOf.1 hy')
      (Φ z : MulAut (IntMod V h.hVe)))
  · obtain ⟨e⟩ : IsE2 3 ↥A :=
      isE2_of_elemAbelian2 hA.off.2.2.1 (by rw [hA.card]; norm_num)
    let e1 : ↥SQ ≃* ↥(A.subgroupOf (autI h.hVe X)) :=
      (MulEquiv.subgroupCongr hSQ).trans
        ((A.subgroupOf (autI h.hVe X)).equivMapOfInjective Φ.symm.toMonoidHom
          Φ.symm.injective).symm
    exact ⟨(e1.trans (Subgroup.subgroupOfEquivOfLe hA.off.1)).trans e⟩

theorem isMSPair_u33
    (hn1 : ∀ C : Subgroup G, C ≤ baum (pCoreOf 2 P) → C ≠ ⊥ →
      (C.subgroupOf (baum (pCoreOf 2 P))).Characteristic → ¬ X ≤ normalizer (C : Set G))
    (hCV : IsSylowTwoOf (baum (pCoreOf 2 P) ⊓ centralizer (V : Set G))
      ((L ⊔ baum (pCoreOf 2 P)) ⊓ centralizer (V : Set G))) :
    IsMSPair (L ⊔ baum (pCoreOf 2 P)) (baum (pCoreOf 2 P)) ∧
      L ∈ cComp (L ⊔ baum (pCoreOf 2 P)) ∧
      ((L ⊔ baum (pCoreOf 2 P) : Subgroup G) : Set G) =
        (L : Set G) * (baum (pCoreOf 2 P) : Set G) := by
  have hPnR : P ≤ normalizer ((pCoreOf 2 P : Subgroup G) : Set G) := le_normalizer_pCoreOf 2 P
  have hPnS := h.hPnS E hF hA
  have hRT : pCoreOf 2 P ≤ T := h.toBaum.hRT
  have hSR : baum (pCoreOf 2 P) ≤ pCoreOf 2 P := inf_le_left
  have hST : baum (pCoreOf 2 P) ≤ T := hSR.trans hRT
  have hS2 : IsPGroup 2 ↥(baum (pCoreOf 2 P)) := h.hT.2.1.to_le hST
  have hSX : baum (pCoreOf 2 P) ≤ X := hST.trans h.hT.1
  have hSnL : baum (pCoreOf 2 P) ≤ normalizer (L : Set G) := hSX.trans h.hn
  have hTnL : T ≤ normalizer (L : Set G) := h.hT.1.trans h.hn
  have hTnS : T ≤ normalizer ((baum (pCoreOf 2 P) : Subgroup G) : Set G) := h.hTP.trans hPnS
  have hTnLS : T ≤ normalizer ((L ⊔ baum (pCoreOf 2 P) : Subgroup G) : Set G) :=
    B2F.le_normalizer_sup hTnL hTnS
  have hLnLS : L ≤ normalizer ((L ⊔ baum (pCoreOf 2 P) : Subgroup G) : Set G) :=
    le_sup_left.trans Subgroup.le_normalizer
  have hXnLS : X ≤ normalizer ((L ⊔ baum (pCoreOf 2 P) : Subgroup G) : Set G) := by
    intro x hx
    obtain ⟨l, hl, t, ht, rfl⟩ := h.hprod x hx
    exact Subgroup.mul_mem _ (hLnLS hl) (hTnLS ht)
  have hLS_set : ((L ⊔ baum (pCoreOf 2 P) : Subgroup G) : Set G) =
      (L : Set G) * (baum (pCoreOf 2 P) : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left L _ hSnL
  have hLcomp : L ∈ cComp (L ⊔ baum (pCoreOf 2 P)) :=
    mem_cComp_of_le_normal h.hL le_sup_left h.hG0X hXnLS (sup_le Subgroup.le_normalizer hSnL)
  refine ⟨⟨⟨CFSG.Quasithin.B5.sqtk_of_le h.hSQ h.hG0X, charTwo_sup_of_normalizes hS2 hSnL h.hL2,
    L, hLcomp, hLS_set, isRankTwoLie2Derived_u33 h.hlie⟩, Or.inr (h.clauseB_u33 E hF hA hCV), ?_⟩,
    hLcomp, hLS_set⟩
  intro C hCS hC0 hCchar hCn
  have hXC : X ≤ normalizer (C : Set G) := by
    intro x hx
    obtain ⟨l, hl, t, ht, rfl⟩ := h.hprod x hx
    refine Subgroup.mul_mem _ (hCn ((le_sup_left : L ≤ L ⊔ baum (pCoreOf 2 P)) hl)) ?_
    exact (normalizer_le_normalizer_of_characteristic_subgroupOf hCS hCchar) (hTnS ht)
  exact hn1 C hCS hC0 hCchar hXC

end U33Cfg

end CFSG.Quasithin.H13.U3.GC137

module

public import CFSG.Quasithin.H13.GoldschmidtC137U33Red
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.H13.GoldschmidtC137U33Frm
public import CFSG.Quasithin.H13.GoldschmidtC137U33Img
public import CFSG.Quasithin.H13.GoldschmidtC137U33Par

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
  CFSG.LieType.BorelTits

variable {G : Type} [Group G]

namespace U33Cfg

variable [Finite G] {X T V L P M : Subgroup G} (h : U33Cfg X T V L P M)
  (E : Entry33 X T V L (pCoreOf 2 P) h.hVe)
  (hF : G2Facts (autI h.hVe X) (autI h.hVe L))
include h E hF

theorem center_Y : Subgroup.center ↥(autI h.hVe X) = ⊥ := by
  ext y
  rw [Subgroup.mem_bot]
  constructor
  · intro hy
    have hcent : (y : MulAut (IntMod V h.hVe)) ∈ centralizer
        ((quasithinGenFitting (autI h.hVe X) : Subgroup (MulAut (IntMod V h.hVe))) :
          Set (MulAut (IntMod V h.hVe))) := by
      rw [E.fstarX, Subgroup.mem_centralizer_iff]
      intro φ hφ
      have := Subgroup.mem_center_iff.1 hy ⟨φ, autI_mono h.hVe h.hLX hφ⟩
      exact congrArg Subtype.val this
    have hyL : (y : MulAut (IntMod V h.hVe)) ∈ autI h.hVe L := by
      rw [← E.fstarX]
      exact centralizer_quasithinGenFitting_le (autI h.hVe X) ⟨y.2, hcent⟩
    have hc : (⟨y, hyL⟩ : ↥(autI h.hVe L)) ∈ Subgroup.center ↥(autI h.hVe L) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hgF : (g : MulAut (IntMod V h.hVe)) ∈ ((quasithinGenFitting (autI h.hVe X) :
          Subgroup (MulAut (IntMod V h.hVe))) : Set (MulAut (IntMod V h.hVe))) := by
        rw [SetLike.mem_coe, E.fstarX]
        exact g.2
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hcent g hgF)
    rw [center_autI_u33 h.hVe h.hLN h.hlie h.hkerL, Subgroup.mem_bot] at hc
    have h1 : (y : MulAut (IntMod V h.hVe)) = 1 := congrArg Subtype.val hc
    exact Subtype.ext h1
  · rintro rfl
    exact Subgroup.one_mem _

theorem isG2Two_Y : IsG2Two ↥(autI h.hVe X) := by
  refine ⟨hF.card_X, h.center_Y E hF, (autI h.hVe L).subgroupOf (autI h.hVe X), ?_, ?_, ?_⟩
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer (autI_mono h.hVe h.hLX)).2
      (autI_le_normalizer h.hVe h.hn)
  · have h1 := Subgroup.relIndex_mul_card (autI h.hVe L) (autI h.hVe X)
    rw [inf_eq_left.2 (autI_mono h.hVe h.hLX), E.card, hF.card_X] at h1
    show (autI h.hVe L).relIndex (autI h.hVe X) = 2
    omega
  · have hσs := C124.starHom_surjective h.hVe h.hLN
    have hk := C124.ker_starHom_eq_pCore h.hVe h.hLN h.hkerL
    let e : ↥((autI h.hVe L).subgroupOf (autI h.hVe X)) ≃* ↥L ⧸ CFSG.pCore 2 ↥L :=
      ((Subgroup.subgroupOfEquivOfLe (autI_mono h.hVe h.hLX)).trans
        (QuotientGroup.quotientKerEquivOfSurjective _ hσs).symm).trans
        (QuotientGroup.quotientMulEquivOfEq hk)
    exact isPSU_of_equiv e (isPSU_of_lieModel h.hlie)

theorem maxPar_Y : IsMaxParabolic2 (⊤ : Subgroup ↥(autI h.hVe X))
    ((autI h.hVe P).subgroupOf (autI h.hVe X)) := by
  have hT := h.sylow_T
  refine ⟨⟨le_top, (autI h.hVe T).subgroupOf (autI h.hVe X), ?_, ?_⟩, ?_, ?_⟩
  · refine ⟨le_top, hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm, ?_⟩
    show ¬ 2 ∣ ((autI h.hVe T).subgroupOf (autI h.hVe X)).relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact hT.2.2
  · intro y hy
    have hyT : (y : MulAut (IntMod V h.hVe)) ∈ normalizer
        ((autI h.hVe T : Subgroup (MulAut (IntMod V h.hVe))) : Set (MulAut (IntMod V h.hVe))) := by
      rw [Subgroup.mem_normalizer_iff]
      intro t
      by_cases htX : t ∈ autI h.hVe X
      · have := Subgroup.mem_normalizer_iff.1 hy.2 ⟨t, htX⟩
        simpa [Subgroup.mem_subgroupOf] using this
      · constructor
        · intro ht
          exact absurd (hT.1 ht) htX
        · intro ht
          refine absurd ?_ htX
          have h1 := hT.1 ht
          have := (autI h.hVe X).mul_mem
            ((autI h.hVe X).mul_mem ((autI h.hVe X).inv_mem y.2) h1) y.2
          simpa [mul_assoc] using this
    exact Subgroup.mem_subgroupOf.2 (h.T_le_P (hF.sylow_self _ hT ⟨y.2, hyT⟩))
  · intro htop
    apply h.P_ne_X
    apply le_antisymm h.P_le_X
    intro x hx
    have : (⟨x, hx⟩ : ↥(autI h.hVe X)) ∈ (autI h.hVe P).subgroupOf (autI h.hVe X) := by
      rw [htop]
      trivial
    exact this
  · intro Q' _ hQ'top hle
    have hPH : autI h.hVe P ≤ Q'.map (autI h.hVe X).subtype := fun p hp =>
      ⟨⟨p, h.P_le_X hp⟩, hle (Subgroup.mem_subgroupOf.2 hp), rfl⟩
    have hHX : Q'.map (autI h.hVe X).subtype ≤ autI h.hVe X := by
      rintro _ ⟨y, -, rfl⟩
      exact y.2
    have hQ' : Q' = (Q'.map (autI h.hVe X).subtype).subgroupOf (autI h.hVe X) :=
      (Subgroup.comap_map_eq_self_of_injective (autI h.hVe X).subtype_injective Q').symm
    rcases h.P_max _ hPH hHX with h3 | h3
    · rw [hQ', h3]
    · exfalso
      apply hQ'top
      rw [hQ', h3]
      exact Subgroup.subgroupOf_self _

end U33Cfg

end CFSG.Quasithin.H13.U3.GC137

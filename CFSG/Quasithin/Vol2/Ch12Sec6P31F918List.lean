module

public import CFSG.Milestones.ASVolI.F9
public import CFSG.Quasithin.Vol2.Ch12Sec6P31F918ListAux
public import CFSG.Quasithin.Vol2.Ch12Sec6P31SecFB
import all CFSG.Milestones.ASVolI.F9

public section

namespace CFSG.Quasithin.H13.P31F

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.RonanF918 CFSG.LieType.BorelTits
  S126 S126P31 F126
open CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

theorem exists_mul_of_mem_sup {G : Type} [Group G] {N F : Subgroup G}
    (hF : F ≤ Subgroup.normalizer (N : Set G)) {x : G} (hx : x ∈ N ⊔ F) :
    ∃ c ∈ N, ∃ f ∈ F, x = c * f := by
  let S : Subgroup G :=
    { carrier := {x | ∃ c ∈ N, ∃ f ∈ F, x = c * f}
      mul_mem' := by
        rintro _ _ ⟨c₁, hc₁, f₁, hf₁, rfl⟩ ⟨c₂, hc₂, f₂, hf₂, rfl⟩
        refine ⟨c₁ * (f₁ * c₂ * f₁⁻¹), N.mul_mem hc₁ ?_, f₁ * f₂, F.mul_mem hf₁ hf₂, by group⟩
        exact (Subgroup.mem_normalizer_iff.1 (hF hf₁) c₂).1 hc₂
      one_mem' := ⟨1, N.one_mem, 1, F.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨c, hc, f, hf, rfl⟩
        refine ⟨f⁻¹ * c⁻¹ * f⁻¹⁻¹, ?_, f⁻¹, F.inv_mem hf, by group⟩
        exact (Subgroup.mem_normalizer_iff.1 (hF (F.inv_mem hf)) c⁻¹).1 (N.inv_mem hc) }
  have hN : N ≤ S := fun c hc => ⟨c, hc, 1, F.one_mem, by simp⟩
  have hF' : F ≤ S := fun f hf => ⟨1, N.one_mem, f, hf, by simp⟩
  exact (sup_le hN hF') hx

section Setting

variable {G : Type} [Group G] {T V L V₁ Vp H K : Subgroup G}

theorem hypF_9_18_of (h : HypF918 T V L V₁ Vp H K) :
    CFSG.ASVolI.ChF.HypF_9_18 T V L V₁ Vp H K where
  toHypF98 := h.toHypF98
  K_cComp := h.K_cComp
  K_quasisimple := h.K_quasisimple
  H_product := fun x => by
    constructor
    · intro hx
      have hx' : x ∈ conjClosure K T ⊔ ((L ⊔ T) ⊓ H) := h.H_eq.le hx
      obtain ⟨c, hc, f, hf, rfl⟩ :=
        exists_mul_of_mem_sup ((inf_le_right : (L ⊔ T) ⊓ H ≤ H).trans h.K₀_normal) hx'
      exact ⟨c, f, hc, hf, rfl⟩
    · rintro ⟨c, f, hc, hf, rfl⟩
      exact H.mul_mem (h.K₀_le_H hc) hf.2

variable [Finite G] [IsMulCommutative ↥V]

theorem isSQTKCat_of_hypF918 (hH : Hyp126 G T L V) (h918 : HypF918 T V L V₁ Vp H K) :
    CFSG.SectionRank.IsSQTKCat ↥H := by
  have hSQTK : SQTKGroup ↥H :=
    sqtkGroup_of_pCoreOf_ne_bot hH.hyp.qtke hH.hyp.simple hH.hyp.nonabelian
      (pCoreOf_ne_bot h918.toHypF98.toHypF91)
  exact ⟨CFSG.SectionRank.isStronglyQuasithin_iff.2 hSQTK.1, hSQTK.2⟩

theorem nonempty_starEquivKst (h918 : HypF918 T V L V₁ Vp H K) :
    Nonempty (↥(S126.star H K) ≃* ↥(CFSG.ASVolI.ChF.KstOf V₁ (conjClosure Vp H) K)) := by
  have h := h918.toHypF98.toHypF91
  have hKH : K ≤ H := le_of_mem_cComp h918.K_cComp
  have hX : autOn (tildeOf V₁ K) (UT V₁ Vp H) = (S126.star H K).map (psiH h) := by
    rw [← range_thetaH h hKH, S126.star, Subgroup.map_map]
    rfl
  exact ⟨((MulEquiv.subgroupCongr hX).trans
    (Subgroup.equivMapOfInjective (S126.star H K) (psiH h) (psiH_injective h)).symm).symm⟩

end Setting

theorem f918List_w31_of (hF : CFSG.ASVolI.F_9_18) : F918List_w31 := by
  intro G _ _ T L V _ F hH hZ H K hIs h918
  have hKc : K ∈ cComp H := h918.K_cComp
  have hq : CFSG.IsQuasisimple ↥(S126.star H K) :=
    CFSG.Quasithin.H13.P31Sec.isQuasisimple_star hKc h918.K_quasisimple
  obtain ⟨e⟩ := nonempty_starEquivKst h918
  obtain ⟨⟨I, hI⟩, -, -, hall⟩ :=
    hF G T V L F.V1 F.V5 H K (hypF_9_18_of h918) (isSQTKCat_of_hypF918 hH h918)
  obtain ⟨-, -, h4, h5, -⟩ := hall I hI
  refine ⟨fun hK0 => ?_, fun hK0 => ?_⟩
  · rw [hK0]
    exact fourList_target e hq (h4 hK0.symm).1
  · exact fiveList_target e hq (h5 ⟨hK0, le_conjClosure K T⟩).1

end CFSG.Quasithin.H13.P31F

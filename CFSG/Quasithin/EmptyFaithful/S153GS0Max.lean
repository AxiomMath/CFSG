module

public import CFSG.Quasithin.EmptyFaithful.S153GCountIneq
public import CFSG.Quasithin.EmptyFaithful.S153GJS0

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

section Tools

variable {G : Type} [Group G]

private theorem s0m_mem_normalizer_commutator {g : G} {A B : Subgroup G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_commutator, hA, hB]

end Tools

section Containment

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

private theorem s0m_omegaOneCenter_le (h : Hyp15310 G T Mc M V₁ V₂ Yp t) :
    quasithinOmegaOneCenter T ≤ quasithinOmegaOneCenter (Sgp153 T V₁) := by
  unfold quasithinOmegaOneCenter
  refine Subgroup.closure_mono fun z hz => ?_
  have hzV : z ∈ VZ T M := le_conjClosure _ _ (Subgroup.subset_closure hz)
  exact ⟨⟨S153D.VZ_le_Sgp153 h hzV, Subgroup.centralizer_le (fun x hx => hx.1) hz.1.2⟩, hz.2⟩

private theorem s0m_le_S0 (hC : CountCentralizer) (c : Ctx15332 T Mc M V₁ V₂ Yp I L t)
    (cc : Concl15332 T M V₁ I L) :
    Sgp153 T V₁ ⊓ Subgroup.centralizer (UL153 T I L : Set G) ≤ S0153 T V₁ L ∧
      UL153 T I L ≤ S0153 T V₁ L := by
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t :=
    c.toCtx15331.toCtx15330.toCtx15328.toCtx15327.toCtx15325L
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c25.ctx.hyp
  have hF : Facts153 T M V₁ Yp I := c25.facts.toFacts153
  have hsyl : IsSylowTwoOf (Sgp153 T V₁) I := hF.sylow
  have hSI : Sgp153 T V₁ ≤ I := hsyl.1
  have hS2 : IsPGroup 2 (Sgp153 T V₁) := hsyl.2.1
  have hLI : L ≤ I := (le_of_mem_cComp c25.conc.1).trans (thompsonJ_le_self I)
  have hIL : I ≤ Subgroup.normalizer (L : Set G) := c.c27.normal
  have hIUI : I ≤ Subgroup.normalizer (UI153 T I : Set G) := le_normalizer_conjClosure _ I
  have hIU : I ≤ Subgroup.normalizer (UL153 T I L : Set G) := fun g hg =>
    s0m_mem_normalizer_commutator (hIUI hg) (hIL hg)
  have hIeq : I = L ⊔ Sgp153 T V₁ := c.I_eq
  have hOS : pCoreOf 2 I ≤ Sgp153 T V₁ := S153D.pCoreOf_le_Sgp153' hF
  have hOL : pCoreOf 2 I ≤ L ⊔ pCoreOf 2 (L ⊔ Sgp153 T V₁) := by
    rw [hIeq]
    exact le_sup_right
  have hOS₀ : pCoreOf 2 I ≤ S0153 T V₁ L := le_inf hOS hOL
  have hKS : I ⊓ Subgroup.centralizer (UL153 T I L : Set G) ≤ Sgp153 T V₁ :=
    hC G T Mc M V₁ V₂ Yp I L t c cc
  have hIK : I ≤ Subgroup.normalizer
      ((I ⊓ Subgroup.centralizer (UL153 T I L : Set G) : Subgroup G) : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hg, B2F.le_normalizer_centralizer hIU hg⟩
  have hK2 : IsPGroup 2 ↥(I ⊓ Subgroup.centralizer (UL153 T I L : Set G)) := hS2.to_le hKS
  have hKO : I ⊓ Subgroup.centralizer (UL153 T I L : Set G) ≤ pCoreOf 2 I :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left hIK hK2
  refine ⟨fun x hx => hOS₀ (hKO ⟨hSI hx.1, hx.2⟩), ?_⟩
  have hUUI : UL153 T I L ≤ UI153 T I :=
    (Subgroup.le_normalizer_iff_commutator_le_left (H := L) (K := UI153 T I)).mp
      (hLI.trans hIUI)
  obtain ⟨hle, -⟩ := conjClosure_le_centerOf_pCoreOf_of_sylowIn hsyl.1 hsyl.2.1 hsyl.2.2
    c25.ctx.charTwo (s0m_omegaOneCenter_le hh)
  exact (hUUI.trans (hle.trans inf_le_left)).trans hOS₀

end Containment

theorem countS0Max_of_inputs (hE : CountExists) (hU : CountSideU) (hUt : CountSideUt)
    (hC : CountCentralizer) : CountS0Max := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c cc t' ht'T ht'S hS0
  obtain ⟨A, hA⟩ := hE G T Mc M V₁ V₂ Yp I L t c cc
  obtain ⟨-, h1b, h1c⟩ := hU G T Mc M V₁ V₂ Yp I L t c cc A hA
  have h2 := hUt G T Mc M V₁ V₂ Yp I L t c cc t' ht'T ht'S A hA
  have h3 := countIneq_of_abstract G T Mc M V₁ V₂ Yp I L t c cc t' ht'T ht'S A hA.1
  have h0 : cm0 (P153 T M V₁) A = 2 := by
    rcases h1c with h | ⟨h, -⟩
    · omega
    · exact h
  have hbw := count_bw_of_equality c cc ht'T ht'S hA.1 (by omega)
  obtain ⟨hCS₀, hUS₀⟩ := s0m_le_S0 hC c cc
  refine ⟨_, hbw, sup_le ?_ (sup_le hUS₀ ?_)⟩
  · intro x hx
    exact hCS₀ ⟨hA.1.1 hx.1, Subgroup.centralizer_le
      (le_sup_left : UL153 T I L ≤ UL153 T I L ⊔ conjBy153 t' (UL153 T I L)) hx.2⟩
  · exact (Subgroup.map_mono hUS₀).trans hS0.le

end CFSG.Quasithin

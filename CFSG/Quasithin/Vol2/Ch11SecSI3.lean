module

public import CFSG.Quasithin.Vol2.Ch11SecSI2
public import CFSG.Quasithin.Vol2.Ch11SecSXK
public import CFSG.Quasithin.Vol2.Ch1Comm

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_lFamily_iff' {T B : Subgroup G} : B ∈ lFamily T ↔ B ∈ cComp (B ⊔ T) :=
  Iff.rfl

namespace StarHyp

variable {T L I V₁ V₂ X K : Subgroup G} {P₁ P₂ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)}

theorem exists_cComp_I (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hN : NatFacts) (h1102 : Stmt11_0_2) (h : StarHyp G T L I V₁ V₂ X K)
    (hc : CartanL L V₁ V₂ X) (hP : ParData T K (LOf L V₁) P₁ P₂)
    (hY : pCoreOf 2 (k0Of K P₂ ⊔ LOf L V₂ ⊔ X ⊔ T) ≠ ⊥) :
    ∃ I₀ : Subgroup G, I₀ ∈ cComp (k0Of K P₂ ⊔ LOf L V₂ ⊔ X ⊔ T) ∧
      T ≤ Subgroup.normalizer (I₀ : Set G) ∧ k0Of K P₂ ≤ I₀ ∧ LOf L V₂ ≤ I₀ ∧ X ≤ I₀ := by
  set Y := k0Of K P₂ ⊔ LOf L V₂ ⊔ X ⊔ T with hYdef
  have hTY : T ≤ Y := le_sup_right
  have hXY : X ≤ Y := le_sup_right.trans le_sup_left
  have hK₀Y : k0Of K P₂ ≤ Y := le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hL₂Y : LOf L V₂ ≤ Y := le_sup_right.trans (le_sup_left.trans le_sup_left)
  have hS := isSylowTwoOf_of_quasithinIsSylowTwo h.sylow hTY
  have hB₂ : LOf L V₂ ∈ lFamily T := lOf_mem_lFamily hN h1102 h.hyp h.v₂ (Or.inr rfl) le_rfl
  have hB₀ : k0Of K P₂ ∈ lFamily T := mem_lFamily_iff'.mpr (h.cComp_k0Of hP)
  obtain ⟨I₀, ⟨hI₀, hL₂I₀⟩, -⟩ := lemma_1_2_4_existsUnique h.hyp.fsu.qtke h.hyp.fsu.simple
    h.hyp.fsu.nonabelian h37 h39 hY hS hL₂Y hB₂
  obtain ⟨I₁, ⟨hI₁, hK₀I₁⟩, -⟩ := lemma_1_2_4_existsUnique h.hyp.fsu.qtke h.hyp.fsu.simple
    h.hyp.fsu.nonabelian h37 h39 hY hS hK₀Y hB₀
  have hn₀ := lemma_1_2_4_normal h.hyp.fsu.qtke h.hyp.fsu.simple h.hyp.fsu.nonabelian h37 h38
    hY hS hB₂ hL₂I₀ hI₀ h.T_le_normalizer_L₂
  have hn₁ := lemma_1_2_4_normal h.hyp.fsu.qtke h.hyp.fsu.simple h.hyp.fsu.nonabelian h37 h38
    hY hS hB₀ hK₀I₁ hI₁ (h.T_le_normalizer_k0Of hP)
  have hI₀Y := le_of_mem_cComp hI₀
  have hI₁Y := le_of_mem_cComp hI₁
  have hY₀ := (Subgroup.normal_subgroupOf_iff_le_normalizer hI₀Y).mp hn₀
  have hY₁ := (Subgroup.normal_subgroupOf_iff_le_normalizer hI₁Y).mp hn₁
  have hXK : X ⊓ LOf L V₁ ≤ I₁ := (h.cartan_inf_L₁_le_k0Of hP).trans hK₀I₁
  have heq : I₁ = I₀ := by
    by_contra hne
    have hlt : I₀ ⊓ I₁ < I₀ := by
      refine lt_of_le_of_ne inf_le_left fun h01 => hne ?_
      have hle : I₀ ≤ I₁ := inf_eq_left.mp h01
      by_contra hne'
      exact not_subnormal_of_mem_cComp hI₁ (lt_of_le_of_ne hle (Ne.symm hne'))
        (ne_bot_of_mem_cComp hI₀) (perfect_of_mem_cComp hI₀) (subnormal_of_mem_cComp hI₀)
    have hsub : IsSubnormal (I₀ ⊓ I₁) I₀ := by
      refine IsSubnormal.step inf_le_left ?_ (IsSubnormal.refl _)
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr fun x hx =>
        Subgroup.inf_normalizer_le_normalizer_inf
          ⟨Subgroup.le_normalizer hx, hY₁ (hI₀Y hx)⟩
    have hR := le_solvRad_of_subnormal_lt hI₀ hsub hlt
    refine h.cartan_inf_L₁_eq_bot hN h1102 hc (solvRad_isSolvable I₀)
      (fun l hl => normalizer_le_normalizer_solvRad I₀ (hY₀ (hL₂Y hl))) fun x hx l hl => hR ?_
    have hlI₀ := hL₂I₀ hl
    have hxI₁ := hXK hx
    refine ⟨?_, ?_⟩
    · exact I₀.mul_mem ((Subgroup.mem_normalizer_iff.mp (hY₀ (hXY hx.1)) l).mp hlI₀)
        (I₀.inv_mem hlI₀)
    · have h1 : l * x⁻¹ * l⁻¹ ∈ I₁ :=
        (Subgroup.mem_normalizer_iff.mp (hY₁ (hL₂Y hl)) x⁻¹).mp (I₁.inv_mem hxI₁)
      have h2 := I₁.mul_mem hxI₁ h1
      simpa [mul_assoc] using h2
  subst heq
  refine ⟨I₁, hI₀, fun t ht => hY₀ (hTY ht), hK₀I₁, hL₂I₀, ?_⟩
  exact hc.b.trans (sup_le hXK (inf_le_right.trans hL₂I₀))

end StarHyp

end CFSG.Quasithin.Vol2.Ch11.SecS

module

public import CFSG.Quasithin.Vol2.Ch11SecA11Setup
public import CFSG.Quasithin.Vol2.Ch1Comm
public import CFSG.Quasithin.Vol2.Ch1List

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G]

theorem eq_of_modO2Image_eq {H S B K : Subgroup G} (hS : QuasithinUnique.IsSylowTwoOf S H)
    (hKH : K ≤ H) (hBK : B ≤ K) (hK : ⁅K, K⁆ = K)
    (hSB : S ≤ Subgroup.normalizer (B : Set G)) (heq : modO2Image H B = modO2Image H K) :
    B = K := by
  refine (eq_of_le_sup_of_perfect hBK hK hS.2.1 hSB fun k hk => ?_).symm
  have hk' : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨k, hKH hk⟩ ∈ modO2Image H K :=
    ⟨⟨k, hKH hk⟩, hk, rfl⟩
  rw [← heq] at hk'
  obtain ⟨b, hb, hbk⟩ := hk'
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hbk
  have hs : ((b⁻¹ * ⟨k, hKH hk⟩ : ↥H) : G) ∈ S := pCore_two_le_subgroupOf hS hbk
  have hmem := Subgroup.mul_mem_sup (show (b : G) ∈ B from hb) hs
  simpa using hmem

variable {T L I : Subgroup G} {n i : ℕ} {Vi V₀ : Subgroup G}

theorem exists_cComp_1111 (hF : Facts11) (hN : NatFacts) (h1102 : Stmt11_0_2)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h312 : A312ForSQTK)
    (h : Hyp11 G T L I n) (hU : IsVi T L I n i Vi) (hc : Hyp1111 T i Vi V₀) :
    ∃ K : Subgroup G, K ∈ cComp (Subgroup.normalizer (V₀ : Set G)) ∧ LOf L Vi ≤ K ∧
      Subgroup.normalizer (V₀ : Set G) ≤ Subgroup.normalizer (K : Set G) ∧
      (LOf L Vi = K ∨
        A312Case (modO2Image (Subgroup.normalizer (V₀ : Set G)) (LOf L Vi))
          (modO2Image (Subgroup.normalizer (V₀ : Set G)) K) ∨
        A312Nonquasi (modO2Image (Subgroup.normalizer (V₀ : Set G)) (LOf L Vi))
          (modO2Image (Subgroup.normalizer (V₀ : Set G)) K)) := by
  have hS := hc.sylow h hU
  have hH := hc.pCoreOf_ne_bot h hU
  have hBH := hc.lOf_le hF h1102 h hU
  have hB := lOf_mem_lFamily hN h1102 h hU hc.i_cases
    (inf_le_left : T ⊓ Subgroup.normalizer (V₀ : Set G) ≤ T)
  obtain ⟨K, ⟨hK, hBK⟩, -⟩ := CFSG.Quasithin.lemma_1_2_4_existsUnique h.fsu.qtke h.fsu.simple
    h.fsu.nonabelian h37 h39 hH hS hBH hB
  have hSB : T ⊓ Subgroup.normalizer (V₀ : Set G) ≤ Subgroup.normalizer (LOf L Vi : Set G) :=
    inf_le_left.trans (T_le_normalizer_lOf h.normal (IsVi.le_normalizer hU))
  have hnorm := CFSG.Quasithin.lemma_1_2_4_normal h.fsu.qtke h.fsu.simple h.fsu.nonabelian h37
    h38 hH hS hB hBK hK hSB
  have hKH := le_of_mem_cComp hK
  refine ⟨K, hK, hBK, (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp hnorm, ?_⟩
  rcases CFSG.Quasithin.lemma_1_2_4_list h.fsu.qtke h.fsu.simple h.fsu.nonabelian h312 hH hS
    hBH hB hK hBK with heq | h2 | h3
  · exact Or.inl (eq_of_modO2Image_eq hS hKH hBK (perfect_of_mem_cComp hK) hSB heq)
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h3)

end CFSG.Quasithin.Vol2.Ch11.SecA

module

public import CFSG.Quasithin.Vol2.Ch11SecBBasic
public import CFSG.Quasithin.Vol2.Ch11SecAVi2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem concl11_3_2_of_wClos_le (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3)
    (h1122 : Stmt11_2_2) (h1123 : Stmt11_2_3) (h1125 : Stmt11_2_5) (hyp : Hyp11 G T L I n)
    {V₁ V₂ H : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) (hV₂ : IsVi T L I n 2 V₂)
    (hV12 : V₁ ≤ V₂) (h31 : Hyp11_3_1 T L I n V₁ H)
    (hW : E3.wClos (fsuV T I) 0 T ≤ pCoreOf 2 H) : Concl11_3_2 T L I n V₁ H := by
  have hHM : ¬ H ≤ Subgroup.normalizer (L : Set G) := h31.hstar.2.1
  have hsl3 : KindSL3 L (fsuV T I) n →
      Subgroup.centralizer (V₂ : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    fun hk => (Subgroup.centralizer_le hV12).trans (h31.sl3 hk)
  have hnab := (h1125 G T L I n V₁ V₂ H hyp hV₁ hV₂ h31.hstar.1 hHM hsl3).resolve_left
    (not_not.mpr hW)
  have hNV : ¬ Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    fun hle => hnab (isMulCommutative_conjClosure h1103 hyp hV₁ hle)
  have h2 : ¬ Subgroup.centralizer (V₁ : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    fun hC => hNV ((h1123 G T L I n V₁ hyp hV₁).2 hC)
  have h3 := inf_centralizer_eq_bot h331 hyp hV₁ h2
  have h4 : ¬ IsMulCommutative ↥(conjClosure (fsuV T I)
      (Subgroup.centralizer (V₁ : Set G))) := fun hab =>
    hnab (isMulCommutative_of_le (conjClosure_normalizer_le h1103 h1123 hyp hV₁ h3) hab)
  refine ⟨?_, h2, h3, fun _ => h4⟩
  rcases SecA.kind_cases h1102 hyp with hk | hk | hk
  · exact absurd (h31.sl3 hk) h2
  · exact hk
  · exfalso
    have h5 := (h1122 G T L I n (2 * n) V₁ V₂ hyp hV₁ hV₂ (Or.inl ⟨hk, rfl⟩)).2.2.2.2.2.1 hk
    exact hHM ((le_normalizer_wClos hyp.fsu.sylow h31.hstar.1.1 hW).trans h5.2.1)

theorem stmt11_3_3_of (hF : SecA.NatFacts) (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2)
    (h1103 : Stmt11_0_3) (h1122 : Stmt11_2_2) (h1123 : Stmt11_2_3) (h1125 : Stmt11_2_5) :
    Stmt11_3_3 := by
  intro G _ _ T L I n V₁ H hyp hV₁ h31 hnot hW
  obtain ⟨-, V₂, -, -, hV₂, -⟩ := SecA.exists_isVi hF h1102 hyp
  exact hnot (concl11_3_2_of_wClos_le h331 h1102 h1103 h1122 h1123 h1125 hyp hV₁ hV₂
    (SecA.IsVi.mono₁₂ hF h1102 hyp hV₁ hV₂) h31 hW)

end CFSG.Quasithin.Vol2.Ch11.SecB

module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront07
import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

private lemma le_derInf_of_perfect_T2J6a {G : Type} [Group G] [Finite G]
    {X L : Subgroup G} (hLX : L ≤ X) (hLperf : ⁅L, L⁆ = L) : L ≤ F07.DerInf X :=
  uc22p21c_le_Hinf hLX hLperf

private lemma derInf_le_of_le_T2J6a {G : Type} [Group G] [Finite G]
    {P X : Subgroup G} (hXP : X ≤ P) : F07.DerInf X ≤ F07.DerInf P :=
  uc22p21c_le_Hinf ((uc22p21c_Hinf_le X).trans hXP) (uc22p21c_Hinf_perfect X)

private lemma pCore_quot_eq_bot_of_equiv_T2J6a {A T : Type} [Group A] [Group T]
    (hT : CFSG.pCore 2 T = ⊥) (e : A ⧸ CFSG.pCore 2 A ≃* T) :
    CFSG.pCore 2 (A ⧸ CFSG.pCore 2 A) = ⊥ := by
  have h := CFSG.pCore_map_iso 2 e
  rw [hT] at h
  exact (Subgroup.map_eq_bot_iff_of_injective
    (H := CFSG.pCore 2 (A ⧸ CFSG.pCore 2 A)) e.injective).1 h

private lemma isPGroup_ker_mk'_comp_T2J6a {C A : Type} [Group C] [Group A]
    {N : Subgroup C} [N.Normal] {p : ℕ} (f : A →* C) (hf : Function.Injective f)
    (hN : IsPGroup p N) : IsPGroup p ((QuotientGroup.mk' N).comp f).ker := by
  have hker_eq : ((QuotientGroup.mk' N).comp f).ker = N.comap f := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  rw [hker_eq]
  exact hN.comap_of_injective f hf

private lemma pCore_eq_ker_of_surjective_T2J6a {A B : Type} [Group A] [Group B]
    (ψ : A →* B) (hψ : Function.Surjective ψ) (hker : IsPGroup 2 ψ.ker)
    (hB : CFSG.pCore 2 B = ⊥) : CFSG.pCore 2 A = ψ.ker := by
  refine le_antisymm ?_ ?_
  · have hle : (CFSG.pCore 2 A).map ψ ≤ CFSG.pCore 2 B :=
      le_sSup ⟨Subgroup.Normal.map (CFSG.pCore_normal (p := 2) (G := A)) ψ hψ,
        IsPGroup.map (CFSG.pCore_isPGroup (p := 2) (G := A)) ψ⟩
    rw [hB] at hle
    exact (Subgroup.map_eq_bot_iff (H := CFSG.pCore 2 A)).1 (le_bot_iff.1 hle)
  · exact le_sSup ⟨inferInstance, hker⟩

theorem nonempty_bar2_derInf_equiv_of_levi {G T : Type} [Group G] [Finite G] [Group T]
    {P L X : Subgroup G} (hLX : L ≤ X) (hXP : X ≤ P) (hLperf : ⁅L, L⁆ = L)
    (hLcore : CFSG.pCore 2 ↥L = ⊥) (hT : CFSG.pCore 2 T = ⊥) (hcard : Nat.card L = Nat.card T)
    (e : Bar2 (F07.DerInf P) ≃* T) : Nonempty (Bar2 (F07.DerInf X) ≃* T) := by
  have hLE : L ≤ F07.DerInf X := le_derInf_of_perfect_T2J6a hLX hLperf
  have hED : F07.DerInf X ≤ F07.DerInf P := derInf_le_of_le_T2J6a hXP
  have hquot : CFSG.pCore 2 (Bar2 (F07.DerInf P)) = ⊥ :=
    pCore_quot_eq_bot_of_equiv_T2J6a hT e
  let φ : ↥L →* Bar2 (F07.DerInf P) :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥(F07.DerInf P))).comp
      ((Subgroup.inclusion hED).comp (Subgroup.inclusion hLE))
  have hφ_inj : Function.Injective φ := by
    have hinc : Function.Injective
        ((Subgroup.inclusion hED).comp (Subgroup.inclusion hLE)) :=
      (Subgroup.inclusion_injective hED).comp (Subgroup.inclusion_injective hLE)
    have hkerP : IsPGroup 2 φ.ker :=
      isPGroup_ker_mk'_comp_T2J6a ((Subgroup.inclusion hED).comp (Subgroup.inclusion hLE))
        hinc (CFSG.pCore_isPGroup (p := 2) (G := ↥(F07.DerInf P)))
    have hle : φ.ker ≤ CFSG.pCore 2 ↥L := le_sSup ⟨inferInstance, hkerP⟩
    rw [hLcore] at hle
    exact φ.ker_eq_bot_iff.mp (le_bot_iff.mp hle)
  have hcardD : Nat.card (Bar2 (F07.DerInf P)) = Nat.card T := Nat.card_congr e.toEquiv
  have hφ_bij : Function.Bijective φ :=
    hφ_inj.bijective_of_nat_card_le (le_of_eq (hcardD.trans hcard.symm))
  have hφ_surj : Function.Surjective φ := hφ_bij.2
  let ψ : ↥(F07.DerInf X) →* Bar2 (F07.DerInf P) :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥(F07.DerInf P))).comp (Subgroup.inclusion hED)
  have hφ_eq : φ = ψ.comp (Subgroup.inclusion hLE) :=
    (MonoidHom.comp_assoc (Subgroup.inclusion hLE) (Subgroup.inclusion hED)
      (QuotientGroup.mk' (CFSG.pCore 2 ↥(F07.DerInf P)))).symm
  have hψ_surj : Function.Surjective ψ := by
    intro y
    obtain ⟨x, hx⟩ := hφ_surj y
    refine ⟨Subgroup.inclusion hLE x, ?_⟩
    change (ψ.comp (Subgroup.inclusion hLE)) x = y
    rw [← hφ_eq]
    exact hx
  have hψkerP : IsPGroup 2 ψ.ker :=
    isPGroup_ker_mk'_comp_T2J6a (Subgroup.inclusion hED) (Subgroup.inclusion_injective hED)
      (CFSG.pCore_isPGroup (p := 2) (G := ↥(F07.DerInf P)))
  have hcoreE : CFSG.pCore 2 ↥(F07.DerInf X) = ψ.ker :=
    pCore_eq_ker_of_surjective_T2J6a ψ hψ_surj hψkerP hquot
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hcoreE).trans
    ((QuotientGroup.quotientKerEquivOfSurjective ψ hψ_surj).trans e)⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

end

module

public import CFSG.LocalAnalysis.StandardType.GGOrthWeakFrameOfMarking
public import CFSG.LocalAnalysis.StandardType.GGSecFivePumpBstar
import CFSG.LocalAnalysis.StandardType.GGResOrthogonalExactTwo

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly

variable {G : Type} [Group G] [Finite G]


theorem qtwoDU5_frameCore_D4 (hRig : GGLabelRigidInput) {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J) (hlt : B < Bs) {K : Subgroup G}
    (hmark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.D, 4, 1⟩) 3 Bs K)
    (hact : ∀ hN : Bs ≤ Subgroup.normalizer (K : Set G), ∃ b : ↥Bs, ggGamma K hN b ≠ 1) :
    ∃ Φ : OrthTorus.OrthFrameCore 3 Bs K, Nat.card Φ.F = 2 ∧ Φ.r = 4 ∧
      Subgroup.center ↥K = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hmarkK : GGInnerDiagOn Bs K :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.2) hmark
  have hN : Bs ≤ Subgroup.normalizer (K : Set G) := GGInnerDiagOn.le_normalizer hmarkK
  have hodd := hcfg.odd_card_center_of_B_lt_Bs hlt hN
  have hZK : ∀ lab : LargeEvenLabel, lab = ⟨.D, 4, 1⟩ →
      GGHasLabel lab (↥K ⧸ Subgroup.center ↥K) → Subgroup.center ↥K = ⊥ := by
    rintro lab rfl hhas
    have h1 : Nat.card ↥(Subgroup.center ↥K) = 1 := by
      by_contra h1
      obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd h1
      have hq2 : q ≠ 2 := by
        rintro rfl
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hqd)
      exact OrthKExactTwo.center_not_dvd_of_orthogonal_marking hq hq2 hmarkK hhas
        (Or.inl rfl) (le_refl 4) hqd
    exact Subgroup.eq_bot_of_card_eq _ h1
  obtain ⟨lab, hP, hhas, Φ, hr, hF, -⟩ :=
    OrthTorus.exists_orthFrameCore_of_marking hRig (by norm_num) hBs hSC
      (P := fun _ lab => lab = ⟨.D, 4, 1⟩)
      (fun lab hl => Or.inl (by subst hl; exact ⟨rfl, le_refl 4, ⟨2, rfl⟩, by norm_num⟩))
      hmark hZK hact
  subst hP
  exact ⟨Φ, by rw [hF]; norm_num, hr, hZK _ rfl hhas⟩

end CFSG.StandardType.QTwo

end

module

public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourR3Comm
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourRk2OmegaComm
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourRk2Cross
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomy
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem

section Inputs

theorem exists_r3comm_mixed_of_tableBPos_POmegaMinus {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs L K : Subgroup G} {x : G} (hpp : p.Prime) (hp2 : p ≠ 2) (hEl : IsElemAbelian p Bs)
    (hNT : GGNoTransvection p Bs) (hx : x ∈ Bs)
    (hL : IsSubnormal L (Subgroup.centralizer ({x} : Set G)))
    (hBL : Bs ≤ Subgroup.normalizer (L : Set G))
    {e : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)}
    (hpres : GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e)
    {f : ℕ} (hf : 2 ≤ f) (hpos : GGTableBPosImage p Bs .POmegaMinus 4 f L)
    (w w' : CoxeterMatrix.F₄.Group) (i j : Fin 4) (hij : i.val < 2 ↔ 2 ≤ j.val)
    {u r' : MulAut ↥Bs}
    (hu : u = ((e (w * CoxeterMatrix.F₄.simple i * w⁻¹) :
      ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs))
    (hr' : r' = ((e (w' * CoxeterMatrix.F₄.simple j * w'⁻¹) :
      ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs))
    (huL : u ∈ ggAutomizer L Bs) (hcomm : u * r' = r' * u) :
    ∃ n ∈ L ⊔ K, n ∈ Subgroup.normalizer (Bs : Set G) ∧
      (∀ b : ↥Bs, ((r' b : ↥Bs) : G) = n * b * n⁻¹) ∧
      n ∈ Subgroup.centralizer (ggRankOneIn L Bs u : Set G) := by
  have hfam := ggF4OriginalRankOneFamily_of_tableBPosImage hpp hp2 hEl hNT hx hL hBL hpres hf
    (Or.inr hpos)
  have hAH : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizer (L ⊔ K) Bs :=
    sup_le (ggAutomizer_mono Bs le_sup_left) (ggAutomizer_mono Bs le_sup_right)
  have hAind : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggInduced ⊤ Bs := by
    intro φ hφ
    have h1 := ggAutomizer_mono Bs le_top (hAH hφ)
    rw [ggAutomizer_eq] at h1
    exact h1
  obtain ⟨-, -, -, ε, hεrefl, -, -⟩ := id hpos
  have hM : ∀ k l : Fin 3, (coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType)
      ((Equiv.refl (Fin 3)) k) ((Equiv.refl (Fin 3)) l) = CoxeterMatrix.B 3 k l := by
    intro k l
    rw [coxeterMatrix_POmegaMinus_four]
    rfl
  have hcS := commute_rankOneFamily_of_exists_conj hAH (ggRankOneFrom p L (L ⊔ K) Bs)
    (fun t ht htR => hfam.2.1 t ht (ggCoxRefl_isReflection hpres.2 htR))
    (fun h hh hhN g hg t _ => (hfam.2.2 h hh hhN g hg t).symm) ⟨w, i, hu⟩ ⟨w', j, hr'⟩
    (exists_conj_commPair_mixed_of_label2 hpp hp2 hEl hNT hAind hpres le_sup_left ε hεrefl
      (Equiv.refl _) hM
      (fun w₀ i₀ j₀ hi₀ hj₀ => ggF4QGeFourRk2_commute_of_tableBPosImage_POmegaMinus hpp hp2 hEl
        hNT hAind hpres le_sup_left hf hpos w₀ i₀ j₀ hi₀ hj₀)
      w w' i j hij hu hr' hcomm)
  exact hfam.exists_centralizing_reflection_lift huL
    (ggCoxRefl_isReflection hpres.2 ⟨w, i, hu⟩) ⟨w', j, hr'⟩ hcS

theorem exists_r3comm_s1s3_of_tableBPos_POmegaMinus {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs L K : Subgroup G} {x : G} (hpp : p.Prime) (hp2 : p ≠ 2) (hEl : IsElemAbelian p Bs)
    (hNT : GGNoTransvection p Bs) (hx : x ∈ Bs)
    (hL : IsSubnormal L (Subgroup.centralizer ({x} : Set G)))
    (hBL : Bs ≤ Subgroup.normalizer (L : Set G))
    {e : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)}
    (hpres : GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e)
    {f : ℕ} (hf : 2 ≤ f) (hpos : GGTableBPosImage p Bs .POmegaMinus 4 f L)
    (w : CoxeterMatrix.F₄.Group) {u r' : MulAut ↥Bs}
    (hu : u = ((e (w * CoxeterMatrix.F₄.simple 1 * w⁻¹) :
      ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs))
    (hr' : r' = ((e (w * CoxeterMatrix.F₄.simple 3 * w⁻¹) :
      ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs))
    (huL : u ∈ ggAutomizer L Bs) :
    ∃ n ∈ L ⊔ K, n ∈ Subgroup.normalizer (Bs : Set G) ∧
      (∀ b : ↥Bs, ((r' b : ↥Bs) : G) = n * b * n⁻¹) ∧
      n ∈ Subgroup.centralizer (ggRankOneIn L Bs u : Set G) := by
  have hcomm : u * r' = r' * u := by
    rw [hu, hr', ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul]
    congr 2
    calc w * CoxeterMatrix.F₄.simple 1 * w⁻¹ * (w * CoxeterMatrix.F₄.simple 3 * w⁻¹)
        = w * (CoxeterMatrix.F₄.simple 1 * CoxeterMatrix.F₄.simple 3) * w⁻¹ := by group
      _ = w * (CoxeterMatrix.F₄.simple 3 * CoxeterMatrix.F₄.simple 1) * w⁻¹ := by
          rw [f4_simple_one_mul_three]
      _ = w * CoxeterMatrix.F₄.simple 3 * w⁻¹ * (w * CoxeterMatrix.F₄.simple 1 * w⁻¹) := by group
  exact exists_r3comm_mixed_of_tableBPos_POmegaMinus hpp hp2 hEl hNT hx hL hBL hpres hf hpos w w
    1 3 (by decide) hu hr' huL hcomm

theorem ggF4QGeFourR3S1S3_POmegaMinus {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hcfg : GGF4QGeFourCfg p B Bs x L D J y K) {f : ℕ} (hf : 2 ≤ f)
    (hpos : GGTableBPosImage p Bs .POmegaMinus 4 f L) :
    ∀ (e' : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)),
      GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e' →
      ∀ (w₂ : CoxeterMatrix.F₄.Group),
        ((e' (w₂ * CoxeterMatrix.F₄.simple 1 * w₂⁻¹) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
          MulAut ↥Bs) ∈ ggAutomizer L Bs →
        ∃ n : G, n ∈ Subgroup.normalizer (Bs : Set G) ∧
          (∀ b : ↥Bs, (((e' (w₂ * CoxeterMatrix.F₄.simple 3 * w₂⁻¹) :
            ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) b : G) = n * b * n⁻¹) ∧
          n ∈ Subgroup.centralizer (ggRankOneIn L Bs
            ((e' (w₂ * CoxeterMatrix.F₄.simple 1 * w₂⁻¹) :
              ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) : Set G) := by
  intro e' hpres' w₂ huL
  obtain ⟨hpp, hp2⟩ : p.Prime ∧ p ≠ 2 := by
    obtain ⟨⟨⟨⟨-, -, -, -, -, hβ, -⟩, -⟩, -⟩, -⟩ := hcfg
    exact ⟨hβ.1, hβ.2.1⟩
  obtain ⟨hDB, -, -, hxD, -⟩ := hcfg.1.1.2.2.1
  obtain ⟨n, -, hnN, hn, hnc⟩ := exists_r3comm_s1s3_of_tableBPos_POmegaMinus hpp hp2
    hcfg.1.1.2.1.2.1 hcfg.1.2.2.2.1 (hcfg.1.1.2.1.1 (hDB hxD))
    hcfg.1.1.1.2.2.2.2.2.2.1.2.2.2.1.2.1
    (GGDichotomy.le_normalizer_of_innerDiagOn hcfg.1.2.2.1.1) hpres' hf hpos w₂ rfl rfl huL
  exact ⟨n, hnN, hn, hnc⟩

end Inputs

end CFSG.StandardType

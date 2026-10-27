module

public import CFSG.LocalAnalysis.StandardType.GGF4OriginalRankOne
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourCommPair
import CFSG.LocalAnalysis.StandardType.GGF4CommPair
import CFSG.LieType.Universal.SymplecticExtras.Matrices
import Mathlib.Tactic.Group
import CFSG.LocalAnalysis.StandardType.GGKGPosSpStd
import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdAssembly
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem

theorem f4_simple_one_mul_three :
    CoxeterMatrix.F₄.simple 1 * CoxeterMatrix.F₄.simple 3 =
      CoxeterMatrix.F₄.simple 3 * CoxeterMatrix.F₄.simple 1 := by
  have h := CoxeterMatrix.F₄.toCoxeterSystem.simple_mul_simple_pow 1 3
  rw [show CoxeterMatrix.F₄.M 1 3 = 2 by decide, pow_two] at h
  have h' := eq_inv_of_mul_eq_one_left h
  rw [mul_inv_rev, CoxeterSystem.inv_simple, CoxeterSystem.inv_simple] at h'
  simpa only [CoxeterMatrix.toCoxeterSystem_simple] using h'

section Inputs

theorem exists_r3comm_mixed_of_tableBPos_PSp {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs L K : Subgroup G} {x : G} (hpp : p.Prime) (hp2 : p ≠ 2) (hEl : IsElemAbelian p Bs)
    (hNT : GGNoTransvection p Bs) (hx : x ∈ Bs)
    (hL : IsSubnormal L (Subgroup.centralizer ({x} : Set G)))
    (hBL : Bs ≤ Subgroup.normalizer (L : Set G))
    {e : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)}
    (hpres : GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e)
    {f : ℕ} (hf : 2 ≤ f) (hpos : GGTableBPosImage p Bs .PSp 3 f L)
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
    (Or.inl hpos)
  have hAH : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizer (L ⊔ K) Bs :=
    sup_le (ggAutomizer_mono Bs le_sup_left) (ggAutomizer_mono Bs le_sup_right)
  have hAind : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggInduced ⊤ Bs := by
    intro φ hφ
    have h1 := ggAutomizer_mono Bs le_top (hAH hφ)
    rw [ggAutomizer_eq] at h1
    exact h1
  have hcS := commute_rankOneFamily_of_commPair_mixed hpp hp2 hEl hNT hAind hpres le_sup_left hAH
    hf hpos (ggRankOneFrom p L (L ⊔ K) Bs)
    (fun t ht htR => hfam.2.1 t ht (ggCoxRefl_isReflection hpres.2 htR))
    (fun h hh hhN g hg t _ => (hfam.2.2 h hh hhN g hg t).symm) w w' i j hij hu hr' hcomm
  exact hfam.exists_centralizing_reflection_lift huL
    (ggCoxRefl_isReflection hpres.2 ⟨w, i, hu⟩) ⟨w', j, hr'⟩ hcS

theorem exists_r3comm_s1s3_of_tableBPos_PSp {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs L K : Subgroup G} {x : G} (hpp : p.Prime) (hp2 : p ≠ 2) (hEl : IsElemAbelian p Bs)
    (hNT : GGNoTransvection p Bs) (hx : x ∈ Bs)
    (hL : IsSubnormal L (Subgroup.centralizer ({x} : Set G)))
    (hBL : Bs ≤ Subgroup.normalizer (L : Set G))
    {e : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)}
    (hpres : GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e)
    {f : ℕ} (hf : 2 ≤ f) (hpos : GGTableBPosImage p Bs .PSp 3 f L)
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
  exact exists_r3comm_mixed_of_tableBPos_PSp hpp hp2 hEl hNT hx hL hBL hpres hf hpos w w 1 3
    (by decide) hu hr' huL hcomm

theorem ggF4QGeFour_original_tableBPos_PSp {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hcfg : GGF4QGeFourCfg p B Bs x L D J y K) {f : ℕ} (hf : 2 ≤ f) (hpf : p ∣ 2 ^ f - 1)
    (himg : GGCentralImage .PSp 3 f L) :
    p.Prime ∧ p ≠ 2 ∧ IsElemAbelian p Bs ∧ GGNoTransvection p Bs ∧ x ∈ Bs ∧
      IsSubnormal L (Subgroup.centralizer ({x} : Set G)) ∧
      Bs ≤ Subgroup.normalizer (L : Set G) ∧ GGTableBPosImage p Bs .PSp 3 f L := by
  obtain ⟨ψ, hloc⟩ := ggKGPosLocalHypSp_of_f4_mp_of_centralImage ggInnerDiagMpInput_holds
    hcfg hf hpf L (Or.inl rfl) himg
  obtain ⟨ψ', hker, hrange, hpos, -⟩ := ggKGPosSp_tableBPos_torus hloc
  obtain ⟨hDB, -, -, hxD, -⟩ := hcfg.1.1.2.2.1
  exact ⟨hloc.1.1, hloc.1.2.1, hloc.2.2.1.1, hcfg.1.2.2.2.1, hcfg.1.1.2.1.1 (hDB hxD),
    hcfg.1.1.1.2.2.2.2.2.2.1.2.2.2.1.2.1, hloc.2.2.1.2.1, ⟨ψ', hker, hrange, hpos⟩⟩

theorem exists_r3comm_s1s3_PSp {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hcfg : GGF4QGeFourCfg p B Bs x L D J y K)
    {e : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)}
    (hpres : GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e)
    {f : ℕ} (hf : 2 ≤ f) (hpf : p ∣ 2 ^ f - 1) (himg : GGCentralImage .PSp 3 f L)
    (w : CoxeterMatrix.F₄.Group) {u r' : MulAut ↥Bs}
    (hu : u = ((e (w * CoxeterMatrix.F₄.simple 1 * w⁻¹) :
      ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs))
    (hr' : r' = ((e (w * CoxeterMatrix.F₄.simple 3 * w⁻¹) :
      ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs))
    (huL : u ∈ ggAutomizer L Bs) :
    ∃ n ∈ L ⊔ K, n ∈ Subgroup.normalizer (Bs : Set G) ∧
      (∀ b : ↥Bs, ((r' b : ↥Bs) : G) = n * b * n⁻¹) ∧
      n ∈ Subgroup.centralizer (ggRankOneIn L Bs u : Set G) := by
  obtain ⟨hpp, hp2, hEl, hNT, hx, hL, hBL, hpos⟩ :=
    ggF4QGeFour_original_tableBPos_PSp hcfg hf hpf himg
  exact exists_r3comm_s1s3_of_tableBPos_PSp hpp hp2 hEl hNT hx hL hBL hpres hf hpos w hu hr' huL

end Inputs

end CFSG.StandardType

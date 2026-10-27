module

public import CFSG.Quasithin.EmptyFaithful.S14112Parts
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.WeakClosure81.W16Inputs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Cfg1620

variable {M V₀ V U S R H : Subgroup G} {g : G} {B : Subgroup G}

theorem exists_mem_inf_centralizer_conjSubgroup_le (h1 : W16One G) (h5 : W16Five G)
    (h15 : W16Fifteen G) (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B) {P : Subgroup G}
    (hP : IsSylowIn 2 P H) (hRP : R ≤ P) {h : G}
    (hle : conjSubgroup V h ≤ P ⊔ (H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G))) :
    ∃ c ∈ H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G), conjSubgroup V (h * c) ≤ P := by
  let CH : Subgroup G := H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)
  have hYH : P ⊔ CH ≤ H := sup_le hP.le inf_le_left
  have hPY : P ≤ P ⊔ CH := le_sup_left
  have hSyl : IsSylowIn 2 P (P ⊔ CH) := E6.isSylowIn_of_le hP hPY hYH
  have hVh2 : IsPGroup 2 (conjSubgroup V h) := E3.isPGroup_conjSubgroup c.cex.hyp.isPGroup h
  have hVhY : conjSubgroup V h ≤ P ⊔ CH := hle
  obtain ⟨y, hyY, hYle⟩ := E3.exists_le_conj_of_isSylowIn hSyl hVhY hVh2
  have hPCH : P ≤ Subgroup.normalizer (CH : Set G) :=
    hP.le.trans (le_normalizer_inf_centralizer_of_le (Subgroup.le_normalizer)
      (le_normalizer_conjClosure (U ⊔ V₀) H))
  have hy' : y ∈ (↑(P ⊔ CH) : Set G) := hyY
  rw [Subgroup.coe_mul_of_left_le_normalizer_right P CH hPCH] at hy'
  rw [Set.mem_mul] at hy'
  obtain ⟨p, hp, d, hd, hpd⟩ := hy'
  have hPy : conjSubgroup P y = conjSubgroup P d := by
    rw [← hpd, ← conjSubgroup_conjSubgroup P p d,
      conjSubgroup_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer (H := P) hp)]
  have hVhd : conjSubgroup V (h * d⁻¹) ≤ P := by
    have hle' : conjSubgroup V h ≤ conjSubgroup P d := by
      rw [hPy] at hYle
      exact hYle
    have h := E3.conjSubgroup_mono_left d⁻¹ hle'
    rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup, mul_inv_cancel,
      conjSubgroup_one] at h
    exact h
  exact ⟨d⁻¹, CH.inv_mem hd, hVhd⟩

end Cfg1620

end CFSG.LocalAnalysis.WeakClosure81

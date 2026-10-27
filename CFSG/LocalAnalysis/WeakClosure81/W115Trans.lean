module

public import CFSG.LocalAnalysis.WeakClosure81.W115ConjOut
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowFstarLift
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81.W115

open CFSG.Blueprint
open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

theorem w115_fourConj_of_isSpor
    {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y)
    (hnorm : (L.subgroupOf Y).Normal) (hF : Fstar Y = L) (hSp : IsSpor ↥L .M22)
    {s : MulAut W} (hs : s ∈ Y) (hs2 : orderOf s = 2) :
    ∃ b : Fin 4 → ↥L, L ≤ Subgroup.closure
      (Set.range fun i => ((b i : ↥L) : MulAut W) * s * ((b i : ↥L) : MulAut W)⁻¹) := by
  classical
  obtain ⟨ψ⟩ := hSp
  have hN : ∀ y ∈ Y, ∀ l ∈ L, y * l * y⁻¹ ∈ L := by
    intro y hy l hl
    have hmem : ((⟨y, hy⟩ : ↥Y) * (⟨l, hLY hl⟩ : ↥Y) * (⟨y, hy⟩ : ↥Y)⁻¹) ∈ L.subgroupOf Y :=
      hnorm.conj_mem (⟨l, hLY hl⟩ : ↥Y) (Subgroup.mem_subgroupOf.mpr hl) (⟨y, hy⟩ : ↥Y)
    simpa using Subgroup.mem_subgroupOf.mp hmem
  have hYnorm : Y ≤ Subgroup.normalizer (L : Set (MulAut W)) := by
    rw [Subgroup.le_normalizer_iff]
    intro y hy l hl
    exact hN y hy l hl
  let κ : ↥Y →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hYnorm)
  have hκ : ∀ (y : ↥Y) (γ : ↥L),
      ((κ y γ : ↥L) : MulAut W) = (y : MulAut W) * (γ : MulAut W) * (y : MulAut W)⁻¹ := by
    intro y γ
    have h := Subgroup.normalizerMonoidHom_apply_apply_coe L (Subgroup.inclusion hYnorm y) γ
    rw [Subgroup.coe_inclusion] at h
    exact h
  let Φ : ↥Y →* MulAut ↥NativeSporadic.M22 :=
    ((MulAut.congr ψ).toMonoidHom).comp κ
  have hΦl : ∀ l : ↥L, Φ ⟨(l : MulAut W), hLY l.2⟩ = MulAut.conj (ψ l) := by
    intro l
    have hκl : κ ⟨(l : MulAut W), hLY l.2⟩ = MulAut.conj l := by
      refine MulEquiv.ext fun γ => Subtype.ext ?_
      rw [hκ ⟨(l : MulAut W), hLY l.2⟩ γ]
      simp [MulAut.conj_apply]
    show (MulAut.congr ψ) (κ ⟨(l : MulAut W), hLY l.2⟩) = MulAut.conj (ψ l)
    rw [hκl]
    exact CFSG.ComponentClassification.OuterAutomorphisms.congr_conj ψ l
  have hZ : Subgroup.center ↥L = ⊥ := by
    have hZnat : Subgroup.center ↥NativeSporadic.M22 = ⊥ :=
      CFSG.Sporadic.Schreier.m22_center_eq_bot'
    have hcard : Nat.card (Subgroup.center ↥L) =
        Nat.card (Subgroup.center ↥NativeSporadic.M22) :=
      Nat.card_congr (Subgroup.centerCongr ψ).toEquiv
    rw [hZnat, Subgroup.card_bot] at hcard
    exact Subgroup.eq_bot_of_card_eq _ hcard
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have hκy : κ y = 1 := by
      apply (MulAut.congr ψ).injective
      rw [map_one]
      exact hy
    have hcent : (y : MulAut W) ∈ Subgroup.centralizer (L : Set (MulAut W)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hfix : (κ y) ⟨l, hl⟩ = ⟨l, hl⟩ := by
        rw [hκy]; rfl
      have hval : ((κ y) ⟨l, hl⟩ : MulAut W) = l := by
        rw [hfix]
      have hyz : (y : MulAut W) * l * (y : MulAut W)⁻¹ = l := by
        rw [← hκ y ⟨l, hl⟩]
        exact hval
      exact (mul_inv_eq_iff_eq_mul.mp hyz).symm
    have hyL : (y : MulAut W) ∈ L :=
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row.mem_of_mem_centralizer_of_fstar_eq
        hLY hF y.2 hcent
    have hyLcenter : (⟨(y : MulAut W), hyL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro γ
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hcent (γ : MulAut W) γ.2
    have hyL1 : (⟨(y : MulAut W), hyL⟩ : ↥L) = 1 := by
      rw [hZ, Subgroup.mem_bot] at hyLcenter
      exact hyLcenter
    exact Subtype.ext (by simpa using Subtype.ext_iff.mp hyL1)
  have hs_mul : s * s = 1 := by rw [← pow_two, ← hs2, pow_orderOf_eq_one]
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hs2
    norm_num at hs2
  have hsY2 : (⟨s, hs⟩ : ↥Y) * ⟨s, hs⟩ = 1 := Subtype.ext (by simpa using hs_mul)
  have hα2 : Φ ⟨s, hs⟩ * Φ ⟨s, hs⟩ = 1 := by
    rw [← map_mul, hsY2, map_one]
  have hα1 : Φ ⟨s, hs⟩ ≠ 1 := by
    intro h
    apply hs1
    have h1 : (⟨s, hs⟩ : ↥Y) = 1 := hΦinj (by rw [map_one]; exact h)
    simpa using Subtype.ext_iff.mp h1
  obtain ⟨h, hinner⟩ := w115_fourConj_aut (Φ ⟨s, hs⟩) hα2 hα1
  let b : Fin 4 → ↥L := fun i => ψ.symm (h i)
  have hψb : ∀ i, ψ (b i) = h i := fun i => MulEquiv.apply_symm_apply ψ (h i)
  refine ⟨b, ?_⟩
  let f : Fin 4 → ↥Y := fun i =>
    ⟨((b i : ↥L) : MulAut W) * s * ((b i : ↥L) : MulAut W)⁻¹, by
      have hbY : ((b i : ↥L) : MulAut W) ∈ Y := hLY (b i).2
      exact Y.mul_mem (Y.mul_mem hbY hs) (Y.inv_mem hbY)⟩
  let C' : Subgroup ↥Y := Subgroup.closure (Set.range f)
  have hsetΦ : Φ '' Set.range f =
      Set.range (fun i => MulAut.conj (h i) * Φ ⟨s, hs⟩ * (MulAut.conj (h i))⁻¹) := by
    rw [← Set.range_comp]
    apply congrArg Set.range
    funext i
    have hfi : (f i : ↥Y) = (⟨(b i : MulAut W), hLY (b i).2⟩ : ↥Y) * ⟨s, hs⟩ *
        (⟨(b i : MulAut W), hLY (b i).2⟩ : ↥Y)⁻¹ := by
      apply Subtype.ext
      simp [f]
    show Φ (f i) = MulAut.conj (h i) * Φ ⟨s, hs⟩ * (MulAut.conj (h i))⁻¹
    rw [hfi, map_mul, map_mul, map_inv, hΦl (b i), hψb i]
    rfl
  have hsetY : Y.subtype '' Set.range f =
      Set.range (fun i => ((b i : ↥L) : MulAut W) * s * ((b i : ↥L) : MulAut W)⁻¹) := by
    rw [← Set.range_comp]
    apply congrArg Set.range
    funext i
    rfl
  have hCmap : C'.map Φ = Subgroup.closure
      (Set.range fun i => MulAut.conj (h i) * Φ ⟨s, hs⟩ * (MulAut.conj (h i))⁻¹) := by
    unfold C'
    rw [MonoidHom.map_closure, hsetΦ]
  have hsub : C'.map Y.subtype = Subgroup.closure
      (Set.range fun i => ((b i : ↥L) : MulAut W) * s * ((b i : ↥L) : MulAut W)⁻¹) := by
    unfold C'
    rw [MonoidHom.map_closure, hsetY]
  intro l hl
  have hmemInner : MulAut.conj (ψ ⟨l, hl⟩) ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner ↥NativeSporadic.M22 := by
    show MulAut.conj (ψ ⟨l, hl⟩) ∈ (MulAut.conj :
      ↥NativeSporadic.M22 →* MulAut ↥NativeSporadic.M22).range
    exact MonoidHom.mem_range.mpr ⟨ψ ⟨l, hl⟩, rfl⟩
  have h1 : Φ ⟨(l : MulAut W), hLY hl⟩ ∈ C'.map Φ := by
    rw [hCmap, hΦl ⟨l, hl⟩]
    exact hinner hmemInner
  obtain ⟨c, hcC', hcΦ⟩ := Subgroup.mem_map.mp h1
  have hc : c = ⟨(l : MulAut W), hLY hl⟩ := hΦinj hcΦ
  have hmemC' : (⟨(l : MulAut W), hLY hl⟩ : ↥Y) ∈ C' := by
    rw [← hc]
    exact hcC'
  rw [← hsub]
  exact Subgroup.mem_map.mpr ⟨⟨(l : MulAut W), hLY hl⟩, hmemC', rfl⟩

end CFSG.LocalAnalysis.WeakClosure81.W115
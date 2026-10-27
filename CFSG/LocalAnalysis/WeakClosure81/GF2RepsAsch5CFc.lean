module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveDefs
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (OInf BarInf)

theorem ker_eq_solvableRadical_of_mem_cComp {Q : Type} [Group Q] [Finite Q] {H C : Subgroup Q}
    (hC : C ∈ cComp H) {Y : Type} [Group Y] (ψ : ↥C →* Y)
    (hψ : ∀ c : ↥C, ψ c = 1 ↔ (c : Q) ∈ OInf H) : ψ.ker = CFSG.solvableRadical ↥C := by
  have hOI : OInf H = solvRad H := (solvRad_eq_map_solvableRadical H).symm
  have hNsolv : Group.IsSolvable ↥(OInf H) := by
    have h := solvRad_isSolvable H
    rwa [← hOI] at h
  apply le_antisymm
  · have hsolv : Group.IsSolvable ↥ψ.ker := by
      let f : ↥ψ.ker →* ↥(OInf H) :=
        (C.subtype.comp ψ.ker.subtype).codRestrict (OInf H) (fun k => (hψ k.1).mp k.2)
      have hf : Function.Injective f := by
        intro a b hab
        have h1 := congrArg Subtype.val hab
        exact Subtype.ext (Subtype.ext h1)
      exact Group.isSolvable_of_isSolvable_injective hf
    exact A3.le_solvableRadical inferInstance hsolv
  · intro c hc
    have h1 : (c : Q) ∈ solvRad C := by
      rw [solvRad_eq_map_solvableRadical]
      exact ⟨c, hc, rfl⟩
    have h2 : solvRad C ≤ solvRad H :=
      solvRad_le_solvRad_of_subnormal (subnormal_of_mem_cComp hC)
    rw [MonoidHom.mem_ker, hψ, hOI]
    exact h2 h1

theorem exists_mulEquiv_barInf_of_hasQuotShape {Q : Type} [Group Q] [Finite Q]
    {H L C : Subgroup Q} (hC : C ∈ cComp H) (hCL : C ≤ L) (hCN : C ⊔ OInf H = L)
    {P : ∀ (X : Type) [Group X], Prop} (h : HasQuotShape L (OInf H : Set Q) P) :
    ∃ (X : Type) (_ : Group X), P X ∧ Nonempty (BarInf C ≃* X) := by
  obtain ⟨X, hXg, φ, hφ, hker, hP⟩ := h
  have hOI : OInf H = solvRad H := (solvRad_eq_map_solvableRadical H).symm
  have hCH : C ≤ H := le_of_mem_cComp hC
  have hnorm : C ≤ normalizer (OInf H : Set Q) := by
    have h1 : H ≤ normalizer (solvRad H : Set Q) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (solvRad_le H)).mp (solvRad_normal H)
    rw [hOI]
    exact hCH.trans h1
  have hNL : OInf H ≤ L := le_sup_right.trans hCN.le
  let ψ : ↥C →* X := φ.comp (Subgroup.inclusion hCL)
  have hψ : ∀ c : ↥C, ψ c = 1 ↔ (c : Q) ∈ OInf H := fun c => hker (Subgroup.inclusion hCL c)
  have hψsurj : Function.Surjective ψ := by
    intro x
    obtain ⟨l, rfl⟩ := hφ x
    have hl : (l : Q) ∈ ((C ⊔ OInf H : Subgroup Q) : Set Q) := by
      rw [hCN]
      exact l.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right C (OInf H) hnorm] at hl
    obtain ⟨c, hc, n, hn, hcn⟩ := hl
    refine ⟨⟨c, hc⟩, ?_⟩
    have h1 : φ ⟨n, hNL hn⟩ = 1 := (hker ⟨n, hNL hn⟩).mpr hn
    have h2 : l = Subgroup.inclusion hCL ⟨c, hc⟩ * ⟨n, hNL hn⟩ := Subtype.ext hcn.symm
    show φ (Subgroup.inclusion hCL ⟨c, hc⟩) = φ l
    rw [h2, map_mul, h1, mul_one]
  have hkerψ := ker_eq_solvableRadical_of_mem_cComp hC ψ hψ
  refine ⟨X, hXg, hP, ?_⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hkerψ.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψsurj)⟩

end CFSG.LocalAnalysis.WeakClosure81

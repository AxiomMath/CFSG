module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrame

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord

variable {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G} {m : ℕ}
  {V VT : Type} [Group V] [Group VT]

theorem qTwoLMFrameC_mem_normalizer_inf {g : G} {S K : Subgroup G}
    (hS : g ∈ Subgroup.normalizer (S : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((S ⊓ K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hS hK ⊢
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hS h, hK h]

noncomputable def qTwoLMFrameC_actVT (F : QTwoFrame m V VT Bs L x) {g : G}
    (hgBs : g ∈ Subgroup.normalizer (Bs : Set G)) (hgL : g ∈ Subgroup.normalizer (L : Set G)) :
    MulAut VT :=
  MulAut.congr F.thetaT.symm (ggConjAut (Bs ⊓ L) (qTwoLMFrameC_mem_normalizer_inf hgBs hgL))

theorem qTwoLMFrameC_actVT_spec (F : QTwoFrame m V VT Bs L x) {g : G}
    (hgBs : g ∈ Subgroup.normalizer (Bs : Set G)) (hgL : g ∈ Subgroup.normalizer (L : Set G))
    (v : VT) :
    ((F.thetaT (qTwoLMFrameC_actVT F hgBs hgL v) : ↥(Bs ⊓ L)) : G) =
      g * ((F.thetaT v : ↥(Bs ⊓ L)) : G) * g⁻¹ := by
  unfold qTwoLMFrameC_actVT
  simp [ggConjAut_apply]

theorem qTwoLMFrameC_actVT_normalizes (F : QTwoFrame m V VT Bs L x) {g : G}
    (hgBs : g ∈ Subgroup.normalizer (Bs : Set G)) (hgL : g ∈ Subgroup.normalizer (L : Set G))
    (σ : Equiv.Perm (Fin m)) :
    ∃ π : Equiv.Perm (Fin m),
      qTwoLMFrameC_actVT F hgBs hgL * F.permVT σ * (qTwoLMFrameC_actVT F hgBs hgL)⁻¹ =
        F.permVT π := by
  obtain ⟨n, hnBs, hn⟩ := F.indT σ
  have hgn : g * (n : G) * g⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp hgL (n : G)).mp n.2
  let n' : ↥L := ⟨g * (n : G) * g⁻¹, hgn⟩
  have hn'coe : (n' : G) = g * (n : G) * g⁻¹ := rfl
  have hn'Bs : (n' : G) ∈ Subgroup.normalizer (Bs : Set G) := by
    rw [hn'coe]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgBs hnBs) (Subgroup.inv_mem _ hgBs)
  obtain ⟨π, hπ⟩ := F.normT n' hn'Bs
  set ψ : MulAut VT := qTwoLMFrameC_actVT F hgBs hgL with hψ
  have hspec : ∀ u : VT,
      ((F.thetaT (ψ u) : ↥(Bs ⊓ L)) : G) =
        g * ((F.thetaT u : ↥(Bs ⊓ L)) : G) * g⁻¹ := by
    intro u
    rw [hψ]
    exact qTwoLMFrameC_actVT_spec F hgBs hgL u
  have hψinv : ∀ u : VT,
      ((F.thetaT (ψ⁻¹ u) : ↥(Bs ⊓ L)) : G) =
        g⁻¹ * ((F.thetaT u : ↥(Bs ⊓ L)) : G) * g := by
    intro u
    have h1 := hspec (ψ⁻¹ u)
    rw [MulAut.apply_inv_self] at h1
    rw [h1]
    group
  refine ⟨π, ?_⟩
  ext w
  simp only [MulAut.mul_apply]
  refine F.thetaT.injective ?_
  apply Subtype.ext
  rw [hspec (F.permVT σ (ψ⁻¹ w)), ← hn (ψ⁻¹ w), hψinv w, ← hπ w, hn'coe]
  group

end CFSG.StandardType.QTwo

end

module

public import CFSG.LocalAnalysis.WeakClosure81.W16PLemmaQBAImg
public import CFSG.LocalAnalysis.WeakClosure81.W16PLemmaQBASum
public import CFSG.LocalAnalysis.WeakClosure81.W16PLemmaQBAComp

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup Matrix
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace CfgLemmaQ

variable {M V₀ V C : Subgroup G} {h : G}

theorem exists_coboundary_of_sz (q : CfgLemmaQ M V₀ V h C) {τ : G}
    (hτ : τ ∈ V) (hτY : τ ∈ centralizer ((nVSub V₀ h ⊔ bSub V₀ h : Subgroup G) : Set G))
    (hτX : ∀ x ∈ V₀ ⊔ conjSubgroup V₀ h, x * τ * x⁻¹ * τ⁻¹ ∈ nVSub V₀ h ⊔ bSub V₀ h)
    {s : Finset (Subgroup G)} (hs : s.SupIndep id) (hsM : s.sup id = nVSub V₀ h ⊔ bSub V₀ h)
    (hXW : ∀ W ∈ s, V₀ ⊔ conjSubgroup V₀ h ≤ normalizer (W : Set G))
    {a : ℕ} (ha : 1 ≤ a) (hrel : (nVSub V₀ h).relIndex V₀ = 2 ^ (2 * a + 1))
    (ψ : ↥(V₀ ⊔ conjSubgroup V₀ h) →* GL (Fin 4) (GaloisField 2 (2 * a + 1)))
    (hψr : ψ.range = Sz a)
    (hψk : ψ.ker = (nVSub V₀ h ⊔ bSub V₀ h).subgroupOf (V₀ ⊔ conjSubgroup V₀ h))
    (hθ : ∀ W ∈ s, ∃ θ : (Fin 4 → GaloisField 2 (2 * a + 1)) → G,
      (∀ v v', θ (v + v') = θ v * θ v') ∧ Function.Injective θ ∧ Set.range θ = (W : Set G) ∧
        ∀ (x : ↥(V₀ ⊔ conjSubgroup V₀ h)) (v : Fin 4 → GaloisField 2 (2 * a + 1)),
          θ (((ψ x : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
            Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))) *ᵥ v) = x * θ v * x⁻¹) :
    ∃ y ∈ nVSub V₀ h ⊔ bSub V₀ h,
      ∀ x ∈ V₀ ⊔ conjSubgroup V₀ h, x * τ * x⁻¹ * τ⁻¹ = x * y * x⁻¹ * y⁻¹ := by
  classical
  let δ : G → G := fun x => x * τ * x⁻¹ * τ⁻¹
  have hYcomm : ∀ a ∈ s.sup id, ∀ b ∈ s.sup id, a * b = b * a := by
    intro a ha b hb
    rw [hsM] at ha hb
    exact q.prop24Setup.comm_M ha hb
  have hδY : ∀ x ∈ V₀ ⊔ conjSubgroup V₀ h, δ x ∈ s.sup id := by
    intro x hx
    rw [hsM]
    exact hτX x hx
  have hYnorm : ∀ u k : G, u ∈ (nVSub V₀ h ⊔ bSub V₀ h) →
      k ∈ V₀ ⊔ conjSubgroup V₀ h → k * u * k⁻¹ ∈ nVSub V₀ h ⊔ bSub V₀ h :=
    (Subgroup.normal_subgroupOf_iff (H := nVSub V₀ h ⊔ bSub V₀ h)
      (K := V₀ ⊔ conjSubgroup V₀ h) q.prop24Setup.M_le_X).mp
      q.prop24Setup.normal_subgroupOf
  have hδ : ∀ x ∈ V₀ ⊔ conjSubgroup V₀ h, ∀ y ∈ V₀ ⊔ conjSubgroup V₀ h,
      δ (x * y) = δ x * (x * δ y * x⁻¹) := by
    intro x hx y hy
    have hxY : δ x ∈ s.sup id := hδY x hx
    have hyY : δ y ∈ s.sup id := hδY y hy
    have hxyY : x * δ y * x⁻¹ ∈ s.sup id := by
      rw [hsM]
      exact hYnorm (δ y) x (hsM ▸ hyY) hx
    rw [hYcomm _ hxY _ hxyY]
    show (x * y) * τ * (x * y)⁻¹ * τ⁻¹ =
      (x * (y * τ * y⁻¹ * τ⁻¹) * x⁻¹) * (x * τ * x⁻¹ * τ⁻¹)
    group
  have hδT : ∀ t ∈ (V₀ : Set G) ∪
      ((nVSub V₀ h ⊔ bSub V₀ h : Subgroup G) : Set G), δ t = 1 := by
    intro t ht
    rcases ht with htV | htY
    · have hc : t * τ = τ * t := congrArg Subtype.val
        (q.hyp.h6.elemAbelian.1.is_comm.comm ⟨t, q.hyp.h6.le htV⟩ ⟨τ, hτ⟩)
      show t * τ * t⁻¹ * τ⁻¹ = 1
      rw [hc]
      group
    · have hc : t * τ = τ * t := (Subgroup.mem_centralizer_iff.mp hτY) t htY
      show t * τ * t⁻¹ * τ⁻¹ = 1
      rw [hc]
      group
  have hW : ∀ W ∈ s, ∀ d : G → G, (∀ x ∈ V₀ ⊔ conjSubgroup V₀ h, d x ∈ W) →
      (∀ x ∈ V₀ ⊔ conjSubgroup V₀ h, ∀ y ∈ V₀ ⊔ conjSubgroup V₀ h,
        d (x * y) = d x * (x * d y * x⁻¹)) →
      (∀ t ∈ (V₀ : Set G) ∪
        ((nVSub V₀ h ⊔ bSub V₀ h : Subgroup G) : Set G), d t = 1) →
      ∃ w ∈ W, ∀ x ∈ V₀ ⊔ conjSubgroup V₀ h, d x = x * w * x⁻¹ * w⁻¹ := by
    intro W hWs d hdW hd hdT
    obtain ⟨θ, hθadd, hθinj, hθrange, hθψ⟩ := hθ W hWs
    have hmem : ∀ x : ↥(V₀ ⊔ conjSubgroup V₀ h), ψ x ∈ Sz a := by
      intro x
      rw [← hψr]
      exact MonoidHom.mem_range.mpr ⟨x, rfl⟩
    let ψ' : ↥(V₀ ⊔ conjSubgroup V₀ h) →* ↥(Sz a) := ψ.codRestrict (Sz a) hmem
    have hψ's : Function.Surjective ψ' := by
      intro g
      have hg : (g : GL (Fin 4) (GaloisField 2 (2 * a + 1))) ∈ ψ.range := by
        rw [hψr]
        exact g.2
      obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hg
      exact ⟨x, Subtype.ext hx⟩
    have hψ'k : ψ'.ker =
        (nVSub V₀ h ⊔ bSub V₀ h).subgroupOf (V₀ ⊔ conjSubgroup V₀ h) := by
      show (ψ.codRestrict (Sz a) hmem).ker = _
      rw [MonoidHom.ker_codRestrict, hψk]
    have hθψ' : ∀ (x : ↥(V₀ ⊔ conjSubgroup V₀ h))
        (v : Fin 4 → GaloisField 2 (2 * a + 1)),
        θ ((((ψ' x : ↥(Sz a)) : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
          Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))) *ᵥ v) = x * θ v * x⁻¹ :=
      fun x v => hθψ x v
    have hV₁ : IsElemAbelian 2
        ((V₀.subgroupOf (V₀ ⊔ conjSubgroup V₀ h)).map ψ') :=
      CfgLemmaQ.isElemAbelian_map_subgroupOf q ψ'
    have hV₁card : Nat.card ((V₀.subgroupOf (V₀ ⊔ conjSubgroup V₀ h)).map ψ') =
        2 ^ (2 * a + 1) := by
      rw [CfgLemmaQ.card_map_subgroupOf_eq_relIndex q ψ' hψ'k, hrel]
    have hdK : ∀ y ∈ ψ'.ker, d (y : G) = 1 := by
      intro y hy
      have hyY : (y : G) ∈ nVSub V₀ h ⊔ bSub V₀ h := by
        rw [hψ'k] at hy
        exact Subgroup.mem_subgroupOf.mp hy
      exact hdT _ (Or.inr hyY)
    have hdV : ∀ v ∈ V₀.subgroupOf (V₀ ⊔ conjSubgroup V₀ h), d (v : G) = 1 := by
      intro v hv
      exact hdT _ (Or.inl (Subgroup.mem_subgroupOf.mp hv))
    exact exists_mem_of_natural_crossedHom (X := V₀ ⊔ conjSubgroup V₀ h) (W := W)
      ha ψ' hψ's θ hθadd hθinj hθrange hθψ' hV₁ hV₁card hdW hd hdK hdV
  obtain ⟨y, hy, hyx⟩ := exists_coboundary_of_supIndep (X := V₀ ⊔ conjSubgroup V₀ h) hs
    hYcomm hXW ((V₀ : Set G) ∪ ((nVSub V₀ h ⊔ bSub V₀ h : Subgroup G) : Set G))
    hW hδY hδ hδT
  exact ⟨y, hsM ▸ hy, fun x hx => hyx x hx⟩

end CfgLemmaQ

end CFSG.LocalAnalysis.WeakClosure81

end

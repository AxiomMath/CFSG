module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.G10Clifford
public import CFSG.Quasithin.Background.G10FifteenRing
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem autAll_of_hiso {H : Subgroup (GLV V)} {J J' : Submodule (ZMod 2) V}
    (hJ : Invariant H J) (h : HIso H J J') (hA : AutAll H J) : AutAll H J' := by
  obtain ⟨φ, hφ⟩ := h
  intro g'
  obtain ⟨k, hk, hkg⟩ := hA (φ.trans (g'.trans φ.symm))
  refine ⟨k, hk, fun j' => ?_⟩
  obtain ⟨i, rfl⟩ := φ.surjective j'
  have h1 := hφ k hk i ⟨k (i : V), hJ k hk i i.2⟩ rfl
  have h2 : (⟨k (i : V), hJ k hk i i.2⟩ : ↥J) = (φ.trans (g'.trans φ.symm)) i :=
    Subtype.ext (hkg i)
  rw [h1, h2]
  simp

theorem autAll_of_conj {Γ H : Subgroup (GLV V)} (hN : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H)
    {γ : GLV V} (hγ : γ ∈ Γ) {I : Submodule (ZMod 2) V} (hA : AutAll H (conjSub γ I)) :
    AutAll H I := by
  intro g
  let cγ : ↥I ≃ₗ[ZMod 2] ↥(conjSub γ I) :=
    LinearEquiv.ofSubmodules (γ : V ≃ₗ[ZMod 2] V) I (conjSub γ I) rfl
  obtain ⟨k, hk, hkg⟩ := hA (cγ.symm.trans (g.trans cγ))
  refine ⟨γ⁻¹ * k * γ, by simpa using hN γ⁻¹ (Γ.inv_mem hγ) k hk, fun u => ?_⟩
  have h1 := hkg (cγ u)
  have h2 : (cγ u : V) = γ (u : V) := rfl
  have h3 : (cγ.symm.trans (g.trans cγ)) (cγ u) = cγ (g u) := by simp
  rw [h3] at h1
  have h4 : k (γ (u : V)) = γ ((g u : ↥I) : V) := by
    have := h1
    rw [h2] at this
    exact this
  show γ⁻¹ (k (γ (u : V))) = ((g u : ↥I) : V)
  rw [h4]
  exact LinearEquiv.symm_apply_apply γ _

theorem invariant_zpowers {a : GLV V} {J : Submodule (ZMod 2) V} (h : conjSub a J = J) :
    Invariant (Subgroup.zpowers a) J := by
  have hz : Subgroup.zpowers a ≤ stabilizerOf ⊤ J :=
    (Subgroup.zpowers_le).2 ⟨Subgroup.mem_top _, h⟩
  intro k hk u hu
  have h1 : k u ∈ conjSub k J := apply_mem_conjSub hu
  rwa [(hz hk).2] at h1

namespace G108Hyp

variable [Finite V] {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} (hyp : G108Hyp B Γ v₁ W X X₀ L)

include hyp

theorem exists_hiso_conj {I : Submodule (ZMod 2) V} (hI : IrrPlus (normalClosure Γ L) I)
    {J : Submodule (ZMod 2) V} (hJ : IsIrr (normalClosure Γ L) J) :
    ∃ γ ∈ Γ, HIso (normalClosure Γ L) J (conjSub γ I) := by
  have hirr : IsIrr (normalClosure Γ L) I := hI.isIrr hyp.fixedSpace_H
  have htop := iSup_conjSub_eq_top hyp.irreducible hirr.ne_bot
  let S : Set (Submodule (ZMod 2) V) := Set.range (fun γ : ↥Γ => conjSub (γ : GLV V) I)
  have hSirr : ∀ K ∈ S, IsIrr (normalClosure Γ L) K := by
    rintro _ ⟨γ, rfl⟩
    exact hirr.conj_of_normal (normalClosure_normal Γ L) γ.2
  have hJS : J ≤ sSup S := by
    rw [sSup_range, htop]
    exact le_top
  obtain ⟨K, ⟨γ, rfl⟩, hJK⟩ := irr_le_sSup hJ hSirr hJS
  exact ⟨γ, γ.2, hJK⟩

end G108Hyp

end G11

end CFSG.Quasithin

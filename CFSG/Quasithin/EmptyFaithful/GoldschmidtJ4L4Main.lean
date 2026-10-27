module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4L4Nat
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4L4IsPSL
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Main
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127EvenMain

public section

namespace CFSG.Quasithin.J4L4

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Blueprint CFSG.Quasithin.J4Loc CFSG.QuasithinUnique

theorem j4L4Inner_of_overgroups
    (hO : J4TwoLocalOvergroups) : A38c8.J4L4Inner := by
  intro Y _ _ N T B hN hNJ hT hBN _ hTB hPSL x hx
  have hF : J4Facts := j4Facts
  have hM := hF.mat
  have hsub : CFSG.Open.IsSubnormal N ⊤ :=
    CFSG.Open.IsSubnormal.step le_top (Subgroup.Normal.subgroupOf hN ⊤)
      (CFSG.Open.IsSubnormal.refl ⊤)
  have hSN : IsSylowTwoOf (T ⊓ N) N := L246C127.isSylowTwoOf_inf_of_isSubnormal' hsub hT
  have hS' : IsSylowTwoOf ((T ⊓ N).subgroupOf N) ⊤ := by
    have := L246C127.isSylowTwoOf_top_map_subgroupOf (MulEquiv.refl ↥N) hSN
    simpa using this
  obtain ⟨e⟩ := hNJ
  obtain ⟨ψ, hψ⟩ := sylow_transport (Γ := J) isSylowTwoOf_P0 (e.trans (seedEquiv hM)) hS'
  set B₁ : Subgroup ↥N := B.subgroupOf N with hB₁
  have hSB : (T ⊓ N).subgroupOf N ≤ Subgroup.normalizer (B₁ : Set ↥N) := by
    intro s hs
    have hsT : (s : Y) ∈ T := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hs)).1
    rw [Subgroup.mem_normalizer_iff]
    intro b
    simp only [hB₁, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.1 (hTB hsT) (b : Y)
  have hPB : P0 ≤ Subgroup.normalizer ((B₁.map (ψ : ↥N →* J) : Subgroup J) : Set J) := by
    rw [map_normalizer_equiv, ← hψ]
    exact Subgroup.map_mono hSB
  have hA8 : HasA8 B := alt8_of_isPSL hPSL
  have hA8₁ : HasA8 B₁ := by
    have h1 := (hasA8_map_iff (N.subtype) N.subtype_injective B₁).1
    rw [hB₁, Subgroup.map_subgroupOf_eq_of_le hBN] at h1
    exact h1 hA8
  have hA8' : HasA8 (B₁.map (ψ : ↥N →* J)) := (hasA8_map_iff _ ψ.injective B₁).2 hA8₁
  have hx1 : (⟨x, hx.2⟩ : ↥N) ∈ (T ⊓ N).subgroupOf N := Subgroup.mem_subgroupOf.2 hx
  have hψx : ψ ⟨x, hx.2⟩ ∈ P0 := by
    rw [← hψ]
    exact Subgroup.mem_map_of_mem _ hx1
  have h2 := innerOnModO2_of_overgroups hO hPB hA8' _ hψx
  have h3 := (innerOnModO2_map_iff (ψ : ↥N →* J) ψ.injective B₁ ⟨x, hx.2⟩).1 h2
  have h4 := (innerOnModO2_map_iff N.subtype N.subtype_injective B₁ ⟨x, hx.2⟩).2 h3
  rwa [hB₁, Subgroup.map_subgroupOf_eq_of_le hBN] at h4

end CFSG.Quasithin.J4L4

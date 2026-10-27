module

public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3BridgeA
public import CFSG.LocalAnalysis.StandardType.GGResExact2KReverse
public import CFSG.LocalAnalysis.StandardType.GGResNonsingularBase
public import CFSG.LocalAnalysis.StandardType.GGNbrU63Setup
public import TauCeti.LinearAlgebra.LinearMap.Cardinality

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggResJ_card_range_gamma_le_pow_of_rootData
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs J : Subgroup G} {I : Type} [Fintype I]
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (ι : Additive ↥Bs ≃+ V) (φ : I → MulAut ↥Bs) (h : I → V)
    (α : I → Module.Dual (ZMod p) V)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i))
    (hgen : ggAutomizer J Bs = Subgroup.closure (Set.range φ))
    (hfwd : ∀ b : ↥Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G)) :
    Nat.card (ggGamma J hN).range ≤ p ^ Fintype.card I := by
  classical
  have hker := ggResJ_rootKernel_card ι φ h α hlin hrefl hgen hfwd
  have hγprod := NbrU63.card_range_ggGamma_mul_card_inf hN
  have hπprod := LinearMap.card_eq_card_range_mul_card_ker (LinearMap.pi α)
  rw [hker, ← card_eq_of_ggLin ι] at hπprod
  have hcard : Nat.card (ggGamma J hN).range = Nat.card (LinearMap.pi α).range :=
    Nat.eq_of_mul_eq_mul_right Nat.card_pos (hγprod.trans hπprod)
  rw [hcard]
  calc
    Nat.card (LinearMap.pi α).range ≤ Nat.card (I → ZMod p) :=
      Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    _ = p ^ Fintype.card I := by
      rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card]

theorem GGResLeviDatumCard.card_range_gamma_J_le_pow_of_fixed_of_weylType
    {G : Type} [Group G] [Finite G] {p k n c : ℕ} [Fact p.Prime]
    {Bs X J Y : Subgroup G}
    (hD : GGResLeviDatumCard k p Bs X J Y ggSelAny ggTypAny)
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (hfwd : ∀ b : ↥Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G))
    (hX : GGWeylTypeData n (Nat.card ↥(ggAutomizer X Bs)) c) :
    Nat.card (ggGamma J hN).range ≤ p ^ (n - k) := by
  classical
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS, ha1, ha3, hML, hCL, hMK, hCK, htyp, hlin, hrefl, hpair, hpairK,
    hsel, ⟨fX, hfX⟩, hother, hgenX, hgenY, hc, hgenJ⟩ := hD
  letI := i1
  letI := i2
  letI := i3
  letI := i4
  letI := i5
  letI := i6
  have hfull : GGWeylTypeData (Fintype.card Λ) (Nat.card ↥(ggAutomizer X Bs))
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer X Bs))) := by
    rw [← Nat.card_congr fX.toEquiv, ← Nat.card_congr (Subgroup.centerCongr fX).toEquiv]
    exact ggWeylTypeData_of_isWeylMatrix hML
  have hn : Fintype.card Λ = n := ggWeylTypeData_rank_eq hfull hX
  have hbound := ggResJ_card_range_gamma_le_pow_of_rootData hN ι
    (fun i : {i : Λ // i ∉ S} => φ (Sum.inl i))
    (fun i => h (Sum.inl i)) (fun i => α (Sum.inl i))
    (fun i w => hlin (Sum.inl i) w) (fun i => hrefl (Sum.inl i)) hgenJ hfwd
  have hsub : Fintype.card {i : Λ // i ∈ S} = S.card := by
    rw [Fintype.card_subtype]
    simp
  have hcomp : Fintype.card {i : Λ // i ∉ S} = Fintype.card Λ - S.card := by
    rw [Fintype.card_subtype_compl (fun i : Λ => i ∈ S), hsub]
  simpa only [hcomp, hn, hS] using hbound

theorem GGResHyp.not_exactThree_either_of_weylRank_gamma_gap
    {G : Type} [Group G] [Finite G] {p n c : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hTBF : GGTBFixInput)
    (hH : GGResHyp p B Bs x L D J y K)
    (hn : 2 ≤ n)
    (hWL : GGWeylTypeData n (Nat.card ↥(ggAutomizer L Bs)) c)
    (hfwd : ∀ b : ↥Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G))
    (hγ : p ^ (n - 1) ≤ Nat.card (ggGamma J hH.Bs_le_normalizer_J).range) :
    ¬ (GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) := by
  have hp : p.Prime := Fact.out
  have hNoL : ¬ GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny := by
    intro hL3
    have hupper := hL3.card_range_gamma_J_le_pow_of_fixed_of_weylType
      hH.Bs_le_normalizer_J hfwd hWL
    exact (Nat.pow_lt_pow_right hp.one_lt (by omega : n - 3 < n - 1)).not_ge
      (hγ.trans hupper)
  rintro (hL3 | hK3)
  · exact hNoL hL3
  · rcases ggResExact3_K_reverse_or_exact2_singular hTBF hH hK3 with
        hL3 | ⟨hL2, _⟩
    · exact hNoL hL3
    · have hupper := hL2.card_range_gamma_J_le_pow_of_fixed_of_weylType
        hH.Bs_le_normalizer_J hfwd hWL
      exact (Nat.pow_lt_pow_right hp.one_lt (by omega : n - 2 < n - 1)).not_ge
        (hγ.trans hupper)

end CFSG.StandardType

end

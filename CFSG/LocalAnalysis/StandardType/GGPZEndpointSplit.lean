module

public import CFSG.LocalAnalysis.StandardType.GGPZVertHolds
public import CFSG.LocalAnalysis.StandardType.GGPZRankTwo

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.ComponentClassification
open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGPZEndpointAt {G : Type} [Group G] {Bs : Subgroup G} (Y : Subgroup G)
    (labJ : LargeEvenLabel) (m : ℕ) : Prop :=
  ∃ (r n c : ℕ) (W : Type) (_ : Group W) (_ : Finite W) (f : W →* MulAut ↥Bs),
    GGWeylTypeData r n c ∧ labJ.rank ≤ r ∧ r ≤ m ∧ Nat.card W = n ∧
      Nat.card ↥(Subgroup.center W) = c ∧ ggAutomizer Y Bs ≤ f.range

@[expose] def GGPZEndpointTriv : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G) (labJ labX : LargeEvenLabel)
    (X : Subgroup G) (m : ℕ) (z : ↥Bs), GGPZPrem p B Bs x L D J y K labJ labX X m z →
    ∀ Y : Subgroup G, LargeEvenPComponent p (Subgroup.centralizer ({(z : G)} : Set G)) Y →
      J ≤ Y → Bs ≤ Subgroup.normalizer (Y : Set G) →
      (⁅Y, Subgroup.zpowers x⁆ : Subgroup G) ≤ LargeEvenPPrimeCoreOf p Y →
      GGPZEndpointAt (Bs := Bs) Y labJ m

@[expose] def GGPZEndpointNbr : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G) (labJ labX : LargeEvenLabel)
    (X : Subgroup G) (m : ℕ) (z : ↥Bs), GGPZPrem p B Bs x L D J y K labJ labX X m z →
    ∀ Y : Subgroup G, LargeEvenPComponent p (Subgroup.centralizer ({(z : G)} : Set G)) Y →
      J ≤ Y → Bs ≤ Subgroup.normalizer (Y : Set G) → GGNbr p B x D J (z : G) Y →
      GGPZEndpointAt (Bs := Bs) Y labJ m

theorem ggPZ_pComponent_unique {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {H J Y Y' : Subgroup G} (hY : LargeEvenPComponent p H Y) (hY' : LargeEvenPComponent p H Y')
    (hJY : J ≤ Y) (hJY' : J ≤ Y') (hJperf : commutator ↥J = ⊤) (hpJ : p ∣ Nat.card ↥J) :
    Y' = Y := by
  by_contra hne
  have hcomm : ∀ v ∈ J, ∀ j ∈ J, ⁅v, j⁆ ∈ LargeEvenPPrimeCoreOf p J := fun v hv j hj =>
    commutator_mem_largeEvenPPrimeCoreOf_of_mem_inf hY hY' (Ne.symm hne) hJY hv (hJY' hv) j hj
  have hJJ : ⁅J, J⁆ = J := by
    have h1 : ⁅(⊤ : Subgroup ↥J), (⊤ : Subgroup ↥J)⁆ = ⊤ := by
      rw [← commutator_def]
      exact hJperf
    have h2 : Subgroup.map J.subtype ⁅(⊤ : Subgroup ↥J), (⊤ : Subgroup ↥J)⁆ =
        ⁅Subgroup.map J.subtype ⊤, Subgroup.map J.subtype ⊤⁆ :=
      Subgroup.map_commutator ⊤ ⊤ J.subtype
    rw [h1, Subgroup.map_top, Subgroup.range_subtype] at h2
    exact h2.symm
  have hJO : J ≤ LargeEvenPPrimeCoreOf p J := by
    calc J = ⁅J, J⁆ := hJJ.symm
      _ ≤ LargeEvenPPrimeCoreOf p J := Subgroup.commutator_le.mpr hcomm
  have hOJ : LargeEvenPPrimeCoreOf p J ≤ J := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.2
  have hcop := ggPPrimeCoreOf_coprime (p := p) J
  rw [le_antisymm hOJ hJO] at hcop
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mp hcop hpJ

theorem ggPZEndpointInput_of_triv_nbr (hPU : GGPumpupInput) (hT : GGPZEndpointTriv)
    (hN : GGPZEndpointNbr) : GGPZEndpointInput := by
  intro G _ _ p _ B Bs x L D J y K labJ labX X m z h Y hY hJY hBsY
  have h' := h
  have hrank : 2 ≤ labJ.rank := ggPZ_rank_two h
  obtain ⟨hH, -, -, -, -, -, -, -, -, hJcard, -, hzD, hzx, -⟩ := h
  have hI : GGThmIHyp p B x L := hH.1.1
  have hDJ : LargeEvenStdSub p B x L D J := hH.1.2.2
  have hJperf : commutator ↥J = ⊤ := hH.1.2.2.1.2.2.2.2.2.1.2.2.1
  have hpJ : p ∣ Nat.card ↥J := by
    have h1 : Nat.card ↥(Bs ⊓ J) ∣ Nat.card ↥J := Subgroup.card_dvd_of_le inf_le_right
    rw [hJcard] at h1
    exact (dvd_pow_self p (by omega)).trans h1
  have hD : D = Subgroup.closure {x, (z : G)} := eq_closure_pair_of_mem hI hDJ hzD hzx
  obtain ⟨hK, hJK, -, hdich⟩ := pumpup_of_stdSub hPU hI hDJ hpJ hD
  have hYeq : Y = ggLayerClosure p (Subgroup.centralizer ({(z : G)} : Set G)) J :=
    ggPZ_pComponent_unique hK hY hJK hJY hJperf hpJ
  subst hYeq
  rcases hdich with hnbr | htriv
  · exact hN G p B Bs x L D J y K labJ labX X m z h' _ hK hJY hBsY hnbr
  · exact hT G p B Bs x L D J y K labJ labX X m z h' _ hK hJY hBsY htriv

end CFSG.StandardType

end

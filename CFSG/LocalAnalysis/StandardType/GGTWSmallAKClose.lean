module

public import CFSG.LocalAnalysis.StandardType.GGTWSmallAClose
public import CFSG.LocalAnalysis.StandardType.GGTWLowOfK

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTWSmallA_close_K
    (hC : GGTWSmallCells) (hPZ : GGPZInput) (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput)
    {G : Type} [Group G] [Finite G] {p N k : ℕ} [Fact p.Prime] (hk : k = 1 ∨ k = 2) (hp : 3 ≤ p)
    (hpN : p ∣ N) (hN : N = 5 ∨ N = 6 ∨ N = 7 ∨ N = 9 ∨ N = 10) {B Bs : Subgroup G} {x y : G}
    {L D J K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hyK : y ∉ K)
    {labJ labX : LargeEvenLabel} (hJΛ : LargeEvenInLambda2 labJ) (hXΛ : LargeEvenInLambda2 labX)
    (hJl : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hXl : GGHasLabel labX (↥K ⧸ Subgroup.center ↥K)) (hrow : ggRowTwoNodeSmall p labJ labX)
    (hAtag : labX.tag = .A ∨ labX.tag = .twA) (hXrank : labX.rank = N - 1)
    (hJrank : labJ.rank = N - 3) (hZJ : ¬ p ∣ Nat.card ↥(Subgroup.center ↥J))
    (hCard : Nat.card ↥Bs = p ^ (N - 1))
    (hHK : Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y → GGTWHLAt p Bs K y)
    (hHL : (N = 5 ∨ N = 6 ∨ N = 9) → GGTWHLAt p Bs L x)
    (hA : GGTWAligned p N k Bs K J L) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  obtain ⟨-, -, -, -, -, hC55, hC36, hC39, hF77, hF510⟩ := hC
  have hJcard : (N = 5 ∨ N = 6 ∨ N = 9) → Nat.card ↥(Bs ⊓ J) = p ^ labJ.rank := fun hN' => by
    rw [hJrank]
    exact ggTW_inf_J_card hp hpN hN' hH hk hCard hZJ (Or.inr hA)
  rcases ggTWSmall_row_of_dvd (Fact.out : p.Prime) hp hpN hN with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hcfg := ggTWLowCfg_of_alignedK hFix hFixK hH hyK hk hp (Or.inl rfl) hpN hCard
      hHK (hHL (Or.inl rfl)) hA
    exact ggTWLow_leaf hPZ hk hp hpN (Or.inl rfl) hH hJΛ hXΛ hJl hXl hrow hAtag hXrank
      hJrank hCard (hJcard (Or.inl rfl)) (fun _ => False) hC55
      (fun {_} [AddCommGroup _] [Module (ZMod 5) _] _ {_} _ _ _ _ h _ _ => h.elim)
      (Or.inr ⟨rfl, hcfg⟩)
  · have hcfg := ggTWLowCfg_of_alignedK hFix hFixK hH hyK hk hp (Or.inr (Or.inl rfl)) hpN
      hCard hHK (hHL (Or.inr (Or.inl rfl))) hA
    exact ggTWLow_leaf hPZ hk hp hpN (Or.inr (Or.inl rfl)) hH hJΛ hXΛ hJl hXl hrow hAtag
      hXrank hJrank hCard (hJcard (Or.inr (Or.inl rfl))) GGTWLowE6Outcome hC36
      (fun {_} [AddCommGroup _] [Module (ZMod 3) _] ι {_} θ gens hA' S hS hS₁ hS₂ =>
        ggTWLow_weyl_E6 ι θ gens hA' S hS₁ hS₂ hS)
      (Or.inr ⟨rfl, hcfg⟩)
  · exfalso
    have hv := ggTWVCfg_of_alignedK hFix hFixK hH hyK hk (Or.inl rfl) hpN hCard hHK hA
    rcases hk with rfl | rfl
    · exact hF77.1 (ggTWSurv1_of_vcfg hp hpN hN hv)
    · exact hF77.2 (ggTWSurv2_of_vcfg hp hpN hN hv)
  · have hcfg := ggTWLowCfg_of_alignedK hFix hFixK hH hyK hk hp (Or.inr (Or.inr rfl)) hpN
      hCard hHK (hHL (Or.inr (Or.inr rfl))) hA
    exact ggTWLow_leaf hPZ hk hp hpN (Or.inr (Or.inr rfl)) hH hJΛ hXΛ hJl hXl hrow hAtag
      hXrank hJrank hCard (hJcard (Or.inr (Or.inr rfl))) GGTWLowE8Outcome hC39
      (fun {_} [AddCommGroup _] [Module (ZMod 3) _] ι {_} θ gens hA' S hS hS₁ hS₂ =>
        ggTWLow_weyl_E8 ι θ gens hA' S hS₁ hS₂ hS)
      (Or.inr ⟨rfl, hcfg⟩)
  · exfalso
    have hv := ggTWVCfg_of_alignedK hFix hFixK hH hyK hk (Or.inr rfl) hpN hCard hHK hA
    rcases hk with rfl | rfl
    · exact hF510.1 (ggTWSurv1_of_vcfg hp hpN hN hv)
    · exact hF510.2 (ggTWSurv2_of_vcfg hp hpN hN hv)

end CFSG.StandardType

end

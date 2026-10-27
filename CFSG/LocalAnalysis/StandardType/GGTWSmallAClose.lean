module

public import CFSG.LocalAnalysis.StandardType.GGTWCardB
public import CFSG.LocalAnalysis.StandardType.GGTWCardDich
public import CFSG.LocalAnalysis.StandardType.GGTWUpOf
public import CFSG.LocalAnalysis.StandardType.GGTWUpClose
public import CFSG.LocalAnalysis.StandardType.GGTWLowOf
public import CFSG.LocalAnalysis.StandardType.GGTWLowLeaf
public import CFSG.LocalAnalysis.StandardType.GGTWVCfgFrom
public import CFSG.LocalAnalysis.StandardType.GGTWSurvOne
public import CFSG.LocalAnalysis.StandardType.GGTWSurvTwo
public import CFSG.LocalAnalysis.StandardType.GGTWLowWeyl
public import CFSG.LocalAnalysis.StandardType.GGTWDCells77
public import CFSG.LocalAnalysis.StandardType.GGTWDCells510
public import CFSG.LocalAnalysis.StandardType.GGTWDCells55
public import CFSG.LocalAnalysis.StandardType.GGTWDCells39
public import CFSG.LocalAnalysis.StandardType.GGTWDCells36Cert
public import CFSG.LocalAnalysis.StandardType.GGTWLowCells55
public import CFSG.LocalAnalysis.StandardType.GGTWLowCells36
public import CFSG.LocalAnalysis.StandardType.GGTWLowCells39
public import CFSG.LocalAnalysis.StandardType.GGTWCells77
public import CFSG.LocalAnalysis.StandardType.GGTWCells510

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGTWSmallCells : Prop :=
  GGTWDCells 7 7 ∧ GGTWDCells 5 10 ∧ GGTWDCells 5 5 ∧ GGTWDCells 3 9 ∧ GGTWDCells36Orb ∧
    GGTWLowCells 5 5 (fun _ => False) ∧ GGTWLowCells 3 6 GGTWLowE6Outcome ∧
    GGTWLowCells 3 9 GGTWLowE8Outcome ∧ GGTWCells .frame 7 7 ∧ GGTWCells .frame 5 10

theorem ggTWSmallCells_holds :
    GGTWSmallCells :=
  ⟨ggTWD_cells_7_7, ggTWD_cells_5_10, ggTWD_cells_5_5, ggTWD_cells_3_9, ggTWD_cells_3_6,
    ggTW_low_cells_5_5, ggTW_low_cells_3_6, ggTW_low_cells_3_9, ggTW_cells_frame_7_7,
    ggTW_cells_frame_5_10⟩

theorem ggTWSmall_row_of_dvd {p N : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hpN : p ∣ N)
    (hN : N = 5 ∨ N = 6 ∨ N = 7 ∨ N = 9 ∨ N = 10) :
    (p = 5 ∧ N = 5) ∨ (p = 3 ∧ N = 6) ∨ (p = 7 ∧ N = 7) ∨ (p = 3 ∧ N = 9) ∨
      (p = 5 ∧ N = 10) := by
  rcases hN with rfl | rfl | rfl | rfl | rfl
  · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5)).mp hpN
    omega
  · have h6 : p ∣ 2 * 3 := hpN
    rcases hp.dvd_mul.mp h6 with h2 | h3
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
      omega
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
      omega
  · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7)).mp hpN
    omega
  · have h9 : p ∣ 3 ^ 2 := hpN
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h9)
    omega
  · have h10 : p ∣ 2 * 5 := hpN
    rcases hp.dvd_mul.mp h10 with h2 | h5
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
      omega
    · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5)).mp h5
      omega

theorem ggTWSmallA_close_up
    (hC : GGTWSmallCells) (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput) {G : Type} [Group G]
    [Finite G] {p N k : ℕ} [Fact p.Prime] (hk : k = 1 ∨ k = 2) (hp : 3 ≤ p) (hpN : p ∣ N)
    (hN : N = 5 ∨ N = 6 ∨ N = 7 ∨ N = 9 ∨ N = 10) {B Bs : Subgroup G} {x y : G}
    {L D J K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hxL : x ∉ L)
    (hCard : Nat.card ↥Bs = p ^ N) (hA : GGTWAligned p N k Bs L J K) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  have hcfg := ggTWUpCfg_of_aligned hFix hFixK hH hxL hk hN hpN hCard hA
  obtain ⟨hC77, hC510, hC55, hC39, hC36, -⟩ := hC
  rcases ggTWSmall_row_of_dvd (Fact.out : p.Prime) hp hpN hN with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exfalso
    rcases hk with rfl | rfl
    · exact ggTWUp_false_one hp hpN hN hC55.1 hcfg
    · exact ggTWUp_false_two hp hpN hN hC55.2 hcfg
  · rcases hk with rfl | rfl
    · exact ggTWUp_weyl36_one hC36 hcfg
    · exact ggTWUp_weyl36_two hC36 hcfg
  · exfalso
    rcases hk with rfl | rfl
    · exact ggTWUp_false_one hp hpN hN hC77.1 hcfg
    · exact ggTWUp_false_two hp hpN hN hC77.2 hcfg
  · exfalso
    rcases hk with rfl | rfl
    · exact ggTWUp_false_one hp hpN hN hC39.1 hcfg
    · exact ggTWUp_false_two hp hpN hN hC39.2 hcfg
  · exfalso
    rcases hk with rfl | rfl
    · exact ggTWUp_false_one hp hpN hN hC510.1 hcfg
    · exact ggTWUp_false_two hp hpN hN hC510.2 hcfg

theorem ggTWSmallA_close_low
    (hC : GGTWSmallCells) (hPZ : GGPZInput) (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput)
    {G : Type} [Group G] [Finite G] {p N k : ℕ} [Fact p.Prime] (hk : k = 1 ∨ k = 2) (hp : 3 ≤ p)
    (hpN : p ∣ N) (hN : N = 5 ∨ N = 6 ∨ N = 7 ∨ N = 9 ∨ N = 10) {B Bs : Subgroup G} {x y : G}
    {L D J K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hxL : x ∉ L)
    {labJ labX : LargeEvenLabel} (hJΛ : LargeEvenInLambda2 labJ) (hXΛ : LargeEvenInLambda2 labX)
    (hJl : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hXl : GGHasLabel labX (↥L ⧸ Subgroup.center ↥L)) (hrow : ggRowTwoNodeSmall p labJ labX)
    (hAtag : labX.tag = .A ∨ labX.tag = .twA) (hXrank : labX.rank = N - 1)
    (hJrank : labJ.rank = N - 3) (hZJ : ¬ p ∣ Nat.card ↥(Subgroup.center ↥J))
    (hCard : Nat.card ↥Bs = p ^ (N - 1)) (hHL : GGTWHLAt p Bs L x)
    (hHK : (N = 5 ∨ N = 6 ∨ N = 9) → GGTWHLAt p Bs K y)
    (hA : GGTWAligned p N k Bs L J K) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  obtain ⟨-, -, -, -, -, hC55, hC36, hC39, hF77, hF510⟩ := hC
  have hJcard : (N = 5 ∨ N = 6 ∨ N = 9) → Nat.card ↥(Bs ⊓ J) = p ^ labJ.rank := fun hN' => by
    rw [hJrank]
    exact ggTW_inf_J_card hp hpN hN' hH hk hCard hZJ (Or.inl hA)
  rcases ggTWSmall_row_of_dvd (Fact.out : p.Prime) hp hpN hN with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hcfg := ggTWLowCfg_of_aligned hFix hFixK hH hxL hk hp (Or.inl rfl) hpN hCard hHL
      (hHK (Or.inl rfl)) hA
    exact ggTWLow_leaf hPZ hk hp hpN (Or.inl rfl) hH hJΛ hXΛ hJl hXl hrow hAtag hXrank hJrank hCard
      (hJcard (Or.inl rfl)) (fun _ => False) hC55
      (fun {_} [AddCommGroup _] [Module (ZMod 5) _] _ {_} _ _ _ _ h _ _ => h.elim)
      (Or.inl ⟨rfl, hcfg⟩)
  · have hcfg := ggTWLowCfg_of_aligned hFix hFixK hH hxL hk hp (Or.inr (Or.inl rfl)) hpN hCard hHL
      (hHK (Or.inr (Or.inl rfl))) hA
    exact ggTWLow_leaf hPZ hk hp hpN (Or.inr (Or.inl rfl)) hH hJΛ hXΛ hJl hXl hrow hAtag hXrank
      hJrank hCard (hJcard (Or.inr (Or.inl rfl))) GGTWLowE6Outcome hC36
      (fun {_} [AddCommGroup _] [Module (ZMod 3) _] ι {_} θ gens hA' S hS hS₁ hS₂ =>
        ggTWLow_weyl_E6 ι θ gens hA' S hS₁ hS₂ hS)
      (Or.inl ⟨rfl, hcfg⟩)
  · exfalso
    have hv := ggTWVCfg_of_aligned hFix hFixK hH hxL hk (Or.inl rfl) hpN hCard hHL hA
    rcases hk with rfl | rfl
    · exact hF77.1 (ggTWSurv1_of_vcfg hp hpN hN hv)
    · exact hF77.2 (ggTWSurv2_of_vcfg hp hpN hN hv)
  · have hcfg := ggTWLowCfg_of_aligned hFix hFixK hH hxL hk hp (Or.inr (Or.inr rfl)) hpN hCard hHL
      (hHK (Or.inr (Or.inr rfl))) hA
    exact ggTWLow_leaf hPZ hk hp hpN (Or.inr (Or.inr rfl)) hH hJΛ hXΛ hJl hXl hrow hAtag hXrank
      hJrank hCard (hJcard (Or.inr (Or.inr rfl))) GGTWLowE8Outcome hC39
      (fun {_} [AddCommGroup _] [Module (ZMod 3) _] ι {_} θ gens hA' S hS hS₁ hS₂ =>
        ggTWLow_weyl_E8 ι θ gens hA' S hS₁ hS₂ hS)
      (Or.inl ⟨rfl, hcfg⟩)
  · exfalso
    have hv := ggTWVCfg_of_aligned hFix hFixK hH hxL hk (Or.inr rfl) hpN hCard hHL hA
    rcases hk with rfl | rfl
    · exact hF510.1 (ggTWSurv1_of_vcfg hp hpN hN hv)
    · exact hF510.2 (ggTWSurv2_of_vcfg hp hpN hN hv)

theorem ggTWSmallA_L_of_aligned
    (hC : GGTWSmallCells) (hPZ : GGPZInput) (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput)
    {G : Type} [Group G] [Finite G] {p N k : ℕ} [Fact p.Prime] (hk : k = 1 ∨ k = 2) (hp : 3 ≤ p)
    (hpN : p ∣ N) (hN : N = 5 ∨ N = 6 ∨ N = 7 ∨ N = 9 ∨ N = 10) {B Bs : Subgroup G} {x y : G}
    {L D J K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hxL : x ∉ L)
    {labJ labX : LargeEvenLabel} (hJΛ : LargeEvenInLambda2 labJ) (hXΛ : LargeEvenInLambda2 labX)
    (hJl : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hXl : GGHasLabel labX (↥L ⧸ Subgroup.center ↥L)) (hrow : ggRowTwoNodeSmall p labJ labX)
    (hAtag : labX.tag = .A ∨ labX.tag = .twA) (hXrank : labX.rank = N - 1)
    (hJrank : labJ.rank = N - 3) (hZJ : ¬ p ∣ Nat.card ↥(Subgroup.center ↥J))
    (hHL : GGTWHLAt p Bs L x)
    (hHK : (N = 5 ∨ N = 6 ∨ N = 9) → Nat.card ↥Bs = p ^ (N - 1) → GGTWHLAt p Bs K y)
    (hA : GGTWAligned p N k Bs L J K) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  rcases ggTW_card_dichotomy hFix hp hpN hN hH hxL hk hA with hlow | hup
  · exact ggTWSmallA_close_low hC hPZ hFix hFixK hk hp hpN hN hH hxL hJΛ hXΛ hJl hXl hrow hAtag
      hXrank hJrank hZJ hlow hHL (fun h9 => hHK h9 hlow) hA
  · exact ggTWSmallA_close_up hC hFix hFixK hk hp hpN hN hH hxL hup hA

end CFSG.StandardType

end

module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitaryAutomizer
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodePermutationDatum
public import CFSG.LocalAnalysis.StandardType.GGTBJTypeAPermutationDatumLE3
public import CFSG.LocalAnalysis.StandardType.GGTDModelU
public import CFSG.LocalAnalysis.StandardType.GGResXDatumAHL
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeParabolic
public import CFSG.LocalAnalysis.StandardType.GGTBJTypeAParabolicLE3

public noncomputable section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag

theorem exists_weyl_datum_of_diagonal_unitary_cover
    {G : Type} [Group G] [Finite G] {p r f : ℕ} [Fact p.Prime]
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f)
    (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f + 1) (hr : 3 ≤ r)
    {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    {ψ : ↥(unitarySU 2 f F (r + 1)) →* X} (hM : UnitTB.Model ψ)
    (hdiag : ∀ a ∈ (ggGamma X hN).range, ∃ t : Fin (r + 1) → F,
      LineU.ActsDiagU ψ a t) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V)
      (ι : Additive ↥Bs ≃+ V) (ρ : Equiv.Perm (Fin (r + 1)) →* MulAut Bs)
      (φ : Fin r → MulAut Bs) (h : Fin r → V) (α : Fin r → Module.Dual (ZMod p) V),
      (∀ σ, (ψ (LineU.permSU hM.field σ) : G) ∈ Subgroup.normalizer (Bs : Set G)) ∧
      (∀ σ b, (ρ σ b : G) = (ψ (LineU.permSU hM.field σ) : G) * b *
        (ψ (LineU.permSU hM.field σ) : G)⁻¹) ∧
      (∀ i, φ i = ρ (Equiv.swap i.castSucc i.succ)) ∧
      (∀ i v, ggLin (p := p) ι (φ i) v = v - α i v • h i) ∧
      (∀ i, GGIsReflection p (φ i)) ∧
      (∀ i j, α i (h j) = (CartanMatrix.A r i j : ZMod p)) ∧
      (∃ e : (CoxeterMatrix.A r).Group ≃* ↥(ggAutomizer X Bs),
        ∀ i, (e ((CoxeterMatrix.A r).simple i) : MulAut Bs) = φ i) ∧
      ggAutomizer X Bs = Subgroup.closure (Set.range φ) := by
  have hp : p.Prime := Fact.out
  have hAe : IsElemAbelian p (ggGamma X hN).range := ggTD_elemAb hN hBs
  have hsc : GGTorusSelfCent p (ggGamma X hN).range := ggTorusSelfCent_ggGamma hN hSC
  obtain ⟨w, hw, hwn⟩ := exists_torusWit_of_model_U hF hp hp2 hpq (by omega) hM hAe hsc hdiag
  obtain ⟨V, hVadd, hVmod, ⟨ι⟩⟩ := exists_ggLinData (p := p) (G := G) (Bs := Bs) hBs
  let : AddCommGroup V := hVadd
  let : Module (ZMod p) V := hVmod
  have hm : Odd (2 ^ f + 1) := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
    rw [hk, pow_succ]
    exact ⟨2 ^ k, by omega⟩
  obtain ⟨hnk, hbk, α, hlin, hpair, -⟩ :=
    ggHLT_lin hm hpq hBs hSC hN w hw V ι Bs.one_mem (Subgroup.one_mem _)
  obtain ⟨e, he⟩ := ggTD_weyl hN hw hp2 hBs hnk
  have hcl := ggTD_closure hN hw hp2 hBs hnk
  let P : Equiv.Perm (Fin (r + 1)) →* ↥(unitarySU 2 f F (r + 1)) :=
    { toFun := LineU.permSU hM.field
      map_one' := UnitAct.permSU_one hM.field
      map_mul' := UnitAct.permSU_mul hM.field }
  let π : Equiv.Perm (Fin (r + 1)) →* G := X.subtype.comp (ψ.comp P)
  have hπ : ∀ σ, π σ ∈ Subgroup.normalizer (Bs : Set G) := by
    intro σ
    have hs : σ ∈ Submonoid.closure
        (Set.range fun i : Fin r => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      trivial
    induction hs using Submonoid.closure_induction with
    | mem σ hσ =>
      obtain ⟨i, rfl⟩ := hσ
      have hi := hnk i
      rw [hwn i] at hi
      exact hi
    | one => exact π.map_one ▸ Subgroup.one_mem _
    | mul σ τ _ _ ihσ ihτ =>
      rw [map_mul]
      exact Subgroup.mul_mem _ ihσ ihτ
  let ρ : Equiv.Perm (Fin (r + 1)) →* MulAut Bs :=
    Bs.normalizerMonoidHom.comp (π.codRestrict (Subgroup.normalizer (Bs : Set G)) hπ)
  have hρ : ∀ σ b, (ρ σ b : G) = (ψ (LineU.permSU hM.field σ) : G) * b *
      (ψ (LineU.permSU hM.field σ) : G)⁻¹ := fun _ _ => rfl
  let φ : Fin r → MulAut Bs := fun i => ggTDρB X Bs (ggTDnH w hnk i)
  have hφ : ∀ i, φ i = ρ (Equiv.swap i.castSucc i.succ) := by
    intro i
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    rw [hρ]
    change (w.n i : G) * b * (w.n i : G)⁻¹ = _
    rw [hwn i]
  have hfx : ∀ i, α i (ι (Additive.ofMul (⟨_, hbk i⟩ : Bs))) = 2 := by
    intro i
    rw [hpair i i, (ggIntCartan_A r).1 i]
    norm_num
  refine ⟨V, hVadd, hVmod, ι, ρ, φ, _, α, hπ, hρ, hφ, hlin, ?_, hpair, ⟨e, he⟩, hcl⟩
  intro i
  exact ggIsReflection_of_eq_reflection hp2 ι (hfx i)
    (ggLin_eq_reflection ι (hfx i) (hlin i))

theorem exists_adapted_weyl_datum_of_diagonal_unitary_block_corank
    {G : Type} [Group G] [Finite G] {p r c f : ℕ} [Fact p.Prime]
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f)
    (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f + 1) (hr : 3 ≤ r) (hcr : c ≤ r) (hrc : 1 ≤ r - c)
    {Bs X J : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    {ψ : ↥(unitarySU 2 f F (r + 1)) →* X} (hM : UnitTB.Model ψ)
    (hdiag : ∀ a ∈ (ggGamma X hN).range, ∃ t : Fin (r + 1) → F,
      LineU.ActsDiagU ψ a t)
    (S : Finset (Fin (r + 1))) (hS : S.card = r + 1 - c)
    (hJ : J = (TableBUE.blockSU (K := F) (n := f) S).map (X.subtype.comp ψ)) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V)
      (ι : Additive ↥Bs ≃+ V) (φ : Fin r → MulAut Bs) (h : Fin r → V)
      (α : Fin r → Module.Dual (ZMod p) V),
      (∀ i v, ggLin (p := p) ι (φ i) v = v - α i v • h i) ∧
      (∀ i, GGIsReflection p (φ i)) ∧
      (∀ i j, α i (h j) = (CartanMatrix.A r i j : ZMod p)) ∧
      (∃ e : (CoxeterMatrix.A r).Group ≃* ↥(ggAutomizer X Bs),
        ∀ i, (e ((CoxeterMatrix.A r).simple i) : MulAut Bs) = φ i) ∧
      ggAutomizer X Bs = Subgroup.closure (Set.range φ) ∧
      ggAutomizer J Bs = Subgroup.closure
        (Set.range (φ ∘ Fin.castLE (by omega : r - c ≤ r))) := by
  obtain ⟨V, hVadd, hVmod, ι, ρ, φ, h, α, hNP, hρ, hφ, hlin, hrefl, hpair, ⟨f, he⟩, hclos⟩ :=
    exists_weyl_datum_of_diagonal_unitary_cover hF hf hp2 hpq (by omega : 3 ≤ r)
      hBs hSC hN hM hdiag
  let : AddCommGroup V := hVadd
  let : Module (ZMod p) V := hVmod
  have hρX : ∀ σ, ρ σ ∈ ggAutomizer X Bs := fun σ =>
    mem_ggAutomizer_iff.mpr ⟨ψ (LineU.permSU hM.field σ), (ψ _).2, hNP σ, hρ σ⟩
  have hJS : ggAutomizer J Bs =
      (fixingSubgroup (Equiv.Perm (Fin (r + 1))) ((S : Set (Fin (r + 1)))ᶜ)).map ρ := by
    rw [hJ]
    exact UnitAct.ggAutomizer_blockSU_ambient_eq_four hM hF (Fact.out : p.Prime) hp2 hpq
      (by omega : 4 ≤ r + 1) hN hBs hSC hdiag hNP ρ hρ S
  obtain ⟨φ', h', α', hlin', hrefl', hpair', ⟨f', hf'⟩, hclos', hJgen'⟩ :=
    exists_adapted_typeA_datum_of_supported_permutations_corank hrc hcr ι ρ hρX
      φ h α hφ hlin hrefl hpair f he hclos S hS hJS
  exact ⟨V, hVadd, hVmod, ι, φ', h', α', hlin', hrefl', hpair', ⟨f', hf'⟩, hclos', hJgen'⟩

theorem ggResSideDatumLE3_of_diagonal_unitary_block
    {G : Type} [Group G] [Finite G] {p r c f : ℕ} [Fact p.Prime]
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f)
    (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f + 1) (hr : 3 ≤ r)
    (hc : 1 ≤ c) (hc3 : c ≤ 3) (hcr : c + 1 ≤ r)
    {Bs X J : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    {ψ : ↥(unitarySU 2 f F (r + 1)) →* X} (hM : UnitTB.Model ψ)
    (hdiag : ∀ a ∈ (ggGamma X hN).range, ∃ t : Fin (r + 1) → F,
      LineU.ActsDiagU ψ a t)
    (S : Finset (Fin (r + 1))) (hS : S.card = r + 1 - c)
    (hJ : J = (TableBUE.blockSU (K := F) (n := f) S).map (X.subtype.comp ψ)) :
    (c = 1 → GGResSideDatum p Bs X J) ∧ (2 ≤ c → GGResLeviSideDatumLE3 p Bs X J) := by
  obtain ⟨V, hVadd, hVmod, ι, φ, h, α, hlin, hrefl, hpair, ⟨e, he⟩, hclos, hJgen⟩ :=
    exists_adapted_weyl_datum_of_diagonal_unitary_block_corank hF hf hp2 hpq hr
      (by omega) (by omega) hBs hSC hN hM hdiag S hS hJ
  let : AddCommGroup V := hVadd
  let : Module (ZMod p) V := hVmod
  exact ggTBJTypeAParabolicLE3 hp2 hc hc3 (by omega) (by omega) rfl rfl hlin hrefl hpair he hclos
    hJgen

theorem ggResTwoNodeSideDatum_of_diagonal_unitary_block
    {G : Type} [Group G] [Finite G] {p r f : ℕ} [Fact p.Prime]
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f)
    (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f + 1) (hr : 4 ≤ r)
    {Bs X J : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    {ψ : ↥(unitarySU 2 f F (r + 1)) →* X} (hM : UnitTB.Model ψ)
    (hdiag : ∀ a ∈ (ggGamma X hN).range, ∃ t : Fin (r + 1) → F,
      LineU.ActsDiagU ψ a t)
    (S : Finset (Fin (r + 1))) (hS : S.card = r - 1)
    (hJ : J = (TableBUE.blockSU (K := F) (n := f) S).map (X.subtype.comp ψ)) :
    GGResTwoNodeSideDatum p Bs X J := by
  obtain ⟨V, hVadd, hVmod, ι, φ, h, α, hlin, hrefl, hpair, ⟨e, he⟩, hclos, hJgen⟩ :=
    exists_adapted_weyl_datum_of_diagonal_unitary_block_corank (c := 2) hF hf hp2 hpq
      (by omega : 3 ≤ r)
      (by omega) (by omega) hBs hSC hN hM hdiag S (by omega) hJ
  let : AddCommGroup V := hVadd
  let : Module (ZMod p) V := hVmod
  exact ggTBJTwoNodeParabolic hp2 hr rfl rfl hlin hrefl hpair he hclos hJgen

end CFSG.StandardType

end

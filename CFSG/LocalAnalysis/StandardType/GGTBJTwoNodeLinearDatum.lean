module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeLinearBlock
public import CFSG.LocalAnalysis.StandardType.GGTDModelA
public import CFSG.LocalAnalysis.StandardType.GGResXDatumAHL
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodePermutationDatum

public noncomputable section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem slPerm_eq_permSL_inv {F : Type} [Field F] [CharP F 2] {d : ℕ}
    (σ : Equiv.Perm (Fin d)) :
    slPerm (show (2 : F) = 0 from CharP.cast_eq_zero F 2) σ = TypeA.permSL σ⁻¹ := by
  apply Subtype.ext
  rw [coe_slPerm, signedPerm_one_eq_permMatrix, TypeA.coe_permSL]

theorem exists_weyl_datum_of_diagonal_linear_cover
    {G : Type} [Group G] [Finite G] {p r : ℕ} [Fact p.Prime]
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F - 1) (hr : 3 ≤ r)
    {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    {ψ : SpecialLinearGroup (Fin (r + 1)) F →* X} (hψ : Function.Surjective ψ)
    (hker : ∀ g, ψ g = 1 → g ∈ scalars (r + 1) F)
    (hdiag : ∀ a ∈ (ggGamma X hN).range, ∃ t : Fin (r + 1) → F,
      TypeANbrDvd.ActsDiag ψ a t) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V)
      (ι : Additive ↥Bs ≃+ V) (ρ : Equiv.Perm (Fin (r + 1)) →* MulAut Bs)
      (φ : Fin r → MulAut Bs) (h : Fin r → V) (α : Fin r → Module.Dual (ZMod p) V),
      (∀ σ, (ψ (TypeA.permSL σ⁻¹) : G) ∈ Subgroup.normalizer (Bs : Set G)) ∧
      (∀ σ b, (ρ σ b : G) = (ψ (TypeA.permSL σ⁻¹) : G) * b *
        (ψ (TypeA.permSL σ⁻¹) : G)⁻¹) ∧
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
  obtain ⟨w, hw, hwn⟩ := exists_torusWit_of_model_A hp hp2 hpF (by omega : 3 ≤ r)
    hψ hker hAe hsc hdiag
  obtain ⟨V, hVadd, hVmod, ⟨ι⟩⟩ := exists_ggLinData (p := p) (G := G) (Bs := Bs) hBs
  let : AddCommGroup V := hVadd
  let : Module (ZMod p) V := hVmod
  have hm : Odd (Nat.card F - 1) := by
    have h2 : 2 ∣ Nat.card F := by
      let : Fintype F := Fintype.ofFinite F
      rw [Nat.card_eq_fintype_card]
      exact (CharP.cast_eq_zero_iff F 2 _).mp (by simp)
    have hpos : 0 < Nat.card F := Nat.card_pos
    obtain ⟨k, hk⟩ := h2
    refine ⟨k - 1, ?_⟩
    omega
  obtain ⟨hnk, hbk, α, hlin, hpair, -⟩ :=
    ggHLT_lin hm hpF hBs hSC hN w hw V ι (Bs.one_mem) (Subgroup.one_mem _)
  obtain ⟨e, he⟩ := ggTD_weyl hN hw hp2 hBs hnk
  have hcl := ggTD_closure hN hw hp2 hBs hnk
  let π : Equiv.Perm (Fin (r + 1)) →* G :=
    X.subtype.comp (ψ.comp (slPerm (show (2 : F) = 0 from CharP.cast_eq_zero F 2)))
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
      simpa only [π, MonoidHom.comp_apply, slPerm_eq_permSL_inv, Equiv.swap_inv,
        Subgroup.coe_subtype] using hi
    | one => exact (π.map_one ▸ Subgroup.one_mem _)
    | mul σ τ _ _ ihσ ihτ =>
      rw [map_mul]
      exact Subgroup.mul_mem _ ihσ ihτ
  let ρ : Equiv.Perm (Fin (r + 1)) →* MulAut Bs :=
    Bs.normalizerMonoidHom.comp (π.codRestrict (Subgroup.normalizer (Bs : Set G)) hπ)
  have hρ : ∀ σ b, (ρ σ b : G) = (ψ (TypeA.permSL σ⁻¹) : G) * b *
      (ψ (TypeA.permSL σ⁻¹) : G)⁻¹ := by
    intro σ b
    change π σ * (b : G) * (π σ)⁻¹ = _
    dsimp only [π, MonoidHom.comp_apply]
    rw [slPerm_eq_permSL_inv]
    rfl
  let φ : Fin r → MulAut Bs := fun i => ggTDρB X Bs (ggTDnH w hnk i)
  have hφ : ∀ i, φ i = ρ (Equiv.swap i.castSucc i.succ) := by
    intro i
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    rw [hρ, Equiv.swap_inv]
    change (w.n i : G) * b * (w.n i : G)⁻¹ = _
    rw [hwn i]
  have hfx : ∀ i, α i (ι (Additive.ofMul (⟨_, hbk i⟩ : Bs))) = 2 := by
    intro i
    rw [hpair i i, (ggIntCartan_A r).1 i]
    norm_num
  have hNperm : ∀ σ, (ψ (TypeA.permSL σ⁻¹) : G) ∈
      Subgroup.normalizer (Bs : Set G) := by
    intro σ
    simpa only [π, MonoidHom.comp_apply, slPerm_eq_permSL_inv, Subgroup.coe_subtype]
      using hπ σ
  refine ⟨V, hVadd, hVmod, ι, ρ, φ, _, α, hNperm, hρ, hφ, hlin, ?_, hpair, ⟨e, he⟩, hcl⟩
  intro i
  exact ggIsReflection_of_eq_reflection hp2 ι (hfx i)
    (ggLin_eq_reflection ι (hfx i) (hlin i))

theorem exists_adapted_weyl_datum_of_diagonal_linear_block
    {G : Type} [Group G] [Finite G] {p r : ℕ} [Fact p.Prime]
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F - 1) (hr : 4 ≤ r)
    {Bs X J : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    {ψ : SpecialLinearGroup (Fin (r + 1)) F →* X} (hψ : Function.Surjective ψ)
    (hker : ∀ g, ψ g = 1 → g ∈ scalars (r + 1) F)
    (hdiag : ∀ a ∈ (ggGamma X hN).range, ∃ t : Fin (r + 1) → F,
      TypeANbrDvd.ActsDiag ψ a t)
    (S : Finset (Fin (r + 1))) (hS : S.card = r - 1)
    (hJ : J = (CFSG.SeitzReduction.LinearPilot.blockSpecialLinear S).map
      (X.subtype.comp ψ)) :
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
        (Set.range (φ ∘ Fin.castLE (by omega : r - 2 ≤ r))) := by
  classical
  obtain ⟨V, hVadd, hVmod, ι, ρ, φ, h, α, hNP, hρ, hφ, hlin, hrefl, hpair, ⟨f, hf⟩, hclos⟩ :=
    exists_weyl_datum_of_diagonal_linear_cover hp2 hpF (by omega : 3 ≤ r) hBs hSC hN hψ hker hdiag
  let : AddCommGroup V := hVadd
  let : Module (ZMod p) V := hVmod
  have hρX : ∀ σ, ρ σ ∈ ggAutomizer X Bs := fun σ =>
    mem_ggAutomizer_iff.mpr ⟨ψ (TypeA.permSL σ⁻¹), (ψ _).2, hNP σ, hρ σ⟩
  have hJS : ggAutomizer J Bs =
      (fixingSubgroup (Equiv.Perm (Fin (r + 1))) ((S : Set (Fin (r + 1)))ᶜ)).map ρ := by
    rw [hJ, ← Subgroup.map_map]
    exact TypeANbrDvd.ggAutomizer_blockSpecialLinear_ambient_eq (Fact.out : p.Prime)
      hp2 hpF hN hBs hSC hψ hker hdiag hNP ρ hρ S
  obtain ⟨φ', h', α', hlin', hrefl', hpair', hf', hclos', hJgen'⟩ :=
    exists_adapted_typeA_datum_of_supported_permutations hr ι ρ hρX φ h α hφ hlin
      hrefl hpair f hf hclos S hS hJS
  exact ⟨V, hVadd, hVmod, ι, φ', h', α', hlin', hrefl', hpair', hf', hclos', hJgen'⟩

end CFSG.StandardType

end

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKMcLDefs
public import CFSG.Quasithin.Background.B4Models
public import CFSG.HardMathSupport.Solomon.Coordinator.I28_14SymModel
import CFSG.Quasithin.Background.B5FinPerm
import CFSG.Quasithin.Background.G64Realize
import CFSG.Quasithin.Background.RealizesFaithful

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.ComponentClassification.OutcomeLocal

private noncomputable def s15k_norm_coordEquiv (m : ℕ) :
    ↥(FFModel.symDn m).sec ≃* Multiplicative (sumZero m) where
  toFun x :=
    Multiplicative.ofAdd ⟨Multiplicative.toAdd (x.1 : G6.PermMod m), mem_sumZero.mpr x.2⟩
  invFun y :=
    ⟨Multiplicative.ofAdd (Multiplicative.toAdd y).1,
      G6.mem_coreMod.mpr (Multiplicative.toAdd y).2⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv y := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    rfl
  map_mul' x y := rfl

theorem s15k_norm_symModel {W : Type} [CommGroup W] {J : Subgroup (MulAut W)}
    {R : Subgroup W} {m : ℕ} (hm : 5 ≤ m) (h : SymmetricNatural J R ⊥ m) (D : McRep J R) :
    ∃ M : SymModel m D.V, M.ψ.range = D.ρ.range := by
  obtain ⟨π₁, hπ⟩ := h
  let π : Equiv.Perm (Fin m) →* ↥J := π₁
  have hinj : Function.Injective π :=
    FFModel.RealizesVia.injective_of_faithful_on (G64.symDn_faithful hm) hπ
  obtain ⟨hsurj, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := hπ
  have hβinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.1 ((hβk u).1 hu))
  let qEquiv : ↥R ≃* ↥(FFModel.symDn m).sec ⧸
      (FFModel.symDn m).ker.subgroupOf (FFModel.symDn m).sec :=
    MulEquiv.ofBijective β ⟨hβinj, hβs⟩
  let c := s15k_norm_coordEquiv m
  let g0 : Multiplicative (sumZero m) →* Multiplicative D.V :=
    D.e.toMonoidHom.comp (qEquiv.symm.toMonoidHom.comp
      ((QuotientGroup.mk' _).comp c.symm.toMonoidHom))
  let γ : sumZero m →ₗ[ZMod 2] D.V :=
    { toFun := fun y => Multiplicative.toAdd (g0 (Multiplicative.ofAdd y))
      map_add' := fun y y' => by
        show Multiplicative.toAdd (g0 (Multiplicative.ofAdd (y + y'))) = _
        rw [ofAdd_add, map_mul]
        rfl
      map_smul' := fun a y => by
        rcases zmod2_eq_zero_or_one a with rfl | rfl
        · simp
        · simp }
  have hγ : ∀ y : sumZero m, γ y = Multiplicative.toAdd (D.e (qEquiv.symm
      (QuotientGroup.mk (c.symm (Multiplicative.ofAdd y))))) := fun y => rfl
  have hsurj' : Function.Surjective γ := by
    intro v
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (qEquiv (D.e.symm (Multiplicative.ofAdd v)))
    refine ⟨Multiplicative.toAdd (c x), ?_⟩
    rw [hγ, ofAdd_toAdd, MulEquiv.symm_apply_apply, hx, MulEquiv.symm_apply_apply,
      MulEquiv.apply_symm_apply]
    rfl
  have hequi : ∀ (σ : Equiv.Perm (Fin m)) (y : sumZero m),
      ((D.ρ.comp π σ : LinearMap.GeneralLinearGroup (ZMod 2) D.V) : D.V →ₗ[ZMod 2] D.V) (γ y) =
        γ (sumZeroEquiv σ y) := by
    intro σ y
    let x : ↥(FFModel.symDn m).sec := c.symm (Multiplicative.ofAdd y)
    let u : ↥R := qEquiv.symm (QuotientGroup.mk x)
    have hu : β u = QuotientGroup.mk x := qEquiv.apply_symm_apply _
    have hmem : ((π σ : ↥J) : MulAut W) (u : W) ∈ R := D.stable _ (π σ).2 _ u.2
    have hx' : (FFModel.symDn m).act σ x.1 ∈ (FFModel.symDn m).sec :=
      G6.permAct_mem_coreMod σ x.2
    have h1 := hβe σ u x hmem hx' hu
    have h2 : (⟨((π σ : ↥J) : MulAut W) (u : W), hmem⟩ : ↥R) =
        qEquiv.symm (QuotientGroup.mk ⟨(FFModel.symDn m).act σ x.1, hx'⟩) := by
      apply qEquiv.injective
      rw [MulEquiv.apply_symm_apply]
      exact h1
    have h3 : c.symm (Multiplicative.ofAdd (sumZeroEquiv σ y)) =
        ⟨(FFModel.symDn m).act σ x.1, hx'⟩ := by
      apply c.injective
      rw [MulEquiv.apply_symm_apply]
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      funext i
      rfl
    show ((D.ρ (π σ) : D.V →ₗ[ZMod 2] D.V)) (γ y) = γ (sumZeroEquiv σ y)
    rw [hγ y, hγ, h3, ← h2, D.hρ (π σ) u hmem, toAdd_ofAdd]
  have hker : ∀ y : sumZero m, γ y = 0 → ∃ a : ZMod 2, (y : Fin m → ZMod 2) = fun _ => a := by
    intro y hy
    have h1 : D.e (qEquiv.symm (QuotientGroup.mk (c.symm (Multiplicative.ofAdd y)))) = 1 := by
      apply Multiplicative.toAdd.injective
      rw [← hγ y]
      exact hy
    have h2 : qEquiv.symm (QuotientGroup.mk (c.symm (Multiplicative.ofAdd y))) = 1 :=
      D.e.injective (by rw [h1, map_one])
    have h3 : (QuotientGroup.mk (c.symm (Multiplicative.ofAdd y)) :
        ↥(FFModel.symDn m).sec ⧸
          (FFModel.symDn m).ker.subgroupOf (FFModel.symDn m).sec) = 1 := by
      have := congrArg qEquiv h2
      rwa [MulEquiv.apply_symm_apply, map_one] at this
    have h4 := (QuotientGroup.eq_one_iff _).1 h3
    have h5 : (c.symm (Multiplicative.ofAdd y)).1 ∈
        Subgroup.zpowers (G6.allOnes m) ⊓ G6.coreMod m := h4
    obtain ⟨hz, -⟩ := Subgroup.mem_inf.1 h5
    rcases B5FinPerm.mem_zpowers_allOnes_iff.1 hz with h6 | h6
    · refine ⟨0, ?_⟩
      have h7 : Multiplicative.toAdd (Multiplicative.ofAdd (y : Fin m → ZMod 2)) = 0 :=
        congrArg Multiplicative.toAdd h6
      funext i
      exact congrFun h7 i
    · refine ⟨1, ?_⟩
      have h7 : Multiplicative.toAdd (Multiplicative.ofAdd (y : Fin m → ZMod 2)) =
          fun _ => (1 : ZMod 2) := congrArg Multiplicative.toAdd h6
      funext i
      exact congrFun h7 i
  refine ⟨{ ψ := D.ρ.comp π
            γ := γ
            surj := hsurj'
            equivariant := hequi
            ker_const := hker
            inj := D.inj.comp hinj }, ?_⟩
  apply le_antisymm
  · rintro _ ⟨σ, rfl⟩
    exact ⟨π σ, rfl⟩
  · rintro _ ⟨j, rfl⟩
    obtain ⟨σ, rfl⟩ := hsurj j
    exact ⟨σ, rfl⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

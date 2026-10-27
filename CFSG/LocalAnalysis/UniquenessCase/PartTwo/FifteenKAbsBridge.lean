module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.F918V2Defs2
public import CFSG.Quasithin.EmptyFaithful.SzN15Nat

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

open scoped Matrix

theorem s15k_abs_apply_of_endUnits {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {Z : Subgroup W} (hE : Z391.EndUnitsTrivial H Z) {x : MulAut W} (hx : x ∈ stabSub Z)
    (hc : ∀ k ∈ H, x * k = k * x) : ∀ z ∈ Z, x z = z := by
  intro z hz
  have hφ : resHom Z ⟨x, hx⟩ = MulEquiv.refl _ := by
    refine hE (resHom Z ⟨x, hx⟩) ?_
    intro l a b hab
    have hl : ∀ w : W, l • w = (l : MulAut W) w := fun w => rfl
    rw [hl] at hab ⊢
    change (l : MulAut W) (x a) = x b
    rw [← hab]
    exact (congrArg (fun f : MulAut W => f (a : W)) (hc l l.2)).symm
  have := congrArg (fun f : MulAut ↥Z => ((f ⟨z, hz⟩ : ↥Z) : W)) hφ
  exact this

theorem s15k_abs_endUnits_of_comm {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {U : Subgroup W} {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)}
    (hcomm : ∀ g : (ι → F) ≃+ (ι → F),
      (∀ γ ∈ Γ, ∀ v : ι → F, g ((γ : Matrix ι ι F) *ᵥ v) = (γ : Matrix ι ι F) *ᵥ g v) →
        ∀ v, g v = v)
    (h : (FFModel.nat Γ).Realizes H U ⊥) : Z391.EndUnitsTrivial H U := by
  obtain ⟨π, hπ⟩ := h
  let R := CFSG.Quasithin.SzN15.NatReal.of_realizesVia hπ
  obtain ⟨β, hβsurj, hβker, hβe⟩ := R.exists_β
  have hβinj : Function.Injective β := by
    intro a b hab
    have h1 : β (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : ((a * b⁻¹ : ↥U) : W) ∈ (⊥ : Subgroup W) := (hβker (a * b⁻¹)).1 h1
    have h3 : a * b⁻¹ = 1 := Subtype.ext (by simpa using Subgroup.mem_bot.1 h2)
    exact mul_inv_eq_one.1 h3
  let βe : ↥U ≃* Multiplicative (ι → F) := MulEquiv.ofBijective β ⟨hβinj, hβsurj⟩
  have hβe_apply : ∀ p : ↥U, βe p = β p := fun _ => rfl
  intro φ hφ
  let f : Multiplicative (ι → F) ≃* Multiplicative (ι → F) :=
    βe.symm.trans (φ.trans βe)
  have hfβ : ∀ p : ↥U, f (βe p) = βe (φ p) := fun p => by simp [f]
  let g : (ι → F) ≃+ (ι → F) := AddEquiv.toMultiplicative.symm f
  have hgapp : ∀ v : ι → F, g v = Multiplicative.toAdd (f (Multiplicative.ofAdd v)) :=
    fun _ => rfl
  have hg0 : ∀ p : ↥U, g (Multiplicative.toAdd (βe p)) =
      Multiplicative.toAdd (βe (φ p)) := by
    intro p
    rw [hgapp, ofAdd_toAdd, hfβ]
  have hg : ∀ γ ∈ Γ, ∀ v : ι → F,
      g ((γ : Matrix ι ι F) *ᵥ v) = (γ : Matrix ι ι F) *ᵥ g v := by
    intro γ hγ v
    let γ' : ↥Γ := ⟨γ, hγ⟩
    obtain ⟨x, rfl⟩ : ∃ x : ↥U, Multiplicative.toAdd (βe x) = v :=
      ⟨βe.symm (Multiplicative.ofAdd v), by rw [MulEquiv.apply_symm_apply, toAdd_ofAdd]⟩
    have hnat : ∀ (y : ↥U) (hu : ((π γ' : ↥H) : MulAut W) (y : W) ∈ U),
        Multiplicative.toAdd (βe ⟨((π γ' : ↥H) : MulAut W) (y : W), hu⟩) =
          (γ : Matrix ι ι F) *ᵥ Multiplicative.toAdd (βe y) := by
      intro y hu
      have h := hβe γ' y hu
      calc Multiplicative.toAdd (βe ⟨((π γ' : ↥H) : MulAut W) (y : W), hu⟩)
          = Multiplicative.toAdd (β ⟨((π γ' : ↥H) : MulAut W) (y : W), hu⟩) := by
            simp only [hβe_apply]
        _ = Multiplicative.toAdd (natAct Γ γ' (β y)) := congrArg Multiplicative.toAdd h
        _ = (γ : Matrix ι ι F) *ᵥ Multiplicative.toAdd (βe y) := by
            simp only [hβe_apply]
            rfl
    have hmemx : ((π γ' : ↥H) : MulAut W) (x : W) ∈ U := R.U_inv (π γ') x x.2
    have e2 : φ ⟨((π γ' : ↥H) : MulAut W) (x : W), hmemx⟩ =
        ⟨((π γ' : ↥H) : MulAut W) ((φ x : ↥U) : W),
          R.U_inv (π γ') (φ x) (φ x).2⟩ :=
      Subtype.ext (hφ (π γ') x ⟨((π γ' : ↥H) : MulAut W) (x : W), hmemx⟩ rfl).symm
    rw [← hnat x hmemx, hg0, e2, hg0, hnat (φ x) (R.U_inv (π γ') (φ x) (φ x).2)]
  have hid := hcomm g hg
  refine MulEquiv.ext fun x => ?_
  apply βe.injective
  apply Multiplicative.toAdd.injective
  rw [← hg0 x, hid]
  rfl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

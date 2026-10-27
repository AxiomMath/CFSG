module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSp6H1Bridge
public import CFSG.Quasithin.Background.B4L3Coord
public import CFSG.ClassicalGroups.Symplectic.StandardForm
public import CFSG.Quasithin.Background.JonesParshallSymplecticBinary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.ClassicalGroups.Symplectic
  CFSG.LocalAnalysis.ComponentInitial CFSG.Quasithin.JonesParshall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

theorem s16sp_module_data {W : Type} [CommGroup W] [Finite W] (hexp : ∀ w : W, w ^ 2 = 1)
    {H : Subgroup (MulAut W)} {Z : Subgroup W} (hZ : Z ≤ fixV H) (hcomm : commV H = ⊤)
    (hreal : (FFModel.nat (StatedSp 3 (ZMod 2))).Realizes H ⊤ Z) :
    ∃ (M : Type) (_ : AddCommGroup M) (_ : Module (ZMod 2) M) (_ : Finite M)
      (θ : W ≃* Multiplicative M)
      (ρM : Representation (ZMod 2) (bilinIsometryGroup (spForm 3 (ZMod 2))) M)
      (q : M →ₗ[ZMod 2] (Fin 3 ⊕ Fin 3 → ZMod 2))
      (π : bilinIsometryGroup (spForm 3 (ZMod 2)) →* ↥H),
      Function.Surjective π ∧ Function.Surjective q ∧
      (∀ g m, q (ρM g m) = binarySymplecticNatural (spForm 3 (ZMod 2)) g (q m)) ∧
      (∀ g m, q m = 0 → ρM g m = m) ∧
      (∀ ψ : M →ₗ[ZMod 2] ZMod 2, (∀ g m, ψ (ρM g m) = ψ m) → ψ = 0) ∧
      (∀ (g : bilinIsometryGroup (spForm 3 (ZMod 2))) (w : W),
        θ ((π g : MulAut W) w) = Multiplicative.ofAdd (ρM g (Multiplicative.toAdd (θ w)))) ∧
      (∀ w : W, q (Multiplicative.toAdd (θ w)) = 0 ↔ w ∈ Z) := by
  obtain ⟨π₀, hπ₀⟩ := hreal
  obtain ⟨β, hβs, hβk, hβe⟩ :=
    FFModel.RealizesVia.coord (D := FFModel.nat (StatedSp 3 (ZMod 2))) rfl rfl hπ₀
  let Γ := ↥(bilinIsometryGroup (spForm 3 (ZMod 2)))
  let ρQ : Representation (ZMod 2) Γ (Fin 3 ⊕ Fin 3 → ZMod 2) :=
    binarySymplecticNatural (spForm 3 (ZMod 2))
  let π : Γ →* ↥H := π₀.comp (spEquiv (m := 3) (K := ZMod 2)).symm.toMonoidHom
  let β' : W →* Multiplicative (Fin 3 ⊕ Fin 3 → ZMod 2) :=
    β.comp (Subgroup.topEquiv (G := W)).symm.toMonoidHom
  have hβs' : Function.Surjective β' := by
    intro x
    obtain ⟨y, hy⟩ := hβs x
    exact ⟨Subgroup.topEquiv y, by
      show β (Subgroup.topEquiv.symm (Subgroup.topEquiv y)) = x
      rw [MulEquiv.symm_apply_apply]
      exact hy⟩
  have hβk' : ∀ w : W, β' w = 1 ↔ w ∈ Z := by
    intro w
    have h := hβk ((Subgroup.topEquiv (G := W)).symm w)
    rw [Subgroup.topEquiv_symm_apply_coe] at h
    exact h
  have hπs : Function.Surjective π := by
    intro x
    obtain ⟨y, hy⟩ := hπ₀.1 x
    let y' : StatedSp 3 (ZMod 2) := y
    have hy' : π₀ y' = x := hy
    refine ⟨spEquiv (m := 3) (K := ZMod 2) y', ?_⟩
    show π₀ ((spEquiv (m := 3) (K := ZMod 2)).symm
      (spEquiv (m := 3) (K := ZMod 2) y')) = x
    rw [MulEquiv.symm_apply_apply]
    exact hy'
  have hβe' : ∀ (γ : Γ) (w : W),
      β' ((π γ : MulAut W) w) =
        Multiplicative.ofAdd (ρQ γ (Multiplicative.toAdd (β' w))) := by
    intro γ w
    set γ' : StatedSp 3 (ZMod 2) := (spEquiv (m := 3) (K := ZMod 2)).symm γ with hdef
    have hγ : spEquiv (m := 3) (K := ZMod 2) γ' = γ := by
      rw [hdef]; exact MulEquiv.apply_symm_apply _ _
    have hDact : ∀ x : Multiplicative (Fin 3 ⊕ Fin 3 → ZMod 2),
        (FFModel.nat (StatedSp 3 (ZMod 2))).act γ' x =
          Multiplicative.ofAdd (Matrix.mulVec
            ((γ' : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)) :
              Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2))
            (Multiplicative.toAdd x)) := fun _ => rfl
    have hρ : ∀ x : Fin 3 ⊕ Fin 3 → ZMod 2,
        ρQ γ x = Matrix.mulVec
          ((γ' : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)) :
            Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) x := by
      intro x
      rw [show ρQ γ x = OddQuadraticFive.sE γ x from rfl, ← hγ]
      rw [show OddQuadraticFive.sE (spEquiv (m := 3) (K := ZMod 2) γ') x =
          (spEquiv (m := 3) (K := ZMod 2) γ').app x from rfl,
        spEquiv_app (m := 3) (K := ZMod 2) γ' x]
    have h := hβe γ' ((Subgroup.topEquiv (G := W)).symm w) (Subgroup.mem_top _)
    have hL : β' ((π γ : MulAut W) w) =
        (FFModel.nat (StatedSp 3 (ZMod 2))).act γ' (β' w) := h
    rw [hL, hDact, hρ]
  obtain ⟨M, hMadd, hMmod, hMfin, θ, ρM, q, hq, heq, hfix, hinv, hθ, hker⟩ :=
    s16sp_module_data_of_cover hexp hZ hcomm π hπs ρQ β' hβs' hβk' hβe'
  exact ⟨M, hMadd, hMmod, hMfin, θ, ρM, q, π, hπs, hq, heq, hfix, hinv, hθ, hker⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end

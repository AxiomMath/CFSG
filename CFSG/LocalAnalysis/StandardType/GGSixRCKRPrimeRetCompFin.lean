module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetIota
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetPin
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetCompFinAux
public import CFSG.LieType.Steinberg.Isogeny.E6
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviHom
public import CFSG.LieType.CurtisTits.ExceptionalQuasisimple
public import CFSG.LieType.CurtisTits.Recognition

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.Timmesfeld
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule

theorem rckE6_theta_fin
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {β : Fin 6 → Fin τ.rank → ℤ} (hroot : ∀ b, IsRoot τ (β b))
    {ι : (Fin τ.rank → ℤ) → (Fin Tag.E6.rank → ℤ)} (hι : RetIotaSpec β ι)
    (K' : Type) [Field K'] [Finite K'] [CharP K' 2] :
    ∃ θK : ↥(rootSpan τ K' (rootsOfFam β Set.univ)) →* ↥(adjointGroup Tag.E6 K'),
      (∀ γ ∈ rootsOfFam β Set.univ, ∀ (c : K')
        (hm : pinnedX τ K' γ c ∈ rootSpan τ K' (rootsOfFam β Set.univ)),
        ((θK ⟨pinnedX τ K' γ c, hm⟩ : ↥(adjointGroup Tag.E6 K')) : ModGL Tag.E6 K') =
          pinnedX Tag.E6 K' (ι γ) c) ∧
      Function.Surjective θK ∧
      (∀ x, θK x = 1 → x ∈ Subgroup.center ↥(rootSpan τ K' (rootsOfFam β Set.univ))) ∧
      Group.IsPerfect ↥(rootSpan τ K' (rootsOfFam β Set.univ)) := by
  classical
  obtain ⟨Ψ, hΨxm, hΨrange, hΨker⟩ := rckE6_pinCanon hτ hroot hι (RingEquiv.refl K')
  let G := rootSpan τ K' (rootsOfFam β Set.univ)
  let Ψ' : ↥(e6Data_valid.minGroup K') →* ↥G :=
    Ψ.codRestrict G (fun x => by
      change Ψ x ∈ rootSpan τ K' (rootsOfFam β Set.univ)
      rw [← hΨrange]
      exact MonoidHom.mem_range.2 ⟨x, rfl⟩)
  have hΨ'surj : Function.Surjective Ψ' := by
    intro y
    have hy : (y : ModGL τ K') ∈ Ψ.range := by rw [hΨrange]; exact y.2
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 hy
    exact ⟨x, Subtype.ext (by simpa [Ψ'] using hx)⟩
  have hcenter_le : Subgroup.center ↥(e6Data_valid.minGroup K') ≤ (e6Isogeny K').ker :=
    rckCf_center_le_isogeny_ker K'
  have hker : Ψ'.ker ≤ (e6Isogeny K').ker := by
    intro x hx
    have hx1 : Ψ x = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
      simpa [Ψ'] using this
    exact hcenter_le (hΨker (MonoidHom.mem_ker.2 hx1))
  let θK : ↥G →* ↥(adjointGroup Tag.E6 K') :=
    MonoidHom.liftOfSurjective Ψ' hΨ'surj ⟨e6Isogeny K', hker⟩
  have hθ : ∀ u : ↥(e6Data_valid.minGroup K'), θK (Ψ' u) = e6Isogeny K' u := fun u =>
    MonoidHom.liftOfRightInverse_comp_apply (f := Ψ')
      (f_inv := Function.surjInv hΨ'surj) (hf := Function.rightInverse_surjInv hΨ'surj)
      (g := ⟨e6Isogeny K', hker⟩) (x := u)
  refine ⟨θK, ?_, ?_, ?_, ?_⟩
  ·
    intro γ hγ c hm
    obtain ⟨hmaps, -, -⟩ := hι.1
    obtain ⟨-, -, hsum, -, -⟩ := hι
    have hγE : IsRoot Tag.E6 (ι γ) := hmaps hγ
    have hsumγ : (∑ j : Fin 6, (ι γ) j • β j) = γ := hsum γ hγ
    have hΨu : Ψ (e6Data_valid.xm K' (ι γ) c) = pinnedX τ K' γ c := by
      have h := hΨxm (ι γ) hγE c
      rw [hsumγ] at h
      simpa using h
    have hu : Ψ' (e6Data_valid.xm K' (ι γ) c) = ⟨pinnedX τ K' γ c, hm⟩ := by
      apply Subtype.ext
      simpa [Ψ'] using hΨu
    rw [← hu, hθ (e6Data_valid.xm K' (ι γ) c)]
    exact CFSG.SeitzReduction.E6Pilot.coe_e6Isogeny_xm hγE c
  ·
    intro y
    obtain ⟨u, rfl⟩ := e6Isogeny_surjective K' y
    exact ⟨Ψ' u, hθ u⟩
  ·
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨u, rfl⟩ := hΨ'surj x
    obtain ⟨v, rfl⟩ := hΨ'surj y
    have hu : u ∈ (e6Isogeny K').ker := by
      rw [MonoidHom.mem_ker]
      rw [← hθ u]; exact hx
    have huC : u ∈ Subgroup.center ↥(e6Data_valid.minGroup K') :=
      CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple
        (φ := e6Isogeny K')
        (CFSG.LieType.CurtisTits.isQuasisimple_e6 (k := K')) (e6Isogeny_ne_one K') hu
    have huv : v * u = u * v := Subgroup.mem_center_iff.1 huC v
    rw [← map_mul, ← map_mul]
    exact congrArg Ψ' huv
  ·
    apply Group.isPerfect_def.2
    have hcomm : _root_.commutator ↥(e6Data_valid.minGroup K') = ⊤ :=
      (CFSG.LieType.CurtisTits.isQuasisimple_e6 (k := K')).1.commutator_eq_top
    have hmap := congrArg (Subgroup.map Ψ') hcomm
    rw [_root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective Ψ' hΨ'surj] at hmap
    rwa [_root_.commutator_def]

end CFSG.StandardType.RCKRP

end

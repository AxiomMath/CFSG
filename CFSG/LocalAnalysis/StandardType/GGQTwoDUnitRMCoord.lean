module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMStabDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitCoord
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBaseThm
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitCoordStdA

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn.QTwo

variable {G : Type} [Group G] [Finite G]

private lemma qtwoDB35_eq_dPerm_of_fix {m : ℕ} {w : DVec m ≃ₗ[ZMod 3] DVec m}
    (hw : w ∈ dEven m) (h1 : w (fun _ => 1) = fun _ => 1) :
    ∃ σ : Equiv.Perm (Fin m), w = dPerm m σ := by
  classical
  obtain ⟨σ, c, -, -, hact⟩ := hw
  refine ⟨σ, (dBasis m).ext' fun i => ?_⟩
  have hsum : (fun _ => (1 : ZMod 3)) = ∑ j : Fin m, dBasis m j := by
    funext k
    simp [dBasis, Finset.sum_apply, Pi.single_apply]
  have hci : c i = 1 := by
    have h : w (fun _ => 1) (σ i) = 1 := congrFun h1 (σ i)
    rw [hsum, map_sum, Finset.sum_apply] at h
    simp only [hact] at h
    simpa [dBasis, Pi.single_apply, σ.injective.eq_iff] using h
  rw [hact i, hci, one_smul, dPerm_apply]

private lemma qtwoDB35_join_acts {Bs : Subgroup G} {x : G} {L : Subgroup G}
    {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} {m : ℕ} {e' : Fin m ≃ ι} {F0 : Type} [Field F0]
    [Finite F0] [CharP F0 2] {ψ : Su F0 2 1 m →* G}
    {ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer L Bs)} {βL : Additive ↥Bs ≃+ DVec m} {ω : F0ˣ}
    (hc : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω) (g : M.Group) :
    ∃ w ∈ dEven m, ∀ s : ↥Bs,
      βL (Additive.ofMul (((e g : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) s)) =
        w (βL (Additive.ofMul s)) := by
  induction g using M.toCoxeterSystem.simple_induction_left with
  | one => exact ⟨1, one_mem _, fun s => by simp⟩
  | mul_simple_left g i ih =>
    obtain ⟨w, hw, hws⟩ := ih
    have hr : (((e (M.simple i)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈ ggCoxRefl M e :=
      show ∃ (u : M.Group) (j : ι), _ = _ from ⟨1, i, by rw [one_mul, inv_one, mul_one]⟩
    obtain ⟨sgn, a, b, hab, hrs⟩ := hc.coxRoot _ hr
    refine ⟨dTau m sgn a b * w, mul_mem (dTau_mem_dEven m sgn hab) hw, fun s => ?_⟩
    rw [CoxeterMatrix.toCoxeterSystem_simple, map_mul, Subgroup.coe_mul, MulAut.mul_apply,
      hrs, hws, LinearEquiv.mul_apply]

theorem qtwoUnitCoords_rmBaseCoord {Bs : Subgroup G} {x : G} {L : Subgroup G}
    {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} {m : ℕ} {e' : Fin m ≃ ι} {F0 : Type} [Field F0]
    [Finite F0] [CharP F0 2] {ψ : Su F0 2 1 m →* G}
    {ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer L Bs)} {βL : Additive ↥Bs ≃+ DVec m} {ω : F0ˣ}
    (hc : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω) (hx : x ∈ Bs) :
    qtwoDActsAs βL (ggAutomizerJoin L Bs 𝒦) (dEven m) ∧
      βL (Additive.ofMul ⟨x, hx⟩) = (fun _ => 1) ∧
        qtwoDActsAs βL (ggAutomizer L Bs) (dEvenStab m (fun _ => 1)) := by
  refine ⟨⟨fun a ha => ?_, hc.join_onto⟩, hc.x_coord hx, fun a ha => ?_, fun w hw => ?_⟩
  · obtain ⟨g, hg⟩ := e.surjective ⟨a, ha⟩
    obtain ⟨w, hw, hws⟩ := qtwoDB35_join_acts hc g
    refine ⟨w, hw, fun s => ?_⟩
    have h := hws s
    rw [hg] at h
    exact h
  · obtain ⟨σ, hσ⟩ := ε.surjective ⟨a, ha⟩
    have hmem : dPerm m σ ∈ dEvenStab m (fun _ => 1) :=
      show dPerm m σ ∈ dEven m ∧ _ from ⟨dPerm_mem_dEven m σ, qtwoDB32_dPerm_const σ 1⟩
    refine ⟨dPerm m σ, hmem, fun s => ?_⟩
    have h := hc.perm σ s
    rw [hσ] at h
    exact h
  · have hw' : w ∈ dEven m ∧ w (fun _ => 1) = fun _ => 1 := hw
    obtain ⟨σ, rfl⟩ := qtwoDB35_eq_dPerm_of_fix hw'.1 hw'.2
    exact ⟨((ε σ : ↥(ggAutomizer L Bs)) : MulAut ↥Bs), (ε σ).2, hc.perm σ⟩


theorem ggQTwoDUnit_rmBaseCoord (hRig : GGLabelRigidInput) (hTBF : GGTBFixInput)
    (hWI : GGNbrInnerWeylInput) {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e)
    {m : ℕ} (e' : Fin m ≃ ι) (hm : 7 ≤ m) (hM : M = (ggCoxeterMatrixD m).reindex e')
    (hL : qtwoOrthL.compl G L 𝒦) :
    ∃ (hx : x ∈ Bs) (β₀ : Additive ↥Bs ≃+ DVec m),
      qtwoDActsAs β₀ (ggAutomizerJoin L Bs 𝒦) (dEven m) ∧
        ∃ ε : DVec m, (∀ i, ε i = 1 ∨ ε i = -1) ∧ β₀ (Additive.ofMul ⟨x, hx⟩) = ε ∧
          qtwoDActsAs β₀ (ggAutomizer L Bs) (dEvenStab m ε) := by
  obtain ⟨F0, hF0, hF0fin, hF0char, ψ, ε, hbase⟩ :=
    ggQTwoDUnit_base hRig hTBF hWI hcfg e' hm hM hL
  letI : Field F0 := hF0
  letI : Finite F0 := hF0fin
  letI : CharP F0 2 := hF0char
  obtain ⟨βL, ω, hc⟩ := ggQTwoDUnit_coords hTBF hWI hcfg e' (by omega) hM hbase
  obtain ⟨hjoin, hxc, hstab⟩ := qtwoUnitCoords_rmBaseCoord hc hbase.x_mem
  exact ⟨hbase.x_mem, βL, hjoin, fun _ => 1, fun _ => Or.inl rfl, hxc, hstab⟩

end CFSG.StandardType.QTwo

end

module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelAssemble
public import CFSG.LocalAnalysis.StandardType.GGE6DepFrameDefs

public section

namespace CFSG.StandardType.E6Dep.ZL

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc.E6Three
  CFSG.StandardType.E6ThreeModel

variable {R : Type} [Group R] [Finite R] {L' : Type} [Group L'] [Finite L'] (D : FrameData R)

theorem zl_model_odd (hAL : GGAbelianLift) (hD : D.Good)
    {ψ : L' →* R} (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hcard : Nat.card ψ.ker = 1 ∨ Nat.card ψ.ker = 3)
    {ρ : MulAut L' →* MulAut R} (hρ : ∀ a l, ρ a (ψ l) = ψ (a l)) (hρinj : Function.Injective ρ)
    {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian 3 A) (hsc : GGTorusSelfCent 3 A)
    (hal : ∀ a ∈ A, ρ a ∈ D.diag.range) :
    ∃ (Φ : A →* Multiplicative (Fin 6 → ZMod 3)) (w : Fin 6 → L'),
      GGE6ThreeWeylModelWith ψ.ker A Φ (D.Tor.comap ψ) w ∧ (∀ i, ψ (w i) = D.nb i) ∧
        ∀ t : L', ψ t ∈ D.V0 → MulAut.conj t ∈ A := by
  have hodd : Odd (Nat.card ψ.ker) := by
    rcases hcard with h | h <;> rw [h] <;> decide
  have hAp : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hA.2 g.1 g.2)⟩
  choose w hw hw2 using fun i => exists_weyl_lift_odd D hD.weyl hψ hker hodd i
  let e : Multiplicative (Fin Tag.E6.rank → ZMod 3) ≃* D.diag.range :=
    MonoidHom.ofInjective hD.faithful
  let ρA : A →* D.diag.range := (ρ.comp A.subtype).codRestrict D.diag.range fun a => hal a a.2
  let Φ : A →* Multiplicative (Fin Tag.E6.rank → ZMod 3) := e.symm.toMonoidHom.comp ρA
  have hΦ : ∀ a : A, D.diag (Φ a) = ρ a := fun a =>
    congrArg Subtype.val (e.apply_symm_apply (ρA a))
  have hinj : Function.Injective Φ := by
    intro a b hab
    apply Subtype.ext
    apply hρinj
    rw [← hΦ a, ← hΦ b, hab]
  obtain ⟨hTab, hTfix, -⟩ := abelianLift_apply D hAL hD hψ hker hcard hρ hAp hal hw
  have hinner := innerPoints_realized D hAL hD hψ hker hcard hρ hA hsc hal hw
  have hinner' : ∀ v ∈ NoOffRest.hypE6, ∃ a ∈ A, ρ a = D.ad v := by
    intro v hv
    obtain ⟨t, -, -, -, a, ha, -, hρa⟩ := hinner v hv
    exact ⟨a, ha, hρa⟩
  have hrange := range_clause D hD.faithful hΦ hinner'
  refine ⟨Φ, w, ⟨hinj, hrange, hTab, ?_, hTfix, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hw, ?_⟩
  · intro z hz _
    show ψ z ∈ D.Tor
    rw [(MonoidHom.mem_ker).1 hz]
    exact D.Tor.one_mem
  · intro i t ht
    show ψ (w i * t * (w i)⁻¹) ∈ D.Tor
    rw [map_mul, map_mul, map_inv, hw i]
    exact hD.weyl.2.1 i (ψ t) ht
  · exact coboundary_clause D hAL hD hψ hker hcard hρ hAp hal hw
  · exact weyl_action_clause D hD.weyl hψ hρ hρinj hΦ hrange hw
  · intro x hx
    obtain ⟨t, htT, ht3, -, a, ha, hta, hρa⟩ := hinner x hx
    refine ⟨t, htT, ht3, ⟨a, ha⟩, hta.symm ▸ rfl, ?_⟩
    have h1 : D.diag (Φ ⟨a, ha⟩) = D.diag (Multiplicative.ofAdd x) := by
      rw [hΦ ⟨a, ha⟩, hρa]
      rfl
    exact congrArg Multiplicative.toAdd (hD.faithful h1)
  · exact inner_automizer_clause D hD hψ hρ hΦ hrange
  · exact full_automizer_clause D hD hψ hρ hΦ hrange
  · exact fun _ => ⟨hw2, normalizer_clause D hD hψ hρ hΦ hrange hw⟩
  · intro t ht
    obtain ⟨-, v, hv, hrv⟩ := (FrameData.mem_V0 D).1 ht
    obtain ⟨a, ha, hρa⟩ := hinner' v hv
    have hat : MulAut.conj t = a := hρinj (by rw [rho_conj hψ hρ, hrv, hρa])
    rw [hat]
    exact ha

end CFSG.StandardType.E6Dep.ZL

end

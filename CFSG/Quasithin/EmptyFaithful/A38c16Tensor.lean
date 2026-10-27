module

public import CFSG.Quasithin.EmptyFaithful.A38c16Tensor2
public import CFSG.Quasithin.EmptyFaithful.A38c16Tensor3

public section

namespace CFSG.Quasithin.A38c16

open scoped MatrixGroups Matrix BigOperators
open CFSG.Quasithin.A38c16.Tensor

theorem tensor_counting {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {K Kp : Subgroup (MulAut W)} (θ : ↥K ≃* SL(3, ZMod 2)) (θp : ↥Kp ≃* SL(3, ZMod 2))
    (hcomm : ∀ k ∈ K, ∀ y ∈ Kp, k * y = y * k)
    (hA : commSub ⊤ K ≤ ⨆ (M : Subgroup W) (_ : IsSimple8 K M), M)
    (hAp : commSub ⊤ Kp ≤ ⨆ (M : Subgroup W) (_ : IsSimple8 Kp M), M)
    {S : Subgroup W} (hSle : S ≤ commSub ⊤ K ⊓ commSub ⊤ Kp) (hS1 : S ≠ ⊥)
    (hSK : IsKSub K S) (hSKp : IsKSub Kp S)
    (hSmin : ∀ N : Subgroup W, N ≤ S → IsKSub K N → IsKSub Kp N → N = ⊥ ∨ N = S) :
    ∃ t : ZMod 2 × ZMod 2, ∀ F : Subgroup (↥K × ↥Kp),
      Nat.card {w : W // w ∈ S ∧ ∀ g ∈ F, ((g.1 : MulAut W) * (g.2 : MulAut W)) w = w} =
        Nat.card (fixSetT t (F.map (MulEquiv.prodCongr θ θp).toMonoidHom)) := by
  classical
  let _ : Module (ZMod 2) (Additive W) := z2Module hW
  let ρ : ↥K →* Module.End (ZMod 2) (Additive W) := linAut.comp K.subtype
  let σ : ↥Kp →* Module.End (ZMod 2) (Additive W) := linAut.comp Kp.subtype
  have hSA : S ≤ ⨆ (M : Subgroup W) (_ : IsSimple8 K M), M := (hSle.trans inf_le_left).trans hA
  have hSAp : S ≤ ⨆ (M : Subgroup W) (_ : IsSimple8 Kp M), M := (hSle.trans inf_le_right).trans hAp
  have hcomm' : ∀ (g : ↥K) (h : ↥Kp) (v : Additive W), ρ g (σ h v) = σ h (ρ g v) := by
    intro g h v
    obtain ⟨w, rfl⟩ := Additive.ofMul.surjective v
    have h1 := congrArg (fun a : MulAut W => a w) (hcomm g g.2 h h.2)
    exact congrArg Additive.ofMul h1
  have hS1' : toSub S ≠ ⊥ := by
    intro h
    apply hS1
    rw [← ofSub_toSub S, h, ofSub_bot]
  obtain ⟨t, ψ, hinj, hψS, hrange, hequiv⟩ := tensor_core ρ σ θ θp hcomm' (S := toSub S) hS1'
    (fun g v hv => hSK g g.2 (Additive.toMul v) hv)
    (fun h v hv => hSKp h h.2 (Additive.toMul v) hv)
    (by
      intro N hNS hNG hNH
      have h1 : IsKSub K (ofSub N) := fun k hk w hw => hNG ⟨k, hk⟩ (Additive.ofMul w) hw
      have h2 : IsKSub Kp (ofSub N) := fun k hk w hw => hNH ⟨k, hk⟩ (Additive.ofMul w) hw
      rcases hSmin (ofSub N) (fun w hw => hNS hw) h1 h2 with h | h
      · left
        rw [← toSub_ofSub N, h, toSub_bot]
      · right
        rw [← toSub_ofSub N, h])
    (fun N hNS hN1 hNG hmin => card_eight_of_toSub_minimal K hSA hNS hN1 hNG hmin)
    (fun N hNS hN1 hNH hmin => card_eight_of_toSub_minimal Kp hSAp hNS hN1 hNH hmin)
  refine ⟨t, fun F => ?_⟩
  let f : ↥(fixSetT t (F.map (MulEquiv.prodCongr θ θp).toMonoidHom)) →
      {w : W // w ∈ S ∧ ∀ g ∈ F, ((g.1 : MulAut W) * (g.2 : MulAut W)) w = w} := fun X =>
    ⟨Additive.toMul (ψ X.1), hψS X.1, fun g hg => by
      have hX : tensorActT t (θ g.1, θp g.2) X.1 = X.1 := X.2 _ ⟨g, hg, rfl⟩
      have h1 := hequiv g.1 g.2 X.1
      rw [hX] at h1
      exact h1.symm⟩
  have hfinj : Function.Injective f := by
    intro X Y hXY
    apply Subtype.ext
    apply hinj
    exact congrArg Subtype.val hXY
  have hfsurj : Function.Surjective f := by
    rintro ⟨w, hwS, hwF⟩
    obtain ⟨X, hX⟩ := hrange (Additive.ofMul w) hwS
    refine ⟨⟨X, ?_⟩, Subtype.ext ?_⟩
    · rintro _ ⟨g, hg, rfl⟩
      apply hinj
      show ψ (tensorActT t (θ g.1, θp g.2) X) = ψ X
      rw [hequiv, hX]
      exact congrArg Additive.ofMul (hwF g hg)
    · show Additive.toMul (ψ X) = w
      rw [hX]
      rfl
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hfinj, hfsurj⟩)).symm

end CFSG.Quasithin.A38c16

module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RSkew

public section

namespace CFSG.StandardType.TableCRes

open Certificates.TcRes CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

section Dual

variable {τ : Tag} {p : ℕ}

@[expose] noncomputable def tcrDualVec (g : WeylGroup τ) (p : ℕ) (v : Fin τ.rank → ZMod p) :
    Fin τ.rank → ZMod p :=
  fun k => ∑ j, (((g⁻¹ • (Pi.single k 1 : Fin τ.rank → ℤ)) j : ℤ) : ZMod p) * v j

private theorem tch_pair (g : WeylGroup τ) (c : Fin τ.rank → ℤ) (v : Fin τ.rank → ZMod p) :
    ∑ k, ((c k : ℤ) : ZMod p) * tcrDualVec g p v k = ∑ j, (((g⁻¹ • c) j : ℤ) : ZMod p) * v j := by
  set Φ : (Fin τ.rank → ℤ) →+ ZMod p :=
    AddMonoidHom.mk' (fun γ => ∑ j, ((γ j : ℤ) : ZMod p) * v j)
      (fun a b => by simp [add_mul, Finset.sum_add_distrib])
  set ψ : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ) :=
    AddMonoidHom.mk' (fun γ => g⁻¹ • γ) (fun a b => smul_add g⁻¹ a b)
  have hc : ψ c = ∑ k, c k • ψ (Pi.single k 1) := by
    conv_lhs => rw [tch_sum_single c]
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => map_zsmul ψ _ _
  have key : ∀ k, ((c k : ℤ) : ZMod p) * tcrDualVec g p v k = Φ (c k • ψ (Pi.single k 1)) := by
    intro k
    rw [map_zsmul, zsmul_eq_mul]
    rfl
  calc ∑ k, ((c k : ℤ) : ZMod p) * tcrDualVec g p v k
      = ∑ k, Φ (c k • ψ (Pi.single k 1)) := Finset.sum_congr rfl fun k _ => key k
    _ = Φ (∑ k, c k • ψ (Pi.single k 1)) := (map_sum Φ _ _).symm
    _ = Φ (ψ c) := by rw [hc]
    _ = ∑ j, (((g⁻¹ • c) j : ℤ) : ZMod p) * v j := rfl

private theorem tch_eq_of_pair (x y : Fin τ.rank → ZMod p)
    (h : ∀ c : Fin τ.rank → ℤ, ∑ k, ((c k : ℤ) : ZMod p) * x k = ∑ k, ((c k : ℤ) : ZMod p) * y k) :
    x = y := by
  funext j
  simpa [Pi.single_apply] using h (Pi.single j 1)

private theorem tch_inv_pair (g : WeylGroup τ) (v : Fin τ.rank → ZMod p) (c : Fin τ.rank → ℤ) :
    ∑ k, ((c k : ℤ) : ZMod p) * tcrDualVec g⁻¹ p (tcrDualVec g p v) k =
      ∑ k, ((c k : ℤ) : ZMod p) * v k := by
  rw [tch_pair g⁻¹ c (tcrDualVec g p v), inv_inv, tch_pair g (g • c) v, inv_smul_smul]

private theorem tch_inv (g : WeylGroup τ) (v : Fin τ.rank → ZMod p) :
    tcrDualVec g⁻¹ p (tcrDualVec g p v) = v :=
  tch_eq_of_pair _ _ (tch_inv_pair g v)

theorem tcrDualVec_pair (g : WeylGroup τ) (γ : Fin τ.rank → ℤ) (v : Fin τ.rank → ZMod p) :
    ∑ k, (((g • γ) k : ℤ) : ZMod p) * tcrDualVec g p v k = ∑ j, ((γ j : ℤ) : ZMod p) * v j := by
  rw [tch_pair g (g • γ) v, inv_smul_smul]

theorem tcrDualVec_add (g : WeylGroup τ) (v w : Fin τ.rank → ZMod p) :
    tcrDualVec g p (v + w) = tcrDualVec g p v + tcrDualVec g p w := by
  funext k
  simp only [tcrDualVec, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem tcrDualVec_smul (g : WeylGroup τ) (c : ZMod p) (v : Fin τ.rank → ZMod p) :
    tcrDualVec g p (c • v) = c • tcrDualVec g p v := by
  funext k
  simp only [tcrDualVec, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem tcrDualVec_injective (g : WeylGroup τ) : Function.Injective (tcrDualVec g p) := by
  intro v w h
  exact (tch_inv g v).symm.trans ((congrArg (tcrDualVec g⁻¹ p) h).trans (tch_inv g w))

@[expose] noncomputable def tcrDualLin (g : WeylGroup τ) (p : ℕ) :
    (Fin τ.rank → ZMod p) →ₗ[ZMod p] (Fin τ.rank → ZMod p) where
  toFun := tcrDualVec g p
  map_add' := tcrDualVec_add g
  map_smul' c v := tcrDualVec_smul g c v

theorem tcrDualLin_apply (g : WeylGroup τ) (v : Fin τ.rank → ZMod p) :
    tcrDualLin g p v = tcrDualVec g p v := rfl

theorem finrank_map_tcrDualLin (g : WeylGroup τ) (P : Submodule (ZMod p) (Fin τ.rank → ZMod p)) :
    Module.finrank (ZMod p) (P.map (tcrDualLin g p)) = Module.finrank (ZMod p) P := by
  have hinj : Function.Injective (tcrDualLin g p) := fun a b h => tcrDualVec_injective g h
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (tcrDualLin g p) hinj P)).symm

theorem kernelRoots_tcChiQ_dual
    (g : WeylGroup τ) (Q : Set (Fin τ.rank → ZMod p)) :
    kernelRoots (tcChiQ τ p (tcrDualVec g p '' Q)) =
      (fun γ => g • γ) '' kernelRoots (tcChiQ τ p Q) := by
  ext γ'
  simp only [Set.mem_image, mem_kernelRoots_chiQ]
  constructor
  · rintro ⟨hroot, hpair⟩
    refine ⟨g⁻¹ • γ', ⟨(isRoot_smul_iff g⁻¹).2 hroot, fun v hv => ?_⟩, smul_inv_smul g γ'⟩
    have h1 := hpair (tcrDualVec g p v) ⟨v, hv, rfl⟩
    have h2 := tcrDualVec_pair g (g⁻¹ • γ') v
    rw [smul_inv_smul] at h2
    rw [← h2]
    exact h1
  · rintro ⟨γ, ⟨hroot, hpair⟩, rfl⟩
    refine ⟨(isRoot_smul_iff g).2 hroot, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    rw [tcrDualVec_pair]
    exact hpair v hv

end Dual

end CFSG.StandardType.TableCRes

end

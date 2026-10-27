module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieCartanAux2
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.StandardType

open Finset Module CFSG.Open
open scoped IsMulCommutative

variable {G : Type} [Group G] {p N : ℕ} {Bs : Subgroup G}

@[instance_reducible] noncomputable def ggNSLiePI2_moduleV (hp : p.Prime) [IsMulCommutative ↥Bs]
    (hexp : ∀ b : ↥Bs, b ^ p = 1) : Module (ZMod p) (Additive ↥Bs) :=
  AddCommGroup.zmodModule (n := p) (fun x => by
    refine Additive.rec ?_ x
    intro b
    have h : p • Additive.ofMul b = @Additive.ofMul ↥Bs (b ^ p) := rfl
    rw [h, hexp b]
    rfl)

@[expose] noncomputable def ggNSLiePI2_linearEquivOfMulAut (hp : p.Prime) [IsMulCommutative ↥Bs]
    [Module (ZMod p) (Additive ↥Bs)] (t : MulAut ↥Bs) :
    Additive ↥Bs ≃ₗ[ZMod p] Additive ↥Bs :=
  let addEquiv : Additive ↥Bs ≃+ Additive ↥Bs := MulEquiv.toAdditive t
  let linMap : Additive ↥Bs →ₗ[ZMod p] Additive ↥Bs :=
    addEquiv.toAddMonoidHom.toZModLinearMap p
  LinearEquiv.ofBijective linMap (by
    change Function.Bijective (addEquiv : Additive ↥Bs → Additive ↥Bs)
    exact addEquiv.bijective)

lemma ggNSLiePI2_linearEquivOfMulAut_apply (hp : p.Prime) [IsMulCommutative ↥Bs]
    [Module (ZMod p) (Additive ↥Bs)] (t : MulAut ↥Bs) (v : Additive ↥Bs) :
    ggNSLiePI2_linearEquivOfMulAut hp t v = Additive.ofMul (t (Additive.toMul v)) :=
  rfl

end CFSG.StandardType

end

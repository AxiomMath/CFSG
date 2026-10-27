module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpPlaneFrameDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

variable {G : Type} [Group G] {p n m : ℕ} {F : Type} [Field F]

@[expose] def GGSpPlaneFrameOn (Bs K : Subgroup G)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (ι : Fin m → Fin n)
    (κ : StatedSp m F →* G)
    (ζ : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) F) : Prop :=
  Function.Injective ι ∧ Function.Injective κ ∧ κ.range = K ∧ Function.Injective ζ ∧
    ∀ (b : ↥Bs) (s : StatedSp m F),
      (b : G) * κ s * (b : G)⁻¹ =
        κ (SpJoin.spPlaneTorus m ζ (fun k => eta b (ι k)) * s *
          (SpJoin.spPlaneTorus m ζ (fun k => eta b (ι k)))⁻¹)

@[expose] def ggBlockTwo (Bs : Subgroup G) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (S : Set (Fin n)) : Subgroup G :=
  Subgroup.closure {g | g ∈ Subgroup.centralizer (ggBsCoordZeroOn Bs eta S : Set G) ∧
    ∃ k : ℕ, g ^ 2 ^ k = 1}

theorem GGSecFiveBPermSpPlaneFrame.planeFrameOn {r : ℕ} {Bs K : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
    {κ : StatedSp (r + 1) F →* G}
    {ζ : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) F}
    (h : GGSecFiveBPermSpPlaneFrame Bs K eta π κ ζ) :
    GGSpPlaneFrameOn Bs K eta (fun l => π l.succ) κ ζ :=
  ⟨π.injective.comp (Fin.succ_injective _), h.1, h.2.1, h.2.2.1, h.2.2.2⟩

end CFSG.StandardType

end

module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenDefs
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenBar

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator

structure Cfg (G : Type) [Group G] [Finite G] (M X : Subgroup G) (n : ℕ) where
  S : Setting G M X n
  α : ↥X →* alternatingGroup (Fin n)
  α_surj : Function.Surjective α
  α_ker : α.ker = CFSG.pCore 2 ↥X
  β : ↥(blockU X) →* Multiplicative (altHeart n)
  β_surj : Function.Surjective β
  β_ker : β.ker = (blockZ X).subgroupOf (blockU X)
  θ : ↥M →* Equiv.Perm (Fin n)
  θ_spec : ∀ (m : ↥M) (u v : ↥(blockU X)), (v : G) = (m : G) * (u : G) * (m : G)⁻¹ →
    Multiplicative.toAdd (β v) = altAct (θ m) (Multiplicative.toAdd (β u))
  θ_X : ∀ x : ↥X, θ ⟨(x : G), S.le x.2⟩ = (α x : Equiv.Perm (Fin n))

namespace Cfg

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ} (C : Cfg G M X n)

@[expose] def K : Subgroup G := C.θ.ker.map M.subtype

theorem K_le : C.K ≤ M := by
  rintro _ ⟨m, -, rfl⟩
  exact m.2

theorem mem_K {g : G} : g ∈ C.K ↔ ∃ hg : g ∈ M, C.θ ⟨g, hg⟩ = 1 := by
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m.2, hm⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

structure PiData where
  π : ↥C.K →* Multiplicative (permBar n)
  comm_mem : ∀ k : ↥C.K, ∀ x ∈ X, (k : G) * x * (k : G)⁻¹ * x⁻¹ ∈ blockU X
  spec : ∀ (k : ↥C.K) (x : ↥X) (u : ↥(blockU X)),
    (u : G) = (k : G) * (x : G) * (k : G)⁻¹ * (x : G)⁻¹ →
    heartToBar (Multiplicative.toAdd (C.β u)) =
      Multiplicative.toAdd (π k) - barAct (C.α x : Equiv.Perm (Fin n)) (Multiplicative.toAdd (π k))
  ker : ∀ k : ↥C.K, π k = 1 ↔ (k : G) ∈ Subgroup.centralizer (X : Set G)
  equivar : ∀ (m : ↥M) (k k' : ↥C.K), (k' : G) = (m : G) * (k : G) * (m : G)⁻¹ →
    Multiplicative.toAdd (π k') = barAct (C.θ m) (Multiplicative.toAdd (π k))

structure UIso where
  ψ : Multiplicative (evenWeight n) ≃* ↥(blockU X)
  equivar : ∀ (m : ↥M) (v : evenWeight n),
    (m : G) * (ψ (Multiplicative.ofAdd v) : G) * (m : G)⁻¹ =
      ψ (Multiplicative.ofAdd (evenWeightPerm (C.θ m) v))
  β_ψ : ∀ v : evenWeight n, Multiplicative.toAdd (C.β (ψ (Multiplicative.ofAdd v))) =
    (v : altHeart n)

end Cfg

end CFSG.RankThree.PartTwo.Sec19.SolEven

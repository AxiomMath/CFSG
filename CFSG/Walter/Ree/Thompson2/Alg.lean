module

public import CFSG.Walter.Ree.Thompson2.Alg.Eq211
public import CFSG.Walter.Ree.Thompson2.Alg.Identity

public section

namespace CFSG.Walter.Ree.T2.Alg

variable {k : Type} [Field k] [CharP k 3] {σ : k ≃+* k} {d : k} {S : k → k × k × k}

theorem thompsonIdentity_alg (hσ2 : ∀ x : k, σ x * x ^ 2 = 1 → x = 1)
    (h1 : ∀ a : ℕ, Even a → (∀ x : k, (σ x * x) ^ a = x ^ 2) → FE1C a S) (h2 : FE2C σ d S)
    (h3 : GF3C d S) (hT : T81C1 σ S) :
    ∀ a : ℕ, Even a → (∀ x : k, (σ x * x) ^ a = x ^ 2) →
      ∀ p ∈ ESigma k σ, thompsonT a p.1 p.2.1 p.2.2 = 0 := fun a ha haσ =>
  thompsonT_eq_zero_of ha haσ hσ2 (h1 a ha haσ) h2 h3 hT

end CFSG.Walter.Ree.T2.Alg

module

public import CFSG.ClassicalInvolution.Sp62Rec.ModelCR1
public import CFSG.ClassicalInvolution.Q3.AE.Models
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixDefs

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven.Yamaki

open CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.ClassicalInvolution.Sp62Rec
open CFSG.ClassicalInvolution.Q3.AE CFSG.Open


structure FusionOut {G : Type} [Group G] [Finite G] (z : G) where
  θ : ↥(Subgroup.centralizer ({z} : Set G)) ≃* ↥Hhat
  θ_z : (θ ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ : StatedSp 3 (ZMod 2)) = alpha
  T : Sylow 2 G
  T_le : (T : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G)
  θ_T : ∀ x (hx : x ∈ Subgroup.centralizer ({z} : Set G)),
    x ∈ (T : Subgroup G) ↔ (θ ⟨x, hx⟩ : StatedSp 3 (ZMod 2)) ∈ S0
  A : Subgroup G
  A_le : A ≤ Subgroup.centralizer ({z} : Set G)
  θ_A : ∀ x (hx : x ∈ Subgroup.centralizer ({z} : Set G)),
    x ∈ A ↔ (θ ⟨x, hx⟩ : StatedSp 3 (ZMod 2)) ∈ A0
  cent_A : Subgroup.centralizer (A : Set G) ≤ A
  b : Fin 7 → G
  b_inj : Function.Injective b
  z_mem : ∃ i, b i = z
  b_orbit : ∀ x, (∃ n ∈ Subgroup.normalizer (A : Set G), n * z * n⁻¹ = x) ↔ ∃ i, b i = x
  b_prod : (List.ofFn b).prod = 1
  b_closure : Subgroup.closure (Set.range b) = A
  perm_mem : ∀ n ∈ Subgroup.normalizer (A : Set G), ∃ σ ∈ l32, ∀ i, n * b i * n⁻¹ = b (σ i)
  card_N : Nat.card ↥(Subgroup.normalizer (A : Set G)) = 10752
  compl : ∃ U : Subgroup G, U ≤ (T : Subgroup G) ∧ U ⊓ A = ⊥ ∧ U ⊔ A = (T : Subgroup G)
  cent_le : ∀ x ∈ A, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≤
    Subgroup.normalizer (A : Set G) ⊔ Subgroup.centralizer ({z} : Set G)
  conj_A : ∀ t ∈ (T : Subgroup G), orderOf t = 2 →
    ∃ c ∈ Subgroup.centralizer ({z} : Set G), c * t * c⁻¹ ∈ A
  gen_inv : Subgroup.closure {x | x ∈ Subgroup.centralizer ({z} : Set G) ∧ orderOf x = 2} =
    Subgroup.centralizer ({z} : Set G)

@[expose] def FusionOutStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    CFSG.Open.IsCharTwoType G →
    ∀ (S : Sylow 2 G) (z : G), orderOf z = 2 → z ∈ (S : Subgroup G) →
      (∀ s ∈ (S : Subgroup G), s * z = z * s) →
      Nonempty (↥(Subgroup.centralizer ({z} : Set G)) ≃* YamakiHat) → Nonempty (FusionOut z)

end CFSG.RankThree.PartTwo.Sec19.SolEven.Yamaki

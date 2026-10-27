module

public import CFSG.LocalAnalysis.StandardType.GGTriD4KnownInputs
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
import CFSG.LocalAnalysis.StandardType.GGTriD4LineRecogC0
import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTri

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem triD4Line_map_centralizer_singleton {G H : Type*} [Group G] [Group H]
    (φ : G ≃* H) (z : G) :
    (Subgroup.centralizer {z}).map φ.toMonoidHom = Subgroup.centralizer {φ z} := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    simpa using congrArg φ h
  · intro h
    apply φ.injective
    simpa using h

private theorem triD4Line_card_commutator_centralizer {G H : Type*} [Group G] [Group H]
    (φ : G ≃* H) (z : G) :
    Nat.card (commutator (Subgroup.centralizer {φ z})) =
      Nat.card (commutator (Subgroup.centralizer {z})) := by
  let ψ : Subgroup.centralizer {z} ≃* Subgroup.centralizer {φ z} :=
    (φ.subgroupMap _).trans (MulEquiv.subgroupCongr (triD4Line_map_centralizer_singleton φ z))
  have h := map_commutator_eq _ ψ.toMonoidHom
  rw [MonoidHom.range_eq_top.mpr ψ.surjective, ← commutator_def] at h
  rw [← h, Subgroup.card_map_of_injective ψ.injective]

theorem triD4Line_conj_z0_of_torus
    {n : ℕ} (K : Type) [Field K] [Finite K]
    (hn : 2 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 3) (z₀ e : GGTriD4R n K)
    (hz3 : orderOf z₀ = 3) (he : orderOf e = 3)
    (hz₀' : ¬ Nat.card (commutator (Subgroup.centralizer {z₀})) ∣ (2 ^ n) ^ 3 * ((2 ^ n) ^ 6 - 1))
    (T : Subgroup (GGTriD4R n K)) (hT : T ≤ Subgroup.centralizer {e})
    (hTiso : Nonempty (T ≃* Multiplicative (ZMod ((2 ^ n) ^ 2 + 2 ^ n + 1)) ×
      Multiplicative (ZMod ((2 ^ n) ^ 2 + 2 ^ n + 1)))) :
    ∃ g : GGTriD4R n K, g * e * g⁻¹ = z₀ := by
  have : CharP K 2 := charP_two_of_card (m := n * 3) (by rw [hK, pow_mul])
  set σ := iterateFrobeniusEquiv K 2 n with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => by
    rw [hσdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  obtain ⟨φ⟩ := TableBExcSmallRest.nonempty_triD4_equiv (by omega) K hK σ hσ
  obtain ⟨g, hg⟩ := triD4Line_conj_z0_of_torus_C0 K hn hK σ hσ (φ z₀) (φ e)
    (by rw [MulEquiv.orderOf_eq, hz3]) (by rw [MulEquiv.orderOf_eq, he])
    (by rwa [triD4Line_card_commutator_centralizer φ z₀]) (T.map φ.toMonoidHom)
    (by
      rw [← triD4Line_map_centralizer_singleton φ e]
      exact Subgroup.map_mono hT)
    ⟨(T.equivMapOfInjective φ.toMonoidHom φ.injective).symm.trans hTiso.some⟩
  refine ⟨φ.symm g, φ.injective ?_⟩
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hg]

end CFSG.StandardType

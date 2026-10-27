module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwNorm
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwLat1
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwLat2
public import CFSG.LocalAnalysis.StandardType.GGKGForkLatticeInvol
public import CFSG.LocalAnalysis.StandardType.GGKGForkLatticeElt
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcLat1
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcLat2
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcLat3
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcLat4

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KE
  CFSG.LieType.AlgebraicGroups

section AtFrame


theorem ggKGTwE6_latticeAt_add
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n : ℕ} {p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1) (F : TwE6Frame K σ n p E)
    (hv : ExcIsLongest TwistTag.E6.tag F.v) : GGKGLatticeAt p E := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * n)
    (by rw [Fintype.card_eq_nat_card, hK, ← pow_mul, mul_comm])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  haveI : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  obtain ⟨ζu, hζu⟩ := CFSG.LieType.SeitzGeneration.exists_primitiveRoot_units
    (L := AlgebraicClosure K) (ℓ := 2) (by norm_num) hp (by omega)
  let ζ : (AlgebraicClosure K)ˣ := ζu
  have hζ : IsPrimitiveRoot ζ p := hζu
  refine ⟨TwistTag.E6.tag.rank, ggKGEl_Q TwistTag.E6.tag,
    ggKGTl_pi hK hσ hp hp5 hpq F hv ζ hζ, ggKGEl_Q_form (τ := TwistTag.E6.tag),
    ggKGTl_pi_surjective hK hσ hp hp5 hpq F hv ζ hζ, ?_⟩
  intro w₀ hrefl
  obtain ⟨v, hv2, hactV⟩ :=
    ggKGTl_normalizer_data hK hσ hp hp5 hpq F hv ζ hζ hrefl
  obtain ⟨w, hwroot, hwform⟩ := ggKGLat_involution_isRoot hp (by omega)
    (ggKGEl_Q_form (τ := TwistTag.E6.tag)) (ggKGEl_mat v) (ggKGEl_Q_invariant v)
    (ggKGEl_mat_mul_self hv2)
    (ggKGTl_fix_count hK hσ hp hp5 hpq F hv ζ hζ hrefl v hactV) (by decide)
  exact ⟨w, hwroot, fun y => by rw [hactV y, hwform y]⟩

end AtFrame

end CFSG.StandardType

module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.H13.L32ASecMod

public section

namespace CFSG.Quasithin.H13.L32A

open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem exists_coboundary_of_odd {K X A B : Subgroup G} (hodd : Odd (X.relIndex K))
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hA2 : ∀ a ∈ A, a * a = 1) (hBA : B ≤ A) (hKA : K ≤ Subgroup.normalizer (A : Set G))
    (hKB : K ≤ Subgroup.normalizer (B : Set G)) (κ : G → G) (hκA : ∀ k ∈ K, κ k ∈ A)
    (hκ : ∀ k ∈ K, ∀ k' ∈ K, κ (k * k') = κ k * (k * κ k' * k⁻¹))
    (hκX : ∀ k ∈ X, κ k ∈ B) :
    ∃ a ∈ A, ∀ g ∈ K, κ g * (a * (g * a * g⁻¹)⁻¹)⁻¹ ∈ B := by
  classical
  have : IsMulCommutative ↥A := ⟨⟨fun a b => Subtype.ext (hAc a a.2 b b.2)⟩⟩
  have hBn : (B.subgroupOf A).Normal := ⟨fun n hn c => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hAc c c.2 n (hBA hn), mul_inv_cancel_right]
    exact hn⟩
  set π : ↥A →* ↥A ⧸ B.subgroupOf A := QuotientGroup.mk' _ with hπ
  have hπ1 : ∀ y : ↥A, π y = 1 ↔ (y : G) ∈ B := fun y => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  let conjA : ↥K → ↥A →* ↥A := fun g =>
    { toFun := fun y => ⟨g * y * (g : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hKA g.2) y).mp y.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun y y' => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hconjA : ∀ (g : ↥K) (y : ↥A), ((conjA g y : ↥A) : G) = g * y * (g : G)⁻¹ := fun _ _ => rfl
  let c : ↥K → ↥A := fun k => ⟨κ k, hκA k k.2⟩
  have hc : ∀ k k' : ↥K, c (k * k') = c k * conjA k (c k') := fun k k' =>
    Subtype.ext (hκ k k.2 k' k'.2)
  set Q := ↥K ⧸ X.subgroupOf K
  have : Fintype Q := Fintype.ofFinite Q
  let r : Q → ↥K := fun q => Quotient.out q
  have hr : ∀ q : Q, (QuotientGroup.mk (r q) : Q) = q := fun q => Quotient.out_eq q
  set a : ↥A := ∏ q : Q, c (r q) with ha
  refine ⟨a, a.2, fun g hg => ?_⟩
  set g' : ↥K := ⟨g, hg⟩
  have hshift : ∀ q : Q, π (c (g' * r q)) = π (c (r (g' • q))) := by
    intro q
    have hrel : (r (g' • q))⁻¹ * (g' * r q) ∈ X.subgroupOf K := by
      rw [← QuotientGroup.eq]
      rw [hr, show (QuotientGroup.mk (g' * r q) : Q) = g' • (QuotientGroup.mk (r q) : Q) from rfl,
        hr]
    set y := (r (g' • q))⁻¹ * (g' * r q) with hy
    have hgr : g' * r q = r (g' • q) * y := by rw [hy]; group
    rw [hgr, hc, map_mul]
    have : π (conjA (r (g' • q)) (c y)) = 1 := by
      rw [hπ1, hconjA]
      exact (Subgroup.mem_normalizer_iff.mp (hKB (r (g' • q)).2) _).mp
        (hκX y (Subgroup.mem_subgroupOf.mp hrel))
    rw [this, mul_one]
  have hkey : π (conjA g' a) = (π (c g'))⁻¹ ^ Fintype.card Q * π a := by
    rw [ha, map_prod, map_prod]
    have h1 : ∀ q : Q, π (conjA g' (c (r q))) = (π (c g'))⁻¹ * π (c (r (g' • q))) := by
      intro q
      rw [← hshift, hc, map_mul]
      group
    simp_rw [h1]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    congr 1
    rw [map_prod]
    exact Fintype.prod_equiv (MulAction.toPerm g' : Equiv.Perm Q)
      (fun q => π (c (r (g' • q)))) (fun q => π (c (r q))) fun q => rfl
  have hcard : Fintype.card Q = X.relIndex K := by
    rw [Fintype.card_eq_nat_card]
    rfl
  have h2 : (π (c g')) ^ 2 = 1 := by
    rw [← map_pow, pow_two, show c g' * c g' = 1 from Subtype.ext (hA2 _ (hκA g hg))]
    exact map_one π
  have hinv : (π (c g'))⁻¹ ^ Fintype.card Q = (π (c g'))⁻¹ := by
    obtain ⟨m, hm⟩ := hodd
    rw [hcard, hm, pow_succ, pow_mul, inv_pow, h2, inv_one, one_pow, one_mul]
  rw [hinv] at hkey
  have hfin : π (c g' * (a * (conjA g' a)⁻¹)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_mul, map_inv, hkey]
    group
  have := (hπ1 _).mp hfin
  simpa [hconjA] using this

end CFSG.Quasithin.H13.L32A

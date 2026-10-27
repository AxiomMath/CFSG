module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDefs
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpCoord
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDkRootsBasic
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDkRootsWeyl

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin

theorem ggDk_exists_coord_fix {G : Type} [Group G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Bs : Subgroup G} (hBs : IsElemAbelian p Bs) {k : ℕ} (hk : 4 ≤ k)
    (hcard : Nat.card Bs = p ^ k) {A : Subgroup (MulAut ↥Bs)} {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥A}
    (hrefl : ∀ i : ι, GGIsReflection p ((e (M.simple i) : ↥A) : MulAut ↥Bs))
    {σ : Fin k ≃ ι} (φ : M.Group ≃* ggWeylD k)
    (hφ : ∀ a : Fin k, φ (M.simple (σ a)) = (coxeterMatrix (isFiniteType_cartanD k)).simple a) :
    ∃ θ : Additive ↥Bs ≃+ (Fin k → ZMod p), ∀ (u : M.Group) (η : Fin k → ℤ),
      GGDReflRoot k (φ u) η → ∀ b : ↥Bs,
        (((e u : ↥A) : MulAut ↥Bs) b = b ↔ ∑ a, θ (Additive.ofMul b) a * (η a : ZMod p) = 0) := by
  haveI : Fact p.Prime := ⟨hp⟩
  let ρ : ggWeylD k →* MulAut ↥Bs := A.subtype.comp (e.toMonoidHom.comp φ.symm.toMonoidHom)
  have hρu : ∀ u, ρ (φ u) = ((e u : ↥A) : MulAut ↥Bs) := fun u => by simp [ρ]
  have hρ : Function.Injective ρ := fun w w' h =>
    φ.symm.injective (e.injective (Subtype.val_injective (by simpa [ρ] using h)))
  obtain ⟨θ, hθ⟩ := ggDk_exists_coord hp hp2 hBs hk hcard hρ fun a => by
    rw [← hφ a, hρu]
    exact hrefl (σ a)
  refine ⟨θ, fun u η hu b => ?_⟩
  rw [← hρu]
  obtain ⟨c, -, -, hc, -⟩ := ggDRootSet_exists_pair (hu.mem (by omega))
  have hc1 : (η c : ZMod p) ≠ 0 := by
    rcases ggDRootSet_sign (hu.mem (by omega)) hc with h | h <;> simp [h]
  constructor
  · intro h
    have h1 := hθ (φ u) η hu b
    rw [h, eq_comm, sub_eq_self] at h1
    have h2 := congrFun h1 c
    rw [Pi.smul_apply, Pi.zero_apply, smul_eq_mul, mul_eq_zero] at h2
    exact h2.resolve_right hc1
  · intro h
    apply Additive.ofMul.injective
    apply θ.injective
    rw [hθ (φ u) η hu b, h, zero_smul]
    exact sub_zero _

theorem ggDk_coord_shift {G : Type} [Group G] {p : ℕ} (hp : p.Prime) {Bs : Subgroup G} {k : ℕ}
    (θ : Additive ↥Bs ≃+ (Fin k → ZMod p)) {ε : Fin k → ℤ} (hε : ∀ a, ε a = 1 ∨ ε a = -1)
    {x : ↥Bs} (hx1 : x ≠ 1)
    (hx : ∀ a b, (ε a : ZMod p) * θ (Additive.ofMul x) a =
      (ε b : ZMod p) * θ (Additive.ofMul x) b) (d : ↥Bs) (c : ZMod p) :
    ∃ n : ℕ, ∀ a, θ (Additive.ofMul (d * (x ^ n)⁻¹)) a =
      (ε a : ZMod p) * ((ε a : ZMod p) * θ (Additive.ofMul d) a - c) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hεsq : ∀ a, (ε a : ZMod p) * ε a = 1 := fun a => by rcases hε a with h | h <;> simp [h]
  obtain ⟨a₁, ha₁⟩ : ∃ a, θ (Additive.ofMul x) a ≠ 0 := by
    by_contra h
    push Not at h
    exact hx1 (Additive.ofMul.injective
      ((θ.injective ((funext h).trans (map_zero θ).symm)).trans ofMul_one.symm))
  obtain ⟨l, hl0, hxa⟩ : ∃ l : ZMod p, l ≠ 0 ∧ ∀ a, θ (Additive.ofMul x) a = ε a * l :=
    ⟨(ε a₁ : ZMod p) * θ (Additive.ofMul x) a₁,
      mul_ne_zero (fun h => one_ne_zero ((hεsq a₁).symm.trans (by rw [h, zero_mul]))) ha₁,
      fun a => by rw [← hx a a₁, ← mul_assoc, hεsq, one_mul]⟩
  refine ⟨(c / l).val, fun a => ?_⟩
  have hcl : c / l * ((ε a : ZMod p) * l) = ε a * c := by
    rw [mul_left_comm, div_mul_cancel₀ c hl0]
  rw [ofMul_mul, ofMul_inv, ofMul_pow, map_add, map_neg, map_nsmul, Pi.add_apply, Pi.neg_apply,
    Pi.smul_apply, hxa a, nsmul_eq_mul, ZMod.natCast_zmod_val, hcl, mul_sub, ← mul_assoc,
    hεsq a, one_mul, sub_eq_add_neg]
  rfl

end CFSG.StandardType

end

module

public import CFSG.LocalAnalysis.StandardType.GGE6DepZLFinite
public import CFSG.LocalAnalysis.StandardType.GGE6DepKMatrix

public section

namespace CFSG.StandardType

namespace E6Dep

namespace ZL

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G]

theorem isRefl6_of_ggIsReflection {Bs : Subgroup G} {ι : Additive ↥Bs ≃+ Vec6}
    {φ : MulAut ↥Bs} {g : Mat6} (hact : ActsAs ι φ g) (hφ : GGIsReflection 3 φ)
    (hcardBs : Nat.card Bs = 3 ^ 6) : IsRefl6 g := by
  obtain ⟨hφ2, hφfix⟩ := hφ
  have hgg : g * g = 1 := by
    have h1 : ActsAs ι (φ * φ) (g * g) := ActsAs.mul hact hact
    rw [show φ * φ = 1 from by rw [← pow_two]; exact hφ2] at h1
    exact actsAs_inj h1 (ActsAs.one ι)
  have hfix : ∀ b : ↥Bs,
      (φ b = b) ↔ g.mulVec (ι (Additive.ofMul b)) = ι (Additive.ofMul b) := by
    intro b
    rw [← hact b]
    exact ⟨fun hb => by rw [hb], fun hb => by
      have h1 := congrArg Additive.toMul (ι.injective hb)
      simpa only [toMul_ofMul] using h1⟩
  have hcard : Nat.card {b : ↥Bs // φ b = b} = Nat.card {v : Vec6 // g.mulVec v = v} :=
    Nat.card_congr (Equiv.subtypeEquiv (Additive.ofMul.trans ι.toEquiv) hfix)
  refine ⟨hgg, ?_⟩
  rw [← Nat.card_eq_fintype_card, ← hcard, hφfix]
  exact hcardBs

theorem closure_of_automizer_gen {Bs L : Subgroup G} {ι : Additive ↥Bs ≃+ Vec6} {Λ : Type}
    (ρ : Λ → MulAut ↥Bs) (g : Λ → Mat6)
    (hgen : ggAutomizer L Bs = Subgroup.closure (Set.range ρ))
    (hρg : ∀ l, ActsAs ι (ρ l) (g l)) (hinv : ∀ l, g l * g l = 1) {M : Submonoid Mat6}
    (hM : ∀ m ∈ M, ∃ φ ∈ ggAutomizer L Bs, ActsAs ι φ m) :
    ∀ m ∈ M, m ∈ Submonoid.closure (Set.range g) := by
  let P : Submonoid Mat6 := Submonoid.closure (Set.range g)
  have hinvP : ∀ m ∈ P, ∃ m' ∈ P, m * m' = 1 ∧ m' * m = 1 := by
    intro m hm
    induction hm using Submonoid.closure_induction with
    | mem y hy =>
        obtain ⟨l, rfl⟩ := hy
        exact ⟨g l, Submonoid.subset_closure ⟨l, rfl⟩, hinv l, hinv l⟩
    | one => exact ⟨1, P.one_mem, by rw [mul_one], by rw [mul_one]⟩
    | mul a b _ _ iha ihb =>
        obtain ⟨a', ha'P, ha1, ha2⟩ := iha
        obtain ⟨b', hb'P, hb1, hb2⟩ := ihb
        refine ⟨b' * a', P.mul_mem hb'P ha'P, ?_, ?_⟩
        · rw [← mul_assoc, mul_assoc a b b', hb1, mul_one, ha1]
        · rw [← mul_assoc, mul_assoc b' a' a, ha2, mul_one, hb2]
  have key : ∀ ψ ∈ Subgroup.closure (Set.range ρ), ∃ m ∈ P, ActsAs ι ψ m := by
    intro ψ hψ
    induction hψ using Subgroup.closure_induction with
    | mem x hx =>
        obtain ⟨l, rfl⟩ := hx
        exact ⟨g l, Submonoid.subset_closure ⟨l, rfl⟩, hρg l⟩
    | one => exact ⟨1, P.one_mem, ActsAs.one ι⟩
    | mul x y _ _ ihx ihy =>
        obtain ⟨mx, hmxP, hxact⟩ := ihx
        obtain ⟨my, hmyP, hyact⟩ := ihy
        exact ⟨mx * my, P.mul_mem hmxP hmyP, ActsAs.mul hxact hyact⟩
    | inv x _ ihx =>
        obtain ⟨mx, hmxP, hxact⟩ := ihx
        obtain ⟨mx', hmx'P, hmx_mx', hmx'_mx⟩ := hinvP mx hmxP
        refine ⟨mx', hmx'P, fun b => ?_⟩
        have hxxinv : x (x⁻¹ b) = b := by
          have h : (x * x⁻¹ : MulAut ↥Bs) = 1 := mul_inv_cancel x
          have h2 := congrArg (fun e : MulAut ↥Bs => e b) h
          simpa [MulAut.mul_apply, MulAut.one_apply] using h2
        symm
        calc mx'.mulVec (ι (Additive.ofMul b))
            = mx'.mulVec (ι (Additive.ofMul (x (x⁻¹ b)))) := by rw [hxxinv]
          _ = mx'.mulVec (mx.mulVec (ι (Additive.ofMul (x⁻¹ b)))) := by rw [hxact (x⁻¹ b)]
          _ = (mx' * mx).mulVec (ι (Additive.ofMul (x⁻¹ b))) :=
                Matrix.mulVec_mulVec (ι (Additive.ofMul (x⁻¹ b))) mx' mx
          _ = ι (Additive.ofMul (x⁻¹ b)) := by rw [hmx'_mx, Matrix.one_mulVec]
  intro m hm
  obtain ⟨φ, hφA, hφm⟩ := hM m hm
  rw [hgen] at hφA
  obtain ⟨m₀, hm₀P, hm₀act⟩ := key φ hφA
  have hm_eq : m = m₀ := actsAs_inj hφm hm₀act
  rwa [hm_eq]

end ZL

end E6Dep

end CFSG.StandardType

end

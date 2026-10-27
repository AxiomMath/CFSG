module

public import CFSG.RankThree.PartTwo.Sec18.Item187NFixDim
public import CFSG.RankThree.PartTwo.Sec18.Item187NSzFpf
import CFSG.RankThree.PartTwo.Sec16.Item166Proof

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

section Cert113


theorem card_fixed_ge_eight {T : Type} [Group T] {n : ℕ}
    (hSz : CFSG.Blueprint.SuzukiModel T 2 n) (α : MulAut T) (hα1 : α ≠ 1) (hα3 : α ^ 3 = 1)
    (W : Type) [Group W] [Finite W] (hcomm : ∀ a b : W, a * b = b * a) (hsq : ∀ a : W, a * a = 1)
    (ρ : T →* MulAut W) (γ : MulAut W) (hγ3 : γ ^ 3 = 1)
    (hγ : ∀ t : T, γ * ρ t = ρ (α t) * γ) (hρ : ∃ t : T, ρ t ≠ 1) :
    8 ≤ Nat.card {w : W // γ w = w} := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsSimpleGroup T := CFSG.RankThree.PartTwo.Sec16.isSimpleGroup_of_suzukiModel hSz
  have hρinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker with h | h
    · exact h
    · exfalso
      obtain ⟨t, ht⟩ := hρ
      exact ht (MonoidHom.mem_ker.mp (by rw [h]; exact Subgroup.mem_top t))
  have hγ1 : γ ≠ 1 := by
    intro h
    apply hα1
    ext t
    have h1 := hγ t
    rw [h, one_mul, mul_one] at h1
    exact (hρinj h1).symm
  have hγord : orderOf γ = 3 := orderOf_eq_prime hγ3 hγ1
  have hαord : orderOf α = 3 := orderOf_eq_prime hα3 hα1
  obtain ⟨F, hFcyc, hFα, hFfpf, hFcard⟩ := exists_fpf_cyclic_of_order_three hSz α hαord
  have hγ' : ∀ t : T, ρ (α t) = γ * ρ t * γ⁻¹ := fun t => by
    rw [hγ t]; group
  letI : CommGroup W := { ‹Group W› with mul_comm := hcomm }
  haveI hmod : Module (ZMod 2) (Additive W) := AddCommGroup.zmodModule (n := 2) (by
    intro x
    rw [two_nsmul]
    show Additive.ofMul (Additive.toMul x * Additive.toMul x) = Additive.ofMul 1
    rw [hsq])
  haveI : Finite (Additive W) := Finite.of_equiv W Additive.ofMul
  haveI : Module.Finite (ZMod 2) (Additive W) := Module.Finite.of_finite
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun σ : MulAut W => (σ : W → W)) (fun σ τ h => by ext w; exact congrFun h w)
  let ρH : Representation (ZMod 2) (MulAut W) (Additive W) :=
    { toFun := fun σ =>
        (MulEquiv.toAdditive σ : Additive W ≃+ Additive W).toAddMonoidHom.toZModLinearMap 2
      map_one' := by ext x; rfl
      map_mul' := fun σ τ => by ext x; rfl }
  have hρHinj : Function.Injective ρH := by
    intro σ τ h
    ext w
    exact congrArg Additive.toMul (LinearMap.congr_fun h (Additive.ofMul w))
  let F' : Subgroup (MulAut W) := F.map ρ
  haveI := hFcyc
  have hF'cyc : IsCyclic F' :=
    isCyclic_of_surjective (Subgroup.equivMapOfInjective F ρ hρinj) (MulEquiv.surjective _)
  have hγF' : γ ∈ Subgroup.normalizer (F' : Set (MulAut W)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨f, hf, rfl⟩
      rw [← hγ' f]
      exact Subgroup.mem_map_of_mem ρ (hFα f hf)
    · rintro ⟨f', hf', e⟩
      have h3 : γ * γ * γ = 1 := by rw [← pow_three']; exact hγ3
      have e2 : ρ (α (α f')) = h := by
        rw [hγ', hγ', e]
        calc γ * (γ * (γ * h * γ⁻¹) * γ⁻¹) * γ⁻¹ = (γ * γ * γ) * h * (γ * γ * γ)⁻¹ := by group
          _ = h := by rw [h3]; simp
      rw [← e2]
      exact Subgroup.mem_map_of_mem ρ (hFα _ (hFα _ hf'))
  have hfpf : ∀ f ∈ F', γ * f = f * γ → f = 1 := by
    rintro _ ⟨f, hf, rfl⟩ hc
    have h1 := hγ f
    rw [hc] at h1
    have h2 : ρ f = ρ (α f) := mul_right_cancel h1
    have h3 : f = 1 := hFfpf f hf (hρinj h2).symm
    rw [h3, map_one]
  have hfaith : Function.Injective (ρH.comp F'.subtype) := fun a b h => Subtype.ext (hρHinj h)
  have hcard : Nat.card F' = 13 ∨ ∃ m : ℕ, Odd m ∧ 3 ≤ m ∧ Nat.card F' = 4 ^ m + 2 ^ m + 1 := by
    have e : Nat.card F' = Nat.card F := Subgroup.card_map_of_injective hρinj
    rw [e]; exact hFcard
  have h3 := three_le_finrank_invariants ρH F' hF'cyc γ hγord hγF' hfpf hfaith hcard
  set Inv := Representation.invariants (ρH.comp (Subgroup.zpowers γ).subtype) with hInv
  have hcardInv : 8 ≤ Nat.card Inv := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ Module.finrank (ZMod 2) Inv := Nat.pow_le_pow_right (by norm_num) h3
  let j : Inv → {w : W // γ w = w} := fun v =>
    ⟨Additive.toMul v.1, congrArg Additive.toMul
      ((Representation.mem_invariants _ _).mp v.2 ⟨γ, Subgroup.mem_zpowers γ⟩)⟩
  have hj : Function.Injective j := by
    intro a b h
    apply Subtype.ext
    have h1 : (j a).1 = (j b).1 := congrArg (fun z : {w : W // γ w = w} => z.1) h
    exact Additive.toMul.injective h1
  exact hcardInv.trans (Nat.card_le_card_of_injective j hj)

end Cert113

end CFSG.RankThree.PartTwo.Sec18.Item187Proof

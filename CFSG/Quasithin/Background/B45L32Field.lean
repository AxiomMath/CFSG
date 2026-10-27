module

public import CFSG.Quasithin.Background.SmithB45SL3L32

public section

namespace CFSG.Quasithin.B45L32

open CFSG.QuasithinUnique.Setup.Family

private theorem subgroup_eq_bot_or_top_of_invariant {F V : Type} [Field F] [AddCommGroup V]
    [Module F V] (h01 : ∀ c : F, c = 0 ∨ c = 1) {G : Type} [Group G] {ρ : G →* (V ≃ₗ[F] V)}
    (hirr : ∀ P : Submodule F V, (∀ g : G, ∀ v ∈ P, ρ g v ∈ P) → P = ⊥ ∨ P = ⊤)
    (σ : G →* MulAut (Multiplicative V))
    (hσ : ∀ (g : G) (v : V), σ g (Multiplicative.ofAdd v) = Multiplicative.ofAdd (ρ g v)) :
    ∀ J : Subgroup (Multiplicative V),
      (∀ l ∈ σ.range, ∀ q ∈ J, l q ∈ J) → J = ⊥ ∨ J = ⊤ := by
  intro J hJ
  let P : Submodule F V :=
    { carrier := {v : V | Multiplicative.ofAdd v ∈ J}
      add_mem' := fun ha hb => J.mul_mem ha hb
      zero_mem' := J.one_mem
      smul_mem' := fun c v hv => by
        rcases h01 c with rfl | rfl
        · simp
        · simpa using hv }
  have hP : ∀ g : G, ∀ v ∈ P, ρ g v ∈ P := fun g v hv => by
    have h := hJ (σ g) (MonoidHom.mem_range.mpr ⟨g, rfl⟩) (Multiplicative.ofAdd v) hv
    rwa [hσ] at h
  rcases hirr P hP with h | h
  · refine Or.inl ((Subgroup.eq_bot_iff_forall J).mpr fun q hq => ?_)
    have hq' : Multiplicative.toAdd q ∈ P := hq
    rw [h, Submodule.mem_bot] at hq'
    simpa using congrArg Multiplicative.ofAdd hq'
  · exact Or.inr ((Subgroup.eq_top_iff' J).mpr fun q => (h ▸ Submodule.mem_top :
      Multiplicative.toAdd q ∈ P))

theorem finrank_eq_three_or_eight_of_field {G : Type} [Group G] (e : G ≃* GL32)
    {F V : Type} [Field F] [Finite F] (hF : Nat.card F = 2) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [Nontrivial V] {ρ : G →* (V ≃ₗ[F] V)} (hρ : Function.Injective ρ)
    (hirr : ∀ P : Submodule F V, (∀ g : G, ∀ v ∈ P, ρ g v ∈ P) → P = ⊥ ∨ P = ⊤) :
    Module.finrank F V = 3 ∨ Module.finrank F V = 8 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = 2 := by simpa [Nat.card_eq_fintype_card] using hF
  have : CharP F 2 :=
    CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero (by
      have h := Nat.cast_card_eq_zero F
      rwa [hcard] at h)
  have : Algebra (ZMod 2) F := ZMod.algebra F 2
  have h01 : ∀ c : F, c = 0 ∨ c = 1 := by
    obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (0 : F)).mp hF
    have hy : y = 1 := (huniq 1 (by simp)).symm
    intro c
    by_cases hc : c = 0
    · exact Or.inl hc
    · exact Or.inr ((huniq c hc).trans hy)
  have : Finite V := Module.finite_of_finite F
  let : Module (ZMod 2) V := Module.compHom V (algebraMap (ZMod 2) F)
  have : IsScalarTower (ZMod 2) F V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let σ : G →* MulAut (Multiplicative V) :=
    { toFun := fun g => (ρ g).toAddEquiv.toMultiplicative
      map_one' := by ext q; simp
      map_mul' := fun a b => by ext q; simp }
  have hσ_apply : ∀ (g : G) (v : V), σ g (Multiplicative.ofAdd v) = Multiplicative.ofAdd (ρ g v) :=
    fun g v => rfl
  have hσ : Function.Injective σ := by
    intro a b hab
    apply hρ
    ext v
    have h1 := congrArg (fun f : MulAut (Multiplicative V) => f (Multiplicative.ofAdd v)) hab
    simpa [hσ_apply] using h1
  let L : Subgroup (MulAut (Multiplicative V)) := σ.range
  have eL : ↥L ≃* GL32 := (MonoidHom.ofInjective hσ).symm.trans e
  have hirrL : ∀ J : Subgroup (Multiplicative V), (∀ l ∈ L, ∀ q ∈ J, l q ∈ J) → J = ⊥ ∨ J = ⊤ :=
    subgroup_eq_bot_or_top_of_invariant h01 hirr σ hσ_apply
  have hdim : Module.finrank (ZMod 2) V = 3 ∨ Module.finrank (ZMod 2) V = 8 :=
    finrank_eq_three_or_eight (θ := MulEquiv.refl (Multiplicative V)) (L := L) hirrL eL
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have hcardV : Nat.card V = Nat.card F ^ Module.finrank F V :=
    Module.natCard_eq_pow_finrank (K := F)
  have hcardV2 : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
    rwa [Nat.card_zmod] at h
  have hpow : 2 ^ Module.finrank F V = 2 ^ Module.finrank (ZMod 2) V := by
    have h1 : 2 ^ Module.finrank F V = Nat.card V := by rw [hcardV, hF]
    rw [h1, hcardV2]
  have hfin : Module.finrank F V = Module.finrank (ZMod 2) V :=
    Nat.pow_right_injective (by norm_num) hpow
  rcases hdim with h | h <;> omega

end CFSG.Quasithin.B45L32

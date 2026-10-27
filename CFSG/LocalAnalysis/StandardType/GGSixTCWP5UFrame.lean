module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UFrame
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.TwE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiag

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.LangTorus

section UFrame

open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem exists_langSetup_of_elem_twE6
    {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (y : ↥(twistedE6RootGroup K σ)) (hy1 : y ≠ 1) (hyp : y ^ p = 1) :
    ∃ (S : LangSetup Tag.E6 (AlgebraicClosure K) 5)
      (ι : ↥(twistedE6RootGroup K σ) →* ModGL Tag.E6 (AlgebraicClosure K)),
      S.D.q = 2 ^ f ∧ Function.Injective ι ∧ ι.range = S.Γ := by
  classical
  have hperf := finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two hf K hK σ.toRingHom hσ
  have hcomm_le : ⁅twistedFixedGroup TwistTag.E6 K σ.toRingHom,
      twistedFixedGroup TwistTag.E6 K σ.toRingHom⁆ ≤
      twistedFixedGroup TwistTag.E6 K σ.toRingHom :=
    Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)
  have hh : (y : ModGL TwistTag.E6.tag K) ∈ twistedFixedGroup TwistTag.E6 K σ.toRingHom :=
    hcomm_le (by rw [hperf.2.2.1]; exact y.2)
  have hmon : MonomialToralAt Tag.E6 p :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five (by simp) hp hp2
  obtain ⟨S, -, ι, hq, -, -, -, -, hinj, hrange, -⟩ :=
    exists_langSetup_of_inner_twE6_of_prime Nat.prime_two hf hK σ hσ hp hp2
      Nat.prime_five (by decide) (Or.inl le_rfl) hmon (MulAut.conj y)
      (y : ModGL TwistTag.E6.tag K) hh (fun c => by simp)
      (by rw [← Subgroup.coe_pow, hyp]; rfl) (fun h => hy1 (Subtype.ext h))
  exact ⟨S, ι, hq, hinj, hrange⟩

theorem exists_uframe_twE6
    {X : Type} [Group X] {G₀ B D : Subgroup X} {f p : ℕ} (hf : 1 ≤ f) (hp : p.Prime) (hp2 : p ≠ 2)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (θ : ↥G₀ ⧸ Subgroup.center ↥G₀ ≃* twistedE6RootGroup K σ)
    (hBN : B ≤ Subgroup.normalizer (G₀ : Set X))
    (hin : ∀ b ∈ B, ∃ g ∈ G₀, b * g ∈ Subgroup.centralizer (G₀ : Set X))
    (hfaith : B ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥) (hBel : IsElemAbelian p B)
    (hDB : D ≤ B) (hDcard : Nat.card D = p ^ 2) :
    ∃ S : LangSetup Tag.E6 (AlgebraicClosure K) 5,
      S.D.q = 2 ^ f ∧ Nonempty (GGTCUFrame S.Γ G₀ B) := by
  classical
  have hZ : Subgroup.center ↥(twistedE6RootGroup K σ) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hcl : Subgroup.center (↥G₀ ⧸ Subgroup.center ↥G₀) = ⊥ := by
    have h1 := Subgroup.map_center_eq θ
    rw [hZ] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ θ.injective).1 h1
  obtain ⟨ν, hνinj, hνact⟩ := exists_inner_hom_of_faithful_inner hBN hin hfaith hcl
  have hDne : D ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hDcard
    have h2 := hp.two_le
    have : 4 ≤ p ^ 2 := by nlinarith
    omega
  obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hDne
  let b₀ : ↥B := ⟨(x : X), hDB x.2⟩
  have hb₀1 : b₀ ≠ 1 := by
    intro h
    apply hx1
    have h' : (x : X) = 1 := congrArg (fun z : ↥B => (z : X)) h
    exact Subtype.ext h'
  have hb₀p : b₀ ^ p = 1 := Subtype.ext (hBel.2 (x : X) (hDB x.2))
  have hy1 : θ (ν b₀) ≠ 1 := fun h => hb₀1 (hνinj (θ.injective (by rw [h, map_one, map_one])))
  have hyp : θ (ν b₀) ^ p = 1 := by rw [← map_pow, ← map_pow, hb₀p, map_one, map_one]
  obtain ⟨S, ι, hq, hinj, hrange⟩ :=
    exists_langSetup_of_elem_twE6 hf hK σ hσ hp hp2 (θ (ν b₀)) hy1 hyp
  exact ⟨S, hq, ⟨⟨ν, hνinj, hνact,
    θ.trans ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange))⟩⟩⟩

theorem uframe_main_twE6
    (hField : UFieldInput Tag.E6)
    {X : Type} [Group X] {G₀ B D J : Subgroup X} [Finite B] {f p : ℕ} (hf : 1 ≤ f) (hp : p.Prime)
    (hp2 : p ≠ 2) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (θ : ↥G₀ ⧸ Subgroup.center ↥G₀ ≃* twistedE6RootGroup K σ)
    (hBN : B ≤ Subgroup.normalizer (G₀ : Set X))
    (hin : ∀ b ∈ B, ∃ g ∈ G₀, b * g ∈ Subgroup.centralizer (G₀ : Set X))
    (hfaith : B ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥) (hBel : IsElemAbelian p B)
    (hDB : D ≤ B) (hDcard : Nat.card D = p ^ 2) (hJG : J ≤ G₀)
    (hJ : IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X)))
    (hcent : B ⊓ Subgroup.centralizer (J : Set X) = D)
    (hF : ∃ (t' : StatedLieTag) (m f' : ℕ), f < f' ∧
      LieModel (↥J ⧸ Subgroup.center ↥J) t' m 2 f')
    (htor : UToralAt Tag.E6 p (Nat.card B)) :
    ∃ (Ψ : Set (Fin Tag.E6.rank → ℤ)) (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)),
      IsRootComponent Ψ ∧ (∀ γ, IsRoot Tag.E6 (ρ γ) ↔ IsRoot Tag.E6 γ) ∧
      (∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ) ∧
      (∀ γ ∈ Ψ, ∀ δ ∈ (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) '' Ψ,
        iform γ δ = 0 ∧ ¬ IsRoot Tag.E6 (γ + δ)) ∧
      Nat.card B ≤ p ^ (2 + Module.finrank ℤ (Submodule.span ℤ Ψ)) ∧
      2 * Module.finrank ℤ (Submodule.span ℤ Ψ) ≤ Tag.E6.rank := by
  have : CharP K 2 := charP_two_of_finite_field_card_two_pow (f := f * 2) (by rw [hK, pow_mul])
  obtain ⟨S, hq, ⟨fr⟩⟩ :=
    exists_uframe_twE6 hf hp hp2 hK σ hσ θ hBN hin hfaith hBel hDB hDcard
  obtain ⟨S₁, hq₁, fr₁, hBT⟩ :=
    exists_torus_uframe (τ := Tag.E6) (Or.inr (Or.inl rfl)) hp hp2 S fr hBel htor
  obtain ⟨Ψ, hΨ, horth, hcard, h2r⟩ :=
    uframe_conclude hField hp hp2 S₁ (hq₁.trans hq) fr₁ hBT hBel hDB hDcard hJG hJ hcent hF
  exact ⟨Ψ, S₁.ρ, hΨ, S₁.frob.isRoot_iff, S₁.frob.iform_eq, horth, hcard, h2r⟩

end UFrame

end CFSG.StandardType.TableCRes

end

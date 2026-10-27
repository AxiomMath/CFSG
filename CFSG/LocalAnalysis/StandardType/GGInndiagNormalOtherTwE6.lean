module

public import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOtherE6
public import CFSG.LieType.Chevalley.TwistedE6NormalForm

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace InndiagE6

section RootSetTw

variable (K : Type) [Field K]

@[expose] def TwistedNFOn (τ : Tag) (ρ : Equiv.Perm (Fin τ.rank)) (n : ℕ)
    (S : (Fin τ.rank → ℤ) → Prop) : Prop :=
  Subgroup.center (MarkChev.twistedH τ.cartan S K ρ n) = ⊥ ∧
    DiagNF (MarkChev.twistedH τ.cartan S K ρ n) (markDiagUnit S K)

variable {K} in
theorem TwistedNFOn.of_eq {τ : Tag} {ρ : Equiv.Perm (Fin τ.rank)} {n : ℕ}
    {S S' : (Fin τ.rank → ℤ) → Prop} (hS : S = S') (h : TwistedNFOn K τ ρ n S) :
    TwistedNFOn K τ ρ n S' :=
  hS ▸ h

end RootSetTw

section TwE6


theorem diagNF_twistedE6 {n : ℕ} (hn : 1 ≤ n) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) :
    Subgroup.center (twistedE6RootGroup K σ) = ⊥ ∧
      DiagNF (twistedE6RootGroup K σ) (rootDiagUnit TwistTag.E6.tag) := by
  obtain ⟨-, -, -, -, -, hcompat, hfield, hnf, -, -, -, hZ, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hn K hK σ hσ
  refine ⟨hZ, fun α b hb hb' => ?_⟩
  obtain ⟨g, u, δ, rfl⟩ := hnf α
  set c : Fin TwistTag.E6.tag.rank → Kˣ := fun i => Units.map δ.toRingHom.toMonoidHom (b i)
  have hδd : Units.map (entrywiseHom δ.toRingHom) (rootDiagUnit TwistTag.E6.tag b) =
      rootDiagUnit TwistTag.E6.tag c :=
    units_map_entrywiseHom_rootDiagUnit_ringEquiv δ b
  have hα : ∀ x : twistedE6RootGroup K σ,
      (((MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u * fieldActor σ δ :
        MulAut (twistedE6RootGroup K σ)) x : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
      (g : ModGL TwistTag.E6.tag K) *
        (rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) *
          Units.map (entrywiseHom δ.toRingHom) (x : ModGL TwistTag.E6.tag K) *
            (rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u))⁻¹) *
        (g : ModGL TwistTag.E6.tag K)⁻¹ := by
    intro x
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_mul, Subgroup.coe_inv, hcompat, hfield]
  have hsurj : ∀ x ∈ twistedE6RootGroup K σ, ∃ y : twistedE6RootGroup K σ,
      Units.map (entrywiseHom δ.toRingHom) (y : ModGL TwistTag.E6.tag K) = x := by
    intro x hx
    refine ⟨(fieldActor σ δ).symm ⟨x, hx⟩, ?_⟩
    rw [← hfield, MulEquiv.apply_symm_apply]
  have hc1 : ∀ x ∈ twistedE6RootGroup K σ, rootDiagUnit TwistTag.E6.tag c * x *
      (rootDiagUnit TwistTag.E6.tag c)⁻¹ ∈ twistedE6RootGroup K σ := by
    intro x hx
    obtain ⟨y, rfl⟩ := hsurj x hx
    have hmem := (fieldActor σ δ ⟨_, hb y y.2⟩).2
    rwa [hfield, Subgroup.coe_mk, map_mul, map_mul, map_inv, hδd] at hmem
  have hc2 : ∀ x ∈ twistedE6RootGroup K σ, (rootDiagUnit TwistTag.E6.tag c)⁻¹ * x *
      rootDiagUnit TwistTag.E6.tag c ∈ twistedE6RootGroup K σ := by
    intro x hx
    obtain ⟨y, rfl⟩ := hsurj x hx
    have hmem := (fieldActor σ δ ⟨_, hb' y y.2⟩).2
    rwa [hfield, Subgroup.coe_mk, map_mul, map_mul, map_inv, hδd] at hmem
  have hcomm : rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) *
      rootDiagUnit TwistTag.E6.tag c = rootDiagUnit TwistTag.E6.tag c *
        rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) := by
    rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
  refine ⟨g, g.2, c, hc1, hc2, fun h hh => ?_⟩
  rw [hα, hα, Subgroup.coe_mk, map_mul, map_mul, map_inv, hδd]
  set du := rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u)
  set dc := rootDiagUnit TwistTag.E6.tag c
  set S := Units.map (entrywiseHom δ.toRingHom) (h : ModGL TwistTag.E6.tag K)
  set G : ModGL TwistTag.E6.tag K := (g : ModGL TwistTag.E6.tag K)
  calc G * (du * (dc * S * dc⁻¹) * du⁻¹) * G⁻¹ = G * ((du * dc) * S * (du * dc)⁻¹) * G⁻¹ := by
        group
    _ = G * ((dc * du) * S * (dc * du)⁻¹) * G⁻¹ := by rw [hcomm]
    _ = G * dc * G⁻¹ * (G * (du * S * du⁻¹) * G⁻¹) * (G * dc * G⁻¹)⁻¹ := by group

theorem twistedNFOn_isRoot_E6 {n : ℕ} (hn : 1 ≤ n) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) :
    TwistedNFOn K TwistTag.E6.tag TwistTag.E6.perm n (IsRoot TwistTag.E6.tag) := by
  have : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  set σ := iterateFrobeniusEquiv K 2 n with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => by
    rw [hσdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  have hC : MarkChev.twistedH TwistTag.E6.tag.cartan (IsRoot TwistTag.E6.tag) K TwistTag.E6.perm
      n = twistedE6RootGroup K σ := by
    rw [twistedH_eq_commutator K .E6 n σ.toRingHom hσ]
    exact (finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two hn K hK σ.toRingHom hσ).2.2.1
  unfold TwistedNFOn
  rw [hC, markDiagUnit_isRoot]
  exact diagNF_twistedE6 hn K hK σ hσ

theorem ggInndiagNormal_twE6 {n : ℕ} (hn : 1 ≤ n) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) :
    GGInndiagNormal
      (LargeEvenCenterQuot (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n))
      (LargeEvenChevIDImage TwistTag.E6.tag.cartan K
        (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n)) := by
  obtain ⟨hZ, hNF⟩ :=
    (twistedNFOn_isRoot_E6 hn K hK).of_eq (largeEvenIsRoot_eq_isRoot TwistTag.E6.tag).symm
  apply ggInndiagNormal_chevID_of_diagNF
  · rw [largeEvenTwistedH_eq]
    exact hZ
  · rw [largeEvenTwistedH_eq, diagHom_eq_markDiagUnit]
    exact hNF

end TwE6

end InndiagE6

end CFSG.StandardType

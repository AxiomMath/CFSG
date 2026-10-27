module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.Converse.PSL2
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.Converse.PSU3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.Converse.Sz
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.Converse.Lift
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.FinalTheorem

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace Converse

open PFchapter1section1 PFAppendixIII

universe u v

/-! ### Parity and involutions

Cauchy's theorem at the prime two, in the form the proof below needs: even order is the
presence of an involution, odd order its absence. -/

private theorem even_natCard_iff_exists_involution (K : Type u) [Group K] [Finite K] :
    Even (Nat.card K) ↔ ∃ x : K, x ≠ 1 ∧ x ^ 2 = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · intro h
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 h.two_dvd
    refine ⟨x, ?_, ?_⟩
    · intro hx1
      rw [hx1, orderOf_one] at hx
      exact absurd hx (by decide)
    · rw [← hx]; exact pow_orderOf_eq_one x
  · rintro ⟨x, hx1, hx2⟩
    have hord : orderOf x = 2 := orderOf_eq_prime hx2 hx1
    have : (2 : ℕ) ∣ Nat.card K := hord ▸ orderOf_dvd_natCard x
    exact even_iff_two_dvd.2 this

private theorem even_natCard_subgroup_iff_exists_involution {G : Type u} [Group G] [Finite G]
    (M : Subgroup G) :
    Even (Nat.card M) ↔ ∃ x ∈ M, _root_.CFSG.IsInvolution x := by
  rw [even_natCard_iff_exists_involution]
  constructor
  · rintro ⟨x, hx1, hx2⟩
    refine ⟨(x : G), x.2, ?_, ?_⟩
    · simpa [OneMemClass.coe_eq_one] using hx1
    · have := congrArg (Subtype.val) hx2
      simpa using this
  · rintro ⟨x, hxM, hx1, hx2⟩
    refine ⟨⟨x, hxM⟩, ?_, ?_⟩
    · simpa [OneMemClass.coe_eq_one] using hx1
    · ext; simpa using hx2

private theorem odd_natCard_subgroup_iff_forall_not_involution {G : Type u} [Group G] [Finite G]
    (M : Subgroup G) :
    Odd (Nat.card M) ↔ ∀ x ∈ M, ¬ _root_.CFSG.IsInvolution x := by
  rw [← Nat.not_even_iff_odd, even_natCard_subgroup_iff_exists_involution]
  constructor
  · intro h x hxM hx
    exact h ⟨x, hxM, hx.1, hx.2⟩
  · rintro h ⟨x, hxM, hx1, hx2⟩
    exact h x hxM ⟨hx1, hx2⟩

/-- The parity conditions give strong embedding as `BenderSuzuki.FinalTheorem` states it.
This is Cauchy's theorem at the prime two, applied twice. -/
private theorem isStronglyEmbedded_of_parity {G : Type u} [Group G] [Finite G]
    {M : Subgroup G} (hne : M ≠ ⊤) (heven : Even (Nat.card M))
    (hodd : ∀ g : G, g ∉ M →
      Odd (Nat.card (M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G))) :
    _root_.IsStronglyEmbedded M :=
  ⟨hne, (even_natCard_subgroup_iff_exists_involution M).1 heven,
    fun g hg => (odd_natCard_subgroup_iff_forall_not_involution _).1 (hodd g hg)⟩

/-- **Hypothesis (A) makes the point stabilizer strongly embedded.**

`H` is proper because the involution `t` lies outside it, and has even order because it
contains `Q`.  For `g ∉ H` the intersection `H ⊓ gHg⁻¹` is the stabilizer of the pair of
distinct points `ω`, `g • ω`, hence has the same order as `D` by double transitivity —
and `|D|` is odd. -/
public theorem hypothesisA_stronglyEmbedded
    {G : Type u} {Ω : Type v} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {H D Q : Subgroup G} {t : G} (hA : HypothesisA G Ω H D Q t) :
    _root_.IsStronglyEmbedded H := by
  obtain ⟨ω, hHω⟩ := hA.A1.point_stabilizer
  have hmem : ∀ g : G, g ∈ H ↔ g • ω = ω := by
    intro g; rw [hHω]; exact MulAction.mem_stabilizer_iff
  -- the involution moves the base point, and so does its inverse
  have htω : t⁻¹ • ω ≠ ω := by
    intro hcon
    refine hA.A1.t_not_mem_H ((hmem t).2 ?_)
    have h := congrArg (fun z : Ω => t • z) hcon
    simp only [smul_inv_smul] at h
    exact h.symm
  have hDstab : D = MulAction.stabilizer G ω ⊓ MulAction.stabilizer G (t⁻¹ • ω) := by
    rw [hA.A1.D_eq, hHω, rightConjugate_stabilizer]
  have hΩpos : 0 < Nat.card Ω - 1 := by
    haveI : Nonempty Ω := ⟨ω⟩
    have hne : Nat.card Ω ≠ 1 := by
      intro h
      obtain ⟨hsub, -⟩ := Nat.card_eq_one_iff_unique.1 h
      exact htω (hsub.allEq _ _)
    have hpos : 0 < Nat.card Ω := Nat.card_pos
    omega
  refine isStronglyEmbedded_of_parity ?_ ?_ ?_
  · intro hc
    exact hA.A1.t_not_mem_H (by rw [hc]; exact Subgroup.mem_top t)
  · obtain ⟨c, hc⟩ : (2 : ℕ) ∣ Nat.card H :=
      dvd_trans hA.A1.Q_even.two_dvd (Subgroup.card_dvd_of_le hA.A1.Q_le_H)
    exact ⟨c, by omega⟩
  · intro g hg
    have hgω : g • ω ≠ ω := fun hc => hg ((hmem g).2 hc)
    have hconj : H ⊓ H.map (MulAut.conj g).toMonoidHom =
        MulAction.stabilizer G ω ⊓ MulAction.stabilizer G (g • ω) := by
      rw [hHω, ← MulAction.stabilizer_smul_eq_stabilizer_map_conj]
    -- both two-point stabilizers satisfy `|H| = |two-point stabilizer| * (|Ω| - 1)`
    have h1 := card_stabilizer_eq_twoPoint_mul hA.A1.two_transitive hgω
    have h2 := card_stabilizer_eq_twoPoint_mul hA.A1.two_transitive htω
    rw [hconj]
    have hEq : Nat.card (MulAction.stabilizer G ω ⊓ MulAction.stabilizer G (g • ω) :
        Subgroup G) = Nat.card D := by
      rw [hDstab]
      exact Nat.eq_of_mul_eq_mul_right hΩpos (h1.symm.trans h2)
    rw [hEq]
    exact hA.A1.D_odd

/-! ### The three families -/

/-- `PSL(2, 2ᵏ)` has a strongly embedded subgroup for every `k ≥ 2`: the Borel subgroup. -/
public theorem stronglyEmbedded_PSL2_binary (k : ℕ) (hk : 2 ≤ k) :
    _root_.IsStronglyEmbedded (PBorel (BinaryGaloisField k)) :=
  hypothesisA_stronglyEmbedded (hypothesisA_PSL2_binary k hk)

/-- `Sz(2^(2m+1))` has a strongly embedded subgroup for every `m ≥ 1`: the stabilizer of
a point of the ovoid. -/
public theorem stronglyEmbedded_Sz (m : ℕ) [NeZero m] :
    _root_.IsStronglyEmbedded (szHstab m) :=
  hypothesisA_stronglyEmbedded (hypothesisA_Sz m)

/-- `PSU₃(2ᵏ)` has a strongly embedded subgroup for every `k ≥ 2`: the stabilizer of an
isotropic point. -/
public theorem stronglyEmbedded_PSU3 (k : ℕ) [NeZero k] (hk : 2 ≤ k) :
    ∃ M : Subgroup (PSU3 k), _root_.IsStronglyEmbedded M := by
  obtain ⟨act, H, D, Q, t, hA⟩ := hypothesisA_PSU3 k hk
  exact ⟨H, @hypothesisA_stronglyEmbedded _ _ _ _ act _ _ _ _ _ hA⟩

end Converse
end CFSG.BenderSuzuki

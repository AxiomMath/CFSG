module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearPostNineData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearPSL2TorusFamily
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearQuotientCard
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearK0CardDvdTorus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationElevenData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationElevenProductFamily
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The outer product region in linear equation (11)
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The product region `P ⊔ E` contains at least
`(p₁-1) q k'` conjugates of `P`.  All quotient-torus data are derived from
the synchronized post-nine package; the sole explicit geometric input is the
source's centerless-cover consequence `P ∩ E = 1`. -/
public theorem secondCase_linearEquation11_outer_region
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (post : SecondCaseLinearPostNineData c w d K)
    {p1 : ℕ}
    (hLines : Nat.card (secondCase_linesIn G post.od.P post.od.P0) = p1 - 1)
    (hPinterE : post.od.P ⊓ d.E = ⊥) :
    (p1 - 1) * Nat.card K * post.equation9.k' ≤
      Nat.card (secondCase_familyIn G post.od.P d.E) := by
  classical
  let : Fact post.od.p.Prime := ⟨post.od.hp_prime⟩
  have hpodd : Odd post.od.p := secondCase_linear_omega_p_odd c w d post.od
  have hK0leK : post.od.K0 ≤ post.od.K := by
    rw [post.od.K0_eq]
    exact inf_le_right
  have hP0leE : post.od.P0 ≤ d.E :=
    post.od.P0_le_K0.trans (hK0leK.trans post.od.K_le_E)
  have hP0interP : post.od.P ⊓ post.od.P0 = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hFK0 : x ∈ post.od.F ⊓ post.od.K0 :=
      ⟨post.od.P_le_F hx.1, post.od.P0_le_K0 hx.2⟩
    exact Subgroup.mem_bot.mp (by
      rwa [secondCase_linear_omega_F_cap_K0 c w d post.od] at hFK0)
  have hEcentP : d.E ≤ Subgroup.centralizer (post.od.P : Set G) := by
    rw [← Subgroup.le_centralizer_iff]
    exact post.od.P_le_F.trans post.od.F_centralizes_E
  have hP0comm : ∀ h : post.od.P, ∀ k : post.od.P0,
      (h : G) * (k : G) = (k : G) * (h : G) := by
    intro h k
    exact (Subgroup.mem_centralizer_iff.mp (hEcentP (hP0leE k.2))) h h.2
  have hpK0 : post.od.p ∣ Nat.card post.od.K0 := by
    simpa [post.od.P0_card] using
      (Subgroup.card_dvd_of_le post.od.P0_le_K0)
  have hpT : post.od.p ∣ Nat.card post.torus.T :=
    dvd_trans hpK0
      (secondCase_linear_K0_card_dvd_quotientTorus c w d K post.od post.torus)
  have hpart := secondCase_linear_quotientTorus_family_partition
    c w d K post.torus hpodd hpT
  have hk'half : post.equation9.k' = (Nat.card K - 1) / 2 ∨
      post.equation9.k' = (Nat.card K + 1) / 2 :=
    post.equation9.k'_is_half.elim Or.inr Or.inl
  have hQcard : Nat.card (d.E ⧸ Subgroup.center d.E) =
      2 * Nat.card K * Nat.card post.torus.T * post.equation9.k' :=
    secondCase_linear_quotient_card_eq d K post.torus post.equation9.k'
      hk'half post.equation9.k'_odd
  have hToriLower : Nat.card K * post.equation9.k' ≤
      Nat.card (secondCase_toriOf G post.od.P0 d.E) := by
    exact secondCase_linearEquation11_E_orbit_card_lower_of_component
      c w d post.od.s post.od.K post.od.K0 post.od.P0 post.od.K_inverted
      post.od.K0_eq post.od.P0_le_K0 (hK0leK.trans post.od.K_le_E)
      post.od.P0_card post.torus.T post.torus.T_cyclic rfl
      post.torus.T_normalizer_card hpart hpT hQcard
  let Tori : Type u := secondCase_toriOf G post.od.P0 d.E
  let : Fintype Tori := Fintype.ofFinite Tori
  let B : Type u := ULift.{u} (Fin (Nat.card K * post.equation9.k'))
  let τ : B → Tori := fun i =>
    (Fintype.equivFin Tori).symm (Fin.castLE (by
      simpa [Nat.card_eq_fintype_card, Tori] using hToriLower) i.down)
  have hτ : Function.Injective τ := by
    intro i j hij
    apply ULift.ext
    apply Fin.ext
    have hcast : Fin.castLE (by
        simpa [Nat.card_eq_fintype_card, Tori] using hToriLower) i.down =
        Fin.castLE (by
          simpa [Nat.card_eq_fintype_card, Tori] using hToriLower) j.down := by
      simpa [τ, Equiv.apply_symm_apply] using
        congrArg (Fintype.equivFin Tori) hij
    simpa using congrArg Fin.val hcast
  exact secondCase_linearEquation11_product_family_conjugate_card
    (G := G) (P := post.od.P) (P0 := post.od.P0) (E := d.E)
    (p := post.od.p) (p1 := p1) (q := Nat.card K)
    (k' := post.equation9.k') post.od.P_card post.od.P0_card
    hP0interP hP0leE hPinterE hEcentP hP0comm hLines
    (B := B) τ hτ (by simp [B])

/-! ## The explicit torus indexing used by the transported region route -/

/-- The torus family used in the outer-region product construction admits an
explicit injection indexed by `Fin (q * k')`.  The cardinal lower bound is the
same PSL₂ orbit calculation as in `secondCase_linearEquation11_outer_region`;
this theorem exposes the indexing data needed to transport the aligned chain
for each product region.
-/
public theorem secondCase_linearEquation11_outer_region_torus_injection
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (post : SecondCaseLinearPostNineData c w d K) :
    ∃ τ : Fin (Nat.card K * post.equation9.k') →
        secondCase_toriOf G post.od.P0 d.E,
      Function.Injective τ := by
  classical
  let : Fact post.od.p.Prime := ⟨post.od.hp_prime⟩
  have hpodd : Odd post.od.p := secondCase_linear_omega_p_odd c w d post.od
  have hK0leK : post.od.K0 ≤ post.od.K := by
    rw [post.od.K0_eq]
    exact inf_le_right
  have hP0leE : post.od.P0 ≤ d.E :=
    post.od.P0_le_K0.trans (hK0leK.trans post.od.K_le_E)
  have hpK0 : post.od.p ∣ Nat.card post.od.K0 := by
    simpa [post.od.P0_card] using
      (Subgroup.card_dvd_of_le post.od.P0_le_K0)
  have hpT : post.od.p ∣ Nat.card post.torus.T :=
    dvd_trans hpK0
      (secondCase_linear_K0_card_dvd_quotientTorus c w d K post.od post.torus)
  have hpart := secondCase_linear_quotientTorus_family_partition
    c w d K post.torus hpodd hpT
  have hk'half : post.equation9.k' = (Nat.card K - 1) / 2 ∨
      post.equation9.k' = (Nat.card K + 1) / 2 :=
    post.equation9.k'_is_half.elim Or.inr Or.inl
  have hQcard : Nat.card (d.E ⧸ Subgroup.center d.E) =
      2 * Nat.card K * Nat.card post.torus.T * post.equation9.k' :=
    secondCase_linear_quotient_card_eq d K post.torus post.equation9.k'
      hk'half post.equation9.k'_odd
  have hToriLower : Nat.card K * post.equation9.k' ≤
      Nat.card (secondCase_toriOf G post.od.P0 d.E) := by
    exact secondCase_linearEquation11_E_orbit_card_lower_of_component
      c w d post.od.s post.od.K post.od.K0 post.od.P0 post.od.K_inverted
      post.od.K0_eq post.od.P0_le_K0 (hK0leK.trans post.od.K_le_E)
      post.od.P0_card post.torus.T post.torus.T_cyclic rfl
      post.torus.T_normalizer_card hpart hpT hQcard
  let Tori : Type u := secondCase_toriOf G post.od.P0 d.E
  let : Fintype Tori := Fintype.ofFinite Tori
  let τ : Fin (Nat.card K * post.equation9.k') → Tori := fun i =>
    (Fintype.equivFin Tori).symm (Fin.castLE (by
      simpa [Nat.card_eq_fintype_card, Tori] using hToriLower) i)
  have hτ : Function.Injective τ := by
    intro i j hij
    apply Fin.ext
    have hcast : Fin.castLE (by
        simpa [Nat.card_eq_fintype_card, Tori] using hToriLower) i =
        Fin.castLE (by
          simpa [Nat.card_eq_fintype_card, Tori] using hToriLower) j := by
      simpa [τ, Equiv.apply_symm_apply] using
        congrArg (Fintype.equivFin Tori) hij
    simpa using congrArg Fin.val hcast
  exact ⟨τ, hτ⟩

end CFSG.GorensteinWalter

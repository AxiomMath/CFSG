module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearQuotientTorusCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearCenterless
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationNine
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private lemma map_centralizer_P0_le_torus
    {G : Type u} [Group G] [Finite G]
    {c : CentralizerSetup G} {w : SecondCaseWitness c}
    {d : SecondCaseComponentData w}
    {P0 : Subgroup G}
    (q : d.E →* (d.E ⧸ Subgroup.center d.E))
    (hP0leE : P0 ≤ d.E)
    {x : d.E}
    (hx : x ∈ (Subgroup.centralizer (P0 : Set G) ⊓ d.E).subgroupOf d.E) :
    q x ∈ Subgroup.centralizer
      (((P0.subgroupOf d.E).map q : Subgroup (d.E ⧸ Subgroup.center d.E)) : Set _) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rcases Subgroup.mem_map.mp hy with ⟨p0, hp0, hp0y⟩
  have hp0G : (p0 : G) ∈ P0 := hp0
  have hcommG : (x : G) * (p0 : G) = (p0 : G) * (x : G) := by
    simpa using ((Subgroup.mem_centralizer_iff.mp hx.1) (p0 : G) hp0G).symm
  have hcommE : x * ⟨p0, hP0leE hp0G⟩ =
      ⟨p0, hP0leE hp0G⟩ * x := by
    apply Subtype.ext
    exact hcommG
  have hqcomm : q x * q ⟨p0, hP0leE hp0G⟩ =
      q ⟨p0, hP0leE hp0G⟩ * q x := by
    rw [← q.map_mul, ← q.map_mul, hcommE]
  rw [← hp0y]
  exact hqcomm.symm

/-- The centralizer in `E` of the selected order-`p` subgroup `P₀` is the
selected quotient torus, after identifying `E` with its centerless quotient.
The quotient centralizer theorem supplies the forward inclusion, and
centerlessness makes the quotient map injective for the reverse inclusion. -/
public theorem secondCase_linear_P0_centralizer_eq_torus
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (post : SecondCaseLinearPostNineData c w d K)
    (hZ : Subgroup.center d.E = ⊥) :
    (((Subgroup.centralizer (post.od.P0 : Set G) ⊓ d.E).subgroupOf d.E).map
      (QuotientGroup.mk' (Subgroup.center d.E))) = post.torus.T := by
  classical
  let q : d.E →* (d.E ⧸ Subgroup.center d.E) :=
    QuotientGroup.mk' (Subgroup.center d.E)
  have hqker : q.ker = ⊥ := by
    rw [show q = QuotientGroup.mk' (Subgroup.center d.E) by rfl,
      QuotientGroup.ker_mk', hZ]
  have hqinj : Function.Injective q :=
    (MonoidHom.ker_eq_bot_iff q).mp hqker
  have hP0leE : post.od.P0 ≤ d.E := by
    exact post.od.P0_le_K0.trans (by
      rw [post.od.K0_eq]
      exact inf_le_right.trans post.od.K_le_E)
  have hK0leE : post.od.K0 ≤ d.E := by
    rw [post.od.K0_eq]
    exact inf_le_right.trans post.od.K_le_E
  have hK0maple : (post.od.K0.subgroupOf d.E).map q ≤ post.torus.T := by
    have hK0leT := secondCase_equationNine_K0_quotient_le_torus
      c w d post.od.s post.od.K post.od.K0 post.od.K_inverted
      post.od.K0_eq hK0leE post.torus.T post.torus.T_odd_centralized_le
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, hxy⟩
    have hyK0 : (y : G) ∈ post.od.K0 := Subgroup.mem_subgroupOf.mp hy
    have hyT : q y ∈ post.torus.T := by
      apply hK0leT
      exact Subgroup.mem_map.mpr ⟨y, hyK0, rfl⟩
    rw [← hxy]
    exact hyT
  have hP0maple : (post.od.P0.subgroupOf d.E).map q ≤ post.torus.T := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, hxy⟩
    have hyK0 : (y : G) ∈ post.od.K0 :=
      post.od.P0_le_K0 (Subgroup.mem_subgroupOf.mp hy)
    have hyK0sub : y ∈ post.od.K0.subgroupOf d.E :=
      Subgroup.mem_subgroupOf.mpr hyK0
    have hyT : q y ∈ post.torus.T := hK0maple (Subgroup.mem_map.mpr ⟨y, hyK0sub, rfl⟩)
    rw [← hxy]
    exact hyT
  have hP0card : Nat.card post.od.P0 = post.od.p := post.od.P0_card
  have hpodd : Odd post.od.p := secondCase_linear_omega_p_odd c w d post.od
  let : Fact (Nat.Prime post.od.p) := ⟨post.od.hp_prime⟩
  have hRcard : Nat.card ((post.od.P0.subgroupOf d.E).map q) = post.od.p := by
    calc
      Nat.card ((post.od.P0.subgroupOf d.E).map q) =
          Nat.card (post.od.P0.subgroupOf d.E) :=
        Subgroup.card_map_of_injective hqinj
      _ = Nat.card post.od.P0 := by
        rw [← Subgroup.card_map_of_injective
          (K := post.od.P0.subgroupOf d.E) d.E.subtype_injective,
          Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hP0leE]
      _ = post.od.p := hP0card
  have hRcent : Subgroup.centralizer
      (((post.od.P0.subgroupOf d.E).map q :
        Subgroup (d.E ⧸ Subgroup.center d.E)) : Set _) = post.torus.T :=
    secondCase_linear_quotientTorus_centralizer_orderP c w d K post.torus hpodd
      ((post.od.P0.subgroupOf d.E).map q) hP0maple hRcard
  apply le_antisymm
  · intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨x, hx, rfl⟩
    have hle := map_centralizer_P0_le_torus q hP0leE hx
    rw [hRcent] at hle
    exact hle
  · intro z hz
    rcases QuotientGroup.mk'_surjective (Subgroup.center d.E) z with ⟨x, rfl⟩
    have hxRcent : q x ∈ Subgroup.centralizer
        (((post.od.P0.subgroupOf d.E).map q :
          Subgroup (d.E ⧸ Subgroup.center d.E)) : Set _) := by
      rw [hRcent]
      exact hz
    have hxP0 : (x : G) ∈ Subgroup.centralizer (post.od.P0 : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro p0 hp0
      have hp0E : p0 ∈ d.E := hP0leE hp0
      have hp0R : q ⟨p0, hp0E⟩ ∈
          (post.od.P0.subgroupOf d.E).map q := by
        exact Subgroup.mem_map.mpr ⟨⟨p0, hp0E⟩,
          Subgroup.mem_subgroupOf.mpr hp0, rfl⟩
      have hcommQ : q ⟨p0, hp0E⟩ * q x =
          q x * q ⟨p0, hp0E⟩ :=
        (Subgroup.mem_centralizer_iff.mp hxRcent) _ hp0R
      have hcommE : x * ⟨p0, hp0E⟩ = ⟨p0, hp0E⟩ * x := by
        apply hqinj
        simpa only [map_mul] using hcommQ.symm
      exact (congrArg Subtype.val hcommE).symm
    exact Subgroup.mem_map.mpr ⟨x, ⟨hxP0, x.2⟩, rfl⟩

end CFSG.GorensteinWalter

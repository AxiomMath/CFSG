module

public import CFSG.RankThree.PartTwo.Sec13.F135LastR1Dim
public import CFSG.RankThree.PartTwo.Sec13.F135LastR1Tr
public import CFSG.RankThree.PartTwo.Sec13.F135LastR1UC

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
open CFSG.RankThree.PartTwo.Sec13.Res7Proof CritProof
open scoped commutatorElement IsMulCommutative

@[expose] def R1U : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (p : ℕ)
    (C : Subgroup (CFSG.pCore p L)), Cfg1 G A c L p C → ∀ z : L, z * z = 1 → z ≠ 1 →
      (∀ x : L, x * z * x⁻¹ * z⁻¹ ∈ CFSG.oddCore L) →
      ∃ u : G, u * u = 1 ∧ u ≠ 1 ∧ u ≠ (z : G) ∧ u * (z : G) = (z : G) * u ∧
        u ∈ Subgroup.normalizer ((dOf L p C : Subgroup G) : Set G)

theorem r1u_holds : R1U := by
  intro G _ _ A c L p C c1 z hz2 hz1 hzc
  haveI : (omegaOneCore p C).Characteristic := c1.crit.characteristic
  obtain ⟨e⟩ := c1.odd_alt7.quotient_center
  obtain ⟨u, hu2, hu1, huz, huc, huN⟩ := u1c_core (L_le_centralizer c1.data) (orderOf_c c1.data)
    c1.c_not_mem c1.t_norm_L c1.t_inv c1.odd_alt7.isQuasisimple.1 c1.center_two e z hz2 hz1 hzc
  exact ⟨u, hu2, hu1, huz, huc, CritProof.mem_normalizer_map_of_characteristic huN⟩

theorem r1_of_u (hU : R1U) : R1 := by
  intro G _ _ A c L p C c1
  have hcrit := c1.crit
  haveI : Fact p.Prime := ⟨hcrit.prime⟩
  have hDD : DData p ((omegaOneCore p C).map L.subtype) := dData_of_crit135 hcrit
  haveI hEA : IsElementaryAbelian p (↥((omegaOneCore p C).map L.subtype) ⧸
      frattini ↥((omegaOneCore p C).map L.subtype)) := hDD.isElementaryAbelian
  obtain ⟨e⟩ := c1.alt7
  obtain ⟨z, hz2, hz1, hzc, h4, h7⟩ := r1_dim_W hcrit c1.odd_alt7 c1.center_two e
  obtain ⟨u, hu2, hu1, huz, hcomm, huN⟩ := hU G A c L p C c1 z hz2 hz1 hzc
  have hLN : L ≤ Subgroup.normalizer (((omegaOneCore p C).map L.subtype : Subgroup G) : Set G) :=
    r1_L_le_normalizer hcrit
  have hz2' : (z : G) * (z : G) = 1 := congrArg Subtype.val hz2
  let z' : Subgroup.normalizer (((omegaOneCore p C).map L.subtype : Subgroup G) : Set G) :=
    ⟨(z : G), hLN z.2⟩
  let u' : Subgroup.normalizer (((omegaOneCore p C).map L.subtype : Subgroup G) : Set G) :=
    ⟨u, huN⟩
  have hz'1 : z' ≠ 1 := by
    intro h
    apply hz1
    apply Subtype.ext
    have h' : ((z' : Subgroup.normalizer (((omegaOneCore p C).map L.subtype : Subgroup G) : Set G)) :
        G) = 1 := by rw [h]; rfl
    exact h'
  have hu'1 : u' ≠ 1 := by
    intro h
    apply hu1
    have h' : ((u' : Subgroup.normalizer (((omegaOneCore p C).map L.subtype : Subgroup G) : Set G)) :
        G) = 1 := by rw [h]; rfl
    exact h'
  have hz'sq : z' ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, pow_two]
    exact hz2'
  have hu'sq : u' ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, pow_two]
    exact hu2
  have hz'o : orderOf z' = 2 := orderOf_eq_prime hz'sq hz'1
  have hu'o : orderOf u' = 2 := orderOf_eq_prime hu'sq hu'1
  have hzu : u' * z' = z' * u' := Subtype.ext hcomm
  have huz' : u' ≠ z' := fun h => huz (congrArg Subtype.val h)
  obtain ⟨hle4, hle2⟩ := r1_count hDD hz'o hu'o hzu huz'
  have hp7 : 7 ≤ p := h7 hle4
  have h4' : 4 ≤ Module.finrank (ZMod p) (Module.End.eigenspace
      (frattiniLinN p ((omegaOneCore p C).map L.subtype) z') (-1 : ZMod p)) := h4
  have hWu : 2 ≤ Module.finrank (ZMod p) (↥(Module.End.eigenspace
      (frattiniLinN p ((omegaOneCore p C).map L.subtype) z') (-1 : ZMod p) ⊓
      Module.End.eigenspace (frattiniLinN p ((omegaOneCore p C).map L.subtype) u') (1 : ZMod p))) := by
    omega
  haveI hEA' : IsElementaryAbelian p (↥(dOf L p C) ⧸ frattini ↥(dOf L p C)) := hEA
  exact ⟨{ c1 with
    z := (z : G)
    u := u
    p_ge_seven := hp7
    z_mem := z.2
    u_sq := hu2
    u_ne := hu1
    Dp_rank := r1_rank_transfer hcrit hLN hz2 h4
    Cu_rank := r1_cu_transfer hcrit hLN hz2 huN hu2 hcomm hWu }⟩

theorem r1_holds : R1 := r1_of_u r1u_holds

end CFSG.RankThree.PartTwo.Sec13.F135Last

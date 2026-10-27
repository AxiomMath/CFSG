module

public import CFSG.Monster.Existence.TwoB
public import CFSG.Monster.Existence.Monolith
public import CFSG.Monster.B.Cbar.SylowControl

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG CFSG.Monster CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated Subgroup

variable {G : Type} [Group G]

abbrev twoCore (z : G) : Subgroup G := inSubgroup (pCore 2) (cent z)

theorem twoCore_le (z : G) : twoCore z ≤ cent z := map_subtype_le _

theorem self_mem_twoCore [Finite G] {z : G} (hz : orderOf z = 2) : z ∈ twoCore z := by
  have hn : (zpowers (⟨z, self_mem_cent z⟩ : cent z)).Normal := ⟨fun n hn g => by
    have hc : (g : G) * z = z * g := mem_centralizer_singleton_iff.1 g.2
    have hc' : g * (⟨z, self_mem_cent z⟩ : cent z) = ⟨z, self_mem_cent z⟩ * g := Subtype.ext hc
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hn
    rw [(Commute.zpow_right hc' k).eq, mul_inv_cancel_right]
    exact zpow_mem (mem_zpowers _) k⟩
  have hp : IsPGroup 2 (zpowers (⟨z, self_mem_cent z⟩ : cent z)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_mk, hz, pow_one])
  have hle : zpowers (⟨z, self_mem_cent z⟩ : cent z) ≤ pCore 2 (cent z) := le_sSup ⟨hn, hp⟩
  show z ∈ (pCore 2 (cent z)).map (cent z).subtype
  exact ⟨⟨z, self_mem_cent z⟩, hle (mem_zpowers _), rfl⟩

theorem twoCore_le_centralizer_self (z : G) :
    twoCore z ≤ centralizer ({z} : Set G) := twoCore_le z

theorem self_mem_centralizer_twoCore (z : G) : z ∈ centralizer (twoCore z : Set G) := by
  rw [mem_centralizer_iff]
  intro q hq
  exact mem_centralizer_singleton_iff.1 (twoCore_le z hq)

theorem IsTwoBCentralizer.center_eq [Finite G] {z : G} (hz : orderOf z = 2)
    (h : IsTwoBCentralizer z) : (center (twoCore z)).map (twoCore z).subtype = zpowers z := by
  obtain ⟨⟨-, -, -, hcard⟩, -⟩ := h
  have hzQ := self_mem_twoCore hz
  let e : pCore 2 (cent z) ≃* twoCore z :=
    (pCore 2 (cent z)).equivMapOfInjective (cent z).subtype (cent z).subtype_injective
  have hcard' : Nat.card (center (twoCore z)) = 2 := by
    rw [← center_map_mulEquiv e, card_map_of_injective e.injective, hcard]
  symm
  refine eq_of_le_of_card_ge ?_ ?_
  · rw [zpowers_le]
    refine ⟨⟨z, hzQ⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_center_iff]
    intro q
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (twoCore_le z q.2))
  · rw [card_map_of_injective (twoCore z).subtype_injective, hcard', Nat.card_zpowers, hz]

theorem IsTwoBCentralizer.inf_centralizer_eq [Finite G] {z : G} (hz : orderOf z = 2)
    (h : IsTwoBCentralizer z) :
    cent z ⊓ centralizer (twoCore z : Set G) = zpowers z := by
  refine le_antisymm ?_ ?_
  · rintro g ⟨-, hg⟩
    have hgQ : g ∈ twoCore z := h.2.2.1 hg
    rw [← h.center_eq hz, B.map_center_eq_inf_centralizer]
    exact ⟨hgQ, hg⟩
  · rw [zpowers_le]
    exact ⟨self_mem_cent z, self_mem_centralizer_twoCore z⟩

theorem IsTwoBCentralizer.card_sylow [Finite G] {z : G} (h : IsTwoBCentralizer z)
    (P : Sylow 2 (cent z)) : Nat.card P = 2 ^ 46 := by
  rw [Sylow.card_eq_multiplicity, h.2.2.2.2.1, Nat.factorization_def _ Nat.prime_two,
    twoBCentralizerOrder]
  rw [show 2 ^ 46 * 3 ^ 9 * 5 ^ 4 * 7 ^ 2 * 11 * 13 * 23 = 2 ^ 46 * 1982582476875 by norm_num,
    padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num), add_zero]

theorem IsTwoBCentralizer.sylow [Finite G] {z : G} (hz : orderOf z = 2)
    (h : IsTwoBCentralizer z) :
    (∀ P : Sylow 2 (cent z), ∃ S : Sylow 2 G,
      (S : Subgroup G) = (P : Subgroup (cent z)).map (cent z).subtype ∧
      Nat.card S = 2 ^ 46 ∧ (center (S : Subgroup G)).map (S : Subgroup G).subtype = zpowers z) ∧
    Nat.Coprime (cent z).index 2 ∧
    (∀ g : G, (∃ n : ℕ, g ^ 2 ^ n = 1) → ∃ c : G, c * g * c⁻¹ ∈ cent z) ∧
    (∀ S : Sylow 2 G, ∃ c : G,
      (center (S : Subgroup G)).map (S : Subgroup G).subtype = zpowers (c * z * c⁻¹)) := by
  have hQn : ((twoCore z).subgroupOf (cent z)).Normal := by
    rw [twoCore, inSubgroup, ← comap_subtype,
      comap_map_eq_self_of_injective (cent z).subtype_injective]
    exact pCore_normal
  have hQp : IsPGroup 2 (twoCore z) := pCore_isPGroup.map _
  obtain ⟨h1, h2, h3, h4⟩ := B.prime_centralizer_sylow_control hz (twoCore_le z) hQn hQp
    (h.center_eq hz) (h.inf_centralizer_eq hz)
  refine ⟨fun P => ?_, h2, h3, h4⟩
  obtain ⟨S, hS, hZ⟩ := h1 P
  refine ⟨S, hS, ?_, hZ⟩
  rw [hS, card_map_of_injective (cent z).subtype_injective, h.card_sylow P]

theorem orderOf_xGmat : orderOf xGmat = 2 := by
  rw [← orderOf_injective Gmat.subtype Gmat.subtype_injective]
  exact orderOf_xmat

theorem generated_group_Sylow_two_reduction :
    (cent xGmat).map Gmat.subtype = Hmat ∧
    (∀ P : Sylow 2 (cent xGmat), ∃ S : Sylow 2 Gmat,
      (S : Subgroup Gmat) = (P : Subgroup (cent xGmat)).map (cent xGmat).subtype ∧
      Nat.card S = 2 ^ 46 ∧
      (center (S : Subgroup Gmat)).map (S : Subgroup Gmat).subtype = zpowers xGmat) ∧
    (conjugatesOf xGmat).ncard = (cent xGmat).index ∧ Odd (cent xGmat).index ∧
    (∀ t : Gmat, orderOf t = 2 → (∃ c : Gmat, c * t * c⁻¹ ∈ cent xGmat ∧
      orderOf (c * t * c⁻¹) = 2) ∧ ∃ c : Gmat, t * (c * xGmat * c⁻¹) = c * xGmat * c⁻¹ * t) ∧
    (∀ S : Sylow 2 Gmat, ∃ c : Gmat,
      (center (S : Subgroup Gmat)).map (S : Subgroup Gmat).subtype =
        zpowers (c * xGmat * c⁻¹)) := by
  have : Finite Gmat := generated_rational_group_finite_simple.2.2
  obtain ⟨h1, h2, h3, h4⟩ :=
    (isTwoBCentralizer_Gmat xGmat (IsConj.refl _)).sylow orderOf_xGmat
  refine ⟨map_cent_xGmat, h1, (index_centralizer_eq_ncard xGmat).symm, ?_, fun t ht => ?_, h4⟩
  · exact Nat.coprime_two_right.1 h2
  obtain ⟨c, hc⟩ := h3 t ⟨1, by rw [pow_one, ← ht, pow_orderOf_eq_one]⟩
  refine ⟨⟨c, hc, by
    rw [← SemiconjBy.orderOf_eq c (x := t) (show c * t = c * t * c⁻¹ * c by group), ht]⟩, c⁻¹, ?_⟩
  have hcomm := mem_centralizer_singleton_iff.1 hc
  calc t * (c⁻¹ * xGmat * c⁻¹⁻¹) = c⁻¹ * ((c * t * c⁻¹) * xGmat) * c := by group
    _ = c⁻¹ * (xGmat * (c * t * c⁻¹)) * c := by rw [hcomm]
    _ = c⁻¹ * xGmat * c⁻¹⁻¹ * t := by group

theorem orderOf_xGriess : orderOf xGriess = 2 := by
  rw [← orderOf_injective AutO.subtype AutO.subtype_injective]
  exact orderOf_xmat

@[expose] noncomputable def tauGriess : MGriess := ⟨tauB, Gmat_le_AutO tauB_mem_Gmat⟩

noncomputable abbrev GmatGriess : Subgroup MGriess := Gmat.subgroupOf AutO

instance : IsSimpleGroup GmatGriess :=
  have : IsSimpleGroup Gmat := generated_rational_group_finite_simple.2.1
  (subgroupOfEquivOfLe Gmat_le_AutO).isSimpleGroup

theorem tauGriess_mem : tauGriess ∈ GmatGriess := mem_subgroupOf.2 tauB_mem_Gmat

theorem cycle_tauGriess :
    tauGriess * (tauGriess * xGriess * tauGriess⁻¹) * tauGriess⁻¹ =
      xGriess * (tauGriess * xGriess * tauGriess⁻¹) := by
  apply Subtype.ext
  change tauB * (tauB * xmat * tauB⁻¹) * tauB⁻¹ = xmat * (tauB * xmat * tauB⁻¹)
  rw [xmat_eq_xB, conj_tauB_xB, conj_tauB_yB, xB_mul_yB]

theorem xGriess_mul_self : xGriess * xGriess = 1 := by
  apply Subtype.ext
  change xmat * xmat = 1
  rw [xmat_eq_xB, xB_mul_self]

theorem centralizer_xGriess_le : cent xGriess ≤ GmatGriess := by
  intro g hg
  rw [mem_subgroupOf]
  have : (g : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Gvis := map_cent_xGriess ▸ ⟨g, hg, rfl⟩
  exact Hmat_le_Gmat this

theorem isSimpleGroup_MGriess :
    IsSimpleGroup MGriess := by
  obtain ⟨h1, -, -, -⟩ := (isTwoBCentralizer_MGriess xGriess (IsConj.refl _)).sylow orderOf_xGriess
  obtain ⟨P, hP, -, hZ⟩ := h1 default
  have hPx : (P : Subgroup MGriess) ≤ cent xGriess := hP ▸ map_subtype_le _
  exact isSimpleGroup_of_cycle xGriess_mul_self tauGriess_mem cycle_tauGriess
    centralizer_xGriess_le P (hPx.trans centralizer_xGriess_le)
    ((normalizer_le_centralizer_of_center orderOf_xGriess hZ).trans centralizer_xGriess_le)

theorem odd_index_Gmat :
    Odd GmatGriess.index := by
  obtain ⟨h1, -, -, -⟩ := (isTwoBCentralizer_MGriess xGriess (IsConj.refl _)).sylow orderOf_xGriess
  obtain ⟨P, hP, -, -⟩ := h1 default
  have hPx : (P : Subgroup MGriess) ≤ cent xGriess := hP ▸ map_subtype_le _
  have h1 := P.not_dvd_index
  have h2 : GmatGriess.index ∣ (P : Subgroup MGriess).index :=
    index_dvd_of_le (hPx.trans centralizer_xGriess_le)
  exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 fun h => h1 (h.trans h2))

theorem MGriess_finite_nonabelian_simple :
    Finite MGriess ∧ IsSimpleGroup MGriess ∧ ∃ g h : MGriess, g * h ≠ h * g := by
  refine ⟨inferInstance, isSimpleGroup_MGriess, tauGriess, xGriess, fun h => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hxxt, -, -, hconj, -, -⟩ :=
    generated_rational_group_finite_centralizer
  have h' : tauB * xmat * tauB⁻¹ = xmat := by
    have := congrArg Subtype.val h
    change tauB * xmat = xmat * tauB at this
    rw [this, mul_inv_cancel_right]
  exact hxxt (h'.symm.trans hconj)

end CFSG.Monster.Existence

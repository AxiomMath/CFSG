module

public import CFSG.Monster.Existence.TwoPoint.ShapeSixMain
public import CFSG.Monster.Existence.TwoPoint.ShapeSixLift
public import CFSG.Monster.Existence.TwoPoint.ShapeSixPair

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster.GMS CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Blueprint.NativeSporadic
  CFSG.Monster.Generated CFSG.Monster.Griess CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
open scoped commutatorElement

theorem shapeSix_tGriess_ne_one : tGriess ≠ 1 := by
  intro h
  have := orderOf_tGriess
  rw [h, orderOf_one] at this
  norm_num at this

theorem shapeSix_sq_ne_one
    (hG : Gmat = AutO) (hT3 : BabyTableIII) {b z u : MGriess}
    (hV : TableV tGriess b z u) {c e : Shat} (hne : c ≠ e) (hcc : c * c = 1) (hee : e * e = 1)
    (hce : c * e = e * c)
    (hC : Nat.card ↥(Subgroup.centralizer ({c * e} : Set Shat)) = 26489012826931200)
    {x y : cent tGriess} (hx : centToShat hG x = c) (hy : centToShat hG y = e) :
    ¬ ((x : MGriess) * y) * ((x : MGriess) * y) = 1 := by
  intro hs
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hπs : centToShat hG (x * y) = c * e := by rw [map_mul, hx, hy]
  have hne1 : c * e ≠ 1 := by
    intro h
    apply hne
    calc c = c * (e * e) := by rw [hee, mul_one]
      _ = (c * e) * e := by rw [mul_assoc]
      _ = e := by rw [h, one_mul]
  have hs1 : ((x * y : cent tGriess) : MGriess) ≠ 1 := fun h => by
    have h' := (centToShat_eq_one_iff hG (x * y)).2 (Or.inl h)
    rw [hπs] at h'
    exact hne1 h'
  have hst : ((x * y : cent tGriess) : MGriess) ≠ tGriess := fun h => by
    have h' := (centToShat_eq_one_iff hG (x * y)).2 (Or.inr h)
    rw [hπs] at h'
    exact hne1 h'
  have hs2 : orderOf ((x * y : cent tGriess) : MGriess) = 2 :=
    orderOf_eq_two_of_mul_self hs hs1
  have hcov := isBabyCover_natCover hG
  have hφs : coverMap (natCover hG) ((x * y : cent tGriess) : MGriess) = phiShat (c * e) := by
    rw [coverMap_apply (x * y).2, natCover_apply, hπs]
  have hord : orderOf (phiShat (c * e)) = 2 := by
    rw [orderOf_phiShat]
    refine orderOf_eq_prime ?_ hne1
    calc (c * e) ^ 2 = c * e * (c * e) := sq _
      _ = c * (e * c) * e := by rw [mul_assoc, mul_assoc, ← mul_assoc e]
      _ = c * (c * e) * e := by rw [hce]
      _ = (c * c) * (e * e) := by group
      _ = 1 := by rw [hcc, hee, one_mul]
  have hcent : Nat.card ↥(Subgroup.centralizer ({phiShat (c * e)} : Set B)) = babyCentOrder 3 := by
    have h1 := @map_centralizer_singleton Shat B _ Units.instGroup phiShat (c * e)
    have h2 : Nat.card ↥(Subgroup.centralizer ({phiShat (c * e)} : Set B)) =
        Nat.card ↥(Subgroup.centralizer ({c * e} : Set Shat)) := by
      rw [← h1]
      exact Subgroup.card_map_of_injective phiShat.injective
    rw [h2, hC]
    simp [babyCentOrder]
  have h3 : BabyInv 3 (coverMap (natCover hG) ((x * y : cent tGriess) : MGriess)) := by
    rw [hφs]
    exact ⟨hord, hcent⟩
  rcases hcov.babyInv_of_involution hT3 hV (x * y).2 hs2 hst with h0 | h0 | h0
  · exact absurd (h0.unique h3) (by decide)
  · exact absurd (h0.unique h3) (by decide)
  · exact absurd (h0.unique h3) (by decide)

theorem exists_shapeSix_of_pair
    (hcard : Nat.card MGriess = CFSG.Open.monsterOrder)
    (hT3 : BabyTableIII) {b z u : MGriess} (hV : TableV tGriess b z u) {c e : Shat}
    (hc : ∃ g : Shat, (c : Dfull) = (g : Dfull)⁻¹ * cQ * g)
    (he : ∃ g : Shat, (e : Dfull) = (g : Dfull)⁻¹ * cQ * g)
    (hce : c * e = e * c) (hne : c ≠ e)
    (hC : Nat.card ↥(Subgroup.centralizer ({c * e} : Set Shat)) = 26489012826931200)
    (hR : Nat.card ↥(Subgroup.centralizer ({c, e} : Set Shat)) =
      4 * Nat.card ↥⁅Subgroup.centralizer ({c, e} : Set Shat),
        Subgroup.centralizer ({c, e} : Set Shat)⁆)
    (hF : Nonempty (↥⁅Subgroup.centralizer ({c, e} : Set Shat),
        Subgroup.centralizer ({c, e} : Set Shat)⁆ ≃* ↥(adjointGroup Tag.F4 (ZMod 2)))) :
    ∃ y, y ∈ tableVIISet tGriess xGriess tGriess .four_B ∧
      TwoPointShape (cent2 tGriess y) 6 := by
  have hG := Gmat_eq_AutO hcard
  have hφ := isBabyCover_natCover hG
  obtain ⟨x, hxc, hxx, hxconj⟩ := exists_lift_of_conj hG hc
  obtain ⟨y, hye, hyy, hyconj⟩ := exists_lift_of_conj hG he
  have hcc : c * c = 1 := by
    rw [← hxc, ← map_mul, show x * x = 1 from Subtype.ext hxx, map_one]
  have hee : e * e = 1 := by
    rw [← hye, ← map_mul, show y * y = 1 from Subtype.ext hyy, map_one]
  have hsq1 : centToShat hG ((x * y) * (x * y)) = 1 := by
    rw [map_mul, map_mul, hxc, hye]
    calc c * e * (c * e) = c * (e * c) * e := by rw [mul_assoc, mul_assoc, ← mul_assoc e]
      _ = c * (c * e) * e := by rw [hce]
      _ = (c * c) * (e * e) := by group
      _ = 1 := by rw [hcc, hee, one_mul]
  have hsq0 : ((x : MGriess) * y) * ((x : MGriess) * y) = 1 ∨
      ((x : MGriess) * y) * ((x : MGriess) * y) = tGriess :=
    (centToShat_eq_one_iff hG ((x * y) * (x * y))).1 hsq1
  have hsq' : ((x : MGriess) * y) * ((x : MGriess) * y) = tGriess :=
    hsq0.resolve_left (shapeSix_sq_ne_one hG hT3 hV hne hcc hee hce hC hxc hye)
  have hsq : (x : MGriess) * y * x * y = tGriess := by simpa only [mul_assoc] using hsq'
  have hcx : coverMap (natCover hG) (x : MGriess) = phiShat c := by
    rw [coverMap_apply x.2, natCover_apply, hxc]
  have hcy : coverMap (natCover hG) (y : MGriess) = phiShat e := by
    rw [coverMap_apply y.2, natCover_apply, hye]
  have hpair : pairCentB (natCover hG) (x : MGriess) (y : MGriess) =
      Subgroup.centralizer ({phiShat c} : Set B) ⊓ Subgroup.centralizer ({phiShat e} : Set B) := by
    simp only [pairCentB, hcx, hcy]
  obtain ⟨h1, h2, ⟨hFB⟩⟩ := @pairCent_transport_equiv Shat B _ Units.instGroup phiShat c e
  obtain ⟨hF'⟩ := hF
  have hRB : Nat.card ↥(pairCentB (natCover hG) (x : MGriess) (y : MGriess)) =
      4 * Nat.card ↥⁅pairCentB (natCover hG) (x : MGriess) (y : MGriess),
        pairCentB (natCover hG) (x : MGriess) (y : MGriess)⁆ := by
    rw [hpair, h1, h2]
    exact hR
  obtain ⟨N, hN, hNc, ⟨hNe⟩⟩ := exists_two_shape_of_dihedral_pair hφ x.2 y.2 hxx hyy hsq hRB
  have hshape : TwoPointShape (cent2 (x : MGriess) (y : MGriess)) 6 := by
    refine ⟨N, hN, by rw [hNc, pow_one], lieModel_F4_of_mulEquiv ?_⟩
    rw [hpair] at hNe
    exact hNe.trans (hFB.trans hF')
  have hmem : (y : MGriess) ∈ tableVIISet tGriess xGriess (x : MGriess) .four_B := by
    have h4 : ((x : MGriess) * y) ^ 2 = tGriess := by rw [sq]; exact hsq'
    refine ⟨hyconj, ?_, by rw [h4]; exact IsConj.refl _⟩
    refine (orderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_ :
      orderOf ((x : MGriess) * y) = 2 ^ (1 + 1))
    · rw [pow_one, h4]
      exact shapeSix_tGriess_ne_one
    · rw [show 2 ^ (1 + 1) = 2 * 2 from rfl, pow_mul, h4, sq, tGriess_mul_self]
  exact exists_base_rep_fourB hxconj hmem hshape

theorem shapeSix_commutator_le {H : Type*} [Group H] (R : Subgroup H) : ⁅R, R⁆ ≤ R :=
  Subgroup.commutator_le.2 fun _ hg _ hh =>
    R.mul_mem (R.mul_mem (R.mul_mem hg hh) (R.inv_mem hg)) (R.inv_mem hh)

theorem exists_shapeSix_of_product_data
    (hcard : Nat.card MGriess = CFSG.Open.monsterOrder)
    (hT3 : BabyTableIII) {b z u : MGriess} (hV : TableV tGriess b z u) {c e : Shat}
    (hc : ∃ g : Shat, (c : Dfull) = (g : Dfull)⁻¹ * cQ * g)
    (he : ∃ g : Shat, (e : Dfull) = (g : Dfull)⁻¹ * cQ * g)
    (hce : c * e = e * c) (hne : c ≠ e) {R F C : Subgroup Shat}
    (hR : R = Subgroup.centralizer ({c, e} : Set Shat)) (hF : F = ⁅R, R⁆)
    (hC : C = Subgroup.centralizer ({c * e} : Set Shat)) (hRC : R ≤ C) (hrel : R.relIndex C = 2)
    (hCcard : Nat.card ↥C = 26489012826931200) (hFcard : Nat.card ↥F = 3311126603366400)
    (hcomp : CFSG.IsComponent (F.subgroupOf C))
    (hF' : ∃ F' : Subgroup ↥C, CFSG.IsComponent F' ∧
      (∀ K : Subgroup ↥C, CFSG.IsComponent K → K = F') ∧
      Nonempty (↥F' ≃* ↥(adjointGroup Tag.F4 (ZMod 2)))) :
    ∃ y, y ∈ tableVIISet tGriess xGriess tGriess .four_B ∧
      TwoPointShape (cent2 tGriess y) 6 := by
  have hFC : F ≤ C := hF ▸ (shapeSix_commutator_le R).trans hRC
  have hRcard : Nat.card ↥R = 4 * Nat.card ↥F := by
    have h1 : Nat.card ↥(R.subgroupOf C) * (R.subgroupOf C).index = Nat.card ↥C :=
      Subgroup.card_mul_index _
    have h2 : Nat.card ↥(R.subgroupOf C) = Nat.card ↥R :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRC).toEquiv
    have h3 : (R.subgroupOf C).index = 2 := hrel
    rw [h3, h2] at h1
    omega
  obtain ⟨F', -, hF'uniq, ⟨eF⟩⟩ := hF'
  have hFF' : F.subgroupOf C = F' := hF'uniq _ hcomp
  have hFad : Nonempty (↥⁅R, R⁆ ≃* ↥(adjointGroup Tag.F4 (ZMod 2))) :=
    ⟨(MulEquiv.subgroupCongr hF.symm).trans ((Subgroup.subgroupOfEquivOfLe hFC).symm.trans
      ((MulEquiv.subgroupCongr hFF').trans eF))⟩
  rw [hF] at hRcard
  rw [hR] at hRcard hFad
  rw [hC] at hCcard
  exact exists_shapeSix_of_pair hcard hT3 hV hc he hce hne hCcard hRcard hFad

end CFSG.Monster.Existence

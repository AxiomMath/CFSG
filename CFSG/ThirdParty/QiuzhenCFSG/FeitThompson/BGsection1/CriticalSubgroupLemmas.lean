module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.Defs
import Mathlib.Data.Nat.Choose.Dvd

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise commutatorElement

section CriticalSubgroupLemmas

variable {G : Type*} [Group G]

/-- The second term `Z₂(G)` of the upper central series is characteristic. -/
public theorem CFSG.upperCentralSeries_two_characteristic (G : Type*) [Group G] :
    (Subgroup.upperCentralSeries G 2).Characteristic := by
  rw [Subgroup.characteristic_iff_comap_eq]
  intro φ
  exact Subgroup.comap_upperCentralSeries (G := G) (H := G) φ 2

/-- Any subgroup of `Z₂(G)` has commutator with `G` contained in `Z(G)`. -/
public theorem CFSG.commutator_le_center_of_le_upperCentralSeries_two
    (H : Subgroup G) (hH : H ≤ Subgroup.upperCentralSeries G 2) :
    ⁅H, (⊤ : Subgroup G)⁆ ≤ Subgroup.center G := by
  refine Subgroup.commutator_le.2 ?_
  intro x hx y hy
  have hxZ2 : x ∈ Subgroup.upperCentralSeries G 2 := hH hx
  have hxStep : ∀ z : G, x * z * x⁻¹ * z⁻¹ ∈ Subgroup.upperCentralSeries G 1 := by
    exact (Subgroup.mem_upperCentralSeries_succ_iff (G := G) (n := 1) (x := x)).1 hxZ2
  have hxy : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.upperCentralSeries G 1 := hxStep y
  simpa [Subgroup.upperCentralSeries_one, commutatorElement_def] using hxy


/-- Convert an ambient commutator containment `⁅H,G⁆ ≤ centerIn(H)` into
`commutator(H) ≤ center(H)` for the subgroup `H`. -/
public theorem CFSG.subgroup_commutator_le_center_of_commutator_le_centerIn
    (H : Subgroup G)
    (hcomm : ⁅H, (⊤ : Subgroup G)⁆ ≤ centerIn (G := G) H) :
    _root_.commutator (↥H) ≤ Subgroup.center (↥H) := by
  have hcommHH : ⁅H, H⁆ ≤ centerIn (G := G) H :=
    (Subgroup.commutator_mono (le_rfl : H ≤ H) (show H ≤ (⊤ : Subgroup G) by simp)).trans hcomm
  intro x hx
  have hx_map : H.subtype x ∈ (_root_.commutator (↥H)).map H.subtype :=
    Subgroup.mem_map_of_mem H.subtype hx
  have hxHH : H.subtype x ∈ ⁅H, H⁆ := by
    simpa using ((Subgroup.map_subtype_commutator (H := H)).symm ▸ hx_map)
  have hx_centH : H.subtype x ∈ centerIn (G := G) H := hcommHH hxHH
  have hx_centralizer : (x : G) ∈ Subgroup.centralizer (H : Set G) := hx_centH.2
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  simpa using
    (Subgroup.mem_centralizer_iff (g := (x : G)) (s := (H : Set G))).1 hx_centralizer
      (y : G) y.property

/-- If `⁅H,G⁆ ≤ centerIn(H)`, then `H` has nilpotency class at most `2`. -/
public theorem CFSG.nilpotencyClassLe_two_of_commutator_le_centerIn
    (H : Subgroup G)
    (hcomm : ⁅H, (⊤ : Subgroup G)⁆ ≤ centerIn (G := G) H) :
    NilpotencyClassLe 2 (↥H) := by
  have hcomm_sub : _root_.commutator (↥H) ≤ Subgroup.center (↥H) :=
    subgroup_commutator_le_center_of_commutator_le_centerIn (G := G) H hcomm
  have hL1_le_center :
      (⊤ : Subgroup (↥H)).lowerCentralSeries 1 ≤ Subgroup.center (↥H) := by
    rw [Subgroup.top_lowerCentralSeries_one]
    exact hcomm_sub
  have hL2_bot : (⊤ : Subgroup (↥H)).lowerCentralSeries 2 = ⊥ := by
    simpa [Nat.succ_eq_add_one] using
      (Subgroup.lowerCentralSeries_succ_eq_bot (⊤ : Subgroup (↥H)) (n := 1) hL1_le_center)
  have hnil : Group.IsNilpotent (↥H) :=
    (Subgroup.nilpotent_iff_lowerCentralSeries (G := ↥H)).2 ⟨2, hL2_bot⟩
  letI : Group.IsNilpotent (↥H) := hnil
  have hclass : Group.nilpotencyClass (↥H) ≤ 2 :=
    (Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le (G := ↥H)).1 hL2_bot
  unfold NilpotencyClassLe
  exact (Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le (G := ↥H)).2 hclass


/-- If `H` is characteristic in `G` and `K` is characteristic in `H`, then the image of `K` in
`G` is characteristic. -/
public theorem CFSG.characteristic_map_subtype_of_characteristic
    (H : Subgroup G) [H.Characteristic] (K : Subgroup H) [K.Characteristic] :
    (K.map H.subtype).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro φ
  have hHmap : H.map φ.toMonoidHom = H :=
    (Subgroup.characteristic_iff_map_eq.mp (inferInstance : H.Characteristic)) φ
  let φH : H ≃* H := (φ.subgroupMap H).trans (MulEquiv.subgroupCongr hHmap)
  have hKmap : K.map φH.toMonoidHom = K :=
    (Subgroup.characteristic_iff_map_eq.mp (inferInstance : K.Characteristic)) φH
  have hcomp :
      φ.toMonoidHom.comp H.subtype = H.subtype.comp φH.toMonoidHom := by
    ext x
    rfl
  calc
    (K.map H.subtype).map φ.toMonoidHom
        = K.map (φ.toMonoidHom.comp H.subtype) := by
            simp [Subgroup.map_map]
    _ = K.map (H.subtype.comp φH.toMonoidHom) := by rw [hcomp]
    _ = (K.map φH.toMonoidHom).map H.subtype := by
          simp [Subgroup.map_map]
    _ = K.map H.subtype := by rw [hKmap]


/-- `p`-group criterion by prime-order elimination:
if every prime-order element of a finite subgroup has order `p`,
then that subgroup is a `p`-group. -/
public theorem CFSG.isPGroup_of_prime_order_eq_p [Finite G]
    (p : ℕ) [Fact p.Prime] (H : Subgroup G)
    (hprime : ∀ x : H, Nat.Prime (orderOf x) → orderOf x = p) :
    IsPGroup p H := by
  refine (IsPGroup.iff_orderOf (p := p) (G := H)).2 ?_
  intro x
  refine ⟨(Nat.primeFactorsList (orderOf x)).length, ?_⟩
  have h0 : orderOf x ≠ 0 := (Nat.pos_iff_ne_zero.mp (orderOf_pos x))
  exact Nat.eq_prime_pow_of_unique_prime_dvd h0 (by
    intro q hq hqd
    have hqd_card : q ∣ Nat.card (Subgroup.zpowers x) := by
      simpa [Nat.card_zpowers] using hqd
    letI : Fintype (Subgroup.zpowers x) := Fintype.ofFinite (Subgroup.zpowers x)
    have hqd_card' : q ∣ Fintype.card (Subgroup.zpowers x) := by
      simpa [Nat.card_eq_fintype_card] using hqd_card
    letI : Fact q.Prime := ⟨hq⟩
    obtain ⟨y, hy⟩ :=
      _root_.exists_prime_orderOf_dvd_card (G := Subgroup.zpowers x) q hqd_card'
    have hy' : Nat.Prime (orderOf (y : H)) := by
      simpa [Subgroup.orderOf_coe, hy] using hq
    have hqy : orderOf (y : H) = p := hprime (y : H) hy'
    have hyq' : orderOf (y : H) = q := by
      simpa [Subgroup.orderOf_coe] using hy
    exact hyq'.symm.trans hqy)

section Z2Omega

variable (p : ℕ)

lemma CFSG.pow_mul_swap_of_relation
    {M : Type*} [Group M] (x y c : M)
    (hrel : y * x = c * x * y)
    (hc_y : Commute c y) :
    ∀ n : ℕ, y ^ n * x = c ^ n * x * y ^ n
  | 0 => by simp
  | n + 1 => by
      calc
        y ^ (n + 1) * x = y * (y ^ n * x) := by simp [pow_succ', mul_assoc]
        _ = y * (c ^ n * x * y ^ n) := by rw [pow_mul_swap_of_relation x y c hrel hc_y n]
        _ = y * c ^ n * x * y ^ n := by simp [mul_assoc]
        _ = c ^ n * y * x * y ^ n := by
              have hycn : Commute (c ^ n) y := hc_y.pow_left n
              rw [hycn.eq]
        _ = c ^ n * (y * x) * y ^ n := by simp [mul_assoc]
        _ = c ^ n * (c * x * y) * y ^ n := by rw [hrel]
        _ = (c ^ n * c) * x * (y * y ^ n) := by simp [mul_assoc]
        _ = (c ^ n * c) * x * (y ^ n * y) := by
              have hy_pow_comm : y * y ^ n = y ^ n * y := by
                calc
                  y * y ^ n = y ^ (n + 1) := (pow_succ' y n).symm
                  _ = y ^ n * y := pow_succ y n
              rw [hy_pow_comm]
        _ = c ^ (n + 1) * x * y ^ (n + 1) := by
              simp [pow_succ, mul_assoc]

lemma CFSG.pow_mul_eq_cpow_mul_pow_mul_pow
    {M : Type*} [Group M] (x y c : M)
    (hrel : y * x = c * x * y)
    (hc_x : Commute c x)
    (hc_y : Commute c y) :
    ∀ n : ℕ, (x * y) ^ n = c ^ (n.choose 2) * x ^ n * y ^ n
  | 0 => by simp
  | n + 1 => by
      calc
        (x * y) ^ (n + 1) = (x * y) ^ n * (x * y) := by simp [pow_succ]
        _ = (c ^ (n.choose 2) * x ^ n * y ^ n) * (x * y) := by
              rw [pow_mul_eq_cpow_mul_pow_mul_pow x y c hrel hc_x hc_y n]
        _ = c ^ (n.choose 2) * x ^ n * (y ^ n * x) * y := by simp [mul_assoc]
        _ = c ^ (n.choose 2) * x ^ n * (c ^ n * x * y ^ n) * y := by
              rw [pow_mul_swap_of_relation x y c hrel hc_y n]
        _ = c ^ (n.choose 2) * (x ^ n * c ^ n) * x * y ^ n * y := by simp [mul_assoc]
        _ = c ^ (n.choose 2) * (c ^ n * x ^ n) * x * y ^ n * y := by
              have hcxnn : Commute (c ^ n) (x ^ n) := (hc_x.pow_left n).pow_right n
              rw [hcxnn.symm.eq]
        _ = (c ^ (n.choose 2) * c ^ n) * (x ^ n * x) * (y ^ n * y) := by simp [mul_assoc]
        _ = c ^ ((n + 1).choose 2) * x ^ (n + 1) * y ^ (n + 1) := by
              have hchoose : (n + 1).choose 2 = n.choose 2 + n := by
                simpa [Nat.choose_one_right, Nat.add_comm] using
                  (Nat.choose_succ_right (n := n + 1) (k := 1) (Nat.succ_pos n))
              rw [hchoose, pow_add, pow_succ, pow_succ]

private lemma CFSG.prime_dvd_choose_two [Fact p.Prime] (hpodd : p ≠ 2) : p ∣ p.choose 2 := by
  have hlt : 2 < p := lt_of_le_of_ne (Fact.out : Nat.Prime p).two_le (Ne.symm hpodd)
  exact (Fact.out : Nat.Prime p).dvd_choose_self (k := 2) (by decide) hlt

private lemma CFSG.choose_two_pow_eq_one
    {M : Type*} [Group M] [Fact p.Prime] {c : M}
    (hpodd : p ≠ 2) (hc : c ^ p = 1) : c ^ (p.choose 2) = 1 := by
  rcases prime_dvd_choose_two (p := p) hpodd with ⟨k, hk⟩
  calc
    c ^ (p.choose 2) = c ^ (p * k) := by simp [hk]
    _ = (c ^ p) ^ k := by rw [pow_mul]
    _ = 1 := by simp [hc]

public lemma CFSG.pth_mul_eq_one_of_class2 [Fact p.Prime]
    (hpodd : p ≠ 2) (x y : G)
    (hxy_center : ⁅y, x⁆ ∈ Subgroup.center G)
    (hx : x ^ p = 1) (hy : y ^ p = 1) :
    (x * y) ^ p = 1 := by
  let c : G := ⁅y, x⁆
  have hc_x : Commute c x := by
    exact (Subgroup.mem_center_iff.mp hxy_center x).symm
  have hc_y : Commute c y := by
    exact (Subgroup.mem_center_iff.mp hxy_center y).symm
  have hrel : y * x = c * x * y := by
    change y * x = ⁅y, x⁆ * x * y
    simp [commutatorElement_def, mul_assoc]
  have hswap := pow_mul_swap_of_relation x y c hrel hc_y p
  have hc_p : c ^ p = 1 := by
    have hx' : x = c ^ p * x := by simpa [hy, mul_assoc] using hswap
    have hx'' := congrArg (fun t => t * x⁻¹) hx'
    exact (by simpa [mul_assoc] using hx''.symm)
  have hpow := pow_mul_eq_cpow_mul_pow_mul_pow x y c hrel hc_x hc_y p
  calc
    (x * y) ^ p = c ^ (p.choose 2) * x ^ p * y ^ p := hpow
    _ = c ^ (p.choose 2) := by simp [hx, hy]
    _ = 1 := choose_two_pow_eq_one (p := p) hpodd hc_p

public lemma CFSG.pth_pow_eq_one_of_mem_omega₁_upperCentralSeries_two [Fact p.Prime]
    (hpodd : p ≠ 2)
    {x : Subgroup.upperCentralSeries G 2}
    (hx : x ∈ omega₁ (G := ↥(Subgroup.upperCentralSeries G 2)) (p := p)) :
    ((x : G) ^ p = 1) := by
  refine Subgroup.closure_induction
    (k := {z : Subgroup.upperCentralSeries G 2 | z ^ (p ^ 1) = 1})
    (x := x) ?mem ?one ?mul ?inv hx
  · intro z hz
    have hz' : z ^ p = 1 := by simpa [pow_one] using hz
    exact congrArg Subtype.val hz'
  · simp
  · intro z₁ z₂ _hz₁ _hz₂ hz₁ hz₂
    have hcomm_le :
        ⁅Subgroup.upperCentralSeries G 2, (⊤ : Subgroup G)⁆ ≤ Subgroup.center G :=
      commutator_le_center_of_le_upperCentralSeries_two (G := G)
        (Subgroup.upperCentralSeries G 2) le_rfl
    have hcomm_mem : ⁅(z₂ : G), (z₁ : G)⁆ ∈ Subgroup.center G := by
      exact hcomm_le (Subgroup.commutator_mem_commutator z₂.property (by simp))
    simpa using
      (pth_mul_eq_one_of_class2 (G := G) (p := p) hpodd (z₁ : G) (z₂ : G) hcomm_mem hz₁ hz₂)
  · intro z _hz hz
    simpa [inv_pow] using congrArg Inv.inv hz

lemma CFSG.pth_pow_eq_one_of_mem_z2OmegaCandidate_raw [Fact p.Prime]
    (hpodd : p ≠ 2) {x : G}
    (hx :
      x ∈ (omega₁ (G := ↥(Subgroup.upperCentralSeries G 2)) (p := p)).map
        (Subgroup.upperCentralSeries G 2).subtype) :
    x ^ p = 1 := by
  rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
  exact pth_pow_eq_one_of_mem_omega₁_upperCentralSeries_two (G := G) (p := p) hpodd hy

/-- Canonical `Z₂`-omega candidate subgroup in `G`. -/
@[expose] public def CFSG.z2OmegaCandidate : Subgroup G :=
  (omega₁ (G := ↥(Subgroup.upperCentralSeries G 2)) (p := p)).map
    (Subgroup.upperCentralSeries G 2).subtype


section PrimeOrderReduction

variable [Finite G] [Fact p.Prime]


end PrimeOrderReduction

public theorem CFSG.z2OmegaCandidate_le_upperCentralSeries_two :
    z2OmegaCandidate (G := G) p ≤ Subgroup.upperCentralSeries G 2 := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
  exact y.property

public theorem CFSG.z2OmegaCandidate_characteristic :
    (z2OmegaCandidate (G := G) p).Characteristic := by
  let Z2 : Subgroup G := Subgroup.upperCentralSeries G 2
  let Ω : Subgroup Z2 := omega₁ (G := ↥Z2) (p := p)
  have hZ2 : Z2.Characteristic := upperCentralSeries_two_characteristic (G := G)
  have hΩ : Ω.Characteristic := by
    simpa [Ω] using (omega₁_characteristic (G := ↥Z2) (p := p))
  simpa [z2OmegaCandidate, Z2, Ω] using
    (characteristic_map_subtype_of_characteristic (G := G) Z2 Ω)


set_option backward.isDefEq.respectTransparency false in
public theorem CFSG.z2OmegaCandidate_exponent_dvd_p_of_odd [Fact p.Prime] (hpodd : p ≠ 2) :
    Monoid.exponent (↥(z2OmegaCandidate (G := G) p)) ∣ p := by
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  apply Subtype.ext
  simpa [z2OmegaCandidate] using
    (pth_pow_eq_one_of_mem_z2OmegaCandidate_raw (G := G) (p := p) hpodd x.property)


end Z2Omega

end CriticalSubgroupLemmas

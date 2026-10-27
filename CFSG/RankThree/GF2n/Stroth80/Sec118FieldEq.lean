module

public import CFSG.RankThree.GF2n.Stroth80.Sec11CM
import CFSG.ClassicalGroups.Symplectic.TransvectionLine
import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
import CFSG.RankThree.GF2n.Stroth80.Sec112
import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoCenter
import CFSG.RankThree.GF2n.Stroth80.Sec118NotTLine
import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194SpBlocks
import CFSG.RankThree.GF2n.Stroth80.Sec34Trans

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
variable [(Q.subgroupOf M).Normal]

theorem Ctx.card_Z_le_two_pow_of_transvAt (hc : Ctx M Q Z B) {n m x : ℕ} (hw : Width Q Z n)
    (hn : 2 < n) {a : ↥M} {h : (a : G) ∈ LB M Q B ∧ IsA2 Q Z (a : G)}
    (hT : CMSpTransvAt M Q Z B m x a h) : Nat.card Z ≤ 2 ^ x := by
  obtain ⟨K, hKf, hKfin, hKcard, φ, g, hg1, hφg⟩ := hT
  have hx : 1 ≤ x := by
    by_contra h0
    have hx0 : x = 0 := by omega
    have := Finite.one_lt_card (α := K)
    rw [hKcard, hx0] at this
    omega
  have hchar : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hx
      hKcard
  let ε : StatedProj (StatedSp m K) ≃* StatedSp m K :=
    CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.statedProjEquivSp
  let ρX : ↥(Xbar M Q Z B) →* StatedSp m K :=
    ((ε.toMonoidHom).comp φ.toMonoidHom).comp
      (QuotientGroup.mk' (Subgroup.center ↥(Xbar M Q Z B)))
  have hρX : ∀ z : ↥(Xbar M Q Z B), ρX z = 1 → z ∈ Subgroup.center ↥(Xbar M Q Z B) := by
    intro z hz
    have h1 : φ (QuotientGroup.mk z) = 1 := ε.injective (by simpa [ρX] using hz)
    have h2 : (QuotientGroup.mk z : XbarMod M Q Z B) = 1 := φ.injective (by simpa using h1)
    exact (QuotientGroup.eq_one_iff z).mp h2
  let aX : ↥(Xbar M Q Z B) :=
    ⟨QuotientGroup.mk a, mk_mem_Xbar_of_LB M Q Z B a h.1 h.2⟩
  have hρa : ρX aX = g := by
    have h1 : φ (QuotientGroup.mk aX) = QuotientGroup.mk g := hφg
    show ε (φ (QuotientGroup.mk aX)) = g
    rw [h1]
    rfl
  obtain ⟨y, hy⟩ := hc.exists_isLBTorus
  obtain ⟨U, hUle, hUcard, -, -, hUE⟩ := hc.exists_lbLine_subset_Ebar hy h
  have hUX : U ≤ Xbar M Q Z B := fun u hu => by
    by_cases hu1 : u = 1
    · rw [hu1]
      exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (hUE u hu hu1)
  let U' : Subgroup ↥(Xbar M Q Z B) := U.subgroupOf (Xbar M Q Z B)
  have hU'card : Nat.card U' = Nat.card Z := by
    rw [← hUcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUX).toEquiv
  let ρ : ↥U' →* StatedSp m K := ρX.comp U'.subtype
  have hsq : ∀ s : ↥U', s * s = 1 := by
    intro s
    apply Subtype.ext
    apply Subtype.ext
    have h1 : ((s : ↥(Xbar M Q Z B)) : Mbar M Q) ∈ U := s.2
    have h2 := hc.isElemAbelian_bar_LB.2 _ (hUle h1)
    simpa [pow_two] using h2
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro s hs
    have hz : (s : ↥(Xbar M Q Z B)) ∈ Subgroup.center ↥(Xbar M Q Z B) := hρX _ hs
    let z : ↥(Subgroup.center ↥(Xbar M Q Z B)) := ⟨s, hz⟩
    have hz2 : z ^ 2 = 1 := by
      apply Subtype.ext
      have := congrArg (fun t : ↥U' => (t : ↥(Xbar M Q Z B))) (hsq s)
      simpa [pow_two, z] using this
    have hodd : Odd (orderOf z) := (hc.odd_card_center_Xbar).of_dvd_nat (orderOf_dvd_natCard z)
    have hdvd : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one hz2
    have h1 : orderOf z = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
      · exact h
      · rw [h] at hodd
        exact absurd hodd (by decide)
    have hz1 : z = 1 := orderOf_eq_one_iff.mp h1
    have hz3 : (s : ↥(Xbar M Q Z B)) = 1 := congrArg Subtype.val hz1
    exact Subtype.ext hz3
  have hrk : ∀ s : ↥U', s ≠ 1 → ((((ρ s : StatedSp m K) : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - 1).rank = 1 := by
    intro s hs
    have hsU : ((s : ↥(Xbar M Q Z B)) : Mbar M Q) ∈ U := s.2
    have hs1 : ((s : ↥(Xbar M Q Z B)) : Mbar M Q) ≠ 1 := by
      intro h1
      apply hs
      apply Subtype.ext
      exact Subtype.ext h1
    obtain ⟨e₀, he₀, hcls⟩ := hc.ebarIsXbarClass hw hn ⟨a, h.1, h.2⟩
    obtain ⟨x₁, hx₁, hx₁'⟩ := (hcls _).1 (hUE _ hsU hs1)
    obtain ⟨x₂, hx₂, hx₂'⟩ := (hcls _).1 (hc.mk_mem_Ebar h.1 h.2)
    let w : ↥(Xbar M Q Z B) := ⟨x₁ * x₂⁻¹, Subgroup.mul_mem _ hx₁ (Subgroup.inv_mem _ hx₂)⟩
    have hsw : (s : ↥(Xbar M Q Z B)) = w * aX * w⁻¹ := by
      apply Subtype.ext
      show ((s : ↥(Xbar M Q Z B)) : Mbar M Q) =
        (x₁ * x₂⁻¹) * (QuotientGroup.mk a : Mbar M Q) * (x₁ * x₂⁻¹)⁻¹
      calc ((s : ↥(Xbar M Q Z B)) : Mbar M Q) = x₁ * e₀ * x₁⁻¹ := hx₁'
        _ = (x₁ * x₂⁻¹) * (x₂ * e₀ * x₂⁻¹) * (x₁ * x₂⁻¹)⁻¹ := by group
        _ = (x₁ * x₂⁻¹) * (QuotientGroup.mk a : Mbar M Q) * (x₁ * x₂⁻¹)⁻¹ := by rw [← hx₂']
    have hρs : ρ s = ρX w * g * (ρX w)⁻¹ := by
      show ρX (s : ↥(Xbar M Q Z B)) = _
      rw [hsw, map_mul, map_mul, map_inv, hρa]
    have hρs' : ((ρ s : StatedSp m K) : GL (Fin m ⊕ Fin m) K) =
        ((ρX w : StatedSp m K) : GL (Fin m ⊕ Fin m) K) * (g : GL (Fin m ⊕ Fin m) K) *
          ((ρX w : StatedSp m K) : GL (Fin m ⊕ Fin m) K)⁻¹ := by
      rw [hρs]
      simp
    rw [hρs', CFSG.ClassicalGroups.Symplectic.rank_conj_sub_one]
    exact hg1
  have hcard := CFSG.ClassicalGroups.Symplectic.card_le_of_forall_rank_eq_one_statedSp
    ρ hinj hsq hrk
  rw [← hU'card, ← hKcard]
  exact hcard

end CFSG.RankThree.GF2n.Stroth80

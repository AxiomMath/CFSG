module

public import CFSG.OddTranspositions.PartFour.OrthFiveLine
import CFSG.OddTranspositions.PartFour.MNeTwo
import CFSG.OddTranspositions.PartFour.OrbitPower
import CFSG.OddTranspositions.PartFour.SideConditions

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Bridge.OddTransp CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem false_of_fischerCentralQuotientModel_five (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {n : ℕ} (hn : 4 ≤ n) {b : LinearMap.BilinForm (ZMod 5) (Fin n → ZMod 5)}
    (hsym : ∀ x y, b x y = b y x) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (hM : CFSG.Open.fischerCentralQuotientModel (imageClass hC)
      (Subgroup.closure
        (CFSG.Open.fischerTransvections (fun x y => -2 * b x y) fun v => b v v = 1))
      (CFSG.Open.fischerTransvections (fun x y => -2 * b x y) fun v => b v v = 1)) :
    False := by
  obtain ⟨u, hu, u', hu', h5⟩ :=
    exists_orderOf_mul_eq_five_of_fischerCentralQuotientModel_five hn hsym hnd hM
  have hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ) :=
    not_threeTransp_of_pow_ne_one hC hu hu' fun k hk0 hk3 hk => by
      have h := Nat.le_of_dvd hk0 (h5 ▸ orderOf_dvd_of_pow_eq_one hk)
      omega
  have hHns : ¬ Group.IsSolvable (Halpha D hC.alpha) := by
    intro hsol
    have htop : CFSG.solvableRadical (Halpha D hC.alpha) = ⊤ :=
      top_le_iff.mp (le_solvableRadical (N := ⊤) Subgroup.normal_top inferInstance)
    have h1 : u * u' = 1 := by
      obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (u * u')
      rw [← hy, QuotientGroup.eq_one_iff, htop]
      exact Subgroup.mem_top y
    rw [h1, orderOf_one] at h5
    exact absurd h5 (by norm_num)
  have hV : ∀ v ∈ imageClass hC, Odd (Vmem (imageClass hC) v).ncard := fun v hv => by
    rw [Vmem_eq_singleton_of_fischerCentralQuotientModel_five hn hsym hnd hM v hv,
      Set.ncard_singleton]
    exact odd_one
  obtain ⟨v, hv, w, hw, hvw, hne, h4⟩ :=
    exists_lineMem_ncard_le_four_of_fischerCentralQuotientModel_five hn hsym hnd hM
  obtain ⟨c, hcStar, -⟩ := id hv
  obtain ⟨β, hβ, -⟩ := mem_DalphaStar_iff.mp ((mem_DstarH_iff hC).mp hcStar)
  have hle := ncard_blockLine_le h89 h113 hC hrad hW hn3 hMZ hv hw hvw hne hβ
  have h3 := two_lt_encard_blockLine h89 h113 hC hrad hW hn3 hMZ hβ
  rw [← (Set.toFinite (blockLine D hC.alpha β)).cast_ncard_eq] at h3
  have h2 : 2 < (blockLine D hC.alpha β).ncard := by exact_mod_cast h3
  have hodd : Odd (blockLine D hC.alpha β).ncard := by
    have hαℓ : hC.alpha ∈ blockLine D hC.alpha β := left_mem_blockLine hC.isBlock_alpha.subset
    have hdiff := ncard_blockLine_diff_eq h113 hC hrad hn3 hHns hβ
    obtain ⟨s, hs⟩ := exists_ncard_orbit_Malpha_eq_two_pow h89 h113 hC hrad hW hn3 hHns hβ
    have hgt := one_lt_ncard_orbit_Malpha h89 h113 hC hrad hW hn3 hMZ hHns hβ
    rw [hs] at hdiff hgt
    have hs0 : s ≠ 0 := by
      rintro rfl
      exact absurd hgt (by norm_num)
    have heven : Even (blockLine D hC.alpha β \ {hC.alpha}).ncard := by
      rw [hdiff]
      exact (Nat.even_pow.mpr ⟨even_two, hs0⟩).mul_left _
    rw [Set.ncard_diff_singleton_of_mem hαℓ] at heven
    rw [← Nat.sub_add_cancel (by omega : 1 ≤ (blockLine D hC.alpha β).ncard)]
    exact heven.add_one
  have hline : (blockLine D hC.alpha β).ncard = 3 := by
    obtain ⟨m, hm⟩ := hodd
    omega
  exact ncard_blockLine_ne_three_of_orderOf_mul h89 h113 hC hrad hW hn3 hMZ hHns hV hu hu'
    (by rw [h5]; decide) (by rw [h5]; decide) (by rw [h5]; decide) hβ hline

theorem meetsSq_of_fischerCentralQuotientModel_five_imageClass (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {n : ℕ} (hn : 4 ≤ n) {b : LinearMap.BilinForm (ZMod 5) (Fin n → ZMod 5)}
    (hsym : ∀ x y, b x y = b y x) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (hM : CFSG.Open.fischerCentralQuotientModel (imageClass hC)
      (Subgroup.closure
        (CFSG.Open.fischerTransvections (fun x y => -2 * b x y) fun v => b v v = 1))
      (CFSG.Open.fischerTransvections (fun x y => -2 * b x y) fun v => b v v = 1)) :
    MeetsSq D :=
  (false_of_fischerCentralQuotientModel_five h89 h113 hC hrad hW hMZ hn hsym hnd hM).elim

end CFSG.OddTranspositions.PartFour

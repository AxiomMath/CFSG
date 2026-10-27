module

public import CFSG.RankThree.PartTwo.Sec11.Item1118StepsProofS
public import CFSG.RankThree.PartTwo.Sec11.Item116
import CFSG.RankThree.PartTwo.Sec11.Item1116NoFifteen
import CFSG.RankThree.PartTwo.Sec11.Item1119Proof
import CFSG.RankThree.PartTwo.Sec11.DataExistsAct

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

namespace Item1118StepsProof

section Group

variable {G : Type} [Group G]

theorem le_innerPreimage_self [Finite G] (Y : Subgroup G) : Y ≤ innerPreimage Y := by
  intro y hy
  refine mem_innerPreimage_iff.mpr ⟨Subgroup.le_normalizer hy, ?_⟩
  rw [thetaQuotMulAut_compAction_of_mem Y hy]
  exact ⟨_, rfl⟩

theorem mem_innerPreimage_of_commute [Finite G] {Y : Subgroup G} {z : G}
    (hz : ∀ y ∈ Y, z * y = y * z) : z ∈ innerPreimage Y := by
  have hzN : z ∈ Subgroup.normalizer (Y : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    rw [hz y hy, mul_inv_cancel_right]
    exact hy
  refine mem_innerPreimage_iff.mpr ⟨hzN, ?_⟩
  have h1 : Sec4.compAction Y ⟨z, hzN⟩ = 1 := by
    refine MulEquiv.ext fun y => Subtype.ext ?_
    change z * (y : G) * z⁻¹ = y
    rw [hz y y.2, mul_inv_cancel_right]
  rw [h1, map_one]
  exact ⟨1, map_one _⟩

end Group

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem exists_eq_of_mem_R (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g)
    (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s}) (hsa : s * a = a * s)
    {y : G} (hy : y ∈ R) : ∃ k m n : ℤ, y = a ^ k * x ^ m * s ^ n := by
  have hR := Item1116NoFifteen.R_eq_of_closure_eq h hrs
  set D := Subgroup.closure ({x, s} : Set G) with hD
  have hxD : x ∈ D := Subgroup.subset_closure (by simp)
  have hsD : s ∈ D := Subgroup.subset_closure (by simp)
  have haD : a ∈ Subgroup.normalizer (D : Set G) := by
    refine mem_normalizer_closure_of_forall ?_
    rintro z (rfl | rfl)
    · exact Subgroup.zpowers_le.mpr hxD
        (Item1119Proof.conj_mem_zpowers_of_mem_normalizer (Item1119Proof.a_mem_normalizer_x h45 h))
    · rw [← hsa, mul_inv_cancel_right]
      exact hsD
  have hyS : y ∈ Subgroup.zpowers a ⊔ D := by
    rw [hR] at hy
    refine (Subgroup.closure_le _).mpr ?_ hy
    rintro z (rfl | rfl | rfl)
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers z)
    · exact Subgroup.mem_sup_right hxD
    · exact Subgroup.mem_sup_right hsD
  obtain ⟨k, w, hw, rfl⟩ := Item1119Proof.exists_zpow_mul_of_mem_sup haD hyS
  obtain ⟨m, n, rfl⟩ := Sec12.exists_zpow_mul_zpow_of_mem_closure_pair h.commute_s_x.symm hw
  exact ⟨k, m, n, by group⟩

theorem exists_eq_of_mem_centralizer (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g)
    (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s}) (hsa : s * a = a * s)
    {y : G} (hy : y ∈ R) (hya : y * a = a * y) : ∃ k m n : ℤ, y = a ^ k * x ^ (3 * m) * s ^ n := by
  obtain ⟨k, m, n, rfl⟩ := exists_eq_of_mem_R h45 h hrs hsa hy
  obtain ⟨hxa, hxa1⟩ := Item1119Proof.commutator_x_a_facts h45 h
  obtain ⟨δ, hδ⟩ := Subgroup.mem_zpowers_iff.mp hxa
  obtain ⟨hdA, -, hd3⟩ := Item1115Proof.d_mem h
  obtain ⟨-, hxR, -⟩ := Item1116Proof.mem_R h
  have hxP := Item1119Proof.R_le_P R g hxR
  have hxd : x * d = d * x := Item1119Proof.commute_d h113 h117 h hxP
  have hxa' : x * a * x⁻¹ = d ^ δ * a := by rw [hδ]; group
  have hconj : x ^ m * a * (x ^ m)⁻¹ = (d ^ δ) ^ m * a :=
    Item1119Proof.zpow_conj_eq_zpow_mul ((Commute.zpow_right hxd δ).eq) hxa' m
  have hsa' : Commute s a := hsa
  have hxma : x ^ m * a = a * x ^ m := by
    have e1 : a ^ k * x ^ m * s ^ n * a = a ^ k * (x ^ m * a) * s ^ n := by
      rw [mul_assoc (a ^ k * x ^ m), (hsa'.zpow_left n).eq]
      group
    have e2 : a * (a ^ k * x ^ m * s ^ n) = a ^ k * (a * x ^ m) * s ^ n := by
      rw [← mul_assoc, ← mul_assoc, (Commute.self_zpow a k).eq]
      group
    rw [e1, e2] at hya
    exact mul_left_cancel (mul_right_cancel hya)
  have hd1 : (d ^ δ) ^ m = 1 := by
    have : x ^ m * a * (x ^ m)⁻¹ = a := by rw [hxma, mul_inv_cancel_right]
    rw [hconj] at this
    exact mul_right_cancel (this.trans (one_mul a).symm)
  rw [← zpow_mul] at hd1
  have hdo : orderOf d = 3 := (Item1115Proof.orderOf_c_d h).2
  have h3 : (3 : ℤ) ∣ δ * m := by
    have := orderOf_dvd_iff_zpow_eq_one.mpr hd1
    rw [hdo] at this
    exact_mod_cast this
  have hδ3 : ¬ (3 : ℤ) ∣ δ := by
    intro h3
    apply hxa1
    rw [← hδ, ActOnA.zpow_eq_one_of_dvd hd3 h3]
  have hm3 : (3 : ℤ) ∣ m :=
    (Int.prime_three.dvd_or_dvd h3).resolve_left hδ3
  obtain ⟨m', rfl⟩ := hm3
  exact ⟨k, m', n, rfl⟩

theorem commutator_le_closure_xs (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g)
    (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s}) (hsa : s * a = a * s)
    (hxg : x * g * x⁻¹ * g⁻¹ ∈ Subgroup.closure {x, s})
    (hsg : s * g * s⁻¹ * g⁻¹ ∈ Subgroup.closure {x, s}) :
    ⁅sec11P R g, sec11P R g⁆ ≤ Subgroup.closure {x, s} := by
  set D := Subgroup.closure ({x, s} : Set G) with hD
  have hxD : x ∈ D := Subgroup.subset_closure (by simp)
  have hsD : s ∈ D := Subgroup.subset_closure (by simp)
  have hxs : s * x = x * s := h.commute_s_x
  have hag : a * g = g * a := (Subgroup.mem_centralizer_singleton_iff.mp
    (Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt_Y h.g_mem.1)).symm
  have hxaD : x * a * x⁻¹ * a⁻¹ ∈ D :=
    Subgroup.zpowers_le.mpr (Subgroup.zpowers_le.mpr hxD (Item1115Proof.d_mem_zpowers_x h))
      (Item1119Proof.commutator_x_a_facts h45 h).1
  have haN : a ∈ Subgroup.normalizer (D : Set G) := by
    refine mem_normalizer_closure_of_forall ?_
    rintro z (rfl | rfl)
    · exact Subgroup.zpowers_le.mpr hxD
        (Item1119Proof.conj_mem_zpowers_of_mem_normalizer (Item1119Proof.a_mem_normalizer_x h45 h))
    · rw [← hsa, mul_inv_cancel_right]
      exact hsD
  have hxN : x ∈ Subgroup.normalizer (D : Set G) := Subgroup.le_normalizer hxD
  have hsN : s ∈ Subgroup.normalizer (D : Set G) := Subgroup.le_normalizer hsD
  have hgN : g ∈ Subgroup.normalizer (D : Set G) := by
    refine mem_normalizer_closure_of_forall ?_
    rintro z (rfl | rfl)
    · have e : g * z * g⁻¹ = (z * g * z⁻¹ * g⁻¹)⁻¹ * z := by group
      rw [e]
      exact D.mul_mem (D.inv_mem hxg) hxD
    · have e : g * z * g⁻¹ = (z * g * z⁻¹ * g⁻¹)⁻¹ * z := by group
      rw [e]
      exact D.mul_mem (D.inv_mem hsg) hsD
  have hR := Item1116NoFifteen.R_eq_of_closure_eq h hrs
  have hPS : sec11P R g = Subgroup.closure ({a, x, s, g} : Set G) := by
    apply le_antisymm
    · refine sup_le ?_ ?_
      · rw [hR, Subgroup.closure_le]
        rintro y (rfl | rfl | rfl) <;> exact Subgroup.subset_closure (by simp)
      · rw [Subgroup.zpowers_le]
        exact Subgroup.subset_closure (by simp)
    · rw [Subgroup.closure_le]
      have hmem : ∀ y ∈ ({a, x, s} : Set G), y ∈ sec11P R g := fun y hy =>
        Item1119Proof.R_le_P R g (by rw [hR]; exact Subgroup.subset_closure hy)
      have hgP := Item1119Proof.g_mem_P R g
      rintro y (rfl | rfl | rfl | rfl)
      · exact hmem _ (by simp)
      · exact hmem _ (by simp)
      · exact hmem _ (by simp)
      · exact hgP
  rw [hPS]
  refine commutator_closure_le ?_ ?_
  · rw [Subgroup.closure_le]
    rintro y (rfl | rfl | rfl | rfl)
    exacts [haN, hxN, hsN, hgN]
  · have hone : ∀ u v : G, u * v = v * u → ⁅u, v⁆ ∈ D := fun u v huv => by
      rw [commutatorElement_def, huv, mul_inv_cancel_right, mul_inv_cancel]
      exact D.one_mem
    have hinv : ∀ u v : G, ⁅u, v⁆ ∈ D → ⁅v, u⁆ ∈ D := fun u v huv => by
      rw [← commutatorElement_inv]
      exact D.inv_mem huv
    have hax' : ⁅x, a⁆ ∈ D := by rw [commutatorElement_def]; exact hxaD
    have hxg' : ⁅x, g⁆ ∈ D := by rw [commutatorElement_def]; exact hxg
    have hsg' : ⁅s, g⁆ ∈ D := by rw [commutatorElement_def]; exact hsg
    have hxs' : x * s = s * x := hxs.symm
    have hsa'' : a * s = s * a := hsa.symm
    have hga : g * a = a * g := hag.symm
    rintro u (rfl | rfl | rfl | rfl) v (rfl | rfl | rfl | rfl)
    exacts [hone _ _ rfl, hinv _ _ hax', hone _ _ hsa'', hone _ _ hag,
      hax', hone _ _ rfl, hone _ _ hxs', hxg',
      hone _ _ hsa, hone _ _ hxs, hone _ _ rfl, hsg',
      hone _ _ hga, hinv _ _ hxg', hinv _ _ hsg', hone _ _ rfl]

end Item1118StepsProof

end CFSG.RankThree.PartTwo.Sec11

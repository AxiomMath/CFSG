module

public import CFSG.LocalAnalysis.StandardType.GGTPDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepBlockLift
public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatTypeDet
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LocalAnalysis.SectionRank.BruhatLift
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
public import CFSG.LocalAnalysis.SectionRank.LargeReeCover
public import CFSG.Sporadic.Schreier.TitsOther

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTPJData_of_layer {L' R : Type} [Group L'] [Finite L'] [Group R] (ψ : L' →* R)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center L')) {c : MulAut L'}
    (hc : ∃ φ : MulAut R, ∀ l, φ (ψ l) = ψ (c l)) {ER : Subgroup R}
    (hER : GGLayerOf (ggRFix ψ {c}) ER) {X : Type} [Group X] (e : ER ≃* X)
    (hX : Subgroup.center X = ⊥) (h3 : 3 ∣ Nat.card X) {J : Subgroup L'}
    (hJ : IsComponentOf J (ggFix c)) :
    Nonempty (J ⧸ Subgroup.center J ≃* X) ∧ ¬ 3 ∣ Nat.card (Subgroup.center J) ∧
      3 ∣ Nat.card J := by
  have hF : ∀ f ∈ ({c} : Set (MulAut L')), ∃ φ : MulAut R, ∀ l, φ (ψ l) = ψ (f l) := by
    intro f hf
    rw [Set.mem_singleton_iff] at hf
    subst hf
    exact hc
  have hC : ∀ l, l ∈ ggFix c ↔ ∀ f ∈ ({c} : Set (MulAut L')), f l = l := by
    intro l
    rw [mem_ggFix]
    constructor
    · intro h f hf
      rw [Set.mem_singleton_iff] at hf
      subst hf
      exact h
    · intro h
      exact h c (Set.mem_singleton c)
  obtain ⟨E, hEcomp, huniq, hmax, hmap⟩ :=
    ggLayerOf_lift ψ hψ hker ({c} : Set (MulAut L')) hF (ggFix c) hC hER
  have hJE : J = E := huniq J hJ
  have hmapJ : J.map ψ = ER := by rw [hJE, hmap]
  have hmem : ∀ j : J, ψ (j : L') ∈ ER := fun j => by
    rw [← hmapJ]
    exact Subgroup.mem_map.mpr ⟨(j : L'), j.2, rfl⟩
  let φJ : J →* ER :=
    { toFun := fun j => ⟨ψ (j : L'), hmem j⟩
      map_one' := Subtype.ext (map_one ψ)
      map_mul' := fun x y => Subtype.ext (map_mul ψ (x : L') (y : L')) }
  have φJ_apply : ∀ j : J, (φJ j : R) = ψ (j : L') := fun j => rfl
  have hφJsurj : Function.Surjective φJ := by
    intro r
    obtain ⟨j, hj, hjr⟩ := Subgroup.mem_map.mp (by rw [hmapJ]; exact r.2)
    exact ⟨⟨j, hj⟩, Subtype.ext hjr⟩
  have hcenterER : Subgroup.center ER = ⊥ := by
    apply le_antisymm
    · intro z hz
      rw [Subgroup.mem_bot]
      have hz' : (e z : X) ∈ Subgroup.center X := by
        rw [Subgroup.mem_center_iff]
        intro x
        obtain ⟨w, rfl⟩ := e.surjective x
        rw [← map_mul, ← map_mul]
        exact congrArg e (Subgroup.mem_center_iff.mp hz w)
      rw [hX] at hz'
      have h1 : e z = 1 := by simpa using hz'
      exact e.injective (by rw [h1, map_one])
    · exact bot_le
  have hker_center : φJ.ker = Subgroup.center J := by
    ext j
    constructor
    · intro hj
      rw [Subgroup.mem_center_iff]
      intro k
      have h1 : ψ (j : L') = 1 := by
        rw [← φJ_apply j]
        exact congrArg Subtype.val (MonoidHom.mem_ker.mp hj)
      have hz : (j : L') ∈ Subgroup.center L' := hker (MonoidHom.mem_ker.mpr h1)
      apply Subtype.ext
      simpa using Subgroup.mem_center_iff.mp hz (k : L')
    · intro hj
      apply MonoidHom.mem_ker.mpr
      have hzER : φJ j ∈ Subgroup.center ER := by
        rw [Subgroup.mem_center_iff]
        intro r
        obtain ⟨k, rfl⟩ := hφJsurj r
        rw [← map_mul, ← map_mul]
        exact congrArg φJ (Subgroup.mem_center_iff.mp hj k)
      have hbot : φJ j ∈ (⊥ : Subgroup ER) := hcenterER ▸ hzER
      simpa using hbot
  have hZJ : (Subgroup.center J).map J.subtype ≤ Subgroup.center L' := by
    rintro x ⟨j, hj, rfl⟩
    have hj' : j ∈ φJ.ker := hker_center.symm ▸ hj
    have h1 : ψ (j : L') = 1 := by
      rw [← φJ_apply j]
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp hj')
    exact hker (MonoidHom.mem_ker.mpr h1)
  have hcardZ : Nat.card (Subgroup.center J) ∣ Nat.card (Subgroup.center L') := by
    have hmap' : Nat.card ((Subgroup.center J).map J.subtype) =
        Nat.card (Subgroup.center J) :=
      Subgroup.card_map_of_injective (f := J.subtype) (Subgroup.subtype_injective J)
    rw [← hmap']
    exact Subgroup.card_dvd_of_le hZJ
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨(QuotientGroup.quotientMulEquivOfEq hker_center).symm.trans
      ((QuotientGroup.quotientKerEquivOfSurjective φJ hφJsurj).trans e)⟩
  · intro h3J
    exact hZ (h3J.trans hcardZ)
  · have hcardERJ : Nat.card ER ∣ Nat.card J :=
      Subgroup.card_dvd_of_surjective (f := φJ) hφJsurj
    have hcardXER : Nat.card X = Nat.card ER := Nat.card_congr e.symm.toEquiv
    exact (hcardXER ▸ h3).trans hcardERJ

private theorem ggTP_three_dvd_ordA_five {q : ℕ} (h2q : 2 ∣ q) (h3q : 3 ∣ q - 1) :
    3 ∣ CFSG.Open.ordA 5 q := by
  rw [CFSG.Open.ordA]
  have h9 : 9 ∣ ∏ i ∈ Finset.Icc 2 (5 + 1), (q ^ i - 1) := by
    have hsub : ({2, 3} : Finset ℕ) ⊆ Finset.Icc 2 (5 + 1) := by decide
    have hprod : (q ^ 2 - 1) * (q ^ 3 - 1) ∣
        ∏ i ∈ Finset.Icc 2 (5 + 1), (q ^ i - 1) := by
      have h := Finset.prod_dvd_prod_of_subset ({2, 3} : Finset ℕ) (Finset.Icc 2 (5 + 1))
        (fun i => q ^ i - 1) hsub
      rw [Finset.prod_pair (by norm_num : (2 : ℕ) ≠ 3)] at h
      exact h
    have hbase : (q - 1) * (q - 1) ∣ (q ^ 2 - 1) * (q ^ 3 - 1) :=
      Nat.mul_dvd_mul (Nat.sub_one_dvd_pow_sub_one q 2) (Nat.sub_one_dvd_pow_sub_one q 3)
    have h9base : 9 ∣ (q - 1) * (q - 1) := by
      simpa [pow_two] using pow_dvd_pow_of_dvd h3q 2
    exact h9base.trans (hbase.trans hprod)
  have h2pow : 2 ∣ q ^ (5 * (5 + 1) / 2) :=
    h2q.trans (dvd_pow_self q (by norm_num))
  have h2 : 2 ∣ q ^ (5 * (5 + 1) / 2) * (∏ i ∈ Finset.Icc 2 (5 + 1), (q ^ i - 1)) :=
    dvd_mul_of_dvd_left h2pow _
  have h9' : 9 ∣ q ^ (5 * (5 + 1) / 2) * (∏ i ∈ Finset.Icc 2 (5 + 1), (q ^ i - 1)) :=
    dvd_mul_of_dvd_right h9 _
  have h18 : 18 ∣ q ^ (5 * (5 + 1) / 2) * (∏ i ∈ Finset.Icc 2 (5 + 1), (q ^ i - 1)) := by
    have h := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 2 9) h2 h9'
    simpa using h
  have hdiv : Nat.gcd (5 + 1) (q - 1) * 3 ∣ 18 := by
    have h := Nat.mul_dvd_mul (Nat.gcd_dvd_left (5 + 1) (q - 1)) (dvd_refl 3)
    simpa using h
  exact Nat.dvd_div_of_mul_dvd (hdiv.trans h18)

private theorem ggTP_three_dvd_ordTwistedA_five {q : ℕ} (h2q : 2 ∣ q) (h3q : 3 ∣ q + 1) :
    3 ∣ CFSG.Open.ordTwistedA 5 q := by
  rw [CFSG.Open.ordTwistedA]
  have hq1 : 1 ≤ q := by
    rcases h3q with ⟨k, hk⟩
    omega
  have h9 : 9 ∣ ∏ i ∈ Finset.Icc 2 (5 + 1), ((q : ℤ) ^ i - (-1) ^ i).toNat := by
    have hsub : ({2, 4} : Finset ℕ) ⊆ Finset.Icc 2 (5 + 1) := by decide
    have hprod : (q ^ 2 - 1) * (q ^ 4 - 1) ∣
        ∏ i ∈ Finset.Icc 2 (5 + 1), ((q : ℤ) ^ i - (-1) ^ i).toNat := by
      have h := Finset.prod_dvd_prod_of_subset ({2, 4} : Finset ℕ) (Finset.Icc 2 (5 + 1))
        (fun i => ((q : ℤ) ^ i - (-1) ^ i).toNat) hsub
      rw [Finset.prod_pair (by norm_num : (2 : ℕ) ≠ 4)] at h
      rw [CFSG.Timmesfeld.Orders.toNat_pow_sub_neg_one_pow_of_even (q := q) (i := 2)
            hq1 (by decide),
          CFSG.Timmesfeld.Orders.toNat_pow_sub_neg_one_pow_of_even (q := q) (i := 4)
            hq1 (by decide)] at h
      exact h
    have h1 : q + 1 ∣ q ^ 2 - 1 := ⟨q - 1, by simpa using (Nat.sq_sub_sq q 1)⟩
    have h4 : q + 1 ∣ q ^ 4 - 1 := by
      have h : q ^ 2 - 1 ∣ (q ^ 2) ^ 2 - 1 := Nat.sub_one_dvd_pow_sub_one (q ^ 2) 2
      rw [show (q ^ 2) ^ 2 = q ^ 4 by rw [← pow_mul]] at h
      exact h1.trans h
    have hbase : (q + 1) * (q + 1) ∣ (q ^ 2 - 1) * (q ^ 4 - 1) :=
      Nat.mul_dvd_mul h1 h4
    have h9base : 9 ∣ (q + 1) * (q + 1) := by
      simpa [pow_two] using pow_dvd_pow_of_dvd h3q 2
    exact h9base.trans (hbase.trans hprod)
  have h2pow : 2 ∣ q ^ (5 * (5 + 1) / 2) :=
    h2q.trans (dvd_pow_self q (by norm_num))
  have h2 : 2 ∣ q ^ (5 * (5 + 1) / 2) *
      (∏ i ∈ Finset.Icc 2 (5 + 1), ((q : ℤ) ^ i - (-1) ^ i).toNat) :=
    dvd_mul_of_dvd_left h2pow _
  have h9' : 9 ∣ q ^ (5 * (5 + 1) / 2) *
      (∏ i ∈ Finset.Icc 2 (5 + 1), ((q : ℤ) ^ i - (-1) ^ i).toNat) :=
    dvd_mul_of_dvd_right h9 _
  have h18 : 18 ∣ q ^ (5 * (5 + 1) / 2) *
      (∏ i ∈ Finset.Icc 2 (5 + 1), ((q : ℤ) ^ i - (-1) ^ i).toNat) := by
    have h := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 2 9) h2 h9'
    simpa using h
  have hdiv : Nat.gcd (5 + 1) (q + 1) * 3 ∣ 18 := by
    have h := Nat.mul_dvd_mul (Nat.gcd_dvd_left (5 + 1) (q + 1)) (dvd_refl 3)
    simpa using h
  exact Nat.dvd_div_of_mul_dvd (hdiv.trans h18)

theorem ggTP_three_dvd_card_PSL6 {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n)
    (h3 : 3 ∣ 2 ^ n - 1) (hX : CFSG.Open.StatedClassicalModel X .PSL 6 2 n) : 3 ∣ Nat.card X := by
  have hmem : (.PSL) ∈ CFSG.Blueprint.classicalTags := by decide
  have hlm : CFSG.Blueprint.LieModel X .PSL 6 2 n := Or.inl ⟨hmem, hX⟩
  rw [CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder_of_mem_classicalTags hmem hlm]
  show 3 ∣ CFSG.Open.ordA 5 (2 ^ n)
  exact ggTP_three_dvd_ordA_five (dvd_pow_self 2 (by omega)) h3

theorem ggTP_three_dvd_card_PSU6 {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n)
    (h3 : 3 ∣ 2 ^ n + 1) (hX : CFSG.Open.StatedClassicalModel X .PSU 6 2 n) : 3 ∣ Nat.card X := by
  have hmem : (.PSU) ∈ CFSG.Blueprint.classicalTags := by decide
  have hlm : CFSG.Blueprint.LieModel X .PSU 6 2 n := Or.inl ⟨hmem, hX⟩
  rw [CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder_of_mem_classicalTags hmem hlm]
  show 3 ∣ CFSG.Open.ordTwistedA 5 (2 ^ n)
  exact ggTP_three_dvd_ordTwistedA_five (dvd_pow_self 2 (by omega)) h3

end CFSG.StandardType

end

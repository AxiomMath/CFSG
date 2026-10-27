module

public import CFSG.Permutation.FiveTransitive.SixteenOrbitLocalization
public import CFSG.Permutation.FiveTransitive.InvolutiveNormalizerExtension
public import CFSG.Permutation.FiveTransitive.SixteenCosetOrderFour

public section

namespace CFSG

namespace FiveTransitive.SixteenExtensionLocalization

open MulAction Equiv

variable {G X : Type*} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]

theorem fixed_subset_union
    (hlocal : SixLocalSylowExponentTwo.EvenSixLocal G X)
    (hinv : ∀ u : G, orderOf u = 2 →
      Nat.card (Function.fixedPoints (toPerm u : Perm X)) ≤ 6)
    (S : Subgroup G) (hcomm : ∀ s t : S, s * t = t * s) (h2 : ∀ s : S, s * s = 1)
    (hcard : Nat.card S = 16) (hF : (fixedPoints S X).ncard = 6)
    (b : G) (hb : b ∈ Subgroup.normalizer (S : Set G)) (hbOrder : orderOf b = 2)
    (hfree : ∀ (s : S) (x : X), x ∉ fixedPoints S X → s • x = x → s = 1)
    (hsix : (fixedBy X b).ncard = 6)
    (htwo : (fixedBy X b ∩ fixedPoints S X).ncard = 2)
    (x : X) (hbx : b • x = x) (hx : x ∉ fixedPoints S X)
    (q : G) (hq : q ∈ S ⊔ Subgroup.zpowers b) (hq1 : q ≠ 1) :
    fixedBy X q ⊆ fixedPoints S X ∪ orbit S x := by
  have hb2 : b * b = 1 := by rw [← pow_two, ← hbOrder, pow_orderOf_eq_one]
  intro y hy
  by_cases hyF : y ∈ fixedPoints S X
  · exact Or.inl hyF
  apply Or.inr
  rcases InvolutiveNormalizerExtension.sup_cases S b hb hbOrder hq with hqS | hqS
  · have h := hfree ⟨q,hqS⟩ y hyF hy
    exact (hq1 (congrArg Subtype.val h)).elim
  · by_cases hq2 : q * q = 1
    · exact SixteenOrbitLocalization.coset_involution_fixed_subset_orbit S hcomm h2 hcard
        b hb hb2 hfree hsix htwo x hbx hx q hq2 hqS ⟨hy,hyF⟩
    · have hp := InvolutiveNormalizerExtension.fourth_power_eq_one S h2 b hb hbOrder hq
      have hd : orderOf q ∣ 4 := orderOf_dvd_of_pow_eq_one hp
      have hle : orderOf q ≤ 4 := Nat.le_of_dvd (by decide) hd
      have ho0 : 0 < orderOf q := orderOf_pos q
      have ho1 : orderOf q ≠ 1 := fun h => hq1 (orderOf_eq_one_iff.mp h)
      have ho2 : orderOf q ≠ 2 := by
        intro h
        apply hq2
        rw [← pow_two, ← h, pow_orderOf_eq_one]
      have ho3 : orderOf q ≠ 3 := by intro h; norm_num [h] at hd
      have ho : orderOf q = 4 := by omega
      exact (hyF (SixteenCosetOrderFour.fixed_subset_common hlocal hinv S hF b hb hb2
        htwo q ho hqS hy)).elim

omit [Fintype X] [FaithfulSMul G X] in
theorem extension_orbit_eq (S : Subgroup G) (b : G)
    (hb : b ∈ Subgroup.normalizer (S : Set G)) (hbOrder : orderOf b = 2)
    (x : X) (hbx : b • x = x) :
    orbit (S ⊔ Subgroup.zpowers b : Subgroup G) x = orbit S x := by
  ext y
  constructor
  · intro hy
    obtain ⟨q,hq⟩ := mem_orbit_iff.mp hy
    rcases InvolutiveNormalizerExtension.sup_cases S b hb hbOrder q.property with hs | hs
    · exact mem_orbit_iff.mpr ⟨⟨q.val,hs⟩,hq⟩
    · apply mem_orbit_iff.mpr
      refine ⟨⟨q.val * b⁻¹,hs⟩, ?_⟩
      change (q.val * b⁻¹) • x = y
      have hbinvx : b⁻¹ • x = x := by
        calc
          b⁻¹ • x = b⁻¹ • (b • x) := congrArg (fun z : X => b⁻¹ • z) hbx.symm
          _ = x := inv_smul_smul b x
      rw [mul_smul,hbinvx]
      exact hq
  · intro hy
    obtain ⟨s,hs⟩ := mem_orbit_iff.mp hy
    exact mem_orbit_iff.mpr ⟨⟨s.val,(show S ≤ S ⊔ Subgroup.zpowers b from le_sup_left) s.property⟩,hs⟩

omit [Finite G] [Fintype X] [FaithfulSMul G X] in
theorem not_mem_common_fixer (S : Subgroup G) (hF : (fixedPoints S X).ncard = 6)
    (b : G) (htwo : (fixedBy X b ∩ fixedPoints S X).ncard = 2) : b ∉ S := by
  intro hb
  have hsub : fixedPoints S X ⊆ fixedBy X b := fun _ hx => mem_fixedPoints.mp hx ⟨b,hb⟩
  have he : fixedBy X b ∩ fixedPoints S X = fixedPoints S X := Set.inter_eq_right.mpr hsub
  rw [he,hF] at htwo
  omega

end FiveTransitive.SixteenExtensionLocalization

end CFSG

module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23Six5C
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23Six5Aut2b

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Six5Data

variable {T M V : Subgroup G} {hV : IsElemAbelian 2 V} (d : Six5Data T M V hV)
include d

theorem a₂_mem_autI_K : d.S.a₂ ∈ autI hV (M ⊓ g1_1516 d.Z₁) := by
  obtain ⟨⟨m, hmN⟩, hmM, hm⟩ := (mem_autI hV).1 (d.hA₂ d.S.a₂_mem)
  refine (mem_autI hV).2 ⟨⟨m, hmN⟩, ⟨hmM, ?_⟩, hm⟩
  refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
  obtain ⟨w, hw, rfl⟩ := (d.mem_V₁_iff).1 (d.Z₁_le_V₁ hz)
  have h1 := conj_val hmN w
  have h2 : convI hV ⟨m, hmN⟩ w = w := by rw [hm]; exact d.S.a₂_fix_W₁ hw
  rw [h2] at h1
  calc IntMod.val w * m = (m * IntMod.val w * m⁻¹) * m := by rw [h1]
    _ = m * IntMod.val w := by group

theorem odd_mem_autI_K
    (hNoE9 : ¬ ∃ E : Subgroup (MulAut ↥V), E ≤ autOn M V ∧ IsElemAbelian 3 E ∧ Nat.card E = 9)
    {y : MulAut (IntMod V hV)} {m : G} (hmK : m ∈ M ⊓ g1_1516 d.Z₁)
    (hmN : m ∈ Subgroup.normalizer (V : Set G)) (hy : convI hV ⟨m, hmN⟩ = y)
    (hodd : Odd (orderOf y)) : y ∈ Subgroup.zpowers d.S.a₂ := by
  obtain ⟨z₀, hz₀, hz₀1⟩ : ∃ z ∈ d.Z₁, z ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact d.Z₁_ne_bot ((Subgroup.eq_bot_iff_forall _).2 hcon)
  obtain ⟨w₀, hw₀, rfl⟩ := (d.mem_V₁_iff).1 (d.Z₁_le_V₁ hz₀)
  have hmC : m ∈ M ⊓ Subgroup.centralizer (d.Z₁ : Set G) := hmK
  have hstab : d.S.Stab₁ y := by
    rw [← hy]
    exact stab_of_mem_normalizer_map hmN (d.centralizer_le_normalizer hmC)
  have hfix : y w₀ = w₀ := by
    apply IntMod.val_injective
    rw [← hy, ← conj_val hmN]
    have := Subgroup.mem_centralizer_iff.mp hmK.2 _ hz₀
    calc m * IntMod.val w₀ * m⁻¹ = IntMod.val w₀ * m * m⁻¹ := by rw [← this]
      _ = IntMod.val w₀ := by group
  have hw₀1 : w₀ ≠ 1 := fun h => hz₀1 (by rw [h]; rfl)
  have hA : d.S.A₁ ⊔ d.S.A₂ ≤ autI hV M := by
    rw [d.hsup]
    exact Jhat_le _
  have hyM : y ∈ autI hV M := by
    rw [← hy]
    exact convI_mem_autI hV hmK.1 hmN
  exact d.S.odd_mem_zpowers_a₂ (fun w => IntMod.sq_eq_one w) d.hcard hA d.hnorm
    (autI_mono hV d.hTM d.hτ) (fun ⟨E, h1, h2, h3⟩ => hNoE9 ⟨E, h1, h2, h3⟩) hyM hstab hw₀
    hw₀1 hfix hodd

theorem prime_o2
    (hNoE9 : ¬ ∃ E : Subgroup (MulAut ↥V), E ≤ autOn M V ∧ IsElemAbelian 3 E ∧ Nat.card E = 9) :
    (Nat.card (oTwoUpper (autOn (M ⊓ g1_1516 d.Z₁) V))).Prime := by
  have h5 : orderOf d.S.a₂ = 5 := d.S.orderOf_a₂_five
  have hle : oTwoUpper (autI hV (M ⊓ g1_1516 d.Z₁)) ≤ Subgroup.zpowers d.S.a₂ := by
    refine oTwoUpper_le_of_pow_mem fun x hx => ?_
    obtain ⟨k, n', hn', hn'eq⟩ := Nat.exists_eq_two_pow_mul_odd (n := orderOf x)
      (orderOf_pos x).ne'
    refine ⟨k, ?_⟩
    obtain ⟨⟨m, hmN⟩, hmK, rfl⟩ := (mem_autI hV).1 hx
    have hmN' : m ^ 2 ^ k ∈ Subgroup.normalizer (V : Set G) := Subgroup.pow_mem _ hmN _
    have hpow : (convI hV ⟨m, hmN⟩) ^ 2 ^ k = convI hV ⟨m ^ 2 ^ k, hmN'⟩ := by
      rw [← map_pow]
      rfl
    have hordd : Odd (orderOf (convI hV ⟨m, hmN⟩ ^ 2 ^ k)) := by
      rw [orderOf_pow_of_dvd (by positivity) (by rw [hn'eq]; exact dvd_mul_right _ _), hn'eq,
        Nat.mul_div_cancel_left _ (by positivity)]
      exact hn'
    exact d.odd_mem_autI_K hNoE9 (m := m ^ 2 ^ k) (Subgroup.pow_mem _ hmK _) hmN' hpow.symm hordd
  have heq : oTwoUpper (autI hV (M ⊓ g1_1516 d.Z₁)) = Subgroup.zpowers d.S.a₂ := by
    refine le_antisymm hle (Subgroup.zpowers_le.2 ?_)
    exact mem_oTwoUpper_of_odd d.a₂_mem_autI_K (by rw [h5]; decide)
  change (Nat.card (oTwoUpper (autI hV (M ⊓ g1_1516 d.Z₁)))).Prime
  rw [heq, Nat.card_zpowers, h5]
  norm_num

theorem v2_comm {Y' : Subgroup G} (hY : Y' ≤ M ⊓ g1_1516 d.Z₁) (h5 : IsPGroup 5 Y')
    (hY2 : ⁅d.V₂, Y'⁆ = d.V₂) : ⁅d.V₂, oTwoUpper (M ⊓ g1_1516 d.Z₁)⁆ = d.V₂ := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro v hv x hx
    have hxK : x ∈ M ⊓ g1_1516 d.Z₁ := oTwoUpper_le _ hx
    have hxN1 := d.centralizer_le_normalizer ⟨hxK.1, hxK.2⟩
    have hxN2 := d.mem_normalizer_V₂ hxK.1 hxN1
    have h1 : x * v⁻¹ * x⁻¹ ∈ d.V₂ :=
      (Subgroup.mem_normalizer_iff.mp hxN2 v⁻¹).1 (d.V₂.inv_mem hv)
    have : ⁅v, x⁆ = v * (x * v⁻¹ * x⁻¹) := by
      simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact d.V₂.mul_mem hv h1
  · have hYO : Y' ≤ oTwoUpper (M ⊓ g1_1516 d.Z₁) := by
      intro y hy
      obtain ⟨k, hk⟩ := h5 ⟨y, hy⟩
      have hord : orderOf y ∣ 5 ^ k := by
        apply orderOf_dvd_of_pow_eq_one
        simpa using congrArg Subtype.val hk
      refine mem_oTwoUpper_of_odd (hY hy) ?_
      exact Odd.of_dvd_nat (Odd.pow (by decide)) hord
    calc d.V₂ = ⁅d.V₂, Y'⁆ := hY2.symm
      _ ≤ ⁅d.V₂, oTwoUpper (M ⊓ g1_1516 d.Z₁)⁆ := Subgroup.commutator_mono le_rfl hYO

end Six5Data

end CFSG.Quasithin

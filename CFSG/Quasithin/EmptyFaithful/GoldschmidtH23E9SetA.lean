module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23Six5E
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23Six5D1Aux

public section

namespace CFSG.Quasithin.E9

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Gen

variable {T M V : Subgroup G} {hV : IsElemAbelian 2 V} (d : Six5Data T M V hV)
include d

theorem centralizer_le_normalizer {Z : Subgroup G} (hZ : Z ≤ d.V₁) (hZne : Z ≠ ⊥) {m : G}
    (hm : m ∈ M ⊓ Subgroup.centralizer (Z : Set G)) :
    m ∈ Subgroup.normalizer (d.V₁ : Set G) := by
  by_contra hn
  obtain ⟨hs1, -⟩ := d.swap_of_not_mem_normalizer hm.1 hn
  obtain ⟨z, hzZ, hz1⟩ : ∃ z ∈ Z, z ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hZne ((Subgroup.eq_bot_iff_forall _).2 hcon)
  have hc : m * z * m⁻¹ = z := by
    have := Subgroup.mem_centralizer_iff.mp hm.2 z hzZ
    calc m * z * m⁻¹ = z * m * m⁻¹ := by rw [← this]
      _ = z := by group
  have h2 : z ∈ d.V₁ ⊓ d.V₂ := ⟨hZ hzZ, hc ▸ hs1 z (hZ hzZ)⟩
  rw [d.V₁_inf_V₂, Subgroup.mem_bot] at h2
  exact hz1 h2

theorem centralizer_le_normalizer₂ {Z : Subgroup G} (hZ : Z ≤ d.V₁) (hZne : Z ≠ ⊥) {m : G}
    (hm : m ∈ M ⊓ Subgroup.centralizer (Z : Set G)) :
    m ∈ Subgroup.normalizer (d.V₂ : Set G) :=
  d.mem_normalizer_V₂ hm.1 (centralizer_le_normalizer d hZ hZne hm)

theorem mem_centralizer_V₁ {y : G} (hyN : y ∈ Subgroup.normalizer (V : Set G))
    (h : convI hV ⟨y, hyN⟩ ∈ Subgroup.zpowers d.S.a₂) :
    y ∈ Subgroup.centralizer (d.V₁ : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  obtain ⟨w, hw, rfl⟩ := (d.mem_V₁_iff).1 hv
  have h1 := d.zpowers_a₂_fix_W₁ h hw
  have h2 := conj_val hyN w
  rw [h1] at h2
  calc IntMod.val w * y = (y * IntMod.val w * y⁻¹) * y := by rw [h2]
    _ = y * IntMod.val w := by group

theorem le_g1_of_autI {Y Z : Subgroup G} (hYM : Y ≤ M) (hZ : Z ≤ d.V₁)
    (hYa : autI hV Y = Subgroup.zpowers d.S.a₂) : Y ≤ M ⊓ g1_1516 Z := by
  intro y hy
  refine ⟨hYM hy, ?_⟩
  have hyN : y ∈ Subgroup.normalizer (V : Set G) := d.hMN (hYM hy)
  have h : convI hV ⟨y, hyN⟩ ∈ Subgroup.zpowers d.S.a₂ := hYa ▸ convI_mem_autI hV hy hyN
  exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hZ) (mem_centralizer_V₁ d hyN h)

theorem caseI {Mc : Subgroup G} (hq : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M)
    (hVeq : V = V154 T Mc M) (h15 : Lemma1515Concl T Mc M) (h19 : Lemma1519Concl T Mc M)
    {Z Y' : Subgroup G} (hY : Y' ≤ M ⊓ g1_1516 Z)
    (hYa : autI hV Y' = Subgroup.zpowers d.S.a₂) : ¬ (M ⊓ g1_1516 Z) ≤ Mc := by
  intro hle
  have hYle : Y' ≤ M ⊓ Mc := fun y hy => ⟨(hY hy).1, hle (hY hy)⟩
  have hA0 : d.S.A₁ ⊔ d.S.A₂ ≤ autI hV (M ⊓ Mc) := d.A₀_le_autI hq.t_le_mc hYle hYa
  subst hVeq
  have hmB : mBar0 T Mc M = d.S.A₁ ⊔ d.S.A₂ := by
    rw [d.hsup]
    exact JhatOn_eq hV
  have hM0 : m0Of T Mc M ≤ Mc := by
    intro h hh
    obtain ⟨hhM, hhN, hhA⟩ := mem_preOn.1 hh
    have hmem : convI hV ⟨h, hhN⟩ ∈ autI hV (M ⊓ Mc) := hA0 (hmB ▸ hhA)
    obtain ⟨⟨g, hgN⟩, hgK, hgeq⟩ := (mem_autI hV).1 hmem
    have hc : g⁻¹ * h ∈ Subgroup.centralizer (V154 T Mc M : Set G) := by
      have h1 : convI hV ⟨g⁻¹ * h, (Subgroup.normalizer _).mul_mem
          ((Subgroup.normalizer _).inv_mem hgN) hhN⟩ = 1 := by
        have : (⟨g⁻¹ * h, (Subgroup.normalizer _).mul_mem
          ((Subgroup.normalizer _).inv_mem hgN) hhN⟩ : Subgroup.normalizer (V154 T Mc M : Set G)) =
            ⟨g, hgN⟩⁻¹ * ⟨h, hhN⟩ := rfl
        rw [this, map_mul, map_inv, hgeq, inv_mul_cancel]
      exact (convI_eq_one_iff hV _).1 h1
    have : h = g * (g⁻¹ * h) := by group
    rw [this]
    exact Mc.mul_mem hgK.2 (h15.centralizer_le hc)
  have hVle : V154 T Mc M ≤ VZ T Mc := by
    rw [h15.gen]
    refine conjClosure_le fun h hh z hz => ?_
    exact mem_conjClosure (hM0 hh) hz.1
  have hord := h19.two.2 Mc ⟨hq.mc_max, hq.t_le_mc⟩
  have hMcN : Mc ≤ Subgroup.normalizer (V154 T Mc M : Set G) := by
    intro h hh
    obtain ⟨a, ha, c, hc, rfl⟩ := hord h hh
    exact (Subgroup.normalizer _).mul_mem (d.hMN ha.2)
      (Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hVle hc.2))
  have hloc : IsTwoLocal (Subgroup.normalizer (V154 T Mc M : Set G)) := by
    refine ⟨V154 T Mc M, ?_, ?_, rfl⟩
    · intro hb
      have h256 := d.hcard
      have : Nat.card (IntMod (V154 T Mc M) hV) = 1 := by
        change Nat.card (V154 T Mc M) = 1
        rw [hb, Subgroup.card_bot]
      omega
    · intro x
      exact ⟨1, by simpa using Subtype.ext (hV.2 x x.2)⟩
  have heq := hq.mc_max.2 _ hloc hMcN
  exact not_le_mc_of_isMf hq hM (by rw [← heq]; exact d.hMN)

theorem v2_comm {Z : Subgroup G} (hZ : Z ≤ d.V₁) (hZne : Z ≠ ⊥) {Y' : Subgroup G}
    (hY : Y' ≤ M ⊓ g1_1516 Z) (h5 : IsPGroup 5 Y') (hY2 : ⁅d.V₂, Y'⁆ = d.V₂) :
    ⁅d.V₂, oTwoUpper (M ⊓ g1_1516 Z)⁆ = d.V₂ := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro v hv x hx
    have hxK : x ∈ M ⊓ g1_1516 Z := oTwoUpper_le _ hx
    have hxN2 := centralizer_le_normalizer₂ d hZ hZne ⟨hxK.1, hxK.2⟩
    have h1 : x * v⁻¹ * x⁻¹ ∈ d.V₂ :=
      (Subgroup.mem_normalizer_iff.mp hxN2 v⁻¹).1 (d.V₂.inv_mem hv)
    have : ⁅v, x⁆ = v * (x * v⁻¹ * x⁻¹) := by
      simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact d.V₂.mul_mem hv h1
  · have hYO : Y' ≤ oTwoUpper (M ⊓ g1_1516 Z) := by
      intro y hy
      obtain ⟨k, hk⟩ := h5 ⟨y, hy⟩
      have hord : orderOf y ∣ 5 ^ k := by
        apply orderOf_dvd_of_pow_eq_one
        simpa using congrArg Subtype.val hk
      refine mem_oTwoUpper_of_odd (hY hy) ?_
      exact Odd.of_dvd_nat (Odd.pow (by decide)) hord
    calc d.V₂ = ⁅d.V₂, Y'⁆ := hY2.symm
      _ ≤ ⁅d.V₂, oTwoUpper (M ⊓ g1_1516 Z)⁆ := Subgroup.commutator_mono le_rfl hYO

end Gen

end CFSG.Quasithin.E9

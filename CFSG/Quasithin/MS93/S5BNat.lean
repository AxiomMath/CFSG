module

public import CFSG.Quasithin.MS93.MSPOff
public import CFSG.Quasithin.MS93.S5BXZ

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

namespace S5B

section Sp4

variable {F : Type} [Field F]

theorem fixSp_eq_perp_commSp (A : Subgroup (MSP.Sp4 F)) :
    MSP.fixSp A = MSP.perp (MSP.commSp A) := by
  ext w
  rw [MSP.mem_perp]
  constructor
  · intro hw x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, hg, v, rfl⟩ := hx
      rw [map_sub, LinearMap.sub_apply, ← hw g hg, MSP.form_mat, hw g hg, sub_self]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, LinearMap.smul_apply, hx, smul_zero]
  · intro hw g hg
    have hnd := MSP.form_nondegenerate (F := F)
    have key : ∀ v : MSP.V4 F, MSP.form F (MSP.mat g *ᵥ w - w) v = 0 := by
      intro v
      have h1 := hw (MSP.mat g⁻¹ *ᵥ v - v) (MSP.sub_mem_commSp (A.inv_mem hg) v)
      have h2 : MSP.form F (MSP.mat g *ᵥ w) v = MSP.form F w (MSP.mat g⁻¹ *ᵥ v) := by
        rw [← MSP.form_mat g w (MSP.mat g⁻¹ *ᵥ v), MSP.mat_mulVec_inv]
      rw [map_sub, LinearMap.sub_apply, MSP.form_swap w (MSP.mat g⁻¹ *ᵥ v),
        MSP.form_swap w v] at h1
      rw [map_sub, LinearMap.sub_apply, h2]
      linear_combination -h1
    exact sub_eq_zero.1 (hnd.1 _ key)

end Sp4

section NatM

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

omit [Fintype F] in
theorem mem_centralizer_iff_vec (h : PUHyp M T L)
    (hlift : ∀ m ∈ M, ∀ u ∈ Uq M T L, m * u * m⁻¹ * u⁻¹ ∈ Subgroup.centralizer (L : Set G) →
      m * u * m⁻¹ = u)
    (c : MSP.NatCoord M (Uq M T L) (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) a)
    {E : Subgroup G} (hEM : E ≤ M) (u : ↥(Uq M T L)) :
    (u : G) ∈ Subgroup.centralizer (E : Set G) ↔ c.vec u ∈ MSP.fixSp ((E.subgroupOf M).map a) := by
  have hUn : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  rw [c.vec_mem_fixSp_iff hUn, Subgroup.mem_centralizer_iff]
  constructor
  · intro hc b hb
    rw [hc b (Subgroup.mem_subgroupOf.1 hb), mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  · intro hc e he
    have h1 := hc ⟨e, hEM he⟩ (Subgroup.mem_subgroupOf.2 he)
    have h2 := hlift e (hEM he) u u.2 h1.2
    calc e * u = e * u * e⁻¹ * e := by group
      _ = u * e := by rw [h2]

omit [Fintype F] in
theorem relIndex_centralizer_mul_card (h : PUHyp M T L)
    (hlift : ∀ m ∈ M, ∀ u ∈ Uq M T L, m * u * m⁻¹ * u⁻¹ ∈ Subgroup.centralizer (L : Set G) →
      m * u * m⁻¹ = u)
    (c : MSP.NatCoord M (Uq M T L) (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) a)
    {E : Subgroup G} (hEM : E ≤ M) :
    (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) *
        Nat.card (MSP.fixSp ((E.subgroupOf M).map a)) = Nat.card (MSP.V4 F) := by
  set W := (MSP.fixSp ((E.subgroupOf M).map a)).toAddSubgroup
  let π : MSP.V4 F →+ MSP.V4 F ⧸ W := QuotientAddGroup.mk' W
  let φ : ↥(Uq M T L) →* Multiplicative (MSP.V4 F ⧸ W) :=
    (AddMonoidHom.toMultiplicative π).comp c.toVec
  have hφs : Function.Surjective φ := by
    intro y
    obtain ⟨w, rfl⟩ := QuotientAddGroup.mk'_surjective W (Multiplicative.toAdd y)
    obtain ⟨u, hu⟩ := c.exists_vec_eq w
    refine ⟨u, ?_⟩
    simp only [φ, MonoidHom.comp_apply]
    change Multiplicative.ofAdd (π (Multiplicative.toAdd (c.toVec u))) = _
    rw [show Multiplicative.toAdd (c.toVec u) = c.vec u from rfl, hu]
    rfl
  have hker : φ.ker = (Subgroup.centralizer (E : Set G)).subgroupOf (Uq M T L) := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_centralizer_iff_vec h hlift c hEM]
    simp only [φ, MonoidHom.comp_apply]
    change Multiplicative.ofAdd (π (c.vec u)) = 1 ↔ _
    rw [← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff]
    simp only [π, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    rfl
  have h1 : (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) = Nat.card (MSP.V4 F ⧸ W) := by
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker, MonoidHom.range_eq_top.2 hφs,
      Subgroup.card_top]
    rfl
  rw [h1]
  exact (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup W).symm

theorem exists_point_of_card_commutator_le (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    (hlift : ∀ m ∈ M, ∀ u ∈ Uq M T L, m * u * m⁻¹ * u⁻¹ ∈ Subgroup.centralizer (L : Set G) →
      m * u * m⁻¹ = u)
    {E : Subgroup G} (hEM : E ≤ M) (hE2 : IsPGroup 2 E) (hEO : ¬ E ≤ pCoreOf 2 M)
    (hcard : Nat.card ↥⁅Uq M T L, E⁆ ≤ 2 ^ k) :
    ∃ p : Submodule F (MSP.V4 F), MSP.IsPoint p ∧
      MSP.commSp ((E.subgroupOf M).map a) = p ∧
      MSP.fixSp ((E.subgroupOf M).map a) = MSP.perp p ∧
      (E.subgroupOf M).map a ≤ MSP.xPoint p ∧
      (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) = 2 ^ k := by
  obtain ⟨c⟩ := MSP.nonempty_natCoord hd.2.2.2
  have hUn : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  set Ē := (E.subgroupOf M).map a
  have hFq : Nat.card F = 2 ^ k := by rw [Nat.card_eq_fintype_card, hd.2.1]
  have hĒ : Ē ≠ ⊥ := by
    intro hbot
    apply hEO
    intro e he
    have h1 : a ⟨e, hEM he⟩ = 1 := by
      have : a ⟨e, hEM he⟩ ∈ Ē := ⟨⟨e, hEM he⟩, Subgroup.mem_subgroupOf.2 he, rfl⟩
      rw [hbot] at this
      exact this
    obtain ⟨n, hn⟩ := hE2 ⟨e, he⟩
    exact mem_pCoreOf_of_ker h hd h1 ⟨n, by simpa using congrArg Subtype.val hn⟩
  have hUE : ⁅Uq M T L, E⁆ ≤ Uq M T L := commutator_le_left_of_le_normalizer (hEM.trans hUn)
  have hclos : ∀ x ∈ Subgroup.closure {x : ↥(Uq M T L) | ∃ b ∈ E.subgroupOf M,
      ∃ v : ↥(Uq M T L), (x : G) = (b : G) * v * (b : G)⁻¹ * (v : G)⁻¹},
      (x : G) ∈ ⁅Uq M T L, E⁆ := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨b, hb, v, hxv⟩ := hx
      rw [hxv, ← commutatorElement_def, Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.1 hb) v.2
    | one => exact one_mem _
    | mul x y _ _ hx hy => exact mul_mem hx hy
    | inv x _ hx => exact inv_mem hx
  have hsurj : ∀ w ∈ MSP.commSp Ē, ∃ x : ↥⁅Uq M T L, E⁆, c.vec ⟨x, hUE x.2⟩ = w := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := (c.mem_commSp_iff hUn _ w).1 hw
    exact ⟨⟨u, hclos u hu⟩, rfl⟩
  have hsub : ((MSP.commSp Ē : Submodule F (MSP.V4 F)) : Set (MSP.V4 F)) ⊆
      Set.range (fun x : ↥⁅Uq M T L, E⁆ => c.vec ⟨x, hUE x.2⟩) := fun w hw => hsurj w hw
  have hcomm : Nat.card (MSP.commSp Ē) ≤ 2 ^ k :=
    ((Nat.card_mono (Set.finite_range _) hsub).trans (Finite.card_range_le _)).trans hcard
  have hcard' : Nat.card (MSP.commSp Ē) = (2 ^ k) ^ Module.finrank F (MSP.commSp Ē) := by
    rw [← hFq]
    exact Module.natCard_eq_pow_finrank (K := F)
  have hk1 : 1 ≤ k := hd.1
  have h2k : 1 < 2 ^ k := Nat.one_lt_two_pow (by omega)
  have hd1 : Module.finrank F (MSP.commSp Ē) ≤ 1 := by
    by_contra hlt
    push Not at hlt
    have : (2 ^ k) ^ 2 ≤ (2 ^ k) ^ Module.finrank F (MSP.commSp Ē) :=
      Nat.pow_le_pow_right (by omega) hlt
    have : 2 ^ k < (2 ^ k) ^ 2 := by nlinarith
    omega
  have hd0 : Module.finrank F (MSP.commSp Ē) ≠ 0 := by
    intro h0
    apply hĒ
    rw [← MSP.fixSp_eq_top_iff, fixSp_eq_perp_commSp, Submodule.finrank_eq_zero.1 h0]
    exact LinearMap.BilinForm.orthogonal_bot
  have hp : MSP.IsPoint (MSP.commSp Ē) := by
    change Module.finrank F (MSP.commSp Ē) = 1
    omega
  refine ⟨MSP.commSp Ē, hp, rfl, fixSp_eq_perp_commSp _, ?_, ?_⟩
  · rw [MSP.le_fixer_iff, fixSp_eq_perp_commSp]
  · have hrel := relIndex_centralizer_mul_card h hlift c hEM
    have hfix : Nat.card (MSP.fixSp Ē) = (2 ^ k) ^ 3 := by
      rw [fixSp_eq_perp_commSp, ← hFq]
      have h4 := MSP.finrank_perp (MSP.commSp Ē)
      rw [Module.natCard_eq_pow_finrank (K := F)]
      congr 1
      have : Module.finrank F (MSP.commSp Ē) = 1 := hp
      omega
    rw [hfix, MSP.card_V4, hFq] at hrel
    have hpos : 0 < (2 ^ k) ^ 3 := by positivity
    have : (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) * (2 ^ k) ^ 3 =
        2 ^ k * (2 ^ k) ^ 3 := by rw [hrel]; ring
    exact Nat.eq_of_mul_eq_mul_right hpos this

end NatM

end S5B

end CFSG.Quasithin.MS93

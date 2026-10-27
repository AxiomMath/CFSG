module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ListedOddRankProj
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Quasithin.EmptyFaithful.LRed5Quot
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Quasithin.Vol2.Ch3Sec2Inputs

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.E9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13
open scoped commutatorElement

variable {G : Type} [Group G]

theorem convI_mem_normalizer_autI {Z K : Subgroup G} (hZ : IsElemAbelian 2 Z)
    {g : Subgroup.normalizer (Z : Set G)} (hgK : (g : G) ∈ Subgroup.normalizer (K : Set G)) :
    convI hZ g ∈ Subgroup.normalizer (autI hZ K : Set (MulAut (IntMod Z hZ))) := by
  have key : ∀ (h : Subgroup.normalizer (Z : Set G)),
      (h : G) ∈ Subgroup.normalizer (K : Set G) → ∀ φ ∈ autI hZ K,
        convI hZ h * φ * (convI hZ h)⁻¹ ∈ autI hZ K := by
    intro h hh φ hφ
    obtain ⟨k, hk, rfl⟩ := (mem_autI hZ).mp hφ
    rw [← map_inv, ← map_mul, ← map_mul]
    exact convI_mem_autI hZ ((Subgroup.mem_normalizer_iff.mp hh k).mp hk) _
  rw [Subgroup.mem_normalizer_iff]
  intro φ
  refine ⟨key g hgK φ, fun hφ => ?_⟩
  have h2 := key g⁻¹ (Subgroup.inv_mem _ hgK) _ hφ
  rw [map_inv, inv_inv] at h2
  simpa [mul_assoc] using h2

theorem mem_fixV_autI_iff {Z K : Subgroup G} (hZ : IsElemAbelian 2 Z)
    (hK : K ≤ Subgroup.normalizer (Z : Set G)) (v : IntMod Z hZ) :
    v ∈ fixV (autI hZ K) ↔ v.val ∈ Subgroup.centralizer (K : Set G) := by
  rw [mem_fixV, Subgroup.mem_centralizer_iff]
  constructor
  · intro h k hk
    have h1 := congrArg IntMod.val (h _ (convI_mem_autI hZ hk (hK hk)))
    rw [convI_apply_val] at h1
    calc k * v.val = k * v.val * k⁻¹ * k := by group
      _ = v.val * k := by rw [h1]
  · intro h φ hφ
    obtain ⟨g, hg, rfl⟩ := (mem_autI hZ).mp hφ
    refine IntMod.val_injective ?_
    rw [convI_apply_val]
    show (g : G) * v.val * (g : G)⁻¹ = v.val
    rw [h g hg, mul_inv_cancel_right]

theorem mk_mem_commV_autI {Z A K : Subgroup G} (hZ : IsElemAbelian 2 Z) (hAZ : A ≤ Z)
    (hK : K ≤ Subgroup.normalizer (Z : Set G)) {x : G} (hx : x ∈ ⁅A, K⁆) (hxZ : x ∈ Z) :
    (IntMod.mk hZ ⟨x, hxZ⟩ : IntMod Z hZ) ∈ commV (autI hZ K) := by
  have hcZ : ⁅A, K⁆ ≤ Z := by
    rw [Subgroup.commutator_le]
    intro a ha k hk
    have hka : k * a⁻¹ * k⁻¹ ∈ Z :=
      (Subgroup.mem_normalizer_iff.mp (hK hk) _).mp (Z.inv_mem (hAZ ha))
    have e : ⁅a, k⁆ = a * (k * a⁻¹ * k⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact Z.mul_mem (hAZ ha) hka
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, k, hk, rfl⟩ := hy
    have hk' := convI_mem_autI hZ hk (hK hk)
    have hmem : convI hZ ⟨k, hK hk⟩ (IntMod.mk hZ ⟨a, hAZ ha⟩) *
        (IntMod.mk hZ ⟨a, hAZ ha⟩)⁻¹ ∈ commV (autI hZ K) :=
      Subgroup.subset_closure ⟨_, hk', _, rfl⟩
    have e : (IntMod.mk hZ ⟨⁅a, k⁆, hxZ⟩ : IntMod Z hZ) =
        (convI hZ ⟨k, hK hk⟩ (IntMod.mk hZ ⟨a, hAZ ha⟩) * (IntMod.mk hZ ⟨a, hAZ ha⟩)⁻¹)⁻¹ := by
      refine IntMod.val_injective ?_
      rw [IntMod.val_inv, IntMod.val_mul, IntMod.val_inv, convI_apply_val]
      show ⁅a, k⁆ = (k * a * k⁻¹ * a⁻¹)⁻¹
      rw [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.inv_mem _ hmem
  | one => exact Subgroup.one_mem _
  | mul y z hy hz ihy ihz =>
    have hyZ := hcZ hy
    have hzZ := hcZ hz
    have e : (IntMod.mk hZ ⟨y * z, hxZ⟩ : IntMod Z hZ) =
        IntMod.mk hZ ⟨y, hyZ⟩ * IntMod.mk hZ ⟨z, hzZ⟩ := rfl
    rw [e]
    exact Subgroup.mul_mem _ (ihy hyZ) (ihz hzZ)
  | inv y hy ihy =>
    have hyZ := hcZ hy
    have e : (IntMod.mk hZ ⟨y⁻¹, hxZ⟩ : IntMod Z hZ) = (IntMod.mk hZ ⟨y, hyZ⟩)⁻¹ := rfl
    rw [e]
    exact Subgroup.inv_mem _ (ihy hyZ)

variable [Finite G]

omit [Finite G] in
theorem mem_of_odd_of_le_sup {N T : Subgroup G} (hT : IsPGroup 2 ↥T)
    (hNT : N ⊔ T ≤ Subgroup.normalizer (N : Set G)) {x : G} (hx : x ∈ N ⊔ T)
    (hodd : Odd (orderOf x)) : x ∈ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (N.subgroupOf (N ⊔ T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hNT
  have hsup : N.subgroupOf (N ⊔ T) ⊔ T.subgroupOf (N ⊔ T) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  have hT' : IsPGroup 2 ↥(T.subgroupOf (N ⊔ T)) :=
    hT.of_equiv (Subgroup.subgroupOfEquivOfLe le_sup_right).symm
  have hQ := LRed5.isPGroup_quotient_of_sup hsup hT'
  set q := (QuotientGroup.mk (⟨x, hx⟩ : ↥(N ⊔ T)) : ↥(N ⊔ T) ⧸ N.subgroupOf (N ⊔ T)) with hq
  obtain ⟨k, hk⟩ := hQ q
  have hord : orderOf q ∣ orderOf (⟨x, hx⟩ : ↥(N ⊔ T)) :=
    orderOf_map_dvd (QuotientGroup.mk' (N.subgroupOf (N ⊔ T))) _
  rw [Subgroup.orderOf_mk] at hord
  have h1 : orderOf q ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf q = 1 := by
    have hc : Nat.Coprime (2 ^ k) (orderOf x) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
    exact Nat.eq_one_of_dvd_coprimes hc h1 hord
  rw [orderOf_eq_one_iff, hq, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h2
  exact h2

omit [Finite G] in
theorem commute_of_commutator {x w : G} (hodd : Odd (orderOf x))
    (hc : x * (x * w * x⁻¹ * w⁻¹) = (x * w * x⁻¹ * w⁻¹) * x)
    (hc2 : (x * w * x⁻¹ * w⁻¹) ^ 2 = 1) : x * w = w * x := by
  obtain ⟨c, hcdef⟩ : ∃ c, c = x * w * x⁻¹ * w⁻¹ := ⟨_, rfl⟩
  rw [← hcdef] at hc hc2
  have hxw : x * w * x⁻¹ = c * w := by rw [hcdef]; group
  have hxc : x * c * x⁻¹ = c := by rw [hc, mul_inv_cancel_right]
  have hx2 : x ^ 2 * w * (x ^ 2)⁻¹ = w := by
    calc x ^ 2 * w * (x ^ 2)⁻¹ = x * (x * w * x⁻¹) * x⁻¹ := by rw [sq]; group
      _ = x * (c * w) * x⁻¹ := by rw [hxw]
      _ = (x * c * x⁻¹) * (x * w * x⁻¹) := by group
      _ = c * (c * w) := by rw [hxc, hxw]
      _ = c ^ 2 * w := by rw [sq, mul_assoc]
      _ = w := by rw [hc2, one_mul]
  have hcomm : Commute (x ^ 2) w := by
    show x ^ 2 * w = w * x ^ 2
    calc x ^ 2 * w = x ^ 2 * w * (x ^ 2)⁻¹ * x ^ 2 := by group
      _ = w * x ^ 2 := by rw [hx2]
  obtain ⟨k, hk⟩ := hodd
  have hx : (x ^ 2) ^ (k + 1) = x := by
    rw [← pow_mul, show 2 * (k + 1) = orderOf x + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have := hcomm.pow_left (k + 1)
  rw [hx] at this
  exact this

end CFSG.Quasithin.Vol2.Ch10.SecB.E9

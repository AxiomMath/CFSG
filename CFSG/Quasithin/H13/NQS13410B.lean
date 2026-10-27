module

public import CFSG.Quasithin.EmptyFaithful.SBd5Perf
public import CFSG.Quasithin.H13.NQS1345B
public import CFSG.Quasithin.H13.U3S1343
public import CFSG.Quasithin.H13.U3S134Defs

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.InternalSec
open CFSG.LieType.BorelTits
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conjClosure_sup_eq {T K Z : Subgroup G} (hTK : T ≤ normalizer (K : Set G))
    (hTZ : T ≤ centralizer (Z : Set G)) : conjClosure Z (K ⊔ T) = conjClosure Z K := by
  refine le_antisymm (conjClosure_le fun x hx z hz => ?_) (conjClosure_mono le_rfl le_sup_left)
  obtain ⟨k, hk, t, ht, rfl⟩ := Vol2.Ch11.SecC.mem_sup_of_le_normalizer hTK hx
  have htz : t * z * t⁻¹ = z := by
    rw [← (mem_centralizer_iff.mp (hTZ ht) z hz), mul_inv_cancel_right]
  have e : k * t * z * (k * t)⁻¹ = k * (t * z * t⁻¹) * k⁻¹ := by group
  rw [e, htz]
  exact mem_conjClosure hk hz

section VH

variable {T K : Subgroup G} (hTsyl : IsSylowTwoOf T (K ⊔ T)) (hchar : CharTwo (K ⊔ T))
  (hTK : T ≤ normalizer (K : Set G))
include hTsyl hchar hTK

theorem isTwoReducedIn_vH :
    IsTwoReducedIn (K ⊔ T) (conjClosure (quasithinOmegaOneCenter T) K) := by
  have hred := isTwoReducedIn_conjClosure_of_sylowIn hTsyl.1 hTsyl.2.1 hTsyl.2.2 hchar
    (le_rfl : quasithinOmegaOneCenter T ≤ quasithinOmegaOneCenter T)
  rwa [conjClosure_sup_eq hTK ((U3.s134_Z_le_center T).trans inf_le_right |>
    le_centralizer_iff.mp)] at hred

theorem vH_le_R2 : conjClosure (quasithinOmegaOneCenter T) K ≤ reducedAggregate (K ⊔ T) :=
  le_R2_of_isTwoReducedIn (isTwoReducedIn_vH hTsyl hchar hTK)

theorem vH_le_T : conjClosure (quasithinOmegaOneCenter T) K ≤ T :=
  ((vH_le_R2 hTsyl hchar hTK).trans (R2_le_pCoreOf (K ⊔ T))).trans
    (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hTsyl)

theorem vH_eq_sup :
    conjClosure (quasithinOmegaOneCenter T) K =
      ⁅conjClosure (quasithinOmegaOneCenter T) K, K⁆ ⊔ U3.cZ T K := by
  set Z := quasithinOmegaOneCenter T with hZdef
  set VH := conjClosure Z K with hVHdef
  have hTZ : T ≤ centralizer (Z : Set G) :=
    le_centralizer_iff.mp ((U3.s134_Z_le_center T).trans inf_le_right)
  have hred := isTwoReducedIn_vH hTsyl hchar hTK
  have hVHe : IsElemAbelian 2 VH := hred.2.2.1
  have hcomm : ∀ a ∈ VH, ∀ b ∈ VH, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hVHe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hKN : K ≤ normalizer (VH : Set G) := le_normalizer_conjClosure Z K
  have hTN : T ≤ normalizer (VH : Set G) := le_sup_right.trans hred.2.1
  have hb213 := Vol2.Ch11.SecC.conjClosure_eq_commutator_sup (X := K ⊔ T) (T := T) (Z := Z)
    hTsyl.2.2 (by rw [conjClosure_sup_eq hTK hTZ]; exact hVHe) hTZ
  rw [conjClosure_sup_eq hTK hTZ] at hb213
  have hwt : ∀ t ∈ T, ∀ w ∈ VH, w * t * w⁻¹ * t⁻¹ ∈ ⁅VH, K⁆ := by
    intro t ht w hw
    induction hw using closure_induction with
    | mem x hx =>
      obtain ⟨k, hk, z, hz, rfl⟩ := hx
      have hk' : t * k * t⁻¹ ∈ K := (mem_normalizer_iff.mp (hTK ht) k).mp hk
      have htz : t * z * t⁻¹ = z := by
        rw [← (mem_centralizer_iff.mp (hTZ ht) z hz), mul_inv_cancel_right]
      have hzVH : z ∈ VH := le_conjClosure Z K hz
      have e : k * z * k⁻¹ * t * (k * z * k⁻¹)⁻¹ * t⁻¹ =
          (z * k * z⁻¹ * k⁻¹)⁻¹ * (z * (t * k * t⁻¹) * z⁻¹ * (t * k * t⁻¹)⁻¹) := by
        calc k * z * k⁻¹ * t * (k * z * k⁻¹)⁻¹ * t⁻¹
            = k * z * k⁻¹ * ((t * k * t⁻¹) * (t * z * t⁻¹)⁻¹ * (t * k * t⁻¹)⁻¹) := by group
          _ = k * z * k⁻¹ * ((t * k * t⁻¹) * z⁻¹ * (t * k * t⁻¹)⁻¹) := by rw [htz]
          _ = (z * k * z⁻¹ * k⁻¹)⁻¹ * (z * (t * k * t⁻¹) * z⁻¹ * (t * k * t⁻¹)⁻¹) := by group
      rw [e]
      refine mul_mem (inv_mem ?_) ?_
      · have := commutator_mem_commutator hzVH hk
        rwa [commutatorElement_def] at this
      · have := commutator_mem_commutator hzVH hk'
        rwa [commutatorElement_def] at this
    | one => simp
    | mul x y hx hy ihx ihy =>
      have hyt : y * t * y⁻¹ * t⁻¹ ∈ VH := by
        have h1 : t * y⁻¹ * t⁻¹ ∈ VH := (mem_normalizer_iff.mp (hTN ht) _).mp (inv_mem hy)
        have e : y * t * y⁻¹ * t⁻¹ = y * (t * y⁻¹ * t⁻¹) := by group
        rw [e]
        exact mul_mem hy h1
      have e : x * y * t * (x * y)⁻¹ * t⁻¹ =
          (x * (y * t * y⁻¹ * t⁻¹) * x⁻¹) * (x * t * x⁻¹ * t⁻¹) := by group
      have hx' : x * (y * t * y⁻¹ * t⁻¹) * x⁻¹ = y * t * y⁻¹ * t⁻¹ := by
        rw [hcomm x hx _ hyt, mul_inv_cancel_right]
      rw [e, hx']
      exact mul_mem ihy ihx
    | inv x hx ih =>
      have hxt : x * t * x⁻¹ * t⁻¹ ∈ VH := by
        have h1 : t * x⁻¹ * t⁻¹ ∈ VH := (mem_normalizer_iff.mp (hTN ht) _).mp (inv_mem hx)
        have e : x * t * x⁻¹ * t⁻¹ = x * (t * x⁻¹ * t⁻¹) := by group
        rw [e]
        exact mul_mem hx h1
      have e : x⁻¹ * t * x⁻¹⁻¹ * t⁻¹ = x⁻¹ * (x * t * x⁻¹ * t⁻¹)⁻¹ * x := by group
      rw [e, hcomm x⁻¹ (inv_mem hx) _ (inv_mem hxt), inv_mul_cancel_right]
      exact inv_mem ih
  have hKTle : ⁅VH, K ⊔ T⁆ ≤ ⁅VH, K⁆ := by
    rw [commutator_le]
    intro w hw x hx
    obtain ⟨k, hk, t, ht, rfl⟩ := Vol2.Ch11.SecC.mem_sup_of_le_normalizer hTK hx
    have hKVK : K ≤ normalizer ((⁅VH, K⁆ : Subgroup G) : Set G) := fun g hg =>
      SBd5.mem_normalizer_commutator_of (hKN hg) (le_normalizer hg)
    have h1 : w * k * w⁻¹ * k⁻¹ ∈ ⁅VH, K⁆ := by
      have := commutator_mem_commutator hw hk
      rwa [commutatorElement_def] at this
    have h2 : k * (w * t * w⁻¹ * t⁻¹) * k⁻¹ ∈ ⁅VH, K⁆ :=
      (mem_normalizer_iff.mp (hKVK hk) _).mp (hwt t ht w hw)
    have e : ⁅w, k * t⁆ = (w * k * w⁻¹ * k⁻¹) * (k * (w * t * w⁻¹ * t⁻¹) * k⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact mul_mem h1 h2
  have hcent : VH ⊓ centralizer ((K ⊔ T : Subgroup G) : Set G) ≤ U3.cZ T K := by
    rintro w ⟨hw, hwc⟩
    have hwT : w ∈ T := vH_le_T hTsyl hchar hTK hw
    refine ⟨mem_quasithinOmegaOneCenter_iff.2 ⟨hwT, ?_, hVHe.2 w hw⟩, ?_⟩
    · exact centralizer_le (SetLike.coe_subset_coe.mpr (le_sup_right : T ≤ K ⊔ T)) hwc
    · exact centralizer_le (SetLike.coe_subset_coe.mpr (le_sup_left : K ≤ K ⊔ T)) hwc
  refine le_antisymm ?_ (sup_le (le_normalizer_iff_commutator_le_left.mp hKN)
    (inf_le_left.trans (le_conjClosure Z K)))
  calc VH = ⁅VH, K ⊔ T⁆ ⊔ (VH ⊓ centralizer ((K ⊔ T : Subgroup G) : Set G)) := hb213
    _ ≤ ⁅VH, K⁆ ⊔ U3.cZ T K := sup_le_sup hKTle hcent

theorem cent_vH_eq :
    (K ⊔ T) ⊓ centralizer (conjClosure (quasithinOmegaOneCenter T) K : Set G) =
      (K ⊔ T) ⊓ centralizer
        ((⁅conjClosure (quasithinOmegaOneCenter T) K, K⁆ : Subgroup G) : Set G) := by
  refine le_antisymm (inf_le_inf_left _ (centralizer_le (SetLike.coe_subset_coe.mpr
    (le_normalizer_iff_commutator_le_left.mp (le_normalizer_conjClosure _ K))))) ?_
  intro x hx'
  obtain ⟨hx, hxc⟩ := mem_inf.mp hx'
  refine mem_inf.mpr ⟨hx, ?_⟩
  have hcZ : K ⊔ T ≤ centralizer (U3.cZ T K : Set G) := by
    refine sup_le (le_centralizer_iff.mp inf_le_right) ?_
    exact le_centralizer_iff.mp (inf_le_left.trans ((U3.s134_Z_le_center T).trans inf_le_right))
  rw [vH_eq_sup hTsyl hchar hTK]
  rw [mem_centralizer_iff] at hxc ⊢
  have hab : ∀ a ∈ ⁅conjClosure (quasithinOmegaOneCenter T) K, K⁆, ∀ b ∈ U3.cZ T K,
      a * b = b * a := by
    intro a ha b hb
    have hred := isTwoReducedIn_vH hTsyl hchar hTK
    have haV : a ∈ conjClosure (quasithinOmegaOneCenter T) K :=
      le_normalizer_iff_commutator_le_left.mp (le_normalizer_conjClosure _ K) ha
    have hbV : b ∈ conjClosure (quasithinOmegaOneCenter T) K := le_conjClosure _ K hb.1
    exact congrArg Subtype.val (hred.2.2.1.1.is_comm.comm ⟨a, haV⟩ ⟨b, hbV⟩)
  intro y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := Vol2.Ch11.SecC.mem_sup_of_le_normalizer
    (Vol2.Ch11.SecC.le_normalizer_of_commute hab) hy
  have h1 := hxc a ha
  have h2 := mem_centralizer_iff.mp (hcZ hx) b hb
  calc a * b * x = a * (x * b) := by rw [mul_assoc, h2]
    _ = x * (a * b) := by rw [← mul_assoc, h1, mul_assoc]

theorem vK_le_comm :
    ⁅conjClosure (quasithinOmegaOneCenter T) K, K⁆ ≤ ⁅reducedAggregate (K ⊔ T), K⁆ :=
  commutator_mono (vH_le_R2 hTsyl hchar hTK) le_rfl

end VH

omit [Finite G] in
theorem vK_comm {T K : Subgroup G} (hK : ⁅K, K⁆ = K)
    (hab : ∀ a ∈ conjClosure (quasithinOmegaOneCenter T) K,
      ∀ b ∈ conjClosure (quasithinOmegaOneCenter T) K, a * b = b * a) :
    ⁅⁅conjClosure (quasithinOmegaOneCenter T) K, K⁆, K⁆ =
      ⁅conjClosure (quasithinOmegaOneCenter T) K, K⁆ :=
  SBd5.commutator_commutator_eq_self hK (le_normalizer_conjClosure _ K) hab

theorem comm_R2_eq_vK {T K : Subgroup G} [IsMulCommutative ↥(reducedAggregate (K ⊔ T))]
    (hTsyl : IsSylowTwoOf T (K ⊔ T)) (hchar : CharTwo (K ⊔ T))
    (hTK : T ≤ normalizer (K : Set G)) (hK : ⁅K, K⁆ = K)
    (hirr : commV (autOn K (reducedAggregate (K ⊔ T))) ∈
      IrrPlus (autOn K (reducedAggregate (K ⊔ T))) ⊤)
    (hne : ⁅conjClosure (quasithinOmegaOneCenter T) K, K⁆ ≠ ⊥) :
    ⁅reducedAggregate (K ⊔ T), K⁆ = ⁅conjClosure (quasithinOmegaOneCenter T) K, K⁆ := by
  have hred := isTwoReducedIn_vH hTsyl hchar hTK
  have hab : ∀ a ∈ conjClosure (quasithinOmegaOneCenter T) K,
      ∀ b ∈ conjClosure (quasithinOmegaOneCenter T) K, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hred.2.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hKW : K ≤ normalizer (reducedAggregate (K ⊔ T) : Set G) :=
    le_sup_left.trans (twoReduced_R2 (K ⊔ T)).2.1
  have hKV : K ≤ normalizer ((⁅conjClosure (quasithinOmegaOneCenter T) K, K⁆ : Subgroup G) :
      Set G) := fun g hg =>
    SBd5.mem_normalizer_commutator_of (le_normalizer_conjClosure _ K hg) (le_normalizer hg)
  exact U3.eq_of_irrPlus hKW hirr ((vK_le_comm hTsyl hchar hTK).trans
    (le_normalizer_iff_commutator_le_left.mp hKW)) hKV (vK_comm hK hab) hne

end CFSG.Quasithin.H13.NQS134

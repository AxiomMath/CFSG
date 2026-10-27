module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCBar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.TC914R

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.WeakClosure81

variable {X : Type} [Group X]

theorem comm_of_isComponent [Finite X] {Lb : Subgroup X} (h : CFSG.IsComponent Lb) (t t' : X)
    (hne : conjSubgroup Lb t ≠ conjSubgroup Lb t') :
    ∀ x ∈ conjSubgroup Lb t, ∀ y ∈ conjSubgroup Lb t', x * y = y * x := by
  intro x hx y hy
  rcases CFSG.LocalCores.distinct_components_commute
      (CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj t⁻¹) h)
      (CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj t'⁻¹) h) with heq | hc
  · exact absurd heq hne
  · exact (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc hx) y hy).symm

structure Pre (Lb Tb : Subgroup X) : Prop where
  sylow : IsSylowIn 2 Tb ⊤
  o2 : ∀ K : Subgroup X, K.Normal → IsPGroup 2 K → K = ⊥
  quasi : CFSG.IsQuasisimple ↥Lb
  comm : ∀ t ∈ Tb, ∀ t' ∈ Tb, conjSubgroup Lb t ≠ conjSubgroup Lb t' →
    ∀ x ∈ conjSubgroup Lb t, ∀ y ∈ conjSubgroup Lb t', x * y = y * x
  gen : tcBase Lb Tb ⊔ Tb = ⊤

namespace Pre

variable {Lb Tb : Subgroup X} (c : Pre Lb Tb)
include c

theorem base_normal : (tcBase Lb Tb).Normal := by
  rw [← normalizer_eq_top_iff, eq_top_iff, ← c.gen]
  exact sup_le le_normalizer (le_normalizer_iSup_conj Lb Tb)

theorem base_le_normalizer_Lb : tcBase Lb Tb ≤ normalizer (Lb : Set X) := by
  refine iSup₂_le fun t ht => ?_
  by_cases h : conjSubgroup Lb t = conjSubgroup Lb 1
  · rw [h, conjSubgroup_one]
    exact le_normalizer
  · refine le_trans ?_ (Subgroup.centralizer_le_normalizer (Lb : Set X))
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    rw [← conjSubgroup_one Lb] at hy
    exact (c.comm t ht 1 Tb.one_mem h x hx y hy).symm

theorem isSylowIn_T1 [Finite X] : IsSylowIn 2 (tcT1 Lb Tb) (tcN1 Lb Tb) := by
  have := c.base_normal
  have h := isSylowIn_inf_normalizer c.sylow c.gen c.base_le_normalizer_Lb
  refine ⟨le_sup_right, h.isPGroup, fun hd => h.not_dvd_relIndex ?_⟩
  have hle : tcN1 Lb Tb ≤ normalizer (Lb : Set X) := sup_le le_normalizer inf_le_right
  rw [← relIndex_mul_relIndex _ _ _ (le_sup_right : tcT1 Lb Tb ≤ tcN1 Lb Tb) hle]
  exact dvd_mul_of_dvd_left hd _

theorem pCore_le_T1 [Finite X] : pCoreOf 2 (tcN1 Lb Tb) ≤ tcT1 Lb Tb :=
  CFSG.Quasithin.AppendixH.H14.pCoreOf_le_of_sylow c.isSylowIn_T1.le c.isSylowIn_T1.isPGroup
    c.isSylowIn_T1.not_dvd_relIndex

theorem conj_le_centralizer_conj {Y : Subgroup X} (hYL : Y ≤ Lb)
    (hYc : ∀ y ∈ Y, ∀ l ∈ Lb, y * l = l * y) {s t : X} (hs : s ∈ Tb) (ht : t ∈ Tb) :
    conjSubgroup Lb s ≤ centralizer (conjSubgroup Y t : Set X) := by
  intro x hx
  rw [mem_centralizer_iff]
  intro y hy
  rw [SetLike.mem_coe, mem_conjSubgroup_iff] at hy
  by_cases h : conjSubgroup Lb s = conjSubgroup Lb t
  · rw [h, mem_conjSubgroup_iff] at hx
    have h2 : t * (y * x) * t⁻¹ = t * (x * y) * t⁻¹ := by
      calc t * (y * x) * t⁻¹ = (t * y * t⁻¹) * (t * x * t⁻¹) := by group
        _ = (t * x * t⁻¹) * (t * y * t⁻¹) := hYc _ hy _ hx
        _ = t * (x * y) * t⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  · exact (c.comm s hs t ht h x hx y (mem_conjSubgroup_iff.mpr (hYL hy))).symm

theorem eq_bot_of_le [Finite X] {Y : Subgroup X} (hYL : Y ≤ Lb) (hYT : Y ≤ Tb)
    (hYn : Lb ≤ normalizer (Y : Set X)) (hY2 : IsPGroup 2 Y) : Y = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ := NF914.le_map_center_of_isPGroup c.quasi hYL
    (fun l hl h hh => (mem_normalizer_iff.mp (hYn hl) h).mp hh) hY2
  have hYc : ∀ y ∈ Y, ∀ l ∈ Lb, y * l = l * y := by
    intro y hy l hl
    obtain ⟨z, hz, rfl⟩ := hZ hy
    exact (congrArg Subtype.val (mem_center_iff.mp hz ⟨l, hl⟩)).symm
  set Yh : Subgroup X := ⨆ (t : X) (_ : t ∈ Tb), conjSubgroup Y t with hYh
  have hYhT : Yh ≤ Tb := iSup₂_le fun t ht x hx => by
    rw [mem_conjSubgroup_iff] at hx
    have := Tb.mul_mem (Tb.mul_mem (Tb.inv_mem ht) (hYT hx)) ht
    simpa [mul_assoc] using this
  have hBC : tcBase Lb Tb ≤ centralizer (Yh : Set X) := le_centralizer_iff.mpr
    (iSup₂_le fun t ht => le_centralizer_iff.mpr
      (iSup₂_le fun s hs => c.conj_le_centralizer_conj hYL hYc hs ht))
  have hYhn : Yh.Normal := by
    rw [← normalizer_eq_top_iff, eq_top_iff, ← c.gen]
    exact sup_le (hBC.trans (Subgroup.centralizer_le_normalizer _)) (le_normalizer_iSup_conj Y Tb)
  have hYh1 := c.o2 Yh hYhn (c.sylow.isPGroup.to_le hYhT)
  have hle : Y ≤ Yh := le_iSup₂_of_le 1 Tb.one_mem (conjSubgroup_one Y).ge
  rw [hYh1] at hle
  exact le_bot_iff.mp hle

theorem pCore_inf_Lb [Finite X] : pCoreOf 2 (tcN1 Lb Tb) ⊓ Lb = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine c.eq_bot_of_le inf_le_right (inf_le_left.trans (c.pCore_le_T1.trans inf_le_left)) ?_
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left)
  exact fun l hl => NFW.mem_normalizer_inf
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (mem_sup_left hl)) (le_normalizer hl)

theorem pCore_le_centralizer [Finite X] : pCoreOf 2 (tcN1 Lb Tb) ≤ centralizer (Lb : Set X) := by
  intro q hq
  rw [mem_centralizer_iff]
  intro l hl
  have hqN : q ∈ tcN1 Lb Tb := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hq
  have hqL : q ∈ normalizer (Lb : Set X) := (sup_le le_normalizer inf_le_right) hqN
  have hcomm : l * q * l⁻¹ * q⁻¹ ∈ pCoreOf 2 (tcN1 Lb Tb) ⊓ Lb := by
    refine mem_inf.mpr ⟨?_, ?_⟩
    · exact mul_mem ((mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (mem_sup_left hl)) q).mp hq)
        (inv_mem hq)
    · have h1 : q * l⁻¹ * q⁻¹ ∈ Lb := (mem_normalizer_iff.mp hqL l⁻¹).mp (inv_mem hl)
      have := mul_mem hl h1
      simpa [mul_assoc] using this
  rw [c.pCore_inf_Lb, mem_bot] at hcomm
  calc l * q = (l * q * l⁻¹ * q⁻¹) * (q * l) := by group
    _ = q * l := by rw [hcomm, one_mul]

theorem exists_mul_of_mem_normalizer {x : X} (hx : x ∈ normalizer (Lb : Set X)) :
    ∃ z ∈ centralizer (Lb : Set X), ∃ y ∈ tcN1 Lb Tb, z * y = x := by
  have := c.base_normal
  have hx' : x ∈ tcBase Lb Tb ⊔ Tb := c.gen ▸ mem_top x
  obtain ⟨b, hb, t, ht, rfl⟩ := mem_sup_of_normal_left.mp hx'
  have hbase : tcBase Lb Tb ≤ centralizer (Lb : Set X) ⊔ Lb := by
    refine iSup₂_le fun s hs => ?_
    by_cases h : conjSubgroup Lb s = conjSubgroup Lb 1
    · rw [h, conjSubgroup_one]
      exact le_sup_right
    · refine le_sup_of_le_left fun y hy => mem_centralizer_iff.mpr fun l hl => ?_
      rw [← conjSubgroup_one Lb] at hl
      exact (c.comm s hs 1 Tb.one_mem h y hy l hl).symm
  have hLC : Lb ≤ normalizer (centralizer (Lb : Set X) : Set X) := fun l hl =>
    NFW.mem_normalizer_centralizer (le_normalizer hl)
  have hb' : b ∈ ((centralizer (Lb : Set X) ⊔ Lb : Subgroup X) : Set X) := hbase hb
  rw [coe_mul_of_right_le_normalizer_left _ _ hLC] at hb'
  obtain ⟨z, hz, l, hl, rfl⟩ := Set.mem_mul.mp hb'
  have hzN : z ∈ normalizer (Lb : Set X) := Subgroup.centralizer_le_normalizer _ hz
  have htN : t ∈ normalizer (Lb : Set X) := by
    have := (normalizer (Lb : Set X)).mul_mem (inv_mem (mul_mem hzN (le_normalizer hl))) hx
    simpa [mul_assoc] using this
  exact ⟨z, hz, l * t, mul_mem (mem_sup_left hl) (mem_sup_right ⟨ht, htN⟩), (mul_assoc _ _ _).symm⟩

end Pre

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.TC914R

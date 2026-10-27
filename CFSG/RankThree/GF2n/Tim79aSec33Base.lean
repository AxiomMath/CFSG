module

public import CFSG.RankThree.GF2n.Tim79aSec33Defs
public import CFSG.RankThree.GF2n.Tim79a32
public import CFSG.RankThree.GF2n.Tim79aSec24Inner

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G]

theorem H_le_normalizer_cX (V H : Subgroup G) : H ≤ Subgroup.normalizer (cX V H : Set G) := by
  have key : ∀ h ∈ H, ∀ c ∈ cX V H, h * c * h⁻¹ ∈ cX V H := by
    intro h hh c hc
    obtain ⟨hcH, hcX⟩ := hc
    refine ⟨H.mul_mem (H.mul_mem hh hcH) (H.inv_mem hh), fun y hy => ?_⟩
    have hy' : h⁻¹ * y * h ∈ xOf V H := by
      have := (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_xOf V H (H.inv_mem hh)) y).mp hy
      simpa using this
    have h1 : h * ⁅c, h⁻¹ * y * h⁆ * h⁻¹ ∈ wOf V H :=
      (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H hh) _).mp (hcX _ hy')
    have e : ⁅h * c * h⁻¹, y⁆ = h * ⁅c, h⁻¹ * y * h⁆ * h⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact h1
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨fun hc => key h hh c hc, fun hc => ?_⟩
  have := key h⁻¹ (H.inv_mem hh) _ hc
  simpa [mul_assoc] using this

namespace MinCex

variable {M V Q P H : Subgroup G} [Finite G]

theorem V_inf_cX_le_wOf (hc : MinCex M V Q P H) : V ⊓ cX V H ≤ wOf V H := fun v hv =>
  hc.mem_wOf_of_centralizes_gen hv.1
    (hc.cPbar_centralizes_wOf (Subgroup.mem_inf.mpr ⟨hc.V_le_P hv.1, hv.2⟩))

theorem mem_wOf_of_mem_conj_of_mem_cX (hc : MinCex M V Q P H) {y x : G} (hy : y ∈ H)
    (hxV : x ∈ conjSubgroup y V) (hxc : x ∈ cX V H) : x ∈ wOf V H := by
  have h1 : y⁻¹ * x * y ∈ cX V H := by
    have := (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_cX V H (H.inv_mem hy)) x).mp hxc
    simpa using this
  have h2 : y⁻¹ * x * y ∈ wOf V H := hc.V_inf_cX_le_wOf ⟨mem_conjSubgroup.mp hxV, h1⟩
  have h3 := (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H hy) _).mp h2
  have e : y * (y⁻¹ * x * y) * y⁻¹ = x := by group
  rwa [e] at h3

theorem commute_conj_of_mem_Ycomm (hc : MinCex M V Q P H) {y : G} (hy : y ∈ Ycomm V H) :
    ∀ u ∈ V, ∀ w ∈ conjSubgroup y V, u * w = w * u := by
  obtain ⟨hyX, hyc⟩ := hy
  have hyH : y ∈ H := xOf_le_H hc.V_le_H hyX
  have h := hc.commute_conj_of_commutator_mem_wOf H.one_mem hyH (by
    intro u hu w hw
    rw [conjSubgroup_one] at hu
    exact hyc u hu w hw)
  intro u hu w hw
  exact h u (by rw [conjSubgroup_one]; exact hu) w hw

end MinCex

theorem card_aof_eq {V H : Subgroup G} {y : G} (hy : y ∈ H) :
    Nat.card ↥(Aof V H y) = Nat.card ↥(V ⊓ wOf V H) := by
  have hW : conjSubgroup y (wOf V H) = wOf V H :=
    mem_normalizer_iff_conjSubgroup_eq.mp (H_le_normalizer_wOf V H hy)
  have e : Aof V H y = conjSubgroup y (V ⊓ wOf V H) := by
    rw [conjSubgroup_inf, hW]
    rfl
  rw [e, card_conjSubgroup]

namespace MinCex

variable {M V Q P H : Subgroup G} [Finite G]

theorem commute_of_mem_sup_eof (hc : MinCex M V Q P H) :
    ∀ x ∈ V ⊔ Eof V H P, ∀ z ∈ V ⊔ Eof V H P, x * z = z * x := by
  have hVV : V ≤ Subgroup.centralizer (V : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hc.maxAb.prop.2.2
  have hEV : Eof V H P ≤ Subgroup.centralizer (V : Set G) := fun e he =>
    Subgroup.mem_centralizer_iff.mpr fun v hv => hc.commute_of_mem_P he.1 hv
  have hEE : Eof V H P ≤ Subgroup.centralizer (Eof V H P : Set G) := fun e he =>
    Subgroup.mem_centralizer_iff.mpr fun e' he' => hc.isElemAbelian_wOf_sup_cPbar.comm he'.2 he.2
  have hle : V ⊔ Eof V H P ≤ Subgroup.centralizer ((V ⊔ Eof V H P : Subgroup G) : Set G) := by
    refine sup_le ?_ ?_
    · rw [Subgroup.le_centralizer_iff]
      exact sup_le hVV hEV
    · rw [Subgroup.le_centralizer_iff]
      exact sup_le (Subgroup.le_centralizer_iff.mp hEV) hEE
  intro x hx z hz
  exact Subgroup.mem_centralizer_iff.mp (hle hz) x hx

end MinCex

namespace Sec3Setup

variable {M V Q P H : Subgroup G} [Finite G]

theorem aof_le_P (hs : Sec3Setup M V Q P H) {y : G} (hy : y ∈ Ycomm V H) : Aof V H y ≤ P := by
  have hc : MinCex M V Q P H := hs.setup.mc.toMinCex
  obtain ⟨g, hgX, hg⟩ := hc.exists_noncomm_conj hs.setup.data
  have hdec := (hs.concl.1 g hgX hg).2.1
  obtain ⟨v, hvV, hvW⟩ := SetLike.not_le_iff_exists.mp hc.not_V_le_wOf
  intro α hα
  exact hc.mem_P_of_commute_of_dec hg hdec v hvV hvW α hα.2
    (hc.commute_conj_of_mem_Ycomm hy v hvV α hα.1)

theorem commutator_mem_of_mem_aof (hs : Sec3Setup M V Q P H) {y : G} (hy : y ∈ Ycomm V H) :
    ∀ x ∈ P, ∀ α ∈ Aof V H y, ⁅x, α⁆ ∈ V ⊓ wOf V H := by
  have hc : MinCex M V Q P H := hs.setup.mc.toMinCex
  intro x hx α hα
  refine ⟨hc.commutator_mem_V_of_mem_P hx (hs.aof_le_P hy hα), ?_⟩
  have h1 : x * α * x⁻¹ ∈ wOf V H :=
    (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H (hc.PleH hx)) α).mp hα.2
  rw [commutatorElement_def]
  exact (wOf V H).mul_mem h1 ((wOf V H).inv_mem hα.2)

theorem aof_le_eof (hs : Sec3Setup M V Q P H) {y : G} (hy : y ∈ Ycomm V H) :
    Aof V H y ≤ Eof V H P := fun α hα =>
  Subgroup.mem_inf.mpr ⟨hs.aof_le_P hy hα, Subgroup.mem_sup_left hα.2⟩

end Sec3Setup

theorem sec3BaseStatement_holds :
    ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), Sec3Setup M V Q P H →
      (∀ y ∈ Ycomm V H, Aof V H y ≤ P) ∧
      (∀ y ∈ Ycomm V H, Nat.card ↥(Aof V H y) = Nat.card ↥(V ⊓ wOf V H)) ∧
      (∀ y ∈ Ycomm V H, ∀ x ∈ P, ∀ α ∈ Aof V H y, ⁅x, α⁆ ∈ V ⊓ wOf V H) ∧
      (∀ x ∈ V ⊔ Eof V H P, ∀ z ∈ V ⊔ Eof V H P, x * z = z * x) ∧
      (∀ y ∈ Ycomm V H, Aof V H y ≤ Eof V H P) := by
  intro G _ _ M V Q P H hs
  have hc : MinCex M V Q P H := hs.setup.mc.toMinCex
  exact ⟨fun y hy => hs.aof_le_P hy,
    fun y hy => card_aof_eq (xOf_le_H hc.V_le_H hy.1),
    fun y hy => hs.commutator_mem_of_mem_aof hy,
    hc.commute_of_mem_sup_eof,
    fun y hy => hs.aof_le_eof hy⟩

end CFSG.RankThree.GF2n.Tim79a

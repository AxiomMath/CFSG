module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Bot47Base
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Bot47Plane
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResultsB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Forty7aCommon

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c1_hyp1643_conj_uOne (D : Data G) {V : Subgroup G} (hV : IsElemAbelian 2 V) {z : G}
    (hV64 : Nat.card ↥V = 64) (hU32 : Nat.card ↥(uOne V z) = 32)
    (hSyl : IsSylowIn 2 (D.T ⊓ centralizer ({z} : Set G)) (centralizer ({z} : Set G)))
    {h : G} (hh : h ∈ centralizer ({z} : Set G)) :
    Hyp1643 D ⊥ V 1 (conjSubgroup (uOne V z) h) h := by
  have hA_M : conjSubgroup (uOne V z) h ≤ D.M := by
    calc conjSubgroup (uOne V z) h
        ≤ conjSubgroup (pCoreOf 2 (centralizer ({z} : Set G))) h :=
          E3.conjSubgroup_mono_left h inf_le_right
      _ = pCoreOf 2 (centralizer ({z} : Set G)) :=
          s16c1_conjSubgroup_pCoreOf_self (centralizer ({z} : Set G)) hh
      _ ≤ D.M := s16c1_pCoreOf_le_M D hSyl
  have hA_le : conjSubgroup (uOne V z) h ≤ conjSubgroup V h :=
    E3.conjSubgroup_mono_left h inf_le_left
  have hpg : IsPGroup 2 (conjSubgroup V h) := IsPGroup.map hV.isPGroup _
  have hcard := E3.card_eq_two_pow_mul (V := conjSubgroup V h)
    (U := conjSubgroup (uOne V z) h) hpg hA_le
  have hcardV : Nat.card ↥(conjSubgroup V h) = 64 := by
    rw [E3.card_conjSubgroup, hV64]
  have hcardU : Nat.card ↥(conjSubgroup (uOne V z) h) = 32 := by
    rw [E3.card_conjSubgroup, hU32]
  have hm : E3.mQuot (conjSubgroup V h) (conjSubgroup (uOne V z) h) = 1 := by
    have h32 : 2 ^ E3.mQuot (conjSubgroup V h) (conjSubgroup (uOne V z) h) * 32 =
        2 * 32 := by
      have h := hcard
      rw [hcardV, hcardU] at h
      exact h.symm.trans (by norm_num)
    have h2 : 2 ^ E3.mQuot (conjSubgroup V h) (conjSubgroup (uOne V z) h) = 2 :=
      Nat.mul_right_cancel (m := 32) (by norm_num) h32
    exact Nat.pow_right_injective (a := 2) (by norm_num) (by simpa using h2)
  refine ⟨Or.inr ⟨rfl, rfl⟩, ?_, hA_le⟩
  rw [E3.mem_gammaSet_iff]
  exact ⟨hA_M, h, hA_le, hm⟩

theorem s16c1_uOne_conj_le_centralizer (D : Data G) (hkit : OmegaKit) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D ⊥ V L hV) (hc : Case167_1 D ⊥ V hV L)
    (h43 : R16_43_1 D) {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hSyl : IsSylowIn 2 (D.T ⊓ centralizer ({z} : Set G)) (centralizer ({z} : Set G)))
    (hV64 : Nat.card ↥V = 64) (hU32 : Nat.card ↥(uOne V z) = 32)
    (hVE : ⁅V, eOne V z⁆ ≤ Subgroup.zpowers z) :
    ∀ h ∈ centralizer ({z} : Set G),
      conjSubgroup (uOne V z) h ≤ centralizer (V : Set G) := by
  intro h hh u hu
  have hUe : u ∈ eOne V z := by
    rw [eOne, hConjClosure]
    exact le_iSup (fun k : ↥(centralizer ({z} : Set G)) =>
      conjSubgroup (uOne V z) (k : G)) ⟨h, hh⟩ hu
  have hM : u ∈ D.M :=
    s16c1_pCoreOf_le_M D hSyl (s16c1_eOne_le_pCoreOf V z hUe)
  have hN : u ∈ normalizer (V : Set G) :=
    hS.setting.hyp151.hyp125.pairFacts.le_normalizer hM
  have hustab : u ∈ stabTil (⊥ : Subgroup G) V := by
    refine ⟨hN, ?_⟩
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top _
  have hmem : actTil (⊥ : Subgroup G) V hV ⟨u, hustab⟩ ∈ lBar (⊥ : Subgroup G) V hV L := by
    have hle := h43 (⊥ : Subgroup G) V L hV hS hc 1 (conjSubgroup (uOne V z) h) h
      (s16c1_hyp1643_conj_uOne D hV hV64 hU32 hSyl hh)
    exact hle (actTil_mem_barSub (⊥ : Subgroup G) V hV hu hustab)
  have hcomm : ∀ v ∈ V, u * v * u⁻¹ * v⁻¹ ∈ Subgroup.zpowers z := by
    intro v hv
    have hvu : ⁅v, u⁆ ∈ ⁅V, eOne V z⁆ := Subgroup.commutator_mem_commutator hv hUe
    have hzv : ⁅v, u⁆ ∈ Subgroup.zpowers z := hVE hvu
    have huv : ⁅u, v⁆ ∈ Subgroup.zpowers z := by
      rw [← commutatorElement_inv]
      exact (Subgroup.zpowers z).inv_mem hzv
    simpa only [commutatorElement_def] using huv
  have hcent := s16c1_centralizes_of_comm_le_zpowers (V := V) (hV := hV)
    (H := lBar (⊥ : Subgroup G) V hV L)
    ((hkit (Vtil (⊥ : Subgroup G) V hV) (lBar (⊥ : Subgroup G) V hV L) hc.2.1).2.2)
    hz hz1 hustab hmem hcomm
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hv' := hcent v hv
  calc v * u = (u * v * u⁻¹) * u := by rw [hv']
    _ = u * v := by group

theorem s16c1_conjV_le_M (D : Data G) {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hV64 : Nat.card ↥V = 64) (hr : (4 : ℕ∞) < rMV D.M V) {z : G}
    (hU32 : Nat.card ↥(uOne V z) = 32)
    (hcent : ∀ h ∈ centralizer ({z} : Set G),
      conjSubgroup (uOne V z) h ≤ centralizer (V : Set G)) :
    ∀ h ∈ centralizer ({z} : Set G), conjSubgroup V h ≤ D.M := by
  intro h hh
  have hh_inv : h⁻¹ ∈ centralizer ({z} : Set G) := (centralizer ({z} : Set G)).inv_mem hh
  have hcent' : conjSubgroup (uOne V z) h⁻¹ ≤ centralizer (V : Set G) := hcent h⁻¹ hh_inv
  have hVle : V ≤ conjSubgroup (centralizer (uOne V z : Set G)) h⁻¹ := by
    rw [E3.conjSubgroup_centralizer]
    exact (Subgroup.le_centralizer_iff).2 hcent'
  have hA : 4 ≤ Nat.card ↥(uOne V z) := by rw [hU32]; norm_num
  have hcU : centralizer (uOne V z : Set G) ≤ D.M :=
    s16c1_cent_le_M (M := D.M) hV hV64 hr inf_le_left hA
  have hVleM : V ≤ conjSubgroup D.M h⁻¹ :=
    hVle.trans (E3.conjSubgroup_mono_left h⁻¹ hcU)
  calc conjSubgroup V h ≤ conjSubgroup (conjSubgroup D.M h⁻¹) h :=
        E3.conjSubgroup_mono_left h hVleM
    _ = D.M := E3.conjSubgroup_inv_conj D.M h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

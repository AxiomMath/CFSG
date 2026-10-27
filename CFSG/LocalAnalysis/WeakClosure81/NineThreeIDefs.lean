module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeA

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

private theorem nineThree_conj_iSup {ι : Sort*} (B : ι → Subgroup G) (g : G) :
    conjSubgroup (⨆ i, B i) g = ⨆ i, conjSubgroup (B i) g := by
  simp only [CFSG.Quasithin.conjSubgroup]
  exact Subgroup.map_iSup _ _

structure Nine3IFacts (V K S : Subgroup G) : Prop where
  abelian : IsElemAbelian 2 (nineI V K)
  comm : ∀ B ∈ nineOmegaIn V K S, ⁅nineI V K, B⁆ = B ⊓ pCoreOf 2 K

namespace Nine3Core

theorem nineI_le_pCoreOf : nineI V K ≤ pCoreOf 2 K :=
  iSup₂_le fun _ _ => inf_le_right

theorem nineI_inf_eq (h : Nine3Core V T A K S X p) {B : Subgroup G}
    (hB : B ∈ nineOmegaIn V K S) : B ⊓ nineI V K = B ⊓ pCoreOf 2 K := by
  have hBΩ : B ∈ omegaIn V K (nineE V K) := ⟨hB.1, hB.2.trans h.S_le_K⟩
  refine le_antisymm (inf_le_inf le_rfl nineI_le_pCoreOf) (le_inf inf_le_left ?_)
  exact le_trans (le_inf_iff.mpr ⟨inf_le_left, inf_le_right⟩)
    (le_iSup₂_of_le B hBΩ le_rfl : B ⊓ pCoreOf 2 K ≤ nineI V K)

theorem conjSubgroup_nineI_le {k : G} (hk : k ∈ K) :
    conjSubgroup (nineI V K) k ≤ nineI V K := by
  unfold nineI
  rw [nineThree_conj_iSup]
  refine iSup_le fun U => ?_
  rw [nineThree_conj_iSup]
  refine iSup_le fun hU => ?_
  have hU' : conjSubgroup U k ∈ omegaIn V K (nineE V K) := conjSubgroup_mem_omegaIn hU hk
  have hle : conjSubgroup (U ⊓ pCoreOf 2 K) k ≤ conjSubgroup U k ⊓ pCoreOf 2 K := by
    rw [E3.conjSubgroup_inf, conjSubgroup_pCoreOf K hk]
  exact hle.trans (le_iSup₂_of_le (conjSubgroup U k) hU' le_rfl)

theorem conjSubgroup_nineI {k : G} (hk : k ∈ K) : conjSubgroup (nineI V K) k = nineI V K := by
  refine le_antisymm (conjSubgroup_nineI_le hk) ?_
  have h1 := E3.conjSubgroup_mono_left k (conjSubgroup_nineI_le (V := V) (K.inv_mem hk))
  rwa [CFSG.Quasithin.conjSubgroup_conjSubgroup, inv_mul_cancel,
    CFSG.Quasithin.conjSubgroup_one] at h1

end Nine3Core

namespace Nine3IFacts

theorem le_normalizer (hI : Nine3IFacts V K S) {B : Subgroup G} (hB : B ∈ nineOmegaIn V K S) :
    nineI V K ≤ normalizer (B : Set G) := by
  have hcomm : ∀ a ∈ nineI V K, ∀ b ∈ B, a * b * a⁻¹ ∈ B := by
    intro a ha b hb
    have h1 : ⁅a, b⁆ ∈ ⁅nineI V K, B⁆ := Subgroup.commutator_mem_commutator ha hb
    rw [hI.comm B hB] at h1
    have h3 : ⁅a, b⁆ * b ∈ B := B.mul_mem h1.1 hb
    simpa [commutatorElement_def, mul_assoc] using h3
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro b
  refine ⟨hcomm a ha b, fun hb => ?_⟩
  have h2 := hcomm a⁻¹ ((nineI V K).inv_mem ha) (a * b * a⁻¹) hb
  simpa [mul_assoc] using h2

theorem commute_inf (h : Nine3Core V T A K S X p) (hI : Nine3IFacts V K S) {B : Subgroup G}
    (hB : B ∈ nineOmegaIn V K S) {a y : G} (ha : a ∈ nineI V K)
    (hy : y ∈ B ⊓ pCoreOf 2 K) : a * y = y * a := by
  rw [← h.nineI_inf_eq hB] at hy
  exact congrArg Subtype.val (hI.abelian.1.is_comm.comm ⟨a, ha⟩ ⟨y, hy.2⟩)

end Nine3IFacts

end CFSG.LocalAnalysis.WeakClosure81

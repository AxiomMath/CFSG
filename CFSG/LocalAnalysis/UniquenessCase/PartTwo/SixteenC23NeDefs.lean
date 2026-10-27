module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23ModA
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsHyp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def c23neQ2 (K₁ K₂ : Subgroup G) : Subgroup G :=
  pCoreOf 2 K₁ ⊔ pCoreOf 2 K₂

@[expose] noncomputable def c23neY (V K₁ K₂ : Subgroup G) : Subgroup G :=
  ⁅V, c23neQ2 K₁ K₂⁆

theorem c23ne_omega_of_generic {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} {x w : G}
    (hwV : w ∈ V) (h₁ : w ∉ wSub V₀ V hV L) (h₂ : w ∉ wSub V₀ V hV (conjSubgroup L x)) :
    mkTil V₀ V hV (IntMod.mk hV ⟨w, hwV⟩) ∈
      c23Omega (wTil V₀ V hV L) (wTil V₀ V hV (conjSubgroup L x)) := by
  unfold c23Omega
  simp only [Set.mem_setOf_eq]
  exact ⟨fun hmem => h₁ ((mem_preTil_iff_of_mem V₀ V hV _ hwV).2 hmem),
    fun hmem => h₂ ((mem_preTil_iff_of_mem V₀ V hV _ hwV).2 hmem)⟩

structure C23NeCtx (D : Data G) (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V) (x : G)
    (K₁ K₂ : Subgroup G) : Prop where
  hxM : x ∈ D.M
  hxn : x ∉ nBar D.M V₀ V hV L
  core : C23Core (wTil V₀ V hV L) (wTil V₀ V hV (conjSubgroup L x)) (barSub V₀ V hV L)
    (barSub V₀ V hV (conjSubgroup L x)) (Mbar D.M V₀ V hV)
  mem₁ : K₁ ∈ calC D.M
  mem₂ : K₂ ∈ calC D.M
  ne : K₁ ≠ K₂
  bar₁ : barSub V₀ V hV K₁ = barSub V₀ V hV L
  bar₂ : barSub V₀ V hV K₂ = barSub V₀ V hV (conjSubgroup L x)
  shape₁ : IsL3 (Bar2 K₁) 1
  shape₂ : IsL3 (Bar2 K₂) 1
  norm₁ : K₁ ≤ normalizer (K₂ : Set G)
  norm₂ : K₂ ≤ normalizer (K₁ : Set G)
  perm : ∀ m ∈ D.M, (conjSubgroup K₁ m = K₁ ∧ conjSubgroup K₂ m = K₂) ∨
    (conjSubgroup K₁ m = K₂ ∧ conjSubgroup K₂ m = K₁)
  cent₀ : K₁ ⊔ K₂ ≤ centralizer (V₀ : Set G)
  ker : F11.CTilde D.M V₀ V ⊓ (K₁ ⊔ K₂) = c23neQ2 K₁ K₂
  q2_pgroup : IsPGroup 2 ↥(c23neQ2 K₁ K₂)

theorem c23ne_M_le_normalizer_sup {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    {x : G} {K₁ K₂ : Subgroup G} (hctx : C23NeCtx D V₀ V L hV x K₁ K₂) :
    D.M ≤ normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) := by
  intro m hm
  have hsup : conjSubgroup (K₁ ⊔ K₂) m = K₁ ⊔ K₂ := by
    unfold conjSubgroup
    rw [Subgroup.map_sup]
    have h := hctx.perm m hm
    unfold conjSubgroup at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, sup_comm]
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [← mem_conjSubgroup_iff, hsup]

@[expose] def C23NeSplit (V₀ V Y KK : Subgroup G) : Prop :=
  ∃ C : Subgroup G, Y ≤ C ∧ C ≤ V ∧ C ⊓ V₀ = Y ∧ C ⊔ V₀ = V ∧
    ∀ k ∈ KK, ∀ c ∈ C, k * c * k⁻¹ ∈ C

structure C23NePair (M V₀ V N₁ N₂ Y : Subgroup G) : Prop where
  elem : IsElemAbelian 2 V
  norm : M ≤ normalizer (V : Set G)
  normV₀ : M ≤ normalizer (V₀ : Set G)
  normY : M ≤ normalizer (Y : Set G)
  le₁ : N₁ ≤ V
  le₂ : N₂ ≤ V
  sup : N₁ ⊔ N₂ = V
  inf : N₁ ⊓ N₂ = V₀
  leY : Y ≤ V₀
  rank_V : mSub V = 8
  rank_N₁ : mSub N₁ = 5
  rank_N₂ : mSub N₂ = 5
  rank_V₀ : mSub V₀ = 2
  rank_Y : mSub Y = 1
  perm : ∀ m ∈ M, (conjSubgroup N₁ m = N₁ ∧ conjSubgroup N₂ m = N₂) ∨
    (conjSubgroup N₁ m = N₂ ∧ conjSubgroup N₂ m = N₁)
  cent : ∀ w ∈ (N₁ : Set G) ∪ (N₂ : Set G), w ≠ 1 → centralizer ({w} : Set G) ≤ M
  oneSided : ∀ t ∈ M, t ^ 2 = 1 → ¬ V ≤ centralizer ({t} : Set G) →
    mSub (commElt V t) ≤ 2 →
      (mSub (commElt V t) = 1 ∧ commElt V t = Y) ∨
      (mSub (commElt V t) = 2 ∧ commElt V t ⊓ Y = ⊥ ∧
        (((∀ y ∈ N₂, t * y = y * t) ∧ commElt V t ≤ N₁) ∨
          ((∀ y ∈ N₁, t * y = y * t) ∧ commElt V t ≤ N₂)))
  rankLe : ∀ E : Subgroup G, E ≤ M → IsElemAbelian 2 E →
    (∀ e ∈ E, e ∈ normalizer (N₁ : Set G)) → (∀ e ∈ E, ∀ y ∈ N₂, e * y = y * e) →
      E3.mQuot E (F11.CTilde M Y V) ≤ 2
  rankLe' : ∀ E : Subgroup G, E ≤ M → IsElemAbelian 2 E →
    (∀ e ∈ E, e ∈ normalizer (N₂ : Set G)) → (∀ e ∈ E, ∀ y ∈ N₁, e * y = y * e) →
      E3.mQuot E (F11.CTilde M Y V) ≤ 2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

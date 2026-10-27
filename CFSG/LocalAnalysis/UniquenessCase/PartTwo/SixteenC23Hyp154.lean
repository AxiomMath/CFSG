module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem c23_wSub_sup_v1Sub_le (D : Data G) {V₀ V L : Subgroup G} (h : Hyp125 D V₀ V)
    (hV : IsElemAbelian 2 V) : wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L ≤ V :=
  sup_le (preTil_le V₀ V hV _) (s15_Infra_v1Sub_le h hV)

theorem c23_third_of_unique₁ (D : Data G) (h22 : R1622 D) {V₀ V L : Subgroup G}
    (h16 : Hyp16 D V₀ V) (h151 : Hyp151 D V₀ V L)
    (hu : ∀ w ∈ wSub V₀ V h151.isElemAbelian L ⊔ v1Sub D.M V₀ V h151.isElemAbelian L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G))) :
    ∀ g : G, g ∉ D.M → ∀ X ∈ wConj D.M V₀ V h151.isElemAbelian L,
      ∀ Y ∈ wConj D.M V₀ V h151.isElemAbelian L, X ≠ Y →
      (X ⊔ Y ⊔ v1Sub D.M V₀ V h151.isElemAbelian L) ⊓
        conjSubgroup (wSub V₀ V h151.isElemAbelian L ⊔ v1Sub D.M V₀ V h151.isElemAbelian L) g
          ≠ ⊥ →
      s15 D.M V₀ V h151.isElemAbelian L = 2 ∧
        delta15 D.M V₀ V h151.isElemAbelian L < gamma15 D.M V₀ V h151.isElemAbelian L - 1 := by
  intro g hg X hX Y hY _hXY hne
  exfalso
  obtain ⟨m, hm, rfl⟩ := hX
  obtain ⟨m', hm', rfl⟩ := hY
  have hXV : conjSubgroup (wSub V₀ V h151.isElemAbelian L) m ≤ V :=
    s15_Tools_conj_wSub_le D h151.hyp125 h151.isElemAbelian hm
  have hYV : conjSubgroup (wSub V₀ V h151.isElemAbelian L) m' ≤ V :=
    s15_Tools_conj_wSub_le D h151.hyp125 h151.isElemAbelian hm'
  have hV1V : v1Sub D.M V₀ V h151.isElemAbelian L ≤ V :=
    s15_Infra_v1Sub_le h151.hyp125 h151.isElemAbelian
  have hWV : wSub V₀ V h151.isElemAbelian L ⊔ v1Sub D.M V₀ V h151.isElemAbelian L ≤ V :=
    c23_wSub_sup_v1Sub_le D h151.hyp125 h151.isElemAbelian
  have hbot : V ⊓ conjSubgroup
      (wSub V₀ V h151.isElemAbelian L ⊔ v1Sub D.M V₀ V h151.isElemAbelian L) g = ⊥ :=
    c23_inf_conjSubgroup_eq_bot D h22 h16 hWV hu hg
  have hXYV : conjSubgroup (wSub V₀ V h151.isElemAbelian L) m ⊔
      conjSubgroup (wSub V₀ V h151.isElemAbelian L) m' ⊔
      v1Sub D.M V₀ V h151.isElemAbelian L ≤ V :=
    sup_le (sup_le hXV hYV) hV1V
  exact hne (le_bot_iff.mp (hbot ▸ inf_le_inf hXYV le_rfl))

private theorem c23_eq_of_mem_pair_of_ne {α : Type*} {A B c a b : α}
    (hc : c ∈ ({A, B} : Set α)) (ha : a ∈ ({A, B} : Set α)) (hb : b ∈ ({A, B} : Set α))
    (hac : a ≠ c) (hbc : b ≠ c) : a = b := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl
  · rfl
  · rfl
  · exact absurd rfl hac
  · exact absurd rfl hbc
  · exact absurd rfl hbc
  · exact absurd rfl hac
  · rfl
  · rfl

theorem c23_unique₂_of_unique₁ (D : Data G) {V₀ V L : Subgroup G} (h151 : Hyp151 D V₀ V L)
    (hs : s15 D.M V₀ V h151.isElemAbelian L = 2)
    (hu : ∀ w ∈ wSub V₀ V h151.isElemAbelian L ⊔ v1Sub D.M V₀ V h151.isElemAbelian L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G))) :
    ∀ x ∈ D.M, ∀ y ∈ D.M,
      ∀ w ∈ v1Sub D.M V₀ V h151.isElemAbelian L ⊔
        ⨆ X ∈ {X | X ∈ wConj D.M V₀ V h151.isElemAbelian L ∧
          X ≠ conjSubgroup (wSub V₀ V h151.isElemAbelian L) x ∧
          X ≠ conjSubgroup (wSub V₀ V h151.isElemAbelian L) y}, X,
      w ≠ 1 → UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  classical
  intro x hx y hy w hw hw1
  let W : Subgroup G := wSub V₀ V h151.isElemAbelian L
  let V₁ : Subgroup G := v1Sub D.M V₀ V h151.isElemAbelian L
  let S : Set (Subgroup G) := {X | X ∈ wConj D.M V₀ V h151.isElemAbelian L ∧
    X ≠ conjSubgroup W x ∧ X ≠ conjSubgroup W y}
  have hcard : (wConj D.M V₀ V h151.isElemAbelian L).ncard = 2 := by
    rw [ncard_wConj D h151 h151.isElemAbelian, hs]
  obtain ⟨A, B, _hAB, hwc⟩ := Set.ncard_eq_two.mp hcard
  have hxwc : conjSubgroup W x ∈ wConj D.M V₀ V h151.isElemAbelian L := ⟨x, hx, rfl⟩
  have hzexists : ∃ z ∈ D.M, ∀ X ∈ S, X = conjSubgroup W z := by
    by_cases hne : S.Nonempty
    · obtain ⟨X₀, hX₀⟩ := hne
      obtain ⟨z, hz, hzX₀⟩ := hX₀.1
      refine ⟨z, hz, fun X hX => ?_⟩
      have hXp : X ∈ ({A, B} : Set (Subgroup G)) := hwc ▸ hX.1
      have hX0p : X₀ ∈ ({A, B} : Set (Subgroup G)) := hwc ▸ hX₀.1
      have hxp : conjSubgroup W x ∈ ({A, B} : Set (Subgroup G)) := hwc ▸ hxwc
      exact (c23_eq_of_mem_pair_of_ne hxp hXp hX0p hX.2.1 hX₀.2.1).trans hzX₀
    · refine ⟨1, D.M.one_mem, fun X hX => ?_⟩
      exact False.elim (hne (show S.Nonempty from ⟨X, hX⟩))
  obtain ⟨z, hz, hzS⟩ := hzexists
  have hsup : (⨆ X ∈ S, X) ≤ conjSubgroup W z :=
    iSup_le fun X => iSup_le fun hX => (hzS X hX).le
  have hsup' : V₁ ⊔ (⨆ X ∈ S, X) ≤ V₁ ⊔ conjSubgroup W z :=
    sup_le le_sup_left (hsup.trans le_sup_right)
  have hv1z : conjSubgroup V₁ z = V₁ :=
    s15_Infra_conjSubgroup_v1Sub h151.hyp125 h151.isElemAbelian hz
  have hconj : conjSubgroup (W ⊔ V₁) z = V₁ ⊔ conjSubgroup W z := by
    have hmap : conjSubgroup (W ⊔ V₁) z = conjSubgroup W z ⊔ conjSubgroup V₁ z := by
      unfold conjSubgroup
      exact Subgroup.map_sup _ _ _
    rw [hmap, hv1z, sup_comm]
  have hle : V₁ ⊔ (⨆ X ∈ S, X) ≤ conjSubgroup (W ⊔ V₁) z := by
    rw [hconj]
    exact hsup'
  have hMz : conjSubgroup D.M z = D.M :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hz)
  have huniq : UniqueMax (conjSubgroup D.M z)
      (conjSubgroup D.M z ⊓ centralizer ({w} : Set G)) :=
    uniqueMax_conjSubgroup_of_mem (M := D.M) (X := W ⊔ V₁) (g := z) (a := w) hu (hle hw) hw1
  rwa [hMz] at huniq

theorem c23_hyp154_of_unique₁ (D : Data G) (h22 : R1622 D) {V₀ V L : Subgroup G}
    (h16 : Hyp16 D V₀ V) (h151 : Hyp151 D V₀ V L)
    (hs : s15 D.M V₀ V h151.isElemAbelian L = 2)
    (hu : ∀ w ∈ wSub V₀ V h151.isElemAbelian L ⊔ v1Sub D.M V₀ V h151.isElemAbelian L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G))) : Hyp154 D V₀ V L :=
  ⟨h151, hu, fun x hx y hy _ => c23_unique₂_of_unique₁ D h151 hs hu x hx y hy,
    c23_third_of_unique₁ D h22 h16 h151 hu⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

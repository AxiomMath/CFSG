module

public import CFSG.RankThree.PartOne.Q1327.Even

public section

namespace CFSG.RankThree.PartOne.Q1327T

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.Q1327
  CFSG.RankThree.PartOne.K1320 CFSG.RankThree.PartOne.K1327
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
  {f r : ℕ} {R : Subgroup G} {s s' zs : MulAut E}

theorem E_le_centralizer_union (H : Hyp G p A c L E f r R s s' zs) {a : G} (haE : a ∈ E) :
    E ≤ Subgroup.centralizer (({a} : Set G) ∪ (R : Set G)) := by
  intro e he
  rw [Subgroup.mem_centralizer_iff]
  rintro y (rfl | hy)
  · exact congrArg Subtype.val (H.h12.E_elem.is_comm.comm (⟨y, haE⟩ : ↥E) ⟨e, he⟩)
  · exact H.hRE y hy e he

theorem exists_N (hS : SchreierFor InCatalog) (H : Hyp G p A c L E f r R s s' zs) {t : MulAut E}
    (ht : t ∈ clsOf p E s) {v : E} (hsv : s v = v) (htv : t v = v) (hnc : s * t ≠ t * s) :
    ∃ N : Subgroup G, N ≤ Subgroup.centralizer (({(v : G)} : Set G) ∪ (R : Set G)) ∧
      N.subgroupOf (Subgroup.centralizer (({(v : G)} : Set G) ∪ (R : Set G))) ∈
        thetaComponents p ↥(Subgroup.centralizer (({(v : G)} : Set G) ∪ (R : Set G))) ∧
      kZero p E s ≤ N ∧ kZero p E t ≤ N := by
  have h := H.h12
  have hp := h.prime
  set M' : Subgroup G := Subgroup.centralizer (({(v : G)} : Set G) ∪ (R : Set G)) with hM'
  have hvE : (v : G) ∈ E := v.2
  have hMM : M' ≤ Subgroup.centralizer (R : Set G) := by
    rw [hM', centralizer_union_eq]
    exact inf_le_left
  have hMne : M' ≠ ⊤ := ne_top_of_le_ne_top (centralizer_R_ne_top H) hMM
  have hKM : ∀ H' : Subgroup G, H' ≤ M' → CFSG.IsKGroup ↥H' :=
    fun H' hH' => h.setup.2.2.1 H' (ne_top_of_le_ne_top hMne hH')
  have hEM : E ≤ M' := E_le_centralizer_union H hvE
  have hcls : s ∈ clsOf p E s := mem_clsOf_self p E s
  have key : ∀ u ∈ clsOf p E s, u v = v → ∃ J ∈ thetaComponents p ↥M',
      (kZero p E u).subgroupOf M' ≤ J ∧ kZero p E u ≤ M' := by
    intro u hu huv
    obtain ⟨-, hKu, -, hKuM⟩ := class_facts H (Or.inl rfl) hu
    have hvfix : (v : G) ∈ autFixedInG E u := ⟨v, huv, rfl⟩
    have hKM' : kZero p E u ≤ M' := by
      intro x hx
      rw [hM', Subgroup.mem_centralizer_iff]
      rintro y (rfl | hy)
      · exact Subgroup.mem_centralizer_iff.1 (kZero_le_centralizer_fixed p E u hx) _ hvfix
      · exact Subgroup.mem_centralizer_iff.1 (hKuM hx) y hy
    have hq : CFSG.IsQuasisimple ↥(kZero p E u) := (KFAt.toLiftAt hKu).1
    have hDM : autFixedInG E u ≤ M' := (Subgroup.map_subtype_le _).trans hEM
    have hDel : IsElementaryAbelian p ↥(autFixedInG E u) :=
      isElementaryAbelian_of_le' h.E_elem (Subgroup.map_subtype_le _)
    obtain ⟨J, hJ, hKJ⟩ := exists_thetaComponent_ge hp h.three_lt hS hKM h.evenRank_eq.le
      (Nat.card ↥(autFixedInG E u)) (autFixedInG E u) hDM rfl hDel (kZero p E u)
      (le_inf hKM' (kZero_le_centralizer_fixed p E u))
      (kZero_mem_thetaComponents_inf hp hq hKM')
    exact ⟨J, hJ, hKJ, hKM'⟩
  obtain ⟨J₁, hJ₁, hKJ₁, hKM₁⟩ := key s hcls hsv
  obtain ⟨J₂, hJ₂, hKJ₂, hKM₂⟩ := key t ht htv
  have hJeq : J₁ = J₂ := by
    by_contra hne
    obtain ⟨-, hKs, -, -⟩ := class_facts H (Or.inl rfl) hcls
    obtain ⟨-, hKt, -, -⟩ := class_facts H (Or.inl rfl) ht
    obtain ⟨-, -, -, -, k, hk, hkK, hks⟩ := hKs
    obtain ⟨-, -, -, -, k', hk', hkK', hkt⟩ := hKt
    set I₁ : Subgroup G := J₁.map M'.subtype with hI₁
    set I₂ : Subgroup G := J₂.map M'.subtype with hI₂
    have hI₁M : I₁ ≤ M' := Subgroup.map_subtype_le _
    have hI₂M : I₂ ≤ M' := Subgroup.map_subtype_le _
    have h1 : I₁.subgroupOf M' = J₁ :=
      Subgroup.comap_map_eq_self_of_injective M'.subtype_injective _
    have h2 : I₂.subgroupOf M' = J₂ :=
      Subgroup.comap_map_eq_self_of_injective M'.subtype_injective _
    have hk₁ : k ∈ I₁ := ⟨⟨k, hKM₁ hkK⟩, hKJ₁ (Subgroup.mem_subgroupOf.mpr hkK), rfl⟩
    have hk₂ : k' ∈ I₂ := ⟨⟨k', hKM₂ hkK'⟩, hKJ₂ (Subgroup.mem_subgroupOf.mpr hkK'), rfl⟩
    have hcomm := commute_of_distinct_components_M hp h.E_elem hEM
      (I₁ := I₁) (I₂ := I₂) (by rw [h1]; exact hJ₁) (by rw [h2]; exact hJ₂)
      (by rw [h1, h2]; exact hne) hI₁M hI₂M hk₁ hk₂ hk hk'
    rw [hks, hkt] at hcomm
    exact hnc hcomm
  subst hJeq
  refine ⟨J₁.map M'.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · have : (J₁.map M'.subtype).subgroupOf M' = J₁ :=
      Subgroup.comap_map_eq_self_of_injective M'.subtype_injective _
    rw [this]
    exact hJ₁
  · intro x hx
    exact ⟨⟨x, hKM₁ hx⟩, hKJ₁ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  · intro x hx
    exact ⟨⟨x, hKM₂ hx⟩, hKJ₂ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

end CFSG.RankThree.PartOne.Q1327T

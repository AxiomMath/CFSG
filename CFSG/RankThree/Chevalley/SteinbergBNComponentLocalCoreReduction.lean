module

public import CFSG.RankThree.PartOne.KC.PlaneReduction

public section

namespace CFSG.RankThree.Chevalley

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.RankThree CFSG.RankThree.GroupTheory
open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne
open scoped Pointwise

@[expose] def LocalCoreTrivialOn (p : ℕ) {T : Type*} [Group T] (P : MulAut T → Prop) : Prop :=
  ∀ B : Subgroup (MulAut T), (MulAut.conj : T →* MulAut T).range ≤ B →
    ∀ α ∈ B, P α → orderOf α = p →
      inSubgroup (aschbacherSolvableCore p) (B ⊓ centralizer ({α} : Set (MulAut T))) = ⊥

theorem localCoreTrivialOn_of_forall {p : ℕ} (hp : p.Prime) {T : Type*} [Group T] [Finite T]
    {P : MulAut T → Prop}
    (h : ∀ B : Subgroup (MulAut T), (MulAut.conj : T →* MulAut T).range ≤ B →
      ∀ α : B, P α → orderOf α = p →
        aschbacherSolvableCore p (centralizer {α} : Subgroup B) = ⊥) :
    LocalCoreTrivialOn p P := by
  intro B hB α hαB hα hαp
  have h1 := h B hB ⟨α, hαB⟩ hα (by rw [← Subgroup.orderOf_coe]; exact hαp)
  rw [← map_subtype_theta_centralizer hp B ⟨α, hαB⟩, inSubgroup, h1, Subgroup.map_bot,
    Subgroup.map_bot]

theorem LocalCoreTrivialOn.of_mulEquiv {p : ℕ} (hp : p.Prime) {T T' : Type*} [Group T]
    [Group T'] [Finite T] (e : T ≃* T') {P : MulAut T → Prop} {P' : MulAut T' → Prop}
    (hP : ∀ α, P α → P' (MulAut.congr e α)) (h : LocalCoreTrivialOn p P') :
    LocalCoreTrivialOn p P := by
  intro B hB α hαB hα hαp
  set φ := MulAut.congr e
  have h1 := h (B.map φ.toMonoidHom)
    (by rw [← map_conj_range_mulAutCongr e]; exact Subgroup.map_mono hB) (φ α)
    (Subgroup.mem_map_of_mem _ hαB) (hP α hα)
    ((orderOf_injective φ.toMonoidHom φ.injective α).trans hαp)
  rw [← map_inSubgroup_theta_centralizer_mulEquiv hp φ B α] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).mp h1

theorem mulAutCongr_not_mem_range_conj {T T' : Type*} [Group T] [Group T'] (e : T ≃* T')
    {α : MulAut T} (hα : α ∉ (MulAut.conj : T →* MulAut T).range) :
    MulAut.congr e α ∉ (MulAut.conj : T' →* MulAut T').range := by
  intro h
  rw [← map_conj_range_mulAutCongr e] at h
  obtain ⟨γ, hγ, hγα⟩ := Subgroup.mem_map.mp h
  exact hα (by rwa [← (MulAut.congr e).injective hγα])

theorem component_local_core_product_centralizes_of_localCoreTrivialOn {G : Type*} [Group G]
    [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup G}
    (hE : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2) {t : G} (ht : t ∈ E)
    (ht1 : t ≠ 1) {L : Subgroup G} (hL : IsComponent L) (hEL : E ≤ normalizer (L : Set G))
    (hSL : inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)) ≤
      normalizer (L : Set G))
    {P : MulAut (L ⧸ center L) → Prop} (hcore : LocalCoreTrivialOn p P)
    (hP : P (Finkelstein1977.automizer L ⟨t, hEL ht⟩)) :
    ((⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔ thetaT p E :
        Subgroup G) : Set G) =
      ((⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ : Subgroup G) :
        Set G) * (thetaT p E : Set G) ∧
      ⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔ thetaT p E ≤
        centralizer (L : Set G) := by
  have := hE
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨(SteinbergBY.section_nine_residual_to_intersection hp hp2 E).1 t ht ht1, ?_⟩
  set S := inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)) with hS
  by_cases hCEL : E ⊓ centralizer (L : Set G) = ⊥
  · obtain ⟨hker, -, hInn, -, -, hEbar, -, htbar, -, hWJ, -, hmap⟩ :=
      SteinbergBM.faithful_component_local_core_almost_simple_image hp hp2 hE hEcard ht ht1 hL
        hEL hSL hCEL
    have hJN : L ⊔ S ⊔ E ≤ normalizer (L : Set G) := sup_le (sup_le le_normalizer hSL) hEL
    set J := L ⊔ S ⊔ E with hJ
    set π : J →* MulAut (L ⧸ center L) := (Finkelstein1977.automizer L).comp (inclusion hJN)
      with hπ
    set B := π.range with hB
    set Ebar : Subgroup B := (E.subgroupOf J).map π.rangeRestrict with hEbar_def
    set tbar : B := π.rangeRestrict ⟨t, mem_sup_right ht⟩ with htbar_def
    set W := ⁅S, E⁆ ⊔ thetaT p E with hW
    have htbarE : tbar ∈ Ebar :=
      Subgroup.mem_map.mpr ⟨⟨t, mem_sup_right ht⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
    have htbarp : orderOf tbar = p := by
      have hp1 : tbar ^ p = 1 := by
        have := hEbar
        exact elemPow_eq_one_of_isElementaryAbelian (p := p) (A := Ebar) tbar htbarE
      exact orderOf_eq_prime hp1 htbar
    have htbar' : ((tbar : B) : MulAut (L ⧸ center L)) =
        Finkelstein1977.automizer L ⟨t, hEL ht⟩ := rfl
    have hθ := hcore B hInn (tbar : MulAut (L ⧸ center L)) tbar.2 (htbar' ▸ hP)
      (by rw [Subgroup.orderOf_coe]; exact htbarp)
    have hθB : inSubgroup (aschbacherSolvableCore p) (centralizer ({tbar} : Set B)) = ⊥ := by
      rw [← map_subtype_theta_centralizer hp B tbar] at hθ
      exact (Subgroup.map_eq_bot_iff_of_injective _ B.subtype_injective).mp hθ
    have hWbar : (⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({tbar} : Set B)), Ebar⁆ ⊔
        thetaT p Ebar : Subgroup B) = ⊥ := by
      rw [hθB, Subgroup.commutator_bot_left, bot_sup_eq, eq_bot_iff]
      intro x hx
      simp only [thetaT, Subgroup.mem_iInf] at hx
      rw [← hθB]
      exact hx tbar htbarE htbar
    have hWker : (W.subgroupOf J).map π.rangeRestrict = ⊥ := le_bot_iff.mp (hWbar ▸ hmap)
    have hker' : π.ker.map J.subtype = J ⊓ centralizer (L : Set G) := hker
    intro w hw
    have hwJ : (⟨w, hWJ hw⟩ : J) ∈ π.rangeRestrict.ker := by
      have : π.rangeRestrict ⟨w, hWJ hw⟩ ∈ (W.subgroupOf J).map π.rangeRestrict :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hw)
      rw [hWker, Subgroup.mem_bot] at this
      exact this
    rw [MonoidHom.ker_rangeRestrict] at hwJ
    have h2 : w ∈ π.ker.map J.subtype := Subgroup.mem_map_of_mem _ hwJ
    rw [hker'] at h2
    exact h2.2
  · obtain ⟨-, -, hWL⟩ :=
      CFSG.RankThree.Coprime.nonfaithful_plane_local_core_product_centralizes_component hp hE
        hEcard ht ht1 hL (commutator_le_normalizer_of_le hSL hEL) hCEL
    exact commutator_eq_bot_iff_le_centralizer.mp hWL

theorem noninner_component_local_core_product_centralizes {G : Type*} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup G} (hE : IsElementaryAbelian p E)
    (hEcard : Nat.card E = p ^ 2) {t : G} (ht : t ∈ E) (ht1 : t ≠ 1) {L : Subgroup G}
    (hL : IsComponent L) (hEL : E ≤ normalizer (L : Set G))
    (hSL : inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)) ≤
      normalizer (L : Set G))
    {T : Type*} [Group T] (e : T ≃* L ⧸ center L)
    (hcore : LocalCoreTrivialOn p fun α : MulAut T => α ∉ (MulAut.conj : T →* MulAut T).range)
    (hnon : Finkelstein1977.automizer L ⟨t, hEL ht⟩ ∉
      (MulAut.conj : L ⧸ center L →* MulAut (L ⧸ center L)).range) :
    ((⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔ thetaT p E :
        Subgroup G) : Set G) =
      ((⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ : Subgroup G) :
        Set G) * (thetaT p E : Set G) ∧
      ⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔ thetaT p E ≤
        centralizer (L : Set G) :=
  component_local_core_product_centralizes_of_localCoreTrivialOn hp hp2 hE hEcard ht ht1 hL hEL
    hSL (P := fun α => α ∉ (MulAut.conj : L ⧸ center L →* MulAut (L ⧸ center L)).range)
    (hcore.of_mulEquiv hp e.symm fun _ hα => mulAutCongr_not_mem_range_conj e.symm hα) hnon

end CFSG.RankThree.Chevalley

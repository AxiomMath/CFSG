module

public import CFSG.RankThree.PartOne.KC.PlaneReduction

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.RankThree CFSG.RankThree.GroupTheory
  CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

@[expose] def PlaneLocalCoreBot (p : ℕ) (T : Type*) [Group T]
    (P : Subgroup (MulAut T) → Prop) : Prop :=
  ∀ B : Subgroup (MulAut T), (MulAut.conj : T →* MulAut T).range ≤ B →
    ∀ A : Subgroup (MulAut T), A ≤ B → IsElementaryAbelian p A → Nat.card A = p ^ 2 → P A →
      ∀ t ∈ A, t ≠ 1 → autPlaneProduct p B A t = ⊥

@[expose] def PlaneDivides (p : ℕ) (T : Type*) [Group T] (n : ℕ) : Prop :=
  ∀ B : Subgroup (MulAut T), (MulAut.conj : T →* MulAut T).range ≤ B →
    ∀ A : Subgroup (MulAut T), A ≤ B → IsElementaryAbelian p A → Nat.card A = p ^ 2 → p ∣ n

@[expose] def PlaneLocalCoreOddIf (p : ℕ) (T : Type*) [Group T]
    (P : Subgroup (MulAut T) → Prop) : Prop :=
  ∀ B : Subgroup (MulAut T), (MulAut.conj : T →* MulAut T).range ≤ B →
    ∀ A : Subgroup (MulAut T), A ≤ B → IsElementaryAbelian p A → Nat.card A = p ^ 2 → P A →
      ∀ t ∈ A, t ≠ 1 → ¬ 2 ∣ Nat.card (autPlaneProduct p B A t)

theorem PlaneLocalCoreBot.of_mulEquiv {T T' : Type*} [Group T] [Group T'] [Finite T] {p : ℕ}
    (hp : p.Prime) (e : T ≃* T') {P' : Subgroup (MulAut T') → Prop}
    (h : PlaneLocalCoreBot p T' P') :
    PlaneLocalCoreBot p T (fun A => P' (A.map (MulAut.congr e).toMonoidHom)) := by
  intro B hB A hAB hA hAcard hPA t htA ht1
  have : Fact p.Prime := ⟨hp⟩
  have := hA
  set φ := MulAut.congr e with hφ
  have h1 := h (B.map φ.toMonoidHom)
    (by rw [← map_conj_range_mulAutCongr e]; exact Subgroup.map_mono hB)
    (A.map φ.toMonoidHom) (Subgroup.map_mono hAB) (IsElementaryAbelian.map φ.toMonoidHom)
    (by rw [Subgroup.card_map_of_injective φ.injective, hAcard]) hPA (φ t)
    (Subgroup.mem_map_of_mem _ htA) (fun h1 => ht1 (φ.injective (by simpa using h1)))
  rw [← map_autPlaneProduct_mulEquiv hp φ] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective (autPlaneProduct p B A t) (f := φ.toMonoidHom)
    φ.injective).mp h1

theorem PlaneLocalCoreOddIf.of_mulEquiv {T T' : Type*} [Group T] [Group T'] [Finite T] {p : ℕ}
    (hp : p.Prime) (e : T ≃* T') {P' : Subgroup (MulAut T') → Prop}
    (h : PlaneLocalCoreOddIf p T' P') :
    PlaneLocalCoreOddIf p T (fun A => P' (A.map (MulAut.congr e).toMonoidHom)) := by
  intro B hB A hAB hA hAcard hPA t htA ht1
  have : Fact p.Prime := ⟨hp⟩
  have := hA
  set φ := MulAut.congr e with hφ
  have h1 := h (B.map φ.toMonoidHom)
    (by rw [← map_conj_range_mulAutCongr e]; exact Subgroup.map_mono hB)
    (A.map φ.toMonoidHom) (Subgroup.map_mono hAB) (IsElementaryAbelian.map φ.toMonoidHom)
    (by rw [Subgroup.card_map_of_injective φ.injective, hAcard]) hPA (φ t)
    (Subgroup.mem_map_of_mem _ htA) (fun h1 => ht1 (φ.injective (by simpa using h1)))
  rw [← map_autPlaneProduct_mulEquiv hp φ, Subgroup.card_map_of_injective φ.injective] at h1
  exact h1

theorem PlaneDivides.of_mulEquiv {T T' : Type*} [Group T] [Group T'] [Finite T] {p n : ℕ}
    (hp : p.Prime) (e : T ≃* T') (h : PlaneDivides p T' n) : PlaneDivides p T n := by
  intro B hB A hAB hA hAcard
  have : Fact p.Prime := ⟨hp⟩
  have := hA
  set φ := MulAut.congr e with hφ
  exact h (B.map φ.toMonoidHom)
    (by rw [← map_conj_range_mulAutCongr e]; exact Subgroup.map_mono hB)
    (A.map φ.toMonoidHom) (Subgroup.map_mono hAB) (IsElementaryAbelian.map φ.toMonoidHom)
    (by rw [Subgroup.card_map_of_injective φ.injective, hAcard])

theorem faithful_plane_data {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {E : Subgroup G} (hE : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2)
    {t : G} (ht : t ∈ E) (ht1 : t ≠ 1) {L : Subgroup G} (hL : IsComponent L)
    (hEL : E ≤ normalizer (L : Set G))
    (hSL : inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)) ≤
      normalizer (L : Set G))
    (hCEL : E ⊓ centralizer (L : Set G) = ⊥) :
    ∃ (B A : Subgroup (MulAut (L ⧸ center L))) (t' : MulAut (L ⧸ center L)),
      (MulAut.conj : L ⧸ center L →* MulAut (L ⧸ center L)).range ≤ B ∧ A ≤ B ∧
      IsElementaryAbelian p A ∧ Nat.card A = p ^ 2 ∧ t' ∈ A ∧ t' ≠ 1 ∧
      A = actualPlane L E ∧
      (autPlaneProduct p B A t' = ⊥ →
        (⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔
          thetaT p E) ≤ centralizer (L : Set G)) ∧
      (¬ 2 ∣ Nat.card (autPlaneProduct p B A t') →
        (⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔
          thetaT p E) ≤ normalizer (L : Set G) ∧
        ¬ 2 ∣ (centralizer (L : Set G)).relIndex
          (⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔
            thetaT p E)) := by
  have hBM := SteinbergBM.faithful_component_local_core_almost_simple_image hp hp2 hE hEcard ht
    ht1 hL hEL hSL hCEL
  obtain ⟨hker, hsolv, hInn, hFit, hIso, hEbar, hEbarcard, htbar, hWset, hWJ, hWbarset, hmap⟩ :=
    hBM
  set S := inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)) with hS
  have hJN : L ⊔ S ⊔ E ≤ normalizer (L : Set G) := sup_le (sup_le le_normalizer hSL) hEL
  set J := L ⊔ S ⊔ E with hJ
  set π : J →* MulAut (L ⧸ center L) := (Finkelstein1977.automizer L).comp (inclusion hJN)
    with hπ
  set B := π.range with hB
  set Ebar : Subgroup B := (E.subgroupOf J).map π.rangeRestrict with hEbar_def
  set tbar : B := π.rangeRestrict ⟨t, mem_sup_right ht⟩ with htbar_def
  set W := ⁅S, E⁆ ⊔ thetaT p E with hW
  have hEJ : E ≤ J := le_sup_right
  have hplaneEq : Ebar.map B.subtype = actualPlane L E := by
    ext x
    simp only [hEbar_def, actualPlane, Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨y, ⟨j, hj, rfl⟩, rfl⟩
      exact ⟨⟨(j : G), hJN j.2⟩, hj, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨π.rangeRestrict ⟨n, hEJ hn⟩, ⟨⟨n, hEJ hn⟩, hn, rfl⟩, rfl⟩
  have hA' : IsElementaryAbelian p (Ebar.map B.subtype) := by
    have : Fact p.Prime := ⟨hp⟩
    have := hEbar
    exact IsElementaryAbelian.map_subtype
  have hA'card : Nat.card (Ebar.map B.subtype) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective B.subtype_injective]; exact hEbarcard
  have htA' : (tbar : MulAut (L ⧸ center L)) ∈ Ebar.map B.subtype := by
    refine Subgroup.mem_map.mpr ⟨tbar, ?_, rfl⟩
    exact Subgroup.mem_map.mpr ⟨⟨t, mem_sup_right ht⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
  have ht'1 : (tbar : MulAut (L ⧸ center L)) ≠ 1 := fun h => htbar (Subtype.ext h)
  have hle := map_subtype_planeProduct_le hp B Ebar tbar
  have hJN' : W ≤ normalizer (L : Set G) := hWJ.trans hJN
  refine ⟨B, Ebar.map B.subtype, tbar, hInn, Subgroup.map_subtype_le _, hA', hA'card, htA', ht'1,
    hplaneEq, ?_, ?_⟩
  swap
  · intro hodd
    refine ⟨hJN', ?_⟩
    have hWbar_odd : ¬ 2 ∣ Nat.card (⁅inSubgroup (aschbacherSolvableCore p)
        (centralizer ({tbar} : Set B)), Ebar⁆ ⊔ thetaT p Ebar : Subgroup B) := by
      intro h2
      apply hodd
      have h3 := Subgroup.card_dvd_of_le hle
      rw [Subgroup.card_map_of_injective B.subtype_injective] at h3
      exact h2.trans h3
    have himg : ¬ 2 ∣ Nat.card ((W.subgroupOf J).map π.rangeRestrict) := fun h2 =>
      hWbar_odd (h2.trans (Subgroup.card_dvd_of_le hmap))
    have hrel : (centralizer (L : Set G)).relIndex W =
        Nat.card ((W.subgroupOf J).map π.rangeRestrict) := by
      have h1 : π.rangeRestrict.ker.relIndex (W.subgroupOf J) =
          Nat.card ((W.subgroupOf J).map π.rangeRestrict) := by
        rw [← MonoidHom.comap_bot, Subgroup.relIndex_comap, Subgroup.relIndex_bot_left]
      have hker' : π.ker.map J.subtype = J ⊓ centralizer (L : Set G) := hker
      rw [← h1, MonoidHom.ker_rangeRestrict,
        ← Subgroup.relIndex_map_map_of_injective π.ker (W.subgroupOf J) J.subtype_injective,
        hker', Subgroup.map_subgroupOf_eq_of_le hWJ, relIndex_inf_left_of_le hWJ]
    rw [hrel]
    exact himg
  intro hbot
  have hWbar_bot : (⁅inSubgroup (aschbacherSolvableCore p)
      (centralizer ({tbar} : Set B)), Ebar⁆ ⊔ thetaT p Ebar : Subgroup B) = ⊥ := by
    have h1 : (⁅inSubgroup (aschbacherSolvableCore p)
      (centralizer ({tbar} : Set B)), Ebar⁆ ⊔ thetaT p Ebar : Subgroup B).map B.subtype = ⊥ :=
      le_bot_iff.mp (hbot ▸ hle)
    exact (Subgroup.map_eq_bot_iff_of_injective _ B.subtype_injective).mp h1
  have hWker : (W.subgroupOf J).map π.rangeRestrict = ⊥ := le_bot_iff.mp (hWbar_bot ▸ hmap)
  have hker' : π.ker.map J.subtype = J ⊓ centralizer (L : Set G) := hker
  intro w hw
  have hwJ : (⟨w, hWJ hw⟩ : J) ∈ π.rangeRestrict.ker := by
    have : π.rangeRestrict ⟨w, hWJ hw⟩ ∈ (W.subgroupOf J).map π.rangeRestrict :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hw)
    rw [hWker, Subgroup.mem_bot] at this
    exact this
  rw [MonoidHom.ker_rangeRestrict] at hwJ
  have : w ∈ π.ker.map J.subtype := Subgroup.mem_map_of_mem _ hwJ
  rw [hker'] at this
  exact this.2

theorem plane_reduction_bot {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {E : Subgroup G} (hE : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2)
    {t : G} (ht : t ∈ E) (ht1 : t ≠ 1) {L : Subgroup G} (hL : IsComponent L)
    (hEL : E ≤ normalizer (L : Set G))
    (hSL : inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)) ≤
      normalizer (L : Set G))
    (hCEL : E ⊓ centralizer (L : Set G) = ⊥)
    {P : Subgroup (MulAut (L ⧸ center L)) → Prop}
    (hplane : PlaneLocalCoreBot p (L ⧸ center L) P) (hP : P (actualPlane L E)) :
    (⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔ thetaT p E) ≤
      centralizer (L : Set G) := by
  obtain ⟨B, A, t', hB, hAB, hA, hAcard, ht'A, ht'1, hAE, hcent, -⟩ :=
    faithful_plane_data hp hp2 hE hEcard ht ht1 hL hEL hSL hCEL
  exact hcent (hplane B hB A hAB hA hAcard (hAE ▸ hP) t' ht'A ht'1)

theorem plane_reduction_division {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {E : Subgroup G} (hE : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2)
    {t : G} (ht : t ∈ E) (ht1 : t ≠ 1) {L : Subgroup G} (hL : IsComponent L)
    (hEL : E ≤ normalizer (L : Set G))
    (hSL : inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)) ≤
      normalizer (L : Set G))
    (hCEL : E ⊓ centralizer (L : Set G) = ⊥) {n : ℕ}
    (hplane : PlaneDivides p (L ⧸ center L) n) : p ∣ n := by
  obtain ⟨B, A, t', hB, hAB, hA, hAcard, -⟩ :=
    faithful_plane_data hp hp2 hE hEcard ht ht1 hL hEL hSL hCEL
  exact hplane B hB A hAB hA hAcard

theorem plane_reduction_odd_if {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {E : Subgroup G} (hE : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2)
    {t : G} (ht : t ∈ E) (ht1 : t ≠ 1) {L : Subgroup G} (hL : IsComponent L)
    (hEL : E ≤ normalizer (L : Set G))
    (hSL : inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)) ≤
      normalizer (L : Set G))
    (hCEL : E ⊓ centralizer (L : Set G) = ⊥)
    {P : Subgroup (MulAut (L ⧸ center L)) → Prop}
    (hplane : PlaneLocalCoreOddIf p (L ⧸ center L) P) (hP : P (actualPlane L E)) :
    (⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔ thetaT p E) ≤
        normalizer (L : Set G) ∧
      ¬ 2 ∣ (centralizer (L : Set G)).relIndex
        (⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔
          thetaT p E) := by
  obtain ⟨B, A, t', hB, hAB, hA, hAcard, ht'A, ht'1, hAE, -, hodd⟩ :=
    faithful_plane_data hp hp2 hE hEcard ht ht1 hL hEL hSL hCEL
  exact hodd (hplane B hB A hAB hA hAcard (hAE ▸ hP) t' ht'A ht'1)

theorem component_local_core_odd_action_of_plane_if {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup G} (hE : IsElementaryAbelian p E)
    (hEcard : Nat.card E = p ^ 2) {t : G} (ht : t ∈ E) (ht1 : t ≠ 1) {L : Subgroup G}
    (hL : IsComponent L) (hEL : E ≤ normalizer (L : Set G))
    (hSL : inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)) ≤
      normalizer (L : Set G))
    {P : Subgroup (MulAut (L ⧸ center L)) → Prop}
    (hplane : PlaneLocalCoreOddIf p (L ⧸ center L) P)
    (hP : E ⊓ centralizer (L : Set G) ≠ ⊥ ∨ P (actualPlane L E)) :
    ((((⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔
        thetaT p E : Subgroup G)) : Set G) =
      ((⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ : Subgroup G) :
        Set G) * (thetaT p E : Set G)) ∧
    (⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔ thetaT p E) ≤
        normalizer (L : Set G) ∧
      ¬ 2 ∣ (centralizer (L : Set G)).relIndex
        (⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔ thetaT p E) ∧
    CFSG.Quasithin.twoPrimeResidual
        (⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔
          thetaT p E) ≤ centralizer (L : Set G) ∧
    (E ⊓ centralizer (L : Set G) ≠ ⊥ →
      (⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔ thetaT p E) ≤
        centralizer (L : Set G)) := by
  have hset := (SteinbergBY.section_nine_residual_to_intersection hp hp2 E).1 t ht ht1
  by_cases hC : E ⊓ centralizer (L : Set G) = ⊥
  · obtain ⟨hWN, hodd⟩ := plane_reduction_odd_if hp hp2 hE hEcard ht ht1 hL hEL hSL hC hplane
      (hP.resolve_left (not_not.mpr hC))
    exact ⟨hset, hWN, hodd, twoPrimeResidual_le_centralizer_of_odd_relIndex hWN hodd,
      fun h => absurd hC h⟩
  · have hXL := commutator_le_normalizer_of_le hSL hEL
    have hcent := (Coprime.nonfaithful_plane_local_core_product_centralizes_component hp hE
      hEcard ht ht1 hL hXL hC).2.2
    have hWC := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcent
    have hWN : (⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔
        thetaT p E) ≤ normalizer (L : Set G) := hWC.trans
          (Subgroup.centralizer_le_normalizer (L : Set G))
    have hodd : ¬ 2 ∣ (centralizer (L : Set G)).relIndex
        (⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔
          thetaT p E) := by
      rw [Subgroup.relIndex_eq_one.mpr hWC]
      omega
    exact ⟨hset, hWN, hodd, twoPrimeResidual_le_centralizer_of_odd_relIndex hWN hodd,
      fun _ => hWC⟩

end CFSG.RankThree.PartOne

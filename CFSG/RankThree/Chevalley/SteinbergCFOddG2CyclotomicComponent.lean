module

public import CFSG.RankThree.PartOne.KC.PlaneReduction
public import CFSG.RankThree.Chevalley.SteinbergCFOddG2CyclotomicLocalCore
public import CFSG.RankThree.Chevalley.EvenRealThreeCentralizingInvolution

public section

namespace CFSG.RankThree.Chevalley

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.RankThree CFSG.RankThree.GroupTheory
open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped Pointwise

@[expose] def PlaneLocalCoreOddAt (p : ℕ) (T : Type*) [Group T] (Q : MulAut T → Prop) : Prop :=
  ∀ B : Subgroup (MulAut T), (MulAut.conj : T →* MulAut T).range ≤ B →
    ∀ A : Subgroup (MulAut T), A ≤ B → IsElementaryAbelian p A → Nat.card A = p ^ 2 →
      ∀ t ∈ A, t ≠ 1 → Q t → ¬ 2 ∣ Nat.card (autPlaneProduct p B A t)

theorem PlaneLocalCoreOddAt.of_mulEquiv {T T' : Type*} [Group T] [Group T'] [Finite T] {p : ℕ}
    (hp : p.Prime) (e : T ≃* T') {Q' : MulAut T' → Prop} (h : PlaneLocalCoreOddAt p T' Q') :
    PlaneLocalCoreOddAt p T fun t => Q' (MulAut.congr e t) := by
  intro B hB A hAB hA hAcard t htA ht1 hQ
  have : Fact p.Prime := ⟨hp⟩
  have := hA
  set φ := MulAut.congr e with hφ
  have h1 := h (B.map φ.toMonoidHom)
    (by rw [← map_conj_range_mulAutCongr e]; exact Subgroup.map_mono hB)
    (A.map φ.toMonoidHom) (Subgroup.map_mono hAB) (IsElementaryAbelian.map φ.toMonoidHom)
    (by rw [Subgroup.card_map_of_injective φ.injective, hAcard]) (φ t)
    (Subgroup.mem_map_of_mem _ htA) (fun h1 => ht1 (φ.injective (by simpa using h1))) hQ
  rw [← map_autPlaneProduct_mulEquiv hp φ, Subgroup.card_map_of_injective φ.injective] at h1
  exact h1

theorem autThetaT_eq_map_thetaT {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    (B : Subgroup M) (A : Subgroup B) {t : B} (htA : t ∈ A) (ht1 : t ≠ 1) :
    autThetaT p B (A.map B.subtype) = (thetaT p A).map B.subtype := by
  refine le_antisymm (fun x hx => ?_) (map_subtype_thetaT_le hp B A)
  simp only [autThetaT, Subgroup.mem_iInf] at hx
  have hxt := hx (t : M) (Subgroup.mem_map_of_mem _ htA) (fun h => ht1 (Subtype.ext h))
  rw [← map_subtype_theta_centralizer hp B t] at hxt
  obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hxt
  refine Subgroup.mem_map_of_mem _ ?_
  simp only [thetaT, Subgroup.mem_iInf]
  intro b hbA hb1
  have h1 := hx (b : M) (Subgroup.mem_map_of_mem _ hbA) (fun h => hb1 (Subtype.ext h))
  rw [← map_subtype_theta_centralizer hp B b] at h1
  obtain ⟨y', hy', hyy'⟩ := Subgroup.mem_map.1 h1
  have hy : y' = y := Subtype.ext hyy'
  rwa [hy] at hy'

theorem plane_reduction_odd_at {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {E : Subgroup G} (hE : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2)
    {t : G} (ht : t ∈ E) (ht1 : t ≠ 1) {L : Subgroup G} (hL : IsComponent L)
    (hEL : E ≤ normalizer (L : Set G))
    (hSL : inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)) ≤
      normalizer (L : Set G))
    (hCEL : E ⊓ centralizer (L : Set G) = ⊥) {Q : MulAut (L ⧸ center L) → Prop}
    (hplane : PlaneLocalCoreOddAt p (L ⧸ center L) Q)
    (hQ : Q (Finkelstein1977.automizer L ⟨t, hEL ht⟩)) :
    (⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔ thetaT p E) ≤
        normalizer (L : Set G) ∧
      ¬ 2 ∣ (centralizer (L : Set G)).relIndex
        (⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔ thetaT p E) := by
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
  have hWN : W ≤ normalizer (L : Set G) := hWJ.trans hJN
  refine ⟨hWN, ?_⟩
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
  have hodd := hplane B hInn (Ebar.map B.subtype) (Subgroup.map_subtype_le _) hA' hA'card _
    htA' ht'1 hQ
  have hle := map_subtype_planeProduct_le hp B Ebar tbar
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

theorem component_local_core_odd_action_of_plane_at {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup G} (hE : IsElementaryAbelian p E)
    (hEcard : Nat.card E = p ^ 2) {t : G} (ht : t ∈ E) (ht1 : t ≠ 1) {L : Subgroup G}
    (hL : IsComponent L) (hEL : E ≤ normalizer (L : Set G))
    (hSL : inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)) ≤
      normalizer (L : Set G)) {Q : MulAut (L ⧸ center L) → Prop}
    (hplane : PlaneLocalCoreOddAt p (L ⧸ center L) Q)
    (hQ : Q (Finkelstein1977.automizer L ⟨t, hEL ht⟩)) :
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
  · obtain ⟨hWN, hodd⟩ := plane_reduction_odd_at hp hp2 hE hEcard ht ht1 hL hEL hSL hC hplane hQ
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

theorem planeLocalCoreOddAt_G2_cyclotomic {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3)
    (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f) (ε : ℤ) (hε : ε = -1 ∨ ε = 1)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + ε * Nat.card K + 1) :
    PlaneLocalCoreOddAt p (adjointGroup .G2 K) fun α =>
      α ∈ (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range := by
  intro B hB A hAB hA hAcard t htA ht1 hinn
  have : Fact p.Prime := ⟨hp⟩
  have := hA
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : Finite (Module.End K (RootModule .G2 K)) := Module.finite_of_finite K
  have hE : IsElementaryAbelian p (A.subgroupOf B) := IsElementaryAbelian.subgroupOf hAB
  have hEcard : Nat.card (A.subgroupOf B) = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv, hAcard]
  have ht'E : (⟨t, hAB htA⟩ : B) ∈ A.subgroupOf B := Subgroup.mem_subgroupOf.2 htA
  have ht'1 : (⟨t, hAB htA⟩ : B) ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  obtain ⟨-, -, -, hodd⟩ := odd_G2_cyclotomic_three_six_inner_actor_local_core_product_odd hℓ
    hℓ2 hℓ3 hf K hK ε hε hp hp3 hpq B hB (A.subgroupOf B) hE hEcard ⟨t, hAB htA⟩ ht'E ht'1 hinn
  have hAE : (A.subgroupOf B).map B.subtype = A := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hAB]
  have heq : autPlaneProduct p B A t = (⁅inSubgroup (aschbacherSolvableCore p)
      (centralizer ({(⟨t, hAB htA⟩ : B)} : Set B)), A.subgroupOf B⁆ ⊔
        thetaT p (A.subgroupOf B)).map B.subtype := by
    rw [Subgroup.map_sup, Subgroup.map_commutator, map_subtype_theta_centralizer hp B,
      ← autThetaT_eq_map_thetaT hp B (A.subgroupOf B) ht'E ht'1, hAE]
    rfl
  rw [heq, Subgroup.card_map_of_injective B.subtype_injective]
  exact hodd.not_two_dvd_nat


theorem odd_G2_cyclotomic_three_six_inner_actor_actual_component_odd_action {G : Type}
    [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {E : Subgroup G}
    (hE : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2) {t : G} (ht : t ∈ E)
    (ht1 : t ≠ 1) {L : Subgroup G} (hL : IsComponent L) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) (ε : ℤ) (hε : ε = -1 ∨ ε = 1)
    (hpq : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * (ℓ ^ f : ℕ) + 1)
    (hT : ChevalleyExceptionalModel (L ⧸ center L) .G2 ℓ f)
    (hEL : E ≤ normalizer (L : Set G))
    (hSL : inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)) ≤
      normalizer (L : Set G)) :
    (Finkelstein1977.automizer L ⟨t, hEL ht⟩ ∈
        (MulAut.conj : L ⧸ center L →* MulAut (L ⧸ center L)).range →
      ((⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔ thetaT p E :
          Subgroup G) : Set G) =
        ((⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ :
          Subgroup G) : Set G) * (thetaT p E : Set G) ∧
      ⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔ thetaT p E ≤
        normalizer (L : Set G) ∧
      ¬ 2 ∣ (centralizer (L : Set G)).relIndex
        (⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔ thetaT p E)) ∧
    (E ⊓ centralizer (L : Set G) ≠ ⊥ →
      ⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔ thetaT p E ≤
        centralizer (L : Set G)) := by
  have hp2 : p ≠ 2 := by omega
  refine ⟨fun hinn => ?_, fun hC => ?_⟩
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup_of_untwisted hT.2
    have hpqK : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + ε * Nat.card K + 1 := by
      rw [hK]
      exact hpq
    have hplane := (planeLocalCoreOddAt_G2_cyclotomic hℓ hℓ2 hℓ3 hf K hK ε hε hp hp3
      hpqK).of_mulEquiv hp e.symm
    have hQ : MulAut.congr e.symm (Finkelstein1977.automizer L ⟨t, hEL ht⟩) ∈
        (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range := by
      obtain ⟨x, hx⟩ := hinn
      rw [← hx, mulAutCongr_conj]
      exact ⟨_, rfl⟩
    obtain ⟨hset, hWN, hodd, -, -⟩ :=
      component_local_core_odd_action_of_plane_at hp hp2 hE hEcard ht ht1 hL hEL hSL hplane hQ
    exact ⟨hset, hWN, hodd⟩
  · have hXL := commutator_le_normalizer_of_le hSL hEL
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (Coprime.nonfaithful_plane_local_core_product_centralizes_component hp hE hEcard ht ht1 hL
        hXL hC).2.2

end CFSG.RankThree.Chevalley

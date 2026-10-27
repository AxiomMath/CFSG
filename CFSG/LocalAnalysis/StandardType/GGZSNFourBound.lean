module

public import CFSG.Certificates.CosetTablePresented
public import CFSG.LocalAnalysis.StandardType.GGZSNFourInputs
public import Certificates.Certificate709543
import all CFSG.LocalAnalysis.StandardType.GGZSHallSoicherBound
public import Mathlib

public section

namespace CFSG.StandardType.ZS

open CFSG.CosetTable

theorem exists_mulEquiv_of_words_of_mem_normal {G H : Type*} [Group G] [Group H] {m N : ℕ}
    {ws : List (List (Fin m × Bool))} (hfin : Finite (PG m ws)) (hN : Nat.card (PG m ws) ≤ N)
    {r : Fin m → G} {s : Fin m → H} (hr : ∀ w ∈ ws, FreeGroup.lift r (FreeGroup.mk w) = 1)
    (hs : ∀ w ∈ ws, FreeGroup.lift s (FreeGroup.mk w) = 1)
    (hG : Subgroup.closure (Set.range r) = ⊤) (hH : Subgroup.closure (Set.range s) = ⊤)
    (hcG : N ≤ Nat.card G) {z : FreeGroup (Fin m)}
    (hz : ∀ K : Subgroup G, K.Normal → K ≠ ⊥ → FreeGroup.lift r z ∈ K)
    (hzs : FreeGroup.lift s z ≠ 1) : ∃ e : G ≃* H, ∀ i, e (r i) = s i := by
  have : Finite (PG m ws) := hfin
  let φ : PG m ws →* G := PresentedGroup.toGroup (rels_of_words hr)
  let ψ : PG m ws →* H := PresentedGroup.toGroup (rels_of_words hs)
  have hsurjφ : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top]
    exact (range_toGroup hr).trans hG
  have hsurjψ : Function.Surjective ψ := by
    rw [← MonoidHom.range_eq_top]
    exact (range_toGroup hs).trans hH
  have hbijφ : Function.Bijective φ :=
    hsurjφ.bijective_of_nat_card_le (hN.trans hcG)
  have hKnormal : ψ.ker.Normal := inferInstance
  have hKmap : (ψ.ker.map φ).Normal := hKnormal.map φ hsurjφ
  have hK : ψ.ker = ⊥ := by
    by_contra hne
    have hKmapne : ψ.ker.map φ ≠ ⊥ := by
      intro hbot
      exact hne ((Subgroup.map_eq_bot_iff_of_injective (H := ψ.ker) (f := φ)
        hbijφ.1).mp hbot)
    have hmem : FreeGroup.lift r z ∈ ψ.ker.map φ := hz _ hKmap hKmapne
    rw [Subgroup.mem_map] at hmem
    obtain ⟨k, hkK, hk⟩ := hmem
    have hφmk : φ (PresentedGroup.mk {ρ : FreeGroup (Fin m) | ρ ∈ ws.map FreeGroup.mk} z) =
        FreeGroup.lift r z := rfl
    have hkz : k = PresentedGroup.mk {ρ : FreeGroup (Fin m) | ρ ∈ ws.map FreeGroup.mk} z :=
      hbijφ.1 (hk.trans hφmk.symm)
    have hmemK : ψ (PresentedGroup.mk {ρ : FreeGroup (Fin m) | ρ ∈ ws.map FreeGroup.mk} z) = 1 := by
      rw [← MonoidHom.mem_ker, ← hkz]
      exact hkK
    have hψmk : ψ (PresentedGroup.mk {ρ : FreeGroup (Fin m) | ρ ∈ ws.map FreeGroup.mk} z) =
        FreeGroup.lift s z := rfl
    exact hzs (hψmk.symm.trans hmemK)
  have hinjψ : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hK
  let eG : PG m ws ≃* G := MulEquiv.ofBijective φ hbijφ
  let eH : PG m ws ≃* H := MulEquiv.ofBijective ψ ⟨hinjψ, hsurjψ⟩
  refine ⟨eG.symm.trans eH, fun i => ?_⟩
  have hGof : eG (PresentedGroup.of i) = r i := by
    change (PresentedGroup.toGroup (rels_of_words hr)) (PresentedGroup.of i) = r i
    rw [PresentedGroup.toGroup.of]
  have hHof : eH (PresentedGroup.of i) = s i := by
    change (PresentedGroup.toGroup (rels_of_words hs)) (PresentedGroup.of i) = s i
    rw [PresentedGroup.toGroup.of]
  rw [MulEquiv.trans_apply, ← hGof, MulEquiv.symm_apply_apply]
  exact hHof

private theorem lift_posWord {G : Type*} [Group G] {m : ℕ} (r : Fin m → G) (l : List (Fin m)) :
    FreeGroup.lift r (FreeGroup.mk (posWord l)) = (l.map r).prod := by
  rw [posWord, FreeGroup.lift_mk]
  simp [List.map_map, Function.comp_def]

private theorem lift_eq_one_of_n4Rel {G : Type*} [Group G] {r : Fin 4 → G}
    (h : N4Rel r) : ∀ w ∈ n4Rels, FreeGroup.lift r (FreeGroup.mk w) = 1 := by
  change (∀ i j, (r i * r j) ^ nFourExp i j = 1) ∧ (n4Extra.map r).prod = 1 at h
  obtain ⟨hpair, hextra⟩ := h
  intro w hw
  simp only [n4Rels, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filter,
    List.mem_finRange, decide_eq_true_eq, true_and, List.mem_singleton] at hw
  rcases hw with ⟨i, -, j, -, rfl⟩ | rfl
  · rw [lift_pairPowWord, hpair]
  · rw [lift_posWord]
    simpa using hextra

private theorem lift_eq_one_of_en4Rel {G : Type*} [Group G] {r : Fin 5 → G}
    (h : EN4Rel r) : ∀ w ∈ en4Rels, FreeGroup.lift r (FreeGroup.mk w) = 1 := by
  change (∀ i j, (r i * r j) ^ enFourExp i j = 1) ∧
    ((n4Extra.map Fin.castSucc).map r).prod = 1 ∧ (en4Extra.map r).prod = 1 at h
  obtain ⟨hpair, hextra1, hextra2⟩ := h
  intro w hw
  simp only [en4Rels, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filter,
    List.mem_finRange, decide_eq_true_eq, true_and, List.mem_cons,
    List.mem_nil_iff, or_false] at hw
  rcases hw with ⟨i, -, j, -, rfl⟩ | rfl | rfl
  · rw [lift_pairPowWord, hpair]
  · rw [lift_posWord]
    simpa using hextra1
  · rw [lift_posWord]
    simpa using hextra2

private theorem card_le_of_n4Rels :
    Finite (PG 4 n4Rels) ∧ Nat.card (PG 4 n4Rels) ≤ 7680 :=
  Certificates.certificate709543.1

private theorem card_le_of_en4Rels :
    Finite (PG 5 en4Rels) ∧ Nat.card (PG 5 en4Rels) ≤ 46080 :=
  Certificates.certificate709543.2

theorem card_closure_le_of_n4Rel {G : Type*} [Group G]
    {r : Fin 4 → G} (h : N4Rel r) : Nat.card (Subgroup.closure (Set.range r)) ≤ 7680 := by
  obtain ⟨hfin, hN⟩ := card_le_of_n4Rels
  exact card_closure_le_of_words hfin hN (lift_eq_one_of_n4Rel h)

theorem card_closure_le_of_en4Rel {G : Type*} [Group G]
    {r : Fin 5 → G} (h : EN4Rel r) : Nat.card (Subgroup.closure (Set.range r)) ≤ 46080 := by
  obtain ⟨hfin, hN⟩ := card_le_of_en4Rels
  exact card_closure_le_of_words hfin hN (lift_eq_one_of_en4Rel h)

theorem exists_mulEquiv_of_n4Rel {G H : Type*} [Group G]
    [Group H] {r : Fin 4 → G} {s : Fin 4 → H} (hr : N4Rel r) (hs : N4Rel s)
    (hG : Subgroup.closure (Set.range r) = ⊤) (hH : Subgroup.closure (Set.range s) = ⊤)
    (hcG : 7680 ≤ Nat.card G) (hz : ∀ K : Subgroup G, K.Normal → K ≠ ⊥ → (n4ZW.map r).prod ∈ K)
    (hzs : (n4ZW.map s).prod ≠ 1) : ∃ e : G ≃* H, ∀ i, e (r i) = s i := by
  obtain ⟨hfin, hN⟩ := card_le_of_n4Rels
  refine exists_mulEquiv_of_words_of_mem_normal (ws := n4Rels) (N := 7680)
    (z := FreeGroup.mk (posWord n4ZW)) hfin hN ?_ ?_ hG hH hcG ?_ ?_
  · exact lift_eq_one_of_n4Rel hr
  · exact lift_eq_one_of_n4Rel hs
  · intro K hK hne
    simpa only [lift_posWord] using hz K hK hne
  · simpa only [lift_posWord] using hzs

theorem exists_mulEquiv_of_en4Rel {G H : Type*} [Group G]
    [Group H] {r : Fin 5 → G} {s : Fin 5 → H} (hr : EN4Rel r) (hs : EN4Rel s)
    (hG : Subgroup.closure (Set.range r) = ⊤) (hH : Subgroup.closure (Set.range s) = ⊤)
    (hcG : 46080 ≤ Nat.card G)
    (hz : ∀ K : Subgroup G, K.Normal → K ≠ ⊥ → (en4ZW.map r).prod ∈ K)
    (hzs : (en4ZW.map s).prod ≠ 1) : ∃ e : G ≃* H, ∀ i, e (r i) = s i := by
  obtain ⟨hfin, hN⟩ := card_le_of_en4Rels
  refine exists_mulEquiv_of_words_of_mem_normal (ws := en4Rels) (N := 46080)
    (z := FreeGroup.mk (posWord en4ZW)) hfin hN ?_ ?_ hG hH hcG ?_ ?_
  · exact lift_eq_one_of_en4Rel hr
  · exact lift_eq_one_of_en4Rel hs
  · intro K hK hne
    simpa only [lift_posWord] using hz K hK hne
  · simpa only [lift_posWord] using hzs

end CFSG.StandardType.ZS

end

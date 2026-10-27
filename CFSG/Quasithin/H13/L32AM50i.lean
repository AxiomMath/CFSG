module

public import CFSG.Quasithin.H13.L32AC49d
public import CFSG.Quasithin.H13.L32AC50b

public section

namespace CFSG.Quasithin.H13.L32A.C.Alt7

open Equiv Equiv.Perm

theorem orbit6_cases : ∀ O : Finset (Fin 7), 6 ∈ O → O.card ∣ 72 →
    taList.all (fun t => decide (∀ i ∈ O, t i ∈ O)) = true → O = {6} ∨ O = d3 := by
  decide +kernel

theorem card_filter_six : (Finset.univ.filter fun σ : Perm (Fin 7) =>
    sign σ = 1 ∧ σ 6 = 6).card = 360 := by
  decide +kernel

@[expose] noncomputable def liftSix : Perm (Fin 6) →* Perm (Fin 7) :=
  Equiv.Perm.viaEmbeddingHom (Fin.castSuccEmb : Fin 6 ↪ Fin 7)

theorem liftSix_injective : Function.Injective liftSix :=
  Equiv.Perm.viaEmbeddingHom_injective (Fin.castSuccEmb : Fin 6 ↪ Fin 7)

theorem sign_liftSix (σ : Perm (Fin 6)) : sign (liftSix σ) = sign σ := by
  classical
  rw [liftSix, Equiv.Perm.viaEmbeddingHom_apply, Equiv.Perm.viaEmbedding]
  convert Equiv.Perm.sign_extendDomain σ
    (Equiv.ofInjective (Fin.castSuccEmb : Fin 6 ↪ Fin 7).1 (Fin.castSuccEmb : Fin 6 ↪ Fin 7).2)

theorem liftSix_apply_six (σ : Perm (Fin 6)) : liftSix σ 6 = 6 := by
  classical
  show Equiv.Perm.viaEmbedding σ (Fin.castSuccEmb : Fin 6 ↪ Fin 7) 6 = 6
  apply Equiv.Perm.viaEmbedding_apply_of_notMem
  rintro ⟨i, hi⟩
  have := i.2
  have h6 : ((Fin.castSuccEmb : Fin 6 ↪ Fin 7) i : ℕ) = i := rfl
  rw [hi] at h6
  simp at h6
  omega

theorem exists_liftSix {n : Perm (Fin 7)} (hn : sign n = 1) (h6 : n 6 = 6) :
    ∃ σ : Alt6.A6, liftSix σ = n := by
  classical
  set F := Finset.univ.filter fun σ : Perm (Fin 7) => sign σ = 1 ∧ σ 6 = 6 with hF
  have hmaps : ∀ σ : Alt6.A6, liftSix σ ∈ F := fun σ => by
    rw [hF, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (sign_liftSix σ).trans (mem_alternatingGroup.mp σ.2),
      liftSix_apply_six σ⟩
  set f : Alt6.A6 → ↥F := fun σ => ⟨liftSix σ, hmaps σ⟩ with hf
  have hinj : Function.Injective f := fun a b hab =>
    Subtype.ext (liftSix_injective (congrArg Subtype.val hab))
  have hcard : Nat.card ↥F ≤ Nat.card Alt6.A6 := by
    rw [Alt6.card_A6, Nat.card_eq_fintype_card, Fintype.card_coe, card_filter_six]
  obtain ⟨σ, hσ⟩ := (hinj.bijective_of_nat_card_le hcard).2
    ⟨n, by rw [hF, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hn, h6⟩⟩
  exact ⟨σ, congrArg Subtype.val hσ⟩

theorem false_of_fix_six {N : Subgroup (Perm (Fin 7))} (hNA : N ≤ alternatingGroup (Fin 7))
    (h6 : ∀ n ∈ N, n 6 = 6) (h72 : Nat.card N = 72) : False := by
  set φ : Alt6.A6 →* Perm (Fin 7) := liftSix.comp (alternatingGroup (Fin 6)).subtype with hφ
  have hφi : Function.Injective φ := liftSix_injective.comp Subtype.val_injective
  set Y : Subgroup Alt6.A6 := N.comap φ with hY
  have hmap : Y.map φ = N := by
    rw [hY, Subgroup.map_comap_eq]
    refine inf_eq_right.mpr fun n hn => ?_
    obtain ⟨σ, hσ⟩ := exists_liftSix (mem_alternatingGroup.mp (hNA hn)) (h6 n hn)
    exact ⟨σ, hσ⟩
  have hYc : Nat.card Y = 72 := by
    rw [← h72, ← hmap, Subgroup.card_map_of_injective hφi]
  have hidx : Y.index = 5 := by
    have := Y.card_mul_index
    rw [hYc, Alt6.card_A6] at this
    omega
  have hne : Y ≠ ⊤ := by
    intro h
    rw [h, Subgroup.index_top] at hidx
    omega
  have := Alt6.six_le_index hne
  omega

theorem eq_stabSub_of_card {N : Subgroup (Perm (Fin 7))} (hNA : N ≤ alternatingGroup (Fin 7))
    (hT : taSub ≤ N) (h72 : Nat.card N = 72) : N = stabSub := by
  classical
  set O : Finset (Fin 7) := (MulAction.orbit N (6 : Fin 7)).toFinset with hO
  have hmemO : ∀ i, i ∈ O ↔ ∃ n ∈ N, n 6 = i := by
    intro i
    rw [hO, Set.mem_toFinset, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, n.2, hn⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n, hn⟩, rfl⟩
  have h6O : (6 : Fin 7) ∈ O := (hmemO 6).mpr ⟨1, N.one_mem, rfl⟩
  have hdvd : O.card ∣ 72 := by
    rw [hO, ← Set.ncard_eq_toFinset_card', ← MulAction.index_stabilizer, ← h72]
    exact Subgroup.index_dvd_card _
  have hNO : ∀ n ∈ N, ∀ i ∈ O, n i ∈ O := by
    intro n hn i hi
    obtain ⟨m, hm, rfl⟩ := (hmemO i).mp hi
    exact (hmemO _).mpr ⟨n * m, N.mul_mem hn hm, rfl⟩
  have hall : taList.all (fun t => decide (∀ i ∈ O, t i ∈ O)) = true :=
    List.all_eq_true.mpr fun t ht => decide_eq_true (hNO t (hT (mem_listSub.mpr ht)))
  rcases orbit6_cases O h6O hdvd hall with h | h
  · exfalso
    refine false_of_fix_six hNA (fun n hn => ?_) h72
    have := hNO n hn 6 h6O
    rwa [h, Finset.mem_singleton] at this
  · refine Subgroup.eq_of_le_of_card_ge (fun n hn => ?_) (by rw [h72, card_stabSub])
    rw [mem_stabSub]
    refine ⟨mem_alternatingGroup.mp (hNA hn), fun i hi => ?_⟩
    rw [← h] at hi ⊢
    exact hNO n hn i hi

end CFSG.Quasithin.H13.L32A.C.Alt7

module

public import CFSG.Quasithin.Vol2.Ch3xC58NSEmbA7b
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin.C58NS.Emb

open Equiv

theorem fixSet_eq_of_conj {H D : Subgroup (Perm (Fin 7))} [IsSimpleGroup H]
    (hH : Nat.card H = 60) (hHA : H ≤ alternatingGroup (Fin 7))
    (hDA : D ≤ alternatingGroup (Fin 7)) (hD : Nat.card D = 8)
    (hDN : D ≤ Subgroup.normalizer (H : Set (Perm (Fin 7)))) {g : Perm (Fin 7)}
    (hg : g⁻¹ * sigma4 * g ∈ D) : fixSet H = {g⁻¹ 4, g⁻¹ 5} := by
  classical
  obtain ⟨i, hi, hcard⟩ := exists_orbit_eq_compl_fixSet hH
  have hsum := Set.ncard_add_ncard_compl (fixSet H)
  rw [← hi, Nat.card_eq_fintype_card, Fintype.card_fin] at hsum
  rcases hcard with h5 | h6
  · obtain ⟨p, q, hpq, hfix⟩ := Set.ncard_eq_two.mp (by omega : (fixSet H).ncard = 2)
    have hd := hDN hg
    have hpF : p ∈ fixSet H := by rw [hfix]; exact Or.inl rfl
    have hqF : q ∈ fixSet H := by rw [hfix]; exact Or.inr rfl
    have h1 := mem_fixSet_of_mem_normalizer hd hpF
    have h2 := mem_fixSet_of_mem_normalizer hd hqF
    rw [hfix] at h1 h2
    have key : ∀ x y : Fin 7, (g⁻¹ * sigma4 * g) x = y ↔ sigma4 (g x) = g y := by
      intro x y
      simp only [Perm.mul_apply]
      constructor
      · intro h; rw [← h]; simp
      · intro h; rw [h]; simp
    have hgpq : g p ≠ g q := fun h => hpq (g.injective h)
    have ha : sigma4 (g p) = g p ∨ sigma4 (g p) = g q := by
      rcases h1 with h | h
      · exact Or.inl ((key p p).mp h)
      · exact Or.inr ((key p q).mp h)
    have hb : sigma4 (g q) = g p ∨ sigma4 (g q) = g q := by
      rcases h2 with h | h
      · exact Or.inl ((key q p).mp h)
      · exact Or.inr ((key q q).mp h)
    rw [hfix]
    rcases sigma4_pair (g p) (g q) hgpq ha hb with ⟨hp4, hq5⟩ | ⟨hp5, hq4⟩
    · have hp' : p = g⁻¹ 4 := by rw [← hp4]; simp
      have hq' : q = g⁻¹ 5 := by rw [← hq5]; simp
      rw [hp', hq']
    · have hp' : p = g⁻¹ 5 := by rw [← hp5]; simp
      have hq' : q = g⁻¹ 4 := by rw [← hq4]; simp
      rw [hp', hq', Set.pair_comm]
  · exfalso
    obtain ⟨p, hp⟩ := Set.ncard_eq_one.mp (by omega : (fixSet H).ncard = 1)
    exact false_of_fixSet_eq_singleton hH hHA hDA hD hDN hp

theorem eq_of_normalized {H B D : Subgroup (Perm (Fin 7))} [IsSimpleGroup H] [IsSimpleGroup B]
    (hH : Nat.card H = 60) (hB : Nat.card B = 60) (hHA : H ≤ alternatingGroup (Fin 7))
    (hBA : B ≤ alternatingGroup (Fin 7)) (hDA : D ≤ alternatingGroup (Fin 7))
    (hD : Nat.card D = 8) (hDH : D ≤ Subgroup.normalizer (H : Set (Perm (Fin 7))))
    (hDB : D ≤ Subgroup.normalizer (B : Set (Perm (Fin 7)))) : H = B := by
  obtain ⟨g, -, hg⟩ := exists_conj_sigma4_mem hDA hD
  have h45 : g⁻¹ 4 ≠ g⁻¹ 5 := fun h => absurd (g⁻¹.injective h) (by decide)
  rw [eq_map_alt_of_fixSet hH hHA h45 (fixSet_eq_of_conj hH hHA hDA hD hDH hg),
    eq_map_alt_of_fixSet hB hBA h45 (fixSet_eq_of_conj hB hBA hDA hD hDB hg)]

theorem eq_of_normalized_of_equiv {Γ : Type*} [Group Γ] [Finite Γ] {L A B D : Subgroup Γ}
    (eL : ↥L ≃* alternatingGroup (Fin 7)) (hAL : A ≤ L) (hBL : B ≤ L)
    (eA : ↥A ≃* alternatingGroup (Fin 5)) (eB : ↥B ≃* alternatingGroup (Fin 5))
    (hD : CFSG.QuasithinUnique.IsSylowTwoOf D L)
    (hDA : D ≤ Subgroup.normalizer (A : Set Γ)) (hDB : D ≤ Subgroup.normalizer (B : Set Γ)) :
    A = B := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ : ↥L →* Perm (Fin 7) := (alternatingGroup (Fin 7)).subtype.comp eL.toMonoidHom with hφ
  have hφi : Function.Injective φ :=
    (alternatingGroup (Fin 7)).subtype_injective.comp eL.injective
  have hrange : ∀ K : Subgroup ↥L, K.map φ ≤ alternatingGroup (Fin 7) := by
    rintro K _ ⟨k, -, rfl⟩
    exact (eL k).2
  have hcardL : Nat.card L = 2520 := by
    rw [Nat.card_congr eL.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    decide
  have hcard5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  have hmapc : ∀ {K : Subgroup Γ}, K ≤ L → Nat.card ((K.subgroupOf L).map φ) = Nat.card K := by
    intro K hK
    rw [Subgroup.card_map_of_injective hφi]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv
  have hmapN : ∀ {K : Subgroup Γ}, D ≤ Subgroup.normalizer (K : Set Γ) →
      (D.subgroupOf L).map φ ≤
        Subgroup.normalizer (((K.subgroupOf L).map φ : Subgroup (Perm (Fin 7))) :
          Set (Perm (Fin 7))) := by
    intro K hK
    refine le_trans (Subgroup.map_mono ?_) (Subgroup.le_normalizer_map φ)
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using (Subgroup.mem_normalizer_iff.mp (hK (Subgroup.mem_subgroupOf.mp hd))) (x : Γ)
  have hsimp : ∀ {K : Subgroup Γ}, K ≤ L → ↥K ≃* alternatingGroup (Fin 5) →
      IsSimpleGroup ((K.subgroupOf L).map φ) := by
    intro K hK eK
    have e : ↥((K.subgroupOf L).map φ) ≃* alternatingGroup (Fin 5) :=
      ((Subgroup.equivMapOfInjective _ φ hφi).symm.trans
        (Subgroup.subgroupOfEquivOfLe hK)).trans eK
    exact (MulEquiv.isSimpleGroup_congr e).2 inferInstance
  have hDcard : Nat.card D = 8 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hD.2.1
    have hmul := Subgroup.card_mul_index (D.subgroupOf L)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD.1).toEquiv, hk, hcardL] at hmul
    have hodd := hD.2.2
    have hk3 : k ≤ 3 := by
      by_contra hk4
      have h16 : 2 ^ 4 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
      have : 2 ^ 4 ∣ 2520 := h16.trans (Dvd.intro _ hmul)
      norm_num at this
    rw [hk]
    interval_cases k <;> simp only [pow_succ, pow_zero, one_mul] at hmul ⊢ <;> omega
  have : IsSimpleGroup ((A.subgroupOf L).map φ) := hsimp hAL eA
  have : IsSimpleGroup ((B.subgroupOf L).map φ) := hsimp hBL eB
  have key := eq_of_normalized (D := (D.subgroupOf L).map φ)
    (by rw [hmapc hAL, Nat.card_congr eA.toEquiv, hcard5])
    (by rw [hmapc hBL, Nat.card_congr eB.toEquiv, hcard5]) (hrange _) (hrange _) (hrange _)
    (by rw [hmapc hD.1, hDcard]) (hmapN hDA) (hmapN hDB)
  have h1 := Subgroup.map_injective hφi key
  rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr hAL, inf_eq_left.mpr hBL] at h1
  exact h1

end CFSG.Quasithin.C58NS.Emb

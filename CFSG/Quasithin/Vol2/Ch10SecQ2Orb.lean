module

public import CFSG.Quasithin.Vol2.Ch10SecQ2Int
public import CFSG.Quasithin.Vol2.Ch10SecQ2Sym

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE.C10P02

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G]

@[expose, instance_reducible] def conjAction (N : Subgroup G) : MulAction ↥N (Subgroup G) where
  smul x B := cjSub (x : G) B
  one_smul B := by
    change cjSub ((1 : ↥N) : G) B = B
    ext y
    simp [mem_cjSub]
  mul_smul x y B := by
    change cjSub ((x * y : ↥N) : G) B = cjSub (x : G) (cjSub (y : G) B)
    ext z
    simp [mem_cjSub, mul_assoc]

theorem cjSub_mul (x y : G) (B : Subgroup G) : cjSub (x * y) B = cjSub x (cjSub y B) := by
  ext z
  simp [mem_cjSub, mul_assoc]

theorem cjSub_one (B : Subgroup G) : cjSub 1 B = B := by
  ext z
  simp [mem_cjSub]

theorem cjSub_eq_iff {g : G} {V : Subgroup G} :
    cjSub g V = V ↔ g ∈ Subgroup.normalizer (V : Set G) :=
  Subgroup.mem_normalizer_iff_map_conj_eq.symm

variable [Finite G]

@[expose] noncomputable def orbF (N V : Subgroup G) : Finset (Subgroup G) :=
  (Set.toFinite {B : Subgroup G | ∃ x ∈ N, cjSub x V = B}).toFinset

theorem mem_orbF {N V B : Subgroup G} : B ∈ orbF N V ↔ ∃ x ∈ N, cjSub x V = B := by
  unfold orbF
  rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]

theorem self_mem_orbF (N V : Subgroup G) : V ∈ orbF N V :=
  mem_orbF.mpr ⟨1, N.one_mem, cjSub_one V⟩

theorem cjSub_mem_orbF {N V B : Subgroup G} {x : G} (hx : x ∈ N) (hB : B ∈ orbF N V) :
    cjSub x B ∈ orbF N V := by
  obtain ⟨y, hy, rfl⟩ := mem_orbF.mp hB
  exact mem_orbF.mpr ⟨x * y, N.mul_mem hx hy, cjSub_mul x y V⟩

theorem card_orbF (N V : Subgroup G) :
    (orbF N V).card = (Subgroup.normalizer (V : Set G)).relIndex N := by
  let _ := conjAction N
  have h1 := MulAction.index_stabilizer (↥N) V
  have hO : MulAction.orbit (↥N) V = {B : Subgroup G | ∃ x ∈ N, cjSub x V = B} := by
    ext B
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hS : MulAction.stabilizer (↥N) V = (Subgroup.normalizer (V : Set G)).subgroupOf N := by
    ext x
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, ← cjSub_eq_iff]
    rfl
  rw [hS, hO] at h1
  unfold orbF
  rw [← Set.ncard_eq_toFinset_card _ (Set.toFinite _), ← h1]
  rfl

theorem odd_card_orbF {N V T : Subgroup G} (hTN : T ≤ N)
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) (hT : ¬ 2 ∣ T.index) : Odd (orbF N V).card := by
  rw [card_orbF, ← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro h
  apply hT
  have h1 : (Subgroup.normalizer (V : Set G)).relIndex N ∣ T.relIndex N :=
    Subgroup.relIndex_dvd_of_le_left N hTV
  exact (h.trans h1).trans (Subgroup.relIndex_dvd_index_of_le hTN)

variable {T L I : Subgroup G} {hyp : Hyp10 G T L I} {t : G} (D : Case2Data hyp t)

theorem props_of_mem_orbF {V : Subgroup G} (hVS : V ≤ baum T) (hV : IsElemAbelian 2 V)
    {B : Subgroup G} (hB : B ∈ orbF (Subgroup.normalizer (baum T : Set G)) V) :
    B ≤ baum T ∧ IsElemAbelian 2 B ∧ Nat.card B = Nat.card V := by
  obtain ⟨x, hx, rfl⟩ := mem_orbF.mp hB
  exact ⟨cjSub_le hx hVS, isElemAbelian_cjSub hV, card_cjSub x _⟩

theorem card_filter_gam_eq {g : Subgroup.normalizer (fsuVM T L I : Set G)}
    (hgN : (g : G) ∈ Subgroup.normalizer (baum T : Set G)) {i j : Fin 4}
    (hij : convI (SecA.isElemAbelian_fsuVM hyp) g * D.tau i *
      (convI (SecA.isElemAbelian_fsuVM hyp) g)⁻¹ = D.tau j) :
    ((orbF (Subgroup.normalizer (baum T : Set G)) (fsuVM T L I)).filter
        fun B => i ∈ gam D B).card =
      ((orbF (Subgroup.normalizer (baum T : Set G)) (fsuVM T L I)).filter
        fun B => j ∈ gam D B).card := by
  refine Finset.card_nbij' (cjSub (g : G)) (cjSub (g : G)⁻¹) ?_ ?_ ?_ ?_
  · intro B hB
    rw [Finset.mem_coe, Finset.mem_filter] at hB ⊢
    exact ⟨cjSub_mem_orbF hgN hB.1, (mem_gam_cjSub_iff D g.2 hij B).mpr hB.2⟩
  · intro B hB
    rw [Finset.mem_coe, Finset.mem_filter] at hB ⊢
    refine ⟨cjSub_mem_orbF (inv_mem hgN) hB.1, ?_⟩
    rw [← mem_gam_cjSub_iff D g.2 hij, cjSub_cjSub_inv]
    exact hB.2
  · intro B _
    exact cjSub_inv_cjSub _ _
  · intro B _
    exact cjSub_cjSub_inv _ _

theorem card_symmDiff_cjSub (hC0 : T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥)
    (hCV : T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) ≤ fsuVM T L I)
    {q : Fin 4 → Subgroup.normalizer (fsuVM T L I : Set G)} (hqT : ∀ i, (q i : G) ∈ T)
    (hq2 : ∀ i, (q i : G) ^ 2 = 1) (hqc : ∀ i j, (q i : G) * q j = q j * q i)
    (hqτ : ∀ i, convI (SecA.isElemAbelian_fsuVM hyp) (q i) = D.tau i)
    {x : G} (hx : x ∈ Subgroup.normalizer (baum T : Set G)) {B B' : Subgroup G}
    (hBS : B ≤ baum T) (hB : IsElemAbelian 2 B) (hcard : Nat.card B = Nat.card (fsuVM T L I))
    (hB'S : B' ≤ baum T) (hB' : IsElemAbelian 2 B')
    (hcard' : Nat.card B' = Nat.card (fsuVM T L I)) :
    (symmDiff (gam D (cjSub x B)) (gam D (cjSub x B'))).card =
      (symmDiff (gam D B) (gam D B')).card := by
  have e1 := card_inf_mul_pow D hC0 hCV hqT hq2 hqc hqτ (cjSub_le hx hBS) (isElemAbelian_cjSub hB)
    ((card_cjSub x B).trans hcard) (cjSub_le hx hB'S) (isElemAbelian_cjSub hB')
    ((card_cjSub x B').trans hcard')
  have e2 := card_inf_mul_pow D hC0 hCV hqT hq2 hqc hqτ hBS hB hcard hB'S hB' hcard'
  have e3 : Nat.card ↥(cjSub x B ⊓ cjSub x B') = Nat.card ↥(B ⊓ B') := by
    rw [cjSub, cjSub, ← Subgroup.map_inf_eq _ _ _ (MulAut.conj x).injective]
    exact card_cjSub x (B ⊓ B')
  rw [e3] at e1
  have hpos : 0 < Nat.card ↥(B ⊓ B') := Nat.card_pos
  exact Nat.pow_right_injective (le_refl 2) (Nat.eq_of_mul_eq_mul_left hpos (e1.trans e2.symm))

theorem sum_card_symmDiff_eq (hC0 : T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥)
    (hCV : T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) ≤ fsuVM T L I)
    {q : Fin 4 → Subgroup.normalizer (fsuVM T L I : Set G)} (hqT : ∀ i, (q i : G) ∈ T)
    (hq2 : ∀ i, (q i : G) ^ 2 = 1) (hqc : ∀ i j, (q i : G) * q j = q j * q i)
    (hqτ : ∀ i, convI (SecA.isElemAbelian_fsuVM hyp) (q i) = D.tau i)
    (hVS : fsuVM T L I ≤ baum T) {B : Subgroup G}
    (hB : B ∈ orbF (Subgroup.normalizer (baum T : Set G)) (fsuVM T L I)) :
    ∑ B' ∈ orbF (Subgroup.normalizer (baum T : Set G)) (fsuVM T L I),
        (symmDiff (gam D B) (gam D B')).card =
      ∑ B' ∈ orbF (Subgroup.normalizer (baum T : Set G)) (fsuVM T L I),
        (symmDiff (gam D (fsuVM T L I)) (gam D B')).card := by
  obtain ⟨x, hx, rfl⟩ := mem_orbF.mp hB
  obtain ⟨hV1, hV2, hV3⟩ := props_of_mem_orbF hVS (SecA.isElemAbelian_fsuVM hyp)
    (self_mem_orbF _ (fsuVM T L I))
  symm
  refine Finset.sum_nbij' (cjSub x) (cjSub x⁻¹) (fun B' hB' => cjSub_mem_orbF hx hB')
    (fun B' hB' => cjSub_mem_orbF (inv_mem hx) hB') (fun B' _ => cjSub_inv_cjSub _ _)
    (fun B' _ => cjSub_cjSub_inv _ _) fun B' hB' => ?_
  obtain ⟨h1, h2, h3⟩ := props_of_mem_orbF hVS (SecA.isElemAbelian_fsuVM hyp) hB'
  exact (card_symmDiff_cjSub D hC0 hCV hqT hq2 hqc hqτ hx hV1 hV2 hV3 h1 h2 h3).symm

end CFSG.Quasithin.Vol2.Ch10.SecE.C10P02

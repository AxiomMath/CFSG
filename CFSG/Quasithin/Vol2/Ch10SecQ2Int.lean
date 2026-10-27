module

public import CFSG.Quasithin.Vol2.Ch10SecQ2Cls
public import CFSG.Quasithin.Vol2.Ch10SecEE3Fix

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE.C10P02

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem centralizer_sup_eq (B B' : Subgroup G) :
    Subgroup.centralizer ((B ⊔ B' : Subgroup G) : Set G) =
      Subgroup.centralizer (B : Set G) ⊓ Subgroup.centralizer (B' : Set G) := by
  refine le_antisymm (le_inf (Subgroup.centralizer_le (le_sup_left : B ≤ B ⊔ B'))
    (Subgroup.centralizer_le (le_sup_right : B' ≤ B ⊔ B'))) ?_
  rintro x ⟨hx, hx'⟩
  have h : B ⊔ B' ≤ Subgroup.centralizer ({x} : Set G) := by
    refine sup_le (fun b hb => ?_) (fun b hb => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hx b hb
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hx' b hb
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact Subgroup.mem_centralizer_singleton_iff.mp (h hy)

theorem card_union_eq_card_inter_add {ι : Type*} [DecidableEq ι] (s t : Finset ι) :
    (s ∪ t).card = (s ∩ t).card + (symmDiff s t).card := by
  have h := symmDiff_sup_inf (a := s) (b := t)
  have hd := disjoint_symmDiff_inf (a := s) (b := t)
  simp only [Finset.sup_eq_union, Finset.inf_eq_inter] at h hd
  rw [← h, Finset.card_union_of_disjoint hd, add_comm]

variable [Finite G] {T L I : Subgroup G} {hyp : Hyp10 G T L I} {t : G} (D : Case2Data hyp t)

theorem card_inf_mul_pow (hC0 : T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥)
    (hCV : T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) ≤ fsuVM T L I)
    {q : Fin 4 → Subgroup.normalizer (fsuVM T L I : Set G)} (hqT : ∀ i, (q i : G) ∈ T)
    (hq2 : ∀ i, (q i : G) ^ 2 = 1) (hqc : ∀ i j, (q i : G) * q j = q j * q i)
    (hqτ : ∀ i, convI (SecA.isElemAbelian_fsuVM hyp) (q i) = D.tau i)
    {B B' : Subgroup G} (hBS : B ≤ baum T) (hB : IsElemAbelian 2 B)
    (hcard : Nat.card B = Nat.card (fsuVM T L I)) (hB'S : B' ≤ baum T) (hB' : IsElemAbelian 2 B')
    (hcard' : Nat.card B' = Nat.card (fsuVM T L I)) :
    Nat.card ↥(B ⊓ B') * 2 ^ (symmDiff (gam D B) (gam D B')).card = 256 := by
  obtain ⟨hY, hinf, hq⟩ := cls D hC0 hCV hqT hq2 hqc hqτ hBS hB hcard
  obtain ⟨hY', hinf', hq'⟩ := cls D hC0 hCV hqT hq2 hqc hqτ hB'S hB' hcard'
  have hV := SecA.isElemAbelian_fsuVM hyp
  have hBN : B ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (hBS.trans inf_le_left).trans (SecA.le_normalizer_fsuVM T L I)
  have hB'N : B' ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (hB'S.trans inf_le_left).trans (SecA.le_normalizer_fsuVM T L I)
  have hIN : B ⊓ B' ≤ Subgroup.normalizer (fsuVM T L I : Set G) := inf_le_left.trans hBN
  have h1 := card_autI_mul_card_inf hV hIN
  have hA : autI hV (B ⊓ B') = D.Yg (gam D B ∩ gam D B') := by
    refine le_antisymm ?_ (D.Yg_le_of fun i hi => ?_)
    · rw [← D.Yg_inf, ← hY, ← hY']
      exact le_inf (autI_mono hV inf_le_left) (autI_mono hV inf_le_right)
    · obtain ⟨hi1, hi2⟩ := Finset.mem_inter.mp hi
      rw [← hqτ i]
      exact convI_mem_autI hV (Subgroup.mem_inf.mpr ⟨hq i hi1, hq' i hi2⟩) (q i).2
  have hC : B ⊓ B' ⊓ Subgroup.centralizer (fsuVM T L I : Set G) =
      fsuVM T L I ⊓ Subgroup.centralizer ((B ⊔ B' : Subgroup G) : Set G) := by
    rw [centralizer_sup_eq]
    calc B ⊓ B' ⊓ Subgroup.centralizer (fsuVM T L I : Set G) =
        (B ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) ⊓
          (B' ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) := by
          rw [inf_inf_inf_comm, inf_idem]
      _ = (fsuVM T L I ⊓ Subgroup.centralizer (B : Set G)) ⊓
          (fsuVM T L I ⊓ Subgroup.centralizer (B' : Set G)) := by rw [hinf, hinf']
      _ = fsuVM T L I ⊓ (Subgroup.centralizer (B : Set G) ⊓
          Subgroup.centralizer (B' : Set G)) := by
          rw [inf_inf_inf_comm, inf_idem]
  have hF : Nat.card ↥(fsuVM T L I ⊓ Subgroup.centralizer ((B ⊔ B' : Subgroup G) : Set G)) =
      Nat.card ↥(fixV (D.Yg (gam D B ∪ gam D B'))) := by
    rw [← card_fixV_autI hV (sup_le hBN hB'N), autI_sup hV hBN hB'N, hY, hY', D.Yg_sup]
  have hfix := D.card_fixV_Yg hC0 (gam D B ∪ gam D B')
  rw [← h1, hA, hC, hF, D.card_Yg, ← hfix, card_union_eq_card_inter_add, pow_add]
  ring

end CFSG.Quasithin.Vol2.Ch10.SecE.C10P02

module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIISp62Check
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Complement
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2Sp4TwoRootSix
public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Pairs

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Levi

open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII CFSG.RankThree.PartTwo.Sec4.Item434Kit
open CFSG.RankThree.PartTwo.Sec21.FF79 (Cen Nor)

@[expose] noncomputable def levJ (p : Fin 3) : Subgroup H6 :=
  (spEmbed (K := ZMod 2) p.succAbove Fin.succAbove_right_injective).range

theorem levJ_eq (p : Fin 3) :
    levJ p = (suppGroup (K := ZMod 2) (coords (n := 3) p)ᶜ : Subgroup H6) := by
  rw [levJ, range_spEmbed, range_succAbove]

theorem nonempty_levJ_equiv (p : Fin 3) : Nonempty (levJ p ≃* Equiv.Perm (Fin 6)) :=
  ⟨(MonoidHom.ofInjective
      (spEmbed_injective (K := ZMod 2) Fin.succAbove_right_injective)).symm.trans
    (CFSG.SeitzReduction.F4Pilot.sp4EquivPerm (K := ZMod 2) (Nat.card_zmod 2))⟩

theorem card_levJ (p : Fin 3) : Nat.card (levJ p) = 720 := by
  obtain ⟨e⟩ := nonempty_levJ_equiv p
  rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem mat_eq_mat6 (g : H6) :
    CFSG.LieType.Universal.Symplectic.SpExtras.mat 3 (ZMod 2) g =
      (mat6 g).submatrix ε6.symm ε6.symm := by
  rw [mat6_apply, submatrix_ε6_symm]
  rfl

private theorem zCode_supp_aux (p : Fin 3) : ∀ r t : Fin 3 ⊕ Fin 3,
    ¬((r = Sum.inl p ∨ r = Sum.inr p) ∧ (t = Sum.inl p ∨ t = Sum.inr p)) →
      (((zCode p).getD (6 * (ε6.symm r).val + (ε6.symm t).val) 0 : ℕ) : ZMod 2) =
        (if r = t then 1 else 0) := by
  fin_cases p <;> decide

section Cert


theorem zH_mem_suppGroup (p : Fin 3) :
    zH p ∈ (suppGroup (K := ZMod 2) (coords (n := 3) p) : Subgroup H6) := by
  rw [mem_suppGroup, mat_eq_mat6, mat6_zH]
  intro r t hrt
  rw [Matrix.one_apply]
  exact zCode_supp_aux p r t (by simpa only [mem_coords] using hrt)

theorem zH_mem_levJ {p q : Fin 3} (h : q ≠ p) : zH q ∈ levJ p := by
  rw [levJ_eq]
  exact suppGroup_mono (coords_subset_compl h) (zH_mem_suppGroup q)

theorem commute_zH_of_mem_levJ (p : Fin 3) {y : H6} (hy : y ∈ levJ p) : Commute (zH p) y := by
  rw [levJ_eq] at hy
  exact commute_suppGroup_compl (zH_mem_suppGroup p) hy

theorem zH_notMem_levJ (p : Fin 3) : zH p ∉ levJ p := by
  intro h
  rw [levJ_eq] at h
  exact z_ne_one wreathFacts_zH p
    ((Subgroup.disjoint_def.mp (disjoint_suppGroup_compl (K := ZMod 2) (coords (n := 3) p)))
      (zH_mem_suppGroup p) h)

private theorem aElt_zero : aElt 0 = zH 0 := by
  simp only [aElt, aVec, vecElt, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  rw [show (1 : ZMod 3).val = 1 from rfl, show (0 : ZMod 3).val = 0 from rfl, pow_one, pow_zero,
    pow_zero, mul_one, mul_one]

private theorem aElt_one : aElt 1 = zH 1 := by
  simp only [aElt, aVec, vecElt, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  rw [show (1 : ZMod 3).val = 1 from rfl, show (0 : ZMod 3).val = 0 from rfl, pow_one, pow_zero,
    pow_zero, one_mul, mul_one]

private theorem aElt_two : aElt 2 = zH 2 := by
  simp only [aElt, aVec, vecElt, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  rw [show (1 : ZMod 3).val = 1 from rfl, show (0 : ZMod 3).val = 0 from rfl, pow_one, pow_zero,
    pow_zero, one_mul, one_mul]

theorem card_cen_zH (p : Fin 3) : Nat.card (Cen (zH p)) = 2160 := by
  fin_cases p
  · show Nat.card (Subgroup.centralizer {zH 0}) = 2160
    rw [← aElt_zero, ← centSub_eq, card_centSub]
    rfl
  · show Nat.card (Subgroup.centralizer {zH 1}) = 2160
    rw [← aElt_one, ← centSub_eq, card_centSub]
    rfl
  · show Nat.card (Subgroup.centralizer {zH 2}) = 2160
    rw [← aElt_two, ← centSub_eq, card_centSub]
    rfl

theorem exists_mul_of_mem_cen (p : Fin 3) {y : H6} (hy : y ∈ Cen (zH p)) :
    ∃ k : ℕ, ∃ j ∈ levJ p, y = zH p ^ k * j := by
  classical
  have hord : orderOf (zH p) = 3 := orderOf_z wreathFacts_zH p
  have hPcard : Nat.card (Subgroup.zpowers (zH p)) = 3 := by rw [Nat.card_zpowers, hord]
  have hcomm : ∀ (a : Subgroup.zpowers (zH p)) (b : levJ p),
      Commute ((Subgroup.zpowers (zH p)).subtype a) ((levJ p).subtype b) := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact ((commute_zH_of_mem_levJ p hb).zpow_left k)
  have hdis : Disjoint (Subgroup.zpowers (zH p)) (levJ p) := by
    rw [disjoint_iff]
    have hdvd : Nat.card ((Subgroup.zpowers (zH p)) ⊓ levJ p : Subgroup H6) ∣ 3 := by
      have h := Subgroup.card_dvd_of_le (inf_le_left : (Subgroup.zpowers (zH p)) ⊓ levJ p ≤
        Subgroup.zpowers (zH p))
      rwa [hPcard] at h
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : (Subgroup.zpowers (zH p)) ⊓ levJ p = Subgroup.zpowers (zH p) :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hPcard])
      apply zH_notMem_levJ p
      have hmem : zH p ∈ Subgroup.zpowers (zH p) := Subgroup.mem_zpowers _
      rw [← heq] at hmem
      exact hmem.2
  set φ := (Subgroup.zpowers (zH p)).subtype.noncommCoprod (levJ p).subtype hcomm with hφ
  have hinj : Function.Injective φ := by
    rw [hφ, MonoidHom.noncommCoprod_injective]
    exact ⟨Subgroup.subtype_injective _, Subgroup.subtype_injective _, by
      simpa only [Subgroup.range_subtype] using hdis⟩
  have hrange : φ.range = Subgroup.zpowers (zH p) ⊔ levJ p := by
    rw [hφ, MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have hle : Subgroup.zpowers (zH p) ⊔ levJ p ≤ Cen (zH p) := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    · intro j hj
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact ((commute_zH_of_mem_levJ p hj).eq).symm
  have hcard : Nat.card φ.range = 2160 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod, hPcard, card_levJ]
  have heq : φ.range = Cen (zH p) :=
    Subgroup.eq_of_le_of_card_ge (hrange ▸ hle) (by rw [hcard, card_cen_zH])
  rw [← heq] at hy
  obtain ⟨⟨⟨a, ha⟩, ⟨j, hj⟩⟩, rfl⟩ := hy
  have hfin : IsOfFinOrder (zH p) :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, zH_pow_three p⟩
  obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (hfin.mem_powers_iff_mem_zpowers.mpr ha)
  exact ⟨k, j, hj, rfl⟩

end Cert

end CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Levi

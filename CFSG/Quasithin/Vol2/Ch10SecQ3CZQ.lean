module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CZP

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I H K : Subgroup G} {n k : ℕ} {b : G}
  {hel : IsElemAbelian 2 (VZ T H)} {I' : Finset (Subgroup (MulAut (IntMod (VZ T H) hel)))}
  {K₀ : Subgroup (MulAut (IntMod (VZ T H) hel))}
  {c : Ctx T L I H K n k b hel I' K₀} {t : G} {L₁ : Subgroup G}

namespace Ctx9

variable (d : Ctx9 c t L₁)
include d

theorem L₂_mem_pair : L₁.map (MulAut.conj t).toMonoidHom = L ∨
    L₁.map (MulAut.conj t).toMonoidHom = CFSG.conjugate L t :=
  eq_or_eq_of_conj c.h37 c.h38 c.hyp d.ht d.htn d.hL₁ (SecA.le_fsuM T L d.ht)

theorem eq_L₁_of_ne {Y : Subgroup G} (hY : Y = L ∨ Y = CFSG.conjugate L t)
    (hne : Y ≠ L₁.map (MulAut.conj t).toMonoidHom) : Y = L₁ := by
  have h12 := d.L₂_ne
  rcases d.hL₁ with h1 | h1 <;> rcases d.L₂_mem_pair with h2 | h2 <;> rcases hY with h3 | h3
  · exact absurd (h2.trans h1.symm) h12
  · exact absurd (h2.trans h1.symm) h12
  · exact h3.trans h1.symm
  · exact absurd (h3.trans h2.symm) hne
  · exact absurd (h3.trans h2.symm) hne
  · exact h3.trans h1.symm
  · exact absurd (h2.trans h1.symm) h12
  · exact absurd (h2.trans h1.symm) h12

theorem not_L₁_le : ¬ L₁ ≤ Subgroup.normalizer (sOne T b : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h
  have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 d.hS₁L₁.1 h d.hS₁L₁.2.1
  have heq : pCoreOf 2 L₁ = sOne T b :=
    le_antisymm (B6.pCoreOf_two_le_of_isSylowTwoOf d.hS₁L₁) hle
  have h2 := two_dvd_relIndex_pCoreOf d.hL₁blk.2.1 (by have := c.h1.1; omega)
  rw [heq] at h2
  exact d.hS₁L₁.2.2 h2

theorem isSylowTwoOf_T1 :
    IsSylowTwoOf (T1 T L) (mOne L₁ T b) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT1_2 : IsPGroup 2 (T1 T L) := c.hyp.fsu.sylow.1.to_le inf_le_left
  rw [A4.isSylowTwoOf_iff_maximal]
  refine ⟨d.T1_le_M₁, hT1_2, fun P hPM hP2 hTP => ?_⟩
  by_contra hPT
  have hlt : T1 T L < P := lt_of_le_of_ne hTP (fun h => hPT (h ▸ le_rfl))
  obtain ⟨s, hsP, hsN, hsT⟩ := A4.exists_mem_normalizer_not_mem hP2 hlt
  have hbaum : baum T = baum (T1 T L) := baum_eq_of_le (c.baum_le_T1 d.h1012) inf_le_left
  have hsS : s ∈ Subgroup.normalizer (baum T : Set G) := by
    rw [hbaum]
    exact normalizer_le_normalizer_baum (T1 T L) hsN
  have hn3 : ¬ Case10_1_1Three T L I := fun h3 => (bender_of_cases (Or.inl ⟨n, c.h1⟩)).2 h3.1
  have hsM : s ∈ fsuM T L := d.h1021 G T L I c.hyp hn3 hsS
  set N := T1 T L ⊔ Subgroup.zpowers s with hN
  have hNP : N ≤ P := sup_le hTP (Subgroup.zpowers_le.mpr hsP)
  have hN2 : IsPGroup 2 N := hP2.to_le hNP
  have hNM : N ≤ fsuM T L := sup_le (fun x hx => SecA.le_fsuM T L hx.1)
    (Subgroup.zpowers_le.mpr hsM)
  have hT : IsSylowTwoOf T (fsuM T L) :=
    isSylowTwoOf_of_quasithinIsSylowTwo c.hyp.fsu.sylow (SecA.le_fsuM T L)
  have hNSyl : IsSylowTwoOf N (fsuM T L) := by
    have h1 : Nat.card T = Nat.card (T1 T L) * 2 := by
      rw [C5.card_eq_card_mul_relIndex (inf_le_left : T1 T L ≤ T), Subgroup.relIndex,
        SecA.index_T1 c.h37 c.h38 c.hyp]
    have h2 : Nat.card N = Nat.card (T1 T L) * (T1 T L).relIndex N :=
      C5.card_eq_card_mul_relIndex le_sup_left
    have h3 : (T1 T L).relIndex N ≠ 1 := fun h =>
      hsT (Subgroup.relIndex_eq_one.mp h (Subgroup.mem_sup_right (Subgroup.mem_zpowers s)))
    have h4 : (T1 T L).relIndex N ≠ 0 := fun h => by
      rw [h, mul_zero] at h2
      exact (Nat.card_pos (α := ↥N)).ne' h2
    have h5 := (isSylowTwoOf_iff.mp hT).2.2
    have h6 := card_le_twoPart hNM hN2
    have hpos : 0 < Nat.card (T1 T L) := Nat.card_pos
    refine isSylowTwoOf_of_card_eq hNM hN2 (le_antisymm h6 ?_)
    rw [← h5, h1, h2]
    exact Nat.mul_le_mul_left _ (by omega)
  by_cases hsL : s ∈ Subgroup.normalizer
      ((L₁.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G)
  · exact not_le_normalizer_of_sylow c.h37 c.h38 c.hyp d.ht d.htn d.L₂_mem_pair hNSyl
      (sup_le d.T1_le_normalizer_L₂ (Subgroup.zpowers_le.mpr hsL))
  ·
    have hY := eq_or_eq_of_conj c.h37 c.h38 c.hyp d.ht d.htn d.L₂_mem_pair hsM
    have hL1 := d.eq_L₁_of_ne hY (fun h => hsL (A38.map_conj_eq_iff.mp h))
    apply d.not_L₁_le
    rw [← hL1]
    rintro _ ⟨x, hx, rfl⟩
    have hsM₁ := hPM hsP
    have hxM₁ := d.L₂_le_M₁ hx
    exact ((mOne L₁ T b).mul_mem ((mOne L₁ T b).mul_mem hsM₁ hxM₁)
      ((mOne L₁ T b).inv_mem hsM₁)).1

end Ctx9

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB

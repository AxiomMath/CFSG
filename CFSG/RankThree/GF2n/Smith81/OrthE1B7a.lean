module

public import CFSG.RankThree.GF2n.Smith81.OrthE1Steps

public section

open scoped commutatorElement

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

theorem b7a_le_commutator_sup {G : Type} [Group G] {F Q : Subgroup G} (hQF : Q ≤ F)
    [hN : (Q.subgroupOf F).Normal] [hP : Group.IsPerfect (↥F ⧸ Q.subgroupOf F)] :
    F ≤ ⁅F, F⁆ ⊔ Q := by
  let p : ↥F →* ↥F ⧸ Q.subgroupOf F := QuotientGroup.mk' (Q.subgroupOf F)
  let T : Subgroup ↥F := (⁅F, F⁆ ⊔ Q).subgroupOf F
  have hNT : Q.subgroupOf F ≤ T := fun y hy =>
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hy))
  have hcomm : ⁅(⊤ : Subgroup ↥F), (⊤ : Subgroup ↥F)⁆ ≤ T := by
    refine Subgroup.commutator_le.mpr fun a _ b _ => Subgroup.mem_subgroupOf.mpr ?_
    have hcoe : ((⁅a, b⁆ : ↥F) : G) = ⁅(a : G), (b : G)⁆ := by
      simp [commutatorElement_def]
    rw [hcoe]
    exact Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator a.2 b.2)
  have htop : Subgroup.map p (⊤ : Subgroup ↥F) = ⊤ :=
    Subgroup.map_top_of_surjective p (QuotientGroup.mk'_surjective _)
  have hkey : Subgroup.map p ⁅(⊤ : Subgroup ↥F), (⊤ : Subgroup ↥F)⁆ = ⊤ := by
    rw [Subgroup.map_commutator, htop]
    exact @Group.IsPerfect.commutator_eq_top _ _ hP
  have hmap : Subgroup.map p T = ⊤ :=
    eq_top_iff.mpr (hkey.symm.le.trans (Subgroup.map_mono (f := p) hcomm))
  have hT : T = ⊤ := by
    refine eq_top_iff.mpr fun y _ => ?_
    have hy : p y ∈ Subgroup.map p T := by
      rw [hmap]
      exact Subgroup.mem_top _
    obtain ⟨t, ht, hty⟩ := Subgroup.mem_map.mp hy
    have hty' : ((t : ↥F) : ↥F ⧸ Q.subgroupOf F) = ((y : ↥F) : ↥F ⧸ Q.subgroupOf F) := hty
    have hN' : t⁻¹ * y ∈ Q.subgroupOf F := QuotientGroup.eq.mp hty'
    have hmul := T.mul_mem ht (hNT hN')
    rwa [mul_inv_cancel_left] at hmul
  intro x hx
  have hxT : (⟨x, hx⟩ : ↥F) ∈ T := by
    rw [hT]
    exact Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp hxT

theorem b7a_le_commutator_sup_of_sl {G : Type} [Group G] {F Q : Subgroup G} {q : ℕ}
    (hq : 4 ≤ q) (hQF : Q ≤ F) (hS : QuotSat F Q (IsSLModel 2 q)) : F ≤ ⁅F, F⁆ ⊔ Q := by
  obtain ⟨hN, K, hK, hfin, hcard, ⟨e⟩⟩ := hS
  haveI := hN
  haveI hSL : Group.IsPerfect ↥(StatedSL 2 K) :=
    (statedSL_quasisimple_of_card 2 K le_rfl (by rw [hcard]; exact hq)).1
  haveI : Group.IsPerfect (↥F ⧸ Q.subgroupOf F) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact b7a_le_commutator_sup hQF

theorem b7a_conj_iSup {G : Type} [Group G] {ι : Sort*} (k : G) (s : ι → Subgroup G) :
    conjSubgroup k (⨆ i, s i) = ⨆ i, conjSubgroup k (s i) :=
  Subgroup.map_iSup (MulAut.conj k).toMonoidHom s

theorem b7a_conj_lgen_le {G : Type} [Group G] {M L : Subgroup G} {k : G} (hk : k ∈ M) :
    conjSubgroup k (Lgen M L) ≤ Lgen M L := by
  unfold Lgen
  rw [b7a_conj_iSup]
  refine iSup_le fun m => ?_
  rw [b7a_conj_iSup]
  refine iSup_le fun hm => ?_
  rw [← CFSG.RankThree.GF2n.conjSubgroup_mul]
  exact le_iSup₂_of_le (k * m) (M.mul_mem hk hm) le_rfl

theorem b7a_of (hB6 : B6Statement) : B7aStatement := by
  intro G _ _ M Q Z B t hH hne
  obtain ⟨D⟩ := hne
  obtain ⟨hLBE, hE0L, -, -⟩ := hB6 G M Q Z B t hH D
  have hq : 4 ≤ Nat.card Z := hH.ctx.hyp.q4
  have hTwo := D.two
  have hTwo' := D.two'
  unfold TwoFactors at hTwo hTwo'
  obtain ⟨hQFb, hQFc, -, -, -, -, -, hSb, hSc⟩ := hTwo
  obtain ⟨hQY, -, -, -, -, -, -, hSY, -⟩ := hTwo'
  set L := Lgen M (LB M Q B)
  have hYL : D.Y ≤ L := le_trans (le_trans le_sup_left le_sup_left) hE0L
  have hFbL : D.Fb ≤ L := le_trans (le_trans le_sup_right le_sup_left) hE0L
  have hFcL : D.Fc ≤ L := le_trans le_sup_right hE0L
  have hQL : Q ≤ L := by
    have hQLB : Q ≤ LB M Q B := le_sup_left
    exact hQLB.trans (hLBE.trans hE0L)
  have hfac : ∀ F : Subgroup G, Q ≤ F → F ≤ L → QuotSat F Q (IsSLModel 2 (Nat.card Z)) →
      F ≤ ⁅L, L⁆ ⊔ Q := fun F hQF hFL hS =>
    (b7a_le_commutator_sup_of_sl hq hQF hS).trans
      (sup_le_sup_right (Subgroup.commutator_mono hFL hFL) Q)
  have hE0H : D.Y ⊔ D.Fb ⊔ D.Fc ≤ ⁅L, L⁆ ⊔ Q :=
    sup_le (sup_le (hfac D.Y hQY hYL hSY) (hfac D.Fb hQFb hFbL hSb)) (hfac D.Fc hQFc hFcL hSc)
  have hLBH : LB M Q B ≤ ⁅L, L⁆ ⊔ Q := hLBE.trans hE0H
  have hQM : ∀ m ∈ M, conjSubgroup m Q ≤ Q := fun m hm =>
    (conjSubgroup_eq_self_iff.mpr (hH.ctx.hyp.Q_normal.2 hm)).le
  have hHM : ∀ m ∈ M, conjSubgroup m (⁅L, L⁆ ⊔ Q) ≤ ⁅L, L⁆ ⊔ Q := by
    intro m hm
    have hLm : conjSubgroup m L ≤ L := b7a_conj_lgen_le hm
    have hcomm : conjSubgroup m ⁅L, L⁆ ≤ ⁅L, L⁆ := by
      show Subgroup.map _ ⁅L, L⁆ ≤ _
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_mono hLm hLm
    rw [conjSubgroup, Subgroup.map_sup]
    exact sup_le (hcomm.trans le_sup_left) ((hQM m hm).trans le_sup_right)
  have hLH : L ≤ ⁅L, L⁆ ⊔ Q := by
    show Lgen M (LB M Q B) ≤ _
    unfold Lgen
    refine iSup₂_le fun m hm => ?_
    exact (show conjSubgroup m (LB M Q B) ≤ conjSubgroup m (⁅L, L⁆ ⊔ Q) from
      Subgroup.map_mono hLBH).trans (hHM m hm)
  have hLC : ⁅L, L⁆ ≤ L := Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact L.mul_mem (L.mul_mem (L.mul_mem ha hb) (L.inv_mem ha)) (L.inv_mem hb)
  exact le_antisymm (sup_le hLC hQL) hLH

end CFSG.RankThree.GF2n.Smith81.Smith23E1

end

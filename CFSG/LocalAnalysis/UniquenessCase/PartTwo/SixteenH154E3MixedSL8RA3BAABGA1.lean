module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8RA3BAABD
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8RA3BAABGA1A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JP

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_sl28_C_TZ_split
    (D : Data G) (S : s16h_Std D) (hσ : D.sig = D.sig1)
    (hJP : K_JonesParshallH1) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {t : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)} (ht : t ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htr : rk ↥(commSub ⊤ (zpowers t)) ≤ 3)
    (hW : Conc4_136W (Mbar D.M ⊥ V h.hyp151.isElemAbelian) t (lBar ⊥ V h.hyp151.isElemAbelian L))
    (hcomp : IsComponentOf (lBar ⊥ V h.hyp151.isElemAbelian L)
      (Mbar D.M ⊥ V h.hyp151.isElemAbelian))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar ⊥ V h.hyp151.isElemAbelian L) ≤ 1)
    (hZ : commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L) ≠ ⊥)
    (hbad : ∀ q ∈ D.sig, ∀ E : Subgroup G, E ≤ D.M → IsElemAbelian q E →
      Nat.card ↥(E ⊓ preBarSub D.M ⊥ V h.hyp151.isElemAbelian
        (centSub (wTil ⊥ V h.hyp151.isElemAbelian L))) < q ^ 2)
    (hrow : s16h_H5RowSL2 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 3)
    (hZ4 : 2 < Nat.card ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)))
    (h7 : 7 ∈ D.sig)
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L)
    (T : Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (Mbar D.M ⊥ V h.hyp151.isElemAbelian)) :
    T ⊓ centSub (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) =
      T ⊓ Subgroup.normalizer
        ((lBar ⊥ V h.hyp151.isElemAbelian L : Subgroup _) : Set _) ∨
      T ≤ centSub (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let hV := h.hyp151.isElemAbelian
  let W := Vtil ⊥ V hV
  let Mb : Subgroup (MulAut W) := Mbar D.M ⊥ V hV
  let A : Subgroup (MulAut W) := lBar ⊥ V hV L
  let Zt : Subgroup W := commSub ⊤ A ⊓ fixV A
  let N : Subgroup (MulAut W) := Mb ⊓ Subgroup.normalizer (A : Set (MulAut W))
  have hTM : T ≤ Mb := hT.le
  obtain ⟨TA, TB, hTA, hTB, hTAsy, hTBsy, hshape⟩ :=
    s16h_sl28_sylow_normalizer_shape D S h hs2 hW hrow hxM hxn T hT
  have hAcent : A ≤ centSub Zt := by
    intro g hg
    rw [mem_centSub]
    intro u hu
    exact (mem_fixV.1 hu.2) g hg
  have hBcent : barSub ⊥ V hV (conjSubgroup L x) ≤ centSub Zt := by
    intro g hg
    rw [mem_centSub]
    intro u hu
    have hcw : commSub (wTil ⊥ V hV L) (barSub ⊥ V hV (conjSubgroup L x)) = ⊥ :=
      (h.hyp151.commute x hxM hxn).2
    have hleB : wTil ⊥ V hV L ≤ fixV (barSub ⊥ V hV (conjSubgroup L x)) :=
      commSub_eq_bot_iff.1 hcw
    exact (mem_fixV.1 (hleB hu.1)) g hg
  have hle : T ⊓ Subgroup.normalizer (A : Set (MulAut W)) ≤ centSub Zt := by
    rw [hshape]
    exact sup_le (hTAsy.le.trans hAcent) (hTBsy.le.trans hBcent)
  have hSrel : (T ⊓ Subgroup.normalizer (A : Set (MulAut W))).relIndex T = 2 := by
    have hNnorm : Mb ≤ Subgroup.normalizer (N : Set (MulAut W)) :=
      (s16h_sl28_normalizer_index_two D S h hs2 hxM hxn).1
    let act : MulAction Mb (Subgroup (MulAut W)) :=
      { smul := fun g H => H.map (MulAut.conj (g : MulAut W)).toMonoidHom
        one_smul := fun H => by
          show H.map (MulAut.conj (((1 : Mb) : MulAut W))).toMonoidHom = H
          rw [show ((1 : Mb) : MulAut W) = 1 from rfl]
          exact Subgroup.map_id H
        mul_smul := fun g g' H => by
          show H.map (MulAut.conj (((g * g' : Mb) : MulAut W))).toMonoidHom =
            (H.map (MulAut.conj (((g' : Mb) : MulAut W))).toMonoidHom).map
              (MulAut.conj (((g : Mb) : MulAut W))).toMonoidHom
          rw [Subgroup.map_map]
          congr 1 }
    letI : MulAction Mb (Subgroup (MulAut W)) := act
    have hstab : MulAction.stabilizer Mb A = N.subgroupOf Mb := by
      ext g
      rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun hg => ⟨g.2, (Subgroup.mem_normalizer_iff_map_conj_eq).2 hg⟩,
        fun hg => (Subgroup.mem_normalizer_iff_map_conj_eq).1 hg.2⟩
    have horbit : MulAction.orbit Mb A = {X : Subgroup (MulAut W) |
        ∃ φ ∈ Mb, X = A.map (MulAut.conj φ).toMonoidHom} := by
      ext X
      constructor
      · rintro ⟨g, rfl⟩
        exact ⟨(g : MulAut W), g.2, rfl⟩
      · rintro ⟨φ, hφ, rfl⟩
        exact ⟨⟨φ, hφ⟩, rfl⟩
    have hidx_orbit : (MulAction.stabilizer Mb A).index = s15 D.M ⊥ V hV L := by
      rw [MulAction.index_stabilizer]
      change (MulAction.orbit Mb A).ncard = s15 D.M ⊥ V hV L
      rw [horbit]
      rfl
    have hNidx : N.relIndex Mb = 2 := by
      show (N.subgroupOf Mb).index = 2
      rw [← hstab, hidx_orbit, hs2]
    have hTN_eq : T ⊓ Subgroup.normalizer (A : Set (MulAut W)) = T ⊓ N := by
      show T ⊓ Subgroup.normalizer (A : Set (MulAut W)) =
        T ⊓ (Mb ⊓ Subgroup.normalizer (A : Set (MulAut W)))
      rw [← inf_assoc, inf_eq_left.mpr hTM]
    rw [hTN_eq]
    exact s16h_sylow_inf_normal_index_two hT inf_le_left hNnorm hNidx
  have hRT : T ⊓ centSub Zt ≤ T := inf_le_left
  have hSR : T ⊓ Subgroup.normalizer (A : Set (MulAut W)) ≤ T ⊓ centSub Zt :=
    le_inf inf_le_left hle
  rcases eq_or_ne (T ⊓ centSub Zt) T with hRT_eq | hRT_ne
  · right
    exact inf_eq_left.mp hRT_eq
  · left
    have hmul := Subgroup.relIndex_mul_relIndex
      (T ⊓ Subgroup.normalizer (A : Set (MulAut W))) (T ⊓ centSub Zt) T hSR hRT
    rw [hSrel] at hmul
    have hdvd : (T ⊓ Subgroup.normalizer (A : Set (MulAut W))).relIndex
        (T ⊓ centSub Zt) ∣ 2 := ⟨_, hmul.symm⟩
    rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two
      ((T ⊓ Subgroup.normalizer (A : Set (MulAut W))).relIndex (T ⊓ centSub Zt))
      hdvd with h1 | h2
    · rw [Subgroup.relIndex_eq_one] at h1
      exact le_antisymm h1 hSR
    · have h2' : (T ⊓ centSub Zt).relIndex T = 1 := by
        rw [h2] at hmul
        omega
      rw [Subgroup.relIndex_eq_one] at h2'
      exact absurd (le_antisymm hRT h2') hRT_ne

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

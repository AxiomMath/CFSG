module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91Defs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight8xK85
import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
import CFSG.GroupTheory.PRankLeOfSylowLe
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
public import CFSG.LocalAnalysis.UniquenessCase.UC6R
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (SigmaStd)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07 (R76Sig)

private theorem k891centaz_normalizer_map_conj {G : Type} [Group G] (H : Subgroup G) (g : G) :
    Subgroup.normalizer ((H.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) =
      (Subgroup.normalizer (H : Set G)).map (MulAut.conj g).toMonoidHom := by
  refine le_antisymm ?_ (Subgroup.le_normalizer_map (H := H)
    (f := (MulAut.conj g).toMonoidHom))
  have hcomp : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id G := by
    ext x
    simp [MulAut.conj_apply]
    group
  have hH : (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = H := by
    rw [Subgroup.map_map, hcomp, Subgroup.map_id]
  have hle := Subgroup.le_normalizer_map (H := H.map (MulAut.conj g).toMonoidHom)
    (f := (MulAut.conj g⁻¹).toMonoidHom)
  rw [hH] at hle
  have h2 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hle
  rw [Subgroup.map_map] at h2
  have hcomp' : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
      MonoidHom.id G := by
    ext x
    simp [MulAut.conj_apply]
    group
  rw [hcomp', Subgroup.map_id] at h2
  exact h2

private theorem k891centaz_map_conj_self {G : Type} [Group G] {H : Subgroup G} {h : G}
    (hh : h ∈ H) : H.map (MulAut.conj h).toMonoidHom = H :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hh)

theorem s891_cent_az {G : Type} [Group G] [Finite G] (D : Data G)
    (hSg : SigmaStd D) (h63 : UC6.R6_3 D) (h76 : R76Sig D)
    (L S R A : Subgroup G) (n : ℕ) (hset : R891Set D L S n) (hbasic : R891Basic D L S)
    (hctx : R891Ctx D L S n R A) (hΓ : ¬ rankThreeGamma 1 3 (S ⊓ L) ≤ D.M) :
    R891CentRank D L S A := by
  classical
  intro p hp
  by_contra hcon
  rw [not_le] at hcon
  have h2 : 2 ≤ CFSG.Open.pRank p
      (D.M ⊓ Subgroup.centralizer ((A ⊔ ZOf (S ⊓ L) : Subgroup G) : Set G)) := by omega
  have hp' := D.sig_prime p hp
  have hp2 : p ≠ 2 := hp'.2
  have hpPrime : p.Prime := hp'.1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hns : ¬ Group.IsSolvable ↥D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.not_solvable_of_mem_calC hset.mem
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.sp_of_mem_sig hSg hns hp
  have hp3 : p ≠ 3 := by
    intro h
    exact hset.notStrong (h ▸ hsp)
  have hLM : L ≤ D.M := hset.mem.1.le
  have hSinfL_M : S ⊓ L ≤ D.M := inf_le_right.trans hLM
  have hA_M : A ≤ D.M := hctx.classes.aLe.trans hLM
  have hZ_M : ZOf (S ⊓ L) ≤ D.M := inf_le_left.trans hSinfL_M
  have hAcard : Nat.card A = 3 := hctx.classes.aOrder
  have hZcard : Nat.card (ZOf (S ⊓ L)) = 3 := hbasic.zOrder
  have hAel : IsElemAbelian 3 A :=
    CFSG.GroupTheory.isElemAbelian_of_card_prime (r := 3) hAcard
  have hZel : IsElemAbelian 3 (ZOf (S ⊓ L)) :=
    CFSG.GroupTheory.isElemAbelian_of_card_prime (r := 3) hZcard
  have hZ_cent : ZOf (S ⊓ L) ≤
      Subgroup.centralizer ((S ⊓ L : Subgroup G) : Set G) := inf_le_right
  have hA_SinfL : A ≤ S ⊓ L := hctx.aLeR.trans hctx.xShape.rSylow
  have hAZ_comm : ∀ a ∈ A, ∀ b ∈ ZOf (S ⊓ L), a * b = b * a := by
    intro a ha b hb
    have hb' := hZ_cent hb
    rw [Subgroup.mem_centralizer_iff] at hb'
    exact hb' a (hA_SinfL ha)
  have hAnotZ : A ≠ ZOf (S ⊓ L) := by
    have hconj1 : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
      ext x
      simp
    intro h
    exact hctx.classes.notConj 1 L.one_mem (by rw [hconj1, Subgroup.map_id, h])
  have hdisjAZ : Disjoint A (ZOf (S ⊓ L)) := by
    rw [disjoint_iff]
    have hdvd : Nat.card ↥(A ⊓ ZOf (S ⊓ L)) ∣ 3 := by
      have h := Subgroup.card_dvd_of_le (inf_le_right : A ⊓ ZOf (S ⊓ L) ≤ ZOf (S ⊓ L))
      rwa [hZcard] at h
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq (H := A ⊓ ZOf (S ⊓ L)) h1
    · exfalso
      have hAZ : A ⊓ ZOf (S ⊓ L) = ZOf (S ⊓ L) :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by omega)
      have hZA : ZOf (S ⊓ L) ≤ A := hAZ ▸ inf_le_left
      exact hAnotZ (Subgroup.eq_of_le_of_card_ge hZA (by omega)).symm
  have hZ_normA : ZOf (S ⊓ L) ≤ Subgroup.normalizer (A : Set G) := by
    have hc : ZOf (S ⊓ L) ≤ Subgroup.centralizer (A : Set G) := by
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact hAZ_comm a ha z hz
    exact hc.trans (Subgroup.centralizer_le_normalizer (A : Set G))
  have hE0_card : Nat.card ↥(A ⊔ ZOf (S ⊓ L)) = 3 ^ 2 := by
    have h := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer A
      (ZOf (S ⊓ L)) hZ_normA hdisjAZ
    rw [h, hAcard, hZcard]
    norm_num
  have hE0_el : IsElemAbelian 3 (A ⊔ ZOf (S ⊓ L)) :=
    hAel.sup_of_commute hZel hAZ_comm
  have hE0_M : (A ⊔ ZOf (S ⊓ L) : Subgroup G) ≤ D.M := sup_le hA_M hZ_M
  have hΓE0 : rankThreeGamma 1 3 (A ⊔ ZOf (S ⊓ L)) ≤ D.M := by
    refine h76 p hp hp2 hsp 3 Nat.prime_three (A ⊔ ZOf (S ⊓ L)) hE0_M hE0_el hE0_card
      (by omega) ?_
    intro X hXE hXcard
    have hcent : Subgroup.centralizer ((A ⊔ ZOf (S ⊓ L) : Subgroup G) : Set G) ≤
        Subgroup.centralizer (X : Set G) :=
      Subgroup.centralizer_le (show (X : Set G) ⊆ ((A ⊔ ZOf (S ⊓ L) : Subgroup G) : Set G) from hXE)
    have hle : D.M ⊓ Subgroup.centralizer ((A ⊔ ZOf (S ⊓ L) : Subgroup G) : Set G) ≤
        D.M ⊓ Subgroup.normalizer (X : Set G) :=
      le_inf inf_le_left (inf_le_right.trans (hcent.trans (Subgroup.centralizer_le_normalizer _)))
    have hmono := CFSG.SectionRank.pRank_mono hpPrime.one_lt hle
    omega
  have hArank : 1 ≤ CFSG.Open.pRank 3 A :=
    CFSG.SectionRank.le_pRank (by norm_num) le_rfl hAel (by rw [hAcard]; norm_num)
  have hZrank : 1 ≤ CFSG.Open.pRank 3 (ZOf (S ⊓ L)) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_rfl hZel (by rw [hZcard]; norm_num)
  have hNA : Subgroup.normalizer (A : Set G) ≤ D.M :=
    (CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore
      (p := 3) (k := 1) (P := A ⊔ ZOf (S ⊓ L)) (Q := A) le_sup_left hArank).trans hΓE0
  have hNZ : Subgroup.normalizer (ZOf (S ⊓ L) : Set G) ≤ D.M :=
    (CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore
      (p := 3) (k := 1) (P := A ⊔ ZOf (S ⊓ L)) (Q := ZOf (S ⊓ L))
      le_sup_right hZrank).trans hΓE0
  have hNB : ∀ B : Subgroup G, B ≤ L → Nat.card B = 3 →
      Subgroup.normalizer (B : Set G) ≤ D.M := by
    intro B hBL hBcard
    rcases hctx.classes.classes B hBL hBcard with ⟨l, hlL, rfl⟩ | ⟨l, hlL, rfl⟩
    · rw [k891centaz_normalizer_map_conj]
      calc (Subgroup.normalizer (ZOf (S ⊓ L) : Set G)).map (MulAut.conj l).toMonoidHom
          ≤ D.M.map (MulAut.conj l).toMonoidHom := Subgroup.map_mono hNZ
        _ = D.M := k891centaz_map_conj_self (hLM hlL)
    · rw [k891centaz_normalizer_map_conj]
      calc (Subgroup.normalizer (A : Set G)).map (MulAut.conj l).toMonoidHom
          ≤ D.M.map (MulAut.conj l).toMonoidHom := Subgroup.map_mono hNA
        _ = D.M := k891centaz_map_conj_self (hLM hlL)
  have hNE : ∀ E : Subgroup G, E ≤ S ⊓ L → IsElemAbelian 3 E → Nat.card E = 9 →
      Subgroup.normalizer (E : Set G) ≤ D.M := by
    intro E hESL hEel hEcard
    have hZE : ZOf (S ⊓ L) ≤ E := by
      by_contra hnot
      have hdvd : Nat.card ↥(E ⊓ ZOf (S ⊓ L)) ∣ 3 := by
        have h := Subgroup.card_dvd_of_le (inf_le_right : E ⊓ ZOf (S ⊓ L) ≤ ZOf (S ⊓ L))
        rwa [hZcard] at h
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · have hdisj : Disjoint E (ZOf (S ⊓ L)) := by
          rw [disjoint_iff]
          exact Subgroup.eq_bot_of_card_eq (H := E ⊓ ZOf (S ⊓ L)) h1
        have hZ_normE : ZOf (S ⊓ L) ≤ Subgroup.normalizer (E : Set G) := by
          have hc : ZOf (S ⊓ L) ≤ Subgroup.centralizer (E : Set G) := by
            intro z hz
            rw [Subgroup.mem_centralizer_iff]
            intro e he
            have hz' := (Subgroup.mem_centralizer_iff.mp (hZ_cent hz)) e (hESL he)
            exact hz'
          exact hc.trans (Subgroup.centralizer_le_normalizer (E : Set G))
        have hEZcard : Nat.card ↥(E ⊔ ZOf (S ⊓ L)) = 27 := by
          rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer E
            (ZOf (S ⊓ L)) hZ_normE hdisj, hEcard, hZcard]
        have hEZel : IsElemAbelian 3 (E ⊔ ZOf (S ⊓ L)) :=
          hEel.sup_of_commute hZel (by
            intro a ha b hb
            exact Subgroup.mem_centralizer_iff.mp (hZ_cent hb) a (hESL ha))
        have hEZ_L : E ⊔ ZOf (S ⊓ L) ≤ L :=
          sup_le (hESL.trans inf_le_right) (inf_le_left.trans hbasic.sylowL.le)
        have h3 : 3 ≤ CFSG.Open.pRank 3 (E ⊔ ZOf (S ⊓ L)) := by
          refine CFSG.SectionRank.le_pRank (by norm_num) le_rfl hEZel ?_
          rw [hEZcard]
          norm_num
        have h2' : CFSG.Open.pRank 3 (E ⊔ ZOf (S ⊓ L)) ≤ 2 := by
          rw [← hbasic.rank]
          exact CFSG.SectionRank.pRank_mono (by norm_num) hEZ_L
        omega
      · exact hnot (by
          have hZEeq : E ⊓ ZOf (S ⊓ L) = ZOf (S ⊓ L) :=
            Subgroup.eq_of_le_of_card_ge inf_le_right (by omega)
          exact hZEeq ▸ inf_le_left)
    intro g hg
    have hgE : E.map (MulAut.conj g).toMonoidHom = E :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
    have hZg_le_E : (ZOf (S ⊓ L)).map (MulAut.conj g).toMonoidHom ≤ E := by
      rw [← hgE]
      exact Subgroup.map_mono hZE
    have hZg_card : Nat.card ((ZOf (S ⊓ L)).map (MulAut.conj g).toMonoidHom) = 3 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hZcard]
    have hZg_L : (ZOf (S ⊓ L)).map (MulAut.conj g).toMonoidHom ≤ L :=
      hZg_le_E.trans (hESL.trans inf_le_right)
    have hNZg : Subgroup.normalizer
        (((ZOf (S ⊓ L)).map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) ≤ D.M :=
      hNB _ hZg_L hZg_card
    rw [k891centaz_normalizer_map_conj] at hNZg
    have hNZ_le : Subgroup.normalizer (ZOf (S ⊓ L) : Set G) ≤
        D.M ⊓ D.M.map (MulAut.conj g⁻¹).toMonoidHom := by
      refine le_inf hNZ ?_
      intro x hx
      have hgx : g * x * g⁻¹ ∈ D.M := hNZg (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
      exact Subgroup.mem_map.mpr ⟨g * x * g⁻¹, hgx, by simp [mul_assoc]⟩
    have hcent_le : D.M ⊓ Subgroup.centralizer ((A ⊔ ZOf (S ⊓ L) : Subgroup G) : Set G) ≤
        Subgroup.normalizer (ZOf (S ⊓ L) : Set G) := by
      have hsub : (ZOf (S ⊓ L) : Set G) ⊆ ((A ⊔ ZOf (S ⊓ L) : Subgroup G) : Set G) :=
        fun z hz => Subgroup.mem_sup_right hz
      exact fun x hx => Subgroup.centralizer_le_normalizer (ZOf (S ⊓ L) : Set G)
        (Subgroup.centralizer_le hsub hx.2)
    have hp_dvd_NZ : p ∣ Nat.card (Subgroup.normalizer (ZOf (S ⊓ L) : Set G)) := by
      have hdvd := CFSG.GroupTheory.dvd_card_of_one_le_pRank hpPrime (H :=
        D.M ⊓ Subgroup.centralizer ((A ⊔ ZOf (S ⊓ L) : Subgroup G) : Set G)) (by omega)
      exact hdvd.trans (Subgroup.card_dvd_of_le hcent_le)
    have hp_dvd_Minf : p ∣ Nat.card
        ↥(D.M ⊓ D.M.map (MulAut.conj g⁻¹).toMonoidHom) :=
      hp_dvd_NZ.trans (Subgroup.card_dvd_of_le hNZ_le)
    by_contra hgM
    have hgi : g⁻¹ ∉ D.M := fun h => hgM (by simpa using D.M.inv_mem h)
    exact hsp.2.2 g⁻¹ hgi hp_dvd_Minf
  have hE9 : ∀ E : Subgroup G, E ≤ S ⊓ L → IsElemAbelian 3 E → Nat.card E = 9 →
      rankThreeGamma 1 3 E ≤ D.M := by
    intro E hESL hEel hEcard
    refine CFSG.HardMathSupport.Solomon.Proving.GLBCore_le_of_forall ?_
    intro Q hQE hQrank
    by_cases hQeq : Q = E
    · exact hQeq ▸ hNE E hESL hEel hEcard
    · have hdvd : Nat.card Q ∣ 3 ^ 2 := by
        have h := Subgroup.card_dvd_of_le hQE
        rw [hEcard] at h
        exact h
      obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
      interval_cases k
      · rw [pow_zero] at hk
        have h3dvd : 3 ∣ Nat.card Q :=
          CFSG.GroupTheory.dvd_card_of_one_le_pRank Nat.prime_three hQrank
        rw [hk] at h3dvd
        exact absurd (Nat.le_of_dvd (by norm_num) h3dvd) (by norm_num)
      · rw [pow_one] at hk
        exact hNB Q (hQE.trans hESL |>.trans inf_le_right) hk
      · rw [pow_two] at hk
        exfalso
        exact hQeq (Subgroup.eq_of_le_of_card_ge hQE (by rw [hk, hEcard]; norm_num))
  have hE9contain : ∀ x ∈ S ⊓ L, orderOf x = 3 →
      ∃ E : Subgroup G, x ∈ E ∧ E ≤ S ⊓ L ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 := by
    intro x hx hxord
    by_cases hxZ : x ∈ ZOf (S ⊓ L)
    ·
      have h2rank : 2 ≤ CFSG.Open.pRank 3 (S ⊓ L) := by
        have h := CFSG.pRank_le_of_isSylowOf_le (p := 3) Nat.prime_three
          (Y := L) (N₁ := S ⊓ L) (S := S ⊓ L) hbasic.sylowL.le hbasic.sylowL le_rfl
        rwa [hbasic.rank] at h
      obtain ⟨E, hZE, hESL, hEel, hEcard⟩ :=
        CFSG.GroupTheory.exists_isElemAbelian_card_sq_of_le_of_card_prime
          (r := 3) hbasic.sylowL.isPGroup h2rank inf_le_left hZcard
      exact ⟨E, hZE hxZ, hESL, hEel, by rw [hEcard]; norm_num⟩
    ·
      have hxpow : x ^ 3 = 1 := by
        rw [← hxord]
        exact pow_orderOf_eq_one x
      have hcomm : ∀ z ∈ ZOf (S ⊓ L), z * x = x * z := by
        intro z hz
        have hz' := (Subgroup.mem_centralizer_iff.mp (hZ_cent hz)) x hx
        exact hz'.symm
      obtain ⟨hel, hcard⟩ :=
        CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute (r := 3) hZcard hxord hxZ hcomm
      refine ⟨ZOf (S ⊓ L) ⊔ Subgroup.zpowers x, Subgroup.mem_sup_right (Subgroup.mem_zpowers x),
        ?_, hel, ?_⟩
      · refine sup_le inf_le_left ?_
        exact Subgroup.zpowers_le.mpr hx
      · rw [hcard]
        norm_num
  exact hΓ (rankThreeGamma_le_of_forall_e9 hbasic.sylowL.isPGroup hSinfL_M hE9contain hE9
    (fun E hEM hEel hEcard hΓE =>
      h63 3 Nat.prime_three (by norm_num) E hEM hEel (by rw [hEcard]; norm_num) hΓE))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

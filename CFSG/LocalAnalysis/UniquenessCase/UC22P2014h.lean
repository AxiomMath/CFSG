module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P2014g
public import CFSG.LocalAnalysis.UniquenessCase.UC22FinThreeN
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20g
import CFSG.LocalAnalysis.UniquenessCase.UC22S13xj
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2014b
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2014c
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2014e

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.Blueprint (LieModel)


variable {G : Type} [Group G] [Finite G]

@[expose] def StrongParab207 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], UC22P20gShape X → CFSG.pCore 2 X = ⊥ →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ Y : Subgroup X, IsParabolicTwo X Y →
      IsStronglyPEmbedded p Y →
        ∃ m n : ℕ, 2 < m ∧ m ≤ 4 ∧ 2 < n ∧ CFSG.Open.IsQuasisimple X ∧
          LieModel (X ⧸ Subgroup.center X) .PSL m 2 n ∧ ¬ 2 ^ n ≡ 1 [MOD p] ∧
          Nonempty (↥(Opp p (⊤ : Subgroup (Bar2 Y))) ≃*
            CFSG.Open.StatedSL (m - 1) (GaloisField 2 n))

theorem s20_14N_of_strongParab207 {D : Data G} (hB : ListBNonabelian) (h66 : UC6.R6_6 D)
    (h204 : S20_4 D) (h207 : S20_7 D) (hSP : StrongParab207) : S20_14N D := by
  intro h1930 p hp hp2 hsp H hH hpH
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf p (H ⊓ D.M)
  have hpP : p ∣ Nat.card P := by
    rw [hP.card_eq]
    exact dvd_pow_self p (Nat.Prime.factorization_pos_of_dvd hp Nat.card_pos.ne' hpH).ne'
  have hP1 : P ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hpP
    exact hp.one_lt.ne' (Nat.dvd_one.1 hpP)
  have hPH := uc22s13xj_isSylowOf_of_inf hsp hP hP1
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := P) p hpP
  rw [← Subgroup.orderOf_coe] at hx
  have hxH : (x : G) ∈ H := (hP.le x.2).1
  have hxM : (x : G) ∈ D.M := (hP.le x.2).2
  obtain ⟨L, hL⟩ := uc22p2014c_exists_calLOf D h204 h1930 hH
  have hxN : (x : G) ∈ normalizer (L : Set G) :=
    uc22p2014b_mem_normalizer_calLOf D hB h1930 hp hsp hH hL hxH hxM hx
  have hLO : L ≤ Opp p H := uc22p2014b_calLOf_le_opp D hB h1930 hp hsp hH hL hxH hxM hx
  have hxp : IsPGroup p (zpowers (x : G)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  have hxL : (x : G) ∈ L := uc22p2014g_le D hB h1930 h207 hp hp2 hsp hL.1 hxp
    (zpowers_le.2 hxM) (zpowers_le.2 hxN) (mem_zpowers _)
  have hyΥ : (QuotientGroup.mk ⟨(x : G), hxL⟩ : Bar2 L) ∈ barImage L (D.M ⊓ L) :=
    (uc22p2014d_mem_barImage_iff D hL.1 ⟨(x : G), hxL⟩).2 hxM
  have hy1 : (QuotientGroup.mk ⟨(x : G), hxL⟩ : Bar2 L) ≠ 1 := by
    intro h
    rw [QuotientGroup.eq_one_iff] at h
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥L) ⟨_, h⟩
    have hk' : (x : G) ^ (2 ^ k) = 1 := by
      have := congrArg (fun z : ↥(CFSG.pCore 2 ↥L) => ((z : ↥L) : G)) hk
      simpa using this
    have h2 : p ∣ 2 ^ k := hx ▸ orderOf_dvd_of_pow_eq_one hk'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2))
  have hpΥ : p ∣ Nat.card (barImage L (D.M ⊓ L)) := by
    have hpow : (QuotientGroup.mk ⟨(x : G), hxL⟩ : Bar2 L) ^ p = 1 := by
      rw [← QuotientGroup.mk_pow]
      have : (⟨(x : G), hxL⟩ : ↥L) ^ p = 1 := Subtype.ext (by
        simpa [hx] using pow_orderOf_eq_one (x : G))
      rw [this, QuotientGroup.mk_one]
    have hord : orderOf (⟨_, hyΥ⟩ : barImage L (D.M ⊓ L)) = p := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_eq_prime hpow hy1
    rw [← hord]
    exact orderOf_dvd_natCard _
  have hstrong : IsStronglyPEmbedded p (barImage L (D.M ⊓ L)) :=
    ⟨uc22p2014d_barImage_ne_top D hL.1, hpΥ, fun w hw =>
      uc22p2014d_not_dvd_card_inf_conj D hsp hL.1 w hw⟩
  obtain ⟨m, n, hm, hm4, hn, hq, hLie, h1, ⟨e⟩⟩ := hSP (Bar2 L) (h207 h1930 L hL.1)
    uc22p20c_pCore_quotient_pCore p hp hp2 _ (uc22p2014d_isParabolicTwo D hB h1930 hL.1) hstrong
  have hLC : L ∈ CFSG.Quasithin.cComp H := uc22p2014c_mem_cComp_of_isQuasisimple D hL hq
  have hpL : p ∣ Nat.card L := hx ▸ Subgroup.orderOf_dvd_natCard L hxL
  have hHL : H ≤ normalizer (L : Set G) :=
    uc22p2014c_le_normalizer_of_dvd_card D hB h1930 h66 hp hp2 hsp hH hLC hpL
  have hPL : P ≤ L := uc22p2014g_le D hB h1930 h207 hp hp2 hsp hL.1 hP.isPGroup
    (hP.le.trans inf_le_right) ((hP.le.trans inf_le_left).trans hHL)
  have hLH : L ≤ H := CFSG.Quasithin.le_of_mem_cComp hLC
  have hOL : Opp p H ≤ L := uc22p2014e_opp_le hPH hLH hHL (Subgroup.card_dvd_of_le hPL)
  have hLeq : L = Opp p H := le_antisymm hLO hOL
  have hOM : Opp p (H ⊓ D.M) ≤ D.M ⊓ L := by
    refine le_inf ((Subgroup.closure_le _).2 fun y hy => hy.1.2) ?_
    rw [hLeq]
    exact Subgroup.closure_mono fun y hy => ⟨hy.1.1, hy.2⟩
  obtain ⟨e'⟩ := uc22p2014e_nonempty_mulEquiv hp (A := D.M ⊓ L) (B := H ⊓ D.M) (L := L)
    (fun y hy => ⟨hLH hy.2, hy.1⟩) (uc22p2014e_inf_le_normalizer hHL) inf_le_right hOM
  subst hLeq
  exact ⟨m, n, hm, hm4, hn, hq, hLie, h1, ⟨e'.trans e⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22

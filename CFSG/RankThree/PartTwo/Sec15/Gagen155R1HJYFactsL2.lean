module

public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJYFacts
public import CFSG.RankThree.PartTwo.Sec18.Item189ListBasic
public import CFSG.CGT.PushingUpLit.C2L.StrongTI
public import CFSG.Assembly.E6FourLabelArith
public import CFSG.Timmesfeld.Bridge.SL2FactsCoord
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
public import CFSG.Timmesfeld.Bridge.RootClosureCoxQ2

public section

namespace CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJ

open CFSG CFSG.RankThree.PartTwo.Sec15 CFSG.Timmesfeld.ARS.NaturalModule
  CFSG.Timmesfeld.Bridge.RootClosure

theorem exists_prime_orderOf_mem_normalizer_sylow_two {L : Type} [Group L] [Finite L] {n r : ℕ}
    (hn : 2 ≤ n) (e : L ≃* CFSG.Theory.Comparator.PSL2Model n) (hr : r.Prime)
    (hdvd : r ∣ 2 ^ n - 1) (P : Sylow 2 L) :
    ∃ t ∈ Subgroup.normalizer ((P : Subgroup L) : Set L), orderOf t = r := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨φ, hφ⟩ := psl2SylowCoordStmt n hn L ⟨e⟩ P
  have hK : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := (GaloisField 2 n)ˣ) r
    (by rw [Nat.card_units, hK]; exact hdvd)
  have hmem : diagElt c ∈ Subgroup.normalizer
      (CFSG.Timmesfeld.upperUnipotent (GaloisField 2 n) :
        Set (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))) :=
    diagElt_mem_normalizer_upperUnipotent c
  have hord : orderOf (diagElt c) = r := by
    let f : (GaloisField 2 n)ˣ →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) :=
      { toFun := diagElt
        map_one' := diagElt_one
        map_mul' := fun a b => (diagElt_mul_diagElt a b).symm }
    have hinj : Function.Injective f := by
      intro a b hab
      have h := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) =>
        (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)) 0 0) hab
      exact Units.ext (by simpa [f, coe_diagElt] using h)
    rw [← hc]
    exact orderOf_injective f hinj c
  have hN : (Subgroup.normalizer ((P : Subgroup L) : Set L)).map φ.toMonoidHom =
      Subgroup.normalizer (CFSG.Timmesfeld.upperUnipotent (GaloisField 2 n) :
        Set (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))) := by
    rw [← hφ, Subgroup.map_equiv_normalizer_eq]
  refine ⟨φ.symm (diagElt c), ?_, ?_⟩
  · have h1 : diagElt c ∈
        (Subgroup.normalizer ((P : Subgroup L) : Set L)).map φ.toMonoidHom := hN ▸ hmem
    obtain ⟨y, hy, hyh⟩ := Subgroup.mem_map.1 h1
    have hy' : y = φ.symm (diagElt c) := by
      rw [← hyh]
      exact (MulEquiv.symm_apply_apply φ y).symm
    rwa [hy'] at hy
  · rw [MulEquiv.orderOf_eq, hord]

theorem five_dvd_card_normalizer_sylow_two {L : Type} [Group L] [Finite L] {n : ℕ}
    (hn : 2 ≤ n) (e : L ≃* CFSG.Theory.Comparator.PSL2Model n) (h4 : 4 ∣ n) (P : Sylow 2 L) :
    5 ∣ Nat.card (Subgroup.normalizer ((P : Subgroup L) : Set L)) := by
  obtain ⟨t, ht, htord⟩ := exists_prime_orderOf_mem_normalizer_sylow_two hn e Nat.prime_five
    (CFSG.Assembly.e6Four_five_dvd_two_pow_sub_one.2 h4) P
  have h := Subgroup.orderOf_dvd_natCard
    (Subgroup.normalizer ((P : Subgroup L) : Set L)) ht
  rwa [htord] at h

theorem res1HJYFacts_projSL {n : ℕ} (hn0 : 0 < n) (h4 : 4 ∣ n) :
    Res1HJYFacts ↥(CFSG.PGLModel.projSL 2 (GaloisField 2 n)) := by
  have hn : 2 ≤ n := by omega
  haveI : Finite ↥(CFSG.PGLModel.projSL 2 (GaloisField 2 n)) :=
    Finite.of_equiv (CFSG.Theory.Comparator.PSL2Model n)
      (CFSG.RankThree.PartTwo.Sec4.projSLEquivPSL (GaloisField 2 n)).toEquiv.symm
  refine res1HJYFacts_of_borel (Y := ↥(CFSG.PGLModel.projSL 2 (GaloisField 2 n))) ?_ ?_
  ·
    have hsyl : ∀ W : Sylow 2 ↥(CFSG.PGLModel.projSL 2 (GaloisField 2 n)),
        CFSG.ABGLocalTools.IsSylowOf 2
          (W : Subgroup ↥(CFSG.PGLModel.projSL 2 (GaloisField 2 n))) ⊤ := by
      intro W
      rw [CFSG.ABGLocalTools.isSylowOf_iff, Subgroup.relIndex_top_right]
      exact ⟨le_top, W.isPGroup', Sylow.not_dvd_index W⟩
    intro U V hUV
    exact CFSG.CGT.PushingUpLit.C2L.StrongTI.bender_sylow_inf_eq_bot
      (CFSG.RankThree.PartTwo.Sec18.fusionIsBenderGroup_of_projSL_two hn (MulEquiv.refl _))
      (hsyl U) (hsyl V) (fun h => hUV (Sylow.ext h))
  ·
    intro P
    obtain ⟨-, ⟨D, hcyc, -, hinf, hsup⟩, -, -, hcardP⟩ :=
      (CFSG.Open.bender_psl2_borel_full n hn).map_mulEquiv
        (CFSG.RankThree.PartTwo.Sec4.projSLEquivPSL (GaloisField 2 n)).symm P
    refine ⟨D, hcyc, ?_, hinf, hsup⟩
    have h5N : 5 ∣ Nat.card (Subgroup.normalizer
        ((P : Subgroup ↥(CFSG.PGLModel.projSL 2 (GaloisField 2 n))) :
          Set ↥(CFSG.PGLModel.projSL 2 (GaloisField 2 n)))) :=
      five_dvd_card_normalizer_sylow_two hn
        (CFSG.RankThree.PartTwo.Sec4.projSLEquivPSL (GaloisField 2 n)) h4 P
    have hDnorm : D ≤ Subgroup.normalizer
        ((P : Subgroup ↥(CFSG.PGLModel.projSL 2 (GaloisField 2 n))) :
          Set ↥(CFSG.PGLModel.projSL 2 (GaloisField 2 n))) := by
      rw [← hsup]
      exact le_sup_right
    have hprod : Nat.card (Subgroup.normalizer
        ((P : Subgroup ↥(CFSG.PGLModel.projSL 2 (GaloisField 2 n))) :
          Set ↥(CFSG.PGLModel.projSL 2 (GaloisField 2 n)))) =
        Nat.card D * Nat.card
          (P : Subgroup ↥(CFSG.PGLModel.projSL 2 (GaloisField 2 n))) := by
      have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
        (H := D) (K := (P : Subgroup ↥(CFSG.PGLModel.projSL 2 (GaloisField 2 n)))) hDnorm
      rw [sup_comm D, inf_comm D, hsup, hinf, Subgroup.card_bot, mul_one] at h
      exact h
    have h5Q : ¬ 5 ∣ Nat.card
        (P : Subgroup ↥(CFSG.PGLModel.projSL 2 (GaloisField 2 n))) := by
      rw [hcardP, pow_one]
      intro h
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_five h) (by norm_num)
    rw [hprod] at h5N
    rcases (Nat.Prime.dvd_mul Nat.prime_five).1 h5N with h | h
    · exact h
    · exact absurd h h5Q

end CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJ

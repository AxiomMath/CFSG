module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DihedralSylow
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2Subgroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoSemilinear
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.GorensteinWalter
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped MatrixGroups

theorem sq_sub_one_eq_eight_mul_odd {q : ℕ} (hq : Odd q)
    (hq8 : q % 8 = 3 ∨ q % 8 = 5) :
    ∃ u : ℕ, Odd u ∧ q ^ 2 - 1 = 8 * u := by
  have hq16 : q % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have hqmod8 : q % 8 = (q % 16) % 8 := (Nat.mod_mod_of_dvd _ (by norm_num)).symm
  have hsq : q ^ 2 % 16 = 9 := by
    rw [Nat.pow_mod]
    interval_cases hr : q % 16 <;> omega
  let k := q ^ 2 / 16
  have hk : q ^ 2 = 16 * k + 9 := by
    have h := Nat.div_add_mod (q ^ 2) 16
    omega
  refine ⟨2 * k + 1, ⟨k, by ring⟩, by omega⟩

theorem odd_of_pow_mod_eight {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) : Odd f := by
  have hpodd : Odd p := Nat.Prime.odd_of_ne_two Fact.out hp2
  by_contra hf
  have hf2 : 2 ∣ f := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hf)
  obtain ⟨k, rfl⟩ := hf2
  have hsq : p ^ 2 % 8 = 1 := by
    obtain ⟨r, rfl⟩ := hpodd
    have h : (2 * r + 1) ^ 2 = 4 * (r * (r + 1)) + 1 := by ring
    obtain ⟨s, hs⟩ := (Nat.even_mul_succ_self r).two_dvd
    rw [h, hs]
    omega
  have hpowsq : p ^ (2 * k) % 8 = 1 := by
    rw [pow_mul, Nat.pow_mod, hsq]
    norm_num
  omega

theorem odd_elim_reduction {K : Type} [Group K] [Finite K] {p f : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hf : 0 < f) (h5 : 5 ≤ p ^ f)
    (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5)
    (e : K ≃* PSL(2, GaloisField p f)) :
    Nat.card K = p ^ f * ((p ^ f) ^ 2 - 1) / 2 ∧
      ∃ w : ℕ, Odd w ∧ Nat.card K = 4 * w := by
  classical
  let F := GaloisField p f
  have hp : p.Prime := Fact.out
  have hFcard : Nat.card F = p ^ f := GaloisField.card p f (by omega)
  have hFodd : IsOddPrimePower (Nat.card F) :=
    ⟨p, f, hp, hp.odd_of_ne_two hp2, hf, hFcard⟩
  have hKcard : Nat.card K = Nat.card (PSL2 F) := Nat.card_congr e.toEquiv
  have hcard : Nat.card K = p ^ f * ((p ^ f) ^ 2 - 1) / 2 := by
    rw [hKcard, psl2_card_formula F hFodd, hFcard]
  have hqodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  obtain ⟨u, hu, hqsq⟩ := sq_sub_one_eq_eight_mul_odd hqodd h8
  refine ⟨hcard, p ^ f * u, Nat.odd_mul.mpr ⟨hqodd, hu⟩, ?_⟩
  rw [hcard, hqsq]
  calc
    p ^ f * (8 * u) / 2 = (2 * (4 * (p ^ f * u))) / 2 := by ring_nf
    _ = 4 * (p ^ f * u) := Nat.mul_div_cancel_left _ (by norm_num)

theorem pgl2_card_eq_eight_mul_odd {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2)
    (h8 : Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5) :
    ∃ u : ℕ, Odd u ∧ Nat.card (PGL2 F) = 8 * u := by
  have hp : p.Prime := Fact.out
  have hqodd : Odd (Nat.card F) := by
    rw [hF]
    exact (hp.odd_of_ne_two hp2).pow
  obtain ⟨u, hu, hqsq⟩ := sq_sub_one_eq_eight_mul_odd hqodd h8
  refine ⟨Nat.card F * u, Nat.odd_mul.mpr ⟨hqodd, hu⟩, ?_⟩
  rw [pgl2_card_formula F, hqsq]
  ring

theorem nat_card_outer_odd_psl2 {K : Type} [Group K] [Finite K] {p f : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hf : 0 < f) (h5 : 5 ≤ p ^ f) (hfodd : Odd f)
    (e : K ≃* PSL(2, GaloisField p f)) :
    Nat.card (Outer K) = 2 * f := by
  classical
  let F := GaloisField p f
  have hp : p.Prime := Fact.out
  have hFcard : Nat.card F = p ^ f := GaloisField.card p f (by omega)
  have hFodd : IsOddPrimePower (Nat.card F) :=
    ⟨p, f, hp, hp.odd_of_ne_two hp2, hf, hFcard⟩
  have hF3 : 3 < Nat.card F := by
    rw [hFcard]
    omega
  let isoHom : PGammaL2 F →* MulAut (PSL2 F) :=
    pGammaL2ToMulAutPSL2 F hFodd hF3
  have hisoInj : Function.Injective isoHom :=
    pGammaL2ToMulAutPSL2_injective F hFodd hF3
  have hisoSrj : Function.Surjective isoHom :=
    pGammaL2ToMulAutPSL2_surjective F hFcard hFodd hF3
  let iso : PGammaL2 F ≃* MulAut (PSL2 F) :=
    MulEquiv.ofBijective isoHom ⟨hisoInj, hisoSrj⟩
  have hcomp :
      iso.symm.toMonoidHom.comp (MulAut.conj : PSL2 F →* MulAut (PSL2 F)) =
        (SemidirectProduct.inl : PGL2 F →* PGammaL2 F).comp
          (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)) := by
    apply MonoidHom.ext
    intro y
    change iso.symm (MulAut.conj y) =
      SemidirectProduct.inl
        (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F) y)
    rw [MulEquiv.symm_apply_eq]
    change MulAut.conj y = isoHom (SemidirectProduct.inl
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F) y))
    rw [pGammaL2ToMulAutPSL2_inl, pgl2InnerAutPSL2_toPGL]
  have hinner :
      (CFSG.ComponentClassification.OuterAutomorphisms.inner (PSL2 F)).map
        iso.symm.toMonoidHom = pGammaL2PSLRange F := by
    rw [show CFSG.ComponentClassification.OuterAutomorphisms.inner (PSL2 F) =
        (MulAut.conj : PSL2 F →* MulAut (PSL2 F)).range from rfl,
      MonoidHom.range_eq_map, Subgroup.map_map, hcomp]
    rw [← MonoidHom.range_eq_map]
    rfl
  let eOut : Outer K ≃* Outer (PSL2 F) :=
    CFSG.ComponentClassification.OuterAutomorphisms.equivalence e
  let qe : Outer (PSL2 F) ≃* (PGammaL2 F ⧸ pGammaL2PSLRange F) :=
    QuotientGroup.congr (G' := CFSG.ComponentClassification.OuterAutomorphisms.inner (PSL2 F))
      (H' := pGammaL2PSLRange F) iso.symm hinner
  have hcardOuter : Nat.card (Outer K) = (pGammaL2PSLRange F).index := by
    rw [Nat.card_congr eOut.toEquiv, Nat.card_congr qe.toEquiv, ← Subgroup.index_eq_card]
  have hcardPSL : Nat.card (pGammaL2PSLRange F) = Nat.card (PSL2 F) :=
    (Nat.card_congr (pGammaL2PSLRangeEquiv F).toEquiv).symm
  have hcardAut : Nat.card (F ≃+* F) = f :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp F hFcard).1
  have hcardPGamma : Nat.card (PGammaL2 F) =
      Nat.card (PGL2 F) * Nat.card (F ≃+* F) := by
    rw [PGammaL2, SemidirectProduct.card]
  have hcardPGL : Nat.card (PGL2 F) = 2 * Nat.card (PSL2 F) := by
    have hidx := pgl2_psl2Range_index_eq_two F hFodd
    have hrange : Nat.card
        ((Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range) =
        Nat.card (PSL2 F) :=
      (Nat.card_congr (psl2EquivToPGLRange F).toEquiv).symm
    have h := Subgroup.index_mul_card
      ((Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range)
    rw [hidx, hrange] at h
    exact h.symm
  have hidx : (pGammaL2PSLRange F).index = 2 * f := by
    have h := Subgroup.card_mul_index (pGammaL2PSLRange F)
    rw [hcardPSL, hcardPGamma, hcardAut, hcardPGL] at h
    have hpos : 0 < Nat.card (PSL2 F) := Nat.card_pos
    have h' : Nat.card (PSL2 F) * (pGammaL2PSLRange F).index =
        Nat.card (PSL2 F) * (2 * f) := by
      rw [h]
      ring
    exact Nat.mul_left_cancel hpos h'
  rw [hcardOuter, hidx]

theorem pgl2_sylow_two_card_eq_eight {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2)
    (h8 : Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5)
    (V : Sylow 2 (PGL2 F)) : Nat.card (V : Subgroup (PGL2 F)) = 8 := by
  classical
  let : Finite (PGL2 F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have hp : p.Prime := Fact.out
  have hfpos : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · rw [pow_zero] at hF
      rw [hF] at h8
      norm_num at h8
    · exact hf
  have hFodd : IsOddPrimePower (Nat.card F) :=
    ⟨p, f, hp, hp.odd_of_ne_two hp2, hfpos, hF⟩
  obtain ⟨u, hu, hcard⟩ := pgl2_card_eq_eight_mul_odd hF hp2 h8
  have h8dvd : 2 ^ 3 ∣ Nat.card (V : Subgroup (PGL2 F)) := by
    refine Sylow.pow_dvd_card_of_pow_dvd_card V ?_
    rw [hcard]
    exact ⟨u, by norm_num⟩
  have h16 : ¬ 2 ^ 4 ∣ Nat.card (V : Subgroup (PGL2 F)) := by
    intro h
    apply hu.not_two_dvd_nat
    have hdvd : 2 ^ 4 ∣ Nat.card (PGL2 F) := h.trans (Subgroup.card_subgroup_dvd_card _)
    rw [hcard] at hdvd
    obtain ⟨c, hc⟩ := hdvd
    omega
  obtain ⟨m, hm, ⟨eD⟩⟩ := pgl2_odd_hasDihedralSylowTwo_model F hFodd V
  have hVcard : Nat.card (V : Subgroup (PGL2 F)) = 2 * 2 ^ m := by
    rw [Nat.card_congr eD.toEquiv, DihedralGroup.nat_card]
  have h8dvd' : 2 ^ 3 ∣ 2 * 2 ^ m := by simpa [hVcard] using h8dvd
  have h16' : ¬ 2 ^ 4 ∣ 2 * 2 ^ m := by simpa [hVcard] using h16
  have hpow8 : 2 ^ 3 ∣ 2 ^ (m + 1) := by
    simpa [pow_succ'] using h8dvd'
  have hpow16 : ¬ 2 ^ 4 ∣ 2 ^ (m + 1) := by
    simpa [pow_succ'] using h16'
  have hmge : 3 ≤ m + 1 :=
    (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp hpow8
  have hmle : m + 1 < 4 := by
    by_contra h
    exact hpow16
      ((Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mpr (by omega))
  have hm2 : m = 2 := by omega
  rw [hVcard, hm2]
  norm_num

theorem pgl2_sylow_two_noncommutative {F : Type} [Field F] [Finite F] {p f : ℕ}
    [Fact p.Prime] (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2)
    (h8 : Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5)
    (V : Sylow 2 (PGL2 F)) : ¬ IsMulCommutative (V : Subgroup (PGL2 F)) := by
  have hp : p.Prime := Fact.out
  have hfpos : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · rw [pow_zero] at hF
      rw [hF] at h8
      norm_num at h8
    · exact hf
  have hFodd : IsOddPrimePower (Nat.card F) :=
    ⟨p, f, hp, hp.odd_of_ne_two hp2, hfpos, hF⟩
  obtain ⟨m, hm, ⟨eD⟩⟩ := pgl2_odd_hasDihedralSylowTwo_model F hFodd V
  have hVcard : Nat.card (V : Subgroup (PGL2 F)) = 2 * 2 ^ m := by
    rw [Nat.card_congr eD.toEquiv, DihedralGroup.nat_card]
  have hV8 : Nat.card (V : Subgroup (PGL2 F)) = 8 :=
    pgl2_sylow_two_card_eq_eight hF hp2 h8 V
  have hm2 : m = 2 := by
    have hcard8 : 2 * 2 ^ m = 8 := by rw [← hVcard, hV8]
    have hpow : 2 ^ (m + 1) = 2 ^ 3 := by
      rw [pow_succ', hcard8]
      norm_num
    have hm1 : m + 1 = 3 :=
      Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpow
    omega
  intro hcomm
  have hcommD : IsMulCommutative (DihedralGroup (2 ^ m)) := by
    refine ⟨⟨fun a b => ?_⟩⟩
    apply eD.symm.injective
    rw [map_mul, map_mul]
    exact hcomm.is_comm.comm _ _
  rw [hm2] at hcommD
  have hnc : ¬ IsMulCommutative (DihedralGroup 4) := by
    intro h
    have hcomm' : DihedralGroup.r (1 : ZMod 4) * DihedralGroup.sr (0 : ZMod 4) =
        DihedralGroup.sr (0 : ZMod 4) * DihedralGroup.r (1 : ZMod 4) :=
      h.is_comm.comm _ _
    revert hcomm'
    decide
  exact hnc hcommD

theorem centralizer_reeLin_false {X : Type} [Group X] [Finite X] {L K : Subgroup X}
    (hKL : K ≤ L) (hKn : K.Normal)
    (hKC : Subgroup.centralizer (K : Set X) = ⊥)
    [hKs : IsSimpleGroup ↥K]
    (hL8 : ∀ S : Sylow 2 ↥L, Nat.card (S : Subgroup ↥L) = 8)
    (hLab : ∀ S : Sylow 2 ↥L, IsMulCommutative (S : Subgroup ↥L))
    {t : ↥L} (ht : orderOf t = 2)
    (hC24 : Nat.card ↥(Subgroup.centralizer ({t} : Set ↥L)) = 24)
    {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 0 < f) (h5 : 5 ≤ p ^ f)
    (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5)
    (e : ↥K ≃* PSL(2, GaloisField p f)) : False := by
  classical
  let F := GaloisField p f
  have hp : p.Prime := Fact.out
  have hFcard : Nat.card F = p ^ f := GaloisField.card p f (by omega)
  have hFodd : IsOddPrimePower (Nat.card F) :=
    ⟨p, f, hp, hp.odd_of_ne_two hp2, hf, hFcard⟩
  have hF3 : 3 < Nat.card F := by
    rw [hFcard]
    omega
  have h8F : Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5 := by
    simpa [hFcard] using h8
  have hfodd : Odd f := odd_of_pow_mod_eight hp2 h8
  haveI : K.Normal := hKn
  have hLnorm : L ≤ Subgroup.normalizer (K : Set X) := Subgroup.le_normalizer_of_normal
  let ψ : ↥L →* MulAut ↥K :=
    K.normalizerMonoidHom.comp (Subgroup.inclusion hLnorm)
  have hψker : ∀ x : ↥L, x ∈ ψ.ker ↔ ((x : X) ∈ Subgroup.centralizer (K : Set X)) := by
    intro x
    constructor
    · intro hx
      have hx' : K.normalizerMonoidHom ⟨(x : X), hLnorm x.2⟩ = 1 := hx
      have hx'' : ⟨(x : X), hLnorm x.2⟩ ∈ K.normalizerMonoidHom.ker := by
        simpa [MonoidHom.mem_ker] using hx'
      rw [Subgroup.normalizerMonoidHom_ker] at hx''
      exact Subgroup.mem_subgroupOf.mp hx''
    · intro hx
      rw [MonoidHom.mem_ker]
      apply MulEquiv.ext
      intro k
      apply Subtype.ext
      have hc : (k : X) * (x : X) = (x : X) * (k : X) :=
        Subgroup.mem_centralizer_iff.mp hx (k : X) k.2
      calc (x : X) * (k : X) * (x : X)⁻¹ = (k : X) * (x : X) * (x : X)⁻¹ := by
            rw [← hc]
        _ = (k : X) := by group
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    ext x
    rw [Subgroup.mem_bot]
    constructor
    · intro hx
      exact Subtype.ext (by
        have hxcent := (hψker x).mp hx
        rw [hKC] at hxcent
        exact Subgroup.mem_bot.mp hxcent)
    · intro hx
      subst hx
      exact (hψker 1).mpr (by simp)
  let S : Sylow 2 ↥L := Classical.choice Sylow.nonempty
  have hScard : Nat.card (S : Subgroup ↥L) = 8 := hL8 S
  have hScomm : IsMulCommutative (S : Subgroup ↥L) := hLab S
  let T : Subgroup (MulAut ↥K) := (S : Subgroup ↥L).map ψ
  have hTcard : Nat.card T = 8 := by
    rw [Subgroup.card_map_of_injective hψinj, hScard]
  have hTcomm : IsMulCommutative T := by
    let eST : ↥(S : Subgroup ↥L) ≃* ↥T :=
      (S : Subgroup ↥L).equivMapOfInjective ψ hψinj
    refine ⟨⟨fun a b => ?_⟩⟩
    apply eST.symm.injective
    rw [map_mul, map_mul]
    exact hScomm.is_comm.comm _ _
  have hTp : IsPGroup 2 T :=
    IsPGroup.of_card (n := 3) (by rw [hTcard]; norm_num)
  obtain ⟨U, hTU⟩ := hTp.exists_le_sylow
  have hcenter : Subgroup.center ↥K = ⊥ :=
    center_eq_bot_of_mulEquiv e (psl2_center_eq_bot F)
  have hconj : Function.Injective (MulAut.conj : ↥K →* MulAut ↥K) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hmem : a ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h := congrArg (fun f : MulAut ↥K => f g) ha
      rw [MulAut.conj_apply, MulAut.one_apply] at h
      calc g * a = a * g * a⁻¹ * a := by rw [h]
        _ = a * g := by group
    rw [hcenter] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hinnerCard :
      Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥K) =
        Nat.card ↥K := by
    change Nat.card (MulAut.conj : ↥K →* MulAut ↥K).range = Nat.card ↥K
    exact (Nat.card_congr (MonoidHom.ofInjective hconj).toEquiv).symm
  have hOuterCard : Nat.card (Outer ↥K) = 2 * f :=
    nat_card_outer_odd_psl2 hp2 hf h5 hfodd e
  obtain ⟨-, w, hw, hK4⟩ := odd_elim_reduction hp2 hf h5 h8 e
  have hMulAutCard : Nat.card (MulAut ↥K) = Nat.card ↥K * Nat.card (Outer ↥K) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥K)
    rw [hinnerCard] at h
    exact h.trans (mul_comm _ _)
  have hMulAut8 : ∃ v : ℕ, Odd v ∧ Nat.card (MulAut ↥K) = 8 * v := by
    refine ⟨w * f, Nat.odd_mul.mpr ⟨hw, hfodd⟩, ?_⟩
    rw [hMulAutCard, hK4, hOuterCard]
    ring
  have hMulAut16 : ¬ 16 ∣ Nat.card (MulAut ↥K) := by
    obtain ⟨v, hv, hvcard⟩ := hMulAut8
    rw [hvcard]
    intro h
    obtain ⟨c, hc⟩ := h
    exact hv.not_two_dvd_nat ⟨c, by omega⟩
  have hU8dvd : 8 ∣ Nat.card (U : Subgroup (MulAut ↥K)) := by
    have h := Subgroup.card_dvd_of_le hTU
    rwa [hTcard] at h
  have hU16 : ¬ 16 ∣ Nat.card (U : Subgroup (MulAut ↥K)) := fun h =>
    hMulAut16 (h.trans (Subgroup.card_subgroup_dvd_card _))
  let k := (Nat.card (MulAut ↥K)).factorization 2
  have hUpow : Nat.card (U : Subgroup (MulAut ↥K)) = 2 ^ k :=
    Sylow.card_eq_multiplicity U
  have hk : k = 3 := by
    have h8dvd : 2 ^ 3 ∣ 2 ^ k := by simpa [hUpow] using hU8dvd
    have h16dvd : ¬ 2 ^ 4 ∣ 2 ^ k := by simpa [hUpow] using hU16
    have hkge : 3 ≤ k :=
      (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp h8dvd
    have hklt : k < 4 := by
      by_contra h
      exact h16dvd
        ((Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mpr (by omega))
    omega
  have hU8 : Nat.card (U : Subgroup (MulAut ↥K)) = 8 := by
    rw [hUpow, hk]
    norm_num
  have hTUeq : T = (U : Subgroup (MulAut ↥K)) := by
    refine Subgroup.eq_of_le_of_card_ge hTU ?_
    rw [hTcard, hU8]
  have hUcomm : IsMulCommutative (U : Subgroup (MulAut ↥K)) := by
    rw [← hTUeq]
    exact hTcomm
  let autIso : PGammaL2 F ≃* MulAut (PSL2 F) :=
    MulEquiv.ofBijective (pGammaL2ToMulAutPSL2 F hFodd hF3)
      ⟨pGammaL2ToMulAutPSL2_injective F hFodd hF3,
        pGammaL2ToMulAutPSL2_surjective F hFcard hFodd hF3⟩
  let isoA : MulAut ↥K ≃* PGammaL2 F :=
    (MulAut.congr e).trans autIso.symm
  let U' : Subgroup (PGammaL2 F) := (U : Subgroup (MulAut ↥K)).map isoA.toMonoidHom
  have hU'card : Nat.card U' = 8 := by
    rw [Subgroup.card_map_of_injective isoA.injective, hU8]
  have hfield : ∀ u : ↥U, (isoA (u : MulAut ↥K)).right = 1 := by
    intro u
    obtain ⟨n, hn⟩ := U.isPGroup'.exists_orderOf_eq_pow u
    have huPow : ((u : MulAut ↥K)) ^ 2 ^ n = 1 := by
      have hu : u ^ 2 ^ n = 1 := by rw [← hn, pow_orderOf_eq_one]
      exact congrArg (fun z : ↥U => (z : MulAut ↥K)) hu
    have hrightPow : ((isoA (u : MulAut ↥K)).right) ^ 2 ^ n = 1 := by
      have hpow : (isoA (u : MulAut ↥K)) ^ 2 ^ n = 1 := by
        rw [← map_pow, huPow, map_one]
      have h := congrArg (SemidirectProduct.rightHom) hpow
      rw [map_pow] at h
      simpa using h
    have hAutCard : Nat.card (F ≃+* F) = f :=
      (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp F hFcard).1
    have hordAut : orderOf ((isoA (u : MulAut ↥K)).right) ∣ f := by
      have hdvd := orderOf_dvd_natCard ((isoA (u : MulAut ↥K)).right)
      rwa [hAutCard] at hdvd
    have hordPow : orderOf ((isoA (u : MulAut ↥K)).right) ∣ 2 ^ n :=
      orderOf_dvd_of_pow_eq_one hrightPow
    have hcop : Nat.Coprime (2 ^ n) f :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hfodd)
    exact orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes hcop hordPow hordAut)
  have hU'le : U' ≤ pGammaL2PGLRange F := by
    rintro x ⟨u, hu, rfl⟩
    rw [pGammaL2PGLRange, SemidirectProduct.range_inl_eq_ker_rightHom]
    exact MonoidHom.mem_ker.mpr (hfield ⟨u, hu⟩)
  let H : Subgroup (PGL2 F) :=
    (U'.subgroupOf (pGammaL2PGLRange F)).map
      (pGammaL2PGLRangeEquiv F).symm.toMonoidHom
  have hHcard : Nat.card H = 8 := by
    rw [Subgroup.card_map_of_injective (pGammaL2PGLRangeEquiv F).symm.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU'le).toEquiv, hU'card]
  have hHp : IsPGroup 2 H :=
    IsPGroup.of_card (n := 3) (by rw [hHcard]; norm_num)
  let : Finite (PGL2 F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  obtain ⟨V, hHV⟩ := hHp.exists_le_sylow
  have hVcard : Nat.card (V : Subgroup (PGL2 F)) = 8 :=
    pgl2_sylow_two_card_eq_eight hFcard hp2 h8F V
  have hVnc : ¬ IsMulCommutative (V : Subgroup (PGL2 F)) :=
    pgl2_sylow_two_noncommutative hFcard hp2 h8F V
  have hHVeq : H = (V : Subgroup (PGL2 F)) := by
    refine Subgroup.eq_of_le_of_card_ge hHV ?_
    rw [hHcard, hVcard]
  have hHnc : ¬ IsMulCommutative H := by
    rw [hHVeq]
    exact hVnc
  let eUU' : ↥(U : Subgroup (MulAut ↥K)) ≃* ↥U' :=
    (U : Subgroup (MulAut ↥K)).equivMapOfInjective isoA.toMonoidHom isoA.injective
  let eU'H : ↥U' ≃* ↥H :=
    (Subgroup.subgroupOfEquivOfLe hU'le).symm.trans
      ((U'.subgroupOf (pGammaL2PGLRange F)).equivMapOfInjective
        (pGammaL2PGLRangeEquiv F).symm.toMonoidHom
        (pGammaL2PGLRangeEquiv F).symm.injective)
  have hHcomm : IsMulCommutative H := by
    refine ⟨⟨fun a b => ?_⟩⟩
    apply (eUU'.trans eU'H).symm.injective
    rw [map_mul, map_mul]
    exact hUcomm.is_comm.comm _ _
  exact hHnc hHcomm

end CFSG.LocalAnalysis.UniquenessCase.UC22

end

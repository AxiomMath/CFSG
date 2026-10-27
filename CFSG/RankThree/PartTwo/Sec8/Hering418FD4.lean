module

public import CFSG.RankThree.PartTwo.Sec8.Hering418FD4U
public import CFSG.RankThree.PartTwo.Sec8.Hering418FD4OT
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofD4

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF418
open CFSG.Open (IsElemAbelian ordTwistedA)
open CFSG.Assembly.RankThreeEven (projSL projSU projImage)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix
open scoped commutatorElement

section D4


variable {G : Type} [Group G] [Finite G] {L K : Subgroup G} {a b : G}

theorem Cfg.false_of_isoGTwoEven
    (c : Cfg L K a b) (hK : K ∈ thetaComponentsIn (L ⊓ Subgroup.centralizer {b}))
    {n : ℕ} (hn : 1 ≤ n) (htype : IsType418 (K ⧸ aschbacherSolvableCore 3 K) n) {f : ℕ}
    (hf : 1 ≤ f) (hC : Sec8.IsoGTwoEven (Sec8.barCentralizer (Subgroup.zpowers b) L) f)
    (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥)
    (hinn : ∃ j : ℕ, c.alpha * c.beta ^ j ∈ innBar L) : False := by
  have hKq := Sec6.isQuasisimple_of_mem_thetaComponentsIn hK
  obtain ⟨k, _, _, hk, ⟨eC⟩⟩ := hC
  by_cases hf1 : f = 1
  ·
    subst hf1
    obtain ⟨kk, hkk⟩ := c.exists_nine_dvd_orderOf_rhoK (hasNineQuot_of_isType418 hn hKq htype)
    set z : L ⧸ aschbacherSolvableCore 3 L :=
      ((⟨(kk : G), c.hKL kk.2⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) with hz
    have hρ : rhoK c.hKL kk = MulAut.conj z := rho_eq_conj L (c.hKL kk.2)
    have hz9 : 9 ∣ orderOf z := by
      have h1 : orderOf (MulAut.conj z) = orderOf z :=
        orderOf_injective _ (conj_injective_of_center_eq_bot hZ) z
      rw [← h1, ← hρ]
      exact hkk
    have hzK : z ∈ Sec8.imageModTheta L K :=
      ⟨⟨kk, c.hKL kk.2⟩, Subgroup.mem_subgroupOf.mpr kk.2, rfl⟩
    have hzC : z ∈ Sec8.barCentralizer (Subgroup.zpowers b) L :=
      Sec8.Item86ResProof.imageModTheta_le_barCentralizer c.hbL c.hKb hzK
    set g := eC ⟨z, hzC⟩ with hg
    have hgo : orderOf g = orderOf z := by
      rw [hg, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    obtain ⟨t, ht⟩ : 9 ∣ orderOf g := hgo ▸ hz9
    have ht0 : t ≠ 0 := by
      rintro rfl
      have := orderOf_pos g
      omega
    have hdvd : t ∣ orderOf g := ⟨9, by rw [ht, mul_comm]⟩
    have h9 : orderOf (g ^ t) = 9 := by
      rw [orderOf_pow_of_dvd ht0 hdvd, ht, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero ht0)]
    exact Sec8.Item86ResProof.kF83GTwoTwo_holds k (by rw [hk]; norm_num) (g ^ t) h9
  ·
    have hf2 : 2 ≤ f := by omega
    have hmodel : Blueprint.ChevalleyExceptionalModel
        ↥(Sec8.barCentralizer (Subgroup.zpowers b) L) .G2 2 f := by
      refine ⟨⟨Nat.prime_two, hf, rfl, ?_⟩, k, inferInstance, inferInstance, hk, ⟨?_⟩⟩
      · calc 3 ≤ 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
      · exact eC.trans (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq
          (center_adjointGroup_eq_bot (τ := Tag.G2) (K := k)).symm))
    have hsimple := (CFSG.LieType.Simplicity.fam_g2_simplicity _ 2 f hmodel).2
    have hC := barCentralizer_le_imageModTheta_of_simple c.hbL c.hb3 hK hsimple
      (imageModTheta_ne_bot c.hKL hKq)
    exact c.false_of_outer_core hZ hinn hC

theorem eq_one_of_conj_eq_one {X : Type*} [Group X] (hZ : Subgroup.center X = ⊥) {x : X}
    (h : (MulAut.conj x : MulAut X) = 1) : x = 1 := by
  have h1 : x ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h2 := congrArg (fun f : MulAut X => f g) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at h2
    exact (mul_inv_eq_iff_eq_mul.mp h2).symm
  rw [hZ] at h1
  exact h1

end D4

section PGL

variable {X : Type} [Group X]

theorem exists_core_of_pgl {C : Subgroup X} {f : ℕ} {π : Bool} {F : Type} [Field F]
    (hPi : Sec4.PiField π 2 f F) (hq2 : 2 < 2 ^ f)
    (Φ : ↥C ≃* ↥(projImage (Sec4.glPi π 3 (2 ^ f) F))) :
    ∃ Q : Subgroup X, Q ≤ C ∧ ⁅C, C⁆ ≤ Q ∧ IsSimpleGroup ↥Q ∧ ¬ Group.IsSolvable ↥Q ∧
      Nonempty (↥Q ≃* ↥(projImage (Sec4.slPi π 3 (2 ^ f) F))) := by
  have := hPi.finite
  have hπ : π = false → UnitaryFieldData 2 f F := fun h => by subst h; exact hPi.unitary
  have hSP : projImage (Sec4.slPi π 3 (2 ^ f) F) ≤ projImage (Sec4.glPi π 3 (2 ^ f) F) :=
    Subgroup.map_mono (Sec4.slPi_le_glPi hπ)
  have hcomm := Sec13.commutator_projImage_glPi hPi hq2
  set M := projImage (Sec4.glPi π 3 (2 ^ f) F) with hM
  set P := projImage (Sec4.slPi π 3 (2 ^ f) F) with hP
  set R : Subgroup ↥M := P.subgroupOf M with hR
  let ι : ↥((R.map Φ.symm.toMonoidHom).map C.subtype) ≃* ↥P :=
    (Subgroup.equivMapOfInjective (R.map Φ.symm.toMonoidHom) C.subtype
      C.subtype_injective).symm.trans
      ((Subgroup.equivMapOfInjective R Φ.symm.toMonoidHom Φ.symm.injective).symm.trans
        (Subgroup.subgroupOfEquivOfLe hSP))
  haveI hs : IsSimpleGroup ↥P := Item8KFacts2Proof.isSimpleGroup_projImage_slPi hPi hq2
  refine ⟨(R.map Φ.symm.toMonoidHom).map C.subtype, Subgroup.map_subtype_le _, ?_, ι.isSimpleGroup,
    ?_, ⟨ι⟩⟩
  · rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    refine ⟨⁅(⟨g₁, hg₁⟩ : ↥C), ⟨g₂, hg₂⟩⁆, ⟨Φ ⁅(⟨g₁, hg₁⟩ : ↥C), ⟨g₂, hg₂⟩⁆, ?_, by simp⟩, rfl⟩
    rw [map_commutatorElement, SetLike.mem_coe, ← hcomm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  · intro hsolv
    haveI : Group.IsSolvable ↥P :=
      Group.isSolvable_of_isSolvable_injective (f := ι.symm.toMonoidHom) ι.symm.injective
    haveI : Group.IsPerfect ↥P := Sec13.isPerfect_projImage_slPi hPi hq2
    exact Group.IsPerfect.not_isSolvable ↥P inferInstance

end PGL

section Class2


theorem exists_fixed_order_four_pgl_model {G : Type} [Group G]
    [Finite G] {K : Subgroup G} {a : G} {f : ℕ} (hf : 1 ≤ f) (hq2 : 2 < 2 ^ f) {π : Bool}
    {F : Type} [Field F] (hPi : Sec4.PiField π 2 f F) (hpar : cond π (Even f) (Odd f))
    (θ : K ⧸ aschbacherSolvableCore 3 K ≃* ↥(projImage (Sec4.slPi π 3 (2 ^ f) F)))
    (hKa : KFacts.InducesStdKind K a .field) (haK : a ∈ Subgroup.normalizer (K : Set G))
    (ha3 : a ^ 3 = 1) :
    ∃ y : K ⧸ aschbacherSolvableCore 3 K,
      Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨a, haK⟩) y = y ∧ y ^ 4 = 1 ∧ y ^ 2 ≠ 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFfin := hPi.finite
  cases π with
  | true =>
    have hfe : Even f := hpar
    have hsl : projSL 3 F = projImage (Sec4.slPi true 3 (2 ^ f) F) :=
      Sec4.projSL_eq_projImage (2 ^ f) F
    have hFcard : Nat.card F = 2 ^ f := hPi.card
    obtain ⟨ψ⟩ : Nonempty (F ≃+* GaloisField 2 f) :=
      nonempty_ringEquiv_of_card_eq (K := GaloisField 2 f) (K' := F)
        (by rw [hFcard, GaloisField.card 2 f (by omega)])
    let θ2 : K ⧸ aschbacherSolvableCore 3 K ≃* projSL 3 (GaloisField 2 f) :=
      (θ.trans (MulEquiv.subgroupCongr hsl.symm)).trans
        ((Sec4.projSLEquivProjectiveSL 3 F).trans
          ((Sec21.Item223CensusResProof.psOfSL (Sec21.Item223CensusResProof.slEquiv ψ 3)).trans
            (Sec4.projSLEquivProjectiveSL 3 (GaloisField 2 f)).symm))
    exact exists_fixed_order_four_lThree hfe hf θ2 hKa haK
  | false =>
    have hfo : Odd f := hpar
    have hf2 : 2 ≤ f := by
      by_contra h
      have : f = 1 := by omega
      subst this
      norm_num at hq2
    have hF := hPi.unitary
    have hGF := Sec4.unitaryFieldData_galoisField 2 f hf
    have hFcard : Nat.card F = (2 ^ f) ^ 2 := hPi.card
    obtain ⟨ψ⟩ : Nonempty (F ≃+* GaloisField 2 (2 * f)) :=
      nonempty_ringEquiv_of_card_eq (K := GaloisField 2 (2 * f)) (K' := F)
        (by rw [hFcard, GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm])
    let θ2 : K ⧸ aschbacherSolvableCore 3 K ≃* projSU 3 2 f :=
      (θ.trans (Sec4.psuEquivUnitary hF)).trans
        ((Sec21.Item223CensusResProof.psuEquiv ψ hGF hF hq2).trans
          (Sec4.projSUEquivUnitaryPSU 2 f hGF).symm)
    exact exists_fixed_order_four_uThree hfo hf2 θ2 hKa haK ha3

theorem charP_two_of_piField {π : Bool} {f : ℕ} {F : Type} [Field F]
    (hPi : Sec4.PiField π 2 f F) : CharP F 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hPi.finite
  haveI : Fintype F := Fintype.ofFinite F
  cases π with
  | true =>
    exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hPi.card]; rfl)
  | false =>
    exact charP_of_card_eq_prime_pow (f := 2 * f) (by
      rw [← Nat.card_eq_fintype_card, hPi.card, Sec4.piCard, Bool.cond_false, ← pow_mul,
        mul_comm])

section Cfgs

variable {G : Type} [Group G] [Finite G] {L K : Subgroup G} {a b : G}

theorem Cfg.false_of_solvable_centralizer (c : Cfg L K a b)
    (hK : K ∈ thetaComponentsIn (L ⊓ Subgroup.centralizer {b}))
    (hsolv : Group.IsSolvable ↥(Sec8.barCentralizer (Subgroup.zpowers b) L)) : False := by
  have hKq := Sec6.isQuasisimple_of_mem_thetaComponentsIn hK
  have hle : Sec8.imageModTheta L K ≤ Sec8.barCentralizer (Subgroup.zpowers b) L :=
    imageModTheta_le_barCentralizer_of_le c.hbL c.hb3 c.hKL c.hKb
  haveI hP := isPerfect_imageModTheta hK
  have hne : Sec8.imageModTheta L K ≠ ⊥ := imageModTheta_ne_bot c.hKL hKq
  haveI : Nontrivial ↥(Sec8.imageModTheta L K) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  haveI := hsolv
  haveI : Group.IsSolvable ↥(Sec8.imageModTheta L K) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  exact Group.IsPerfect.not_isSolvable ↥(Sec8.imageModTheta L K) inferInstance


theorem Cfg.false_of_pgl_class (c : Cfg L K a b)
    (hK : K ∈ thetaComponentsIn (L ⊓ Subgroup.centralizer {b}))
    (hKa : KFacts.InducesStdKind K a .field) (hβ : Sec4.InducesOuterTheta b L)
    (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥)
    (hOTC : KFacts.OutThreeCyclic (L ⧸ aschbacherSolvableCore 3 L))
    {f : ℕ} (hf : 1 ≤ f) {π : Bool} {F : Type} [Field F] (hPi : Sec4.PiField π 2 f F)
    (hpar : cond π (Even f) (Odd f))
    (Φ : ↥(Sec8.barCentralizer (Subgroup.zpowers b) L) ≃*
      ↥(projImage (Sec4.glPi π 3 (2 ^ f) F))) : False := by
  haveI := hPi.finite
  by_cases hq2 : 2 < 2 ^ f
  · haveI := charP_two_of_piField hPi
    obtain ⟨Q, hQC, hQcomm, hQs, hQns, ⟨ιQ⟩⟩ := exists_core_of_pgl hPi hq2 Φ
    obtain ⟨Ψ, hΨ⟩ := c.exists_mulEquiv_of_simple_core hK hQC hQcomm hQs hQns
    obtain ⟨y, hyfix, hy4, hy2⟩ := exists_fixed_order_four_pgl_model hf hq2 hPi hpar
      (Ψ.trans ιQ) hKa c.haK c.ha3
    let ι : K ⧸ aschbacherSolvableCore 3 K →* L ⧸ aschbacherSolvableCore 3 L :=
      Q.subtype.comp Ψ.toMonoidHom
    have hι : Function.Injective ι := Subtype.val_injective.comp Ψ.injective
    set u : L ⧸ aschbacherSolvableCore 3 L := ι y with hu
    have hu4 : u ^ 4 = 1 := by rw [hu, ← map_pow, hy4, map_one]
    have hu2 : u ^ 2 ≠ 1 := by
      rw [hu, ← map_pow]
      intro h
      exact hy2 (hι (h.trans (map_one ι).symm))
    have hαu : c.alpha u = u := by
      have h1 := hΨ y
      rw [hyfix] at h1
      exact h1.symm
    have huC : u ∈ Sec8.barCentralizer (Subgroup.zpowers b) L := hQC (Ψ y).2
    have hβu : c.beta u = u := (KFacts.mem_barCentralizer_zpowers_iff c.hbL u).mp huC
    have hcomm : Commute c.beta c.alpha := c.alpha_mul_beta.symm
    obtain ⟨i, -, x, hx⟩ := hOTC c.beta c.alpha hcomm c.beta_pow_three c.alpha_pow_three hβ.2
    have hτu : (c.beta ^ i * c.alpha) u = u := by
      rw [MulAut.mul_apply, hαu]
      exact pow_apply_eq_of_apply_eq hβu i
    have hτ3 : (c.beta ^ i * c.alpha) ^ 3 = 1 := by
      rw [(hcomm.pow_left i).mul_pow, c.alpha_pow_three, mul_one, ← pow_mul, mul_comm, pow_mul,
        c.beta_pow_three, one_pow]
    have hx3 : x ^ 3 = 1 := by
      apply eq_one_of_conj_eq_one hZ
      rw [map_pow, hx, hτ3]
    have hxu : x * u * x⁻¹ = u := by
      have h1 : MulAut.conj x u = u := by rw [hx]; exact hτu
      simpa [MulAut.conj_apply] using h1
    have hxβ : c.beta x = x := by
      apply conj_injective_of_center_eq_bot hZ
      change MulAut.conj (c.beta x) = MulAut.conj x
      rw [← KFacts.mul_mulAutConj_mul_inv c.beta x, hx]
      have hc : Commute c.beta (c.beta ^ i * c.alpha) :=
        ((Commute.refl c.beta).pow_right i).mul_right hcomm
      rw [hc.eq, mul_inv_cancel_right]
    have hxC : x ∈ Sec8.barCentralizer (Subgroup.zpowers b) L :=
      (KFacts.mem_barCentralizer_zpowers_iff c.hbL x).mpr hxβ
    let xC : ↥(Sec8.barCentralizer (Subgroup.zpowers b) L) := ⟨x, hxC⟩
    let uC : ↥(Sec8.barCentralizer (Subgroup.zpowers b) L) := ⟨u, huC⟩
    have hxC3 : xC ^ 3 = 1 := Subtype.ext (by simpa [xC] using hx3)
    have huC4 : uC ^ 4 = 1 := Subtype.ext (by simpa [uC] using hu4)
    have hΦx3 : ((Φ xC : ↥(projImage (Sec4.glPi π 3 (2 ^ f) F))) :
        Matrix.ProjGenLinGroup (Fin 3) F) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, ← map_pow, hxC3, map_one, Subgroup.coe_one]
    have hΦu4 : ((Φ uC : ↥(projImage (Sec4.glPi π 3 (2 ^ f) F))) :
        Matrix.ProjGenLinGroup (Fin 3) F) ^ 4 = 1 := by
      rw [← Subgroup.coe_pow, ← map_pow, huC4, map_one, Subgroup.coe_one]
    have hΦu2 : ((Φ uC : ↥(projImage (Sec4.glPi π 3 (2 ^ f) F))) :
        Matrix.ProjGenLinGroup (Fin 3) F) ^ 2 ≠ 1 := by
      intro h
      apply hu2
      have h1 : Φ (uC ^ 2) = 1 := by
        rw [map_pow]
        exact Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact h)
      have h2 : uC ^ 2 = 1 := Φ.injective (by rw [h1, map_one])
      simpa [uC] using congrArg Subtype.val h2
    have hΦxu : ((Φ xC : ↥(projImage (Sec4.glPi π 3 (2 ^ f) F))) :
          Matrix.ProjGenLinGroup (Fin 3) F) *
        ((Φ uC : ↥(projImage (Sec4.glPi π 3 (2 ^ f) F))) : Matrix.ProjGenLinGroup (Fin 3) F) *
          ((Φ xC : ↥(projImage (Sec4.glPi π 3 (2 ^ f) F))) :
            Matrix.ProjGenLinGroup (Fin 3) F)⁻¹ =
        ((Φ uC : ↥(projImage (Sec4.glPi π 3 (2 ^ f) F))) : Matrix.ProjGenLinGroup (Fin 3) F) := by
      have h1 : Φ xC * Φ uC * (Φ xC)⁻¹ = Φ uC := by
        rw [← map_inv, ← map_mul, ← map_mul]
        exact congrArg Φ (Subtype.ext hxu)
      exact congrArg Subtype.val h1
    have hΦx1 : ((Φ xC : ↥(projImage (Sec4.glPi π 3 (2 ^ f) F))) :
        Matrix.ProjGenLinGroup (Fin 3) F) = 1 := eq_one_of_pgl3_fixed hΦx3 hΦxu hΦu4 hΦu2
    have hxC1 : xC = 1 := Φ.injective (by rw [map_one]; exact Subtype.ext hΦx1)
    have hx0 : x = 1 := congrArg Subtype.val hxC1
    have hτ1 : c.beta ^ i * c.alpha = 1 := by rw [← hx, hx0, map_one]
    apply c.hαβ (i : ℤ)
    rw [zpow_natCast, (hcomm.pow_left i).symm.eq]
    exact hτ1
  ·
    have hf1 : f = 1 := by
      by_contra hne
      have hf2 : 2 ≤ f := by omega
      exact hq2 (calc 2 < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2)
    have h2 : 2 ^ f = 2 := by rw [hf1]; norm_num
    cases π with
    | true => exact absurd hpar (by rw [hf1]; decide)
    | false =>
      haveI : Group.IsSolvable ↥(projImage (Sec4.glPi false 3 (2 ^ f) F)) :=
        Sec13.isSolvable_projImage_glPi_two hPi h2
      exact c.false_of_solvable_centralizer hK
        (Group.isSolvable_of_isSolvable_injective (f := Φ.toMonoidHom) Φ.injective)

end Cfgs

end Class2

end CFSG.RankThree.PartTwo.Sec8.Hering418

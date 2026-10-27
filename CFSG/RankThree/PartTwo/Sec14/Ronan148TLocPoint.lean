module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148TLocDefs
public import CFSG.RankThree.PartTwo.Sec4.Item41Narrow
import CFSG.RankThree.PartTwo.Sec14.Item142L3ResProofListBar
import CFSG.RankThree.PartTwo.Sec14.Item14Res8ProofHessConj
import CFSG.RankThree.PartTwo.Sec14.Ronan148HPointK
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item13Res4ProofAlpha
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.Sec15.Item1423ProofTools
import CFSG.RankThree.PartTwo.Sec4.Census.Cover46
import CFSG.RankThree.PartTwo.Sec14.Item142L3ResProofHessList

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148T

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS CFSG.RankThree.PartTwo.Sec14
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.RankThree.PartTwo.Sec4 (slPi)
open Matrix (ProjGenLinGroup)

variable {G : Type} [Group G] [Finite G]

theorem sigmaOf_eq_conj_mk {L : Subgroup G} {y : G} (hyL : y ∈ L)
    (hyN : y ∈ Subgroup.normalizer (L : Set G)) :
    L3PGL.sigmaOf L hyN =
      MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨y, hyL⟩) := by
  ext z
  induction z using QuotientGroup.induction_on with
  | H z =>
    rw [MulAut.conj_apply, QuotientGroup.mk'_apply, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    rfl

theorem fixSubgroup_conj {X : Type} [Group X] (z : X) :
    Res5Types.fixSubgroup (MulAut.conj z) = Subgroup.centralizer ({z} : Set X) := by
  ext x
  rw [Res5Types.mem_fixSubgroup, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc x * z = z * x * z⁻¹ * z := by rw [h]
      _ = z * x := by group
  · intro h
    rw [← h, mul_inv_cancel_right]

theorem locA_fixA_hess {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) (hcL : c ∉ L)
    (hAc : A = Subgroup.zpowers c ⊔ (A ⊓ L)) (h9 : Nat.card (A ⊓ L : Subgroup G) = 9)
    (hQ8 : Nonempty (Sec4.autIn L A ≃* QuaternionGroup 2) ∨
      Nonempty (Sec4.autIn L A ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)))
    (hL3 : IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :
    LocA A L ∧ IsPGroup 3 (L3PGL.fixA A L) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.toSec13Data
  have hcA := hD.mem_A
  have hc3 : c ^ 3 = 1 := hD.isElemAbelian.2 c hcA
  have hLc : ∀ l ∈ L, l * c = c * l := fun l hl =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer hl))
  have hAL : A ≤ Subgroup.normalizer (L : Set G) := hD.mem_lA.2.1
  have hB : CFSG.Assembly.IsElemAbelian 3 (A ⊓ L) :=
    ⟨⟨⟨fun x y => Subtype.ext (hD.commute x.2.1 y.2.1)⟩⟩,
      fun x hx => hD.isElemAbelian.2 x hx.1⟩
  have hLq : CFSG.IsQuasisimple (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    Sec15.Proof1423.isQuasisimple_of_mem_thetaComponentsIn1423
      (M := Subgroup.centralizer ({c} : Set G)) hD.mem_thetaComponentsAt
  have hLp : Group.IsPerfect (↥L ⧸ aschbacherSolvableCore 3 ↥L) := hLq.1
  have : Nontrivial (↥L ⧸ aschbacherSolvableCore 3 ↥L) := LocalCores.isQuasisimple_nontrivial hLq
  have hZ := center_eq_bot_of_isLThreePi hL3 hLp
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set π := QuotientGroup.mk' θ with hπ
  set Eb := ((A ⊓ L).subgroupOf L).map π with hEb
  have hE9 : Nat.card Eb = 9 := Res5Gen.card_image_inf h h9
  have hEq : (A ⊓ L).subgroupOf L = A.subgroupOf L := Subgroup.inf_subgroupOf_right A L
  have hEe : CFSG.Assembly.IsElemAbelian 3 Eb := by
    rw [hEb, hEq]
    exact CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 π (A.subgroupOf L)
      (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_subgroupOf 3 A L hD.isElemAbelian)
  have hpt : ∀ z ∈ Eb, z ≠ 1 → ∃ y ∈ A ⊓ L, y ≠ 1 ∧ ∃ hyL : y ∈ L, π ⟨y, hyL⟩ = z := by
    rintro z ⟨y', hy', rfl⟩ hz1
    refine ⟨y', Subgroup.mem_subgroupOf.mp hy', fun hy1 => hz1 ?_, y'.2, rfl⟩
    have : y' = 1 := Subtype.ext hy1
    rw [this, map_one]
  have htrans : ∀ y₀ ∈ Eb, y₀ ≠ 1 → ∀ y₁ ∈ Eb, y₁ ≠ 1 →
      ∃ w ∈ Subgroup.normalizer (Eb : Set (↥L ⧸ θ)), w * y₀ * w⁻¹ = y₁ := by
    intro z₀ hz₀ hz₀1 z₁ hz₁ hz₁1
    obtain ⟨y₀, hy₀, hy₀1, hy₀L, rfl⟩ := hpt z₀ hz₀ hz₀1
    obtain ⟨y₁, hy₁, hy₁1, hy₁L, rfl⟩ := hpt z₁ hz₁ hz₁1
    obtain ⟨w, hwL, hwN, hw⟩ :=
      exists_conj_eq_of_autIn hc3 hcL hLc hAc hB h9 hQ8 hy₀ hy₁ hy₀1 hy₁1
    refine ⟨π ⟨w, hwL⟩, ?_, ?_⟩
    · have hwN' : (⟨w, hwL⟩ : ↥L) ∈ Subgroup.normalizer
          (((A ⊓ L).subgroupOf L : Subgroup ↥L) : Set ↥L) := by
        rw [Subgroup.mem_normalizer_iff]
        intro x
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
        exact Subgroup.mem_normalizer_iff.mp hwN (x : G)
      exact Subgroup.le_normalizer_map π ⟨_, hwN', rfl⟩
    · rw [← map_mul, ← map_inv, ← map_mul]
      congr 1
      exact Subtype.ext hw
  have hσ : ∀ (y : G) (hyAL : y ∈ A ⊓ L),
      L3PGL.sigmaOf L (hAL hyAL.1) = MulAut.conj (π ⟨y, hyAL.2⟩) :=
    fun y hyAL => sigmaOf_eq_conj_mk hyAL.2 (hAL hyAL.1)
  obtain ⟨p, e, hp, he, hiso⟩ := hL3
  obtain ⟨πm, K, _, hKm, hq, τ, hτ, hτ1, dM, cM, hdM, hcM, hdc, hdo, hco, hcd, Φ, hΦE⟩ :=
    Res8Hess.exists_hessian_equiv he hiso hEe hE9 htrans
  have := hKm.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  set Ê := Subgroup.zpowers dM ⊔ Subgroup.zpowers cM with hÊ
  have hφE : Eb.map Φ.symm.toMonoidHom = Ê := by
    ext x
    rw [← hΦE, Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
    simp
  have hEbσ : ∀ z ∈ Eb, MulAut.conj z ∈ Sec4.autThetaQuot A L := by
    rintro _ ⟨⟨y, hyL⟩, hy, rfl⟩
    have hyAL : y ∈ A ⊓ L := Subgroup.mem_subgroupOf.mp hy
    rw [← hσ y hyAL]
    exact Sec4.mem_autThetaQuot_iff.mpr ⟨y, hAL hyAL.1, hyAL.1, rfl⟩
  constructor
  · intro Y hY3 hYE
    have hEbY : Eb ≤ Subgroup.normalizer (Y : Set (↥L ⧸ θ)) := by
      intro z hz
      refine Subgroup.mem_normalizer_fintype fun x hx => ?_
      have h1 := hYE _ (hEbσ z hz)
      exact h1 ⟨x, hx, rfl⟩
    set Y' := Y.map Φ.symm.toMonoidHom with hY'
    have hY'3 : ¬ 3 ∣ Nat.card Y' := by
      rwa [hY', Subgroup.card_map_of_injective Φ.symm.injective]
    have hÊY' : Ê ≤ Subgroup.normalizer (Y' : Set (projImage (slPi πm 3 (p ^ e) K))) := by
      rw [← hφE, hY']
      rintro _ ⟨z, hz, rfl⟩
      rw [← Subgroup.map_equiv_normalizer_eq]
      exact ⟨z, hEbY hz, rfl⟩
    obtain ⟨b, hb, hb1, hY'b⟩ := L3PGL.hess_le_thetaC hτ hτ1 hKm hq hdM hcM hdc hdo hco hcd
      hY'3 hÊY'
    have hΦb : Φ b ∈ Eb := by
      rw [← hΦE]
      exact ⟨b, hb, rfl⟩
    obtain ⟨⟨y, hyL⟩, hyAL, hyb⟩ := hΦb
    have hyAL' : y ∈ A ⊓ L := Subgroup.mem_subgroupOf.mp hyAL
    refine ⟨y, hyAL'.1, hAL hyAL'.1, ?_, ?_⟩
    · rw [hσ y hyAL']
      intro h1
      apply hb1
      have h2 : π ⟨y, hyAL'.2⟩ ∈ Subgroup.center (↥L ⧸ θ) := by
        rw [Subgroup.mem_center_iff]
        intro w
        have h3 := congrArg (fun σ : MulAut (↥L ⧸ θ) => σ w) h1
        simp only [MulAut.conj_apply, MulAut.one_apply] at h3
        calc w * π ⟨y, hyAL'.2⟩ = π ⟨y, hyAL'.2⟩ * w * (π ⟨y, hyAL'.2⟩)⁻¹ * π ⟨y, hyAL'.2⟩ := by
              rw [h3]
          _ = π ⟨y, hyAL'.2⟩ * w := by group
      rw [hZ, Subgroup.mem_bot] at h2
      have h4 : Φ b = 1 := by
        rw [← hyb]
        exact h2
      exact (map_eq_one_iff Φ Φ.injective).mp h4
    · rw [hσ y hyAL', fixSubgroup_conj]
      have hYY : Y = Y'.map Φ.toMonoidHom := by
        rw [hY', Subgroup.map_map]
        ext w
        simp
      rw [hYY]
      refine (Subgroup.map_mono hY'b).trans (le_of_eq ?_)
      rw [Res8Hess.thetaC_map_equiv Φ b]
      change Res8Hess.thetaC (Φ b) = _
      rw [← hyb]
  ·
    have hle : L3PGL.fixA A L ≤ (Subgroup.centralizer (Ê : Set (projImage (slPi πm 3 (p ^ e) K)))).map
        Φ.toMonoidHom := by
      intro x hx
      refine ⟨Φ.symm x, ?_, by simp⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro b hb
      have hb' : Φ b ∈ Eb := by
        rw [← hΦE]
        exact ⟨b, hb, rfl⟩
      have h1 := hx _ (hEbσ _ hb')
      rw [MulAut.conj_apply] at h1
      apply Φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      calc Φ b * x = Φ b * x * (Φ b)⁻¹ * Φ b := by group
        _ = x * Φ b := by rw [h1]
    exact ((L3PGL.hess_centralizer_isPGroup hτ hτ1 hdM hcM).map Φ.toMonoidHom).to_le hle

theorem two_or_le_two_of_sec13 (h41 : Sec4.Item4_1LargePrime) {A L : Subgroup G} {c : G}
    (hD : Sec13Data G A c L) :
    ∀ (p e : ℕ) [Fact p.Prime], 1 ≤ e →
      Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e → p = 2 ∨ e ≤ 2 := by
  intro p e _ he hiso
  have hst := hD.toPartTwoStanding
  have hc1 := hD.ne_one
  set C := Subgroup.centralizer ({c} : Set G) with hCdef
  obtain ⟨hLC, hL'⟩ := mem_thetaComponentsIn_iff.mp hD.mem_thetaComponentsAt
  have hCtop : C ≠ ⊤ := by
    intro hCt
    have hcZ : c ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr fun g => by
      have hg : g ∈ C := hCt ▸ Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.mp hg
    rcases hst.isSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · rw [h, Subgroup.mem_bot] at hcZ
      exact hc1 hcZ
    · obtain ⟨a, b, hab⟩ := hst.nonabelian
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  have hS4 : SectionFourHyp C := hst.toTheoremFourHyp.sectionFourHyp hCtop
  have hS := Sec4.Item41Narrow.sectionFourHyp_thetaQuotient h41 hS4 hL'
  set e₀ := Subgroup.subgroupOfEquivOfLe hLC with he₀
  let φ : ↥(L.subgroupOf C) ⧸ aschbacherSolvableCore 3 ↥(L.subgroupOf C) ≃*
      ↥L ⧸ aschbacherSolvableCore 3 ↥L :=
    QuotientGroup.congr _ _ e₀ (aschbacherSolvableCore_map_mulEquiv Nat.prime_three e₀)
  exact Sec4.Census.two_or_le_two_of_isoLThreePi hS he
    (Ronan148K.isoLThreePi_of_mulEquiv φ.symm hiso)


theorem locA_fixA_of_std (h131 : Item131) {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (hL3 : IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :
    LocA A L ∧ IsPGroup 3 (L3PGL.fixA A L) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.toSec13Data
  have hspor := Sec13.sporadicModels131
  have hLq : CFSG.IsQuasisimple (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    Sec15.Proof1423.isQuasisimple_of_mem_thetaComponentsIn1423
      (M := Subgroup.centralizer ({c} : Set G)) hD.mem_thetaComponentsAt
  have hLp : Group.IsPerfect (↥L ⧸ aschbacherSolvableCore 3 ↥L) := hLq.1
  have : Nontrivial (↥L ⧸ aschbacherSolvableCore 3 ↥L) := LocalCores.isQuasisimple_nontrivial hLq
  have hZ := center_eq_bot_of_isLThreePi hL3 hLp
  have hcL' : c ∉ L := not_mem_of_center_eq_bot hD hZ
  rcases cases131 h131 hspor slTwoCenter hD with
      ⟨hcL, h9AL, -, hcase⟩ | ⟨-, -, hcase, -⟩ | ⟨-, hPGLA, -, hx⟩ | ⟨hcL, -⟩
  · rcases hcase with ⟨-, hQ8⟩ | ⟨⟨φ⟩, -⟩ | ⟨⟨φ⟩, -⟩
    ·
      have hA : Late.IsE27 A := h.isE27'
      have hcA := hD.mem_A
      have hAc : A = Subgroup.zpowers c ⊔ (A ⊓ L) := by
        have hcAL : Subgroup.zpowers c ≤ A := Subgroup.zpowers_le.mpr hcA
        have hle : Subgroup.zpowers c ⊔ (A ⊓ L) ≤ A := sup_le hcAL inf_le_left
        have hcomm : ∀ x ∈ Subgroup.zpowers c, ∀ y ∈ A ⊓ L, x * y = y * x := fun x hx y hy =>
          hD.commute (hcAL hx) hy.1
        have hdisj : Subgroup.zpowers c ⊓ (A ⊓ L) = ⊥ := by
          rw [eq_bot_iff, ← Sec4.Census.inf_zpowers_eq_bot_of_not_mem Nat.prime_three
            hD.orderOf_eq hcL]
          exact fun x hx => ⟨hx.2.2, hx.1⟩
        have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm).1
        rw [hdisj, Subgroup.card_bot, mul_one, Nat.card_zpowers, hD.orderOf_eq, h9AL] at hcard
        exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hA.2])).symm
      exact locA_fixA_hess h hcL hAc h9AL hQ8 hL3
    · exact absurd hL3 (not_isLThreePi_of_mulEquiv φ not_isoLThreePi_alternating_seven)
    · exact absurd hL3 (not_isLThreePi_of_mulEquiv φ KFacts.KS14.not_isoLThreePi_M22)
  ·
    obtain ⟨⟨hM22p, hM22z⟩, ⟨hM12p, hM12z⟩, ⟨hJ2p, hJ2z⟩⟩ := hspor
    rcases hcase with hφ | hφ
    · obtain ⟨φ⟩ := hφ
      obtain ⟨-, -, -, ⟨ψ⟩⟩ := facts_of_prod hD hM12p hM12z φ
      exact absurd hL3 (not_isLThreePi_of_mulEquiv ψ KFacts.KS14.not_isoLThreePi_M12)
    · obtain ⟨φ⟩ := hφ
      obtain ⟨-, -, -, ⟨ψ⟩⟩ := facts_of_prod hD hJ2p hJ2z φ
      exact absurd hL3 (not_isLThreePi_of_mulEquiv ψ KFacts.KS14.ks17J2NotList.1)
  ·
    exact L3PGL.list_bar h hPGLA hx
  · exact absurd hcL hcL'

theorem step148KThetaL3_of_loc (h131 : Item131) (h46 : Sec4.Item4_6)
    (h41 : Sec4.Item4_1LargePrime) (hKF : KF148SigL3Loc) : Step148KThetaL3 := by
  intro G _ _ A c L h Y hY hs hYB B Q e K Le hP he hLe hL3
  have hD : Sec13Data G A e Le :=
    { h.toSec13Data with zpowers_mem_omegaA := he, mem_lA := hLe }
  have h' : Sec14Std G A e Le := { h with toSec13Data := hD }
  obtain ⟨hloc, hfix⟩ := locA_fixA_of_std h131 h' hL3
  have hK := hP.2.2.2.2.2.1
  have hKe : K ≤ Subgroup.centralizer ({e} : Set G) :=
    (le_of_mem_thetaComponentsIn hK).trans inf_le_right
  have he3 : e ^ 3 = 1 := hD.isElemAbelian.2 e hD.mem_A
  have hK46 : Sec4.IsList46 (↥K ⧸ aschbacherSolvableCore 3 ↥K) :=
    Ronan148H.isList46_of_perfect_le_centralizer h46 h.toTheoremFourHyp he3 hP.2.2.2.2.1 hKe
      (isPerfect_of_mem_thetaComponentsIn hK) (Sec6.isQuasisimple_of_mem_thetaComponentsIn hK)
  exact hKF G A Le K e (Res7Sig.sig148_of_isPoint148 h hYB hP) hLe.2.2.1 hL3
    (Sec13.Res4Proof.exists_isList46 h46 hD) (two_or_le_two_of_sec13 h41 hD) hloc hfix hK46

end CFSG.RankThree.PartTwo.Sec14.Ronan148T

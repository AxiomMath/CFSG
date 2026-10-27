module

public import CFSG.RankThree.PartTwo.Sec14.Item142L3Res3ProofPowCore
public import CFSG.RankThree.PartTwo.Sec14.Item142L3Res3ProofPowAut
public import CFSG.RankThree.PartTwo.Sec14.Item142L3ResProofInner
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec15.Item1423ProofTools
import CFSG.RankThree.PartTwo.Sec4.Census.Lift46
import CFSG.RankThree.PartTwo.Sec14.Item142L3Res2ProofNorm
import CFSG.RankThree.PartTwo.Sec14.Item142L3ResProofTypesCent
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec4 (slPi glPi PiField ModThree slPi_le_glPi diagTau_mem_slPi
  cycThree_mem_slPi diagTau cycThree projOf coe_projOf)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open Matrix (ProjGenLinGroup)
open scoped commutatorElement

namespace L3PGLPow

variable {G : Type} [Group G] [Finite G]

open CFSG.RankThree.PartTwo.Sec14.L3PGL (sigmaOf)

theorem sigmaOf_comm_of_commute {L : Subgroup G} {a b : G}
    (haN : a ∈ Subgroup.normalizer (L : Set G)) (hbN : b ∈ Subgroup.normalizer (L : Set G))
    (hab : a * b = b * a) : sigmaOf L haN * sigmaOf L hbN = sigmaOf L hbN * sigmaOf L haN := by
  rw [sigmaOf, sigmaOf, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
  congr 2
  exact Subtype.ext hab

theorem sigmaOf_eq_conj {L : Subgroup G} {β : G} (hβL : β ∈ L)
    (z : ↥L ⧸ aschbacherSolvableCore 3 ↥L) :
    sigmaOf L (Subgroup.le_normalizer hβL) z =
      QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨β, hβL⟩ * z *
        (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨β, hβL⟩)⁻¹ := by
  induction z using QuotientGroup.induction_on with
  | H l =>
    have e1 : sigmaOf L (Subgroup.le_normalizer hβL) (l : ↥L ⧸ aschbacherSolvableCore 3 ↥L) =
        QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)
          (L.normalizerMonoidHom ⟨β, Subgroup.le_normalizer hβL⟩ l) :=
      Sec4.thetaQuotMulAut_mk _ l
    have e2 : L.normalizerMonoidHom ⟨β, Subgroup.le_normalizer hβL⟩ l =
        ⟨β, hβL⟩ * l * (⟨β, hβL⟩ : ↥L)⁻¹ :=
      Subtype.ext rfl
    rw [e1, e2, map_mul, map_mul, map_inv]
    rfl

theorem conj_eq_self_iff {X : Type*} [Group X] (x z : X) : x * z * x⁻¹ = z ↔ z * x = x * z := by
  rw [mul_inv_eq_iff_eq_mul, eq_comm]

end L3PGLPow

open CFSG.RankThree.PartTwo.Sec14.L3PGL (sigmaOf) in
open L3PGLPow in
theorem step142TypesL3InnerPowCent_proof :
    Step142TypesL3InnerPowCent := by
  intro G _ _ A c L h Q hQ hK hL3 hprod hQ8 _ _
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.toSec13Data
  have : (ker142 A (lB A) c).Normal := ker142_normal hD.isElemAbelian.1 hD.mem_A
  have hLq : CFSG.IsQuasisimple (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    Sec15.Proof1423.isQuasisimple_of_mem_thetaComponentsIn1423
      (M := Subgroup.centralizer ({c} : Set G)) hD.mem_thetaComponentsAt
  have hLp : Group.IsPerfect (↥L ⧸ aschbacherSolvableCore 3 ↥L) := hLq.1
  have : Nontrivial (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    LocalCores.isQuasisimple_nontrivial hLq
  have hZ := center_eq_bot_of_isLThreePi hL3 hLp
  have hcL : c ∉ L := not_mem_of_center_eq_bot hD hZ
  obtain ⟨φ⟩ := hprod
  have h9 : Nat.card (A ⊓ L : Subgroup G) = 9 := card_inf_eq_nine hD (isPerfect_lBar hD) φ
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
    rw [hdisj, Subgroup.card_bot, mul_one, Nat.card_zpowers, hD.orderOf_eq, h9] at hcard
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hA.2])).symm
  have hLK : L ≤ k142 A (lB A) c := by
    rw [hK]
    exact le_sup_left.trans le_sup_left
  have hRK : pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤ k142 A (lB A) c := by
    rw [hK]
    exact le_sup_right
  have d : Pow142 A c L := ⟨h, hK, fun V hV =>
    (Item148Point.le_sup_of_eq_zpowers_sup142 h hAc hV).trans (sup_le hLK hRK)⟩
  have hc3 : c ^ 3 = 1 := hD.isElemAbelian.2 c hcA
  have hLc : ∀ l ∈ L, l * c = c * l := fun l hl =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer hl))
  have hB : CFSG.Assembly.IsElemAbelian 3 (A ⊓ L) :=
    ⟨⟨⟨fun x y => Subtype.ext (hD.commute x.2.1 y.2.1)⟩⟩,
      fun x hx => hD.isElemAbelian.2 x hx.1⟩
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set πθ := QuotientGroup.mk' θ with hπθ
  set Eb := ((A ⊓ L).subgroupOf L).map πθ with hEb
  have hE9 : Nat.card Eb = 9 := Res5Gen.card_image_inf h h9
  have hEq : (A ⊓ L).subgroupOf L = A.subgroupOf L := Subgroup.inf_subgroupOf_right A L
  have hEe : CFSG.Assembly.IsElemAbelian 3 Eb := by
    rw [hEb, hEq]
    exact CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 πθ (A.subgroupOf L)
      (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_subgroupOf 3 A L hD.isElemAbelian)
  have hpt : ∀ z ∈ Eb, z ≠ 1 → ∃ y ∈ A ⊓ L, y ≠ 1 ∧ ∃ hyL : y ∈ L, πθ ⟨y, hyL⟩ = z := by
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
    refine ⟨πθ ⟨w, hwL⟩, ?_, ?_⟩
    · have hwN' : (⟨w, hwL⟩ : ↥L) ∈ Subgroup.normalizer
          (((A ⊓ L).subgroupOf L : Subgroup ↥L) : Set ↥L) := by
        rw [Subgroup.mem_normalizer_iff]
        intro x
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
        exact Subgroup.mem_normalizer_iff.mp hwN (x : G)
      exact Subgroup.le_normalizer_map πθ ⟨_, hwN', rfl⟩
    · rw [← map_mul, ← map_inv, ← map_mul]
      congr 1
      exact Subtype.ext hw
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
  have hEβ : ∀ z ∈ Eb, ∃ (β : G) (hβ : β ∈ A ⊓ L), πθ ⟨β, hβ.2⟩ = z := by
    rintro z ⟨⟨β, hβL⟩, hβ, rfl⟩
    exact ⟨β, Subgroup.mem_subgroupOf.mp hβ, rfl⟩
  have hlist : ∀ Y : Subgroup (↥L ⧸ θ), ¬ 3 ∣ Nat.card Y →
      (∀ σ ∈ Sec4.autThetaQuot A L, Y.map σ.toMonoidHom ≤ Y) →
      ∃ (a : G) (_ : a ∈ A) (haN : a ∈ Subgroup.normalizer (L : Set G)),
        sigmaOf L haN ≠ 1 ∧
          Y ≤ inSubgroup (aschbacherSolvableCore 3) (Res5Types.fixSubgroup (sigmaOf L haN)) := by
    intro Y hY3 hYinv
    have hEbY : Eb ≤ Subgroup.normalizer (Y : Set (↥L ⧸ θ)) := by
      intro z hz
      obtain ⟨β, hβ, rfl⟩ := hEβ z hz
      refine Subgroup.mem_normalizer_fintype fun y hy => ?_
      have hσ : sigmaOf L (Subgroup.le_normalizer hβ.2) ∈ Sec4.autThetaQuot A L :=
        Sec4.mem_autThetaQuot_iff.mpr ⟨β, Subgroup.le_normalizer hβ.2, hβ.1, rfl⟩
      have h1 := hYinv _ hσ ⟨y, hy, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, sigmaOf_eq_conj hβ.2 y] at h1
      exact h1
    set Y' := Y.map Φ.symm.toMonoidHom with hY'
    have hY'3 : ¬ 3 ∣ Nat.card Y' := by
      rw [hY', Subgroup.card_map_of_injective Φ.symm.injective]
      exact hY3
    have hÊY' : Ê ≤ Subgroup.normalizer (Y' : Set (projImage (slPi πm 3 (p ^ e) K))) := by
      rw [← hφE, hY', ← Subgroup.map_equiv_normalizer_eq]
      exact Subgroup.map_mono hEbY
    obtain ⟨b, hb, hb1, hYb⟩ :=
      L3PGL.hess_le_thetaC hτ hτ1 hKm hq hdM hcM hdc hdo hco hcd hY'3 hÊY'
    have hbE : Φ b ∈ Eb := by
      rw [← hΦE]
      exact ⟨b, hb, rfl⟩
    obtain ⟨β, hβ, hβb⟩ := hEβ _ hbE
    refine ⟨β, hβ.1, Subgroup.le_normalizer hβ.2, ?_, ?_⟩
    ·
      intro h1
      apply hb1
      have hcen : Φ b ∈ Subgroup.center (↥L ⧸ θ) := by
        rw [Subgroup.mem_center_iff]
        intro z
        have h2 := congrArg (fun σ : MulAut (↥L ⧸ θ) => σ z) h1
        simp only [MulAut.one_apply] at h2
        rw [sigmaOf_eq_conj hβ.2 z, hβb, conj_eq_self_iff] at h2
        exact h2
      rw [hZ, Subgroup.mem_bot] at hcen
      exact Φ.injective (hcen.trans (map_one Φ).symm)
    ·
      have hfix : Res5Types.fixSubgroup (sigmaOf L (Subgroup.le_normalizer hβ.2)) =
          Subgroup.centralizer ({Φ b} : Set (↥L ⧸ θ)) := by
        ext z
        rw [Res5Types.mem_fixSubgroup, sigmaOf_eq_conj hβ.2 z, hβb, conj_eq_self_iff,
          Subgroup.mem_centralizer_singleton_iff]
      rw [hfix]
      intro y hy
      have hy' : Φ.symm y ∈ Y' := ⟨y, hy, rfl⟩
      have h3 : y ∈ (Res8Hess.thetaC b).map Φ.toMonoidHom :=
        ⟨Φ.symm y, hYb hy', by simp⟩
      rw [Res8Hess.thetaC_map_equiv, Res8Hess.thetaC] at h3
      exact h3
  have hcomm : ∀ r₁ ∈ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)),
      ∀ r₂ ∈ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)),
      ∀ (h₁ : r₁ ∈ Subgroup.normalizer (L : Set G)) (h₂ : r₂ ∈ Subgroup.normalizer (L : Set G)),
        sigmaOf L h₁ * sigmaOf L h₂ = sigmaOf L h₂ * sigmaOf L h₁ := by
    intro r₁ hr₁ r₂ hr₂ hr₁N hr₂N
    have hπ : πm = false → UnitaryFieldData p e K := fun h => by subst h; exact hKm.unitary
    have hq2 : 2 < p ^ e := L3PGL.two_lt_of_model hLq hKm hq Φ.symm
    have hdS : diagTau hτ ∈ slPi πm 3 (p ^ e) K :=
      diagTau_mem_slPi hπ (fun h => by subst h; exact hq) hτ
    have hcS : (cycThree : GL (Fin 3) K) ∈ slPi πm 3 (p ^ e) K := cycThree_mem_slPi hπ
    have hd : diagTau hτ ∈ glPi πm 3 (p ^ e) K := slPi_le_glPi hπ hdS
    have hc : (cycThree : GL (Fin 3) K) ∈ glPi πm 3 (p ^ e) K := slPi_le_glPi hπ hcS
    have hconjd : Res8Hess.conjM' hπ hd = MulAut.conj dM := by
      have hρd : projOf (slPi πm 3 (p ^ e) K) ⟨diagTau hτ, hdS⟩ = dM :=
        Subtype.ext (by rw [coe_projOf, hdM])
      rw [← hρd]
      exact L3PGLU.conjM'_eq_conj hπ ⟨diagTau hτ, hdS⟩
    have hconjc : Res8Hess.conjM' hπ hc = MulAut.conj cM := by
      have hρc : projOf (slPi πm 3 (p ^ e) K) ⟨cycThree, hcS⟩ = cM :=
        Subtype.ext (by rw [coe_projOf, hcM])
      rw [← hρc]
      exact L3PGLU.conjM'_eq_conj hπ ⟨cycThree, hcS⟩
    have hτcomm : ∀ (r : G) (_ : r ∈ Subgroup.centralizer (A : Set G))
        (hrN : r ∈ Subgroup.normalizer (L : Set G)) (x : projImage (slPi πm 3 (p ^ e) K)),
        x ∈ Ê → Commute (MulAut.congr Φ.symm (sigmaOf L hrN)) (MulAut.conj x) := by
      intro r hrA hrN x hx
      have hxE : Φ x ∈ Eb := by
        rw [← hΦE]
        exact ⟨x, hx, rfl⟩
      obtain ⟨β, hβ, hβx⟩ := hEβ _ hxE
      have hσx : MulAut.congr Φ.symm (sigmaOf L (Subgroup.le_normalizer hβ.2)) =
          MulAut.conj x := by
        ext m
        rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, sigmaOf_eq_conj hβ.2,
          hβx, MulAut.conj_apply]
        simp
      rw [← hσx]
      show _ * _ = _ * _
      rw [← map_mul, ← map_mul, sigmaOf_comm_of_commute hrN (Subgroup.le_normalizer hβ.2)
        ((Subgroup.mem_centralizer_iff.mp hrA β hβ.1).symm)]
    have hr₁A : r₁ ∈ Subgroup.centralizer (A : Set G) := pPrimeCoreOf_le 3 _ hr₁
    have hr₂A : r₂ ∈ Subgroup.centralizer (A : Set G) := pPrimeCoreOf_le 3 _ hr₂
    have hdÊ : dM ∈ Ê := Subgroup.mem_sup_left (Subgroup.mem_zpowers dM)
    have hcÊ : cM ∈ Ê := Subgroup.mem_sup_right (Subgroup.mem_zpowers cM)
    have h1d := hτcomm r₁ hr₁A hr₁N dM hdÊ
    have h1c := hτcomm r₁ hr₁A hr₁N cM hcÊ
    have h2d := hτcomm r₂ hr₂A hr₂N dM hdÊ
    have h2c := hτcomm r₂ hr₂A hr₂N cM hcÊ
    rw [← hconjd] at h1d h2d
    rw [← hconjc] at h1c h2c
    have hcR : ⁅r₁, r₂⁆ ∈ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hr₁ hr₂) (inv_mem hr₁)) (inv_mem hr₂)
    have hcN : ⁅r₁, r₂⁆ ∈ Subgroup.normalizer (L : Set G) := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hr₁N hr₂N) (inv_mem hr₁N)) (inv_mem hr₂N)
    set n := orderOf ⁅r₁, r₂⁆ with hn
    have hn3 : ¬ 3 ∣ n := fun h3 =>
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
        (h3.trans (Subgroup.orderOf_dvd_natCard _ hcR))
    have hζ : ⁅MulAut.congr Φ.symm (sigmaOf L hr₁N), MulAut.congr Φ.symm (sigmaOf L hr₂N)⁆ =
        MulAut.congr Φ.symm (sigmaOf L hcN) := by
      rw [sigmaOf_commutator hr₁N hr₂N hcN, map_commutatorElement]
    have hζn : ⁅MulAut.congr Φ.symm (sigmaOf L hr₁N),
        MulAut.congr Φ.symm (sigmaOf L hr₂N)⁆ ^ n = 1 := by
      rw [hζ, ← map_pow]
      have h1 : (⟨⁅r₁, r₂⁆, hcN⟩ : Subgroup.normalizer (L : Set G)) ^ n = 1 :=
        Subtype.ext (by simp [hn, pow_orderOf_eq_one])
      rw [sigmaOf, ← map_pow, ← map_pow, h1, map_one, map_one, map_one]
    have hcomm := comm_of_commute_hess hπ hKm hq hq2 hτ hτ1 hc hd h1d h1c h2d h2c hn3 hζn
    apply (MulAut.congr Φ.symm).injective
    rw [map_mul, map_mul]
    exact hcomm
  exact d.typesOne_of_list_comm hQ hlist hcomm

theorem step142TypesL3InnerPow_proof :
    Step142TypesL3InnerPow :=
  step142TypesL3InnerPow_of step142TypesL3InnerPowCent_proof

end CFSG.RankThree.PartTwo.Sec14

module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoKyhat
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputs
import all CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoKy
import all CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoKyNormal
import all CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoKyhat
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoRankTwo
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoShapeB
import CFSG.GroupTheory.PRankCommutingPerfect
import CFSG.Quasithin.H13.U3S1348J

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace CaseTwoTransitive

variable {c : Ctx812E G} (t : CaseTwoTransitive c)

private theorem hperm_d : ∀ m ∈ t.d.M, ∀ i : Fin 3,
    ∃ j, (t.d.Lf i).map (MulAut.conj m).toMonoidHom = t.d.Lf j :=
  fun m hm i => t.hperm m (t.hdM ▸ hm) i

private theorem permHom_y_eq_cycle :
    t.d.permHom t.hinj (hperm_d t)
        ⟨t.y, t.hdM.symm ▸ t.hP.le t.hyP⟩ =
      Equiv.swap 0 1 * Equiv.swap 1 2 := by
  apply Equiv.ext
  intro i
  apply t.hinj
  rw [← t.d.map_conj_Lf_eq t.hinj (hperm_d t)
    ⟨t.y, t.hdM.symm ▸ t.hP.le t.hyP⟩ i, t.hyL i]
  fin_cases i <;> rfl

private theorem permHom_commute_of_centralizes {g : ↥t.Xz} (hgM : (g : G) ∈ c.S.M) :
    Commute
      (t.d.permHom t.hinj (hperm_d t) ⟨g, t.hdM.symm ▸ hgM⟩)
      (t.d.permHom t.hinj (hperm_d t) ⟨t.y, t.hdM.symm ▸ t.hP.le t.hyP⟩) := by
  show t.d.permHom t.hinj (hperm_d t) ⟨g, t.hdM.symm ▸ hgM⟩ *
      t.d.permHom t.hinj (hperm_d t) ⟨t.y, t.hdM.symm ▸ t.hP.le t.hyP⟩ =
    t.d.permHom t.hinj (hperm_d t) ⟨t.y, t.hdM.symm ▸ t.hP.le t.hyP⟩ *
      t.d.permHom t.hinj (hperm_d t) ⟨g, t.hdM.symm ▸ hgM⟩
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact Subgroup.mem_centralizer_singleton_iff.mp (t.Xz_le_centralizer g.2)

private theorem permHom_eq_one_of_orderOf_prime_to_three {g : ↥t.Xz}
    (hgM : (g : G) ∈ c.S.M) (hg3 : ¬ 3 ∣ orderOf g) :
    t.d.permHom t.hinj (hperm_d t) ⟨g, t.hdM.symm ▸ hgM⟩ = 1 := by
  let σ : Equiv.Perm (Fin 3) :=
    t.d.permHom t.hinj (hperm_d t) ⟨g, t.hdM.symm ▸ hgM⟩
  let τ : Equiv.Perm (Fin 3) :=
    t.d.permHom t.hinj (hperm_d t) ⟨t.y, t.hdM.symm ▸ t.hP.le t.hyP⟩
  have hcyc : τ = Equiv.swap 0 1 * Equiv.swap 1 2 := permHom_y_eq_cycle t
  have hcomm : Commute σ τ := permHom_commute_of_centralizes t hgM
  have hthree : ∀ σ : Equiv.Perm (Fin 3),
      σ * (Equiv.swap 0 1 * Equiv.swap 1 2) =
        (Equiv.swap 0 1 * Equiv.swap 1 2) * σ → σ ^ 3 = 1 := by decide
  have hσ3 : σ ^ 3 = 1 := hthree σ (by
    rw [hcyc] at hcomm
    exact hcomm)
  have hσn : σ ^ orderOf g = 1 := by
    have hgm : (⟨g, t.hdM.symm ▸ hgM⟩ : ↥t.d.M) ^ orderOf g = 1 := by
      have hord : orderOf (⟨g, t.hdM.symm ▸ hgM⟩ : ↥t.d.M) = orderOf g := by
        simpa using (Subgroup.orderOf_coe (⟨g, t.hdM.symm ▸ hgM⟩ : ↥t.d.M)).symm
      rw [← hord]
      exact pow_orderOf_eq_one _
    change (t.d.permHom t.hinj (hperm_d t) ⟨g, t.hdM.symm ▸ hgM⟩) ^ orderOf g = 1
    rw [← map_pow, hgm, map_one]
  have hcop : Nat.Coprime 3 (orderOf g) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hg3
  have hdvd3 : orderOf σ ∣ 3 := orderOf_dvd_of_pow_eq_one hσ3
  have hdvdn : orderOf σ ∣ orderOf g := orderOf_dvd_of_pow_eq_one hσn
  have hone : orderOf σ = 1 := by
    have hd : orderOf σ ∣ Nat.gcd 3 (orderOf g) := Nat.dvd_gcd hdvd3 hdvdn
    rw [hcop.gcd_eq_one] at hd
    exact Nat.dvd_one.mp hd
  exact orderOf_eq_one_iff.mp hone

private theorem normalizes_Lf {g : ↥t.Xz} (hgM : (g : G) ∈ c.S.M)
    (hg3 : ¬ 3 ∣ orderOf g) (i : Fin 3) :
    (g : G) ∈ Subgroup.normalizer (t.d.Lf i : Set G) := by
  have hσ := permHom_eq_one_of_orderOf_prime_to_three t hgM hg3
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hspec := t.d.map_conj_Lf_eq t.hinj (hperm_d t) ⟨g, t.hdM.symm ▸ hgM⟩ i
  rw [hσ] at hspec
  simpa using hspec

private theorem commutator_mem_Ky_inf_N (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) {g : ↥t.Xz}
    (hgM : (g : G) ∈ c.S.M)
    (hgK : ∀ k ∈ t.Kyhat, (QuotientGroup.mk g : t.Xhat) * k * (QuotientGroup.mk g)⁻¹ * k⁻¹ ∈
      t.O2Kyhat) (k : ↥t.Ky) :
    ⁅(g : G), (k : G)⁆ ∈ c.L ⊓ t.d.N := by
  classical
  have hKyX : t.Ky ≤ t.Xz := t.Ky_le_Xz hK32 hGA hSp
  have hkX : (k : G) ∈ t.Xz := hKyX k.2
  have hnorm := t.mem_normalizer_Ky_of_mem_M_of_mem_Xz hgM g.2
  rw [Subgroup.mem_normalizer_iff] at hnorm
  have hconj : (g : G) * (k : G) * (g : G)⁻¹ ∈ t.Ky := (hnorm (k : G)).mp k.2
  have hcommKy : ⁅(g : G), (k : G)⁆ ∈ t.Ky := by
    rw [commutatorElement_def]
    exact t.Ky.mul_mem hconj (t.Ky.inv_mem k.2)
  have hcommX : ⁅(g : G), (k : G)⁆ ∈ t.Xz := hKyX hcommKy
  let a : ↥t.Xz := ⟨⁅(g : G), (k : G)⁆, hcommX⟩
  let kX : ↥t.Xz := ⟨(k : G), hkX⟩
  have hkhat : (QuotientGroup.mk kX : t.Xhat) ∈ t.Kyhat :=
    Subgroup.mem_map.mpr ⟨kX, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩
  let π : ↥t.Xz →* t.Xhat := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥t.Xz)
  have hπa : π a ∈ t.O2Kyhat := by
    have h := hgK (QuotientGroup.mk kX) hkhat
    show π a ∈ t.O2Kyhat
    rw [show π a = ⁅π g, π kX⁆ by exact map_commutatorElement π g kX]
    rw [commutatorElement_def]
    rwa [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
  change π a ∈ Subgroup.map π ((t.Ky ⊓ t.d.N).subgroupOf t.Xz) at hπa
  obtain ⟨bX, hbX, hbXeq⟩ := Subgroup.mem_map.mp hπa
  have hbX' : (bX : G) ∈ t.Ky ⊓ t.d.N := Subgroup.mem_subgroupOf.mp hbX
  have hbKy : (bX : G) ∈ t.Ky := hbX'.1
  have hbN : (bX : G) ∈ t.d.N := hbX'.2
  have hker : a * bX⁻¹ ∈ CFSG.pPrimeCore 3 ↥t.Xz := by
    rw [← QuotientGroup.eq_one_iff]
    show π (a * bX⁻¹) = 1
    rw [map_mul, map_inv, ← hbXeq, mul_inv_cancel]
  have hkerKy : ((a * bX⁻¹ : ↥t.Xz) : G) ∈ t.Ky :=
    t.Ky.mul_mem hcommKy (t.Ky.inv_mem hbKy)
  have hkerN : ((a * bX⁻¹ : ↥t.Xz) : G) ∈ t.d.N := by
    have hmemOz : ((a * bX⁻¹ : ↥t.Xz) : G) ∈ t.Oz :=
      Subgroup.mem_map.mpr ⟨a * bX⁻¹, hker, rfl⟩
    exact t.Ky_inf_Oz_le hK32 hGA hSp (Subgroup.mem_inf.mpr ⟨hkerKy, hmemOz⟩)
  have haN : (a : G) ∈ t.d.N := by
    have hdecomp : (a : G) = ((a * bX⁻¹ : ↥t.Xz) : G) * (bX : G) := by
      simp
    rw [hdecomp]
    exact t.d.N.mul_mem hkerN hbN
  have haL : (a : G) ∈ c.L := (t.Ky_le hcommKy).1
  exact Subgroup.mem_inf.mpr ⟨haL, haN⟩


private noncomputable def gM {g : ↥t.Xz} (hgM : (g : G) ∈ c.S.M) : ↥t.M :=
  ⟨(g : G), hgM⟩

private noncomputable def kM (k : ↥t.Ky) : ↥t.M :=
  ⟨(k : G), t.Ky_le_M k.2⟩

private noncomputable def gbar {g : ↥t.Xz} (hgM : (g : G) ∈ c.S.M) : t.Mb :=
  t.qmk (gM t hgM)

private theorem gbar_mul_ybar {g : ↥t.Xz} (hgM : (g : G) ∈ c.S.M) :
    gbar t hgM * t.ybar = t.ybar * gbar t hgM := by
  have hgy : gM t hgM * t.yM = t.yM * gM t hgM := by
    apply Subtype.ext
    change (g : G) * t.y = t.y * (g : G)
    exact Subgroup.mem_centralizer_singleton_iff.mp (t.Xz_le_centralizer g.2)
  change t.qmk (gM t hgM) * t.qmk (t.yM) = t.qmk (t.yM) * t.qmk (gM t hgM)
  rw [← map_mul, ← map_mul, hgy]

private theorem gbar_mul_qmk_kM (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) {g : ↥t.Xz}
    (hgM : (g : G) ∈ c.S.M)
    (hgK : ∀ k ∈ t.Kyhat, (QuotientGroup.mk g : t.Xhat) * k * (QuotientGroup.mk g)⁻¹ * k⁻¹ ∈
      t.O2Kyhat) (k : ↥t.Ky) :
    gbar t hgM * t.qmk (kM t k) * (gbar t hgM)⁻¹ * (t.qmk (kM t k))⁻¹ = 1 := by
  have hmem := commutator_mem_Ky_inf_N t hK32 hGA hSp hgM hgK k
  have hKq : ⁅gM t hgM, kM t k⁆ ∈ t.Kq := by
    rw [Subgroup.mem_subgroupOf]
    exact hmem
  have h1 : t.qmk ⁅gM t hgM, kM t k⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr hKq
  rw [map_commutatorElement] at h1
  exact h1

private theorem gbar_commute_phiKy (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) {g : ↥t.Xz}
    (hgM : (g : G) ∈ c.S.M)
    (hgK : ∀ k ∈ t.Kyhat, (QuotientGroup.mk g : t.Xhat) * k * (QuotientGroup.mk g)⁻¹ * k⁻¹ ∈
      t.O2Kyhat) {z : t.Mb} (hz : z ∈ t.phiKy.range) :
    gbar t hgM * z * (gbar t hgM)⁻¹ = z := by
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hz
  have h := gbar_mul_qmk_kM t hK32 hGA hSp hgM hgK k
  rw [show t.phiKy k = t.qmk (kM t k) from rfl]
  calc gbar t hgM * t.qmk (kM t k) * (gbar t hgM)⁻¹ =
      (gbar t hgM * t.qmk (kM t k) * (gbar t hgM)⁻¹ * (t.qmk (kM t k))⁻¹) *
        t.qmk (kM t k) := by group
    _ = t.qmk (kM t k) := by rw [h, one_mul]

private theorem gbar_conj_mem_Lhat {g : ↥t.Xz} (hgM : (g : G) ∈ c.S.M)
    (hg3 : ¬ 3 ∣ orderOf g) {i : Fin 3} {x : t.Mb} (hx : x ∈ t.Lhat i) :
    gbar t hgM * x * (gbar t hgM)⁻¹ ∈ t.Lhat i := by
  obtain ⟨aM, haM, rfl⟩ := Subgroup.mem_map.mp hx
  have haLf : (aM : G) ∈ t.d.Lf i := Subgroup.mem_subgroupOf.mp haM
  have hga : (g : G) * (aM : G) * (g : G)⁻¹ ∈ t.d.Lf i :=
    (Subgroup.mem_normalizer_iff.mp (normalizes_Lf t hgM hg3 i) (aM : G)).mp haLf
  have hgaM : (g : G) * (aM : G) * (g : G)⁻¹ ∈ t.M :=
    t.M.mul_mem (t.M.mul_mem hgM aM.2) (t.M.inv_mem hgM)
  refine Subgroup.mem_map.mpr ⟨⟨(g : G) * (aM : G) * (g : G)⁻¹, hgaM⟩,
    Subgroup.mem_subgroupOf.mpr hga, ?_⟩
  change t.qmk ⟨(g : G) * (aM : G) * (g : G)⁻¹, hgaM⟩ =
    gbar t hgM * t.qmk aM * (gbar t hgM)⁻¹
  rw [gbar, ← map_mul, ← map_inv]
  rfl

private theorem gbar_centralizes_Lhat_zero (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) {g : ↥t.Xz}
    (hgM : (g : G) ∈ c.S.M) (hg3 : ¬ 3 ∣ orderOf g)
    (hgK : ∀ k ∈ t.Kyhat, (QuotientGroup.mk g : t.Xhat) * k * (QuotientGroup.mk g)⁻¹ * k⁻¹ ∈
      t.O2Kyhat) {x : t.Mb} (hx : x ∈ t.Lhat 0) :
    gbar t hgM * x * (gbar t hgM)⁻¹ = x := by
  let u : ↥(t.Lhat 0) := ⟨x, hx⟩
  have hdelta_mem : t.delta u ∈ t.phiKy.range := by
    have hz : t.delta u ∈ t.delta.range := ⟨u, rfl⟩
    have hz' : t.delta u ∈ (t.Ky.subgroupOf t.M).map (t.qmk) :=
      t.delta_range_le_image_Ky hz
    rwa [← t.phiKy_range] at hz'
  have hgcent : gbar t hgM * t.delta u * (gbar t hgM)⁻¹ = t.delta u :=
    gbar_commute_phiKy t hK32 hGA hSp hgM hgK hdelta_mem
  have hx' : gbar t hgM * x * (gbar t hgM)⁻¹ ∈ t.Lhat 0 :=
    gbar_conj_mem_Lhat t hgM hg3 hx
  have hconj_delta :
      gbar t hgM * t.delta u * (gbar t hgM)⁻¹ =
        t.delta ⟨gbar t hgM * x * (gbar t hgM)⁻¹, hx'⟩ := by
    rw [t.delta_apply, t.delta_apply]
    have hycomm := gbar_mul_ybar t hgM
    have hconj_y : gbar t hgM * t.ybar * (gbar t hgM)⁻¹ = t.ybar := by
      rw [hycomm]; group
    have hconj_y2 : gbar t hgM * t.ybar ^ 2 * (gbar t hgM)⁻¹ = t.ybar ^ 2 := by
      calc gbar t hgM * t.ybar ^ 2 * (gbar t hgM)⁻¹
          = (gbar t hgM * t.ybar * (gbar t hgM)⁻¹) *
              (gbar t hgM * t.ybar * (gbar t hgM)⁻¹) := by
            rw [pow_two]; group
        _ = t.ybar ^ 2 := by rw [hconj_y, pow_two]
    have hconj_yx : gbar t hgM * (t.ybar * x * t.ybar⁻¹) * (gbar t hgM)⁻¹ =
        t.ybar * (gbar t hgM * x * (gbar t hgM)⁻¹) * t.ybar⁻¹ := by
      calc gbar t hgM * (t.ybar * x * t.ybar⁻¹) * (gbar t hgM)⁻¹
          = (gbar t hgM * t.ybar * (gbar t hgM)⁻¹) *
              (gbar t hgM * x * (gbar t hgM)⁻¹) *
              (gbar t hgM * t.ybar * (gbar t hgM)⁻¹)⁻¹ := by group
        _ = t.ybar * (gbar t hgM * x * (gbar t hgM)⁻¹) * t.ybar⁻¹ := by
            rw [hconj_y]
    have hconj_y2x : gbar t hgM * (t.ybar ^ 2 * x * (t.ybar ^ 2)⁻¹) *
        (gbar t hgM)⁻¹ =
        t.ybar ^ 2 * (gbar t hgM * x * (gbar t hgM)⁻¹) * (t.ybar ^ 2)⁻¹ := by
      calc gbar t hgM * (t.ybar ^ 2 * x * (t.ybar ^ 2)⁻¹) * (gbar t hgM)⁻¹
          = (gbar t hgM * t.ybar ^ 2 * (gbar t hgM)⁻¹) *
              (gbar t hgM * x * (gbar t hgM)⁻¹) *
              (gbar t hgM * t.ybar ^ 2 * (gbar t hgM)⁻¹)⁻¹ := by group
        _ = t.ybar ^ 2 * (gbar t hgM * x * (gbar t hgM)⁻¹) * (t.ybar ^ 2)⁻¹ := by
            rw [hconj_y2]
    calc gbar t hgM * (x * (t.ybar * x * t.ybar⁻¹) *
          (t.ybar ^ 2 * x * (t.ybar ^ 2)⁻¹)) * (gbar t hgM)⁻¹
        = (gbar t hgM * x * (gbar t hgM)⁻¹) *
            (gbar t hgM * (t.ybar * x * t.ybar⁻¹) * (gbar t hgM)⁻¹) *
            (gbar t hgM * (t.ybar ^ 2 * x * (t.ybar ^ 2)⁻¹) * (gbar t hgM)⁻¹) := by
          group
      _ = (gbar t hgM * x * (gbar t hgM)⁻¹) *
            (t.ybar * (gbar t hgM * x * (gbar t hgM)⁻¹) * t.ybar⁻¹) *
            (t.ybar ^ 2 * (gbar t hgM * x * (gbar t hgM)⁻¹) *
              (t.ybar ^ 2)⁻¹) := by
          rw [hconj_yx, hconj_y2x]
  have hdelta_eq : t.delta ⟨gbar t hgM * x * (gbar t hgM)⁻¹, hx'⟩ = t.delta u :=
    hconj_delta.symm.trans hgcent
  have hux : (⟨gbar t hgM * x * (gbar t hgM)⁻¹, hx'⟩ : ↥(t.Lhat 0)) = u :=
    t.delta_injective (t.muL_injective hK32 hGA hSp) hdelta_eq
  exact congrArg Subtype.val hux


private theorem gbar_centralizes_Lhat_one (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) {g : ↥t.Xz}
    (hgM : (g : G) ∈ c.S.M) (hg3 : ¬ 3 ∣ orderOf g)
    (hgK : ∀ k ∈ t.Kyhat, (QuotientGroup.mk g : t.Xhat) * k * (QuotientGroup.mk g)⁻¹ * k⁻¹ ∈
      t.O2Kyhat) {x : t.Mb} (hx : x ∈ t.Lhat 1) :
    gbar t hgM * x * (gbar t hgM)⁻¹ = x := by
  have hx' : x ∈ (t.Lhat 0).map (MulAut.conj (t.ybar)).toMonoidHom := by
    rw [t.Lhat_conj 0]
    simpa using hx
  obtain ⟨x0, hx0, rfl⟩ := Subgroup.mem_map.mp hx'
  have hcomm := gbar_mul_ybar t hgM
  have hconj_y : gbar t hgM * t.ybar * (gbar t hgM)⁻¹ = t.ybar := by
    rw [hcomm]; group
  calc gbar t hgM * (t.ybar * x0 * t.ybar⁻¹) * (gbar t hgM)⁻¹
      = (gbar t hgM * t.ybar * (gbar t hgM)⁻¹) *
          (gbar t hgM * x0 * (gbar t hgM)⁻¹) *
          (gbar t hgM * t.ybar * (gbar t hgM)⁻¹)⁻¹ := by group
    _ = t.ybar * x0 * t.ybar⁻¹ := by
        rw [hconj_y, gbar_centralizes_Lhat_zero t hK32 hGA hSp hgM hg3 hgK hx0]

private theorem gbar_centralizes_Lhat_two (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) {g : ↥t.Xz}
    (hgM : (g : G) ∈ c.S.M) (hg3 : ¬ 3 ∣ orderOf g)
    (hgK : ∀ k ∈ t.Kyhat, (QuotientGroup.mk g : t.Xhat) * k * (QuotientGroup.mk g)⁻¹ * k⁻¹ ∈
      t.O2Kyhat) {x : t.Mb} (hx : x ∈ t.Lhat 2) :
    gbar t hgM * x * (gbar t hgM)⁻¹ = x := by
  have hx' : x ∈ (t.Lhat 1).map (MulAut.conj (t.ybar)).toMonoidHom := by
    rw [t.Lhat_conj 1]
    simpa using hx
  obtain ⟨x1, hx1, rfl⟩ := Subgroup.mem_map.mp hx'
  have hcomm := gbar_mul_ybar t hgM
  have hconj_y : gbar t hgM * t.ybar * (gbar t hgM)⁻¹ = t.ybar := by
    rw [hcomm]; group
  calc gbar t hgM * (t.ybar * x1 * t.ybar⁻¹) * (gbar t hgM)⁻¹
      = (gbar t hgM * t.ybar * (gbar t hgM)⁻¹) *
          (gbar t hgM * x1 * (gbar t hgM)⁻¹) *
          (gbar t hgM * t.ybar * (gbar t hgM)⁻¹)⁻¹ := by group
    _ = t.ybar * x1 * t.ybar⁻¹ := by
        rw [hconj_y, gbar_centralizes_Lhat_one t hK32 hGA hSp hgM hg3 hgK hx1]

private theorem gbar_commutes_image_L (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) {g : ↥t.Xz}
    (hgM : (g : G) ∈ c.S.M) (hg3 : ¬ 3 ∣ orderOf g)
    (hgK : ∀ k ∈ t.Kyhat, (QuotientGroup.mk g : t.Xhat) * k * (QuotientGroup.mk g)⁻¹ * k⁻¹ ∈
      t.O2Kyhat) {z : t.Mb} (hz : z ∈ (c.L.subgroupOf t.M).map t.qmk) :
    gbar t hgM * z * (gbar t hgM)⁻¹ = z := by
  rw [← t.muL_range] at hz
  obtain ⟨⟨⟨a, b⟩, e⟩, rfl⟩ := MonoidHom.mem_range.mp hz
  rw [t.muL_apply]
  have ha := gbar_centralizes_Lhat_zero t hK32 hGA hSp hgM hg3 hgK a.2
  have hb := gbar_centralizes_Lhat_one t hK32 hGA hSp hgM hg3 hgK b.2
  have he := gbar_centralizes_Lhat_two t hK32 hGA hSp hgM hg3 hgK e.2
  calc gbar t hgM * ((a : t.Mb) * (b : t.Mb) * (e : t.Mb)) * (gbar t hgM)⁻¹
      = (gbar t hgM * (a : t.Mb) * (gbar t hgM)⁻¹) *
          (gbar t hgM * (b : t.Mb) * (gbar t hgM)⁻¹) *
          (gbar t hgM * (e : t.Mb) * (gbar t hgM)⁻¹) := by group
    _ = (a : t.Mb) * (b : t.Mb) * (e : t.Mb) := by rw [ha, hb, he]


private theorem eq_one_of_mem_image_L_of_centralizes
    (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) {z : t.Mb}
    (hzL : z ∈ (c.L.subgroupOf t.M).map t.qmk)
    (hzC : ∀ w ∈ (c.L.subgroupOf t.M).map t.qmk, z * w = w * z) : z = 1 := by
  rw [← t.muL_range] at hzL
  obtain ⟨⟨⟨a, b⟩, e⟩, rfl⟩ := MonoidHom.mem_range.mp hzL
  have hzC' : ∀ w ∈ (t.muL).range, (a : t.Mb) * (b : t.Mb) * (e : t.Mb) * w =
      w * ((a : t.Mb) * (b : t.Mb) * (e : t.Mb)) := by
    intro w hw
    rw [t.muL_range] at hw
    have h := hzC w hw
    rw [t.muL_apply] at h
    exact h
  have ha_center : a ∈ Subgroup.center ↥(t.Lhat 0) := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    have hw : (w : t.Mb) ∈ (t.muL).range :=
      ⟨((w, 1), 1), by rw [t.muL_apply]; simp⟩
    have hcomm := hzC' (w : t.Mb) hw
    have hbw : Commute (b : t.Mb) (w : t.Mb) :=
      commute_of_mem_Lhat t 1 0 (by decide) (b : t.Mb) (w : t.Mb) b.2 w.2
    have hew : Commute (e : t.Mb) (w : t.Mb) :=
      commute_of_mem_Lhat t 2 0 (by decide) (e : t.Mb) (w : t.Mb) e.2 w.2
    have hbew : Commute ((b : t.Mb) * (e : t.Mb)) (w : t.Mb) := hbw.mul_left hew
    have h1 : (a : t.Mb) * (w : t.Mb) * ((b : t.Mb) * (e : t.Mb)) =
        (w : t.Mb) * (a : t.Mb) * ((b : t.Mb) * (e : t.Mb)) := by
      calc (a : t.Mb) * (w : t.Mb) * ((b : t.Mb) * (e : t.Mb))
          = (a : t.Mb) * ((b : t.Mb) * (e : t.Mb) * (w : t.Mb)) := by
            rw [hbew.eq]; group
        _ = (a : t.Mb) * (b : t.Mb) * (e : t.Mb) * (w : t.Mb) := by group
        _ = (w : t.Mb) * ((a : t.Mb) * (b : t.Mb) * (e : t.Mb)) := hcomm
        _ = (w : t.Mb) * (a : t.Mb) * ((b : t.Mb) * (e : t.Mb)) := by group
    exact (mul_right_cancel h1).symm
  have hb_center : b ∈ Subgroup.center ↥(t.Lhat 1) := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    have hw : (w : t.Mb) ∈ (t.muL).range :=
      ⟨((1, w), 1), by rw [t.muL_apply]; simp⟩
    have hcomm := hzC' (w : t.Mb) hw
    have haw : Commute (a : t.Mb) (w : t.Mb) :=
      commute_of_mem_Lhat t 0 1 (by decide) (a : t.Mb) (w : t.Mb) a.2 w.2
    have hew : Commute (e : t.Mb) (w : t.Mb) :=
      commute_of_mem_Lhat t 2 1 (by decide) (e : t.Mb) (w : t.Mb) e.2 w.2
    have h1 : (a : t.Mb) * ((b : t.Mb) * (w : t.Mb) * (e : t.Mb)) =
        (a : t.Mb) * ((w : t.Mb) * (b : t.Mb) * (e : t.Mb)) := by
      calc (a : t.Mb) * ((b : t.Mb) * (w : t.Mb) * (e : t.Mb))
          = (a : t.Mb) * (b : t.Mb) * (w : t.Mb) * (e : t.Mb) := by group
        _ = (a : t.Mb) * (b : t.Mb) * ((e : t.Mb) * (w : t.Mb)) := by rw [hew.eq]; group
        _ = (a : t.Mb) * (b : t.Mb) * (e : t.Mb) * (w : t.Mb) := by group
        _ = (w : t.Mb) * ((a : t.Mb) * (b : t.Mb) * (e : t.Mb)) := hcomm
        _ = (w : t.Mb) * (a : t.Mb) * (b : t.Mb) * (e : t.Mb) := by group
        _ = (a : t.Mb) * (w : t.Mb) * (b : t.Mb) * (e : t.Mb) := by rw [haw.eq]
        _ = (a : t.Mb) * ((w : t.Mb) * (b : t.Mb) * (e : t.Mb)) := by group
    have h2 : (b : t.Mb) * (w : t.Mb) * (e : t.Mb) =
        (w : t.Mb) * (b : t.Mb) * (e : t.Mb) := mul_left_cancel h1
    exact (mul_right_cancel h2).symm
  have he_center : e ∈ Subgroup.center ↥(t.Lhat 2) := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    have hw : (w : t.Mb) ∈ (t.muL).range :=
      ⟨((1, 1), w), by rw [t.muL_apply]; simp⟩
    have hcomm := hzC' (w : t.Mb) hw
    have haw : Commute (a : t.Mb) (w : t.Mb) :=
      commute_of_mem_Lhat t 0 2 (by decide) (a : t.Mb) (w : t.Mb) a.2 w.2
    have hbw : Commute (b : t.Mb) (w : t.Mb) :=
      commute_of_mem_Lhat t 1 2 (by decide) (b : t.Mb) (w : t.Mb) b.2 w.2
    have h1 : (a : t.Mb) * (b : t.Mb) * ((e : t.Mb) * (w : t.Mb)) =
        (a : t.Mb) * (b : t.Mb) * ((w : t.Mb) * (e : t.Mb)) := by
      calc (a : t.Mb) * (b : t.Mb) * ((e : t.Mb) * (w : t.Mb))
          = (a : t.Mb) * (b : t.Mb) * (e : t.Mb) * (w : t.Mb) := by group
        _ = (w : t.Mb) * ((a : t.Mb) * (b : t.Mb) * (e : t.Mb)) := hcomm
        _ = (a : t.Mb) * (w : t.Mb) * (b : t.Mb) * (e : t.Mb) := by rw [haw.eq]; group
        _ = (a : t.Mb) * (b : t.Mb) * (w : t.Mb) * (e : t.Mb) := by
            calc (a : t.Mb) * (w : t.Mb) * (b : t.Mb) * (e : t.Mb)
                = (a : t.Mb) * ((w : t.Mb) * (b : t.Mb)) * (e : t.Mb) := by group
              _ = (a : t.Mb) * ((b : t.Mb) * (w : t.Mb)) * (e : t.Mb) := by
                  rw [← hbw.eq]
              _ = (a : t.Mb) * (b : t.Mb) * (w : t.Mb) * (e : t.Mb) := by group
        _ = (a : t.Mb) * (b : t.Mb) * ((w : t.Mb) * (e : t.Mb)) := by group
    exact (mul_left_cancel h1).symm
  have ha1 : a = 1 := by
    have h := ha_center
    rw [center_Lhat_eq_bot t hK32 hGA hSp 0] at h
    exact Subgroup.mem_bot.mp h
  have hb1 : b = 1 := by
    have h := hb_center
    rw [center_Lhat_eq_bot t hK32 hGA hSp 1] at h
    exact Subgroup.mem_bot.mp h
  have he1 : e = 1 := by
    have h := he_center
    rw [center_Lhat_eq_bot t hK32 hGA hSp 2] at h
    exact Subgroup.mem_bot.mp h
  rw [ha1, hb1, he1]
  rw [t.muL_apply]
  simp

private theorem gbar_ne_one {g : ↥t.Xz} (hgM : (g : G) ∈ c.S.M)
    (hodd : ¬ 2 ∣ orderOf g) (hgt : 1 < orderOf g) : gbar t hgM ≠ 1 := by
  intro h1
  have hmem : gM t hgM ∈ t.Kq := by
    rw [← QuotientGroup.eq_one_iff]
    exact h1
  have h2 : IsPGroup 2 (Subgroup.zpowers (gM t hgM)) :=
    t.Kq_isPGroup.to_le (Subgroup.zpowers_le.mpr hmem)
  obtain ⟨n, hn⟩ := h2.exists_card_eq
  have hord : Nat.card (Subgroup.zpowers (gM t hgM)) = orderOf g := by
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe (gM t hgM)]
    have hcoe : ((gM t hgM : ↥t.M) : G) = g := by simp [gM]
    rw [hcoe, Subgroup.orderOf_coe]
  rw [hord] at hn
  have hdvd : orderOf g ∣ 2 ^ n := ⟨1, by rw [hn, mul_one]⟩
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (by omega : orderOf g ≠ 1)
  have hp2 : p = 2 := by
    have hpd : p ∣ 2 ^ n := hpdvd.trans hdvd
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hpd)
  exact hodd (hp2 ▸ hpdvd)

private theorem gbar_not_mem_image_L (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) {g : ↥t.Xz}
    (hgM : (g : G) ∈ c.S.M) (hg3 : ¬ 3 ∣ orderOf g)
    (hgK : ∀ k ∈ t.Kyhat, (QuotientGroup.mk g : t.Xhat) * k * (QuotientGroup.mk g)⁻¹ * k⁻¹ ∈
      t.O2Kyhat) (hodd : ¬ 2 ∣ orderOf g) (hgt : 1 < orderOf g) :
    gbar t hgM ∉ (c.L.subgroupOf t.M).map t.qmk := by
  intro hmem
  have hzC : ∀ w ∈ (c.L.subgroupOf t.M).map t.qmk,
      gbar t hgM * w = w * gbar t hgM := by
    intro w hw
    have h := gbar_commutes_image_L t hK32 hGA hSp hgM hg3 hgK hw
    calc gbar t hgM * w = (gbar t hgM * w * (gbar t hgM)⁻¹) * gbar t hgM := by group
      _ = w * gbar t hgM := by rw [h]
  have h1 : gbar t hgM = 1 := eq_one_of_mem_image_L_of_centralizes t hK32 hGA hSp hmem hzC
  exact gbar_ne_one t hgM hodd hgt h1

theorem mem_inf_N_of_centralizes_Kyhat (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) {g : ↥t.Xz}
    (hgM : (g : G) ∈ c.S.M) (hg3 : ¬ 3 ∣ orderOf g)
    (hgK : ∀ k ∈ t.Kyhat, (QuotientGroup.mk g : t.Xhat) * k * (QuotientGroup.mk g)⁻¹ * k⁻¹ ∈
      t.O2Kyhat) :
    ∀ l ∈ c.L, (g : G) * l * (g : G)⁻¹ * l⁻¹ ∈ c.L ⊓ t.d.N := by
  intro l hl
  have hlM : l ∈ t.M := c.hyp81.1 hl
  let lM : ↥t.M := ⟨l, hlM⟩
  have hcomm := gbar_commutes_image_L t hK32 hGA hSp hgM hg3 hgK
    (Subgroup.mem_map.mpr ⟨lM, hl, rfl⟩)
  have hq : t.qmk (⟨(g : G) * l * (g : G)⁻¹ * l⁻¹,
      t.M.mul_mem (t.M.mul_mem (t.M.mul_mem hgM hlM) (t.M.inv_mem hgM))
        (t.M.inv_mem hlM)⟩ : ↥t.M) = 1 := by
    change t.qmk (gM t hgM * lM * (gM t hgM)⁻¹ * lM⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    rw [show t.qmk (gM t hgM) = gbar t hgM from rfl]
    calc gbar t hgM * t.qmk lM * (gbar t hgM)⁻¹ * (t.qmk lM)⁻¹ =
        (gbar t hgM * t.qmk lM * (gbar t hgM)⁻¹) * (t.qmk lM)⁻¹ := by group
      _ = t.qmk lM * (t.qmk lM)⁻¹ := by rw [hcomm]
      _ = 1 := mul_inv_cancel _
  have hKq : (⟨(g : G) * l * (g : G)⁻¹ * l⁻¹,
      t.M.mul_mem (t.M.mul_mem (t.M.mul_mem hgM hlM) (t.M.inv_mem hgM))
        (t.M.inv_mem hlM)⟩ : ↥t.M) ∈ t.Kq :=
    (QuotientGroup.eq_one_iff _).mp hq
  exact Subgroup.mem_subgroupOf.mp hKq


private theorem Lhat_perfect (i : Fin 3) : ⁅t.Lhat i, t.Lhat i⁆ = t.Lhat i := by
  have h1 : ⁅t.Lhat 1, t.Lhat 1⁆ = t.Lhat 1 := by
    rw [show t.Lhat 1 = (t.Lhat 0).map (MulAut.conj (t.ybar)).toMonoidHom from
      (t.Lhat_conj 0).symm]
    rw [← Subgroup.map_commutator, t.Lhat0_perfect]
  fin_cases i
  · exact t.Lhat0_perfect
  · exact h1
  · change ⁅t.Lhat 2, t.Lhat 2⁆ = t.Lhat 2
    rw [show t.Lhat 2 = (t.Lhat 1).map (MulAut.conj (t.ybar)).toMonoidHom from
      (t.Lhat_conj 1).symm]
    rw [← Subgroup.map_commutator, h1]

private theorem card_Lhat_eq (i : Fin 3) : Nat.card ↥(t.Lhat i) = Nat.card ↥(t.Lhat 0) := by
  fin_cases i
  · rfl
  · change Nat.card ↥(t.Lhat 1) = Nat.card ↥(t.Lhat 0)
    rw [show t.Lhat 1 = (t.Lhat 0).map (MulAut.conj (t.ybar)).toMonoidHom from
      (t.Lhat_conj 0).symm]
    exact Subgroup.card_map_of_injective (MulAut.conj (t.ybar)).injective
  · change Nat.card ↥(t.Lhat 2) = Nat.card ↥(t.Lhat 0)
    rw [show t.Lhat 2 = (t.Lhat 1).map (MulAut.conj (t.ybar)).toMonoidHom from
      (t.Lhat_conj 1).symm]
    rw [Subgroup.card_map_of_injective (MulAut.conj (t.ybar)).injective]
    change Nat.card ↥(t.Lhat 1) = Nat.card ↥(t.Lhat 0)
    rw [show t.Lhat 1 = (t.Lhat 0).map (MulAut.conj (t.ybar)).toMonoidHom from
      (t.Lhat_conj 0).symm]
    exact Subgroup.card_map_of_injective (MulAut.conj (t.ybar)).injective

private theorem mem_sup_Lhat01 {x : t.Mb} (hx : x ∈ t.Lhat 0 ⊔ t.Lhat 1) :
    ∃ a ∈ t.Lhat 0, ∃ b ∈ t.Lhat 1, x = a * b := by
  have hcent : t.Lhat 1 ≤ Subgroup.centralizer (t.Lhat 0 : Set (t.Mb)) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact t.Lhat_comm 0 1 (by decide) a ha b hb
  have hnorm : t.Lhat 1 ≤ Subgroup.normalizer (t.Lhat 0 : Set (t.Mb)) :=
    hcent.trans (Subgroup.centralizer_le_normalizer _)
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right (t.Lhat 1) (t.Lhat 0) hnorm
  have hx' : x ∈ (t.Lhat 1 ⊔ t.Lhat 0 : Subgroup (t.Mb)) := by
    rwa [sup_comm]
  have hx'' : x ∈ ((t.Lhat 1 : Set (t.Mb)) * (t.Lhat 0 : Set (t.Mb))) := by
    rw [← hset]
    exact hx'
  obtain ⟨b, hb, a, ha, hba⟩ := hx''
  refine ⟨a, ha, b, hb, ?_⟩
  rw [← hba, t.Lhat_comm 0 1 (by decide) a ha b hb]

private theorem commute_sup_Lhat01_Lhat2 {x y : t.Mb} (hx : x ∈ t.Lhat 0 ⊔ t.Lhat 1)
    (hy : y ∈ t.Lhat 2) : x * y = y * x := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_Lhat01 t hx
  have hay : a * y = y * a := t.Lhat_comm 0 2 (by decide) a ha y hy
  have hby : b * y = y * b := t.Lhat_comm 1 2 (by decide) b hb y hy
  calc (a * b) * y = a * (b * y) := by group
    _ = a * (y * b) := by rw [hby]
    _ = (a * y) * b := by group
    _ = (y * a) * b := by rw [hay]
    _ = y * (a * b) := by group

private theorem dvd_card_Lhat {r : ℕ} (hrLhat0 : r ∣ Nat.card ↥(t.Lhat 0)) (i : Fin 3) :
    r ∣ Nat.card ↥(t.Lhat i) := by
  rw [card_Lhat_eq t i]
  exact hrLhat0

private theorem one_le_pRank_Lhat_zero {r : ℕ} [Fact r.Prime] {u : ↥(t.Lhat 0)}
    (huord : orderOf u = r) :
    1 ≤ CFSG.Open.pRank r (t.Lhat 0) := by
  have hupow : (u : t.Mb) ^ r = 1 := by
    simpa [Subgroup.orderOf_coe, huord] using pow_orderOf_eq_one (u : t.Mb)
  refine CFSG.SectionRank.le_pRank (p := r) (Nat.Prime.one_lt (Fact.out : Nat.Prime r))
    (H := t.Lhat 0) (E := Subgroup.zpowers (u : t.Mb)) (Subgroup.zpowers_le.mpr u.2)
    (CFSG.Open.isElemAbelian_zpowers hupow) (k := 1) ?_
  rw [Nat.card_zpowers, Subgroup.orderOf_coe, huord, pow_one]

private theorem two_le_pRank_sup_Lhat01 {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    (hrLhat0 : r ∣ Nat.card ↥(t.Lhat 0)) :
    2 ≤ CFSG.Open.pRank r (t.Lhat 0 ⊔ t.Lhat 1) := by
  have hX : ⁅t.Lhat 1, t.Lhat 1⁆ = t.Lhat 1 := Lhat_perfect t 1
  have hqX : r ∣ Nat.card ↥(t.Lhat 1) := dvd_card_Lhat t hrLhat0 1
  have hcomm : ⁅t.Lhat 0, t.Lhat 1⁆ ≤ CFSG.Open.pCoreOf 2 (t.Lhat 0 ⊔ t.Lhat 1) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun a ha =>
      Subgroup.mem_centralizer_iff.mpr fun b hb =>
        (t.Lhat_comm 0 1 (by decide) a ha b hb).symm).le.trans bot_le
  have hstep := CFSG.GroupTheory.pRank_add_one_le_of_commutator_le_pCoreOf
    (G := t.Mb) (q := r) (M := t.Lhat 0 ⊔ t.Lhat 1) (L := t.Lhat 0) (X := t.Lhat 1)
    hr2 le_sup_left le_sup_right hcomm hX hqX
  have h1 : 1 ≤ CFSG.Open.pRank r (t.Lhat 0) := by
    haveI : Fact r.Prime := ⟨Fact.out⟩
    obtain ⟨u, huord⟩ := exists_prime_orderOf_dvd_card' (G := ↥(t.Lhat 0)) r hrLhat0
    exact one_le_pRank_Lhat_zero t huord
  omega

private theorem three_le_pRank_image_L {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    (hrLhat0 : r ∣ Nat.card ↥(t.Lhat 0)) :
    3 ≤ CFSG.Open.pRank r ((c.L.subgroupOf t.M).map t.qmk) := by
  have hX : ⁅t.Lhat 2, t.Lhat 2⁆ = t.Lhat 2 := Lhat_perfect t 2
  have hqX : r ∣ Nat.card ↥(t.Lhat 2) := dvd_card_Lhat t hrLhat0 2
  have hcomm : ⁅t.Lhat 0 ⊔ t.Lhat 1, t.Lhat 2⁆ ≤
      CFSG.Open.pCoreOf 2 ((c.L.subgroupOf t.M).map t.qmk) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun x hx =>
      Subgroup.mem_centralizer_iff.mpr fun y hy =>
        (commute_sup_Lhat01_Lhat2 t hx hy).symm).le.trans bot_le
  have hsup_le : t.Lhat 0 ⊔ t.Lhat 1 ≤ (c.L.subgroupOf t.M).map t.qmk :=
    sup_le (t.Lhat_le_image_L 0) (t.Lhat_le_image_L 1)
  have hX_le : t.Lhat 2 ≤ (c.L.subgroupOf t.M).map t.qmk := t.Lhat_le_image_L 2
  have hstep := CFSG.GroupTheory.pRank_add_one_le_of_commutator_le_pCoreOf
    (G := t.Mb) (q := r) (M := (c.L.subgroupOf t.M).map t.qmk)
    (L := t.Lhat 0 ⊔ t.Lhat 1) (X := t.Lhat 2) hr2 hsup_le hX_le hcomm hX hqX
  have h2 := two_le_pRank_sup_Lhat01 t hr2 hrLhat0
  omega


private theorem pow_centralizes_Kyhat {x : t.Xhat} (hxY : x ∈ t.Yhat)
    (hx : ∀ k ∈ t.Kyhat, x * k * x⁻¹ * k⁻¹ ∈ t.O2Kyhat) (n : ℕ) :
    ∀ k ∈ t.Kyhat, x ^ n * k * (x ^ n)⁻¹ * k⁻¹ ∈ t.O2Kyhat := by
  induction n with
  | zero =>
      intro k hk
      simpa using t.O2Kyhat.one_mem
  | succ n ih =>
      intro k hk
      have hxnorm : x ∈ Subgroup.normalizer (t.O2Kyhat : Set t.Xhat) :=
        t.Yhat_le_normalizer_O2Kyhat hxY
      have h1 : ⁅x ^ n, k⁆ ∈ t.O2Kyhat := ih k hk
      have h2 : ⁅x, k⁆ ∈ t.O2Kyhat := hx k hk
      have h3 : x * ⁅x ^ n, k⁆ * x⁻¹ ∈ t.O2Kyhat :=
        (Subgroup.mem_normalizer_iff.mp hxnorm ⁅x ^ n, k⁆).mp h1
      rw [pow_succ']
      change ⁅x * x ^ n, k⁆ ∈ t.O2Kyhat
      rw [commutator_mul_left]
      exact t.O2Kyhat.mul_mem h3 h2

private theorem gbar_commutes_image_L_of_mem_inf_N {g : ↥t.Xz}
    (hgM : (g : G) ∈ c.S.M)
    (hmem : ∀ l ∈ c.L, (g : G) * l * (g : G)⁻¹ * l⁻¹ ∈ c.L ⊓ t.d.N) :
    ∀ z ∈ (c.L.subgroupOf t.M).map t.qmk, gbar t hgM * z * (gbar t hgM)⁻¹ = z := by
  rintro z ⟨lM, hlM, rfl⟩
  have hl : (lM : G) ∈ c.L := Subgroup.mem_subgroupOf.mp hlM
  have hcomm := hmem (lM : G) hl
  have hq : gbar t hgM * t.qmk lM * (gbar t hgM)⁻¹ * (t.qmk lM)⁻¹ = 1 := by
    have hQ : gM t hgM * lM * (gM t hgM)⁻¹ * lM⁻¹ ∈ t.Kq := by
      rw [Subgroup.mem_subgroupOf]
      exact hcomm
    have h1 : t.qmk (gM t hgM * lM * (gM t hgM)⁻¹ * lM⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hQ
    rw [← h1, map_mul, map_mul, map_mul, map_inv, map_inv]
    rfl
  calc gbar t hgM * t.qmk lM * (gbar t hgM)⁻¹ =
      (gbar t hgM * t.qmk lM * (gbar t hgM)⁻¹ * (t.qmk lM)⁻¹) * t.qmk lM := by group
    _ = t.qmk lM := by rw [hq, one_mul]

private theorem orderOf_qmk_eq_of_not_mem_Kq {x : ↥t.M} {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hxord : orderOf x = r) (hxKq : x ∉ t.Kq) :
    orderOf (t.qmk x) = r := by
  have hdvd : orderOf (t.qmk x) ∣ r := by
    have h := orderOf_map_dvd (t.qmk) x
    rwa [hxord] at h
  have hne : t.qmk x ≠ 1 := by
    intro h1
    have hmem : x ∈ t.Kq := (QuotientGroup.eq_one_iff _).mp h1
    obtain ⟨k, hk⟩ := t.Kq_isPGroup.exists_card_eq
    have hd : orderOf x ∣ 2 ^ k := by
      rw [← hk]
      exact Subgroup.orderOf_dvd_natCard t.Kq hmem
    rw [hxord] at hd
    have h2 : r ∣ 2 := hr.dvd_of_dvd_pow hd
    have h3 : r = 2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2
    exact hr2 h3
  rcases hr.eq_one_or_self_of_dvd (orderOf (t.qmk x)) hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hne
  · exact h

theorem centralizer_y_le_of_centralizes_Kyhat (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes)
    (hSE : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.StronglyEmbeddedFive)
    {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) (hrK : r ∣ Nat.card t.Kyhat) {f : t.Xhat}
    (hfY : f ∈ t.Yhat) (hf : orderOf f = r)
    (hfK : ∀ k ∈ t.Kyhat, f * k * f⁻¹ * k⁻¹ ∈ t.O2Kyhat) :
    Subgroup.centralizer ({t.y} : Set G) ≤ c.S.M := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g0, hg0M, hg0f⟩ := Subgroup.mem_map.mp hfY
  have hg0M' : (g0 : G) ∈ c.S.M := Subgroup.mem_subgroupOf.mp hg0M
  have hr_dvd_n : r ∣ orderOf g0 := by
    have h := orderOf_map_dvd (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥t.Xz)) g0
    rw [hg0f, hf] at h
    exact h
  set n : ℕ := orderOf g0 with hn_def
  set m : ℕ := n / r with hm_def
  have hn_eq : n = r * m := by
    rw [hn_def, hm_def]
    exact (Nat.mul_div_cancel' hr_dvd_n).symm
  let g : ↥t.Xz := g0 ^ m
  have hgord : orderOf g = r := by
    have ho : orderOf g0 = r * m := by
      rw [← hn_def]
      exact hn_eq
    change orderOf (g0 ^ m) = r
    rw [orderOf_pow, ho]
    have hgcd : Nat.gcd (r * m) m = m := Nat.gcd_eq_right (dvd_mul_left m r)
    have hn_pos : 0 < n := by rw [hn_def]; exact orderOf_pos g0
    have hm_pos : 0 < m := by
      rw [hm_def]
      exact Nat.div_pos (Nat.le_of_dvd hn_pos hr_dvd_n) (Nat.Prime.pos hr)
    rw [hgcd, Nat.mul_comm r m, Nat.mul_div_right r hm_pos]
  have hgM : (g : G) ∈ c.S.M := by
    change ((g0 ^ m : ↥t.Xz) : G) ∈ c.S.M
    rw [Subgroup.coe_pow]
    exact c.S.M.pow_mem hg0M' m
  have hg3 : ¬ 3 ∣ orderOf g := by
    rw [hgord]
    intro h
    have h3 : 3 = r := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).mp h
    omega
  have hodd : ¬ 2 ∣ orderOf g := by
    rw [hgord]
    intro h
    have h2 : 2 = r := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hr).mp h
    omega
  have hgt : 1 < orderOf g := by
    rw [hgord]
    omega
  have hπg : (QuotientGroup.mk g : t.Xhat) = f ^ m := by
    change (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥t.Xz)) (g0 ^ m) = f ^ m
    rw [map_pow, hg0f]
  have hgK : ∀ k ∈ t.Kyhat, (QuotientGroup.mk g : t.Xhat) * k * (QuotientGroup.mk g)⁻¹ * k⁻¹ ∈
      t.O2Kyhat := by
    have hpow := pow_centralizes_Kyhat t hfY hfK m
    intro k hk
    rw [hπg]
    exact hpow k hk
  have hmem := mem_inf_N_of_centralizes_Kyhat t hK32 hGA hSp hgM hg3 hgK
  have hcent := gbar_commutes_image_L_of_mem_inf_N t hgM hmem
  have hnotmem := gbar_not_mem_image_L t hK32 hGA hSp hgM hg3 hgK hodd hgt
  have hrKy : r ∣ Nat.card t.Ky := by
    have h := Subgroup.card_map_dvd (t.Ky.subgroupOf t.Xz)
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥t.Xz))
    rw [show Nat.card ↥(t.Ky.subgroupOf t.Xz) = Nat.card ↥t.Ky from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (t.Ky_le_Xz hK32 hGA hSp)).toEquiv] at h
    exact hrK.trans h
  have hr_not_dvd_inf : ¬ r ∣ Nat.card ↥(t.Ky ⊓ t.d.N) := by
    obtain ⟨k, hk⟩ := t.d.N_isPGroup.exists_card_eq
    have hdvd : Nat.card ↥(t.Ky ⊓ t.d.N) ∣ 2 ^ k := by
      rw [← hk]
      exact Subgroup.card_dvd_of_le inf_le_right
    intro hrdvd
    have h2 : r ∣ 2 := hr.dvd_of_dvd_pow (hrdvd.trans hdvd)
    have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2
    omega
  have hr_dvd_range : r ∣ Nat.card ↥(t.phiKy.range) := by
    have hcard := Subgroup.card_ker_mul_card_range (t.phiKy)
    have hker_le : (t.phiKy.ker : Subgroup ↥t.Ky) ≤ (t.Ky ⊓ t.d.N).subgroupOf t.Ky := by
      intro k hk
      rw [MonoidHom.mem_ker] at hk
      have hq : t.qmk (⟨(k : G), t.Ky_le_M k.2⟩ : ↥t.M) = 1 := by
        change t.phiKy k = 1
        exact hk
      refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨k.2, ?_⟩)
      exact (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hq)).2
    have hker_dvd : Nat.card ↥(t.phiKy.ker) ∣ Nat.card ↥(t.Ky ⊓ t.d.N) := by
      have h1 := Subgroup.card_dvd_of_le hker_le
      have hcard_sub : Nat.card ↥((t.Ky ⊓ t.d.N).subgroupOf t.Ky) =
          Nat.card ↥(t.Ky ⊓ t.d.N) :=
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe (inf_le_left : t.Ky ⊓ t.d.N ≤ t.Ky)).toEquiv
      rwa [hcard_sub] at h1
    have hnot : ¬ r ∣ Nat.card ↥(t.phiKy.ker) := fun h => hr_not_dvd_inf (h.trans hker_dvd)
    have hprod : r ∣ Nat.card ↥(t.phiKy.ker) * Nat.card ↥(t.phiKy.range) := by
      rw [hcard]
      exact hrKy
    rcases hr.dvd_mul.mp hprod with h | h
    · exact absurd h hnot
    · exact h
  have hrLhat0 : r ∣ Nat.card ↥(t.Lhat 0) := by
    have hcard : Nat.card ↥(t.Lhat 0) = Nat.card ↥(t.phiKy.range) := by
      rw [t.phiKy_range_eq_delta_range hK32 hGA hSp]
      exact Nat.card_congr (MonoidHom.ofInjective
        (t.delta_injective (t.muL_injective hK32 hGA hSp))).toEquiv
    rwa [hcard]
  obtain ⟨u, huord⟩ := exists_prime_orderOf_dvd_card' (G := ↥(t.Lhat 0)) r hrLhat0
  have hr2 : r ≠ 2 := by omega
  have h3rank : 3 ≤ CFSG.Open.pRank r ((c.L.subgroupOf t.M).map t.qmk) :=
    three_le_pRank_image_L t hr2 hrLhat0
  obtain ⟨E3, hE3_le, hE3_abel, hE3_card⟩ :=
    CFSG.SectionRank.exists_pRank (p := r) hr.one_lt ((c.L.subgroupOf t.M).map t.qmk)
  have hgbar_ne : gbar t hgM ≠ 1 := gbar_ne_one t hgM hodd hgt
  have hcoe_gM : ((gM t hgM : ↥t.M) : G) = g := by simp [gM]
  have hord_gM : orderOf (gM t hgM) = orderOf g := by
    rw [← Subgroup.orderOf_coe (gM t hgM), hcoe_gM, Subgroup.orderOf_coe]
  have hgbar_dvd : orderOf (gbar t hgM) ∣ r := by
    have h := orderOf_map_dvd (t.qmk) (gM t hgM)
    rw [hord_gM, hgord] at h
    simpa [gbar] using h
  have hgbar_ord : orderOf (gbar t hgM) = r := by
    rcases hr.eq_one_or_self_of_dvd (orderOf (gbar t hgM)) hgbar_dvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hgbar_ne
    · exact h
  have hgbar_pow : (gbar t hgM) ^ r = 1 := by
    rw [← hgbar_ord]
    exact pow_orderOf_eq_one _
  have hgbar_not_E3 : gbar t hgM ∉ E3 := fun h => hnotmem (hE3_le h)
  have hgbar_comm_E3 : ∀ a ∈ E3, a * gbar t hgM = gbar t hgM * a := by
    intro a ha
    have h := hcent a (hE3_le ha)
    have h' : gbar t hgM * a = a * gbar t hgM := by
      calc gbar t hgM * a = (gbar t hgM * a * (gbar t hgM)⁻¹) * gbar t hgM := by group
        _ = a * gbar t hgM := by rw [h]
    exact h'.symm
  obtain ⟨hE4_abel, hE4_card⟩ :=
    CFSG.Quasithin.H13.U3.elemAbelian_sup_zpowers (p := r) (A := E3)
      hE3_abel hgbar_not_E3 hgbar_pow hgbar_comm_E3
  have h4top : 4 ≤ CFSG.Open.pRank r (⊤ : Subgroup (t.Mb)) := by
    have hk := h3rank
    have hle := CFSG.SectionRank.le_pRank (p := r) hr.one_lt
      (H := (⊤ : Subgroup (t.Mb))) (E := E3 ⊔ Subgroup.zpowers (gbar t hgM))
      le_top hE4_abel (k := CFSG.Open.pRank r ((c.L.subgroupOf t.M).map t.qmk) + 1) ?_
    · omega
    · rw [hE4_card, hE3_card, pow_succ]
  have hnotdvd_Kq : ¬ r ∣ Nat.card ↥(t.Kq) := by
    obtain ⟨k, hk⟩ := t.Kq_isPGroup.exists_card_eq
    intro hrdvd
    have h2 : r ∣ 2 := hr.dvd_of_dvd_pow (by rwa [hk] at hrdvd)
    have h3 : r = 2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2
    omega
  have hEq : CFSG.Open.pRank r (⊤ : Subgroup (t.Mb)) = CFSG.Open.pRank r c.S.M := by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top r (t.Mb),
      CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hr (t.Kq) hnotdvd_Kq,
      CFSG.SectionRank.pRank_coe_eq_openPRank r (t.M)]
  have h4M : 4 ≤ CFSG.Open.pRank r c.S.M := hEq ▸ h4top
  have hrσ : r ∈ c.sig := c.four_le_imp_mem r hr hr2 h4M
  obtain ⟨v, hvord⟩ := exists_prime_orderOf_dvd_card' (G := ↥t.Ky) r hrKy
  let H : Subgroup G := c.S.M ⊓ Subgroup.centralizer ({t.y} : Set G)
  have hH_le_M : H ≤ t.M := inf_le_left
  let qH : ↥H →* t.Mb := (t.qmk).comp (Subgroup.inclusion hH_le_M)
  let gH : ↥H := ⟨g, Subgroup.mem_inf.mpr ⟨hgM, t.Xz_le_centralizer g.2⟩⟩
  let vH : ↥H := ⟨v, Subgroup.mem_inf.mpr ⟨c.hyp81.1 (t.Ky_le v.2).1, (t.Ky_le v.2).2⟩⟩
  have hqg : qH gH = gbar t hgM := rfl
  have hqv : qH vH = t.qmk (kM t v) := rfl
  have hvM_ord : orderOf (kM t v) = r := by
    rw [← Subgroup.orderOf_coe (kM t v)]
    have hcoe : ((kM t v : ↥t.M) : G) = (v : G) := by simp [kM]
    rw [hcoe, Subgroup.orderOf_coe, hvord]
  have hvM_notKq : kM t v ∉ t.Kq := by
    intro hmem
    obtain ⟨k, hk⟩ := t.Kq_isPGroup.exists_card_eq
    have hd : orderOf (kM t v) ∣ 2 ^ k := by
      rw [← hk]
      exact Subgroup.orderOf_dvd_natCard t.Kq hmem
    rw [hvM_ord] at hd
    have h2 : r ∣ 2 := hr.dvd_of_dvd_pow hd
    have h3 : r = 2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2
    exact hr2 h3
  have hvbar_ord : orderOf (t.qmk (kM t v)) = r :=
    orderOf_qmk_eq_of_not_mem_Kq t hr hr2 hvM_ord hvM_notKq
  have hvbar_mem_imageL : t.qmk (kM t v) ∈ (c.L.subgroupOf t.M).map t.qmk :=
    Subgroup.mem_map.mpr ⟨kM t v, (t.Ky_le v.2).1, rfl⟩
  have hvbar_mem_range : t.qmk (kM t v) ∈ qH.range := ⟨vH, hqv⟩
  have hgbar_mem_range : gbar t hgM ∈ qH.range := ⟨gH, hqg⟩
  have hgbar_not_zpowers : gbar t hgM ∉ Subgroup.zpowers (t.qmk (kM t v)) := by
    intro hmem
    exact hnotmem (Subgroup.zpowers_le.mpr hvbar_mem_imageL hmem)
  have hcomm_gv : gbar t hgM * t.qmk (kM t v) = t.qmk (kM t v) * gbar t hgM := by
    have h := gbar_mul_qmk_kM t hK32 hGA hSp hgM hgK v
    calc gbar t hgM * t.qmk (kM t v) =
        (gbar t hgM * t.qmk (kM t v) * (gbar t hgM)⁻¹ * (t.qmk (kM t v))⁻¹) *
          (t.qmk (kM t v) * gbar t hgM) := by group
      _ = t.qmk (kM t v) * gbar t hgM := by rw [h, one_mul]
  have hcomm_zpowers : ∀ a ∈ Subgroup.zpowers (t.qmk (kM t v)),
      a * gbar t hgM = gbar t hgM * a := by
    intro a ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (show Commute (t.qmk (kM t v)) (gbar t hgM) from hcomm_gv.symm).zpow_left n |>.eq
  have hEbar := CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute
    (r := r) (X := Subgroup.zpowers (t.qmk (kM t v))) (v := gbar t hgM)
    (by rw [Nat.card_zpowers, hvbar_ord]) hgbar_ord hgbar_not_zpowers hcomm_zpowers
  have h2range : 2 ≤ CFSG.Open.pRank r qH.range := by
    have hEbar_le : Subgroup.zpowers (t.qmk (kM t v)) ⊔ Subgroup.zpowers (gbar t hgM) ≤
        qH.range :=
      sup_le (Subgroup.zpowers_le.mpr hvbar_mem_range)
        (Subgroup.zpowers_le.mpr hgbar_mem_range)
    exact CFSG.SectionRank.le_pRank hr.one_lt hEbar_le hEbar.1 (k := 2) hEbar.2
  have hker2 : IsPGroup 2 ↥qH.ker := by
    have hcomap2 : IsPGroup 2 ↥((t.Kq).comap (Subgroup.inclusion hH_le_M)) :=
      t.Kq_isPGroup.comap_of_injective (Subgroup.inclusion hH_le_M)
        (Subgroup.inclusion_injective hH_le_M)
    refine hcomap2.to_le ?_
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_comap]
    exact (QuotientGroup.eq_one_iff _).mp hx
  have hrank_eq : CFSG.Open.pRank r (⊤ : Subgroup ↥H) = CFSG.Open.pRank r qH.range := by
    have hquot := CFSG.SectionRank.pRank_quotient_two_group (G := ↥H) qH.ker hker2 hr hr2
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt
        (QuotientGroup.quotientKerEquivRange qH)] at hquot
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top r qH.range,
      CFSG.SectionRank.pRank_coe_eq_openPRank r qH.range] at hquot
    exact hquot.symm
  have h2H : 2 ≤ CFSG.Open.pRank r H := by
    have hHeq : CFSG.Open.pRank r H = CFSG.Open.pRank r (⊤ : Subgroup ↥H) := by
      rw [← CFSG.SectionRank.pRank_coe_eq_openPRank r H,
        CFSG.SectionRank.pRank_eq_open_pRank_top r ↥H]
    rw [hHeq, hrank_eq]
    exact h2range
  have h2 : 2 ≤ CFSG.Open.pRank r (c.S.M ⊓ Subgroup.centralizer ({t.y} : Set G)) := h2H
  exact t.centralizer_y_le_of_two_le_pRank hrσ hSE h2

end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

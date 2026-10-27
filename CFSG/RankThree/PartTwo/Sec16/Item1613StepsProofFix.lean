module

public import CFSG.RankThree.PartTwo.Sec16.Item16Tail13Defs
public import CFSG.RankThree.PartTwo.Sec13.Item138N
import CFSG.RankThree.PartTwo.Sec16.Item1613StepsProofFixMat
import CFSG.RankThree.PartTwo.Sec16.Item1613StepsProofInv
import CFSG.RankThree.PartTwo.Sec16.Item16Tail14Tools
import CFSG.RankThree.PartTwo.Sec16.Item16Tail13PGL
import CFSG.RankThree.PartTwo.Sec16.Item16Tail
import CFSG.RankThree.PartTwo.Sec12.KS128NotHJPGL
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.Sec15.NoModNine
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.LocalAnalysis.SignalizerFunctor.Maximality
public import CFSG.RankThree.PartTwo.Sec13.Item136PGL
public import CFSG.RankThree.PartTwo.Sec15.HypS

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof1613Fix

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Sec16.Proof169
  CFSG.RankThree.PartTwo.Sec16.Proof1613 CFSG.RankThree.PartTwo.Sec16.Proof1614
  CFSG.RankThree.PartTwo.Sec16.Proof1613Inv CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open Matrix (ProjGenLinGroup GeneralLinearGroup)
open scoped Matrix commutatorElement

section Theta

variable {G : Type} [Group G] [Finite G]

theorem inf_centralizer_le_theta {L T : Subgroup G} {z : G}
    (hzN : z ∈ Subgroup.normalizer (L : Set G)) (hTL : T ≤ L) (hT2 : IsPGroup 2 T)
    (hfix : ∀ u : ↥L ⧸ aschbacherSolvableCore 3 ↥L,
      thetaQuotMulAut L (L.normalizerMonoidHom ⟨z, hzN⟩) u = u → u ^ 2 = 1 → u = 1) :
    T ⊓ Subgroup.centralizer ({z} : Set G) ≤ inSubgroup (aschbacherSolvableCore 3) L := by
  rintro t ⟨htT, htz⟩
  set σ := thetaQuotMulAut L (L.normalizerMonoidHom ⟨z, hzN⟩) with hσ
  set t' : ↥L := ⟨t, hTL htT⟩ with ht'
  set u : ↥L ⧸ aschbacherSolvableCore 3 ↥L := QuotientGroup.mk' _ t' with hu
  have hzt : z * t * z⁻¹ = t := by
    rw [← Subgroup.mem_centralizer_singleton_iff.mp htz, mul_inv_cancel_right]
  have hσu : σ u = u := by
    rw [hσ, hu, QuotientGroup.mk'_apply, thetaQuotMulAut_mk]
    congr 1
    apply Subtype.ext
    rw [normalizerMonoidHom_apply_coe, hzt]
  obtain ⟨k, hk⟩ := hT2 ⟨t, htT⟩
  have huk : u ^ 2 ^ k = 1 := by
    have h1 : t' ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [hu, ← map_pow, h1, map_one]
  have key : ∀ m : ℕ, ∀ v, σ v = v → v ^ 2 ^ m = 1 → v = 1 := by
    intro m
    induction m with
    | zero => intro v _ hv; simpa using hv
    | succ m ih =>
      intro v hv hvm
      refine ih v hv (hfix _ (by rw [map_pow, hv]) ?_)
      rw [← pow_mul, ← pow_succ]
      exact hvm
  have hu1 := key k u hσu huk
  exact ⟨t', (QuotientGroup.eq_one_iff t').mp hu1, rfl⟩

theorem commutator_le_theta_of {L T D E : Subgroup G} (hTL : T ≤ L) (hDL : D ≤ L)
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : 9 ≤ Nat.card E)
    (hET : E ≤ Subgroup.normalizer (T : Set G)) (hT3 : ¬ 3 ∣ Nat.card T)
    (h : ∀ F : Subgroup G, F ≤ E → Nat.card F = 3 → F ≠ D →
      T ⊓ Subgroup.centralizer (F : Set G) ≤ inSubgroup (aschbacherSolvableCore 3) L) :
    ⁅T, D⁆ ≤ inSubgroup (aschbacherSolvableCore 3) L := by
  set mk := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) with hmk
  set Db := (D.subgroupOf L).map mk with hDb
  set Y : Subgroup G :=
    ((Subgroup.centralizer (Db : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L))).comap mk).map
      L.subtype with hY
  have hθY : inSubgroup (aschbacherSolvableCore 3) L ≤ Y := by
    rintro _ ⟨l, hl, rfl⟩
    refine ⟨l, ?_, rfl⟩
    show l ∈ Subgroup.comap mk _
    rw [Subgroup.mem_comap, show mk l = 1 from (QuotientGroup.eq_one_iff l).mpr hl]
    exact Subgroup.one_mem _
  have hDY : T ⊓ Subgroup.centralizer (D : Set G) ≤ Y := by
    rintro t ⟨htT, htD⟩
    refine ⟨⟨t, hTL htT⟩, ?_, rfl⟩
    show (⟨t, hTL htT⟩ : ↥L) ∈ Subgroup.comap mk _
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    rintro _ ⟨δ, hδ, rfl⟩
    have hδD : (δ : G) ∈ D := Subgroup.mem_subgroupOf.mp hδ
    have hc : δ * ⟨t, hTL htT⟩ = ⟨t, hTL htT⟩ * δ :=
      Subtype.ext (Subgroup.mem_centralizer_iff.mp htD _ hδD)
    rw [← map_mul, ← map_mul, hc]
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 3 1
    Nat.prime_three E T ⟨hE.1, hE.2⟩ (by norm_num; exact hE9) hET
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hT3)
  have hTY : T ≤ Y := by
    rw [← hgen]
    refine iSup_le fun F => iSup_le fun hF => ?_
    obtain ⟨hFE, hF3⟩ := hF
    by_cases hFD : F = D
    · rw [hFD]
      exact hDY
    · exact (h F hFE (by simpa using hF3) hFD).trans hθY
  rw [Subgroup.commutator_le]
  intro t ht δ hδ
  obtain ⟨l, hl, rfl⟩ := hTY ht
  change l ∈ Subgroup.comap mk _ at hl
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at hl
  set δ' : ↥L := ⟨δ, hDL hδ⟩ with hδ'
  have hcomm := hl (mk δ') ⟨δ', Subgroup.mem_subgroupOf.mpr hδ, rfl⟩
  have h1 : mk ⁅l, δ'⁆ = 1 := by
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm]
    group
  refine ⟨⁅l, δ'⁆, (QuotientGroup.eq_one_iff _).mp h1, ?_⟩
  simp [commutatorElement_def, hδ']

theorem exists_mul_zpow_mem {x d : G} (hx3 : x ^ 3 = 1) (hxd : x * d = d * x)
    {F : Subgroup G} (hFE : F ≤ Subgroup.zpowers x ⊔ Subgroup.zpowers d)
    (hF3 : Nat.card F = 3) (hFD : F ≠ Subgroup.zpowers d) (hd3 : d ^ 3 = 1) :
    ∃ j : ℤ, x * d ^ j ∈ F := by
  obtain ⟨f, hfF, hf1, rfl⟩ := Sec5.exists_eq_zpowers_of_card_eq_prime Nat.prime_three hF3
  have hfd : f ∉ Subgroup.zpowers d := by
    intro hf
    apply hFD
    have hle : Subgroup.zpowers f ≤ Subgroup.zpowers d := Subgroup.zpowers_le.mpr hf
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hF3]
    have hdo : orderOf d ∣ 3 := orderOf_dvd_of_pow_eq_one hd3
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) hdo
  obtain ⟨i, k, hik⟩ := exists_zpow_mul_of_mem_sup hxd (hFE (Subgroup.mem_zpowers f))
  have hx3' : ∀ m : ℤ, x ^ (3 * m) = 1 := fun m => by
    rw [zpow_mul, show (x ^ (3 : ℤ)) = x ^ (3 : ℕ) by norm_cast, hx3, one_zpow]
  have hxi : ∀ r m : ℤ, i = 3 * m + r → x ^ i = x ^ r := fun r m h => by
    rw [h, zpow_add, hx3', one_mul]
  obtain ⟨m, hm⟩ : ∃ m, i = 3 * m + i % 3 := ⟨i / 3, by omega⟩
  have hr : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  rcases hr with h0 | h1 | h2
  · exfalso
    apply hfd
    rw [hik, hxi _ m (by rw [hm, h0]), zpow_zero, one_mul]
    exact Subgroup.zpow_mem_zpowers d k
  · refine ⟨k, ?_⟩
    have hx1 : x ^ i = x := by rw [hxi 1 m (by rw [hm, h1]), zpow_one]
    have hf : x * d ^ k = f := by rw [hik, hx1]
    rw [hf]
    exact Subgroup.mem_zpowers f
  · refine ⟨2 * k, ?_⟩
    have hf2 : f ^ (2 : ℤ) = x * d ^ (2 * k) := by
      have hc : Commute (x ^ i) (d ^ k) := Commute.zpow_zpow hxd i k
      rw [hik, hc.mul_zpow, ← zpow_mul, ← zpow_mul, mul_comm k 2]
      congr 1
      have : i * 2 = 3 * (2 * m + 1) + 1 := by rw [hm, h2]; ring
      rw [this, zpow_add, hx3', one_mul, zpow_one]
    rw [← hf2]
    exact Subgroup.zpow_mem_zpowers f 2

end Theta

section Outer

variable {G : Type} [Group G] [Finite G]

theorem not_mem_of_inducesTypeOn_three {a : G} {L : Subgroup G}
    (hL : L ∈ thetaComponentsAt 3 a) {x : G} (hx : InducesTypeOn L x 3) : x ∉ L := by
  intro hxL
  obtain ⟨hxN, π, p, f, K, _, hK, hq, e, y, hyH, hy3, hact⟩ := hx
  have hPerfL : Group.IsPerfect (L ⧸ aschbacherSolvableCore 3 L) :=
    (Sec6.isQuasisimple_of_mem_thetaComponentsAt hL).1
  have hPerf : Group.IsPerfect (projImage (slPi π 3 (p ^ f) K)) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  apply not_inner_of_type3 hK hq hyH hy3
  set w : L ⧸ aschbacherSolvableCore 3 L := QuotientGroup.mk' _ ⟨x, hxL⟩ with hw
  obtain ⟨s, hs, hse⟩ := (e w).2
  refine ⟨s, hs, ?_⟩
  have hmod : ∀ m ∈ slPi π 3 (p ^ f) K,
      s⁻¹ * y * m * (s⁻¹ * y)⁻¹ * m⁻¹ ∈ StatedScalars (Fin 3) K := by
    intro m hm
    rw [← mk_eq_one_iff_mem_statedScalars]
    set z := e.symm ⟨ProjGenLinGroup.mk m, Subgroup.mem_map_of_mem _ hm⟩ with hz
    have hez : (e z : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk m := by
      rw [hz, MulEquiv.apply_symm_apply]
    have h1 := hact z
    have h2 : thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hxN⟩) z = w * z * w⁻¹ := by
      induction z using QuotientGroup.induction_on with
      | H l =>
        rw [thetaQuotMulAut_mk, hw, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul,
          ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
        congr 1
    rw [h2, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      ← hse, hez] at h1
    simp only [map_mul, map_inv]
    calc (ProjGenLinGroup.mk s)⁻¹ * ProjGenLinGroup.mk y * ProjGenLinGroup.mk m *
          ((ProjGenLinGroup.mk s)⁻¹ * ProjGenLinGroup.mk y)⁻¹ * (ProjGenLinGroup.mk m)⁻¹ =
        (ProjGenLinGroup.mk s)⁻¹ * (ProjGenLinGroup.mk y * ProjGenLinGroup.mk m *
          (ProjGenLinGroup.mk y)⁻¹) * ProjGenLinGroup.mk s * (ProjGenLinGroup.mk m)⁻¹ := by group
      _ = 1 := by rw [← h1]; group
  intro m hm
  have hc := commute_of_comm_mod_scalars hmod m hm
  calc y * m * y⁻¹ = s * (s⁻¹ * y * m) * y⁻¹ := by group
    _ = s * (m * (s⁻¹ * y)) * y⁻¹ := by rw [hc]
    _ = s * m * s⁻¹ := by group

end Outer

section Scalars

variable {K : Type} [Field K]

theorem pow_three_mul_of_conj {y u : GL (Fin 3) K} {μ : Kˣ} (hμ3 : μ ^ 3 = 1)
    (h : y * u * y⁻¹ = GeneralLinearGroup.scalar (Fin 3) μ * u) :
    (y * u) ^ 3 = u ^ 3 * y ^ 3 := by
  have hsc : ∀ (c : Kˣ) (A : GL (Fin 3) K),
      A * GeneralLinearGroup.scalar (Fin 3) c = GeneralLinearGroup.scalar (Fin 3) c * A :=
    fun c A => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c A).eq
  set S := GeneralLinearGroup.scalar (Fin 3) μ with hS
  have hk : ∀ k : ℕ, y ^ k * u * (y ^ k)⁻¹ = GeneralLinearGroup.scalar (Fin 3) (μ ^ k) * u := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc y ^ (k + 1) * u * (y ^ (k + 1))⁻¹ = y * (y ^ k * u * (y ^ k)⁻¹) * y⁻¹ := by
            rw [pow_succ']
            group
        _ = y * (GeneralLinearGroup.scalar (Fin 3) (μ ^ k) * u) * y⁻¹ := by rw [ih]
        _ = GeneralLinearGroup.scalar (Fin 3) (μ ^ k) * (y * u * y⁻¹) := by
            rw [← mul_assoc, hsc]
            group
        _ = GeneralLinearGroup.scalar (Fin 3) (μ ^ (k + 1)) * u := by
            rw [h, ← mul_assoc, ← map_mul, ← pow_succ]
  have e1 : (y * u) ^ 3 =
      (y ^ 1 * u * (y ^ 1)⁻¹) * (y ^ 2 * u * (y ^ 2)⁻¹) * (y ^ 3 * u * (y ^ 3)⁻¹) * y ^ 3 := by
    rw [pow_three]
    group
  rw [e1, hk 1, hk 2, hk 3]
  have hS3 : GeneralLinearGroup.scalar (Fin 3) (μ ^ 3) = 1 := by rw [hμ3, map_one]
  have hS12 : GeneralLinearGroup.scalar (Fin 3) (μ ^ 1) * GeneralLinearGroup.scalar (Fin 3) (μ ^ 2)
      = 1 := by
    rw [← map_mul, ← pow_add, show 1 + 2 = 3 by norm_num, hμ3, map_one]
  calc GeneralLinearGroup.scalar (Fin 3) (μ ^ 1) * u *
        (GeneralLinearGroup.scalar (Fin 3) (μ ^ 2) * u) *
        (GeneralLinearGroup.scalar (Fin 3) (μ ^ 3) * u) * y ^ 3 =
      GeneralLinearGroup.scalar (Fin 3) (μ ^ 1) * (u * GeneralLinearGroup.scalar (Fin 3) (μ ^ 2)) *
        u * (GeneralLinearGroup.scalar (Fin 3) (μ ^ 3) * u) * y ^ 3 := by group
    _ = GeneralLinearGroup.scalar (Fin 3) (μ ^ 1) * (GeneralLinearGroup.scalar (Fin 3) (μ ^ 2) * u)
        * u * (GeneralLinearGroup.scalar (Fin 3) (μ ^ 3) * u) * y ^ 3 := by rw [hsc]
    _ = (GeneralLinearGroup.scalar (Fin 3) (μ ^ 1) * GeneralLinearGroup.scalar (Fin 3) (μ ^ 2)) *
        (u * u) * (GeneralLinearGroup.scalar (Fin 3) (μ ^ 3) * u) * y ^ 3 := by group
    _ = u ^ 3 * y ^ 3 := by rw [hS12, hS3, pow_three u, pow_three y]; group

end Scalars

section TypeThree

variable {G : Type} [Group G] [Finite G]

theorem fix_of_type3 {L : Subgroup G} {d x : G}
    (hdL : d ∈ L) (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) (hxd : x * d = d * x)
    (hx : InducesTypeOn L x 3) (j : ℤ) (hzN : x * d ^ j ∈ Subgroup.normalizer (L : Set G)) :
    ∀ u : ↥L ⧸ aschbacherSolvableCore 3 ↥L,
      thetaQuotMulAut L (L.normalizerMonoidHom ⟨x * d ^ j, hzN⟩) u = u → u ^ 2 = 1 →
        u = 1 := by
  obtain ⟨hxN, π, p, f, K, _, hK, hq, e, y, hyH, hy3, hact⟩ := hx
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have h3 := hK.three_ne_zero hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hsc : ∀ (c : Kˣ) (A : GL (Fin 3) K),
      A * GeneralLinearGroup.scalar (Fin 3) c = GeneralLinearGroup.scalar (Fin 3) c * A :=
    fun c A => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c A).eq
  have hdN : d ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hdL
  set σx := thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hxN⟩) with hσx
  have hact' : ∀ z : L ⧸ aschbacherSolvableCore 3 L,
      ((e (σx z) : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk y * (e z : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk y)⁻¹ :=
    hact
  set d' : ↥L := ⟨d, hdL⟩ with hd'
  have hd'3 : d' ^ 3 = 1 := Subtype.ext (by simpa using hd3)
  set db : ↥L ⧸ aschbacherSolvableCore 3 ↥L := QuotientGroup.mk' _ d' with hdb
  have hdb3 : db ^ 3 = 1 := by rw [hdb, ← map_pow, hd'3, map_one]
  have hdb1 : db ≠ 1 := by
    intro h1
    have h2 := CFSG.RankThree.injOn_mk_of_isPGroup Nat.prime_three
      (isPGroup_zpowers_three hd'3) (Subgroup.mem_zpowers _) (Subgroup.one_mem _)
      (by rw [map_one]; exact h1)
    exact hd1 (congrArg Subtype.val h2)
  obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.mp (e db).2
  have hsH : s ∈ glPi π 3 (p ^ f) K := slPi_le_glPi hπ hs
  have hsZ : s ∉ StatedScalars (Fin 3) K := by
    intro hsZ
    apply hdb1
    apply e.injective
    apply Subtype.ext
    rw [← hse, map_one, Subgroup.coe_one, mk_eq_one_iff_mem_statedScalars]
    exact hsZ
  have hs3 : s ^ 3 ∈ StatedScalars (Fin 3) K := by
    rw [← mk_eq_one_iff_mem_statedScalars, map_pow, hse, ← Subgroup.coe_pow, ← map_pow, hdb3,
      map_one, Subgroup.coe_one]
  have hsdet : (s : Matrix (Fin 3) (Fin 3) K).det = 1 := ((mem_slPi_iff hπ).mp hs).2
  have hfix : σx db = db := by
    rw [hσx, hdb, QuotientGroup.mk'_apply, thetaQuotMulAut_mk]
    congr 1
    apply Subtype.ext
    rw [normalizerMonoidHom_apply_coe, hxd, mul_inv_cancel_right]
  have h1 := hact' db
  rw [hfix, ← hse] at h1
  have hysZ : y * s * y⁻¹ * s⁻¹ ∈ StatedScalars (Fin 3) K := by
    rw [← mk_eq_one_iff_mem_statedScalars, map_mul, map_mul, map_mul, map_inv, map_inv, ← h1,
      mul_inv_cancel]
  obtain ⟨lam, hlam⟩ := hysZ
  have hys : y * s * y⁻¹ = GeneralLinearGroup.scalar (Fin 3) lam * s := by
    rw [hlam]
    group
  have hlam3 : lam ^ 3 = 1 := pow_three_eq_one_of_conj_eq_scalar_mul hys
  have hlam1 : lam ≠ 1 := by
    intro hlam1
    refine Sec12.KS128NotHJTC.false_of_commute_irreducible hτ hτ1 h3 hsdet hs3 hsZ ?_ hy3.2.2
    rw [hlam1, map_one, one_mul] at hys
    calc y * s = y * s * y⁻¹ * y := by group
      _ = s * y := by rw [hys]
  have htr := trace_eq_zero_of_conj_eq_scalar_mul hlam1 hys
  have hsZ' : s ∉ zPi π 3 (p ^ f) K := fun hz =>
    hsZ (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz)
  have hs3' : s ^ 3 ∈ zPi π 3 (p ^ f) K := by
    rw [zPi_eq hπ hq' hτ hτ1]
    exact ⟨pow_mem hsH 3, hs3⟩
  have htype : Type123 π (p ^ f) K s 1 := by
    rcases type123_exhaust hK hq hsH hsZ' hs3' with h1 | h2 | h3'
    · exact h1
    · exact absurd htr (trace_ne_zero_of_type2 hK hq h2)
    · exact absurd ⟨s, hs, fun m _ => rfl⟩ (not_inner_of_type3 hK hq hsH h3')
  obtain ⟨τ', hτ', hτ'1, z₀, hz₀, g, -, hD⟩ := htype
  obtain ⟨ζ, -, hζ⟩ := exists_scalar_of_mem_zPi hK hq hτ' hτ'1 hz₀
  have hsz : s * z₀ = g * diagTau hτ' * g⁻¹ := by
    rw [← hD]
    group
  have hs3c : s ^ 3 = GeneralLinearGroup.scalar (Fin 3) (ζ⁻¹ ^ 3) := by
    have e1 : (s * z₀) ^ 3 = 1 := by
      rw [hsz, conj_pow, diagTau_pow_three hτ', mul_one, mul_inv_cancel]
    have e2 : (s * z₀) ^ 3 = s ^ 3 * z₀ ^ 3 := by
      rw [← hζ]
      exact (Commute.mul_pow (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ζ s) 3)
    rw [e2, ← hζ, ← map_pow] at e1
    rw [map_pow, map_inv, inv_pow]
    calc s ^ 3 = s ^ 3 * GeneralLinearGroup.scalar (Fin 3) (ζ ^ 3) *
          (GeneralLinearGroup.scalar (Fin 3) (ζ ^ 3))⁻¹ := by group
      _ = (GeneralLinearGroup.scalar (Fin 3) ζ ^ 3)⁻¹ := by rw [e1, map_pow]; group
  obtain ⟨ℓ, hℓ⟩ := mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hy3.2.1
  have hy3m : (y : Matrix (Fin 3) (Fin 3) K) ^ 3 = (ℓ : K) • 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hℓ, coe_scalar_eq_smul]
  have hℓnc : ∀ μ : K, μ ^ 3 ≠ ℓ :=
    Sec12.KS128NotHJTC.not_cube_of_irreducible hτ hτ1 h3 hy3m hy3.2.2
  set w := y * s ^ j with hw
  have hysj : y * s ^ j * y⁻¹ = GeneralLinearGroup.scalar (Fin 3) (lam ^ j) * s ^ j := by
    have e1 : y * s ^ j * y⁻¹ = (y * s * y⁻¹) ^ j := by
      rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]
    rw [e1, hys, (Commute.mul_zpow (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar lam s).symm
      j), map_zpow]
  have hlamj3 : (lam ^ j) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hlam3, one_zpow]
  have hw3 : w ^ 3 = GeneralLinearGroup.scalar (Fin 3) ((ζ⁻¹ ^ 3) ^ j * ℓ) := by
    have e3 : (s ^ j) ^ 3 = (s ^ 3) ^ j := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    rw [hw, pow_three_mul_of_conj hlamj3 hysj, e3, hs3c, ← map_zpow, ← hℓ, ← map_mul]
  have hw3m : (w : Matrix (Fin 3) (Fin 3) K) ^ 3 = (((ζ⁻¹ ^ 3) ^ j * ℓ : Kˣ) : K) • 1 := by
    rw [← Units.val_pow_eq_pow_val, hw3, coe_scalar_eq_smul]
  have hwnc : ∀ μ : K, μ ^ 3 ≠ (((ζ⁻¹ ^ 3) ^ j * ℓ : Kˣ) : K) := by
    intro μ hμ
    apply hℓnc (μ * ((ζ ^ j : Kˣ) : K))
    have hone : (ζ⁻¹ ^ 3) ^ j * (ζ ^ j) ^ 3 = 1 := by group
    have key : (((ζ⁻¹ ^ 3) ^ j * ℓ : Kˣ) : K) * ((ζ ^ j : Kˣ) : K) ^ 3 = (ℓ : K) := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_mul]
      congr 1
      rw [mul_comm _ ℓ, mul_assoc, hone, mul_one]
    rw [mul_pow, hμ, key]
  have hirr : ∀ W : Submodule K (Fin 3 → K),
      (∀ v ∈ W, (w : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤ := fun W hW =>
    eq_bot_or_eq_top_of_invariant hwnc hw3m hW
  have hwsc : ∀ h ∈ slPi π 3 (p ^ f) K, h * w = w * h → h ^ 2 ∈ StatedScalars (Fin 3) K →
      h ∈ StatedScalars (Fin 3) K := fun h _ hc hh2 =>
    mem_statedScalars_of_commute_irred hirr hc hh2
  have hσd : thetaQuotMulAut L (L.normalizerMonoidHom ⟨d, hdN⟩) = MulAut.conj db := by
    ext v
    induction v using QuotientGroup.induction_on with
    | H l =>
      rw [thetaQuotMulAut_mk, MulAut.conj_apply, hdb, QuotientGroup.mk'_apply,
        ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      congr 1
  have hσz : thetaQuotMulAut L (L.normalizerMonoidHom ⟨x * d ^ j, hzN⟩) =
      σx * MulAut.conj (db ^ j) := by
    have e1 : (⟨x * d ^ j, hzN⟩ : Subgroup.normalizer (L : Set G)) =
        ⟨x, hxN⟩ * ⟨d, hdN⟩ ^ j := Subtype.ext (by simp)
    rw [e1, map_mul, map_mul, map_zpow, map_zpow, hσd, map_zpow]
  intro u hu hu2
  have hcomm : (e u : ProjGenLinGroup (Fin 3) K) * ProjGenLinGroup.mk w =
      ProjGenLinGroup.mk w * (e u : ProjGenLinGroup (Fin 3) K) := by
    have e1 := congrArg (fun v => ((e v : projImage (slPi π 3 (p ^ f) K)) :
      ProjGenLinGroup (Fin 3) K)) hu
    simp only [hσz, MulAut.mul_apply, MulAut.conj_apply] at e1
    rw [hact', map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      map_zpow, Subgroup.coe_zpow, ← hse] at e1
    have e2 : ProjGenLinGroup.mk w = ProjGenLinGroup.mk y * ProjGenLinGroup.mk s ^ j := by
      rw [hw, map_mul, map_zpow]
    rw [e2]
    calc (e u : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk y * ProjGenLinGroup.mk s ^ j) =
        ProjGenLinGroup.mk y * (ProjGenLinGroup.mk s ^ j * (e u : ProjGenLinGroup (Fin 3) K) *
          (ProjGenLinGroup.mk s ^ j)⁻¹) * (ProjGenLinGroup.mk y)⁻¹ *
          (ProjGenLinGroup.mk y * ProjGenLinGroup.mk s ^ j) := by rw [e1]
      _ = ProjGenLinGroup.mk y * ProjGenLinGroup.mk s ^ j * (e u : ProjGenLinGroup (Fin 3) K) := by
          group
  have hu2' : (e u : ProjGenLinGroup (Fin 3) K) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, ← map_pow, hu2, map_one, Subgroup.coe_one]
  have h1u := eq_one_of_sq_of_commute_mk hwsc (e u).2 hu2' hcomm
  apply e.injective
  rw [map_one]
  exact Subtype.ext h1u

end TypeThree

section ModNine

variable {G : Type} [Group G] [Finite G]

theorem two_eq_zero_of_piField {π : Bool} {n : ℕ} {K : Type} [Field K]
    (hK : PiField π 2 n K) : (2 : K) = 0 := by
  have := hK.finite
  let _ := Fintype.ofFinite K
  have hc : ((Nat.card K : ℕ) : K) = 0 := by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero K
  have hcard := hK.card
  have hm : ∃ m : ℕ, Nat.card K = 2 ^ m := by
    cases π
    · exact ⟨2 * n, by rw [hcard]; change (2 ^ n) ^ 2 = _; rw [← pow_mul, mul_comm]⟩
    · exact ⟨n, hcard⟩
  obtain ⟨m, hm⟩ := hm
  rw [hm, Nat.cast_pow, Nat.cast_ofNat] at hc
  exact eq_zero_of_pow_eq_zero hc

theorem fix_of_not_modNine {L : Subgroup G} {z : G} (hzL : z ∈ L) (hz3 : z ^ 3 = 1)
    (hz1 : z ≠ 1) {n : ℕ} (hn : 1 ≤ n)
    (hiso : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 n)
    (h9 : ¬ (2 ^ n % 9 = 1 ∨ 2 ^ n % 9 = 8)) (hzN : z ∈ Subgroup.normalizer (L : Set G)) :
    ∀ u : ↥L ⧸ aschbacherSolvableCore 3 ↥L,
      thetaQuotMulAut L (L.normalizerMonoidHom ⟨z, hzN⟩) u = u → u ^ 2 = 1 → u = 1 := by
  obtain ⟨π, K, _, hK, hq, ⟨e⟩⟩ := exists_projImage_model hn hiso
  have hπ : π = false → UnitaryFieldData 2 n K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (2 ^ n) := fun h => by subst h; exact hq
  have h2 : (2 : K) = 0 := two_eq_zero_of_piField hK
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hsc : ∀ (c : Kˣ) (A : GL (Fin 3) K),
      A * GeneralLinearGroup.scalar (Fin 3) c = GeneralLinearGroup.scalar (Fin 3) c * A :=
    fun c A => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c A).eq
  set z' : ↥L := ⟨z, hzL⟩ with hz'
  have hz'3 : z' ^ 3 = 1 := Subtype.ext (by simpa using hz3)
  set zb : ↥L ⧸ aschbacherSolvableCore 3 ↥L := QuotientGroup.mk' _ z' with hzb
  have hzb3 : zb ^ 3 = 1 := by rw [hzb, ← map_pow, hz'3, map_one]
  have hzb1 : zb ≠ 1 := by
    intro h1
    have h2' := CFSG.RankThree.injOn_mk_of_isPGroup Nat.prime_three
      (isPGroup_zpowers_three hz'3) (Subgroup.mem_zpowers _) (Subgroup.one_mem _)
      (by rw [map_one]; exact h1)
    exact hz1 (congrArg Subtype.val h2')
  obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.mp (e zb).2
  have hsH : s ∈ glPi π 3 (2 ^ n) K := slPi_le_glPi hπ hs
  have hsZ : s ∉ StatedScalars (Fin 3) K := by
    intro hsZ
    apply hzb1
    apply e.injective
    apply Subtype.ext
    rw [← hse, map_one, Subgroup.coe_one, mk_eq_one_iff_mem_statedScalars]
    exact hsZ
  have hs3 : s ^ 3 ∈ StatedScalars (Fin 3) K := by
    rw [← mk_eq_one_iff_mem_statedScalars, map_pow, hse, ← Subgroup.coe_pow, ← map_pow, hzb3,
      map_one, Subgroup.coe_one]
  have hsZ' : s ∉ zPi π 3 (2 ^ n) K := fun hz =>
    hsZ (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz)
  have hs3' : s ^ 3 ∈ zPi π 3 (2 ^ n) K := by
    rw [zPi_eq hπ hq' hτ hτ1]
    exact ⟨pow_mem hsH 3, hs3⟩
  obtain ⟨z₀, hz₀, g, -, hD⟩ : ∃ z₀ ∈ zPi π 3 (2 ^ n) K, ∃ g ∈ glPi π 3 (2 ^ n) K,
      g⁻¹ * (s * z₀) * g = diagTau hτ := by
    rcases (rank3II_4_10_two hK hq hτ hτ1 hsH hsZ' hs3').mp ⟨s, hs, fun m _ => rfl⟩ with
        ⟨y, ⟨z₀, hz₀, rfl⟩, g, hg, hD⟩ | ⟨-, hmod⟩
    · exact ⟨z₀, hz₀, g, hg, hD⟩
    · exfalso
      apply h9
      cases π
      · exact Or.inr hmod
      · exact Or.inl hmod
  have hz₀s : z₀ ∈ StatedScalars (Fin 3) K := mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz₀
  have hwsc : ∀ h ∈ slPi π 3 (2 ^ n) K, h * s = s * h → h ^ 2 ∈ StatedScalars (Fin 3) K →
      h ∈ StatedScalars (Fin 3) K := by
    intro h _ hc hh2
    obtain ⟨ζ, hζ⟩ := hz₀s
    have hcz : h * (s * z₀) = (s * z₀) * h := by
      rw [← hζ, ← mul_assoc, hc, mul_assoc, hsc, ← mul_assoc]
    set h' := g⁻¹ * h * g with hh'
    have hc' : h' * diagTau hτ = diagTau hτ * h' := by
      rw [← hD, hh']
      calc g⁻¹ * h * g * (g⁻¹ * (s * z₀) * g) = g⁻¹ * (h * (s * z₀)) * g := by group
        _ = g⁻¹ * ((s * z₀) * h) * g := by rw [hcz]
        _ = g⁻¹ * (s * z₀) * g * (g⁻¹ * h * g) := by group
    have hh'2 : h' ^ 2 ∈ StatedScalars (Fin 3) K := by
      have e1 : h' ^ 2 = g⁻¹ * h ^ 2 * g := by rw [hh', pow_two, pow_two]; group
      rw [e1]
      have := (StatedScalars.normal (Fin 3) K).conj_mem _ hh2 g⁻¹
      simpa using this
    have hh's := mem_statedScalars_of_commute_diagTau h2 hτ hτ1 hc' hh'2
    have e2 : h = g * h' * g⁻¹ := by rw [hh']; group
    rw [e2]
    exact (StatedScalars.normal (Fin 3) K).conj_mem _ hh's g
  have hσz : thetaQuotMulAut L (L.normalizerMonoidHom ⟨z, hzN⟩) = MulAut.conj zb := by
    ext v
    induction v using QuotientGroup.induction_on with
    | H l =>
      rw [thetaQuotMulAut_mk, MulAut.conj_apply, hzb, QuotientGroup.mk'_apply,
        ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      congr 1
  intro u hu hu2
  have hcomm : (e u : ProjGenLinGroup (Fin 3) K) * ProjGenLinGroup.mk s =
      ProjGenLinGroup.mk s * (e u : ProjGenLinGroup (Fin 3) K) := by
    have e1 := congrArg (fun v => ((e v : projImage (slPi π 3 (2 ^ n) K)) :
      ProjGenLinGroup (Fin 3) K)) hu
    simp only [hσz, MulAut.conj_apply] at e1
    rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      ← hse] at e1
    calc (e u : ProjGenLinGroup (Fin 3) K) * ProjGenLinGroup.mk s =
        ProjGenLinGroup.mk s * (e u : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk s)⁻¹ *
          ProjGenLinGroup.mk s := by rw [e1]
      _ = ProjGenLinGroup.mk s * (e u : ProjGenLinGroup (Fin 3) K) := by group
  have hu2' : (e u : ProjGenLinGroup (Fin 3) K) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, ← map_pow, hu2, map_one, Subgroup.coe_one]
  have h1u := eq_one_of_sq_of_commute_mk hwsc (e u).2 hu2' hcomm
  apply e.injective
  rw [map_one]
  exact Subtype.ext h1u

end ModNine

end CFSG.RankThree.PartTwo.Sec16.Proof1613Fix

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16.Proof169 CFSG.RankThree.PartTwo.Sec16.Proof1613
  CFSG.RankThree.PartTwo.Sec16.Proof1614 CFSG.RankThree.PartTwo.Sec16.Proof1613Inv
  CFSG.RankThree.PartTwo.Sec16.Proof1613Fix CFSG.GH74.GLS

theorem ks1613Fix_of
    (h131 : Item131) (h138 : Item138N) : KS1613Fix := by
  intro G _ _ A c L h h11 D hDAL hD3 T hT
  obtain ⟨hTL, hT2', hAT⟩ := hT
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 T := (isPiSubgroup_piOf_iff Nat.prime_two T).mp hT2'
  have hT3 : ¬ 3 ∣ Nat.card T :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_three_of_isPGroup_two hT2)
  have hA := h.isElemAbelian
  obtain ⟨d, hdD, hd1, rfl⟩ := Sec5.exists_eq_zpowers_of_card_eq_prime Nat.prime_three hD3
  have hdA : d ∈ A := (hDAL hdD).1
  have hdL : d ∈ L := (hDAL hdD).2
  have hd3 : d ^ 3 = 1 := hA.2 d hdA
  have hDL : Subgroup.zpowers d ≤ L := Subgroup.zpowers_le.mpr hdL
  rcases h11 with hPGL | ⟨n, hn1, hiso, hprod⟩
  ·
    have hcL : c ∉ L := h.toSec15R.hypS.2.2 c h.zpowers_mem_omegaA L h.mem_lA
    obtain ⟨-, ⟨hM12p, hM12z⟩, ⟨hJ2p, hJ2z⟩⟩ := sporadicModels131
    obtain ⟨hL3, -, -⟩ := facts_of_isZ3PGLThreePi h.toSec13Data hPGL
    obtain ⟨p, e, hp, -, hisoL⟩ := hL3
    obtain ⟨x, hxA, hx⟩ : ∃ x ∈ A, Sec4.InducesTypeOn L x 3 := by
      rcases cases131 h131 sporadicModels131 slTwoCenter h.toSec13Data with
          ⟨-, -, ⟨ψ⟩, -⟩ | ⟨-, -, hMJ, -⟩ | ⟨-, -, -, hx⟩ | ⟨hcL', -⟩
      · exact (false_of_pgl_of_prod kSPGLProper h.toSec13Data hPGL ψ).elim
      · exfalso
        rcases hMJ with ⟨⟨χ⟩⟩ | ⟨⟨χ⟩⟩
        · obtain ⟨-, -, -, ⟨χ'⟩⟩ := facts_of_prod h.toSec13Data hM12p hM12z χ
          exact KFacts.KS14.not_isoLThreePi_M12 p e (isoLThreePi_of_mulEquiv χ' hisoL)
        · obtain ⟨-, -, -, ⟨χ'⟩⟩ := facts_of_prod h.toSec13Data hJ2p hJ2z χ
          exact KFacts.KS14.ks17J2NotList.1 p e (isoLThreePi_of_mulEquiv χ' hisoL)
      · exact hx
      · exact (hcL hcL').elim
    have hx3 : x ^ 3 = 1 := hA.2 x hxA
    have hxd : x * d = d * x := h.commute hxA hdA
    have hxL : x ∉ L := not_mem_of_inducesTypeOn_three h.mem_thetaComponentsAt hx
    have hxD : x ∉ Subgroup.zpowers d := fun hmem => hxL (hDL hmem)
    set E := Subgroup.zpowers x ⊔ Subgroup.zpowers d with hE
    have hEA : E ≤ A := sup_le (Subgroup.zpowers_le.mpr hxA) (Subgroup.zpowers_le.mpr hdA)
    have hEe : CFSG.Assembly.IsElemAbelian 3 E := isElemAbelian_of_le hA hEA
    have hE9 : Nat.card E = 9 := by
      rw [hE, sup_comm]
      exact Sec4.card_zpowers_sup_zpowers hx3 (orderOf_eq_prime hd3 hd1) hxD hxd
    refine commutator_le_theta_of hTL hDL hEe hE9.ge (hEA.trans hAT) hT3 ?_
    intro F hFE hF3 hFD
    obtain ⟨j, hjF⟩ := exists_mul_zpow_mem hx3 hxd hFE hF3 hFD hd3
    have hzN : x * d ^ j ∈ Subgroup.normalizer (L : Set G) :=
      Subgroup.mul_mem _ (h.le_normalizer hxA)
        (Subgroup.zpow_mem _ (Subgroup.le_normalizer hdL) j)
    refine (inf_le_inf_left _ (Subgroup.centralizer_le
      (Set.singleton_subset_iff.mpr hjF))).trans ?_
    exact inf_centralizer_le_theta hzN hTL hT2 (fix_of_type3 hdL hd3 hd1 hxd hx j hzN)
  ·
    obtain ⟨ψ⟩ := hprod
    have h9 := not_modNine_of_inner h.toSec15R h138 KFacts.kSL3PiOrder3TypeC hn1 hiso ⟨ψ⟩
    have hAL9 : Nat.card (A ⊓ L : Subgroup G) = 9 :=
      card_inf_eq_nine h.toSec13Data (isPerfect_lBar h.toSec13Data) ψ
    have hEe : CFSG.Assembly.IsElemAbelian 3 (A ⊓ L) := isElemAbelian_of_le hA inf_le_left
    refine commutator_le_theta_of hTL hDL hEe hAL9.ge (inf_le_left.trans hAT) hT3 ?_
    intro F hFE hF3 _
    obtain ⟨z, hzF, hz1, -⟩ := Sec5.exists_eq_zpowers_of_card_eq_prime Nat.prime_three hF3
    have hzA : z ∈ A := (hFE hzF).1
    have hzL : z ∈ L := (hFE hzF).2
    have hzN : z ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hzL
    refine (inf_le_inf_left _ (Subgroup.centralizer_le
      (Set.singleton_subset_iff.mpr hzF))).trans ?_
    exact inf_centralizer_le_theta hzN hTL hT2
      (fix_of_not_modNine hzL (hA.2 z hzA) hz1 hn1 hiso h9 hzN)

end CFSG.RankThree.PartTwo.Sec16

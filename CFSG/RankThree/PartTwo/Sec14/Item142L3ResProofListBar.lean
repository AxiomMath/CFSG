module

public import CFSG.RankThree.PartTwo.Sec14.Item142L3ResProofListStd
public import CFSG.RankThree.PartTwo.Sec14.Item142L3ResProofTypesBase
import CFSG.RankThree.PartTwo.Sec16.Item1613StepsProofTrans
import CFSG.RankThree.PartTwo.Sec16.Item1613StepsProofFix
import CFSG.RankThree.PartTwo.Sec16.Item1613StepsProofInv
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item13K410
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian

public section

namespace CFSG.RankThree.PartTwo.Sec14.L3PGL

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec14.Proof142Res
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open Matrix (ProjGenLinGroup GeneralLinearGroup)

theorem coe_zpow_apply {P : Type*} [Group P] {M : Subgroup P} (φ : MulAut M) (g : P)
    (hφ : ∀ m : M, ((φ m : M) : P) = g * m * g⁻¹) (j : ℤ) (m : M) :
    (((φ ^ j) m : M) : P) = g ^ j * m * (g ^ j)⁻¹ := by
  have hφi : ∀ m : M, ((φ⁻¹ m : M) : P) = g⁻¹ * m * g := by
    intro m
    have h1 := hφ (φ⁻¹ m)
    rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply] at h1
    calc ((φ⁻¹ m : M) : P) = g⁻¹ * (g * (φ⁻¹ m : P) * g⁻¹) * g := by group
      _ = g⁻¹ * m * g := by rw [← h1]
  induction j using Int.induction_on generalizing m with
  | zero => simp
  | succ k ih =>
    rw [zpow_add_one, MulAut.mul_apply, ih, hφ, zpow_add_one]
    group
  | pred k ih =>
    rw [zpow_sub_one, MulAut.mul_apply, ih, hφi, zpow_sub_one]
    group

variable {G : Type} [Group G] [Finite G]

theorem plane_model {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (hPGLA : Sec8.IsZ3PGLThreePi (Sec13.lBarA c L A)) {x : G} (hxA : x ∈ A)
    (hxN : x ∈ Subgroup.normalizer (L : Set G)) {π : Bool} {p f : ℕ} {K : Type} [Field K]
    (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (e : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* projImage (slPi π 3 (p ^ f) K))
    {y : GL (Fin 3) K} (hyH : y ∈ glPi π 3 (p ^ f) K) (hy3 : Type123 π (p ^ f) K y 3)
    (hact : ∀ z : ↥L ⧸ aschbacherSolvableCore 3 ↥L,
      ((e (sigmaOf L hxN z) : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk y * (e z : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk y)⁻¹) :
    ∃ s : GL (Fin 3) K, s ∈ slPi π 3 (p ^ f) K ∧ s ∉ StatedScalars (Fin 3) K ∧
      s ^ 3 ∈ StatedScalars (Fin 3) K ∧ y * s * y⁻¹ * s⁻¹ ∈ StatedScalars (Fin 3) K ∧
      (∀ (a : G) (_ : a ∈ A) (haN : a ∈ Subgroup.normalizer (L : Set G)), ∃ i j : ℤ,
        ∀ z : ↥L ⧸ aschbacherSolvableCore 3 ↥L,
          ((e (sigmaOf L haN z) : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
            (ProjGenLinGroup.mk s ^ i * ProjGenLinGroup.mk y ^ j) *
              (e z : ProjGenLinGroup (Fin 3) K) *
                (ProjGenLinGroup.mk s ^ i * ProjGenLinGroup.mk y ^ j)⁻¹) ∧
      ∀ i j : ℤ, ∃ (a : G) (_ : a ∈ A) (haN : a ∈ Subgroup.normalizer (L : Set G)),
        ∀ z : ↥L ⧸ aschbacherSolvableCore 3 ↥L,
          ((e (sigmaOf L haN z) : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
            (ProjGenLinGroup.mk s ^ i * ProjGenLinGroup.mk y ^ j) *
              (e z : ProjGenLinGroup (Fin 3) K) *
                (ProjGenLinGroup.mk s ^ i * ProjGenLinGroup.mk y ^ j)⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.toSec13Data
  have hA := hD.isElemAbelian
  have h27 := hD.card_eq
  have hcA := hD.mem_A
  have hAN := hD.le_normalizer
  have hLc := hD.le_centralizer
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => hD.commute ha hb
  have hx : InducesTypeOn L x 3 := ⟨hxN, π, p, f, K, inferInstance, hK, hq, e, y, hyH, hy3, hact⟩
  obtain ⟨d, hdAL, hd1, -⟩ := Sec5.exists_eq_zpowers_of_card_eq_prime Nat.prime_three
    (Sec16.Proof1614Trans.card_inf_eq_three_of_pgl hD hPGLA)
  have hdA : d ∈ A := hdAL.1
  have hdL : d ∈ L := hdAL.2
  have hd3 : d ^ 3 = 1 := hA.2 d hdA
  have hcL : c ∉ L := Sec13.not_mem_of_center_eq_bot hD
    (Sec13.facts_of_isZ3PGLThreePi hD hPGLA).2.1
  have hcd : c ∉ Subgroup.zpowers d := fun h => hcL (Subgroup.zpowers_le.mpr hdL h)
  have h9 := Sec13.card_zpowers_sup_zpowers_eq_nine hA h27 hcA hdA hd1 hcd
  have hcN : c ∈ Subgroup.normalizer (L : Set G) := hAN hcA
  have hdN : d ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hdL
  have hσc : ∀ k : ℤ, ∀ hk : c ^ k ∈ Subgroup.normalizer (L : Set G),
      thetaQuotMulAut L (L.normalizerMonoidHom ⟨c ^ k, hk⟩) = 1 := by
    intro k hk
    ext v
    induction v using QuotientGroup.induction_on with
    | H l =>
      rw [thetaQuotMulAut_mk, MulAut.one_apply]
      congr 1
      apply Subtype.ext
      rw [normalizerMonoidHom_apply_coe]
      have hlc : (l : G) * c ^ k = c ^ k * l :=
        (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp (hLc l.2)) k)
      rw [← hlc, mul_inv_cancel_right]
  have hcLθ := hD.mem_thetaComponentsAt
  have hxcd : x ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
    intro hxcd
    obtain ⟨i, j, hij⟩ := Sec4.exists_zpow_mul_of_mem_sup (hcomm c hcA d hdA) hxcd
    have hx' := inducesTypeOn_mul_of_eq_one hx (Subgroup.zpow_mem _ hcN (-i))
      (hσc (-i) (Subgroup.zpow_mem _ hcN (-i)))
    apply Sec16.Proof1613Fix.not_mem_of_inducesTypeOn_three hcLθ hx'
    rw [hij, mul_assoc, (hcomm _ (Subgroup.zpow_mem _ hdA j) _
      (Subgroup.zpow_mem _ hcA (-i))), ← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero,
      one_mul]
    exact Subgroup.zpow_mem _ hdL j
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set σx := thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hxN⟩) with hσx
  set d' : ↥L := ⟨d, hdL⟩ with hd'
  have hd'3 : d' ^ 3 = 1 := Subtype.ext (by simpa using hd3)
  set db : ↥L ⧸ θ := QuotientGroup.mk' _ d' with hdb
  have hdb3 : db ^ 3 = 1 := by rw [hdb, ← map_pow, hd'3, map_one]
  have hdb1 : db ≠ 1 := by
    intro h1
    have h2 := CFSG.RankThree.injOn_mk_of_isPGroup Nat.prime_three
      (Sec16.Proof1613Inv.isPGroup_zpowers_three hd'3) (Subgroup.mem_zpowers _)
      (Subgroup.one_mem _) (by rw [map_one]; exact h1)
    exact hd1 (congrArg Subtype.val h2)
  obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.mp (e db).2
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
  have hxd : x * d = d * x := hcomm x hxA d hdA
  have hfix : σx db = db := by
    rw [hσx, hdb, QuotientGroup.mk'_apply, thetaQuotMulAut_mk]
    congr 1
    apply Subtype.ext
    rw [normalizerMonoidHom_apply_coe, hxd, mul_inv_cancel_right]
  have h1 := hact db
  change ((e (σx db) : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) = _ at h1
  rw [hfix, ← hse] at h1
  have hysZ : y * s * y⁻¹ * s⁻¹ ∈ StatedScalars (Fin 3) K := by
    rw [← mk_eq_one_iff_mem_statedScalars, map_mul, map_mul, map_mul, map_inv, map_inv, ← h1,
      mul_inv_cancel]
  set σd := thetaQuotMulAut L (L.normalizerMonoidHom ⟨d, hdN⟩) with hσd
  have hσdc : σd = MulAut.conj db := by
    ext v
    induction v using QuotientGroup.induction_on with
    | H l =>
      rw [hσd, thetaQuotMulAut_mk, MulAut.conj_apply, hdb, QuotientGroup.mk'_apply,
        ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      congr 1
  have hed : ∀ m : projImage (slPi π 3 (p ^ f) K),
      ((MulAut.congr e σd m : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk s * m * (ProjGenLinGroup.mk s)⁻¹ := by
    intro m
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, hσdc, MulAut.conj_apply,
      map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, ← hse]
  have hex : ∀ m : projImage (slPi π 3 (p ^ f) K),
      ((MulAut.congr e σx m : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk y * m * (ProjGenLinGroup.mk y)⁻¹ := by
    intro m
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
    have := hact (e.symm m)
    rwa [MulEquiv.apply_symm_apply] at this
  have hij : ∀ (i j : ℤ) (z : ↥L ⧸ θ),
      ((e ((σd ^ i * σx ^ j) z) : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
        (ProjGenLinGroup.mk s ^ i * ProjGenLinGroup.mk y ^ j) *
          (e z : ProjGenLinGroup (Fin 3) K) *
            (ProjGenLinGroup.mk s ^ i * ProjGenLinGroup.mk y ^ j)⁻¹ := by
    intro i j z
    have e1 : e ((σd ^ i * σx ^ j) z) =
        (MulAut.congr e σd ^ i) ((MulAut.congr e σx ^ j) (e z)) := by
      rw [← map_zpow (MulAut.congr e) σd i, ← map_zpow (MulAut.congr e) σx j]
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
        MulAut.mul_apply]
    rw [e1, coe_zpow_apply _ _ hed, coe_zpow_apply _ _ hex]
    group
  refine ⟨s, hs, hsZ, hs3, hysZ, fun a haA haN => ?_, fun i j => ?_⟩
  · obtain ⟨i, j, m, -, rfl⟩ := exists_pow_mul_eq hA h27 hcA hdA hxA h9 hxcd haA
    refine ⟨j, m, fun z => ?_⟩
    have hdec : (⟨c ^ i * d ^ j * x ^ m, haN⟩ : Subgroup.normalizer (L : Set G)) =
        ⟨c, hcN⟩ ^ i * ⟨d, hdN⟩ ^ j * ⟨x, hxN⟩ ^ m := Subtype.ext (by simp)
    have hc1 : thetaQuotMulAut L (L.normalizerMonoidHom ⟨c, hcN⟩) = 1 := by
      have := hσc 1 (by simpa using hcN)
      simpa using this
    have hσa : sigmaOf L haN = σd ^ j * σx ^ (m : ℤ) := by
      rw [zpow_natCast, sigmaOf, hdec]
      simp only [map_mul, map_zpow, map_pow, hc1, one_zpow, one_mul]
      rfl
    rw [hσa, hij]
  · refine ⟨d ^ i * x ^ j, mul_mem (zpow_mem hdA i) (zpow_mem hxA j),
      mul_mem (zpow_mem hdN i) (zpow_mem hxN j), fun z => ?_⟩
    have hσa : sigmaOf L (mul_mem (zpow_mem hdN i) (zpow_mem hxN j)) = σd ^ i * σx ^ j := by
      have hdec : (⟨d ^ i * x ^ j, mul_mem (zpow_mem hdN i) (zpow_mem hxN j)⟩ :
          Subgroup.normalizer (L : Set G)) = ⟨d, hdN⟩ ^ i * ⟨x, hxN⟩ ^ j :=
        Subtype.ext (by simp)
      rw [sigmaOf, hdec]
      simp only [map_mul, map_zpow]
      rfl
    rw [hσa, hij]

theorem list_bar {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (hPGLA : Sec8.IsZ3PGLThreePi (Sec13.lBarA c L A)) (hx : ∃ x ∈ A, Sec4.InducesTypeOn L x 3) :
    (∀ Y : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L), ¬ 3 ∣ Nat.card Y →
      (∀ σ ∈ Sec4.autThetaQuot A L, Y.map σ.toMonoidHom ≤ Y) →
      ∃ (a : G) (_ : a ∈ A) (haN : a ∈ Subgroup.normalizer (L : Set G)),
        sigmaOf L haN ≠ 1 ∧
          Y ≤ inSubgroup (aschbacherSolvableCore 3) (Res5Types.fixSubgroup (sigmaOf L haN))) ∧
    IsPGroup 3 (fixA A L) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.toSec13Data
  obtain ⟨x, hxA, hx⟩ := hx
  obtain ⟨hxN, π, p, f, K, _, hK, hq, e, y, hyH, hy3, hact⟩ := hx
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  obtain ⟨s, hs, hsZ, hs3, hysZ, -, hσ'⟩ := plane_model h hPGLA hxA hxN hK hq e hyH hy3 hact
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  have hLθ := hD.mem_thetaComponentsAt
  have hqs := Sec6.isQuasisimple_of_mem_thetaComponentsAt hLθ
  have hLp : Group.IsPerfect (↥L ⧸ aschbacherSolvableCore 3 ↥L) := hqs.1
  have : IsSimpleGroup ((↥L ⧸ aschbacherSolvableCore 3 ↥L) ⧸
      Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := hqs.2.1
  have hLnt : Nontrivial (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    (QuotientGroup.mk_surjective
      (s := Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L))).nontrivial
  have hq2 : 2 < p ^ f := by
    by_contra h2
    have hp := hK.prime
    have hf := hK.one_le
    have h2' : p ^ f = 2 := by
      have : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) _)
      omega
    cases π
    · have := Sec13.isSolvable_projImage_slPi_two hK h2'
      have : Group.IsSolvable (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
        Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
      exact Group.IsPerfect.not_isSolvable _ this
    · change p ^ f % 3 = 1 at hq
      omega
  set ι : (↥L ⧸ aschbacherSolvableCore 3 ↥L) →* ProjGenLinGroup (Fin 3) K :=
    (projImage (slPi π 3 (p ^ f) K)).subtype.comp e.toMonoidHom with hιdef
  have hιz : ∀ z, ι z = ((e z : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) :=
    fun z => rfl
  have hι : Function.Injective ι := fun a b hab => e.injective (Subtype.ext hab)
  have hc : ProjGenLinGroup.mk y * ProjGenLinGroup.mk s * (ProjGenLinGroup.mk y)⁻¹ *
      (ProjGenLinGroup.mk s)⁻¹ = 1 := by
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    exact mk_eq_one_iff_mem_statedScalars.mpr hysZ
  have hsy : ProjGenLinGroup.mk s * ProjGenLinGroup.mk y =
      ProjGenLinGroup.mk y * ProjGenLinGroup.mk s := by
    have h1 := mul_inv_eq_one.mp hc
    calc ProjGenLinGroup.mk s * ProjGenLinGroup.mk y =
        ProjGenLinGroup.mk y * ProjGenLinGroup.mk s * (ProjGenLinGroup.mk y)⁻¹ *
          ProjGenLinGroup.mk y := by rw [h1]
      _ = ProjGenLinGroup.mk y * ProjGenLinGroup.mk s := by group
  have hfixcomm : ∀ (a : G) (haN : a ∈ Subgroup.normalizer (L : Set G))
      (g : ProjGenLinGroup (Fin 3) K),
      (∀ z, ι (sigmaOf L haN z) = g * ι z * g⁻¹) →
      ∀ z, sigmaOf L haN z = z → ι z * g = g * ι z := by
    intro a haN g hg z hz
    have h1 := hg z
    rw [hz] at h1
    calc ι z * g = g * ι z * g⁻¹ * g := by rw [← h1]
      _ = g * ι z := by group
  refine ⟨fun Y hY3 hYinv => ?_, ?_⟩
  · set YP := Y.map ι with hYP
    have hYP3 : ¬ 3 ∣ Nat.card YP := by
      rw [hYP, Subgroup.card_map_of_injective hι]
      exact hY3
    have hnorm : ∀ i j : ℤ, ProjGenLinGroup.mk s ^ i * ProjGenLinGroup.mk y ^ j ∈
        Subgroup.normalizer (YP : Set (ProjGenLinGroup (Fin 3) K)) := by
      intro i j
      obtain ⟨a, haA, haN, hz⟩ := hσ' i j
      refine Subgroup.mem_normalizer_fintype fun u hu => ?_
      obtain ⟨z, hzY, rfl⟩ := hu
      have hσY : Y.map (sigmaOf L haN).toMonoidHom ≤ Y :=
        hYinv _ (Sec4.mem_autThetaQuot_iff.mpr ⟨a, haN, haA, rfl⟩)
      exact ⟨sigmaOf L haN z, hσY ⟨z, hzY, rfl⟩, hz z⟩
    have hsY : ProjGenLinGroup.mk s ∈ Subgroup.normalizer (YP : Set (ProjGenLinGroup (Fin 3) K)) :=
      by simpa using hnorm 1 0
    have hyY : ProjGenLinGroup.mk y ∈ Subgroup.normalizer (YP : Set (ProjGenLinGroup (Fin 3) K)) :=
      by simpa using hnorm 0 1
    obtain ⟨b, hbE, hb1, hYb⟩ :=
      exists_le_thetaP_ys hπ hK hq hyH hy3 hs hsZ hs3 hysZ hYP3 hyY hsY
    have hfacts := thetaP_facts_ys hπ hK hq hyH hy3 hs hsZ hs3 hysZ hbE hb1
    obtain ⟨i, j, rfl⟩ := Sec4.exists_zpow_mul_of_mem_sup hsy hbE
    obtain ⟨a, haA, haN, hz⟩ := hσ' i j
    set b := ProjGenLinGroup.mk s ^ i * ProjGenLinGroup.mk y ^ j with hb
    have hz' : ∀ w, ι (sigmaOf L haN w) = b * ι w * b⁻¹ := fun w => hz w
    refine ⟨a, haA, haN, fun h1 => hb1 ?_, ?_⟩
    ·
      apply Sec13.eq_one_of_conj_eq_self hK hq hq2
      intro m hm
      have h2 := hz' (e.symm ⟨m, hm⟩)
      rw [h1, MulAut.one_apply, hιz, MulEquiv.apply_symm_apply] at h2
      exact h2.symm
    ·
      set V₀ : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) := (thetaP b).comap ι with hV₀
      have hYV : Y ≤ V₀ := fun z hz => hYb ⟨z, hz, rfl⟩
      have hVfix : V₀ ≤ Res5Types.fixSubgroup (sigmaOf L haN) := by
        intro z hz
        change sigmaOf L haN z = z
        apply hι
        rw [hz' z, (comm_of_mem_thetaP hz).symm, mul_inv_cancel_right]
      have hVn : ∀ g ∈ Res5Types.fixSubgroup (sigmaOf L haN), ∀ v ∈ V₀, g * v * g⁻¹ ∈ V₀ := by
        intro g hg v hv
        have hgb := hfixcomm a haN b hz' g hg
        change ι (g * v * g⁻¹) ∈ thetaP b
        have h2 := conj_mem_thetaP (ι g) hv
        have e2 : ι g * b * (ι g)⁻¹ = b := by rw [hgb, mul_inv_cancel_right]
        rw [e2] at h2
        rwa [map_mul, map_mul, map_inv]
      have hVc : ∀ v ∈ V₀, ∀ w ∈ V₀, v * w = w * v := fun v hv w hw =>
        hι (by rw [map_mul, map_mul, hfacts.1 _ hv _ hw])
      have : IsMulCommutative V₀ := ⟨⟨fun v w => Subtype.ext (hVc v v.2 w w.2)⟩⟩
      have hVp : ¬ 3 ∣ Nat.card V₀ := by
        refine not_three_dvd_card_of_pow_three fun v hv hv3 => ?_
        have h3 := hfacts.2 _ hv
        rw [orderOf_injective ι hι] at h3
        exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes h3
          (orderOf_dvd_of_pow_eq_one hv3) (dvd_refl _))
      exact hYV.trans (Res8Hess.le_theta_of_normal hVfix hVn inferInstance hVp)
  ·
    rintro ⟨g, hg⟩
    obtain ⟨k, m, hm3, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' 3 (by norm_num)
    refine ⟨k, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    set g' := g ^ (3 ^ k) with hg'
    have hg'fix : g' ∈ fixA A L := pow_mem hg _
    have hord : Nat.Coprime 3 (orderOf g') := by
      have hdvd : orderOf g' ∣ m := by
        refine orderOf_dvd_of_pow_eq_one ?_
        rw [hg', ← pow_mul, ← hnm, pow_orderOf_eq_one]
      exact Nat.Coprime.coprime_dvd_right hdvd
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm3)
    obtain ⟨a₁, ha₁A, ha₁N, hz₁⟩ := hσ' 1 0
    obtain ⟨a₂, ha₂A, ha₂N, hz₂⟩ := hσ' 0 1
    have hs1 := hfixcomm a₁ ha₁N (ProjGenLinGroup.mk s ^ (1 : ℤ) * ProjGenLinGroup.mk y ^ (0 : ℤ))
      (fun w => hz₁ w) g'
      (hg'fix _ (Sec4.mem_autThetaQuot_iff.mpr ⟨a₁, ha₁N, ha₁A, rfl⟩))
    have hy1 := hfixcomm a₂ ha₂N (ProjGenLinGroup.mk s ^ (0 : ℤ) * ProjGenLinGroup.mk y ^ (1 : ℤ))
      (fun w => hz₂ w) g'
      (hg'fix _ (Sec4.mem_autThetaQuot_iff.mpr ⟨a₂, ha₂N, ha₂A, rfl⟩))
    simp only [zpow_one, zpow_zero, mul_one, one_mul] at hs1 hy1
    have h1 := eq_one_of_comm_ys hπ hK hq hyH hy3 hs hsZ hs3 hysZ hy1 hs1
      (by rw [orderOf_injective ι hι]; exact hord)
    exact hι (h1.trans (map_one ι).symm)

end CFSG.RankThree.PartTwo.Sec14.L3PGL

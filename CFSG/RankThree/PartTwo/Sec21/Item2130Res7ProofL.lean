module

public import CFSG.RankThree.PartTwo.Sec21.Item2130Res7ProofSL
public import CFSG.RankThree.PartTwo.Sec21.Item2130Res7ProofLTools
import CFSG.RankThree.PartTwo.Sec6.Item612
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec21.Item21Res7ProofOmegaTools
import CFSG.RankThree.PartTwo.Sec21.Item2119End3Proof2125Unique
import CFSG.RankThree.PartTwo.Sec10.Step1012ClaimProofExcl
import CFSG.RankThree.PartTwo.Sec10.Item101
public import CFSG.RankThree.PartTwo.Sec21.Item2130Res6ProofB

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly (IsElemAbelian)

open CFSG.Assembly.LowTwoRank (StatedScalars)

open CFSG.Assembly.RankThreeEven (projImage)

open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

open Matrix (ProjGenLinGroup GeneralLinearGroup diagonal)

open Item211Res2Proof Item2130Res6Proof

namespace Item2130Res7Proof

variable {G : Type} [Group G] [Finite G] {A E U L U₀ Y : Subgroup G} {c b : G}

section Certs


theorem false_of_typeC_l (hcfg : Config2130 G A E U c L) (h9 : Nat.card (A ⊓ L : Subgroup G) = 9)
    (hC : Choice2130 A E c L b U₀ Y) (hcY : c ∉ Y) {p f : ℕ} {K : Type} [Field K]
    (hK : PiField true p f K) (hq : ModThree true (p ^ f)) (h2 : (2 : K) = 0)
    (e : lBar Y ≃* projImage (slPi true 3 (p ^ f) K)) {D : Subgroup (GL (Fin 3) K)}
    (hD : IsTypeC true (p ^ f) K D)
    (hAD : ∀ τ ∈ autThetaQuot A Y, ∃ y ∈ D, ∀ z : lBar Y,
      ((e (τ z) : ProjGenLinGroup (Fin 3) K)) =
        ProjGenLinGroup.mk y * (e z : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk y)⁻¹)
    (hDA : ∀ y ∈ D, ∃ τ ∈ autThetaQuot A Y, ∀ z : lBar Y,
      ((e (τ z) : ProjGenLinGroup (Fin 3) K)) =
        ProjGenLinGroup.mk y * (e z : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk y)⁻¹)
    {yc : GL (Fin 3) K} (hycD : yc ∈ D)
    (hyc : ∀ z : lBar Y, ((e (barHom Y ⟨c, hC.c_norm⟩ z) : ProjGenLinGroup (Fin 3) K)) =
      ProjGenLinGroup.mk yc * (e z : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk yc)⁻¹)
    (h2t : Type123 true (p ^ f) K yc 2) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  have hAe : IsElemAbelian 3 A := hcfg.pair.mem_S.1.1
  have hAmax : ∀ B : Subgroup G, IsElemAbelian 3 B → A ≤ B → B = A := hcfg.pair.mem_S.1.2.1
  have hA : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAe.2 g g.2)⟩
  have hpairs := mem_lThreeStarPairs_iff.mp hcfg.pair.mem_pair
  have hcA : c ∈ A := hcfg.pair.mem_E.2 hpairs.1.1
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  have hbA : b ∈ A := hC.b_mem.1
  have hb3 : b ^ 3 = 1 := hAe.2 b hbA
  have hb1 : b ≠ 1 := hC.b_ne_one
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hAC : A ≤ Subgroup.centralizer ({b} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hx b hbA)
  have hAL : A ≤ Subgroup.normalizer (Y : Set G) := hC.three_norm A hA hAC
  have hYb : Y ∈ thetaComponentsAt 3 b := lZeroStarAt_subset A b hC.y_mem
  have hYC : Y ≤ Subgroup.centralizer ({b} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hYb
  have hqY : IsQuasisimple (lBar Y) := Sec6.isQuasisimple_of_mem_thetaComponentsAt hYb
  have : Group.IsPerfect (lBar Y) := hqY.1
  have hπ : true = false → UnitaryFieldData p f K := fun h => absurd h (by decide)
  have hq2 := two_lt_of_projImage hK hq hqY e
  have hM := isBarModel_projImage hK hq hq2 e
  have : Group.IsPerfect (projImage (slPi true 3 (p ^ f) K)) := hM.isPerfect
  set ε : lBar Y →* ProjGenLinGroup (Fin 3) K :=
    (projImage (slPi true 3 (p ^ f) K)).subtype.comp e.toMonoidHom with hε
  have hεinj : Function.Injective ε := fun z z' h => e.injective (Subtype.ext h)
  have hle : ε.range ≤ projImage (slPi true 3 (p ^ f) K) := hM.range_eq.le
  have hge : projImage (slPi true 3 (p ^ f) K) ≤ ε.range := hM.range_eq.ge
  have hCA : A ⊓ thetaQuotCentralizer Y = Subgroup.zpowers b := by
    have hset := Sec13.sectionCentralizer_eq_inf hAL
    rw [hC.sec_cent] at hset
    exact SetLike.coe_injective hset.symm
  have hbK : b ∈ thetaQuotCentralizer Y :=
    Sec6.mem_thetaQuotCentralizer_of_mem_thetaComponentsAt hYb
  set toY : ∀ M : GL (Fin 3) K, M ∈ slPi true 3 (p ^ f) K → lBar Y :=
    fun M hM => e.symm ⟨ProjGenLinGroup.mk M, ⟨M, hM, rfl⟩⟩ with htoY
  have hεtoY : ∀ M (hM : M ∈ slPi true 3 (p ^ f) K), ε (toY M hM) = ProjGenLinGroup.mk M :=
    fun M hM => by simp [hε, htoY]
  have hSL : ∀ X ∈ slPi true 3 (p ^ f) K, ∀ g : GL (Fin 3) K, g * X * g⁻¹ ∈ slPi true 3 (p ^ f) K :=
    fun X hX g => conj_mem_slPi hπ (mem_glPi_true _ g) hX
  have hAD' : ∀ x ∈ A, ∃ y ∈ D, ActsVia Y ε x y := fun x hx => by
    obtain ⟨y, hy, hyz⟩ := hAD _ (mem_autThetaQuot_iff.mpr ⟨x, hAL hx, hx, rfl⟩)
    exact ⟨y, hy, hAL hx, hyz⟩
  have hycA : ActsVia Y ε c yc := ⟨hC.c_norm, hyc⟩
  have hycZ : yc ∉ StatedScalars (Fin 3) K := by
    intro hZ
    have hcC := hycA.mem_thetaQuotCentralizer hM.faithful hZ
    have hcb : c ∈ Subgroup.zpowers b := hCA ▸ (⟨hcA, hcC⟩ : c ∈ A ⊓ thetaQuotCentralizer Y)
    exact hcfg.not_mem ((Subgroup.zpowers_le.mpr hC.b_mem.2) hcb)
  obtain ⟨g, -, hdiag, hsurj, lc, σ, hσ, hσ1, hgc⟩ :=
    exists_frame_of_type2 hK hq hD hycD hycZ h2t
  have hσ3 : σ ^ 3 = 1 := (mem_rootsOfUnity _ _).mp hσ
  have hAmat : ∀ x ∈ A, ∃ s t : Kˣ, s ^ 3 = 1 ∧ t ^ 3 = 1 ∧
      ActsVia Y ε x (g * diagUnits 1 s t * g⁻¹) := by
    intro x hx
    obtain ⟨y, hyD, hy⟩ := hAD' x hx
    obtain ⟨l, s, t, hs, ht, hl⟩ := hdiag y hyD
    refine ⟨s, t, (mem_rootsOfUnity _ _).mp hs, (mem_rootsOfUnity _ _).mp ht,
      ActsVia.of_mk_eq hy ?_⟩
    have hy' : y = g * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) * g⁻¹ := by
      rw [← hl]
      group
    rw [hy', conj_frame_scalar, mk_scalar_mul]
  have hfixA : ∀ (u v w : Kˣ) (hM : g * diagUnits u v w * g⁻¹ ∈ slPi true 3 (p ^ f) K)
      (a : G) (ha : a ∈ A), barHom Y ⟨a, hAL ha⟩ (toY _ hM) = toY _ hM := by
    intro u v w hM a ha
    obtain ⟨s, t, -, -, hst⟩ := hAmat a ha
    apply hεinj
    obtain ⟨hg', hst'⟩ := hst
    rw [hst' (toY _ hM), hεtoY _ hM, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    calc g * diagUnits 1 s t * g⁻¹ * (g * diagUnits u v w * g⁻¹) *
          (g * diagUnits 1 s t * g⁻¹)⁻¹ =
        g * (diagUnits 1 s t * diagUnits u v w * (diagUnits 1 s t)⁻¹) * g⁻¹ := by group
      _ = g * diagUnits u v w * g⁻¹ := by rw [diagUnits_comm, mul_inv_cancel_right]
  have hcube : ∀ (u v w : Kˣ) (hM : g * diagUnits u v w * g⁻¹ ∈ slPi true 3 (p ^ f) K),
      u ^ 3 = 1 → v ^ 3 = 1 → w ^ 3 = 1 → (toY _ hM) ^ 3 = 1 := by
    intro u v w hM hu hv hw
    apply hεinj
    rw [map_pow, hεtoY _ hM, ← map_pow, conj_pow, diagUnits_pow, hu, hv, hw, diagUnits_one,
      mul_one, mul_inv_cancel, map_one, map_one]
  have hD'S : g * diagUnits 1 σ (σ ^ 2) * g⁻¹ ∈ slPi true 3 (p ^ f) K :=
    hSL _ (diagUnits_mem_slPi_true (by rw [one_mul, ← pow_succ', hσ3]) _) g
  set Dp : lBar Y := toY _ hD'S with hDp
  have hσ6 : (σ ^ 2) ^ 3 = 1 := by
    rw [← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hσ3, one_pow]
  have hDp3 : Dp ^ 3 = 1 := hcube 1 σ (σ ^ 2) hD'S (one_pow 3) hσ3 hσ6
  obtain ⟨d, hdA, hd⟩ := exists_lift_mem hAe hAmax hAL hDp3 (hfixA 1 σ (σ ^ 2) hD'S)
  have hdB : (d : G) ∈ A ⊓ L := mem_inf_of_mem hcfg hC hcY hdA d.2
  have hd3 : (d : G) ^ 3 = 1 := hAe.2 _ hdA
  have hbY : b ∉ Y := by
    intro hbY
    have h1 : ((⟨b, hbY⟩ : Y) : lBar Y) = 1 := by
      refine eq_one_of_commute_of_mulEquiv hK hq e fun u => ?_
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective u
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hYC u.2)).symm
    have h2 := eq_one_of_mk_eq_one h1 (k := 1) (by apply Subtype.ext; simpa using hb3)
    exact hb1 (congrArg Subtype.val h2)
  have hDp1 : Dp ≠ 1 := by
    intro h
    have h0 := hεtoY _ hD'S
    rw [← hDp, h, map_one] at h0
    have h1 := mk_eq_one_iff_mem_statedScalars.mp h0.symm
    rw [← inv_conj_mem_statedScalars_iff g,
      show g⁻¹ * (g * diagUnits 1 σ (σ ^ 2) * g⁻¹) * g = diagUnits 1 σ (σ ^ 2) by group] at h1
    have h2 : GeneralLinearGroup.scalar (Fin 3) 1 * diagUnits 1 σ (σ ^ 2) ∈
        StatedScalars (Fin 3) K := by rwa [map_one, one_mul]
    exact hσ1 ((scalar_mul_diagUnits_mem_iff 1 σ (σ ^ 2)).mp h2).1
  have hd1 : (d : G) ≠ 1 := by
    intro h
    apply hDp1
    rw [← hd, show d = 1 from Subtype.ext h, QuotientGroup.mk_one]
  have hdb : (d : G) ∉ Subgroup.zpowers b := fun h =>
    hbY ((Subgroup.zpowers_le.mpr d.2)
      (Item21Late2Proof.mem_zpowers_of_mem hb3 h hd1 (Subgroup.mem_zpowers b)))
  have hbd : b * (d : G) = d * b := hcomm b hbA d hdA
  have hBbd : A ⊓ L = Subgroup.zpowers b ⊔ Subgroup.zpowers (d : G) := by
    obtain ⟨-, hcard⟩ := Item2119End3Proof.isElemAbelian_sup_zpowers
      (Item2119End3Proof.isElemAbelian_zpowers' hb3) hd3 (fun y hy => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact ((Commute.zpow_right (show Commute (d : G) b from hbd.symm) k).eq))
    have h9' : Nat.card (Subgroup.zpowers b ⊔ Subgroup.zpowers (d : G) : Subgroup G) = 9 := by
      rw [hcard hdb, Nat.card_zpowers, orderOf_eq_prime hb3 hb1]
    symm
    exact Subgroup.eq_of_le_of_card_ge
      (sup_le (Subgroup.zpowers_le.mpr hC.b_mem) (Subgroup.zpowers_le.mpr hdB)) (by rw [h9, h9'])
  have hAYd : ∀ y : G, y ∈ A → y ∈ Y → y ∈ Subgroup.zpowers (d : G) := by
    intro y hyA hyY
    have hyB := mem_inf_of_mem hcfg hC hcY hyA hyY
    rw [hBbd] at hyB
    obtain ⟨i, hi3, j, -, hij⟩ := Item21Late2Proof.exists_pow_mul_pow_of_mem_sup hbd hb3 hd3 hyB
    have hbi : b ^ i ∈ Y := by
      have e1 : b ^ i = y * ((d : G) ^ j)⁻¹ := by rw [hij]; group
      rw [e1]
      exact Y.mul_mem hyY (Y.inv_mem (Y.pow_mem d.2 j))
    by_cases hi0 : i = 0
    · rw [hij, hi0, pow_zero, one_mul]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) j
    · exact absurd ((Subgroup.zpowers_le.mpr hbi) (mem_zpowers_pow_of_lt_three hb3 hi0 hi3)) hbY
  have hcnot : ∀ w : lBar Y, (∀ z, barHom Y ⟨c, hC.c_norm⟩ z = w * z * w⁻¹) → False := by
    intro w hw
    have hwA : ∀ (a : G) (ha : a ∈ A), barHom Y ⟨a, hAL ha⟩ w = w := by
      intro a ha
      set α := barHom Y ⟨a, hAL ha⟩ with hα
      have hac : α * barHom Y ⟨c, hC.c_norm⟩ = barHom Y ⟨c, hC.c_norm⟩ * α := by
        rw [hα, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (hcomm a ha c hcA)
      have h1 : ∀ z, α w * z * (α w)⁻¹ = w * z * w⁻¹ := by
        intro z
        have h2 := congrArg (fun φ : MulAut (lBar Y) => φ (α.symm z)) hac
        simp only [MulAut.mul_apply] at h2
        rw [hw, hw, MulEquiv.apply_symm_apply, map_mul, map_mul, map_inv,
          MulEquiv.apply_symm_apply] at h2
        exact h2
      have h3 : w⁻¹ * α w = 1 := eq_one_of_commute_of_mulEquiv hK hq e fun u => by
        calc w⁻¹ * α w * u = w⁻¹ * (α w * u * (α w)⁻¹) * α w := by group
          _ = w⁻¹ * (w * u * w⁻¹) * α w := by rw [h1 u]
          _ = u * (w⁻¹ * α w) := by group
      rw [inv_mul_eq_one] at h3
      exact h3.symm
    have hw3 : w ^ 3 = 1 := by
      apply eq_one_of_commute_of_mulEquiv hK hq e
      intro u
      have hc3' : barHom Y ⟨c, hC.c_norm⟩ ^ 3 = 1 := by
        rw [← map_pow]
        have : (⟨c, hC.c_norm⟩ : Subgroup.normalizer (Y : Set G)) ^ 3 = 1 :=
          Subtype.ext (by simpa using hc3)
        rw [this, map_one]
      have h1 : (barHom Y ⟨c, hC.c_norm⟩ ^ 3) u = w ^ 3 * u * (w ^ 3)⁻¹ := by
        simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, hw]
        group
      rw [hc3', MulAut.one_apply] at h1
      calc w ^ 3 * u = w ^ 3 * u * (w ^ 3)⁻¹ * w ^ 3 := by group
        _ = u * w ^ 3 := by rw [← h1]
    obtain ⟨c₁, hc₁A, hc₁⟩ := exists_lift_mem hAe hAmax hAL hw3 hwA
    have hc₁c : barHom Y ⟨(c₁ : G), hAL hc₁A⟩ = barHom Y ⟨c, hC.c_norm⟩ := by
      ext z
      have h1 : barHom Y ⟨(c₁ : G), hAL hc₁A⟩ =
          barHom Y ⟨(c₁ : G), Subgroup.le_normalizer c₁.2⟩ := rfl
      rw [h1, barHom_of_mem c₁.2, hw z]
      change (c₁ : lBar Y) * z * (c₁ : lBar Y)⁻¹ = w * z * w⁻¹
      rw [hc₁]
    have hK1 : (c₁ : G)⁻¹ * c ∈ thetaQuotCentralizer Y := by
      refine mem_thetaQuotCentralizer_iff.mpr ⟨mul_mem (inv_mem (hAL hc₁A)) hC.c_norm, ?_⟩
      have e1 : (⟨(c₁ : G)⁻¹ * c, mul_mem (inv_mem (hAL hc₁A)) hC.c_norm⟩ :
          Subgroup.normalizer (Y : Set G)) = (⟨(c₁ : G), hAL hc₁A⟩)⁻¹ * ⟨c, hC.c_norm⟩ := rfl
      rw [e1, map_mul, map_inv, hc₁c, inv_mul_cancel]
    have hc₁cb : (c₁ : G)⁻¹ * c ∈ Subgroup.zpowers b :=
      hCA ▸ (⟨A.mul_mem (A.inv_mem hc₁A) hcA, hK1⟩ : _ ∈ A ⊓ thetaQuotCentralizer Y)
    have hc₁B := mem_inf_of_mem hcfg hC hcY hc₁A c₁.2
    apply hcfg.not_mem
    have e1 : c = (c₁ : G) * ((c₁ : G)⁻¹ * c) := by group
    rw [e1]
    exact L.mul_mem hc₁B.2 ((Subgroup.zpowers_le.mpr hC.b_mem.2) hc₁cb)
  have hlift : ∀ (P : GL (Fin 3) K) (hP : P ∈ slPi true 3 (p ^ f) K),
      (∀ s t : Kˣ, s ^ 3 = 1 → t ^ 3 = 1 → ∃ u v w : Kˣ, u ^ 3 = 1 ∧ v ^ 3 = 1 ∧ w ^ 3 = 1 ∧
        u * v * w = 1 ∧ P * diagUnits 1 s t * P⁻¹ * (diagUnits 1 s t)⁻¹ = diagUnits u v w) →
      ∃ y : Y, (y : G) ∈ Subgroup.normalizer (A : Set G) ∧
        (y : lBar Y) = toY (g * P * g⁻¹) (hSL P hP g) := by
    intro P hP hPd
    obtain ⟨w₀, hw₀⟩ := QuotientGroup.mk_surjective (toY (g * P * g⁻¹) (hSL P hP g))
    have hFr : ∀ a ∈ A, (w₀ : G) * a * (w₀ : G)⁻¹ ∈
        A ⊔ (aschbacherSolvableCore 3 Y).map Y.subtype := by
      intro a ha
      obtain ⟨s, t, hs, ht, hst⟩ := hAmat a ha
      obtain ⟨u, v, w, hu, hv, hw, huvw, hP'⟩ := hPd s t hs ht
      set u' : Y := w₀ * Y.normalizerMonoidHom ⟨a, hAL ha⟩ w₀⁻¹ with hu'
      have hucoe : (u' : G) = (w₀ : G) * a * (w₀ : G)⁻¹ * a⁻¹ := by
        rw [hu', Subgroup.coe_mul, normalizerMonoidHom_apply_coe]
        simp only [Subgroup.coe_inv]
        group
      have hMS : g * diagUnits u v w * g⁻¹ ∈ slPi true 3 (p ^ f) K :=
        hSL _ (diagUnits_mem_slPi_true huvw _) g
      have huimg : (u' : lBar Y) = toY _ hMS := by
        apply hεinj
        have h1 : (u' : lBar Y) = toY _ (hSL P hP g) *
            (barHom Y ⟨a, hAL ha⟩ (toY _ (hSL P hP g)))⁻¹ := by
          rw [hu', QuotientGroup.mk_mul, ← barHom_mk, QuotientGroup.mk_inv, hw₀, map_inv]
        obtain ⟨hgx, hst'⟩ := hst
        rw [h1, map_mul, map_inv, hst', hεtoY _ (hSL P hP g), hεtoY _ hMS]
        simp only [← map_inv, ← map_mul]
        congr 1
        calc g * P * g⁻¹ * (g * diagUnits 1 s t * g⁻¹ * (g * P * g⁻¹) *
              (g * diagUnits 1 s t * g⁻¹)⁻¹)⁻¹ =
            g * (P * diagUnits 1 s t * P⁻¹ * (diagUnits 1 s t)⁻¹) * g⁻¹ := by group
          _ = g * diagUnits u v w * g⁻¹ := by rw [hP']
      obtain ⟨z, hzA, hz⟩ := exists_lift_mem hAe hAmax hAL (hcube u v w hMS hu hv hw)
        (hfixA u v w hMS)
      have hzu : ((z⁻¹ * u' : Y) : lBar Y) = 1 := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hz, huimg, inv_mul_cancel]
      have hθ : z⁻¹ * u' ∈ aschbacherSolvableCore 3 Y := (QuotientGroup.eq_one_iff _).mp hzu
      have e1 : (w₀ : G) * a * (w₀ : G)⁻¹ = (z : G) * ((z⁻¹ * u' : Y) : G) * a := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hucoe]
        group
      rw [e1]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hzA)
        (Subgroup.mem_sup_right ⟨_, hθ, rfl⟩)) (Subgroup.mem_sup_left ha)
    obtain ⟨t₀, ⟨t₀', ht₀', rfl⟩, hN⟩ := exists_mem_normalizer_of_conj_mem hA hAL hFr
    refine ⟨t₀' * w₀, hN, ?_⟩
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr ht₀', one_mul, hw₀]
  have hPS : g * cycThree * g⁻¹ ∈ slPi true 3 (p ^ f) K := hSL _ (cycThree_mem_slPi hπ) g
  set Wb : lBar Y := toY _ hPS with hWb
  have hWbD : ∀ j : ℕ, Wb ≠ Dp ^ j := by
    intro j h
    have h1 := congrArg ε h
    rw [map_pow, hWb, hDp, hεtoY _ hPS, hεtoY _ hD'S, ← map_pow, conj_pow, diagUnits_pow] at h1
    have h2 : (g * cycThree * g⁻¹)⁻¹ * (g * diagUnits (1 ^ j) (σ ^ j) ((σ ^ 2) ^ j) * g⁻¹) ∈
        StatedScalars (Fin 3) K := by
      rw [← mk_eq_one_iff_mem_statedScalars, map_mul, map_inv, ← h1, inv_mul_cancel]
    rw [← inv_conj_mem_statedScalars_iff g,
      show g⁻¹ * ((g * cycThree * g⁻¹)⁻¹ * (g * diagUnits (1 ^ j) (σ ^ j) ((σ ^ 2) ^ j) * g⁻¹)) *
        g = cycThree⁻¹ * diagUnits (1 ^ j) (σ ^ j) ((σ ^ 2) ^ j) by group] at h2
    exact cycThree_inv_mul_diagUnits_not_mem _ _ _ h2
  have hWb3 : Wb ^ 3 = 1 := by
    apply hεinj
    rw [map_pow, hWb, hεtoY _ hPS, ← map_pow, conj_pow, cycThree_pow_three, mul_one,
      mul_inv_cancel, map_one, map_one]
  obtain ⟨w, hwN, hw⟩ := hlift cycThree (cycThree_mem_slPi hπ) (fun s t hs ht =>
    ⟨t, s⁻¹, s * t⁻¹, ht, by rw [inv_pow, hs, inv_one],
      by rw [mul_pow, inv_pow, hs, ht, inv_one, one_mul], by group,
      by rw [cycThree_conj_diagUnits, diagUnits_inv, diagUnits_mul, inv_one, mul_one, one_mul]⟩)
  obtain ⟨r, hr, kk, hkk⟩ := exists_pow_three_part w
  set w' : Y := w ^ r with hw'
  have hw'img : (w' : lBar Y) = Wb := by
    rw [hw', QuotientGroup.mk_pow, hw, pow_eq_self_of_pow_three hWb3 hr]
  have hw'3 : w' ^ 3 = 1 := eq_one_of_mk_eq_one (k := kk)
    (by rw [QuotientGroup.mk_pow, hw'img, hWb3])
    (by rw [← pow_mul, mul_comm, pow_mul, hkk, one_pow])
  have hw'3G : (w' : G) ^ 3 = 1 := by
    have := congrArg Subtype.val hw'3
    simpa using this
  have hw'N : (w' : G) ∈ Subgroup.normalizer (A : Set G) := by
    rw [hw', Subgroup.coe_pow]
    exact pow_mem hwN r
  have hAYeq : ∀ u v : G, u ∈ A → v ∈ A → ∀ (hu : u ∈ Y) (hv : v ∈ Y),
      ((⟨u, hu⟩ : Y) : lBar Y) = ((⟨v, hv⟩ : Y) : lBar Y) → u = v := fun u v huA hvA hu hv h =>
    congrArg Subtype.val (eq_of_mk_eq hAe (u := ⟨u, hu⟩) (v := ⟨v, hv⟩) huA hvA h)
  have hw'd : (w' : G) * d * (w' : G)⁻¹ = d := by
    have hmY : (w' : G) * d * (w' : G)⁻¹ ∈ Y := by
      have := (w' * d * w'⁻¹ : Y).2
      simpa using this
    refine hAYeq _ _ ((Subgroup.mem_normalizer_iff.mp hw'N d).mp hdA) hdA hmY d.2 ?_
    have e1 : ((⟨(w' : G) * d * (w' : G)⁻¹, hmY⟩ : Y) : lBar Y) = Wb * Dp * Wb⁻¹ := by
      rw [show (⟨(w' : G) * d * (w' : G)⁻¹, hmY⟩ : Y) = w' * d * w'⁻¹ from rfl,
        QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hw'img, hd]
    rw [e1, show ((⟨(d : G), d.2⟩ : Y) : lBar Y) = Dp from hd]
    apply hεinj
    rw [map_mul, map_mul, map_inv, hWb, hDp, hεtoY _ hPS, hεtoY _ hD'S]
    simp only [← map_inv, ← map_mul]
    rw [show g * cycThree * g⁻¹ * (g * diagUnits 1 σ (σ ^ 2) * g⁻¹) * (g * cycThree * g⁻¹)⁻¹ =
        g * (cycThree * diagUnits 1 σ (σ ^ 2) * cycThree⁻¹) * g⁻¹ by group,
      cycThree_conj_diag_sigma hσ3, conj_frame_scalar, mk_scalar_mul]
  have hw'b : (w' : G) * b * (w' : G)⁻¹ = b := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hYC w'.2), mul_inv_cancel_right]
  have hw'B : ∀ β ∈ A ⊓ L, (w' : G) * β * (w' : G)⁻¹ = β := by
    intro β hβ
    have hle : A ⊓ L ≤ Subgroup.centralizer ({(w' : G)} : Set G) := by
      rw [hBbd]
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        calc b * (w' : G) = (w' : G) * b * (w' : G)⁻¹ * (w' : G) := by rw [hw'b]
          _ = (w' : G) * b := by group
      · rw [Subgroup.mem_centralizer_singleton_iff]
        calc (d : G) * (w' : G) = (w' : G) * d * (w' : G)⁻¹ * (w' : G) := by rw [hw'd]
          _ = (w' : G) * d := by group
    rw [← Subgroup.mem_centralizer_singleton_iff.mp (hle hβ), mul_inv_cancel_right]
  have hNS : g * negSwap * g⁻¹ ∈ slPi true 3 (p ^ f) K := hSL _ (negSwap_mem_slPi _) g
  obtain ⟨t, htN, ht⟩ := hlift negSwap (negSwap_mem_slPi _) (fun s t hs ht =>
    ⟨1, t * s⁻¹, s * t⁻¹, one_pow 3, by rw [mul_pow, inv_pow, hs, ht, inv_one, mul_one],
      by rw [mul_pow, inv_pow, hs, ht, inv_one, one_mul], by group,
      by rw [negSwap_conj_diagUnits, diagUnits_inv, diagUnits_mul, inv_one, mul_one]⟩)
  have htd : (t : G) * d * (t : G)⁻¹ = (d : G)⁻¹ := by
    have hmY : (t : G) * d * (t : G)⁻¹ ∈ Y := by
      have := (t * d * t⁻¹ : Y).2
      simpa using this
    refine hAYeq _ _ ((Subgroup.mem_normalizer_iff.mp htN d).mp hdA) (A.inv_mem hdA) hmY
      (Y.inv_mem d.2) ?_
    rw [show (⟨(t : G) * d * (t : G)⁻¹, hmY⟩ : Y) = t * d * t⁻¹ from rfl,
      show (⟨(d : G)⁻¹, Y.inv_mem d.2⟩ : Y) = d⁻¹ from rfl, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv, ht, hd]
    apply hεinj
    rw [map_mul, map_mul, map_inv, map_inv, hDp, hεtoY (g * negSwap * g⁻¹) hNS, hεtoY _ hD'S]
    simp only [← map_inv, ← map_mul]
    rw [show g * negSwap * g⁻¹ * (g * diagUnits 1 σ (σ ^ 2) * g⁻¹) * (g * negSwap * g⁻¹)⁻¹ =
        g * (negSwap * diagUnits 1 σ (σ ^ 2) * negSwap⁻¹) * g⁻¹ by group,
      negSwap_conj_diag_sigma hσ3]
    congr 1
    group
  have htb : (t : G) * b * (t : G)⁻¹ = b := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hYC t.2), mul_inv_cancel_right]
  have hBW : ∀ x ∈ Subgroup.normalizer (A : Set G), ∀ y ∈ Subgroup.zpowers b ⊔
      Subgroup.zpowers (d : G), x * y * x⁻¹ ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers (d : G) := by
    intro x hx y hy
    rw [← hBbd] at hy ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hcfg.normal hx) y).mp hy
  have hmove : ∀ y : G, y ∈ A ⊓ L → y ≠ 1 → y ^ 3 = 1 →
      ∃ h ∈ Subgroup.normalizer (A : Set G), h * y * h⁻¹ ∉ Subgroup.zpowers y := by
    intro y hyB hy1 hy3
    by_contra hno
    push Not at hno
    have hN : L ⊓ Subgroup.normalizer (A : Set G) ≤
        Subgroup.normalizer ((Subgroup.zpowers y : Subgroup G) : Set G) := by
      intro h hh
      refine Subgroup.mem_normalizer_fintype fun z hz => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
      exact zpow_mem (hno h hh.2) k
    rcases hcfg.irred _ (Subgroup.zpowers_le.mpr hyB) hN with h | h
    · exact hy1 (by simpa using (Subgroup.eq_bot_iff_forall _).mp h y (Subgroup.mem_zpowers y))
    · have h1 := congrArg (fun X : Subgroup G => Nat.card X) h
      simp only [Nat.card_zpowers, orderOf_eq_prime hy3 hy1, h9] at h1
      norm_num at h1
  obtain ⟨h₁, hh₁N, hh₁⟩ := hmove b hC.b_mem hb1 hb3
  obtain ⟨h₂, hh₂N, hh₂⟩ := hmove d hdB hd1 hd3
  obtain ⟨k, hkN, hkb⟩ := Item21Late2Proof.exists_conj_mem_zpowers hbd hb3 hd3 hBW htN htb htd
    hh₁N hh₁ hh₂N hh₂
  have hkb1 : k * b * k⁻¹ ≠ 1 := by
    intro h
    apply hb1
    calc b = k⁻¹ * (k * b * k⁻¹) * k := by group
      _ = 1 := by rw [h]; group
  have hdk : (d : G) ∈ Subgroup.zpowers (k * b * k⁻¹) :=
    Item21Late2Proof.mem_zpowers_of_mem hd3 hkb hkb1 (Subgroup.mem_zpowers _)
  have hdkb : ∀ y ∈ Subgroup.zpowers (d : G), k⁻¹ * y * k ∈ Subgroup.zpowers b := by
    intro y hy
    have hy' := (Subgroup.zpowers_le.mpr hdk) hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy'
    rw [conj_zpow, show k⁻¹ * (k * b ^ j * k⁻¹) * k = b ^ j by group]
    exact zpow_mem (Subgroup.mem_zpowers b) j
  set x : G := k⁻¹ * (w' : G) * k with hx
  have hxN : x ∈ Subgroup.normalizer (A : Set G) :=
    mul_mem (mul_mem (inv_mem hkN) hw'N) hkN
  have hx3 : x ^ 3 = 1 := by
    rw [hx, show k⁻¹ * (w' : G) * k = k⁻¹ * (w' : G) * k⁻¹⁻¹ by group, conj_pow, hw'3G]
    group
  have hxB : ∀ β ∈ A ⊓ L, x * β * x⁻¹ = β := by
    intro β hβ
    have hkβ : k * β * k⁻¹ ∈ A ⊓ L := (Subgroup.mem_normalizer_iff.mp (hcfg.normal hkN) β).mp hβ
    calc x * β * x⁻¹ = k⁻¹ * ((w' : G) * (k * β * k⁻¹) * (w' : G)⁻¹) * k := by rw [hx]; group
      _ = β := by rw [hw'B _ hkβ]; group
  have hxb : x * b * x⁻¹ = b := hxB b hC.b_mem
  set c' : G := k * c * k⁻¹ with hc'
  have hc'A : c' ∈ A := (Subgroup.mem_normalizer_iff.mp hkN c).mp hcA
  have hc'B : c' ∉ A ⊓ L := by
    intro h
    apply hcfg.not_mem
    have := (Subgroup.mem_normalizer_iff.mp (hcfg.normal (inv_mem hkN)) c').mp h
    rw [hc', show k⁻¹ * (k * c * k⁻¹) * k⁻¹⁻¹ = c by group] at this
    exact this.2
  set γ : G := c'⁻¹ * ((w' : G) * c' * (w' : G)⁻¹) with hγ
  have hγA : γ ∈ A := A.mul_mem (A.inv_mem hc'A) ((Subgroup.mem_normalizer_iff.mp hw'N c').mp hc'A)
  have hγY : γ ∈ Y := by
    have h1 : c'⁻¹ * (w' : G) * c' ∈ Y := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hAL hc'A)) (w' : G)).mp w'.2
      simpa using this
    rw [hγ, show c'⁻¹ * ((w' : G) * c' * (w' : G)⁻¹) = c'⁻¹ * (w' : G) * c' * (w' : G)⁻¹ by group]
    exact Y.mul_mem h1 (Y.inv_mem w'.2)
  have hγ1 : γ ≠ 1 := by
    intro h1
    have hwc' : (w' : G) * c' = c' * (w' : G) := by
      have : (w' : G) * c' * (w' : G)⁻¹ = c' := by
        rw [hγ, inv_mul_eq_one] at h1
        exact h1.symm
      calc (w' : G) * c' = (w' : G) * c' * (w' : G)⁻¹ * (w' : G) := by group
        _ = c' * (w' : G) := by rw [this]
    have hAc' : A = Subgroup.zpowers c' ⊔ (A ⊓ L) :=
      Item2130Proof.eq_zpowers_sup hc'A inf_le_left hc'B hcfg.card_eq
    have hw'A : (w' : G) ∈ A := by
      refine mem_of_commute_of_pow_three hAe hAmax hw'3G fun a ha => ?_
      have hle : A ≤ Subgroup.centralizer ({(w' : G)} : Set G) := by
        rw [hAc']
        refine sup_le (Subgroup.zpowers_le.mpr ?_) fun β hβ => ?_
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact hwc'.symm
        · rw [Subgroup.mem_centralizer_singleton_iff]
          calc β * (w' : G) = (w' : G) * β * (w' : G)⁻¹ * (w' : G) := by rw [hw'B β hβ]
            _ = (w' : G) * β := by group
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hle ha)).symm
    obtain ⟨j, -, hj⟩ := Item21LateProof.exists_pow_lt_three_of_mem_zpowers hd3
      (hAYd _ hw'A w'.2)
    apply hWbD j
    rw [← hw'img, ← hd, ← QuotientGroup.mk_pow]
    congr 1
    exact Subtype.ext (by rw [Subgroup.coe_pow]; exact hj)
  set b' : G := k⁻¹ * γ * k with hb'
  have hb'b : b' ∈ Subgroup.zpowers b := hdkb γ (hAYd γ hγA hγY)
  have hb'1 : b' ≠ 1 := by
    intro h
    apply hγ1
    calc γ = k * (k⁻¹ * γ * k) * k⁻¹ := by group
      _ = 1 := by rw [← hb', h]; group
  have hxc : x * c * x⁻¹ = c * b' := by
    calc x * c * x⁻¹ = k⁻¹ * ((w' : G) * c' * (w' : G)⁻¹) * k := by rw [hx, hc']; group
      _ = k⁻¹ * (c' * γ) * k := by rw [hγ]; group
      _ = c * b' := by rw [hc', hb']; group
  have hb'A : b' ∈ A := (Subgroup.zpowers_le.mpr hbA) hb'b
  have hAc : A = Subgroup.zpowers c ⊔ (A ⊓ L) :=
    Item2130Proof.eq_zpowers_sup hcA inf_le_left (fun h => hcfg.not_mem h.2) hcfg.card_eq
  have hxA : ∀ a₀ ∈ A, a₀⁻¹ * (x * a₀ * x⁻¹) ∈ Subgroup.zpowers b := by
    intro a₀ ha₀
    have ha₀' : a₀ ∈ Subgroup.zpowers c ⊔ (A ⊓ L) := hAc ▸ ha₀
    obtain ⟨i, β, hβ, rfl⟩ := Sec10.exists_zpow_mul_of_mem_sup_zpowers (H := A ⊓ L)
      (fun h hh => hcomm h (Subgroup.mem_inf.mp hh).1 c hcA) ha₀'
    have e1 : x * (c ^ i * β) * x⁻¹ = (x * c * x⁻¹) ^ i * (x * β * x⁻¹) := by
      rw [conj_zpow]
      group
    have hcb' : Commute c b' := hcomm c hcA b' hb'A
    have hβb' : Commute β b' := hcomm β hβ.1 b' hb'A
    rw [e1, hxc, hxB β hβ, hcb'.mul_zpow]
    have e2 : (c ^ i * β)⁻¹ * (c ^ i * b' ^ i * β) = β⁻¹ * (b' ^ i * β) := by group
    rw [e2, ← (hβb'.zpow_right i).eq, inv_mul_cancel_left]
    exact zpow_mem (Subgroup.mem_zpowers_iff.mp hb'b |>.choose_spec ▸
      Subgroup.zpow_mem_zpowers b _) i
  have hxbc : x * b = b * x := by
    calc x * b = x * b * x⁻¹ * x := by group
      _ = b * x := by rw [hxb]
  have hxY : x ∈ Subgroup.normalizer (Y : Set G) := by
    have hZ : IsPGroup 3 (Subgroup.zpowers x) := by
      refine IsPGroup.of_card_dvd_pow (n := 1) ?_
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_dvd_of_pow_eq_one hx3
    have hZC : Subgroup.zpowers x ≤ Subgroup.centralizer ({b} : Set G) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      exact hxbc
    exact hC.three_norm _ hZ hZC (Subgroup.mem_zpowers x)
  rcases actsVia_or_field hxY hx3 hK hq2 e with ⟨yx, -, hyx⟩ | ⟨f₀, hf⟩
  swap
  ·
    have hp2 : p = 2 := Item2130Res6Proof.eq_two_of_two_eq_zero hK h2
    subst hp2
    obtain ⟨wc, hwc⟩ := Sec13.exists_conj_eq_of_isTypeC hK hq (modNine_of_eq_three_mul hq hf) e hD
      hycD hyc
    exact hcnot wc hwc
  have hdact : ActsVia Y ε d (g * diagUnits 1 σ (σ ^ 2) * g⁻¹) :=
    actsVia_of_mem d.2 (by
      change ε (d : lBar Y) = _
      rw [hd, hεtoY _ hD'S])
  have hxd : x * d = d * x := by
    calc x * d = x * d * x⁻¹ * x := by group
      _ = d * x := by rw [hxB d hdB]
  have hcomm2 := commMod_of_commute hK hq hge hyx hdact hxd
  have hb'K : b' ∈ thetaQuotCentralizer Y := (Subgroup.zpowers_le.mpr hbK) hb'b
  have hcomm1 : yx * yc * yx⁻¹ * yc⁻¹ ∈ StatedScalars (Fin 3) K := by
    have h1 : ActsVia Y ε (x * c * x⁻¹) (yx * yc * yx⁻¹) := (hyx.mul hycA).mul hyx.inv
    rw [hxc] at h1
    have h2 : ActsVia Y ε (c * b') (yc * 1) := hycA.mul (actsVia_one_of_mem ε hb'K)
    rw [mul_one] at h2
    have h3 := inv_mem (ActsVia.inv_mul_mem hK hq hge h1 h2)
    have h5 := (StatedScalars.normal (Fin 3) K).conj_mem _ h3 yc
    convert h5 using 1
    group
  have hyc' : yc = GeneralLinearGroup.scalar (Fin 3) lc * (g * diagUnits 1 σ σ * g⁻¹) := by
    rw [← conj_frame_scalar, ← hgc]
    group
  have hscal : ∀ (l : Kˣ) (X Z : GL (Fin 3) K), Z * (GeneralLinearGroup.scalar (Fin 3) l * X) *
      Z⁻¹ * (GeneralLinearGroup.scalar (Fin 3) l * X)⁻¹ = Z * X * Z⁻¹ * X⁻¹ := by
    intro l X Z
    have hc1 := scalar_mul_comm l Z
    have hc2 := scalar_mul_comm l (Z * X * Z⁻¹ * X⁻¹)
    calc Z * (GeneralLinearGroup.scalar (Fin 3) l * X) * Z⁻¹ *
          (GeneralLinearGroup.scalar (Fin 3) l * X)⁻¹ =
        (Z * GeneralLinearGroup.scalar (Fin 3) l) * X * Z⁻¹ * X⁻¹ *
          (GeneralLinearGroup.scalar (Fin 3) l)⁻¹ := by group
      _ = GeneralLinearGroup.scalar (Fin 3) l * (Z * X * Z⁻¹ * X⁻¹) *
          (GeneralLinearGroup.scalar (Fin 3) l)⁻¹ := by rw [← hc1]; group
      _ = Z * X * Z⁻¹ * X⁻¹ := by rw [hc2]; group
  have hMc : (g⁻¹ * yx * g) * diagUnits 1 σ σ * (g⁻¹ * yx * g)⁻¹ * (diagUnits 1 σ σ)⁻¹ ∈
      StatedScalars (Fin 3) K := by
    rw [show (g⁻¹ * yx * g) * diagUnits 1 σ σ * (g⁻¹ * yx * g)⁻¹ * (diagUnits 1 σ σ)⁻¹ =
      g⁻¹ * (yx * (g * diagUnits 1 σ σ * g⁻¹) * yx⁻¹ * (g * diagUnits 1 σ σ * g⁻¹)⁻¹) * g by
        group, inv_conj_mem_statedScalars_iff, ← hscal lc, ← hyc']
    exact hcomm1
  have hMD : (g⁻¹ * yx * g) * diagUnits 1 σ (σ ^ 2) * (g⁻¹ * yx * g)⁻¹ *
      (diagUnits 1 σ (σ ^ 2))⁻¹ ∈ StatedScalars (Fin 3) K := by
    rw [show (g⁻¹ * yx * g) * diagUnits 1 σ (σ ^ 2) * (g⁻¹ * yx * g)⁻¹ *
        (diagUnits 1 σ (σ ^ 2))⁻¹ = g⁻¹ * (yx * (g * diagUnits 1 σ (σ ^ 2) * g⁻¹) * yx⁻¹ *
          (g * diagUnits 1 σ (σ ^ 2) * g⁻¹)⁻¹) * g by group, inv_conj_mem_statedScalars_iff]
    exact hcomm2
  have hMdiag := isDiag_of_commMod h2 hσ3 hσ1 hMc hMD
  have hM3 : (g⁻¹ * yx * g) ^ 3 ∈ StatedScalars (Fin 3) K := by
    rw [show g⁻¹ * yx * g = g⁻¹ * yx * g⁻¹⁻¹ by group, conj_pow,
      show g⁻¹ * yx ^ 3 * g⁻¹⁻¹ = g⁻¹ * yx ^ 3 * g by group, inv_conj_mem_statedScalars_iff]
    exact pow_mem_of_actsVia hK hq hge hyx hx3
  obtain ⟨l, s, t', hs, ht', hMeq⟩ := exists_diag_of_cube hMdiag hM3
  obtain ⟨y', hy'D, l', hl'⟩ := hsurj s hs t' ht'
  have hmk : ProjGenLinGroup.mk yx = ProjGenLinGroup.mk y' := by
    have e1 : yx = GeneralLinearGroup.scalar (Fin 3) l * (g * diagUnits 1 s t' * g⁻¹) := by
      rw [← conj_frame_scalar, ← hMeq]
      group
    have e2 : y' = GeneralLinearGroup.scalar (Fin 3) l' * (g * diagUnits 1 s t' * g⁻¹) := by
      rw [← conj_frame_scalar, ← hl']
      group
    rw [e1, e2, mk_scalar_mul, mk_scalar_mul]
  have hyx' : ActsVia Y ε x y' := ActsVia.of_mk_eq hyx hmk
  obtain ⟨τ, hτA, hτ⟩ := hDA y' hy'D
  obtain ⟨a, haN, haA, hτeq⟩ := mem_autThetaQuot_iff.mp hτA
  have hya : ActsVia Y ε a y' := ⟨haN, fun z => by
    have := hτ z
    rw [← hτeq] at this
    exact this⟩
  set k₀ : G := x * a⁻¹ with hk₀
  have hk₀act : ActsVia Y ε k₀ (y' * y'⁻¹) := hyx'.mul hya.inv
  rw [mul_inv_cancel] at hk₀act
  have hk₀K : k₀ ∈ thetaQuotCentralizer Y :=
    hk₀act.mem_thetaQuotCentralizer hM.faithful (Subgroup.one_mem _)
  have hk₀B : ∀ β ∈ A ⊓ L, k₀ * β = β * k₀ := by
    intro β hβ
    have h1 := hxB β hβ
    have h2 : a⁻¹ * β = β * a⁻¹ := hcomm _ (A.inv_mem haA) β hβ.1
    calc k₀ * β = x * (a⁻¹ * β) := by rw [hk₀]; group
      _ = x * (β * a⁻¹) := by rw [h2]
      _ = (x * β * x⁻¹) * x * a⁻¹ := by group
      _ = β * k₀ := by rw [h1, hk₀]; group
  have hk₀3 : k₀ ^ 3 = 1 := by
    set β₀ : G := a * (x * a⁻¹ * x⁻¹) with hβ₀
    have hβ₀A : β₀ ∈ A := A.mul_mem haA ((Subgroup.mem_normalizer_iff.mp hxN _).mp (A.inv_mem haA))
    have hβ₀b : β₀ ∈ Subgroup.zpowers b := by
      have := hxA a⁻¹ (A.inv_mem haA)
      rwa [inv_inv] at this
    have hβ₀B : β₀ ∈ A ⊓ L := (Subgroup.zpowers_le.mpr hC.b_mem) hβ₀b
    have h1 := Item21Res7Proof.mul_pow_three_eq_one (a := a⁻¹) (b := β₀) (ℓ := x) hx3
      (by rw [hβ₀]; group) (hxB β₀ hβ₀B) (hcomm _ (A.inv_mem haA) _ hβ₀A)
      (hAe.2 _ (A.inv_mem haA)) (hAe.2 _ hβ₀A)
    have e1 : k₀ ^ 3 = x * (a⁻¹ * x) ^ 3 * x⁻¹ := by
      rw [hk₀]
      simp only [pow_succ, pow_zero, one_mul]
      group
    rw [e1, h1, mul_one, mul_inv_cancel]
  have hk₀nA : k₀ ∉ A := by
    intro hk
    have h1 : k₀ * c * k₀⁻¹ = c := by rw [hcomm k₀ hk c hcA, mul_inv_cancel_right]
    have h2 : k₀ * c * k₀⁻¹ = c * b' := by
      calc k₀ * c * k₀⁻¹ = x * (a⁻¹ * c * a) * x⁻¹ := by rw [hk₀]; group
        _ = x * c * x⁻¹ := by
            rw [hcomm _ (A.inv_mem haA) c hcA, inv_mul_cancel_right]
        _ = c * b' := hxc
    apply hb'1
    have := h1.symm.trans h2
    calc b' = c⁻¹ * (c * b') := by group
      _ = 1 := by rw [← this]; group
  have hBe : IsElemAbelian 3 (A ⊓ L) :=
    ⟨⟨⟨fun u v => Subtype.ext (hcomm u u.2.1 v v.2.1)⟩⟩, fun u hu => hAe.2 u hu.1⟩
  obtain ⟨hE₀e, hE₀card⟩ := Item2119End3Proof.isElemAbelian_sup_zpowers hBe hk₀3 hk₀B
  have hE₀27 : Nat.card ((A ⊓ L) ⊔ Subgroup.zpowers k₀ : Subgroup G) = 27 := by
    rw [hE₀card (fun h => hk₀nA h.1), h9]
  have hE₀3 : IsPGroup 3 ((A ⊓ L) ⊔ Subgroup.zpowers k₀ : Subgroup G) := fun z =>
    ⟨1, Subtype.ext (by simpa using hE₀e.2 z z.2)⟩
  have hE₀Y : (A ⊓ L) ⊔ Subgroup.zpowers k₀ ≤ Subgroup.normalizer (Y : Set G) :=
    sup_le (fun β hβ => hAL hβ.1)
      (Subgroup.zpowers_le.mpr (thetaQuotCentralizer_le_normalizer Y hk₀K))
  obtain ⟨V, hV1, hV2, hVinv⟩ := exists_two_subgroup_of_frame e g
  have hE₀N : (A ⊓ L) ⊔ Subgroup.zpowers k₀ ≤
      Subgroup.normalizer ((Sec10.thetaPreimage Y V : Subgroup G) : Set G) := by
    refine sup_le (fun β hβ => ?_) (Subgroup.zpowers_le.mpr
      (Sec10.mem_normalizer_thetaPreimage_of_mem_thetaQuotCentralizer hk₀K))
    obtain ⟨s₁, t₁, -, -, hst⟩ := hAmat β hβ.1
    obtain ⟨hgβ, hst'⟩ := hst
    refine Sec10.Step1012ClaimProof.mem_normalizer_thetaPreimage_of_invariant (hAL hβ.1)
      fun v hv => ?_
    exact hVinv _ (diagUnits 1 s₁ t₁)
      (fun i j hij => by rw [coe_diagUnits, Matrix.diagonal_apply_ne _ hij]) hst' v hv
  obtain ⟨T, -, hT1, hT2, hE₀T⟩ := Sec10.exists_pGroup_le_normalizer (p := 3) (q := 2) hE₀3
    (Sec10.not_three_dvd_card_thetaPreimage hV2) (Sec10.two_dvd_card_thetaPreimage hV2 hV1) hE₀N
  have hA27 : Nat.card A = 27 := by rw [hcfg.card_eq, h9]
  have hAE : A ∈ partTwoE G := by
    have hEA : E = A := Subgroup.eq_of_le_of_card_ge hcfg.pair.mem_E.2
      (by rw [hA27, hcfg.pair.mem_E.1.2.1])
    exact hEA ▸ hcfg.pair.mem_E.1
  have hE₀mem : (A ⊓ L) ⊔ Subgroup.zpowers k₀ ∈ partTwoE G :=
    ⟨hE₀e, hE₀27, T, hT1, hT2, hE₀T⟩
  rw [hcfg.pair.side hAE] at hE₀mem
  have hE₀max := hE₀mem.2.1
  have hfixWb : ∀ (z : G) (hz : z ∈ (A ⊓ L) ⊔ Subgroup.zpowers k₀),
      barHom Y ⟨z, hE₀Y hz⟩ Wb = Wb := by
    set S : Subgroup G := ((MulAction.stabilizer (MulAut (lBar Y)) Wb).comap (barHom Y)).map
      (Subgroup.normalizer (Y : Set G)).subtype with hS
    have hmemS : ∀ (z : G) (hz : z ∈ Subgroup.normalizer (Y : Set G)),
        barHom Y ⟨z, hz⟩ Wb = Wb → z ∈ S := fun z hz h =>
      ⟨⟨z, hz⟩, MulAction.mem_stabilizer_iff.mpr h, rfl⟩
    have hSmem : ∀ z ∈ S, ∀ hz : z ∈ Subgroup.normalizer (Y : Set G),
        barHom Y ⟨z, hz⟩ Wb = Wb := by
      rintro z ⟨⟨z', hz'⟩, hmem, rfl⟩ hz
      exact MulAction.mem_stabilizer_iff.mp hmem
    have hle : (A ⊓ L) ⊔ Subgroup.zpowers k₀ ≤ S := by
      rw [hBbd]
      refine sup_le (sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_))
        (Subgroup.zpowers_le.mpr ?_)
      · obtain ⟨hbN, hb1'⟩ := mem_thetaQuotCentralizer_iff.mp hbK
        refine hmemS b hbN ?_
        rw [hb1', MulAut.one_apply]
      · refine hmemS d (Subgroup.le_normalizer d.2) ?_
        rw [barHom_of_mem d.2]
        change (d : lBar Y) * Wb * (d : lBar Y)⁻¹ = Wb
        rw [hd]
        apply hεinj
        rw [map_mul, map_mul, map_inv, hWb, hDp, hεtoY _ hPS, hεtoY _ hD'S]
        simp only [← map_inv, ← map_mul]
        rw [show g * diagUnits 1 σ (σ ^ 2) * g⁻¹ * (g * cycThree * g⁻¹) *
            (g * diagUnits 1 σ (σ ^ 2) * g⁻¹)⁻¹ =
            g * (diagUnits 1 σ (σ ^ 2) * cycThree * (diagUnits 1 σ (σ ^ 2))⁻¹) * g⁻¹ by group,
          diag_sigma_conj_cycThree hσ3, conj_frame_scalar, mk_scalar_mul]
      · obtain ⟨hkN', hk1'⟩ := mem_thetaQuotCentralizer_iff.mp hk₀K
        refine hmemS k₀ hkN' ?_
        rw [hk1', MulAut.one_apply]
    exact fun z hz => hSmem z (hle hz) (hE₀Y hz)
  obtain ⟨w₂, hw₂, hw₂E⟩ := exists_lift_fixed hE₀3 hE₀Y Wb hfixWb
  obtain ⟨r₂, hr₂, k₂, hk₂⟩ := exists_pow_three_part w₂
  set w₃ : Y := w₂ ^ r₂ with hw₃
  have hw₃img : (w₃ : lBar Y) = Wb := by
    rw [hw₃, QuotientGroup.mk_pow, hw₂, pow_eq_self_of_pow_three hWb3 hr₂]
  have hw₃3 : w₃ ^ 3 = 1 := eq_one_of_mk_eq_one (k := k₂)
    (by rw [QuotientGroup.mk_pow, hw₃img, hWb3])
    (by rw [← pow_mul, mul_comm, pow_mul, hk₂, one_pow])
  have hw₃3G : (w₃ : G) ^ 3 = 1 := by
    have := congrArg Subtype.val hw₃3
    simpa using this
  have hw₃E : ∀ z ∈ (A ⊓ L) ⊔ Subgroup.zpowers k₀, (w₃ : G) * z = z * (w₃ : G) := by
    intro z hz
    have h1 : z * (w₂ : G) * z⁻¹ = w₂ := hw₂E z hz
    have hc : Commute (w₂ : G) z := by
      calc (w₂ : G) * z = z * (w₂ : G) * z⁻¹ * z := by rw [h1]
        _ = z * (w₂ : G) := by group
    rw [hw₃, Subgroup.coe_pow]
    exact (hc.pow_left r₂).eq
  obtain ⟨hF, -⟩ := Item2119End3Proof.isElemAbelian_sup_zpowers hE₀e hw₃3G hw₃E
  have hEq := hE₀max _ hF le_sup_left
  have hw₃mem : (w₃ : G) ∈ Subgroup.zpowers k₀ ⊔ (A ⊓ L) := by
    rw [sup_comm, ← hEq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  obtain ⟨i, β, hβ, hw₃eq⟩ := Sec10.exists_zpow_mul_of_mem_sup_zpowers (H := A ⊓ L)
    (fun h hh => (hk₀B h hh).symm) hw₃mem
  rw [hBbd] at hβ
  obtain ⟨i₁, -, j₁, -, hβeq⟩ := Item21Late2Proof.exists_pow_mul_pow_of_mem_sup hbd hb3 hd3 hβ
  have h1 : ActsVia Y ε (w₃ : G) (1 * (1 * (g * diagUnits 1 σ (σ ^ 2) * g⁻¹) ^ j₁)) := by
    rw [hw₃eq, hβeq]
    exact (actsVia_one_of_mem ε (zpow_mem hk₀K i)).mul
      ((actsVia_one_of_mem ε (pow_mem hbK i₁)).mul (hdact.pow j₁))
  have h2 : ActsVia Y ε (w₃ : G) (g * cycThree * g⁻¹) :=
    actsVia_of_mem w₃.2 (by
      change ε (w₃ : lBar Y) = _
      rw [hw₃img, hWb, hεtoY _ hPS])
  have h3 := ActsVia.inv_mul_mem hK hq hge h2 h1
  rw [one_mul, one_mul, conj_pow, diagUnits_pow,
    show (g * cycThree * g⁻¹)⁻¹ * (g * diagUnits (1 ^ j₁) (σ ^ j₁) ((σ ^ 2) ^ j₁) * g⁻¹) =
      g⁻¹⁻¹ * (cycThree⁻¹ * diagUnits (1 ^ j₁) (σ ^ j₁) ((σ ^ 2) ^ j₁)) * g⁻¹ by group,
    inv_conj_mem_statedScalars_iff] at h3
  exact cycThree_inv_mul_diagUnits_not_mem _ _ _ h3

end Certs

end Item2130Res7Proof

end CFSG.RankThree.PartTwo.Sec21

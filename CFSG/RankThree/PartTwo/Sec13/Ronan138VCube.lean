module

public import CFSG.RankThree.PartTwo.Sec13.Ronan138P5Res
public import CFSG.RankThree.PartTwo.Sec13.Ronan138SSN
import CFSG.RankThree.PartTwo.Sec13.Ronan138VCubeMat
import CFSG.RankThree.PartTwo.Sec13.Ronan138S131
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Ronan138SKSetup
import CFSG.RankThree.PartTwo.KFacts.KS18M12Proof
import CFSG.Quasithin.Background.SmithB45MatM12Cls
import CFSG.RankThree.PartTwo.Sec11.Item116H3Rank
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item137NormLe
import CFSG.RankThree.PartTwo.Sec13.Item137Delta
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
public import CFSG.Sporadic.Schreier.M12
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix (ProjGenLinGroup)

@[expose] def Step138KInndiag : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E : Subgroup G),
    Hyp138 A c L E → Sec8.IsZ3PGLThreePi (lBarA c L E) → ∀ F : Subgroup G, IsF138N L E F →
    (∀ F' : Subgroup G, CFSG.Assembly.IsElemAbelian 3 F' → F ≤ F' → F' = F) →
    ∀ (e : G) (K : Subgroup G), Subgroup.zpowers e ∈ omegaA E → K ∈ lA E e → e ∈ F →
      e ∉ Subgroup.zpowers c → e ∉ L → Sec8.IsZ3PGLThreePi (lBarA e K E) →
    ∀ P : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf 3 P (Subgroup.normalizer (Subgroup.zpowers c : Set G)) →
      E ⊔ F ≤ P → P ≤ Subgroup.normalizer (L : Set G) →
      (∀ v ∈ P ⊓ Sec4.thetaQuotCentralizer L, v ^ 3 = 1 → v ∈ Subgroup.zpowers c) →
    ∀ (π : Bool) (p f : ℕ) (Fld : Type) [Field Fld], Sec4.PiField π p f Fld →
      Sec4.ModThree π (p ^ f) →
    ∀ ψ : K ⧸ aschbacherSolvableCore 3 K ≃* projImage (Sec4.slPi π 3 (p ^ f) Fld),
    ∀ (w : G) (hw : w ∈ Subgroup.normalizer (K : Set G)), w ∈ P ⊓ Sec4.thetaQuotCentralizer L →
      (∀ f ∈ F, f * w = w * f) → w ^ 3 = c →
      ∃ y ∈ Sec4.glPi π 3 (p ^ f) Fld, ∀ z : K ⧸ aschbacherSolvableCore 3 K,
        ((ψ (Sec4.thetaQuotMulAut K (K.normalizerMonoidHom ⟨w, hw⟩) z) :
            projImage (Sec4.slPi π 3 (p ^ f) Fld)) : ProjGenLinGroup (Fin 3) Fld) =
          ProjGenLinGroup.mk y * (ψ z : ProjGenLinGroup (Fin 3) Fld) * (ProjGenLinGroup.mk y)⁻¹

end CFSG.RankThree.PartTwo.Sec13

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138V

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open Matrix (ProjGenLinGroup GeneralLinearGroup)

variable {G : Type} [Group G] [Finite G]

theorem normalizer_zpowers_le_normalizer_of_not_mem (h131 : Item131) (hspor : SporadicModels131)
    {A L : Subgroup G} {c : G} (h : Sec13Data G A c L) (hcL : c ∉ L) :
    Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have hc3 : c ^ 3 = 1 := h.isElemAbelian.2 c h.mem_A
  have h3L := three_dvd_card_of_sec13Data h131 hspor h
  have huniq := moreover_of_not_mem h131 hspor slTwoCenter h hcL
  intro x hx
  have hxc : x * c * x⁻¹ ∈ Subgroup.zpowers c :=
    (Subgroup.mem_normalizer_iff.mp hx c).mp (Subgroup.mem_zpowers c)
  have hL' := Sec11.map_conj_mem_thetaComponentsAt hc3 h.mem_thetaComponentsAt hxc
  have h3L' : 3 ∣ Nat.card (L.map (MulAut.conj x).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
    exact h3L
  exact map_conj_eq_iff_mem_normalizer.mp (huniq _ hL' h3L')

theorem pow_three_eq_one_of_m12
    {X : Type} [Group X] [Finite X]
    (φ : X ≃* CFSG.Blueprint.NativeSporadic.M12) {σ : MulAut X} {k : ℕ} (hσ : σ ^ 3 ^ k = 1) :
    σ ^ 3 = 1 := by
  obtain ⟨-, hZ, hinn, -⟩ := KFacts.ks18M12 X ⟨φ⟩
  obtain ⟨x, rfl⟩ := hinn σ ⟨k, hσ⟩
  have hxk : x ^ 3 ^ k = 1 := by
    have h1 : MulAut.conj (x ^ 3 ^ k) = 1 := by rw [map_pow, hσ]
    have h2 : x ^ 3 ^ k ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun α : MulAut X => α g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc g * x ^ 3 ^ k = x ^ 3 ^ k * g * (x ^ 3 ^ k)⁻¹ * x ^ 3 ^ k := by rw [this]
        _ = x ^ 3 ^ k * g := by group
    rw [hZ, Subgroup.mem_bot] at h2
    exact h2
  obtain ⟨j, hj, hjo⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hxk)
  have hj1 : j ≤ 1 := by
    by_contra hj2
    have hdvd : 3 ^ (j - 2) ∣ orderOf x := by
      rw [hjo]
      exact pow_dvd_pow 3 (by omega)
    have ho : orderOf (x ^ 3 ^ (j - 2)) = 9 := by
      rw [orderOf_pow_of_dvd (by positivity) hdvd, hjo, Nat.pow_div (by omega) (by norm_num),
        show j - (j - 2) = 2 by omega]
    apply CFSG.Quasithin.B45Mat.M12.orderOf_ne_of_mem
      (g := ((φ (x ^ 3 ^ (j - 2)) : ↥CFSG.Blueprint.NativeSporadic.M12) : Equiv.Perm (Fin 12)))
      (m := 9) ?_ (by simp)
    · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ho]
    · rw [CFSG.Sporadic.Schreier.m12Certificate_originalSubgroup]
      exact (φ (x ^ 3 ^ (j - 2))).2
  have hx3 : x ^ 3 = 1 := by
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [hjo]
    interval_cases j <;> norm_num
  rw [← map_pow, hx3, map_one]

theorem eq_one_of_mem_of_pow_three {T C : Subgroup G} {c : G} (hT3 : IsPGroup 3 T)
    (hTc : ∀ v ∈ T, v ^ 3 = 1 → v ∈ Subgroup.zpowers c) (hc3 : c ^ 3 = 1) (hcC : c ∉ C)
    {t : G} (htT : t ∈ T) (htC : t ∈ C) : t = 1 := by
  by_contra ht1
  have hc1 : c ≠ 1 := fun h => hcC (h ▸ C.one_mem)
  obtain ⟨k, hk⟩ := hT3 ⟨t, htT⟩
  have hk' : t ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨j, -, hjo⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hk')
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact ht1 (orderOf_eq_one_iff.mp (by simpa using hjo))
  have hdvd : 3 ^ (j - 1) ∣ orderOf t := by
    rw [hjo]
    exact pow_dvd_pow 3 (by omega)
  set t' := t ^ 3 ^ (j - 1) with ht'
  have ht'o : orderOf t' = 3 := by
    rw [ht', orderOf_pow_of_dvd (by positivity) hdvd, hjo, Nat.pow_div (by omega) (by norm_num),
      show j - (j - 1) = 1 by omega, pow_one]
  have ht'3 : t' ^ 3 = 1 := by
    rw [← ht'o]
    exact pow_orderOf_eq_one t'
  have ht'1 : t' ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht'o
    norm_num at ht'o
  have ht'c := hTc t' (pow_mem htT _) ht'3
  have heq := Ronan138S.zpowers_eq_of_mem ht'3 ht'1 hc3 hc1 ht'c
  apply hcC
  have hcm : c ∈ Subgroup.zpowers t' := heq ▸ Subgroup.mem_zpowers c
  exact Subgroup.zpowers_le.mpr (pow_mem htC _) hcm

theorem false_of_actsPGL {K T : Subgroup G} {c x₀ w : G} {π : Bool} {p f : ℕ} {Fld : Type}
    [Field Fld] (hPi : Sec4.PiField π p f Fld) (hq : Sec4.ModThree π (p ^ f))
    {ψ : K ⧸ aschbacherSolvableCore 3 K ≃* projImage (Sec4.slPi π 3 (p ^ f) Fld)}
    [Group.IsPerfect (projImage (Sec4.slPi π 3 (p ^ f) Fld))] {y₀ M : GL (Fin 3) Fld}
    (hx₀ : Ronan138S.ActsPGL ψ x₀ y₀) (hy₀3 : Sec4.Type123 π (p ^ f) Fld y₀ 3)
    (hwM : Ronan138S.ActsPGL ψ w M) (hwc : w ^ 3 = c) (hc3 : c ^ 3 = 1)
    (hcK : c ∉ Sec4.thetaQuotCentralizer K) (hx₀c : x₀ * c = c * x₀)
    (huT : x₀ * w * x₀⁻¹ * w⁻¹ ∈ T)
    (hTK : ∀ t ∈ T, t ∈ Sec4.thetaQuotCentralizer K → t = 1)
    (hTc : ∀ v ∈ T, v ^ 3 = 1 → v ∈ Subgroup.zpowers c) : False := by
  have hπ : π = false → UnitaryFieldData p f Fld := fun h => by subst h; exact hPi.unitary
  have hcM : Ronan138S.ActsPGL ψ c (M ^ 3) := by
    rw [← hwc]
    exact hwM.pow hπ 3
  have hMZ : M ^ 3 ∉ StatedScalars (Fin 3) Fld := fun hS =>
    hcK (hcM.mem_thetaQuotCentralizer (Sec4.mk_eq_one_iff_mem_statedScalars.mpr hS))
  have hM9 : (M ^ 3) ^ 3 ∈ StatedScalars (Fin 3) Fld := by
    have h1 := hcM.pow hπ 3
    rw [hc3] at h1
    have h2 := Ronan138S.ActsPGL.mk_eq hPi hq h1 (Ronan138S.actsPGL_one hπ)
    rw [map_one] at h2
    exact Sec4.mk_eq_one_iff_mem_statedScalars.mp h2
  have hcomm : y₀ * M ^ 3 * y₀⁻¹ * (M ^ 3)⁻¹ ∈ StatedScalars (Fin 3) Fld := by
    have h1 := Ronan138S.ActsPGL.commute hPi hq hx₀ hcM hx₀c
    rw [← Sec4.mk_eq_one_iff_mem_statedScalars, map_mul, map_mul, map_mul, map_inv, map_inv, h1]
    group
  have hU : (y₀ * M * y₀⁻¹ * M⁻¹) ^ 3 ∈ StatedScalars (Fin 3) Fld →
      ∃ n : ℕ, y₀ * M * y₀⁻¹ * M⁻¹ * ((M ^ 3) ^ n)⁻¹ ∈ StatedScalars (Fin 3) Fld := by
    intro hU3
    have huU : Ronan138S.ActsPGL ψ (x₀ * w * x₀⁻¹ * w⁻¹) (y₀ * M * y₀⁻¹ * M⁻¹) :=
      ((hx₀.mul hwM).mul hx₀.inv).mul hwM.inv
    have hu3K : (x₀ * w * x₀⁻¹ * w⁻¹) ^ 3 ∈ Sec4.thetaQuotCentralizer K :=
      (huU.pow hπ 3).mem_thetaQuotCentralizer (Sec4.mk_eq_one_iff_mem_statedScalars.mpr hU3)
    have hu3 : (x₀ * w * x₀⁻¹ * w⁻¹) ^ 3 = 1 := hTK _ (pow_mem huT 3) hu3K
    obtain ⟨n, hn⟩ := Ronan138S.exists_pow_eq_of_mem_zpowers (hTc _ huT hu3)
    refine ⟨n, ?_⟩
    have hcn : Ronan138S.ActsPGL ψ (x₀ * w * x₀⁻¹ * w⁻¹) ((M ^ 3) ^ n) := by
      rw [← hn]
      exact hcM.pow hπ n
    have h1 := Ronan138S.ActsPGL.mk_eq hPi hq huU hcn
    rw [← Sec4.mk_eq_one_iff_mem_statedScalars, map_mul, map_inv, h1, mul_inv_cancel]
  exact false_of_cube_root_of_type3 hPi hq hwM.2.1 hMZ hM9 hy₀3 hcomm hU

section Main

theorem step138NoCubeRootC_of_inndiag (h131 : Item131) (hKStr : Step138KStr)
    (hinn : Step138KInndiag) : Step138NoCubeRootC := by
  intro G _ _ A c L E hH hPGL F hF hFmax P hP hEFP hPN horder3 w hw hwF hwc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e, K, heΩ, hK, heF, hec, heL, hKcase⟩ := hKStr G A c L E hH hPGL F hF
  have hH' := hH
  obtain ⟨h, -, hcE, hE3, -, hEN, -, -, -⟩ := hH'
  have hc3 : c ^ 3 = 1 := hE3.2 c hcE
  have hP3 := CFSG.ABGLocalTools.IsSylowOf.isPGroup hP
  have hEP : E ≤ P := le_sup_left.trans hEFP
  have heE : e ∈ E := (zpowers_mem_omegaA_iff.mp heΩ).1
  have he3 : e ^ 3 = 1 := hE3.2 e heE
  have he1 : e ≠ 1 := by
    rintro rfl
    exact hec (Subgroup.one_mem _)
  have hc1 : c ≠ 1 := h.ne_one
  have hcK : c ∉ Sec4.thetaQuotCentralizer K := by
    intro hcK
    have hCE := sectionCentralizer_eq_inf hK.2.1
    rw [hK.2.2.1] at hCE
    have hce : c ∈ Subgroup.zpowers e := by
      have : c ∈ ((E ⊓ Sec4.thetaQuotCentralizer K : Subgroup G) : Set G) :=
        Subgroup.mem_inf.mpr ⟨hcE, hcK⟩
      rw [← hCE] at this
      exact this
    apply hec
    rw [Ronan138S.zpowers_eq_of_mem hc3 hc1 he3 he1 hce]
    exact Subgroup.mem_zpowers e
  have hT3 : IsPGroup 3 ↥(P ⊓ Sec4.thetaQuotCentralizer L) := hP3.to_le inf_le_left
  have hTK : ∀ t ∈ P ⊓ Sec4.thetaQuotCentralizer L, t ∈ Sec4.thetaQuotCentralizer K → t = 1 :=
    fun t htT htK => eq_one_of_mem_of_pow_three hT3 horder3 hc3 hcK htT htK
  have hXF := Ronan138S.mem_partTwoF_of_hyp138 hH
  have hD : Sec13Data G E e K :=
    { h.toPartTwoStanding with
      partTwoS_eq := h.partTwoS_eq
      mem_partTwoF := hXF.1
      not_mem_partTwoT := hXF.2
      zpowers_mem_omegaA := heΩ
      mem_lA := hK }
  have heK : e ∉ K := by
    rcases hKcase with hPGLK | hM
    · exact (Ronan138S.facts131_of_isZ3PGLThreePi h131 sporadicModels131 hD hPGLK).1
    · obtain ⟨φ⟩ := hM
      obtain ⟨-, ⟨hM12p, -⟩, -⟩ := sporadicModels131
      exact (facts_of_m12 h131 sporadicModels131 hD (nonempty_thetaQuot_equiv hD hM12p φ)).1
  have hwNe : w ∈ Subgroup.normalizer (Subgroup.zpowers e : Set G) := by
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (Commute.zpow_left (show Commute e w from hwF e heF) k).eq
  have hwN : w ∈ Subgroup.normalizer (K : Set G) :=
    normalizer_zpowers_le_normalizer_of_not_mem h131 sporadicModels131 hD heK hwNe
  rcases hKcase with hPGLK | hM
  ·
    obtain ⟨-, -, x₀, hx₀E, hx₀type⟩ := Ronan138S.facts131_of_isZ3PGLThreePi h131
      sporadicModels131 hD hPGLK
    obtain ⟨hx₀N, π, p, f, Fld, _, hPi, hq, ψ, y₀, hy₀, hy₀3, hx₀act⟩ := hx₀type
    have hx₀ψ : Ronan138S.ActsPGL ψ x₀ y₀ := ⟨hx₀N, hy₀, hx₀act⟩
    have hKq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hK.1
    haveI : Group.IsPerfect (K ⧸ aschbacherSolvableCore 3 K) := hKq.1
    haveI : Group.IsPerfect (projImage (Sec4.slPi π 3 (p ^ f) Fld)) :=
      Group.IsPerfect.ofSurjective (f := ψ.toMonoidHom) ψ.surjective
    obtain ⟨M, hM, hwact⟩ := hinn G A c L E hH hPGL F hF hFmax e K heΩ hK heF hec heL hPGLK P hP
      hEFP hPN horder3 π p f Fld hPi hq ψ w hwN hw hwF hwc
    have hwM : Ronan138S.ActsPGL ψ w M := ⟨hwN, hM, hwact⟩
    have hx₀c : x₀ * c = c * x₀ :=
      congrArg Subtype.val (hE3.1.is_comm.comm ⟨x₀, hx₀E⟩ ⟨c, hcE⟩)
    have huT : x₀ * w * x₀⁻¹ * w⁻¹ ∈ P ⊓ Sec4.thetaQuotCentralizer L := by
      refine Subgroup.mul_mem _ ⟨?_, ?_⟩ (Subgroup.inv_mem _ hw)
      · exact P.mul_mem (P.mul_mem (hEP hx₀E) hw.1) (P.inv_mem (hEP hx₀E))
      · exact Sec6.conj_mem_thetaQuotCentralizer hw.2 (hEN hx₀E)
    exact false_of_actsPGL hPi hq hx₀ψ hy₀3 hwM hwc hc3 hcK hx₀c huT hTK horder3
  ·
    set ν := (Sec4.thetaQuotMulAut K).comp K.normalizerMonoidHom with hν
    obtain ⟨k, hk⟩ := hP3 ⟨w, hw.1⟩
    have hwk : w ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hσk : ν ⟨w, hwN⟩ ^ 3 ^ k = 1 := by
      rw [← map_pow]
      have : (⟨w, hwN⟩ : Subgroup.normalizer (K : Set G)) ^ 3 ^ k = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow, hwk, Subgroup.coe_one])
      rw [this, map_one]
    obtain ⟨φ⟩ := hM
    obtain ⟨-, ⟨hM12p, -⟩, -⟩ := sporadicModels131
    obtain ⟨φK⟩ := nonempty_thetaQuot_equiv hD hM12p φ
    have hσ3 : ν ⟨w, hwN⟩ ^ 3 = 1 := pow_three_eq_one_of_m12 φK hσk
    apply hcK
    have hcN : c ∈ Subgroup.normalizer (K : Set G) := hK.2.1 hcE
    refine Subgroup.mem_map.mpr ⟨⟨c, hcN⟩, ?_, rfl⟩
    have : (⟨c, hcN⟩ : Subgroup.normalizer (K : Set G)) = ⟨w, hwN⟩ ^ 3 :=
      Subtype.ext (by rw [Subgroup.coe_pow, hwc])
    rw [MonoidHom.mem_ker, this, map_pow]
    exact hσ3

end Main

end CFSG.RankThree.PartTwo.Sec13.Ronan138V

module

public import CFSG.RankThree.PartTwo.Sec13.Ronan138SBase
public import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes
import CFSG.RankThree.PartTwo.Sec13.Ronan138SKTwoType
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarSetup
import CFSG.RankThree.PartTwo.Sec4.LThreePiRank
import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseI
import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseA
import CFSG.RankThree.PartTwo.Sec4.LThreePiEigen
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
import CFSG.RankThree.PartTwo.Sec4.Item423Res4ProofHeis
import CFSG.RankThree.PartTwo.Sec13.Item138ProofExists
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec4.Item424ProofInner
import CFSG.RankThree.PartTwo.KFacts.K71Lift
import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeSylow
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitSylow
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.RankThree.PartTwo.Sec13.Ronan138SEnd
public import CFSG.RankThree.PartTwo.Sec13.Ronan138SKIn
public import CFSG.RankThree.PartTwo.Sec4.Statements417
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.Sporadic.Th.F2Spec
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials
import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance
import CFSG.RankThree.PartTwo.Sec11.Item118
import CFSG.RankThree.PartTwo.Sec11.Theorem1134
import CFSG.RankThree.PartTwo.Sec21.Item211ProofListOf
import CFSG.RankThree.PartTwo.Sec6.Item612

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138T

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 (PiField ModThree slPi glPi zPi Type123 IsTypeC)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open Matrix (ProjGenLinGroup GeneralLinearGroup)
open scoped commutatorElement

local notation "pmk" => Matrix.ProjGenLinGroup.mk

theorem sup_zpowers_comm_exp {F : Type} [Field F] {s y : GL (Fin 3) F}
    (hsy : ((s * y : GL (Fin 3) F) : GL (Fin 3) F ⧸ StatedScalars (Fin 3) F) = y * s)
    (hs3 : s ^ 3 ∈ StatedScalars (Fin 3) F) (hy3 : y ^ 3 ∈ StatedScalars (Fin 3) F) :
    (∀ a ∈ Subgroup.zpowers (s : GL (Fin 3) F ⧸ StatedScalars (Fin 3) F) ⊔
        Subgroup.zpowers (y : GL (Fin 3) F ⧸ StatedScalars (Fin 3) F),
      ∀ b ∈ Subgroup.zpowers (s : GL (Fin 3) F ⧸ StatedScalars (Fin 3) F) ⊔
        Subgroup.zpowers (y : GL (Fin 3) F ⧸ StatedScalars (Fin 3) F), a * b = b * a) ∧
      ∀ a ∈ Subgroup.zpowers (s : GL (Fin 3) F ⧸ StatedScalars (Fin 3) F) ⊔
        Subgroup.zpowers (y : GL (Fin 3) F ⧸ StatedScalars (Fin 3) F), a ^ 3 = 1 := by
  set S : GL (Fin 3) F ⧸ StatedScalars (Fin 3) F := (s : GL (Fin 3) F ⧸ StatedScalars (Fin 3) F)
  set Y : GL (Fin 3) F ⧸ StatedScalars (Fin 3) F := (y : GL (Fin 3) F ⧸ StatedScalars (Fin 3) F)
  have hSY : S * Y = Y * S := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact hsy
  have hS3 : S ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).mpr hs3
  have hY3 : Y ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).mpr hy3
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
  · obtain ⟨i, j, rfl⟩ := Sec4.exists_zpow_mul_of_mem_sup hSY ha
    obtain ⟨k, l, rfl⟩ := Sec4.exists_zpow_mul_of_mem_sup hSY hb
    have c1 : Commute S Y := hSY
    have h1 := (c1.zpow_zpow i l)
    have h2 := (c1.zpow_zpow k j)
    calc S ^ i * Y ^ j * (S ^ k * Y ^ l) = S ^ i * S ^ k * (Y ^ j * Y ^ l) := by
          rw [mul_assoc, ← mul_assoc (Y ^ j), ← h2.eq, mul_assoc, mul_assoc]
      _ = S ^ k * S ^ i * (Y ^ l * Y ^ j) := by
          rw [← zpow_add, ← zpow_add, ← zpow_add, ← zpow_add, add_comm i k, add_comm j l]
      _ = S ^ k * Y ^ l * (S ^ i * Y ^ j) := by
          rw [mul_assoc, ← mul_assoc (S ^ i), h1.eq, mul_assoc, mul_assoc]
  · obtain ⟨i, j, rfl⟩ := Sec4.exists_zpow_mul_of_mem_sup hSY ha
    have c1 : Commute (S ^ i) (Y ^ j) := (Commute.zpow_zpow hSY i j)
    rw [c1.mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm i,
      mul_comm j, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hS3, hY3, one_zpow, one_zpow,
      one_mul]

section Model

variable {K : Type} [Field K] {π : Bool} {p f : ℕ}

theorem trace_eq_zero_of_type1 (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {x : GL (Fin 3) K} (h1 : Type123 π (p ^ f) K x 1) :
    (x : Matrix (Fin 3) (Fin 3) K).trace = 0 := by
  obtain ⟨τ, hτ, hτ1, z, hz, g, -, hD⟩ := h1
  obtain ⟨τ₀, hτ₀, hτ₀1⟩ := Sec4.exists_tau hK hq
  obtain ⟨c, rfl⟩ := Sec4.mem_statedScalars_of_mem_zPi hK hq hτ₀ hτ₀1 hz
  have h := Sec4.trace_inv_conj g (x * GeneralLinearGroup.scalar (Fin 3) c)
  rw [hD, Sec4.trace_diagTau, Sec4.trace_mul_scalar] at h
  have h0 : τ + τ ^ 2 + 1 = 0 := by
    have := Sec4.one_add_tau_add_sq hτ hτ1
    linear_combination this
  rw [h0] at h
  exact (mul_eq_zero.mp h.symm).resolve_left c.ne_zero

theorem mkQ_eq_iff {u v : GL (Fin 3) K} :
    ((u : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) = (v : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K))
      ↔ pmk u = pmk v := by
  rw [QuotientGroup.eq, ← Sec4.mk_eq_one_iff_mem_statedScalars, map_mul, map_inv,
    inv_mul_eq_one]

theorem type1_of_fused (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {s₁ s₂ : GL (Fin 3) K} (hs₁ : s₁ ∈ slPi π 3 (p ^ f) K) (hs₂ : s₂ ∈ slPi π 3 (p ^ f) K)
    (hs₁3 : s₁ ^ 3 ∈ StatedScalars (Fin 3) K) (hs₂3 : s₂ ^ 3 ∈ StatedScalars (Fin 3) K)
    (hcomm : ((s₁ * s₂ : GL (Fin 3) K) : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) =
      (s₂ : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) * s₁)
    (hs₁1 : s₁ ∉ StatedScalars (Fin 3) K)
    (hind : (s₂ : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∉
      Subgroup.zpowers (s₁ : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K))
    (hfus : ∀ w ∈ Subgroup.zpowers (s₁ : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ⊔
        Subgroup.zpowers (s₂ : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K), w ≠ 1 →
      ∃ g ∈ slPi π 3 (p ^ f) K, w = ((g * s₁ * g⁻¹ : GL (Fin 3) K) :
        GL (Fin 3) K ⧸ StatedScalars (Fin 3) K)) :
    Type123 π (p ^ f) K s₁ 1 := by
  classical
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have := hK.finite
  obtain ⟨τ, hτ, hτ1⟩ := Sec4.exists_tau hK hq
  have hzPi := Sec4.zPi_eq hπ hq' hτ hτ1
  have hs₁H : s₁ ∈ glPi π 3 (p ^ f) K := Sec4.slPi_le_glPi hπ hs₁
  have hs₁Z : s₁ ∉ zPi π 3 (p ^ f) K := by
    rw [hzPi]
    exact fun h => hs₁1 (Subgroup.mem_inf.mp h).2
  have hs₁3' : s₁ ^ 3 ∈ zPi π 3 (p ^ f) K := by
    rw [hzPi]
    exact Subgroup.mem_inf.mpr ⟨pow_mem hs₁H 3, hs₁3⟩
  rcases Sec4.type123_exhaust hK hq hs₁H hs₁Z hs₁3' with h1 | h2 | h3
  · exact h1
  · exfalso
    set Q := GL (Fin 3) K ⧸ StatedScalars (Fin 3) K
    set E : Subgroup Q := Subgroup.zpowers (s₁ : Q) ⊔ Subgroup.zpowers (s₂ : Q) with hE
    obtain ⟨hEc, hE3⟩ := sup_zpowers_comm_exp hcomm hs₁3 hs₂3
    have hS3 : (s₁ : Q) ^ 3 = 1 := by
      rw [← QuotientGroup.mk_pow]
      exact (QuotientGroup.eq_one_iff _).mpr hs₁3
    have hS1 : (s₁ : Q) ≠ 1 := fun h => hs₁1 ((QuotientGroup.eq_one_iff _).mp h)
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hE9 : Nat.card E = 9 := by
      have hY3 : (s₂ : Q) ^ 3 = 1 := by
        rw [← QuotientGroup.mk_pow]
        exact (QuotientGroup.eq_one_iff _).mpr hs₂3
      have hSY : (s₂ : Q) * (s₁ : Q) = (s₁ : Q) * (s₂ : Q) := by
        rw [← hcomm, QuotientGroup.mk_mul]
      exact Sec4.card_zpowers_sup_zpowers hY3 (orderOf_eq_prime hS3 hS1) hind hSY
    have htr2 := Sec4.trace_ne_zero_of_type2 hK hq h2
    have htrE : ∀ w : GL (Fin 3) K, (w : Q) ∈ E → (w : Q) ≠ 1 →
        (w : Matrix (Fin 3) (Fin 3) K).trace ≠ 0 := by
      intro w hwE hw1
      obtain ⟨g, -, hgw⟩ := hfus _ hwE hw1
      obtain ⟨l, hl⟩ : (g * s₁ * g⁻¹)⁻¹ * w ∈ StatedScalars (Fin 3) K :=
        QuotientGroup.eq.mp hgw.symm
      have hw : w = g⁻¹⁻¹ * s₁ * g⁻¹ * GeneralLinearGroup.scalar (Fin 3) l := by
        rw [hl, inv_inv]
        group
      rw [hw, Sec4.trace_mul_scalar, Sec4.trace_inv_conj]
      exact mul_ne_zero l.ne_zero htr2
    rcases Sec4.frame_or_heis (hK.three_ne_zero hq) hτ hτ1 E hEc hE3 (by rw [hE9]; norm_num) with
        ⟨b, hb, hd, -⟩ | ⟨y₁, y₂, -, hy₂E, ζ, hζ1, hζ⟩
    ·
      set A : Subgroup (GL (Fin 3) K) :=
        E.comap (QuotientGroup.mk' (StatedScalars (Fin 3) K)) ⊓ glPi π 3 (p ^ f) K with hA
      have hAmap : A.map (QuotientGroup.mk' (StatedScalars (Fin 3) K)) = E := by
        apply le_antisymm
        · rintro _ ⟨a, ha, rfl⟩
          exact (Subgroup.mem_inf.mp ha).1
        · intro w hw
          obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective w
          by_cases hw1 : (w : Q) = 1
          · rw [hw1]
            exact Subgroup.one_mem _
          · obtain ⟨g, hg, hgw⟩ := hfus _ hw hw1
            refine ⟨g * s₁ * g⁻¹, Subgroup.mem_inf.mpr ⟨?_, ?_⟩, hgw.symm⟩
            · change ((g * s₁ * g⁻¹ : GL (Fin 3) K) : Q) ∈ E
              rw [← hgw]
              exact hw
            · exact Sec4.slPi_le_glPi hπ (Sec4.conj_mem_slPi hπ (Sec4.slPi_le_glPi hπ hg) hs₁)
      have hC : IsTypeC π (p ^ f) K A := by
        refine ⟨inf_le_right, fun a ha => ?_, by rw [hAmap, hE9], b, hb,
          fun a ha => hd a (Subgroup.mem_inf.mp ha).1⟩
        have h1 : ((a : GL (Fin 3) K) : Q) ^ 3 = 1 := hE3 _ (Subgroup.mem_inf.mp ha).1
        rw [← QuotientGroup.mk_pow] at h1
        exact (QuotientGroup.eq_one_iff _).mp h1
      obtain ⟨a₁, ha₁A, ha₁T, -⟩ := Sec4.isTypeC_types hK hq hC
      have htr0 := trace_eq_zero_of_type1 hK hq ha₁T
      refine htrE a₁ (Subgroup.mem_inf.mp ha₁A).1 (fun h1 => ?_) htr0
      obtain ⟨l, hl⟩ := (QuotientGroup.eq_one_iff _).mp h1
      rw [← hl, ← one_mul (GeneralLinearGroup.scalar (Fin 3) l), Sec4.trace_mul_scalar] at htr0
      have h3 : ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace = 3 := by
        rw [Units.val_one, Matrix.trace_one, Fintype.card_fin]
        norm_num
      rw [h3] at htr0
      exact mul_ne_zero l.ne_zero (hK.three_ne_zero hq) htr0
    ·
      have h0 := Sec4.trace_eq_zero_of_conj_eq_scalar_mul hζ1 hζ
      refine htrE y₂ hy₂E (fun h1 => ?_) h0
      apply hζ1
      obtain ⟨l, hl⟩ := (QuotientGroup.eq_one_iff _).mp h1
      have hl' : y₁ * GeneralLinearGroup.scalar (Fin 3) l * y₁⁻¹ =
          GeneralLinearGroup.scalar (Fin 3) l := by
        rw [(CFSG.ClassicalGroups.UnitaryFlag.commute_scalar l y₁).eq, mul_inv_cancel_right]
      rw [← hl, hl'] at hζ
      have h2 : GeneralLinearGroup.scalar (Fin 3) ζ = 1 := by
        have := congrArg (fun v => v * (GeneralLinearGroup.scalar (Fin 3) l)⁻¹) hζ
        simpa using this.symm
      have h4 := congrArg (fun v : GL (Fin 3) K => (v : Matrix (Fin 3) (Fin 3) K) 0 0) h2
      simp [GeneralLinearGroup.coe_scalar] at h4
      exact h4
  · exfalso
    exact Sec4.not_inner_of_type3 hK hq hs₁H h3 ⟨s₁, hs₁, fun m _ => rfl⟩

end Model

section Frame

variable {G : Type} [Group G] [Finite G]

open Ronan138S (mem_zpowers_of_thetaQuotMulAut_eq_one inv_mul_mem_statedScalars_of_acts acts_mul
  acts_inv eq_one_of_acts_one)

theorem type1_of_lift_d {A L E F : Subgroup G} {c x y t : G}
    (hfr : Ronan138S.Frame138Base A L E F c x y t) {π : Bool} {p f : ℕ} {K : Type} [Field K]
    (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (φ : L ⧸ aschbacherSolvableCore 3 L ≃* projImage (slPi π 3 (p ^ f) K))
    {N : GL (Fin 3) K} (hN : N ∈ slPi π 3 (p ^ f) K)
    (hNd : pmk N = (φ (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨⁅x, y⁆, hfr.hdL⟩) :
      ProjGenLinGroup (Fin 3) K)) :
    Type123 π (p ^ f) K N 1 := by
  classical
  set d := ⁅x, y⁆ with hd
  set θ := aschbacherSolvableCore 3 L with hθ
  set ι : L →* ProjGenLinGroup (Fin 3) K :=
    (projImage (slPi π 3 (p ^ f) K)).subtype.comp (φ.toMonoidHom.comp (QuotientGroup.mk' θ))
    with hι
  have hιapp : ∀ l : L, ι l = (φ (QuotientGroup.mk' θ l) : ProjGenLinGroup (Fin 3) K) :=
    fun l => rfl
  have hι1 : ∀ l : L, l ^ 3 = 1 → ι l = 1 → l = 1 := by
    intro l hl3 h1
    have h2 : QuotientGroup.mk' θ l = 1 := by
      apply φ.injective
      apply Subtype.ext
      rw [map_one]
      exact h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    exact Item134SylowBarProof.eq_one_of_mem_theta_of_pow h2 (k := 1) (by simpa using hl3)
  have hlift : ∀ l : L, ∃ s ∈ slPi π 3 (p ^ f) K, pmk s = ι l := fun l => by
    obtain ⟨s, hs, hse⟩ := (φ (QuotientGroup.mk' θ l)).2
    exact ⟨s, hs, hse⟩
  have hFab := hfr.hFab
  have hF3 : ∀ z ∈ F, z ^ 3 = 1 := hfr.hF.1.2.1.2
  have hdF : d ∈ F := (Subgroup.mem_inf.mp hfr.hdZ).2
  have hdFL : d ∈ F ⊓ L := Subgroup.mem_inf.mpr ⟨hdF, hfr.hdL⟩
  obtain ⟨f', hf'FL, hf'd⟩ : ∃ f' ∈ F ⊓ L, f' ∉ Subgroup.zpowers d := by
    by_contra hall
    push Not at hall
    have hle : F ⊓ L ≤ Subgroup.zpowers d := fun z hz => hall z hz
    have h1 := Subgroup.card_le_of_le hle
    rw [hfr.hF.2, card_zpowers_of_pow_three hfr.hd3 hfr.hd1] at h1
    omega
  have hf'F : f' ∈ F := (Subgroup.mem_inf.mp hf'FL).1
  have hf'L : f' ∈ L := (Subgroup.mem_inf.mp hf'FL).2
  set dL : L := ⟨d, hfr.hdL⟩ with hdL'
  set fL : L := ⟨f', hf'L⟩ with hfL'
  obtain ⟨Nf, hNf, hNfe⟩ := hlift fL
  have hNe : pmk N = ι dL := hNd
  have hdLfL : dL * fL = fL * dL := Subtype.ext (hFab d hdF f' hf'F)
  have hdL3 : dL ^ 3 = 1 := Subtype.ext (by simpa using hfr.hd3)
  have hfL3 : fL ^ 3 = 1 := Subtype.ext (by simpa using hF3 f' hf'F)
  have hpow3 : ∀ s : GL (Fin 3) K, ∀ l : L, pmk s = ι l → l ^ 3 = 1 →
      s ^ 3 ∈ StatedScalars (Fin 3) K := by
    intro s l hsl hl3
    rw [← Sec4.mk_eq_one_iff_mem_statedScalars, map_pow, hsl, ← map_pow, hl3, map_one]
  refine type1_of_fused hK hq hN hNf (hpow3 N dL hNe hdL3) (hpow3 Nf fL hNfe hfL3) ?_ ?_ ?_ ?_
  ·
    rw [← QuotientGroup.mk_mul, mkQ_eq_iff, map_mul, map_mul, hNe, hNfe, ← map_mul, ← map_mul,
      hdLfL]
  ·
    intro hsc
    apply hfr.hd1
    have h1 : ι dL = 1 := by rw [← hNe]; exact Sec4.mk_eq_one_iff_mem_statedScalars.mpr hsc
    exact congrArg Subtype.val (hι1 dL hdL3 h1)
  ·
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [← QuotientGroup.mk_zpow, mkQ_eq_iff, map_zpow, hNe, hNfe, ← map_zpow] at hk
    have h1 : ι (fL * (dL ^ k)⁻¹) = 1 := by rw [map_mul, map_inv, ← hk, mul_inv_cancel]
    have h3 : (fL * (dL ^ k)⁻¹) ^ 3 = 1 := by
      have hc : Commute fL ((dL ^ k)⁻¹) := ((Commute.zpow_right hdLfL.symm k)).inv_right
      rw [hc.mul_pow, hfL3, one_mul, inv_pow, ← zpow_natCast, ← zpow_mul, mul_comm k,
        zpow_mul, zpow_natCast, hdL3, one_zpow, inv_one]
    have h4 := hι1 _ h3 h1
    apply hf'd
    have h5 : fL = dL ^ k := by
      rw [mul_inv_eq_one] at h4
      exact h4
    have h6 := congrArg Subtype.val h5
    rw [Subgroup.coe_zpow] at h6
    rw [show f' = d ^ k from h6]
    exact zpow_mem (Subgroup.mem_zpowers d) k
  ·
    intro w hw hw1
    have hNNf : ((N : GL (Fin 3) K) : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) *
        (Nf : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) =
        (Nf : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) *
          (N : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) := by
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mkQ_eq_iff, map_mul, map_mul, hNe, hNfe,
        ← map_mul, ← map_mul, hdLfL]
    obtain ⟨i, j, rfl⟩ := Sec4.exists_zpow_mul_of_mem_sup hNNf hw
    set zL : L := dL ^ i * fL ^ j with hzL
    have hzw : pmk (N ^ i * Nf ^ j) = ι zL := by
      rw [map_mul, map_zpow, map_zpow, hNe, hNfe, hzL, map_mul, map_zpow, map_zpow]
    have hzFL : (zL : G) ∈ F ⊓ L := by
      refine Subgroup.mem_inf.mpr ⟨?_, zL.2⟩
      rw [hzL, Subgroup.coe_mul, Subgroup.coe_zpow, Subgroup.coe_zpow]
      exact mul_mem (zpow_mem hdF i) (zpow_mem hf'F j)
    have hz1 : (zL : G) ≠ 1 := by
      intro h1
      apply hw1
      rw [← QuotientGroup.mk_zpow, ← QuotientGroup.mk_zpow, ← QuotientGroup.mk_mul,
        QuotientGroup.eq_one_iff, ← Sec4.mk_eq_one_iff_mem_statedScalars, hzw,
        show zL = 1 from Subtype.ext h1, map_one]
    obtain ⟨l, hl, hlz⟩ := hfr.hF.1.2.2.2.1 d hdFL hfr.hd1 _ hzFL hz1
    obtain ⟨g, hg, hge⟩ := hlift ⟨l, hl⟩
    have hconj : (⟨l, hl⟩ : L) * dL * (⟨l, hl⟩ : L)⁻¹ = zL := Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact hlz)
    refine ⟨g, hg, ?_⟩
    rw [← QuotientGroup.mk_zpow, ← QuotientGroup.mk_zpow, ← QuotientGroup.mk_mul, mkQ_eq_iff, hzw,
      ← hconj, map_mul ι, map_mul ι, map_inv ι, ← hge, ← hNe, map_mul, map_mul, map_inv]

theorem type2_of_not_mem_zpowers {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec13Data G A c L) (hEN : E ≤ Subgroup.normalizer (L : Set G))
    (hCE : Late.sectionCentralizer E L ((aschbacherSolvableCore 3 L).map L.subtype) =
      (Subgroup.zpowers c : Set G))
    {d : G} (hdE : d ∈ E) (hdL : d ∈ L) (hd1 : d ≠ 1)
    {π : Bool} {p f : ℕ} {K : Type} [Field K] (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (φ : L ⧸ aschbacherSolvableCore 3 L ≃* projImage (slPi π 3 (p ^ f) K))
    (hd1T : ∀ N ∈ slPi π 3 (p ^ f) K,
      ProjGenLinGroup.mk N = (φ (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨d, hdL⟩) :
        ProjGenLinGroup (Fin 3) K) → Type123 π (p ^ f) K N 1)
    {D : Subgroup (GL (Fin 3) K)} (hD : IsTypeC π (p ^ f) K D)
    (hτD : ∀ τ ∈ Sec4.autThetaQuot E L, ∃ y ∈ D, ∀ z : L ⧸ aschbacherSolvableCore 3 L,
      ((φ (τ z) : ProjGenLinGroup (Fin 3) K)) =
        ProjGenLinGroup.mk y * (φ z : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk y)⁻¹)
    {e : G} (heE : e ∈ E) (he : e ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d) {y : GL (Fin 3) K}
    (hyD : y ∈ D)
    (hy : ∀ z : L ⧸ aschbacherSolvableCore 3 L,
      ((φ (Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨e, hEN heE⟩) z) :
        ProjGenLinGroup (Fin 3) K)) =
        ProjGenLinGroup.mk y * (φ z : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk y)⁻¹) :
    Type123 π (p ^ f) K y 2 := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have hL := h.mem_thetaComponentsAt
  have hq2 := Item138Proof.two_lt_of_mulEquiv (Sec6.isQuasisimple_of_mem_thetaComponentsAt hL)
    hK hq φ
  have hc3 : c ^ 3 = 1 := h.isElemAbelian.2 c h.mem_A
  have hZL := Sec13.center_eq_bot_of_mulEquiv φ (Sec13.center_projImage_slPi hK hq hq2)
  have hcL : c ∉ L := Sec13.not_mem_of_center_eq_bot h hZL
  have hdN : d ∈ Subgroup.normalizer (L : Set G) := hEN hdE
  obtain ⟨yd, hydD, hyd⟩ := hτD _ (Sec4.mem_autThetaQuot_iff.mpr ⟨d, hdN, hdE, rfl⟩)
  have hy1 : ProjGenLinGroup.mk y ≠ 1 := by
    intro h1
    apply he
    refine Subgroup.mem_sup_left (mem_zpowers_of_thetaQuotMulAut_eq_one hEN hCE heE
      (eq_one_of_acts_one φ fun z => ?_))
    rw [hy z, h1]
  have hyd1 : ProjGenLinGroup.mk yd ≠ 1 := by
    intro h1
    have hdc := mem_zpowers_of_thetaQuotMulAut_eq_one hEN hCE hdE
      (eq_one_of_acts_one φ fun z => by rw [hyd z, h1])
    apply hd1
    have hmem : d ∈ Subgroup.zpowers c ⊓ L := Subgroup.mem_inf.mpr ⟨hdc, hdL⟩
    rw [zpowers_inf_eq_bot hc3 hcL] at hmem
    exact Subgroup.mem_bot.mp hmem
  obtain ⟨N, hN, hNd⟩ := (φ (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨d, hdL⟩)).2
  have hτd : ∀ z : L ⧸ aschbacherSolvableCore 3 L,
      ((φ (Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨d, hdN⟩) z) :
        ProjGenLinGroup (Fin 3) K)) =
        ProjGenLinGroup.mk N * (φ z : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk N)⁻¹ := by
    intro z
    rw [show Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨d, hdN⟩) =
        MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨d, hdL⟩) from
      KFacts.thetaQuotMulAut_compAction_of_mem hdL hdN, MulAut.conj_apply, map_mul, map_mul,
      map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hNd]
  have hsc := inv_mul_mem_statedScalars_of_acts hK hq hq2 φ hτd hyd
  obtain ⟨τ, hτ, hτ1⟩ := Sec4.exists_tau hK hq
  have hydH : yd ∈ glPi π 3 (p ^ f) K := hD.1 hydD
  have hydsc : yd ∉ StatedScalars (Fin 3) K := fun h =>
    hyd1 (Sec4.mk_eq_one_iff_mem_statedScalars.mpr h)
  have hysc : y ∉ StatedScalars (Fin 3) K := fun h =>
    hy1 (Sec4.mk_eq_one_iff_mem_statedScalars.mpr h)
  have hydZ : yd ∉ zPi π 3 (p ^ f) K := fun hz => by
    rw [Sec4.zPi_eq hπ hq' hτ hτ1] at hz
    exact hydsc hz.2
  have hyd3 : yd ^ 3 ∈ zPi π 3 (p ^ f) K := by
    rw [Sec4.zPi_eq hπ hq' hτ hτ1]
    exact ⟨pow_mem hydH 3, hD.2.1 yd hydD⟩
  have hydT : Type123 π (p ^ f) K yd 1 := by
    have hNT := hd1T N hN hNd
    have hNH : N ∈ glPi π 3 (p ^ f) K := Sec4.slPi_le_glPi hπ hN
    have hz : N⁻¹ * yd ∈ zPi π 3 (p ^ f) K := by
      rw [Sec4.zPi_eq hπ hq' hτ hτ1]
      exact Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hNH) hydH, hsc⟩
    have h1 := Sec4.Res423Four.type1_conj_mul hK hq hNT (one_mem _) hz
    rwa [one_mul, inv_one, mul_one, mul_inv_cancel_left] at h1
  obtain ⟨a₁, -, -, htypes⟩ := Sec4.isTypeC_types hK hq hD
  refine (htypes y hyD hysc).2 fun hyT => ?_
  have key : ∀ x : GL (Fin 3) K,
      (x * a₁⁻¹ ∈ StatedScalars (Fin 3) K ∨ x * a₁ ∈ StatedScalars (Fin 3) K) →
      (ProjGenLinGroup.mk x = ProjGenLinGroup.mk a₁ ∨
        ProjGenLinGroup.mk x = (ProjGenLinGroup.mk a₁)⁻¹) := by
    rintro x (hx | hx)
    · left
      rw [← Sec4.mk_eq_one_iff_mem_statedScalars, map_mul, map_inv, mul_inv_eq_one] at hx
      exact hx
    · right
      rw [← Sec4.mk_eq_one_iff_mem_statedScalars, map_mul, mul_eq_one_iff_eq_inv] at hx
      exact hx
  have hcomb : ProjGenLinGroup.mk y = ProjGenLinGroup.mk yd ∨
      ProjGenLinGroup.mk y = (ProjGenLinGroup.mk yd)⁻¹ := by
    rcases key y ((htypes y hyD hysc).1.mp hyT) with hY | hY <;>
      rcases key yd ((htypes yd hydD hydsc).1.mp hydT) with hYd | hYd
    · exact Or.inl (by rw [hY, hYd])
    · exact Or.inr (by rw [hY, hYd, inv_inv])
    · exact Or.inr (by rw [hY, hYd])
    · exact Or.inl (by rw [hY, hYd])
  apply he
  have hdEL : d ∈ Subgroup.zpowers d := Subgroup.mem_zpowers d
  rcases hcomb with hc | hc
  ·
    have hw : Sec4.thetaQuotMulAut L
        (L.normalizerMonoidHom ⟨e * d⁻¹, hEN (mul_mem heE (inv_mem hdE))⟩) = 1 := by
      have hsplit : Sec4.thetaQuotMulAut L
          (L.normalizerMonoidHom ⟨e * d⁻¹, hEN (mul_mem heE (inv_mem hdE))⟩) =
          Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨e, hEN heE⟩) *
            (Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨d, hdN⟩))⁻¹ := by
        have h1 := map_mul ((Sec4.thetaQuotMulAut L).comp L.normalizerMonoidHom) ⟨e, hEN heE⟩
          (⟨d, hdN⟩ : Subgroup.normalizer (L : Set G))⁻¹
        rw [map_inv] at h1
        exact h1
      rw [hsplit]
      refine eq_one_of_acts_one φ fun z => ?_
      rw [acts_mul φ hy (acts_inv φ hyd) z, hc, mul_inv_cancel]
    have hwc := mem_zpowers_of_thetaQuotMulAut_eq_one hEN hCE (mul_mem heE (inv_mem hdE)) hw
    rw [show e = e * d⁻¹ * d by group]
    exact mul_mem (Subgroup.mem_sup_left hwc) (Subgroup.mem_sup_right hdEL)
  ·
    have hw : Sec4.thetaQuotMulAut L
        (L.normalizerMonoidHom ⟨e * d, hEN (mul_mem heE hdE)⟩) = 1 := by
      have hsplit : Sec4.thetaQuotMulAut L
          (L.normalizerMonoidHom ⟨e * d, hEN (mul_mem heE hdE)⟩) =
          Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨e, hEN heE⟩) *
            Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨d, hdN⟩) := by
        have h1 := map_mul ((Sec4.thetaQuotMulAut L).comp L.normalizerMonoidHom) ⟨e, hEN heE⟩
          ⟨d, hdN⟩
        exact h1
      rw [hsplit]
      refine eq_one_of_acts_one φ fun z => ?_
      rw [acts_mul φ hy hyd z, hc, inv_mul_cancel]
    have hwc := mem_zpowers_of_thetaQuotMulAut_eq_one hEN hCE (mul_mem heE hdE) hw
    rw [show e = e * d * d⁻¹ by group]
    exact mul_mem (Subgroup.mem_sup_left hwc) (Subgroup.mem_sup_right (inv_mem hdEL))

end Frame

end CFSG.RankThree.PartTwo.Sec13.Ronan138T

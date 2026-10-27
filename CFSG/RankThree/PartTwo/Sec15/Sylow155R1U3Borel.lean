module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Defs
import CFSG.Milestones.ASVolI.A3Aut.D5U3
import CFSG.Holt.General.DLineTools
import CFSG.LocalAnalysis.ComponentClassification.GMS78BasicSylow
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1R0
public import CFSG.RankThree.PartTwo.Sec21.HoltCatalog

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.PGLModel (projSU)

section Abstract

variable {Y : Type} [Group Y]

private theorem res1U3_two_lt_two_pow {n : ℕ} (hn : 2 ≤ n) : 2 < 2 ^ n :=
  calc 2 < 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

private theorem res1U3_two_pow_mod_three {n : ℕ} (hn : Even n) : 2 ^ n % 3 = 1 := by
  obtain ⟨k, rfl⟩ := hn
  rw [← two_mul, pow_mul, Nat.pow_mod]
  norm_num

private noncomputable def res1U3Equiv {n : ℕ} (hn : 1 ≤ n) (e : Y ≃* projSU 3 2 n) :
    Y ≃* unitaryPSU (Sec4.unitaryFieldData_galoisField 2 n hn) 3 :=
  e.trans (Sec4.projSUEquivUnitaryPSU 2 n (Sec4.unitaryFieldData_galoisField 2 n hn))

theorem res1U3_exists_fusionBenderBorel [Finite Y] {n : ℕ} (hn : 2 ≤ n)
    (e : Y ≃* projSU 3 2 n) :
    ∃ f k : ℕ, 2 ≤ f ∧ CFSG.Open.fusionBenderBorel Y (2 ^ f) k := by
  have hU := Sec4.unitaryFieldData_galoisField 2 n (by omega)
  exact CFSG.Holt.General.exists_fusionBenderBorel_two_pow_of_fusionIsBenderGroup
    (Sec21.fusionIsBenderGroup_of_mulEquiv (res1U3Equiv (by omega) e).symm
      (CFSG.ASVolI.burnsideAut_d5u3_fusionIsBender hU hn))

theorem res1U3_center_eq_bot {n : ℕ} (hn : 2 ≤ n) (e : Y ≃* projSU 3 2 n) :
    Subgroup.center Y = ⊥ := by
  set E := res1U3Equiv (by omega) e
  have h := KFacts.center_unitaryPSU_three_eq_bot (Sec4.unitaryFieldData_galoisField 2 n
    (by omega)) (res1U3_two_lt_two_pow hn)
  rw [eq_bot_iff]
  intro z hz
  have hEz : E z ∈ Subgroup.center _ := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    obtain ⟨y, rfl⟩ := E.surjective g
    rw [← map_mul, ← map_mul, hz y]
  rw [h, Subgroup.mem_bot] at hEz
  exact Subgroup.mem_bot.mpr (E.map_eq_one_iff.mp hEz)

theorem res1U3_smul_sylow_eq [Finite Y] {n : ℕ} (hn : 2 ≤ n) (e : Y ≃* projSU 3 2 n)
    (U : Sylow 2 Y) {t : Y} (ht : t ≠ 1) (htU : t ∈ U) (σ : MulAut Y) (hσ : σ t ∈ U) :
    σ • U = U := by
  obtain ⟨f, k, -, hB⟩ := res1U3_exists_fusionBenderBorel hn e
  refine CFSG.ASVolI.burnsideAut_d5_sylow_eq_of_mem hB (t := σ t) ?_ ?_ hσ
  · rwa [Ne, MulEquiv.map_eq_one_iff]
  · rw [Sylow.pointwise_smul_def]
    exact Subgroup.smul_mem_pointwise_smul t σ (U : Subgroup Y) htU

theorem res1U3_isSolvable_stabilizer [Finite Y] {n : ℕ} (hn : 0 < n) (heven : Even n)
    (e : Y ≃* projSU 3 2 n) (U : Sylow 2 Y) :
    Group.IsSolvable (MulAction.stabilizer (MulAut Y) U) := by
  have hn2 : 2 ≤ n := by
    obtain ⟨k, rfl⟩ := heven
    omega
  obtain ⟨f, k, -, hB⟩ := res1U3_exists_fusionBenderBorel hn2 e
  obtain ⟨D, hD, -, -, hsup⟩ := (hB U).2.1
  haveI : Group.IsSolvable (Subgroup.normalizer ((U : Subgroup Y) : Set Y)) :=
    CFSG.ComponentClassification.GMS78.isSolvable_normalizer_of_sup_cyclic U.isPGroup' hD hsup
  set B := MulAction.stabilizer (MulAut Y) U with hBdef
  have hconj : ∀ g : Y, MulAut.conj g ∈ B ↔
      g ∈ Subgroup.normalizer ((U : Subgroup Y) : Set Y) := by
    intro g
    rw [MulAction.mem_stabilizer_iff, ← Sylow.smul_def]
    exact Sylow.smul_eq_iff_mem_normalizer
  let φ : Subgroup.normalizer ((U : Subgroup Y) : Set Y) →* B :=
    { toFun := fun g => ⟨MulAut.conj (g : Y), (hconj g).mpr g.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
  have hU' := Sec4.unitaryFieldData_galoisField 2 n (by omega)
  have hI : ∀ σ τ : MulAut Y, KFacts.IsInnerAut (σ * τ * σ⁻¹ * τ⁻¹) :=
    KFacts.isInnerAut_commutator_of_mulEquiv_unitaryPSU hU' (res1U3_two_pow_mod_three heven)
      (res1U3_two_lt_two_pow hn2) (res1U3Equiv (by omega) e)
  refine Group.isSolvable_of_ker_le_range φ Abelianization.of ?_
  rw [Abelianization.ker_of, commutator_def, Subgroup.commutator_le]
  rintro σ - τ -
  obtain ⟨g, hg⟩ := hI σ τ
  have hgB : MulAut.conj g ∈ B := by
    rw [hg]
    exact B.mul_mem (B.mul_mem (B.mul_mem σ.2 τ.2) (B.inv_mem σ.2)) (B.inv_mem τ.2)
  refine ⟨⟨g, (hconj g).mp hgB⟩, Subtype.ext ?_⟩
  change MulAut.conj g = _
  rw [hg, commutatorElement_def]
  simp

theorem res1U3_exists_solvable_of_isPGroup [Finite Y] {n : ℕ} (hn : 0 < n) (heven : Even n)
    (e : Y ≃* projSU 3 2 n) {R : Subgroup Y} (hR : IsPGroup 2 R) (hR1 : R ≠ ⊥) :
    ∃ B : Subgroup (MulAut Y), Group.IsSolvable B ∧
      ∀ σ : MulAut Y, (∀ r ∈ R, σ r ∈ R) → σ ∈ B := by
  have hn2 : 2 ≤ n := by
    obtain ⟨k, rfl⟩ := heven
    omega
  obtain ⟨U, hRU⟩ := hR.exists_le_sylow
  obtain ⟨⟨t, htR⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hR1
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  refine ⟨MulAction.stabilizer (MulAut Y) U, res1U3_isSolvable_stabilizer hn heven e U,
    fun σ hσ => ?_⟩
  exact MulAction.mem_stabilizer_iff.mpr
    (res1U3_smul_sylow_eq hn2 e U ht1' (hRU htR) σ (hRU (hσ t htR)))

end Abstract

variable {G : Type} [Group G] [Finite G]

private theorem res1U3_conj_mem_pCoreOf {M : Subgroup G} {m v : G} (hm : m ∈ M)
    (hv : v ∈ CFSG.Open.pCoreOf 2 M) : m * v * m⁻¹ ∈ CFSG.Open.pCoreOf 2 M :=
  (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hm) v).mp hv

theorem res1_rho_mem_borel {A : Subgroup G} {c : G} {L M : Subgroup G}
    {Yc : Subgroup (Res1Q A L)} [Yc.Normal] (hS : Sec14Std G A c L) (hAM : A ≤ M)
    (h142 : Concl142 A (lB A)) (hY : Res1AtOf A c L M Yc) {n : ℕ} (hn : 0 < n)
    (heven : Even n) (e : ↥Yc ≃* projSU 3 2 n) :
    ∃ B : Subgroup (MulAut ↥Yc), Group.IsSolvable ↥B ∧ ∀ m : ↥(Res1C A L), (m : G) ∈ M →
      MulAut.conjNormal (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) m) ∈ B := by
  have hn2 : 2 ≤ n := by
    obtain ⟨k, rfl⟩ := heven
    omega
  set C := Res1C A L with hCdef
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C) with hπdef
  let ρ : Res1Q A L →* MulAut ↥Yc := MulAut.conjNormal
  set W : Subgroup ↥C := (CFSG.Open.pCoreOf 2 M ⊓ C).subgroupOf C with hWdef
  have hWconj : ∀ m : ↥C, (m : G) ∈ M → ∀ q ∈ W, m * q * m⁻¹ ∈ W := by
    intro m hm q hq
    rw [hWdef, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hq ⊢
    exact ⟨by simpa using res1U3_conj_mem_pCoreOf hm hq.1, (m * q * m⁻¹).2⟩
  set Vh : Subgroup (MulAut ↥Yc) := (W.map π).map ρ with hVhdef
  set R₀ : Subgroup ↥Yc := Vh.comap MulAut.conj with hR₀def
  have hρconj : ∀ m : ↥C, (m : G) ∈ M → ∀ r ∈ R₀, ρ (π m) r ∈ R₀ := by
    intro m hm r hr
    obtain ⟨_, ⟨w, hw, rfl⟩, hwr⟩ := hr
    refine ⟨π (m * w * m⁻¹), ⟨m * w * m⁻¹, hWconj m hm w hw, rfl⟩, ?_⟩
    have e1 : MulAut.conj (ρ (π m) r) = ρ (π m) * MulAut.conj r * (ρ (π m))⁻¹ := by
      ext z
      simp
    rw [e1, ← hwr]
    simp
  have hR₀ne : R₀ ≠ ⊥ := by
    obtain ⟨w, hwM, y₀, hy₀Y, hy₀1, hy₀w⟩ := res1_exists_inner hS hAM h142 hY
    intro hbot
    have hmem : (⟨y₀, hy₀Y⟩ : ↥Yc) ∈ R₀ := by
      refine ⟨π w, ⟨w, Subgroup.mem_subgroupOf.mpr ⟨hwM, w.2⟩, rfl⟩, ?_⟩
      refine MulEquiv.ext fun z => Subtype.ext ?_
      simp only [ρ, MulAut.conjNormal_apply, MulAut.conj_apply, Subgroup.coe_mul,
        Subgroup.coe_inv]
      exact hy₀w z z.2
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hy₀1 (congrArg Subtype.val hmem)
  have hcenter : Subgroup.center ↥Yc = ⊥ := res1U3_center_eq_bot hn2 e
  have hW2 : IsPGroup 2 W :=
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le inf_le_left).comap_subtype
  have hR₀2 : IsPGroup 2 R₀ := by
    refine IsPGroup.comap_of_ker_isPGroup ((hW2.map π).map ρ) MulAut.conj ?_
    have hker : (MulAut.conj : ↥Yc →* MulAut ↥Yc).ker = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      rw [← hcenter, Subgroup.mem_center_iff]
      intro w
      have h := congrArg (fun α : MulAut ↥Yc => α w) (MonoidHom.mem_ker.mp hz)
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      exact (mul_inv_eq_iff_eq_mul.mp h).symm
    rw [hker]
    exact IsPGroup.of_bot
  obtain ⟨B, hB, hmem⟩ := res1U3_exists_solvable_of_isPGroup hn heven e hR₀2 hR₀ne
  exact ⟨B, hB, fun m hm => hmem _ (hρconj m hm)⟩

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsOmegaK
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOm.MinusModel
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOm.MinusSylow
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOm.MinusBorel
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOm.OddConj
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOm.RootGroupGL
import CFSG.ClassicalGroups.Orthogonal.RootGroupGLEichler
import CFSG.GroupTheory.WeirSylow.UniqueE27Orthogonal
public import CFSG.GroupTheory.GL52.Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsComponents
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsSL3
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21b
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Matrix
open CFSG.ClassicalGroups.Orthogonal (lineStabilizer mem_lineStabilizer_iff rootGroupGL)
open CFSG.LieType.Universal.Spin (quadMinus)

local notation "ιM" => Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2

private theorem glPull_conj {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {W : Type} [CommGroup W] (e : W ≃* Multiplicative (ι → K)) (A B : GL ι K) :
    KOm.glPull e A * KOm.glPull e B * (KOm.glPull e A)⁻¹ =
      KOm.glPull e (A * B * A⁻¹) := by
  rw [← map_mul, ← map_inv, ← map_mul]

private theorem mem_lineStabilizer_of_mem_statedOmega {K : Type} [Field K] {b c : K}
    {A : GL ιM K} (hA : A ∈ StatedOmega (StatedQuadMinus 2 K b c)) {s : K}
    (hs : (A : Matrix ιM ιM K) *ᵥ KTabC.e1M K = s • KTabC.e1M K) :
    A ∈ lineStabilizer (quadMinus 2 K b c) (KTabC.e1M K) := by
  rw [mem_lineStabilizer_iff]
  refine ⟨fun v => ?_, s, hs⟩
  have h := CFSG.GroupTheory.WeirSylow.apply_mulVec_of_mem_isometryCore
    (CFSG.GroupTheory.WeirSylow.statedOmega_le_isometryCore (StatedQuadMinus 2 K b c) hA) v
  simpa only [CFSG.LieType.Universal.Spin.coe_quadMinus] using h

theorem kOmC_holds : KOmC := by
  intro W _ _ H n S Tstar hF hTnot B hBH hBodd hBfix
  obtain ⟨K, hKfield, hKfin, hKchar, b, c, hKcard, hirr, e, T, hH, hTstar, hTiso, hT2,
    hUT, hfixV⟩ := KOm.exists_minusModel hF
  letI : Field K := hKfield
  letI : Finite K := hKfin
  letI : CharP K 2 := hKchar
  classical
  have hBle : B ≤ (StatedOmega (StatedQuadMinus 2 K b c)).map (KOm.glPull e) := by
    rw [← hH]
    exact hBH
  obtain ⟨B', hB'Ω, hBeq⟩ := KOm.exists_eq_map_glPull_of_le e hBle
  have hB'card : Nat.card ↥B' = Nat.card ↥B := by
    rw [hBeq, Subgroup.card_map_of_injective (KOm.glPull_injective e)]
  have hB'odd : Odd (Nat.card ↥B') := by
    rw [hB'card]
    exact hBodd
  have hmem : ∀ g ∈ B', KOm.glPull e g ∈ B := by
    intro g hg
    rw [hBeq]
    exact Subgroup.mem_map_of_mem (KOm.glPull e) hg
  have hline : ∀ g ∈ B', (KOm.linePull e (KTabC.e1M K)).map (KOm.glPull e g).toMonoidHom =
      KOm.linePull e (KTabC.e1M K) := by
    intro g hg
    have h := hBfix (KOm.glPull e g) (hmem g hg)
    rwa [hfixV] at h
  have hB'line : B' ≤ lineStabilizer (quadMinus 2 K b c) (KTabC.e1M K) := by
    intro g hg
    obtain ⟨s, hs⟩ := KOm.exists_mulVec_eq_smul_of_map_glPull_linePull e (hline g hg)
    exact mem_lineStabilizer_of_mem_statedOmega (hB'Ω hg) hs
  have hB'norm : B' ≤ Subgroup.normalizer
      (rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K) : Set (GL ιM K)) := by
    rw [Subgroup.le_normalizer_iff]
    intro g hg k hk
    exact CFSG.ClassicalGroups.Orthogonal.conj_mem_rootGroupGL (hB'line hg) hk
  have hnotTΩ : ¬ T ≤ StatedOmega (StatedQuadMinus 2 K b c) := by
    intro hle
    exact hTnot (by rw [hTstar, hH]; exact Subgroup.map_mono hle)
  have hnotsub : ¬ (T : Set (GL ιM K)) ⊆
      (StatedOmega (StatedQuadMinus 2 K b c) : Set (GL ιM K)) :=
    fun hsub => hnotTΩ fun t ht => hsub ht
  obtain ⟨t₀, ht₀T, ht₀Ω⟩ := Set.not_subset.1 hnotsub
  have ht₀U : t₀ ∉ rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K) := fun h =>
    ht₀Ω (KOm.rootGroupGL_le_statedOmega_minus (K := K) (b := b) (c := c) hirr
      (KTabC.e1M K) h)
  have ht₀iso : t₀ ∈ KOm.isoFix (StatedQuadMinus 2 K b c) (KTabC.e1M K) := hTiso ht₀T
  obtain ⟨mT, hmT⟩ := IsPGroup.exists_card_eq hT2
  have ht₀pow : t₀ ^ 2 ^ mT = 1 := by
    rw [← hmT]
    exact orderOf_dvd_iff_pow_eq_one.1 (Subgroup.orderOf_dvd_natCard T ht₀T)
  have hconj : ∀ g ∈ B', t₀ * g * t₀⁻¹ * (g ^ Nat.card K)⁻¹ ∈
      rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K) := by
    intro g hg
    exact KOm.conj_mul_inv_pow_card_mem_rootGroupGL (K := K) (b := b) (c := c) hirr ht₀iso
      ht₀U ht₀pow (hB'line hg) (hB'odd.of_dvd_nat (Subgroup.orderOf_dvd_natCard B' hg))
  have hU2 : IsPGroup 2 ↥(rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K)) :=
    KOm.isPGroup_rootGroupGL
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite
        (K := K) (n := 2) (b := b) (c := c) hirr)
      (KOm.quadMinus_e1M b c) KOm.e1M_ne_zero
  obtain ⟨kU, hUcard⟩ := IsPGroup.exists_card_eq hU2
  have hcop : Nat.Coprime (Nat.card ↥(rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K)))
      (Nat.card ↥B') := by
    rw [hUcard]
    exact Nat.Coprime.pow_left kU (Odd.coprime_two_left hB'odd)
  obtain ⟨a, haU, haconj⟩ :=
    KOm.exists_mem_conj_eq_pow (U := rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K)) (B := B')
      hcop hB'norm hconj
  have htT : KOm.glPull e (a * t₀) ∈ Tstar := by
    rw [hTstar]
    exact Subgroup.mem_map_of_mem (KOm.glPull e) (T.mul_mem (hUT haU) ht₀T)
  have htconj : ∀ g ∈ B', KOm.glPull e (a * t₀) * KOm.glPull e g *
      (KOm.glPull e (a * t₀))⁻¹ = KOm.glPull e (g ^ Nat.card K) := by
    intro g hg
    rw [glPull_conj e (a * t₀) g, haconj g hg]
  refine ⟨KOm.glPull e (a * t₀), htT, ?_, ?_⟩
  · intro y hy
    rw [hBeq] at hy ⊢
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hy
    rw [htconj g hg]
    exact Subgroup.mem_map_of_mem (KOm.glPull e) (B'.pow_mem hg (Nat.card K))
  · intro y hy hyfix
    rw [hBeq] at hy
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hy
    have hfixline : ∀ w ∈ KOm.linePull e (KTabC.e1M K), KOm.glPull e g w = w := by
      intro w hw
      exact hyfix w (by rw [hfixV]; exact hw)
    have hge1 : (g : Matrix ιM ιM K) *ᵥ KTabC.e1M K = KTabC.e1M K :=
      KOm.mulVec_eq_of_forall_mem_linePull e hfixline
    have hgiso : g ∈ KOm.isoFix (StatedQuadMinus 2 K b c) (KTabC.e1M K) := by
      rw [KOm.mem_isoFix]
      refine ⟨fun v => ?_, hge1⟩
      have h := CFSG.GroupTheory.WeirSylow.apply_mulVec_of_mem_isometryCore
        (CFSG.GroupTheory.WeirSylow.statedOmega_le_isometryCore (StatedQuadMinus 2 K b c)
          (hB'Ω hg)) v
      simpa only [CFSG.LieType.Universal.Spin.coe_quadMinus] using h
    have hoddg : Odd (orderOf g) :=
      hB'odd.of_dvd_nat (Subgroup.orderOf_dvd_natCard B' hg)
    have hpowU : g ^ (Nat.card K + 1) ∈ rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K) :=
      KOm.pow_card_add_one_mem_rootGroupGL (K := K) (b := b) (c := c) hirr hgiso hoddg
    have hbot : rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K) ⊓ B' = ⊥ :=
      Subgroup.inf_eq_bot_of_coprime hcop
    have hone : g ^ (Nat.card K + 1) = 1 := by
      have hmem' : g ^ (Nat.card K + 1) ∈
          rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K) ⊓ B' :=
        Subgroup.mem_inf.mpr ⟨hpowU, B'.pow_mem hg (Nat.card K + 1)⟩
      simpa only [hbot, Subgroup.mem_bot] using hmem'
    have hgq : g ^ Nat.card K = g⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hone)
    rw [htconj g hg, hgq, map_inv]

end CFSG.LocalAnalysis.UniquenessCase.UC22

end

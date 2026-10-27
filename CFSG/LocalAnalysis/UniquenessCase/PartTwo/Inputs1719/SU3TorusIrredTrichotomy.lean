module

public import CFSG.ClassicalGroups.UnitaryFlag.SU3TorusFrame
import all CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQSSL2
import CFSG.ClassicalGroups.UnitaryFlag.SU3NonisotropicStabilizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU3TorusIrred

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups
open scoped MatrixGroups

variable {n : ℕ} {K : Type} [Field K] {T : Subgroup (unitarySU 2 n K 3)}

private theorem centralizer_zpowers_eq_subgroupOf {h : UnitaryFieldData 2 n K} [Finite K]
    (F : SU3TorusFrame h T) (hT : Nat.card T = 2 ^ n - 1) {F' : Type} [Field F'] [Finite F']
    (ψ : ↥(MulAction.stabilizer (unitarySU 2 n K 3) F.v) ≃* SL(2, F'))
    (hF' : Nat.card F' = 2 ^ n) {d : ↥(MulAction.stabilizer (unitarySU 2 n K 3) F.v)}
    (hdT : (d : unitarySU 2 n K 3) ∈ T)
    (hmap : (Subgroup.centralizer (Subgroup.zpowers d : Set _)).map ψ.toMonoidHom =
      CFSG.CGT.Timmesfeld75.torus F') :
    Subgroup.centralizer (Subgroup.zpowers d : Set _) =
      T.subgroupOf (MulAction.stabilizer (unitarySU 2 n K 3) F.v) := by
  let L := MulAction.stabilizer (unitarySU 2 n K 3) F.v
  have : Finite ↥L := inferInstance
  have hTL : T ≤ L := fun t ht => MulAction.mem_stabilizer_iff.2 (F.smul_v ⟨t, ht⟩)
  have hle : T.subgroupOf L ≤ Subgroup.centralizer (Subgroup.zpowers d : Set ↥L) := by
    rw [CFSG.LocalAnalysis.EvenBN.Common.centralizer_zpowers]
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (F.mul_comm_of_mem (Subgroup.mem_subgroupOf.mp hx) hdT)
  have hcardT' : Nat.card (T.subgroupOf L) = 2 ^ n - 1 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTL).toEquiv, hT]
  have hcardTorus : Nat.card (CFSG.CGT.Timmesfeld75.torus F') = Nat.card F' - 1 := by
    rw [← TorusQS.torusSL_eq_torus]
    exact CFSG.LocalAnalysis.EvenBN.Common.card_torusSL
  have hcardC : Nat.card (Subgroup.centralizer (Subgroup.zpowers d : Set ↥L)) = 2 ^ n - 1 := by
    calc Nat.card (Subgroup.centralizer (Subgroup.zpowers d : Set ↥L))
        = Nat.card ((Subgroup.centralizer (Subgroup.zpowers d : Set ↥L)).map ψ.toMonoidHom) :=
          (Subgroup.card_map_of_injective ψ.injective).symm
      _ = Nat.card (CFSG.CGT.Timmesfeld75.torus F') := by rw [hmap]
      _ = Nat.card F' - 1 := hcardTorus
      _ = 2 ^ n - 1 := by rw [hF']
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardC, hcardT'])).symm

private theorem le_normalizer_of_le_normalizer_map {h : UnitaryFieldData 2 n K}
    {F : SU3TorusFrame h T} {N : Subgroup (unitarySU 2 n K 3)}
    (hNL : N ≤ MulAction.stabilizer (unitarySU 2 n K 3) F.v) {F' : Type} [Field F']
    {ψ : ↥(MulAction.stabilizer (unitarySU 2 n K 3) F.v) ≃* SL(2, F')}
    (hmap : (T.subgroupOf (MulAction.stabilizer (unitarySU 2 n K 3) F.v)).map ψ.toMonoidHom =
      CFSG.CGT.Timmesfeld75.torus F')
    (hN' : (N.subgroupOf (MulAction.stabilizer (unitarySU 2 n K 3) F.v)).map ψ.toMonoidHom ≤
      Subgroup.normalizer (CFSG.CGT.Timmesfeld75.torus F' : Set SL(2, F'))) :
    N ≤ Subgroup.normalizer (T : Set (unitarySU 2 n K 3)) := by
  let L := MulAction.stabilizer (unitarySU 2 n K 3) F.v
  have hTL : T ≤ L := fun t ht => MulAction.mem_stabilizer_iff.2 (F.smul_v ⟨t, ht⟩)
  have h1 : N.subgroupOf L ≤ Subgroup.normalizer ((T.subgroupOf L) : Set ↥L) := by
    refine (Subgroup.map_le_map_iff_of_injective (f := ψ.toMonoidHom) ψ.injective).mp ?_
    rwa [Subgroup.map_equiv_normalizer_eq, hmap]
  intro g hgN
  have hgL : g ∈ L := hNL hgN
  have hmem : (⟨g, hgL⟩ : ↥L) ∈
      (Subgroup.normalizer (T : Set (unitarySU 2 n K 3))).subgroupOf L := by
    rw [Subgroup.subgroupOf_normalizer_eq hTL]
    exact h1 (by rw [Subgroup.mem_subgroupOf]; exact hgN)
  rwa [Subgroup.mem_subgroupOf] at hmem

private theorem eq_stabilizer_of_map_eq_top {h : UnitaryFieldData 2 n K}
    {F : SU3TorusFrame h T} {N : Subgroup (unitarySU 2 n K 3)}
    (hNL : N ≤ MulAction.stabilizer (unitarySU 2 n K 3) F.v) {F' : Type} [Field F']
    {ψ : ↥(MulAction.stabilizer (unitarySU 2 n K 3) F.v) ≃* SL(2, F')}
    (hN' : (N.subgroupOf (MulAction.stabilizer (unitarySU 2 n K 3) F.v)).map ψ.toMonoidHom = ⊤) :
    N = MulAction.stabilizer (unitarySU 2 n K 3) F.v := by
  let L := MulAction.stabilizer (unitarySU 2 n K 3) F.v
  refine le_antisymm hNL fun g hgL => ?_
  have hmem : ψ ⟨g, hgL⟩ ∈ (N.subgroupOf L).map ψ.toMonoidHom := by
    rw [hN']
    exact Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp ((Subgroup.mem_map_iff_mem ψ.injective).mp hmem)

private theorem exists_isPGroup_le_normalizer {h : UnitaryFieldData 2 n K}
    {F : SU3TorusFrame h T} {N : Subgroup (unitarySU 2 n K 3)}
    (hNL : N ≤ MulAction.stabilizer (unitarySU 2 n K 3) F.v) {F' : Type} [Field F']
    {ψ : ↥(MulAction.stabilizer (unitarySU 2 n K 3) F.v) ≃* SL(2, F')}
    {P' : Subgroup SL(2, F')}
    (hP'N : P' ≤ (N.subgroupOf (MulAction.stabilizer (unitarySU 2 n K 3) F.v)).map ψ.toMonoidHom)
    (hN'P : (N.subgroupOf (MulAction.stabilizer (unitarySU 2 n K 3) F.v)).map ψ.toMonoidHom ≤
      Subgroup.normalizer (P' : Set SL(2, F')))
    (hP2 : IsPGroup 2 P') (hPne : P' ≠ ⊥) :
    ∃ P : Subgroup (unitarySU 2 n K 3), P ≤ N ∧ P ≠ ⊥ ∧ IsPGroup 2 P ∧
      N ≤ Subgroup.normalizer (P : Set (unitarySU 2 n K 3)) := by
  let L := MulAction.stabilizer (unitarySU 2 n K 3) F.v
  let P : Subgroup (unitarySU 2 n K 3) := (P'.comap ψ.toMonoidHom).map L.subtype
  have hPL : P ≤ L := Subgroup.map_subtype_le _
  have hPsub : P.subgroupOf L = P'.comap ψ.toMonoidHom :=
    Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  have hNP : N.subgroupOf L ≤ Subgroup.normalizer (P'.comap ψ.toMonoidHom : Set ↥L) := by
    refine (Subgroup.map_le_map_iff_of_injective (f := ψ.toMonoidHom) ψ.injective).mp ?_
    rw [Subgroup.map_equiv_normalizer_eq, Subgroup.map_comap_eq_self_of_surjective ψ.surjective]
    exact hN'P
  refine ⟨P, ?_, ?_, ?_, ?_⟩
  · rintro x ⟨y, hy, rfl⟩
    exact Subgroup.mem_subgroupOf.mp
      ((Subgroup.mem_map_iff_mem ψ.injective).mp (hP'N (Subgroup.mem_comap.mp hy)))
  · intro hbot
    change (P'.comap ψ.toMonoidHom).map L.subtype = ⊥ at hbot
    rw [Subgroup.map_eq_bot_iff_of_injective (H := P'.comap ψ.toMonoidHom) (f := L.subtype)
      L.subtype_injective] at hbot
    have h : P'.comap ψ.toMonoidHom = (⊥ : Subgroup SL(2, F')).comap ψ.toMonoidHom := by
      rw [hbot, MonoidHom.comap_bot]
      exact ((MonoidHom.ker_eq_bot_iff ψ.toMonoidHom).mpr ψ.injective).symm
    exact hPne ((Subgroup.comap_injective ψ.surjective).eq_iff.mp h)
  · exact (hP2.comap_of_injective ψ.toMonoidHom ψ.injective).map L.subtype
  · intro g hgN
    have hgL : g ∈ L := hNL hgN
    have hmem : (⟨g, hgL⟩ : ↥L) ∈
        (Subgroup.normalizer (P : Set (unitarySU 2 n K 3))).subgroupOf L := by
      rw [Subgroup.subgroupOf_normalizer_eq hPL, hPsub]
      exact hNP (by rw [Subgroup.mem_subgroupOf]; exact hgN)
    rwa [Subgroup.mem_subgroupOf] at hmem

theorem le_normalizer_or_eq_or_exists_isPGroup {h : UnitaryFieldData 2 n K} (hn : 2 ≤ n)
    (F : SU3TorusFrame h T) (hT : Nat.card T = 2 ^ n - 1) {N : Subgroup (unitarySU 2 n K 3)}
    (hTN : T ≤ N) (hNL : N ≤ MulAction.stabilizer (unitarySU 2 n K 3) F.v) :
    N ≤ Subgroup.normalizer (T : Set (unitarySU 2 n K 3)) ∨
      N = MulAction.stabilizer (unitarySU 2 n K 3) F.v ∨
      ∃ P : Subgroup (unitarySU 2 n K 3), P ≤ N ∧ P ≠ ⊥ ∧ IsPGroup 2 P ∧
        N ≤ Subgroup.normalizer (P : Set (unitarySU 2 n K 3)) := by
  let L := MulAction.stabilizer (unitarySU 2 n K 3) F.v
  have := h.finite
  have : Finite ↥L := inferInstance
  have hTL : T ≤ L := fun t ht => MulAction.mem_stabilizer_iff.2 (F.smul_v ⟨t, ht⟩)
  have hIsL2 := isL2_of_forall_mem_iff_mulVec_eq h hn F.stdHermForm_v_v F.stdHermForm_e_e
    F.stdHermForm_f_f F.stdHermForm_e_f F.stdHermForm_e_v F.stdHermForm_f_v (L := L) fun g => by
      rw [MulAction.mem_stabilizer_iff, unitarySU_smul_def h, Matrix.mulVecLin_apply]
  obtain ⟨F', hField, hFin, hChar, hFcard, ⟨e⟩⟩ := TorusQS.exists_sl2_of_isL2 hIsL2
  let := hField
  let := hFin
  let := hChar
  have hTbot : T ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hT
    have h4 : 4 ≤ 2 ^ n :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot T).mpr hTbot
  obtain ⟨t₀, ht₀T, ht₀1⟩ := Subgroup.exists_ne_one_of_nontrivial T
  let d : ↥L := ⟨t₀, hTL ht₀T⟩
  have hd1 : d ≠ 1 := fun hd => ht₀1 (by simpa [d] using congrArg Subtype.val hd)
  have hd : d ^ (Nat.card F' - 1) = 1 := by
    have hpow : (⟨t₀, ht₀T⟩ : T) ^ (2 ^ n - 1) = 1 := by
      apply F.χ_injective
      rw [map_pow, map_one]
      exact Units.ext (by simpa using F.χ_pow (⟨t₀, ht₀T⟩ : T))
    have hpow' : t₀ ^ (2 ^ n - 1) = 1 := by
      simpa using congrArg (fun x : T => (x : unitarySU 2 n K 3)) hpow
    rw [hFcard]
    exact Subtype.ext (by simpa [d] using hpow')
  obtain ⟨ψ, -, -, -, hC⟩ :=
    CFSG.LocalAnalysis.EvenBN.Common.exists_mulEquiv_map_centralizer_zpowers e hd1 hd
  rw [TorusQS.torusSL_eq_torus] at hC
  have hCeq := centralizer_zpowers_eq_subgroupOf F hT ψ hFcard
    (d := d) (by simpa [d] using ht₀T) hC
  have hTmap : (T.subgroupOf L).map ψ.toMonoidHom = CFSG.CGT.Timmesfeld75.torus F' := by
    rw [← hCeq, hC]
  have hT'le : T.subgroupOf L ≤ N.subgroupOf L := Subgroup.subgroupOf_mono L hTN
  have htorus_le : CFSG.CGT.Timmesfeld75.torus F' ≤ (N.subgroupOf L).map ψ.toMonoidHom := by
    rw [← hTmap]
    exact Subgroup.map_mono hT'le
  have h4 : 4 ≤ Nat.card F' := by
    rw [hFcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  by_cases hO : ∀ P' : Subgroup SL(2, F'),
      P' ≤ (N.subgroupOf L).map ψ.toMonoidHom →
      (N.subgroupOf L).map ψ.toMonoidHom ≤ Subgroup.normalizer (P' : Set SL(2, F')) →
      IsPGroup 2 P' → P' = ⊥
  · rcases CFSG.RankThree.GF2n.Smith81.SL2Torus.le_normalizer_torus_or_eq_top h4 htorus_le hO
      with hle | htop
    · exact Or.inl (le_normalizer_of_le_normalizer_map hNL hTmap hle)
    · exact Or.inr (Or.inl (eq_stabilizer_of_map_eq_top hNL htop))
  · push Not at hO
    obtain ⟨P', hP'N, hN'P, hP'2, hP'ne⟩ := hO
    exact Or.inr (Or.inr (exists_isPGroup_le_normalizer hNL hP'N hN'P hP'2 hP'ne))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU3TorusIrred

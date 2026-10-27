module

public import CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocalRealizers
public import CFSG.Open.LocalVocabulary
import CFSG.GroupTheory.UniqueElemSylow
import CFSG.GroupTheory.WeirSylow.UniqueE27Orthogonal
import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutClassicalOmMinus
import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalBasic
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.ClassicalInvolution.Orders.OrthogonalCount
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.StandardType

open CFSG.Open
open CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal (omegaMinus8)

namespace B48Om

private lemma conj_mul_conj_apply {G : Type*} [Group G] (h n a : G) :
    MulAut.conj (h * n * h⁻¹) (MulAut.conj h a) = MulAut.conj h (MulAut.conj n a) := by
  simp only [MulAut.conj_apply]
  group

private theorem card_E_eq_27 {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4)
    {b c : K} (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {E : Subgroup ↥(omegaMinus8 K b c)}
    (hE : IsElemAbelian 3 E)
    (hself : ∀ g : ↥(omegaMinus8 K b c), g ∈ Subgroup.centralizer (E : Set ↥(omegaMinus8 K b c)) →
      g ^ 3 = 1 → g ∈ E) :
    Nat.card E = 27 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : NeZero 3 := ⟨by norm_num⟩
  let H : Subgroup (GL CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal.OmegaIdx K) := omegaMinus8 K b c
  set E₁ : Subgroup (GL CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal.OmegaIdx K) := E.map H.subtype with hE₁
  have hE₁_ea : IsElemAbelian 3 E₁ := by
    rw [hE₁]
    exact CFSG.SectionRank.isElemAbelian_map hE H.subtype
  have hE₁_le_H : E₁ ≤ H := by
    rintro _ ⟨e, he, rfl⟩
    exact e.2
  have hH_le_O : H ≤ CFSG.Assembly.LargeEvenOrthGroup (StatedQuadMinus 4 K b c) := by
    change omegaMinus8 K b c ≤ CFSG.Assembly.LargeEvenOrthGroup (StatedQuadMinus 4 K b c)
    exact TableBOrth.omega_le_orth _
  have hE₁_O : E₁ ≤ CFSG.Assembly.LargeEvenOrthGroup (StatedQuadMinus 4 K b c) := hE₁_le_H.trans hH_le_O
  have h3dvd : (3 : ℕ) ∣ Nat.card K - 1 := by norm_num [hK]
  obtain ⟨ζ, hζo, hζ, _hζ1, _hζsq⟩ :=
    TableBOrth.exists_zeta (K := K) (p := 3) Nat.prime_three (by norm_num) h3dvd
  obtain ⟨g, hgO, χ, hχ⟩ :=
    OrdPOm.exists_orth_conj_minus_le (K := K) (n := 4) (p := 3) (b := b) (c := c)
      (by norm_num : (3 : ℕ) ≠ 2) hζo hbc (by norm_num : 1 ≤ 4) hE₁_O hE₁_ea
  set T : Subgroup (GL CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal.OmegaIdx K) := (OrdPOm.minusTorusGL (K := K) (m := 3) hζ).range with hT
  have hT_ea : IsElemAbelian 3 T := by
    rw [hT]
    exact OrdPOm.isElemAbelian_range_minusTorusGL hζ
  have hT_card : Nat.card T = 27 := by
    rw [hT, OrdPOm.card_range_minusTorusGL hζ hζo]
    norm_num
  have hT_le_H : T ≤ H := by
    change T ≤ omegaMinus8 K b c
    intro a ha
    rw [hT] at ha
    obtain ⟨f, rfl⟩ := ha
    exact OrdPOm.minusTorusGL_mem_omega (n := 4) hζ (by decide) f
  have hζprim : IsPrimitiveRoot ζ 3 := hζo ▸ IsPrimitiveRoot.orderOf ζ
  have hmem : ∀ x : E₁, g * (x : GL CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal.OmegaIdx K) * g⁻¹ ∈ T := by
    intro x
    have hx3 : x ^ 3 = 1 := Subtype.ext (hE₁_ea.2 (x : GL CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal.OmegaIdx K) x.2)
    have hroot : ∀ k, χ k x ∈ rootsOfUnity 3 K := by
      intro k
      exact (mem_rootsOfUnity 3 (χ k x)).mpr (by rw [← map_pow, hx3, map_one])
    choose nn _ hn using fun k => hζprim.eq_pow_of_mem_rootsOfUnity (hroot k)
    have hx_eq : g * (x : GL CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal.OmegaIdx K) * g⁻¹ =
        OrdPOm.minusTorusGL (K := K) (m := 3) hζ
          (fun k => Multiplicative.ofAdd ((nn k : ℕ) : ZMod 3)) := by
      have hfg : (fun k => χ k x) =
          (fun k => TableBSymp.zmodPowHom hζ (Multiplicative.ofAdd ((nn k : ℕ) : ZMod 3))) := by
        funext k
        rw [TableBSymp.zmodPowHom_natCast]
        exact (hn k).symm
      rw [hχ x, OrdPOm.minusTorusGL_apply, hfg]
    rw [hx_eq, hT]
    exact ⟨_, rfl⟩
  set Y : Subgroup (GL CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal.OmegaIdx K) := T.map (MulAut.conj g⁻¹).toMonoidHom with hY
  have hY_ea : IsElemAbelian 3 Y := by
    rw [hY]
    exact CFSG.SectionRank.isElemAbelian_map hT_ea (MulAut.conj g⁻¹).toMonoidHom
  have hY_le_H : Y ≤ H := by
    rw [hY]
    calc T.map (MulAut.conj g⁻¹).toMonoidHom ≤ H.map (MulAut.conj g⁻¹).toMonoidHom :=
          Subgroup.map_mono hT_le_H
      _ = H := TableBOrth.map_conj_omega (Q := StatedQuadMinus 4 K b c) (inv_mem hgO)
  have hE₁_le_Y : E₁ ≤ Y := by
    intro x hx
    refine ⟨g * x * g⁻¹, hmem ⟨x, hx⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  have hY_le_E₁ : Y ≤ E₁ := by
    intro y hy
    have hyH : y ∈ H := hY_le_H hy
    have hcent : (⟨y, hyH⟩ : ↥H) ∈ Subgroup.centralizer (E : Set ↥H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      apply Subtype.ext
      have heE₁ : (e : GL CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal.OmegaIdx K) ∈ E₁ := ⟨e, he, rfl⟩
      exact IsElemAbelian.comm hY_ea (a := (e : GL CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal.OmegaIdx K)) (b := y) (hE₁_le_Y heE₁) hy
    have hcube : (⟨y, hyH⟩ : ↥H) ^ 3 = 1 := by
      apply Subtype.ext
      simpa using hY_ea.2 y hy
    exact ⟨⟨y, hyH⟩, hself ⟨y, hyH⟩ hcent hcube, rfl⟩
  have hE₁_eq_Y : E₁ = Y := le_antisymm hE₁_le_Y hY_le_E₁
  have hcardE₁ : Nat.card E = Nat.card E₁ := by
    rw [hE₁]
    exact (Subgroup.card_map_of_injective H.subtype_injective).symm
  have hcardY : Nat.card Y = Nat.card T := by
    rw [hY]
    exact Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  calc Nat.card E = Nat.card E₁ := hcardE₁
    _ = Nat.card Y := by rw [hE₁_eq_Y]
    _ = Nat.card T := hcardY
    _ = 27 := hT_card

theorem exists_signedRealizers {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4)
    {b c : K} (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {E : Subgroup ↥(omegaMinus8 K b c)}
    (hE : IsElemAbelian 3 E)
    (hself : ∀ g : ↥(omegaMinus8 K b c), g ∈ Subgroup.centralizer (E : Set ↥(omegaMinus8 K b c)) →
      g ^ 3 = 1 → g ∈ E) :
    ∃ s : Equiv.Perm (Fin 3) × (Fin 3 → (ZMod 3)ˣ) → ↥(omegaMinus8 K b c),
      (∀ i, s i ∈ Subgroup.normalizer (E : Set ↥(omegaMinus8 K b c))) ∧
        ∀ i j, (∀ e ∈ E, s i * e * (s i)⁻¹ = s j * e * (s j)⁻¹) → i = j := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : (3 : K) ≠ 0 := by
    intro h
    have hdvd : (2 : ℕ) ∣ 3 := (CharP.cast_eq_zero_iff K 2 3).mp h
    norm_num at hdvd
  let A₀ : Subgroup ↥(omegaMinus8 K b c) :=
    (CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal.c₀ h3 hbc).range
  have hA₀_ea : IsElemAbelian 3 A₀ := by
    dsimp only [A₀]
    rw [MonoidHom.range_eq_map]
    refine CFSG.SectionRank.isElemAbelian_map ?_
      (CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal.c₀ h3 hbc)
    refine ⟨isMulCommutative_iff.mpr ?_, ?_⟩
    · intro a b
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact mul_comm _ _
    · intro x _
      exact TableBSymp.pow_card_eq_one_zmod (m := 3) (p := 3)
        (x : Multiplicative (Fin 3 → ZMod 3))
  have hA₀_card : Nat.card A₀ = 3 ^ 3 := by
    dsimp only [A₀]
    rw [MonoidHom.range_eq_map,
      Subgroup.card_map_of_injective
        (CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal.c₀_injective h3 hbc),
      Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fin,
      Nat.card_zmod]
  have hE_card : Nat.card E = 3 ^ 3 := by
    rw [card_E_eq_27 hK hbc hE hself]
    norm_num
  obtain ⟨hconj, hEconj⟩ :=
    CFSG.GroupTheory.UniqueElemSylow.exists_conj_eq
      (CFSG.GroupTheory.WeirSylow.uniqueElemSylow_statedOmega_quadMinus_four K hbc
        (by rw [hK]; decide))
      hA₀_ea hA₀_card hE hE_card
  choose n hn using fun (i : Equiv.Perm (Fin 3) × (Fin 3 → (ZMod 3)ˣ)) =>
    CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal.exists_conj_c₀_signedPerm
      h3 hbc i.1 (fun k => (i.2 k : ZMod 3)) (fun k => (i.2 k).ne_zero)
  let s : Equiv.Perm (Fin 3) × (Fin 3 → (ZMod 3)ˣ) → ↥(omegaMinus8 K b c) :=
    fun i => hconj * n i * hconj⁻¹
  refine ⟨s, ?_, ?_⟩
  · intro i
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨e, he, rfl⟩
      rw [hEconj] at he ⊢
      obtain ⟨a, ha, rfl⟩ := he
      dsimp only [A₀] at ha ⊢
      obtain ⟨v, rfl⟩ := ha
      refine ⟨n i * CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal.c₀ h3 hbc v *
        (n i)⁻¹, ?_, ?_⟩
      · rw [hn i v]
        exact ⟨_, rfl⟩
      · have hsub : MulAut.conj hconj
              (n i * CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal.c₀ h3 hbc v *
                (n i)⁻¹) =
            MulAut.conj (s i) (MulAut.conj hconj
              (CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal.c₀ h3 hbc v)) := by
          dsimp only [s]
          rw [conj_mul_conj_apply]
          rfl
        exact hsub
    · rw [Subgroup.card_map_of_injective (MulAut.conj (s i)).injective]
  · intro i j hij
    have hA : ∀ v : Multiplicative (Fin 3 → ZMod 3),
        MulAut.conj (n i) (CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal.c₀ h3 hbc v) =
          MulAut.conj (n j) (CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal.c₀ h3 hbc v) := by
      intro v
      have hmem : MulAut.conj hconj
          (CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal.c₀ h3 hbc v) ∈ E := by
        rw [hEconj]
        exact ⟨CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal.c₀ h3 hbc v,
          ⟨v, rfl⟩, rfl⟩
      have hh := hij _ hmem
      have hh' : MulAut.conj (s i) (MulAut.conj hconj
            (CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal.c₀ h3 hbc v)) =
          MulAut.conj (s j) (MulAut.conj hconj
            (CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal.c₀ h3 hbc v)) := by
        simpa only [MulAut.conj_apply] using hh
      dsimp only [s] at hh'
      rw [conj_mul_conj_apply, conj_mul_conj_apply] at hh'
      exact (MulAut.conj hconj).injective hh'
    have hfun : ∀ v : Multiplicative (Fin 3 → ZMod 3),
        Multiplicative.ofAdd (fun k => (i.2 k : ZMod 3) * Multiplicative.toAdd v (i.1 k)) =
        Multiplicative.ofAdd (fun k => (j.2 k : ZMod 3) * Multiplicative.toAdd v (j.1 k)) := by
      intro v
      have h1 : CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal.c₀ h3 hbc
            (Multiplicative.ofAdd (fun k => (i.2 k : ZMod 3) *
              Multiplicative.toAdd v (i.1 k))) =
          CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal.c₀ h3 hbc
            (Multiplicative.ofAdd (fun k => (j.2 k : ZMod 3) *
              Multiplicative.toAdd v (j.1 k))) := by
        rw [← hn i v, ← hn j v]
        simpa only [MulAut.conj_apply] using hA v
      exact CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal.c₀_injective h3 hbc h1
    have hcoord : ∀ (v : Fin 3 → ZMod 3) (k : Fin 3),
        (i.2 k : ZMod 3) * v (i.1 k) = (j.2 k : ZMod 3) * v (j.1 k) := by
      intro v k
      have := congrFun (Multiplicative.ofAdd.injective (hfun (Multiplicative.ofAdd v))) k
      simpa using this
    have hσ : i.1 = j.1 := by
      apply Equiv.ext
      intro k
      by_contra hne
      have h1 := hcoord (Pi.single (i.1 k) 1) k
      rw [Pi.single_eq_same, mul_one, Pi.single_eq_of_ne' hne, mul_zero] at h1
      exact (i.2 k).ne_zero h1
    have hε : i.2 = j.2 := by
      funext k
      apply Units.ext
      have hk : j.1 k = i.1 k :=
        congrFun (congrArg (fun e : Equiv.Perm (Fin 3) => (e : Fin 3 → Fin 3)) hσ.symm) k
      have h1 := hcoord (Pi.single (i.1 k) 1) k
      simp only [hk, Pi.single_eq_same, mul_one] at h1
      exact h1
    exact Prod.ext hσ hε

end B48Om

end CFSG.StandardType

end

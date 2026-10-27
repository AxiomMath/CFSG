module

public import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalBorelAut
public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34DCTransport
import CFSG.Quasithin.Recognition.St84.Gen.L3qAmalExtend
import CFSG.LieType.Chevalley.OddF4G2AutomorphismNormalForm
public import CFSG.GH74.QTGen4.DSGen4.OpenLeaves
public import CFSG.GH74.QTGen4.DSGen4.Statements
public import CFSG.GH74.QTGen4.U42.AmalgamGen
public import CFSG.GH74.QTGen4.U42.GSidePairCore
public import CFSG.GH74.QTGen4.U42.GSidePairData
public import CFSG.GH74.QTGen4.U42.MSplitB
public import CFSG.GH74.QTGen4.U42.ModelP1
public import CFSG.GH74.QTGen4.U42.ModelPairCore
public import CFSG.GH74.QTGen4.U42.StubA4b
public import CFSG.GH74.QTGen4.U42.StubA4h
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import CFSG.Quasithin.Background.F3
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.Recognition.F4Moufang
public import CFSG.Quasithin.Recognition.F4Thirtyone
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Model
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Pair5
public import CFSG.Sporadic.Schreier.J4SCommGenBase1
public import CFSG.Sporadic.Schreier.J4SLocalNodes

public noncomputable section

namespace CFSG.Quasithin.F112R.St84

open scoped Pointwise

private theorem mem_iff_of_map_eq {Γ : Type*} [Group Γ] {H : Subgroup Γ} {α : MulAut Γ}
    (h : H.map α.toMonoidHom = H) (b : Γ) : b ∈ H ↔ α b ∈ H := by
  constructor
  · intro hb
    rw [← h]
    exact ⟨b, hb, rfl⟩
  · intro hb
    rw [← h] at hb
    obtain ⟨c, hc, hcb⟩ := hb
    simp only [MulEquiv.coe_toMonoidHom] at hcb
    rwa [← α.injective hcb]

theorem exists_conj_mulAut_preserves_complement {Γ : Type*} [Group Γ] [Finite Γ]
    {U T : Subgroup Γ} [hUn : U.Normal] (hU : IsPGroup 2 U) (hT : Odd (Nat.card T))
    (hUT : U.IsComplement' T) (σ : MulAut Γ) :
    (∀ b, b ∈ U ↔ σ b ∈ U) ∧ ∃ e ∈ U, ∀ b, b ∈ T ↔ (MulAut.conj e * σ) b ∈ T := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ¬ 2 ∣ U.index := by
    rw [hUT.symm.index_eq_card]
    exact hT.not_two_dvd_nat
  have key : ∀ α : MulAut Γ, U.map α.toMonoidHom ≤ U := by
    intro α
    haveI : (U.map α.toMonoidHom).Normal := hUn.map α.toMonoidHom α.surjective
    have h := (hU.map α.toMonoidHom).le_sylow_of_normal (hU.toSylow hidx)
    rwa [IsPGroup.toSylow_coe] at h
  have hσU : U.map σ.toMonoidHom = U :=
    le_antisymm (key σ) fun x hx => ⟨σ.symm x, key σ.symm ⟨x, hx, rfl⟩, by simp⟩
  refine ⟨mem_iff_of_map_eq hσU, ?_⟩
  let Y : Subgroup Γ := T.map σ.toMonoidHom
  have hdisj : Disjoint U Y := by
    have e := congrArg (fun S : Subgroup Γ => S.map σ.toMonoidHom) (disjoint_iff.mp hUT.disjoint)
    rw [Subgroup.map_inf _ _ _ σ.injective, hσU, Subgroup.map_bot] at e
    exact disjoint_iff.mpr e
  have htop : U ⊔ Y = ⊤ := by
    have e := congrArg (fun S : Subgroup Γ => S.map σ.toMonoidHom) hUT.sup_eq_top
    rw [Subgroup.map_sup, hσU, Subgroup.map_top, MonoidHom.range_eq_top.mpr σ.surjective] at e
    exact e
  have hUY : U.IsComplement' Y :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj (by
      rw [← Subgroup.normal_mul, htop]
      simp)
  have hcop : Nat.Coprime (Nat.card U) U.index := by
    obtain ⟨k, hk⟩ := hU.exists_card_eq
    rw [hk, hUT.symm.index_eq_card]
    exact (Nat.coprime_two_left.2 hT).pow_left k
  obtain ⟨g, hg⟩ := CFSG.GorensteinWalter.SchurZassenhaus.complements_conjugate_of_coprime
    U Y T hUn hUY hUT hcop
  obtain ⟨⟨u, y⟩, huy⟩ := hUY.2 g
  have huy' : (u : Γ) * (y : Γ) = g := by simpa using huy
  have hc : (MulAut.conj g).toMonoidHom =
      (MulAut.conj (u : Γ)).toMonoidHom.comp (MulAut.conj (y : Γ)).toMonoidHom := by
    ext x
    simp [← huy', MulAut.conj_apply, mul_assoc]
  have hyY : Y.map (MulAut.conj (y : Γ)).toMonoidHom = Y :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).mp (Subgroup.le_normalizer y.2)
  have hmap : Y.map (MulAut.conj g).toMonoidHom = Y.map (MulAut.conj (u : Γ)).toMonoidHom := by
    rw [hc, ← Subgroup.map_map, hyY]
  have hcomp : (MulAut.conj (u : Γ) * σ).toMonoidHom =
      (MulAut.conj (u : Γ)).toMonoidHom.comp σ.toMonoidHom := by
    ext x
    rfl
  have hτ : T.map (MulAut.conj (u : Γ) * σ).toMonoidHom = T := by
    rw [hcomp, ← Subgroup.map_map]
    change Y.map (MulAut.conj (u : Γ)).toMonoidHom = T
    rw [← hmap]
    exact hg.symm
  exact ⟨u, u.2, mem_iff_of_map_eq hτ⟩

namespace G2q

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open
open CFSG.GH74.QTGen4.DSGen4.L34 (DCProp)
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2 (i1)

variable {K : Type} [Field K]

section Embedding

variable {Γ : Type*} [Group Γ] (ι : Γ →* ModGL Tag.G2 K)

private theorem comap_posUnipotent_normal
    (hrange : ∀ g, g ∈ borelGroup Tag.G2 K ↔ ∃ b, ι b = g) :
    ((posUnipotent Tag.G2 K).comap ι).Normal := by
  have hBN : borelGroup Tag.G2 K ≤
      Subgroup.normalizer (posUnipotent Tag.G2 K : Set (ModGL Tag.G2 K)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).1
      (triangular_borel_structure.{0, 0} Tag.G2 K).2.2.2.2.2.2.2.2.1
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
  exact (Subgroup.mem_normalizer_iff.1 (hBN ((hrange _).2 ⟨g, rfl⟩)) (ι n)).1 hn

private theorem isPGroup_comap_posUnipotent [Finite K] (hι : Function.Injective ι) {f : ℕ}
    (hK : Nat.card K = 2 ^ f) : IsPGroup 2 ((posUnipotent Tag.G2 K).comap ι) := by
  have hU : IsPGroup 2 (posUnipotent Tag.G2 K) :=
    IsPGroup.of_card
      (n := f * {α : Fin Tag.G2.rank → ℤ | IsRoot Tag.G2 α ∧ 0 < height α}.ncard)
      (by rw [card_posUnipotent, hK, ← pow_mul])
  exact hU.comap_of_injective ι hι

private theorem odd_card_comap_torusGroup [Finite K] (hι : Function.Injective ι)
    (hrange : ∀ g, g ∈ borelGroup Tag.G2 K ↔ ∃ b, ι b = g) {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f) : Odd (Nat.card ((torusGroup Tag.G2 K).comap ι)) := by
  have hle : torusGroup Tag.G2 K ≤ ι.range := fun t ht => by
    obtain ⟨b, hb⟩ := (hrange t).1 (Subgroup.mem_sup_left ht)
    exact ⟨b, hb⟩
  rw [← Subgroup.card_map_of_injective hι, Subgroup.map_comap_eq_self hle, card_torusGroup, hK]
  have hodd : Odd (2 ^ f - 1) :=
    Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one
  exact hodd.pow

private theorem isComplement'_comap (hι : Function.Injective ι)
    (hrange : ∀ g, g ∈ borelGroup Tag.G2 K ↔ ∃ b, ι b = g) :
    ((posUnipotent Tag.G2 K).comap ι).IsComplement' ((torusGroup Tag.G2 K).comap ι) := by
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [Subgroup.disjoint_def]
    intro x hxU hxT
    have hx : ι x ∈ torusGroup Tag.G2 K ⊓ posUnipotent Tag.G2 K := ⟨hxT, hxU⟩
    rw [torusGroup_inf_posUnipotent, Subgroup.mem_bot] at hx
    exact hι (by rw [hx, map_one])
  · refine Set.eq_univ_of_forall fun b => ?_
    have hb : ι b ∈ (posUnipotent Tag.G2 K : Set (ModGL Tag.G2 K)) *
        (torusGroup Tag.G2 K : Set (ModGL Tag.G2 K)) := by
      rw [← (triangular_borel_structure.{0, 0} Tag.G2 K).2.2.2.2.2.1]
      exact (hrange _).2 ⟨b, rfl⟩
    obtain ⟨u, hu, t, ht, hut⟩ := hb
    obtain ⟨b₁, hb₁⟩ := (hrange u).1 (Subgroup.mem_sup_right hu)
    obtain ⟨b₂, hb₂⟩ := (hrange t).1 (Subgroup.mem_sup_left ht)
    refine ⟨b₁, ?_, b₂, ?_, hι ?_⟩
    · change ι b₁ ∈ posUnipotent Tag.G2 K
      rw [hb₁]
      exact hu
    · change ι b₂ ∈ torusGroup Tag.G2 K
      rw [hb₂]
      exact ht
    · rw [map_mul, hb₁, hb₂]
      exact hut

end Embedding

end G2q

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open
open CFSG.GH74.QTGen4.DSGen4.L34 (DCProp)
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2 (i1)
open G2q

variable {K : Type} [Field K]

theorem dcProp_g2 [Finite K] [CharP K 2] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hf : 3 ≤ f) : DCProp (g2ParA K) (g2ParB K) := by
  classical
  refine dcProp_of_forall_exists_extend fun σ hσ => ?_
  let ι : ↥(g2ParA K ⊓ g2ParB K) →* ModGL Tag.G2 K :=
    (adjointGroup Tag.G2 K).subtype.comp (g2ParA K ⊓ g2ParB K).subtype
  have hι : Function.Injective ι := Subtype.val_injective.comp Subtype.val_injective
  have hrange : ∀ g, g ∈ borelGroup Tag.G2 K ↔ ∃ b, ι b = g := by
    intro g
    constructor
    · intro hg
      exact ⟨⟨⟨g, borelGroup_le_adjointGroup' hg⟩, mem_g2ParA_inf_g2ParB.2 hg⟩, rfl⟩
    · rintro ⟨b, rfl⟩
      exact mem_g2ParA_inf_g2ParB.1 b.2
  haveI := finite_modGL (τ := Tag.G2) (K := K)
  haveI hUn := comap_posUnipotent_normal ι hrange
  obtain ⟨hσU, e, -, heT⟩ := exists_conj_mulAut_preserves_complement
    (isPGroup_comap_posUnipotent ι hι hK) (odd_card_comap_torusGroup ι hι hrange hK (by omega))
    (isComplement'_comap ι hι hrange) σ
  let τ : MulAut ↥(g2ParA K ⊓ g2ParB K) := MulAut.conj e * σ
  have hτb : ∀ b, ι (τ b) = ι e * ι (σ b) * (ι e)⁻¹ := fun b => by
    change ι (e * σ b * e⁻¹) = _
    rw [map_mul, map_mul, map_inv]
  have heB : ι e ∈ borelGroup Tag.G2 K := (hrange _).2 ⟨e, rfl⟩
  have hU : ∀ b, ι b ∈ posUnipotent Tag.G2 K ↔ ι (τ b) ∈ posUnipotent Tag.G2 K := by
    intro b
    have h1 : ι b ∈ posUnipotent Tag.G2 K ↔ ι (σ b) ∈ posUnipotent Tag.G2 K := hσU b
    have hBN : borelGroup Tag.G2 K ≤
        Subgroup.normalizer (posUnipotent Tag.G2 K : Set (ModGL Tag.G2 K)) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).1
        (triangular_borel_structure.{0, 0} Tag.G2 K).2.2.2.2.2.2.2.2.1
    rw [hτb]
    exact h1.trans (Subgroup.mem_normalizer_iff.1 (hBN heB) _)
  have hT : ∀ b, ι b ∈ torusGroup Tag.G2 K ↔ ι (τ b) ∈ torusGroup Tag.G2 K := heT
  have hQ : ∀ b, ι b ∈ parabolicRadical Tag.G2 K {i1} ↔
      ι (τ b) ∈ parabolicRadical Tag.G2 K {i1} := by
    intro b
    have h1 : ι b ∈ parabolicRadical Tag.G2 K {i1} ↔ ι (σ b) ∈ parabolicRadical Tag.G2 K {i1} :=
      (mem_pCoreOf_g2ParA_iff (y := (b : ↥(adjointGroup Tag.G2 K)))).symm.trans
        ((hσ b).trans mem_pCoreOf_g2ParA_iff)
    rw [hτb]
    exact h1.trans (Subgroup.mem_normalizer_iff.1
      (borelGroup_le_normalizer_parabolicRadical {i1} heB) _)
  obtain ⟨ρ, s, t, hρ⟩ := exists_eq_conj_entrywise_of_mulAut ι hι hrange hK hf τ hU hT hQ
  let c : ↥(adjointGroup Tag.G2 K) :=
    (e : ↥(adjointGroup Tag.G2 K))⁻¹ * ⟨dT s t, dT_mem_adjointGroup s t⟩
  have hc : (c : ModGL Tag.G2 K) = (ι e)⁻¹ * dT s t := rfl
  let Ψ : MulAut ↥(adjointGroup Tag.G2 K) := MulAut.conj c * exactNormalAut Tag.G2 K 1 ρ 0
  have hΨ : ∀ y : ↥(adjointGroup Tag.G2 K), ((Ψ y : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) =
      (c : ModGL Tag.G2 K) * Units.map (entrywiseHom ρ.toRingHom) (y : ModGL Tag.G2 K) *
        (c : ModGL Tag.G2 K)⁻¹ := by
    intro y
    simp only [Ψ, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
      coe_exactNormalAut_zero, rootDiagUnit_one, one_mul, inv_one, mul_one]
  have hcB : (c : ModGL Tag.G2 K) ∈ borelGroup Tag.G2 K := by
    rw [hc]
    exact mul_mem (inv_mem heB) (dT_mem_borelGroup s t)
  have hpar : ∀ (J : Set (Fin Tag.G2.rank)) (y : ↥(adjointGroup Tag.G2 K)),
      (y : ModGL Tag.G2 K) ∈ parabolicSubgroup Tag.G2 K J ↔
        ((Ψ y : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) ∈ parabolicSubgroup Tag.G2 K J := by
    intro J y
    have hcP : (c : ModGL Tag.G2 K) ∈ parabolicSubgroup Tag.G2 K J :=
      borelGroup_le_parabolicSubgroup J hcB
    rw [hΨ, mul_mem_cancel_right (inv_mem hcP), mul_mem_cancel_left hcP,
      entrywise_mem_parabolicSubgroup_iff]
  refine ⟨Ψ, fun y => ?_, fun y => ?_, fun b => ?_⟩
  · simp only [g2ParA, Subgroup.mem_subgroupOf]
    exact hpar _ y
  · simp only [g2ParB, Subgroup.mem_subgroupOf]
    exact hpar _ y
  · apply Subtype.ext
    rw [hΨ]
    calc (c : ModGL Tag.G2 K) * Units.map (entrywiseHom ρ.toRingHom) (ι b) *
          (c : ModGL Tag.G2 K)⁻¹
        = (ι e)⁻¹ * (dT s t * Units.map (entrywiseHom ρ.toRingHom) (ι b) * (dT s t)⁻¹) *
            ι e := by
          rw [hc]
          group
      _ = ι (σ b) := by
          rw [← hρ b, hτb]
          group

end CFSG.Quasithin.F112R.St84

end

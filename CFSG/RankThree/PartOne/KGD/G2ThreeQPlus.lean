module

public import CFSG.RankThree.PartOne.KGD.G2Abstract
public import CFSG.RankThree.Chevalley.SteinbergBNG2QPlusLocalCore
public import CFSG.LieType.Ree.ExceptionalAutomorphismData

public section

namespace CFSG.RankThree.PartOne.KGD

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.LocalRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.RankThree.QuadraticSL2
  CFSG.RankThree.Classical CFSG.RankThree.PartOne CFSG.RankThree.Chevalley
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups
open CFSG.RankThree.Chevalley.SteinbergBN
open CFSG.LieType.Ree

theorem solvable_normal_qplus (K : Type) [Field K] [Finite K]
    (hKodd : Odd (Nat.card K)) (hK2 : ringChar K ≠ 2) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ Nat.card K + 1) (x : adjointGroup .G2 K) (hxp : orderOf x = p) :
    ∀ V : Subgroup (centralizer ({x} : Set (adjointGroup .G2 K))), V.Normal →
      Group.IsSolvable V →
      (∀ v ∈ V, ∀ w ∈ V, v * w = w * v) ∧ Nat.card {v : V // v ^ 2 = 1} ≤ 4 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hinj :
      Function.Injective (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)) :=
    mulAut_conj_injective_of_center_eq_bot center_adjointGroup_eq_bot
  obtain ⟨K₂, _, _, hdeg, σ, hσ⟩ := exists_quadratic_frobenius hK2
  obtain ⟨g, z, -, -, -, -, -, -, -, ⟨S₀, hS₀T⟩, -, hroot, hTuniq, hcases⟩ :=
    odd_G2_qplus_toral_Sylow_and_fixed_root_centralizers K hKodd hp hp3 hpq K₂ hdeg σ hσ
  have : Module.Finite K K₂ := Module.finite_of_finrank_pos (by omega)
  have hfin : Finite K₂ := Module.finite_of_finite K
  set ψ : ModGL .G2 K →* ModGL .G2 K₂ :=
    (MulAut.conj g).toMonoidHom.comp (baseChangeGL (algebraMap K K₂)) with hψ
  have hψinj : Function.Injective ψ :=
    (MulAut.conj g).injective.comp (baseChangeGL_injective (τ := .G2) (algebraMap K K₂))
  let ε : adjointGroup .G2 K ≃* conjEntrywiseImage K g :=
    (adjointGroup .G2 K).equivMapOfInjective ψ hψinj
  have hPx : IsPGroup p (Subgroup.zpowers (ε x)) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, MulEquiv.orderOf_eq ε x, hxp, pow_one])
  obtain ⟨Q', hQ'⟩ := hPx.exists_le_sylow
  obtain ⟨u, hu⟩ := MulAction.exists_smul_eq (conjEntrywiseImage K g) Q' S₀
  have hux : MulAut.conj u • ε x ∈ (S₀ : Subgroup (conjEntrywiseImage K g)) := by
    have h1 : MulAut.conj u • ε x ∈ MulAut.conj u • (Q' : Subgroup (conjEntrywiseImage K g)) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ (hQ' (Subgroup.mem_zpowers _))
    rwa [← Sylow.coe_subgroup_smul, hu] at h1
  set F : adjointGroup .G2 K →* ModGL .G2 K₂ := (conjEntrywiseImage K g).subtype.comp
    ((MulAut.conj u).toMonoidHom.comp ε.toMonoidHom) with hFdef
  have hF : Function.Injective F := (conjEntrywiseImage K g).subtype_injective.comp
    ((MulAut.conj u).injective.comp ε.injective)
  have hFT : F x ∈ torusGroup .G2 K₂ ⊓ conjEntrywiseImage K g :=
    Subgroup.mem_subgroupOf.1 (hS₀T hux)
  obtain ⟨a, ha, -⟩ := hTuniq _ hFT
  have hFrange : F.range = conjEntrywiseImage K g := by
    rw [hFdef, MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective _
      ((MulAut.conj u).surjective.comp ε.surjective), ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hmapF : (centralizer ({x} : Set (adjointGroup .G2 K))).map F =
      conjEntrywiseImage K g ⊓ centralizer {rootDiagUnit .G2 a} := by
    rw [map_centralizer_singleton_of_injective F hF x, hFrange, ← ha]
  have hTa : rootDiagUnit .G2 a ∈ torusGroup .G2 K₂ ⊓ conjEntrywiseImage K g := ha ▸ hFT
  have hao : orderOf (rootDiagUnit .G2 a) = p := by
    rw [ha, orderOf_injective F hF, hxp]
  by_cases hkerE : rootCharKernel a = ∅
  · obtain ⟨hDT, -, -⟩ := (hcases a hTa hao).1 hkerE
    obtain ⟨φ, hφ⟩ := exists_injective_of_map_le_torusGroup F hF
      (X := centralizer ({x} : Set (adjointGroup .G2 K))) (by
        rw [hmapF, hDT]
        exact inf_le_left)
    exact solvable_normal_abelian_card_le _ (Or.inl ⟨φ, hφ⟩)
  · obtain ⟨α, hα, -, hcomm, hZ, hZH, -⟩ := (hcases a hTa hao).2 hkerE
    obtain ⟨_, -, hQq⟩ := hroot α hα
    obtain ⟨-, hRq, φ, hφ⟩ := derived_centralizer_data_of_map F hF hmapF hcomm hQq hZ hZH
    exact solvable_normal_abelian_card_le _ (Or.inr ⟨hRq, φ, hφ⟩)

section BaseChange

variable {K L : Type} [Field K] [Field L]

@[expose] noncomputable def bcAdj {τ : Tag} (ι : K →+* L) : adjointGroup τ K →* adjointGroup τ L :=
  ((baseChangeGL ι).comp (adjointGroup τ K).subtype).codRestrict (adjointGroup τ L) fun g =>
    baseChangeGL_mem_adjointGroup ι g.2

theorem coe_bcAdj {τ : Tag} (ι : K →+* L) (g : adjointGroup τ K) :
    (bcAdj ι g : ModGL τ L) = baseChangeGL ι (g : ModGL τ K) :=
  rfl

theorem bcAdj_xElement {τ : Tag} (ι : K →+* L) (i : Fin τ.rank) (c : K) :
    bcAdj ι (xElement i c) = xElement i (ι c) :=
  Subtype.ext (baseChangeGL_xUnit _ i c)

theorem bcAdj_yElement {τ : Tag} (ι : K →+* L) (i : Fin τ.rank) (c : K) :
    bcAdj ι (yElement i c) = yElement i (ι c) :=
  Subtype.ext (baseChangeGL_yUnit _ i c)

variable [Finite K] [Finite L] [CharP K ReeTag.G2.prime] [CharP L ReeTag.G2.prime]

theorem finiteExceptionalAut_comp_bcAdj (ι : K →+* L) :
    (ReeTag.G2.finiteExceptionalAut L).toMonoidHom.comp (bcAdj ι) =
      (bcAdj ι).comp (ReeTag.G2.finiteExceptionalAut K).toMonoidHom := by
  refine adjointGroup_hom_ext (fun i c => ?_) fun i c => ?_
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, bcAdj_xElement,
      ReeTag.finiteExceptionalAut_xElement, map_pow]
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, bcAdj_yElement,
      ReeTag.finiteExceptionalAut_yElement, map_pow]

theorem finiteExceptionalAut_pow_bcAdj (ι : K →+* L) (n : ℕ)
    (g : adjointGroup ReeTag.G2.tag K) :
    (ReeTag.G2.finiteExceptionalAut L ^ n) (bcAdj ι g) =
      bcAdj ι ((ReeTag.G2.finiteExceptionalAut K ^ n) g) := by
  induction n generalizing g with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply]
    have h := DFunLike.congr_fun (finiteExceptionalAut_comp_bcAdj ι) g
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h
    rw [h, ih]

end BaseChange

end CFSG.RankThree.PartOne.KGD

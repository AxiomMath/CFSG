module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGNsq2QuotCover
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosAdapterAux
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieEsuAux2
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.RankThree.PartOne.S15K.CentralCover
import CFSG.LieType.Steinberg.CentralExt.SUThree
import CFSG.LieType.Universal.Unitary.Comparison
import CFSG.ClassicalGroups.Unitary.Perfect
import CFSG.ClassicalGroups.Unitary.Finite
public import CFSG.Sporadic.Bridge.ONSurj

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary CFSG.LieType.Steinberg
  CFSG.RankThree.PartOne.S15K Matrix

theorem su_eq_largeEven {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = (2 ^ 1) ^ 2) {n : ℕ} :
    SUid (unitaryInvolution K 2 1) n = LargeEvenSUGroup (Fin n) K (2 ^ 1) := by
  have h2 : LargeEvenSUGroup (Fin n) K (2 ^ 1) = CFSG.Open.StatedSU n (2 ^ 1) K := rfl
  rw [h2]
  exact SUid_eq_statedSU (F := K) (p := 2) (f := 1) hK n

theorem ggNSq2_acts_quot {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = (2 ^ 1) ^ 2) {n : ℕ}
    (hn : 4 ≤ n)
    {Q : Type} [Group Q] {Y : Subgroup Q}
    (η : ↥Y →* LargeEvenProj (LargeEvenSUGroup (Fin n) K (2 ^ 1)))
    (hηker : η.ker ≤ Subgroup.center ↥Y) (ψ₀ : Su K 2 1 n →* ↥Y)
    (hψη : ∀ s, η (ψ₀ s) = LargeEvenProjMk (LargeEvenSUGroup (Fin n) K (2 ^ 1))
      (MulEquiv.subgroupCongr (su_eq_largeEven hK) s))
    {b : Q} (hbY : ∀ y ∈ Y, b * y * b⁻¹ ∈ Y)
    {φ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin n) K (2 ^ 1)))}
    (hφ : φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K (2 ^ 1)))
      (LargeEvenGUSet (Fin n) K (2 ^ 1)))
    (hind : ∀ y y' : ↥Y, (y' : Q) = b⁻¹ * y * b → φ (η y) = η y') :
    ∃ g : GL (Fin n) K, GGInducesUnitary (p := 2) (f := 1) (Y.subtype.comp ψ₀) b g := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, hAgu, hgraph⟩ := hφ
  obtain ⟨g, hgu, hconj⟩ := ggNSLieN3A_gu_rescale hK hAgu
  have hperfSU : Group.IsPerfect (Su K 2 1 n) :=
    isPerfect_SUid (isUnitaryInvolution_unitaryInvolution hK) (by omega)
      (fun h3 => absurd h3 (by omega))
  refine ⟨g, hgu, fun x => ?_⟩
  let c : Su K 2 1 n →* Su K 2 1 n :=
    MonoidHom.mk' (fun x => ⟨g * (x : GL (Fin n) K) * g⁻¹,
      conj_mem_SUid (isUnitaryInvolution_unitaryInvolution hK).invol hgu x.2⟩)
      (by
        intro x y
        apply Subtype.ext
        show g * ((x * y : Su K 2 1 n) : GL (Fin n) K) * g⁻¹ =
          (g * (x : GL (Fin n) K) * g⁻¹) * (g * (y : GL (Fin n) K) * g⁻¹)
        rw [Subgroup.coe_mul]
        group)
  let τ₁ : Su K 2 1 n →* ↥Y :=
    MonoidHom.mk' (fun x => ⟨b * ((ψ₀ x : ↥Y) : Q) * b⁻¹, hbY _ (ψ₀ x).2⟩)
      (by
        intro x y
        apply Subtype.ext
        show b * ((ψ₀ (x * y) : ↥Y) : Q) * b⁻¹ =
          (b * ((ψ₀ x : ↥Y) : Q) * b⁻¹) * (b * ((ψ₀ y : ↥Y) : Q) * b⁻¹)
        rw [map_mul, Subgroup.coe_mul]
        group)
  let τ₂ : Su K 2 1 n →* ↥Y := ψ₀.comp c
  have hmod : ∀ u, η (τ₁ u) = η (τ₂ u) := by
    intro u
    apply φ.injective
    have h1 : φ (η (τ₁ u)) = η (ψ₀ u) :=
      hind (τ₁ u) (ψ₀ u) (by
        show ((ψ₀ u : ↥Y) : Q) = b⁻¹ * (b * ((ψ₀ u : ↥Y) : Q) * b⁻¹) * b
        group)
    have h2 : φ (η (τ₂ u)) = η (ψ₀ u) := by
      have e1 : η (τ₂ u) = LargeEvenProjMk (LargeEvenSUGroup (Fin n) K (2 ^ 1))
          (MulEquiv.subgroupCongr (su_eq_largeEven hK) (c u)) := hψη (c u)
      have e2 : η (ψ₀ u) = LargeEvenProjMk (LargeEvenSUGroup (Fin n) K (2 ^ 1))
          (MulEquiv.subgroupCongr (su_eq_largeEven hK) u) := hψη u
      rw [e1, e2]
      exact hgraph _ _ (hconj (u : GL (Fin n) K)).symm
    exact h1.trans h2.symm
  have heq := eq_of_perfect_of_map_eq η hηker hperfSU τ₁ τ₂ hmod x
  exact ⟨c x, rfl, congrArg Subtype.val heq⟩

namespace NsQuot

variable {G : Type} [Group G] [Finite G] {Q : Type} [Group Q]
variable {p : ℕ} {N : Subgroup G} {f : ↥N →* Q} {L Bs Z : Subgroup G}

theorem ggNSLocalHyp_of_quot [Finite Q] {B : Subgroup G} {x : G} {L' D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L' D J 𝒦) (hD : Datum p N f L Bs Z)
    (hperfL : Group.IsPerfect ↥L) (hcentL : Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) = p)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = (2 ^ 1) ^ 2) {n : ℕ} (hn : 4 ≤ n)
    (hn6 : n ≤ 6) (hdvd : p ∣ 2 ^ 1 + 1) {ψ₀ : Su K 2 1 n →* ↥(img N f L)}
    (hker : ψ₀.ker ≤ Subgroup.center (Su K 2 1 n)) (hsurj : Function.Surjective ψ₀)
    (hacts : GGActsUnitarily (p := 2) (f := 1) ((img N f L).subtype.comp ψ₀) (img N f Bs)) :
    GGNSLocalHyp p (img N f B) (img N f Bs) K 1 n ((img N f L).subtype.comp ψ₀) := by
  have hcfg' : GGConfig p B Bs x L' D J := hcfg.1.1
  have hBBs : B ≤ Bs := hcfg'.2.1.1
  have hp : p.Prime := (ggRouteCfg_prime hcfg).1
  refine ⟨hp, (ggRouteCfg_prime hcfg).2, hK, hdvd, hn, ?_, hD.bstar hcfg'.2.1, ?_,
    Or.inl hn6, ?_, hD.noTr (ggRouteCfg_noTransvection hcfg), hacts⟩
  · intro s hs
    apply hker
    rw [MonoidHom.mem_ker] at hs ⊢
    exact Subtype.ext hs
  · rw [hD.card_img hBBs]
    exact ggNSPosPD_routeCfg_rank hcfg'
  · have hrange : ((img N f L).subtype.comp ψ₀).range = img N f L := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
        Subgroup.range_subtype]
    rw [hrange, hD.cent hperfL hBBs]
    exact hcentL

end NsQuot

end CFSG.StandardType

end

module

public import CFSG.Open.Catalog
public import CFSG.Open.LocalVocabulary
public import Certificates.Certificate113
public import CFSG.LocalAnalysis.WeakClosure81.SuzukiGen
public import CFSG.LocalAnalysis.WeakClosure81.W16PLemmaQSzBA
public import CFSG.LocalAnalysis.WeakClosure81.W16PLemmaQSzBB
public import CFSG.LocalAnalysis.WeakClosure81.W16PLemmaQSzBC
public import CFSG.LocalAnalysis.WeakClosure81.W16PLemmaQSzBD
public import CFSG.Blueprint.SourceExceptionalModels
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.CharacterTheory.Semidihedral.CharacteristicSL2Layer
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.Foundations
public import CFSG.GF2Type.Aschbacher1976
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.LieType.Ree.Duality
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderSuzuki
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderUnitary
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeUC.Asc1930
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.S4Free.Statement
public import CFSG.StronglyEmbedded
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_1_12
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.Walter.Defs
public import Certificates.Certificate43

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open Matrix CFSG.CGT.PushingUpLit.SolKNA CFSG.RankThree.GF2n.SzExplicit
open CFSG.RankThree.S4Free.SzNatural

theorem exists_eq_mulVec_sub_of_normalizer_sz_of_sylow {a : ℕ}
    (ha : 1 ≤ a) (P : Sylow 2 ↥(Sz a))
    {δ : ↥(Sz a) → (Fin 4 → GaloisField 2 (2 * a + 1))}
    (hδ : ∀ x y : ↥(Sz a), δ (x * y) = δ x +
      (((x : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
        Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))) *ᵥ δ y))
    (hδZ : ∀ z ∈ ((P : Subgroup ↥(Sz a)) ⊓
        Subgroup.centralizer ((P : Subgroup ↥(Sz a)) : Set ↥(Sz a))), δ z = 0) :
    ∃ n : Fin 4 → GaloisField 2 (2 * a + 1),
      (∀ z ∈ ((P : Subgroup ↥(Sz a)) ⊓
          Subgroup.centralizer ((P : Subgroup ↥(Sz a)) : Set ↥(Sz a))),
        (((z : ↥(Sz a)) : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
          Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))) *ᵥ n = n) ∧
      ∀ x ∈ Subgroup.normalizer (((P : Subgroup ↥(Sz a)) ⊓
          Subgroup.centralizer ((P : Subgroup ↥(Sz a)) : Set ↥(Sz a))) : Set ↥(Sz a)), δ x =
        (((x : ↥(Sz a)) : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
          Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))) *ᵥ n - n := by
  let mm : ↥(Sz a) →* Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1)) :=
    (Units.coeHom (Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1)))).comp
      (Sz a).subtype
  have hδmm : ∀ x y : ↥(Sz a), δ (x * y) = δ x + mm x *ᵥ δ y := fun x y => hδ x y
  obtain ⟨g, hg⟩ := exists_conj_rootSub a P
  have hδ'Z : ∀ b : GaloisField 2 (2 * a + 1),
      conjCrossed mm δ g (rootSz a 0 b) = 0 := by
    intro b
    have hz : rootSz a 0 b ∈ rootSub a ⊓ Subgroup.centralizer (rootSub a : Set ↥(Sz a)) := by
      rw [rootSub_inf_centralizer (n := a) ha]
      exact (mem_rootCenter (n := a)).mpr ⟨b, rfl⟩
    have hgZ : g * rootSz a 0 b * g⁻¹ ∈ (P : Subgroup ↥(Sz a)) ⊓
        Subgroup.centralizer ((P : Subgroup ↥(Sz a)) : Set ↥(Sz a)) :=
      (inf_centralizer_conj (n := a) g hg (g * rootSz a 0 b * g⁻¹)).mpr (by
        have he : g⁻¹ * (g * rootSz a 0 b * g⁻¹) * g = rootSz a 0 b := by group
        rwa [he])
    unfold conjCrossed
    rw [hδZ _ hgZ, mulVec_zero]
  obtain ⟨n', _, _, hn'root, hn'torus⟩ :=
    exists_eq_mulVec_sub_of_rootSz_torusSz (a := a) ha
      (δ := conjCrossed mm δ g) (fun x y => conjCrossed_mul mm hδmm g x y) hδ'Z
  refine ⟨mm g *ᵥ n', ?_, ?_⟩
  · intro z hz
    have hz' : g⁻¹ * z * g ∈ rootSub a ⊓ Subgroup.centralizer (rootSub a : Set ↥(Sz a)) :=
      (inf_centralizer_conj (n := a) g hg z).mp hz
    rw [rootSub_inf_centralizer (n := a) ha] at hz'
    obtain ⟨b, hb⟩ := (mem_rootCenter (n := a)).mp hz'
    have hfix : mm (rootSz a 0 b) *ᵥ n' = n' := by
      have h := hn'root 0 b
      rw [hδ'Z b] at h
      exact sub_eq_zero.mp h.symm
    have hconj := mulVec_conj_mulVec mm (g := g) (z := rootSz a 0 b) (n := n') hfix
    have hz_eq : g * rootSz a 0 b * g⁻¹ = z := by
      rw [show rootSz a 0 b = rootElt a 0 b from rfl, hb]
      group
    rwa [hz_eq] at hconj
  · intro x hx
    have hxN : x ∈ Subgroup.normalizer ((P : Subgroup ↥(Sz a)) : Set ↥(Sz a)) := by
      rw [← normalizer_inf_centralizer_eq_of_mulEquiv_sz ha (MulEquiv.refl ↥(Sz a)) P]
      exact hx
    have hyN : g⁻¹ * x * g ∈ Subgroup.normalizer (rootSub a : Set ↥(Sz a)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro n
      constructor
      · intro hn
        have hgn : g * n * g⁻¹ ∈ (P : Subgroup ↥(Sz a)) :=
          (hg (g * n * g⁻¹)).mpr (by
            have he : g⁻¹ * (g * n * g⁻¹) * g = n := by group
            rwa [he])
        have hxgn : x * (g * n * g⁻¹) * x⁻¹ ∈ (P : Subgroup ↥(Sz a)) :=
          (Subgroup.mem_normalizer_iff.mp hxN (g * n * g⁻¹)).mp hgn
        have hmem := (hg (x * (g * n * g⁻¹) * x⁻¹)).mp hxgn
        have heq : g⁻¹ * (x * (g * n * g⁻¹) * x⁻¹) * g =
            (g⁻¹ * x * g) * n * (g⁻¹ * x * g)⁻¹ := by group
        rwa [heq] at hmem
      · intro hn
        have hk : g * ((g⁻¹ * x * g) * n * (g⁻¹ * x * g)⁻¹) * g⁻¹ ∈
            (P : Subgroup ↥(Sz a)) :=
          (hg _).mpr (by
            have he : g⁻¹ * (g * ((g⁻¹ * x * g) * n * (g⁻¹ * x * g)⁻¹) * g⁻¹) * g =
                (g⁻¹ * x * g) * n * (g⁻¹ * x * g)⁻¹ := by group
            rwa [he])
        have hxinv : x⁻¹ ∈ Subgroup.normalizer ((P : Subgroup ↥(Sz a)) : Set ↥(Sz a)) :=
          Subgroup.inv_mem _ hxN
        have hxk : x⁻¹ * (g * ((g⁻¹ * x * g) * n * (g⁻¹ * x * g)⁻¹) * g⁻¹) * x ∈
            (P : Subgroup ↥(Sz a)) :=
          (Subgroup.mem_normalizer_iff.mp hxinv
            (g * ((g⁻¹ * x * g) * n * (g⁻¹ * x * g)⁻¹) * g⁻¹)).mp hk
        have hmem := (hg _).mp hxk
        have heq : g⁻¹ * (x⁻¹ *
            (g * ((g⁻¹ * x * g) * n * (g⁻¹ * x * g)⁻¹) * g⁻¹) * x) * g = n := by group
        rwa [heq] at hmem
    obtain ⟨u, w, y, hy⟩ := exists_eq_rootSz_mul_torusSz_of_mem_normalizer (a := a) ha hyN
    have h' : conjCrossed mm δ g (g⁻¹ * x * g) = mm (g⁻¹ * x * g) *ᵥ n' - n' := by
      rw [hy]
      have h1 := conjCrossed_mul mm hδmm g (rootSz a u w) (torusSz a y)
      have hS : conjCrossed mm δ g (rootSz a u w) = mm (rootSz a u w) *ᵥ n' - n' :=
        hn'root u w
      have hM : conjCrossed mm δ g (torusSz a y) = mm (torusSz a y) *ᵥ n' - n' :=
        hn'torus y
      rw [hS, hM] at h1
      rw [h1, map_mul, ← mulVec_mulVec, mulVec_sub]
      abel
    have hfin := conjCrossed_eq_sub mm (g := g) (x := g⁻¹ * x * g) (n := n') h'
    have hgx : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [hgx] at hfin
    exact hfin

theorem exists_eq_mulVec_sub_of_normalizer_sz {a : ℕ} (ha : 1 ≤ a)
    {Z : Subgroup ↥(Sz a)} (hZ : IsElemAbelian 2 Z) (hZcard : Nat.card Z = 2 ^ (2 * a + 1))
    {δ : ↥(Sz a) → (Fin 4 → GaloisField 2 (2 * a + 1))}
    (hδ : ∀ x y : ↥(Sz a), δ (x * y) = δ x +
      (((x : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
        Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))) *ᵥ δ y))
    (hδZ : ∀ z ∈ Z, δ z = 0) :
    ∃ n : Fin 4 → GaloisField 2 (2 * a + 1),
      (∀ z ∈ Z, (((z : ↥(Sz a)) : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
        Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))) *ᵥ n = n) ∧
      ∀ x ∈ Subgroup.normalizer (Z : Set ↥(Sz a)), δ x =
        (((x : ↥(Sz a)) : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
          Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))) *ᵥ n - n := by
  obtain ⟨P, hZeq⟩ := exists_sylow_eq_inf_centralizer_of_isElemAbelian (Q := ↥(Sz a))
    ha (MulEquiv.refl ↥(Sz a)) hZ hZcard
  obtain ⟨n, hnfix, hn⟩ := exists_eq_mulVec_sub_of_normalizer_sz_of_sylow (a := a) ha P hδ
    (by rw [← hZeq]; exact hδZ)
  refine ⟨n, ?_, ?_⟩
  · intro z hz
    rw [hZeq] at hz
    exact hnfix z hz
  · intro x hx
    rw [hZeq] at hx
    exact hn x hx

end CFSG.LocalAnalysis.WeakClosure81

end

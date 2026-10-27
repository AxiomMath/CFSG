module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LemmaHDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1L5
public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LieType.Universal.SymplecticExtras.Matrices

public section

namespace CFSG.StandardType.RCKC1

open CFSG.LieType.Universal CFSG.StandardType CFSG.Open
open CFSG.LieType.RootSystem CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Universal.Symplectic.SpExtras TauCeti.GLSymplecticFin

private theorem rckHBC_longRoot_mem_roots {K : Type*} [Group K] (Δ : UniversalRootDatum K)
    {γ : Fin Δ.rank → ℤ} (hγ : GGLongRoot Δ γ) : γ ∈ Δ.roots := by
  obtain ⟨w, γ₀, hγ₀, -, rfl⟩ := hγ
  exact weylAction_mem_roots Δ.isFiniteType w hγ₀

private theorem rckHBC_mat_elt {n : ℕ} {F : Type} [Field F] (r : RootSubgroupIndex n) (c : F) :
    mat n F (elt r c) = 1 + c • E F r :=
  mat_elt r c

private theorem rckHBC_commute_elt {n : ℕ} {F : Type} [Field F] (r : RootSubgroupIndex n)
    {c₀ : F} (hc₀ : c₀ ≠ 0) {k : StatedSp n F} (h : Commute k (elt r c₀)) (c : F) :
    Commute k (elt r c) := by
  have hm0 : Commute (mat n F k) (mat n F (elt r c₀)) := h.map (mat n F)
  have hm : Commute (mat n F k) (1 + c₀ • E F r) := by
    rwa [rckHBC_mat_elt] at hm0
  have hmat : Commute (mat n F k) (1 + c • E F r) :=
    commute_one_add_smul_of_ne_zero hc₀ hm c
  have hmat' : Commute (mat n F k) (mat n F (elt r c)) := by
    rwa [← rckHBC_mat_elt] at hmat
  exact Commute.of_map mat_injective hmat'

private theorem rckHBC_rootGroup_cent {n : ℕ} {F : Type} [Field F] {β : Fin n → ℤ}
    (hβ : β ∈ roots (isFiniteType_cartanC n) ∅) :
    ∀ x ∈ rootGroup n F β, x ≠ 1 →
      Subgroup.centralizer {x} ≤
        Subgroup.centralizer (rootGroup n F β : Set (StatedSp n F)) := by
  intro x hx hx1 k hk
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hβ
  obtain ⟨c₀, rfl⟩ := (mem_rootGroup_iff hr).1 hx
  have hc₀ : c₀ ≠ 0 := by
    intro hc
    exact hx1 (by rw [hc, elt_zero])
  have hcomm : Commute k (elt r c₀) := Subgroup.mem_centralizer_singleton_iff.mp hk
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hr).1 hy
  exact (rckHBC_commute_elt r hc₀ hcomm c).symm

theorem rck_lemmaHC_BC
    {m g : ℕ} (hg : 1 ≤ g) {β : Fin (ggU .PSp m g).D.rank → ℤ}
    (hβ : GGLongRoot (ggU .PSp m g).D β) :
    RCKLemmaHCent (ggU .PSp m g) β := by
  change RCKLemmaHCent
    ⟨StatedSp m (GaloisField 2 g), Symplectic.rootDatum m (GaloisField 2 g)⟩ β
  exact rckHBC_rootGroup_cent (rckHBC_longRoot_mem_roots _ hβ)

end CFSG.StandardType.RCKC1

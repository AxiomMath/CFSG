module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoTorus
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoAutLQAux2
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.StandardType CFSG.StandardType.USixTwo
open USixTwo TorConj TorHomKernel MainProof TorHyperplanes
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K]

theorem le_card_ggAutomizer_of_isPGroup (hK : Nat.card K = 4) {Bs L : Subgroup G} {x : G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hZ2 : IsPGroup 2 (Subgroup.center L))
    (hmap : ((Bs ⊓ L).subgroupOf L).map
      (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))) = USixTwo.torU K)
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 5) (hx : x ∈ Bs) (hxL : x ∉ L)
    (hLx : L ≤ Subgroup.centralizer {x}) :
    720 ≤ Nat.card (ggAutomizer L Bs) := by
  obtain ⟨ω, hω⟩ := USixTwo.exists_root_omega hK
  haveI : Finite (MulAut ↥Bs) :=
    Finite.of_injective (fun f : MulAut ↥Bs => (f : ↥Bs → ↥Bs)) DFunLike.coe_injective
  have hinj : Function.Injective (fun σ : Equiv.Perm (Fin 6) =>
      (⟨psi hK θ hZ2 hBs hcard hmap hx hxL hLx hω σ,
        psi_mem_ggAutomizer hK θ hZ2 hBs hcard hmap hx hxL hLx hω σ⟩ :
        ggAutomizer L Bs)) := by
    intro σ τ h
    exact psi_injective hK θ hZ2 hBs hcard hmap hx hxL hLx hω (congrArg Subtype.val h)
  have h720 : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  calc 720 = Nat.card (Equiv.Perm (Fin 6)) := h720.symm
    _ ≤ Nat.card (ggAutomizer L Bs) := Nat.card_le_card_of_injective _ hinj

theorem apply_eq_one_of_forall_ggAutomizer_of_isPGroup (hK : Nat.card K = 4)
    {Bs L : Subgroup G} {x : G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hZ2 : IsPGroup 2 (Subgroup.center L))
    (hmap : ((Bs ⊓ L).subgroupOf L).map
      (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))) = USixTwo.torU K)
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 5) (hx : x ∈ Bs) (hxL : x ∉ L)
    (hLx : L ≤ Subgroup.centralizer {x}) (f : ↥Bs →* Multiplicative (ZMod 3))
    (hf : ∀ ψ ∈ ggAutomizer L Bs, ∀ b, f (ψ b) = f b) {b : ↥Bs} (hb : (b : G) ∈ L) :
    f b = 1 := by
  obtain ⟨ω, hω⟩ := USixTwo.exists_root_omega hK
  let g : ↥sumZeroSubgroup →* Multiplicative (ZMod 3) :=
    f.comp (bsOfHom hK θ hZ2 hBs hmap hω)
  have hinv : ∀ (σ : Equiv.Perm (Fin 6)) (v : ↥sumZeroSubgroup), g (permX σ v) = g v := by
    intro σ v
    change f (bsOf hK θ hmap hω (permX σ v)) = f (bsOf hK θ hmap hω v)
    rw [← psi_apply_bsOf hK θ hZ2 hBs hcard hmap hx hxL hLx hω σ v]
    exact hf _ (psi_mem_ggAutomizer hK θ hZ2 hBs hcard hmap hx hxL hLx hω σ) _
  have hdelta : ∀ i : Fin 5, g (deltaS i) = 1 := by
    intro i
    have h := hinv (Equiv.swap i.castSucc 5) (deltaS i)
    rw [permX_swap_deltaS_inv i, map_inv] at h
    exact eq_one_of_inv_eq_self h
  have hg1 : ∀ v : ↥sumZeroSubgroup, g v = 1 := by
    intro v
    rw [MainProof.eq_prod_deltaS v]
    simp_rw [MainProof.deltaSB_eq_deltaS]
    rw [map_prod]
    apply Finset.prod_eq_one
    intro i _
    rw [map_pow, hdelta i, one_pow]
  obtain ⟨v, hv⟩ := bsOf_surj hK θ hZ2 hBs hmap hω b hb
  rw [← hv]
  exact hg1 v

theorem exists_reflection_threeA_of_isPGroup (hK : Nat.card K = 4) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) {Bs L : Subgroup G} {x : G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hZ2 : IsPGroup 2 (Subgroup.center L))
    (hmap : ((Bs ⊓ L).subgroupOf L).map
      (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))) = USixTwo.torU K)
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 5) (hx : x ∈ Bs) (hxL : x ∉ L)
    (hLx : L ≤ Subgroup.centralizer {x}) :
    ∃ (a : ↥Bs) (ha : (a : G) ∈ L), θ (QuotientGroup.mk (⟨a, ha⟩ : L)) = USixTwo.threeA hω ∧
      a ≠ 1 ∧ ∃ ψ ∈ ggAutomizer L Bs, ψ ^ 2 = 1 ∧ ψ a = a⁻¹ ∧
        ∀ b : ↥Bs, b⁻¹ * ψ b ∈ Subgroup.zpowers a := by
  have hmap' : ((Bs ⊓ L).subgroupOf L).map (piOf (K := K) θ) = USixTwo.torU K := hmap
  refine ⟨bsOf hK θ hmap' hω threeAArg, bsOf_coe_mem_L hK θ hmap' hω threeAArg, ?_, ?_, ?_⟩
  · change piOf θ (⟨(bsOf hK θ hmap' hω threeAArg : ↥Bs),
      bsOf_coe_mem_L hK θ hmap' hω threeAArg⟩ : L) = USixTwo.threeA hω
    rw [bsOf_pi, MainProof.torHom_threeAArg]
  · intro ha1
    apply threeA_ne_one hK hω
    have hphi := bsOf_pi hK θ hmap' hω threeAArg
    rw [MainProof.torHom_threeAArg] at hphi
    have hL1 : (⟨(bsOf hK θ hmap' hω threeAArg : ↥Bs),
        bsOf_coe_mem_L hK θ hmap' hω threeAArg⟩ : L) = 1 :=
      Subtype.ext (congrArg (fun y : ↥Bs => (y : G)) ha1)
    rw [← hphi, hL1, map_one]
  · refine ⟨psi hK θ hZ2 hBs hcard hmap' hx hxL hLx hω (Equiv.swap 0 1),
      psi_mem_ggAutomizer hK θ hZ2 hBs hcard hmap' hx hxL hLx hω (Equiv.swap 0 1),
      psi_swap01_sq hK θ hZ2 hBs hcard hmap' hx hxL hLx hω,
      psi_apply_swap01_threeAArg hK θ hZ2 hBs hcard hmap' hx hxL hLx hω, ?_⟩
    intro b
    obtain ⟨p, hp, q, hq, hb⟩ :=
      exists_mul_zpowers hK θ hZ2 hmap' hBs hcard hx hxL hLx b.2
    set pbs : ↥Bs := ⟨p, Subgroup.zpowers_le.mpr hx hp⟩ with hpb
    set qbs : ↥Bs := ⟨q, hq.1⟩ with hqb
    have hb' : b = pbs * qbs := Subtype.ext hb.symm
    have hpp : psi hK θ hZ2 hBs hcard hmap' hx hxL hLx hω (Equiv.swap 0 1) pbs = pbs :=
      psi_fixes_zpowers hK θ hZ2 hBs hcard hmap' hx hxL hLx hω (Equiv.swap 0 1) hp
    rw [hb', map_mul, hpp]
    have heq : (pbs * qbs)⁻¹ * (pbs * psi hK θ hZ2 hBs hcard hmap' hx hxL hLx hω
        (Equiv.swap 0 1) qbs) = qbs⁻¹ * psi hK θ hZ2 hBs hcard hmap' hx hxL hLx hω
          (Equiv.swap 0 1) qbs := by group
    rw [heq]
    exact inv_mul_psi_swap01_mem_zpowers hK θ hZ2 hBs hcard hmap' hx hxL hLx hω hq.2

end CFSG.StandardType.E6QTwo

end

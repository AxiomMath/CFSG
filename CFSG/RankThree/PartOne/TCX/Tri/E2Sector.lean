module

public import CFSG.RankThree.PartOne.TCX.Tri.A3Layer
public import CFSG.RankThree.PartOne.TCX.Tri.E2A1
public import CFSG.RankThree.PartOne.TCX.Tri.E2Kernel
public import CFSG.RankThree.PartOne.TCX.Tri.E2Frame
public import CFSG.RankThree.PartOne.TCX.Tri.Frame
public import CFSG.RankThree.PartOne.TCX.Tri.RegularBound
public import CFSG.RankThree.PartOne.KGD.D4QA3
public import CFSG.RankThree.PartOne.KD4T.Certs

public section

namespace CFSG.RankThree.PartOne.TCX.Tri

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.Chevalley CFSG.RankThree.Chevalley.TrialityFold CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.TCX
open scoped MatrixGroups

section Roots

theorem e013_orth :
    iform (Pi.single i0 1 : Fin TwistTag.D4.tag.rank → ℤ) (Pi.single i1 1) = 0 ∧
      iform (Pi.single i0 1 : Fin TwistTag.D4.tag.rank → ℤ) (Pi.single i3 1) = 0 ∧
      iform (Pi.single i1 1 : Fin TwistTag.D4.tag.rank → ℤ) (Pi.single i3 1) = 0 := by
  decide +kernel

theorem e013_sum_check :
    List.ofFn (Pi.single i0 1 + Pi.single i1 1 : Fin TwistTag.D4.tag.rank → ℤ) ∉
        TwistTag.D4.tag.artifactRoots ∧
      List.ofFn (Pi.single i0 1 - Pi.single i1 1 : Fin TwistTag.D4.tag.rank → ℤ) ∉
        TwistTag.D4.tag.artifactRoots ∧
      List.ofFn (Pi.single i0 1 + Pi.single i3 1 : Fin TwistTag.D4.tag.rank → ℤ) ∉
        TwistTag.D4.tag.artifactRoots ∧
      List.ofFn (Pi.single i0 1 - Pi.single i3 1 : Fin TwistTag.D4.tag.rank → ℤ) ∉
        TwistTag.D4.tag.artifactRoots ∧
      List.ofFn (Pi.single i1 1 + Pi.single i3 1 : Fin TwistTag.D4.tag.rank → ℤ) ∉
        TwistTag.D4.tag.artifactRoots ∧
      List.ofFn (Pi.single i1 1 - Pi.single i3 1 : Fin TwistTag.D4.tag.rank → ℤ) ∉
        TwistTag.D4.tag.artifactRoots := by
  decide +kernel

variable {L : Type} [Field L]

theorem not_isRoot_of_notMem {v : Fin TwistTag.D4.tag.rank → ℤ}
    (h : List.ofFn v ∉ TwistTag.D4.tag.artifactRoots) : ¬ IsRoot TwistTag.D4.tag v :=
  fun hv => h (isRoot_iff_mem_artifactRoots.1 hv)

theorem commute_smul_single (w : WeylGroup TwistTag.D4.tag) {a b : Fin TwistTag.D4.tag.rank}
    (h0 : iform (Pi.single a 1 : Fin TwistTag.D4.tag.rank → ℤ) (Pi.single b 1) = 0)
    (hp : ¬ IsRoot TwistTag.D4.tag (Pi.single a 1 + Pi.single b 1 :
      Fin TwistTag.D4.tag.rank → ℤ))
    (hm : ¬ IsRoot TwistTag.D4.tag (Pi.single a 1 - Pi.single b 1 :
      Fin TwistTag.D4.tag.rank → ℤ)) (A B : SL(2, L)) :
    Commute (rootSL2 TwistTag.D4.tag L (w • (Pi.single a 1 : Fin TwistTag.D4.tag.rank → ℤ)) A)
      (rootSL2 TwistTag.D4.tag L (w • (Pi.single b 1 : Fin TwistTag.D4.tag.rank → ℤ)) B) :=
  rootSL2_commute_of_orth (IsRoot.smul (isRoot_single _ a) w) (IsRoot.smul (isRoot_single _ b) w)
    (by rw [iform_smul]; exact h0) (by rw [← smul_add, isRoot_smul_iff]; exact hp)
    (by rw [← smul_sub, isRoot_smul_iff]; exact hm) A B

variable [CharP L 2]

theorem pAct_smul_single {w : WeylGroup TwistTag.D4.tag} (hw : w ∈ relWeylTwist TwistTag.D4)
    {a b : Fin TwistTag.D4.tag.rank}
    (hab : permLattice TwistTag.D4.perm (Pi.single a 1 : Fin TwistTag.D4.tag.rank → ℤ) =
      Pi.single b 1) :
    PAct L (w • (Pi.single a 1 : Fin TwistTag.D4.tag.rank → ℤ))
      (w • (Pi.single b 1 : Fin TwistTag.D4.tag.rank → ℤ)) := by
  have h := triP_conj_rootSL2_gen (L := L) (IsRoot.smul (isRoot_single _ a) w)
  have e : permLattice TwistTag.D4.perm (w • (Pi.single a 1 : Fin TwistTag.D4.tag.rank → ℤ)) =
      w • (Pi.single b 1 : Fin TwistTag.D4.tag.rank → ℤ) := by
    rw [← hab]
    exact ((mem_relWeylTwist_iff_smul TwistTag.D4).1 hw _).symm
  rw [e] at h
  exact h

end Roots

section Sector

variable {C : Type} [Group C] [Finite C] {L : Type} [Field L] [CharP L 2] [IsAlgClosed L]
  {p f₀ : ℕ} {ι : C →* ModGL TwistTag.D4.tag L} {α₀ : MulAut C}

theorem tri_sector_e2 (h : IsShintani p ι (triF0 L f₀) (triPhi L p f₀) α₀) (hp : p.Prime)
    (hp5 : 5 ≤ p) (hf₀ : 1 ≤ f₀)
    (hodd : ∀ t ∈ torusGroup TwistTag.D4.tag L, ∃ m : ℕ, Odd m ∧ t ^ m = 1)
    {k : Type} [Field k] [Finite k] [Algebra k L] [IsAlgClosure k L] (σk : k ≃+* k)
    (hkc : Nat.card k = (2 ^ f₀) ^ 3) (hσk : ∀ c, σk c = c ^ 2 ^ f₀)
    (hpq : (p : ℤ) ∣ ((2 ^ f₀ : ℕ) : ℤ) + 1)
    {x : C} (hx : orderOf x = p) (hxα : α₀ x = x) :
    RegularShape (2 ^ (p * f₀)) x ∨
      SingleLayerData p α₀ (Subgroup.centralizer ({x} : Set C)) := by
  classical
  have hp3 : 3 < p := by omega
  have hpq' : p ∣ 2 ^ f₀ + 1 := by exact_mod_cast hpq
  obtain ⟨g₀, hg₀C, hg₀, hfr₁, hfr₂⟩ := tri_frame_e2 hf₀ k hkc σk hσk hp hp3 hpq L
  have hF₀ : triF0 L f₀ = twistHom TwistTag.D4 L (iterateFrobenius L 2 f₀) := rfl
  obtain ⟨c, hcα, hcmem⟩ := h.frame_transfer hp hF₀ σk hσk hfr₁ hfr₂ hx hxα
  obtain ⟨hmemT, -⟩ := mem_twistedTorusOf.1 hcmem
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hmemT
  have hb' : rootDiagUnit TwistTag.D4.tag b = g₀⁻¹ * ι (c * x * c⁻¹) * g₀ := hb.symm
  have hbo : orderOf (rootDiagUnit TwistTag.D4.tag b) = p := by
    rw [hb']
    have e1 : orderOf (g₀⁻¹ * ι (c * x * c⁻¹) * g₀) = orderOf (ι (c * x * c⁻¹)) := by
      have := orderOf_injective (MulAut.conj g₀⁻¹).toMonoidHom (MulAut.conj g₀⁻¹).injective
        (ι (c * x * c⁻¹))
      simpa [MulAut.conj_apply] using this
    have e2 : orderOf (ι (c * x * c⁻¹)) = orderOf (c * x * c⁻¹) :=
      orderOf_injective ι h.inj _
    have e3 : orderOf (c * x * c⁻¹) = orderOf x := by
      have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x
      simpa [MulAut.conj_apply] using this
    rw [e1, e2, e3, hx]
  have hbT : rootDiagUnit TwistTag.D4.tag b ∈ twistedTorusOf (triNeg L) (triF0 L f₀) := by
    rw [hb']
    exact hcmem
  rcases tri_kernel_e2 (f := f₀) hp hp3 hpq' L hbT hbo with hE | ⟨w, hw, hker⟩ | ⟨w, hw, hker⟩
  ·
    left
    obtain ⟨ψ, hψinj, -, hψt, hψT⟩ := tri_regular_of_frame h hp hp3 hg₀C hg₀ hx hb' hbT hE
    refine regularShape_of_torus_embedding ψ hψinj hψt fun y hy => ?_
    obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hψt y)
    have hT := hψT y
    rw [ha] at hT hy ⊢
    exact tri_regular_exponent_e2 hp hp5 hT hy
  ·
    right
    have hcl := hw
    have hs₀ : IsRoot TwistTag.D4.tag (w • (Pi.single i0 1 : Fin TwistTag.D4.tag.rank → ℤ)) :=
      IsRoot.smul (isRoot_single _ i0) w
    have hs₁ : IsRoot TwistTag.D4.tag (w • (Pi.single i1 1 : Fin TwistTag.D4.tag.rank → ℤ)) :=
      IsRoot.smul (isRoot_single _ i1) w
    have hs₃ : IsRoot TwistTag.D4.tag (w • (Pi.single i3 1 : Fin TwistTag.D4.tag.rank → ℤ)) :=
      IsRoot.smul (isRoot_single _ i3) w
    obtain ⟨o01, o03, o13⟩ := e013_orth
    obtain ⟨p01, m01, p03, m03, p13, m13⟩ := e013_sum_check
    have c01 := fun A B : SL(2, L) => commute_smul_single w o01 (not_isRoot_of_notMem p01)
      (not_isRoot_of_notMem m01) A B
    have c03 := fun A B : SL(2, L) => commute_smul_single w o03 (not_isRoot_of_notMem p03)
      (not_isRoot_of_notMem m03) A B
    have c13 := fun A B : SL(2, L) => commute_smul_single w o13 (not_isRoot_of_notMem p13)
      (not_isRoot_of_notMem m13) A B
    have a01 : PAct L (w • (Pi.single i0 1 : Fin TwistTag.D4.tag.rank → ℤ))
        (w • (Pi.single i1 1 : Fin TwistTag.D4.tag.rank → ℤ)) :=
      pAct_smul_single hw (by rw [permLattice_single, perm_i0])
    have a13 : PAct L (w • (Pi.single i1 1 : Fin TwistTag.D4.tag.rank → ℤ))
        (w • (Pi.single i3 1 : Fin TwistTag.D4.tag.rank → ℤ)) :=
      pAct_smul_single hw (by rw [permLattice_single, perm_i1])
    have a30 : PAct L (w • (Pi.single i3 1 : Fin TwistTag.D4.tag.rank → ℤ))
        (w • (Pi.single i0 1 : Fin TwistTag.D4.tag.rank → ℤ)) :=
      pAct_smul_single hw (by rw [permLattice_single, perm_i3])
    have hKS : ∀ α, α ∈ rootCharKernel b ↔ α ∈ threeRootSet
        (w • (Pi.single i0 1 : Fin TwistTag.D4.tag.rank → ℤ))
        (w • (Pi.single i1 1 : Fin TwistTag.D4.tag.rank → ℤ))
        (w • (Pi.single i3 1 : Fin TwistTag.D4.tag.rank → ℤ)) := by
      intro α
      rw [hker α]
      constructor
      · rintro ⟨β, hβ, rfl⟩
        simp only [threeRootSet, d4Qr₁, d4Qr₂, d4Qr₃, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hβ
        rcases hβ with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [threeRootSet, smul_neg]
      · intro hα
        simp only [threeRootSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hα
        rcases hα with rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨d4Qr₁, by simp [threeRootSet], rfl⟩
        · exact ⟨-d4Qr₁, by simp [threeRootSet], by simp [d4Qr₁, smul_neg]⟩
        · exact ⟨-d4Qr₂, by simp [threeRootSet], by simp [d4Qr₂]⟩
        · exact ⟨d4Qr₂, by simp [threeRootSet], by simp [d4Qr₂, smul_neg]⟩
        · exact ⟨d4Qr₃, by simp [threeRootSet], rfl⟩
        · exact ⟨-d4Qr₃, by simp [threeRootSet], by simp [d4Qr₃, smul_neg]⟩
    have hrootsS : ∀ α ∈ threeRootSet (w • (Pi.single i0 1 : Fin TwistTag.D4.tag.rank → ℤ))
        (w • (Pi.single i1 1 : Fin TwistTag.D4.tag.rank → ℤ))
        (w • (Pi.single i3 1 : Fin TwistTag.D4.tag.rank → ℤ)), IsRoot TwistTag.D4.tag α := by
      intro α hα
      rcases hα with rfl | rfl | rfl | rfl | rfl | rfl
      exacts [hs₀, IsRoot.neg hs₀, hs₁, IsRoot.neg hs₁, hs₃, IsRoot.neg hs₃]
    have hbS1 : rootCharKernel b ⊆ threeRootSet (w • (Pi.single i0 1 : Fin TwistTag.D4.tag.rank → ℤ))
        (w • (Pi.single i1 1 : Fin TwistTag.D4.tag.rank → ℤ))
        (w • (Pi.single i3 1 : Fin TwistTag.D4.tag.rank → ℤ)) := fun α hα => (hKS α).1 hα
    have hbc1 : rootDiagUnit TwistTag.D4.tag b ∈ Subgroup.centralizer
        (rootSpan TwistTag.D4.tag L (threeRootSet
          (w • (Pi.single i0 1 : Fin TwistTag.D4.tag.rank → ℤ))
          (w • (Pi.single i1 1 : Fin TwistTag.D4.tag.rank → ℤ))
          (w • (Pi.single i3 1 : Fin TwistTag.D4.tag.rank → ℤ))) :
            Set (ModGL TwistTag.D4.tag L)) := by
      refine (rootDiagUnit_mem_centralizer_rootSpan_iff b hrootsS).2 fun β hβ => ?_
      exact ((hKS β).2 hβ).2
    have hp3' : p % 3 = 1 ∨ p % 3 = 2 := by
      have h3 : ¬ 3 ∣ p := fun hd => by
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 hd
        omega
      omega
    rcases hp3' with hmod | hmod
    · exact tri_a3_layer h hp hp5 hf₀ hodd hg₀C hg₀ hs₀ hs₁ hs₃ c01 c03 c13
        (Or.inl ⟨hmod, a01, a13, a30⟩) hx hcα hb' hbT hbS1 hbc1
    · have hswap : threeRootSet (w • (Pi.single i0 1 : Fin TwistTag.D4.tag.rank → ℤ))
          (w • (Pi.single i3 1 : Fin TwistTag.D4.tag.rank → ℤ))
          (w • (Pi.single i1 1 : Fin TwistTag.D4.tag.rank → ℤ)) =
          threeRootSet (w • (Pi.single i0 1 : Fin TwistTag.D4.tag.rank → ℤ))
            (w • (Pi.single i1 1 : Fin TwistTag.D4.tag.rank → ℤ))
            (w • (Pi.single i3 1 : Fin TwistTag.D4.tag.rank → ℤ)) :=
        (threeRootSet_swap₂₃ _ _ _).symm
      exact tri_a3_layer h hp hp5 hf₀ hodd hg₀C hg₀ hs₀ hs₃ hs₁ c03 c01
        (fun A B => (c13 B A).symm) (Or.inr ⟨hmod, a01, a13, a30⟩) hx hcα hb' hbT
        (by rw [hswap]; exact hbS1) (by rw [hswap]; exact hbc1)
  ·
    right
    set θ : Fin TwistTag.D4.tag.rank → ℤ := w • (Pi.single i2 1 : Fin TwistTag.D4.tag.rank → ℤ)
      with hθdef
    have hθ : IsRoot TwistTag.D4.tag θ := IsRoot.smul (isRoot_single _ i2) w
    have hρθ : permLattice TwistTag.D4.perm θ = θ := by
      rw [hθdef, ← ((mem_relWeylTwist_iff_smul TwistTag.D4).1 hw _), permLattice_single, perm_i2]
    have hKS : ∀ α, α ∈ rootCharKernel b ↔ α = θ ∨ α = -θ := by
      intro α
      rw [hker α]
      constructor
      · rintro ⟨β, hβ, rfl⟩
        rcases hβ with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (by rw [hθdef, smul_neg])
      · rintro (rfl | rfl)
        · exact ⟨_, Or.inl rfl, rfl⟩
        · exact ⟨-Pi.single i2 1, Or.inr rfl, by rw [hθdef, smul_neg]⟩
    have hbS : rootCharKernel b ⊆ ({θ, -θ} : Set (Fin TwistTag.D4.tag.rank → ℤ)) :=
      fun α hα => by
        rcases (hKS α).1 hα with h1 | h1
        exacts [Or.inl h1, Or.inr h1]
    have hSroot : ∀ α ∈ ({θ, -θ} : Set (Fin TwistTag.D4.tag.rank → ℤ)),
        IsRoot TwistTag.D4.tag α := by
      intro α hα
      rcases hα with rfl | rfl
      exacts [hθ, IsRoot.neg hθ]
    have hbc : rootDiagUnit TwistTag.D4.tag b ∈ Subgroup.centralizer
        (rootSpan TwistTag.D4.tag L ({θ, -θ} : Set (Fin TwistTag.D4.tag.rank → ℤ)) :
          Set (ModGL TwistTag.D4.tag L)) := by
      refine (rootDiagUnit_mem_centralizer_rootSpan_iff b hSroot).2 fun β hβ => ?_
      have hβ' : β ∈ rootCharKernel b := (hKS β).2 (by
        rcases hβ with rfl | rfl
        exacts [Or.inl rfl, Or.inr rfl])
      exact hβ'.2
    exact tri_a1_layer h hp hp5 hf₀ hodd hg₀C hg₀ hθ hρθ hx hcα hb' hbT hbS hbc

end Sector

end CFSG.RankThree.PartOne.TCX.Tri

module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Hall.Basic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearFourCentralCover

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.BenderSuzuki.External

variable {G : Type*} [Group G]

theorem normal_subgroup_conjugation_of_member (L : Subgroup G) [L.Normal]
    (w a : L) : MulAut.conjNormal (w : G) a = MulAut.conj w a := by
  apply Subtype.ext
  rfl

variable [Finite G]

theorem sylow_center_mem_normal_sylow_centralizer {p : ℕ} [Fact p.Prime]
    (T : Sylow p G) (L : Subgroup G) [L.Normal] (w : L)
    (hwT : (w : G) ∈ (T : Subgroup G))
    (hwcenter : (⟨(w : G), hwT⟩ : (T : Subgroup G)) ∈
      Subgroup.center (T : Subgroup G)) :
    w ∈ Subgroup.centralizer (hallSylowSubgroupOfNormal T L : Set L) := by
  apply Subgroup.mem_centralizer_iff.mpr
  intro a ha
  have haT : (a : G) ∈ (T : Subgroup G) := by
    change a ∈ (hallSylowSubgroupOfNormal T L : Subgroup L) at ha
    rw [hallSylowSubgroupOfNormal_coe] at ha
    exact ha
  have hcomm : (a : G) * (w : G) = (w : G) * (a : G) :=
    congrArg (fun t : (T : Subgroup G) => (t : G))
      (Subgroup.mem_center_iff.mp hwcenter (⟨(a : G), haT⟩ : (T : Subgroup G)))
  exact Subtype.ext hcomm

theorem normal_inner_sylow_witness_kernel_eq_bot {J : Type*} [Group J]
    (T : Sylow 2 G) (L : Subgroup G) [L.Normal] (η : L →* J)
    (hcentral : η.ker ≤ Subgroup.center L)
    (hcover : η.ker ≠ ⊥ → ∀ P : Sylow 2 L,
      Subgroup.centralizer (P : Set L) ≤ η.ker)
    (w : L) (hwT : (w : G) ∈ (T : Subgroup G))
    (hwcenter : (⟨(w : G), hwT⟩ : (T : Subgroup G)) ∈
      Subgroup.center (T : Subgroup G)) (hwnoncentral : w ∉ Subgroup.center L) :
    η.ker = ⊥ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  exact hwnoncentral (hcentral (hcover hne (hallSylowSubgroupOfNormal T L)
    (sylow_center_mem_normal_sylow_centralizer T L w hwT hwcenter)))

theorem even_linear_cover_inner_sylow_witness_kernel_eq_bot
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (T : Sylow 2 G) (L : Subgroup G) [L.Normal] [Group.IsPerfect L]
    (f : ℕ) (hf : 2 ≤ f) (hcard : Nat.card F = 2 ^ f)
    (η : L →* GLAProj (GLASLGroup (Fin 2) F)) (hsurj : Function.Surjective η)
    (hcentral : η.ker ≤ Subgroup.center L) (hp : IsPGroup 2 η.ker)
    (w : L) (hwT : (w : G) ∈ (T : Subgroup G))
    (hwcenter : (⟨(w : G), hwT⟩ : (T : Subgroup G)) ∈
      Subgroup.center (T : Subgroup G)) (hwnoncentral : w ∉ Subgroup.center L) :
    η.ker = ⊥ := by
  by_cases hfour : f = 2
  · have hcardfour : Nat.card F = 4 := by simpa [hfour] using hcard
    apply normal_inner_sylow_witness_kernel_eq_bot T L η hcentral
      (w := w) (hwT := hwT) (hwcenter := hwcenter) (hwnoncentral := hwnoncentral)
    intro hne P
    exact le_of_eq ((four_field_linear_central_two_cover_full hcardfour η hsurj
      hcentral hp).2 hne P).2.2.2.1
  · exact (large_even_linear_central_two_cover_trivial f (by omega) hcard η
      hsurj hcentral hp).1

end CFSG.ShultStronglyClosedTI

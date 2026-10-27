module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerLift
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerTor
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMPrimeCBase
import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCoverLift
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosCommCornerGrp

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary Matrix CFSG.Assembly

variable {G : Type} [Group G] [Finite G]

theorem qTwoLMDivCoordInner_tcl_ind {B Bs L : Subgroup G} {x : G} (hG : GGThmIHyp 3 B x L)
    (hBs : GGBstar 3 B Bs) (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {m : ℕ} (h3 : 3 ∣ m)
    {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {L0 : Type} [Group L0]
    {c : ↥L →* L0} {π : Su F0 2 1 m →* L0} {ρ : ↥Bs →* MulAut L0}
    (hU : QTwoDivInnerFrame m Bs L hN F0 L0 c π ρ) {δ : ↥(sumZero m 3) →* Su F0 2 1 m}
    (hδ : QTwoDivTorus h3 δ) {τ : ↥(sumZero m 3) →* ↥L} (hτ : QTwoDivLift Bs L c π δ τ)
    (hrange : ∀ t : ↥L, (t : G) ∈ Bs → ∃ f, τ f = t)
    (hsplit : ∀ b ∈ Bs, ∃ t : ↥L, (t : G) ∈ Bs ∧ ∃ k : ℕ, b = (t : G) * x ^ k) :
    ∀ σ : Equiv.Perm (Fin m), ∃ n : ↥L, (n : G) ∈ Subgroup.normalizer (Bs : Set G) ∧
      ∀ f, (n : G) * ((τ f : ↥L) : G) * (n : G)⁻¹ = ((τ (permAutV σ f) : ↥L) : G) := by
  intro σ
  have hS : LargeEvenSStar 3 B x L := hG.2.2.2.2.2.2.1
  obtain ⟨⟨-, -, -⟩, hxB, _, _, _⟩ := hS
  obtain ⟨n, hn⟩ := hU.c_surj (π (ggPermSU σ⁻¹))
  have hxcomm : (n : G) * x = x * (n : G) :=
    ((Subgroup.mem_centralizer_iff.mp (qTwoLMFrameC_le_centralizer hG n.2) x
      (Set.mem_singleton x))).symm
  have hconjG : ∀ f, (n : G) * ((τ f : ↥L) : G) * (n : G)⁻¹ =
      ((τ (permAutV σ f) : ↥L) : G) := by
    intro f
    have hc : c (n * τ f * n⁻¹) = c (τ (permAutV σ f)) := by
      rw [map_mul, map_mul, map_inv, hn, hτ.comm f, hτ.comm (permAutV σ f),
        ← map_mul, ← map_inv, ← map_mul, hδ.perm σ f]
    have h3 : (n * τ f * n⁻¹) ^ 3 = 1 := by
      rw [conj_pow, hτ.cube f]
      group
    have heq : n * τ f * n⁻¹ = τ (permAutV σ f) :=
      CFSG.LocalAnalysis.ComponentInitial.eq_of_pow_three_eq_one_of_map_eq hU.c_ker hU.c_two
        h3 (hτ.cube (permAutV σ f)) hc
    simpa using congrArg (fun y : ↥L => (y : G)) heq
  have hconj_mem : ∀ b ∈ Bs, (n : G) * b * (n : G)⁻¹ ∈ Bs := by
    intro b hb
    obtain ⟨t, htBs, k, rfl⟩ := hsplit b hb
    obtain ⟨f, hf⟩ := hrange t htBs
    rw [← hf]
    have heq1 : (n : G) * (((τ f : ↥L) : G) * x ^ k) * (n : G)⁻¹
        = ((n : G) * ((τ f : ↥L) : G) * (n : G)⁻¹) *
            ((n : G) * x ^ k * (n : G)⁻¹) := by group
    have heq2 : (n : G) * x ^ k * (n : G)⁻¹ = x ^ k := by
      rw [← conj_pow]
      rw [show (n : G) * x * (n : G)⁻¹ = x by rw [hxcomm]; group]
    rw [heq1, heq2, hconjG f]
    exact Subgroup.mul_mem _ (hτ.mem (permAutV σ f)) (Subgroup.pow_mem _ (hBs.1 hxB) k)
  exact ⟨n, ggNSPosPF3C_mem_normalizer_of_conj_mem hconj_mem, hconjG⟩

end CFSG.StandardType.QTwo

end

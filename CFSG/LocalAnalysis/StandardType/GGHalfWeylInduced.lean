module

public import CFSG.LocalAnalysis.StandardType.GGHalfWeylDefs
public import CFSG.LocalAnalysis.StandardType.GGHalfWeylTorusCoord
public import CFSG.LocalAnalysis.StandardType.GGHalfWeylSignedConj
public import CFSG.LocalAnalysis.StandardType.GGSpJoinOrbitBound
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf SpJoin

namespace GGHalfTorusFrame

theorem exists_aut_signed {G : Type} [Group G] [Finite G] {Bs X : Subgroup G} {n : ℕ}
    {ψ : SpecialLinearGroup (Fin (n + 1)) F2 →* G} (hψ : GGHalfTorusFrame Bs X (halfTorus n) ψ)
    (Φ : (Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) ≃* ↥(halfTorus n))
    (hΦ : ∀ j : Fin ((n + 1) / 2),
      ((Φ (Pi.mulSingle j (Multiplicative.ofAdd 1)) : ↥(halfTorus n)) :
        SpecialLinearGroup (Fin (n + 1)) F2) =
        omegaBlock n ⟨2 * j.val, two_mul_lt_of_lt_half j.isLt⟩)
    (h : Equiv.Perm (Fin ((n + 1) / 2) → Multiplicative (ZMod 3)))
    (hh : h ∈ spSignedGroup ((n + 1) / 2) 3) :
    ∃ σ ∈ ggAutomizer X Bs, ∀ (a : Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) (c : G)
      (hb : ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * c ∈ Bs),
      c ∈ Subgroup.centralizer (X : Set G) →
        ((σ ⟨ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * c, hb⟩ : ↥Bs) : G) =
          ψ (Φ (h a) : SpecialLinearGroup (Fin (n + 1)) F2) * c := by
  obtain ⟨e, he⟩ := GGHalf.exists_conj_of_spSigned n Φ hΦ h hh
  have hgT : e ∈ Subgroup.normalizer
      (halfTorus n : Set (SpecialLinearGroup (Fin (n + 1)) F2)) :=
    Subgroup.mem_normalizer_fintype fun s hs => by
      obtain ⟨a, ha⟩ := Φ.surjective ⟨s, hs⟩
      have hsa : (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) = s := congrArg Subtype.val ha
      rw [← hsa, he a]
      exact (Φ (h a)).2
  have hg : ψ e ∈ Subgroup.normalizer (Bs : Set G) := GGHalfTorusFrame.mem_normalizer hψ hgT
  have hgX : ψ e ∈ X := by
    rw [← hψ.range]
    exact ⟨e, rfl⟩
  refine ⟨ggConjAut Bs hg, ggConjAut_mem_ggAutomizer hgX hg, fun a c hb hc => ?_⟩
  rw [ggConjAut_apply]
  have hcomm : ψ e * c = c * ψ e := Subgroup.mem_centralizer_iff.mp hc (ψ e) hgX
  have hcinv : c * (ψ e)⁻¹ = (ψ e)⁻¹ * c := by
    calc c * (ψ e)⁻¹ = (ψ e)⁻¹ * (ψ e * c) * (ψ e)⁻¹ := by group
      _ = (ψ e)⁻¹ * (c * ψ e) * (ψ e)⁻¹ := by rw [hcomm]
      _ = (ψ e)⁻¹ * c := by group
  have hconj : ψ e * ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * (ψ e)⁻¹ =
      ψ (Φ (h a) : SpecialLinearGroup (Fin (n + 1)) F2) := by
    rw [← map_inv, ← map_mul, ← map_mul, he a]
  calc ψ e * (ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * c) * (ψ e)⁻¹
      = ψ e * ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * (c * (ψ e)⁻¹) := by group
    _ = ψ e * ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * ((ψ e)⁻¹ * c) := by
          rw [hcinv]
    _ = (ψ e * ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * (ψ e)⁻¹) * c := by group
    _ = ψ (Φ (h a) : SpecialLinearGroup (Fin (n + 1)) F2) * c := by rw [hconj]

end GGHalfTorusFrame

end CFSG.StandardType

end

module

public import CFSG.LocalAnalysis.StandardType.GGHalfWeylDefs
public import CFSG.LocalAnalysis.StandardType.GGHalfWeylTorusCoord
public import CFSG.LocalAnalysis.StandardType.GGHalfWeylInduced
public import CFSG.LocalAnalysis.StandardType.GGSpJoinOrbitBound
public import CFSG.LocalAnalysis.StandardType.GGSpJoinSignedPermGen

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf SpJoin

namespace GGHalfTorusFrame

theorem card_automizer_ge {G : Type} [Group G] [Finite G] {Bs X : Subgroup G} {n : ℕ}
    {ψ : SpecialLinearGroup (Fin (n + 1)) F2 →* G} (hψ : GGHalfTorusFrame Bs X (halfTorus n) ψ)
    (hn : 1 ≤ n) :
    2 ^ ((n + 1) / 2) * ((n + 1) / 2).factorial ≤ Nat.card (ggAutomizer X Bs) := by
  classical
  obtain ⟨Φ, hΦ⟩ := exists_torusCoord n
  have hTle : ∀ a : Fin ((n + 1) / 2) → Multiplicative (ZMod 3),
      ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) ∈ Bs := fun a =>
    hψ.torus_le (Subgroup.mem_map.mpr
      ⟨(Φ a : ↥(halfTorus n)), (Φ a).2, rfl⟩)
  let σ : ↥(spSignedGroup ((n + 1) / 2) 3) → ↥(ggAutomizer X Bs) := fun h =>
    ⟨Classical.choose (hψ.exists_aut_signed Φ hΦ h.1 h.2),
      (Classical.choose_spec (hψ.exists_aut_signed Φ hΦ h.1 h.2)).1⟩
  have hσspec : ∀ (h : ↥(spSignedGroup ((n + 1) / 2) 3))
      (a : Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) (c : G)
      (hb : ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * c ∈ Bs),
      c ∈ Subgroup.centralizer (X : Set G) →
      ((((σ h : ↥(ggAutomizer X Bs)) : MulAut ↥Bs)
          ⟨ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * c, hb⟩ : ↥Bs) : G) =
        ψ (Φ (h.1 a) : SpecialLinearGroup (Fin (n + 1)) F2) * c := by
    intro h a c hb hc
    exact (Classical.choose_spec (hψ.exists_aut_signed Φ hΦ h.1 h.2)).2 a c hb hc
  have hinj : Function.Injective σ := by
    intro h h' heq
    apply Subtype.ext
    apply Equiv.ext
    intro a
    have hb : ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * 1 ∈ Bs := by
      simpa using hTle a
    have hmem : (1 : G) ∈ Subgroup.centralizer (X : Set G) := Subgroup.one_mem _
    have e1 := hσspec h a 1 hb hmem
    have e2 := hσspec h' a 1 hb hmem
    have hvaleq : (((σ h : ↥(ggAutomizer X Bs)) : MulAut ↥Bs)
          ⟨ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * 1, hb⟩ : ↥Bs)
        = (((σ h' : ↥(ggAutomizer X Bs)) : MulAut ↥Bs)
          ⟨ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * 1, hb⟩ : ↥Bs) := by
      rw [heq]
    have hψeq : ψ (Φ (h.1 a) : SpecialLinearGroup (Fin (n + 1)) F2)
        = ψ (Φ (h'.1 a) : SpecialLinearGroup (Fin (n + 1)) F2) := by
      have h3 : ψ (Φ (h.1 a) : SpecialLinearGroup (Fin (n + 1)) F2) * 1
          = ψ (Φ (h'.1 a) : SpecialLinearGroup (Fin (n + 1)) F2) * 1 := by
        rw [← e1, ← e2, hvaleq]
      simpa using h3
    have hhalf : (Φ (h.1 a) : ↥(halfTorus n)) = Φ (h'.1 a) :=
      Subtype.ext (hψ.inj hψeq)
    exact Φ.injective hhalf
  have hcard := Nat.card_le_card_of_injective σ hinj
  have hsp := two_pow_mul_factorial_le_card_spSignedGroup (n := (n + 1) / 2) (p := 3)
    Nat.prime_three (by norm_num)
  exact le_trans hsp hcard

end GGHalfTorusFrame

end CFSG.StandardType

end

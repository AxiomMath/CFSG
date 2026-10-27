module

public import CFSG.LocalAnalysis.StandardType.GGQ2SubStab
public import TauCeti.LinearAlgebra.Matrix.Cartan.Classical
import CFSG.LocalAnalysis.StandardType.GGLargeDepNoSymPerm
import CFSG.LocalAnalysis.StandardType.GGLargeDepOrder
import CFSG.LocalAnalysis.StandardType.GGRCMonomial
import CFSG.LocalAnalysis.StandardType.GGRCMonomialHom
import CFSG.LocalAnalysis.StandardType.GGRCPermMonomial
import Mathlib.RingTheory.Finiteness.Cardinality

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V]

theorem ggQ2TN_caseI (hK : GGReflClassOmegaLarge) [Module.Finite (ZMod 3) V]
    (A : Subgroup (V ≃ₗ[ZMod 3] V)) {m : ℕ} (hm : 11 ≤ m) (h3 : 3 ∣ m + 1)
    (hdim : Module.finrank (ZMod 3) V = m) (c : Fin m → V) (α : Fin m → Module.Dual (ZMod 3) V)
    (hpair : ∀ i j, α i (c j) = (CartanMatrix.A m i j : ZMod 3))
    (s : Fin m → (V ≃ₗ[ZMod 3] V)) (hs : ∀ i v, s i v = v - α i v • c i) (hsA : ∀ i, s i ∈ A)
    (x : V) (hfix : ∀ z, (∀ i, α i z = 0) → z ∈ Submodule.span (ZMod 3) {x})
    (hconn : ∀ i j, Relation.ReflTransGen (fun a b => α a (c b) ≠ 0 ∧ α b (c a) ≠ 0) i j)
    (hH : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range c)) = m - 1)
    (hRx : ¬ ∀ r ∈ reflGp A, r x ∈ Submodule.span (ZMod 3) {x})
    (hcard : Nat.card A ≤ 3 ^ m * (3 * (m + 1).factorial))
    (hHR : ¬ ∀ r ∈ reflGp A, ∀ h ∈ Submodule.span (ZMod 3) (Set.range c),
      r h ∈ Submodule.span (ZMod 3) (Set.range c)) :
    False := by
  classical
  have hαc : ∀ i, α i (c i) = 2 := by
    intro i
    rw [hpair i i]
    simp [CartanMatrix.A]
  have hsRefl : ∀ i, IsReflLin (s i) := by
    intro i
    refine ⟨c i, α i, hαc i, ?_⟩
    ext v
    rw [Module.reflection_apply, hs i v]
  have hsR : ∀ i, s i ∈ reflGp A := by
    intro i
    exact Subgroup.subset_closure ⟨hsA i, hsRefl i⟩
  have : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  have hW : ∀ W : Submodule (ZMod 3) V,
      (∀ r ∈ reflGp A, ∀ w ∈ W, r w ∈ W) →
      Submodule.span (ZMod 3) (Set.range c) ≤ W → W = ⊤ := by
    intro W hWs hHW
    by_contra hWne
    have hlt : Module.finrank (ZMod 3) W < Module.finrank (ZMod 3) V :=
      Submodule.finrank_lt hWne
    rw [hdim] at hlt
    have hle : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range c)) ≤
        Module.finrank (ZMod 3) W := Submodule.finrank_mono hHW
    rw [hH] at hle
    have heq : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range c)) =
        Module.finrank (ZMod 3) W := by
      rw [hH]
      omega
    have hWH : Submodule.span (ZMod 3) (Set.range c) = W :=
      Submodule.eq_of_le_of_finrank_eq hHW heq
    exact hHR (fun r hr h hh => by
      rw [hWH] at hh ⊢
      exact hWs r hr h hh)
  have habs : ZS.AbsIrred 3 (reflGp A) :=
    ggQ2Hyp_absIrred_of_stable (ι := Fin m) A c α hαc s hs hsR x hfix hconn hW hRx
  have hgen : reflGp A = Subgroup.closure {r | r ∈ reflGp A ∧ GGLinRefl r} :=
    ggWAut_reflGp_closure A
  have : Finite V := Module.finite_of_finite (ZMod 3)
  have : Finite (V ≃ₗ[ZMod 3] V) :=
    Finite.of_injective (fun g : V ≃ₗ[ZMod 3] V => (g : V → V)) DFunLike.coe_injective
  have : Finite A :=
    Finite.of_injective (fun a : A => (a : V ≃ₗ[ZMod 3] V)) Subtype.coe_injective
  have hcardR : Nat.card (reflGp A) ≤ 3 ^ m * (3 * (m + 1).factorial) :=
    (Subgroup.card_le_of_le (ggWAut_reflGp_le A)).trans hcard
  have hcontra : ¬ (3 ^ (m * (m - 1) / 2) ≤ 8 * Nat.card (reflGp A)) := by
    intro hord
    have hkey := l04fD3_key12 (p := 3) (N := m + 1) (by norm_num) (by omega)
    have hexp : ((m + 1) - 2) * ((m + 1) - 3) / 2 ≤ m * (m - 1) / 2 := by
      have h1 : (m + 1) - 2 = m - 1 := by omega
      have h2 : (m + 1) - 3 = m - 2 := by omega
      rw [h1, h2]
      have hmul : (m - 1) * (m - 2) ≤ m * (m - 1) := by
        calc (m - 1) * (m - 2) ≤ (m - 1) * m := Nat.mul_le_mul_left _ (by omega)
          _ = m * (m - 1) := Nat.mul_comm _ _
      exact Nat.div_le_div_right (c := 2) hmul
    have hle1 : 3 ^ (m * (m - 1) / 2) ≤ 8 * (3 ^ m * (3 * (m + 1).factorial)) :=
      hord.trans (Nat.mul_le_mul_left 8 hcardR)
    have hle2 : 8 * (3 ^ m * (3 * (m + 1).factorial)) ≤
        8 * (3 ^ (m + 1) * (6 * (3 - 1) * (2 ^ (m + 1) * (m + 1).factorial))) := by
      rw [pow_succ]
      have h12 : 1 ≤ 6 * (3 - 1) * 2 ^ (m + 1) := by
        have hpos : 0 < 6 * (3 - 1) * 2 ^ (m + 1) := by positivity
        omega
      have hstep : 3 * (m + 1).factorial ≤
          3 * (m + 1).factorial * (6 * (3 - 1) * 2 ^ (m + 1)) := by
        calc 3 * (m + 1).factorial = 3 * (m + 1).factorial * 1 := by ring
          _ ≤ 3 * (m + 1).factorial * (6 * (3 - 1) * 2 ^ (m + 1)) :=
              Nat.mul_le_mul_left _ h12
      calc 8 * (3 ^ m * (3 * (m + 1).factorial))
          ≤ 8 * (3 ^ m * (3 * (m + 1).factorial *
              (6 * (3 - 1) * 2 ^ (m + 1)))) :=
            Nat.mul_le_mul_left 8 (Nat.mul_le_mul_left (3 ^ m) hstep)
        _ = 8 * ((3 ^ m * 3) * (6 * (3 - 1) * (2 ^ (m + 1) * (m + 1).factorial))) := by
            ring
    have hle4 : 3 ^ (((m + 1) - 2) * ((m + 1) - 3) / 2) ≤ 3 ^ (m * (m - 1) / 2) :=
      Nat.pow_le_pow_right (by norm_num) hexp
    exact (Nat.lt_irrefl _) (lt_of_le_of_lt hle1 (hle2.trans_lt hkey) |>.trans_le hle4)
  rcases hK 3 (by decide) V m hdim (by omega) (reflGp A) habs hgen with
    h1 | ⟨-, h2⟩ | ⟨-, h3'⟩ | ⟨h4, -⟩ | ⟨h5, -⟩
  · obtain ⟨b, hmon⟩ := ggRC_monomial_of_imprimitive (p := 3) (n := m) hdim (reflGp A)
      habs hgen h1
    obtain ⟨π, -, -, hkercomm, -⟩ := ggRC_monomial_hom (p := 3) (n := m) b (reflGp A) hmon
    obtain ⟨ρ, -, hρmem, hρinj⟩ :=
      l04fD5_perm_embed (p := 3) (m := m) (V := V) (by decide) (by omega) hpair s hs
    have hclosure : Subgroup.closure (Set.range s) ≤ reflGp A := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact hsR i
    let ρ' : Equiv.Perm (Fin (m + 1)) →* reflGp A :=
      ρ.codRestrict (reflGp A) (fun σ => hclosure (hρmem σ))
    have hρ'inj : Function.Injective ρ' := by
      intro a b h
      apply hρinj
      exact congrArg Subtype.val h
    have hcomm : IsMulCommutative (π.comp ρ').ker := by
      rw [isMulCommutative_iff]
      intro a b
      apply Subtype.ext
      apply hρ'inj
      have ha : ρ' (a : Equiv.Perm (Fin (m + 1))) ∈ π.ker :=
        MonoidHom.mem_ker.mpr a.2
      have hb : ρ' (b : Equiv.Perm (Fin (m + 1))) ∈ π.ker :=
        MonoidHom.mem_ker.mpr b.2
      have hcl := isMulCommutative_iff.mp hkercomm
        ⟨ρ' (a : Equiv.Perm (Fin (m + 1))), ha⟩
        ⟨ρ' (b : Equiv.Perm (Fin (m + 1))), hb⟩
      have hcl' : ρ' (a : Equiv.Perm (Fin (m + 1))) *
          ρ' (b : Equiv.Perm (Fin (m + 1))) =
          ρ' (b : Equiv.Perm (Fin (m + 1))) *
          ρ' (a : Equiv.Perm (Fin (m + 1))) :=
        congrArg Subtype.val hcl
      simpa only [Subgroup.coe_mul, map_mul] using hcl'
    exact ggRC_perm_not_monomial (N := m + 1) (m := m) (by omega) (by omega)
      (π.comp ρ') hcomm
  · exact hcontra h2
  · exact hcontra h3'
  · exact h4 h3
  · obtain ⟨k, hk⟩ := h3
    obtain ⟨l, hl⟩ := h5
    omega

end CFSG.StandardType

end

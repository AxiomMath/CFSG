module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearPostNineData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseFactorization
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Involution fusion in the linear second-case maximal subgroup

After equation (9), the ambient Sylow two-subgroup satisfies `S ≤ E ≤ M`.
Thus every involution of `M` can be moved by Sylow conjugacy in `M` into
`S`, hence into the selected component `E`, where the component fusion
theorem conjugates it to `t`.
-/

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-- In the aligned linear branch, any two involutions of `M` are conjugate
inside `M`. -/
public theorem secondCase_linear_M_involutions_conjugate
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (post : SecondCaseLinearPostNineData c w d K) :
    ∀ a b : G, a ∈ w.M → IsInvolution a → b ∈ w.M → IsInvolution b →
      ∃ n : G, n ∈ w.M ∧ n * a * n⁻¹ = b := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSleM : (c.S : Subgroup G) ≤ w.M :=
    post.hSleE.trans d.E_component.1
  let SM : Sylow 2 w.M := c.S.subtype hSleM
  have hfuse_t : ∀ a : G, a ∈ w.M → IsInvolution a →
      ∃ n : G, n ∈ w.M ∧ n * a * n⁻¹ = c.t := by
    intro a haM haI
    let aM : w.M := ⟨a, haM⟩
    have haMI : IsInvolution aM := by
      constructor
      · intro ha1
        exact haI.1 (congrArg Subtype.val ha1)
      · apply Subtype.ext
        exact haI.2
    have haOrder : orderOf aM = 2 :=
      orderOf_eq_prime haMI.2 haMI.1
    let A2 : Subgroup w.M := Subgroup.zpowers aM
    have hA2card : Nat.card A2 = 2 := by
      rw [Nat.card_zpowers, haOrder]
    have hA2p : IsPGroup 2 A2 :=
      IsPGroup.of_card (G := A2) (p := 2) (n := 1) (by
        simpa using hA2card)
    obtain ⟨Q, hA2leQ⟩ := hA2p.exists_le_sylow
    obtain ⟨m, hm⟩ :=
      @MulAction.IsPretransitive.exists_smul_eq w.M (Sylow 2 w.M)
        inferInstance inferInstance Q SM
    have haQ : aM ∈ (Q : Subgroup w.M) :=
      hA2leQ (Subgroup.mem_zpowers aM)
    have hmaQ : m * aM * m⁻¹ ∈ ((m • Q : Sylow 2 w.M) : Subgroup w.M) := by
      rw [Sylow.coe_subgroup_smul]
      change m * aM * m⁻¹ ∈
        (Q : Subgroup w.M).map (MulAut.conj m).toMonoidHom
      exact Subgroup.mem_map.mpr ⟨aM, haQ, rfl⟩
    have hmaSM : m * aM * m⁻¹ ∈ (SM : Subgroup w.M) := by
      rwa [hm] at hmaQ
    let ma : G := (m : G) * a * (m : G)⁻¹
    have hmaS : ma ∈ (c.S : Subgroup G) := by
      exact hmaSM
    have hmaE : ma ∈ d.E := post.hSleE hmaS
    have hmaI : IsInvolution ma := by
      constructor
      · intro h1
        apply haI.1
        have h := congrArg (fun z : G => (m : G)⁻¹ * z * (m : G)) h1
        simpa [ma, mul_assoc] using h
      · calc
          ma ^ 2 = (m : G) * (a ^ 2) * (m : G)⁻¹ := by
            simp only [pow_two]
            dsimp [ma]
            group
          _ = 1 := by rw [haI.2]; simp
    obtain ⟨e0, he0E, he0⟩ :=
      secondCase_involutions_fused w d ma hmaE hmaI
    refine ⟨e0 * (m : G), w.M.mul_mem (d.E_component.1 he0E) m.2, ?_⟩
    calc
      (e0 * (m : G)) * a * (e0 * (m : G))⁻¹ = e0 * ma * e0⁻¹ := by
        simp [ma, mul_assoc]
      _ = c.t := he0
  intro a b haM haI hbM hbI
  obtain ⟨x, hxM, hxa⟩ := hfuse_t a haM haI
  obtain ⟨y, hyM, hyb⟩ := hfuse_t b hbM hbI
  refine ⟨y⁻¹ * x, w.M.mul_mem (w.M.inv_mem hyM) hxM, ?_⟩
  have hb : b = y⁻¹ * c.t * y := by
    calc
      b = y⁻¹ * (y * b * y⁻¹) * y := by group
      _ = y⁻¹ * c.t * y := by rw [hyb]
  calc
    (y⁻¹ * x) * a * (y⁻¹ * x)⁻¹ = y⁻¹ * (x * a * x⁻¹) * y := by group
    _ = y⁻¹ * c.t * y := by rw [hxa]
    _ = b := hb.symm

end CFSG.GorensteinWalter

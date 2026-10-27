module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvertedInfVU
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The two-core cannot centralize an outside-inverted odd subgroup
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- A nonidentity element of `V = O₂(Ĥ)` cannot centralize a nontrivial odd
subgroup of `Ĥ` inverted by an involution outside `Ĥ`. -/
public theorem firstCase_klein_twoCore_not_centralize_inverted_subgroup
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    {y : G} (hy : IsInvolution y) (hyH : y ∉ c.Hhat)
    {X : Subgroup G} (hXne : X ≠ ⊥) (hXle : X ≤ c.Hhat)
    (hXodd : Nat.Coprime 2 (Nat.card X))
    (hXinv : ∀ x : G, x ∈ X → x ∈ invertedElements c.Hhat y)
    {v : G} (hvV : v ∈ twoCoreOf c.Hhat) (hvne : v ≠ 1) :
    ¬ (∀ x : G, x ∈ X → v * x * v⁻¹ = x) := by
  classical
  intro hvCent
  let V : Subgroup G := twoCoreOf c.Hhat
  let B : Subgroup G := V ⊔ c.U
  have hXinf : X ⊓ B = ⊥ := by
    simpa [V, B] using
      firstCase_klein_inverted_subgroup_inf_VU_eq_bot
        hmin c hfirst hklein hy hyH hXle hXinv
  have hVK : IsKleinFour V := by
    simpa [V] using firstCase_klein_V_klein c hklein
  have hvI : IsInvolution v := by
    refine ⟨hvne, ?_⟩
    simpa [pow_two, V] using
      congrArg Subtype.val (hVK.mul_self (⟨v, hvV⟩ : V))
  have hVcent : V ≤ Subgroup.centralizer (c.U : Set G) := by
    have h26 := theorem_2_6 hmin c
    simpa [V, h26.1] using twoCoreOf_centralizes_oddCoreOf c.Hhat
  have hVleS : V ≤ (c.S : Subgroup G) := by
    dsimp [V]
    rw [← (theorem_2_6 hmin c).2.1]
    exact inf_le_left
  have hVne : V ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card V = 1 := by rw [hbot]; simp
    have hfour : Nat.card V = 4 := hVK.card_four
    omega
  have hUne : c.U ≠ ⊥ := (lemma_2_2 hmin c).2
  have hNormU : Subgroup.normalizer (c.U : Set G) = c.Hhat :=
    theorem26_normalizer_U_eq_Hhat hmin c hVne hUne
  have htV : c.t ∈ V := by
    exact centralizerStructure_t_mem_twoCore c (theorem_2_6 hmin c)
  have hvC : v ∈ (c.S : Subgroup G) ⊓
      Subgroup.centralizer (c.U : Set G) :=
    ⟨hVleS hvV, hVcent hvV⟩
  have htC : c.t ∈ (c.S : Subgroup G) ⊓
      Subgroup.centralizer (c.U : Set G) :=
    ⟨hVleS htV, hVcent htV⟩
  obtain ⟨a, haH, hav⟩ := theorem26_involutions_in_C_conjugate
    hmin c hNormU hvI c.t_involution hvC htC
  let Xa : Subgroup G := conjugateSubgroup X a
  have hXaH : Xa ≤ c.H := by
    intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨x, hx, hzx⟩
    rw [c.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
    have hvx : v * x = x * v := by
      have h := hvCent x hx
      exact mul_inv_eq_iff_eq_mul.mp (by simpa [mul_assoc] using h)
    have hzx' : z = a * x * a⁻¹ := by
      simpa [Xa, conjugateSubgroup] using hzx.symm
    rw [hzx', ← hav]
    change (a * x * a⁻¹) * (a * v * a⁻¹) =
      (a * v * a⁻¹) * (a * x * a⁻¹)
    calc
      (a * x * a⁻¹) * (a * v * a⁻¹) = a * (x * v) * a⁻¹ := by group
      _ = a * (v * x) * a⁻¹ := by rw [hvx]
      _ = (a * v * a⁻¹) * (a * x * a⁻¹) := by group
  have hXacard : Nat.card Xa = Nat.card X := by
    exact Nat.card_congr
      (Subgroup.equivMapOfInjective X (MulAut.conj a).toMonoidHom
        (MulAut.conj a).injective).toEquiv.symm
  have hXaU : Xa ≤ c.U :=
    odd_order_subgroup_le_U_of_H_eq_SU hmin c hXaH (by
      rw [hXacard]
      exact hXodd)
  have hUnormHhat : IsNormalIn c.U c.Hhat := by
    rw [(theorem_2_6 hmin c).1]
    refine ⟨Subgroup.map_subtype_le (pPrimeCore 2 c.Hhat), ?_⟩
    intro h hh u hu
    rcases Subgroup.mem_map.mp hu with ⟨u0, hu0, rfl⟩
    refine Subgroup.mem_map.mpr
      ⟨(⟨h, hh⟩ : c.Hhat) * u0 * (⟨h, hh⟩ : c.Hhat)⁻¹, ?_, by simp⟩
    exact (pPrimeCore_normal (p := 2) (G := c.Hhat)).conj_mem
      u0 hu0 (⟨h, hh⟩ : c.Hhat)
  have hXleU : X ≤ c.U := by
    intro x hx
    have hxa : a * x * a⁻¹ ∈ c.U :=
      hXaU (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
    have hback := hUnormHhat.2 a⁻¹ (c.Hhat.inv_mem haH)
      (a * x * a⁻¹) hxa
    simpa [mul_assoc] using hback
  apply hXne
  apply le_antisymm
  · intro x hx
    have hmem : x ∈ X ⊓ B :=
      ⟨hx, (show c.U ≤ B from le_sup_right) (hXleU hx)⟩
    rw [hXinf] at hmem
    exact hmem
  · exact bot_le

end CFSG.GorensteinWalter

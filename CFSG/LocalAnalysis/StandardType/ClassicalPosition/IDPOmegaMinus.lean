module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LieType.Universal.Spin.Twisted.Datum
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerMinus

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType

theorem exists_conj_eq_POmegaMinus (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2] {bq cq : F}
    (hirr : ∀ s : F, s ^ 2 + bq * s + cq ≠ 0) (hn : 4 ≤ n) {X : Type} [Group X]
    (ψ : ↥(spinGroup (Spin.quadMinus n F bq cq)) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) {b : X}
    (hb : GGPsiInnerDiag (Spin.Twisted.minusDatum n hirr) ψ b) :
    ∃ s : ↥(spinGroup (Spin.quadMinus n F bq cq)), ∀ u, b⁻¹ * ψ u * b = ψ (s * u * s⁻¹) := by
  obtain ⟨g, hg, hcent⟩ :=
    CFSG.StandardType.PsiDiag.SpinM.exists_mem_centralizer hirr hn ψ hψ hb
  obtain ⟨s, rfl⟩ := hg
  refine ⟨s, fun u => ?_⟩
  have hmem : ψ u ∈ (ψ.range : Set X) := ⟨u, rfl⟩
  have hc := Subgroup.mem_centralizer_iff.mp hcent (ψ u) hmem
  have hmain : b⁻¹ * ψ u * b = ψ s * ψ u * (ψ s)⁻¹ := by
    have h1 : b⁻¹ * (ψ u * (b * ψ s)) = ψ s * ψ u := by
      rw [hc]
      group
    rw [← h1]
    group
  rw [hmain, map_mul, map_mul, map_inv]

theorem conj_eq_unique_POmegaMinus (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2] {bq cq : F}
    (hirr : ∀ s : F, s ^ 2 + bq * s + cq ≠ 0) (hn : 4 ≤ n) {X : Type} [Group X]
    (ψ : ↥(spinGroup (Spin.quadMinus n F bq cq)) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) {s s' : ↥(spinGroup (Spin.quadMinus n F bq cq))}
    (hss' : ∀ u, ψ (s * u * s⁻¹) = ψ (s' * u * s'⁻¹)) : s = s' := by
  have hcenter : Subgroup.center ↥(spinGroup (Spin.quadMinus n F bq cq)) = ⊥ :=
    CFSG.StandardType.PsiDiag.SpinM.center_eq_bot hirr hn
  have hkerbot : ψ.ker = ⊥ := le_bot_iff.mp (hψ.trans (le_of_eq hcenter))
  have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hkerbot
  have key : ∀ u, (s'⁻¹ * s) * u * (s'⁻¹ * s)⁻¹ = u := by
    intro u
    have h := hss' u
    have hid : s * u * s⁻¹ = s' * ((s'⁻¹ * s) * u * (s'⁻¹ * s)⁻¹) * s'⁻¹ := by group
    rw [hid] at h
    have h' : s' * ((s'⁻¹ * s) * u * (s'⁻¹ * s)⁻¹) * s'⁻¹ = s' * u * s'⁻¹ := hinj h
    calc (s'⁻¹ * s) * u * (s'⁻¹ * s)⁻¹
        = s'⁻¹ * (s' * ((s'⁻¹ * s) * u * (s'⁻¹ * s)⁻¹) * s'⁻¹) * s' := by group
      _ = s'⁻¹ * (s' * u * s'⁻¹) * s' := by rw [h']
      _ = u := by group
  have hcomm : ∀ u, (s'⁻¹ * s) * u = u * (s'⁻¹ * s) := by
    intro u
    calc (s'⁻¹ * s) * u
        = (s'⁻¹ * s) * u * (s'⁻¹ * s)⁻¹ * (s'⁻¹ * s) := by group
      _ = u * (s'⁻¹ * s) := by rw [key u]
  have hw : (s'⁻¹ * s) ∈ Subgroup.center ↥(spinGroup (Spin.quadMinus n F bq cq)) :=
    Subgroup.mem_center_iff.mpr fun u => (hcomm u).symm
  have hw1 : s'⁻¹ * s = 1 := by
    rw [hcenter] at hw
    exact Subgroup.mem_bot.mp hw
  have hfin : s' * (s'⁻¹ * s) = s := by group
  rw [hw1, mul_one] at hfin
  exact hfin.symm

theorem conj_eq_commute_POmegaMinus (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2] {bq cq : F}
    (hirr : ∀ s : F, s ^ 2 + bq * s + cq ≠ 0) (hn : 4 ≤ n) {X : Type} [Group X]
    (ψ : ↥(spinGroup (Spin.quadMinus n F bq cq)) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) {b b' : X} (hbb' : Commute b b')
    {s s' : ↥(spinGroup (Spin.quadMinus n F bq cq))}
    (hs : ∀ u, b⁻¹ * ψ u * b = ψ (s * u * s⁻¹)) (hs' : ∀ u, b'⁻¹ * ψ u * b' = ψ (s' * u * s'⁻¹)) :
    Commute s s' := by
  have h1 : ∀ u, (b * b')⁻¹ * ψ u * (b * b') =
      ψ ((s' * s) * u * (s' * s)⁻¹) := by
    intro u
    calc (b * b')⁻¹ * ψ u * (b * b')
        = b'⁻¹ * (b⁻¹ * ψ u * b) * b' := by group
      _ = b'⁻¹ * ψ (s * u * s⁻¹) * b' := by rw [hs u]
      _ = ψ (s' * (s * u * s⁻¹) * s'⁻¹) := by rw [hs' (s * u * s⁻¹)]
      _ = ψ ((s' * s) * u * (s' * s)⁻¹) := by congr 1; group
  have h2 : ∀ u, (b' * b)⁻¹ * ψ u * (b' * b) =
      ψ ((s * s') * u * (s * s')⁻¹) := by
    intro u
    calc (b' * b)⁻¹ * ψ u * (b' * b)
        = b⁻¹ * (b'⁻¹ * ψ u * b') * b := by group
      _ = b⁻¹ * ψ (s' * u * s'⁻¹) * b := by rw [hs' u]
      _ = ψ (s * (s' * u * s'⁻¹) * s⁻¹) := by rw [hs (s' * u * s'⁻¹)]
      _ = ψ ((s * s') * u * (s * s')⁻¹) := by congr 1; group
  have hss'' : ∀ u, ψ ((s * s') * u * (s * s')⁻¹) = ψ ((s' * s) * u * (s' * s)⁻¹) := by
    intro u
    calc ψ ((s * s') * u * (s * s')⁻¹)
        = (b' * b)⁻¹ * ψ u * (b' * b) := (h2 u).symm
      _ = (b * b')⁻¹ * ψ u * (b * b') := by rw [hbb'.eq]
      _ = ψ ((s' * s) * u * (s' * s)⁻¹) := h1 u
  exact conj_eq_unique_POmegaMinus n hirr hn ψ hψ hss''

end CFSG.StandardType.ClassicalPosition

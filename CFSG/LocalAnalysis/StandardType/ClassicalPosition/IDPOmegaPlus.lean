module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LieType.Universal.Spin.Datum
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerSpin
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaSpin

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType

theorem exists_conj_eq_POmegaPlus (n : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2] (hn : 3 ≤ n)
    {X : Type} [Group X] (ψ : ↥(spinGroup (Spin.quadPlus n F)) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) {b : X}
    (hb : GGPsiInnerDiag (Spin.plusDatum n F hn) ψ b) :
    ∃ s : ↥(spinGroup (Spin.quadPlus n F)), ∀ u, b⁻¹ * ψ u * b = ψ (s * u * s⁻¹) := by
  obtain ⟨g, hg, hcent⟩ :=
    CFSG.StandardType.PsiDiag.SpinP.exists_mem_centralizer hn ψ hψ hb
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

theorem conj_eq_unique_POmegaPlus (n : ℕ) (F : Type) [Field F] [CharP F 2] (hn : 3 ≤ n)
    {X : Type} [Group X] (ψ : ↥(spinGroup (Spin.quadPlus n F)) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) {s s' : ↥(spinGroup (Spin.quadPlus n F))}
    (hss' : ∀ u, ψ (s * u * s⁻¹) = ψ (s' * u * s'⁻¹)) : s = s' := by
  have hcenter : Subgroup.center ↥(spinGroup (Spin.quadPlus n F)) = ⊥ :=
    CFSG.StandardType.RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo (n := n) (K := F) hn
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
  have hw : (s'⁻¹ * s) ∈ Subgroup.center ↥(spinGroup (Spin.quadPlus n F)) :=
    Subgroup.mem_center_iff.mpr fun u => (hcomm u).symm
  have hw1 : s'⁻¹ * s = 1 := by
    rw [hcenter] at hw
    exact Subgroup.mem_bot.mp hw
  have hfin : s' * (s'⁻¹ * s) = s := by group
  rw [hw1, mul_one] at hfin
  exact hfin.symm

theorem conj_eq_commute_POmegaPlus (n : ℕ) (F : Type) [Field F] [CharP F 2] (hn : 3 ≤ n)
    {X : Type} [Group X] (ψ : ↥(spinGroup (Spin.quadPlus n F)) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) {b b' : X} (hbb' : Commute b b')
    {s s' : ↥(spinGroup (Spin.quadPlus n F))}
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
  exact conj_eq_unique_POmegaPlus n F hn ψ hψ hss''

theorem exists_liftHom_POmegaPlus (n : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n) {X : Type} [Group X] (ψ : ↥(spinGroup (Spin.quadPlus n F)) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) (B : Subgroup X) [IsMulCommutative ↥B]
    (hB : ∀ b ∈ B, GGPsiInnerDiag (Spin.plusDatum n F hn) ψ b) :
    ∃ ℓ : ↥B →* ↥(spinGroup (Spin.quadPlus n F)),
      ∀ (b : ↥B) (u : ↥(spinGroup (Spin.quadPlus n F))),
        (b : X)⁻¹ * ψ u * (b : X) = ψ (ℓ b * u * (ℓ b)⁻¹) := by
  classical
  have hchoose : ∀ b : ↥B, ∃ s : ↥(spinGroup (Spin.quadPlus n F)),
      ∀ u : ↥(spinGroup (Spin.quadPlus n F)),
        (b : X)⁻¹ * ψ u * (b : X) = ψ (s * u * s⁻¹) :=
    fun b => exists_conj_eq_POmegaPlus n F hn ψ hψ (hB b b.2)
  let ℓ₀ : ↥B → ↥(spinGroup (Spin.quadPlus n F)) := fun b => Classical.choose (hchoose b)
  have hℓ₀ : ∀ (b : ↥B) (u : ↥(spinGroup (Spin.quadPlus n F))),
      (b : X)⁻¹ * ψ u * (b : X) = ψ (ℓ₀ b * u * (ℓ₀ b)⁻¹) :=
    fun b => Classical.choose_spec (hchoose b)
  have hone : ℓ₀ 1 = 1 := by
    apply conj_eq_unique_POmegaPlus n F hn ψ hψ (s' := 1)
    intro u
    rw [← hℓ₀ 1 u]
    simp
  have hmul : ∀ b b' : ↥B, ℓ₀ (b * b') = ℓ₀ b * ℓ₀ b' := by
    intro b b'
    have hanti : ℓ₀ (b' * b) = ℓ₀ b * ℓ₀ b' := by
      apply conj_eq_unique_POmegaPlus n F hn ψ hψ (s' := ℓ₀ b * ℓ₀ b')
      intro u
      calc ψ (ℓ₀ (b' * b) * u * (ℓ₀ (b' * b))⁻¹)
          = (↑(b' * b) : X)⁻¹ * ψ u * (↑(b' * b) : X) := (hℓ₀ (b' * b) u).symm
        _ = (b : X)⁻¹ * ((b' : X)⁻¹ * ψ u * (b' : X)) * (b : X) := by
              rw [Subgroup.coe_mul]; group
        _ = (b : X)⁻¹ * ψ (ℓ₀ b' * u * (ℓ₀ b')⁻¹) * (b : X) := by rw [hℓ₀ b' u]
        _ = ψ (ℓ₀ b * (ℓ₀ b' * u * (ℓ₀ b')⁻¹) * (ℓ₀ b)⁻¹) := by
              rw [hℓ₀ b (ℓ₀ b' * u * (ℓ₀ b')⁻¹)]
        _ = ψ ((ℓ₀ b * ℓ₀ b') * u * (ℓ₀ b * ℓ₀ b')⁻¹) := by congr 1; group
    calc ℓ₀ (b * b') = ℓ₀ (b' * b) := by
          rw [isMulCommutative_iff.mp inferInstance b b']
      _ = ℓ₀ b * ℓ₀ b' := hanti
  exact ⟨{ toFun := ℓ₀, map_one' := hone, map_mul' := hmul }, hℓ₀⟩

end CFSG.StandardType.ClassicalPosition

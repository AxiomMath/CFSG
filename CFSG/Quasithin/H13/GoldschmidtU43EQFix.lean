module

public import CFSG.Quasithin.H13.GoldschmidtU43EBasic

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

set_option synthInstance.maxSize 1024

theorem cube1_card_fixed_le : ∀ x : OC, Cube1 x.cols → x.cols ≠ idc →
    (Finset.univ.filter (fun ξ : V4 => app x.cols ξ = ξ)).card ≤ 4 := by
  decide +kernel

theorem card_fixed_Rbar_le {g : MulAut (Multiplicative V4)} (hg : g ∈ Rbar) (hne : g ≠ 1) :
    Nat.card {ξ : V4 // vapp g ξ = ξ} ≤ 4 := by
  have hcube : Cube1 (toOC ⟨g, hg.1⟩).cols := by
    rw [toOC_mk_cols, cube1_iff]
    exact hg.2
  have hne' : (toOC ⟨g, hg.1⟩).cols ≠ idc := by
    rw [toOC_mk_cols]
    exact fun h => hne ((cols_eq_idc_iff g).1 h)
  have key := cube1_card_fixed_le _ hcube hne'
  rw [toOC_mk_cols] at key
  have e : Nat.card {ξ : V4 // vapp g ξ = ξ} =
      (Finset.univ.filter (fun ξ : V4 => app (colsOf g) ξ = ξ)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp only [vapp_eq_app]
  rw [e]
  exact key

variable {G : Type} [Group G]

namespace JWSetup

variable {z : G} (S : JWSetup z)

@[expose] def Cg1 : Subgroup G := Subgroup.centralizer ({(S.σ₁ : G)} : Set G)

@[expose] def Yg : Subgroup G := Uz z ⊓ S.Cg1

theorem act_σ₁_mem_Rbar : S.hyp.act S.σ₁ ∈ Rbar := by
  refine ⟨S.hyp.act_mem_Oq S.σ₁, ?_⟩
  rw [← map_pow, S.jw.r1, map_one]

variable [Finite G]

theorem act_σ₁_ne_one : S.hyp.act S.σ₁ ≠ 1 := fun h1 =>
  S.σ₁_ne_one (S.hR.act_inj S.hσR h1)

theorem card_Yg_le : Nat.card S.Yg ≤ 8 := by
  classical
  have h := S.hyp
  set g₁ := h.act S.σ₁ with hg₁
  have hfix : ∀ u : ↥(Uz z), (u : G) ∈ S.Cg1 → vapp g₁ (h.tv u) = h.tv u := by
    intro u hu
    have hc : (u : G) * S.σ₁ = S.σ₁ * u := Subgroup.mem_centralizer_singleton_iff.mp hu
    have hconj : conjU S.σ₁ u = u := Subtype.ext (by
      rw [coe_conjU]
      calc (S.σ₁ : G) * u * (S.σ₁ : G)⁻¹ = ((u : G) * S.σ₁) * (S.σ₁ : G)⁻¹ := by rw [hc]
        _ = u := by group)
    have key := h.act_θ S.σ₁ u
    rw [hconj] at key
    show Multiplicative.toAdd (g₁ (Multiplicative.ofAdd (Multiplicative.toAdd (h.θ u)))) =
      Multiplicative.toAdd (h.θ u)
    rw [ofAdd_toAdd, key]
  have hYU : S.Yg ≤ Uz z := inf_le_left
  let ψ : ↥S.Yg →* Multiplicative V4 := h.θ.comp (Subgroup.inclusion hYU)
  have hker : Nat.card ψ.ker ≤ 2 := by
    let f : ψ.ker → Bool := fun y => decide ((y.1 : G) = 1)
    have hf : Function.Injective f := by
      intro y y' hyy
      have hz : ∀ w : ψ.ker, (w.1 : G) = 1 ∨ (w.1 : G) = z := fun w => by
        have hw : ψ w.1 = 1 := w.2
        exact (h.θ_eq_one_iff ⟨(w.1 : G), hYU w.1.2⟩).mp hw
      apply Subtype.ext
      apply Subtype.ext
      rcases hz y with h1 | h1 <;> rcases hz y' with h2 | h2
      · rw [h1, h2]
      · exfalso
        have : decide ((y.1 : G) = 1) = decide ((y'.1 : G) = 1) := hyy
        rw [h1] at this
        have h3 : (y'.1 : G) ≠ 1 := by
          rw [h2]
          exact h.z_ne_one
        simp [h3] at this
      · exfalso
        have : decide ((y.1 : G) = 1) = decide ((y'.1 : G) = 1) := hyy
        rw [h2] at this
        have h3 : (y.1 : G) ≠ 1 := by
          rw [h1]
          exact h.z_ne_one
        simp [h3] at this
      · rw [h1, h2]
    calc Nat.card ψ.ker ≤ Nat.card Bool := Nat.card_le_card_of_injective f hf
      _ = 2 := by simp
  have hrange : Nat.card ψ.range ≤ 4 := by
    have hne : g₁ ≠ 1 := S.act_σ₁_ne_one
    have hfixc := card_fixed_Rbar_le S.act_σ₁_mem_Rbar hne
    let f : ψ.range → {ξ : V4 // vapp g₁ ξ = ξ} := fun x =>
      ⟨Multiplicative.toAdd x.1, by
        obtain ⟨y, hy⟩ := x.2
        rw [← hy]
        exact hfix ⟨(y.1 : G), hYU y.2⟩ y.2.2⟩
    have hf : Function.Injective f := by
      intro x x' hxx
      apply Subtype.ext
      have := congrArg Subtype.val hxx
      exact Multiplicative.toAdd.injective this
    exact (Nat.card_le_card_of_injective f hf).trans hfixc
  have hmul := Subgroup.card_ker_mul_card_range ψ
  calc Nat.card S.Yg = Nat.card ψ.ker * Nat.card ψ.range := hmul.symm
    _ ≤ 2 * 4 := Nat.mul_le_mul hker hrange
    _ = 8 := by norm_num

end JWSetup

end CFSG.Quasithin.H13.U43

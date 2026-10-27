module

public import CFSG.RankThree.PartTwo.Sec21.Hering214Reduce
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open CFSG.Assembly (IsElemAbelian)
open CFSG.ComponentClassification.PerfectAutomorphisms
open scoped commutatorElement

section PerfectCover

variable {X Y : Type} [Group X] [Finite X] [Group Y]

theorem eq_one_of_onCenterQuotient_of_perfect [Group.IsPerfect X] {α : MulAut X}
    (h1 : onCenterQuotient α = 1) : α = 1 := by
  have hcent : ∀ x : X, x⁻¹ * α x ∈ Subgroup.center X := by
    intro x
    have hfixed : (QuotientGroup.mk' (Subgroup.center X)) (α x) =
        (QuotientGroup.mk' (Subgroup.center X)) x := by
      have hdescend := onCenterQuotient_apply_mk α x
      rw [h1] at hdescend
      exact hdescend.symm
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' (Subgroup.center X)) (x⁻¹ * α x) = 1
    rw [map_mul, map_inv, hfixed, inv_mul_cancel]
  let f : X →* Subgroup.center X :=
    { toFun := fun x => ⟨x⁻¹ * α x, hcent x⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        intro l r
        apply Subtype.ext
        change (l * r)⁻¹ * α (l * r) = (l⁻¹ * α l) * (r⁻¹ * α r)
        have hcomm := (Subgroup.mem_center_iff.mp (hcent l)) r⁻¹
        calc (l * r)⁻¹ * α (l * r) = r⁻¹ * (l⁻¹ * α l) * α r := by
              rw [map_mul]; group
          _ = (l⁻¹ * α l) * r⁻¹ * α r := by rw [hcomm]
          _ = (l⁻¹ * α l) * (r⁻¹ * α r) := mul_assoc _ _ _ }
  have hf : f = 1 := hom_eq_one_of_commutative f
  ext x
  have hx : f x = 1 := by rw [hf]; rfl
  have hx' : x⁻¹ * α x = 1 := congrArg Subtype.val hx
  have : α x = x := (inv_mul_eq_one.mp hx').symm
  simpa using this

theorem eInvFour_of_perfect_central_quotient [Group.IsPerfect X]
    (hZ3 : Nat.card (Subgroup.center X) = 3) (e : X ⧸ Subgroup.center X ≃* Y)
    (hY : ∀ Ē' Ū' : Subgroup (MulAut Y), BarData Y Ē' Ū' → EInvFour Y Ē')
    {Ē Ū : Subgroup (MulAut X)} (hd : BarData X Ē Ū) : EInvFour X Ē := by
  set q : X →* X ⧸ Subgroup.center X := QuotientGroup.mk' (Subgroup.center X) with hq
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hker : q.ker = Subgroup.center X := QuotientGroup.ker_mk' _
  set φ : MulAut X →* MulAut (X ⧸ Subgroup.center X) := centerQuotientHom X with hφ
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro α h
    exact eq_one_of_onCenterQuotient_of_perfect (h : onCenterQuotient α = 1)
  set ψ : MulAut X →* MulAut Y := (MulAut.congr e).toMonoidHom.comp φ with hψ
  have hψinj : Function.Injective ψ := (MulAut.congr e).injective.comp hφinj
  have hbar : BarData Y (Ē.map ψ) (Ū.map ψ) := by
    refine ⟨CFSG.Open.IsElemAbelian.map hd.elem3 ψ, ?_, CFSG.Open.IsElemAbelian.map hd.elem2 ψ,
      ?_, ?_, ?_⟩
    · rw [Subgroup.card_map_of_injective hψinj, hd.card9]
    · intro h
      apply hd.ne_bot
      rw [eq_bot_iff]
      intro u hu
      have : ψ u ∈ Ū.map ψ := ⟨u, hu, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      rw [Subgroup.mem_bot]
      exact hψinj (this.trans (map_one ψ).symm)
    · rw [Subgroup.card_map_of_injective hψinj]
      exact hd.card_le
    · intro x hx
      obtain ⟨σ, hσ, rfl⟩ := hx
      exact Subgroup.le_normalizer_map ψ ⟨σ, hd.norm hσ, rfl⟩
  obtain ⟨W, hW, hW4, hWinv, σ', hσ', w, hw, hne⟩ := hY _ _ hbar
  set WQ : Subgroup (X ⧸ Subgroup.center X) := W.map e.symm.toMonoidHom with hWQdef
  have hWQ : IsElemAbelian 2 WQ := CFSG.Open.IsElemAbelian.map hW _
  have hWQ4 : Nat.card WQ = 4 := by
    rw [hWQdef, Subgroup.card_map_of_injective e.symm.injective, hW4]
  have hmemWQ : ∀ y, y ∈ WQ ↔ e y ∈ W := by
    intro y
    constructor
    · rintro ⟨v, hv, rfl⟩
      simpa using hv
    · intro hy
      exact ⟨e y, hy, by simp⟩
  obtain ⟨S, hSmem, hSel, hS4, hSsurj⟩ := exists_lift_four (q := q) hqsurj
    (by rw [hker]) (by rw [hker, hZ3]; decide) hWQ hWQ4
  have hqα : ∀ (ρ : MulAut X) (x : X), q (ρ x) = φ ρ (q x) := fun ρ x =>
    (onCenterQuotient_apply_mk ρ x).symm
  have hψq : ∀ (ρ : MulAut X) (x : X), e (q (ρ x)) = ψ ρ (e (q x)) := by
    intro ρ x
    rw [hqα]
    simp [hψ, MulAut.congr_apply]
  refine ⟨S, hSel, hS4, ?_, ?_⟩
  · intro ρ hρ x hx
    rw [hSmem] at hx ⊢
    obtain ⟨hxW, hx4⟩ := hx
    refine ⟨?_, ?_⟩
    · rw [hmemWQ] at hxW ⊢
      rw [hψq]
      exact hWinv _ ⟨ρ, hρ, rfl⟩ _ hxW
    · rw [← map_pow, hx4, map_one]
  · obtain ⟨σ, hσ, rfl⟩ := hσ'
    obtain ⟨x, hxS, hxq⟩ := hSsurj (e.symm w) ((hmemWQ _).mpr (by simpa using hw))
    refine ⟨σ, hσ, x, hxS, fun h => hne ?_⟩
    have h1 : e (q (σ x)) = e (q x) := by rw [h]
    rw [hψq, hxq] at h1
    simpa using h1

end PerfectCover

end CFSG.RankThree.PartTwo.Sec21.Hering214

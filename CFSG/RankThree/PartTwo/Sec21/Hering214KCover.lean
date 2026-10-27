module

public import CFSG.RankThree.PartTwo.Sec21.Hering214KNine
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open CFSG.Assembly (IsElemAbelian)
open CFSG.ComponentClassification.PerfectAutomorphisms
open scoped commutatorElement

theorem isPerfect_of_simple_noncomm {K : Type*} [Group K] (hs : IsSimpleGroup K)
    (h : ∃ a b : K, a * b ≠ b * a) : Group.IsPerfect K := by
  refine Group.isPerfect_def.2 ?_
  rcases hs.eq_bot_or_eq_top_of_normal (commutator K) with h1 | h1
  · exfalso
    obtain ⟨a, b, hab⟩ := h
    apply hab
    have hmem : ⁅a, b⁆ ∈ commutator K :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rwa [h1, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  · exact h1

theorem isPerfect_of_mulEquiv {K L : Type*} [Group K] [Group L] (e : K ≃* L)
    (h : Group.IsPerfect K) : Group.IsPerfect L := by
  refine Group.isPerfect_def.2 ?_
  have h1 : commutator K = ⊤ := Group.isPerfect_def.1 h
  have h2 : (commutator K).map e.toMonoidHom = commutator L := by
    unfold commutator
    rw [Subgroup.map_commutator, Subgroup.map_top, MonoidHom.range_eq_top.2 e.surjective]
  rw [← h2, h1, Subgroup.map_top, MonoidHom.range_eq_top.2 e.surjective]

section Cover

variable {X : Type} [Group X]

theorem eq_one_or_eq_or_eq_inv_of_card_three {Z : Type*} [Group Z] (hZ : Nat.card Z = 3) {z : Z}
    (hz : z ≠ 1) (w : Z) : w = 1 ∨ w = z ∨ w = z⁻¹ := by
  have hfin : Finite Z := Nat.finite_of_card_ne_zero (by omega)
  have hz3 : z ^ 3 = 1 := by
    have := pow_card_eq_one' (G := Z) (x := z)
    rwa [hZ] at this
  have hzi1 : z⁻¹ ≠ 1 := inv_ne_one.mpr hz
  have hzz : z⁻¹ ≠ z := by
    intro h
    have h2 : z * z = 1 := by
      calc z * z = z * z⁻¹ := by rw [h]
        _ = 1 := mul_inv_cancel z
    apply hz
    calc z = z ^ 3 * (z * z)⁻¹ := by group
      _ = 1 := by rw [hz3, h2]; simp
  by_contra hcon
  push_neg at hcon
  obtain ⟨hw1, hwz, hwi⟩ := hcon
  let f : Fin 4 → Z := ![1, z, z⁻¹, w]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [f] at hij ⊢ <;>
      first
      | exact absurd hij (Ne.symm hz)
      | exact absurd hij hz
      | exact absurd hij (Ne.symm hzi1)
      | exact absurd hij hzi1
      | exact absurd hij hzz
      | exact absurd hij (Ne.symm hzz)
      | exact absurd hij (Ne.symm hw1)
      | exact absurd hij hw1
      | exact absurd hij (Ne.symm hwz)
      | exact absurd hij hwz
      | exact absurd hij (Ne.symm hwi)
      | exact absurd hij hwi
  have := Nat.card_le_card_of_injective f hf
  simp [hZ] at this

theorem apply_eq_self_of_mem_center (hZ3 : Nat.card (Subgroup.center X) = 3) {α : MulAut X}
    (h3 : α ^ 3 = 1) {z : X} (hz : z ∈ Subgroup.center X) : α z = z := by
  by_cases hz1 : z = 1
  · rw [hz1, map_one]
  have hαz : α z ∈ Subgroup.center X := by
    have hmap := (Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : (Subgroup.center X).Characteristic)) α
    rw [← hmap]
    exact ⟨z, hz, rfl⟩
  have hα3 : ∀ x : X, α (α (α x)) = x := fun x => by
    have := congrArg (fun f : MulAut X => f x) h3
    simpa [pow_succ, MulAut.mul_apply] using this
  have hz1' : (⟨z, hz⟩ : Subgroup.center X) ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  rcases eq_one_or_eq_or_eq_inv_of_card_three hZ3 hz1' ⟨α z, hαz⟩ with h | h | h
  · exfalso
    have : α z = 1 := congrArg Subtype.val h
    apply hz1
    have h0 : α (α (α z)) = 1 := by rw [this, map_one, map_one]
    rw [← hα3 z, h0]
  · exact congrArg Subtype.val h
  · exfalso
    have hαz' : α z = z⁻¹ := congrArg Subtype.val h
    have hα2 : α (α z) = z := by rw [hαz', map_inv, hαz', inv_inv]
    have hα3z : α (α (α z)) = z⁻¹ := by rw [hα2, hαz']
    rw [hα3 z] at hα3z
    have hz3 : z ^ 3 = 1 := by
      have := pow_card_eq_one' (G := Subgroup.center X) (x := ⟨z, hz⟩)
      rw [hZ3] at this
      simpa using congrArg Subtype.val this
    have h2 : z * z = 1 := by
      calc z * z = z⁻¹ * z := by rw [← hα3z]
        _ = 1 := inv_mul_cancel z
    apply hz1
    calc z = z ^ 3 * (z * z)⁻¹ := by group
      _ = 1 := by rw [hz3, h2]; simp

theorem eq_one_of_pow_three_of_onCenterQuotient [Finite X]
    (hZ3 : Nat.card (Subgroup.center X) = 3) (hperf : Group.IsPerfect (X ⧸ Subgroup.center X))
    {α : MulAut X} (h3 : α ^ 3 = 1) (h1 : onCenterQuotient α = 1) : α = 1 := by
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
  have hfZ : Subgroup.center X ≤ f.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    change z⁻¹ * α z = 1
    rw [apply_eq_self_of_mem_center hZ3 h3 hz, inv_mul_cancel]
  let f' : (X ⧸ Subgroup.center X) →* Subgroup.center X := QuotientGroup.lift _ f hfZ
  have hf' : f' = 1 := hom_eq_one_of_commutative f'
  ext x
  have hx : f x = 1 := by
    have := congrArg (fun g : (X ⧸ Subgroup.center X) →* Subgroup.center X => g (x : X ⧸ _)) hf'
    simpa [f'] using this
  have hx' : x⁻¹ * α x = 1 := congrArg Subtype.val hx
  have : α x = x := (inv_mul_eq_one.mp hx').symm
  simpa using this

end Cover

section Transfer

variable {X Y : Type} [Group X] [Finite X] [Group Y]

theorem eInvNine_of_central_quotient (hZ3 : Nat.card (Subgroup.center X) = 3)
    (hperf : Group.IsPerfect (X ⧸ Subgroup.center X)) (e : X ⧸ Subgroup.center X ≃* Y)
    (hY : EInvNine Y) : EInvNine X := by
  intro Ē hE3 hE9
  have hQ : EInvNine (X ⧸ Subgroup.center X) := EInvNine.of_mulEquiv e hY
  set q : X →* X ⧸ Subgroup.center X := QuotientGroup.mk' (Subgroup.center X) with hq
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hker : q.ker = Subgroup.center X := QuotientGroup.ker_mk' _
  set φ : MulAut X →* MulAut (X ⧸ Subgroup.center X) := centerQuotientHom X with hφ
  have hφinj : Function.Injective (φ.comp Ē.subtype) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨α, hα⟩ h
    apply Subtype.ext
    have h1 : onCenterQuotient α = 1 := h
    exact eq_one_of_pow_three_of_onCenterQuotient hZ3 hperf (hE3.2 α hα) h1
  have hcard : Nat.card (Ē.map φ) = 9 := by
    have hrange : (φ.comp Ē.subtype).range = Ē.map φ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hE9, ← hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv).symm
  obtain ⟨W, hW, hW4, hWinv, σ', hσ', w, hw, hne⟩ :=
    hQ (Ē.map φ) (CFSG.Open.IsElemAbelian.map hE3 φ) hcard
  obtain ⟨S, hSmem, hSel, hS4, hSsurj⟩ := exists_lift_four (q := q) hqsurj
    (by rw [hker]) (by rw [hker, hZ3]; decide) hW hW4
  have hqα : ∀ (ρ : MulAut X) (x : X), q (ρ x) = φ ρ (q x) := fun ρ x =>
    (onCenterQuotient_apply_mk ρ x).symm
  refine ⟨S, hSel, hS4, ?_, ?_⟩
  · intro ρ hρ x hx
    rw [hSmem] at hx ⊢
    refine ⟨?_, ?_⟩
    · rw [hqα]
      exact hWinv _ ⟨ρ, hρ, rfl⟩ _ hx.1
    · rw [← map_pow, hx.2, map_one]
  · obtain ⟨σ, hσ, rfl⟩ := hσ'
    obtain ⟨x, hxS, hxq⟩ := hSsurj w hw
    refine ⟨σ, hσ, x, hxS, fun h => hne ?_⟩
    rw [← hxq, ← hqα, h]

end Transfer

end CFSG.RankThree.PartTwo.Sec21.Hering214

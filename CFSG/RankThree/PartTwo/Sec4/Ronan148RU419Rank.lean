module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RU419Tools
public import CFSG.RankThree.PartTwo.Sec4.Item47Kinds
import CFSG.RankThree.PartTwo.Sec4.Census.Lift46
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieE27
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowTools

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts

variable {X : Type} [Group X]

theorem card_map_conj_of_cfg {E Y : Subgroup X}
    (hEZ : ∀ z ∈ E, (∀ k ∈ Y, z * k = k * z) → z = 1) :
    Nat.card (E.map (MulAut.conj : X →* MulAut X)) = Nat.card E := by
  set f : E →* MulAut X := (MulAut.conj : X →* MulAut X).comp E.subtype with hf
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 : MulAut.conj ((a : X) * (b : X)⁻¹) = 1 := by
      have : MulAut.conj (a : X) = MulAut.conj (b : X) := hab
      rw [map_mul, map_inv, this, mul_inv_cancel]
    have hcen : ∀ k ∈ Y, ((a : X) * (b : X)⁻¹) * k = k * ((a : X) * (b : X)⁻¹) := by
      intro k _
      have h2 := congrArg (fun φ : MulAut X => φ k) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h2
      calc ((a : X) * (b : X)⁻¹) * k =
          ((a : X) * (b : X)⁻¹) * k * ((a : X) * (b : X)⁻¹)⁻¹ * ((a : X) * (b : X)⁻¹) := by
            group
        _ = k * ((a : X) * (b : X)⁻¹) := by rw [h2]
    have h3 := hEZ _ (mul_mem a.2 (inv_mem b.2)) hcen
    exact Subtype.ext (mul_inv_eq_one.mp h3)
  have hrange : E.map (MulAut.conj : X →* MulAut X) = f.range := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]

theorem false_of_cfg_of_le' [Finite X] (D : Subgroup (MulAut X))
    (hD : ∀ B ≤ D, (∀ b ∈ B, b ^ 3 = 1) → (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) → Nat.card B ≤ 9)
    (hinn : ∀ s : X, MulAut.conj s ∈ D) {α : MulAut X} (hαD : α ∈ D) {Y : Subgroup X} {m : ℕ}
    (hc : CfgU419 X α Y m) : False := by
  obtain ⟨E, hEY, hEc, hE3, hE9, hEZ⟩ := exists_e9_of_cfg hc
  have hfix : ∀ k ∈ Y, α k = k := fun k hk => hc.le_autFix hk
  set I : Subgroup (MulAut X) := E.map (MulAut.conj : X →* MulAut X) with hI
  have hI9 : Nat.card I = 9 := by rw [hI, card_map_conj_of_cfg hEZ, hE9]
  set S : Set (MulAut X) := insert α (I : Set (MulAut X)) with hS
  have hαI : ∀ y ∈ I, α * y = y * α := by
    rintro _ ⟨e, he, rfl⟩
    have h := mul_mulAutConj_mul_inv α e
    rw [hfix e (hEY he)] at h
    calc α * MulAut.conj e = α * MulAut.conj e * α⁻¹ * α := by group
      _ = MulAut.conj e * α := by rw [h]
  have hII : ∀ x ∈ I, ∀ y ∈ I, x * y = y * x := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
    rw [← map_mul, ← map_mul, hEc e he e' he']
  have hSc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    intro x hx y hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · rfl
    · exact hαI y hy
    · exact (hαI x hx).symm
    · exact hII x hx y hy
  have hS3 : ∀ x ∈ S, x ^ 3 = 1 := by
    intro x hx
    rcases hx with rfl | ⟨e, he, rfl⟩
    · exact hc.pow_three
    · rw [← map_pow, hE3 e he, map_one]
  set B : Subgroup (MulAut X) := Subgroup.closure S with hB
  have hBD : B ≤ D := by
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    rcases hx with rfl | ⟨e, -, rfl⟩
    · exact hαD
    · exact hinn e
  have hB9 := hD B hBD (fun b hb => RonanK429Lie.pow_three_of_mem_closure hSc hS3 hb)
    (fun a ha b hb => RonanK429Lie.commute_of_mem_closure hSc ha hb)
  have hIB : I ≤ B := fun x hx => Subgroup.subset_closure (Set.mem_insert_of_mem _ hx)
  have hIeq : I = B := Subgroup.eq_of_le_of_card_ge hIB (by rw [hI9]; exact hB9)
  have hαB : α ∈ B := Subgroup.subset_closure (Set.mem_insert _ _)
  rw [← hIeq] at hαB
  obtain ⟨e, he, rfl⟩ := hαB
  apply hc.ne_one
  have he1 : e = 1 := by
    refine hEZ e he (fun k hk => ?_)
    have h := hfix k hk
    simp only [MonoidHom.coe_coe, MulAut.conj_apply] at h
    calc e * k = e * k * e⁻¹ * e := by group
      _ = k * e := by rw [h]
  rw [he1, map_one]

theorem noCfgU419_of_autNoE27' [Finite X] (h : RonanK429.AutNoE27 X) : NoCfgU419 X := by
  intro α Y m hc
  have : Finite (MulAut X) :=
    Finite.of_injective (fun f : MulAut X => (f : X → X)) DFunLike.coe_injective
  exact false_of_cfg_of_le' ⊤ (fun B _ h3 hcomm =>
    card_le_nine_of_noE27 (fun E hE h27 => h E ⟨hE, h27⟩) h3 hcomm)
    (fun _ => Subgroup.mem_top _) (Subgroup.mem_top α) hc

theorem noCfgU419_of_noE27_of_cubeInner [Finite X] (hZ3 : IsPGroup 3 (Subgroup.center X))
    (hN : ∀ E : Subgroup X, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E ≠ 27)
    (hcube : CubeInner X) : NoCfgU419 X := by
  intro α Y m hc
  obtain ⟨E, hEY, hEc, hE3, hE9, hEZ⟩ := exists_e9_of_cfg hc
  have key : ∀ w : X, w ^ 3 = 1 → (∀ e ∈ E, w * e = e * w) → w ∈ E := by
    intro w hw3 hwc
    set S : Set X := insert w (E : Set X) with hS
    have hSc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
      intro x hx y hy
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · rfl
      · exact hwc y hy
      · exact (hwc x hx).symm
      · exact hEc x hx y hy
    have hS3 : ∀ x ∈ S, x ^ 3 = 1 := by
      intro x hx
      rcases hx with rfl | hx
      · exact hw3
      · exact hE3 x hx
    have hF9 := card_le_nine_of_noE27 hN
      (fun b hb => RonanK429Lie.pow_three_of_mem_closure hSc hS3 hb)
      (fun a ha b hb => RonanK429Lie.commute_of_mem_closure hSc ha hb)
    have hEF : E ≤ Subgroup.closure S :=
      fun x hx => Subgroup.subset_closure (Set.mem_insert_of_mem _ hx)
    have hEq : E = Subgroup.closure S := Subgroup.eq_of_le_of_card_ge hEF (by rw [hE9]; exact hF9)
    have hw : w ∈ Subgroup.closure S := Subgroup.subset_closure (Set.mem_insert _ _)
    rw [← hEq] at hw
    exact hw
  have hZ : Subgroup.center X = ⊥ := by
    by_contra hne
    have h3 : 3 ∣ Nat.card (Subgroup.center X) := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨k, hk⟩ := hZ3.exists_card_eq
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · exact absurd (Subgroup.eq_bot_of_card_eq _ (by rw [hk, h0, pow_zero])) hne
      · rw [hk]
        exact dvd_pow_self 3 hpos.ne'
    obtain ⟨z, hz, hz3⟩ := Census.exists_orderOf_eq_three_of_dvd h3
    have hzE := key z (by rw [← hz3]; exact pow_orderOf_eq_one z)
      (fun e _ => (Subgroup.mem_center_iff.mp hz e).symm)
    have hz1 := hEZ z hzE (fun k _ => (Subgroup.mem_center_iff.mp hz k).symm)
    rw [hz1, orderOf_one] at hz3
    omega
  obtain ⟨s, rfl⟩ := hcube α hc.pow_three
  have hs3 : s ^ 3 = 1 := by
    have h' : MulAut.conj (s ^ 3) = 1 := by rw [map_pow, hc.pow_three]
    have hzc : s ^ 3 ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun φ : MulAut X => φ g) h'
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc g * s ^ 3 = s ^ 3 * g * (s ^ 3)⁻¹ * s ^ 3 := by rw [this]
        _ = s ^ 3 * g := by group
    rw [hZ, Subgroup.mem_bot] at hzc
    exact hzc
  have hsY : ∀ k ∈ Y, s * k = k * s := by
    intro k hk
    have h : s * k * s⁻¹ = k := hc.le_autFix hk
    calc s * k = s * k * s⁻¹ * s := by group
      _ = k * s := by rw [h]
  have hsE := key s hs3 (fun e he => hsY e (hEY he))
  have hs1 := hEZ s hsE hsY
  exact hc.ne_one (by rw [hs1, map_one])

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

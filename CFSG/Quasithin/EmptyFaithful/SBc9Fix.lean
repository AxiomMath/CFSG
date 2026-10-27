module

public import CFSG.Quasithin.EmptyFaithful.SBc9Heart
import CFSG.LieType.SteinbergBRSmallAltSylow
import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.Quasithin

namespace SBc9

open CFSG.QuasithinUnique
open CFSG.LieType.SteinbergBR.SmallAlt
  (a6P a6P_mul a6P_inv a6P_one a6P_sign a6P_injective finSubgroup card_finSubgroup card_alternating)

section Standard

set_option maxRecDepth 100000 in
private theorem std_fixed_check :
    ∀ x x' : Fin 6 → ZMod 2, ∑ i, x i = 0 → ∑ i, x' i = 0 →
      (∀ g : Fin 8, ∀ i j : Fin 6, x ((a6P g)⁻¹ i) - x i = x ((a6P g)⁻¹ j) - x j) →
      (∀ g : Fin 8, ∀ i j : Fin 6, x' ((a6P g)⁻¹ i) - x' i = x' ((a6P g)⁻¹ j) - x' j) →
      (∀ i j, x i = x j) ∨ (∀ i j, x' i = x' j) ∨ (∀ i j, x i - x' i = x j - x' j) := by
  decide +kernel

private theorem sum_eq_zero_of_mem (x : ↥(evenWeight 6)) : ∑ i, (x : Fin 6 → ZMod 2) i = 0 := by
  simpa [evenWeight] using x.2

private theorem heartAct_mk_eq_iff (σ : Equiv.Perm (Fin 6)) (x : ↥(evenWeight 6)) :
    heartAct σ (QuotientAddGroup.mk x : AltHeart 6) = QuotientAddGroup.mk x ↔
      ∀ i j : Fin 6, (x : Fin 6 → ZMod 2) (σ⁻¹ i) - (x : Fin 6 → ZMod 2) i =
        (x : Fin 6 → ZMod 2) (σ⁻¹ j) - (x : Fin 6 → ZMod 2) j := by
  rw [heartAct_mk, QuotientAddGroup.eq_iff_sub_mem]
  exact Iff.rfl

private theorem mk_eq_zero_iff (x : ↥(evenWeight 6)) :
    (QuotientAddGroup.mk x : AltHeart 6) = 0 ↔
      ∀ i j : Fin 6, (x : Fin 6 → ZMod 2) i = (x : Fin 6 → ZMod 2) j := by
  rw [QuotientAddGroup.eq_zero_iff]
  exact Iff.rfl

private abbrev stdP : Subgroup (alternatingGroup (Fin 6)) :=
  finSubgroup a6P a6P_mul a6P_inv a6P_one

private theorem std_fixed_le_one {c e : AltHeart 6}
    (hc : ∀ g : Fin 8, heartAct (a6P g) c = c) (he : ∀ g : Fin 8, heartAct (a6P g) e = e) :
    c = 0 ∨ e = 0 ∨ c = e := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective c
  obtain ⟨x', rfl⟩ := QuotientAddGroup.mk_surjective e
  have key := std_fixed_check (x : Fin 6 → ZMod 2) (x' : Fin 6 → ZMod 2) (sum_eq_zero_of_mem x)
    (sum_eq_zero_of_mem x') (fun g => (heartAct_mk_eq_iff (a6P g) x).mp (hc g))
    (fun g => (heartAct_mk_eq_iff (a6P g) x').mp (he g))
  rcases key with h | h | h
  · exact Or.inl ((mk_eq_zero_iff x).mpr h)
  · exact Or.inr (Or.inl ((mk_eq_zero_iff x').mpr h))
  · refine Or.inr (Or.inr ?_)
    rw [QuotientAddGroup.eq_iff_sub_mem]
    exact h

end Standard

section Conjugation

private theorem card_stdP : Nat.card stdP = 8 :=
  card_finSubgroup _ _ _ _ a6P_injective fun i =>
    (Equiv.Perm.mem_alternatingGroup).2 (a6P_sign i)

private theorem card_alt6 : Nat.card (alternatingGroup (Fin 6)) = 8 * 45 := by
  have := card_alternating (m := 6) (by norm_num)
  rw [show Nat.factorial 6 = 720 by decide] at this
  omega

private theorem stdP_isSylowTwoOf : IsSylowTwoOf stdP ⊤ := by
  refine ⟨le_top, IsPGroup.of_card (n := 3) (by rw [card_stdP]; norm_num), ?_⟩
  have h1 : (stdP.subgroupOf ⊤).index = stdP.index :=
    Subgroup.relIndex_top_right stdP
  have h2 := Subgroup.card_mul_index stdP
  rw [card_stdP, card_alt6] at h2
  rw [h1]
  have h3 : stdP.index = 45 := by omega
  rw [h3]
  decide

private theorem std_fixes_of_conj {T : Subgroup (alternatingGroup (Fin 6))}
    {g : alternatingGroup (Fin 6)} (hg : T = B6.conjSub g stdP) {v : AltHeart 6}
    (hv : ∀ t ∈ T, heartAct (t : Equiv.Perm (Fin 6)) v = v) (i : Fin 8) :
    heartAct (a6P i) (heartAct (g : Equiv.Perm (Fin 6))⁻¹ v) =
      heartAct (g : Equiv.Perm (Fin 6))⁻¹ v := by
  let p : alternatingGroup (Fin 6) := ⟨a6P i, (Equiv.Perm.mem_alternatingGroup).2 (a6P_sign i)⟩
  have hp : p ∈ stdP := ⟨i, rfl⟩
  have ht : g * p * g⁻¹ ∈ T := by
    rw [hg, B6.mem_conjSub]
    simpa [mul_assoc] using hp
  have h1 := hv _ ht
  have h2 : (p : Equiv.Perm (Fin 6)) * (g : Equiv.Perm (Fin 6))⁻¹ =
      (g : Equiv.Perm (Fin 6))⁻¹ *
        ((g * p * g⁻¹ : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) := by
    simp [mul_assoc]
  show heartAct (p : Equiv.Perm (Fin 6)) (heartAct (g : Equiv.Perm (Fin 6))⁻¹ v) = _
  rw [← heartAct_mul, h2, heartAct_mul, h1]

end Conjugation

theorem heart_fixed_le_one {T : Subgroup (alternatingGroup (Fin 6))} (hT : IsSylowTwoOf T ⊤)
    {c e : AltHeart 6} (hc : ∀ t ∈ T, heartAct (t : Equiv.Perm (Fin 6)) c = c)
    (he : ∀ t ∈ T, heartAct (t : Equiv.Perm (Fin 6)) e = e) :
    c = 0 ∨ e = 0 ∨ c = e := by
  obtain ⟨g, -, hg⟩ := B6.isSylowTwoOf_exists_conj stdP_isSylowTwoOf hT
  rcases std_fixed_le_one (std_fixes_of_conj hg hc) (std_fixes_of_conj hg he) with h | h | h
  · left
    have h' := congrArg (heartAct (g : Equiv.Perm (Fin 6))) h
    rwa [heartAct_apply_inv, map_zero] at h'
  · right
    left
    have h' := congrArg (heartAct (g : Equiv.Perm (Fin 6))) h
    rwa [heartAct_apply_inv, map_zero] at h'
  · right
    right
    have h' := congrArg (heartAct (g : Equiv.Perm (Fin 6))) h
    rwa [heartAct_apply_inv, heartAct_apply_inv] at h'

section Fixed

private theorem heart_add_self (a : AltHeart 6) : a + a = 0 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective a
  rw [← QuotientAddGroup.mk_add]
  have hx : x + x = 0 := by
    apply Subtype.ext
    funext i
    have h : ∀ b : ZMod 2, b + b = 0 := by decide
    exact h _
  rw [hx, QuotientAddGroup.mk_zero]

private def fixedHeart (Y : Subgroup (alternatingGroup (Fin 6))) : AddSubgroup (AltHeart 6) where
  carrier := {v | ∀ y ∈ Y, heartAct (y : Equiv.Perm (Fin 6)) v = v}
  zero_mem' := fun y _ => map_zero _
  add_mem' := fun {a b} ha hb y hy => by rw [map_add, ha y hy, hb y hy]
  neg_mem' := fun {a} ha y hy => by rw [map_neg, ha y hy]

private theorem mem_fixedHeart {Y : Subgroup (alternatingGroup (Fin 6))} {v : AltHeart 6} :
    v ∈ fixedHeart Y ↔ ∀ y ∈ Y, heartAct (y : Equiv.Perm (Fin 6)) v = v := Iff.rfl

private theorem heartAct_mem_fixedHeart {Y T : Subgroup (alternatingGroup (Fin 6))}
    (hN : ∀ τ ∈ T, ∀ y ∈ Y, τ * y * τ⁻¹ ∈ Y) {τ : alternatingGroup (Fin 6)} (hτ : τ ∈ T)
    {c : AltHeart 6} (hc : c ∈ fixedHeart Y) :
    heartAct (τ : Equiv.Perm (Fin 6)) c ∈ fixedHeart Y := by
  rw [mem_fixedHeart] at hc ⊢
  intro y hy
  have hy' : τ⁻¹ * y * τ ∈ Y := by simpa using hN τ⁻¹ (T.inv_mem hτ) y hy
  have h1 := hc _ hy'
  have h2 : (y : Equiv.Perm (Fin 6)) * (τ : Equiv.Perm (Fin 6)) =
      (τ : Equiv.Perm (Fin 6)) *
        ((τ⁻¹ * y * τ : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) := by
    simp [mul_assoc]
  rw [← heartAct_mul, h2, heartAct_mul, h1]

private theorem exists_fixed_of_invariant {T : Subgroup (alternatingGroup (Fin 6))}
    (hT : IsPGroup 2 T) (A : AddSubgroup (AltHeart 6))
    (hA : ∀ τ ∈ T, ∀ a ∈ A, heartAct (τ : Equiv.Perm (Fin 6)) a ∈ A) {u : AltHeart 6}
    (hu : u ∈ A) (hu0 : u ≠ 0) :
    ∃ a ∈ A, a ≠ 0 ∧ ∀ τ ∈ T, heartAct (τ : Equiv.Perm (Fin 6)) a = a := by
  have hcard : 2 ∣ Nat.card A := by
    have h2 : addOrderOf (⟨u, hu⟩ : A) = 2 := by
      refine addOrderOf_eq_prime ?_ ?_
      · rw [two_nsmul]
        exact Subtype.ext (heart_add_self u)
      · intro h
        exact hu0 (congrArg Subtype.val h)
    have h3 := addOrderOf_dvd_natCard (⟨u, hu⟩ : A)
    rwa [h2] at h3
  let _ : MulAction T A :=
    { smul := fun τ a =>
        ⟨heartAct ((τ : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) a, hA τ τ.2 a a.2⟩
      one_smul := fun a => Subtype.ext (by
        show heartAct (((1 : T) : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) a = a
        exact heartAct_one a)
      mul_smul := fun τ σ a => Subtype.ext (by
        show heartAct (((τ * σ : T) : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) a =
          heartAct ((τ : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6))
            (heartAct ((σ : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) a)
        exact heartAct_mul _ _ a) }
  have h0 : (0 : A) ∈ MulAction.fixedPoints T A := by
    rw [MulAction.mem_fixedPoints]
    intro τ
    exact Subtype.ext (map_zero _)
  obtain ⟨b, hb, hb0⟩ := hT.exists_fixed_point_of_prime_dvd_card_of_fixed_point A hcard h0
  refine ⟨b, b.2, fun h => hb0 (Subtype.ext h.symm), fun τ hτ => ?_⟩
  exact congrArg Subtype.val (MulAction.mem_fixedPoints.mp hb ⟨τ, hτ⟩)

end Fixed

theorem heart_noFixed_of_invariant {Y T : Subgroup (alternatingGroup (Fin 6))} (hT : IsSylowTwoOf T ⊤)
    (hN : ∀ τ ∈ T, ∀ y ∈ Y, τ * y * τ⁻¹ ∈ Y)
    (E : AddSubgroup (AltHeart 6)) (hE : E ≠ ⊥)
    (hET : ∀ τ ∈ T, ∀ e ∈ E, heartAct (τ : Equiv.Perm (Fin 6)) e ∈ E)
    (hCE : ∀ e ∈ E, (∀ y ∈ Y, heartAct (y : Equiv.Perm (Fin 6)) e = e) → e = 0) :
    ∀ u : AltHeart 6, (∀ y ∈ Y, heartAct (y : Equiv.Perm (Fin 6)) u = u) → u = 0 := by
  intro u hu
  by_contra hu0
  obtain ⟨c, hcC, hc0, hcT⟩ := exists_fixed_of_invariant hT.2.1 (fixedHeart Y)
    (fun τ hτ c hc => heartAct_mem_fixedHeart hN hτ hc) (mem_fixedHeart.mpr hu) hu0
  obtain ⟨⟨e₀, he₀⟩, he₀0⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.mp hE
  obtain ⟨e, heE, he0, heT⟩ := exists_fixed_of_invariant hT.2.1 E hET he₀
    (fun h => he₀0 (Subtype.ext h))
  have hce : c ≠ e := by
    rintro rfl
    exact hc0 (hCE _ heE (mem_fixedHeart.mp hcC))
  rcases heart_fixed_le_one hT hcT heT with h | h | h
  · exact hc0 h
  · exact he0 h
  · exact hce h

end SBc9

end CFSG.Quasithin

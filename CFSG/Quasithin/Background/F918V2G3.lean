module

public import CFSG.Quasithin.Background.F918L1
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.EmptyFaithful.S153ZD

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Pointwise

namespace Z391

variable {W : Type} [CommGroup W] [Finite W] {M T L : Subgroup (MulAut W)} {V : Subgroup W}

@[expose] def centTrivQ (M L : Subgroup (MulAut W)) : Subgroup (MulAut W) where
  carrier := {c | c ∈ M ∧ (∀ l ∈ L, c * l = l * c) ∧ ∀ w : W, c w * w⁻¹ ∈ fixV L}
  one_mem' := ⟨M.one_mem, fun l _ => by simp, fun w => by simp⟩
  mul_mem' := by
    rintro a b ⟨haM, haL, haQ⟩ ⟨hbM, hbL, hbQ⟩
    refine ⟨M.mul_mem haM hbM, fun l hl => ?_, fun w => ?_⟩
    · rw [mul_assoc, hbL l hl, ← mul_assoc, haL l hl, mul_assoc]
    · have h := (fixV L).mul_mem (haQ (b w)) (hbQ w)
      have e : (a * b) w * w⁻¹ = a (b w) * (b w)⁻¹ * (b w * w⁻¹) := by
        simp only [MulAut.mul_apply]
        group
      rw [e]
      exact h
  inv_mem' := by
    rintro a ⟨haM, haL, haQ⟩
    refine ⟨M.inv_mem haM, fun l hl => ?_, fun w => ?_⟩
    · have h := haL l hl
      calc a⁻¹ * l = a⁻¹ * (l * a) * a⁻¹ := by group
        _ = a⁻¹ * (a * l) * a⁻¹ := by rw [h]
        _ = l * a⁻¹ := by group
    · have h := (fixV L).inv_mem (haQ (a⁻¹ w))
      have e : a⁻¹ w * w⁻¹ = (a (a⁻¹ w) * (a⁻¹ w)⁻¹)⁻¹ := by
        rw [MulAut.apply_inv_self, mul_inv_rev, inv_inv, mul_comm]
      rw [e]
      exact h

theorem v2g_odd_trivial (hD : D3Std M L T L V) {c : MulAut W} (hc : c ∈ centTrivQ M L)
    (hodd : Odd (orderOf c)) : c = 1 := by
  obtain ⟨-, hVcomm, -, -⟩ := mem_irrPlus_top_iff.1 hD.hyp.irr
  have hMn : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L := fun m hm l hl =>
    ((Subgroup.mem_normalizer_iff.1 (hD.hyp.Mp_normal hm)) l).1 hl
  obtain ⟨hcM, hcL, hcQ⟩ := hc
  set A : Subgroup (MulAut W) := Subgroup.zpowers c with hA
  have hAle : A ≤ centTrivQ M L := Subgroup.zpowers_le.2 ⟨hcM, hcL, hcQ⟩
  have hAodd : Odd (Nat.card A) := by
    rw [hA, Nat.card_zpowers]
    exact hodd
  have hcompl := XMod.isCompl_fixed_commOf_of_odd (A := ↥A) (Q := W) hAodd hD.hyp.exp
  rw [fixed_eq_inf_fixV, top_inf_eq, commOf_eq_commSub] at hcompl
  have hsup : fixV A ⊔ commSub ⊤ A = ⊤ := hcompl.sup_eq_top
  have hcomm_le : commSub ⊤ A ≤ fixV L := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, -, rfl⟩
    exact (hAle hx).2.2 w
  have hAcomm : ∀ a ∈ A, ∀ l ∈ L, a * l = l * a := by
    intro a ha l hl
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    exact ((Commute.zpow_left (show Commute c l from hcL l hl) k))
  have hUinv : ∀ l ∈ L, ∀ w ∈ fixV A, l w ∈ fixV A := by
    intro l hl w hw a ha
    have := congrArg (fun φ : MulAut W => φ w) (hAcomm a ha l hl)
    simp only [MulAut.mul_apply] at this
    rw [this, hw a ha]
  have hLtop : commSub (⊤ : Subgroup W) L = ⊤ := by
    rw [← commV_eq_commSub]
    exact Z391.commV_eq_top hMn hVcomm hD.hyp.gen
  have hfix : fixV A = ⊤ := by
    refine top_unique ?_
    calc (⊤ : Subgroup W) = commSub ⊤ L := hLtop.symm
      _ = commSub (fixV A ⊔ commSub ⊤ A) L := by rw [hsup]
      _ = commSub (fixV A) L := commSub_sup_fixV hcomm_le
      _ ≤ fixV A := commSub_le_of_invariant hUinv
  ext w
  have := hfix ▸ (show w ∈ (⊤ : Subgroup W) from trivial)
  exact this c (Subgroup.mem_zpowers c)

theorem v2g_faithful_on_Q (hD : D3Std M L T L V) {c : MulAut W} (hcM : c ∈ M)
    (hcL : ∀ l ∈ L, c * l = l * c) (hcQ : ∀ w : W, c w * w⁻¹ ∈ fixV L) : c = 1 := by
  have hMn : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L := fun m hm l hl =>
    ((Subgroup.mem_normalizer_iff.1 (hD.hyp.Mp_normal hm)) l).1 hl
  have hFinv : ∀ g ∈ M, ∀ w ∈ fixV L, g w ∈ fixV L := by
    intro g hg w hw l hl
    have h1 : g⁻¹ * l * g⁻¹⁻¹ ∈ L := hMn g⁻¹ (M.inv_mem hg) l hl
    have h2 := congrArg (fun φ : W => g φ) (hw _ h1)
    simp only [← MulAut.mul_apply] at h2
    have h3 : g * (g⁻¹ * l * g⁻¹⁻¹) = l * g := by group
    rw [h3] at h2
    simpa [MulAut.mul_apply] using h2
  set K := centTrivQ M L with hK
  have hKM : K ≤ M := fun x hx => hx.1
  have key : ∀ g ∈ M, ∀ x ∈ K, g * x * g⁻¹ ∈ K := by
    rintro g hg x ⟨hxM, hxL, hxQ⟩
    refine ⟨M.mul_mem (M.mul_mem hg hxM) (M.inv_mem hg), fun l hl => ?_, fun w => ?_⟩
    · have hl' : g⁻¹ * l * g⁻¹⁻¹ ∈ L := hMn g⁻¹ (M.inv_mem hg) l hl
      have h := hxL _ hl'
      calc g * x * g⁻¹ * l = g * (x * (g⁻¹ * l * g⁻¹⁻¹)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * l * g⁻¹⁻¹) * x) * g⁻¹ := by rw [h]
        _ = l * (g * x * g⁻¹) := by group
    · have h := hFinv g hg _ (hxQ (g⁻¹ w))
      have e : (g * x * g⁻¹) w * w⁻¹ = g (x (g⁻¹ w) * (g⁻¹ w)⁻¹) := by
        simp only [MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self]
      rw [e]
      exact h
  have hKnorm : M ≤ Subgroup.normalizer (K : Set (MulAut W)) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => key g hg h hh, fun hh => ?_⟩
    have := key g⁻¹ (M.inv_mem hg) _ hh
    have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
    rwa [e] at this
  have hK2 : IsPGroup 2 K := by
    intro x
    obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd
      (n := orderOf (x : MulAut W)) (orderOf_pos _).ne'
    refine ⟨a, ?_⟩
    have hy : ((x : MulAut W) ^ (2 ^ a)) ∈ K := K.pow_mem x.2 _
    have hyo : orderOf ((x : MulAut W) ^ (2 ^ a)) = m := by
      rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) ⟨m, hord⟩, hord, Nat.mul_div_cancel_left _
        (pow_pos two_pos _)]
    have h1 := v2g_odd_trivial hD hy (hyo ▸ hm)
    exact Subtype.ext (by simpa using h1)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbot : K ≤ pCoreOf 2 M :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hKM hKnorm hK2
  rw [D31.pCoreOf_eq_bot hD.hyp] at hbot
  exact Subgroup.mem_bot.1 (hbot ⟨hcM, hcL, hcQ⟩)

end Z391

end CFSG.Quasithin

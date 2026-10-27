module

public import CFSG.LocalAnalysis.StandardType.GGFrameModelNum
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUCoord

public section

namespace CFSG.StandardType.FrameRoute

open CFSG UCoord

variable {d : ℕ}

@[expose] def sumZeroPermSet (d : ℕ) : Set (MulAut ↥(sumZero d 3)) :=
  Set.range (permAutVHom d 3)

private def frameAZ_coordDiffHom (i j : Fin d) :
    ↥(sumZero d 3) →* Multiplicative (ZMod 3) where
  toFun f := Multiplicative.ofAdd (crd f i - crd f j)
  map_one' := by
    rw [crd_one, crd_one, sub_self, ofAdd_zero]
  map_mul' f g := by
    rw [crd_mul, crd_mul, ← ofAdd_add]
    congr 1
    abel

private theorem frameAZ_coordDiffHom_ker {i j : Fin d} :
    (frameAZ_coordDiffHom (d := d) i j).ker =
      {f : ↥(sumZero d 3) | crd f i = crd f j} := by
  ext f
  change Multiplicative.ofAdd (crd f i - crd f j) = 1 ↔ crd f i = crd f j
  rw [show (1 : Multiplicative (ZMod 3)) = Multiplicative.ofAdd 0 from ofAdd_zero.symm,
    Multiplicative.ofAdd.injective.eq_iff, sub_eq_zero]

private theorem frameAZ_card_range_coordDiffHom {i j : Fin d} (hij : i ≠ j) :
    Nat.card (frameAZ_coordDiffHom (d := d) i j).range = 3 := by
  let δ := frameAZ_coordDiffHom (d := d) i j
  have h2 : δ (rootV i j) = Multiplicative.ofAdd (2 : ZMod 3) := by
    change Multiplicative.ofAdd (crd (rootV i j) i - crd (rootV i j) j) = _
    rw [crd_rootV_left hij, crd_rootV_right hij]
    norm_num
  have hne : δ (rootV i j) ≠ 1 := by
    rw [h2]
    show Multiplicative.ofAdd (2 : ZMod 3) ≠ Multiplicative.ofAdd 0
    rw [Ne, Multiplicative.ofAdd.injective.eq_iff]
    exact SpCoord.coord_two_ne_zero Nat.prime_three (by decide)
  have hmem : δ (rootV i j) ∈ δ.range := ⟨_, rfl⟩
  have hcard_target : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hdvd : Nat.card δ.range ∣ 3 := by
    have h := Subgroup.card_subgroup_dvd_card δ.range
    rwa [hcard_target] at h
  have hne_card : Nat.card δ.range ≠ 1 := by
    intro h1
    have hbot : δ.range = ⊥ := by
      rw [Subgroup.eq_bot_iff_card]
      exact h1
    have hmem' := hmem
    rw [hbot] at hmem'
    exact hne (by simpa using hmem')
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
  · exact absurd h hne_card
  · exact h

private theorem frameAZ_card_ker_coordDiffHom {i j : Fin d} (hij : i ≠ j) :
    Nat.card {f : ↥(sumZero d 3) // crd f i = crd f j} * 3 =
      Nat.card ↥(sumZero d 3) := by
  let δ := frameAZ_coordDiffHom (d := d) i j
  have hker : δ.ker = {f : ↥(sumZero d 3) | crd f i = crd f j} :=
    frameAZ_coordDiffHom_ker
  have hcard := Subgroup.card_ker_mul_card_range δ
  have hcard_eq : Nat.card ↥δ.ker =
      Nat.card {f : ↥(sumZero d 3) // crd f i = crd f j} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquiv (Equiv.refl _) (fun f => Iff.of_eq (congrArg (fun s => s f) hker))
  rw [hcard_eq, frameAZ_card_range_coordDiffHom hij] at hcard
  exact hcard

private theorem frameAZ_card_ker_eq_fix_swap {i j : Fin d} (hij : i ≠ j) :
    Nat.card {f : ↥(sumZero d 3) // crd f i = crd f j} =
      Nat.card {f : ↥(sumZero d 3) // permAutV (Equiv.swap i j) f = f} := by
  apply Nat.card_congr
  refine Equiv.subtypeEquiv (Equiv.refl _) fun f => ?_
  constructor
  · intro hf
    refine ext_crd fun k => ?_
    rw [crd_permAutV, Equiv.swap_inv]
    by_cases hk : k = i
    · rw [hk, Equiv.swap_apply_left]
      exact hf.symm
    · by_cases hk' : k = j
      · rw [hk', Equiv.swap_apply_right]
        exact hf
      · rw [Equiv.swap_apply_of_ne_of_ne hk hk']
  · intro hf
    have h := crd_apply_eq_of_fix hf i
    rw [Equiv.swap_apply_left] at h
    exact h.symm

private theorem frameAZ_card_fix_permAutV_swap {i j : Fin d} (hij : i ≠ j) :
    Nat.card {f : ↥(sumZero d 3) // permAutV (Equiv.swap i j) f = f} * 3 =
      Nat.card ↥(sumZero d 3) := by
  have h := frameAZ_card_ker_coordDiffHom (d := d) hij
  rw [frameAZ_card_ker_eq_fix_swap hij] at h
  exact h

private theorem frameAZ_eq_swap_of_fix_eq_ker {σ : Equiv.Perm (Fin d)} {i : Fin d}
    (hσσ : ∀ l : Fin d, σ (σ l) = l)
    (hEq : {f : ↥(sumZero d 3) | permAutV σ f = f} =
      {f : ↥(sumZero d 3) | crd f (σ i) = crd f i}) :
    σ = Equiv.swap i (σ i) := by
  have hfix_out : ∀ l : Fin d, l ≠ i → l ≠ σ i → σ l = l := by
    intro l hli hlj
    by_contra hl
    have hsi_ne_l : σ i ≠ l := fun h => hlj h.symm
    have hsi_ne_sl : σ i ≠ σ l := fun h => hli (σ.injective h.symm)
    have hi_ne_sl : i ≠ σ l := by
      intro h
      have h' : σ i = l := by
        calc σ i = σ (σ l) := by rw [h]
          _ = l := hσσ l
      exact hlj h'.symm
    have hwH : crd (rootV l (σ l) : ↥(sumZero d 3)) (σ i) =
        crd (rootV l (σ l) : ↥(sumZero d 3)) i := by
      rw [crd_rootV_other hsi_ne_l hsi_ne_sl, crd_rootV_other hli.symm hi_ne_sl]
    have hwFix : permAutV σ (rootV l (σ l) : ↥(sumZero d 3)) =
        rootV l (σ l) := by
      have hw : (rootV l (σ l) : ↥(sumZero d 3)) ∈
          {f : ↥(sumZero d 3) | permAutV σ f = f} := by
        rw [hEq]
        exact hwH
      exact hw
    rw [permAutV_rootV, hσσ l] at hwFix
    have hcoord := congrArg (fun f : ↥(sumZero d 3) => crd f l) hwFix
    rw [crd_rootV_right hl, crd_rootV_left (Ne.symm hl)] at hcoord
    exact (by decide : (-1 : ZMod 3) ≠ 1) hcoord
  refine Equiv.ext fun x => ?_
  by_cases hxi : x = i
  · rw [hxi, Equiv.swap_apply_left]
  · by_cases hxj : x = σ i
    · rw [hxj, hσσ i, Equiv.swap_apply_right]
    · rw [hfix_out x hxi hxj, Equiv.swap_apply_of_ne_of_ne hxi hxj]

theorem mem_modelReflSet_sumZeroPermSet_iff (u : MulAut ↥(sumZero d 3)) :
    u ∈ modelReflSet (sumZeroPermSet d) ↔
      ∃ a b : Fin d, a ≠ b ∧ u = permAutVHom d 3 (Equiv.swap a b) := by
  constructor
  · rintro ⟨huS, hu2, hufix⟩
    obtain ⟨σ, rfl⟩ := huS
    have hu2' : (permAutV σ : MulAut ↥(sumZero d 3)) ^ 2 = 1 := by
      simpa [permAutVHom_apply] using hu2
    have hufix' : Nat.card {f : ↥(sumZero d 3) // permAutV σ f = f} * 3 =
        Nat.card ↥(sumZero d 3) := by
      simpa [permAutVHom_apply] using hufix
    have hinj : Function.Injective (permAutV (d := d) (p := 3)) :=
      permAutV_injective (d := d) (p := 3) Nat.prime_three (by decide)
    have hσ2 : σ ^ 2 = 1 := by
      apply hinj
      rw [sq, permAutV_mul, permAutV_one]
      simpa [sq] using hu2'
    have hσne : σ ≠ 1 := by
      intro h1
      rw [h1, permAutV_one] at hufix'
      have hcard : Nat.card {f : ↥(sumZero d 3) // (1 : MulAut ↥(sumZero d 3)) f = f} =
          Nat.card ↥(sumZero d 3) :=
        Nat.card_congr (Equiv.subtypeUnivEquiv fun f => rfl)
      rw [hcard] at hufix'
      have hpos : 0 < Nat.card ↥(sumZero d 3) := Nat.card_pos
      omega
    obtain ⟨i, hi⟩ : ∃ i : Fin d, σ i ≠ i := by
      by_contra h
      push Not at h
      exact hσne (Equiv.ext h)
    have hsub : {f : ↥(sumZero d 3) | permAutV σ f = f} ⊆
        {f : ↥(sumZero d 3) | crd f (σ i) = crd f i} := by
      intro f hf
      exact crd_apply_eq_of_fix hf i
    have hcardEq : Nat.card {f : ↥(sumZero d 3) // permAutV σ f = f} =
        Nat.card {f : ↥(sumZero d 3) // crd f (σ i) = crd f i} := by
      apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 3)
      rw [hufix', frameAZ_card_ker_coordDiffHom (d := d) (i := σ i) (j := i) hi]
    have hEq : {f : ↥(sumZero d 3) | permAutV σ f = f} =
        {f : ↥(sumZero d 3) | crd f (σ i) = crd f i} := by
      refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
      rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
      exact hcardEq.ge
    have hσσ : ∀ l : Fin d, σ (σ l) = l := by
      intro l
      have h := congrArg (fun τ : Equiv.Perm (Fin d) => τ l) hσ2
      simpa [pow_two, Equiv.Perm.mul_apply] using h
    have hσeq : σ = Equiv.swap i (σ i) :=
      frameAZ_eq_swap_of_fix_eq_ker hσσ hEq
    refine ⟨i, σ i, Ne.symm hi, ?_⟩
    change permAutV σ = permAutV (Equiv.swap i (σ i))
    exact congrArg permAutV hσeq
  · rintro ⟨a, b, hab, rfl⟩
    change permAutV (Equiv.swap a b) ∈ modelReflSet (sumZeroPermSet d)
    refine ⟨⟨Equiv.swap a b, rfl⟩, ?_, frameAZ_card_fix_permAutV_swap hab⟩
    rw [sq, ← permAutV_mul, Equiv.swap_mul_self, permAutV_one]

end CFSG.StandardType.FrameRoute

end

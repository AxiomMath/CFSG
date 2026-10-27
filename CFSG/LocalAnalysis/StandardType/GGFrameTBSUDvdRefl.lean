module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUCoord
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGFrameModelNumSumZero

public section

namespace CFSG.StandardType.FrameRoute

open CFSG UCoord SpCoord
open Multiplicative

private lemma frameQP_pow_three (c : Multiplicative (ZMod 3)) : c ^ 3 = 1 := by
  refine Multiplicative.toAdd.injective ?_
  rw [toAdd_pow, toAdd_one, nsmul_eq_mul, ZMod.natCast_self, zero_mul]

private lemma frameQP_involution_iff {d : ℕ} {M : Type*} [Group M]
    {Φ : Equiv.Perm (Fin d) →* MulAut M} (hinj : Function.Injective Φ)
    (σ : Equiv.Perm (Fin d)) : (Φ σ) ^ 2 = 1 ↔ σ ^ 2 = 1 := by
  rw [← map_pow Φ σ 2]
  constructor
  · intro h
    exact hinj (h.trans (map_one Φ).symm)
  · intro h
    rw [h, map_one]

private lemma frameQP_const_eq_one {d : ℕ} {σ : Equiv.Perm (Fin d)} (hσ2 : σ ^ 2 = 1)
    (hd : d ≠ 0) {g : Fin d → Multiplicative (ZMod 3)} {c : Multiplicative (ZMod 3)}
    (hg : ∀ k : Fin d, g (σ⁻¹ k) * (g k)⁻¹ = c) : c = 1 := by
  have hσσ : ∀ l : Fin d, σ (σ l) = l := by
    intro l
    have h := congrArg (fun τ : Equiv.Perm (Fin d) => τ l) hσ2
    simpa [pow_two, Equiv.Perm.mul_apply] using h
  have hσinv : σ⁻¹ * σ⁻¹ = 1 := by
    have h : σ * σ = 1 := by rw [← pow_two]; exact hσ2
    have h2 : σ⁻¹ = σ := by
      refine Equiv.ext fun x => ?_
      have hx := Equiv.symm_apply_apply σ (σ x)
      rwa [hσσ x] at hx
    rw [h2, h]
  let k0 : Fin d := ⟨0, Nat.pos_of_ne_zero hd⟩
  have h1 := hg k0
  have h2 := hg (σ⁻¹ k0)
  have e1 : g (σ⁻¹ k0) = c * g k0 := mul_inv_eq_iff_eq_mul.mp h1
  have e2 : g (σ⁻¹ (σ⁻¹ k0)) = c * g (σ⁻¹ k0) := mul_inv_eq_iff_eq_mul.mp h2
  have e3 : g (σ⁻¹ (σ⁻¹ k0)) = g k0 := by
    rw [show σ⁻¹ (σ⁻¹ k0) = (σ⁻¹ * σ⁻¹) k0 from rfl, hσinv]
    rfl
  have hcc : c * c = 1 := by
    have h3 : g k0 = (c * c) * g k0 := by
      calc g k0 = g (σ⁻¹ (σ⁻¹ k0)) := e3.symm
        _ = c * g (σ⁻¹ k0) := e2
        _ = c * (c * g k0) := by rw [e1]
        _ = (c * c) * g k0 := by rw [mul_assoc]
    have h3' : (c * c) * g k0 = 1 * g k0 := by
      rw [one_mul]
      exact h3.symm
    exact mul_right_cancel h3'
  have hc3 : c ^ 3 = 1 := frameQP_pow_three c
  have h : c ^ 3 = c := by
    calc c ^ 3 = c ^ 2 * c := by rw [pow_succ]
      _ = 1 * c := by rw [pow_two, hcc]
      _ = c := one_mul c
  rw [← h]
  exact hc3

private lemma frameQP_fix_iff {G : Type} [Group G] {A : Subgroup G} {d : ℕ}
    {S : Subgroup (Fin d → Multiplicative (ZMod 3))}
    (hmem : ∀ (τ : Equiv.Perm (Fin d)) (f : Fin d → Multiplicative (ZMod 3)),
      f ∈ S → permAut τ f ∈ S)
    {Θ : ↥S →* ↥A}
    (hker : ∀ f : ↥S, Θ f = 1 ↔ ∃ c : Multiplicative (ZMod 3),
      (f : Fin d → Multiplicative (ZMod 3)) = fun _ => c)
    {Φ : Equiv.Perm (Fin d) →* MulAut ↥A}
    (hΦ : ∀ (τ : Equiv.Perm (Fin d)) (f g : ↥S),
      (g : Fin d → Multiplicative (ZMod 3)) =
        permAut τ (f : Fin d → Multiplicative (ZMod 3)) → Φ τ (Θ f) = Θ g)
    {σ : Equiv.Perm (Fin d)} (hσ2 : σ ^ 2 = 1) (f : ↥S) :
    Φ σ (Θ f) = Θ f ↔
      permAut σ (f : Fin d → Multiplicative (ZMod 3)) =
        (f : Fin d → Multiplicative (ZMod 3)) := by
  constructor
  · intro hfix
    by_cases hd : d = 0
    · subst hd
      exact Subsingleton.elim _ _
    · have hP : Φ σ (Θ f) =
          Θ ⟨permAut σ (f : Fin d → Multiplicative (ZMod 3)), hmem σ _ f.2⟩ :=
        hΦ σ f _ rfl
      have hΘ : Θ ⟨permAut σ (f : Fin d → Multiplicative (ZMod 3)), hmem σ _ f.2⟩ = Θ f :=
        hP.symm.trans hfix
      have hker1 : Θ (⟨permAut σ (f : Fin d → Multiplicative (ZMod 3)),
          hmem σ _ f.2⟩ * f⁻¹) = 1 := by
        rw [map_mul, map_inv, hΘ, mul_inv_cancel]
      obtain ⟨c, hc⟩ :=
        (hker (⟨permAut σ (f : Fin d → Multiplicative (ZMod 3)), hmem σ _ f.2⟩ * f⁻¹)).mp hker1
      have hc2 : permAut σ (f : Fin d → Multiplicative (ZMod 3)) *
          ((f : Fin d → Multiplicative (ZMod 3)))⁻¹ = (fun _ => c) := by
        rw [← hc, Subgroup.coe_mul, Subgroup.coe_inv]
        rfl
      have hc' : ∀ k : Fin d, (f : Fin d → Multiplicative (ZMod 3)) (σ⁻¹ k) *
          ((f : Fin d → Multiplicative (ZMod 3)) k)⁻¹ = c := by
        intro k
        have h1 := congrFun hc2 k
        simpa only [Pi.mul_apply, Pi.inv_apply, permAut_apply, Function.comp_apply] using h1
      have hc1 : c = 1 := frameQP_const_eq_one hσ2 hd hc'
      have hconst : (⟨permAut σ (f : Fin d → Multiplicative (ZMod 3)), hmem σ _ f.2⟩ * f⁻¹ :
          ↥S) = 1 := by
        refine Subtype.ext ?_
        rw [Subgroup.coe_one, hc, hc1]
        rfl
      have hthis : (⟨permAut σ (f : Fin d → Multiplicative (ZMod 3)), hmem σ _ f.2⟩ : ↥S) = f :=
        mul_inv_eq_one.mp hconst
      exact congrArg (fun g : ↥S => (g : Fin d → Multiplicative (ZMod 3))) hthis
  · intro hf
    have hP : Φ σ (Θ f) =
        Θ ⟨permAut σ (f : Fin d → Multiplicative (ZMod 3)), hmem σ _ f.2⟩ :=
      hΦ σ f _ rfl
    rw [hP, show (⟨permAut σ (f : Fin d → Multiplicative (ZMod 3)), hmem σ _ f.2⟩ : ↥S) = f
      from Subtype.ext hf]

private def frameQP_fixSubgroup {d : ℕ} (S : Subgroup (Fin d → Multiplicative (ZMod 3)))
    (σ : Equiv.Perm (Fin d)) : Subgroup ↥S :=
  { carrier := {f : ↥S | permAut σ (f : Fin d → Multiplicative (ZMod 3)) =
      (f : Fin d → Multiplicative (ZMod 3))}
    one_mem' := by
      show permAut σ ((1 : ↥S) : Fin d → Multiplicative (ZMod 3)) =
        ((1 : ↥S) : Fin d → Multiplicative (ZMod 3))
      rw [Subgroup.coe_one, map_one]
    mul_mem' := fun {a b} ha hb => by
      show permAut σ ((a * b : ↥S) : Fin d → Multiplicative (ZMod 3)) =
        ((a * b : ↥S) : Fin d → Multiplicative (ZMod 3))
      rw [Subgroup.coe_mul, map_mul, ha, hb]
    inv_mem' := fun {a} ha => by
      show permAut σ ((a⁻¹ : ↥S) : Fin d → Multiplicative (ZMod 3)) =
        ((a⁻¹ : ↥S) : Fin d → Multiplicative (ZMod 3))
      rw [Subgroup.coe_inv, map_inv, ha]
      rfl }

private def frameQP_fixSubgroupA {G : Type} [Group G] {A : Subgroup G} {d : ℕ}
    (Φ : Equiv.Perm (Fin d) →* MulAut ↥A) (σ : Equiv.Perm (Fin d)) : Subgroup ↥A :=
  { carrier := {b : ↥A | Φ σ b = b}
    one_mem' := by show Φ σ 1 = 1; rw [map_one]
    mul_mem' := fun {a b} ha hb => by
      show Φ σ (a * b) = a * b
      rw [map_mul, ha, hb]
    inv_mem' := fun {a} ha => by
      show Φ σ a⁻¹ = a⁻¹
      rw [map_inv, ha] }

private lemma frameQP_three_mul_iff {xF xA xT xS iF iT : ℕ}
    (hF : xF * iF = xA) (hT : xT * iT = xS) (hi : iF = iT)
    (hposF : 0 < xF) (hposT : 0 < xT) : xF * 3 = xA ↔ xT * 3 = xS := by
  have h1 : (xF * 3 = xA) ↔ 3 = iF := by
    rw [← hF]
    exact ⟨fun h => Nat.eq_of_mul_eq_mul_left hposF h, fun h => by rw [h]⟩
  have h2 : (xT * 3 = xS) ↔ 3 = iT := by
    rw [← hT]
    exact ⟨fun h => Nat.eq_of_mul_eq_mul_left hposT h, fun h => by rw [h]⟩
  rw [h1, h2, hi]

private lemma frameQP_card_iff {G : Type} [Group G] {A : Subgroup G} {d : ℕ}
    {S : Subgroup (Fin d → Multiplicative (ZMod 3))}
    (hmem : ∀ (τ : Equiv.Perm (Fin d)) (f : Fin d → Multiplicative (ZMod 3)),
      f ∈ S → permAut τ f ∈ S)
    {Θ : ↥S →* ↥A} (hΘ : Function.Surjective Θ)
    (hker : ∀ f : ↥S, Θ f = 1 ↔ ∃ c : Multiplicative (ZMod 3),
      (f : Fin d → Multiplicative (ZMod 3)) = fun _ => c)
    {Φ : Equiv.Perm (Fin d) →* MulAut ↥A}
    (hΦ : ∀ (τ : Equiv.Perm (Fin d)) (f g : ↥S),
      (g : Fin d → Multiplicative (ZMod 3)) =
        permAut τ (f : Fin d → Multiplicative (ZMod 3)) → Φ τ (Θ f) = Θ g)
    {σ : Equiv.Perm (Fin d)} (hσ2 : σ ^ 2 = 1) :
    Nat.card {b : ↥A // Φ σ b = b} * 3 = Nat.card ↥A ↔
      Nat.card {f : ↥S // permAut σ (f : Fin d → Multiplicative (ZMod 3)) =
        (f : Fin d → Multiplicative (ZMod 3))} * 3 = Nat.card ↥S := by
  classical
  haveI : Finite ↥A := Finite.of_surjective Θ hΘ
  have hmemT : ∀ f : ↥S, f ∈ frameQP_fixSubgroup S σ ↔
      permAut σ (f : Fin d → Multiplicative (ZMod 3)) =
        (f : Fin d → Multiplicative (ZMod 3)) := fun f => Iff.rfl
  have hmemF : ∀ b : ↥A, b ∈ frameQP_fixSubgroupA Φ σ ↔ Φ σ b = b := fun b => Iff.rfl
  have hmap : (frameQP_fixSubgroup S σ).map Θ = frameQP_fixSubgroupA Φ σ := by
    ext b
    constructor
    · rintro ⟨t, ht, rfl⟩
      rw [hmemF]
      have hP : Φ σ (Θ t) =
          Θ ⟨permAut σ (t : Fin d → Multiplicative (ZMod 3)), hmem σ _ t.2⟩ := hΦ σ t _ rfl
      rw [hP]
      exact congrArg Θ (Subtype.ext ((hmemT t).mp ht))
    · intro hb
      obtain ⟨t, ht⟩ := hΘ b
      refine ⟨t, (hmemT t).mpr ((frameQP_fix_iff hmem hker hΦ hσ2 t).mp ?_), ht⟩
      rw [ht]
      exact (hmemF b).mp hb
  have hkerT : Θ.ker ≤ frameQP_fixSubgroup S σ := by
    intro f hf
    rw [MonoidHom.mem_ker] at hf
    obtain ⟨c, hc⟩ := (hker f).mp hf
    exact (hmemT f).mpr (by
      rw [hc]
      funext k
      simp [permAut_apply])
  have hidx : (frameQP_fixSubgroupA Φ σ).index = (frameQP_fixSubgroup S σ).index := by
    rw [← hmap]
    exact Subgroup.index_map_eq (H := frameQP_fixSubgroup S σ) hΘ hkerT
  have hcardF : Nat.card ↥(frameQP_fixSubgroupA Φ σ) *
      (frameQP_fixSubgroupA Φ σ).index = Nat.card ↥A := Subgroup.card_mul_index _
  have hcardT : Nat.card ↥(frameQP_fixSubgroup S σ) *
      (frameQP_fixSubgroup S σ).index = Nat.card ↥S := Subgroup.card_mul_index _
  haveI : Nonempty ↥(frameQP_fixSubgroupA Φ σ) := ⟨⟨1, Subgroup.one_mem _⟩⟩
  haveI : Nonempty ↥(frameQP_fixSubgroup S σ) := ⟨⟨1, Subgroup.one_mem _⟩⟩
  have hposF : 0 < Nat.card ↥(frameQP_fixSubgroupA Φ σ) := Nat.card_pos
  have hposT : 0 < Nat.card ↥(frameQP_fixSubgroup S σ) := Nat.card_pos
  have hFcard : Nat.card {b : ↥A // Φ σ b = b} = Nat.card ↥(frameQP_fixSubgroupA Φ σ) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun b => (hmemF b).symm)
  have hTcard : Nat.card {f : ↥S // permAut σ (f : Fin d → Multiplicative (ZMod 3)) =
      (f : Fin d → Multiplicative (ZMod 3))} = Nat.card ↥(frameQP_fixSubgroup S σ) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun f => (hmemT f).symm)
  rw [hFcard, hTcard]
  exact frameQP_three_mul_iff hcardF hcardT hidx hposF hposT

private def frameQP_coordDiffHom {d : ℕ} (i j : Fin d) :
    (Fin d → Multiplicative (ZMod 3)) →* Multiplicative (ZMod 3) where
  toFun f := Multiplicative.ofAdd (toAdd (f i) - toAdd (f j))
  map_one' := by simp
  map_mul' f g := by
    rw [Pi.mul_apply, Pi.mul_apply, toAdd_mul, toAdd_mul, ← ofAdd_add]
    exact congrArg Multiplicative.ofAdd (by ring)

private theorem frameQP_coordDiffHom_ker {d : ℕ} {i j : Fin d} :
    (frameQP_coordDiffHom (d := d) i j).ker =
      {f : Fin d → Multiplicative (ZMod 3) | f i = f j} := by
  ext f
  change Multiplicative.ofAdd (toAdd (f i) - toAdd (f j)) = 1 ↔ f i = f j
  rw [show (1 : Multiplicative (ZMod 3)) = Multiplicative.ofAdd 0 from ofAdd_zero.symm,
    Multiplicative.ofAdd.injective.eq_iff, sub_eq_zero,
    Multiplicative.toAdd.injective.eq_iff]

private theorem frameQP_card_range_coordDiffHom {d : ℕ} {i j : Fin d} (hij : i ≠ j) :
    Nat.card (frameQP_coordDiffHom (d := d) i j).range = 3 := by
  let δ := frameQP_coordDiffHom (d := d) i j
  set w : Fin d → Multiplicative (ZMod 3) :=
    Pi.mulSingle i (ofAdd 1) * Pi.mulSingle j (ofAdd (-1)) with hw
  have h2 : δ w = Multiplicative.ofAdd (2 : ZMod 3) := by
    show Multiplicative.ofAdd (toAdd (w i) - toAdd (w j)) = Multiplicative.ofAdd 2
    congr 1
    rw [hw]
    simp [Pi.mul_apply, toAdd_mul, SpCoord.toAdd_mulSingle, Pi.mulSingle_eq_same,
      Pi.mulSingle_eq_of_ne (Ne.symm hij), Pi.mulSingle_eq_of_ne hij, toAdd_one, toAdd_ofAdd]
    decide
  have hne : δ w ≠ 1 := by
    rw [h2]
    show Multiplicative.ofAdd (2 : ZMod 3) ≠ Multiplicative.ofAdd 0
    rw [Ne, Multiplicative.ofAdd.injective.eq_iff]
    exact SpCoord.coord_two_ne_zero Nat.prime_three (by decide)
  have hmem : δ w ∈ δ.range := ⟨w, rfl⟩
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

private theorem frameQP_card_ker_coordDiffHom {d : ℕ} {i j : Fin d} (hij : i ≠ j) :
    Nat.card {f : Fin d → Multiplicative (ZMod 3) // f i = f j} * 3 =
      Nat.card (Fin d → Multiplicative (ZMod 3)) := by
  let δ := frameQP_coordDiffHom (d := d) i j
  have hker : δ.ker = {f : Fin d → Multiplicative (ZMod 3) | f i = f j} :=
    frameQP_coordDiffHom_ker
  have hcard := Subgroup.card_ker_mul_card_range δ
  have hcard_eq : Nat.card ↥δ.ker =
      Nat.card {f : Fin d → Multiplicative (ZMod 3) // f i = f j} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquiv (Equiv.refl _) (fun f => Iff.of_eq (congrArg (fun s => s f) hker))
  rw [hcard_eq, frameQP_card_range_coordDiffHom hij] at hcard
  exact hcard

private theorem frameQP_eq_swap_of_fix_eq_ker {d : ℕ} {σ : Equiv.Perm (Fin d)} {i : Fin d}
    (hσσ : ∀ l : Fin d, σ (σ l) = l)
    (hEq : {f : Fin d → Multiplicative (ZMod 3) | permAut σ f = f} =
      {f : Fin d → Multiplicative (ZMod 3) | f (σ i) = f i}) :
    σ = Equiv.swap i (σ i) := by
  have hσinv : σ⁻¹ = σ := by
    refine Equiv.ext fun x => ?_
    have h := Equiv.symm_apply_apply σ (σ x)
    rwa [hσσ x] at h
  have hfix_out : ∀ l : Fin d, l ≠ i → l ≠ σ i → σ l = l := by
    intro l hli hlj
    by_contra hl
    set w : Fin d → Multiplicative (ZMod 3) :=
      Pi.mulSingle l (ofAdd 1) * Pi.mulSingle (σ l) (ofAdd (-1)) with hw
    have hwl : w l = ofAdd 1 := by
      rw [hw]
      simp [Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (Ne.symm hl)]
    have hwsl : w (σ l) = ofAdd (-1) := by
      rw [hw]
      simp [Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hl]
    have hone : ∀ c : Fin d, c ≠ l → c ≠ σ l → w c = 1 := by
      intro c hcl hcsl
      rw [hw]
      simp [Pi.mul_apply, Pi.mulSingle_eq_of_ne hcl, Pi.mulSingle_eq_of_ne hcsl]
    have h2 : i ≠ σ l := by
      intro h
      apply hlj
      calc l = σ (σ l) := (hσσ l).symm
        _ = σ i := by rw [← h]
    have hwH : w (σ i) = w i := by
      rw [hone (σ i) (Ne.symm hlj) (fun h => hli (σ.injective h).symm), hone i (Ne.symm hli) h2]
    have hwfix : permAut σ w = w := by
      have hin : w ∈ {f : Fin d → Multiplicative (ZMod 3) | permAut σ f = f} := by
        rw [hEq]
        exact hwH
      exact hin
    have hcoord := congrFun hwfix (σ l)
    change w (σ⁻¹ (σ l)) = w (σ l) at hcoord
    rw [hσinv, hσσ l, hwl, hwsl] at hcoord
    exact absurd (Multiplicative.ofAdd.injective hcoord) (by decide)
  refine Equiv.ext fun x => ?_
  by_cases hxi : x = i
  · rw [hxi, Equiv.swap_apply_left]
  · by_cases hxj : x = σ i
    · rw [hxj, hσσ i, Equiv.swap_apply_right]
    · rw [hfix_out x hxi hxj, Equiv.swap_apply_of_ne_of_ne hxi hxj]

private lemma frameQP_permAut_one {d : ℕ} :
    (permAut (1 : Equiv.Perm (Fin d)) : MulAut (Fin d → Multiplicative (ZMod 3))) = 1 := by
  refine MulEquiv.ext fun f => ?_
  funext k
  simp [permAut_apply]

private theorem frameQP_topSpace_iff {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    (σ ^ 2 = 1 ∧ Nat.card {f : Fin d → Multiplicative (ZMod 3) // permAut σ f = f} * 3 =
        Nat.card (Fin d → Multiplicative (ZMod 3))) ↔
      ∃ a b : Fin d, a ≠ b ∧ σ = Equiv.swap a b := by
  constructor
  · rintro ⟨hσ2, hcard⟩
    have hσne : σ ≠ 1 := by
      intro h1
      rw [h1, frameQP_permAut_one] at hcard
      have hcard1 : Nat.card {f : Fin d → Multiplicative (ZMod 3) //
          (1 : MulAut (Fin d → Multiplicative (ZMod 3))) f = f} =
          Nat.card (Fin d → Multiplicative (ZMod 3)) :=
        Nat.card_congr (Equiv.subtypeUnivEquiv fun f => rfl)
      rw [hcard1] at hcard
      have hpos : 0 < Nat.card (Fin d → Multiplicative (ZMod 3)) := Nat.card_pos
      have h3 : 3 = 1 := Nat.eq_of_mul_eq_mul_left hpos (by rw [mul_one]; exact hcard)
      exact absurd h3 (by norm_num)
    obtain ⟨i, hi⟩ : ∃ i : Fin d, σ i ≠ i := by
      by_contra h
      push Not at h
      exact hσne (Equiv.ext h)
    have hσσ : ∀ l : Fin d, σ (σ l) = l := by
      intro l
      have h := congrArg (fun τ : Equiv.Perm (Fin d) => τ l) hσ2
      simpa [pow_two, Equiv.Perm.mul_apply] using h
    have hsub : {f : Fin d → Multiplicative (ZMod 3) | permAut σ f = f} ⊆
        {f : Fin d → Multiplicative (ZMod 3) | f (σ i) = f i} := by
      intro f hf
      have h1 := congrFun hf (σ i)
      rw [permAut_apply] at h1
      simpa using h1.symm
    have hσinv : σ⁻¹ = σ := by
      refine Equiv.ext fun x => ?_
      have h := Equiv.symm_apply_apply σ (σ x)
      rwa [hσσ] at h
    have hcardEq : Nat.card {f : Fin d → Multiplicative (ZMod 3) // permAut σ f = f} =
        Nat.card {f : Fin d → Multiplicative (ZMod 3) // f (σ i) = f i} := by
      apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 3)
      rw [hcard, frameQP_card_ker_coordDiffHom (i := σ i) (j := i) hi]
    have hEq : {f : Fin d → Multiplicative (ZMod 3) | permAut σ f = f} =
        {f : Fin d → Multiplicative (ZMod 3) | f (σ i) = f i} := by
      refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
      rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
      exact hcardEq.ge
    exact ⟨i, σ i, Ne.symm hi, frameQP_eq_swap_of_fix_eq_ker hσσ hEq⟩
  · rintro ⟨a, b, hab, hσ⟩
    refine ⟨?_, ?_⟩
    · rw [hσ, pow_two, Equiv.swap_mul_self]
    · rw [hσ]
      exact SpCoord.card_fix_permAut_swap (k := d) (p := 3) Nat.prime_three (by decide) hab

private theorem frameQP_fixCard_top {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    Nat.card {f : ↥(⊤ : Subgroup (Fin d → Multiplicative (ZMod 3))) //
      permAut σ (f : Fin d → Multiplicative (ZMod 3)) =
        (f : Fin d → Multiplicative (ZMod 3))} =
      Nat.card {f : Fin d → Multiplicative (ZMod 3) // permAut σ f = f} := by
  apply Nat.card_congr
  exact Equiv.subtypeEquiv Subgroup.topEquiv.toEquiv fun f => Iff.rfl

private theorem frameQP_card_top {d : ℕ} :
    Nat.card ↥(⊤ : Subgroup (Fin d → Multiplicative (ZMod 3))) =
      Nat.card (Fin d → Multiplicative (ZMod 3)) :=
  Nat.card_congr Subgroup.topEquiv.toEquiv

private theorem frameQP_top_iff {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    (σ ^ 2 = 1 ∧ Nat.card {f : ↥(⊤ : Subgroup (Fin d → Multiplicative (ZMod 3))) //
      permAut σ (f : Fin d → Multiplicative (ZMod 3)) =
        (f : Fin d → Multiplicative (ZMod 3))} * 3 =
        Nat.card ↥(⊤ : Subgroup (Fin d → Multiplicative (ZMod 3)))) ↔
      ∃ a b : Fin d, a ≠ b ∧ σ = Equiv.swap a b := by
  rw [frameQP_fixCard_top σ, frameQP_card_top]
  exact frameQP_topSpace_iff σ

private theorem frameQP_card_fixV_eq {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    Nat.card {f : ↥(sumZero d 3) // permAutV σ f = f} =
      Nat.card {f : ↥(sumZero d 3) // permAut σ (f : Fin d → Multiplicative (ZMod 3)) =
        (f : Fin d → Multiplicative (ZMod 3))} := by
  apply Nat.card_congr
  refine Equiv.subtypeEquiv (Equiv.refl _) fun f => ?_
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

private lemma frameQP_mem_modelReflSet_sumZero {d : ℕ} {σ : Equiv.Perm (Fin d)}
    (hσ2 : σ ^ 2 = 1)
    (hcard : Nat.card {f : ↥(sumZero d 3) // permAut σ (f : Fin d → Multiplicative (ZMod 3)) =
        (f : Fin d → Multiplicative (ZMod 3))} * 3 = Nat.card ↥(sumZero d 3)) :
    (permAutVHom d 3 σ) ∈ modelReflSet (sumZeroPermSet d) := by
  refine ⟨⟨σ, rfl⟩, ?_, ?_⟩
  · rw [permAutVHom_apply, sq,
      ← permAutV_mul, show σ * σ = 1 from by rw [← pow_two]; exact hσ2, permAutV_one]
  · rw [permAutVHom_apply, frameQP_card_fixV_eq σ]
    exact hcard

private lemma frameQP_sumZero_swap {d : ℕ} {σ : Equiv.Perm (Fin d)} {a b : Fin d}
    (hab : a ≠ b) (hσ : σ = Equiv.swap a b) :
    σ ^ 2 = 1 ∧ Nat.card {f : ↥(sumZero d 3) // permAut σ (f : Fin d → Multiplicative (ZMod 3)) =
        (f : Fin d → Multiplicative (ZMod 3))} * 3 = Nat.card ↥(sumZero d 3) := by
  refine ⟨?_, ?_⟩
  · rw [hσ, pow_two, Equiv.swap_mul_self]
  · rw [hσ, ← frameQP_card_fixV_eq (Equiv.swap a b)]
    have hu := (mem_modelReflSet_sumZeroPermSet_iff (permAutVHom d 3 (Equiv.swap a b))).mpr
      ⟨a, b, hab, rfl⟩
    simpa [permAutVHom_apply] using hu.2.2

private theorem frameQP_sumZero_iff {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    (σ ^ 2 = 1 ∧ Nat.card {f : ↥(sumZero d 3) // permAut σ (f : Fin d → Multiplicative (ZMod 3)) =
        (f : Fin d → Multiplicative (ZMod 3))} * 3 = Nat.card ↥(sumZero d 3)) ↔
      ∃ a b : Fin d, a ≠ b ∧ σ = Equiv.swap a b := by
  have hinjV : Function.Injective (permAutV : Equiv.Perm (Fin d) → MulAut ↥(sumZero d 3)) :=
    permAutV_injective (d := d) (p := 3) Nat.prime_three (by decide)
  constructor
  · rintro ⟨hσ2, hcard⟩
    obtain ⟨a, b, hab, hσab⟩ := (mem_modelReflSet_sumZeroPermSet_iff (permAutVHom d 3 σ)).mp
      (frameQP_mem_modelReflSet_sumZero hσ2 hcard)
    exact ⟨a, b, hab, hinjV (by simpa [permAutVHom_apply] using hσab)⟩
  · rintro ⟨a, b, hab, hσ⟩
    exact frameQP_sumZero_swap hab hσ

theorem isReflection_quotPerm_iff {G : Type} [Group G] {A : Subgroup G} {d : ℕ}
    {S : Subgroup (Fin d → Multiplicative (ZMod 3))} (hS : S = ⊤ ∨ S = sumZero d 3)
    {Θ : ↥S →* ↥A} (hΘ : Function.Surjective Θ)
    (hker : ∀ f : ↥S, Θ f = 1 ↔
      ∃ c : Multiplicative (ZMod 3), (f : Fin d → Multiplicative (ZMod 3)) = fun _ => c)
    {Φ : Equiv.Perm (Fin d) →* MulAut ↥A} (hinj : Function.Injective Φ)
    (hΦ : ∀ (σ : Equiv.Perm (Fin d)) (f g : ↥S),
      (g : Fin d → Multiplicative (ZMod 3)) = permAut σ (f : Fin d → Multiplicative (ZMod 3)) →
        Φ σ (Θ f) = Θ g)
    (σ : Equiv.Perm (Fin d)) :
    GGIsReflection 3 (Φ σ) ↔ ∃ a b : Fin d, a ≠ b ∧ σ = Equiv.swap a b := by
  classical
  rcases hS with rfl | rfl
  · have hmem : ∀ (τ : Equiv.Perm (Fin d)) (f : Fin d → Multiplicative (ZMod 3)),
        f ∈ (⊤ : Subgroup (Fin d → Multiplicative (ZMod 3))) → permAut τ f ∈ ⊤ :=
      fun _ _ _ => Subgroup.mem_top _
    rw [GGIsReflection]
    constructor
    · rintro ⟨h2, hcard⟩
      have hσ2 : σ ^ 2 = 1 := (frameQP_involution_iff hinj σ).mp h2
      exact (frameQP_top_iff σ).mp
        ⟨hσ2, (frameQP_card_iff hmem hΘ hker hΦ hσ2).mp hcard⟩
    · rintro ⟨a, b, hab, hσ⟩
      have hσ2 : σ ^ 2 = 1 := by rw [hσ, pow_two, Equiv.swap_mul_self]
      exact ⟨(frameQP_involution_iff hinj σ).mpr hσ2,
        (frameQP_card_iff hmem hΘ hker hΦ hσ2).mpr
          ((frameQP_top_iff σ).mpr ⟨a, b, hab, hσ⟩).2⟩
  · have hmem : ∀ (τ : Equiv.Perm (Fin d)) (f : Fin d → Multiplicative (ZMod 3)),
        f ∈ sumZero d 3 → permAut τ f ∈ sumZero d 3 :=
      fun τ f hf => permAut_mem_sumZero τ hf
    rw [GGIsReflection]
    constructor
    · rintro ⟨h2, hcard⟩
      have hσ2 : σ ^ 2 = 1 := (frameQP_involution_iff hinj σ).mp h2
      exact (frameQP_sumZero_iff σ).mp
        ⟨hσ2, (frameQP_card_iff hmem hΘ hker hΦ hσ2).mp hcard⟩
    · rintro ⟨a, b, hab, hσ⟩
      have hσ2 : σ ^ 2 = 1 := by rw [hσ, pow_two, Equiv.swap_mul_self]
      exact ⟨(frameQP_involution_iff hinj σ).mpr hσ2,
        (frameQP_card_iff hmem hΘ hker hΦ hσ2).mpr
          ((frameQP_sumZero_iff σ).mpr ⟨a, b, hab, hσ⟩).2⟩

end CFSG.StandardType.FrameRoute

end

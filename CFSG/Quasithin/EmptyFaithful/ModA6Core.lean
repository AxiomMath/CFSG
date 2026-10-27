module

public import CFSG.Quasithin.H13.A6Model
public import CFSG.Quasithin.EmptyFaithful.Der6CMod
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin.ModA6

open scoped Pointwise

open Equiv CFSG.Quasithin CFSG.Quasithin.H13.A6

private theorem exists_alt_wt_two_of_wt_four : ∀ x : P6, wt x = 4 →
    ∃ σ : Perm (Fin 6), σ ∈ alternatingGroup (Fin 6) ∧ wt (G6.permAct 6 σ x * x) = 2 := by
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

theorem core_le_of_invariant (M : Subgroup (G6.PermMod 6))
    (hinv : ∀ σ ∈ alternatingGroup (Fin 6), ∀ x ∈ M, G6.permAct 6 σ x ∈ M)
    {x : G6.PermMod 6} (hxM : x ∈ M) (hxcore : x ∈ G6.coreMod 6) (hx1 : x ≠ 1)
    (hxo : x ≠ G6.allOnes 6) : G6.coreMod 6 ≤ M := by
  have hpair : ∃ y ∈ M, wt y = 2 := by
    rcases wt_core x (G6.mem_coreMod.mp hxcore) hx1 hxo with h | h
    · exact ⟨x, hxM, h⟩
    · obtain ⟨σ, hσ, hw⟩ := exists_alt_wt_two_of_wt_four x h
      exact ⟨G6.permAct 6 σ x * x, M.mul_mem (hinv σ hσ x hxM) hxM, hw⟩
  obtain ⟨y, hyM, hy⟩ := hpair
  have hp01 : pv 0 1 ∈ M := by
    obtain ⟨σ, hσ, hσy⟩ := trans_two y hy
    have hσ' : σ⁻¹ ∈ alternatingGroup (Fin 6) := inv_mem hσ
    have := hinv σ⁻¹ hσ' y hyM
    rwa [← hσy, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply] at this
  have hall : ∀ z : G6.PermMod 6, wt z = 2 → z ∈ M := by
    intro z hz
    obtain ⟨σ, hσ, hσz⟩ := trans_two z hz
    rw [← hσz]
    exact hinv σ hσ _ hp01
  intro c hc
  rw [eq_prod_pv c (G6.mem_coreMod.mp hc)]
  have h1 : ∀ j : Fin 6, j ≠ 0 → ∀ k : ℕ, pv 0 j ^ k ∈ M := fun j hj k =>
    M.pow_mem (hall _ (wt_pv_zero j hj)) k
  exact M.mul_mem (M.mul_mem (M.mul_mem (M.mul_mem (h1 1 (by decide) _) (h1 2 (by decide) _))
    (h1 3 (by decide) _)) (h1 4 (by decide) _)) (h1 5 (by decide) _)

theorem exists_alt_ne_of_wt_two : ∀ x : P6, wt x = 2 →
    ∃ σ : Perm (Fin 6), σ ∈ alternatingGroup (Fin 6) ∧ G6.permAct 6 σ x ≠ x := by
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

theorem card_wt_two : (Finset.univ.filter fun y : P6 => wt y = 2).card = 15 := by
  decide +kernel

theorem card_core : Nat.card (G6.coreMod 6) = 32 := by
  show Nat.card {x : G6.PermMod 6 // x ∈ G6.coreMod 6} = 32
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

private theorem card_modEq_fixed {α : Type*} [Finite α] (f : α → α) (hf : f^[5] = id) :
    Nat.card α ≡ Nat.card {a // f a = a} [MOD 5] := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have hp : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let g : Function.End α := f
  have h5 : g ^ 5 ^ 1 = (1 : Function.End α) := by
    rw [pow_one]
    funext a
    exact congrFun hf a
  have h := Equiv.Perm.card_fixedPoints_modEq (α := α) (f := g) (p := 5) (n := 1) h5
  have e : Nat.card {a // f a = a} = Nat.card ↑(Function.fixedPoints g) :=
    Nat.card_congr (Equiv.refl _)
  rw [e, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact h

section Element

variable {W : Type*} [CommGroup W]

private def cm (x : MulAut W) : W →* W where
  toFun w := x w * w⁻¹
  map_one' := by simp
  map_mul' a b := by
    simp only [map_mul, mul_inv_rev]
    rw [mul_comm b⁻¹ a⁻¹]
    exact mul_mul_mul_comm (x a) (x b) a⁻¹ b⁻¹

private theorem cm_apply (x : MulAut W) (w : W) : cm x w = x w * w⁻¹ := rfl

private theorem mem_ker_cm {x : MulAut W} {w : W} : w ∈ (cm x).ker ↔ x w = w := by
  rw [MonoidHom.mem_ker, cm_apply, mul_inv_eq_one]

private theorem x_cm {x : MulAut W} (w : W) : x (cm x w) = cm x (x w) := by
  simp only [cm_apply, map_mul, map_inv]

private theorem x5_apply {x : MulAut W} (hx : x ^ 5 = 1) (w : W) : x (x (x (x (x w)))) = w := by
  have h := congrArg (fun g : MulAut W => g w) hx
  simpa [pow_succ, MulAut.mul_apply] using h

private theorem iterate5_eq_id {x : MulAut W} (hx : x ^ 5 = 1) : (⇑x)^[5] = id := by
  funext w
  exact x5_apply hx w

private def pi5 (x : MulAut W) : W →* W where
  toFun w := w * x w * x (x w) * x (x (x w)) * x (x (x (x w)))
  map_one' := by simp
  map_mul' a b := by
    simp only [map_mul]
    ac_rfl

private theorem pi5_apply (x : MulAut W) (w : W) :
    pi5 x w = w * x w * x (x w) * x (x (x w)) * x (x (x (x w))) := rfl

private theorem pi5_x {x : MulAut W} (hx : x ^ 5 = 1) (w : W) : pi5 x (x w) = pi5 x w := by
  simp only [pi5_apply, x5_apply hx]
  ac_rfl

private theorem pi5_cm {x : MulAut W} (hx : x ^ 5 = 1) (w : W) : pi5 x (cm x w) = 1 := by
  rw [cm_apply, map_mul, map_inv, pi5_x hx, mul_inv_cancel]

private theorem pi5_of_fix {x : MulAut W} {c : W} (hc : x c = c) : pi5 x c = c ^ 5 := by
  simp only [pi5_apply, hc]
  simp [pow_succ, mul_assoc]

variable [Finite W]

private theorem card_ker_cm (h32 : Nat.card W = 32) {x : MulAut W} (hx : x ^ 5 = 1) (hx1 : x ≠ 1) :
    Nat.card (cm x).ker = 2 := by
  have h := card_modEq_fixed (⇑x) (iterate5_eq_id hx)
  have e : Nat.card {a // x a = a} = Nat.card (cm x).ker :=
    Nat.card_congr (Equiv.subtypeEquivRight fun w => mem_ker_cm.symm)
  rw [e, h32] at h
  have hd : Nat.card (cm x).ker ∣ 2 ^ 5 := by
    have := Subgroup.card_subgroup_dvd_card (cm x).ker
    rwa [h32] at this
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  rw [hk'] at h ⊢
  interval_cases k
  · exact absurd h (by decide)
  · rfl
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exfalso
    apply hx1
    have htop : (cm x).ker = ⊤ := by
      rw [← Subgroup.card_eq_iff_eq_top, hk', h32]
      norm_num
    ext w
    have : w ∈ (cm x).ker := htop ▸ Subgroup.mem_top w
    exact mem_ker_cm.mp this

private theorem card_range_cm (h32 : Nat.card W = 32) {x : MulAut W} (hx : x ^ 5 = 1) (hx1 : x ≠ 1) :
    Nat.card (cm x).range = 16 := by
  have h := Subgroup.card_ker_mul_card_range (cm x)
  rw [card_ker_cm h32 hx hx1, h32] at h
  omega

omit [Finite W] in
private theorem ker_inf_range_cm (hW2 : ∀ w : W, w ^ 2 = 1) {x : MulAut W} (hx : x ^ 5 = 1) :
    (cm x).ker ⊓ (cm x).range = ⊥ := by
  rw [eq_bot_iff]
  rintro c ⟨hc1, w, rfl⟩
  have hfix : x (cm x w) = cm x w := mem_ker_cm.mp hc1
  have h1 := pi5_cm hx w
  rw [pi5_of_fix hfix] at h1
  have h2 : cm x w ^ 5 = cm x w := by
    have h4 : cm x w ^ 4 = 1 := by
      have := hW2 (cm x w ^ 2)
      simpa [← pow_mul] using this
    rw [pow_succ, h4, one_mul]
  rw [h2] at h1
  exact Subgroup.mem_bot.mpr h1

private theorem eq_range_of_invariant (hW2 : ∀ w : W, w ^ 2 = 1) (h32 : Nat.card W = 32)
    {x : MulAut W} (hx : x ^ 5 = 1) (hx1 : x ≠ 1) {H : Subgroup W} (hH : Nat.card H = 16)
    (hinv : ∀ w ∈ H, x w ∈ H) : H = (cm x).range := by
  set Y : Subgroup W := (cm x).range with hY
  have hY16 : Nat.card Y = 16 := card_range_cm h32 hx hx1
  have hHidx : H.index = 2 := by
    have := Subgroup.card_mul_index H
    rw [hH, h32] at this
    omega
  have hYidx : Y.index = 2 := by
    have := Subgroup.card_mul_index Y
    rw [hY16, h32] at this
    omega
  set D : Subgroup W := H ⊓ Y with hD
  have hDidx : D.index ≤ 4 := by
    have := Subgroup.index_inf_le (H := H) (K := Y)
    rw [hHidx, hYidx] at this
    exact this
  have hD8 : 8 ≤ Nat.card D := by
    have h := Subgroup.card_mul_index D
    rw [h32] at h
    have hpos : 0 < D.index := Nat.pos_of_ne_zero (fun h0 => by rw [h0] at h; omega)
    by_contra hlt
    push Not at hlt
    interval_cases hi : D.index <;> omega
  have hDinv : ∀ d ∈ D, x d ∈ D := fun d hd => ⟨hinv d hd.1, by
    obtain ⟨w, hw⟩ := hd.2
    exact ⟨x w, by rw [← hw, x_cm]⟩⟩
  let xD : D → D := fun d => ⟨x d, hDinv d d.2⟩
  have hxD : xD^[5] = id := by
    funext d
    apply Subtype.ext
    have : ∀ n : ℕ, ((xD^[n] d : D) : W) = (⇑x)^[n] (d : W) := by
      intro n
      induction n generalizing d with
      | zero => rfl
      | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
    rw [this, iterate5_eq_id hx]
    rfl
  have h := card_modEq_fixed xD hxD
  have hfix : Nat.card {d : D // xD d = d} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => ?_⟩, ⟨⟨1, Subtype.ext (by simp [xD])⟩⟩⟩
    have key : ∀ c : {d : D // xD d = d}, c.1 = 1 := by
      intro c
      have hc : x (c.1 : W) = c.1 := congrArg Subtype.val c.2
      have hmem : (c.1 : W) ∈ (cm x).ker ⊓ (cm x).range :=
        ⟨mem_ker_cm.mpr hc, c.1.2.2⟩
      rw [ker_inf_range_cm hW2 hx] at hmem
      exact Subtype.ext (Subgroup.mem_bot.mp hmem)
    exact Subtype.ext ((key a).trans (key b).symm)
  rw [hfix] at h
  have hDdvd : Nat.card D ∣ 16 := by
    have := Subgroup.card_dvd_of_le (inf_le_right : D ≤ Y)
    rwa [hY16] at this
  have hD16 : Nat.card D = 16 := by
    have h16 : Nat.card D ∣ 2 ^ 4 := by simpa using hDdvd
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h16
    rw [hk'] at h hD8 ⊢
    interval_cases k <;> first | rfl | (exfalso; revert h hD8; decide)
  have hDY : D = Y := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hY16, hD16])
  have hDH : D = H := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hH, hD16])
  exact hDH.symm.trans hDY

end Element

section Hyperplanes

variable {W : Type*} [CommGroup W]

open scoped Classical in
private noncomputable def chiOf (H : Subgroup W) : W →* ℂˣ :=
  if h : H.index = 2 then
    { toFun := fun w => if w ∈ H then 1 else -1
      map_one' := by simp
      map_mul' := fun a b => by
        have key := Subgroup.mul_mem_iff_of_index_two h (a := a) (b := b)
        by_cases ha : a ∈ H <;> by_cases hb : b ∈ H <;> simp [ha, hb, key] }
  else 1

private theorem neg_one_ne_one : (-1 : ℂˣ) ≠ 1 := by
  intro h
  have := congrArg (fun u : ℂˣ => (u : ℂ)) h
  norm_num at this

open scoped Classical in
private theorem chiOf_apply {H : Subgroup W} (h : H.index = 2) (w : W) :
    chiOf H w = if w ∈ H then 1 else -1 := by
  simp [chiOf, h]

private theorem chiOf_injOn : Set.InjOn (chiOf (W := W)) {H : Subgroup W | H.index = 2} := by
  intro H hH K hK hHK
  ext w
  have h1 := chiOf_apply hH w
  have h2 := chiOf_apply hK w
  rw [hHK] at h1
  rw [h1] at h2
  by_cases hwH : w ∈ H <;> by_cases hwK : w ∈ K <;> simp_all [neg_one_ne_one.symm]

private theorem chiOf_ne_one {H : Subgroup W} (h : H.index = 2) : chiOf H ≠ 1 := by
  intro h1
  have hne : H ≠ ⊤ := by
    intro htop
    rw [htop, Subgroup.index_top] at h
    omega
  obtain ⟨w, hw⟩ : ∃ w, w ∉ H := by
    by_contra hcon
    push Not at hcon
    exact hne (eq_top_iff.mpr fun w _ => hcon w)
  have := chiOf_apply h w
  rw [h1] at this
  simp [hw] at this

variable [Finite W]

private theorem ncard_index_two_le (hW2 : ∀ w : W, w ^ 2 = 1) (h32 : Nat.card W = 32) :
    {H : Subgroup W | H.index = 2}.ncard ≤ 31 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp (by rw [h32]; norm_num)
  have hexp : Monoid.exponent W = 2 :=
    (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr fun g hg => orderOf_eq_prime (hW2 g) hg
  have : HasEnoughRootsOfUnity ℂ (Monoid.exponent W) := by rw [hexp]; infer_instance
  have hcard : Nat.card (W →* ℂˣ) = 32 := by
    rw [CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity W ℂ, h32]
  have h1 : ({χ : W →* ℂˣ | χ ≠ 1}).ncard = 31 := by
    have : ({χ : W →* ℂˣ | χ ≠ 1}) = Set.univ \ {1} := by ext; simp
    rw [this, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ, hcard]
  rw [← h1]
  exact Set.ncard_le_ncard_of_injOn (chiOf (W := W)) (fun H hH => chiOf_ne_one hH) chiOf_injOn
    (Set.toFinite _)

end Hyperplanes

section Orbit

variable {W : Type*} [CommGroup W]

private theorem mem_smul_iff (g : MulAut W) (H : Subgroup W) (w : W) : w ∈ g • H ↔ g⁻¹ w ∈ H := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

private theorem card_smul (g : MulAut W) (H : Subgroup W) : Nat.card ↥(g • H) = Nat.card ↥H := by
  rw [Subgroup.pointwise_smul_def]
  exact Subgroup.card_map_of_injective (fun a b (h : g • a = g • b) => g.injective h)

private theorem false_of_invariant (h32 : Nat.card W = 32) {L : Subgroup (MulAut W)}
    (hcomm : commV L = ⊤) {Y : Subgroup W} (hY16 : Nat.card Y = 16)
    (hinv : ∀ g ∈ L, g • Y = Y) : False := by
  have hYidx : Y.index = 2 := by
    have := Subgroup.card_mul_index Y
    rw [hY16, h32] at this
    omega
  have hle : commV L ≤ Y := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨g, hg, v, rfl⟩
    have h1 : g v ∈ Y ↔ v ∈ Y := by
      have := mem_smul_iff g Y (g v)
      rw [hinv g hg] at this
      simpa using this
    rw [SetLike.mem_coe, Subgroup.mul_mem_iff_of_index_two hYidx, Subgroup.inv_mem_iff]
    exact h1
  rw [hcomm] at hle
  have htop : Y = ⊤ := top_le_iff.mp hle
  rw [htop, Subgroup.card_top, h32] at hY16
  omega

variable [Finite W]

private theorem smul_range_cm {x : MulAut W} : x • (cm x).range = (cm x).range := by
  apply Subgroup.eq_of_le_of_card_ge
  · intro w hw
    obtain ⟨s, ⟨v, rfl⟩, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hw
    exact ⟨x v, (x_cm v).symm⟩
  · rw [card_smul]

private theorem ncard_orbit_cm (hW2 : ∀ w : W, w ^ 2 = 1) (h32 : Nat.card W = 32)
    {L : Subgroup (MulAut W)} (hcomm : commV L = ⊤) (hL : Nat.card L = 360)
    {x : MulAut W} (hxL : x ∈ L) (hx : x ^ 5 = 1) (hx1 : x ≠ 1) :
    (MulAction.orbit L (cm x).range).ncard = 6 := by
  set Y : Subgroup W := (cm x).range with hY
  have hY16 : Nat.card Y = 16 := card_range_cm h32 hx hx1
  let xL : L := ⟨x, hxL⟩
  have hxL5 : xL ^ 5 = 1 := Subtype.ext (by simpa using hx)
  have hcard16 : ∀ O ∈ MulAction.orbit L Y, Nat.card O = 16 := by
    rintro O ⟨g, rfl⟩
    rw [← hY16]
    exact card_smul (g : MulAut W) Y
  let f : MulAction.orbit L Y → MulAction.orbit L Y := fun O => xL • O
  have hfiter : ∀ n : ℕ, ∀ O, f^[n] O = (xL ^ n) • O := by
    intro n
    induction n with
    | zero => intro O; simp
    | succ n ih =>
      intro O
      rw [Function.iterate_succ_apply, ih, ← mul_smul, ← pow_succ]
  have hf5 : f^[5] = id := by
    funext O
    rw [hfiter, hxL5, one_smul]
    rfl
  have hmod := card_modEq_fixed f hf5
  have hfix : Nat.card {O : MulAction.orbit L Y // f O = O} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    have hbase : f ⟨Y, MulAction.mem_orbit_self Y⟩ = ⟨Y, MulAction.mem_orbit_self Y⟩ :=
      Subtype.ext smul_range_cm
    refine ⟨⟨fun a b => ?_⟩, ⟨⟨_, hbase⟩⟩⟩
    have key : ∀ c : {O : MulAction.orbit L Y // f O = O}, (c.1 : Subgroup W) = Y := by
      intro c
      have hc : (x : MulAut W) • (c.1 : Subgroup W) = (c.1 : Subgroup W) := congrArg Subtype.val c.2
      refine eq_range_of_invariant hW2 h32 hx hx1 (hcard16 _ c.1.2) (fun w hw => ?_)
      have h1 : x • w ∈ x • (c.1 : Subgroup W) := Subgroup.smul_mem_pointwise_smul w x _ hw
      rw [hc] at h1
      exact h1
    exact Subtype.ext (Subtype.ext ((key a).trans (key b).symm))
  have hn : (MulAction.orbit L Y).ncard % 5 = 1 := by
    have h := hmod
    rw [hfix, Nat.card_coe_set_eq] at h
    exact h
  have hdvd : (MulAction.orbit L Y).ncard ∣ 360 := by
    have h1 := MulAction.index_stabilizer L Y
    have h2 := Subgroup.index_dvd_card (MulAction.stabilizer L Y)
    rw [h1, hL] at h2
    exact h2
  have hsub : MulAction.orbit L Y ⊆ {H : Subgroup W | H.index = 2} := by
    intro O hO
    have := Subgroup.card_mul_index O
    rw [hcard16 O hO, h32] at this
    show O.index = 2
    omega
  have hle : (MulAction.orbit L Y).ncard ≤ 31 :=
    (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (ncard_index_two_le hW2 h32)
  have hcases : ∀ n : ℕ, n ≤ 31 → n ∣ 360 → n % 5 = 1 → n = 1 ∨ n = 6 := by decide
  rcases hcases _ hle hdvd hn with h1 | h6
  · exfalso
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp h1
    refine false_of_invariant h32 hcomm hY16 (fun g hg => ?_)
    have h1 : ((⟨g, hg⟩ : L) • Y : Subgroup W) ∈ MulAction.orbit L Y := MulAction.mem_orbit Y (⟨g, hg⟩ : L)
    have h2 : Y ∈ MulAction.orbit L Y := MulAction.mem_orbit_self Y
    rw [ha, Set.mem_singleton_iff] at h1 h2
    exact h1.trans h2.symm
  · exact h6

end Orbit

section Rep

variable {W : Type*} [CommGroup W] [Finite W]

private theorem card_alt6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup]
  simp [Nat.factorial]

private theorem exists_rep (hW2 : ∀ w : W, w ^ 2 = 1) (h32 : Nat.card W = 32)
    (L : Subgroup (MulAut W)) (hL : Nonempty (↥L ≃* ↥(alternatingGroup (Fin 6))))
    (hcomm : commV L = ⊤) :
    ∃ (ρ : ↥L →* Equiv.Perm (Fin 6)) (H : Fin 6 → Subgroup W),
      (∀ i, Nat.card (H i) = 16) ∧ Function.Injective H ∧
      (∀ (g : ↥L) (i : Fin 6), H (ρ g i) = (g : MulAut W) • H i) ∧
      (∀ g : ↥L, ρ g ∈ alternatingGroup (Fin 6)) ∧
      (∀ σ ∈ alternatingGroup (Fin 6), ∃ g : ↥L, ρ g = σ) := by
  obtain ⟨θ⟩ := hL
  have hL360 : Nat.card L = 360 := by rw [Nat.card_congr θ.toEquiv, card_alt6]
  have hsimple : IsSimpleGroup ↥L := by
    have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    exact θ.isSimpleGroup
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x₀, hx₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 5 (by rw [hL360]; norm_num)
  set x : MulAut W := (x₀ : MulAut W) with hxdef
  have hxord : orderOf x = 5 := by rw [hxdef, Subgroup.orderOf_coe, hx₀]
  have hx : x ^ 5 = 1 := by rw [← hxord]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at hxord; omega
  have hcard6 := ncard_orbit_cm hW2 h32 hcomm hL360 x₀.2 hx hx1
  set Y : Subgroup W := (cm x).range with hY
  have hY16 : Nat.card Y = 16 := card_range_cm h32 hx hx1
  have hcard16 : ∀ O ∈ MulAction.orbit L Y, Nat.card O = 16 := by
    rintro O ⟨g, rfl⟩
    rw [← hY16]
    exact card_smul (g : MulAut W) Y
  have hNat : Nat.card (MulAction.orbit L Y) = 6 := by rw [Nat.card_coe_set_eq, hcard6]
  let e : MulAction.orbit L Y ≃ Fin 6 := (Finite.equivFin _).trans (finCongr hNat)
  let ρ : ↥L →* Equiv.Perm (Fin 6) :=
    (Equiv.permCongrHom e).toMonoidHom.comp (MulAction.toPermHom L (MulAction.orbit L Y))
  have hρ : ∀ (g : ↥L) (i : Fin 6), e.symm (ρ g i) = g • e.symm i := by
    intro g i
    show e.symm (e ((MulAction.toPerm g) (e.symm i))) = _
    rw [e.symm_apply_apply, MulAction.toPerm_apply]
  let H : Fin 6 → Subgroup W := fun i => ((e.symm i : MulAction.orbit L Y) : Subgroup W)
  have hH : ∀ (g : ↥L) (i : Fin 6), H (ρ g i) = (g : MulAut W) • H i := by
    intro g i
    show ((e.symm (ρ g i) : MulAction.orbit L Y) : Subgroup W) = _
    rw [hρ]
    rfl
  have hfaith : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker with h | h
    · exact h
    · exfalso
      have hall : ∀ g : ↥L, ρ g = 1 := fun g => by
        have : g ∈ ρ.ker := h ▸ Subgroup.mem_top g
        exact this
      refine false_of_invariant h32 hcomm hY16 (fun g hg => ?_)
      have h1 : ((e ⟨Y, MulAction.mem_orbit_self Y⟩ : Fin 6)) = e ⟨Y, MulAction.mem_orbit_self Y⟩ := rfl
      have h2 := hH ⟨g, hg⟩ (e ⟨Y, MulAction.mem_orbit_self Y⟩)
      rw [hall, Equiv.Perm.coe_one, id_eq] at h2
      have h3 : H (e ⟨Y, MulAction.mem_orbit_self Y⟩) = Y := by
        show ((e.symm (e ⟨Y, MulAction.mem_orbit_self Y⟩) : MulAction.orbit L Y) : Subgroup W) = Y
        rw [e.symm_apply_apply]
      rw [h3] at h2
      exact h2.symm
  have halt : ∀ g : ↥L, ρ g ∈ alternatingGroup (Fin 6) := by
    have hs : (Equiv.Perm.sign.comp ρ).ker = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Equiv.Perm.sign.comp ρ).ker with h | h
      · exfalso
        have hinj : Function.Injective (Equiv.Perm.sign.comp ρ) := (MonoidHom.ker_eq_bot_iff _).mp h
        have := Nat.card_le_card_of_injective _ hinj
        rw [hL360, Nat.card_eq_fintype_card (α := ℤˣ), Fintype.card_units_int] at this
        omega
      · exact h
    intro g
    have : g ∈ (Equiv.Perm.sign.comp ρ).ker := hs ▸ Subgroup.mem_top g
    exact Equiv.Perm.mem_alternatingGroup.mpr this
  have hsurj : ∀ σ ∈ alternatingGroup (Fin 6), ∃ g : ↥L, ρ g = σ := by
    have hle : ρ.range ≤ alternatingGroup (Fin 6) := by
      rintro _ ⟨g, rfl⟩
      exact halt g
    have hcard : Nat.card ρ.range = 360 := by
      rw [← hL360]
      exact (Nat.card_congr (MonoidHom.ofInjective hfaith).toEquiv).symm
    have heq : ρ.range = alternatingGroup (Fin 6) :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [card_alt6, hcard])
    intro σ hσ
    have : σ ∈ ρ.range := heq ▸ hσ
    exact this
  refine ⟨ρ, H, fun i => hcard16 _ (e.symm i).2, ?_, hH, halt, hsurj⟩
  intro i j hij
  have : (e.symm i : MulAction.orbit L Y) = e.symm j := Subtype.ext hij
  exact e.symm.injective this

end Rep

section Equivalence

variable {W : Type*} [CommGroup W] [Finite W]

private def sumHom : G6.PermMod 6 →* Multiplicative (ZMod 2) where
  toFun x := Multiplicative.ofAdd (∑ i, Multiplicative.toAdd x i)
  map_one' := by simp
  map_mul' x y := by simp [Finset.sum_add_distrib]

theorem exists_core_equiv (hW2 : ∀ w : W, w ^ 2 = 1) (h32 : Nat.card W = 32)
    (L : Subgroup (MulAut W)) (hL : Nonempty (↥L ≃* ↥(alternatingGroup (Fin 6))))
    (hcomm : commV L = ⊤) :
    ∃ Φ : W ≃* ↥(G6.coreMod 6), ∀ g : MulAut W, g ∈ L ↔
      ∃ σ ∈ alternatingGroup (Fin 6), ∀ w, Φ (g w) = G6.coreAct 6 σ (Φ w) := by
  classical
  obtain ⟨ρ, H, hH16, hHinj, hHρ, halt, hsurj⟩ := exists_rep hW2 h32 L hL hcomm
  have hidx : ∀ i, (H i).index = 2 := fun i => by
    have := Subgroup.card_mul_index (H i)
    rw [hH16 i, h32] at this
    omega
  let Φ : W →* G6.PermMod 6 :=
    { toFun := fun w => Multiplicative.ofAdd (fun i => if w ∈ H i then (0 : ZMod 2) else 1)
      map_one' := by
        apply Multiplicative.toAdd.injective
        funext i
        simp
      map_mul' := fun a b => by
        apply Multiplicative.toAdd.injective
        funext i
        have key := Subgroup.mul_mem_iff_of_index_two (hidx i) (a := a) (b := b)
        have h11 : (1 : ZMod 2) + 1 = 0 := by decide
        by_cases ha : a ∈ H i <;> by_cases hb : b ∈ H i <;> simp [ha, hb, key, h11] }
  have hΦ : ∀ (w : W) (i : Fin 6),
      Multiplicative.toAdd (Φ w) i = if w ∈ H i then (0 : ZMod 2) else 1 := fun w i => rfl
  have hmem : ∀ (g : ↥L) (w : W) (i : Fin 6), w ∈ H ((ρ g)⁻¹ i) ↔ (g : MulAut W) w ∈ H i := by
    intro g w i
    have h1 : (ρ g)⁻¹ i = ρ g⁻¹ i := by rw [map_inv]
    rw [h1, hHρ, mem_smul_iff]
    simp
  have hequiv : ∀ (g : ↥L) (w : W), Φ ((g : MulAut W) w) = G6.permAct 6 (ρ g) (Φ w) := by
    intro g w
    apply Multiplicative.toAdd.injective
    funext i
    rw [G6.permAct_apply, hΦ, hΦ]
    simp only [hmem g w i]
  have hcore : ∀ w : W, Φ w ∈ G6.coreMod 6 := by
    let ψ : W →* Multiplicative (ZMod 2) := sumHom.comp Φ
    have hψ : ∀ (g : ↥L) (w : W), ψ ((g : MulAut W) w) = ψ w := by
      intro g w
      show Multiplicative.ofAdd (∑ i, Multiplicative.toAdd (Φ ((g : MulAut W) w)) i) =
        Multiplicative.ofAdd (∑ i, Multiplicative.toAdd (Φ w) i)
      rw [hequiv]
      congr 1
      simp only [G6.permAct_apply]
      exact Equiv.sum_comp (ρ g)⁻¹ (fun i => Multiplicative.toAdd (Φ w) i)
    have hle : commV L ≤ ψ.ker := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨g, hg, v, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv]
      have := hψ ⟨g, hg⟩ v
      rw [this]
      exact mul_inv_cancel (ψ v)
    rw [hcomm] at hle
    intro w
    have hw : w ∈ ψ.ker := hle (Subgroup.mem_top w)
    rw [MonoidHom.mem_ker] at hw
    exact G6.mem_coreMod.mpr (ofAdd_eq_one.mp hw)
  let Φ' : W →* ↥(G6.coreMod 6) := Φ.codRestrict _ hcore
  have hsurj' : Function.Surjective Φ' := by
    have hinv : ∀ σ ∈ alternatingGroup (Fin 6), ∀ x ∈ Φ.range, G6.permAct 6 σ x ∈ Φ.range := by
      rintro σ hσ _ ⟨w, rfl⟩
      obtain ⟨g, hg⟩ := hsurj σ hσ
      exact ⟨(g : MulAut W) w, by rw [hequiv g w, hg]⟩
    have hne : H 0 ≠ H 1 := fun h => by
      have := hHinj h
      exact absurd this (by decide)
    obtain ⟨w, hw⟩ : ∃ w, ¬ (w ∈ H 0 ↔ w ∈ H 1) := by
      by_contra hcon
      push Not at hcon
      exact hne (SetLike.ext hcon)
    have hw1 : Φ w ≠ 1 := fun h => by
      have h0 := congrArg (fun x : G6.PermMod 6 => Multiplicative.toAdd x 0) h
      have h1 := congrArg (fun x : G6.PermMod 6 => Multiplicative.toAdd x 1) h
      simp only [hΦ, toAdd_one, Pi.zero_apply] at h0 h1
      apply hw
      constructor
      · intro _; by_contra hn; simp [hn] at h1
      · intro _; by_contra hn; simp [hn] at h0
    have hwo : Φ w ≠ G6.allOnes 6 := fun h => by
      have h0 := congrArg (fun x : G6.PermMod 6 => Multiplicative.toAdd x 0) h
      have h1 := congrArg (fun x : G6.PermMod 6 => Multiplicative.toAdd x 1) h
      simp only [hΦ, G6.allOnes, toAdd_ofAdd] at h0 h1
      apply hw
      constructor
      · intro hh; simp [hh] at h0
      · intro hh; simp [hh] at h1
    have hle := core_le_of_invariant Φ.range hinv ⟨w, rfl⟩ (hcore w) hw1 hwo
    intro c
    obtain ⟨v, hv⟩ := hle c.2
    exact ⟨v, Subtype.ext hv⟩
  have hbij : Function.Bijective Φ' :=
    Function.Surjective.bijective_of_nat_card_le hsurj' (by rw [h32, card_core])
  refine ⟨MulEquiv.ofBijective Φ' hbij, fun g => ⟨fun hg => ⟨ρ ⟨g, hg⟩, halt _, fun w => ?_⟩,
    fun ⟨σ, hσ, hσg⟩ => ?_⟩⟩
  · exact Subtype.ext (hequiv ⟨g, hg⟩ w)
  · obtain ⟨g', hg'⟩ := hsurj σ hσ
    have hgg : g = (g' : MulAut W) := by
      ext w
      apply hbij.1
      have h1 : Φ' (g w) = G6.coreAct 6 σ (Φ' w) := hσg w
      have h2 : Φ' ((g' : MulAut W) w) = G6.coreAct 6 σ (Φ' w) := by
        apply Subtype.ext
        rw [← hg']
        exact hequiv g' w
      exact h1.trans h2.symm
    rw [hgg]
    exact g'.2

end Equivalence

section Normalizer

variable {W : Type*} [CommGroup W]

private theorem exists_perm_of_normalizes (L : Subgroup (MulAut W)) (Φ : W ≃* ↥(G6.coreMod 6))
    (hΦ : ∀ g : MulAut W, g ∈ L ↔
      ∃ σ ∈ alternatingGroup (Fin 6), ∀ w, Φ (g w) = G6.coreAct 6 σ (Φ w))
    {p : MulAut W} (hp : p ∈ Subgroup.normalizer (L : Set (MulAut W))) :
    ∃ π : Equiv.Perm (Fin 6), ∀ w, Φ (p w) = G6.coreAct 6 π (Φ w) := by
  let ρ : MulAut ↥(G6.coreMod 6) := Φ.symm.trans (p.trans Φ)
  have hρ : ∀ w, ρ (Φ w) = Φ (p w) := fun w => by simp [ρ]
  let lift : Equiv.Perm (Fin 6) → MulAut W := fun σ => Φ.trans ((G6.coreAct 6 σ).trans Φ.symm)
  have hlift : ∀ σ w, Φ (lift σ w) = G6.coreAct 6 σ (Φ w) := fun σ w => by simp [lift]
  have hliftL : ∀ σ ∈ alternatingGroup (Fin 6), lift σ ∈ L := fun σ hσ =>
    (hΦ _).mpr ⟨σ, hσ, hlift σ⟩
  have hnorm : ∀ q ∈ Subgroup.normalizer (L : Set (MulAut W)), ∀ g ∈ L, q * g * q⁻¹ ∈ L :=
    fun q hq g hg => (Subgroup.mem_normalizer_iff.mp hq g).mp hg
  have h1 : ∀ σ ∈ alternatingGroup (Fin 6), ∃ τ ∈ alternatingGroup (Fin 6),
      ∀ x, ρ (G6.coreAct 6 σ x) = G6.coreAct 6 τ (ρ x) := by
    intro σ hσ
    obtain ⟨τ, hτ, hτg⟩ := (hΦ _).mp (hnorm p hp _ (hliftL σ hσ))
    refine ⟨τ, hτ, fun x => ?_⟩
    obtain ⟨w, rfl⟩ := Φ.surjective x
    rw [← hlift σ w, hρ, hρ]
    have := hτg (p w)
    simpa [MulAut.mul_apply] using this
  have h2 : ∀ τ ∈ alternatingGroup (Fin 6), ∃ σ ∈ alternatingGroup (Fin 6),
      ∀ x, ρ (G6.coreAct 6 σ x) = G6.coreAct 6 τ (ρ x) := by
    intro τ hτ
    obtain ⟨σ, hσ, hσg⟩ := (hΦ _).mp (hnorm p⁻¹ (inv_mem hp) _ (hliftL τ hτ))
    refine ⟨σ, hσ, fun x => ?_⟩
    obtain ⟨w, rfl⟩ := Φ.surjective x
    have hσw : Φ (p⁻¹ (lift τ (p w))) = G6.coreAct 6 σ (Φ w) := by
      simpa [MulAut.mul_apply] using hσg w
    rw [← hσw, hρ, hρ]
    rw [show p (p⁻¹ (lift τ (p w))) = lift τ (p w) by simp]
    exact hlift τ (p w)
  obtain ⟨π, hπ⟩ := CFSG.Quasithin.H13.A6.exists_perm_of_normalizes_core ρ h1 h2
  exact ⟨π, fun w => by rw [← hρ, hπ]⟩

end Normalizer

end CFSG.Quasithin.ModA6

namespace CFSG.Quasithin

open CFSG.Quasithin.ModA6 CFSG.Quasithin.H13.A6


theorem asI231A6_holds : AsI231A6 := by
  intro W _ _ hW2 hcard L P hL hcomm hP hPN
  have h32 : Nat.card W = 32 := by rw [hcard]; norm_num
  obtain ⟨Φ, hΦ⟩ := exists_core_equiv hW2 h32 L hL hcomm
  let D : SubMulAction ↥P W :=
    { carrier := {w | wt ((Φ w : G6.coreMod 6) : G6.PermMod 6) = 2}
      smul_mem' := fun p w hw => by
        obtain ⟨π, hπ⟩ := exists_perm_of_normalizes L Φ hΦ (hPN p.2)
        show wt ((Φ ((p : MulAut W) w) : G6.coreMod 6) : G6.PermMod 6) = 2
        rw [hπ w, G6.coreAct_coe, wt_permAct]
        exact hw }
  have hDcard : Nat.card D = 15 := by
    have hbij : Function.Bijective
        (fun w : D => (⟨((Φ w : G6.coreMod 6) : G6.PermMod 6), w.2⟩ : {y : G6.PermMod 6 // wt y = 2})) := by
      constructor
      · intro a b h
        have h' : ((Φ a : G6.coreMod 6) : G6.PermMod 6) = ((Φ b : G6.coreMod 6) : G6.PermMod 6) := by
          have := congrArg (fun y : {y : G6.PermMod 6 // wt y = 2} => y.1) h
          exact this
        exact Subtype.ext (Φ.injective (Subtype.ext h'))
      · rintro ⟨y, hy⟩
        have hyc : y ∈ G6.coreMod 6 := G6.mem_coreMod.2 (sum_eq_zero_of_wt_two y hy)
        refine ⟨⟨Φ.symm ⟨y, hyc⟩, ?_⟩, Subtype.ext ?_⟩
        · show wt ((Φ (Φ.symm ⟨y, hyc⟩) : G6.coreMod 6) : G6.PermMod 6) = 2
          rw [MulEquiv.apply_symm_apply]
          exact hy
        · show ((Φ (Φ.symm ⟨y, hyc⟩) : G6.coreMod 6) : G6.PermMod 6) = y
          rw [MulEquiv.apply_symm_apply]
    rw [Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact card_wt_two
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := hP.card_modEq_card_fixedPoints D
  rw [hDcard] at hmod
  have hpos : 0 < Nat.card (MulAction.fixedPoints ↥P D) := by
    apply Nat.pos_of_ne_zero
    intro h0
    rw [h0] at hmod
    exact absurd hmod (by decide)
  obtain ⟨⟨d, hd⟩, -⟩ := Nat.card_pos_iff.mp hpos
  have hdP : d.1 ∈ fixV P := fun p hp => congrArg Subtype.val (hd ⟨p, hp⟩)
  obtain ⟨σ, hσ, hσd⟩ := exists_alt_ne_of_wt_two ((Φ d.1 : G6.coreMod 6) : G6.PermMod 6) d.2
  let g : MulAut W := Φ.trans ((G6.coreAct 6 σ).trans Φ.symm)
  have hgΦ : ∀ w, Φ (g w) = G6.coreAct 6 σ (Φ w) := fun w => by simp [g]
  have hgL : g ∈ L := (hΦ g).mpr ⟨σ, hσ, hgΦ⟩
  intro hle
  have hfix := hle hdP g hgL
  apply hσd
  have := congrArg (fun w => ((Φ w : G6.coreMod 6) : G6.PermMod 6)) hfix
  simpa [hgΦ, G6.coreAct_coe] using this




end CFSG.Quasithin

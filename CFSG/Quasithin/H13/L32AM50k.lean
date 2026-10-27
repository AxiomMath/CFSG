module

public import CFSG.Quasithin.H13.L32AC40d
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.Quasithin.H13.L32A.C.Alt7Mod

open Equiv Equiv.Perm CFSG.Quasithin.B3
open CFSG.Quasithin.H13.L32A.C.A5Mod (apply_eq_commHom_mul pow_twelve_eq_one
  card_map_mul_relIndex_le)

@[expose] def c3List : List (Perm (Fin 7)) :=
  [swap 4 5 * swap 5 6, swap 2 3 * swap 3 4, swap 1 2 * swap 2 5, swap 2 4 * swap 4 5,
    swap 3 4 * swap 4 6, swap 1 2 * swap 2 3, swap 1 3 * swap 3 6]

theorem c3_sign : ∀ g ∈ c3List, sign g = 1 := by
  have h : c3List.all (fun g => decide (sign g = 1)) = true := by
    decide +kernel
  intro g hg
  exact of_decide_eq_true (List.all_eq_true.mp h g hg)

theorem inv_five_card : (Finset.univ.filter fun e : Perm (Fin 7) =>
    e * e = 1 ∧ sign e = 1 ∧ e ≠ 1 ∧ c3List.any (fun g =>
      decide ((e * (g * e * g⁻¹)) ^ 5 = 1 ∧ e * (g * e * g⁻¹) ≠ 1)) = false).card = 0 := by
  decide +kernel

theorem alt7_exists_conj : ∀ u : alternatingGroup (Fin 7), u * u = 1 → u ≠ 1 →
    ∃ g : alternatingGroup (Fin 7), (u * (g * u * g⁻¹)) ^ 5 = 1 ∧ u * (g * u * g⁻¹) ≠ 1 := by
  intro u hu2 hu1
  have h0 := inv_five_card
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
  have h1 := h0 (Finset.mem_univ (u : Perm (Fin 7)))
  have hu2' : (u : Perm (Fin 7)) * u = 1 := congrArg Subtype.val hu2
  have hu1' : (u : Perm (Fin 7)) ≠ 1 := fun h => hu1 (Subtype.ext h)
  have hany : c3List.any (fun g => decide (((u : Perm (Fin 7)) * (g * u * g⁻¹)) ^ 5 = 1 ∧
      (u : Perm (Fin 7)) * (g * u * g⁻¹) ≠ 1)) = true := by
    by_contra h
    exact h1 ⟨hu2', mem_alternatingGroup.mp u.2, hu1', by simpa using h⟩
  obtain ⟨g, hg, hg5⟩ := List.any_eq_true.mp hany
  obtain ⟨h5, hne⟩ := of_decide_eq_true hg5
  refine ⟨⟨g, mem_alternatingGroup.mpr (c3_sign g hg)⟩, Subtype.ext ?_, fun h => hne ?_⟩
  · simpa using h5
  · simpa using congrArg Subtype.val h

variable {X : Type*} [CommGroup X] [Finite X]

theorem four_le_card_range (hX : ∀ x : X, x * x = 1) {Γ : Subgroup (MulAut X)}
    (e : ↥Γ ≃* alternatingGroup (Fin 7)) {u : MulAut X} (hu : u ∈ Γ) (hu2 : u * u = 1)
    (hu1 : u ≠ 1) : 4 ≤ Nat.card (A5Mod.commHom u).range := by
  have hp : IsPGroup 2 X := fun x => ⟨1, by rw [pow_one, pow_two]; exact hX x⟩
  obtain ⟨n, hn⟩ := (hp.to_subgroup (A5Mod.commHom u).range).exists_card_eq
  have hne1 : n ≠ 0 := by
    rintro rfl
    apply hu1
    have hbot : (A5Mod.commHom u).range = ⊥ := Subgroup.card_eq_one.mp (by simpa using hn)
    ext x
    have h1 : A5Mod.commHom u x = 1 := by
      have : A5Mod.commHom u x ∈ (A5Mod.commHom u).range := ⟨x, rfl⟩
      rwa [hbot, Subgroup.mem_bot] at this
    rw [MulAut.one_apply, apply_eq_commHom_mul, h1, one_mul]
  have hne2 : n ≠ 1 := by
    rintro rfl
    set γu : ↥Γ := ⟨u, hu⟩ with hγu
    have hγu2 : γu * γu = 1 := Subtype.ext hu2
    have hγu1 : γu ≠ 1 := fun h => hu1 (congrArg Subtype.val h)
    have hu'2 : e γu * e γu = 1 := by rw [← map_mul, hγu2, map_one]
    have hu'1 : e γu ≠ 1 := fun h => hγu1 (e.injective (h.trans (map_one e).symm))
    obtain ⟨g', hg5, hg1⟩ := alt7_exists_conj (e γu) hu'2 hu'1
    set γg : ↥Γ := e.symm g' with hγg
    set γv : ↥Γ := γg * γu * γg⁻¹ with hγv
    have hv2 : Nat.card (A5Mod.commHom (γv : MulAut X)).range ≤ 2 := by
      have hr : (A5Mod.commHom (γv : MulAut X)).range =
          (A5Mod.commHom u).range.map (γg : MulAut X).toMonoidHom := by
        ext y
        constructor
        · rintro ⟨x, rfl⟩
          refine ⟨A5Mod.commHom u ((γg : MulAut X)⁻¹ x), ⟨_, rfl⟩, ?_⟩
          simp only [hγv, Subgroup.coe_mul, Subgroup.coe_inv, A5Mod.commHom_apply, MulAut.mul_apply,
            MulEquiv.coe_toMonoidHom, map_mul, map_inv, hγu]
          rw [MulAut.inv_apply, MulEquiv.apply_symm_apply]
        · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
          refine ⟨(γg : MulAut X) x, ?_⟩
          simp only [hγv, Subgroup.coe_mul, Subgroup.coe_inv, A5Mod.commHom_apply, MulAut.mul_apply,
            MulEquiv.coe_toMonoidHom, map_mul, map_inv, hγu]
          rw [MulAut.inv_apply, MulEquiv.symm_apply_apply]
      rw [hr, Subgroup.card_map_of_injective (γg : MulAut X).injective, hn, pow_one]
    have h12 := pow_twelve_eq_one hX (u := u) (v := (γv : MulAut X)) (by rw [hn, pow_one]) hv2
    have h12' : (γu * γv) ^ 12 = 1 := Subtype.ext (by simpa [hγu] using h12)
    have hev : e γv = g' * e γu * g'⁻¹ := by
      rw [hγv, map_mul, map_mul, map_inv, hγg, MulEquiv.apply_symm_apply]
    have hw12 : (e γu * (g' * e γu * g'⁻¹)) ^ 12 = 1 := by
      rw [← hev, ← map_mul, ← map_pow, h12', map_one]
    set w := e γu * (g' * e γu * g'⁻¹) with hw
    have h1 : orderOf w ∣ 1 := by
      have := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hg5) (orderOf_dvd_of_pow_eq_one hw12)
      simpa using this
    exact hg1 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1))
  rw [hn]
  have : 2 ≤ n := by omega
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) this

theorem four_le_relIndex_map (hW : ∀ w : X, w * w = 1) {L : Subgroup (MulAut X)}
    (e : ↥L ≃* alternatingGroup (Fin 7)) {Y Z : Subgroup X}
    (hY : ∀ l ∈ L, ∀ y ∈ Y, l y ∈ Y) (hZ : ∀ l ∈ L, ∀ z ∈ Z, l z ∈ Z)
    (hnt : ∃ l ∈ L, ∃ z ∈ Z, l z * z⁻¹ ∉ Y) {u : MulAut X} (hu : u ∈ L) (hu2 : u * u = 1)
    (hu1 : u ≠ 1) : 4 ≤ Y.relIndex (Z.map (A5Mod.commHom u)) := by
  set ρ : ↥L →* MulAut X := L.subtype with hρ
  have hZ' : IsInv ρ Z := fun g z hz => hZ g g.2 z hz
  have hY' : IsInv ρ Y := fun g y hy => hY g g.2 y hy
  set σ := secAct ρ hZ' hY' with hσ
  have hσmk : ∀ (g : ↥L) (z : ↥Z), σ g (QuotientGroup.mk z) =
      QuotientGroup.mk (restrictEquiv ρ Z hZ' g z) := fun _ _ => rfl
  have hS2 : ∀ q : Sec Z Y, q * q = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H z =>
      rw [← QuotientGroup.mk_mul, show z * z = 1 from Subtype.ext (hW z), QuotientGroup.mk_one]
  have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  have : IsSimpleGroup ↥L := e.isSimpleGroup
  have hσinj : Function.Injective σ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal σ.ker with h | h
    · exact h
    · exfalso
      obtain ⟨l, hl, z, hz, hlz⟩ := hnt
      have h1 : σ ⟨l, hl⟩ = 1 := by
        rw [← MonoidHom.mem_ker, h]
        exact Subgroup.mem_top _
      have h2 := congrArg (fun φ : MulAut (Sec Z Y) => φ (QuotientGroup.mk ⟨z, hz⟩)) h1
      simp only [hσmk, MulAut.one_apply] at h2
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h2
      apply hlz
      have e2 : l z * z⁻¹ = ((restrictEquiv ρ Z hZ' ⟨l, hl⟩ ⟨z, hz⟩)⁻¹ * ⟨z, hz⟩ : ↥Z)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, restrictEquiv_apply, mul_inv_rev, inv_inv]
        exact mul_comm _ _
      rw [e2]
      exact Y.inv_mem h2
  set Γ := σ.range with hΓ
  let eΓ : ↥Γ ≃* alternatingGroup (Fin 7) := (MonoidHom.ofInjective hσinj).symm.trans e
  set γu : ↥L := ⟨u, hu⟩ with hγu
  have hγ2 : σ γu * σ γu = 1 := by
    rw [← map_mul, show γu * γu = 1 from Subtype.ext hu2, map_one]
  have hγ1 : σ γu ≠ 1 := fun h => hu1 (congrArg Subtype.val (hσinj (h.trans (map_one σ).symm)))
  have h4 := four_le_card_range hS2 eΓ (MonoidHom.mem_range.mpr ⟨γu, rfl⟩) hγ2 hγ1
  set K' := Z.map (A5Mod.commHom u) with hK'
  have hK'Z : K' ≤ Z := by
    rintro _ ⟨z, hz, rfl⟩
    exact Z.mul_mem (hZ u hu z hz) (Z.inv_mem hz)
  let g : ↥K' →* Sec Z Y := (QuotientGroup.mk' (Y.subgroupOf Z)).comp (Subgroup.inclusion hK'Z)
  have hpt : ∀ z : ↥Z, A5Mod.commHom (σ γu) (QuotientGroup.mk z) =
      g ⟨A5Mod.commHom u z, z, z.2, rfl⟩ := by
    intro z
    rw [A5Mod.commHom_apply, hσmk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    rfl
  have hrange : g.range = (A5Mod.commHom (σ γu)).range := by
    ext q
    constructor
    · rintro ⟨⟨_, z, hz, rfl⟩, rfl⟩
      exact ⟨QuotientGroup.mk ⟨z, hz⟩, hpt ⟨z, hz⟩⟩
    · rintro ⟨q, rfl⟩
      induction q using QuotientGroup.induction_on with
      | H z => exact ⟨⟨A5Mod.commHom u z, z, z.2, rfl⟩, (hpt z).symm⟩
  have hker : g.ker = Y.subgroupOf K' := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show QuotientGroup.mk (Subgroup.inclusion hK'Z k) = (1 : Sec Z Y) ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  calc 4 ≤ Nat.card (A5Mod.commHom (σ γu)).range := h4
    _ = Nat.card g.range := by rw [hrange]
    _ = g.ker.index := (Subgroup.index_ker g).symm
    _ = Y.relIndex K' := by rw [hker]; rfl

theorem sixteen_le_card_range (hW : ∀ w : X, w * w = 1) {L : Subgroup (MulAut X)}
    (e : ↥L ≃* alternatingGroup (Fin 7)) {Y Z : Subgroup X} (hYZ : Y ≤ Z)
    (hY : ∀ l ∈ L, ∀ y ∈ Y, l y ∈ Y) (hZ : ∀ l ∈ L, ∀ z ∈ Z, l z ∈ Z)
    (hntY : ∃ l ∈ L, ∃ y ∈ Y, l y * y⁻¹ ≠ 1) (hntZ : ∃ l ∈ L, ∃ z ∈ Z, l z * z⁻¹ ∉ Y)
    {u : MulAut X} (hu : u ∈ L) (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    16 ≤ Nat.card (A5Mod.commHom u).range := by
  have h1 : 4 ≤ (⊥ : Subgroup X).relIndex (Y.map (A5Mod.commHom u)) :=
    four_le_relIndex_map hW e
      (fun _ _ _ h => by rw [Subgroup.mem_bot.mp h, map_one]; exact one_mem _) hY (by
        obtain ⟨l, hl, y, hy, hly⟩ := hntY
        exact ⟨l, hl, y, hy, fun h => hly (Subgroup.mem_bot.mp h)⟩) hu hu2 hu1
  rw [Subgroup.relIndex_bot_left] at h1
  have h2 := four_le_relIndex_map hW e hY hZ hntZ hu hu2 hu1
  have hfY : Y.map (A5Mod.commHom u) ≤ Y := by
    rintro _ ⟨y, hy, rfl⟩
    exact Y.mul_mem (hY u hu y hy) (Y.inv_mem hy)
  have h3 := card_map_mul_relIndex_le hYZ hfY
  have h4 : Nat.card (Z.map (A5Mod.commHom u)) ≤ Nat.card (A5Mod.commHom u).range :=
    Subgroup.card_le_of_le (Subgroup.map_le_range _ _)
  nlinarith

end CFSG.Quasithin.H13.L32A.C.Alt7Mod

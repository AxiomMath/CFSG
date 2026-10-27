module

public import CFSG.Quasithin.EmptyFaithful.SzN31SmD6A
public import CFSG.Quasithin.EmptyFaithful.SzN31Mas

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SzN31

open CFSG.Quasithin.G11

namespace SmD6

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {Γ A : Subgroup (GLV V)}

theorem pgroup_card_modEq {q : ℕ} (hq : q.Prime) (P : Subgroup (GLV V)) (hP : IsPGroup q P)
    (T : Submodule (ZMod 2) V) (hT : ∀ g ∈ P, ∀ v ∈ T, g v ∈ T) :
    2 ^ Module.finrank (ZMod 2) T ≡ 2 ^ Module.finrank (ZMod 2) ↥(T ⊓ fixedSpace P) [MOD q] := by
  have : Fact q.Prime := ⟨hq⟩
  let T' : SubMulAction P V := ⟨(T : Set V), fun g v hv => hT g g.2 v hv⟩
  have hmod := hP.card_modEq_card_fixedPoints T'
  have hfix : Nat.card (MulAction.fixedPoints P T') = Nat.card ↥(T ⊓ fixedSpace P) := by
    refine Nat.card_congr
      { toFun := fun a => ⟨(a.1 : V), a.1.2, fun g hg => congrArg Subtype.val (a.2 ⟨g, hg⟩)⟩
        invFun := fun b => ⟨⟨b.1, b.2.1⟩, fun g => Subtype.ext (b.2.2 g g.2)⟩
        left_inv := fun a => rfl
        right_inv := fun b => rfl }
  have hcard : ∀ S : Submodule (ZMod 2) V, Nat.card S = 2 ^ Module.finrank (ZMod 2) S := by
    intro S
    have : Module.Finite (ZMod 2) S := Module.Finite.of_finite
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have h1 : Nat.card T' = 2 ^ Module.finrank (ZMod 2) T := by
    rw [show Nat.card T' = Nat.card T from Nat.card_congr (Equiv.refl _), hcard]
  rw [hfix, h1, hcard] at hmod
  exact hmod

theorem trichotomy {P : Subgroup (GLV V)} (hP : IsPGroup 3 P) {U : Submodule (ZMod 2) V}
    (hU : Invariant P U) (hU2 : Module.finrank (ZMod 2) U = 2) {p : GLV V} (hp : p ∈ P) :
    (∀ u ∈ U, p u = u) ∨ (∀ u ∈ U, p u = u → u = 0) := by
  have hH : Subgroup.zpowers p ≤ P := Subgroup.zpowers_le.2 hp
  have hHp : IsPGroup 3 (Subgroup.zpowers p) := hP.to_le hH
  have hmod := pgroup_card_modEq Nat.prime_three (Subgroup.zpowers p) hHp U
    (fun g hg v hv => hU g (hH hg) v hv)
  have hc : Module.finrank (ZMod 2) ↥(U ⊓ fixedSpace (Subgroup.zpowers p)) ≤ 2 := by
    exact (Submodule.finrank_mono inf_le_left).trans hU2.le
  rw [hU2] at hmod
  have hfin : Module.Finite (ZMod 2) ↥(U ⊓ fixedSpace (Subgroup.zpowers p)) := Module.Finite.of_finite
  generalize hcdef : Module.finrank (ZMod 2) ↥(U ⊓ fixedSpace (Subgroup.zpowers p)) = c at hmod hc
  interval_cases c
  · right
    intro u hu hpu
    have hmem : u ∈ U ⊓ fixedSpace (Subgroup.zpowers p) := by
      refine ⟨hu, fun k hk => ?_⟩
      have hstab : Subgroup.zpowers p ≤ MulAction.stabilizer (GLV V) u :=
        Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 hpu)
      exact MulAction.mem_stabilizer_iff.1 (hstab hk)
    have h0 : U ⊓ fixedSpace (Subgroup.zpowers p) = ⊥ := Submodule.finrank_eq_zero.1 hcdef
    rw [h0] at hmem
    exact (Submodule.mem_bot (ZMod 2)).1 hmem
  · exfalso
    unfold Nat.ModEq at hmod
    norm_num at hmod
  · left
    have heq : U ⊓ fixedSpace (Subgroup.zpowers p) = U :=
      Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [hcdef, hU2])
    intro u hu
    have : u ∈ U ⊓ fixedSpace (Subgroup.zpowers p) := by rw [heq]; exact hu
    exact this.2 p (Subgroup.mem_zpowers p)


structure ThreePlanes (Γ P : Subgroup (GLV V)) (W : Fin 3 → Submodule (ZMod 2) V) : Prop where
  inv : ∀ i, Invariant P (W i)
  rank : ∀ i, Module.finrank (ZMod 2) (W i) = 2
  conj : ∀ i, ∃ g ∈ Γ, W i = G11.conjSub g (W 0)
  min : ∀ U : Submodule (ZMod 2) V, Invariant P U → U ≠ ⊥ → 2 ≤ Module.finrank (ZMod 2) U
  disj01 : Disjoint (W 0) (W 1)
  disj012 : Disjoint (W 0 ⊔ W 1) (W 2)
  sup : W 0 ⊔ W 1 ⊔ W 2 = ⊤

theorem exists_threePlanes (hirr : IsIrr Γ ⊤) {P : Subgroup (GLV V)}
    (hPn : ∀ γ ∈ Γ, ∀ n ∈ P, γ * n * γ⁻¹ ∈ P) (hd : Module.finrank (ZMod 2) V = 6)
    {W : Submodule (ZMod 2) V} (hWinv : Invariant P W) (hW2 : Module.finrank (ZMod 2) W = 2)
    (hmin : ∀ U : Submodule (ZMod 2) V, Invariant P U → U ≠ ⊥ → 2 ≤ Module.finrank (ZMod 2) U) :
    ∃ W' : Fin 3 → Submodule (ZMod 2) V, ThreePlanes Γ P W' := by
  have hWne : W ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hW2
    omega
  have hcinv : ∀ g ∈ Γ, Invariant P (G11.conjSub g W) := fun g hg => hWinv.conj_of_normal hPn hg
  have hcrank : ∀ g : GLV V, Module.finrank (ZMod 2) (G11.conjSub g W) = 2 := fun g => by
    rw [finrank_conjSub, hW2]
  have hS : (⨆ g : Γ, G11.conjSub (g : GLV V) W) = ⊤ := by
    have hSinv : Invariant Γ (⨆ g : Γ, G11.conjSub (g : GLV V) W) := by
      intro h hh u hu
      have hu' : u ∈ ⨆ g : Γ, G11.conjSub (g : GLV V) W := hu
      refine Submodule.iSup_induction _ (motive := fun u => h u ∈ ⨆ g : Γ, G11.conjSub (g : GLV V) W)
        hu' ?_ ?_ ?_
      · rintro ⟨g, hg⟩ x hx
        have : h x ∈ G11.conjSub ((⟨h, hh⟩ * ⟨g, hg⟩ : Γ) : GLV V) W := by
          obtain ⟨w, hw, rfl⟩ := hx
          exact ⟨w, hw, rfl⟩
        exact Submodule.mem_iSup_of_mem (⟨h, hh⟩ * ⟨g, hg⟩ : Γ) this
      · simp
      · intro x y hx hy
        rw [map_add]
        exact Submodule.add_mem _ hx hy
    rcases hirr.eq_bot_or_eq hSinv le_top with h | h
    · exfalso
      apply hWne
      rw [eq_bot_iff, ← h]
      have : G11.conjSub (1 : GLV V) W ≤ ⨆ g : Γ, G11.conjSub (g : GLV V) W :=
        le_iSup (fun g : Γ => G11.conjSub (g : GLV V) W) 1
      rwa [G11.conjSub_one] at this
    · exact h
  have step : ∀ U : Submodule (ZMod 2) V, Invariant P U → Module.finrank (ZMod 2) U < 6 →
      ∃ g ∈ Γ, Disjoint U (G11.conjSub g W) := by
    intro U hU hU6
    by_contra hcon
    push Not at hcon
    have hle : ∀ g : Γ, G11.conjSub (g : GLV V) W ≤ U := by
      intro g
      have hne : U ⊓ G11.conjSub (g : GLV V) W ≠ ⊥ := fun h => hcon g g.2 (disjoint_iff.2 h)
      have hinv : Invariant P (U ⊓ G11.conjSub (g : GLV V) W) := hU.inf (hcinv g g.2)
      have h2 := hmin _ hinv hne
      have heq : U ⊓ G11.conjSub (g : GLV V) W = G11.conjSub (g : GLV V) W :=
        Submodule.eq_of_le_of_finrank_eq inf_le_right (le_antisymm
          (Submodule.finrank_mono inf_le_right) (by rw [hcrank]; exact h2))
      rw [← heq]
      exact inf_le_left
    have : (⊤ : Submodule (ZMod 2) V) ≤ U := by
      rw [← hS]
      exact iSup_le hle
    have := Submodule.finrank_mono this
    rw [finrank_top, hd] at this
    omega
  obtain ⟨g₂, hg₂, hd₂⟩ := step W hWinv (by omega)
  have hU₂inv : Invariant P (W ⊔ G11.conjSub g₂ W) := hWinv.sup (hcinv g₂ hg₂)
  have hU₂rank : Module.finrank (ZMod 2) ↥(W ⊔ G11.conjSub g₂ W) = 4 := by
    have h1 : Module.Finite (ZMod 2) W := Module.Finite.of_finite
    have h2 : Module.Finite (ZMod 2) (G11.conjSub g₂ W) := Module.Finite.of_finite
    have := Submodule.finrank_sup_add_finrank_inf_eq W (G11.conjSub g₂ W)
    rw [disjoint_iff.1 hd₂, finrank_bot, hW2, hcrank] at this
    omega
  obtain ⟨g₃, hg₃, hd₃⟩ := step (W ⊔ G11.conjSub g₂ W) hU₂inv (by omega)
  have hsup : W ⊔ G11.conjSub g₂ W ⊔ G11.conjSub g₃ W = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h1 : Module.Finite (ZMod 2) ↥(W ⊔ G11.conjSub g₂ W) := Module.Finite.of_finite
    have h2 : Module.Finite (ZMod 2) (G11.conjSub g₃ W) := Module.Finite.of_finite
    have := Submodule.finrank_sup_add_finrank_inf_eq (W ⊔ G11.conjSub g₂ W) (G11.conjSub g₃ W)
    rw [disjoint_iff.1 hd₃, finrank_bot, hU₂rank, hcrank] at this
    rw [hd]
    omega
  refine ⟨![W, G11.conjSub g₂ W, G11.conjSub g₃ W], ?_, ?_, ?_, hmin, hd₂, hd₃, hsup⟩
  · intro i
    fin_cases i
    · exact hWinv
    · exact hcinv g₂ hg₂
    · exact hcinv g₃ hg₃
  · intro i
    fin_cases i
    · exact hW2
    · exact hcrank g₂
    · exact hcrank g₃
  · intro i
    fin_cases i
    · exact ⟨1, Γ.one_mem, (G11.conjSub_one W).symm⟩
    · exact ⟨g₂, hg₂, rfl⟩
    · exact ⟨g₃, hg₃, rfl⟩


theorem not_three_dvd_two_pow_sub_one_of_odd {d : ℕ} (hd : Odd d) : ¬ 3 ∣ 2 ^ d - 1 := by
  obtain ⟨k, rfl⟩ := hd
  have h : 2 ^ (2 * k + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hpos : 1 ≤ 2 ^ (2 * k + 1) := Nat.one_le_two_pow
  generalize 2 ^ (2 * k + 1) = x at h hpos ⊢
  omega

theorem Ctx.simple_or_planes (hC : Ctx Γ A) :
    (∀ U : Submodule (ZMod 2) V, Invariant (CFSG.Open.pCoreOf 3 Γ) U → U = ⊥ ∨ U = ⊤) ∨
      ∃ W : Fin 3 → Submodule (ZMod 2) V, ThreePlanes Γ (CFSG.Open.pCoreOf 3 Γ) W := by
  classical
  have hirr := hC.hyp.irreducible
  have hPn : ∀ γ ∈ Γ, ∀ n ∈ CFSG.Open.pCoreOf 3 Γ, γ * n * γ⁻¹ ∈ CFSG.Open.pCoreOf 3 Γ :=
    pCoreOf_normal_conj 3 Γ
  have hP3 : IsPGroup 3 (CFSG.Open.pCoreOf 3 Γ) := isPGroup_pCoreOf 3 Γ
  have hfix : fixedSpace (CFSG.Open.pCoreOf 3 Γ) = ⊥ := hC.fixedSpace_eq_bot
  have hex : ∃ n, ∃ U : Submodule (ZMod 2) V, U ≠ ⊥ ∧ Invariant (CFSG.Open.pCoreOf 3 Γ) U ∧
      Module.finrank (ZMod 2) U = n := ⟨_, ⊤, hirr.ne_bot, invariant_top _, rfl⟩
  obtain ⟨W, hWne, hWinv, hWn⟩ := Nat.find_spec hex
  have hmin : ∀ U : Submodule (ZMod 2) V, Invariant (CFSG.Open.pCoreOf 3 Γ) U → U ≠ ⊥ →
      Nat.find hex ≤ Module.finrank (ZMod 2) U := fun U h1 h2 => Nat.find_min' hex ⟨U, h2, h1, rfl⟩
  generalize Nat.find hex = n at hWn hmin
  have hdvd : 3 ∣ 2 ^ n - 1 := by
    rw [← hWn]
    exact pgroup_dvd_two_pow Nat.prime_three _ hP3 W hWinv (fun v hvW hv => by
      have hv' : v ∈ fixedSpace (CFSG.Open.pCoreOf 3 Γ) := fun q hq => hv q hq
      rw [hfix] at hv'
      exact (Submodule.mem_bot (ZMod 2)).1 hv')
  have heven : Even n := by
    by_contra h
    exact not_three_dvd_two_pow_sub_one_of_odd (Nat.not_even_iff_odd.1 h) hdvd
  have hnpos : 0 < n := by
    rw [← hWn]
    have : Module.Finite (ZMod 2) W := Module.Finite.of_finite
    exact Nat.pos_of_ne_zero fun h => hWne (Submodule.finrank_eq_zero.1 h)
  have hn6 : n ≤ 6 := by
    rw [← hWn, ← hC.hd]
    exact Submodule.finrank_le W
  have hn4 : n ≠ 4 := by
    intro h4
    have hodd := odd_card_pCoreOf Nat.prime_three (by norm_num) Γ
    have hnd : ¬ 2 ∣ Nat.card ↥(CFSG.Open.pCoreOf 3 Γ) := by
      have := Nat.odd_iff.1 hodd
      omega
    obtain ⟨U', hU'inv, hcompl⟩ := exists_invariant_isCompl_of_odd hnd hWinv
    have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
    rw [hC.hd, hWn, h4] at hsum
    have hU'ne : U' ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hsum
      omega
    have := hmin U' hU'inv hU'ne
    omega
  have hn : n = 2 ∨ n = 6 := by
    obtain ⟨k, hk⟩ := heven
    omega
  rcases hn with rfl | rfl
  · exact Or.inr (exists_threePlanes hirr hPn hC.hd hWinv hWn hmin)
  · left
    intro U hUinv
    by_cases hU : U = ⊥
    · exact Or.inl hU
    · right
      apply Submodule.eq_top_of_finrank_eq
      have h1 := hmin U hUinv hU
      have h2 : Module.finrank (ZMod 2) U ≤ Module.finrank (ZMod 2) V := Submodule.finrank_le U
      rw [hC.hd] at h2 ⊢
      omega


end SmD6

end CFSG.Quasithin.SzN31

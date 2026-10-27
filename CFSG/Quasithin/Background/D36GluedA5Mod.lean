module

public import CFSG.Quasithin.Background.B1MoreQuot

public section

namespace CFSG.Quasithin.A5Mod

variable {M : Type} [CommGroup M]

@[expose] def fixSub (φ : MulAut M) : Subgroup M where
  carrier := {x | φ x = x}
  one_mem' := map_one φ
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, ha, hb]
  inv_mem' := fun {a} ha => by
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_inv, ha]

theorem mem_fixSub {φ : MulAut M} {x : M} : x ∈ fixSub φ ↔ φ x = x := Iff.rfl

@[expose] def commHom (φ : MulAut M) : M →* M where
  toFun x := φ x * x⁻¹
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul, mul_inv_rev]
    ac_rfl

theorem commHom_apply (φ : MulAut M) (x : M) : commHom φ x = φ x * x⁻¹ := rfl

theorem ker_commHom (φ : MulAut M) : (commHom φ).ker = fixSub φ := by
  ext x
  rw [MonoidHom.mem_ker, commHom_apply, mem_fixSub, mul_inv_eq_one]

theorem card_fixSub_mul_card_range (φ : MulAut M) :
    Nat.card (fixSub φ) * Nat.card (commHom φ).range = Nat.card M := by
  have h1 := (commHom φ).ker.card_mul_index
  rw [Subgroup.index_ker, ker_commHom] at h1
  exact h1

theorem range_commHom_le_fixSub (hM : ∀ x : M, x ^ 2 = 1) {φ : MulAut M} (hφ : φ * φ = 1) :
    (commHom φ).range ≤ fixSub φ := by
  rintro _ ⟨x, rfl⟩
  show φ (φ x * x⁻¹) = φ x * x⁻¹
  have h1 : φ (φ x) = x := by
    have := congrArg (fun ψ : MulAut M => ψ x) hφ
    simpa [MulAut.mul_apply] using this
  have h2 : (φ x * x⁻¹) ^ 2 = 1 := hM _
  have h3 : (φ x * x⁻¹)⁻¹ = φ x * x⁻¹ := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using h2)
  rw [map_mul, map_inv, h1, ← h3]
  simp [mul_comm]

theorem card_le_sq_fixSub [Finite M] (hM : ∀ x : M, x ^ 2 = 1) {φ : MulAut M} (hφ : φ * φ = 1) :
    Nat.card M ≤ Nat.card (fixSub φ) * Nat.card (fixSub φ) := by
  rw [← card_fixSub_mul_card_range φ]
  exact Nat.mul_le_mul_left _ (Subgroup.card_le_of_le (range_commHom_le_fixSub hM hφ))

theorem pow_mem_of_invariant {φ : MulAut M} {S : Subgroup M} (hS : ∀ x ∈ S, φ x ∈ S) (n : ℕ) :
    ∀ x ∈ S, (φ ^ n) x ∈ S := by
  induction n with
  | zero => intro x hx; simpa using hx
  | succ n ih =>
    intro x hx
    have : (φ ^ (n + 1)) x = (φ ^ n) (φ x) := by
      rw [pow_succ, MulAut.mul_apply]
    rw [this]
    exact ih _ (hS x hx)

theorem card_fixedPoints_modEq' {α : Type} [Finite α] (p : ℕ) [Fact p.Prime]
    (σ : Equiv.Perm α) (hσ : σ ^ p = 1) :
    Nat.card α ≡ Nat.card {x // σ x = x} [MOD p] := by
  classical
  haveI := Fintype.ofFinite α
  have h := Equiv.Perm.card_compl_support_modEq (p := p) (n := 1) (σ := σ) (by rwa [pow_one])
  have e : (σ.supportᶜ : Finset α).card = Nat.card {x // σ x = x} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext x
    simp
  rw [e] at h
  rw [Nat.card_eq_fintype_card]
  exact h.symm

theorem card_fix_modEq [Finite M] (p : ℕ) [hp : Fact p.Prime] (φ : MulAut M) (hφ : φ ^ p = 1)
    (S : Subgroup M) (hS : ∀ x ∈ S, φ x ∈ S) :
    Nat.card S ≡ Nat.card ↥(S ⊓ fixSub φ) [MOD p] := by
  have hinvφ : φ⁻¹ = φ ^ (p - 1) := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_succ' φ (p - 1), Nat.sub_add_cancel hp.out.one_lt.le, hφ]
  have hinv : ∀ x ∈ S, φ⁻¹ x ∈ S := by
    intro x hx
    rw [hinvφ]
    exact pow_mem_of_invariant hS _ x hx
  let σ : Equiv.Perm S :=
    { toFun := fun x => ⟨φ x, hS x x.2⟩
      invFun := fun x => ⟨φ⁻¹ x, hinv x x.2⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp) }
  have hσn : ∀ n : ℕ, ∀ x : S, ((σ ^ n) x : M) = (φ ^ n) (x : M) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, Equiv.Perm.mul_apply, ih, pow_succ, MulAut.mul_apply]
      rfl
  have hσp : σ ^ p = 1 := by
    ext x
    rw [hσn, hφ]
    simp
  have h := card_fixedPoints_modEq' p σ hσp
  have e : Nat.card {x : S // σ x = x} = Nat.card ↥(S ⊓ fixSub φ) := by
    refine Nat.card_congr ⟨fun x => ⟨(x.1 : M), x.1.2, ?_⟩, fun x => ⟨⟨(x : M), x.2.1⟩, ?_⟩, ?_, ?_⟩
    · have := congrArg (fun y : S => (y : M)) x.2
      exact this
    · exact Subtype.ext x.2.2
    · intro x; rfl
    · intro x; rfl
  rw [e] at h
  exact h

theorem exists_ne_one_of_two_le_card {S : Subgroup M} (h : 2 ≤ Nat.card S) : ∃ x ∈ S, x ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have : S = ⊥ := (Subgroup.eq_bot_iff_forall S).mpr hcon
  rw [this, Subgroup.card_bot] at h
  omega

theorem card_fixSub_inf_le_two [Finite M] (hM : ∀ x : M, x ^ 2 = 1) (hcard : Nat.card M = 16)
    {b l g : MulAut M} (hb2 : b * b = 1) (hb1 : b ≠ 1) (hl2 : l * l = 1) (hg3 : g ^ 3 = 1)
    (hgfix : ∀ x : M, g x = x → x = 1) (hbg : b * g = g * b) (hbl : b * l = l * b)
    (hlg : l * g * l = g⁻¹) : Nat.card ↥(fixSub b ⊓ fixSub l) ≤ 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hbg' : ∀ x : M, b (g x) = g (b x) := fun x => by
    have := congrArg (fun ψ : MulAut M => ψ x) hbg
    simpa [MulAut.mul_apply] using this
  have hbl' : ∀ x : M, b (l x) = l (b x) := fun x => by
    have := congrArg (fun ψ : MulAut M => ψ x) hbl
    simpa [MulAut.mul_apply] using this
  have hCg : ∀ x ∈ fixSub b, g x ∈ fixSub b := fun x hx => by
    rw [mem_fixSub] at hx ⊢
    rw [hbg', hx]
  have hCl : ∀ x ∈ fixSub b, l x ∈ fixSub b := fun x hx => by
    rw [mem_fixSub] at hx ⊢
    rw [hbl', hx]
  have hmod := card_fix_modEq 3 g hg3 (fixSub b) hCg
  have hbot : fixSub b ⊓ fixSub g = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    exact hgfix x hx.2
  rw [hbot, Subgroup.card_bot] at hmod
  have hdvd : Nat.card (fixSub b) ∣ 2 ^ 4 := by
    have := Subgroup.card_subgroup_dvd_card (fixSub b)
    rwa [hcard] at this
  obtain ⟨i, hi4, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hsq := card_le_sq_fixSub hM hb2
  rw [hcard, hi] at hsq
  have hC4 : Nat.card (fixSub b) = 4 := by
    rw [hi] at hmod ⊢
    interval_cases i
    · norm_num at hsq
    · norm_num at hsq
    · rfl
    · norm_num [Nat.ModEq] at hmod
    · exfalso
      apply hb1
      have htop : fixSub b = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hi, hcard]; norm_num)
      refine MulEquiv.ext fun x => ?_
      have : x ∈ fixSub b := by rw [htop]; trivial
      exact this
  by_contra hcon
  push Not at hcon
  have hd2 : Nat.card ↥(fixSub b ⊓ fixSub l) ∣ 4 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : fixSub b ⊓ fixSub l ≤ fixSub b)
    rwa [hC4] at this
  have h4 : Nat.card ↥(fixSub b ⊓ fixSub l) = 4 := by
    have hle : Nat.card ↥(fixSub b ⊓ fixSub l) ≤ 4 := Nat.le_of_dvd (by norm_num) hd2
    generalize Nat.card ↥(fixSub b ⊓ fixSub l) = c at hd2 hle hcon ⊢
    interval_cases c <;> omega
  have hCle : fixSub b ≤ fixSub l := by
    have heq : fixSub b ⊓ fixSub l = fixSub b :=
      Subgroup.eq_of_le_of_card_ge (inf_le_left) (by rw [h4, hC4])
    rw [← heq]
    exact inf_le_right
  have hCtriv : ∀ x ∈ fixSub b, x = 1 := by
    intro x hx
    have h1 : l x = x := hCle hx
    have h2 : l (g x) = g x := hCle (hCg x hx)
    have h3 : (l * g * l) x = g⁻¹ x := by rw [hlg]
    simp only [MulAut.mul_apply, h1, h2] at h3
    have h4 : g (g x) = x := by
      have := congrArg g h3
      simpa using this
    have h5 : g x = x := by
      have h6 : (g ^ 3) x = x := by rw [hg3]; rfl
      have h7 : (g ^ 3) x = g (g (g x)) := by
        simp [pow_succ, MulAut.mul_apply]
      rw [h7, h4] at h6
      exact h6
    exact hgfix x h5
  have : fixSub b = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hCtriv
  rw [this, Subgroup.card_bot] at hC4
  omega

theorem exists_fixed_of_two [Finite M] (hM : ∀ x : M, x ^ 2 = 1) {l g : MulAut M}
    (hl2 : l * l = 1) (hlg : l * g * l = g⁻¹) (hne : ∃ x : M, g x = x ∧ x ≠ 1) :
    ∃ p : M, p ≠ 1 ∧ g p = p ∧ l p = p := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hl2' : l ^ 2 = 1 := by rw [pow_two]; exact hl2
  have hll : ∀ x : M, l (l x) = x := fun x => by
    have := congrArg (fun ψ : MulAut M => ψ x) hl2
    simpa [MulAut.mul_apply] using this
  have hS : ∀ x ∈ fixSub g, l x ∈ fixSub g := by
    intro x hx
    rw [mem_fixSub] at hx ⊢
    have h1 : (l * g * l) (l x) = g⁻¹ (l x) := by rw [hlg]
    simp only [MulAut.mul_apply, hll] at h1
    have h2 : l (g x) = g⁻¹ (l x) := h1
    rw [hx] at h2
    have h3 : g (l x) = l x := by
      have := congrArg g h2
      simpa using this
    exact h3
  have hmod := card_fix_modEq 2 l hl2' (fixSub g) hS
  have hpg : IsPGroup 2 (fixSub g) :=
    (isPGroup_two_of_sq_eq_one hM).to_subgroup (fixSub g)
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hpg
  obtain ⟨x, hxg, hx1⟩ := hne
  have hn1 : 1 ≤ n := by
    by_contra h0
    have h0' : n = 0 := by omega
    rw [h0', pow_zero] at hn
    have : fixSub g = ⊥ := Subgroup.card_eq_one.mp hn
    exact hx1 (by simpa [this] using (show x ∈ fixSub g from hxg))
  have heven : 2 ∣ Nat.card (fixSub g) := by
    rw [hn]
    exact dvd_pow_self 2 (by omega)
  have h2le : 2 ≤ Nat.card ↥(fixSub g ⊓ fixSub l) := by
    have hdvd2 : 2 ∣ Nat.card ↥(fixSub g ⊓ fixSub l) :=
      (Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr heven)))
    have hpos : 0 < Nat.card ↥(fixSub g ⊓ fixSub l) := Nat.card_pos
    obtain ⟨c, hc⟩ := hdvd2
    omega
  obtain ⟨y, hy, hy1⟩ := exists_ne_one_of_two_le_card h2le
  exact ⟨y, hy1, hy.1, hy.2⟩

section Hom

variable {G : Type} [CommGroup G]

theorem card_ker_mul_card_range [Finite G] {N : Type} [Group N] (f : G →* N) :
    Nat.card f.ker * Nat.card f.range = Nat.card G := by
  have h1 := f.ker.card_mul_index
  rwa [Subgroup.index_ker] at h1

theorem card_range_commHom_le_two [Finite G] {M : Type} [CommGroup M] (π : G →* M)
    (hπ : Function.Surjective π) (a : MulAut M) (K : Subgroup G) (hK : Nat.card G ≤ 2 * Nat.card K)
    (hker : ∀ g ∈ K, commHom a (π g) = 1) : Nat.card (commHom a).range ≤ 2 := by
  have hrange : ((commHom a).comp π).range = (commHom a).range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hπ, Subgroup.map_top]
  have hK' : K ≤ ((commHom a).comp π).ker := fun g hg => hker g hg
  have h1 := card_ker_mul_card_range ((commHom a).comp π)
  have h2 := Subgroup.card_le_of_le hK'
  rw [hrange] at h1
  have hpos : 0 < Nat.card K := Nat.card_pos
  by_contra hcon
  push Not at hcon
  have : Nat.card K * 3 ≤ Nat.card ((commHom a).comp π).ker * Nat.card (commHom a).range :=
    Nat.mul_le_mul h2 hcon
  omega

theorem card_le_mul_of_map_le [Finite G] {M : Type} [CommGroup M] [Finite M] (π : G →* M)
    (K : Subgroup G)
    (C : Subgroup M) (hKC : K.map π ≤ C) : Nat.card K ≤ Nat.card C * Nat.card π.ker := by
  have h1 := B1More.card_map_mul_card_inf_ker K π
  have h2 : Nat.card (K.map π) ≤ Nat.card C := Subgroup.card_le_of_le hKC
  have h3 : Nat.card ↥(K ⊓ π.ker) ≤ Nat.card π.ker := Subgroup.card_le_of_le
    (by intro x hx; exact hx.2)
  rw [← h1]
  exact Nat.mul_le_mul h2 h3

end Hom

end CFSG.Quasithin.A5Mod

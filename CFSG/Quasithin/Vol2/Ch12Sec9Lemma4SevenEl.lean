module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.Quasithin.H13.G112Seven

open scoped Pointwise

section Count

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def fix (g : V ≃ₗ[ZMod 2] V) : Submodule (ZMod 2) V :=
  LinearMap.ker ((g : V →ₗ[ZMod 2] V) - LinearMap.id)

theorem mem_fix {g : V ≃ₗ[ZMod 2] V} {v : V} : v ∈ fix g ↔ g v = v := by
  simp [fix, sub_eq_zero]

theorem eq_one_of_fix_eq_top {g : V ≃ₗ[ZMod 2] V} (h : fix g = ⊤) : g = 1 := by
  ext v
  exact mem_fix.1 (h ▸ Submodule.mem_top)

theorem card_top : Nat.card ↥(⊤ : Submodule (ZMod 2) V) = Nat.card V :=
  Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => Submodule.mem_top)

theorem card_eq_two_pow (hV : Nat.card V = 2 ^ 12) (U : Submodule (ZMod 2) V) :
    ∃ k ≤ 12, Nat.card U = 2 ^ k := by
  have h := AddSubgroup.card_addSubgroup_dvd_card U.toAddSubgroup
  rw [hV] at h
  exact (Nat.dvd_prime_pow Nat.prime_two).1 h

theorem card_dvd_of_le {U U' : Submodule (ZMod 2) V} (h : U ≤ U') :
    Nat.card U ∣ Nat.card U' :=
  AddSubgroup.card_dvd_of_le (H := U.toAddSubgroup) (K := U'.toAddSubgroup) h

theorem eq_of_le_of_card [Finite V] {U U' : Submodule (ZMod 2) V} (h : U ≤ U')
    (hc : Nat.card U' = Nat.card U) : U = U' :=
  Submodule.toAddSubgroup_injective
    (AddSubgroup.eq_of_le_of_card_ge (H := U.toAddSubgroup) (K := U'.toAddSubgroup) h hc.le)

theorem fix_eq_top_of_card [Finite V] (hV : Nat.card V = 2 ^ 12) {g : V ≃ₗ[ZMod 2] V}
    (h : Nat.card ↥(fix g) = 2 ^ 12) : fix g = ⊤ :=
  eq_of_le_of_card le_top (by rw [card_top, hV, h])

theorem card_modEq_fixedPoints {α : Type*} [Finite α] {p : ℕ} [Fact p.Prime] (f : α → α)
    (hf : ∀ x, f^[p] x = x) : Nat.card α ≡ Nat.card ↑(Function.fixedPoints f) [MOD p] := by
  classical
  have := Fintype.ofFinite α
  let F : Function.End α := f
  have hpow : ∀ (n : ℕ) (x : α), (F ^ n) x = f^[n] x := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ', Function.iterate_succ_apply', ← ih]
      rfl
  have hF : F ^ p ^ 1 = 1 := by
    rw [pow_one]
    funext x
    rw [hpow, hf]
    rfl
  have h := Equiv.Perm.card_fixedPoints_modEq (p := p) (n := 1) hF
  rwa [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at h

theorem card_modEq_inf_fix [Finite V] {p : ℕ} [Fact p.Prime] {g : V ≃ₗ[ZMod 2] V} (hg : g ^ p = 1)
    {U : Submodule (ZMod 2) V} (hU : ∀ v ∈ U, g v ∈ U) :
    Nat.card U ≡ Nat.card ↥(U ⊓ fix g) [MOD p] := by
  let f : ↥U → ↥U := fun x => ⟨g x, hU x x.2⟩
  have hpow : ∀ (n : ℕ) (x : ↥U), (f^[n] x : V) = (g ^ n) x := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply', pow_succ']
      show g (f^[n] x : V) = g ((g ^ n) x)
      rw [ih]
  have h := card_modEq_fixedPoints f fun x => Subtype.ext (by rw [hpow, hg]; rfl)
  have e : Nat.card ↑(Function.fixedPoints f) = Nat.card ↥(U ⊓ fix g) := Nat.card_congr
    { toFun := fun x => ⟨x.1.1, x.1.2, mem_fix.2 (congrArg Subtype.val x.2)⟩
      invFun := fun y => ⟨⟨y.1, y.2.1⟩, Subtype.ext (mem_fix.1 y.2.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rwa [e] at h

theorem false_of_commute [Finite V] (hV : Nat.card V = 2 ^ 12) {a b : V ≃ₗ[ZMod 2] V}
    (ha : a ^ 7 = 1) (ha1 : a ≠ 1) (hb : b ^ 11 = 1) (hb1 : b ≠ 1) (hab : a * b = b * a) :
    False := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hc : ∀ v, a (b v) = b (a v) := fun v => congrArg (fun g : V ≃ₗ[ZMod 2] V => g v) hab
  have hinvA : ∀ v ∈ fix b, a v ∈ fix b := fun v hv => by
    rw [mem_fix] at hv ⊢
    rw [← hc, hv]
  have hinvB : ∀ v ∈ fix a, b v ∈ fix a := fun v hv => by
    rw [mem_fix] at hv ⊢
    rw [hc, hv]
  have htop : ∀ g : V ≃ₗ[ZMod 2] V, ∀ v ∈ (⊤ : Submodule (ZMod 2) V),
      g v ∈ (⊤ : Submodule (ZMod 2) V) := fun _ _ _ => Submodule.mem_top
  have h1 := card_modEq_inf_fix hb (htop b)
  rw [card_top, hV, top_inf_eq] at h1
  obtain ⟨k, hk, hkc⟩ := card_eq_two_pow hV (fix b)
  rw [hkc] at h1
  have hk12 : k ≠ 12 := by
    rintro rfl
    exact hb1 (eq_one_of_fix_eq_top (fix_eq_top_of_card hV hkc))
  have hk2 : k = 2 := by
    interval_cases k <;> first | rfl | exact absurd h1 (by decide) | exact absurd rfl hk12
  rw [hk2] at hkc
  have h2 := card_modEq_inf_fix ha hinvA
  obtain ⟨j, -, hjc⟩ := card_eq_two_pow hV (fix b ⊓ fix a)
  have hjdvd : 2 ^ j ∣ 2 ^ 2 := by
    have := card_dvd_of_le (inf_le_left : fix b ⊓ fix a ≤ fix b)
    rwa [hjc, hkc] at this
  have hj : j ≤ 2 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hjdvd
  rw [hkc, hjc] at h2
  have hj2 : j = 2 := by
    interval_cases j <;> first | rfl | exact absurd h2 (by decide)
  have hle : fix b ≤ fix a := by
    have heq : fix b ⊓ fix a = fix b :=
      eq_of_le_of_card (inf_le_left : fix b ⊓ fix a ≤ fix b) (by rw [hjc, hkc, hj2])
    exact inf_eq_left.1 heq
  have h3 := card_modEq_inf_fix ha (htop a)
  rw [card_top, hV, top_inf_eq] at h3
  obtain ⟨m, hm, hmc⟩ := card_eq_two_pow hV (fix a)
  have hm12 : m ≠ 12 := by
    rintro rfl
    exact ha1 (eq_one_of_fix_eq_top (fix_eq_top_of_card hV hmc))
  have h4 := card_modEq_inf_fix hb hinvB
  rw [inf_eq_right.2 hle, hkc, hmc] at h4
  rw [hmc] at h3
  interval_cases m <;> first | exact absurd h3 (by decide) | exact absurd h4 (by decide) |
    exact hm12 rfl

end Count

section Eleven

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem factorization_seven : (2661120 : ℕ).factorization 7 = 1 := by
  have h : (2661120 : ℕ) = 7 * 380160 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_self (by norm_num), Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem eleven_dvd_card (hV : Nat.card V = 2 ^ 12) {Γ : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hΓ : Nat.card Γ = 2661120) (N : Subgroup ↥Γ) [N.Normal] (h7 : 7 ∣ Nat.card N) :
    11 ∣ Nat.card N := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have : Finite Γ := Nat.finite_of_card_ne_zero (by rw [hΓ]; norm_num)
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := Γ) 11 (by rw [hΓ]; norm_num)
  set φ : MulAut ↥N := MulAut.conjNormal b with hφ
  have hφ11 : φ ^ 11 = 1 := by rw [hφ, ← map_pow, ← hb, pow_orderOf_eq_one, map_one]
  have hN0 : Nat.card N ≠ 0 := Nat.card_pos.ne'
  have hN7 : (Nat.card N).factorization 7 = 1 := by
    refine le_antisymm ?_ ((Nat.Prime.dvd_iff_one_le_factorization (by norm_num) hN0).1 h7)
    have := (Nat.factorization_le_iff_dvd hN0 (by rw [hΓ]; norm_num)).2
      (Subgroup.card_subgroup_dvd_card N) 7
    rwa [hΓ, factorization_seven] at this
  let f : Sylow 7 ↥N → Sylow 7 ↥N := fun P => φ • P
  have hfpow : ∀ (n : ℕ) (P : Sylow 7 ↥N), f^[n] P = (φ ^ n) • P := by
    intro n
    induction n with
    | zero => intro P; exact (one_smul _ P).symm
    | succ n ih =>
      intro P
      rw [Function.iterate_succ_apply', ih, pow_succ', mul_smul]
  have hmod := card_modEq_fixedPoints f fun P => by rw [hfpow, hφ11, one_smul]
  have hnofix : Nat.card ↑(Function.fixedPoints f) = 0 := by
    suffices IsEmpty ↑(Function.fixedPoints f) from Nat.card_of_isEmpty
    refine ⟨fun ⟨P, hP⟩ => ?_⟩
    have hPP : φ • P = P := hP
    have hPc : Nat.card (P : Subgroup ↥N) = 7 := by
      rw [Sylow.card_eq_multiplicity, hN7, pow_one]
    have hφP : ∀ y ∈ (P : Subgroup ↥N), φ y ∈ (P : Subgroup ↥N) := by
      intro y hy
      have h := Subgroup.smul_mem_pointwise_smul y φ (P : Subgroup ↥N) hy
      rw [← Sylow.pointwise_smul_def, hPP] at h
      exact h
    let g : ↥(P : Subgroup ↥N) → ↥(P : Subgroup ↥N) := fun y => ⟨φ y, hφP y y.2⟩
    have hgpow : ∀ (n : ℕ) (y : ↥(P : Subgroup ↥N)), (g^[n] y : ↥N) = (φ ^ n) y := by
      intro n
      induction n with
      | zero => intro y; rfl
      | succ n ih =>
        intro y
        rw [Function.iterate_succ_apply', pow_succ']
        show φ (g^[n] y : ↥N) = φ ((φ ^ n) y)
        rw [ih]
    have hmodP := card_modEq_fixedPoints g fun y => Subtype.ext (by rw [hgpow, hφ11]; rfl)
    rw [hPc, Nat.card_coe_set_eq] at hmodP
    have hle : (Function.fixedPoints g).ncard ≤ 7 := by
      have h1 := Set.ncard_le_ncard (Set.subset_univ (Function.fixedPoints g))
      rwa [Set.ncard_univ, hPc] at h1
    have hcard : (Function.fixedPoints g).ncard = 7 := by
      unfold Nat.ModEq at hmodP
      omega
    obtain ⟨y, hy, hy1⟩ := Set.exists_ne_of_one_lt_ncard (s := Function.fixedPoints g)
      (by rw [hcard]; norm_num) 1
    have hy' : g y = y := hy
    have hyφ : φ (y : ↥N) = y := congrArg Subtype.val hy'
    have hcomm : (b : V ≃ₗ[ZMod 2] V) * (((y : ↥N) : ↥Γ) : V ≃ₗ[ZMod 2] V) =
        (((y : ↥N) : ↥Γ) : V ≃ₗ[ZMod 2] V) * (b : V ≃ₗ[ZMod 2] V) := by
      have h := congrArg (fun z : ↥N => ((z : ↥Γ) : V ≃ₗ[ZMod 2] V)) hyφ
      simp only [hφ, MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h
      calc (b : V ≃ₗ[ZMod 2] V) * (((y : ↥N) : ↥Γ) : V ≃ₗ[ZMod 2] V)
          = ((b : V ≃ₗ[ZMod 2] V) * (((y : ↥N) : ↥Γ) : V ≃ₗ[ZMod 2] V) *
            (b : V ≃ₗ[ZMod 2] V)⁻¹) * (b : V ≃ₗ[ZMod 2] V) := by group
        _ = (((y : ↥N) : ↥Γ) : V ≃ₗ[ZMod 2] V) * (b : V ≃ₗ[ZMod 2] V) := by rw [h]
    have hy7 : y ^ 7 = 1 := by
      have := (pow_card_eq_one' : y ^ Nat.card ↥(P : Subgroup ↥N) = 1)
      rwa [hPc] at this
    have hb11 : b ^ 11 = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
    refine false_of_commute hV (a := (((y : ↥N) : ↥Γ) : V ≃ₗ[ZMod 2] V))
      (b := (b : V ≃ₗ[ZMod 2] V)) ?_ ?_ ?_ ?_ hcomm.symm
    · have := congrArg (fun z : ↥(P : Subgroup ↥N) => (((z : ↥N) : ↥Γ) : V ≃ₗ[ZMod 2] V)) hy7
      simpa using this
    · intro h1
      apply hy1
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact h1
    · have := congrArg (fun z : ↥Γ => (z : V ≃ₗ[ZMod 2] V)) hb11
      simpa using this
    · intro h1
      have : b = 1 := Subtype.ext h1
      rw [this, orderOf_one] at hb
      norm_num at hb
  rw [hnofix] at hmod
  have h11 : 11 ∣ Nat.card (Sylow 7 ↥N) := Nat.modEq_zero_iff_dvd.1 hmod
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 7 ↥N))
  rw [Sylow.card_eq_index_normalizer P] at h11
  exact h11.trans (Subgroup.index_dvd_card _)

end Eleven

end CFSG.Quasithin.H13.G112Seven

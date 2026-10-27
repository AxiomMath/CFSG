module

public import CFSG.Quasithin.Background.SmithB42Sp4Excl

public section

namespace CFSG.Quasithin.B45Sp4

open CFSG.QuasithinUnique.Setup.X7b CFSG.QuasithinUnique.Setup.SL2Modules
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.Quasithin.B42Sp4

section Counting

theorem mul_card_fixed_lt {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    (A : Subgroup (M ≃ₗ[ZMod 2] M)) (t : M ≃ₗ[ZMod 2] M) (ht : t ∈ A) {N : ℕ}
    (hN : N < 2 ^ dispRank t) :
    N * Nat.card {m : M // ∀ a ∈ A, a m = m} < Nat.card M := by
  have : Module.Finite (ZMod 2) M := Module.Finite.of_finite
  set D : M →ₗ[ZMod 2] M := t.toLinearMap - 1 with hD
  have h1 : Nat.card M = 2 ^ Module.finrank (ZMod 2) M := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have h2 : Nat.card (LinearMap.ker D) = 2 ^ Module.finrank (ZMod 2) (LinearMap.ker D) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have h3 := LinearMap.finrank_range_add_finrank_ker D
  have hC : Nat.card {m : M // ∀ a ∈ A, a m = m} ≤ Nat.card (LinearMap.ker D) := by
    refine Nat.card_le_card_of_injective (fun m => ⟨m.1, ?_⟩) ?_
    · show t m.1 - m.1 = 0
      rw [m.2 t ht, sub_self]
    · intro a b h
      exact Subtype.ext (congrArg (fun x => x.1) h)
  have hpos : 0 < Nat.card (LinearMap.ker D) := Nat.card_pos
  calc N * Nat.card {m : M // ∀ a ∈ A, a m = m}
      ≤ N * Nat.card (LinearMap.ker D) := Nat.mul_le_mul_left _ hC
    _ < 2 ^ Module.finrank (ZMod 2) (LinearMap.range D) * Nat.card (LinearMap.ker D) :=
        Nat.mul_lt_mul_of_pos_right hN hpos
    _ = Nat.card M := by rw [h1, h2, ← pow_add, h3]

end Counting

section Reduction

variable {K : Type} [Field K] [CharP K 2] [Fintype K] {M : Type} [AddCommGroup M]
  [Module (ZMod 2) M] {π : antiSp K →* (M ≃ₗ[ZMod 2] M)} {A : Subgroup (M ≃ₗ[ZMod 2] M)}

omit [Fintype K] in
theorem offender_reduction_sq {f : ℕ} (hf : 2 ≤ f) [Finite M] (H : Offender π A) (hA1 : A ≠ ⊥)
    [Finite (Outer (antiSp K))] (hcyc : IsCyclic (Outer (antiSp K)))
    (h25 : ∀ z : antiSp K, z * z = 1 → z ≠ 1 → 6 * f ≤ dispRank (π z) ∧
      (rk0 z = 2 → rk1 z = 2 → 6 * f < dispRank (π z)))
    (hmax : ∀ E : Subgroup (antiSp K), (∀ x ∈ E, x * x = 1) → Nat.card E ≤ 2 ^ (3 * f) ∧
      (Nat.card E = 2 ^ (3 * f) → ∃ z ∈ E, rk0 z = 2 ∧ rk1 z = 2))
    (h24 : ∀ θ : MulAut (antiSp K), θ * θ = 1 → θ ∉ inner (antiSp K) →
      ∀ E : Subgroup (antiSp K), E ≤ fixedSubgroup θ → (∀ x ∈ E, x * x = 1) →
        Nat.card E ≤ 2 ^ (if Even f then 3 * (f / 2) else 2 * f))
    (h26 : ∀ a : A, normAut π H.inj A H.norm a ∉ inner (antiSp K) → 4 ≤ dispRank a.1) :
    Nat.card A ^ 2 * Nat.card {m : M // ∀ a ∈ A, a m = m} < Nat.card M := by
  classical
  have : Finite (M ≃ₗ[ZMod 2] M) :=
    Finite.of_injective (fun e : M ≃ₗ[ZMod 2] M => (e : M → M)) DFunLike.coe_injective
  have : Finite A := inferInstance
  set Ψ := outerHom π A H.inj H.norm with hΨ
  have hcardA := H.card_eq
  have hq := H.card_range_le_two hcyc
  set Ê : Subgroup (antiSp K) := A.comap π with hÊ
  have hÊsq : ∀ x ∈ Ê, x * x = 1 := fun x hx => by
    apply H.inj
    rw [map_mul, map_one]
    exact H.sq _ hx
  have hÊA : ∀ x ∈ Ê, π x ∈ A := fun x hx => hx
  have hpowle : ∀ {m n : ℕ}, m ≤ n → 2 ^ m ≤ 2 ^ n := fun h =>
    Nat.pow_le_pow_right (by norm_num) h
  by_cases hΨ1 : ∀ a : A, Ψ a = 1
  ·
    have hrange : Ψ.range = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨a, rfl⟩
      exact hΨ1 a
    have hAÊ : Nat.card A = Nat.card Ê := by
      rw [hcardA, hrange, Subgroup.card_bot, mul_one]
    have hÊne : Ê ≠ ⊥ := fun h =>
      hA1 (Subgroup.card_eq_one.mp (by rw [hAÊ, h, Subgroup.card_bot]))
    obtain ⟨⟨z, hzÊ⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hÊne
    have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
    obtain ⟨hmax1, hmax2⟩ := hmax Ê hÊsq
    rcases hmax1.lt_or_eq with hlt | heq
    · refine mul_card_fixed_lt A (π z) (hÊA z hzÊ) ?_
      calc Nat.card A ^ 2 = Nat.card Ê ^ 2 := by rw [hAÊ]
        _ < (2 ^ (3 * f)) ^ 2 := Nat.pow_lt_pow_left hlt (by norm_num)
        _ = 2 ^ (6 * f) := by rw [← pow_mul]; ring_nf
        _ ≤ 2 ^ dispRank (π z) := hpowle (h25 z (hÊsq z hzÊ) hz1').1
    · obtain ⟨z', hz'Ê, hr0, hr1⟩ := hmax2 heq
      have hz'1 : z' ≠ 1 := fun h => by
        rw [h, rk0_one] at hr0
        omega
      refine mul_card_fixed_lt A (π z') (hÊA z' hz'Ê) ?_
      calc Nat.card A ^ 2 = (2 ^ (3 * f)) ^ 2 := by rw [hAÊ, heq]
        _ = 2 ^ (6 * f) := by rw [← pow_mul]; ring_nf
        _ < 2 ^ dispRank (π z') :=
            Nat.pow_lt_pow_right (by norm_num) ((h25 z' (hÊsq z' hz'Ê) hz'1).2 hr0 hr1)
  · push Not at hΨ1
    obtain ⟨a₀, ha₀⟩ := hΨ1
    have hout : normAut π H.inj A H.norm a₀ ∉ inner (antiSp K) := fun h =>
      ha₀ (MonoidHom.mem_ker.mp ((mem_ker_outerHom H a₀).mpr h))
    have hθθ : normAut π H.inj A H.norm a₀ * normAut π H.inj A H.norm a₀ = 1 := by
      rw [← map_mul]
      have : a₀ * a₀ = 1 := Subtype.ext (H.sq a₀.1 a₀.2)
      rw [this, map_one]
    have hcard2 : Nat.card A ≤ 2 * Nat.card Ê := by
      calc Nat.card A = Nat.card Ê * Nat.card Ψ.range := hcardA
        _ ≤ Nat.card Ê * 2 := Nat.mul_le_mul_left _ hq
        _ = 2 * Nat.card Ê := mul_comm _ _
    by_cases hÊbot : Ê = ⊥
    · have h1 : Nat.card Ê = 1 := by rw [hÊbot, Subgroup.card_bot]
      refine mul_card_fixed_lt A a₀.1 a₀.2 ?_
      have h4 := h26 a₀ hout
      have h2 : Nat.card A ≤ 2 := by rw [h1] at hcard2; omega
      calc Nat.card A ^ 2 ≤ 2 ^ 2 := Nat.pow_le_pow_left h2 2
        _ < 2 ^ 4 := by norm_num
        _ ≤ 2 ^ dispRank a₀.1 := hpowle h4
    · obtain ⟨⟨z, hzÊ⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hÊbot
      have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
      have hfix : Ê ≤ fixedSubgroup (normAut π H.inj A H.norm a₀) := by
        intro x hx
        rw [mem_fixedSubgroup]
        apply H.inj
        rw [π_normAut]
        have := H.comm a₀.1 a₀.2 (π x) (hÊA x hx)
        calc a₀.1 * π x * a₀.1⁻¹ = (π x * a₀.1) * a₀.1⁻¹ := by rw [this]
          _ = π x := by group
      have h24' := h24 _ hθθ hout Ê hfix hÊsq
      set c := (if Even f then 3 * (f / 2) else 2 * f) with hc
      have hbd : 2 * (c + 1) < 6 * f := by
        rw [hc]
        split_ifs with hev
        · omega
        · omega
      refine mul_card_fixed_lt A (π z) (hÊA z hzÊ) ?_
      calc Nat.card A ^ 2 ≤ (2 * 2 ^ c) ^ 2 :=
            Nat.pow_le_pow_left (hcard2.trans (Nat.mul_le_mul_left _ h24')) 2
        _ = 2 ^ (2 * (c + 1)) := by rw [← pow_succ', ← pow_mul, mul_comm]
        _ < 2 ^ (6 * f) := Nat.pow_lt_pow_right (by norm_num) hbd
        _ ≤ 2 ^ dispRank (π z) := hpowle (h25 z (hÊsq z hzÊ) hz1').1

end Reduction

section Arith

theorem twelve_mul_add_two_pow_le {s : ℕ} (hs : 3 ≤ s) : 12 * s + 2 ^ s ≤ 4 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s hs ih =>
    have h2 : 2 ^ s ≤ 4 ^ s := Nat.pow_le_pow_left (by norm_num) s
    rw [pow_succ, pow_succ]
    omega

theorem two_mul_eq_of_shiftSet {f d : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.range (2 * f))
    (hcard : S.card = 2) (hshift : shiftSet f (2 * d) S = S) (hd0 : 0 < d) (hdf : d < f) :
    2 * d = f := by
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hcard
  have hi : i < 2 * f := Finset.mem_range.mp (hS (Finset.mem_insert_self i {j}))
  have hj : j < 2 * f := Finset.mem_range.mp (hS (Finset.mem_insert_of_mem
    (Finset.mem_singleton_self j)))
  have hmem : ∀ x ∈ ({i, j} : Finset ℕ), (x + 2 * d) % (2 * f) ∈ ({i, j} : Finset ℕ) := by
    intro x hx
    have : (x + 2 * d) % (2 * f) ∈ shiftSet f (2 * d) {i, j} := Finset.mem_image_of_mem _ hx
    rwa [hshift] at this
  have hmod : ∀ x, x < 2 * f → (x + 2 * d) % (2 * f) =
      if x + 2 * d < 2 * f then x + 2 * d else x + 2 * d - 2 * f := by
    intro x hx
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  have h1 := hmem i (Finset.mem_insert_self i {j})
  have h2 := hmem j (Finset.mem_insert_of_mem (Finset.mem_singleton_self j))
  rw [hmod i hi] at h1
  rw [hmod j hj] at h2
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  split_ifs at h1 h2 <;> omega

end Arith

section Disp

variable {F : Type} [Field F] [CharP F 2] [Fintype F]
variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]

theorem six_mul_le_dispRank {f : ℕ} (hf : 1 ≤ f)
    (π : antiSp F →* (M ≃ₗ[ZMod 2] M)) [Fact (repOf π).IsIrreducible] {d : ℕ} (hd1 : 1 ≤ d)
    (hDcard : Nat.card (EndRing (repOf π)) = 2 ^ d)
    {E : Type} [Field E] [Finite E] [CharP E 2] (ιF : F →+* E) (ιD : EndRing (repOf π) →+* E)
    (S : Finset ℕ) (hSne : S.Nonempty) (hS : S ⊆ Finset.range (2 * f))
    (Φ : (letI := ιF.toAlgebra
      (CFSG.QuasithinUnique.Setup.X7.matRep (tensorRepS (F := F) E S)).Equiv
        (matRepE (Module.finBasis (EndRing (repOf π)) M) ιD)))
    (hshift : shiftSet f (2 * d) S = S)
    (hdimW : Module.finrank (EndRing (repOf π)) M = 4 ^ S.card)
    (hlab : 3 ≤ S.card ∨ (S.card = 2 ∧ 2 * d ≠ f))
    {z : antiSp F} (hz : z * z = 1) (hz1 : z ≠ 1) :
    6 * f ≤ dispRank (π z) ∧ (rk0 z = 2 → rk1 z = 2 → 6 * f < dispRank (π z)) := by
  classical
  have : Module.Finite (EndRing (repOf π)) M := Module.Finite.of_finite
  let _ : Algebra F E := ιF.toAlgebra
  have hdisp : dispRank (π z) = d * (tensorRepS (F := F) E S z - 1).rank :=
    finrank_range_eq hDcard _ ιF ιD S Φ hdimW z
  have hfd : f ≤ S.card * d := by
    have h := n_le_card_mul (n := 2 * f) (d := 2 * d) (by omega) (by omega)
      (fun i hi => Finset.mem_range.mp (hS hi)) hSne hshift
    nlinarith
  have hge := rank_tensorRepS_sub_one_ge E S hz hz1
  have htwo : rk0 z = 2 → rk1 z = 2 → (tensorRepS (F := F) E S z - 1).rank = 4 ^ S.card / 2 := by
    intro h0 h1
    obtain ⟨i, hi⟩ := hSne
    have hr2 : (natRepS E i z - 1).rank = 2 := by
      rw [rank_natRepS_sub_one_eq]
      split_ifs <;> assumption
    exact rank_tensorRepS_sub_one_of_rank_two E S hz hi hr2
  rcases hlab with h3 | ⟨h2, hne⟩
  ·
    have hb := twelve_mul_add_two_pow_le h3
    have hle : 6 * S.card ≤ (4 ^ S.card - 2 ^ S.card) / 2 := by omega
    refine ⟨?_, fun h0 h1 => ?_⟩
    · rw [hdisp]
      calc 6 * f ≤ 6 * (S.card * d) := Nat.mul_le_mul_left 6 hfd
        _ = d * (6 * S.card) := by ring
        _ ≤ d * (tensorRepS (F := F) E S z - 1).rank := Nat.mul_le_mul_left d (hle.trans hge)
    · rw [hdisp, htwo h0 h1]
      have h2s : 2 ≤ 2 ^ S.card :=
        (pow_one 2).symm.le.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
      have hlt : 6 * S.card < 4 ^ S.card / 2 := by omega
      calc 6 * f ≤ 6 * (S.card * d) := Nat.mul_le_mul_left 6 hfd
        _ = d * (6 * S.card) := by ring
        _ < d * (4 ^ S.card / 2) := Nat.mul_lt_mul_of_pos_left hlt (by omega)
  ·
    have hdf : f ≤ d := by
      by_contra h
      exact hne (two_mul_eq_of_shiftSet hS h2 hshift (by omega) (by omega))
    rw [h2] at hge htwo
    norm_num at hge htwo
    refine ⟨?_, fun h0 h1 => ?_⟩
    · rw [hdisp]
      nlinarith
    · rw [hdisp, htwo h0 h1]
      nlinarith

end Disp

section Label

variable {F : Type} [Field F] [CharP F 2] [Fintype F]
variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]

theorem twoF_label {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card F = 2 ^ f) (π : antiSp F →* (M ≃ₗ[ZMod 2] M)) (hπ : Function.Injective π)
    [Fact (repOf π).IsIrreducible] (hdim : Module.finrank (EndRing (repOf π)) M ≠ 4)
    (A : Subgroup (M ≃ₗ[ZMod 2] M)) (hnorm : ∀ a ∈ A, ∀ x, ∃ y, a * π x * a⁻¹ = π y)
    (hAe : CFSG.IsElementaryAbelian 2 A) (hA1 : A ≠ ⊥)
    (hoff : Nat.card M ≤ Nat.card A ^ 2 * Nat.card {m : M // ∀ a ∈ A, a m = m}) :
    ∃ a : ℕ, f = 2 * a ∧ Nat.card (EndRing (repOf π)) = 2 ^ a ∧
      Module.finrank (EndRing (repOf π)) M = 16 := by
  classical
  have hKf : Fintype.card F = 2 ^ f := by rw [← Nat.card_eq_fintype_card]; exact hK
  have := hAe
  have hsq : ∀ a ∈ A, a * a = 1 := fun a ha => by
    have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) a ha
    rwa [_root_.sq] at this
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb' => by
    exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := A)).comm ⟨a, ha⟩ ⟨b, hb'⟩)
  have hπ'inj : Function.Injective (repOf π) := fun g g' hg =>
    hπ (LinearEquiv.toLinearMap_injective hg)
  have hπ'nt : ∃ g, repOf π g ≠ 1 :=
    ⟨invX F, fun h1 => invX_ne_one (hπ'inj (h1.trans (map_one (repOf π)).symm))⟩
  obtain ⟨hnontriv, hirr⟩ :=
    (CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff (repOf π)).mp Fact.out
  have hsum : SimpleSummandsStable π A := by
    obtain ⟨g, hg⟩ := hπ'nt
    obtain ⟨x, hx⟩ : ∃ x, repOf π g x ≠ x := by
      by_contra h
      push Not at h
      exact hg (LinearMap.ext fun x => by rw [h x]; rfl)
    refine ⟨Unit, fun _ => ⊤, iSupIndep_subsingleton _, iSup_const, fun _ =>
      ⟨top_ne_bot, ⟨x, Submodule.mem_top, g, hx⟩, fun _ _ _ => Submodule.mem_top,
        fun U _ hU => hirr U hU, fun _ _ _ _ => Submodule.mem_top⟩⟩
  have H : Offender π A := ⟨hπ, hnorm, hsq, hcomm, hsum⟩
  obtain ⟨-, hcyc, hcard, hN24⟩ :=
    even_symplectic_four_outer_involution_rank_and_perfect_residual hf hK
  have : Finite (Outer (antiSp F)) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  obtain ⟨d, hd1, hDcard, hdesc⟩ := sp4_descent hKf (by omega) hπ'nt
  have : Module.Finite (EndRing (repOf π)) M := Module.Finite.of_finite
  obtain ⟨E, _, _, _, ιF, ιD, S, hSne, hS, ⟨Φ⟩, hshift, hdimW⟩ :=
    hdesc (Module.finBasis (EndRing (repOf π)) M)
  have hs2 : 2 ≤ S.card := by
    have hs1 : 1 ≤ S.card := Finset.card_pos.mpr hSne
    by_contra h
    have h1 : S.card = 1 := by omega
    rw [h1, pow_one] at hdimW
    exact hdim hdimW
  by_cases hlab : S.card = 2 ∧ 2 * d = f
  · refine ⟨d, hlab.2.symm, hDcard, ?_⟩
    rw [hdimW, hlab.1]
    norm_num
  · exfalso
    have hlab' : 3 ≤ S.card ∨ (S.card = 2 ∧ 2 * d ≠ f) := by
      by_cases h3 : S.card = 2
      · exact Or.inr ⟨h3, fun h => hlab ⟨h3, h⟩⟩
      · exact Or.inl (by omega)
    have h25 : ∀ z : antiSp F, z * z = 1 → z ≠ 1 → 6 * f ≤ dispRank (π z) ∧
        (rk0 z = 2 → rk1 z = 2 → 6 * f < dispRank (π z)) := fun z hz hz1 =>
      six_mul_le_dispRank (by omega) π hd1 hDcard ιF ιD S hSne hS Φ hshift hdimW hlab' hz hz1
    have hmax := (involution_rank_pairs_and_maximal_elementary_witness hK).2.2
    have h24 : ∀ θ : MulAut (antiSp F), θ * θ = 1 → θ ∉ inner (antiSp F) →
        ∀ E : Subgroup (antiSp F), E ≤ fixedSubgroup θ → (∀ x ∈ E, x * x = 1) →
          Nat.card E ≤ 2 ^ (if Even f then 3 * (f / 2) else 2 * f) :=
      fun θ hθ hθinn E hE hEsq => (hN24 θ hθ hθinn).2.1 E hE hEsq
    have h26 : ∀ a : A, normAut π H.inj A H.norm a ∉ inner (antiSp F) → 4 ≤ dispRank a.1 := by
      intro a ha
      have ha1 : a.1 ≠ 1 := fun h1 => ha (by
        have : a = 1 := Subtype.ext h1
        rw [this, map_one]
        exact one_mem _)
      have hord : orderOf a.1 = 2 :=
        orderOf_eq_prime (by rw [_root_.sq]; exact hsq a.1 a.2) ha1
      exact outer_involutions_have_binary_displacement_at_least_four hf hKf (repOf π) hπ'inj a.1
        hord (normAut π H.inj A H.norm a) ha (fun g w => by
          have := π_normAut π H.inj A H.norm a g
          have h2 := congrArg (fun e : M ≃ₗ[ZMod 2] M => e w) this
          exact h2.symm)
    have hlt := offender_reduction_sq hf H hA1 hcyc h25 hmax h24 h26
    omega

end Label

end CFSG.Quasithin.B45Sp4

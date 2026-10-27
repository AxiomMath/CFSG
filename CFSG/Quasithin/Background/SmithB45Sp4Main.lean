module

public import CFSG.Quasithin.Background.RAVBounds
public import CFSG.Quasithin.Background.SmithB45Sp4Red
public import CFSG.Quasithin.Background.SmithB45Sp4Ident
public import CFSG.Quasithin.Background.SmithB45Sp4Up
public import CFSG.Quasithin.Background.SmithB45Families
public import CFSG.Quasithin.Background.SmithB42Sp4Main
public import CFSG.Quasithin.Background.D2Misc

public section

namespace CFSG.Quasithin.B45Sp4

open CFSG.QuasithinUnique.Setup.X7b CFSG.QuasithinUnique.Setup.SL2Modules
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.Quasithin.B42Sp4 CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour (radical card_radical)
open CFSG.QuasithinUnique.Setup.Layer (binPsi)

section Counting

theorem mul_card_fixed_le {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    (A : Subgroup (M ≃ₗ[ZMod 2] M)) (t : M ≃ₗ[ZMod 2] M) (ht : t ∈ A) {N : ℕ}
    (hN : N ≤ 2 ^ dispRank t) :
    N * Nat.card {m : M // ∀ a ∈ A, a m = m} ≤ Nat.card M := by
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
  calc N * Nat.card {m : M // ∀ a ∈ A, a m = m}
      ≤ N * Nat.card (LinearMap.ker D) := Nat.mul_le_mul_left _ hC
    _ ≤ 2 ^ Module.finrank (ZMod 2) (LinearMap.range D) * Nat.card (LinearMap.ker D) :=
        Nat.mul_le_mul_right _ hN
    _ = Nat.card M := by rw [h1, h2, ← pow_add, h3]

end Counting

section WBounds

variable {K : Type} [Field K] [CharP K 2] [Fintype K]
variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

@[expose] noncomputable def gam (K : Type) [Field K] [CharP K 2] [Fintype K] (j : ℕ) :
    antiSp K ≃* StatedSp 2 K :=
  (minorAut K ^ j).trans (antiSpEquiv K)

omit [Finite W] in
theorem card_fix_inner {a : ℕ} (π : antiSp K →* (W ≃ₗ[ZMod 2] W)) (j : ℕ)
    (φ : W ≃+ ↥(hermA a (Fin 2 ⊕ Fin 2) K))
    (hφ : ∀ g w, (φ (π g w) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      tw a (spMat (antiSpEquiv K ((minorAut K ^ j) g))) (φ w))
    (Ê : Subgroup (antiSp K)) :
    Nat.card {m : W // ∀ x ∈ Ê, π x m = m} =
      Nat.card ↥(hermFix a _ K (spM '' ((Ê.map (gam K j).toMonoidHom : Subgroup _) :
        Set (StatedSp 2 K)))) := by
  refine Nat.card_congr
    { toFun := fun m => ⟨(φ m.1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K), ?_⟩
      invFun := fun Y => ⟨φ.symm ⟨Y.1, (mem_hermFix.mp Y.2).1⟩, ?_⟩
      left_inv := fun m => by
        apply Subtype.ext
        simp
      right_inv := fun Y => by
        apply Subtype.ext
        simp }
  · refine mem_hermFix.mpr ⟨(φ m.1).2, ?_⟩
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have := hφ x m.1
    rw [m.2 x hx] at this
    exact this.symm
  · intro x hx
    apply φ.injective
    apply Subtype.ext
    rw [hφ, AddEquiv.apply_symm_apply]
    exact (mem_hermFix.mp Y.2).2 _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩

theorem w_bounds {a : ℕ} (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a)) (π : antiSp K →* (W ≃ₗ[ZMod 2] W))
    (hπ : Function.Injective π) [Fact (repOf π).IsIrreducible]
    (hdim : Module.finrank (EndRing (repOf π)) W ≠ 4) (j : ℕ)
    (φ : W ≃+ ↥(hermA a (Fin 2 ⊕ Fin 2) K))
    (hφ : ∀ g w, (φ (π g w) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      tw a (spMat (antiSpEquiv K ((minorAut K ^ j) g))) (φ w))
    (A : Subgroup (W ≃ₗ[ZMod 2] W)) (hnorm : ∀ c ∈ A, ∀ x, ∃ y, c * π x * c⁻¹ = π y)
    (hAe : CFSG.IsElementaryAbelian 2 A) (hA1 : A ≠ ⊥) :
    Nat.card A ^ 2 * Nat.card {m : W // ∀ c ∈ A, c m = m} ≤ Nat.card W ∧
      ((∀ c ∈ A, ∀ d ∈ A, ∀ w, d (c w - w) = c w - w) →
        Nat.card A ^ 2 * Nat.card {m : W // ∀ c ∈ A, c m = m} < Nat.card W) := by
  classical
  have hKf : Fintype.card K = 2 ^ (2 * a) := by rw [← Nat.card_eq_fintype_card]; exact hK
  have hf2 : 2 ≤ 2 * a := by omega
  have := hAe
  have hsq : ∀ c ∈ A, c * c = 1 := fun c hc => by
    have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) c hc
    rwa [_root_.sq] at this
  have hcomm : ∀ c ∈ A, ∀ d ∈ A, c * d = d * c := fun c hc d hd => by
    exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := A)).comm ⟨c, hc⟩ ⟨d, hd⟩)
  have hπ'inj : Function.Injective (repOf π) := fun g g' hg =>
    hπ (LinearEquiv.toLinearMap_injective hg)
  have hπ'nt : ∃ g, repOf π g ≠ 1 :=
    ⟨invX K, fun h1 => invX_ne_one (hπ'inj (h1.trans (map_one (repOf π)).symm))⟩
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
    even_symplectic_four_outer_involution_rank_and_perfect_residual hf2 hK
  have : Finite (Outer (antiSp K)) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have : Finite (W ≃ₗ[ZMod 2] W) :=
    Finite.of_injective (fun e : W ≃ₗ[ZMod 2] W => (e : W → W)) DFunLike.coe_injective
  set q := Nat.card K with hq
  have hcardW : Nat.card W = q ^ 8 := by
    rw [Nat.card_congr φ.toEquiv, card_hermA_eq ha hK]
  have hq4 : q ^ 4 = 2 ^ (8 * a) := by rw [hK, ← pow_mul]; ring_nf
  set Ψ := outerHom π A H.inj H.norm with hΨ
  have hcardA := H.card_eq
  have hq2 := H.card_range_le_two hcyc
  set Ê : Subgroup (antiSp K) := A.comap π with hÊ
  have hÊsq : ∀ x ∈ Ê, x * x = 1 := fun x hx => by
    apply H.inj
    rw [map_mul, map_one]
    exact H.sq _ hx
  have hÊA : ∀ x ∈ Ê, π x ∈ A := fun x hx => hx
  set E' : Subgroup (StatedSp 2 K) := Ê.map (gam K j).toMonoidHom with hE'
  have hE'sq : ∀ y ∈ E', y * y = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, hÊsq x hx, map_one]
  have hcardE' : Nat.card E' = Nat.card Ê :=
    Subgroup.card_map_of_injective (gam K j).injective
  have hfix := card_fix_inner π j φ hφ Ê
  rw [← hE'] at hfix
  obtain ⟨hM1, hM2⟩ := card_bounds ha hK E' hE'sq
  rw [hcardE', ← hfix] at hM1 hM2
  have hCle : Nat.card {m : W // ∀ c ∈ A, c m = m} ≤ Nat.card {m : W // ∀ x ∈ Ê, π x m = m} :=
    Nat.card_le_card_of_injective (fun m => ⟨m.1, fun x hx => m.2 _ (hÊA x hx)⟩)
      (fun m m' h => Subtype.ext (by simpa using congrArg Subtype.val h))
  have hquad : (∀ c ∈ A, ∀ d ∈ A, ∀ w, d (c w - w) = c w - w) → Nat.card Ê ≤ 2 ^ a := by
    intro hQ
    rw [← hcardE']
    refine card_le_of_quadratic ha hK E' hE'sq ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ Y hY
    set w := φ.symm ⟨Y, hY⟩ with hw
    have hYw : Y = (φ w : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
      rw [hw, AddEquiv.apply_symm_apply]
    have e1' : ∀ g v, tw a (spM (gam K j g)) (φ v : Matrix (Fin 2 ⊕ Fin 2) _ K) =
        (φ (π g v) : Matrix (Fin 2 ⊕ Fin 2) _ K) := fun g v => (hφ g v).symm
    have e2 : tw a (spM (gam K j x)) Y - Y = (φ (π x w - w) : Matrix (Fin 2 ⊕ Fin 2) _ K) := by
      rw [hYw, e1', map_sub, AddSubgroup.coe_sub]
    show tw a (spM (gam K j y)) (tw a (spM (gam K j x)) Y - Y) = tw a (spM (gam K j x)) Y - Y
    rw [e2, e1', hQ _ (hÊA x hx) _ (hÊA y hy) w]
  have h25 : ∀ z : antiSp K, z * z = 1 → z ≠ 1 → 6 * a ≤ dispRank (π z) := by
    intro z hz hz1
    have := (displacement_ge hKf (by omega) π hπ'nt hdim hz hz1).1
    omega
  have hpowle : ∀ {m n : ℕ}, m ≤ n → 2 ^ m ≤ 2 ^ n := fun h =>
    Nat.pow_le_pow_right (by norm_num) h
  by_cases hΨ1 : ∀ c : A, Ψ c = 1
  ·
    have hrange : Ψ.range = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨c, rfl⟩
      exact hΨ1 c
    have hAÊ : Nat.card A = Nat.card Ê := by
      rw [hcardA, hrange, Subgroup.card_bot, mul_one]
    have hinner : ∀ c ∈ A, ∃ x ∈ Ê, π x = c := by
      intro c hc
      obtain ⟨x, hx⟩ := (H.normAut_mem_inner_iff ⟨c, hc⟩).mp
        ((mem_ker_outerHom H _).mp (MonoidHom.mem_ker.mpr (hΨ1 ⟨c, hc⟩)))
      exact ⟨x, show π x ∈ A by rw [hx]; exact hc, hx⟩
    have hCeq : Nat.card {m : W // ∀ c ∈ A, c m = m} =
        Nat.card {m : W // ∀ x ∈ Ê, π x m = m} := by
      refine Nat.card_congr (Equiv.subtypeEquivRight fun m => ⟨fun h x hx => h _ (hÊA x hx),
        fun h c hc => ?_⟩)
      obtain ⟨x, hx, rfl⟩ := hinner c hc
      exact h x hx
    refine ⟨?_, fun hQ => ?_⟩
    · rw [hAÊ, hCeq, hcardW]
      exact hM1
    · have hÊne : Ê ≠ ⊥ := fun h =>
        hA1 (Subgroup.card_eq_one.mp (by rw [hAÊ, h, Subgroup.card_bot]))
      obtain ⟨⟨z, hzÊ⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hÊne
      have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
      refine mul_card_fixed_lt A (π z) (hÊA z hzÊ) ?_
      calc Nat.card A ^ 2 = Nat.card Ê ^ 2 := by rw [hAÊ]
        _ ≤ (2 ^ a) ^ 2 := Nat.pow_le_pow_left (hquad hQ) 2
        _ = 2 ^ (2 * a) := by rw [← pow_mul, mul_comm]
        _ < 2 ^ (6 * a) := Nat.pow_lt_pow_right (by norm_num) (by omega)
        _ ≤ 2 ^ dispRank (π z) := hpowle (h25 z (hÊsq z hzÊ) hz1')
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
        _ ≤ Nat.card Ê * 2 := Nat.mul_le_mul_left _ hq2
        _ = 2 * Nat.card Ê := mul_comm _ _
    by_cases hÊbot : Ê = ⊥
    ·
      have h1 : Nat.card Ê = 1 := by rw [hÊbot, Subgroup.card_bot]
      have ha₀1 : a₀.1 ≠ 1 := fun h1' => hout (by
        have : a₀ = 1 := Subtype.ext h1'
        rw [this, map_one]
        exact one_mem _)
      have hord : orderOf a₀.1 = 2 :=
        orderOf_eq_prime (by rw [_root_.sq]; exact H.sq a₀.1 a₀.2) ha₀1
      have h4 : 4 ≤ dispRank a₀.1 :=
        outer_involutions_have_binary_displacement_at_least_four hf2 hKf (repOf π) hπ'inj a₀.1
          hord (normAut π H.inj A H.norm a₀) hout (fun g w => by
            have := π_normAut π H.inj A H.norm a₀ g
            have h2 := congrArg (fun e : W ≃ₗ[ZMod 2] W => e w) this
            exact h2.symm)
      have hlt : Nat.card A ^ 2 < 2 ^ dispRank a₀.1 := by
        have h2 : Nat.card A ≤ 2 := by rw [h1] at hcard2; omega
        calc Nat.card A ^ 2 ≤ 2 ^ 2 := Nat.pow_le_pow_left h2 2
          _ < 2 ^ 4 := by norm_num
          _ ≤ 2 ^ dispRank a₀.1 := hpowle h4
      have hstrict := mul_card_fixed_lt A a₀.1 a₀.2 hlt
      exact ⟨hstrict.le, fun _ => hstrict⟩
    · obtain ⟨⟨z, hzÊ⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hÊbot
      have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
      have hfixθ : Ê ≤ fixedSubgroup (normAut π H.inj A H.norm a₀) := by
        intro x hx
        rw [mem_fixedSubgroup]
        apply H.inj
        rw [π_normAut]
        have := H.comm a₀.1 a₀.2 (π x) (hÊA x hx)
        calc a₀.1 * π x * a₀.1⁻¹ = (π x * a₀.1) * a₀.1⁻¹ := by rw [this]
          _ = π x := by group
      have h24 := (hN24 _ hθθ hout).2.1 Ê hfixθ hÊsq
      have hev : Even (2 * a) := even_two_mul a
      simp only [hev, ite_true, show 2 * a / 2 = a by omega] at h24
      have hdz := h25 z (hÊsq z hzÊ) hz1'
      refine ⟨?_, fun hQ => ?_⟩
      · by_cases hsmall : Nat.card Ê ≤ q
        ·
          refine mul_card_fixed_le A (π z) (hÊA z hzÊ) ?_
          calc Nat.card A ^ 2 ≤ (2 * q) ^ 2 :=
                Nat.pow_le_pow_left (hcard2.trans (Nat.mul_le_mul_left 2 hsmall)) 2
            _ = 2 ^ (4 * a + 2) := by rw [hK, mul_pow, ← pow_mul]; ring
            _ ≤ 2 ^ dispRank (π z) := hpowle (by omega)
        ·
          push Not at hsmall
          have hM := hM2 hsmall
          have hA2 : Nat.card A ^ 2 ≤ q ^ 4 := by
            calc Nat.card A ^ 2 ≤ (2 * 2 ^ (3 * a)) ^ 2 :=
                  Nat.pow_le_pow_left (hcard2.trans (Nat.mul_le_mul_left 2 h24)) 2
              _ = 2 ^ (6 * a + 2) := by rw [mul_pow, ← pow_mul]; ring
              _ ≤ 2 ^ (8 * a) := hpowle (by omega)
              _ = q ^ 4 := hq4.symm
          rw [hcardW]
          calc Nat.card A ^ 2 * Nat.card {m : W // ∀ c ∈ A, c m = m}
              ≤ q ^ 4 * Nat.card {m : W // ∀ x ∈ Ê, π x m = m} := Nat.mul_le_mul hA2 hCle
            _ ≤ q ^ 8 := hM
      ·
        refine mul_card_fixed_lt A (π z) (hÊA z hzÊ) ?_
        calc Nat.card A ^ 2 ≤ (2 * 2 ^ a) ^ 2 :=
              Nat.pow_le_pow_left (hcard2.trans (Nat.mul_le_mul_left 2 (hquad hQ))) 2
          _ = 2 ^ (2 * a + 2) := by rw [mul_pow, ← pow_mul]; ring
          _ < 2 ^ (6 * a) := Nat.pow_lt_pow_right (by norm_num) (by omega)
          _ ≤ 2 ^ dispRank (π z) := hpowle hdz

end WBounds

section Transfer

variable {V : Type} [CommGroup V] [Finite V]

theorem two_le_rAV_iff (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)} (hA : IsA2 X A) :
    (2 : ℚ) ≤ rAV A ↔ Nat.card A ^ 2 * Nat.card ↥(fixV A) ≤ Nat.card V :=
  CFSG.Quasithin.RAV.two_le_rAV_iff hV hA

theorem two_lt_rAV_iff (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)} (hA : IsA2 X A) :
    (2 : ℚ) < rAV A ↔ Nat.card A ^ 2 * Nat.card ↥(fixV A) < Nat.card V :=
  CFSG.Quasithin.RAV.two_lt_rAV_iff hV hA

theorem rAV_le_two_iff' (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)} (hA : IsA2 X A) :
    rAV A ≤ 2 ↔ Nat.card V ≤ Nat.card A ^ 2 * Nat.card ↥(fixV A) := by
  rw [← not_lt, two_lt_rAV_iff hV hA, not_lt]

@[expose] def cm (g : MulAut V) (v : V) : V := g v * v⁻¹

omit [Finite V] in
theorem cm_mul (g : MulAut V) (v w : V) : cm g (v * w) = cm g v * cm g w := by
  simp only [cm, map_mul]
  rw [mul_inv]
  ac_rfl

omit [Finite V] in
theorem cm_one (g : MulAut V) : cm g 1 = 1 := by simp [cm]

omit [Finite V] in
theorem cm_inv (g : MulAut V) (v : V) : cm g v⁻¹ = (cm g v)⁻¹ := by
  simp only [cm, map_inv, inv_inv, mul_inv]

omit [Finite V] in
theorem commSeries_three_eq_bot_of {X : Subgroup (MulAut V)}
    (h : ∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X, ∀ v : V, cm z (cm y (cm x v)) = 1) :
    commSeries X 3 = ⊥ := by
  let S₂ : Subgroup V :=
    { carrier := {v | ∀ z ∈ X, cm z v = 1}
      mul_mem' := fun {v w} hv hw z hz => by rw [cm_mul, hv z hz, hw z hz, one_mul]
      one_mem' := fun z _ => cm_one z
      inv_mem' := fun {v} hv z hz => by rw [cm_inv, hv z hz, inv_one] }
  let S₁ : Subgroup V :=
    { carrier := {v | ∀ y ∈ X, cm y v ∈ S₂}
      mul_mem' := fun {v w} hv hw y hy => by rw [cm_mul]; exact S₂.mul_mem (hv y hy) (hw y hy)
      one_mem' := fun y _ => by rw [cm_one]; exact S₂.one_mem
      inv_mem' := fun {v} hv y hy => by rw [cm_inv]; exact S₂.inv_mem (hv y hy) }
  have hcs : ∀ (U S : Subgroup V), (∀ x ∈ X, ∀ u ∈ U, cm x u ∈ S) → commSub U X ≤ S := by
    intro U S hUS
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, u, hu, rfl⟩
    exact hUS x hx u hu
  have h1 : commSeries X 1 ≤ S₁ :=
    hcs ⊤ S₁ fun x hx v _ y hy z hz => h x hx y hy z hz v
  have h2 : commSeries X 2 ≤ S₂ := hcs _ S₂ fun y hy u hu => h1 hu y hy
  have h3 : commSeries X 3 ≤ ⊥ := hcs _ ⊥ fun z hz u hu => by
    rw [Subgroup.mem_bot]
    exact h2 hu z hz
  exact le_bot_iff.mp h3

end Transfer

section Realize

variable {V : Type} [CommGroup V] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
variable {K : Type} [Field K] [CharP K 2] [Finite K]

theorem twistedTensorSp4_of {a : ℕ} (hK : Nat.card K = 2 ^ (2 * a)) (θ : V ≃* Multiplicative W)
    (L : Subgroup (MulAut V)) (δ : ↥L ≃* StatedSp 2 K) (φ : W ≃+ ↥(hermA a (Fin 2 ⊕ Fin 2) K))
    (hφ : ∀ (l : ↥L) (w : W), (φ (binPsi θ (l : MulAut V) w)).1 = tw a (spMat (δ l)) (φ w).1) :
    TwistedTensorSp4 L ⊤ ⊥ a := by
  classical
  refine ⟨K, inferInstance, inferInstance, inferInstance, hK, δ.symm.toMonoidHom, ?_⟩
  let e : V → ↥(hermSub a (Fin 2 ⊕ Fin 2) K) := fun v =>
    ⟨Multiplicative.ofAdd (φ (Multiplicative.toAdd (θ v))).1, (φ (Multiplicative.toAdd (θ v))).2⟩
  have he_mul : ∀ v w, e (v * w) = e v * e w := by
    intro v w
    apply Subtype.ext
    simp [e]
  have he_one : e 1 = 1 := by
    apply Subtype.ext
    simp [e]
  have he_inj : ∀ v, e v = 1 → v = 1 := by
    intro v hv
    have h0 := congrArg Subtype.val hv
    have h1 : (φ (Multiplicative.toAdd (θ v))).1 = 0 := by
      simpa [e] using congrArg Multiplicative.toAdd h0
    have h2 : φ (Multiplicative.toAdd (θ v)) = 0 := Subtype.ext h1
    rw [AddEquiv.map_eq_zero_iff] at h2
    have h3 : θ v = 1 := Multiplicative.toAdd.injective h2
    simpa using congrArg θ.symm h3
  have he_surj : ∀ m : ↥(hermSub a (Fin 2 ⊕ Fin 2) K), ∃ v, e v = m := by
    intro m
    refine ⟨θ.symm (Multiplicative.ofAdd (φ.symm ⟨Multiplicative.toAdd
      (m : Multiplicative (Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)), m.2⟩)), ?_⟩
    apply Subtype.ext
    simp [e]
  have he_act : ∀ (γ : StatedSp 2 K) (v : V),
      e (((δ.symm γ : ↥L) : MulAut V) v) = ⟨twistAct a (StatedSp 2 K) γ (e v),
        twistAct_mem_hermSub a _ hK γ (e v).2⟩ := by
    intro γ v
    apply Subtype.ext
    show Multiplicative.ofAdd (φ (Multiplicative.toAdd (θ (((δ.symm γ : ↥L) : MulAut V) v)))).1
      = _
    rw [← B42L2.toAdd_binPsi, hφ, MulEquiv.apply_symm_apply]
    rfl
  let β : ↥(⊤ : Subgroup V) →* ↥(hermSub a (Fin 2 ⊕ Fin 2) K) ⧸
      ((⊥ : Subgroup (Multiplicative (Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))).subgroupOf
        (hermSub a (Fin 2 ⊕ Fin 2) K)) :=
    { toFun := fun u => QuotientGroup.mk (e u)
      map_one' := by
        show QuotientGroup.mk (e 1) = 1
        rw [he_one]
        rfl
      map_mul' := fun u u' => by
        show QuotientGroup.mk (e ((u : V) * u')) = _
        rw [he_mul]
        rfl }
  have hmk : ∀ x y : ↥(hermSub a (Fin 2 ⊕ Fin 2) K),
      (QuotientGroup.mk x : ↥(hermSub a (Fin 2 ⊕ Fin 2) K) ⧸
        ((⊥ : Subgroup (Multiplicative (Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))).subgroupOf
          (hermSub a (Fin 2 ⊕ Fin 2) K))) = QuotientGroup.mk y ↔ x = y := by
    intro x y
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.mem_bot, Subgroup.coe_mul,
      Subgroup.coe_inv, inv_mul_eq_one]
    exact Subtype.ext_iff.symm
  refine ⟨δ.symm.surjective, bot_le, bot_le, fun _ _ _ => trivial, fun h z hz => ?_,
    fun γ m hm => twistAct_mem_hermSub a _ hK γ hm, fun γ m hm => ?_, β, ?_, fun u => ?_, ?_⟩
  · rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · have hm' : m = 1 := hm
    show twistAct a (StatedSp 2 K) γ m ∈ (⊥ : Subgroup _)
    rw [Subgroup.mem_bot, hm']
    exact act_map_one (twistAct a (StatedSp 2 K)) γ (twistAct_mul a _ γ)
  · intro q
    induction q using QuotientGroup.induction_on with
    | H m =>
      obtain ⟨v, hv⟩ := he_surj m
      exact ⟨⟨v, trivial⟩, by
        show QuotientGroup.mk (e v) = _
        rw [hv]
        rfl⟩
  · show (QuotientGroup.mk (e u) : ↥(hermSub a (Fin 2 ⊕ Fin 2) K) ⧸
        ((⊥ : Subgroup (Multiplicative (Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))).subgroupOf
          (hermSub a (Fin 2 ⊕ Fin 2) K))) = 1 ↔ (u : V) ∈ ⊥
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_bot, Subgroup.mem_bot]
    constructor
    · intro h
      exact he_inj u (Subtype.ext h)
    · intro h
      rw [h, he_one]
      rfl
  · intro γ u m hu hm hum
    have hum' : e u = m := (hmk _ _).mp hum
    show (QuotientGroup.mk (e (((δ.symm γ : ↥L) : MulAut V) (u : V))) :
        ↥(hermSub a (Fin 2 ⊕ Fin 2) K) ⧸
          ((⊥ : Subgroup (Multiplicative (Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))).subgroupOf
            (hermSub a (Fin 2 ⊕ Fin 2) K))) =
      QuotientGroup.mk (⟨twistAct a (StatedSp 2 K) γ m.1, hm⟩ : ↥(hermSub a (Fin 2 ⊕ Fin 2) K))
    rw [hmk]
    refine (he_act γ (u : V)).trans ?_
    apply Subtype.ext
    show twistAct a (StatedSp 2 K) γ (e u).1 = twistAct a (StatedSp 2 K) γ m.1
    rw [hum']

end Realize

section Main

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique.Setup.Layer.Actor

variable {V : Type} [CommGroup V] [Finite V]

theorem part3_of_sp4 (hV : ∀ v : V, v ^ 2 = 1)
    {G L : Subgroup (MulAut V)} (hHyp : B4Hyp G L) (hP : B42TypeSp4Even ↥L)
    (hq1 : ((1 : ℚ) : WithTop ℚ) < qhatOf G) (hq2 : qhatOf G ≤ ((2 : ℚ) : WithTop ℚ)) :
    AsB45Part3 G L := by
  classical
  obtain ⟨hZ, f, hf2, hmodel⟩ := hP
  obtain ⟨K, _, _, _, hK, ⟨θL⟩⟩ := exists_antiSp_equiv hZ hmodel
  have hKf : Fintype.card K = 2 ^ f := by rw [← Nat.card_eq_fintype_card]; exact hK
  have hV' : ∀ v : V, v * v = 1 := fun v => by rw [← pow_two]; exact hV v
  obtain ⟨W, _, _, _, ⟨θ⟩⟩ := exists_binModel_of_binary hV'
  set ψ := binPsi θ with hψ
  let πW : antiSp K →* (W ≃ₗ[ZMod 2] W) :=
    ψ.toMonoidHom.comp (L.subtype.comp θL.symm.toMonoidHom)
  have hπW : ∀ g, πW g = ψ ((θL.symm g : ↥L) : MulAut V) := fun g => rfl
  have hπinj : Function.Injective πW := fun g g' h => by
    have h1 := ψ.injective h
    exact θL.symm.injective (Subtype.ext h1)
  have hirrV := Bridge.TypeList.irr_of_isIrrSec hHyp.2.2.2
  have hirr : ∀ U : Submodule (ZMod 2) W, (∀ g, ∀ u ∈ U, πW g u ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    refine B42L2.irr_map θ hirrV U fun x hx u hu => ?_
    obtain ⟨l, hl, rfl⟩ := hx
    have h1 := hU (θL ⟨l, hl⟩) u hu
    rwa [hπW, MulEquiv.symm_apply_apply] at h1
  have hntW : Nontrivial W := by
    obtain ⟨v, -, hv⟩ := IsConcreteLE.exists_of_lt hHyp.2.2.2.1
    replace hv : v ≠ 1 := fun h => hv (h ▸ Subgroup.one_mem _)
    refine ⟨⟨Multiplicative.toAdd (θ v), 0, fun h => hv ?_⟩⟩
    have h1 : θ v = 1 := Multiplicative.toAdd.injective (by simpa using h)
    simpa using congrArg θ.symm h1
  have : Fact (repOf πW).IsIrreducible :=
    ⟨(CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff (repOf πW)).mpr ⟨hntW, hirr⟩⟩
  have hπ'inj : Function.Injective (repOf πW) := fun g g' hg =>
    hπinj (LinearEquiv.toLinearMap_injective hg)
  have hπ'nt : ∃ g, repOf πW g ≠ 1 :=
    ⟨invX K, fun h1 => invX_ne_one (hπ'inj (h1.trans (map_one (repOf πW)).symm))⟩
  have hGN : G ≤ Subgroup.normalizer (L : Set (MulAut V)) := B42L2.le_normalizer_of_b4Hyp hHyp
  have hLG : L ≤ G := (FFC.b4hyp_data hHyp).1
  have hnormMap : ∀ B ≤ G, ∀ c ∈ B.map ψ.toMonoidHom, ∀ x, ∃ y, c * πW x * c⁻¹ = πW y := by
    rintro B hBG _ ⟨b, hb, rfl⟩ x
    have hl : b * ((θL.symm x : ↥L) : MulAut V) * b⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hGN (hBG hb)) _).mp (θL.symm x).2
    refine ⟨θL ⟨_, hl⟩, ?_⟩
    rw [hπW (θL _), MulEquiv.symm_apply_apply, hπW x]
    change ψ b * ψ ((θL.symm x : ↥L) : MulAut V) * (ψ b)⁻¹ =
      ψ (b * ((θL.symm x : ↥L) : MulAut V) * b⁻¹)
    rw [map_mul, map_mul, map_inv]
  have hcardMap : ∀ B : Subgroup (MulAut V), Nat.card ↥(B.map ψ.toMonoidHom) = Nat.card B :=
    fun B => Subgroup.card_map_of_injective ψ.injective
  have hfixMap : ∀ B : Subgroup (MulAut V),
      Nat.card {m : W // ∀ c ∈ B.map ψ.toMonoidHom, c m = m} = Nat.card ↥(fixV B) :=
    fun B => natCard_fixGL_map θ B
  have hcardVW : Nat.card V = Nat.card W := natCard_eq θ
  obtain ⟨A, hA2, -, hAr⟩ := kq_le_iff.mp hq2
  have hoffV := (rAV_le_two_iff' hV hA2).mp hAr
  have hA₀e := (isElemAbelian2_iff_map θ A).1 hA2.isElemAbelian2
  have hA₀1 : A.map ψ.toMonoidHom ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective A ψ.injective]
    exact hA2.ne_bot
  have hoff : Nat.card W ≤ Nat.card ↥(A.map ψ.toMonoidHom) ^ 2 *
      Nat.card {m : W // ∀ c ∈ A.map ψ.toMonoidHom, c m = m} := by
    rw [hcardMap, hfixMap, ← hcardVW]
    exact hoffV
  by_cases hdim : Module.finrank (EndRing (repOf πW)) W = 4
  ·
    exfalso
    obtain ⟨i, φ, hφ⟩ := exists_natural_of_four hKf (by omega) πW hπ'nt hdim
    obtain ⟨K', _, _, hK', hreal⟩ := binaryNaturalSp4_of_coords θ hK θL i φ hφ
    obtain ⟨-, hlow, R, hR, hrR⟩ := natural_facts hV hHyp hf2 hK' hreal
    have hq := qOf_eq_of_offenders hV (by norm_num) hlow ⟨R, hR, hrR.le⟩
    have h1 := hq1.trans_le ((qhatOf_le_qOf G).trans hq.le)
    have h2 : (1 : ℚ) < 2 / 3 := WithTop.coe_lt_coe.mp h1
    norm_num at h2
  obtain ⟨a, hfa, hD, hdim16⟩ :=
    twoF_label hf2 hK πW hπinj hdim _ (hnormMap A hA2.le) hA₀e hA₀1 hoff
  have ha : 1 ≤ a := by omega
  have hK2 : Nat.card K = 2 ^ (2 * a) := by rw [hK, hfa]
  have hKf2 : Fintype.card K = 2 ^ (2 * a) := by rw [hKf, hfa]
  obtain ⟨j, φ, hφ⟩ := exists_hermA_equiv ha hKf2 πW hπ'nt hD hdim16
  have hbd : ∀ B, IsA2 G B → Nat.card B ^ 2 * Nat.card ↥(fixV B) ≤ Nat.card V ∧
      (IsQuadratic B → Nat.card B ^ 2 * Nat.card ↥(fixV B) < Nat.card V) := by
    intro B hB
    have hBe := (isElemAbelian2_iff_map θ B).1 hB.isElemAbelian2
    have hB1 : B.map ψ.toMonoidHom ≠ ⊥ := by
      rw [Ne, Subgroup.map_eq_bot_iff_of_injective B ψ.injective]
      exact hB.ne_bot
    obtain ⟨h1, h2⟩ := w_bounds ha hK2 πW hπinj hdim j φ hφ _ (hnormMap B hB.le) hBe hB1
    rw [hcardMap, hfixMap, ← hcardVW] at h1 h2
    exact ⟨h1, fun hQ => h2 (B42L2.quad_map θ hQ)⟩
  set δ : ↥L ≃* StatedSp 2 K := θL.trans (gam K j) with hδ
  have hφL : ∀ (l : ↥L) (w : W),
      (φ (binPsi θ (l : MulAut V) w)).1 = tw a (spMat (δ l)) (φ w).1 := by
    intro l w
    have h1 := hφ (θL l) w
    rw [hπW, MulEquiv.symm_apply_apply] at h1
    exact h1
  set X : Subgroup (MulAut V) := ((radical K).comap δ.toMonoidHom).map L.subtype with hX
  have hmemX : ∀ x ∈ X, ∃ l : ↥L, (l : MulAut V) = x ∧ δ l ∈ radical K := by
    rintro _ ⟨l, hl, rfl⟩
    exact ⟨l, rfl, hl⟩
  have hXL : X ≤ L := by
    intro x hx
    obtain ⟨l, rfl, -⟩ := hmemX x hx
    exact l.2
  have hXcard : Nat.card X = Nat.card K ^ 3 := by
    rw [hX, Subgroup.card_map_of_injective L.subtype_injective, ← card_radical (K := K)]
    rw [show (radical K).comap δ.toMonoidHom = (radical K).map δ.symm.toMonoidHom from
      Subgroup.comap_equiv_eq_map_symm δ (radical K)]
    exact Subgroup.card_map_of_injective δ.symm.injective
  have hXe : IsElemAbelian2 X := by
    refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
    · obtain ⟨l, rfl, hl⟩ := hmemX x hx
      obtain ⟨m, rfl, hm⟩ := hmemX y hy
      obtain ⟨C, hC, hCe⟩ := hl
      obtain ⟨E, hE, hEe⟩ := hm
      have h1 : δ (l * m) = δ (m * l) := by
        rw [map_mul, map_mul, hCe, hEe,
          CFSG.LocalAnalysis.ComponentInitial.SymplecticFour.tau_comm]
      have h2 := δ.injective h1
      exact congrArg Subtype.val h2
    · obtain ⟨l, rfl, hl⟩ := hmemX x hx
      obtain ⟨C, hC, hCe⟩ := hl
      have h1 : δ (l ^ 2) = δ 1 := by
        rw [map_pow, hCe, CFSG.LocalAnalysis.ComponentInitial.SymplecticFour.tau_sq, map_one]
      have h2 := δ.injective h1
      exact congrArg Subtype.val h2
  have hq1' : 1 < Nat.card K := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  have hX2 : IsA2 G X := by
    refine ⟨hXL.trans hLG, fun h => ?_, hXe⟩
    have : Nat.card X = 1 := by rw [h, Subgroup.card_bot]
    rw [hXcard] at this
    have : 1 < Nat.card K ^ 3 := Nat.one_lt_pow (by norm_num) hq1'
    omega
  have hcmW : ∀ (l : ↥L) (v : V), (φ (Multiplicative.toAdd (θ (cm (l : MulAut V) v)))).1 =
      twm a (δ l) (φ (Multiplicative.toAdd (θ v))).1 := by
    intro l v
    have e1 : Multiplicative.toAdd (θ (cm (l : MulAut V) v)) =
        binPsi θ (l : MulAut V) (Multiplicative.toAdd (θ v)) - Multiplicative.toAdd (θ v) := by
      rw [cm, map_mul, map_inv, toAdd_mul, toAdd_inv, ← sub_eq_add_neg, B42L2.toAdd_binPsi]
    rw [e1, map_sub, AddSubgroup.coe_sub, hφL]
    rfl
  have hXcubic : commSeries X 3 = ⊥ := by
    refine commSeries_three_eq_bot_of fun x hx y hy z hz v => ?_
    obtain ⟨lx, rfl, hlx⟩ := hmemX x hx
    obtain ⟨ly, rfl, hly⟩ := hmemX y hy
    obtain ⟨lz, rfl, hlz⟩ := hmemX z hz
    have h1 : (φ (Multiplicative.toAdd (θ (cm (lz : MulAut V) (cm (ly : MulAut V)
        (cm (lx : MulAut V) v)))))).1 = 0 := by
      rw [hcmW, hcmW, hcmW]
      exact radical_cubic a hlx hly hlz _
    have h2 : φ (Multiplicative.toAdd (θ (cm (lz : MulAut V) (cm (ly : MulAut V)
        (cm (lx : MulAut V) v))))) = 0 := Subtype.ext h1
    rw [AddEquiv.map_eq_zero_iff] at h2
    have h3 : θ (cm (lz : MulAut V) (cm (ly : MulAut V) (cm (lx : MulAut V) v))) = 1 :=
      Multiplicative.toAdd.injective h2
    simpa using congrArg θ.symm h3
  have hXfix : Nat.card K ^ 2 ≤ Nat.card ↥(fixV X) := by
    rw [← hfixMap]
    refine (card_hermFix_radical ha hK2).trans (Nat.card_le_card_of_injective
      (fun Y => ⟨φ.symm ⟨Y.1, (mem_hermFix.mp Y.2).1⟩, ?_⟩) ?_)
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨l, rfl, hl⟩ := hmemX x hx
      apply φ.injective
      apply Subtype.ext
      show (φ (binPsi θ (l : MulAut V) _)).1 = _
      rw [hφL, AddEquiv.apply_symm_apply]
      exact (mem_hermFix.mp Y.2).2 _ ⟨_, hl, rfl⟩
    · intro Y Y' h
      have h1 := congrArg (fun m : {m : W // ∀ c ∈ X.map ψ.toMonoidHom, c m = m} => φ m.1) h
      simp only [AddEquiv.apply_symm_apply] at h1
      exact Subtype.ext (Subtype.mk.inj h1)
  have hcardV : Nat.card V = Nat.card K ^ 8 := by
    rw [hcardVW, Nat.card_congr φ.toEquiv, card_hermA_eq ha hK2]
  have hXr : rAV X = 2 := by
    refine le_antisymm ((rAV_le_two_iff' hV hX2).mpr ?_) ((two_le_rAV_iff hV hX2).mpr (hbd X hX2).1)
    rw [hXcard, hcardV]
    calc Nat.card K ^ 8 = (Nat.card K ^ 3) ^ 2 * Nat.card K ^ 2 := by ring
      _ ≤ (Nat.card K ^ 3) ^ 2 * Nat.card ↥(fixV X) := Nat.mul_le_mul_left _ hXfix
  refine ⟨?_, ?_, Or.inl ⟨a, ha, twistedTensorSp4_of hK2 θ L δ φ hφL⟩⟩
  ·
    rw [qhatOf, kq_eq_coe_iff]
    exact ⟨⟨X, hX2, hXcubic, hXr⟩, fun B hB _ => (two_le_rAV_iff hV hB).mpr (hbd B hB).1⟩
  ·
    rw [qOf, lt_kq_iff]
    intro B hB hB2
    exact (two_lt_rAV_iff hV hB).mpr ((hbd B hB).2 ((isQuadratic_iff_commSeries_two B).mpr hB2))

end Main

end CFSG.Quasithin.B45Sp4

namespace CFSG.Quasithin

theorem asB45Sp4Even_holds : AsB45Sp4Even :=
  fun _ _ _ hV _ _ hHyp hP hq1 hq2 => Or.inr (B45Sp4.part3_of_sp4 hV hHyp hP hq1 hq2)

end CFSG.Quasithin

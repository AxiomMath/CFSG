module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutPSLNonsplitLinear

public section

namespace CFSG.StandardType

namespace OrdPFieldNs

theorem exists_orderOf_eq_fixed {S : Type*} [Group S] [Finite S] {p : ℕ} (hp : p.Prime)
    (Φ : MulAut S) {v : ℕ} (hΦ : Φ ^ p ^ v = 1) (hpS : p ∣ Nat.card S) :
    ∃ x : S, orderOf x = p ∧ Φ x = x := by
  have : Fact p.Prime := ⟨hp⟩
  have hHp : IsPGroup p (Subgroup.zpowers Φ) := by
    intro g
    refine ⟨v, Subtype.ext ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
    rw [Subgroup.coe_pow, ← hk, ← zpow_natCast, ← _root_.zpow_mul, mul_comm,
      _root_.zpow_mul, zpow_natCast, hΦ, one_zpow]
    rfl
  set F : Subgroup S := MonoidHom.eqLocus Φ.toMonoidHom (MonoidHom.id S) with hF
  have hfix : ∀ x : S, x ∈ MulAction.fixedPoints (Subgroup.zpowers Φ) S ↔ x ∈ F := by
    intro x
    constructor
    · intro hx
      exact hx ⟨Φ, Subgroup.mem_zpowers Φ⟩
    · intro hx g
      have hst : Φ ∈ MulAction.stabilizer (MulAut S) x := hx
      exact Subgroup.zpowers_le.mpr hst g.2
  have hmod := hHp.card_modEq_card_fixedPoints S
  have hpF : p ∣ Nat.card F := by
    have h1 : Nat.card (MulAction.fixedPoints (Subgroup.zpowers Φ) S) = Nat.card F :=
      Nat.card_congr (Equiv.subtypeEquivRight hfix)
    rw [← h1]
    exact Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hpS))
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := F) p hpF
  exact ⟨x, by rw [Subgroup.orderOf_coe, hx], x.2⟩

theorem exists_orderOf_eq_fixed_of_le {G : Type*} [Group G] {S : Subgroup G} [Finite S] {p : ℕ}
    (hp : p.Prime) (Φ : MulAut G) {v : ℕ} (hΦ : Φ ^ p ^ v = 1) (hΦS : ∀ g ∈ S, Φ g ∈ S)
    (hpS : p ∣ Nat.card S) : ∃ x ∈ S, orderOf x = p ∧ Φ x = x := by
  have hpow : ∀ k : ℕ, ∀ g ∈ S, (Φ ^ k) g ∈ S := by
    intro k
    induction k with
    | zero => intro g hg; simpa using hg
    | succ k ih => intro g hg; rw [pow_succ', MulAut.mul_apply]; exact hΦS _ (ih g hg)
  have hmap : S.map (Φ : G →* G) = S := by
    refine le_antisymm ?_ fun g hg => ⟨(Φ ^ (p ^ v - 1)) g, hpow _ g hg, ?_⟩
    · rintro _ ⟨g, hg, rfl⟩
      exact hΦS g hg
    · change Φ ((Φ ^ (p ^ v - 1)) g) = g
      rw [← MulAut.mul_apply, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_pow v p hp.pos), hΦ,
        MulAut.one_apply]
  set Ψ : MulAut S := (MulEquiv.subgroupMap Φ S).trans (MulEquiv.subgroupCongr hmap) with hΨdef
  have hΨ : ∀ x : S, ((Ψ x : S) : G) = Φ x := fun x => rfl
  have hΨk : ∀ k : ℕ, ∀ x : S, (((Ψ ^ k) x : S) : G) = (Φ ^ k) x := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih =>
      intro x
      rw [pow_succ', MulAut.mul_apply, hΨ, ih, pow_succ', MulAut.mul_apply]
  have hΨp : Ψ ^ p ^ v = 1 := MulEquiv.ext fun x => Subtype.ext (by rw [hΨk, hΦ]; rfl)
  obtain ⟨x, hxo, hxΨ⟩ := exists_orderOf_eq_fixed hp Ψ hΨp hpS
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe, hxo], by rw [← hΨ, hxΨ]⟩

section Fixed

variable {K : Type} [Field K]

theorem mem_fixed_of_fixed {σ : K ≃+* K} {a : K} (ha : σ a = a) :
    a ∈ FixedPoints.subfield (Subgroup.zpowers σ) K := by
  intro g
  have hst : σ ∈ MulAction.stabilizer (K ≃+* K) a := ha
  exact Subgroup.zpowers_le.mpr hst g.2

theorem fixed_of_mem_fixed {σ : K ≃+* K} (a : FixedPoints.subfield (Subgroup.zpowers σ) K) :
    σ (a : K) = a :=
  a.2 ⟨σ, Subgroup.mem_zpowers σ⟩

variable [Finite K]

theorem card_eq_card_fixed_pow {ℓ : ℕ} {σ : K ≃+* K} (hσ : orderOf σ = ℓ) :
    Nat.card K = Nat.card (FixedPoints.subfield (Subgroup.zpowers σ) K) ^ ℓ := by
  have : Finite (K ≃+* K) := Finite.of_injective (fun τ : K ≃+* K => (τ : K → K))
    fun a b hab => RingEquiv.ext (congrFun hab)
  have : Fintype (Subgroup.zpowers σ) := Fintype.ofFinite _
  have hfr : Module.finrank (FixedPoints.subfield (Subgroup.zpowers σ) K) K = ℓ := by
    rw [FixedPoints.finrank_eq_card, ← Nat.card_eq_fintype_card, Nat.card_zpowers, hσ]
  have : Fintype K := Fintype.ofFinite K
  have : Fintype (FixedPoints.subfield (Subgroup.zpowers σ) K) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := FixedPoints.subfield (Subgroup.zpowers σ) K) (V := K), hfr]

theorem ordQ_fixed {ℓ : ℕ} (hℓ : ℓ.Prime) {σ : K ≃+* K} {v : ℕ} (hσ : orderOf σ = ℓ ^ v) :
    OrdPNS.ordQ (FixedPoints.subfield (Subgroup.zpowers σ) K) ℓ = OrdPNS.ordQ K ℓ := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  rw [OrdPNS.ordQ_def, OrdPNS.ordQ_def, card_eq_card_fixed_pow hσ, Nat.cast_pow,
    ZMod.pow_card_pow]

omit [Finite K] in
theorem exists_gl_map_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {σ : K ≃+* K} (x : GL ι K)
    (hx : Matrix.GeneralLinearGroup.map (σ : K →+* K) x = x) :
    ∃ x₀ : GL ι (FixedPoints.subfield (Subgroup.zpowers σ) K),
      Matrix.GeneralLinearGroup.map (FixedPoints.subfield (Subgroup.zpowers σ) K).subtype x₀ =
        x := by
  set K₀ := FixedPoints.subfield (Subgroup.zpowers σ) K with hK₀
  have hxi : Matrix.GeneralLinearGroup.map (σ : K →+* K) x⁻¹ = x⁻¹ := by rw [map_inv, hx]
  have hfx : ∀ z : GL ι K, Matrix.GeneralLinearGroup.map (σ : K →+* K) z = z →
      ∀ i j, (z : Matrix ι ι K) i j ∈ K₀ := fun z hz i j => by
    apply mem_fixed_of_fixed
    have h1 := congrArg (fun w : GL ι K => (w : Matrix ι ι K) i j) hz
    simpa using h1
  set M₀ : Matrix ι ι K₀ := Matrix.of fun i j => ⟨(x : Matrix ι ι K) i j, hfx x hx i j⟩
  set N₀ : Matrix ι ι K₀ :=
    Matrix.of fun i j => ⟨((x⁻¹ : GL ι K) : Matrix ι ι K) i j, hfx _ hxi i j⟩
  have hM : M₀.map K₀.subtype = (x : Matrix ι ι K) := by ext i j; rfl
  have hN : N₀.map K₀.subtype = ((x⁻¹ : GL ι K) : Matrix ι ι K) := by ext i j; rfl
  have hinj : Function.Injective fun A : Matrix ι ι K₀ => A.map K₀.subtype :=
    Matrix.map_injective Subtype.val_injective
  have h1 : M₀ * N₀ = 1 := hinj (by
    simp only
    rw [Matrix.map_mul, hM, hN, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)])
  have h2 : N₀ * M₀ = 1 := hinj (by
    simp only
    rw [Matrix.map_mul, hM, hN, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)])
  exact ⟨⟨M₀, N₀, h1, h2⟩, Units.ext hM⟩

omit [Finite K] in
theorem gl_map_fixed {ι : Type*} [Fintype ι] [DecidableEq ι] {σ : K ≃+* K}
    (x₀ : GL ι (FixedPoints.subfield (Subgroup.zpowers σ) K)) :
    Matrix.GeneralLinearGroup.map (σ : K →+* K)
        (Matrix.GeneralLinearGroup.map (FixedPoints.subfield (Subgroup.zpowers σ) K).subtype x₀) =
      Matrix.GeneralLinearGroup.map (FixedPoints.subfield (Subgroup.zpowers σ) K).subtype x₀ := by
  ext i j
  exact fixed_of_mem_fixed _

end Fixed

end OrdPFieldNs

end CFSG.StandardType

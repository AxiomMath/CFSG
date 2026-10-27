module

public import CFSG.Timmesfeld.Transvection.ModelSUTheta
public import CFSG.Timmesfeld.Transvection.ModelRankSU

public section

namespace CFSG.Timmesfeld.Transvection

namespace ModelRank

open Matrix CFSG.LieType.Universal.Unitary CFSG.Timmesfeld.LieEmbed CFSG.Timmesfeld.ARS
  CFSG.Open CFSG.LieType.BorelTits

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}

theorem suMat_pow_mulVec_of_eq_smul {a : Fin m → F} {x : SU σ m} {μ : F}
    (hx : suMat σ m x *ᵥ a = μ • a) (n : ℕ) : suMat σ m (x ^ n) *ᵥ a = μ ^ n • a := by
  induction n with
  | zero => rw [pow_zero, pow_zero, map_one, one_mulVec, one_smul]
  | succ n ih =>
    rw [pow_succ', map_mul, ← mulVec_mulVec, ih, mulVec_smul, hx, smul_smul, pow_succ]

theorem suMat_mulVec_eq_of_pow_two_pow [CharP F 2] {a : Fin m → F} (ha : a ≠ 0) {x : SU σ m}
    (hx : x ∈ uLine σ a) {k : ℕ} (hk : x ^ 2 ^ k = 1) : suMat σ m x *ᵥ a = a := by
  obtain ⟨μ, -, hxa⟩ := hx
  have h1 : μ ^ 2 ^ k • a = a := by
    rw [← suMat_pow_mulVec_of_eq_smul hxa, hk, map_one, one_mulVec]
  have h2 : μ ^ 2 ^ k = 1 := by
    have h3 : (μ ^ 2 ^ k - 1) • a = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right ha)
  have h4 : (μ - 1) ^ 2 ^ k = 0 := by rw [sub_pow_char_pow, h2, one_pow, sub_self]
  have h5 : μ = 1 := sub_eq_zero.1 ((pow_eq_zero_iff (pow_ne_zero k two_ne_zero)).1 h4)
  rw [hxa, h5, one_smul]

theorem exists_levAct_fixed [Finite F] [CharP F 2] {a d : Fin m → F} {T : Subgroup (SU σ m)}
    (Θ : SUThetaFacts σ a d T) (hG : SUGeomFacts σ a d) {R : Subgroup (SU σ m)}
    (hR : R ≤ uLine σ a) (hRp : IsPGroup 2 R) :
    ∃ w₀ ∈ perpPair σ a d, w₀ ≠ 0 ∧ ∀ x ∈ R, levAct σ a d x w₀ = w₀ := by
  letI : MulAction R (perpPair σ a d) :=
    { smul := fun x w => ⟨levAct σ a d x w, Θ.levAct_mem (hR x.2) w.2⟩
      one_smul := fun w => Subtype.ext (Θ.levAct_one w.2)
      mul_smul := fun x y w => Subtype.ext (Θ.levAct_mul (hR x.2) (hR y.2) w.2) }
  have h0 : (0 : perpPair σ a d) ∈ MulAction.fixedPoints R (perpPair σ a d) := by
    intro x
    apply Subtype.ext
    change levAct σ a d x 0 = 0
    have := Θ.levAct_smul x 0 0
    rwa [zero_smul, zero_smul] at this
  obtain ⟨e, he, he0, -⟩ := hG.exists_iso
  have hcard : 2 ∣ Nat.card (perpPair σ a d) := by
    have h2 : addOrderOf (⟨e, he⟩ : perpPair σ a d) = 2 := by
      apply addOrderOf_eq_prime
      · apply Subtype.ext
        change (2 : ℕ) • e = 0
        rw [two_nsmul, ← two_smul F e, CharTwo.two_eq_zero, zero_smul]
      · intro h
        exact he0 (congrArg Subtype.val h)
    rw [← h2]
    exact addOrderOf_dvd_natCard _
  obtain ⟨w, hw, hw0⟩ := hRp.exists_fixed_point_of_prime_dvd_card_of_fixed_point _ hcard h0
  refine ⟨w.1, w.2, fun h => hw0 (Subtype.ext h.symm), fun x hx => ?_⟩
  exact congrArg Subtype.val (hw ⟨x, hx⟩)

theorem levAct_eq_self_of_fixed [CharP F 2] (hσ : ∀ c, σ (σ c) = c) {a d : Fin m → F}
    {T : Subgroup (SU σ m)} (Θ : SUThetaFacts σ a d T) (hG : SUGeomFacts σ a d)
    {R : Subgroup (SU σ m)} (hR : R ≤ uLine σ a)
    (hnorm : ∀ b ∈ uLine σ a, ∀ r ∈ R, b * r * b⁻¹ ∈ R) {w₀ : Fin m → F}
    (hw₀ : w₀ ∈ perpPair σ a d) (hw₀0 : w₀ ≠ 0) (hfix : ∀ x ∈ R, levAct σ a d x w₀ = w₀) :
    ∀ x ∈ R, ∀ w ∈ perpPair σ a d, levAct σ a d x w = w := by
  have hlev0 : ∀ g : SU σ m, levAct σ a d g 0 = 0 := fun g => by
    have := Θ.levAct_smul g 0 0
    rwa [zero_smul, zero_smul] at this
  obtain ⟨C, hC⟩ : ∃ C : AddSubgroup (Fin m → F),
      ∀ w, w ∈ C ↔ w ∈ perpPair σ a d ∧ ∀ x ∈ R, levAct σ a d x w = w :=
    ⟨{ carrier := {w | w ∈ perpPair σ a d ∧ ∀ x ∈ R, levAct σ a d x w = w}
       add_mem' := fun {w w'} hw hw' => ⟨add_mem hw.1 hw'.1, fun x hx => by
         rw [Θ.levAct_add, hw.2 x hx, hw'.2 x hx]⟩
       zero_mem' := ⟨zero_mem _, fun x _ => hlev0 x⟩
       neg_mem' := fun {w} hw => ⟨neg_mem hw.1, fun x hx => by
         rw [← neg_one_smul F w, Θ.levAct_smul, hw.2 x hx]⟩ }, fun w => Iff.rfl⟩
  have hCsmul : ∀ c : F, ∀ w ∈ C, c • w ∈ C := fun c w hw => (hC _).2
    ⟨Submodule.smul_mem _ c ((hC w).1 hw).1, fun x hx => by
      rw [Θ.levAct_smul, ((hC w).1 hw).2 x hx]⟩
  have hkl := hG.kl C (fun w hw => ((hC w).1 hw).1) ?_
  · rcases hkl with h | h
    · exfalso
      have h1 : w₀ ∈ C := (hC w₀).2 ⟨hw₀, hfix⟩
      rw [h, AddSubgroup.mem_bot] at h1
      exact hw₀0 h1
    · intro x hx w hw
      exact ((hC w).1 (h w hw)).2 x hx
  · intro v hv hvv x hx hvx c
    have hxP := ((hC x).1 hx).1
    have hxR := ((hC x).1 hx).2
    have h1 : (1 : F) + σ 1 = 0 := by rw [map_one, CharTwo.add_self_eq_zero]
    obtain ⟨t, ht⟩ := exists_suMat_eq_uTrans hσ hvv h1
    have hta : suMat σ m t *ᵥ a = a := Θ.transv_a hv ht
    have htL : t ∈ uLine σ a := ⟨1, one_ne_zero, by rw [hta, one_smul]⟩
    have htx : levAct σ a d t x ∈ C := by
      refine (hC _).2 ⟨Θ.levAct_mem htL hxP, fun y hy => ?_⟩
      have hy' : t⁻¹ * y * t ∈ R := by
        have := hnorm t⁻¹ (inv_mem htL) y hy
        rwa [inv_inv] at this
      rw [← Θ.levAct_mul (hR hy) htL hxP, show y * t = t * (t⁻¹ * y * t) by group,
        Θ.levAct_mul htL (hR hy') hxP, hxR _ hy']
    rw [Θ.levAct_transv hv hvv ht hxP, one_mul] at htx
    have h2 : uForm σ v x • v ∈ C := by
      have := sub_mem htx hx
      rwa [add_sub_cancel_left] at this
    have h3 := hCsmul (c / uForm σ v x) _ h2
    rwa [smul_smul, div_mul_cancel₀ c hvx] at h3

theorem pCoreOf_normalizer_eq_uRad [CharP F 2] [Finite F] (hσ : ∀ c, σ (σ c) = c)
    {a d : Fin m → F} {T : Subgroup (SU σ m)} (ha : a ≠ 0) (hT : IsUTransGroup σ a T)
    (Θ : SUThetaFacts σ a d T) (hG : SUGeomFacts σ a d) :
    pCoreOf 2 (Subgroup.normalizer (T : Set (SU σ m))) = uRad σ a := by
  refine le_antisymm ?_ (uRad_le_pCoreOf hσ ha hT)
  rw [normalizer_eq_uLine hσ ha hT]
  have hle : pCoreOf 2 (uLine σ a) ≤ uLine σ a := pCoreOf_le 2 _
  have hp : IsPGroup 2 (pCoreOf 2 (uLine σ a)) := pCoreOf_isPGroup 2 _
  have hnorm : ∀ b ∈ uLine σ a, ∀ r ∈ pCoreOf 2 (uLine σ a), b * r * b⁻¹ ∈ pCoreOf 2 (uLine σ a) :=
    fun b hb r hr => (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 _ hb) r).1 hr
  obtain ⟨w₀, hw₀, hw₀0, hfix⟩ := exists_levAct_fixed Θ hG hle hp
  have hall := levAct_eq_self_of_fixed hσ Θ hG hle hnorm hw₀ hw₀0 hfix
  intro x hx
  obtain ⟨k, hk⟩ := hp ⟨x, hx⟩
  have hk' : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
  exact Θ.mem_uRad (suMat_mulVec_eq_of_pow_two_pow ha (hle hx) hk') (hall x hx)

end ModelRank

end CFSG.Timmesfeld.Transvection

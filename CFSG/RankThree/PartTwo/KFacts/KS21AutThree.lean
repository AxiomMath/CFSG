module

public import CFSG.RankThree.PartTwo.KFacts.KS21FusionCore

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS21

open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

@[expose] def AutThree (M : Type) [Group M] (n : ℕ) : Prop :=
  ∀ P : Sylow 3 M, ∀ A : Subgroup M, A ≤ P → IsElemAbelian 3 A → Nat.card A = 3 ^ n →
    ∀ α : MulAut M, (∃ k : ℕ, α ^ 3 ^ k = 1) → (P : Subgroup M).map α.toMonoidHom = P →
      ∃ p ∈ (P : Subgroup M), ∃ φ : MulAut M, φ ^ 3 = 1 ∧ (∀ a ∈ A, φ a = a) ∧
        α = MulAut.conj p * φ

@[expose] def TerminalAutThree : Prop :=
  AutThree (projSU 5 2 3) 4 ∧ AutThree (projSL 4 (GaloisField 2 2)) 3 ∧
    AutThree (projSp 3 (GaloisField 2 2)) 3

theorem AutThree.of_mulEquiv {M M' : Type} [Group M] [Group M'] {n : ℕ} (e : M ≃* M')
    (h : AutThree M n) : AutThree M' n := by
  intro P' A' hAP' hA' hcard α' hα' hα'P
  obtain ⟨P, hP⟩ : ∃ P : Sylow 3 M, (P : Subgroup M) = (P' : Subgroup M').comap e.toMonoidHom :=
    ⟨P'.comapOfInjective e.toMonoidHom e.injective (fun y _ => ⟨e.symm y, by simp⟩),
      Sylow.coe_comapOfInjective _ _ _ _⟩
  set α := (MulAut.congr e).symm α' with hαdef
  have hα_apply : ∀ x, α x = e.symm (α' (e x)) := fun x => by
    rw [hαdef, MulAut.congr_symm_apply]
    rfl
  have hα : ∃ k : ℕ, α ^ 3 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hα'
    exact ⟨k, by rw [hαdef, ← map_pow, hk, map_one]⟩
  have hαP : (P : Subgroup M).map α.toMonoidHom = P := by
    ext x
    rw [Subgroup.mem_map, hP, Subgroup.mem_comap]
    constructor
    · rintro ⟨y, hy, rfl⟩
      change e (α y) ∈ (P' : Subgroup M')
      rw [hα_apply, MulEquiv.apply_symm_apply]
      have : α' (e y) ∈ (P' : Subgroup M').map α'.toMonoidHom := ⟨e y, hy, rfl⟩
      rwa [hα'P] at this
    · intro hx
      have : e x ∈ (P' : Subgroup M').map α'.toMonoidHom := by rw [hα'P]; exact hx
      obtain ⟨y', hy', hy'x⟩ := this
      refine ⟨e.symm y', ?_, ?_⟩
      · change e (e.symm y') ∈ (P' : Subgroup M')
        rw [MulEquiv.apply_symm_apply]
        exact hy'
      · change α (e.symm y') = x
        rw [hα_apply, MulEquiv.apply_symm_apply]
        have hy'x' : α' y' = e x := hy'x
        rw [hy'x', MulEquiv.symm_apply_apply]
  set A := A'.map e.symm.toMonoidHom with hAdef
  have hAP : A ≤ P := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hP, Subgroup.mem_comap]
    simpa using hAP' hy
  have hAcard : Nat.card A = 3 ^ n := by
    rw [hAdef, Subgroup.card_map_of_injective e.symm.injective, hcard]
  obtain ⟨p, hpP, φ, hφ3, hφA, hαφ⟩ := h P A hAP (isElemAbelian_map _ hA') hAcard α hα hαP
  refine ⟨e p, ?_, MulAut.congr e φ, by rw [← map_pow, hφ3, map_one], fun a ha => ?_, ?_⟩
  · rw [hP] at hpP
    exact hpP
  · rw [MulAut.congr_apply]
    change e (φ (e.symm a)) = a
    have := hφA (e.symm a) ⟨a, ha, rfl⟩
    rw [this, MulEquiv.apply_symm_apply]
  · have hα' : α' = MulAut.congr e α := by rw [hαdef, MulEquiv.apply_symm_apply]
    rw [hα', hαφ, map_mul]
    congr 1
    ext x
    rw [MulAut.congr_apply]
    change e (p * e.symm x * p⁻¹) = e p * x * (e p)⁻¹
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem center_eq_bot_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : Subgroup.center X = ⊥) : Subgroup.center Y = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  have hx : e.symm y ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff] at hy ⊢
    intro x
    have := hy (e x)
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, this]
  rw [h, Subgroup.mem_bot] at hx
  rw [Subgroup.mem_bot, ← MulEquiv.apply_symm_apply e y, hx, map_one]

theorem mulAut_mul_conj_mul_inv {M : Type} [Group M] (φ : MulAut M) (g : M) :
    φ * MulAut.conj g * φ⁻¹ = MulAut.conj (φ g) := by
  ext x
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul,
    map_inv, MulAut.apply_inv_self]

theorem conj_range_normal {M : Type} [Group M] :
    (MulAut.conj : M →* MulAut M).range.Normal :=
  ⟨fun _ ⟨g, hg⟩ φ => ⟨φ g, by rw [← hg, mulAut_mul_conj_mul_inv]⟩⟩

theorem mem_range_conj_of_sq_mem {M : Type} [Group M] {α : MulAut M}
    (h2 : α ^ 2 ∈ (MulAut.conj : M →* MulAut M).range) (h3 : ∃ k : ℕ, α ^ 3 ^ k = 1) :
    α ∈ (MulAut.conj : M →* MulAut M).range := by
  obtain ⟨k, hk⟩ := h3
  obtain ⟨m, hm⟩ : ∃ m, 3 ^ k = 2 * m + 1 := Odd.pow (by decide : Odd 3)
  have hα : α = ((α ^ 2) ^ m)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_mul, ← pow_succ', ← hm, hk]
  rw [hα]
  exact Subgroup.inv_mem _ (Subgroup.pow_mem _ h2 m)

theorem autThree_of_inner {M : Type} [Group M] [Finite M] (hZ : Subgroup.center M = ⊥)
    (hinn : ∀ α : MulAut M, (∃ k : ℕ, α ^ 3 ^ k = 1) →
      α ∈ (MulAut.conj : M →* MulAut M).range) (n : ℕ) : AutThree M n := by
  intro P A _ _ _ α hα hαP
  obtain ⟨g, rfl⟩ := hinn α hα
  obtain ⟨k, hk⟩ := hα
  have hgk : g ^ 3 ^ k = 1 := by
    rw [← map_pow] at hk
    have hz : g ^ 3 ^ k ∈ Subgroup.center M := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := congrArg (fun φ : MulAut M => φ y) hk
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc y * g ^ 3 ^ k = g ^ 3 ^ k * y * (g ^ 3 ^ k)⁻¹ * g ^ 3 ^ k := by
            rw [this]
        _ = g ^ 3 ^ k * y := by rw [inv_mul_cancel_right]
    rw [hZ, Subgroup.mem_bot] at hz
    exact hz
  have hgN : g ∈ Subgroup.normalizer ((P : Subgroup M) : Set M) := by
    refine Subgroup.mem_normalizer_fintype fun q hq => ?_
    have : MulAut.conj g q ∈ (P : Subgroup M).map (MulAut.conj g).toMonoidHom := ⟨q, hq, rfl⟩
    rwa [hαP] at this
  have hzp : IsPGroup 3 (Subgroup.zpowers g) := by
    intro x
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp x.2
    refine ⟨k, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, ← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      hgk, one_zpow, Subgroup.coe_one]
  have hsup := IsPGroup.to_sup_of_normal_left' P.isPGroup' hzp (Subgroup.zpowers_le.mpr hgN)
  have heq := P.is_maximal' hsup le_sup_left
  have hgP : g ∈ (P : Subgroup M) := by
    rw [← heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
  exact ⟨g, hgP, 1, one_pow 3, fun a _ => rfl, (mul_one _).symm⟩

end CFSG.RankThree.PartTwo.KFacts.KS21

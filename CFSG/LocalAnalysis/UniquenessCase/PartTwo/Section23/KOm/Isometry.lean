module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Out
public import CFSG.Quasithin.Background.Module
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8SimQuad

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KOm

open CFSG.Open Matrix
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.RankThree.GF2n.Stroth80 (AddCommutantScalar)

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] def isoFix (Q : (ι → K) → K) (w₀ : ι → K) : Subgroup (GL ι K) where
  carrier := {A | (∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v) ∧ (A : Matrix ι ι K) *ᵥ w₀ = w₀}
  mul_mem' {A B} hA hB := by
    refine ⟨fun v => ?_, ?_⟩
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, hA.1, hB.1]
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, hB.2, hA.2]
  one_mem' := ⟨fun v => by simp, by simp⟩
  inv_mem' {A} hA := by
    have hAA : ∀ v, (A : Matrix ι ι K) *ᵥ (((A⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v) = v := by
      intro v
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec]
    refine ⟨fun v => ?_, ?_⟩
    · rw [← hA.1, hAA]
    · conv_lhs => rw [← hA.2]
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]

theorem mem_isoFix {Q : (ι → K) → K} {w₀ : ι → K} {A : GL ι K} :
    A ∈ isoFix Q w₀ ↔
      (∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v) ∧ (A : Matrix ι ι K) *ᵥ w₀ = w₀ :=
  Iff.rfl

theorem exists_isoFix_of_mem_s16gNorm [Finite K] [CharP K 2] [Nonempty ι]
    (Q : QuadraticForm K (ι → K)) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {Γ : Subgroup (GL ι K)} (hΓ : AddCommutantScalar Γ)
    (hΓQ : ∀ A ∈ Γ, ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v)
    {w₀ : ι → K} (hw₀ : w₀ ≠ 0) {t : MulAut (Multiplicative (ι → K))} (ht : t ∈ s16gNorm Γ)
    {k : ℕ} (htk : t ^ 2 ^ k = 1)
    (hfix : ∀ c : K, t (Multiplicative.ofAdd (c • w₀)) = Multiplicative.ofAdd (c • w₀)) :
    ∃ A ∈ isoFix (⇑Q) w₀, A ∈ Subgroup.normalizer (Γ : Set (GL ι K)) ∧
      s16gNatHom ι K A = t := by
  classical
  obtain ⟨θ, hθ, hker⟩ := s16g_exists_theta (K := K) hΓ
  let t' : ↥(s16gNorm Γ) := ⟨t, ht⟩
  have hfix1 : t (Multiplicative.ofAdd w₀) = Multiplicative.ofAdd w₀ := by
    simpa using hfix 1
  have htheta : θ t' = 1 := by
    ext c
    have h := hθ t' c (Multiplicative.ofAdd w₀)
    change t (s16gSMul c (Multiplicative.ofAdd w₀)) =
      s16gSMul (θ t' c) (t (Multiplicative.ofAdd w₀)) at h
    rw [s16gSMul, toAdd_ofAdd, hfix c, hfix1, s16gSMul, toAdd_ofAdd] at h
    have h' : c • w₀ = (θ t' c) • w₀ := by
      simpa using congrArg Multiplicative.toAdd h
    have hsub : (c - θ t' c) • w₀ = 0 := by
      rw [sub_smul, h', sub_self]
    have hzero : c - θ t' c = 0 := by
      rcases smul_eq_zero.1 hsub with hz | hz
      · exact hz
      · exact absurd hz hw₀
    show θ t' c = c
    exact (sub_eq_zero.1 hzero).symm
  have htlin : t ∈ s16gLin ι K := (hker t').1 htheta
  obtain ⟨A, hAeq⟩ :=
    MonoidHom.mem_range.mp (show t ∈ (s16gNatHom ι K).range from htlin)
  have hAnorm : A ∈ Subgroup.normalizer (Γ : Set (GL ι K)) :=
    (s16g_mem_norm_natHom_iff Γ A).1 (by rw [hAeq]; exact ht)
  have hAw : (A : Matrix ι ι K) *ᵥ w₀ = w₀ := by
    have h := hfix 1
    simp only [one_smul] at h
    have h' := congrArg Multiplicative.toAdd h
    simp only [toAdd_ofAdd] at h'
    rw [← hAeq, s16gNatHom_apply, toAdd_ofAdd] at h'
    exact h'
  obtain ⟨μ, -, hμ1⟩ := s16g_exists_mult_quadratic Q hQ hΓ hΓQ
  let A' : ↥(Subgroup.normalizer (Γ : Set (GL ι K))) := ⟨A, hAnorm⟩
  have hA1 : A ^ 2 ^ k = 1 := by
    apply s16gNatHom_injective
    rw [map_pow, map_one, hAeq, htk]
  have hA'1 : A' ^ 2 ^ k = 1 := by
    apply Subtype.ext
    simpa [Subgroup.coe_pow, Subgroup.coe_one] using hA1
  have hpow : (μ A') ^ 2 ^ k = 1 := by
    rw [← map_pow, hA'1, map_one]
  have hodd : Odd (Nat.card K - 1) := by
    haveI : Fintype K := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    have hK : Nat.card K = 2 ^ (n : ℕ) := by
      rw [Nat.card_eq_fintype_card]
      exact hn
    rw [hK]
    have heven : Even (2 ^ (n : ℕ)) := by
      rw [Nat.even_pow]
      exact ⟨by norm_num, n.pos.ne'⟩
    exact Nat.Even.sub_odd Nat.one_le_two_pow heven (by norm_num)
  have hcop : Nat.Coprime (2 ^ k) (Nat.card K - 1) :=
    Nat.Coprime.pow_left k (Odd.coprime_two_left hodd)
  have hord1 : orderOf (μ A') ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hpow
  have hord2 : orderOf (μ A') ∣ Nat.card K - 1 := by
    simpa [Nat.card_units] using orderOf_dvd_natCard (μ A')
  have hμA' : μ A' = 1 :=
    orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop hord1 hord2)
  have hQiso : ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v := (hμ1 A').1 hμA'
  refine ⟨A, ?_, hAnorm, hAeq⟩
  rw [mem_isoFix]
  exact ⟨hQiso, hAw⟩

theorem exists_glModel {W : Type} [CommGroup W] (e : W ≃* Multiplicative (ι → K))
    {X : Subgroup (MulAut W)} {Y : Subgroup (GL ι K)}
    (hXY : X.map (MulAut.congr e).toMonoidHom ≤ Y.map (s16gNatHom ι K)) :
    ∃ X' : Subgroup (GL ι K), X' ≤ Y ∧
      X'.map (s16gNatHom ι K) = X.map (MulAut.congr e).toMonoidHom ∧
      Nonempty (↥X ≃* ↥X') ∧
      Nat.card ↥(CFSG.Quasithin.fixV X) =
        Nat.card {v : ι → K // ∀ g ∈ X', (g : Matrix ι ι K) *ᵥ v = v} := by
  classical
  let Φ : MulAut W →* MulAut (Multiplicative (ι → K)) := (MulAut.congr e).toMonoidHom
  let X' : Subgroup (GL ι K) := (X.map Φ).comap (s16gNatHom ι K)
  have hmapX' : X'.map (s16gNatHom ι K) = X.map Φ := by
    change Subgroup.map (s16gNatHom ι K)
      (Subgroup.comap (s16gNatHom ι K) (X.map Φ)) = X.map Φ
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.2 (hXY.trans (Subgroup.map_le_range (s16gNatHom ι K) Y))
  have hX'Y : X' ≤ Y := by
    intro g hg
    have hg' : s16gNatHom ι K g ∈ X.map Φ := hg
    exact (Subgroup.mem_map_iff_mem s16gNatHom_injective).1 (hXY hg')
  have hiso : Nonempty (↥X ≃* ↥X') := by
    refine ⟨(X.equivMapOfInjective Φ (MulAut.congr e).injective).trans
      ((MulEquiv.subgroupCongr hmapX').symm.trans
        (X'.equivMapOfInjective (s16gNatHom ι K) s16gNatHom_injective).symm)⟩
  have hcongr : ∀ (x : MulAut W) (w : W), (Φ x) (e w) = e (x w) := by
    intro x w
    change (MulAut.congr e x) (e w) = e (x w)
    rw [MulAut.congr_apply]
    simp [MulEquiv.trans_apply]
  have hfixiff : ∀ w : W,
      w ∈ CFSG.Quasithin.fixV X ↔
        ∀ g ∈ X', (g : Matrix ι ι K) *ᵥ
          (Multiplicative.toAdd (e w)) = Multiplicative.toAdd (e w) := by
    intro w
    rw [CFSG.Quasithin.mem_fixV]
    constructor
    · intro hw g hg
      have hg' : s16gNatHom ι K g ∈ X.map Φ := hg
      obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.1 hg'
      have h1 : Multiplicative.toAdd (s16gNatHom ι K g (e w)) =
          (g : Matrix ι ι K) *ᵥ Multiplicative.toAdd (e w) := by
        rw [s16gNatHom_apply, toAdd_ofAdd]
      rw [← h1, ← hxeq, hcongr x w, hw x hx]
    · intro hfix x hx
      have hmem : Φ x ∈ X.map Φ := Subgroup.mem_map_of_mem Φ hx
      rw [← hmapX'] at hmem
      obtain ⟨g, hg, hgeq⟩ := Subgroup.mem_map.1 hmem
      have hfixg := hfix g hg
      have h1 : Multiplicative.toAdd (s16gNatHom ι K g (e w)) =
          (g : Matrix ι ι K) *ᵥ Multiplicative.toAdd (e w) := by
        rw [s16gNatHom_apply, toAdd_ofAdd]
      rw [← h1, hgeq, hcongr x w] at hfixg
      exact e.injective (Multiplicative.toAdd.injective hfixg)
  refine ⟨X', hX'Y, hmapX', hiso, ?_⟩
  exact Nat.card_congr ((e.toEquiv.trans Multiplicative.toAdd).subtypeEquiv hfixiff)

theorem toAdd_congr_symm_natHom {W : Type} [CommGroup W] (e : W ≃* Multiplicative (ι → K))
    (A : GL ι K) (w : W) :
    Multiplicative.toAdd (e ((MulAut.congr e).symm (s16gNatHom ι K A) w)) =
      (A : Matrix ι ι K) *ᵥ Multiplicative.toAdd (e w) := by
  rw [MulAut.congr_symm_apply]
  simp [MulEquiv.trans_apply, s16gNatHom_apply]

theorem congr_symm_natHom_mem {W : Type} [CommGroup W] {e : W ≃* Multiplicative (ι → K)}
    {H : Subgroup (MulAut W)} {Γ : Subgroup (GL ι K)}
    (hH : H.map (MulAut.congr e).toMonoidHom = Γ.map (s16gNatHom ι K)) {A : GL ι K}
    (hA : A ∈ Γ) : (MulAut.congr e).symm (s16gNatHom ι K A) ∈ H := by
  have hmem : s16gNatHom ι K A ∈ H.map (MulAut.congr e).toMonoidHom := by
    rw [hH]
    exact Subgroup.mem_map_of_mem _ hA
  obtain ⟨h, hh, hheq⟩ := Subgroup.mem_map.1 hmem
  have h2 : h = (MulAut.congr e).symm (s16gNatHom ι K A) := by
    rw [← hheq]
    exact (MulEquiv.symm_apply_apply (MulAut.congr e) h).symm
  rw [← h2]
  exact hh

end CFSG.LocalAnalysis.UniquenessCase.UC22.KOm

end

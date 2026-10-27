module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Defs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.TorusSp4
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.TorusAutomizerWeyl
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.TorusAutomizerLin
import CFSG.Quasithin.Vol2.F134LieSp4

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.QuasithinUnique.Lin2.Five (tauEquiv tauAut projEquiv)

private theorem tasp_exists_equiv {X : Type} [Group X] {K : Type} [Field K] [Finite K]
    [CharP K 2] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 3 ≤ n) (hodd : Odd n)
    (e : X ≃* StatedSp 2 K) {T : Subgroup X} (hT : IsZModSq T n) :
    ∃ E : StatedSp 2 K ≃* X, ∀ z, z ∈ T ↔ E.symm z ∈ torus 2 K := by
  obtain ⟨eT⟩ := hT
  obtain ⟨g, hg⟩ := exists_conj_eq_torus_of_isZModSq_sp4 hK hn hodd (T := T.map e.toMonoidHom)
    ⟨(T.equivMapOfInjective e.toMonoidHom e.injective).symm.trans eT⟩
  refine ⟨(MulAut.conj g).trans e.symm, fun z => ?_⟩
  show z ∈ T ↔ (MulAut.conj g).symm (e z) ∈ torus 2 K
  rw [← Subgroup.mem_map_equiv, ← hg, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

private theorem tasp_inv_mem {G : Type*} [Group G] [Finite G] {H : Subgroup G} (φ : MulAut G)
    (hφ : ∀ h ∈ H, φ h ∈ H) : ∀ h ∈ H, φ⁻¹ h ∈ H := by
  have hle : H.map φ.toMonoidHom ≤ H := by
    rintro _ ⟨h, hh, rfl⟩
    exact hφ h hh
  have heq : H.map φ.toMonoidHom = H := Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective).ge
  intro h hh
  rw [← heq, Subgroup.mem_map_equiv] at hh
  exact hh

private theorem tasp_tau_pow_torusHom {K : Type} [Field K] [Finite K] [CharP K 2] (m : ℕ)
    (t : Fin 2 → Kˣ) :
    ((tauEquiv : MulAut (StatedSp 2 K)) ^ m) (torusHom t) =
      torusHom ((⇑(uc22pwI2Rho K))^[m] t) := by
  induction m generalizing t with
  | zero => rw [pow_zero]; rfl
  | succ m ih =>
    rw [pow_succ, MulAut.mul_apply, Function.iterate_succ_apply, ← ih]
    exact congrArg _ (uc22pwI2_sp4_tau_torus t)

private theorem tasp_tauAut_pow {K : Type} [Field K] [Finite K] [CharP K 2] (m : ℕ)
    (h : StatedSp 2 K) :
    ((tauAut : MulAut (StatedProj (StatedSp 2 K))) ^ m) (projEquiv K h) =
      projEquiv K (((tauEquiv : MulAut (StatedSp 2 K)) ^ m) h) := by
  have hτ : (tauAut : MulAut (StatedProj (StatedSp 2 K))) =
      MulAut.congr (projEquiv K) tauEquiv := rfl
  rw [hτ, ← map_pow, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply]

private theorem tasp_normal_form {K : Type} [Field K] [Finite K] [CharP K 2]
    (σ₁ : MulAut (StatedSp 2 K)) : ∃ (x : StatedSp 2 K) (m : ℕ),
      ∀ h, σ₁ h = x * ((tauEquiv : MulAut (StatedSp 2 K)) ^ m) h * x⁻¹ := by
  obtain ⟨y, m, hy⟩ := CFSG.Quasithin.F134.Sp4.exists_eq_conj_mul_tauAut_pow
    (MulAut.congr (projEquiv K) σ₁)
  refine ⟨(projEquiv K).symm y, m, fun h => (projEquiv K).injective ?_⟩
  have h1 := congrArg (fun α : MulAut (StatedProj (StatedSp 2 K)) => α (projEquiv K h)) hy
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    MulAut.mul_apply, MulAut.conj_apply] at h1
  rw [h1, tasp_tauAut_pow, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

private theorem tasp_mem_normalizer {K : Type} [Field K] [Finite K] [CharP K 2]
    {σ₁ : MulAut (StatedSp 2 K)} (hσ₁ : ∀ h ∈ torus 2 K, σ₁ h ∈ torus 2 K) {x : StatedSp 2 K}
    {m : ℕ} (hx : ∀ h, σ₁ h = x * ((tauEquiv : MulAut (StatedSp 2 K)) ^ m) h * x⁻¹) :
    x ∈ normalizer ((torus 2 K : Subgroup (StatedSp 2 K)) : Set (StatedSp 2 K)) := by
  have hτ : ∀ h ∈ torus 2 K, ((tauEquiv : MulAut (StatedSp 2 K)) ^ m) h ∈ torus 2 K := by
    rintro _ ⟨t, rfl⟩
    rw [tasp_tau_pow_torusHom]
    exact torusHom_mem_torus _
  have hc : ∀ h ∈ torus 2 K, MulAut.conj x h ∈ torus 2 K := fun h hh => by
    have h1 := hx (((tauEquiv : MulAut (StatedSp 2 K)) ^ m)⁻¹ h)
    rw [MulAut.apply_inv_self] at h1
    rw [MulAut.conj_apply, ← h1]
    exact hσ₁ _ (tasp_inv_mem _ hτ h hh)
  have hc' := tasp_inv_mem _ hc
  refine mem_normalizer_iff.mpr fun h => ⟨hc h, fun hh => ?_⟩
  have h1 := hc' _ hh
  rwa [MulAut.conj_inv_apply, show x⁻¹ * (x * h * x⁻¹) * x = h by group] at h1

private theorem tasp_conj {X : Type} [Group X] {K : Type} [Field K] {T : Subgroup X}
    {E : StatedSp 2 K ≃* X} (hTE : ∀ z, z ∈ T ↔ E.symm z ∈ torus 2 K) (σ : MulAut X)
    (hσ : ∃ k : ℕ, orderOf σ = 2 ^ k) (hσT : T.map σ.toMonoidHom = T)
    (ht₀ : ∃ t₀ ∈ T, t₀ ≠ 1 ∧ σ t₀ = t₀) :
    ∃ σ₁ : MulAut (StatedSp 2 K), (∀ h, E (σ₁ h) = σ (E h)) ∧
      (∀ h ∈ torus 2 K, σ₁ h ∈ torus 2 K) ∧ (∃ k : ℕ, σ₁ ^ 2 ^ k = 1) ∧
      ∃ s₀ : Fin 2 → Kˣ, s₀ ≠ 1 ∧ σ₁ (torusHom s₀) = torusHom s₀ := by
  have hσ₁E : ∀ h, E (MulAut.congr E.symm σ h) = σ (E h) := fun h => by
    simp [MulAut.congr_apply]
  refine ⟨MulAut.congr E.symm σ, hσ₁E, fun h hh => ?_, ?_, ?_⟩
  · have h1 : E h ∈ T := (hTE _).mpr (by rwa [MulEquiv.symm_apply_apply])
    have h2 : σ (E h) ∈ T := by
      rw [← hσT]
      exact Subgroup.mem_map_of_mem σ.toMonoidHom h1
    rwa [← hσ₁E, hTE, MulEquiv.symm_apply_apply] at h2
  · obtain ⟨k, hk⟩ := hσ
    refine ⟨k, ?_⟩
    rw [← hk, ← MulEquiv.orderOf_eq (MulAut.congr E.symm) σ]
    exact pow_orderOf_eq_one _
  · obtain ⟨t₀, ht₀T, ht₀1, ht₀σ⟩ := ht₀
    obtain ⟨s₀, hs₀⟩ := (hTE t₀).mp ht₀T
    have hE : E (torusHom s₀) = t₀ := by rw [hs₀, MulEquiv.apply_symm_apply]
    refine ⟨s₀, fun h => ht₀1 ?_, E.injective ?_⟩
    · rw [← hE, h, map_one, map_one]
    · rw [hσ₁E, hE, ht₀σ]

private theorem tasp_pow_torusHom {K : Type} [Field K] {σ₁ : MulAut (StatedSp 2 K)}
    {φ : (Fin 2 → Kˣ) → Fin 2 → Kˣ} (hφ : ∀ t, σ₁ (torusHom t) = torusHom (φ t)) (j : ℕ)
    (t : Fin 2 → Kˣ) : (σ₁ ^ j) (torusHom t) = torusHom (φ^[j] t) := by
  induction j generalizing t with
  | zero => rw [pow_zero]; rfl
  | succ j ih => rw [pow_succ, MulAut.mul_apply, hφ, ih, Function.iterate_succ_apply]

private theorem tasp_transport {X : Type} [Group X] {K : Type} [Field K] {T : Subgroup X} {n : ℕ}
    {E : StatedSp 2 K ≃* X} (hTE : ∀ z, z ∈ T ↔ E.symm z ∈ torus 2 K) {σ : MulAut X}
    {φ : (Fin 2 → Kˣ) → Fin 2 → Kˣ} (hσE : ∀ t, σ (E (torusHom t)) = E (torusHom (φ t)))
    (hφ : (∀ t, φ t = t) ∨ ((∀ t, φ (φ t) = t) ∧
      ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ 2 ^ n - 1 → ∃ t, orderOf t = ℓ ∧ φ t = t⁻¹)) :
    (∀ x ∈ T, σ x = x) ∨ ((∀ x ∈ T, σ (σ x) = x) ∧
      ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ 2 ^ n - 1 → ∃ x ∈ T, orderOf x = ℓ ∧ σ x = x⁻¹) := by
  have hT : ∀ z ∈ T, ∃ t, E (torusHom t) = z := fun z hz => by
    obtain ⟨t, ht⟩ := (hTE z).mp hz
    exact ⟨t, by rw [ht, MulEquiv.apply_symm_apply]⟩
  rcases hφ with h1 | ⟨h2, hinv⟩
  · left
    intro z hz
    obtain ⟨t, rfl⟩ := hT z hz
    rw [hσE, h1]
  · right
    refine ⟨fun z hz => ?_, fun ℓ hp hdvd => ?_⟩
    · obtain ⟨t, rfl⟩ := hT z hz
      rw [hσE, hσE, h2]
    · obtain ⟨t, hto, htφ⟩ := hinv ℓ hp hdvd
      refine ⟨E (torusHom t), (hTE _).mpr ?_, ?_, ?_⟩
      · rw [MulEquiv.symm_apply_apply]
        exact torusHom_mem_torus t
      · rw [MulEquiv.orderOf_eq, orderOf_injective (torusHom (r := 2) (k := K))
          (torusHom_injective (r := 2) (k := K)), hto]
      · rw [hσE, htφ, map_inv, map_inv]

theorem k_19_28_torusAutomizer_sp4
    {X : Type} [Group X] [Finite X] {n : ℕ}
    (hn : 3 ≤ n) (hodd : Odd n) (hX : IsSp4 X n) {T : Subgroup X} (hT : IsZModSq T n)
    (σ : MulAut X) (hσ : ∃ k : ℕ, orderOf σ = 2 ^ k) (hσT : T.map σ.toMonoidHom = T)
    (ht₀ : ∃ t₀ ∈ T, t₀ ≠ 1 ∧ σ t₀ = t₀) :
    (∀ x ∈ T, σ x = x) ∨ ((∀ x ∈ T, σ (σ x) = x) ∧
      ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ 2 ^ n - 1 → ∃ x ∈ T, orderOf x = ℓ ∧ σ x = x⁻¹) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFour.exists_mulEquiv_statedSp_of_lieModel hX
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK
  have h3 : 3 ≤ Nat.card K := by
    rw [hK]
    calc 3 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨E, hTE⟩ := tasp_exists_equiv hK hn hodd e hT
  obtain ⟨σ₁, hσ₁E, hσ₁T, ⟨k, hk⟩, ⟨s₀, hs₀, hfix⟩⟩ := tasp_conj hTE σ hσ hσT ht₀
  obtain ⟨x, m, hx⟩ := tasp_normal_form σ₁
  obtain ⟨ε, δ, b, hε, hδ, hw⟩ :=
    exists_signedPerm_of_mem_normalizer_torus h3 (tasp_mem_normalizer hσ₁T hx)
  obtain ⟨φ, hφdef⟩ : ∃ φ : (Fin 2 → Kˣ) → Fin 2 → Kˣ, ∀ t, φ t =
      (fun s : Fin 2 → Kˣ => if b then ![s 1 ^ δ, s 0 ^ ε] else ![s 0 ^ ε, s 1 ^ δ])
        ((⇑(uc22pwI2Rho K))^[m] t) := ⟨_, fun _ => rfl⟩
  have hφ : ∀ t, σ₁ (torusHom t) = torusHom (φ t) := fun t => by
    rw [hφdef, hx, tasp_tau_pow_torusHom, hw]
  have hφk : φ^[2 ^ k] = id := funext fun t => torusHom_injective (by
    rw [← tasp_pow_torusHom hφ, hk]
    rfl)
  have hφs₀ : φ s₀ = s₀ := torusHom_injective ((hφ s₀).symm.trans hfix)
  exact tasp_transport hTE (fun t => by rw [← hσ₁E, hφ])
    (torusAutomizer_of_signedPerm_rho hK hn hodd ε δ b hε hδ m φ hφdef ⟨k, hφk⟩
      ⟨s₀, hs₀, hφs₀⟩)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

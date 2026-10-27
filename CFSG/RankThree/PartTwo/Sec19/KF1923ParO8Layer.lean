module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelCoordinates
import CFSG.ClassicalGroups.Orthogonal.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open QuadraticMap CFSG.ClassicalGroups.Orthogonal
open scoped Pointwise

local notation "𝔽₂" => GaloisField 2 1
local notation "𝕍" => (Fin 3 ⊕ Fin 3 → GaloisField 2 1) × (Fin 2 → GaloisField 2 1)

@[expose] noncomputable def kfO8Tail : QuadraticForm 𝔽₂ (Fin 2 → 𝔽₂) := minusTailForm 𝔽₂ 1 1

@[expose] noncomputable def kfO8Form : QuadraticForm 𝔽₂ 𝕍 := quadTail 3 kfO8Tail

@[expose] noncomputable def kfO8Flag : Submodule 𝔽₂ 𝕍 := tailFlag 𝔽₂ (Fin 2 → 𝔽₂) 3 3

theorem kfO8_mem_flag {v : 𝕍} : v ∈ kfO8Flag ↔ (∀ i, v.1 (Sum.inr i) = 0) ∧ v.2 = 0 := by
  constructor
  · intro hv
    unfold kfO8Flag tailFlag at hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, -, rfl⟩ := hx
      refine ⟨fun i => ?_, rfl⟩
      simp [hypVec]
    | zero => exact ⟨fun _ => rfl, rfl⟩
    | add x y _ _ hx hy => exact ⟨fun i => by simp [hx.1 i, hy.1 i], by simp [hx.2, hy.2]⟩
    | smul c x _ hx => exact ⟨fun i => by simp [hx.1 i], by simp [hx.2]⟩
  · rintro ⟨h1, h2⟩
    have : v = ∑ l : Fin 3, v.1 (Sum.inl l) • hypVec 𝔽₂ (Fin 2 → 𝔽₂) (Sum.inl l) := by
      refine Prod.ext (funext fun c => ?_) ?_
      · rcases c with k | k
        · simp [hypVec, Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
        · simp [hypVec, Prod.fst_sum, Finset.sum_apply, h1 k]
      · simp [hypVec, Prod.snd_sum, h2]
    rw [this]
    exact Submodule.sum_mem _ fun l _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, by simp, rfl⟩)

theorem kfO8_flag_expand {v : 𝕍} (hv : v ∈ kfO8Flag) :
    v = ∑ l : Fin 3, v.1 (Sum.inl l) • hypVec 𝔽₂ (Fin 2 → 𝔽₂) (Sum.inl l) := by
  obtain ⟨h1, h2⟩ := kfO8_mem_flag.1 hv
  refine Prod.ext (funext fun c => ?_) ?_
  · rcases c with k | k
    · simp [hypVec, Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
    · simp [hypVec, Prod.fst_sum, Finset.sum_apply, h1 k]
  · simp [hypVec, Prod.snd_sum, h2]

theorem kfO8_hypVec_mem_flag (l : Fin 3) :
    hypVec 𝔽₂ (Fin 2 → 𝔽₂) (Sum.inl l) ∈ kfO8Flag :=
  kfO8_mem_flag.2 ⟨fun i => by simp [hypVec], rfl⟩

theorem kfO8_forall_polar_flag_iff (v : 𝕍) :
    (∀ f ∈ kfO8Flag, polar kfO8Form v f = 0) ↔ ∀ i, v.1 (Sum.inr i) = 0 := by
  constructor
  · intro h i
    have := h _ (kfO8_hypVec_mem_flag i)
    rw [kfO8Form, polar_hypVec] at this
    exact this
  · intro h f hf
    rw [kfO8_flag_expand hf]
    rw [← QuadraticMap.polarBilin_apply_apply, map_sum]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [map_smul, QuadraticMap.polarBilin_apply_apply, kfO8Form, polar_hypVec]
    simp [h l]

@[expose] noncomputable def kfO8Gam : Subgroup (𝕍 ≃ₗ[𝔽₂] 𝕍) :=
  TauCeti.QuadraticMap.orthogonalGroup kfO8Form ⊓ MulAction.stabilizer (𝕍 ≃ₗ[𝔽₂] 𝕍) kfO8Flag

theorem mem_kfO8Gam {g : 𝕍 ≃ₗ[𝔽₂] 𝕍} : g ∈ kfO8Gam ↔
    g ∈ TauCeti.QuadraticMap.orthogonalGroup kfO8Form ∧
      kfO8Flag.map (g : 𝕍 →ₗ[𝔽₂] 𝕍) = kfO8Flag := by
  simp only [kfO8Gam, Subgroup.mem_inf, Submodule.mem_stabilizer_submodule_iff_map_eq]
  rfl

theorem kfO8_Gam_apply_mem {g : 𝕍 ≃ₗ[𝔽₂] 𝕍} (hg : g ∈ kfO8Gam) {f : 𝕍} (hf : f ∈ kfO8Flag) :
    g f ∈ kfO8Flag := by
  have := (mem_kfO8Gam.1 hg).2
  rw [← this]
  exact Submodule.mem_map_of_mem hf

theorem kfO8_Gam_symm_apply_mem {g : 𝕍 ≃ₗ[𝔽₂] 𝕍} (hg : g ∈ kfO8Gam) {f : 𝕍}
    (hf : f ∈ kfO8Flag) : g⁻¹ f ∈ kfO8Flag := by
  have h := (mem_kfO8Gam.1 hg).2
  rw [← h] at hf
  obtain ⟨f', hf', rfl⟩ := hf
  simpa using hf'

theorem kfO8_Gam_perp {g : 𝕍 ≃ₗ[𝔽₂] 𝕍} (hg : g ∈ kfO8Gam) {v : 𝕍}
    (hv : ∀ i, v.1 (Sum.inr i) = 0) : ∀ i, (g v).1 (Sum.inr i) = 0 := by
  rw [← kfO8_forall_polar_flag_iff] at hv ⊢
  intro f hf
  have h1 := kfO8_Gam_symm_apply_mem hg hf
  have h2 := polar_map_of_mem (mem_kfO8Gam.1 hg).1 v (g⁻¹ f)
  rw [show g (g⁻¹ f) = f from by simp] at h2
  rw [h2]
  exact hv _ h1

@[expose] noncomputable def kfO8_rho1 (g : 𝕍 ≃ₗ[𝔽₂] 𝕍) : Matrix (Fin 3) (Fin 3) 𝔽₂ :=
  Matrix.of fun i j => (g (hypVec 𝔽₂ (Fin 2 → 𝔽₂) (Sum.inl j))).1 (Sum.inl i)

theorem kfO8_rho1_one : kfO8_rho1 1 = 1 := by
  ext i j
  simp [kfO8_rho1, hypVec, Matrix.one_apply, Pi.single_apply]

theorem kfO8_rho1_mul {g h : 𝕍 ≃ₗ[𝔽₂] 𝕍} (hg : g ∈ kfO8Gam) (hh : h ∈ kfO8Gam) :
    kfO8_rho1 (g * h) = kfO8_rho1 g * kfO8_rho1 h := by
  ext i j
  have h1 := kfO8_Gam_apply_mem hh (kfO8_hypVec_mem_flag j)
  have h2 := kfO8_flag_expand h1
  have key : g (h (hypVec 𝔽₂ (Fin 2 → 𝔽₂) (Sum.inl j))) =
      ∑ l : Fin 3, ((h (hypVec 𝔽₂ (Fin 2 → 𝔽₂) (Sum.inl j))).1 (Sum.inl l)) •
        g (hypVec 𝔽₂ (Fin 2 → 𝔽₂) (Sum.inl l)) := by
    conv_lhs => rw [h2]
    simp [map_sum, map_smul]
  simp only [kfO8_rho1, Matrix.of_apply, Matrix.mul_apply, LinearEquiv.mul_apply]
  rw [key]
  simp only [Prod.fst_sum, Prod.smul_fst, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

@[expose] noncomputable def kfO8_rho2 (g : 𝕍 ≃ₗ[𝔽₂] 𝕍) : Matrix (Fin 2) (Fin 2) 𝔽₂ :=
  Matrix.of fun k l => (g (0, Pi.single l 1)).2 k

theorem kfO8_rho2_one : kfO8_rho2 1 = 1 := by
  ext k l
  simp [kfO8_rho2, Matrix.one_apply, Pi.single_apply, eq_comm]

theorem kfO8_Gam_snd_apply {g : 𝕍 ≃ₗ[𝔽₂] 𝕍} (hg : g ∈ kfO8Gam) {v : 𝕍}
    (hvp : ∀ i, v.1 (Sum.inr i) = 0) :
    (g v).2 = ∑ m : Fin 2, v.2 m • (g (0, Pi.single m 1)).2 := by
  have hvF : ((v.1, 0) : 𝕍) ∈ kfO8Flag := kfO8_mem_flag.2 ⟨hvp, rfl⟩
  have hsplit : v = (v.1, 0) + (0, v.2) := by simp
  have hexp : ((0 : Fin 3 ⊕ Fin 3 → 𝔽₂), v.2) =
      ∑ m : Fin 2, v.2 m • ((0 : Fin 3 ⊕ Fin 3 → 𝔽₂),
        (Pi.single m (1 : 𝔽₂) : Fin 2 → 𝔽₂)) := by
    refine Prod.ext (by simp [Prod.fst_sum]) ?_
    funext c
    fin_cases c <;> simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  have hgF : (g (v.1, 0)).2 = 0 := (kfO8_mem_flag.1 (kfO8_Gam_apply_mem hg hvF)).2
  have h0 : g v = g (v.1, 0) + ∑ m : Fin 2, v.2 m • g (0, Pi.single m 1) := by
    conv_lhs => rw [hsplit, map_add, hexp, map_sum]
    simp only [map_smul]
  rw [h0]
  simp [Prod.snd_add, Prod.snd_sum, hgF]

theorem kfO8_rho2_mul {g h : 𝕍 ≃ₗ[𝔽₂] 𝕍} (hg : g ∈ kfO8Gam) (hh : h ∈ kfO8Gam) :
    kfO8_rho2 (g * h) = kfO8_rho2 g * kfO8_rho2 h := by
  ext k l
  set v := h (0, Pi.single l 1) with hv
  have hvp : ∀ i, v.1 (Sum.inr i) = 0 := kfO8_Gam_perp hh (fun i => by simp)
  simp only [kfO8_rho2, Matrix.of_apply, Matrix.mul_apply, LinearEquiv.mul_apply]
  rw [← hv, kfO8_Gam_snd_apply hg hvp]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun m _ => mul_comm _ _

theorem kfO8_gf2_two : (2 : GaloisField 2 1) = 0 := by
  have := CharP.cast_eq_zero (GaloisField 2 1) 2
  simpa using this

theorem kfO8_gf2_add_self {M : Type*} [AddCommGroup M] [Module 𝔽₂ M] (w : M) : w + w = 0 := by
  rw [← two_smul 𝔽₂ w, kfO8_gf2_two, zero_smul]

theorem kfO8_eq_one_of_rho_eq_one {e : 𝕍 ≃ₗ[𝔽₂] 𝕍} (he : e ∈ kfO8Gam) (h3 : e ^ 3 = 1)
    (h1 : kfO8_rho1 e = 1) (h2 : kfO8_rho2 e = 1) : e = 1 := by
  have hj : ∀ j : Fin 3, e (hypVec 𝔽₂ (Fin 2 → 𝔽₂) (Sum.inl j)) =
      hypVec 𝔽₂ (Fin 2 → 𝔽₂) (Sum.inl j) := by
    intro j
    have hm := kfO8_Gam_apply_mem he (kfO8_hypVec_mem_flag j)
    conv_lhs => rw [kfO8_flag_expand hm]
    have hc : ∀ l : Fin 3, (e (hypVec 𝔽₂ (Fin 2 → 𝔽₂) (Sum.inl j))).1 (Sum.inl l) =
        if l = j then 1 else 0 := by
      intro l
      have := congrFun (congrFun (congrArg (fun M => M) h1) l) j
      simpa [kfO8_rho1, Matrix.one_apply] using this
    simp only [hc]
    simp [hypVec, Prod.fst_sum, Prod.snd_sum]
  have hF : ∀ f ∈ kfO8Flag, e f = f := by
    intro f hf
    conv_lhs => rw [kfO8_flag_expand hf]
    simp only [map_sum, map_smul, hj]
    exact (kfO8_flag_expand hf).symm
  have hP : ∀ v : 𝕍, (∀ i, v.1 (Sum.inr i) = 0) → e v - v ∈ kfO8Flag := by
    intro v hv
    have h2' : (e v).2 = v.2 := by
      rw [kfO8_Gam_snd_apply he hv]
      have hk : ∀ m : Fin 2, (e (0, Pi.single m 1)).2 = Pi.single m 1 := by
        intro m
        funext k
        have := congrFun (congrFun (congrArg (fun M => M) h2) k) m
        simpa [kfO8_rho2, Matrix.one_apply, Pi.single_apply, eq_comm] using this
      simp only [hk]
      funext c
      simp [Finset.sum_apply, Pi.single_apply]
    refine kfO8_mem_flag.2 ⟨fun i => ?_, ?_⟩
    · simp [kfO8_Gam_perp he hv i, hv i]
    · simp [h2']
  have hD : ∀ v : 𝕍, ∀ i, (e v - v).1 (Sum.inr i) = 0 := by
    intro v
    rw [← kfO8_forall_polar_flag_iff]
    intro f hf
    have h1' := polar_map_of_mem (mem_kfO8Gam.1 he).1 v f
    rw [hF f hf] at h1'
    rw [polar_sub_left, h1']
    exact sub_self _
  have hv : ∀ v : 𝕍, e v = v := by
    intro v
    set w := e v - v with hw
    have hwp := hD v
    set u := e w - w with hu
    have huF : u ∈ kfO8Flag := hP w hwp
    have h_ev : e v = v + w := by simp [hw]
    have h_ew : e w = w + u := by simp [hu]
    have h_eu : e u = u := hF u huF
    have h3v : e (e (e v)) = v := by
      have := congrArg (fun g : 𝕍 ≃ₗ[𝔽₂] 𝕍 => g v) h3
      simpa [pow_succ, LinearEquiv.mul_apply] using this
    have hw2 : w + w = 0 := kfO8_gf2_add_self w
    have hu2 : u + u = 0 := kfO8_gf2_add_self u
    have e1 : e (e v) = (v + w) + (w + u) := by rw [h_ev, map_add, h_ev, h_ew]
    have h_sum : e (e (e v)) = v + w + u := by
      rw [e1]
      simp only [map_add]
      rw [h_ev, h_ew, h_eu]
      have hh : v + w + (w + u) + (w + u + u) = v + (w + w) + w + (u + u) + u := by abel
      rw [hh, hw2, hu2]
      abel
    have hsum0 : w + u = 0 := by
      rw [h_sum] at h3v
      have : v + (w + u) = v + 0 := by rw [add_zero, ← add_assoc]; exact h3v
      exact add_left_cancel this
    have hue : u = w := by
      have : w + u = w + w := by rw [hsum0, hw2]
      exact add_left_cancel this
    have hew0 : e w = 0 := by rw [h_ew, hue, hw2]
    have hw0 : w = 0 := (e.map_eq_zero_iff).1 hew0
    rw [h_ev, hw0, add_zero]
  exact LinearEquiv.ext hv

theorem kfO8_invariant_eq {G : Type*} [Group G] {E K : Subgroup G} (hKE : K ≤ E)
    (hE3 : ∀ e ∈ E, e ^ 3 = 1) (hE9 : Nat.card E = 9) {t : G}
    (hinv : ∀ e ∈ E, t ^ 2 * e * (t ^ 2)⁻¹ = e⁻¹) (hK : ∀ k ∈ K, t * k * t⁻¹ ∈ K)
    (hK1 : K ≠ ⊥) : K = E := by
  by_contra hne
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hE9]; norm_num)
  haveI : Finite K :=
    Finite.of_injective (Subgroup.inclusion hKE) (Subgroup.inclusion_injective hKE)
  have hdvd : Nat.card K ∣ 3 ^ 2 := by
    have := hE9 ▸ Subgroup.card_dvd_of_le hKE
    simpa using this
  have hK3 : Nat.card K = 3 := by
    have h1 : Nat.card K ≠ 1 := fun h => hK1 (Subgroup.eq_bot_of_card_eq K h)
    have h9 : Nat.card K ≠ 9 := fun h =>
      hne (Subgroup.eq_of_le_of_card_ge hKE (by rw [h, hE9]))
    obtain ⟨i, hi, hKi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    interval_cases i
    · exact absurd (by simpa using hKi) h1
    · simpa using hKi
    · exact absurd (by simpa using hKi) h9
  obtain ⟨⟨k, hk⟩, hk1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hK1
  have hk1' : k ≠ 1 := fun h => hk1 (Subtype.ext h)
  have hkE : k ∈ E := hKE hk
  have hk3 : k ^ 3 = 1 := hE3 k hkE
  have hord : orderOf k = 3 := orderOf_eq_prime hk3 hk1'
  have hKz : K = Subgroup.zpowers k := by
    symm
    apply Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hk)
    rw [Nat.card_zpowers, hord, hK3]
  obtain ⟨n, hn⟩ : ∃ n : ℤ, k ^ n = t * k * t⁻¹ := by
    have := hK k hk
    rw [hKz] at this
    exact Subgroup.mem_zpowers_iff.1 this
  have hsq : t ^ 2 * k * (t ^ 2)⁻¹ = k ^ (n * n) := by
    have : t ^ 2 * k * (t ^ 2)⁻¹ = t * (t * k * t⁻¹) * t⁻¹ := by rw [pow_two]; group
    rw [this, ← hn]
    have hc : t * k ^ n * t⁻¹ = (t * k * t⁻¹) ^ n := by
      have := map_zpow (MulAut.conj t) k n
      simpa [MulAut.conj_apply] using this
    rw [hc, ← hn, ← zpow_mul]
  have h1 : k ^ (n * n) = k⁻¹ := by rw [← hsq]; exact hinv k hkE
  have h2 : k ^ (n * n + 1) = 1 := by rw [zpow_add_one, h1, inv_mul_cancel]
  have h3 : (3 : ℤ) ∣ n * n + 1 := by
    have := (orderOf_dvd_iff_zpow_eq_one (x := k) (i := n * n + 1)).2 h2
    rwa [hord] at this
  have h4 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h4 with h | h | h <;> simp [Int.dvd_iff_emod_eq_zero, Int.add_emod, Int.mul_emod, h] at h3

theorem kfO8_card_GL (n : ℕ) :
    Nat.card (Matrix.GeneralLinearGroup (Fin n) 𝔽₂) = ∏ i : Fin n, (2 ^ n - 2 ^ (i : ℕ)) := by
  haveI : Fintype 𝔽₂ := Fintype.ofFinite _
  have hq : Fintype.card 𝔽₂ = 2 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 1 one_ne_zero]; simp
  rw [Matrix.card_GL_field, hq]

theorem kfO8_not_nine_dvd_GL3 : ¬ 9 ∣ Nat.card (Matrix.GeneralLinearGroup (Fin 3) 𝔽₂) := by
  rw [kfO8_card_GL]; decide

theorem kfO8_not_nine_dvd_GL2 : ¬ 9 ∣ Nat.card (Matrix.GeneralLinearGroup (Fin 2) 𝔽₂) := by
  rw [kfO8_card_GL]; decide

theorem kfO8_ker_ne_bot {E : Type*} [Group E] [Finite E] (hE : Nat.card E = 9) {G : Type*}
    [Group G] [Finite G] (hG : ¬ 9 ∣ Nat.card G) (f : E →* G) : f.ker ≠ ⊥ := by
  intro h
  have h1 := Subgroup.card_ker_mul_card_range f
  rw [h, Subgroup.card_bot, one_mul, hE] at h1
  exact hG (h1 ▸ Subgroup.card_subgroup_dvd_card f.range)

@[expose] noncomputable def kfO8_rho1Hom : kfO8Gam →* Matrix (Fin 3) (Fin 3) 𝔽₂ where
  toFun g := kfO8_rho1 g.1
  map_one' := kfO8_rho1_one
  map_mul' g h := kfO8_rho1_mul g.2 h.2

@[expose] noncomputable def kfO8_rho2Hom : kfO8Gam →* Matrix (Fin 2) (Fin 2) 𝔽₂ where
  toFun g := kfO8_rho2 g.1
  map_one' := kfO8_rho2_one
  map_mul' g h := kfO8_rho2_mul g.2 h.2

theorem kfO8_layer (E : Subgroup (𝕍 ≃ₗ[𝔽₂] 𝕍)) (hEΓ : E ≤ kfO8Gam) (hE3 : ∀ e ∈ E, e ^ 3 = 1)
    (hE9 : Nat.card E = 9) (t : 𝕍 ≃ₗ[𝔽₂] 𝕍) (htΓ : t ∈ kfO8Gam)
    (htN : ∀ e ∈ E, t * e * t⁻¹ ∈ E) (hinv : ∀ e ∈ E, t ^ 2 * e * (t ^ 2)⁻¹ = e⁻¹) :
    False := by
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hE9]; norm_num)
  let r1 : E →* Matrix.GeneralLinearGroup (Fin 3) 𝔽₂ :=
    (kfO8_rho1Hom.comp (Subgroup.inclusion hEΓ)).toHomUnits
  let r2 : E →* Matrix.GeneralLinearGroup (Fin 2) 𝔽₂ :=
    (kfO8_rho2Hom.comp (Subgroup.inclusion hEΓ)).toHomUnits
  have hr1 : ∀ x : E, ((r1 x : Matrix.GeneralLinearGroup (Fin 3) 𝔽₂) :
      Matrix (Fin 3) (Fin 3) 𝔽₂) = kfO8_rho1 x.1 := fun x => rfl
  have hr2 : ∀ x : E, ((r2 x : Matrix.GeneralLinearGroup (Fin 2) 𝔽₂) :
      Matrix (Fin 2) (Fin 2) 𝔽₂) = kfO8_rho2 x.1 := fun x => rfl
  set K1 : Subgroup (𝕍 ≃ₗ[𝔽₂] 𝕍) := r1.ker.map E.subtype with hK1
  set K2 : Subgroup (𝕍 ≃ₗ[𝔽₂] 𝕍) := r2.ker.map E.subtype with hK2
  have hK1E : K1 ≤ E := Subgroup.map_subtype_le _
  have hK2E : K2 ≤ E := Subgroup.map_subtype_le _
  have hmem1 : ∀ e : 𝕍 ≃ₗ[𝔽₂] 𝕍, e ∈ K1 → e ∈ E ∧ kfO8_rho1 e = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨x.2, ?_⟩
    have := congrArg
      (fun u : Matrix.GeneralLinearGroup (Fin 3) 𝔽₂ => (u : Matrix (Fin 3) (Fin 3) 𝔽₂))
      (MonoidHom.mem_ker.1 hx)
    simpa [hr1] using this
  have hmem2 : ∀ e : 𝕍 ≃ₗ[𝔽₂] 𝕍, e ∈ K2 → e ∈ E ∧ kfO8_rho2 e = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨x.2, ?_⟩
    have := congrArg
      (fun u : Matrix.GeneralLinearGroup (Fin 2) 𝔽₂ => (u : Matrix (Fin 2) (Fin 2) 𝔽₂))
      (MonoidHom.mem_ker.1 hx)
    simpa [hr2] using this
  have hK1ne : K1 ≠ ⊥ := by
    intro h
    exact kfO8_ker_ne_bot hE9 kfO8_not_nine_dvd_GL3 r1
      ((Subgroup.map_eq_bot_iff_of_injective _ E.subtype_injective).1 h)
  have hK2ne : K2 ≠ ⊥ := by
    intro h
    exact kfO8_ker_ne_bot hE9 kfO8_not_nine_dvd_GL2 r2
      ((Subgroup.map_eq_bot_iff_of_injective _ E.subtype_injective).1 h)
  have htinv1 : ∀ k ∈ K1, t * k * t⁻¹ ∈ K1 := by
    intro k hk
    obtain ⟨hkE, hk1⟩ := hmem1 k hk
    have hkΓ : k ∈ kfO8Gam := hEΓ hkE
    refine ⟨⟨t * k * t⁻¹, htN k hkE⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    apply Units.ext
    rw [hr1]
    show kfO8_rho1 (t * k * t⁻¹) = 1
    rw [kfO8_rho1_mul (kfO8Gam.mul_mem htΓ hkΓ) (kfO8Gam.inv_mem htΓ),
      kfO8_rho1_mul htΓ hkΓ, hk1, mul_one,
      ← kfO8_rho1_mul htΓ (kfO8Gam.inv_mem htΓ), mul_inv_cancel, kfO8_rho1_one]
  have htinv2 : ∀ k ∈ K2, t * k * t⁻¹ ∈ K2 := by
    intro k hk
    obtain ⟨hkE, hk1⟩ := hmem2 k hk
    have hkΓ : k ∈ kfO8Gam := hEΓ hkE
    refine ⟨⟨t * k * t⁻¹, htN k hkE⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    apply Units.ext
    rw [hr2]
    show kfO8_rho2 (t * k * t⁻¹) = 1
    rw [kfO8_rho2_mul (kfO8Gam.mul_mem htΓ hkΓ) (kfO8Gam.inv_mem htΓ),
      kfO8_rho2_mul htΓ hkΓ, hk1, mul_one,
      ← kfO8_rho2_mul htΓ (kfO8Gam.inv_mem htΓ), mul_inv_cancel, kfO8_rho2_one]
  have e1 : K1 = E := kfO8_invariant_eq hK1E hE3 hE9 hinv htinv1 hK1ne
  have e2 : K2 = E := kfO8_invariant_eq hK2E hE3 hE9 hinv htinv2 hK2ne
  have hE1 : ∀ e ∈ E, e = 1 := by
    intro e he
    have h1 := (hmem1 e (e1 ▸ he)).2
    have h2 := (hmem2 e (e2 ▸ he)).2
    exact kfO8_eq_one_of_rho_eq_one (hEΓ he) (hE3 e he) h1 h2
  have hcard : Nat.card E = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun a b => Subtype.ext (by rw [hE1 a a.2, hE1 b b.2])⟩, ⟨1⟩⟩
  omega

end CFSG.RankThree.PartTwo.Late

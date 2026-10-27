module

public import CFSG.LocalAnalysis.SteinbergSFFullCenterFirstParabolic
public import CFSG.LocalAnalysis.SteinbergCDCentralTwoExtensionSquare

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace FullCenterTorus

open Subgroup GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open scoped Matrix Pointwise

section General

variable {G : Type*} [Group G]

theorem mem_of_telescope {Z U : Subgroup G} (hZ2 : ∀ z ∈ Z, z * z = 1) {a f : G} {m : ℕ}
    (hm : Odd m) (ham : a ^ m = 1) (hZa : ∀ z ∈ Z, a⁻¹ * z * a ∈ Z)
    (hZU : ∀ z ∈ Z, z⁻¹ * (a⁻¹ * z * a) ∈ U) (hf : f⁻¹ * (a⁻¹ * f * a) ∈ Z) :
    f⁻¹ * (a⁻¹ * f * a) ∈ U := by
  set μ := f⁻¹ * (a⁻¹ * f * a) with hμ
  have key : ∀ k : ℕ, ∃ c ∈ Z, (a ^ k)⁻¹ * f * a ^ k = f * c ∧ (μ ^ k)⁻¹ * c ∈ U := by
    intro k
    induction k with
    | zero => exact ⟨1, one_mem _, by simp, by simp⟩
    | succ k ih =>
      obtain ⟨c, hc, hck, hcU⟩ := ih
      refine ⟨μ * (a⁻¹ * c * a), mul_mem hf (hZa c hc), ?_, ?_⟩
      · rw [pow_succ, show (a ^ k * a)⁻¹ * f * (a ^ k * a) =
          a⁻¹ * ((a ^ k)⁻¹ * f * a ^ k) * a by group, hck, hμ]
        group
      · rw [pow_succ', show (μ * μ ^ k)⁻¹ * (μ * (a⁻¹ * c * a)) =
          (μ ^ k)⁻¹ * c * (c⁻¹ * (a⁻¹ * c * a)) by group]
        exact mul_mem hcU (hZU c hc)
  obtain ⟨c, -, hcm, hcU⟩ := key m
  rw [ham, inv_one, mul_one, one_mul] at hcm
  rw [mul_eq_left.mp hcm.symm, mul_one] at hcU
  obtain ⟨k, rfl⟩ := hm
  have hμ2 : μ * μ = 1 := hZ2 μ hf
  have e : μ ^ (2 * k + 1) = μ := by rw [pow_succ, pow_mul, sq, hμ2, one_pow, one_mul]
  rw [e] at hcU
  simpa using inv_mem hcU


theorem mem_of_mem_closure_delta {Hs E Z : Subgroup G} {j : G} (hEH : E ≤ Hs) (hZE : Z ≤ E)
    (hZc : ∀ x ∈ Hs, ∀ z ∈ Z, x * z = z * x)
    (hcomm : ∀ x ∈ Hs, ∀ y ∈ Hs, x⁻¹ * (y⁻¹ * x * y) ∈ Z)
    (hjE : ∀ e ∈ E, j⁻¹ * e * j ∈ E)
    (hδZ : ∀ z ∈ Z, ∃ w ∈ Z, w⁻¹ * (j⁻¹ * w * j) = z) {x : G}
    (hx : x ∈ closure {x : G | ∃ e ∈ E, x = e⁻¹ * (j⁻¹ * e * j)}) :
    ∃ e ∈ E, x = e⁻¹ * (j⁻¹ * e * j) := by
  have hδE : ∀ e ∈ E, e⁻¹ * (j⁻¹ * e * j) ∈ E := fun e he => mul_mem (inv_mem he) (hjE e he)
  have hδZmul : ∀ e ∈ E, ∀ w ∈ Z, (e * w)⁻¹ * (j⁻¹ * (e * w) * j) =
      e⁻¹ * (j⁻¹ * e * j) * (w⁻¹ * (j⁻¹ * w * j)) := by
    intro e he w hw
    have hc := hZc _ (hEH (hδE e he)) w⁻¹ (inv_mem hw)
    calc (e * w)⁻¹ * (j⁻¹ * (e * w) * j) = w⁻¹ * (e⁻¹ * (j⁻¹ * e * j)) * (j⁻¹ * w * j) := by
          group
      _ = e⁻¹ * (j⁻¹ * e * j) * w⁻¹ * (j⁻¹ * w * j) := by rw [← hc]
      _ = e⁻¹ * (j⁻¹ * e * j) * (w⁻¹ * (j⁻¹ * w * j)) := by group
  have habs : ∀ e ∈ E, ∀ c ∈ Z, ∃ e' ∈ E, e⁻¹ * (j⁻¹ * e * j) * c = e'⁻¹ * (j⁻¹ * e' * j) := by
    intro e he c hc
    obtain ⟨w, hw, rfl⟩ := hδZ c hc
    exact ⟨e * w, mul_mem he (hZE hw), (hδZmul e he w hw).symm⟩
  refine closure_induction (p := fun x _ => ∃ e ∈ E, x = e⁻¹ * (j⁻¹ * e * j))
    (fun x hx => hx) ⟨1, one_mem _, by group⟩ ?_ ?_ hx
  · rintro _ _ _ _ ⟨e, he, rfl⟩ ⟨f, hf, rfl⟩
    set c := (e⁻¹ * (j⁻¹ * e * j))⁻¹ * (f⁻¹ * (e⁻¹ * (j⁻¹ * e * j)) * f) with hcdef
    have hc : c ∈ Z := hcomm _ (hEH (hδE e he)) _ (hEH hf)
    have hcc := hZc _ (hEH (hδE f hf)) c hc
    have e1 : (e * f)⁻¹ * (j⁻¹ * (e * f) * j) =
        e⁻¹ * (j⁻¹ * e * j) * (f⁻¹ * (j⁻¹ * f * j)) * c := by
      calc (e * f)⁻¹ * (j⁻¹ * (e * f) * j)
          = e⁻¹ * (j⁻¹ * e * j) * c * (f⁻¹ * (j⁻¹ * f * j)) := by rw [hcdef]; group
        _ = e⁻¹ * (j⁻¹ * e * j) * (f⁻¹ * (j⁻¹ * f * j)) * c := by rw [mul_assoc _ c, ← hcc,
            ← mul_assoc]
    obtain ⟨e', he', he'eq⟩ := habs (e * f) (mul_mem he hf) c⁻¹ (inv_mem hc)
    refine ⟨e', he', ?_⟩
    rw [← he'eq, e1, mul_inv_cancel_right]
  · rintro _ _ ⟨e, he, rfl⟩
    set d := e * (j⁻¹ * e⁻¹ * j) with hddef
    have hd : d ∈ E := by
      have := hδE e⁻¹ (inv_mem he)
      rwa [inv_inv] at this
    have hc : d⁻¹ * (e⁻¹ * d * e) ∈ Z := hcomm _ (hEH hd) _ (hEH he)
    obtain ⟨e', he', he'eq⟩ := habs e⁻¹ (inv_mem he) _ hc
    refine ⟨e', he', ?_⟩
    rw [← he'eq, inv_inv, hddef]
    group


theorem exists_conj_eq_of_card [Finite G] {X U : Subgroup G} {t : G}
    (hU : ∀ x ∈ X, t⁻¹ * (x⁻¹ * t * x) ∈ U)
    (hcard : Nat.card X = Nat.card U * Nat.card (centralizer ({t} : Set G) ⊓ X : Subgroup G))
    {u : G} (hu : u ∈ U) : ∃ x ∈ X, t⁻¹ * (x⁻¹ * t * x) = u := by
  have hsub : {y : G | ∃ x ∈ X, y = x⁻¹ * t * x} ⊆ {y | ∃ u ∈ U, y = t * u} := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨_, hU x hx, by group⟩
  have h1 := relIndex_mul_card (centralizer ({t} : Set G)) X
  rw [relIndex_centralizer_eq_card, hcard] at h1
  have hpos : 0 < Nat.card (centralizer ({t} : Set G) ⊓ X : Subgroup G) := Nat.card_pos
  have h2 := Nat.eq_of_mul_eq_mul_right hpos h1
  have heq : {y : G | ∃ x ∈ X, y = x⁻¹ * t * x} = {y | ∃ u ∈ U, y = t * u} := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, h2, card_mul_set]
  have hmem : t * u ∈ {y : G | ∃ x ∈ X, y = x⁻¹ * t * x} := by
    rw [heq]
    exact ⟨u, hu, rfl⟩
  obtain ⟨x, hx, hxu⟩ := hmem
  exact ⟨x, hx, by rw [← hxu, inv_mul_cancel_left]⟩


theorem card_eq_of_conj_surj [Finite G] {X U : Subgroup G} {t : G}
    (hU : ∀ x ∈ X, t⁻¹ * (x⁻¹ * t * x) ∈ U)
    (hsurj : ∀ u ∈ U, ∃ x ∈ X, t⁻¹ * (x⁻¹ * t * x) = u) :
    Nat.card X = Nat.card U * Nat.card (centralizer ({t} : Set G) ⊓ X : Subgroup G) := by
  have horb : {y : G | ∃ x ∈ X, y = x⁻¹ * t * x} = {y | ∃ u ∈ U, y = t * u} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, hU x hx, by group⟩
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨x, hx, hxu⟩ := hsurj u hu
      exact ⟨x, hx, by rw [← hxu, mul_inv_cancel_left]⟩
  have h1 := relIndex_mul_card (centralizer ({t} : Set G)) X
  rw [relIndex_centralizer_eq_card, horb, card_mul_set] at h1
  exact h1.symm

end General


section Torus

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  {φ : L ≃* antiSp K}

@[expose] def zc (φ : L ≃* antiSp K) (b c : K) : G := ((φ.symm (uElt 0 b c 0) : L) : G)

theorem zc_mul (b c b' c' : K) : zc φ b c * zc φ b' c' = zc φ (b + b') (c + c') := by
  have e : uElt 0 b c 0 * uElt 0 b' c' 0 = uElt (0 : K) (b + b') (c + c') 0 := by
    rw [uElt_mul]
    congr 1 <;> ring
  rw [zc, zc, zc, ← coe_mul, ← map_mul, e]

theorem zc_mem (b c : K) : zc φ b c ∈ pull φ (antiUnipotentCenter K) :=
  symm_mem_pull.mpr ⟨b, c, rfl⟩

theorem exists_zc {z : G} (hz : z ∈ pull φ (antiUnipotentCenter K)) : ∃ b c, zc φ b c = z := by
  obtain ⟨w, ⟨b, c, rfl⟩, rfl⟩ := exists_eq_symm_of_mem_pull hz
  exact ⟨b, c, rfl⟩

theorem zc_inj {b c b' c' : K} (e : zc φ b c = zc φ b' c') : b = b' ∧ c = c' := by
  have := uElt_inj (φ.symm.injective (Subtype.ext e))
  exact ⟨this.2.1, this.2.2.1⟩

theorem zc_zero : zc φ (0 : K) 0 = 1 := by
  rw [zc, uElt_zero_eq_one, map_one]
  rfl

theorem zc_inv (b c : K) : (zc φ b c)⁻¹ = zc φ b c := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [zc_mul, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, zc_zero]

theorem coordG_one_eq [Finite K] (b : K) : coordG φ Axis.one b = zc φ b 0 := rfl

theorem coordG_two_eq [Finite K] (c : K) : coordG φ Axis.two c = zc φ 0 c := rfl

theorem zc_mem_U_one {b c : K} : zc φ b c ∈ pull φ (rootU K Axis.one) ↔ c = 0 := by
  rw [zc, symm_mem_pull]
  constructor
  · rintro ⟨b', h⟩
    exact (uElt_inj h).2.2.1
  · rintro rfl
    exact ⟨b, rfl⟩

theorem zc_mem_U_two {b c : K} : zc φ b c ∈ pull φ (rootU K Axis.two) ↔ b = 0 := by
  rw [zc, symm_mem_pull]
  constructor
  · rintro ⟨c', h⟩
    exact (uElt_inj h).2.1
  · rintro rfl
    exact ⟨c, rfl⟩

theorem conj_zc {δ : antiSp K} {r s : K} (hr : r ≠ 0) (hs : s ≠ 0)
    (hδ : glMat (δ : GL (Fin 4) K) = diagMat r s) (b c : K) :
    ((φ.symm δ : L) : G)⁻¹ * zc φ b c * ((φ.symm δ : L) : G) = zc φ (r * s * b) (r ^ 2 * c) := by
  have e : δ⁻¹ * uElt 0 b c 0 * δ = uElt 0 (r * s * b) (r ^ 2 * c) 0 := by
    rw [diagTorus_conj hr hs hδ]
    congr 1 <;> ring
  exact Setup.symm_conj e

theorem exists_conj_zc {j : G} (hj : j ∈ pull φ (diagTorus K)) :
    ∃ r s : K, r ≠ 0 ∧ s ≠ 0 ∧ ∀ b c : K, j⁻¹ * zc φ b c * j = zc φ (r * s * b) (r ^ 2 * c) := by
  obtain ⟨δ, ⟨r, s, hr, hs, hδ⟩, rfl⟩ := exists_eq_symm_of_mem_pull hj
  exact ⟨r, s, hr, hs, conj_zc hr hs hδ⟩

omit [CharP K 2] in
theorem diagMat_pow (r s : K) (m : ℕ) : diagMat r s ^ m = diagMat (r ^ m) (s ^ m) := by
  induction m with
  | zero => rw [pow_zero, pow_zero, pow_zero, diagMat_one]
  | succ m ih => rw [pow_succ, ih, diagMat_mul_diagMat, pow_succ, pow_succ]

omit [CharP K 2] in
theorem torus_comm {j j' : G} (hj : j ∈ pull φ (diagTorus K)) (hj' : j' ∈ pull φ (diagTorus K)) :
    j * j' = j' * j := by
  obtain ⟨δ, ⟨r, s, -, -, hδ⟩, rfl⟩ := exists_eq_symm_of_mem_pull hj
  obtain ⟨δ', ⟨r', s', -, -, hδ'⟩, rfl⟩ := exists_eq_symm_of_mem_pull hj'
  have e : δ * δ' = δ' * δ := by
    apply antiSp_ext
    change glMat (δ : GL (Fin 4) K) * glMat (δ' : GL (Fin 4) K) =
      glMat (δ' : GL (Fin 4) K) * glMat (δ : GL (Fin 4) K)
    rw [hδ, hδ', diagMat_mul_diagMat, diagMat_mul_diagMat, mul_comm r, mul_comm s]
  rw [← coe_mul, ← coe_mul, ← map_mul, ← map_mul, e]

omit [CharP K 2] in
theorem torus_pow_card_sub_one [Finite K] {j : G} (hj : j ∈ pull φ (diagTorus K)) :
    j ^ (Nat.card K - 1) = 1 := by
  obtain ⟨δ, ⟨r, s, hr, hs, hδ⟩, rfl⟩ := exists_eq_symm_of_mem_pull hj
  have := Fintype.ofFinite K
  have e : δ ^ (Nat.card K - 1) = 1 := by
    apply antiSp_ext
    change ((δ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) ^ (Nat.card K - 1) = 1
    rw [show ((δ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = diagMat r s from hδ, diagMat_pow,
      Nat.card_eq_fintype_card, FiniteField.pow_card_sub_one_eq_one r hr,
      FiniteField.pow_card_sub_one_eq_one s hs, diagMat_one]
  rw [← SubgroupClass.coe_pow, ← map_pow, e, map_one]
  rfl


omit [CharP K 2] in
theorem glMat_inv_eq {δ : antiSp K} {r s : K} (hr : r ≠ 0) (hs : s ≠ 0)
    (hδ : glMat (δ : GL (Fin 4) K) = diagMat r s) :
    glMat ((δ⁻¹ : antiSp K) : GL (Fin 4) K) = diagMat r⁻¹ s⁻¹ := by
  have h1 : glMat ((δ⁻¹ : antiSp K) : GL (Fin 4) K) * glMat (δ : GL (Fin 4) K) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
    rfl
  have h2 : diagMat r s * diagMat r⁻¹ s⁻¹ = 1 := by
    rw [diagMat_mul_diagMat, mul_inv_cancel₀ hr, mul_inv_cancel₀ hs, diagMat_one]
  calc glMat ((δ⁻¹ : antiSp K) : GL (Fin 4) K)
      = glMat ((δ⁻¹ : antiSp K) : GL (Fin 4) K) * (diagMat r s * diagMat r⁻¹ s⁻¹) := by
        rw [h2, Matrix.mul_one]
    _ = diagMat r⁻¹ s⁻¹ := by rw [← Matrix.mul_assoc, ← hδ, h1, Matrix.one_mul]

omit [CharP K 2] in
variable (K) in
@[expose] def axisTorus : Axis → Subgroup (antiSp K)
  | .one =>
    { carrier := {g | ∃ r : K, r ≠ 0 ∧ glMat (g : GL (Fin 4) K) = diagMat r r⁻¹}
      one_mem' := ⟨1, one_ne_zero, by rw [inv_one, diagMat_one]; rfl⟩
      mul_mem' := by
        rintro g g' ⟨r, hr, hg⟩ ⟨r', hr', hg'⟩
        refine ⟨r * r', mul_ne_zero hr hr', ?_⟩
        change glMat (g : GL (Fin 4) K) * glMat (g' : GL (Fin 4) K) = _
        rw [hg, hg', diagMat_mul_diagMat, mul_inv]
      inv_mem' := by
        rintro g ⟨r, hr, hg⟩
        exact ⟨r⁻¹, inv_ne_zero hr, glMat_inv_eq hr (inv_ne_zero hr) hg⟩ }
  | .two =>
    { carrier := {g | ∃ s : K, s ≠ 0 ∧ glMat (g : GL (Fin 4) K) = diagMat 1 s}
      one_mem' := ⟨1, one_ne_zero, by rw [diagMat_one]; rfl⟩
      mul_mem' := by
        rintro g g' ⟨s, hs, hg⟩ ⟨s', hs', hg'⟩
        refine ⟨s * s', mul_ne_zero hs hs', ?_⟩
        change glMat (g : GL (Fin 4) K) * glMat (g' : GL (Fin 4) K) = _
        rw [hg, hg', diagMat_mul_diagMat, one_mul]
      inv_mem' := by
        rintro g ⟨s, hs, hg⟩
        refine ⟨s⁻¹, inv_ne_zero hs, ?_⟩
        rw [glMat_inv_eq one_ne_zero hs hg, inv_one] }

omit [CharP K 2] in
theorem axisTorus_le (i : Axis) : axisTorus K i ≤ diagTorus K := by
  cases i
  · rintro g ⟨r, hr, hg⟩
    exact ⟨r, r⁻¹, hr, inv_ne_zero hr, hg⟩
  · rintro g ⟨s, hs, hg⟩
    exact ⟨1, s, one_ne_zero, hs, hg⟩

theorem axisTorus_cent [Finite K] (i : Axis) {j : G} (hj : j ∈ pull φ (axisTorus K i)) {u : G}
    (hu : u ∈ pull φ (rootU K i)) : j⁻¹ * u * j = u := by
  obtain ⟨x, rfl⟩ := exists_coordG_eq φ i hu
  cases i
  · obtain ⟨δ, ⟨r, hr, hδ⟩, rfl⟩ := exists_eq_symm_of_mem_pull hj
    rw [coordG_one_eq, conj_zc hr (inv_ne_zero hr) hδ, mul_inv_cancel₀ hr, one_mul, mul_zero]
  · obtain ⟨δ, ⟨s, hs, hδ⟩, rfl⟩ := exists_eq_symm_of_mem_pull hj
    rw [coordG_two_eq, conj_zc one_ne_zero hs hδ]
    simp only [one_pow, one_mul, mul_zero]

theorem axisTorus_mod (i : Axis) {j : G} (hj : j ∈ pull φ (axisTorus K i)) {z : G}
    (hz : z ∈ pull φ (antiUnipotentCenter K)) :
    z⁻¹ * (j⁻¹ * z * j) ∈ pull φ (rootU K i.swap) := by
  obtain ⟨b, c, rfl⟩ := exists_zc hz
  cases i
  · obtain ⟨δ, ⟨r, hr, hδ⟩, rfl⟩ := exists_eq_symm_of_mem_pull hj
    rw [conj_zc hr (inv_ne_zero hr) hδ, zc_inv, zc_mul]
    exact zc_mem_U_two.mpr (by rw [mul_inv_cancel₀ hr, one_mul, CharTwo.add_self_eq_zero])
  · obtain ⟨δ, ⟨s, hs, hδ⟩, rfl⟩ := exists_eq_symm_of_mem_pull hj
    rw [conj_zc one_ne_zero hs hδ, zc_inv, zc_mul]
    exact zc_mem_U_one.mpr (by rw [one_pow, one_mul, CharTwo.add_self_eq_zero])

theorem U_inf_U : pull φ (rootU K Axis.one) ⊓ pull φ (rootU K Axis.two) = (⊥ : Subgroup G) := by
  rw [← pull_inf, rootU_inf, pull_bot]

theorem U_inf_U_swap (i : Axis) :
    pull φ (rootU K i) ⊓ pull φ (rootU K i.swap) = (⊥ : Subgroup G) := by
  cases i
  · exact U_inf_U
  · rw [inf_comm]
    exact U_inf_U

omit [CharP K 2] in
theorem exists_diagHom (f g : Kˣ →* Kˣ) :
    ∃ τ : Kˣ →* antiSp K, ∀ l, glMat (τ l : GL (Fin 4) K) = diagMat (f l : K) (g l : K) := by
  choose δ hδ using fun l : Kˣ => exists_diagTorus (K := K) (f l).ne_zero (g l).ne_zero
  refine ⟨{ toFun := δ, map_one' := ?_, map_mul' := fun l l' => ?_ }, fun l => (hδ l).2⟩
  · apply antiSp_ext
    rw [(hδ 1).2, map_one, map_one, Units.val_one, diagMat_one]
    rfl
  · apply antiSp_ext
    change _ = glMat (δ l : GL (Fin 4) K) * glMat (δ l' : GL (Fin 4) K)
    rw [(hδ _).2, (hδ l).2, (hδ l').2, diagMat_mul_diagMat, map_mul, map_mul, Units.val_mul,
      Units.val_mul]


end Torus

section Kappa

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

local notation "𝐏" => pull φ (antiUnipotent K)
local notation "𝐐" => (pull φ (antiUnipotent K) ⊔ zpowers t : Subgroup G)
local notation "𝐙" => pull φ (antiUnipotentCenter K)
local notation "𝐁[" i "]" => (zpowers t ⊔ pull φ (rootA K i) : Subgroup G)
local notation "𝐀[" i "]" => pull φ (rootA K i)
local notation "𝐔[" i "]" => pull φ (rootU K i)
local notation "𝐍[" i "]" => normalizer (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) :
  Subgroup G) : Set G)
local notation "𝐌[" i "]" => normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) :
  Subgroup G) : Set G)
set_option quotPrecheck false in
local notation "𝐃[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐐[" i "]" => (pull φ (antiUnipotent K) ⊔ zpowers t ⊔ 𝐃[i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐑[" i "]" => (pull φ (antiUnipotent K) ⊔ zpowers t ⊔ 𝐄[i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐇" => (𝐐[Axis.one] ⊔ 𝐐[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐄₀" => (𝐄[Axis.one] ⊓ 𝐄[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐂" => centralizer ({t} : Set G)
local notation "𝐉" => pull φ (diagTorus K)
set_option quotPrecheck false in
local notation "𝐅" => closure {x : G | ∃ e ∈ 𝐄₀, ∃ j ∈ pull φ (diagTorus K),
  x = e⁻¹ * (j⁻¹ * e * j)}
local notation "𝐉[" i "]" => pull φ (axisTorus K i)
set_option quotPrecheck false in
local notation "𝐖[" i "]" => (𝐅 ⊓ centralizer (𝐉[i] : Set G) : Subgroup G)

omit [Finite G] [Finite K] in
theorem Q_le_H : 𝐐 ≤ 𝐇 := le_sup_left.trans le_sup_left

omit [Finite G] [Finite K] in
theorem t_mem_H : t ∈ 𝐇 := Q_le_H (mem_sup_right (mem_zpowers t))

omit [Finite G] [Finite K] in
theorem ZP_le_H : 𝐙 ≤ 𝐇 := fun _ hz => Q_le_H (mem_sup_left (Setup.ZP_le_PG hz))

theorem comm_ZP (h : FCHyp L K n φ t) {x : G} (hx : x ∈ 𝐇) {z : G} (hz : z ∈ 𝐙) :
    x * z = z * x :=
  FCHyp.comm_ZP_of (fun _ hu => h.H_centralizes_U Axis.one hx hu)
    (fun _ hu => h.H_centralizes_U Axis.two hx hu) hz

theorem commutator_mem_ZP (h : FCHyp L K n φ t) {x y : G} (hx : x ∈ 𝐇) (hy : y ∈ 𝐇) :
    x⁻¹ * (y⁻¹ * x * y) ∈ 𝐙 :=
  closure_sq_H h ▸ commutator_mem_closure_sq hx hy

theorem kappa_mem (h : FCHyp L K n φ t) {x : G} (hx : x ∈ 𝐇) : t⁻¹ * (x⁻¹ * t * x) ∈ 𝐙 :=
  commutator_mem_ZP h t_mem_H hx

theorem kappa_mul (h : FCHyp L K n φ t) {x y : G} (hx : x ∈ 𝐇) (hy : y ∈ 𝐇) :
    t⁻¹ * ((x * y)⁻¹ * t * (x * y)) = t⁻¹ * (x⁻¹ * t * x) * (t⁻¹ * (y⁻¹ * t * y)) := by
  have hkx := kappa_mem h hx
  have hky := kappa_mem h hy
  have h1 : y⁻¹ * (t⁻¹ * (x⁻¹ * t * x)) * y = t⁻¹ * (x⁻¹ * t * x) := by
    rw [mul_assoc, ← comm_ZP h hy hkx, inv_mul_cancel_left]
  have h2 := comm_ZP h (ZP_le_H hky) hkx
  calc t⁻¹ * ((x * y)⁻¹ * t * (x * y))
      = t⁻¹ * (y⁻¹ * t * y) * (y⁻¹ * (t⁻¹ * (x⁻¹ * t * x)) * y) := by group
    _ = t⁻¹ * (x⁻¹ * t * x) * (t⁻¹ * (y⁻¹ * t * y)) := by rw [h1, h2]

omit [Finite G] [Finite K] [CharP K 2] in
theorem kappa_eq_one_iff {x : G} : t⁻¹ * (x⁻¹ * t * x) = 1 ↔ x ∈ 𝐂 := by
  rw [inv_mul_eq_one, mem_centralizer_singleton_iff]
  constructor
  · intro e
    calc x * t = x * (x⁻¹ * t * x) := by rw [← e]
      _ = t * x := by group
  · intro e
    rw [mul_assoc, ← e, inv_mul_cancel_left]

theorem t_mem_E (h : FCHyp L K n φ t) (i : Axis) : t ∈ 𝐄[i] :=
  h.D_le_E i (h.B_le_D i (mem_sup_left (mem_zpowers t)))

omit [Finite G] [Finite K] in
theorem ZP_le_B (i : Axis) : 𝐙 ≤ 𝐁[i] :=
  (pull_mono φ (center_le_rootA i)).trans le_sup_right

theorem t_mem_E0 (h : FCHyp L K n φ t) : t ∈ 𝐄₀ := ⟨t_mem_E h _, t_mem_E h _⟩

theorem ZP_le_E0 (h : FCHyp L K n φ t) : 𝐙 ≤ 𝐄₀ := fun _ hz =>
  ⟨h.D_le_E _ (h.B_le_D _ (ZP_le_B _ hz)), h.D_le_E _ (h.B_le_D _ (ZP_le_B _ hz))⟩

theorem E0_le_H (h : FCHyp L K n φ t) : 𝐄₀ ≤ 𝐇 := by
  rw [← R_inf_R h]
  exact inf_le_inf le_sup_right le_sup_right

theorem conj_mem_Hi (h : FCHyp L K n φ t) (i : Axis) {x : G} (hx : x ∈ 𝐇) {e : G}
    (he : e ∈ 𝐇 ⊓ 𝐄[i]) : x * e * x⁻¹ ∈ 𝐇 ⊓ 𝐄[i] :=
  mem_inf.mpr ⟨mul_mem (mul_mem hx (mem_inf.mp he).1) (inv_mem hx),
    conj_mem_E h i (H_le_R h i hx) (mem_inf.mp he).2⟩

theorem H_le_normalizer_Hi (h : FCHyp L K n φ t) (i : Axis) :
    𝐇 ≤ normalizer ((𝐇 ⊓ 𝐄[i] : Subgroup G) : Set G) := fun _ hx =>
  RootAxisTwoCore.mem_normalizer_of_conj_le fun _ he => conj_mem_Hi h i hx he

theorem D_le_Hi (h : FCHyp L K n φ t) (i : Axis) : 𝐃[i] ≤ 𝐇 ⊓ 𝐄[i] :=
  le_inf (D_le_H i) (h.D_le_E i)

theorem Hi_sup_Hi (h : FCHyp L K n φ t) : (𝐇 ⊓ 𝐄[Axis.one]) ⊔ (𝐇 ⊓ 𝐄[Axis.two]) = 𝐇 := by
  refine le_antisymm (sup_le inf_le_left inf_le_left) ?_
  have hQ : 𝐐 ≤ (𝐇 ⊓ 𝐄[Axis.one]) ⊔ (𝐇 ⊓ 𝐄[Axis.two]) :=
    (B_sup_B_eq_Q (φ := φ) (t := t)).symm.le.trans
      (sup_le_sup ((h.B_le_D _).trans (D_le_Hi h _)) ((h.B_le_D _).trans (D_le_Hi h _)))
  exact sup_le (sup_le hQ ((D_le_Hi h _).trans le_sup_left))
    (sup_le hQ ((D_le_Hi h _).trans le_sup_right))

theorem Hi_inf_Hi (h : FCHyp L K n φ t) : (𝐇 ⊓ 𝐄[Axis.one]) ⊓ (𝐇 ⊓ 𝐄[Axis.two]) = 𝐄₀ := by
  refine le_antisymm (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))
    (le_inf (le_inf (E0_le_H h) inf_le_left) (le_inf (E0_le_H h) inf_le_right))

theorem card_E0 (h : FCHyp L K n φ t) : Nat.card 𝐄₀ = 2 * Nat.card K ^ 4 := by
  have h1 := card_sup_mul_card_inf (𝐇 ⊓ 𝐄[Axis.one]) (𝐇 ⊓ 𝐄[Axis.two])
    (inf_le_left.trans (H_le_normalizer_Hi h _))
  rw [Hi_sup_Hi h, Hi_inf_Hi h, h.H_facts.2.2, card_Hi h, card_Hi h] at h1
  have hq : 0 < 2 * Nat.card K ^ 6 := by have : 0 < Nat.card K := Nat.card_pos; positivity
  have h2 : 2 * Nat.card K ^ 6 * Nat.card 𝐄₀ = 2 * Nat.card K ^ 6 * (2 * Nat.card K ^ 4) := by
    rw [h1]; ring
  exact Nat.eq_of_mul_eq_mul_left hq h2

omit [Finite G] [Finite K] in
theorem B_inf_B (h : FCHyp L K n φ t) : 𝐁[Axis.one] ⊓ 𝐁[Axis.two] = zpowers t ⊔ 𝐙 := by
  apply le_antisymm
  · intro x hx
    rcases mem_ZP_of_mem_B_inf_B h hx.1 hx.2 with h1 | h1
    · exact mem_sup_right h1
    · have e : x = t * (t * x) := by rw [← mul_assoc, h.setup.t_mul_t, one_mul]
      rw [e]
      exact mul_mem (mem_sup_left (mem_zpowers t)) (mem_sup_right h1)
  · exact sup_le (le_inf le_sup_left le_sup_left) (le_inf (ZP_le_B _) (ZP_le_B _))

theorem E0_inf_Q (h : FCHyp L K n φ t) : 𝐄₀ ⊓ 𝐐 = zpowers t ⊔ 𝐙 := by
  rw [← B_inf_B h]
  apply le_antisymm
  · intro x hx
    have h1 : x ∈ 𝐐 ⊓ 𝐄[Axis.one] := mem_inf.mpr ⟨(mem_inf.mp hx).2, (mem_inf.mp hx).1.1⟩
    have h2 : x ∈ 𝐐 ⊓ 𝐄[Axis.two] := mem_inf.mpr ⟨(mem_inf.mp hx).2, (mem_inf.mp hx).1.2⟩
    rw [Q_inf_E h] at h1 h2
    exact mem_inf.mpr ⟨h1, h2⟩
  · intro x hx
    obtain ⟨h1, h2⟩ := mem_inf.mp hx
    exact mem_inf.mpr ⟨⟨h.D_le_E _ (h.B_le_D _ h1), h.D_le_E _ (h.B_le_D _ h2)⟩,
      FCHyp.B_le_Q _ h1⟩

theorem E0_inf_C (h : FCHyp L K n φ t) : 𝐄₀ ⊓ 𝐂 = zpowers t ⊔ 𝐙 := by
  rw [← E0_inf_Q h]
  apply le_antisymm
  · intro x hx
    refine ⟨hx.1, ?_⟩
    rw [← h.H_inf_C]
    exact ⟨E0_le_H h hx.1, hx.2⟩
  · exact inf_le_inf_left _ h.setup.Q_le_C

omit [Finite G] [Finite K] in
theorem zpowers_inf_ZP (h : FCHyp L K n φ t) : zpowers t ⊓ 𝐙 = ⊥ :=
  h.twoCore.zpowers_inf (pull_le φ _)

theorem card_tZ (h : FCHyp L K n φ t) : Nat.card (zpowers t ⊔ 𝐙 : Subgroup G) =
    2 * Nat.card K ^ 2 := by
  rw [card_sup_of_commute (fun y hy z hz => h.twoCore.zpowers_comm hy (pull_le φ _ hz))
    (zpowers_inf_ZP h), Nat.card_zpowers, h.setup.order_t, FCHyp.card_ZP]

omit [Finite K] in
theorem center_Q (h : FCHyp L K n φ t) : (center 𝐐).map 𝐐.subtype = zpowers t ⊔ 𝐙 := by
  apply le_antisymm
  · intro x hx
    obtain ⟨z, hz, c, hc, rfl⟩ := h.setup.exists_of_mem_ZQ hx
    rw [sup_comm]
    exact mul_mem (mem_sup_left hz) (mem_sup_right hc)
  · refine sup_le ?_ fun z hz => ?_
    · rw [zpowers_le]
      simpa using Setup.mul_mem_ZQ h.setup (one_mem 𝐙) (mem_zpowers t)
    · simpa using Setup.mul_mem_ZQ h.setup hz (one_mem (zpowers t))

theorem exists_kappa_eq (h : FCHyp L K n φ t) {z : G} (hz : z ∈ 𝐙) :
    ∃ e ∈ 𝐄₀, t⁻¹ * (e⁻¹ * t * e) = z := by
  have hsub : {x : G | ∃ e ∈ 𝐄₀, x = e⁻¹ * t * e} ⊆ {x | ∃ z ∈ 𝐙, x = t * z} := by
    rintro _ ⟨e, he, rfl⟩
    exact ⟨_, kappa_mem h (E0_le_H h he), by group⟩
  have h1 := relIndex_mul_card 𝐂 𝐄₀
  rw [relIndex_centralizer_eq_card, inf_comm 𝐂 𝐄₀, E0_inf_C h, card_tZ h, card_E0 h] at h1
  have hcard : Nat.card {x : G | ∃ e ∈ 𝐄₀, x = e⁻¹ * t * e} = Nat.card K ^ 2 := by
    have hq : 0 < 2 * Nat.card K ^ 2 := by have : 0 < Nat.card K := Nat.card_pos; positivity
    have h2 : Nat.card {x : G | ∃ e ∈ 𝐄₀, x = e⁻¹ * t * e} * (2 * Nat.card K ^ 2) =
        Nat.card K ^ 2 * (2 * Nat.card K ^ 2) := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_right hq h2
  have heq : {x : G | ∃ e ∈ 𝐄₀, x = e⁻¹ * t * e} = {x | ∃ z ∈ 𝐙, x = t * z} := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hcard, card_mul_set, FCHyp.card_ZP]
  have hmem : t * z ∈ {x : G | ∃ e ∈ 𝐄₀, x = e⁻¹ * t * e} := by
    rw [heq]
    exact ⟨z, hz, rfl⟩
  obtain ⟨e, he, hez⟩ := hmem
  exact ⟨e, he, by rw [← hez, inv_mul_cancel_left]⟩


omit [Finite K] in
theorem conj_torus_mem_E (h : FCHyp L K n φ t) (i : Axis) {j : G} (hj : j ∈ 𝐉) {e : G}
    (he : e ∈ 𝐄[i]) : j⁻¹ * e * j ∈ 𝐄[i] := by
  have := conj_mem_pCore_map (h.torus_le_N i (inv_mem hj)) he
  rwa [inv_inv] at this

omit [Finite K] in
theorem conj_torus_mem_D (h : FCHyp L K n φ t) (i : Axis) {j : G} (hj : j ∈ 𝐉) {e : G}
    (he : e ∈ 𝐃[i]) : j⁻¹ * e * j ∈ 𝐃[i] := by
  have := conj_mem_pCore_map (h.torus_le_M i (inv_mem hj)) he
  rwa [inv_inv] at this

omit [Finite K] in
theorem conj_torus_mem_E0 (h : FCHyp L K n φ t) {j : G} (hj : j ∈ 𝐉) {e : G} (he : e ∈ 𝐄₀) :
    j⁻¹ * e * j ∈ 𝐄₀ :=
  mem_inf.mpr ⟨conj_torus_mem_E h _ hj (mem_inf.mp he).1, conj_torus_mem_E h _ hj (mem_inf.mp he).2⟩

omit [Finite K] in
theorem conj_torus_mem_H (h : FCHyp L K n φ t) {j : G} (hj : j ∈ 𝐉) {x : G} (hx : x ∈ 𝐇) :
    j⁻¹ * x * j ∈ 𝐇 := by
  have := conj_mem_sup (g := j⁻¹)
    (fun y hy => (mem_normalizer_iff.mp (h.torus_le_normalizer_Qi Axis.one (inv_mem hj)) y).mp hy)
    (fun y hy => (mem_normalizer_iff.mp (h.torus_le_normalizer_Qi Axis.two (inv_mem hj)) y).mp hy)
    hx
  rwa [inv_inv] at this

omit [Finite G] [Finite K] in
theorem conj_torus_mem_ZP {j : G} (hj : j ∈ 𝐉) {z : G} (hz : z ∈ 𝐙) : j⁻¹ * z * j ∈ 𝐙 := by
  obtain ⟨r, s, -, -, hrs⟩ := exists_conj_zc hj
  obtain ⟨b, c, rfl⟩ := exists_zc hz
  rw [hrs]
  exact zc_mem _ _

omit [Finite G] [Finite K] in
theorem torus_comm_t (h : FCHyp L K n φ t) {j : G} (hj : j ∈ 𝐉) : j * t = t * j :=
  mem_centralizer_singleton_iff.mp (h.torus_le_C hj)

omit [Finite G] [Finite K] in
theorem kappa_conj_torus (h : FCHyp L K n φ t) {j : G} (hj : j ∈ 𝐉) (x : G) :
    t⁻¹ * ((j⁻¹ * x * j)⁻¹ * t * (j⁻¹ * x * j)) = j⁻¹ * (t⁻¹ * (x⁻¹ * t * x)) * j := by
  have e : j⁻¹ * t * j = t := by rw [mul_assoc, ← torus_comm_t h hj, inv_mul_cancel_left]
  calc t⁻¹ * ((j⁻¹ * x * j)⁻¹ * t * (j⁻¹ * x * j))
      = (j⁻¹ * t * j)⁻¹ * ((j⁻¹ * x * j)⁻¹ * (j⁻¹ * t * j) * (j⁻¹ * x * j)) := by rw [e]
    _ = j⁻¹ * (t⁻¹ * (x⁻¹ * t * x)) * j := by group

theorem kappa_inv (h : FCHyp L K n φ t) {x : G} (hx : x ∈ 𝐇) :
    t⁻¹ * (x⁻¹⁻¹ * t * x⁻¹) = (t⁻¹ * (x⁻¹ * t * x))⁻¹ := by
  have h1 := kappa_mul h (inv_mem hx) hx
  rw [inv_mul_cancel, inv_one, one_mul, mul_one, inv_mul_cancel] at h1
  exact eq_inv_of_mul_eq_one_left h1.symm

theorem kappa_delta (h : FCHyp L K n φ t) {j : G} (hj : j ∈ 𝐉) {e : G} (he : e ∈ 𝐇) :
    t⁻¹ * ((e⁻¹ * (j⁻¹ * e * j))⁻¹ * t * (e⁻¹ * (j⁻¹ * e * j))) =
      (t⁻¹ * (e⁻¹ * t * e))⁻¹ * (j⁻¹ * (t⁻¹ * (e⁻¹ * t * e)) * j) := by
  rw [kappa_mul h (inv_mem he) (conj_torus_mem_H h hj he), kappa_inv h he,
    kappa_conj_torus h hj]

structure GoodTorus (φ : L ≃* antiSp K) (j : G) : Prop where
  mem : j ∈ pull φ (diagTorus K)
  fpf : ∀ z ∈ pull φ (antiUnipotentCenter K), j⁻¹ * z * j = z → z = 1
  surj : ∀ z ∈ pull φ (antiUnipotentCenter K), ∃ w ∈ pull φ (antiUnipotentCenter K),
    w⁻¹ * (j⁻¹ * w * j) = z

omit [Finite G] [Finite K] in
theorem one_add_ne_zero {r : K} (hr : r ≠ 1) : 1 + r ≠ 0 ∧ 1 + r ^ 2 ≠ 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  refine ⟨fun h0 => hr (by linear_combination h0 - h2), fun h0 => hr ?_⟩
  have h1 : (1 + r) ^ 2 = 0 := by linear_combination h0 + r * h2
  linear_combination (pow_eq_zero_iff two_ne_zero).mp h1 - h2

omit [Finite G] [Finite K] in
theorem exists_goodTorus (h : FCHyp L K n φ t) : ∃ j : G, GoodTorus φ j := by
  have hK2 : 2 < Nat.card K := by have := h.four_le_card; omega
  obtain ⟨r, hr0, hr1⟩ := exists_ne_zero_ne hK2 (1 : K)
  obtain ⟨δ, hδ, hδm⟩ := exists_diagTorus (K := K) hr0 one_ne_zero
  have hconj := conj_zc (φ := φ) hr0 one_ne_zero hδm
  obtain ⟨h1, h2⟩ := one_add_ne_zero (Ne.symm hr1)
  refine ⟨((φ.symm δ : L) : G), ⟨symm_mem_pull.mpr hδ, fun z hz hzz => ?_, fun z hz => ?_⟩⟩
  · obtain ⟨b, c, rfl⟩ := exists_zc hz
    rw [hconj] at hzz
    obtain ⟨hb, hc⟩ := zc_inj hzz
    have htwo : (2 : K) = 0 := CharTwo.two_eq_zero
    have hb' : (1 + r) * b = 0 := by linear_combination hb + b * htwo
    have hc' : (1 + r ^ 2) * c = 0 := by linear_combination hc + c * htwo
    rw [(mul_eq_zero.mp hb').resolve_left h1, (mul_eq_zero.mp hc').resolve_left h2, zc_zero]
  · obtain ⟨b, c, rfl⟩ := exists_zc hz
    refine ⟨zc φ (b / (1 + r)) (c / (1 + r ^ 2)), zc_mem _ _, ?_⟩
    rw [hconj, zc_inv, zc_mul]
    congr 1
    · field_simp
    · field_simp

section Complement

variable {j₀ : G}

set_option quotPrecheck false in
local notation "𝐒" => closure {x : G | ∃ e ∈ 𝐄₀, x = e⁻¹ * (j₀⁻¹ * e * j₀)}

theorem mem_S_iff (h : FCHyp L K n φ t) (hj : GoodTorus φ j₀) {x : G} :
    x ∈ 𝐒 ↔ ∃ e ∈ 𝐄₀, x = e⁻¹ * (j₀⁻¹ * e * j₀) :=
  ⟨mem_of_mem_closure_delta (E0_le_H h) (ZP_le_E0 h) (fun _ hx _ hz => comm_ZP h hx hz)
    (fun _ hx _ hy => commutator_mem_ZP h hx hy) (fun _ he => conj_torus_mem_E0 h hj.mem he)
    hj.surj, fun hx => subset_closure hx⟩

theorem S_le_E0 (h : FCHyp L K n φ t) (hj : GoodTorus φ j₀) : 𝐒 ≤ 𝐄₀ := fun x hx => by
  obtain ⟨e, he, rfl⟩ := (mem_S_iff h hj).mp hx
  exact mul_mem (inv_mem he) (conj_torus_mem_E0 h hj.mem he)

theorem ZP_le_S (h : FCHyp L K n φ t) (hj : GoodTorus φ j₀) : 𝐙 ≤ 𝐒 := fun z hz => by
  obtain ⟨w, hw, rfl⟩ := hj.surj z hz
  exact subset_closure ⟨w, ZP_le_E0 h hw, rfl⟩

theorem conj_torus_mem_S (h : FCHyp L K n φ t) (hj : GoodTorus φ j₀) {j : G} (hjJ : j ∈ 𝐉)
    {x : G} (hx : x ∈ 𝐒) : j⁻¹ * x * j ∈ 𝐒 := by
  obtain ⟨e, he, rfl⟩ := (mem_S_iff h hj).mp hx
  refine subset_closure ⟨j⁻¹ * e * j, conj_torus_mem_E0 h hjJ he, ?_⟩
  have hc : Commute j j₀ := torus_comm hjJ hj.mem
  have e1 : j * j₀⁻¹ * j⁻¹ = j₀⁻¹ := by rw [hc.inv_right.eq, mul_inv_cancel_right]
  calc j⁻¹ * (e⁻¹ * (j₀⁻¹ * e * j₀)) * j = j⁻¹ * e⁻¹ * j₀⁻¹ * e * (j₀ * j) := by group
    _ = j⁻¹ * e⁻¹ * (j * j₀⁻¹ * j⁻¹) * e * (j * j₀) := by rw [e1, hc.eq]
    _ = (j⁻¹ * e * j)⁻¹ * (j₀⁻¹ * (j⁻¹ * e * j) * j₀) := by group

theorem t_not_mem_S (h : FCHyp L K n φ t) (hj : GoodTorus φ j₀) : t ∉ 𝐒 := by
  intro ht
  obtain ⟨e, he, hte⟩ := (mem_S_iff h hj).mp ht
  have heH := E0_le_H h he
  have hk := kappa_delta h hj.mem heH
  rw [← hte, inv_mul_cancel, one_mul, inv_mul_cancel] at hk
  have hfix : j₀⁻¹ * (t⁻¹ * (e⁻¹ * t * e)) * j₀ = t⁻¹ * (e⁻¹ * t * e) := by
    have := eq_of_inv_mul_eq_one hk.symm
    exact this.symm
  have hκ := hj.fpf _ (kappa_mem h heH) hfix
  have heC : e ∈ 𝐄₀ ⊓ 𝐂 := mem_inf.mpr ⟨he, kappa_eq_one_iff.mp hκ⟩
  rw [E0_inf_C h] at heC
  have hδZ : ∀ w ∈ 𝐙, w⁻¹ * (j₀⁻¹ * w * j₀) ∈ 𝐙 := fun w hw =>
    mul_mem (inv_mem hw) (conj_torus_mem_ZP hj.mem hw)
  have htZ : t ∈ 𝐙 := by
    rcases (mem_zpowers_sup_iff h.setup.t_mul_t (fun w hw => h.twoCore.comm (pull_le φ _ hw))).mp
      heC with h1 | h1
    · rw [hte]
      exact hδZ e h1
    · have e1 : e = t * (t * e) := by rw [← mul_assoc, h.setup.t_mul_t, one_mul]
      have hjt := torus_comm_t h hj.mem
      have e2 : e⁻¹ * (j₀⁻¹ * e * j₀) = (t * e)⁻¹ * (j₀⁻¹ * (t * e) * j₀) := by
        have : j₀⁻¹ * t * j₀ = t := by rw [mul_assoc, ← hjt, inv_mul_cancel_left]
        calc e⁻¹ * (j₀⁻¹ * e * j₀) = e⁻¹ * t⁻¹ * (j₀⁻¹ * t * j₀) * (j₀⁻¹ * e * j₀) := by
              rw [this]; group
          _ = (t * e)⁻¹ * (j₀⁻¹ * (t * e) * j₀) := by group
      rw [hte, e2]
      exact hδZ _ h1
  exact h.twoCore.t_not_mem (pull_le φ _ htZ)

theorem conj_H_mem_S (h : FCHyp L K n φ t) (hj : GoodTorus φ j₀) {x : G} (hx : x ∈ 𝐇) {s : G}
    (hs : s ∈ 𝐒) : x * s * x⁻¹ ∈ 𝐒 := by
  have hsH : s ∈ 𝐇 := E0_le_H h (S_le_E0 h hj hs)
  have hc := commutator_mem_ZP h hsH (inv_mem hx)
  rw [inv_inv] at hc
  rw [show x * s * x⁻¹ = s * (s⁻¹ * (x * s * x⁻¹)) by group]
  exact mul_mem hs (ZP_le_S h hj hc)

theorem S_inf_tZ (h : FCHyp L K n φ t) (hj : GoodTorus φ j₀) : 𝐒 ⊓ (zpowers t ⊔ 𝐙) = 𝐙 := by
  refine le_antisymm (fun x hx => ?_) (le_inf (ZP_le_S h hj) le_sup_right)
  obtain ⟨hxS, hxt⟩ := mem_inf.mp hx
  rcases (mem_zpowers_sup_iff h.setup.t_mul_t (fun w hw => h.twoCore.comm (pull_le φ _ hw))).mp
    hxt with h1 | h1
  · exact h1
  · exfalso
    apply t_not_mem_S h hj
    have := mul_mem (ZP_le_S h hj h1) (inv_mem hxS)
    rwa [mul_inv_cancel_right] at this

theorem S_inf_C (h : FCHyp L K n φ t) (hj : GoodTorus φ j₀) : 𝐂 ⊓ 𝐒 = 𝐙 := by
  rw [← S_inf_tZ h hj, ← E0_inf_C h]
  ext x
  simp only [mem_inf]
  constructor
  · rintro ⟨hxC, hxS⟩
    exact ⟨hxS, S_le_E0 h hj hxS, hxC⟩
  · rintro ⟨hxS, -, hxC⟩
    exact ⟨hxC, hxS⟩

theorem exists_kappa_eq_S (h : FCHyp L K n φ t) (hj : GoodTorus φ j₀) {z : G} (hz : z ∈ 𝐙) :
    ∃ s ∈ 𝐒, t⁻¹ * (s⁻¹ * t * s) = z := by
  obtain ⟨w, hw, rfl⟩ := hj.surj z hz
  obtain ⟨e, he, rfl⟩ := exists_kappa_eq h hw
  exact ⟨_, subset_closure ⟨e, he, rfl⟩, kappa_delta h hj.mem (E0_le_H h he)⟩

theorem card_S (h : FCHyp L K n φ t) (hj : GoodTorus φ j₀) : Nat.card 𝐒 = Nat.card K ^ 4 := by
  have horb : {x : G | ∃ s ∈ 𝐒, x = s⁻¹ * t * s} = {x | ∃ z ∈ 𝐙, x = t * z} := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨_, kappa_mem h (E0_le_H h (S_le_E0 h hj hs)), by group⟩
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨s, hs, hsz⟩ := exists_kappa_eq_S h hj hz
      exact ⟨s, hs, by rw [← hsz, mul_inv_cancel_left]⟩
  have h1 := relIndex_mul_card 𝐂 𝐒
  rw [relIndex_centralizer_eq_card, horb, card_mul_set, S_inf_C h hj, FCHyp.card_ZP] at h1
  rw [← h1]
  ring

theorem S_sup_t (h : FCHyp L K n φ t) (hj : GoodTorus φ j₀) :
    𝐒 ⊓ zpowers t = ⊥ ∧ 𝐒 ⊔ zpowers t = 𝐄₀ := by
  have hinf : 𝐒 ⊓ zpowers t = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxS, hxt⟩ := mem_inf.mp hx
    have hx' : x = 1 ∨ x = t := by
      obtain ⟨j, rfl⟩ := hxt
      exact zpow_eq_one_or_eq h.setup.t_mul_t j
    rcases hx' with rfl | rfl
    · exact one_mem _
    · exact absurd hxS (t_not_mem_S h hj)
  refine ⟨hinf, ?_⟩
  have hnorm : zpowers t ≤ normalizer (𝐒 : Set G) := fun c hc =>
    RootAxisTwoCore.mem_normalizer_of_conj_le fun _ hs =>
      conj_H_mem_S h hj (zpowers_le.mpr t_mem_H hc) hs
  have h1 := card_sup_mul_card_inf 𝐒 (zpowers t) hnorm
  rw [hinf, card_bot, mul_one, card_S h hj, Nat.card_zpowers, h.setup.order_t] at h1
  refine eq_of_le_of_card_ge (sup_le (S_le_E0 h hj) (zpowers_le.mpr (t_mem_E0 h))) ?_
  rw [card_E0 h, h1]
  ring_nf
  exact le_rfl

theorem F_eq_S (h : FCHyp L K n φ t) (hj : GoodTorus φ j₀) : 𝐅 = 𝐒 := by
  apply le_antisymm
  · rw [closure_le]
    rintro _ ⟨e, he, j, hjJ, rfl⟩
    have hnorm : zpowers t ≤ normalizer (𝐒 : Set G) := fun c hc =>
      RootAxisTwoCore.mem_normalizer_of_conj_le fun _ hs =>
        conj_H_mem_S h hj (zpowers_le.mpr t_mem_H hc) hs
    have he' : e ∈ ((𝐒 : Subgroup G) : Set G) * (zpowers t : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _ hnorm, (S_sup_t h hj).2]
      exact he
    obtain ⟨s, hs, c, hc, rfl⟩ := he'
    have hcj : j⁻¹ * c * j = c := by
      obtain ⟨k, rfl⟩ := hc
      have hjt := torus_comm_t h hjJ
      have : Commute j t := hjt
      rw [mul_assoc, ← (this.zpow_right k).eq, inv_mul_cancel_left]
    have hsj : s⁻¹ * (j⁻¹ * s * j) ∈ 𝐒 := mul_mem (inv_mem hs) (conj_torus_mem_S h hj hjJ hs)
    have hcH : c⁻¹ ∈ 𝐇 := inv_mem (zpowers_le.mpr t_mem_H hc)
    have := conj_H_mem_S h hj hcH hsj
    rw [inv_inv] at this
    have e1 : (s * c)⁻¹ * (j⁻¹ * (s * c) * j) = c⁻¹ * (s⁻¹ * (j⁻¹ * s * j)) * c := by
      calc (s * c)⁻¹ * (j⁻¹ * (s * c) * j)
          = c⁻¹ * (s⁻¹ * (j⁻¹ * s * j)) * (j⁻¹ * c * j) := by group
        _ = c⁻¹ * (s⁻¹ * (j⁻¹ * s * j)) * c := by rw [hcj]
    rw [e1]
    exact this
  · rw [closure_le]
    rintro _ ⟨e, he, rfl⟩
    exact subset_closure ⟨e, he, j₀, hj.mem, rfl⟩

end Complement


omit [Finite K] in
theorem F_le_E0 (h : FCHyp L K n φ t) : 𝐅 ≤ 𝐄₀ := by
  rw [closure_le]
  rintro _ ⟨e, he, j, hj, rfl⟩
  exact mul_mem (inv_mem he) (conj_torus_mem_E0 h hj he)

theorem F_le_H (h : FCHyp L K n φ t) : 𝐅 ≤ 𝐇 := (F_le_E0 h).trans (E0_le_H h)

theorem ZP_le_F (h : FCHyp L K n φ t) : 𝐙 ≤ 𝐅 := by
  obtain ⟨j₀, hj⟩ := exists_goodTorus h
  rw [F_eq_S h hj]
  exact ZP_le_S h hj

theorem conj_torus_mem_F (h : FCHyp L K n φ t) {j : G} (hjJ : j ∈ 𝐉) {x : G} (hx : x ∈ 𝐅) :
    j⁻¹ * x * j ∈ 𝐅 := by
  obtain ⟨j₀, hj⟩ := exists_goodTorus h
  rw [F_eq_S h hj] at hx ⊢
  exact conj_torus_mem_S h hj hjJ hx

theorem torus_le_normalizer_F (h : FCHyp L K n φ t) : 𝐉 ≤ normalizer (𝐅 : Set G) := fun j hj =>
  RootAxisTwoCore.mem_normalizer_of_conj_le fun x hx => by
    simpa using conj_torus_mem_F h (inv_mem hj) hx

theorem conj_H_mem_F (h : FCHyp L K n φ t) {x : G} (hx : x ∈ 𝐇) {f : G} (hf : f ∈ 𝐅) :
    x * f * x⁻¹ ∈ 𝐅 := by
  obtain ⟨j₀, hj⟩ := exists_goodTorus h
  rw [F_eq_S h hj] at hf ⊢
  exact conj_H_mem_S h hj hx hf

theorem F_normal_H (h : FCHyp L K n φ t) : (𝐅.subgroupOf 𝐇).Normal :=
  ⟨fun _ hf x => mem_subgroupOf.mpr (conj_H_mem_F h x.2 (mem_subgroupOf.mp hf))⟩

theorem H_le_normalizer_F (h : FCHyp L K n φ t) : 𝐇 ≤ normalizer (𝐅 : Set G) := fun _ hx =>
  RootAxisTwoCore.mem_normalizer_of_conj_le fun _ hf => conj_H_mem_F h hx hf

theorem t_not_mem_F (h : FCHyp L K n φ t) : t ∉ 𝐅 := by
  obtain ⟨j₀, hj⟩ := exists_goodTorus h
  rw [F_eq_S h hj]
  exact t_not_mem_S h hj

theorem F_inf_tZ (h : FCHyp L K n φ t) : 𝐅 ⊓ (zpowers t ⊔ 𝐙) = 𝐙 := by
  obtain ⟨j₀, hj⟩ := exists_goodTorus h
  rw [F_eq_S h hj]
  exact S_inf_tZ h hj

theorem C_inf_F (h : FCHyp L K n φ t) : 𝐂 ⊓ 𝐅 = 𝐙 := by
  obtain ⟨j₀, hj⟩ := exists_goodTorus h
  rw [F_eq_S h hj]
  exact S_inf_C h hj

theorem mem_ZP_of_mem_F (h : FCHyp L K n φ t) {x : G} (hx : x ∈ 𝐅) (hxC : x ∈ 𝐂) : x ∈ 𝐙 := by
  rw [← C_inf_F h]
  exact mem_inf.mpr ⟨hxC, hx⟩

theorem exists_kappa_eq_F (h : FCHyp L K n φ t) {z : G} (hz : z ∈ 𝐙) :
    ∃ f ∈ 𝐅, t⁻¹ * (f⁻¹ * t * f) = z := by
  obtain ⟨j₀, hj⟩ := exists_goodTorus h
  rw [F_eq_S h hj]
  exact exists_kappa_eq_S h hj hz

theorem card_F (h : FCHyp L K n φ t) : Nat.card 𝐅 = Nat.card K ^ 4 := by
  obtain ⟨j₀, hj⟩ := exists_goodTorus h
  rw [F_eq_S h hj]
  exact card_S h hj

theorem F_sup_t (h : FCHyp L K n φ t) : 𝐅 ⊓ zpowers t = ⊥ ∧ 𝐅 ⊔ zpowers t = 𝐄₀ := by
  obtain ⟨j₀, hj⟩ := exists_goodTorus h
  rw [F_eq_S h hj]
  exact S_sup_t h hj

theorem F_normal_E0 (h : FCHyp L K n φ t) : (𝐅.subgroupOf 𝐄₀).Normal :=
  ⟨fun _ hf x => mem_subgroupOf.mpr (conj_H_mem_F h (E0_le_H h x.2) (mem_subgroupOf.mp hf))⟩

theorem exists_kappa_quotient (h : FCHyp L K n φ t) {X Y U : Subgroup G} (hXH : X ≤ 𝐇)
    (hU : ∀ x ∈ X, t⁻¹ * (x⁻¹ * t * x) ∈ U) (hUZ : U ≤ 𝐙) (hker : ∀ x ∈ X, x ∈ 𝐂 ↔ x ∈ Y)
    (hsurj : ∀ u ∈ U, ∃ x ∈ X, t⁻¹ * (x⁻¹ * t * x) = u)
    (hJ : ∀ j ∈ 𝐉, ∀ x ∈ X, j⁻¹ * x * j ∈ X) :
    ∃ _ : (Y.subgroupOf X).Normal, ∃ θ : (↥X ⧸ Y.subgroupOf X) ≃* ↥U,
      (∀ x : X, (θ x : G) = t⁻¹ * ((x : G)⁻¹ * t * x)) ∧
      ∀ j ∈ 𝐉, ∀ x : X, ∃ x' : X, (x' : G) = j⁻¹ * x * j ∧ (θ x' : G) = j⁻¹ * θ x * j := by
  have hn : (Y.subgroupOf X).Normal := ⟨fun y hy x => by
    rw [mem_subgroupOf] at hy ⊢
    have hyX := y.2
    have hy1 : t⁻¹ * ((y : G)⁻¹ * t * y) = 1 := kappa_eq_one_iff.mpr ((hker _ hyX).mpr hy)
    refine (hker _ (mul_mem (mul_mem x.2 hyX) (inv_mem x.2))).mp (kappa_eq_one_iff.mp ?_)
    rw [kappa_mul h (mul_mem (hXH x.2) (hXH hyX)) (inv_mem (hXH x.2)),
      kappa_mul h (hXH x.2) (hXH hyX), hy1, mul_one, kappa_inv h (hXH x.2), mul_inv_cancel]⟩
  obtain ⟨θ, hθ⟩ := exists_quotient_mulEquiv (D := X) (B := Y) (U := U) (t := t) hU
    (fun d hd u hu => comm_ZP h (hXH hd) (hUZ hu))
    (fun u hu v hv => comm_ZP h (ZP_le_H (hUZ hu)) (hUZ hv))
    (fun d hd => by rw [← hker d hd, ← kappa_eq_one_iff, inv_mul_eq_one, eq_comm])
    hsurj
  refine ⟨hn, θ, hθ, fun j hj x => ⟨⟨_, hJ j hj x x.2⟩, rfl, ?_⟩⟩
  rw [hθ, hθ]
  exact kappa_conj_torus h hj x

theorem quotient_F (h : FCHyp L K n φ t) :
    ∃ _ : (𝐙.subgroupOf 𝐅).Normal, ∃ θ : (↥𝐅 ⧸ 𝐙.subgroupOf 𝐅) ≃* ↥𝐙,
      (∀ x : 𝐅, (θ x : G) = t⁻¹ * ((x : G)⁻¹ * t * x)) ∧
      ∀ j ∈ 𝐉, ∀ x : 𝐅, ∃ x' : 𝐅, (x' : G) = j⁻¹ * x * j ∧ (θ x' : G) = j⁻¹ * θ x * j :=
  exists_kappa_quotient h (F_le_H h) (fun _ hx => kappa_mem h (F_le_H h hx)) le_rfl
    (fun _ hx => ⟨fun hxC => mem_ZP_of_mem_F h hx hxC, fun hxZ =>
      h.setup.Q_le_C (mem_sup_left (Setup.ZP_le_PG hxZ))⟩)
    (fun _ hz => exists_kappa_eq_F h hz) (fun _ hj _ hx => conj_torus_mem_F h hj hx)


omit [Finite G] [Finite K] in
theorem B_inf_B_swap (h : FCHyp L K n φ t) (i : Axis) :
    𝐁[i] ⊓ 𝐁[i.swap] = zpowers t ⊔ 𝐙 := by
  cases i
  · exact B_inf_B h
  · rw [inf_comm]
    exact B_inf_B h

theorem Hj_inf_B (h : FCHyp L K n φ t) (i : Axis) :
    (𝐇 ⊓ 𝐄[i.swap]) ⊓ 𝐁[i] = zpowers t ⊔ 𝐙 := by
  rw [← B_inf_B_swap h i]
  apply le_antisymm
  · intro x hx
    obtain ⟨⟨-, hxE⟩, hxB⟩ := hx
    have h1 : x ∈ 𝐐 ⊓ 𝐄[i.swap] := mem_inf.mpr ⟨FCHyp.B_le_Q i hxB, hxE⟩
    rw [Q_inf_E h] at h1
    exact mem_inf.mpr ⟨hxB, h1⟩
  · intro x hx
    obtain ⟨h1, h2⟩ := mem_inf.mp hx
    exact mem_inf.mpr ⟨mem_inf.mpr ⟨Q_le_H (FCHyp.B_le_Q i h1), h.D_le_E _ (h.B_le_D _ h2)⟩, h1⟩

theorem Hj_sup_B (h : FCHyp L K n φ t) (i : Axis) : (𝐇 ⊓ 𝐄[i.swap]) ⊔ 𝐁[i] = 𝐇 := by
  have hBH : 𝐁[i] ≤ 𝐇 := (FCHyp.B_le_Q i).trans Q_le_H
  have h1 := card_sup_mul_card_inf (𝐇 ⊓ 𝐄[i.swap]) 𝐁[i] (hBH.trans (H_le_normalizer_Hi h _))
  rw [Hj_inf_B h i, card_tZ h, card_Hi h, h.card_B] at h1
  refine eq_of_le_of_card_ge (sup_le inf_le_left hBH) ?_
  have hq : 0 < 2 * Nat.card K ^ 2 := by have : 0 < Nat.card K := Nat.card_pos; positivity
  have h2 : Nat.card ((𝐇 ⊓ 𝐄[i.swap]) ⊔ 𝐁[i] : Subgroup G) = 2 * Nat.card K ^ 6 :=
    Nat.eq_of_mul_eq_mul_right hq (by rw [h1]; ring)
  rw [h2, h.H_facts.2.2]

theorem D_inf_E0 (h : FCHyp L K n φ t) (i : Axis) :
    𝐃[i] ⊓ 𝐄₀ = 𝐃[i] ⊓ (𝐇 ⊓ 𝐄[i.swap]) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxD, hxE⟩ := mem_inf.mp hx
    refine mem_inf.mpr ⟨hxD, mem_inf.mpr ⟨E0_le_H h hxE, ?_⟩⟩
    cases i
    · exact (mem_inf.mp hxE).2
    · exact (mem_inf.mp hxE).1
  · intro x hx
    obtain ⟨hxD, hxHE⟩ := mem_inf.mp hx
    have hxE := (mem_inf.mp hxHE).2
    have hxEi := h.D_le_E i hxD
    refine mem_inf.mpr ⟨hxD, ?_⟩
    cases i
    · exact mem_inf.mpr ⟨hxEi, hxE⟩
    · exact mem_inf.mpr ⟨hxE, hxEi⟩

theorem card_D_inf_E0 (h : FCHyp L K n φ t) (i : Axis) :
    Nat.card (𝐃[i] ⊓ 𝐄₀ : Subgroup G) = 2 * Nat.card K ^ 3 := by
  rw [D_inf_E0 h i]
  have hDH : 𝐃[i] ≤ 𝐇 := D_le_H i
  have h1 := card_sup_mul_card_inf (𝐇 ⊓ 𝐄[i.swap]) 𝐃[i] (hDH.trans (H_le_normalizer_Hi h _))
  have hsup : (𝐇 ⊓ 𝐄[i.swap]) ⊔ 𝐃[i] = 𝐇 := le_antisymm (sup_le inf_le_left hDH)
    ((Hj_sup_B h i).symm.le.trans (sup_le_sup_left (h.B_le_D i) _))
  rw [hsup, h.H_facts.2.2, card_Hi h, h.card_D, inf_comm (𝐇 ⊓ 𝐄[i.swap]) 𝐃[i]] at h1
  have hq : 0 < 2 * Nat.card K ^ 6 := by have : 0 < Nat.card K := Nat.card_pos; positivity
  exact Nat.eq_of_mul_eq_mul_left hq (by rw [h1]; ring)

theorem t_mem_D (h : FCHyp L K n φ t) (i : Axis) : t ∈ 𝐃[i] :=
  h.B_le_D i (mem_sup_left (mem_zpowers t))

theorem card_Fi (h : FCHyp L K n φ t) (i : Axis) :
    Nat.card (𝐅 ⊓ 𝐃[i] : Subgroup G) = Nat.card K ^ 3 := by
  have hle : 𝐃[i] ⊓ 𝐄₀ ≤ normalizer (𝐅 : Set G) :=
    inf_le_right.trans ((E0_le_H h).trans (H_le_normalizer_F h))
  have h1 := card_sup_mul_card_inf 𝐅 (𝐃[i] ⊓ 𝐄₀) hle
  have hsup : 𝐅 ⊔ (𝐃[i] ⊓ 𝐄₀) = 𝐄₀ := le_antisymm (sup_le (F_le_E0 h) inf_le_right)
    ((F_sup_t h).2.symm.le.trans (sup_le_sup_left
      (zpowers_le.mpr (mem_inf.mpr ⟨t_mem_D h i, t_mem_E0 h⟩)) _))
  have hinf : 𝐅 ⊓ (𝐃[i] ⊓ 𝐄₀) = 𝐅 ⊓ 𝐃[i] := le_antisymm (inf_le_inf_left _ inf_le_left)
    (le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans (F_le_E0 h))))
  rw [hsup, hinf, card_E0 h, card_F h, card_D_inf_E0 h] at h1
  have hq : 0 < 2 * Nat.card K ^ 4 := by have : 0 < Nat.card K := Nat.card_pos; positivity
  exact Nat.eq_of_mul_eq_mul_left hq (by rw [h1]; ring)

theorem ZP_le_Fi (h : FCHyp L K n φ t) (i : Axis) : 𝐙 ≤ 𝐅 ⊓ 𝐃[i] :=
  le_inf (ZP_le_F h) ((ZP_le_B i).trans (h.B_le_D i))

theorem Fi_inf_B (h : FCHyp L K n φ t) (i : Axis) : (𝐅 ⊓ 𝐃[i]) ⊓ 𝐁[i] = 𝐙 := by
  refine le_antisymm (fun x hx => ?_) (le_inf (ZP_le_Fi h i) (ZP_le_B i))
  obtain ⟨⟨hxF, -⟩, hxB⟩ := hx
  exact mem_ZP_of_mem_F h hxF (h.setup.Q_le_C (FCHyp.B_le_Q i hxB))

theorem Fi_mul_B (h : FCHyp L K n φ t) (i : Axis) :
    ((𝐅 ⊓ 𝐃[i] : Subgroup G) : Set G) * (𝐁[i] : Set G) = 𝐃[i] := by
  have hN : 𝐅 ⊓ 𝐃[i] ≤ normalizer (𝐁[i] : Set G) := fun x hx =>
    h.twoCore.M_le_normalizer_B φ i (map_subtype_le _ (mem_inf.mp hx).2)
  have h1 := card_sup_mul_card_inf 𝐁[i] (𝐅 ⊓ 𝐃[i]) hN
  rw [inf_comm 𝐁[i] (𝐅 ⊓ 𝐃[i]), Fi_inf_B h i, FCHyp.card_ZP, h.card_B, card_Fi h] at h1
  have hsup : 𝐅 ⊓ 𝐃[i] ⊔ 𝐁[i] = 𝐃[i] := by
    refine eq_of_le_of_card_ge (sup_le inf_le_right (h.B_le_D i)) ?_
    have hq : 0 < Nat.card K ^ 2 := by have : 0 < Nat.card K := Nat.card_pos; positivity
    have h2 : Nat.card (𝐁[i] ⊔ (𝐅 ⊓ 𝐃[i]) : Subgroup G) = 2 * Nat.card K ^ 4 :=
      Nat.eq_of_mul_eq_mul_right hq (by rw [h1]; ring)
    rw [sup_comm (𝐅 ⊓ 𝐃[i]) 𝐁[i], h2, h.card_D]
  rw [← coe_mul_of_left_le_normalizer_right _ _ hN, hsup]

omit [Finite G] [Finite K] in
theorem kappa_mem_U (h : FCHyp L K n φ t) (i : Axis) {x : G} (hx : x ∈ 𝐃[i]) :
    t⁻¹ * (x⁻¹ * t * x) ∈ 𝐔[i] := by
  rw [h.twoCore.t_inv]
  exact h.twoCore.conj_t_mem φ i (map_subtype_le _ hx)

theorem C_inf_Fi (h : FCHyp L K n φ t) (i : Axis) : 𝐂 ⊓ (𝐅 ⊓ 𝐃[i]) = 𝐙 :=
  le_antisymm (fun _ hx => mem_ZP_of_mem_F h (mem_inf.mp (mem_inf.mp hx).2).1 (mem_inf.mp hx).1)
    (le_inf (fun _ hz => h.setup.Q_le_C (mem_sup_left (Setup.ZP_le_PG hz))) (ZP_le_Fi h i))

theorem exists_kappa_eq_Fi (h : FCHyp L K n φ t) (i : Axis) {u : G} (hu : u ∈ 𝐔[i]) :
    ∃ f ∈ 𝐅 ⊓ 𝐃[i], t⁻¹ * (f⁻¹ * t * f) = u :=
  exists_conj_eq_of_card (fun _ hx => kappa_mem_U h i (mem_inf.mp hx).2)
    (by rw [C_inf_Fi h i, card_Fi h, FCHyp.card_U, FCHyp.card_ZP]; ring) hu

theorem Fi_inf_Fi (h : FCHyp L K n φ t) : (𝐅 ⊓ 𝐃[Axis.one]) ⊓ (𝐅 ⊓ 𝐃[Axis.two]) = 𝐙 := by
  refine le_antisymm (fun x hx => ?_) (le_inf (ZP_le_Fi h _) (ZP_le_Fi h _))
  obtain ⟨⟨hxF, hx1⟩, ⟨-, hx2⟩⟩ := hx
  have hinf : 𝐔[Axis.one] ⊓ 𝐔[Axis.two] = ⊥ := by rw [← pull_inf, rootU_inf, pull_bot]
  have hκ : t⁻¹ * (x⁻¹ * t * x) ∈ 𝐔[Axis.one] ⊓ 𝐔[Axis.two] :=
    mem_inf.mpr ⟨kappa_mem_U h _ hx1, kappa_mem_U h _ hx2⟩
  rw [hinf, mem_bot] at hκ
  exact mem_ZP_of_mem_F h hxF (kappa_eq_one_iff.mp hκ)

theorem quotient_Fi (h : FCHyp L K n φ t) (i : Axis) :
    ∃ _ : (𝐙.subgroupOf (𝐅 ⊓ 𝐃[i])).Normal,
      ∃ θ : (↥(𝐅 ⊓ 𝐃[i]) ⧸ 𝐙.subgroupOf (𝐅 ⊓ 𝐃[i])) ≃* ↥𝐔[i],
      (∀ x : ↥(𝐅 ⊓ 𝐃[i]), (θ x : G) = t⁻¹ * ((x : G)⁻¹ * t * x)) ∧
      ∀ j ∈ 𝐉, ∀ x : ↥(𝐅 ⊓ 𝐃[i]), ∃ x' : ↥(𝐅 ⊓ 𝐃[i]), (x' : G) = j⁻¹ * x * j ∧
        (θ x' : G) = j⁻¹ * θ x * j :=
  exists_kappa_quotient h (inf_le_left.trans (F_le_H h))
    (fun _ hx => kappa_mem_U h i (mem_inf.mp hx).2) (pull_mono φ (rootU_le_center i))
    (fun _ hx => ⟨fun hxC => mem_ZP_of_mem_F h (mem_inf.mp hx).1 hxC, fun hxZ =>
      h.setup.Q_le_C (mem_sup_left (Setup.ZP_le_PG hxZ))⟩)
    (fun _ hu => exists_kappa_eq_Fi h i hu)
    (fun _ hj _ hx => mem_inf.mpr ⟨conj_torus_mem_F h hj (mem_inf.mp hx).1,
      conj_torus_mem_D h i hj (mem_inf.mp hx).2⟩)


omit [Finite G] [Finite K] [CharP K 2] in
theorem axisTorus_le_J0 (i : Axis) : 𝐉[i] ≤ 𝐉 := pull_mono φ (axisTorus_le i)

omit [Finite G] in
theorem exists_good_axisTorus (h : FCHyp L K n φ t) (i : Axis) :
    ∃ a ∈ 𝐉[i], (∀ z ∈ 𝐙, a⁻¹ * z * a = z → z ∈ 𝐔[i]) ∧
      ∀ u ∈ 𝐔[i.swap], ∃ w ∈ 𝐔[i.swap], a⁻¹ * (w⁻¹ * a * w) = u := by
  have hK2 : 2 < Nat.card K := by have := h.four_le_card; omega
  obtain ⟨r, hr0, hr1⟩ := exists_ne_zero_ne hK2 (1 : K)
  obtain ⟨h1, h2⟩ := one_add_ne_zero (Ne.symm hr1)
  have htwo : (2 : K) = 0 := CharTwo.two_eq_zero
  have hinv : ∀ a w : G, a⁻¹ * (w⁻¹ * a * w) = (a⁻¹ * w * a)⁻¹ * w := fun a w => by group
  cases i
  · obtain ⟨δ, -, hδm⟩ := exists_diagTorus (K := K) hr0 (inv_ne_zero hr0)
    have hconj : ∀ b c : K, ((φ.symm δ : L) : G)⁻¹ * zc φ b c * ((φ.symm δ : L) : G) =
        zc φ b (r ^ 2 * c) := fun b c => by
      rw [conj_zc hr0 (inv_ne_zero hr0) hδm, mul_inv_cancel₀ hr0, one_mul]
    refine ⟨_, symm_mem_pull.mpr ⟨r, hr0, hδm⟩, fun z hz hzz => ?_, fun u hu => ?_⟩
    · obtain ⟨b, c, rfl⟩ := exists_zc hz
      rw [hconj] at hzz
      have hc := (zc_inj hzz).2
      have hc' : (1 + r ^ 2) * c = 0 := by linear_combination hc + c * htwo
      rw [zc_mem_U_one]
      exact (mul_eq_zero.mp hc').resolve_left h2
    · obtain ⟨c, rfl⟩ := exists_coordG_eq φ Axis.two hu
      refine ⟨zc φ 0 (c / (1 + r ^ 2)), zc_mem_U_two.mpr rfl, ?_⟩
      rw [hinv, hconj, zc_inv, zc_mul, coordG_two_eq, add_zero]
      congr 1
      field_simp
      ring
  · obtain ⟨δ, -, hδm⟩ := exists_diagTorus (K := K) one_ne_zero hr0
    have hconj : ∀ b c : K, ((φ.symm δ : L) : G)⁻¹ * zc φ b c * ((φ.symm δ : L) : G) =
        zc φ (r * b) c := fun b c => by
      rw [conj_zc one_ne_zero hr0 hδm, one_mul, one_pow, one_mul]
    refine ⟨_, symm_mem_pull.mpr ⟨r, hr0, hδm⟩, fun z hz hzz => ?_, fun u hu => ?_⟩
    · obtain ⟨b, c, rfl⟩ := exists_zc hz
      rw [hconj] at hzz
      have hb := (zc_inj hzz).1
      have hb' : (1 + r) * b = 0 := by linear_combination hb + b * htwo
      rw [zc_mem_U_two]
      exact (mul_eq_zero.mp hb').resolve_left h1
    · obtain ⟨b, rfl⟩ := exists_coordG_eq φ Axis.one hu
      refine ⟨zc φ (b / (1 + r)) 0, zc_mem_U_one.mpr rfl, ?_⟩
      rw [hinv, hconj, zc_inv, zc_mul, coordG_one_eq, add_zero]
      congr 1
      field_simp
      ring

omit [Finite G] [Finite K] in
theorem W_le_F (i : Axis) : 𝐖[i] ≤ 𝐅 := inf_le_left

omit [Finite G] [Finite K] in
theorem conj_W_eq {i : Axis} {w : G} (hw : w ∈ 𝐖[i]) {b : G} (hb : b ∈ 𝐉[i]) :
    b⁻¹ * w * b = w := by
  rw [mul_assoc, ← mem_centralizer_iff.mp (mem_inf.mp hw).2 b hb, inv_mul_cancel_left]

theorem W_le_Fi (h : FCHyp L K n φ t) (i : Axis) : 𝐖[i] ≤ 𝐅 ⊓ 𝐃[i] := by
  intro w hw
  have hwF := W_le_F i hw
  have hwH := F_le_H h hwF
  obtain ⟨a, haJ, hfix, -⟩ := exists_good_axisTorus h i
  have hκ : a⁻¹ * (t⁻¹ * (w⁻¹ * t * w)) * a = t⁻¹ * (w⁻¹ * t * w) := by
    rw [← kappa_conj_torus h (axisTorus_le_J0 i haJ), conj_W_eq hw haJ]
  obtain ⟨f, hf, hfκ⟩ := exists_kappa_eq_Fi h i (hfix _ (kappa_mem h hwH) hκ)
  have hfF := (mem_inf.mp hf).1
  have hfH := F_le_H h hfF
  have hwf : w * f⁻¹ ∈ 𝐂 := by
    apply kappa_eq_one_iff.mp
    rw [kappa_mul h hwH (inv_mem hfH), kappa_inv h hfH, hfκ, mul_inv_cancel]
  have hz := mem_ZP_of_mem_F h (mul_mem hwF (inv_mem hfF)) hwf
  rw [show w = w * f⁻¹ * f by group]
  exact mul_mem (ZP_le_Fi h i hz) hf

theorem mu_mem_ZP (h : FCHyp L K n φ t) (i : Axis) {f : G} (hf : f ∈ 𝐅 ⊓ 𝐃[i]) {b : G}
    (hb : b ∈ 𝐉[i]) : f⁻¹ * (b⁻¹ * f * b) ∈ 𝐙 := by
  have hbJ := axisTorus_le_J0 i hb
  have hfF := (mem_inf.mp hf).1
  have hfH := F_le_H h hfF
  refine mem_ZP_of_mem_F h (mul_mem (inv_mem hfF) (conj_torus_mem_F h hbJ hfF))
    (kappa_eq_one_iff.mp ?_)
  rw [kappa_mul h (inv_mem hfH) (conj_torus_mem_H h hbJ hfH), kappa_inv h hfH,
    kappa_conj_torus h hbJ, axisTorus_cent i hb (kappa_mem_U h i (mem_inf.mp hf).2),
    inv_mul_cancel]

omit [Finite G] [Finite K] in
theorem odd_card_sub_one (h : FCHyp L K n φ t) : Odd (Nat.card K - 1) := by
  rw [h.setup.card_K]
  exact Nat.Even.sub_odd Nat.one_le_two_pow
    (Nat.even_pow.mpr ⟨even_two, by have := h.setup.two_le; omega⟩) odd_one

theorem mu_mem_U (h : FCHyp L K n φ t) (i : Axis) {f : G} (hf : f ∈ 𝐅 ⊓ 𝐃[i]) {b : G}
    (hb : b ∈ 𝐉[i]) : f⁻¹ * (b⁻¹ * f * b) ∈ 𝐔[i.swap] :=
  mem_of_telescope (fun _ hz => Setup.ZP_mul_self hz) (odd_card_sub_one h)
    (torus_pow_card_sub_one (axisTorus_le_J0 i hb))
    (fun _ hz => conj_torus_mem_ZP (axisTorus_le_J0 i hb) hz) (fun _ hz => axisTorus_mod i hb hz)
    (mu_mem_ZP h i hf hb)

theorem mem_W_of_fix (h : FCHyp L K n φ t) (i : Axis) {a : G} (ha : a ∈ 𝐉[i])
    (hfix : ∀ z ∈ 𝐙, a⁻¹ * z * a = z → z ∈ 𝐔[i]) {w : G} (hw : w ∈ 𝐅 ⊓ 𝐃[i])
    (hwa : a⁻¹ * w * a = w) : w ∈ 𝐖[i] := by
  refine mem_inf.mpr ⟨(mem_inf.mp hw).1, mem_centralizer_iff.mpr fun b hb => ?_⟩
  have hab : a * b = b * a := torus_comm (axisTorus_le_J0 i ha) (axisTorus_le_J0 i hb)
  have hba : a⁻¹ * b * a = b := by rw [mul_assoc, ← hab, inv_mul_cancel_left]
  have hcfix : a⁻¹ * (w⁻¹ * (b⁻¹ * w * b)) * a = w⁻¹ * (b⁻¹ * w * b) := by
    calc a⁻¹ * (w⁻¹ * (b⁻¹ * w * b)) * a
        = (a⁻¹ * w * a)⁻¹ * ((a⁻¹ * b * a)⁻¹ * (a⁻¹ * w * a) * (a⁻¹ * b * a)) := by group
      _ = w⁻¹ * (b⁻¹ * w * b) := by rw [hwa, hba]
  have hc : w⁻¹ * (b⁻¹ * w * b) ∈ 𝐔[i] ⊓ 𝐔[i.swap] :=
    mem_inf.mpr ⟨hfix _ (mu_mem_ZP h i hw hb) hcfix, mu_mem_U h i hw hb⟩
  rw [U_inf_U_swap i, mem_bot] at hc
  have e := inv_mul_eq_one.mp hc
  calc b * w = b * (b⁻¹ * w * b) := by rw [← e]
    _ = w * b := by group

theorem W_eq_centralizer (h : FCHyp L K n φ t) (i : Axis) {a : G} (ha : a ∈ 𝐉[i])
    (hfix : ∀ z ∈ 𝐙, a⁻¹ * z * a = z → z ∈ 𝐔[i]) :
    𝐖[i] = centralizer ({a} : Set G) ⊓ (𝐅 ⊓ 𝐃[i]) := by
  apply le_antisymm
  · intro w hw
    refine mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr ?_, W_le_Fi h i hw⟩
    exact (mem_centralizer_iff.mp (mem_inf.mp hw).2 a ha).symm
  · intro w hw
    obtain ⟨hwa, hwF⟩ := mem_inf.mp hw
    refine mem_W_of_fix h i ha hfix hwF ?_
    rw [mem_centralizer_singleton_iff] at hwa
    rw [mul_assoc, hwa, inv_mul_cancel_left]

theorem card_W (h : FCHyp L K n φ t) (i : Axis) : Nat.card 𝐖[i] = Nat.card K ^ 2 := by
  obtain ⟨a, haJ, hfix, hsurj⟩ := exists_good_axisTorus h i
  have h1 := card_eq_of_conj_surj (X := 𝐅 ⊓ 𝐃[i]) (U := 𝐔[i.swap]) (t := a)
    (fun x hx => by
      have := inv_mem (mu_mem_U h i hx haJ)
      rwa [show (x⁻¹ * (a⁻¹ * x * a))⁻¹ = a⁻¹ * (x⁻¹ * a * x) by group] at this)
    (fun u hu => by
      obtain ⟨w, hw, hwu⟩ := hsurj u hu
      exact ⟨w, ZP_le_Fi h i (pull_mono φ (rootU_le_center _) hw), hwu⟩)
  rw [← W_eq_centralizer h i haJ hfix, card_Fi h, FCHyp.card_U] at h1
  have hq : 0 < Nat.card K := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hq (by rw [← h1]; ring)

theorem U_le_W (h : FCHyp L K n φ t) (i : Axis) : 𝐔[i] ≤ 𝐖[i] := fun u hu =>
  mem_inf.mpr ⟨ZP_le_F h (pull_mono φ (rootU_le_center i) hu), mem_centralizer_iff.mpr
    fun b hb => by
      have e := axisTorus_cent i hb hu
      calc b * u = b * (b⁻¹ * u * b) := by rw [e]
        _ = u * b := by group⟩

theorem W_inf_ZP (h : FCHyp L K n φ t) (i : Axis) : 𝐖[i] ⊓ 𝐙 = 𝐔[i] := by
  refine le_antisymm (fun z hz => ?_) (le_inf (U_le_W h i) (pull_mono φ (rootU_le_center i)))
  obtain ⟨a, haJ, hfix, -⟩ := exists_good_axisTorus h i
  exact hfix z (mem_inf.mp hz).2 (conj_W_eq (mem_inf.mp hz).1 haJ)

theorem W_inf_C (h : FCHyp L K n φ t) (i : Axis) : 𝐖[i] ⊓ 𝐂 = 𝐔[i] := by
  rw [← W_inf_ZP h i]
  refine le_antisymm (fun x hx => ?_) (inf_le_inf_left _ fun z hz =>
    h.setup.Q_le_C (mem_sup_left (Setup.ZP_le_PG hz)))
  exact mem_inf.mpr ⟨(mem_inf.mp hx).1, mem_ZP_of_mem_F h (W_le_F i (mem_inf.mp hx).1)
    (mem_inf.mp hx).2⟩

theorem W_inf_U_swap (h : FCHyp L K n φ t) (i : Axis) : 𝐖[i] ⊓ 𝐔[i.swap] = ⊥ := by
  rw [← U_inf_U_swap (φ := φ) i, ← W_inf_ZP h i]
  exact le_antisymm (le_inf (le_inf inf_le_left
    (inf_le_right.trans (pull_mono φ (rootU_le_center _)))) inf_le_right)
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right)

theorem conj_torus_mem_W (h : FCHyp L K n φ t) (i : Axis) {j : G} (hj : j ∈ 𝐉) {w : G}
    (hw : w ∈ 𝐖[i]) : j⁻¹ * w * j ∈ 𝐖[i] := by
  refine mem_inf.mpr ⟨conj_torus_mem_F h hj (W_le_F i hw), mem_centralizer_iff.mpr
    fun b hb => ?_⟩
  have hbj : b * j = j * b := torus_comm (axisTorus_le_J0 i hb) hj
  have hbw := mem_centralizer_iff.mp (mem_inf.mp hw).2 b hb
  calc b * (j⁻¹ * w * j) = j⁻¹ * (j * b * j⁻¹) * w * j := by group
    _ = j⁻¹ * b * w * j := by rw [← hbj, mul_inv_cancel_right]
    _ = j⁻¹ * w * b * j := by rw [mul_assoc j⁻¹, hbw, ← mul_assoc]
    _ = j⁻¹ * w * j * b := by rw [mul_assoc (j⁻¹ * w), hbj, ← mul_assoc]

omit [Finite G] [Finite K] in
theorem t_comm_torus (h : FCHyp L K n φ t) {j : G} (hj : j ∈ 𝐉) : t * j = j * t :=
  (torus_comm_t h hj).symm

theorem conj_t_mem_W (h : FCHyp L K n φ t) (i : Axis) {w : G} (hw : w ∈ 𝐖[i]) :
    t * w * t⁻¹ ∈ 𝐖[i] := by
  refine mem_inf.mpr ⟨conj_H_mem_F h t_mem_H (W_le_F i hw), mem_centralizer_iff.mpr
    fun b hb => ?_⟩
  have htb := t_comm_torus h (axisTorus_le_J0 i hb)
  have hbw := mem_centralizer_iff.mp (mem_inf.mp hw).2 b hb
  have htb' : b * t⁻¹ = t⁻¹ * b := by
    rw [h.twoCore.t_inv]
    exact htb.symm
  calc b * (t * w * t⁻¹) = t * (b * w) * t⁻¹ := by rw [← mul_assoc, ← mul_assoc, ← htb]; group
    _ = t * w * (b * t⁻¹) := by rw [hbw]; group
    _ = t * w * t⁻¹ * b := by rw [htb']; group

theorem t_mem_normalizer_W (h : FCHyp L K n φ t) (i : Axis) :
    t ∈ normalizer (𝐖[i] : Set G) :=
  RootAxisTwoCore.mem_normalizer_of_conj_le fun _ hw => conj_t_mem_W h i hw

theorem exists_kappa_eq_W (h : FCHyp L K n φ t) (i : Axis) {u : G} (hu : u ∈ 𝐔[i]) :
    ∃ w ∈ 𝐖[i], t⁻¹ * (w⁻¹ * t * w) = u :=
  exists_conj_eq_of_card (fun _ hw => kappa_mem_U h i (mem_inf.mp (W_le_Fi h i hw)).2)
    (by rw [inf_comm 𝐂 𝐖[i], W_inf_C h i, card_W h i, FCHyp.card_U]; ring) hu

theorem quotient_W (h : FCHyp L K n φ t) (i : Axis) :
    ∃ _ : (𝐔[i].subgroupOf 𝐖[i]).Normal, ∃ θ : (↥𝐖[i] ⧸ 𝐔[i].subgroupOf 𝐖[i]) ≃* ↥𝐔[i],
      (∀ x : 𝐖[i], (θ x : G) = t⁻¹ * ((x : G)⁻¹ * t * x)) ∧
      ∀ j ∈ 𝐉, ∀ x : 𝐖[i], ∃ x' : 𝐖[i], (x' : G) = j⁻¹ * x * j ∧ (θ x' : G) = j⁻¹ * θ x * j :=
  exists_kappa_quotient h ((W_le_F i).trans (F_le_H h))
    (fun _ hw => kappa_mem_U h i (mem_inf.mp (W_le_Fi h i hw)).2)
    (pull_mono φ (rootU_le_center i))
    (fun x hx => by rw [← W_inf_C h i]; exact ⟨fun hxC => ⟨hx, hxC⟩, fun hxU => hxU.2⟩)
    (fun _ hu => exists_kappa_eq_W h i hu) (fun _ hj _ hw => conj_torus_mem_W h i hj hw)

theorem W_mul_U (h : FCHyp L K n φ t) (i : Axis) :
    (𝐖[i] : Set G) * (𝐔[i.swap] : Set G) = ((𝐅 ⊓ 𝐃[i] : Subgroup G) : Set G) := by
  have hc : ∀ x ∈ 𝐖[i], ∀ y ∈ 𝐔[i.swap], x * y = y * x := fun x hx y hy =>
    comm_ZP h (F_le_H h (W_le_F i hx)) (pull_mono φ (rootU_le_center _) hy)
  have hsup : 𝐖[i] ⊔ 𝐔[i.swap] = 𝐅 ⊓ 𝐃[i] := by
    refine eq_of_le_of_card_ge (sup_le (W_le_Fi h i)
      ((pull_mono φ (rootU_le_center _)).trans (ZP_le_Fi h i))) ?_
    rw [card_sup_of_commute hc (W_inf_U_swap h i), card_W h i, FCHyp.card_U, card_Fi h]
    ring_nf
    exact le_rfl
  rw [← coe_mul_of_left_le_normalizer_right _ _ (le_normalizer_of_commute hc), hsup]

theorem comm_mul_right (h : FCHyp L K n φ t) {w x y : G} (hw : w ∈ 𝐇) (hx : x ∈ 𝐇)
    (hy : y ∈ 𝐇) :
    w⁻¹ * ((x * y)⁻¹ * w * (x * y)) = w⁻¹ * (x⁻¹ * w * x) * (w⁻¹ * (y⁻¹ * w * y)) := by
  have hc := commutator_mem_ZP h hw hx
  have hcy := comm_ZP h hy hc
  have hcc := comm_ZP h (ZP_le_H (commutator_mem_ZP h hw hy)) hc
  have e : y⁻¹ * (w⁻¹ * (x⁻¹ * w * x)) * y = w⁻¹ * (x⁻¹ * w * x) := by
    rw [mul_assoc, ← hcy, inv_mul_cancel_left]
  calc w⁻¹ * ((x * y)⁻¹ * w * (x * y))
      = w⁻¹ * (y⁻¹ * w * y) * (y⁻¹ * (w⁻¹ * (x⁻¹ * w * x)) * y) := by group
    _ = w⁻¹ * (y⁻¹ * w * y) * (w⁻¹ * (x⁻¹ * w * x)) := by rw [e]
    _ = w⁻¹ * (x⁻¹ * w * x) * (w⁻¹ * (y⁻¹ * w * y)) := hcc

theorem comm_mem_U (h : FCHyp L K n φ t) (i : Axis) {w : G} (hw : w ∈ 𝐖[i]) {x : G}
    (hx : x ∈ 𝐖[i.swap]) : w⁻¹ * (x⁻¹ * w * x) ∈ 𝐔[i.swap] := by
  obtain ⟨a, haJ, -, hsurj⟩ := exists_good_axisTorus h i
  have haJ0 := axisTorus_le_J0 i haJ
  have hwa := conj_W_eq hw haJ
  have hwH := F_le_H h (W_le_F i hw)
  have hxF := W_le_F i.swap hx
  have hxH := F_le_H h hxF
  have hκx := kappa_mem_U h i.swap (mem_inf.mp (W_le_Fi h i.swap hx)).2
  obtain ⟨v, hv, hva⟩ := hsurj _ (inv_mem hκx)
  obtain ⟨y, hy, hyv⟩ := exists_kappa_eq_W h i.swap hv
  have hyH := F_le_H h (W_le_F i.swap hy)
  set d := y⁻¹ * (a⁻¹ * y * a) with hd
  have hdF : d ∈ 𝐅 := mul_mem (inv_mem (W_le_F i.swap hy))
    (conj_torus_mem_F h haJ0 (W_le_F i.swap hy))
  have hdH := F_le_H h hdF
  have hκd : t⁻¹ * (d⁻¹ * t * d) = t⁻¹ * (x⁻¹ * t * x) := by
    rw [hd, kappa_delta h haJ0 hyH, hyv]
    have e1 : v⁻¹ * (a⁻¹ * v * a) = (a⁻¹ * (v⁻¹ * a * v))⁻¹ := by group
    rw [e1, hva, inv_inv]
  have hu : d⁻¹ * x ∈ 𝐙 := by
    refine mem_ZP_of_mem_F h (mul_mem (inv_mem hdF) hxF) (kappa_eq_one_iff.mp ?_)
    rw [kappa_mul h (inv_mem hdH) hxH, kappa_inv h hdH, hκd, inv_mul_cancel]
  have huH : d⁻¹ * x ∈ 𝐇 := ZP_le_H hu
  have hc0 : w⁻¹ * ((d⁻¹ * x)⁻¹ * w * (d⁻¹ * x)) = 1 := by
    rw [mul_assoc _ w, comm_ZP h hwH hu, inv_mul_cancel_left, inv_mul_cancel]
  have hconj : w⁻¹ * ((a⁻¹ * y * a)⁻¹ * w * (a⁻¹ * y * a)) =
      a⁻¹ * (w⁻¹ * (y⁻¹ * w * y)) * a := by
    calc w⁻¹ * ((a⁻¹ * y * a)⁻¹ * w * (a⁻¹ * y * a))
        = (a⁻¹ * w * a)⁻¹ * ((a⁻¹ * y * a)⁻¹ * (a⁻¹ * w * a) * (a⁻¹ * y * a)) := by rw [hwa]
      _ = a⁻¹ * (w⁻¹ * (y⁻¹ * w * y)) * a := by group
  have e2 : a⁻¹ * y * a = y * d := by rw [hd]; group
  have hcd : w⁻¹ * (d⁻¹ * w * d) =
      (w⁻¹ * (y⁻¹ * w * y))⁻¹ * (a⁻¹ * (w⁻¹ * (y⁻¹ * w * y)) * a) := by
    rw [← hconj, e2, comm_mul_right h hwH hyH hdH, inv_mul_cancel_left]
  have hU := axisTorus_mod i haJ (commutator_mem_ZP h hwH hyH)
  rw [← hcd] at hU
  rw [show x = d * (d⁻¹ * x) by group, comm_mul_right h hwH hdH huH, hc0, mul_one]
  exact hU

theorem W_comm (h : FCHyp L K n φ t) {x y : G} (hx : x ∈ 𝐖[Axis.one]) (hy : y ∈ 𝐖[Axis.two]) :
    x * y = y * x := by
  have h1 := comm_mem_U h Axis.one hx hy
  have h2 := comm_mem_U h Axis.two hy hx
  have e : x⁻¹ * (y⁻¹ * x * y) = (y⁻¹ * (x⁻¹ * y * x))⁻¹ := by group
  have hc : x⁻¹ * (y⁻¹ * x * y) ∈ 𝐔[Axis.one] ⊓ 𝐔[Axis.two] :=
    mem_inf.mpr ⟨by rw [e]; exact inv_mem h2, h1⟩
  rw [U_inf_U, mem_bot] at hc
  calc x * y = y * x * (x⁻¹ * (y⁻¹ * x * y)) := by group
    _ = y * x := by rw [hc, mul_one]

theorem W_inf_W (h : FCHyp L K n φ t) : 𝐖[Axis.one] ⊓ 𝐖[Axis.two] = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hx1, hx2⟩ := mem_inf.mp hx
  have hxZ : x ∈ 𝐙 := by
    rw [← Fi_inf_Fi h]
    exact mem_inf.mpr ⟨W_le_Fi h _ hx1, W_le_Fi h _ hx2⟩
  have h1 : x ∈ 𝐔[Axis.one] := by rw [← W_inf_ZP h]; exact mem_inf.mpr ⟨hx1, hxZ⟩
  have h2 : x ∈ 𝐔[Axis.two] := by rw [← W_inf_ZP h]; exact mem_inf.mpr ⟨hx2, hxZ⟩
  have := mem_inf.mpr ⟨h1, h2⟩
  rwa [U_inf_U] at this

theorem W_mul_W (h : FCHyp L K n φ t) :
    (𝐖[Axis.one] : Set G) * (𝐖[Axis.two] : Set G) = 𝐅 := by
  have hc : ∀ x ∈ 𝐖[Axis.one], ∀ y ∈ 𝐖[Axis.two], x * y = y * x := fun _ hx _ hy =>
    W_comm h hx hy
  have hsup : 𝐖[Axis.one] ⊔ 𝐖[Axis.two] = 𝐅 := by
    refine eq_of_le_of_card_ge (sup_le (W_le_F _) (W_le_F _)) ?_
    rw [card_sup_of_commute hc (W_inf_W h), card_W h, card_W h, card_F h]
    ring_nf
    exact le_rfl
  rw [← coe_mul_of_left_le_normalizer_right _ _ (le_normalizer_of_commute hc), hsup]

end Kappa



end FullCenterTorus

end CFSG.LocalAnalysis.SymplecticFourStandard

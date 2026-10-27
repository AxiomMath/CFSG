module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715L

open Module Matrix

section Coord

variable {K L : Type*} [Field K] [AddCommGroup L] [Module K L]

@[expose] def contr (d : Fin 2 → K) : (Fin 2 → L) →ₗ[K] L where
  toFun x := d 0 • x 0 + d 1 • x 1
  map_add' x y := by
    simp only [Pi.add_apply, smul_add]
    abel
  map_smul' c x := by
    simp only [Pi.smul_apply, RingHom.id_apply, smul_add]
    rw [smul_comm (d 0) c, smul_comm (d 1) c]

theorem contr_apply (d : Fin 2 → K) (x : Fin 2 → L) : contr d x = d 0 • x 0 + d 1 • x 1 := rfl

@[expose] def pureT (f : Fin 2 → K) : L →ₗ[K] (Fin 2 → L) where
  toFun n i := f i • n
  map_add' n n' := funext fun i => smul_add (f i) n n'
  map_smul' c n := funext fun i => by
    simp only [Pi.smul_apply, RingHom.id_apply]
    rw [smul_comm]

theorem pureT_apply (f : Fin 2 → K) (n : L) (i : Fin 2) : pureT f n i = f i • n := rfl

theorem contr_pureT (d f : Fin 2 → K) (n : L) :
    contr d (pureT f n) = (d 0 * f 0 + d 1 * f 1) • n := by
  rw [contr_apply, pureT_apply, pureT_apply, smul_smul, smul_smul, add_smul]

theorem contr_surjective {d : Fin 2 → K} (hd : d ≠ 0) :
    Function.Surjective (contr d : (Fin 2 → L) →ₗ[K] L) := by
  intro y
  by_cases h0 : d 0 = 0
  · have h1 : d 1 ≠ 0 := by
      intro h1
      exact hd (funext fun i => by fin_cases i <;> simp [h0, h1])
    refine ⟨![0, (d 1)⁻¹ • y], ?_⟩
    simp [contr_apply, smul_smul, h1]
  · refine ⟨![(d 0)⁻¹ • y, 0], ?_⟩
    simp [contr_apply, smul_smul, h0]

theorem pureT_injective {f : Fin 2 → K} (hf : f ≠ 0) :
    Function.Injective (pureT f : L →ₗ[K] (Fin 2 → L)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro n hn
  obtain ⟨i, hi⟩ : ∃ i, f i ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (funext h)
  have h1 := congrFun hn i
  rw [pureT_apply, Pi.zero_apply] at h1
  exact (smul_eq_zero.mp h1).resolve_left hi

theorem finrank_comap_contr_span [FiniteDimensional K L] {d : Fin 2 → K} (hd : d ≠ 0) {n : L}
    (hn : n ≠ 0) :
    finrank K (Submodule.comap (contr d) (K ∙ n)) = finrank K L + 1 := by
  set c := (contr d : (Fin 2 → L) →ₗ[K] L) with hc
  have hsurj := contr_surjective (L := L) hd
  have hker : LinearMap.ker c ≤ Submodule.comap c (K ∙ n) := fun x hx => by
    rw [Submodule.mem_comap, LinearMap.mem_ker.mp hx]
    exact Submodule.zero_mem _
  have hrn := LinearMap.finrank_range_add_finrank_ker (c.domRestrict (Submodule.comap c (K ∙ n)))
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict,
    LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hker),
    Submodule.map_comap_eq_of_surjective hsurj, finrank_span_singleton hn] at hrn
  have hrn' := LinearMap.finrank_range_add_finrank_ker c
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at hrn'
  have e : finrank K (Fin 2 → L) = 2 * finrank K L := by
    rw [Module.finrank_pi_fintype, Fin.sum_univ_two, two_mul]
  omega

theorem eq_smul_of_map_pureT_eq {d d' : Fin 2 → K} (hd : d ≠ 0) (hd' : d' ≠ 0)
    {S S' : Submodule K L} (hS : S ≠ ⊥)
    (h : S.map (pureT d) = S'.map (pureT d')) : (∃ c : K, c ≠ 0 ∧ d' = c • d) ∧ S = S' := by
  obtain ⟨k, hkS, hk0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
  have hk : pureT d k ∈ S'.map (pureT d') := h ▸ Submodule.mem_map_of_mem hkS
  obtain ⟨k', hk'S, hkk'⟩ := Submodule.mem_map.mp hk
  have hcomp : ∀ i, d' i • k' = d i • k := fun i => congrFun hkk' i
  obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hd (funext hh)
  have hd'i : d' i ≠ 0 := by
    intro h0
    have := hcomp i
    rw [h0, zero_smul, eq_comm] at this
    exact hk0 ((smul_eq_zero.mp this).resolve_left hi)
  set lam := (d i)⁻¹ * d' i with hlam
  have hkk : k = lam • k' := by
    rw [hlam, mul_smul, hcomp i, smul_smul, inv_mul_cancel₀ hi, one_smul]
  have hk'0 : k' ≠ 0 := by
    intro h0
    rw [h0, smul_zero] at hkk
    exact hk0 hkk
  have hlam0 : lam ≠ 0 := mul_ne_zero (inv_ne_zero hi) hd'i
  have hdd : d' = lam • d := by
    funext j
    have h1 := hcomp j
    rw [hkk, smul_smul] at h1
    have h2 : (d' j - d j * lam) • k' = 0 := by
      rw [sub_smul, h1, sub_self]
    have h3 := (smul_eq_zero.mp h2).resolve_right hk'0
    rw [Pi.smul_apply, smul_eq_mul, mul_comm]
    exact sub_eq_zero.mp h3
  refine ⟨⟨lam, hlam0, hdd⟩, ?_⟩
  have hpure : ∀ x : L, pureT d x = pureT d' (lam⁻¹ • x) := fun x => by
    funext j
    rw [pureT_apply, pureT_apply, hdd, Pi.smul_apply, smul_eq_mul, smul_smul, mul_right_comm,
      mul_inv_cancel₀ hlam0, one_mul]
  have hinj := pureT_injective (L := L) hd'
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · have h1 : pureT d x ∈ S'.map (pureT d') := h ▸ Submodule.mem_map_of_mem hx
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp h1
    rw [hpure] at hyx
    have h2 := hinj hyx
    rw [h2] at hy
    have h3 := S'.smul_mem lam hy
    rwa [smul_smul, mul_inv_cancel₀ hlam0, one_smul] at h3
  · have h1 : pureT d (lam • x) ∈ S'.map (pureT d') := by
      rw [hpure, smul_smul, inv_mul_cancel₀ hlam0, one_smul]
      exact Submodule.mem_map_of_mem hx
    rw [← h] at h1
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp h1
    have h2 := pureT_injective (L := L) hd hyx
    rw [h2] at hy
    have h3 := S.smul_mem lam⁻¹ hy
    rwa [smul_smul, inv_mul_cancel₀ hlam0, one_smul] at h3

end Coord

section Pairing

variable {K L₃ L₄ U : Type*} [Field K] [AddCommGroup L₃] [Module K L₃] [AddCommGroup L₄]
  [Module K L₄] [AddCommGroup U] [Module K U]

@[expose] def betaMu (μ : L₃ →ₗ[K] L₄ →ₗ[K] U) (x : Fin 2 → L₄) : (Fin 2 → L₃) →ₗ[K] U where
  toFun m := μ (m 0) (x 0) + μ (m 1) (x 1)
  map_add' m m' := by
    simp only [Pi.add_apply, map_add, LinearMap.add_apply]
    abel
  map_smul' c m := by
    simp only [Pi.smul_apply, map_smul, LinearMap.smul_apply, RingHom.id_apply, smul_add]

theorem betaMu_apply (μ : L₃ →ₗ[K] L₄ →ₗ[K] U) (x : Fin 2 → L₄) (m : Fin 2 → L₃) :
    betaMu μ x m = μ (m 0) (x 0) + μ (m 1) (x 1) := rfl

theorem range_betaMu (μ : L₃ →ₗ[K] L₄ →ₗ[K] U) (x : Fin 2 → L₄) :
    LinearMap.range (betaMu μ x) =
      LinearMap.range (μ.flip (x 0)) ⊔ LinearMap.range (μ.flip (x 1)) := by
  apply le_antisymm
  · rintro _ ⟨m, rfl⟩
    rw [betaMu_apply]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self _ _) (LinearMap.mem_range_self _ _)
  · refine sup_le ?_ ?_
    · rintro _ ⟨a, rfl⟩
      refine ⟨![a, 0], ?_⟩
      simp [betaMu_apply]
    · rintro _ ⟨a, rfl⟩
      refine ⟨![0, a], ?_⟩
      simp [betaMu_apply]

theorem betaMu_pureT (μ : L₃ →ₗ[K] L₄ →ₗ[K] U) (x : Fin 2 → L₄) (d : Fin 2 → K) (k : L₃) :
    betaMu μ x (pureT d k) = μ k (contr d x) := by
  rw [betaMu_apply, pureT_apply, pureT_apply, contr_apply, map_smul, map_smul, map_add, map_smul,
    map_smul, LinearMap.smul_apply, LinearMap.smul_apply]

theorem exists_eq_pureT_of_finrank_range_le [FiniteDimensional K U] (q : L₄ → K)
    (μ : L₃ →ₗ[K] L₄ →ₗ[K] U)
    (hns : ∀ c : L₄, c ≠ 0 → q c ≠ 0 → 4 < finrank K (LinearMap.range (μ.flip c)))
    (hs : ∀ c : L₄, c ≠ 0 → q c = 0 → finrank K (LinearMap.range (μ.flip c)) = 4)
    (hdet : ∀ c c' : L₄, c ≠ 0 → c' ≠ 0 → q c = 0 → q c' = 0 →
      LinearMap.range (μ.flip c) = LinearMap.range (μ.flip c') → ∃ a : K, c' = a • c)
    {x : Fin 2 → L₄} (hx : x ≠ 0) (hrk : finrank K (LinearMap.range (betaMu μ x)) ≤ 4) :
    ∃ (f : Fin 2 → K) (n : L₄), f ≠ 0 ∧ n ≠ 0 ∧ q n = 0 ∧ x = pureT f n := by
  rw [range_betaMu] at hrk
  have hle0 : LinearMap.range (μ.flip (x 0)) ≤
      LinearMap.range (μ.flip (x 0)) ⊔ LinearMap.range (μ.flip (x 1)) := le_sup_left
  have hle1 : LinearMap.range (μ.flip (x 1)) ≤
      LinearMap.range (μ.flip (x 0)) ⊔ LinearMap.range (μ.flip (x 1)) := le_sup_right
  have hsing : ∀ i, x i ≠ 0 → q (x i) = 0 := by
    intro i hi
    by_contra hq
    have h1 := hns (x i) hi hq
    have h2 : finrank K (LinearMap.range (μ.flip (x i))) ≤ 4 := by
      fin_cases i
      · exact (Submodule.finrank_mono hle0).trans hrk
      · exact (Submodule.finrank_mono hle1).trans hrk
    omega
  by_cases h0 : x 0 = 0
  · have h1 : x 1 ≠ 0 := by
      intro h1
      exact hx (funext fun i => by fin_cases i <;> simp [h0, h1])
    refine ⟨![0, 1], x 1, by simp [funext_iff, Fin.forall_fin_two], h1, hsing 1 h1, ?_⟩
    funext i
    fin_cases i <;> simp [pureT_apply, h0]
  by_cases h1 : x 1 = 0
  · refine ⟨![1, 0], x 0, by simp [funext_iff, Fin.forall_fin_two], h0, hsing 0 h0, ?_⟩
    funext i
    fin_cases i <;> simp [pureT_apply, h1]
  have hr0 := hs (x 0) h0 (hsing 0 h0)
  have hr1 := hs (x 1) h1 (hsing 1 h1)
  have he0 : LinearMap.range (μ.flip (x 0)) =
      LinearMap.range (μ.flip (x 0)) ⊔ LinearMap.range (μ.flip (x 1)) :=
    Submodule.eq_of_le_of_finrank_le hle0 (by omega)
  have he1 : LinearMap.range (μ.flip (x 1)) =
      LinearMap.range (μ.flip (x 0)) ⊔ LinearMap.range (μ.flip (x 1)) :=
    Submodule.eq_of_le_of_finrank_le hle1 (by omega)
  obtain ⟨a, ha⟩ := hdet (x 0) (x 1) h0 h1 (hsing 0 h0) (hsing 1 h1) (he0.trans he1.symm)
  refine ⟨![1, a], x 0, by simp [funext_iff, Fin.forall_fin_two], h0, hsing 0 h0, ?_⟩
  funext i
  fin_cases i <;> simp [pureT_apply, ha]

theorem le_ker_flip_iff [FiniteDimensional K L₃] (q : L₄ → K) (μ : L₃ →ₗ[K] L₄ →ₗ[K] U)
    (hns : ∀ c : L₄, c ≠ 0 → q c ≠ 0 → LinearMap.ker (μ.flip c) = ⊥)
    (hs : ∀ c c' : L₄, c ≠ 0 → c' ≠ 0 → q c = 0 → q c' = 0 →
      finrank K (LinearMap.ker (μ.flip c)) = finrank K (LinearMap.ker (μ.flip c')))
    (hpos : ∀ c : L₄, c ≠ 0 → q c = 0 → LinearMap.ker (μ.flip c) ≠ ⊥)
    (hdet : ∀ c c' : L₄, c ≠ 0 → c' ≠ 0 → q c = 0 → q c' = 0 →
      LinearMap.ker (μ.flip c) = LinearMap.ker (μ.flip c') → ∃ a : K, c' = a • c)
    {n : L₄} (hn : n ≠ 0) (hqn : q n = 0) (m : L₄) :
    LinearMap.ker (μ.flip n) ≤ LinearMap.ker (μ.flip m) ↔ m ∈ K ∙ n := by
  constructor
  · intro hle
    by_cases hm : m = 0
    · rw [hm]
      exact Submodule.zero_mem _
    by_cases hqm : q m = 0
    · have heq : LinearMap.ker (μ.flip n) = LinearMap.ker (μ.flip m) :=
        Submodule.eq_of_le_of_finrank_eq hle (hs n m hn hm hqn hqm)
      obtain ⟨a, ha⟩ := hdet n m hn hm hqn hqm heq
      rw [ha]
      exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self n)
    · exfalso
      rw [hns m hm hqm, le_bot_iff] at hle
      exact hpos n hn hqn hle
  · intro hm
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hm
    intro k hk
    rw [LinearMap.mem_ker] at hk ⊢
    rw [LinearMap.flip_apply] at hk ⊢
    rw [map_smul, hk, smul_zero]

theorem forall_betaMu_pureT_eq_zero_iff [FiniteDimensional K L₃] (q : L₄ → K)
    (μ : L₃ →ₗ[K] L₄ →ₗ[K] U)
    (hns : ∀ c : L₄, c ≠ 0 → q c ≠ 0 → LinearMap.ker (μ.flip c) = ⊥)
    (hs : ∀ c c' : L₄, c ≠ 0 → c' ≠ 0 → q c = 0 → q c' = 0 →
      finrank K (LinearMap.ker (μ.flip c)) = finrank K (LinearMap.ker (μ.flip c')))
    (hpos : ∀ c : L₄, c ≠ 0 → q c = 0 → LinearMap.ker (μ.flip c) ≠ ⊥)
    (hdet : ∀ c c' : L₄, c ≠ 0 → c' ≠ 0 → q c = 0 → q c' = 0 →
      LinearMap.ker (μ.flip c) = LinearMap.ker (μ.flip c') → ∃ a : K, c' = a • c)
    {n : L₄} (hn : n ≠ 0) (hqn : q n = 0) (d : Fin 2 → K) (x : Fin 2 → L₄) :
    (∀ k ∈ LinearMap.ker (μ.flip n), betaMu μ x (pureT d k) = 0) ↔
      contr d x ∈ K ∙ n := by
  rw [← le_ker_flip_iff q μ hns hs hpos hdet hn hqn]
  refine ⟨fun h k hk => ?_, fun h k hk => ?_⟩
  · rw [LinearMap.mem_ker, LinearMap.flip_apply, ← betaMu_pureT]
    exact h k hk
  · rw [betaMu_pureT, ← LinearMap.flip_apply]
    exact LinearMap.mem_ker.mp (h hk)

end Pairing

section TwoDim

variable {K : Type*} [Field K]

theorem exists_eq_smul_of_dotProduct_eq_zero {a u v : Fin 2 → K} (ha : a ≠ 0) (hu0 : u ≠ 0)
    (hu : a ⬝ᵥ u = 0) (hv : a ⬝ᵥ v = 0) : ∃ c : K, v = c • u := by
  simp only [dotProduct, Fin.sum_univ_two] at hu hv
  by_cases ha0 : a 0 = 0
  · have ha1 : a 1 ≠ 0 := by
      intro ha1
      exact ha (funext fun i => by fin_cases i <;> simp [ha0, ha1])
    rw [ha0, zero_mul, zero_add] at hu hv
    have hu1 : u 1 = 0 := (mul_eq_zero.mp hu).resolve_left ha1
    have hv1 : v 1 = 0 := (mul_eq_zero.mp hv).resolve_left ha1
    have hu0' : u 0 ≠ 0 := by
      intro h
      exact hu0 (funext fun i => by fin_cases i <;> simp [h, hu1])
    refine ⟨v 0 / u 0, funext fun i => ?_⟩
    fin_cases i
    · simp [div_mul_cancel₀ _ hu0']
    · simp [hu1, hv1]
  · have hu0eq : u 0 = -(a 1 * u 1) / a 0 := by
      field_simp
      linear_combination hu
    have hv0eq : v 0 = -(a 1 * v 1) / a 0 := by
      field_simp
      linear_combination hv
    have hu1 : u 1 ≠ 0 := by
      intro h
      exact hu0 (funext fun i => by fin_cases i <;> simp [hu0eq, h])
    refine ⟨v 1 / u 1, funext fun i => ?_⟩
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, smul_eq_mul]
      rw [hv0eq, hu0eq]
      field_simp
    · simp [div_mul_cancel₀ _ hu1]

theorem dotProduct_mulVec_self_eq_zero_of_isotropic {φ ψ : Matrix (Fin 2) (Fin 2) K}
    (hφ : φᵀ = φ) (hφψ : φ * ψ = 1) {d g : Fin 2 → K} (hg : g ≠ 0) (hdg : d ⬝ᵥ g = 0)
    (hgg : g ⬝ᵥ (ψ *ᵥ g) = 0) : (φ *ᵥ d) ⬝ᵥ (ψ *ᵥ (φ *ᵥ d)) = 0 := by
  have hψφ : ψ * φ = 1 := mul_eq_one_comm.mp hφψ
  have hψ : ψᵀ = ψ := by
    have h1 : ψᵀ * φ = 1 := by
      rw [← hφ, ← Matrix.transpose_mul, hφψ, Matrix.transpose_one]
    calc ψᵀ = ψᵀ * (φ * ψ) := by rw [hφψ, Matrix.mul_one]
      _ = ψᵀ * φ * ψ := by rw [Matrix.mul_assoc]
      _ = ψ := by rw [h1, Matrix.one_mul]
  have hsym : ∀ (A : Matrix (Fin 2) (Fin 2) K), Aᵀ = A → ∀ u v : Fin 2 → K,
      u ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ (A *ᵥ u) := by
    intro A hA u v
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA, dotProduct_comm]
  set e := ψ *ᵥ g with he
  have hφe : φ *ᵥ e = g := by
    rw [he, Matrix.mulVec_mulVec, hφψ, Matrix.one_mulVec]
  have he0 : e ≠ 0 := by
    intro h
    rw [h, Matrix.mulVec_zero] at hφe
    exact hg hφe.symm
  have h1 : g ⬝ᵥ e = 0 := by
    rw [he, hgg]
  have h2 : g ⬝ᵥ d = 0 := by rw [dotProduct_comm, hdg]
  obtain ⟨c, hc⟩ := exists_eq_smul_of_dotProduct_eq_zero hg he0 h1 h2
  have h3 : d ⬝ᵥ (φ *ᵥ d) = 0 := by
    rw [hc, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, hφe, dotProduct_comm, h1,
      smul_zero, smul_zero]
  rw [Matrix.mulVec_mulVec, hψφ, Matrix.one_mulVec, dotProduct_comm]
  exact h3

end TwoDim

section Isotropic

variable {K X : Type*} [Field K] [AddCommGroup X] [Module K X] [FiniteDimensional K X]

theorem two_mul_finrank_le_add_inf_ker_of_isotropic (b : LinearMap.BilinForm K X)
    {T : Submodule K X} (hT : ∀ x ∈ T, ∀ y ∈ T, b x y = 0) :
    2 * finrank K T ≤ finrank K X + finrank K (T ⊓ LinearMap.ker b : Submodule K X) := by
  have h1 := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := b) T
  have h2 : T ≤ b.orthogonal T := fun y hy => by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    exact fun x hx => hT x hx y hy
  have h3 := Submodule.finrank_mono h2
  omega

end Isotropic

section Root

variable {K L H : Type*} [Field K] [AddCommGroup L] [Module K L] [Group H]

@[expose] def rootN (f : Fin 2 → K) : Matrix (Fin 2) (Fin 2) K :=
  Matrix.of fun i j => f i * ![f 1, -f 0] j

@[expose] def det2 (f f' : Fin 2 → K) : K := f 0 * f' 1 - f 1 * f' 0

@[expose] def matAct (A : Matrix (Fin 2) (Fin 2) K) : (Fin 2 → L) →ₗ[K] (Fin 2 → L) where
  toFun x i := A i 0 • x 0 + A i 1 • x 1
  map_add' x y := funext fun i => by
    simp only [Pi.add_apply, smul_add]
    abel
  map_smul' c x := funext fun i => by
    simp only [Pi.smul_apply, RingHom.id_apply, smul_add]
    rw [smul_comm (A i 0) c, smul_comm (A i 1) c]

theorem matAct_apply (A : Matrix (Fin 2) (Fin 2) K) (x : Fin 2 → L) (i : Fin 2) :
    matAct A x i = A i 0 • x 0 + A i 1 • x 1 := rfl

theorem matAct_rootN_pureT (f f' : Fin 2 → K) (y : L) :
    matAct (rootN f) (pureT f' y) = det2 f' f • pureT f y := by
  funext i
  simp only [matAct_apply, pureT_apply, rootN, det2, Matrix.of_apply, Pi.smul_apply]
  rw [smul_smul, smul_smul, smul_smul, ← add_smul]
  congr 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  ring

theorem exists_eq_pureT_add_pureT {f f' : Fin 2 → K} (hdet : det2 f f' ≠ 0) (x : Fin 2 → L) :
    ∃ y y' : L, x = pureT f y + pureT f' y' := by
  refine ⟨(det2 f f')⁻¹ • (f' 1 • x 0 - f' 0 • x 1), (det2 f f')⁻¹ • (f 0 • x 1 - f 1 • x 0), ?_⟩
  have key : ∀ i : Fin 2, f i • (f' 1 • x 0 - f' 0 • x 1) + f' i • (f 0 • x 1 - f 1 • x 0) =
      det2 f f' • x i := by
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩ <;> simp only [det2] <;> module
  funext i
  rw [Pi.add_apply, pureT_apply, pureT_apply, smul_comm (f i), smul_comm (f' i), ← smul_add,
    key i, smul_smul, inv_mul_cancel₀ hdet, one_smul]

theorem eq_bot_or_eq_top_of_rootN (ρ : H →* (L ≃ₗ[K] L))
    (hirr : ∀ S : Submodule K L, (∀ h, ∀ y ∈ S, ρ h y ∈ S) → S = ⊥ ∨ S = ⊤)
    {f' f'' : Fin 2 → K} (hdet : det2 f' f'' ≠ 0) (A : AddSubgroup (Fin 2 → L))
    (hH : ∀ h, ∀ x ∈ A, (fun i => ρ h (x i)) ∈ A)
    (h' : ∀ (s : K), ∀ x ∈ A, x + s • matAct (rootN f') x ∈ A)
    (h'' : ∀ (s : K), ∀ x ∈ A, x + s • matAct (rootN f'') x ∈ A) :
    A = ⊥ ∨ A = ⊤ := by
  have hN' : ∀ (s : K), ∀ x ∈ A, s • matAct (rootN f') x ∈ A := fun s x hx => by
    have := A.sub_mem (h' s x hx) hx
    rwa [add_sub_cancel_left] at this
  have hN'' : ∀ (s : K), ∀ x ∈ A, s • matAct (rootN f'') x ∈ A := fun s x hx => by
    have := A.sub_mem (h'' s x hx) hx
    rwa [add_sub_cancel_left] at this
  have hd' : det2 f'' f' ≠ 0 := by
    intro h
    apply hdet
    unfold det2 at h ⊢
    linear_combination -h
  let A₀ : Submodule K L :=
    { carrier := {y | pureT f' y ∈ A}
      add_mem' := fun {y y'} hy hy' => by
        show pureT f' (y + y') ∈ A
        rw [map_add]
        exact A.add_mem hy hy'
      zero_mem' := by
        show pureT f' (0 : L) ∈ A
        rw [map_zero]
        exact A.zero_mem
      smul_mem' := fun c y hy => by
        show pureT f' (c • y) ∈ A
        have h1 := hN'' (c / (det2 f' f'' * det2 f'' f')) _ hy
        rw [matAct_rootN_pureT, smul_smul] at h1
        have h2 := hN' 1 _ h1
        rw [one_smul, map_smul, matAct_rootN_pureT, smul_smul] at h2
        have e : c / (det2 f' f'' * det2 f'' f') * det2 f' f'' * det2 f'' f' = c := by
          field_simp
        rw [e] at h2
        rw [map_smul]
        exact h2 }
  have hA₀ : ∀ y, y ∈ A₀ ↔ pureT f' y ∈ A := fun y => Iff.rfl
  have hA₀H : ∀ h, ∀ y ∈ A₀, ρ h y ∈ A₀ := fun h y hy => by
    rw [hA₀] at hy ⊢
    have := hH h _ hy
    have e : (fun i => ρ h (pureT f' y i)) = pureT f' (ρ h y) := funext fun i => by
      rw [pureT_apply, pureT_apply, map_smul]
    rwa [e] at this
  have hmove : ∀ y, pureT f' y ∈ A → pureT f'' y ∈ A := fun y hy => by
    have h1 := hN'' (det2 f' f'')⁻¹ _ hy
    rwa [matAct_rootN_pureT, smul_smul, inv_mul_cancel₀ hdet, one_smul] at h1
  have hmove' : ∀ y, pureT f'' y ∈ A → pureT f' y ∈ A := fun y hy => by
    have h1 := hN' (det2 f'' f')⁻¹ _ hy
    rwa [matAct_rootN_pureT, smul_smul, inv_mul_cancel₀ hd', one_smul] at h1
  rcases hirr A₀ hA₀H with h0 | htop
  ·
    left
    refine (AddSubgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
    obtain ⟨y, y', rfl⟩ := exists_eq_pureT_add_pureT (L := L) hdet x
    have hy' : y' ∈ A₀ := by
      rw [hA₀]
      have h1 := hN' (det2 f'' f')⁻¹ _ hx
      rw [map_add, matAct_rootN_pureT, matAct_rootN_pureT, smul_add, smul_smul, smul_smul,
        inv_mul_cancel₀ hd'] at h1
      have e : det2 f' f' = 0 := by unfold det2; ring
      rwa [e, mul_zero, zero_smul, zero_add, one_smul] at h1
    have hy : y ∈ A₀ := by
      rw [hA₀]
      refine hmove' y ?_
      have h1 := hN'' (det2 f' f'')⁻¹ _ hx
      rw [map_add, matAct_rootN_pureT, matAct_rootN_pureT, smul_add, smul_smul, smul_smul,
        inv_mul_cancel₀ hdet] at h1
      have e : det2 f'' f'' = 0 := by unfold det2; ring
      rwa [e, mul_zero, zero_smul, add_zero, one_smul] at h1
    rw [h0] at hy hy'
    rw [(Submodule.mem_bot K).mp hy, (Submodule.mem_bot K).mp hy', map_zero, map_zero, add_zero]
  ·
    right
    refine (AddSubgroup.eq_top_iff' _).mpr fun x => ?_
    obtain ⟨y, y', rfl⟩ := exists_eq_pureT_add_pureT (L := L) hdet x
    have hy : pureT f' y ∈ A := (hA₀ y).mp (htop ▸ Submodule.mem_top)
    have hy' : pureT f'' y' ∈ A := hmove y' ((hA₀ y').mp (htop ▸ Submodule.mem_top))
    exact A.add_mem hy hy'

end Root

end CFSG.RankThree.GF2n.Stroth80.S715L

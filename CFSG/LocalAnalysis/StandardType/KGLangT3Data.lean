module

public import CFSG.LocalAnalysis.StandardType.KGLangT3Recog

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private lemma l02qj5b2_mem_centralizer_singleton_iff {G : Type*} [Group G] {a x : G} :
    x ∈ Subgroup.centralizer ({a} : Set G) ↔ a * x = x * a := by
  constructor
  · intro h
    have := (Subgroup.mem_centralizer_iff.mp h) a (Set.mem_singleton a)
    first | exact this | exact this.symm
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    first | exact h | exact h.symm

private lemma l02qj5b2_mulAut_mul_inv_apply {G : Type*} [Group G] (β a : MulAut G) (x : G) :
    (β * a * β⁻¹) x = β (a (β⁻¹ x)) := by
  rw [MulAut.mul_apply, MulAut.mul_apply]

private lemma l02qj5b2_mulAut_conjAut {G : Type*} [Group G] (β : MulAut G) (m : G) :
    β * MulAut.conj m * β⁻¹ = MulAut.conj (β m) := by
  ext x
  rw [l02qj5b2_mulAut_mul_inv_apply, MulAut.conj_apply, MulAut.conj_apply]
  simp only [map_mul, map_inv]
  rw [MulAut.inv_apply, MulEquiv.apply_symm_apply]

private lemma l02qj5b2_orderOf_conj {G : Type*} [Group G] (β a : G) :
    orderOf (β * a * β⁻¹) = orderOf a := by
  refine SemiconjBy.orderOf_eq β⁻¹ ?_
  unfold SemiconjBy
  group

private lemma l02qj5b2_orderOf_mulAut_conj {G : Type*} [Group G] (a x : G) :
    orderOf ((MulAut.conj a) x) = orderOf x := by
  rw [MulAut.conj_apply]
  exact l02qj5b2_orderOf_conj a x

private lemma l02qj5b2_conj_pow {G : Type*} [Group G] (β a : G) (n : ℕ) :
    (β * a * β⁻¹) ^ n = β * a ^ n * β⁻¹ := by
  rw [← MulAut.conj_apply β a, ← MulAut.conj_apply β (a ^ n), map_pow]

private lemma l02qj5b2_mulAut_mem_centralizer {G : Type*} [Group G] (φ : MulAut G) {z : G}
    (hz : φ z = z) {x : G} (hx : x ∈ Subgroup.centralizer ({z} : Set G)) :
    φ x ∈ Subgroup.centralizer ({z} : Set G) := by
  rw [l02qj5b2_mem_centralizer_singleton_iff] at hx ⊢
  calc z * φ x = φ z * φ x := by rw [hz]
    _ = φ (z * x) := by rw [map_mul]
    _ = φ (x * z) := by rw [hx]
    _ = φ x * φ z := by rw [map_mul]
    _ = φ x * z := by rw [hz]

private def l02qj5b2_conjCentralizerEquiv {G : Type*} [Group G] (g a b : G)
    (hg : g * a * g⁻¹ = b) :
    Subgroup.centralizer ({a} : Set G) ≃* Subgroup.centralizer ({b} : Set G) where
  toFun x := ⟨g * (x : G) * g⁻¹, by
    rw [l02qj5b2_mem_centralizer_singleton_iff]
    have hx : a * (x : G) = (x : G) * a :=
      l02qj5b2_mem_centralizer_singleton_iff.mp x.2
    rw [← hg]
    calc (g * a * g⁻¹) * (g * (x : G) * g⁻¹)
        = g * (a * (x : G)) * g⁻¹ := by group
      _ = g * ((x : G) * a) * g⁻¹ := by rw [hx]
      _ = (g * (x : G) * g⁻¹) * (g * a * g⁻¹) := by group⟩
  invFun y := ⟨g⁻¹ * (y : G) * g, by
    rw [l02qj5b2_mem_centralizer_singleton_iff]
    have hy : b * (y : G) = (y : G) * b :=
      l02qj5b2_mem_centralizer_singleton_iff.mp y.2
    have hb : (g * a * g⁻¹) * (y : G) = (y : G) * (g * a * g⁻¹) := by
      rw [hg]
      exact hy
    calc a * (g⁻¹ * (y : G) * g)
        = g⁻¹ * ((g * a * g⁻¹) * (y : G)) * g := by group
      _ = g⁻¹ * ((y : G) * (g * a * g⁻¹)) * g := by rw [hb]
      _ = (g⁻¹ * (y : G) * g) * a := by group⟩
  left_inv x := by
    ext
    change g⁻¹ * (g * (x : G) * g⁻¹) * g = (x : G)
    group
  right_inv y := by
    ext
    change g * (g⁻¹ * (y : G) * g) * g⁻¹ = (y : G)
    group
  map_mul' x y := by
    ext
    change g * ((x : G) * (y : G)) * g⁻¹ =
      (g * (x : G) * g⁻¹) * (g * (y : G) * g⁻¹)
    group


theorem kgLangT3_exists_data {n : ℕ} (hn : 2 ≤ n) (hev : Even n) (K : Type) [Field K]
    (hK : Nat.card K = (2 ^ n) ^ 3) (k : Type) [Field k] [Algebra k K] (hk : Nat.card k = 2 ^ n)
    (h : GGTriD4R n K) (h1 : h ≠ 1) (h3 : h ^ 3 = 1) (J₀ : Subgroup (GGTriD4R n K))
    (hJ : IsComponentOf J₀ (Subgroup.centralizer ({h} : Set (GGTriD4R n K))))
    (E : Type) [Field E] [Finite E]
    (θ₀ : ↥J₀ ⧸ Subgroup.center ↥J₀ ≃* LargeEvenProj (LargeEvenSLGroup (Fin 3) E)) :
    ∃ D : TriD4LineKGXData n K k, D.z₀ = h := by
  obtain ⟨D₀⟩ := triD4Line_kgXData K hev hK k hk
  obtain ⟨g, hg⟩ := kgLangT3_conj_z0 hn hev K hK k hk D₀ h h1 h3 J₀ hJ E θ₀
  let β : MulAut (GGTriD4R n K) := MulAut.conj g⁻¹
  let e : Subgroup.centralizer ({h} : Set (GGTriD4R n K)) ≃*
      Subgroup.centralizer ({D₀.z₀} : Set (GGTriD4R n K)) :=
    l02qj5b2_conjCentralizerEquiv g h D₀.z₀ hg
  have hβinv_eq : β⁻¹ = MulAut.conj g := by
    have h := (map_inv (MulAut.conj : GGTriD4R n K →* MulAut (GGTriD4R n K)) g⁻¹).symm
    rw [inv_inv] at h
    exact h
  refine ⟨{ z₀ := h
            α := β * D₀.α * β⁻¹
            σ := D₀.σ
            Θ := e.trans D₀.Θ
            orderOf_z₀ := ?_
            sylow_z₀ := ?_
            α_outer := ?_
            orderOf_α := ?_
            α_z₀ := ?_
            orderOf_σ := D₀.orderOf_σ
            Θ_α := ?_ }, rfl⟩
  ·
    have hh : h = (MulAut.conj g⁻¹) D₀.z₀ := by
      rw [MulAut.conj_apply, ← hg]
      group
    rw [hh, l02qj5b2_orderOf_mulAut_conj, D₀.orderOf_z₀]
  ·
    obtain ⟨P, hzP, hcomm⟩ := D₀.sylow_z₀
    have hmem : (MulAut.conj g⁻¹) • D₀.z₀ = h := by
      rw [show (MulAut.conj g⁻¹) • D₀.z₀ = (MulAut.conj g⁻¹) D₀.z₀ from rfl,
        MulAut.conj_apply, ← hg]
      group
    refine ⟨(MulAut.conj g⁻¹) • P, ?_, ?_⟩
    · rw [Sylow.pointwise_smul_def]
      have := Subgroup.smul_mem_pointwise_smul D₀.z₀ (MulAut.conj g⁻¹)
        (P : Subgroup (GGTriD4R n K)) hzP
      rwa [hmem] at this
    · intro y hy
      rw [Sylow.pointwise_smul_def] at hy
      rw [Subgroup.mem_smul_pointwise_iff_exists] at hy
      obtain ⟨x, hxP, hxy⟩ := hy
      rw [← hxy]
      have hxcomm := hcomm x hxP
      have hc := congrArg (MulAut.conj g⁻¹) hxcomm
      simp only [map_mul] at hc
      rw [show (MulAut.conj g⁻¹) • x = (MulAut.conj g⁻¹) x from rfl]
      rw [show (MulAut.conj g⁻¹) D₀.z₀ = h from hmem] at hc
      exact hc
  ·
    intro hmem
    apply D₀.α_outer
    obtain ⟨x, hx⟩ := hmem
    refine ⟨β⁻¹ x, ?_⟩
    calc MulAut.conj (β⁻¹ x) = β⁻¹ * MulAut.conj x * β :=
          (l02qj5b2_mulAut_conjAut β⁻¹ x).symm
      _ = β⁻¹ * (β * D₀.α * β⁻¹) * β := by rw [hx]
      _ = D₀.α := by group
  ·
    have hD0pow : D₀.α ^ 3 = 1 := by
      rw [← D₀.orderOf_α]
      exact pow_orderOf_eq_one D₀.α
    have hpow : (β * D₀.α * β⁻¹) ^ 3 = 1 := by
      rw [l02qj5b2_conj_pow, hD0pow]
      group
    have hdvd : orderOf (β * D₀.α * β⁻¹) ∣ 3 := orderOf_dvd_of_pow_eq_one hpow
    have hne1 : orderOf (β * D₀.α * β⁻¹) ≠ 1 := by
      rw [l02qj5b2_orderOf_conj β D₀.α, D₀.orderOf_α]
      norm_num
    rcases Nat.prime_three.eq_one_or_self_of_dvd (orderOf (β * D₀.α * β⁻¹)) hdvd with h' | h'
    · exact absurd h' hne1
    · exact h'
  ·
    show (β * D₀.α * β⁻¹) h = h
    rw [l02qj5b2_mulAut_mul_inv_apply]
    have h1 : β⁻¹ h = D₀.z₀ := by
      rw [hβinv_eq, MulAut.conj_apply]
      exact hg
    rw [h1, D₀.α_z₀]
    show (MulAut.conj g⁻¹) D₀.z₀ = h
    rw [MulAut.conj_apply, ← hg]
    group
  ·
    intro y hy
    show (D₀.Θ (e ⟨(β * D₀.α * β⁻¹) y, hy⟩) : TriD4LineX k K) =
      triD4LineSigma k K D₀.σ (D₀.Θ (e y))
    have heα : (e ⟨(β * D₀.α * β⁻¹) y, hy⟩ : GGTriD4R n K) =
        D₀.α ((e y : GGTriD4R n K)) := by
      show g * ((β * D₀.α * β⁻¹) y) * g⁻¹ = D₀.α (g * (y : GGTriD4R n K) * g⁻¹)
      rw [l02qj5b2_mulAut_mul_inv_apply]
      rw [show β⁻¹ y = g * (y : GGTriD4R n K) * g⁻¹ from by
        rw [hβinv_eq, MulAut.conj_apply]]
      have hgz : ∀ z : GGTriD4R n K, g * (β z) * g⁻¹ = z := by
        intro z
        show g * (MulAut.conj g⁻¹ z) * g⁻¹ = z
        rw [MulAut.conj_apply]
        group
      rw [hgz]
    have hmem0 : D₀.α ((e y : GGTriD4R n K)) ∈
        Subgroup.centralizer ({D₀.z₀} : Set (GGTriD4R n K)) :=
      l02qj5b2_mulAut_mem_centralizer D₀.α D₀.α_z₀ (e y).2
    have key : e ⟨(β * D₀.α * β⁻¹) y, hy⟩ =
        ⟨D₀.α ((e y : GGTriD4R n K)), hmem0⟩ := by
      ext
      exact heα
    rw [key]
    exact D₀.Θ_α (e y) hmem0

end CFSG.StandardType

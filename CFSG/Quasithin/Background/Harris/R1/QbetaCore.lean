module

public import CFSG.Quasithin.Recognition.F112J2FamC

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112J2 CFSG.Quasithin.A5Model

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G}

theorem vBeta_le_K1 (C : FiveCtx K1 L2 S Zs)
    (hcenter : ∀ x ∈ vBeta K1 L2 S Zs, (∀ u ∈ vBeta K1 L2 S Zs, x * u = u * x) → x ∈ Zs) :
    vBeta K1 L2 S Zs ≤ K1 := by
  classical
  have hXN : K1 ⊔ S ≤ Subgroup.normalizer (K1 : Set G) :=
    sup_le Subgroup.le_normalizer C.hSK
  have hNn : (K1.subgroupOf (K1 ⊔ S)).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hXN
  let φ : ↥(K1 ⊔ S) →* ↥(K1 ⊔ S) ⧸ K1.subgroupOf (K1 ⊔ S) := QuotientGroup.mk' _
  let f : G → ↥(K1 ⊔ S) ⧸ K1.subgroupOf (K1 ⊔ S) :=
    fun g => if h : g ∈ K1 ⊔ S then φ ⟨g, h⟩ else 1
  have hUX : ∀ {g : G}, g ∈ vBeta K1 L2 S Zs → g ∈ K1 ⊔ S := fun hg => C.U_le_sup hg
  have f_mul : ∀ {g h : G}, g ∈ K1 ⊔ S → h ∈ K1 ⊔ S → f (g * h) = f g * f h := by
    intro g h hg hh
    have hgh : g * h ∈ K1 ⊔ S := (K1 ⊔ S).mul_mem hg hh
    simp only [f, hg, hh, hgh, ↓reduceDIte]
    rw [← map_mul]
    rfl
  have f_one : f 1 = 1 := by
    simp only [f, (K1 ⊔ S).one_mem, ↓reduceDIte]
    rw [← map_one φ]
    rfl
  have f_inv : ∀ {g : G}, g ∈ K1 ⊔ S → f g⁻¹ = (f g)⁻¹ := by
    intro g hg
    have h1 : f (g * g⁻¹) = f g * f g⁻¹ := f_mul hg ((K1 ⊔ S).inv_mem hg)
    rw [mul_inv_cancel, f_one] at h1
    exact (eq_inv_of_mul_eq_one_right h1.symm)
  have f_zpow : ∀ {g : G}, g ∈ K1 ⊔ S → ∀ n : ℤ, f (g ^ n) = (f g) ^ n := by
    intro g hg n
    have hgn : g ^ n ∈ K1 ⊔ S := (K1 ⊔ S).zpow_mem hg n
    simp only [f, hg, hgn, ↓reduceDIte]
    rw [← map_zpow]
    rfl
  have f_K1 : ∀ {g : G}, g ∈ K1 → f g = 1 := by
    intro g hg
    have hgX : g ∈ K1 ⊔ S := Subgroup.mem_sup_left hg
    simp only [f, hgX, ↓reduceDIte]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hg)
  have f_eq_one : ∀ {g : G}, g ∈ K1 ⊔ S → f g = 1 → g ∈ K1 := by
    intro g hg h
    simp only [f, hg, ↓reduceDIte] at h
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h)
  have hzX : ∀ i, C.zf i ∈ K1 ⊔ S := fun i => hUX (C.zf_mem_U i)
  have hcX : C.cm 0 1 ∈ K1 ⊔ S := hUX (Zs_le_vBeta K1 L2 S Zs (C.cm_mem 0 1))
  set c : ↥(K1 ⊔ S) ⧸ K1.subgroupOf (K1 ⊔ S) := f (C.cm 0 1) with hc
  set a : Fin 5 → ↥(K1 ⊔ S) ⧸ K1.subgroupOf (K1 ⊔ S) := fun i => f (C.zf i) with ha
  have key : ∀ i j : Fin 5, ∃ n : ℤ, a i = a j * c ^ n := by
    intro i j
    obtain ⟨g, hg⟩ := a5_trans i j
    obtain ⟨k, hk⟩ := C.D.surj g
    obtain ⟨ε, hε, hconj⟩ := C.conj_zf k i
    have hθ : (C.D.θ k : Equiv.Perm (Fin 5)) i = j := by rw [hk]; exact hg
    rw [hθ] at hconj
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp
      ((C.Zs_eq_zpowers (C.cm_mem 0 1) C.cm_ne_one).le hε)
    refine ⟨n, ?_⟩
    have hkX : (k : G) ∈ K1 ⊔ S := Subgroup.mem_sup_left k.2
    have hfk : f (k : G) = 1 := f_K1 k.2
    have hεX : ε ∈ K1 ⊔ S := hUX (Zs_le_vBeta K1 L2 S Zs hε)
    have h1 : f ((k : G) * C.zf i * (k : G)⁻¹) = a i := by
      rw [f_mul ((K1 ⊔ S).mul_mem hkX (hzX i)) ((K1 ⊔ S).inv_mem hkX),
        f_mul hkX (hzX i), f_inv hkX, hfk]
      simp [ha]
    have h2 : f (C.zf j * ε) = a j * c ^ n := by
      rw [f_mul (hzX j) hεX, ← hn, f_zpow hcX n]
    rw [← h1, hconj, h2]
  have hcomm : ∀ j, a j * c = c * a j := by
    intro j
    have h := C.Zs_central (C.zf_mem_U j) (C.cm_mem 0 1)
    have := congrArg f h
    rwa [f_mul (hzX j) hcX, f_mul hcX (hzX j)] at this
  have hc_def : c = a 0 * a 1 * (a 0)⁻¹ * (a 1)⁻¹ := by
    have e : C.cm 0 1 = C.zf 0 * C.zf 1 * (C.zf 0)⁻¹ * (C.zf 1)⁻¹ := rfl
    have hX : ∀ {x : G}, x ∈ K1 ⊔ S → x⁻¹ ∈ K1 ⊔ S := fun hx => (K1 ⊔ S).inv_mem hx
    rw [hc, e, f_mul ((K1 ⊔ S).mul_mem ((K1 ⊔ S).mul_mem (hzX 0) (hzX 1)) (hX (hzX 0)))
      (hX (hzX 1)), f_mul ((K1 ⊔ S).mul_mem (hzX 0) (hzX 1)) (hX (hzX 0)),
      f_mul (hzX 0) (hzX 1), f_inv (hzX 0), f_inv (hzX 1)]
  have hc1 : c = 1 := by
    obtain ⟨n, hn⟩ := key 0 1
    have hw : c ^ n * a 1 = a 1 * c ^ n := by
      have h1 : Commute (a 1) c := hcomm 1
      exact (h1.symm.zpow_left n).eq
    rw [hc_def, hn]
    calc a 1 * c ^ n * a 1 * (a 1 * c ^ n)⁻¹ * (a 1)⁻¹
        = a 1 * (c ^ n * a 1) * (c ^ n)⁻¹ * (a 1)⁻¹ * (a 1)⁻¹ := by group
      _ = a 1 * (a 1 * c ^ n) * (c ^ n)⁻¹ * (a 1)⁻¹ * (a 1)⁻¹ := by rw [hw]
      _ = 1 := by group
  have hall : ∀ i j, a i = a j := by
    intro i j
    obtain ⟨n, hn⟩ := key i j
    rw [hn, hc1, one_zpow, mul_one]
  have ha2 : a 0 * a 0 = 1 := by
    have h := congrArg f (C.Vf_sq (C.zf_mem 0))
    rwa [f_mul (hzX 0) (hzX 0), f_one] at h
  have hy : a 0 = 1 := by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (C.y_mem_zpowers hcenter)
    have hm' : (C.cm 0 1) ^ m = C.zf 0 * C.zf 1 * C.zf 2 * C.zf 3 * C.zf 4 := by
      have := congrArg Subtype.val hm
      simpa [FiveCtx.zU, FiveCtx.wU] using this
    have hprod : f (C.zf 0 * C.zf 1 * C.zf 2 * C.zf 3 * C.zf 4) = a 0 * a 1 * a 2 * a 3 * a 4 := by
      have hX : ∀ {x y : G}, x ∈ K1 ⊔ S → y ∈ K1 ⊔ S → x * y ∈ K1 ⊔ S :=
        fun hx hy => (K1 ⊔ S).mul_mem hx hy
      rw [f_mul (hX (hX (hX (hzX 0) (hzX 1)) (hzX 2)) (hzX 3)) (hzX 4),
        f_mul (hX (hX (hzX 0) (hzX 1)) (hzX 2)) (hzX 3), f_mul (hX (hzX 0) (hzX 1)) (hzX 2),
        f_mul (hzX 0) (hzX 1)]
    have hlhs : f ((C.cm 0 1) ^ m) = 1 := by rw [f_zpow hcX m, ← hc, hc1, one_zpow]
    rw [hm', hprod, hall 1 0, hall 2 0, hall 3 0, hall 4 0] at hlhs
    calc a 0 = a 0 * (a 0 * a 0) * (a 0 * a 0) := by rw [ha2]; group
      _ = a 0 * a 0 * a 0 * a 0 * a 0 := by group
      _ = 1 := hlhs
  have hzK : ∀ i, C.zf i ∈ K1 := fun i => f_eq_one (hzX i) (by
    have := hall i 0
    simp only [ha] at this
    rw [this]
    exact hy)
  have hcK : C.cm 0 1 ∈ K1 := f_eq_one hcX hc1
  rw [C.U_eq_closure (C.cm_mem 0 1) C.cm_ne_one, Subgroup.closure_le]
  rintro x (rfl | ⟨j, rfl⟩)
  · exact hcK
  · exact hzK j

end CFSG.Quasithin.Background.Harris.R1

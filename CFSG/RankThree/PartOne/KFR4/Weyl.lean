module

public import CFSG.RankThree.PartOne.KFR4.Defs

public section

namespace CFSG.RankThree.PartOne.KFR4

open QuadraticMap CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.OrthogonalInvolutions

namespace Wey

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E]

theorem N_sigma (D : EvenNormPlane K E) (z : E) : D.N (D.σ z) = D.N z := by
  apply (algebraMap K E).injective
  rw [D.algebraMap_N, D.algebraMap_N, D.sigma_sigma, mul_comm]

theorem conjCoord_mem_O (D : EvenNormPlane K E) (k : Fin 3) :
    conjCoord D k ∈ TauCeti.QuadraticMap.orthogonalGroup (Qs D) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  rw [Qs_apply, Qs_apply, conjCoord_apply]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  show D.N (if j = k then D.σ (v.1 j) else v.1 j) = D.N (v.1 j)
  split_ifs <;> simp [N_sigma]

theorem swapH_mem_O (D : EvenNormPlane K E) :
    swapH K E ∈ TauCeti.QuadraticMap.orthogonalGroup (Qs D) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  rw [Qs_apply, Qs_apply]
  show ∑ i, D.N (v.1 i) + v.2.2 * v.2.1 = ∑ i, D.N (v.1 i) + v.2.1 * v.2.2
  rw [mul_comm v.2.2]

theorem swapCoord_mem_O (D : EvenNormPlane K E) (i j : Fin 3) :
    swapCoord K E i j ∈ TauCeti.QuadraticMap.orthogonalGroup (Qs D) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  rw [Qs_apply, Qs_apply]
  show ∑ k, D.N (v.1 (Equiv.swap i j k)) + v.2.1 * v.2.2 = ∑ k, D.N (v.1 k) + v.2.1 * v.2.2
  rw [Equiv.sum_comp (Equiv.swap i j) (fun k => D.N (v.1 k))]

omit [Finite K] [CharP K 2] in
theorem finrank_commSpace_eq_one {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {g : V ≃ₗ[K] V} (hg : g ≠ 1) (e : V)
    (h : ∀ v, ∃ c : K, g v - v = c • e) : Module.finrank K (commSpace g) = 1 := by
  have he : e ≠ 0 := by
    rintro rfl
    apply hg
    ext v
    obtain ⟨c, hc⟩ := h v
    rw [smul_zero, sub_eq_zero] at hc
    simpa using hc
  have hle : commSpace g ≤ K ∙ e := by
    intro x hx
    obtain ⟨v, rfl⟩ := mem_commSpace.mp hx
    obtain ⟨c, hc⟩ := h v
    rw [hc]
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self e)
  have h1 := Submodule.finrank_mono hle
  rw [finrank_span_singleton he] at h1
  have h2 := one_le_finrank_commSpace hg
  omega

theorem conjCoord_ne_one (D : EvenNormPlane K E) (k : Fin 3) : conjCoord D k ≠ 1 := by
  intro h
  apply D.σ_ne_one
  ext z
  have := congrArg
    (fun g : Vs K E ≃ₗ[K] Vs K E => (g ((Pi.single k z : Fin 3 → E), (0, 0))).1 k) h
  simpa [conjCoord_apply] using this

theorem sigma_sub_mem (D : EvenNormPlane K E) (z : E) :
    ∃ c : K, algebraMap K E c = D.σ z - z := by
  have : CharP E 2 := charP_two_of_algebra (K := K)
  have h : D.σ (D.σ z - z) = D.σ z - z := by
    rw [map_sub, D.sigma_sigma, CharTwo.sub_eq_add, CharTwo.sub_eq_add, add_comm]
  obtain ⟨c, hc⟩ := (D.sigma_eq_self_iff _).1 h
  exact ⟨c, hc⟩

theorem finrank_commSpace_conjCoord [Module.Finite K E] (D : EvenNormPlane K E) (k : Fin 3) :
    Module.finrank K (commSpace (conjCoord D k)) = 1 := by
  refine finrank_commSpace_eq_one (conjCoord_ne_one D k) ((Pi.single k 1 : Fin 3 → E), (0, 0))
    fun v => ?_
  obtain ⟨c, hc⟩ := sigma_sub_mem D (v.1 k)
  refine ⟨c, Prod.ext (funext fun j => ?_) ?_⟩
  · by_cases hj : j = k
    · subst hj
      simp [conjCoord_apply, Algebra.smul_def, hc]
    · simp [conjCoord_apply, hj]
  · simp [conjCoord_apply]
    rfl

omit [Finite K] [CharP K 2] in
theorem swapH_ne_one : swapH K E ≠ 1 := by
  intro h
  have := congrArg (fun g : Vs K E ≃ₗ[K] Vs K E => (g (0, (1, 0))).2.1) h
  simp [swapH] at this

omit [Finite K] [CharP K 2] in
theorem finrank_commSpace_swapH [Module.Finite K E] :
    Module.finrank K (commSpace (swapH K E)) = 1 := by
  refine finrank_commSpace_eq_one swapH_ne_one ((0 : Fin 3 → E), (1, -1)) fun v => ?_
  refine ⟨v.2.2 - v.2.1, Prod.ext (funext fun j => ?_) (Prod.ext ?_ ?_)⟩
  · simp [swapH]
  · simp [swapH]
  · simp [swapH]

theorem finrank_commSpace_swapCoord [Module.Finite K E] (D : EvenNormPlane K E) {i j : Fin 3}
    (hij : i ≠ j) : Module.finrank K (commSpace (swapCoord K E i j)) = 2 := by
  let f : E →ₗ[K] Vs K E :=
    { toFun := fun u => (Pi.single i u - Pi.single j u, 0)
      map_add' := fun u w => by
        refine Prod.ext ?_ (by simp)
        simp only [Pi.single_add, Prod.fst_add]
        abel
      map_smul' := fun c u => by
        refine Prod.ext ?_ (by simp)
        simp [Pi.single_smul', smul_sub] }
  have hinj : Function.Injective f := by
    intro u w h
    have := congrArg (fun v : Vs K E => v.1 i) h
    simpa [f, hij] using this
  have heq : commSpace (swapCoord K E i j) = LinearMap.range f := by
    ext x
    rw [mem_commSpace, LinearMap.mem_range]
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨v.1 j - v.1 i, Prod.ext (funext fun m => ?_) ?_⟩
      · by_cases hmi : m = i
        · subst hmi
          simp [f, swapCoord, hij]
        · by_cases hmj : m = j
          · subst hmj
            simp [f, swapCoord, hmi]
          · simp [f, swapCoord, hmi, hmj, Equiv.swap_apply_of_ne_of_ne hmi hmj]
      · simp [f, swapCoord]
    · rintro ⟨u, rfl⟩
      refine ⟨((Pi.single j u : Fin 3 → E), (0, 0)), Prod.ext (funext fun m => ?_) ?_⟩
      · by_cases hmi : m = i
        · subst hmi
          simp [f, swapCoord, hij]
        · by_cases hmj : m = j
          · subst hmj
            simp [f, swapCoord, hmi]
          · simp [f, swapCoord, hmi, hmj, Equiv.swap_apply_of_ne_of_ne hmi hmj]
      · simp [f, swapCoord]
  rw [heq, LinearMap.finrank_range_of_inj hinj, D.finrank_eq]

section Mem

variable [Module.Finite K E]

theorem mem_Om_iff (D : EvenNormPlane K E) (g : Vs K E ≃ₗ[K] Vs K E) :
    g ∈ Om D ↔ g ∈ TauCeti.QuadraticMap.orthogonalGroup (Qs D) ∧
      ((Module.finrank K (commSpace g) : ℕ) : ZMod 2) = 0 := by
  rw [Om_eq_omegaGroup, mem_omegaGroup, ZMod.natCast_eq_zero_iff_even]

theorem weyl_short_mem (D : EvenNormPlane K E) (k : Fin 3) :
    conjCoord D k * swapH K E ∈ Om D := by
  rw [mem_Om_iff]
  refine ⟨mul_mem (conjCoord_mem_O D k) (swapH_mem_O D), ?_⟩
  rw [natCast_finrank_commSpace_mul (Qs_nondegenerate D) (conjCoord_mem_O D k) (swapH_mem_O D),
    finrank_commSpace_conjCoord, finrank_commSpace_swapH]
  decide

theorem weyl_m_mem (D : EvenNormPlane K E) {i j : Fin 3} (hij : i ≠ j) :
    swapCoord K E i j ∈ Om D := by
  rw [mem_Om_iff]
  refine ⟨swapCoord_mem_O D i j, ?_⟩
  rw [finrank_commSpace_swapCoord D hij]
  decide

theorem weyl_p_mem (D : EvenNormPlane K E) {i j : Fin 3} (hij : i ≠ j) :
    swapCoord K E i j * conjCoord D i * conjCoord D j ∈ Om D := by
  rw [mem_Om_iff]
  have h1 := mul_mem (swapCoord_mem_O D i j) (conjCoord_mem_O D i)
  refine ⟨mul_mem h1 (conjCoord_mem_O D j), ?_⟩
  rw [natCast_finrank_commSpace_mul (Qs_nondegenerate D) h1 (conjCoord_mem_O D j),
    natCast_finrank_commSpace_mul (Qs_nondegenerate D) (swapCoord_mem_O D i j)
      (conjCoord_mem_O D i), finrank_commSpace_swapCoord D hij, finrank_commSpace_conjCoord,
    finrank_commSpace_conjCoord]
  decide

end Mem

section Torus

variable {p : ℕ} (S : StdData K E p)

theorem swapH_mul_tor (a : Fin 3 → ZMod p) : swapH K E * tor S a = tor S a * swapH K E :=
  LinearEquiv.ext fun _ => rfl

theorem swapCoord_conj_tor (i j : Fin 3) (a : Fin 3 → ZMod p) :
    swapCoord K E i j * tor S a * (swapCoord K E i j)⁻¹ =
      tor S (fun m => a (Equiv.swap i j m)) := by
  rw [mul_inv_eq_iff_eq_mul]
  exact LinearEquiv.ext fun _ => rfl

theorem conj_mul {G : Type*} [Group G] (x y t : G) :
    x * y * t * (x * y)⁻¹ = x * (y * t * y⁻¹) * x⁻¹ := by
  group

theorem conj_short (k : Fin 3) (a : Fin 3 → ZMod p) :
    conjCoord S.D k * swapH K E * tor S a * (conjCoord S.D k * swapH K E)⁻¹ =
      tor S (flipVec k a) := by
  rw [conj_mul, swapH_mul_tor, mul_inv_cancel_right, conj_tor]

theorem conj_pair (i j : Fin 3) (a : Fin 3 → ZMod p) :
    swapCoord K E i j * conjCoord S.D i * conjCoord S.D j * tor S a *
        (swapCoord K E i j * conjCoord S.D i * conjCoord S.D j)⁻¹ =
      tor S (fun m => flipVec i (flipVec j a) (Equiv.swap i j m)) := by
  rw [conj_mul, conj_tor, conj_mul, conj_tor, swapCoord_conj_tor]

end Torus

section Refl

variable (p : ℕ)

theorem reflLin_s1 (a : Fin 3 → ZMod p) : reflLin p .s1 a = flipVec 0 a := by
  funext m
  fin_cases m <;> simp [reflLin_apply_coord, flipVec, dotProduct, Fin.sum_univ_three, Root.vecp,
    Root.corp, Root.vec, Root.cor, mul_two]

theorem reflLin_s2 (a : Fin 3 → ZMod p) : reflLin p .s2 a = flipVec 1 a := by
  funext m
  fin_cases m <;> simp [reflLin_apply_coord, flipVec, dotProduct, Fin.sum_univ_three, Root.vecp,
    Root.corp, Root.vec, Root.cor, mul_two]

theorem reflLin_s3 (a : Fin 3 → ZMod p) : reflLin p .s3 a = flipVec 2 a := by
  funext m
  fin_cases m <;> simp [reflLin_apply_coord, flipVec, dotProduct, Fin.sum_univ_three, Root.vecp,
    Root.corp, Root.vec, Root.cor, mul_two]

theorem reflLin_m12 (a : Fin 3 → ZMod p) :
    reflLin p .m12 a = fun m => a (Equiv.swap 0 1 m) := by
  funext m
  fin_cases m <;> simp [reflLin_apply_coord, dotProduct, Fin.sum_univ_three, Root.vecp,
    Root.corp, Root.vec, Root.cor, Equiv.swap_apply_of_ne_of_ne]

theorem reflLin_m13 (a : Fin 3 → ZMod p) :
    reflLin p .m13 a = fun m => a (Equiv.swap 0 2 m) := by
  funext m
  fin_cases m <;> simp [reflLin_apply_coord, dotProduct, Fin.sum_univ_three, Root.vecp,
    Root.corp, Root.vec, Root.cor, Equiv.swap_apply_of_ne_of_ne]

theorem reflLin_m23 (a : Fin 3 → ZMod p) :
    reflLin p .m23 a = fun m => a (Equiv.swap 1 2 m) := by
  funext m
  fin_cases m <;> simp [reflLin_apply_coord, dotProduct, Fin.sum_univ_three, Root.vecp,
    Root.corp, Root.vec, Root.cor, Equiv.swap_apply_of_ne_of_ne]

theorem reflLin_p12 (a : Fin 3 → ZMod p) :
    reflLin p .p12 a = fun m => flipVec 0 (flipVec 1 a) (Equiv.swap 0 1 m) := by
  funext m
  fin_cases m <;> simp [reflLin_apply_coord, flipVec, dotProduct, Fin.sum_univ_three, Root.vecp,
    Root.corp, Root.vec, Root.cor, Equiv.swap_apply_of_ne_of_ne, Function.update_apply]

theorem reflLin_p13 (a : Fin 3 → ZMod p) :
    reflLin p .p13 a = fun m => flipVec 0 (flipVec 2 a) (Equiv.swap 0 2 m) := by
  funext m
  fin_cases m <;> simp [reflLin_apply_coord, flipVec, dotProduct, Fin.sum_univ_three, Root.vecp,
    Root.corp, Root.vec, Root.cor, Equiv.swap_apply_of_ne_of_ne, Function.update_apply]

theorem reflLin_p23 (a : Fin 3 → ZMod p) :
    reflLin p .p23 a = fun m => flipVec 1 (flipVec 2 a) (Equiv.swap 1 2 m) := by
  funext m
  fin_cases m <;> simp [reflLin_apply_coord, flipVec, dotProduct, Fin.sum_univ_three, Root.vecp,
    Root.corp, Root.vec, Root.cor, Equiv.swap_apply_of_ne_of_ne, Function.update_apply]

end Refl

end Wey

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E] [Module.Finite K E]
  {p : ℕ} (S : StdData K E p)

theorem exists_weyl (σ : Root) :
    ∃ w ∈ Om S.D, ∀ a : Fin 3 → ZMod p, w * tor S a * w⁻¹ = tor S (reflLin p σ a) := by
  cases σ
  · exact ⟨_, Wey.weyl_short_mem S.D 0, fun a => by rw [Wey.conj_short, Wey.reflLin_s1]⟩
  · exact ⟨_, Wey.weyl_short_mem S.D 1, fun a => by rw [Wey.conj_short, Wey.reflLin_s2]⟩
  · exact ⟨_, Wey.weyl_short_mem S.D 2, fun a => by rw [Wey.conj_short, Wey.reflLin_s3]⟩
  · exact ⟨_, Wey.weyl_m_mem S.D (i := 0) (j := 1) (by decide),
      fun a => by rw [Wey.swapCoord_conj_tor, Wey.reflLin_m12]⟩
  · exact ⟨_, Wey.weyl_m_mem S.D (i := 0) (j := 2) (by decide),
      fun a => by rw [Wey.swapCoord_conj_tor, Wey.reflLin_m13]⟩
  · exact ⟨_, Wey.weyl_m_mem S.D (i := 1) (j := 2) (by decide),
      fun a => by rw [Wey.swapCoord_conj_tor, Wey.reflLin_m23]⟩
  · exact ⟨_, Wey.weyl_p_mem S.D (i := 0) (j := 1) (by decide),
      fun a => by rw [Wey.conj_pair, Wey.reflLin_p12]⟩
  · exact ⟨_, Wey.weyl_p_mem S.D (i := 0) (j := 2) (by decide),
      fun a => by rw [Wey.conj_pair, Wey.reflLin_p13]⟩
  · exact ⟨_, Wey.weyl_p_mem S.D (i := 1) (j := 2) (by decide),
      fun a => by rw [Wey.conj_pair, Wey.reflLin_p23]⟩

set_option linter.unusedSectionVars false in
theorem conjCoord_mem_orthogonalGroup (k : Fin 3) :
    conjCoord S.D k ∈ TauCeti.QuadraticMap.orthogonalGroup (Qs S.D) :=
  Wey.conjCoord_mem_O S.D k

end CFSG.RankThree.PartOne.KFR4

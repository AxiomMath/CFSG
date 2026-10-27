module

public import CFSG.Quasithin.Background.FFC9A
public import CFSG.Quasithin.Background.HConj
public import CFSG.Quasithin.Background.HSL

public section

namespace CFSG.Quasithin

namespace FFC

namespace SumNat

open CFSG.Assembly.LowTwoRank Matrix CFSG.Quasithin.H
open scoped Matrix

variable {F : Type} [Field F]

theorem diagAut_mem_natImage (s : ↥(StatedSL 3 F)) : diagAut (s : GL (Fin 3) F) ∈ natImage F :=
  ⟨s, rfl⟩

theorem exists_conj_fwd {a : MulAut (PM F)}
    (ha : a ∈ Subgroup.normalizer (natImage F : Set (MulAut (PM F)))) (s : ↥(StatedSL 3 F)) :
    ∃ s' : ↥(StatedSL 3 F),
      a * diagAut (s : GL (Fin 3) F) = diagAut (s' : GL (Fin 3) F) * a := by
  obtain ⟨s', hs'⟩ := (Subgroup.mem_normalizer_iff.1 ha _).1 (diagAut_mem_natImage s)
  refine ⟨s', ?_⟩
  have h : diagAut (s' : GL (Fin 3) F) = a * diagAut (s : GL (Fin 3) F) * a⁻¹ := hs'
  rw [h]
  group

theorem exists_conj_bwd {a : MulAut (PM F)}
    (ha : a ∈ Subgroup.normalizer (natImage F : Set (MulAut (PM F)))) (s' : ↥(StatedSL 3 F)) :
    ∃ s : ↥(StatedSL 3 F),
      a * diagAut (s : GL (Fin 3) F) = diagAut (s' : GL (Fin 3) F) * a := by
  obtain ⟨s, hs⟩ := (Subgroup.mem_normalizer_iff.1 (inv_mem ha) _).1 (diagAut_mem_natImage s')
  refine ⟨s, ?_⟩
  have h : diagAut (s : GL (Fin 3) F) = a⁻¹ * diagAut (s' : GL (Fin 3) F) * a⁻¹⁻¹ := hs
  rw [h]
  group

@[expose] def blk (a : MulAut (PM F)) (i j : Fin 2) : (Fin 3 → F) →+ (Fin 3 → F) where
  toFun n := adP a (Pi.single j n) i
  map_zero' := by simp [adP_zero]
  map_add' n m := by simp [Pi.single_add, adP_add]

theorem adP_eq_sum_blk (a : MulAut (PM F)) (v : PV F) (i : Fin 2) :
    adP a v i = ∑ j, blk a i j (v j) := by
  have hv : v = ∑ j, (Pi.single j (v j) : PV F) := (Finset.univ_sum_single v).symm
  conv_lhs => rw [hv]
  rw [adP_sum, Finset.sum_apply]
  rfl

theorem adP_diagAut_single (s : GL (Fin 3) F) (j : Fin 2) (n : Fin 3 → F) :
    adP (diagAut s) (Pi.single j n) = Pi.single j ((s : Matrix (Fin 3) (Fin 3) F) *ᵥ n) := by
  funext i
  rw [adP_diagAut]
  by_cases h : i = j
  · subst h
    simp
  · simp [Pi.single_eq_of_ne h]

theorem blk_conj {a : MulAut (PM F)} {s s' : GL (Fin 3) F}
    (h : a * diagAut s = diagAut s' * a) (i j : Fin 2) (n : Fin 3 → F) :
    blk a i j ((s : Matrix (Fin 3) (Fin 3) F) *ᵥ n) =
      (s' : Matrix (Fin 3) (Fin 3) F) *ᵥ blk a i j n := by
  have h1 := congrArg (fun g => adP g (Pi.single j n) i) h
  simp only [adP_mul, adP_diagAut_single, adP_diagAut] at h1
  exact h1

theorem exists_blk_ne_zero (a : MulAut (PM F)) :
    ∃ i : Fin 2, blk a i 0 (Pi.single 0 1) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have h0 : adP a (Pi.single 0 (Pi.single 0 1)) = 0 := by
    funext i
    rw [adP_eq_sum_blk]
    simp [Fin.sum_univ_two, hcon i]
  have := (adP_eq_zero_iff a).1 h0
  have h3 := congrFun (congrFun this 0) 0
  simp at h3

theorem exists_statedSL_transvection (i j : Fin 3) (hij : i ≠ j) (c : F) :
    ∃ s : ↥(StatedSL 3 F), ((s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.transvection i j c := by
  refine ⟨⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection i j c)
    (by rw [Matrix.det_transvection_of_ne i j hij c]; exact one_ne_zero), ?_⟩, rfl⟩
  exact Subgroup.subset_closure (by
    change (Matrix.transvection i j c).det = 1
    exact Matrix.det_transvection_of_ne i j hij c)

theorem blk_injective {a : MulAut (PM F)}
    (ha : ∀ s : ↥(StatedSL 3 F), ∃ s' : ↥(StatedSL 3 F),
      a * diagAut (s : GL (Fin 3) F) = diagAut (s' : GL (Fin 3) F) * a)
    {i j : Fin 2} (hne : ∃ n, blk a i j n ≠ 0) : Function.Injective (blk a i j) := by
  let U : AddSubgroup (Fin 3 → F) := AddMonoidHom.ker (blk a i j)
  have hU : ∀ k l : Fin 3, k ≠ l → ∀ c : F, ∀ u ∈ U, Matrix.transvection k l c *ᵥ u ∈ U := by
    intro k l hkl c u hu
    obtain ⟨s, hs⟩ := exists_statedSL_transvection (F := F) k l hkl c
    obtain ⟨s', hs'⟩ := ha s
    rw [← hs]
    show blk a i j _ = 0
    rw [blk_conj hs' i j u, show blk a i j u = 0 from hu, Matrix.mulVec_zero]
  rcases eq_bot_or_eq_top_of_transvection_inv (by norm_num : 2 ≤ 3) U hU with h | h
  · refine (injective_iff_map_eq_zero _).2 fun n hn => ?_
    have : n ∈ U := hn
    rw [h] at this
    exact AddSubgroup.mem_bot.1 this
  · exfalso
    obtain ⟨n, hn⟩ := hne
    have : n ∈ U := by rw [h]; trivial
    exact hn this

theorem blk_eq_comp_scalar {a : MulAut (PM F)}
    (ha : ∀ s : ↥(StatedSL 3 F), ∃ s' : ↥(StatedSL 3 F),
      a * diagAut (s : GL (Fin 3) F) = diagAut (s' : GL (Fin 3) F) * a)
    (fe : (Fin 3 → F) ≃+ (Fin 3 → F)) {i₀ j₀ : Fin 2} (hfe : ∀ n, fe n = blk a i₀ j₀ n)
    (i j : Fin 2) : ∃ ν : F, ∀ n, blk a i j n = fe (ν • n) := by
  let u : (Fin 3 → F) →+ (Fin 3 → F) :=
    (fe.symm : (Fin 3 → F) →+ (Fin 3 → F)).comp (blk a i j)
  obtain ⟨c, hc⟩ := hasScalarCommutant_statedSL (K := F) (d := 3) (by norm_num) u (by
    intro γ hγ v
    obtain ⟨s', hs'⟩ := ha ⟨γ, hγ⟩
    have hf : ∀ x, fe ((γ : Matrix (Fin 3) (Fin 3) F) *ᵥ x) =
        ((s' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ fe x := fun x => by
      rw [hfe, hfe]
      exact blk_conj hs' i₀ j₀ x
    show fe.symm (blk a i j ((γ : Matrix (Fin 3) (Fin 3) F) *ᵥ v)) =
      (γ : Matrix (Fin 3) (Fin 3) F) *ᵥ fe.symm (blk a i j v)
    rw [blk_conj hs' i j v]
    have := hf (fe.symm (blk a i j v))
    rw [AddEquiv.apply_symm_apply] at this
    rw [← this, AddEquiv.symm_apply_apply])
  refine ⟨c, fun n => ?_⟩
  have := hc n
  show blk a i j n = fe (c • n)
  rw [← this]
  show blk a i j n = fe (fe.symm (blk a i j n))
  rw [AddEquiv.apply_symm_apply]

@[expose] def RelPair (fe : (Fin 3 → F) ≃+ (Fin 3 → F)) (s s' : ↥(StatedSL 3 F)) : Prop :=
  ∀ x, fe (((s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x) =
    ((s' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ fe x

theorem mem_natNorm_of_rel (fe : (Fin 3 → F) ≃+ (Fin 3 → F))
    (h1 : ∀ s, ∃ s', RelPair fe s s') (h2 : ∀ s', ∃ s, RelPair fe s s') :
    (AddEquiv.toMultiplicative fe : MulAut (StdMod (Fin 3) F)) ∈ natNorm (StatedSL 3 F) := by
  set g : MulAut (StdMod (Fin 3) F) := AddEquiv.toMultiplicative fe with hg
  have hgf : ∀ w, toAddMap g w = fe w := fun w => rfl
  have hgi : ∀ w, toAddMap g⁻¹ w = fe.symm w := fun w => rfl
  refine Subgroup.mem_normalizer_iff.2 fun h => ⟨?_, ?_⟩
  · rintro ⟨γ, rfl⟩
    obtain ⟨s', hs'⟩ := h1 γ
    refine ⟨s', toAddMap_injective fun v => ?_⟩
    simp only [toAddMap_mul, toAddMap_natAut, hgf, hgi]
    have := hs' (fe.symm v)
    rw [AddEquiv.apply_symm_apply] at this
    exact this.symm
  · rintro ⟨γ', hγ'⟩
    obtain ⟨s, hs⟩ := h2 γ'
    refine ⟨s, toAddMap_injective fun v => ?_⟩
    have hh : h = g⁻¹ * natAut (StatedSL 3 F) γ' * g := by
      rw [hγ']
      group
    rw [hh]
    simp only [toAddMap_mul, toAddMap_natAut, hgf, hgi]
    have := hs v
    rw [← this, AddEquiv.symm_apply_apply]

theorem exists_semilinear_of_rel [Finite F] (fe : (Fin 3 → F) ≃+ (Fin 3 → F))
    (h1 : ∀ s, ∃ s', RelPair fe s s') (h2 : ∀ s', ∃ s, RelPair fe s s') :
    ∃ σ : F ≃+* F, ∀ (c : F) (n : Fin 3 → F), fe (c • n) = σ c • fe n := by
  obtain ⟨σ, hσ⟩ := exists_semilinear (hasScalarCommutant_statedSL (K := F) (d := 3) (by norm_num))
    (mem_natNorm_of_rel fe h1 h2)
  exact ⟨σ, fun c n => hσ c n⟩

theorem exists_form [Finite F] {a : MulAut (PM F)}
    (h1 : ∀ s : ↥(StatedSL 3 F), ∃ s' : ↥(StatedSL 3 F),
      a * diagAut (s : GL (Fin 3) F) = diagAut (s' : GL (Fin 3) F) * a)
    (h2 : ∀ s' : ↥(StatedSL 3 F), ∃ s : ↥(StatedSL 3 F),
      a * diagAut (s : GL (Fin 3) F) = diagAut (s' : GL (Fin 3) F) * a) :
    ∃ (fe : (Fin 3 → F) ≃+ (Fin 3 → F)) (ν : Matrix (Fin 2) (Fin 2) F) (σ : F ≃+* F),
      (∀ (c : F) (n : Fin 3 → F), fe (c • n) = σ c • fe n) ∧
        ∀ v, adP a v = fun i => fe (cAct ν v i) := by
  classical
  obtain ⟨i₀, hi₀⟩ := exists_blk_ne_zero a
  have hinj : Function.Injective (blk a i₀ 0) := blk_injective h1 ⟨_, hi₀⟩
  have hbij : Function.Bijective (blk a i₀ 0) := Finite.injective_iff_bijective.1 hinj
  let fe : (Fin 3 → F) ≃+ (Fin 3 → F) := AddEquiv.ofBijective (blk a i₀ 0) hbij
  have hfe : ∀ n, fe n = blk a i₀ 0 n := fun n => rfl
  have hrel1 : ∀ s, ∃ s', RelPair fe s s' := by
    intro s
    obtain ⟨s', hs'⟩ := h1 s
    exact ⟨s', fun x => by rw [hfe, hfe]; exact blk_conj hs' i₀ 0 x⟩
  have hrel2 : ∀ s', ∃ s, RelPair fe s s' := by
    intro s'
    obtain ⟨s, hs⟩ := h2 s'
    exact ⟨s, fun x => by rw [hfe, hfe]; exact blk_conj hs i₀ 0 x⟩
  obtain ⟨σ, hσ⟩ := exists_semilinear_of_rel fe hrel1 hrel2
  have hν : ∀ i j, ∃ ν : F, ∀ n, blk a i j n = fe (ν • n) := fun i j =>
    blk_eq_comp_scalar h1 fe hfe i j
  choose ν hν using hν
  refine ⟨fe, Matrix.of ν, σ, hσ, fun v => ?_⟩
  funext i
  rw [adP_eq_sum_blk]
  simp only [hν, cAct, Matrix.of_apply, map_sum]

theorem adP_cAct_smul (σ : F ≃+* F) {a : MulAut (PM F)} (fe : (Fin 3 → F) ≃+ (Fin 3 → F))
    (ν : Matrix (Fin 2) (Fin 2) F) (hσ : ∀ (c : F) (n : Fin 3 → F), fe (c • n) = σ c • fe n)
    (hform : ∀ v, adP a v = fun i => fe (cAct ν v i)) (c : F) (v : PV F) :
    adP a (c • v) = σ c • adP a v := by
  funext i
  rw [hform, hform]
  simp only [cAct_smul, Pi.smul_apply, hσ]

theorem sigma_eq_refl [Finite F] {m : ℕ} (hm : Odd m) (hF : Nat.card F = 2 ^ m)
    {a : MulAut (PM F)} (ha2 : a * a = 1) (σ : F ≃+* F)
    (hσ : ∀ (c : F) (v : PV F), adP a (c • v) = σ c • adP a v) : σ = RingEquiv.refl F := by
  have hinv : ∀ w, adP a (adP a w) = w := fun w => by
    rw [← adP_mul, ha2, adP_one]
  have hσσ : ∀ c, σ (σ c) = c := by
    intro c
    set v₀ : PV F := Pi.single 0 (Pi.single 0 1) with hv₀
    have h1 : c • v₀ = σ (σ c) • v₀ := by
      calc c • v₀ = adP a (adP a (c • v₀)) := (hinv _).symm
        _ = adP a (σ c • adP a v₀) := by rw [hσ]
        _ = σ (σ c) • adP a (adP a v₀) := by rw [hσ]
        _ = σ (σ c) • v₀ := by rw [hinv]
    have h2 := congrFun (congrFun h1 0) 0
    simpa [hv₀] using h2.symm
  by_contra hne
  have hg := isSemilinear_fieldMap (ι := Fin 3) σ
  have hg2 : fieldMap (ι := Fin 3) σ ^ 2 = 1 := by
    refine toAddMap_injective fun v => ?_
    simp only [pow_two, toAddMap_mul, toAddMap_fieldMap, toAddMap_one]
    funext i
    exact hσσ (v i)
  obtain ⟨h2, -⟩ := rkIdx_fixV_of_semilinear_two (ι := Fin 3) (K := F) (n := m) hm.pos hF hg hne hg2
  exact (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 h2)

theorem exists_matrix_of_linear (fe : (Fin 3 → F) ≃+ (Fin 3 → F))
    (hlin : ∀ (c : F) (n : Fin 3 → F), fe (c • n) = c • fe n) :
    ∃ A : GL (Fin 3) F, ∀ n, fe n = (A : Matrix (Fin 3) (Fin 3) F) *ᵥ n := by
  let fl : (Fin 3 → F) →ₗ[F] (Fin 3 → F) :=
    { toFun := fe
      map_add' := map_add fe
      map_smul' := hlin }
  let fl' : (Fin 3 → F) →ₗ[F] (Fin 3 → F) :=
    { toFun := fe.symm
      map_add' := map_add fe.symm
      map_smul' := fun c n => by
        apply fe.injective
        show fe (fe.symm (c • n)) = fe (c • fe.symm n)
        rw [AddEquiv.apply_symm_apply, hlin, AddEquiv.apply_symm_apply] }
  have h1 : fl ∘ₗ fl' = LinearMap.id := LinearMap.ext fun v => fe.apply_symm_apply v
  have h2 : fl' ∘ₗ fl = LinearMap.id := LinearMap.ext fun v => fe.symm_apply_apply v
  refine ⟨⟨LinearMap.toMatrix' fl, LinearMap.toMatrix' fl', ?_, ?_⟩, fun n => ?_⟩
  · rw [← LinearMap.toMatrix'_comp, h1, LinearMap.toMatrix'_id]
  · rw [← LinearMap.toMatrix'_comp, h2, LinearMap.toMatrix'_id]
  · show fl n = _
    exact (LinearMap.congr_fun (Matrix.toLin'_toMatrix' fl) n).symm.trans (Matrix.toLin'_apply _ _)

theorem isUnit_of_form {a : MulAut (PM F)} (fe : (Fin 3 → F) ≃+ (Fin 3 → F))
    (ν : Matrix (Fin 2) (Fin 2) F) (hform : ∀ v, adP a v = fun i => fe (cAct ν v i)) :
    IsUnit ν := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro x y hxy
  set e₀ : Fin 3 → F := Pi.single 0 1 with he₀
  have hd : ν *ᵥ (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
  set d := x - y with hdd
  have hv : adP a (fun j => d j • e₀) = 0 := by
    funext i
    rw [hform]
    have : cAct ν (fun j => d j • e₀) i = 0 := by
      have h1 : cAct ν (fun j => d j • e₀) i = (∑ j, ν i j * d j) • e₀ := by
        simp only [cAct, Finset.sum_smul, smul_smul]
      rw [h1]
      have h2 : ∑ j, ν i j * d j = (ν *ᵥ d) i := rfl
      rw [h2, hd]
      simp
    simp [this]
  have hv0 := (adP_eq_zero_iff a).1 hv
  have : d = 0 := by
    funext j
    have := congrFun (congrFun hv0 j) 0
    simpa [he₀] using this
  rw [hdd] at this
  exact sub_eq_zero.1 this

@[expose] def smulGL {n : ℕ} (t : F) (ht : t ≠ 0) (A : GL (Fin n) F) : GL (Fin n) F :=
  ⟨t • (A : Matrix (Fin n) (Fin n) F), t⁻¹ • ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F),
    by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ ht, one_smul,
      ← Units.val_mul, mul_inv_cancel, Units.val_one],
    by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ ht, one_smul,
      ← Units.val_mul, inv_mul_cancel, Units.val_one]⟩

theorem smulGL_val {n : ℕ} (t : F) (ht : t ≠ 0) (A : GL (Fin n) F) :
    ((smulGL t ht A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      t • (A : Matrix (Fin n) (Fin n) F) := rfl

theorem diagAut_smulGL_mul_cAut_smulGL (t u : F) (ht : t ≠ 0) (hu : u ≠ 0) (htu : t * u = 1)
    (A : GL (Fin 3) F) (N : GL (Fin 2) F) :
    diagAut (smulGL t ht A) * cAut (smulGL u hu N) = diagAut A * cAut N := by
  refine adP_ext fun v => ?_
  funext i
  have hY : ∑ j, (u • (N : Matrix (Fin 2) (Fin 2) F)) i j • v j =
      u • ∑ j, (N : Matrix (Fin 2) (Fin 2) F) i j • v j := by
    simp only [Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]
  simp only [adP_mul, adP_diagAut, adP_cAut, smulGL_val, cAct]
  rw [hY, Matrix.mulVec_smul, Matrix.smul_mulVec, smul_smul, mul_comm u t, htu, one_smul]

theorem diagAut_mul_cAut_sq (A : GL (Fin 3) F) (N : GL (Fin 2) F) :
    (diagAut A * cAut N) * (diagAut A * cAut N) = diagAut (A * A) * cAut (N * N) := by
  have h := diagAut_comm_cAut A N
  calc (diagAut A * cAut N) * (diagAut A * cAut N)
      = diagAut A * (cAut N * diagAut A) * cAut N := by simp only [mul_assoc]
    _ = diagAut A * (diagAut A * cAut N) * cAut N := by rw [← h]
    _ = (diagAut A * diagAut A) * (cAut N * cAut N) := by simp only [mul_assoc]
    _ = diagAut (A * A) * cAut (N * N) := by
      rw [show diagAut (A * A) = diagAut A * diagAut A from diagHom.map_mul A A,
        show cAut (N * N) = cAut N * cAut N from cHom.map_mul N N]

theorem det_eq_one_of_mul_self_eq_one [CharP F 2] {n : ℕ} {A : GL (Fin n) F} (h : A * A = 1) :
    (A : Matrix (Fin n) (Fin n) F).det = 1 := by
  have h1 : (A : Matrix (Fin n) (Fin n) F).det * (A : Matrix (Fin n) (Fin n) F).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, h, Units.val_one, Matrix.det_one]
  set x := (A : Matrix (Fin n) (Fin n) F).det with hx
  have h2 : (x + 1) * (x + 1) = 0 := by
    have : x + x = 0 := CharTwo.add_self_eq_zero x
    calc (x + 1) * (x + 1) = x * x + (x + x) + 1 := by ring
      _ = 0 := by rw [h1, this, add_zero, CharTwo.add_self_eq_zero]
  have h3 : x + 1 = 0 := mul_self_eq_zero.1 h2
  calc x = x + 1 + 1 := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    _ = 1 := by rw [h3, zero_add]

theorem exists_model_of_involution [Finite F] [CharP F 2] {m : ℕ} (hm : Odd m)
    (hF : Nat.card F = 2 ^ m) {a : MulAut (PM F)}
    (ha : a ∈ Subgroup.normalizer (natImage F : Set (MulAut (PM F)))) (ha2 : a * a = 1) :
    ∃ (s : ↥(StatedSL 3 F)) (c : GL (Fin 2) F), a = modelHom (s, c) ∧ s * s = 1 ∧ c * c = 1 := by
  have h1 := fun s => exists_conj_fwd ha s
  have h2 := fun s' => exists_conj_bwd ha s'
  obtain ⟨fe, ν, σ, hσ, hform⟩ := exists_form h1 h2
  have hsemi : ∀ (c : F) (v : PV F), adP a (c • v) = σ c • adP a v :=
    adP_cAct_smul σ fe ν hσ hform
  have hσ1 : σ = RingEquiv.refl F := sigma_eq_refl hm hF ha2 σ hsemi
  have hlin : ∀ (c : F) (n : Fin 3 → F), fe (c • n) = c • fe n := by
    intro c n
    rw [hσ, hσ1]
    rfl
  obtain ⟨A, hA⟩ := exists_matrix_of_linear fe hlin
  have hνu : IsUnit ν := isUnit_of_form fe ν hform
  let N : GL (Fin 2) F := hνu.unit
  have hN : (N : Matrix (Fin 2) (Fin 2) F) = ν := hνu.unit_spec
  have hdecomp : a = diagAut A * cAut N := by
    refine adP_ext fun v => ?_
    funext i
    rw [hform, adP_mul, adP_diagAut, adP_cAut, hN]
    exact hA _
  have hsq : diagAut (A * A) * cAut (N * N) = 1 := by
    rw [← diagAut_mul_cAut_sq, ← hdecomp, ha2]
  obtain ⟨μ, hμ0, hAA, hNN⟩ := exists_scalar_of_diagAut_mul_cAut_eq_one hsq
  have hchar : ringChar F = 2 := ringChar.eq F 2
  obtain ⟨ρ, hρ⟩ := FiniteField.isSquare_of_char_two hchar μ
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    exact hμ0 (by simpa using hρ)
  have hρρ : ρ⁻¹ * ρ = 1 := inv_mul_cancel₀ hρ0
  have hρ' : ρ⁻¹ ≠ 0 := inv_ne_zero hρ0
  have hss : smulGL ρ⁻¹ hρ' A * smulGL ρ⁻¹ hρ' A = 1 := by
    apply Units.ext
    rw [Units.val_mul, smulGL_val, Units.val_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      show (A : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) = μ • 1 by
        rw [← Units.val_mul]; exact hAA, smul_smul, hρ]
    have : ρ⁻¹ * ρ⁻¹ * (ρ * ρ) = 1 := by
      calc ρ⁻¹ * ρ⁻¹ * (ρ * ρ) = (ρ⁻¹ * ρ) * (ρ⁻¹ * ρ) := by ring
        _ = 1 := by rw [hρρ, mul_one]
    rw [this, one_smul]
  have hcc : smulGL ρ hρ0 N * smulGL ρ hρ0 N = 1 := by
    apply Units.ext
    rw [Units.val_mul, smulGL_val, Units.val_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      show (N : Matrix (Fin 2) (Fin 2) F) * (N : Matrix (Fin 2) (Fin 2) F) = μ⁻¹ • 1 by
        rw [← Units.val_mul]; exact hNN, smul_smul, hρ]
    have : ρ * ρ * (ρ * ρ)⁻¹ = 1 := mul_inv_cancel₀ (mul_ne_zero hρ0 hρ0)
    rw [this, one_smul]
  have hdet : (((smulGL ρ⁻¹ hρ' A : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F).det = 1 :=
    det_eq_one_of_mul_self_eq_one hss
  refine ⟨⟨smulGL ρ⁻¹ hρ' A, mem_statedSL_of_det_eq_one hdet⟩, smulGL ρ hρ0 N, ?_, ?_, hcc⟩
  · rw [modelHom_apply, hdecomp]
    exact (diagAut_smulGL_mul_cAut_smulGL ρ⁻¹ ρ hρ' hρ0 hρρ A N).symm
  · apply Subtype.ext
    exact hss

end SumNat

end FFC

end CFSG.Quasithin

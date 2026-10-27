module

public import CFSG.RankThree.PartOne.S11c.Sec66Torus

public section

namespace CFSG.RankThree.PartOne.Sec66T

open CFSG Matrix

section Matrices

variable (n : ℕ) (K : Type) [Field K]

@[expose] noncomputable def diagGL : (Fin n → Kˣ) →* GL (Fin n) K :=
  (Units.map (Matrix.diagonalRingHom (Fin n) K).toMonoidHom).comp
    (MulEquiv.piUnits.symm : (∀ _ : Fin n, Kˣ) ≃* (Fin n → K)ˣ).toMonoidHom

variable {n K}

theorem coe_diagGL (u : Fin n → Kˣ) :
    ((diagGL n K u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = diagonal fun i => (u i : K) :=
  rfl

@[expose] noncomputable def tvGL (i j : Fin n) (hij : i ≠ j) :
    Multiplicative K →* GL (Fin n) K where
  toFun t :=
    ⟨transvection i j (Multiplicative.toAdd t), transvection i j (-(Multiplicative.toAdd t)),
      by rw [transvection_mul_transvection_same i j hij, add_neg_cancel, transvection_zero],
      by rw [transvection_mul_transvection_same i j hij, neg_add_cancel, transvection_zero]⟩
  map_one' := by
    apply Units.ext
    simp [transvection_zero]
  map_mul' s t := by
    apply Units.ext
    simp [transvection_mul_transvection_same i j hij]

theorem coe_tvGL (i j : Fin n) (hij : i ≠ j) (t : Multiplicative K) :
    ((tvGL i j hij t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      transvection i j (Multiplicative.toAdd t) :=
  rfl

theorem det_tvGL (i j : Fin n) (hij : i ≠ j) (t : Multiplicative K) :
    (tvGL i j hij t : GL (Fin n) K).val.det = 1 :=
  det_transvection_of_ne i j hij _

theorem diagonal_mul_transvection_mul_inv (d : Fin n → K) (hd : ∀ k, d k ≠ 0) (i j : Fin n)
    (hij : i ≠ j) (c : K) :
    diagonal d * (1 + Matrix.single i j c) * diagonal (fun k => (d k)⁻¹) =
      1 + Matrix.single i j (d i * c * (d j)⁻¹) := by
  ext a b
  simp only [diagonal_mul, mul_diagonal, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  by_cases hab : a = b
  · subst hab
    have h1 : ¬ (i = a ∧ j = a) := fun h => hij (h.1.trans h.2.symm)
    simp [h1, hd a]
  · by_cases h : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := h
      simp [hab]
    · simp [hab, h]

theorem diagGL_mul_tvGL_mul_inv (u : Fin n → Kˣ) (i j : Fin n) (hij : i ≠ j)
    (t : Multiplicative K) :
    diagGL n K u * tvGL i j hij t * (diagGL n K u)⁻¹ =
      tvGL i j hij
        (Multiplicative.ofAdd ((u i : K) * Multiplicative.toAdd t * ((u j)⁻¹ : Kˣ))) := by
  rw [← map_inv]
  apply Units.ext
  simp only [Units.val_mul, coe_diagGL, coe_tvGL, transvection, Pi.inv_apply,
    Units.val_inv_eq_inv_val, toAdd_ofAdd]
  exact diagonal_mul_transvection_mul_inv (fun k => (u k : K)) (fun k => (u k).ne_zero) i j hij _

end Matrices

section Torus

variable {n : ℕ} {K : Type} [Field K]

@[expose] def torusVec (i₀ i₁ i₂ i₃ : Fin n) (a b c : Kˣ) : Fin n → Kˣ := fun i =>
  (if i = i₀ then a else 1) * (if i = i₁ then b else 1) * (if i = i₂ then c else 1) *
    (if i = i₃ then (a * b * c)⁻¹ else 1)

theorem torusVec_mul (i₀ i₁ i₂ i₃ : Fin n) (h01 : i₀ ≠ i₁) (h02 : i₀ ≠ i₂) (h03 : i₀ ≠ i₃)
    (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h23 : i₂ ≠ i₃) (a b c a' b' c' : Kˣ) :
    torusVec i₀ i₁ i₂ i₃ (a * a') (b * b') (c * c') =
      torusVec i₀ i₁ i₂ i₃ a b c * torusVec i₀ i₁ i₂ i₃ a' b' c' := by
  funext i
  simp only [torusVec, Pi.mul_apply]
  by_cases h0 : i = i₀
  · subst h0
    simp [h01, h02, h03]
  · by_cases h1 : i = i₁
    · subst h1
      simp [h0, h12, h13]
    · by_cases h2 : i = i₂
      · subst h2
        simp [h0, h1, h23]
      · by_cases h3 : i = i₃
        · subst h3
          simp [h0, h1, h2, mul_comm, mul_left_comm, mul_assoc]
        · simp [h0, h1, h2, h3]

theorem torusVec_apply_of_ne {i₀ i₁ i₂ i₃ w : Fin n} (h0 : w ≠ i₀) (h1 : w ≠ i₁) (h2 : w ≠ i₂)
    (h3 : w ≠ i₃) (a b c : Kˣ) : torusVec i₀ i₁ i₂ i₃ a b c w = 1 := by
  simp [torusVec, h0, h1, h2, h3]

theorem torusVec_mem {M : Subgroup Kˣ} {i₀ i₁ i₂ i₃ : Fin n} {a b c : Kˣ} (ha : a ∈ M)
    (hb : b ∈ M) (hc : c ∈ M) (i : Fin n) : torusVec i₀ i₁ i₂ i₃ a b c i ∈ M := by
  unfold torusVec
  refine M.mul_mem (M.mul_mem (M.mul_mem ?_ ?_) ?_) ?_
  · split_ifs
    exacts [ha, M.one_mem]
  · split_ifs
    exacts [hb, M.one_mem]
  · split_ifs
    exacts [hc, M.one_mem]
  · split_ifs
    exacts [M.inv_mem (M.mul_mem (M.mul_mem ha hb) hc), M.one_mem]

theorem prod_torusVec (i₀ i₁ i₂ i₃ : Fin n) (a b c : Kˣ) :
    ∏ i, torusVec i₀ i₁ i₂ i₃ a b c i = 1 := by
  simp only [torusVec]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_ite_eq' Finset.univ i₀ (fun _ => a),
    Finset.prod_ite_eq' Finset.univ i₁ (fun _ => b),
    Finset.prod_ite_eq' Finset.univ i₂ (fun _ => c),
    Finset.prod_ite_eq' Finset.univ i₃ (fun _ => (a * b * c)⁻¹)]
  simp [mul_assoc]

end Torus

open CFSG.Assembly.LowTwoRank (StatedSL StatedProj StatedScalars StatedClassicalModel)

theorem localRankLeTwo_of_mulEquiv {T X : Type} [Group T] [Group X] (e : T ≃* X) {p : ℕ}
    (hp : p.Prime) (h : LocalRankLeTwo p T) : LocalRankLeTwo p X := by
  have : Fact p.Prime := ⟨hp⟩
  intro R hR hRcard U hU1 hU2 hRU
  have hRT : IsElementaryAbelian p ↥(R.map e.symm.toMonoidHom) :=
    IsElementaryAbelian.map (A := R) e.symm.toMonoidHom
  refine h (R.map e.symm.toMonoidHom) hRT ?_ (U.map e.symm.toMonoidHom) ?_ (hU2.map _) ?_
  · rw [Subgroup.card_map_of_injective e.symm.injective, hRcard]
  · intro hbot
    exact hU1 ((Subgroup.map_eq_bot_iff_of_injective U e.symm.injective).mp hbot)
  · rintro _ ⟨r, hr, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := (Subgroup.mem_normalizer_iff.mp (hRU hr)) (e x)
    simp only [Subgroup.mem_map_equiv, MulEquiv.symm_symm, MulEquiv.coe_toMonoidHom, map_mul,
      map_inv, MulEquiv.apply_symm_apply]
    exact h1

section Abstract

variable {n : ℕ} {K : Type} [Field K]

@[expose] noncomputable def torusGL (i₀ i₁ i₂ i₃ : Fin n) (h01 : i₀ ≠ i₁) (h02 : i₀ ≠ i₂)
    (h03 : i₀ ≠ i₃) (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h23 : i₂ ≠ i₃) :
    Kˣ × Kˣ × Kˣ →* GL (Fin n) K where
  toFun x := diagGL n K (torusVec i₀ i₁ i₂ i₃ x.1 x.2.1 x.2.2)
  map_one' := by
    rw [← map_one (diagGL n K)]
    congr 1
    funext i
    simp [torusVec]
  map_mul' x y := by
    simp only [Prod.fst_mul, Prod.snd_mul]
    rw [torusVec_mul i₀ i₁ i₂ i₃ h01 h02 h03 h12 h13 h23, map_mul]

theorem isElementaryAbelian_range_comm {p : ℕ} {A P : Type*} [CommGroup A] [Group P] (f : A →* P)
    (hA : ∀ a : A, a ^ p = 1) : IsElementaryAbelian p ↥f.range := by
  refine { toIsMulCommutative := ⟨⟨?_⟩⟩, exponent_dvd_p := ?_ }
  · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← map_mul, ← map_mul, mul_comm a b]
  · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
    rintro ⟨_, a, rfl⟩
    apply Subtype.ext
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← map_pow, hA a, map_one]

theorem not_localRankLeTwo_of_torus {p : ℕ} (G : Subgroup (GL (Fin n) K))
    (j₀ j₁ j₂ j₃ w : Fin n) (h01 : j₀ ≠ j₁) (h02 : j₀ ≠ j₂) (h03 : j₀ ≠ j₃) (h12 : j₁ ≠ j₂)
    (h13 : j₁ ≠ j₃) (h23 : j₂ ≠ j₃) (hw0 : w ≠ j₀) (hw1 : w ≠ j₁) (hw2 : w ≠ j₂) (hw3 : w ≠ j₃)
    (M : Subgroup Kˣ) (hMcard : Nat.card M = p) (hMp : ∀ x ∈ M, x ^ p = 1)
    (hG : ∀ a ∈ M, ∀ b ∈ M, ∀ c ∈ M, diagGL n K (torusVec j₀ j₁ j₂ j₃ a b c) ∈ G)
    (U : Subgroup (GL (Fin n) K)) (hUG : U ≤ G) (hUne : ∃ u ∈ U, u ∉ StatedScalars (Fin n) K)
    (hU2 : ∀ u ∈ U, u ^ 2 = 1)
    (hnorm : ∀ a ∈ M, ∀ b ∈ M, ∀ c ∈ M, ∀ u ∈ U,
      diagGL n K (torusVec j₀ j₁ j₂ j₃ a b c) * u *
        (diagGL n K (torusVec j₀ j₁ j₂ j₃ a b c))⁻¹ ∈ U) :
    ¬ LocalRankLeTwo p (StatedProj G) := by
  intro hloc
  let π : G →* StatedProj G := QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf G)
  have hπ1 : ∀ g : G, π g = 1 ↔ (g : GL (Fin n) K) ∈ StatedScalars (Fin n) K := fun g =>
    (QuotientGroup.eq_one_iff g).trans Subgroup.mem_subgroupOf
  let τ : M × M × M →* GL (Fin n) K :=
    (torusGL j₀ j₁ j₂ j₃ h01 h02 h03 h12 h13 h23).comp
      (M.subtype.prodMap (M.subtype.prodMap M.subtype))
  have hτ : ∀ x : M × M × M,
      τ x = diagGL n K (torusVec j₀ j₁ j₂ j₃ (x.1 : Kˣ) (x.2.1 : Kˣ) (x.2.2 : Kˣ)) :=
    fun x => rfl
  have hτG : ∀ x, τ x ∈ G := fun x => by
    rw [hτ]
    exact hG _ x.1.2 _ x.2.1.2 _ x.2.2.2
  let τG : M × M × M →* G := τ.codRestrict G hτG
  let Φ : M × M × M →* StatedProj G := π.comp τG
  have hτGval : ∀ x, ((τG x : G) : GL (Fin n) K) = τ x := fun x => rfl
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : τ x ∈ StatedScalars (Fin n) K := (hπ1 (τG x)).mp hx
    rw [StatedScalars, MonoidHom.mem_range] at h1
    obtain ⟨c, hc⟩ := h1
    have hent : ∀ i, ((torusVec j₀ j₁ j₂ j₃ (x.1 : Kˣ) (x.2.1 : Kˣ) (x.2.2 : Kˣ) i : Kˣ) : K) =
        c := by
      intro i
      have := congrArg (fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K) i i) hc
      simpa [hτ, coe_diagGL] using this.symm
    have hcw : (c : K) = 1 := by
      rw [← hent w, torusVec_apply_of_ne hw0 hw1 hw2 hw3, Units.val_one]
    have hvec : ∀ i, torusVec j₀ j₁ j₂ j₃ (x.1 : Kˣ) (x.2.1 : Kˣ) (x.2.2 : Kˣ) i = 1 := fun i =>
      Units.ext (by rw [hent i, hcw, Units.val_one])
    have ha : (x.1 : Kˣ) = 1 := by simpa [torusVec, h01, h02, h03] using hvec j₀
    have hb : (x.2.1 : Kˣ) = 1 := by simpa [torusVec, h01.symm, h12, h13] using hvec j₁
    have hc' : (x.2.2 : Kˣ) = 1 := by simpa [torusVec, h02.symm, h12.symm, h23] using hvec j₂
    exact Prod.ext (Subtype.ext ha) (Prod.ext (Subtype.ext hb) (Subtype.ext hc'))
  have hpowM : ∀ y : M, y ^ p = 1 := fun y => Subtype.ext (by simpa using hMp _ y.2)
  have hR : IsElementaryAbelian p ↥Φ.range := isElementaryAbelian_range_comm Φ fun x =>
    Prod.ext (hpowM x.1) (Prod.ext (hpowM x.2.1) (hpowM x.2.2))
  have hRcard : Nat.card ↥Φ.range = p ^ 3 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hΦinj).toEquiv, Nat.card_prod, Nat.card_prod,
      hMcard]
    ring
  let U' : Subgroup (StatedProj G) := (U.subgroupOf G).map π
  have hU'ne : U' ≠ ⊥ := by
    obtain ⟨u, hu, huZ⟩ := hUne
    intro hbot
    have hmem : π ⟨u, hUG hu⟩ ∈ U' := ⟨⟨u, hUG hu⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact huZ ((hπ1 ⟨u, hUG hu⟩).mp hmem)
  have hU'2 : IsPGroup 2 ↥U' := by
    rintro ⟨_, g, hg, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    have hg2 : g ^ 2 = 1 := Subtype.ext (hU2 _ (Subgroup.mem_subgroupOf.mp hg))
    simp only [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← map_pow, hg2, map_one]
  have hfwd : ∀ x : M × M × M, ∀ y ∈ U', Φ x * y * (Φ x)⁻¹ ∈ U' := by
    rintro x _ ⟨g, hg, rfl⟩
    refine ⟨τG x * g * (τG x)⁻¹, ?_, ?_⟩
    · have hg' := Subgroup.mem_subgroupOf.mp hg
      refine Subgroup.mem_subgroupOf.mpr ?_
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hτGval]
      rw [hτ]
      exact hnorm _ x.1.2 _ x.2.1.2 _ x.2.2.2 _ hg'
    · simp [Φ, map_mul, map_inv]
  have hRnorm : Φ.range ≤ Subgroup.normalizer (U' : Set (StatedProj G)) := by
    rintro _ ⟨x, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hfwd x y hy, fun hy => ?_⟩
    have := hfwd x⁻¹ _ hy
    simpa [map_inv, mul_assoc] using this
  exact hloc _ hR hRcard U' hU'ne hU'2 hRnorm

end Abstract

theorem psl_torus_rank : PSLTorusRank := by
  intro T _ _ n f p hp hp5 hpn hpq hmodel hloc
  obtain ⟨hadm, K, _, hKfin, hK, ⟨e⟩⟩ := hmodel
  have hP : LocalRankLeTwo p (StatedProj (StatedSL n K)) := localRankLeTwo_of_mulEquiv e hp hloc
  have hn2 : 2 ≤ n := hadm.2.2.1
  have hpn' : p ≤ n := Nat.le_of_dvd (by omega) hpn
  have hn5 : 5 ≤ n := le_trans hp5 hpn'
  have : Fact p.Prime := ⟨hp⟩
  have hcardU : p ∣ Nat.card Kˣ := by rw [Nat.card_units, hK]; exact hpq
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p hcardU
  have hchar : CharP K 2 := by
    have : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (p := 2) (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
  let j₀ : Fin n := ⟨0, by omega⟩
  let j₁ : Fin n := ⟨1, by omega⟩
  let j₂ : Fin n := ⟨2, by omega⟩
  let j₃ : Fin n := ⟨3, by omega⟩
  let w : Fin n := ⟨4, by omega⟩
  have h01 : j₀ ≠ j₁ := by simp [j₀, j₁, Fin.ext_iff]
  have h02 : j₀ ≠ j₂ := by simp [j₀, j₂, Fin.ext_iff]
  have h03 : j₀ ≠ j₃ := by simp [j₀, j₃, Fin.ext_iff]
  have h12 : j₁ ≠ j₂ := by simp [j₁, j₂, Fin.ext_iff]
  have h13 : j₁ ≠ j₃ := by simp [j₁, j₃, Fin.ext_iff]
  have h23 : j₂ ≠ j₃ := by simp [j₂, j₃, Fin.ext_iff]
  have hw0 : w ≠ j₀ := by simp [w, j₀, Fin.ext_iff]
  have hw1 : w ≠ j₁ := by simp [w, j₁, Fin.ext_iff]
  have hw2 : w ≠ j₂ := by simp [w, j₂, Fin.ext_iff]
  have hw3 : w ≠ j₃ := by simp [w, j₃, Fin.ext_iff]
  refine not_localRankLeTwo_of_torus (StatedSL n K) j₀ j₁ j₂ j₃ w h01 h02 h03 h12 h13 h23 hw0 hw1
    hw2 hw3 (Subgroup.zpowers ζ) (by rw [Nat.card_zpowers, hζ]) ?_ ?_ (tvGL j₀ j₁ h01).range ?_ ?_
    ?_ ?_ hP
  · intro x hx
    exact orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_mem_zpowers hx).trans (by rw [hζ]))
  · intro a _ b _ c _
    refine Subgroup.subset_closure ?_
    show ((diagGL n K (torusVec j₀ j₁ j₂ j₃ a b c) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det
      = 1
    rw [coe_diagGL, Matrix.det_diagonal, ← Units.coe_prod, prod_torusVec, Units.val_one]
  · rintro _ ⟨t, rfl⟩
    exact Subgroup.subset_closure (det_tvGL j₀ j₁ h01 t)
  · refine ⟨tvGL j₀ j₁ h01 (Multiplicative.ofAdd 1), ⟨_, rfl⟩, ?_⟩
    intro h
    rw [StatedScalars, MonoidHom.mem_range] at h
    obtain ⟨c, hc⟩ := h
    have := congrArg (fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K) j₀ j₁) hc
    simp [coe_tvGL, transvection, h01] at this
  · rintro _ ⟨t, rfl⟩
    rw [← map_pow]
    have ht : t ^ 2 = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one, two_nsmul]
      exact CharTwo.add_self_eq_zero _
    rw [ht, map_one]
  · rintro a _ b _ c _ _ ⟨t, rfl⟩
    rw [diagGL_mul_tvGL_mul_inv]
    exact ⟨_, rfl⟩

end CFSG.RankThree.PartOne.Sec66T

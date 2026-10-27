module

public import CFSG.RankThree.PartOne.S11c.Sec66TorusPSL

public section

namespace CFSG.RankThree.PartOne.FOC

open CFSG Matrix
open CFSG.RankThree.PartOne.Sec66T (LocalRankLeTwo diagGL tvGL coe_diagGL coe_tvGL det_tvGL
  torusVec torusGL torusVec_mul torusVec_apply_of_ne prod_torusVec isElementaryAbelian_range_comm
  diagGL_mul_tvGL_mul_inv)
open CFSG.Assembly.LowTwoRank (StatedScalars)

section Abstract

variable {m : ℕ} {F : Type} [Field F] {T : Type} [Group T]

theorem not_localRankLeTwo_of_torus_hom {p : ℕ} (G : Subgroup (GL (Fin m) F)) (φ : G →* T)
    (hker : ∀ g : G, φ g = 1 → (g : GL (Fin m) F) ∈ StatedScalars (Fin m) F)
    (j₀ j₁ j₂ j₃ w : Fin m) (h01 : j₀ ≠ j₁) (h02 : j₀ ≠ j₂) (h03 : j₀ ≠ j₃) (h12 : j₁ ≠ j₂)
    (h13 : j₁ ≠ j₃) (h23 : j₂ ≠ j₃) (hw0 : w ≠ j₀) (hw1 : w ≠ j₁) (hw2 : w ≠ j₂) (hw3 : w ≠ j₃)
    (M : Subgroup Fˣ) (hMcard : Nat.card M = p) (hMp : ∀ x ∈ M, x ^ p = 1)
    (hG : ∀ a ∈ M, ∀ b ∈ M, ∀ c ∈ M, diagGL m F (torusVec j₀ j₁ j₂ j₃ a b c) ∈ G)
    (U : Subgroup (GL (Fin m) F)) (hUG : U ≤ G) (hUne : ∃ u ∈ U, u ∉ StatedScalars (Fin m) F)
    (hU2 : ∀ u ∈ U, u ^ 2 = 1)
    (hnorm : ∀ a ∈ M, ∀ b ∈ M, ∀ c ∈ M, ∀ u ∈ U,
      diagGL m F (torusVec j₀ j₁ j₂ j₃ a b c) * u *
        (diagGL m F (torusVec j₀ j₁ j₂ j₃ a b c))⁻¹ ∈ U) :
    ¬ LocalRankLeTwo p T := by
  intro hloc
  let τ : M × M × M →* GL (Fin m) F :=
    (torusGL j₀ j₁ j₂ j₃ h01 h02 h03 h12 h13 h23).comp
      (M.subtype.prodMap (M.subtype.prodMap M.subtype))
  have hτ : ∀ x : M × M × M,
      τ x = diagGL m F (torusVec j₀ j₁ j₂ j₃ (x.1 : Fˣ) (x.2.1 : Fˣ) (x.2.2 : Fˣ)) :=
    fun x => rfl
  have hτG : ∀ x, τ x ∈ G := fun x => by
    rw [hτ]
    exact hG _ x.1.2 _ x.2.1.2 _ x.2.2.2
  let τG : M × M × M →* G := τ.codRestrict G hτG
  let Φ : M × M × M →* T := φ.comp τG
  have hτGval : ∀ x, ((τG x : G) : GL (Fin m) F) = τ x := fun x => rfl
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : τ x ∈ StatedScalars (Fin m) F := hker (τG x) hx
    rw [StatedScalars, MonoidHom.mem_range] at h1
    obtain ⟨c, hc⟩ := h1
    have hent : ∀ i, ((torusVec j₀ j₁ j₂ j₃ (x.1 : Fˣ) (x.2.1 : Fˣ) (x.2.2 : Fˣ) i : Fˣ) : F) =
        c := by
      intro i
      have := congrArg (fun A : GL (Fin m) F => (A : Matrix (Fin m) (Fin m) F) i i) hc
      simpa [hτ, coe_diagGL] using this.symm
    have hcw : (c : F) = 1 := by
      rw [← hent w, torusVec_apply_of_ne hw0 hw1 hw2 hw3, Units.val_one]
    have hvec : ∀ i, torusVec j₀ j₁ j₂ j₃ (x.1 : Fˣ) (x.2.1 : Fˣ) (x.2.2 : Fˣ) i = 1 := fun i =>
      Units.ext (by rw [hent i, hcw, Units.val_one])
    have ha : (x.1 : Fˣ) = 1 := by simpa [torusVec, h01, h02, h03] using hvec j₀
    have hb : (x.2.1 : Fˣ) = 1 := by simpa [torusVec, h01.symm, h12, h13] using hvec j₁
    have hc' : (x.2.2 : Fˣ) = 1 := by simpa [torusVec, h02.symm, h12.symm, h23] using hvec j₂
    exact Prod.ext (Subtype.ext ha) (Prod.ext (Subtype.ext hb) (Subtype.ext hc'))
  have hpowM : ∀ y : M, y ^ p = 1 := fun y => Subtype.ext (by simpa using hMp _ y.2)
  have hR : IsElementaryAbelian p ↥Φ.range := isElementaryAbelian_range_comm Φ fun x =>
    Prod.ext (hpowM x.1) (Prod.ext (hpowM x.2.1) (hpowM x.2.2))
  have hRcard : Nat.card ↥Φ.range = p ^ 3 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hΦinj).toEquiv, Nat.card_prod, Nat.card_prod,
      hMcard]
    ring
  let U' : Subgroup T := (U.subgroupOf G).map φ
  have hU'ne : U' ≠ ⊥ := by
    obtain ⟨u, hu, huZ⟩ := hUne
    intro hbot
    have hmem : φ ⟨u, hUG hu⟩ ∈ U' := ⟨⟨u, hUG hu⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact huZ (hker ⟨u, hUG hu⟩ hmem)
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
  have hRnorm : Φ.range ≤ Subgroup.normalizer (U' : Set T) := by
    rintro _ ⟨x, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hfwd x y hy, fun hy => ?_⟩
    have := hfwd x⁻¹ _ hy
    simpa [map_inv, mul_assoc] using this
  exact hloc _ hR hRcard U' hU'ne hU'2 hRnorm

end Abstract

section SL

variable {m : ℕ} {F : Type} [Field F] {T : Type} [Group T]

theorem diagGL_commute (u v : Fin m → Fˣ) : diagGL m F u * diagGL m F v = diagGL m F v * diagGL m F u := by
  rw [← map_mul, ← map_mul, mul_comm]

theorem det_diagGL_torusVec (j₀ j₁ j₂ j₃ : Fin m) (a b c : Fˣ) :
    GeneralLinearGroup.det (diagGL m F (torusVec j₀ j₁ j₂ j₃ a b c)) = 1 := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, coe_diagGL, Matrix.det_diagonal, ← Units.coe_prod,
    prod_torusVec, Units.val_one]

theorem not_localRankLeTwo_of_SL_hom [Finite F] {p : ℕ} (hp : p.Prime) (hm : 5 ≤ m)
    (hpF : p ∣ Nat.card Fˣ) (φ : Matrix.SpecialLinearGroup (Fin m) F →* T)
    (hker : ∀ s, φ s = 1 → s ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin m) F)) :
    ¬ LocalRankLeTwo p T := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p hpF
  set G : Subgroup (GL (Fin m) F) :=
    (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin m) F →* GL (Fin m) F).range
    with hGdef
  let e : Matrix.SpecialLinearGroup (Fin m) F ≃* G :=
    MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective
  let φG : G →* T := φ.comp e.symm.toMonoidHom
  have hφG : ∀ s, φG (e s) = φ s := fun s => by simp [φG]
  have hkerG : ∀ g : G, φG g = 1 → (g : GL (Fin m) F) ∈ StatedScalars (Fin m) F := by
    intro g hg
    obtain ⟨s, rfl⟩ := e.surjective g
    rw [hφG] at hg
    obtain ⟨r, hr, hrs⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp (hker s hg)
    have hru : IsUnit r := IsUnit.of_pow_eq_one hr (by rw [Fintype.card_fin]; omega)
    obtain ⟨u, rfl⟩ := hru
    refine ⟨u, Units.ext ?_⟩
    rw [GeneralLinearGroup.coe_scalar]
    exact hrs
  have hmem : ∀ g : GL (Fin m) F, GeneralLinearGroup.det g = 1 → g ∈ G := fun g hg => by
    rw [hGdef, Matrix.SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker]
    exact hg
  let j₀ : Fin m := ⟨0, by omega⟩
  let j₁ : Fin m := ⟨1, by omega⟩
  let j₂ : Fin m := ⟨2, by omega⟩
  let j₃ : Fin m := ⟨3, by omega⟩
  let w : Fin m := ⟨4, by omega⟩
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
  have hMcard : Nat.card (Subgroup.zpowers ζ) = p := by rw [Nat.card_zpowers, hζ]
  have hMp : ∀ x ∈ Subgroup.zpowers ζ, x ^ p = 1 := fun x hx =>
    orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_mem_zpowers hx).trans (by rw [hζ]))
  have hG : ∀ a ∈ Subgroup.zpowers ζ, ∀ b ∈ Subgroup.zpowers ζ, ∀ c ∈ Subgroup.zpowers ζ,
      diagGL m F (torusVec j₀ j₁ j₂ j₃ a b c) ∈ G := fun a _ b _ c _ =>
    hmem _ (det_diagGL_torusVec j₀ j₁ j₂ j₃ a b c)
  by_cases hF2 : ringChar F = 2
  · have : CharP F 2 := ringChar.of_eq hF2
    refine not_localRankLeTwo_of_torus_hom G φG hkerG j₀ j₁ j₂ j₃ w h01 h02 h03 h12 h13 h23 hw0 hw1
      hw2 hw3 (Subgroup.zpowers ζ) hMcard hMp hG (tvGL j₀ j₁ h01).range ?_ ?_ ?_ ?_
    · rintro _ ⟨t, rfl⟩
      exact hmem _ (Units.ext (by
        rw [GeneralLinearGroup.val_det_apply]
        exact det_tvGL j₀ j₁ h01 t))
    · refine ⟨tvGL j₀ j₁ h01 (Multiplicative.ofAdd 1), ⟨_, rfl⟩, ?_⟩
      intro h
      rw [StatedScalars, MonoidHom.mem_range] at h
      obtain ⟨c, hc⟩ := h
      have := congrArg (fun A : GL (Fin m) F => (A : Matrix (Fin m) (Fin m) F) j₀ j₁) hc
      simp [coe_tvGL, Matrix.transvection, h01] at this
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
  · have hneg : (-1 : F) ≠ 1 := Ring.neg_one_ne_one_of_char_ne_two hF2
    set u₀ : GL (Fin m) F := diagGL m F (torusVec j₀ j₁ j₂ j₃ (-1 : Fˣ) (-1 : Fˣ) 1) with hu₀
    have hu₀G : u₀ ∈ G := hmem _ (det_diagGL_torusVec j₀ j₁ j₂ j₃ _ _ _)
    have hu₀sq : u₀ ^ 2 = 1 := by
      have h1 : u₀ = torusGL j₀ j₁ j₂ j₃ h01 h02 h03 h12 h13 h23 ((-1 : Fˣ), (-1 : Fˣ), (1 : Fˣ)) :=
        rfl
      rw [h1, ← map_pow]
      have h2 : ((-1 : Fˣ), (-1 : Fˣ), (1 : Fˣ)) ^ 2 = 1 :=
        Prod.ext (by simp) (Prod.ext (by simp) (by simp))
      rw [h2, map_one]
    refine not_localRankLeTwo_of_torus_hom G φG hkerG j₀ j₁ j₂ j₃ w h01 h02 h03 h12 h13 h23 hw0 hw1
      hw2 hw3 (Subgroup.zpowers ζ) hMcard hMp hG (Subgroup.zpowers u₀) ?_ ?_ ?_ ?_
    · exact Subgroup.zpowers_le.mpr hu₀G
    · refine ⟨u₀, Subgroup.mem_zpowers u₀, ?_⟩
      intro h
      rw [StatedScalars, MonoidHom.mem_range] at h
      obtain ⟨c, hc⟩ := h
      have hent : ∀ i, ((torusVec j₀ j₁ j₂ j₃ (-1 : Fˣ) (-1 : Fˣ) 1 i : Fˣ) : F) = c := by
        intro i
        have := congrArg (fun A : GL (Fin m) F => (A : Matrix (Fin m) (Fin m) F) i i) hc
        simpa [hu₀, coe_diagGL] using this.symm
      have h0 := hent j₀
      have hw := hent w
      rw [torusVec_apply_of_ne hw0 hw1 hw2 hw3, Units.val_one] at hw
      simp only [torusVec, h01, h02, h03, ↓reduceIte, mul_one] at h0
      apply hneg
      have h3 : ((-1 : Fˣ) : F) = 1 := h0.trans hw.symm
      simpa using h3
    · intro u hu
      obtain ⟨k, rfl⟩ := hu
      rw [← _root_.zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, _root_.zpow_natCast, hu₀sq, _root_.one_zpow]
    · rintro a _ b _ c _ u hu
      obtain ⟨k, rfl⟩ := hu
      have hcomm : Commute (diagGL m F (torusVec j₀ j₁ j₂ j₃ a b c)) u₀ :=
        diagGL_commute _ _
      have h2 := (hcomm.zpow_right k).eq
      have h3 : diagGL m F (torusVec j₀ j₁ j₂ j₃ a b c) * u₀ ^ k *
          (diagGL m F (torusVec j₀ j₁ j₂ j₃ a b c))⁻¹ = u₀ ^ k := by
        rw [mul_inv_eq_iff_eq_mul]
        exact h2
      rw [h3]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers u₀) k

end SL

end CFSG.RankThree.PartOne.FOC

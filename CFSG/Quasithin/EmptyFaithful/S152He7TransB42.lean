module

public import CFSG.Quasithin.EmptyFaithful.S152He7B42
public import CFSG.Quasithin.EmptyFaithful.S152He7TransBridge

public section

namespace CFSG.Quasithin.He7

open CFSG.Quasithin CFSG.Quasithin.He5 CFSG.Quasithin.He6 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X1

theorem sqtkGroup_of_mulEquiv' {A B : Type} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) (h : SQTKGroup B) : SQTKGroup A := by
  refine ⟨fun p hp hp2 => ?_, h.2.of_mulEquiv e⟩
  have h1 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e
  have h2 : CFSG.Open.pRank p (⊤ : Subgroup B) ≤ 2 := h.1 p hp hp2
  show CFSG.Open.pRank p (⊤ : Subgroup A) ≤ 2
  omega

theorem sqtkGroup_subgroup' {A : Type} [Group A] [Finite A] (h : SQTKGroup A) (K : Subgroup A) :
    SQTKGroup ↥K := by
  refine ⟨fun p hp hp2 => ?_, h.2.subgroup K⟩
  have h1 := CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt K.subtype K.subtype_injective
  have h2 : CFSG.Open.pRank p (⊤ : Subgroup A) ≤ 2 := h.1 p hp hp2
  show CFSG.Open.pRank p (⊤ : Subgroup ↥K) ≤ 2
  omega

theorem card_projectiveSL_K2 {n : ℕ} (hn : n = 4 ∨ n = 5) :
    Nat.card (projectiveSL n K2) = 20160 ∨ Nat.card (projectiveSL n K2) = 9999360 := by
  have e : CFSG.Assembly.LowTwoRank.StatedSL n K2 ≃* projectiveSL n K2 :=
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K2).symm.trans
      (MulEquiv.ofBijective (proj n K2) ⟨proj_injective n, proj_surjective n K2⟩)
  rw [← Nat.card_congr e.toEquiv]
  rcases hn with rfl | rfl
  · left
    exact card_statedSL_four_zmod1527d
  · right
    exact card_statedSL_five_zmod1527d

variable {n : ℕ}

theorem pureTransIi_aux (hB42 : AsB42) (hn : n = 4 ∨ n = 5)
    [Finite (MulAut (projectiveSL n K2))] (hSQ : SQTKGroup (MulAut (projectiveSL n K2)))
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1) [Nontrivial W]
    (φ : MulAut (projectiveSL n K2) →* MulAut W)
    (hirr : ∀ U : Subgroup W, (∀ y, ∀ u ∈ U, φ y u ∈ U) → U = ⊥ ∨ U = ⊤)
    {T₀ V₀ : Subgroup (MulAut (projectiveSL n K2))} (hT : IsPGroup 2 ↥T₀) (hTi : ¬ 2 ∣ T₀.index)
    (hV₀T : V₀ ≤ T₀) (hV₀n : ∀ s ∈ T₀, ∀ v ∈ V₀, s * v * s⁻¹ ∈ V₀)
    (hbd : ∀ v ∈ V₀, (fixV (Subgroup.zpowers (φ v))).index ≤ 2) : ∀ v ∈ V₀, φ v = 1 := by
  classical
  have hn3 : 3 ≤ n := by omega
  by_contra hcon
  push Not at hcon
  obtain ⟨v₀, hv₀, hφv₀⟩ := hcon
  have hv₀1 : v₀ ≠ 1 := fun h => hφv₀ (by rw [h, map_one])
  have hirrG : ∀ U : Subgroup W, (∀ g ∈ φ.range, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤ :=
    fun U hU => hirr U (fun y u hu => hU (φ y) ⟨y, rfl⟩ u hu)
  rcases hom_injective_or_exp_two hn3 φ with hinj | hexp
  swap
  ·
    have hG2 : IsPGroup 2 ↥φ.range := by
      rintro ⟨_, y, rfl⟩
      refine ⟨1, Subtype.ext ?_⟩
      simpa [sq] using hexp y
    have hbot := eq_bot_of_irr_of_isPGroup hW hG2 hirrG
    apply hφv₀
    have : φ v₀ ∈ φ.range := ⟨v₀, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  have hTnil : Group.IsNilpotent ↥T₀ := hT.isNilpotent
  have hV₀normal : (V₀.subgroupOf T₀).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hV₀T]
    exact fun v t hv ht => hV₀n t ht v hv
  have hV₀ne : V₀.subgroupOf T₀ ≠ ⊥ := by
    intro h
    apply hv₀1
    have : (⟨v₀, hV₀T hv₀⟩ : ↥T₀) ∈ V₀.subgroupOf T₀ := hv₀
    rw [h, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  obtain ⟨z', hz'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hV₀ne)
  have hz'V : (z' : ↥T₀) ∈ V₀.subgroupOf T₀ := z'.2.1
  have hz'c : (z' : ↥T₀) ∈ Subgroup.center ↥T₀ := z'.2.2
  set z : MulAut (projectiveSL n K2) := ((z' : ↥T₀) : MulAut (projectiveSL n K2)) with hzdef
  have hzV : z ∈ V₀ := hz'V
  have hz1 : z ≠ 1 := fun h => hz' (Subtype.ext (Subtype.ext h))
  have hzcomm : ∀ t ∈ T₀, z * t = t * z := fun t ht =>
    congrArg Subtype.val ((Subgroup.mem_center_iff.1 hz'c ⟨t, ht⟩).symm)
  have hzInn : z ∈ InnP n := eq_inn_of_commute_sylow hn3 hT hTi hzcomm
  have hζ1 : φ z ≠ 1 := fun h => hz1 (hinj (by rw [h, map_one]))
  have hζi : (fixV (Subgroup.zpowers (φ z))).index = 2 := by
    refine le_antisymm (hbd z hzV) ?_
    rw [index_fixV_zpowers_eq_card_cmt]
    have hne : cmt (φ z) ⊤ ≠ ⊥ := fun h => hζ1 (MulEquiv.ext fun w => by
      exact cmt_eq_bot_iff.1 h w (Subgroup.mem_top w))
    exact (Subgroup.one_lt_card_iff_ne_bot _).2 hne
  set Λ : Subgroup (MulAut W) := (InnP n).map φ with hΛ
  have hζΛ : φ z ∈ Λ := ⟨z, hzInn, rfl⟩
  have eΛ : ↥(InnP n) ≃* ↥Λ := Subgroup.equivMapOfInjective (InnP n) φ hinj
  have hsimp : IsSimpleGroup ↥Λ := by
    have := isSimpleGroup_innP hn3
    exact eΛ.symm.isSimpleGroup
  have hN : Nat.card ↥Λ = 20160 ∨ Nat.card ↥Λ = 9999360 := by
    rw [← Nat.card_congr eΛ.toEquiv]
    have e2 : projectiveSL n K2 ≃* ↥(InnP n) := MonoidHom.ofInjective (conj_injective n)
    rw [← Nat.card_congr e2.toEquiv]
    exact card_projectiveSL_K2 hn
  have hSQΛ : SQTKGroup ↥Λ :=
    sqtkGroup_of_mulEquiv' eΛ.symm (sqtkGroup_subgroup' hSQ (InnP n))
  have hnorm : ∀ g ∈ φ.range, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ := by
    rintro _ ⟨y, rfl⟩ _ ⟨i, hi, rfl⟩
    exact ⟨y * i * y⁻¹, innP_conj_mem y hi, by simp [map_mul, map_inv]⟩
  have hirrΛ := irr_of_transvection hnorm hirrG hsimp hζΛ hζ1 hζi
  set y₀ : MulAut (projectiveSL n K2) := LinearFlag.dualAut n K2 with hy₀
  have hy₀out : y₀ ∉ InnP n := dualAut_not_mem_inn hn3
  have hsΛ : ∀ l ∈ Λ, φ y₀ * l * (φ y₀)⁻¹ ∈ Λ := by
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨y₀ * i * y₀⁻¹, innP_conj_mem y₀ hi, by simp [map_mul, map_inv]⟩
  have hout : ¬ ∃ l ∈ Λ, ∀ x ∈ Λ, φ y₀ * x * (φ y₀)⁻¹ = l * x * l⁻¹ := by
    rintro ⟨_, ⟨c, hc, rfl⟩, h⟩
    apply hy₀out
    have hcomm : ∀ i ∈ InnP n, (c⁻¹ * y₀) * i = i * (c⁻¹ * y₀) := by
      intro i hi
      have h1 := h (φ i) ⟨i, hi, rfl⟩
      have h2 : y₀ * i * y₀⁻¹ = c * i * c⁻¹ := hinj (by simpa [map_mul, map_inv] using h1)
      calc c⁻¹ * y₀ * i = c⁻¹ * (y₀ * i * y₀⁻¹) * y₀ := by group
        _ = c⁻¹ * (c * i * c⁻¹) * y₀ := by rw [h2]
        _ = i * (c⁻¹ * y₀) := by group
    have h3 : c⁻¹ * y₀ = 1 := eq_one_of_commute_innP hcomm
    have h4 : y₀ = c := by
      calc y₀ = c * (c⁻¹ * y₀) := by group
        _ = c := by rw [h3, mul_one]
    rw [h4]
    exact hc
  exact b42_out_false hB42 hW hN hsimp hSQΛ hirrΛ hζΛ hζ1 hζi hsΛ hout

theorem pureTransIi_of_b42 (hB42 : AsB42) : PureTransIi := by
  intro Y _ _ n hn hiso hSQ W _ _ hW hnt φ hirr T₀ V₀ hT₀ hVT hVn hbd
  classical
  obtain ⟨e₀⟩ := hiso
  let e : Y ≃* MulAut (projectiveSL n K2) :=
    e₀.trans (MulAut.congr (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K2))
  have : Finite (MulAut (projectiveSL n K2)) := Finite.of_equiv Y e.toEquiv
  have := hnt
  let φ' : MulAut (projectiveSL n K2) →* MulAut W := φ.comp e.symm.toMonoidHom
  have hφ' : ∀ y : Y, φ' (e y) = φ y := fun y => by simp [φ']
  have hSQ' : SQTKGroup (MulAut (projectiveSL n K2)) := sqtkGroup_of_mulEquiv' e.symm hSQ
  have hirr' : ∀ U : Subgroup W, (∀ y, ∀ u ∈ U, φ' y u ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    refine hirr U (fun y u hu => ?_)
    have := hU (e y) u hu
    rwa [hφ'] at this
  have hT' : IsPGroup 2 ↥(T₀.map e.toMonoidHom) := hT₀.2.1.map _
  have hTi' : ¬ 2 ∣ (T₀.map e.toMonoidHom).index := by
    intro h2
    apply hT₀.2.2
    have h3 : (T₀.subgroupOf ⊤).index = T₀.index := Subgroup.relIndex_top_right T₀
    rw [h3, ← Subgroup.index_map_equiv T₀ e]
    exact h2
  have hVT' : V₀.map e.toMonoidHom ≤ T₀.map e.toMonoidHom := Subgroup.map_mono hVT
  have hVn' : ∀ s ∈ T₀.map e.toMonoidHom, ∀ v ∈ V₀.map e.toMonoidHom,
      s * v * s⁻¹ ∈ V₀.map e.toMonoidHom := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨v, hv, rfl⟩
    exact ⟨s * v * s⁻¹, hVn s hs v hv, by simp [map_mul, map_inv]⟩
  have hbd' : ∀ v ∈ V₀.map e.toMonoidHom, (fixV (Subgroup.zpowers (φ' v))).index ≤ 2 := by
    rintro _ ⟨v, hv, rfl⟩
    have := hbd v hv
    rwa [← hφ' v] at this
  have key := pureTransIi_aux hB42 hn hSQ' hW φ' hirr' hT' hTi' hVT' hVn' hbd'
  intro v hv
  rw [← hφ' v]
  exact key _ ⟨v, hv, rfl⟩

end CFSG.Quasithin.He7

theorem CFSG.Quasithin.insp15227TransIi_of_b42 (hB42 : AsB42) : Insp15227TransIi :=
  insp15227TransIi_of_pure (He7.pureTransIi_of_b42 hB42)

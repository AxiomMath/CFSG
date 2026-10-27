module

public import CFSG.Quasithin.Recognition.WBN.Weyl
import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
import CFSG.GroupTheory.PermSylowTwo.Alt

public section

namespace CFSG.Quasithin.WBN

open CFSG.Open CFSG.QuasithinUnique

variable {Y : Type} [Group Y]

private theorem finite_of_index_two {C Ŷ : Type} [Group C] [Finite C] [Group Ŷ]
    (e : Y ≃* C) (ι : Y →* Ŷ) (hι : Function.Injective ι) (hidx : ι.range.index = 2) :
    Finite Ŷ := by
  haveI : Finite Y := Finite.of_injective e.toMonoidHom e.injective
  haveI : Finite ↥(ι.range) := Finite.of_surjective
    ((MonoidHom.ofInjective hι).toMonoidHom) (MonoidHom.ofInjective hι).surjective
  exact (Subgroup.finite_iff_finite_and_finiteIndex (H := ι.range)).mpr
    ⟨inferInstance, Subgroup.finiteIndex_iff.mpr (by rw [hidx]; decide)⟩

private theorem mem_range_of_pow_eq_one {Ŷ : Type} [Group Ŷ] [Finite Ŷ] (ι : Y →* Ŷ)
    (hidx : ι.range.index = 2) {m : ℕ} (hm : Odd m) {x : Ŷ} (hx : x ^ m = 1) :
    x ∈ ι.range := by
  have hodd : Odd (orderOf x) := hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one hx)
  exact CFSG.Quasithin.F1.mem_of_odd_orderOf (N := ι.range) (by omega) hodd

private theorem eq_top_of_range_le_maxTwoLocal {C Ŷ : Type} [Group C] [Finite C] [Group Ŷ]
    {U P₀ P₁ : Subgroup C} (S : CFSG.Quasithin.H13.Sec53F.Yam.YamStd C U P₀ P₁) (e : Y ≃* C)
    (ι : Y →* Ŷ) (hι : Function.Injective ι) (hidx : ι.range.index = 2)
    {M : Subgroup Ŷ} (hM : IsMaximalTwoLocal M) (hY0M : ι.range ≤ M) : M = ⊤ := by
  classical
  haveI : Finite Ŷ := finite_of_index_two e ι hι hidx
  obtain ⟨R, hRne, hR2, rfl⟩ := hM.1
  have hY0N : ι.range ≤ Subgroup.normalizer (R : Set Ŷ) := hY0M
  have hY0Ninf : ι.range ≤ Subgroup.normalizer ((R ⊓ ι.range : Subgroup Ŷ) : Set Ŷ) :=
    (le_inf hY0N Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf
  let ψ : ↥(ι.range) ≃* C := (MonoidHom.ofInjective hι).symm.trans e
  let N0 : Subgroup ↥(ι.range) := (R ⊓ ι.range).subgroupOf ι.range
  have hN0n : N0.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr hY0Ninf
  have hN0p : IsPGroup 2 N0 :=
    (hR2.to_inf_left).of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  have hNCn : (N0.map ψ.toMonoidHom).Normal := hN0n.map ψ.toMonoidHom ψ.surjective
  have hNCp : IsPGroup 2 (N0.map ψ.toMonoidHom) := hN0p.map ψ.toMonoidHom
  have hNCbot : N0.map ψ.toMonoidHom = ⊥ := S.no_normal _ hNCn hNCp
  have hN0bot : N0 = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective N0 ψ.injective).mp hNCbot
  have hNbot : R ⊓ ι.range = ⊥ := by
    have hmapN0 : N0.map ι.range.subtype = R ⊓ ι.range :=
      Subgroup.map_subgroupOf_eq_of_le inf_le_right
    rw [← hmapN0, hN0bot, Subgroup.map_bot]
  obtain ⟨r, hrR, hrY⟩ : ∃ r ∈ R, r ∉ ι.range := by
    by_contra h
    have hRle : R ≤ ι.range := fun r hr => by
      by_contra hrY
      exact h ⟨r, hr, hrY⟩
    exact hRne (le_bot_iff.mp (by rw [← hNbot]; exact le_inf le_rfl hRle))
  have hdvd : (Subgroup.normalizer (R : Set Ŷ)).index ∣ ι.range.index :=
    Subgroup.index_dvd_of_le hY0M
  rw [hidx] at hdvd
  have hMne2 : (Subgroup.normalizer (R : Set Ŷ)).index ≠ 2 := by
    intro h2
    have heq : ι.range = Subgroup.normalizer (R : Set Ŷ) :=
      Subgroup.eq_of_index_dvd_index hY0M (by rw [hidx, h2])
    exact hrY (heq ▸ Subgroup.le_normalizer hrR)
  have hpos : 0 < (Subgroup.normalizer (R : Set Ŷ)).index :=
    Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  have hle2 : (Subgroup.normalizer (R : Set Ŷ)).index ≤ 2 := Nat.le_of_dvd (by decide) hdvd
  exact Subgroup.index_eq_one.mp (by omega)

private theorem not_range_le_maxTwoLocal {C Ŷ : Type} [Group C] [Finite C] [Group Ŷ]
    {U P₀ P₁ : Subgroup C} (S : CFSG.Quasithin.H13.Sec53F.Yam.YamStd C U P₀ P₁) (e : Y ≃* C)
    (ι : Y →* Ŷ) (hι : Function.Injective ι) (hidx : ι.range.index = 2)
    {T M₁ M₂ : Subgroup Ŷ} (hY : IsYAmalgamPair T M₁ M₂) {M : Subgroup Ŷ}
    (hM : IsMaximalTwoLocal M) (hNM : Subgroup.normalizer (T : Set Ŷ) ≤ M) :
    ¬ ι.range ≤ M := by
  intro hle
  have htop := eq_top_of_range_le_maxTwoLocal S e ι hι hidx hM hle
  rcases (hY.2.2 M).1 ⟨hM, hNM⟩ with rfl | rfl
  · have hloc : IsTwoLocal (⊤ : Subgroup Ŷ) := htop ▸ hM.1
    have h2 : ⊤ = M₂ := (((hY.2.2 M₂).2 (Or.inr rfl)).1).2 ⊤ hloc le_top
    exact hY.2.1 (htop.trans h2)
  · have hloc : IsTwoLocal (⊤ : Subgroup Ŷ) := htop ▸ hM.1
    have h1 : ⊤ = M₁ := (((hY.2.2 M₁).2 (Or.inl rfl)).1).2 ⊤ hloc le_top
    exact hY.2.1 (h1.symm.trans htop.symm)

private theorem exists_theta_of_index_two {C Ŷ : Type} [Group C] [Finite C] [Group Ŷ]
    {U P₀ P₁ : Subgroup C} (S : CFSG.Quasithin.H13.Sec53F.Yam.YamStd C U P₀ P₁)
    (e : Y ≃* C) (ι : Y →* Ŷ) (hι : Function.Injective ι) (hidx : ι.range.index = 2)
    {T : Subgroup Ŷ} (hT : IsSylowTwoOf T ⊤) :
    ∃ θ : C ≃* ↥(ι.range),
      U.map θ.toMonoidHom = (T ⊓ ι.range).subgroupOf ι.range ∧
        IsYAmalgamPair ((T ⊓ ι.range).subgroupOf ι.range)
          (P₀.map θ.toMonoidHom) (P₁.map θ.toMonoidHom) := by
  classical
  haveI : Finite Ŷ := finite_of_index_two e ι hι hidx
  haveI : ι.range.Normal := Subgroup.normal_of_index_eq_two hidx
  have hTN : T ≤ Subgroup.normalizer (ι.range : Set Ŷ) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact le_top
  have hT0 : IsSylowTwoOf ((T ⊓ ι.range).subgroupOf ι.range) ⊤ :=
    CFSG.GroupTheory.PermSylowTwo.isSylowTwoOf_subgroupOf_top
      (CFSG.Quasithin.F7.isSylowTwoOf_inf_normal hT le_top hTN)
  let ψ : ↥(ι.range) ≃* C := (MonoidHom.ofInjective hι).symm.trans e
  have hT0C : IsSylowTwoOf (((T ⊓ ι.range).subgroupOf ι.range).map ψ.toMonoidHom) ⊤ := by
    simpa using CFSG.GroupTheory.PermSylowTwo.isSylowTwoOf_map_mulEquiv ψ hT0
  obtain ⟨c, -, hc⟩ := CFSG.QuasithinUnique.IsSylowTwoOf.exists_conj
    (S := U) (S' := ((T ⊓ ι.range).subgroupOf ι.range).map ψ.toMonoidHom) (H := ⊤)
    S.sylow hT0C
  let θ : C ≃* ↥(ι.range) := (MulAut.conj c).trans ψ.symm
  have hθU : U.map θ.toMonoidHom = (T ⊓ ι.range).subgroupOf ι.range := by
    rw [show θ.toMonoidHom = ψ.symm.toMonoidHom.comp (MulAut.conj c).toMonoidHom from
      MulEquiv.toMonoidHom_trans (MulAut.conj c) ψ.symm,
      ← Subgroup.map_map, ← hc, Subgroup.map_map]
    have hcomp : ψ.symm.toMonoidHom.comp ψ.toMonoidHom = MonoidHom.id ↥(ι.range) := by
      ext z
      simp [ψ]
    rw [hcomp, Subgroup.map_id]
  refine ⟨θ, hθU, ?_⟩
  have hpair := IsYAmalgamPair.map θ S.isYAmalgamPair
  rw [hθU] at hpair
  exact hpair

private theorem parabolics_fixed_under_automorphism {C Y0 : Type} [Group C] [Group Y0]
    {U P₀ P₁ : Subgroup C} (S : CFSG.Quasithin.H13.Sec53F.Yam.YamStd C U P₀ P₁)
    (hswap : ∀ φ : C ≃* C, P₀.map φ.toMonoidHom ≠ P₁)
    (θ : C ≃* Y0)
    (φ : Y0 ≃* Y0) (hφT : (U.map θ.toMonoidHom).map φ.toMonoidHom =
      U.map θ.toMonoidHom) :
    (P₀.map θ.toMonoidHom).map φ.toMonoidHom = P₀.map θ.toMonoidHom ∧
      (P₁.map θ.toMonoidHom).map φ.toMonoidHom = P₁.map θ.toMonoidHom := by
  let β : C ≃* C := (θ.trans φ).trans θ.symm
  have hcomp : θ.toMonoidHom.comp β.toMonoidHom = φ.toMonoidHom.comp θ.toMonoidHom := by
    ext c
    simp [β]
  have hβU : U.map β.toMonoidHom = U := by
    apply Subgroup.map_injective (f := θ.toMonoidHom) θ.injective
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hφT]
  have hβN : (Subgroup.normalizer (U : Set C)).map β.toMonoidHom =
      Subgroup.normalizer (U : Set C) := by
    rw [Subgroup.map_equiv_normalizer_eq, hβU]
  have hβP0 : P₀.map β.toMonoidHom = P₀ := by
    have hco : IsCoatom (P₀.map β.toMonoidHom) :=
      (show IsCoatom ((MulEquiv.mapSubgroup β) P₀) from
        ((MulEquiv.mapSubgroup β).isCoatom_iff P₀).mpr S.coatom₀)
    have hN : Subgroup.normalizer (U : Set C) ≤ P₀.map β.toMonoidHom := by
      rw [← hβN]
      exact Subgroup.map_mono S.le₀
    rcases S.above _ hN hco.ne_top with hle | hle
    · exact ((hco.le_iff_eq S.coatom₀.ne_top).mp hle).symm
    · exact absurd ((hco.le_iff_eq S.coatom₁.ne_top).mp hle).symm (hswap β)
  have hβP1 : P₁.map β.toMonoidHom = P₁ := by
    have hco : IsCoatom (P₁.map β.toMonoidHom) :=
      (show IsCoatom ((MulEquiv.mapSubgroup β) P₁) from
        ((MulEquiv.mapSubgroup β).isCoatom_iff P₁).mpr S.coatom₁)
    have hN : Subgroup.normalizer (U : Set C) ≤ P₁.map β.toMonoidHom := by
      rw [← hβN]
      exact Subgroup.map_mono S.le₁
    rcases S.above _ hN hco.ne_top with hle | hle
    · have hEq : P₁.map β.toMonoidHom = P₀ :=
        ((hco.le_iff_eq S.coatom₀.ne_top).mp hle).symm
      have hcontr : P₀.map β.symm.toMonoidHom = P₁ := by
        rw [← hEq, Subgroup.map_map]
        have hcomp' : β.symm.toMonoidHom.comp β.toMonoidHom = MonoidHom.id C := by
          ext c
          simp [β]
        rw [hcomp', Subgroup.map_id]
      exact absurd hcontr (hswap β.symm)
    · exact ((hco.le_iff_eq S.coatom₁.ne_top).mp hle).symm
  refine ⟨?_, ?_⟩
  · calc (P₀.map θ.toMonoidHom).map φ.toMonoidHom
        = P₀.map (φ.toMonoidHom.comp θ.toMonoidHom) := Subgroup.map_map P₀ _ _
      _ = P₀.map (θ.toMonoidHom.comp β.toMonoidHom) := by rw [hcomp]
      _ = (P₀.map β.toMonoidHom).map θ.toMonoidHom := (Subgroup.map_map P₀ _ _).symm
      _ = P₀.map θ.toMonoidHom := by rw [hβP0]
  · calc (P₁.map θ.toMonoidHom).map φ.toMonoidHom
        = P₁.map (φ.toMonoidHom.comp θ.toMonoidHom) := Subgroup.map_map P₁ _ _
      _ = P₁.map (θ.toMonoidHom.comp β.toMonoidHom) := by rw [hcomp]
      _ = (P₁.map β.toMonoidHom).map θ.toMonoidHom := (Subgroup.map_map P₁ _ _).symm
      _ = P₁.map θ.toMonoidHom := by rw [hβP1]

private theorem conjNormal_fixes_theta_U {C Ŷ : Type} [Group C] [Group Ŷ]
    {U : Subgroup C} (ι : Y →* Ŷ) (hι : Function.Injective ι)
    (hidx : ι.range.index = 2) [ι.range.Normal] {T : Subgroup Ŷ} {θ : C ≃* ↥(ι.range)}
    (hθU : U.map θ.toMonoidHom = (T ⊓ ι.range).subgroupOf ι.range) {x : Ŷ}
    (hx : x ∈ Subgroup.normalizer (T : Set Ŷ)) :
    (U.map θ.toMonoidHom).map (MulAut.conjNormal (H := ι.range) x).toMonoidHom =
      U.map θ.toMonoidHom := by
  let φx : ↥(ι.range) ≃* ↥(ι.range) := MulAut.conjNormal (H := ι.range) x
  have hφT0 : ((T ⊓ ι.range).subgroupOf ι.range).map φx.toMonoidHom =
      (T ⊓ ι.range).subgroupOf ι.range := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hwT : (w : Ŷ) ∈ T := (Subgroup.mem_subgroupOf.mp hw).1
      have hwY : (w : Ŷ) ∈ ι.range := (Subgroup.mem_subgroupOf.mp hw).2
      refine Subgroup.mem_subgroupOf.mpr ⟨?_, ?_⟩
      · change x * (w : Ŷ) * x⁻¹ ∈ T
        exact (Subgroup.mem_normalizer_iff.mp hx (w : Ŷ)).mp hwT
      · change x * (w : Ŷ) * x⁻¹ ∈ ι.range
        exact Subgroup.Normal.conj_mem inferInstance (w : Ŷ) hwY x
    · intro hz
      have hzT : (z : Ŷ) ∈ T := (Subgroup.mem_subgroupOf.mp hz).1
      refine ⟨φx.symm z, ?_, MulEquiv.apply_symm_apply φx z⟩
      refine Subgroup.mem_subgroupOf.mpr ⟨?_, (φx.symm z).2⟩
      rw [show ((φx.symm z : ↥(ι.range)) : Ŷ) = x⁻¹ * (z : Ŷ) * x by
        simp only [φx, MulEquiv.coe_toMonoidHom, MulAut.conjNormal_symm_apply]]
      change x⁻¹ * (z : Ŷ) * x ∈ T
      simpa only [inv_inv] using
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) (z : Ŷ)).mp hzT
  simpa [φx, ← hθU] using hφT0

private theorem normalizer_T_normalizes_Q {C Ŷ : Type} [Group C] [Finite C] [Group Ŷ]
    {U P₀ P₁ : Subgroup C} (S : CFSG.Quasithin.H13.Sec53F.Yam.YamStd C U P₀ P₁)
    (hswap : ∀ φ : C ≃* C, P₀.map φ.toMonoidHom ≠ P₁)
    (e : Y ≃* C) (ι : Y →* Ŷ) (hι : Function.Injective ι) (hidx : ι.range.index = 2)
    {T : Subgroup Ŷ} {θ : C ≃* ↥(ι.range)}
    (hθU : U.map θ.toMonoidHom = (T ⊓ ι.range).subgroupOf ι.range) (i : Fin 2) :
    Subgroup.normalizer (T : Set Ŷ) ≤ Subgroup.normalizer
      (((![(P₀.map θ.toMonoidHom), (P₁.map θ.toMonoidHom)] :
        Fin 2 → Subgroup ↥(ι.range)) i).map ι.range.subtype : Set Ŷ) := by
  intro x hx
  haveI : ι.range.Normal := Subgroup.normal_of_index_eq_two hidx
  let P : Fin 2 → Subgroup ↥(ι.range) := ![(P₀.map θ.toMonoidHom), (P₁.map θ.toMonoidHom)]
  let φx : ↥(ι.range) ≃* ↥(ι.range) := MulAut.conjNormal (H := ι.range) x
  have hφU : (U.map θ.toMonoidHom).map φx.toMonoidHom = U.map θ.toMonoidHom :=
    conjNormal_fixes_theta_U ι hι hidx hθU hx
  have hfix := parabolics_fixed_under_automorphism S hswap θ φx hφU
  have hQmap : (P i).map φx.toMonoidHom = P i := by
    fin_cases i
    · simpa [P] using hfix.1
    · simpa [P] using hfix.2
  have hcomp : ι.range.subtype.comp φx.toMonoidHom =
      (MulAut.conj x).toMonoidHom.comp ι.range.subtype := by
    ext z
    simp only [φx, MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
      MulAut.conjNormal_apply, MulAut.conj_apply, inv_inv]
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change ((P i).map ι.range.subtype).map (MulAut.conj x).toMonoidHom =
    (P i).map ι.range.subtype
  rw [Subgroup.map_map, ← hcomp, ← Subgroup.map_map, hQmap]

private theorem range_Q_le_M_or_M {C Ŷ : Type} [Group C] [Finite C] [Group Ŷ] [Finite Ŷ]
    {U P₀ P₁ : Subgroup C} (S : CFSG.Quasithin.H13.Sec53F.Yam.YamStd C U P₀ P₁)
    (hswap : ∀ φ : C ≃* C, P₀.map φ.toMonoidHom ≠ P₁)
    (e : Y ≃* C) (ι : Y →* Ŷ) (hι : Function.Injective ι) (hidx : ι.range.index = 2)
    {T M₁ M₂ : Subgroup Ŷ} (hY : IsYAmalgamPair T M₁ M₂) {θ : C ≃* ↥(ι.range)}
    (hθU : U.map θ.toMonoidHom = (T ⊓ ι.range).subgroupOf ι.range) (i : Fin 2) :
    (((![(P₀.map θ.toMonoidHom), (P₁.map θ.toMonoidHom)] :
        Fin 2 → Subgroup ↥(ι.range)) i).map ι.range.subtype ≤ M₁) ∨
      (((![(P₀.map θ.toMonoidHom), (P₁.map θ.toMonoidHom)] :
        Fin 2 → Subgroup ↥(ι.range)) i).map ι.range.subtype ≤ M₂) := by
  classical
  haveI : ι.range.Normal := Subgroup.normal_of_index_eq_two hidx
  let P : Fin 2 → Subgroup ↥(ι.range) :=
    ![(P₀.map θ.toMonoidHom), (P₁.map θ.toMonoidHom)]
  let Q : Subgroup ↥(ι.range) := P i
  have hQ2 : IsTwoLocal Q := by
    fin_cases i
    · simpa [Q, P] using CFSG.Quasithin.isTwoLocal_map (φ := θ) (M := P₀) S.twoLoc₀
    · simpa [Q, P] using CFSG.Quasithin.isTwoLocal_map (φ := θ) (M := P₁) S.twoLoc₁
  obtain ⟨R, hRne, hR2, hQR⟩ := hQ2
  have hRQ : R ≤ Q := hQR ▸ Subgroup.le_normalizer
  have hQN : Q ≤ Subgroup.normalizer (R : Set ↥(ι.range)) := hQR ▸ le_rfl
  have hRcore : R ≤ pCoreOf 2 Q :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (2) hRQ hQN hR2
  have hOne : pCoreOf 2 Q ≠ ⊥ := fun h => hRne (le_bot_iff.mp (h ▸ hRcore))
  let Rbar : Subgroup Ŷ := R.map ι.range.subtype
  let Qbar : Subgroup Ŷ := Q.map ι.range.subtype
  let O : Subgroup Ŷ := pCoreOf 2 Qbar
  have hRbarne : Rbar ≠ ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective R ι.range.subtype_injective).not.mpr hRne
  have hRbar2 : IsPGroup 2 Rbar := hR2.map ι.range.subtype
  have hRbarQ : Rbar ≤ Qbar := Subgroup.map_mono hRQ
  have hQbarN : Qbar ≤ Subgroup.normalizer (Rbar : Set Ŷ) :=
    (Subgroup.map_mono hQN).trans (Subgroup.le_normalizer_map ι.range.subtype)
  have hRbarO : Rbar ≤ O :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (2) hRbarQ hQbarN hRbar2
  have hOne' : O ≠ ⊥ := fun h => hRbarne (le_bot_iff.mp (h ▸ hRbarO))
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Qbar
  have hNTQ : Subgroup.normalizer (T : Set Ŷ) ≤ Subgroup.normalizer (Qbar : Set Ŷ) :=
    normalizer_T_normalizes_Q S hswap e ι hι hidx hθU i
  have hNQO : Subgroup.normalizer (Qbar : Set Ŷ) ≤ Subgroup.normalizer (O : Set Ŷ) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (2) Qbar
  have hNTO : Subgroup.normalizer (T : Set Ŷ) ≤ Subgroup.normalizer (O : Set Ŷ) :=
    hNTQ.trans hNQO
  have hQbarO : Qbar ≤ Subgroup.normalizer (O : Set Ŷ) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf (2) Qbar
  have hNloc : IsTwoLocal (Subgroup.normalizer (O : Set Ŷ)) := ⟨O, hOne', hO2, rfl⟩
  obtain ⟨M, hNOM, hmax⟩ :=
    (Set.toFinite ({M : Subgroup Ŷ | IsTwoLocal M})).exists_le_maximal hNloc
  have hMmax : IsMaximalTwoLocal M :=
    ⟨hmax.prop, fun H hH hMH => (hmax.eq_of_le hH hMH).symm⟩
  have hNTM : Subgroup.normalizer (T : Set Ŷ) ≤ M := hNTO.trans hNOM
  have hQbarM : Qbar ≤ M := hQbarO.trans hNOM
  rcases (hY.2.2 M).1 ⟨hMmax, hNTM⟩ with rfl | rfl
  · exact Or.inl (by simpa [Qbar, Q, P] using hQbarM)
  · exact Or.inr (by simpa [Qbar, Q, P] using hQbarM)

private theorem inf_range_eq_of_coatom {Ŷ : Type} [Group Ŷ] (ι : Y →* Ŷ)
    {Q : Subgroup ↥(ι.range)} (hco : IsCoatom Q) {M : Subgroup Ŷ}
    (hle : Q.map ι.range.subtype ≤ M) (hMproper : ¬ ι.range ≤ M) :
    M ⊓ ι.range = Q.map ι.range.subtype := by
  have hQN : Q ≤ (M ⊓ ι.range).subgroupOf ι.range := by
    intro q hq
    exact Subgroup.mem_subgroupOf.mpr
      ⟨hle (Subgroup.mem_map_of_mem _ hq), q.2⟩
  have hNtop : (M ⊓ ι.range).subgroupOf ι.range ≠ ⊤ := by
    intro htop
    apply hMproper
    intro y hy
    have hyN : (⟨y, hy⟩ : ↥(ι.range)) ∈ (M ⊓ ι.range).subgroupOf ι.range := by
      rw [htop]
      exact Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.mp hyN).1
  have hNQ : (M ⊓ ι.range).subgroupOf ι.range = Q := by
    rcases hco.le_iff.mp hQN with h | h
    · exact absurd h hNtop
    · exact h
  rw [← hNQ, Subgroup.map_subgroupOf_eq_of_le inf_le_right]

private theorem isCoatom_range_Q {C Ŷ : Type} [Group C] [Group Ŷ]
    {U P₀ P₁ : Subgroup C} (S : CFSG.Quasithin.H13.Sec53F.Yam.YamStd C U P₀ P₁)
    (ι : Y →* Ŷ) (θ : C ≃* ↥(ι.range)) (j : Fin 2) :
    IsCoatom (((![(P₀.map θ.toMonoidHom), (P₁.map θ.toMonoidHom)] :
      Fin 2 → Subgroup ↥(ι.range)) j)) := by
  fin_cases j
  · have h := ((MulEquiv.mapSubgroup θ).isCoatom_iff P₀).mpr S.coatom₀
    simpa using h
  · have h := ((MulEquiv.mapSubgroup θ).isCoatom_iff P₁).mpr S.coatom₁
    simpa using h

private theorem of_index_two_labelled {Ŷ : Type} [Group Ŷ] [Finite Ŷ]
    (ι : Y →* Ŷ) (hidx : ι.range.index = 2) {m : ℕ} (hm : Odd m)
    {Q₀ Q₁ M₁ M₂ : Subgroup Ŷ} (hQ : InvertsByWeyl Q₀ Q₁ m)
    (hQ₀M₁ : Q₀ ≤ M₁) (hQ₁M₂ : Q₁ ≤ M₂)
    (hM₁ : M₁ ⊓ ι.range = Q₀) (hM₂ : M₂ ⊓ ι.range = Q₁) :
    InvertsByWeyl M₁ M₂ m := by
  intro E hE hmE
  have hErange : E ≤ ι.range := fun e he =>
    mem_range_of_pow_eq_one ι hidx hm (hmE e he)
  have hEsub : E ≤ Q₀ ⊓ Q₁ := by
    intro e he
    have he₁ : e ∈ M₁ ⊓ ι.range := ⟨hE he |>.1, hErange he⟩
    have he₂ : e ∈ M₂ ⊓ ι.range := ⟨hE he |>.2, hErange he⟩
    exact Subgroup.mem_inf.mpr ⟨hM₁ ▸ he₁, hM₂ ▸ he₂⟩
  obtain ⟨H, hEH, hH, l, hl, hinv⟩ := hQ E hEsub hmE
  refine ⟨H, hEH, hH.trans (inf_le_inf hQ₀M₁ hQ₁M₂), l, ?_, hinv⟩
  intro x hx
  obtain ⟨hxmem, hxnorm⟩ := hl x hx
  refine ⟨?_, hxnorm⟩
  rcases hxmem with hx | hx
  · exact Or.inl (hQ₀M₁ hx)
  · exact Or.inr (hQ₁M₂ hx)

theorem InvertsByWeyl.of_index_two {C : Type} [Group C] [Finite C] {U P₀ P₁ : Subgroup C}
    (S : CFSG.Quasithin.H13.Sec53F.Yam.YamStd C U P₀ P₁)
    (hswap : ∀ φ : C ≃* C, P₀.map φ.toMonoidHom ≠ P₁) {m : ℕ} (hm : Odd m)
    (h : InvertsByWeyl P₀ P₁ m) {Y Ŷ : Type} [Group Y] [Group Ŷ] (e : Y ≃* C)
    (ι : Y →* Ŷ) (hι : Function.Injective ι) (hidx : ι.range.index = 2)
    {T M₁ M₂ : Subgroup Ŷ} (hY : IsYAmalgamPair T M₁ M₂) : InvertsByWeyl M₁ M₂ m := by
  classical
  haveI : Finite Ŷ := finite_of_index_two e ι hι hidx
  obtain ⟨θ, hθU, -⟩ := exists_theta_of_index_two S e ι hι hidx hY.1
  let P : Fin 2 → Subgroup ↥(ι.range) :=
    ![(P₀.map θ.toMonoidHom), (P₁.map θ.toMonoidHom)]
  let Q : Fin 2 → Subgroup Ŷ := fun i => (P i).map ι.range.subtype
  have hco0 : IsCoatom (P 0) := by simpa [P] using isCoatom_range_Q S ι θ 0
  have hco1 : IsCoatom (P 1) := by simpa [P] using isCoatom_range_Q S ι θ 1
  have hQbaseY : InvertsByWeyl (P 0) (P 1) m := by
    simpa [P] using InvertsByWeyl.map θ h
  have hQbase : InvertsByWeyl (Q 0) (Q 1) m := by
    have := InvertsByWeyl.map_injective ι.range.subtype ι.range.subtype_injective hQbaseY
    simpa [Q] using this
  have hQ01 : Q 0 ≠ Q 1 := by
    intro hq
    have hP : P 0 = P 1 := Subgroup.map_injective ι.range.subtype_injective hq
    exact S.ne (Subgroup.map_injective θ.injective (by simpa [P] using hP))
  have hM1max : IsMaximalTwoLocal M₁ := ((hY.2.2 M₁).2 (Or.inl rfl)).1
  have hM2max : IsMaximalTwoLocal M₂ := ((hY.2.2 M₂).2 (Or.inr rfl)).1
  have hNT1 : Subgroup.normalizer (T : Set Ŷ) ≤ M₁ :=
    ((hY.2.2 M₁).2 (Or.inl rfl)).2
  have hNT2 : Subgroup.normalizer (T : Set Ŷ) ≤ M₂ :=
    ((hY.2.2 M₂).2 (Or.inr rfl)).2
  have hproper1 : ¬ ι.range ≤ M₁ := not_range_le_maxTwoLocal S e ι hι hidx hY hM1max hNT1
  have hproper2 : ¬ ι.range ≤ M₂ := not_range_le_maxTwoLocal S e ι hι hidx hY hM2max hNT2
  have hle0 : Q 0 ≤ M₁ ∨ Q 0 ≤ M₂ := by
    simpa [Q, P] using range_Q_le_M_or_M S hswap e ι hι hidx hY hθU 0
  have hle1 : Q 1 ≤ M₁ ∨ Q 1 ≤ M₂ := by
    simpa [Q, P] using range_Q_le_M_or_M S hswap e ι hι hidx hY hθU 1
  rcases hle0 with h0 | h0 <;> rcases hle1 with h1 | h1
  · exfalso
    have h01 : M₁ ⊓ ι.range = Q 0 := inf_range_eq_of_coatom ι hco0 h0 hproper1
    have h11 : M₁ ⊓ ι.range = Q 1 := inf_range_eq_of_coatom ι hco1 h1 hproper1
    exact hQ01 (h01.symm.trans h11)
  · refine of_index_two_labelled ι hidx hm hQbase h0 h1 ?_ ?_
    · exact inf_range_eq_of_coatom ι hco0 h0 hproper1
    · exact inf_range_eq_of_coatom ι hco1 h1 hproper2
  · refine of_index_two_labelled ι hidx hm hQbase.swap h1 h0 ?_ ?_
    · exact inf_range_eq_of_coatom ι hco1 h1 hproper1
    · exact inf_range_eq_of_coatom ι hco0 h0 hproper2
  · exfalso
    have h02 : M₂ ⊓ ι.range = Q 0 := inf_range_eq_of_coatom ι hco0 h0 hproper2
    have h12 : M₂ ⊓ ι.range = Q 1 := inf_range_eq_of_coatom ι hco1 h1 hproper2
    exact hQ01 (h02.symm.trans h12)

module

public import CFSG.Quasithin.Vol2.Ch9Sec4Gv
public import CFSG.Quasithin.Vol2.Ch9Sec4Xi
public import CFSG.Quasithin.EmptyFaithful.S152He9W

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H Matrix
open scoped commutatorElement

namespace Om4Pt

variable {K : Type} [Field K]

theorem detPolar_add_right (X Y Y' : Matrix (Fin 2) (Fin 2) K) :
    detPolarCh6 X (Y + Y') = detPolarCh6 X Y + detPolarCh6 X Y' := by
  simp only [detPolarCh6, Matrix.add_apply]
  ring

theorem detPolar_sub_right (X Y Y' : Matrix (Fin 2) (Fin 2) K) :
    detPolarCh6 X (Y - Y') = detPolarCh6 X Y - detPolarCh6 X Y' := by
  simp only [detPolarCh6, Matrix.sub_apply]
  ring

theorem detPolar_smul_right (X Y : Matrix (Fin 2) (Fin 2) K) (c : K) :
    detPolarCh6 X (c • Y) = c * detPolarCh6 X Y := by
  simp only [detPolarCh6, Matrix.smul_apply, smul_eq_mul]
  ring

theorem eq_smul_of_detPolar {X₀ X₁ : Matrix (Fin 2) (Fin 2) K} {c : K}
    (h : ∀ Y, detPolarCh6 X₁ Y = c * detPolarCh6 X₀ Y) : X₁ = c • X₀ := by
  have h00 := h !![0, 0; 0, 1]
  have h11 := h !![1, 0; 0, 0]
  have h01 := h !![0, 0; 1, 0]
  have h10 := h !![0, 1; 0, 0]
  simp [detPolarCh6] at h00 h11 h01 h10
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h11, h01, h10]

theorem exists_perp_add {X₀ X₁ : Matrix (Fin 2) (Fin 2) K} (hX₀ : X₀ ≠ 0)
    (hne : ∀ c : K, X₁ ≠ c • X₀) (Y : Matrix (Fin 2) (Fin 2) K) :
    ∃ Y₀ Y₁ : Matrix (Fin 2) (Fin 2) K, Y = Y₀ + Y₁ ∧ detPolarCh6 X₀ Y₀ = 0 ∧
      detPolarCh6 X₁ Y₁ = 0 := by
  obtain ⟨E₀, hE₀⟩ : ∃ E₀, detPolarCh6 X₀ E₀ = 1 := by
    by_contra hall
    push Not at hall
    apply hX₀
    have h0 : ∀ Y, detPolarCh6 X₀ Y = 0 * detPolarCh6 X₀ Y := by
      intro Y
      by_contra hY
      rw [zero_mul] at hY
      apply hall ((detPolarCh6 X₀ Y)⁻¹ • Y)
      rw [detPolar_smul_right, inv_mul_cancel₀ hY]
    have := eq_smul_of_detPolar h0
    rwa [zero_smul] at this
  obtain ⟨E, hE0, hE1⟩ : ∃ E, detPolarCh6 X₀ E = 0 ∧ detPolarCh6 X₁ E = 1 := by
    by_contra hall
    push Not at hall
    apply hne (detPolarCh6 X₁ E₀)
    apply eq_smul_of_detPolar
    intro Y
    set Y' := Y - detPolarCh6 X₀ Y • E₀ with hY'
    have h1 : detPolarCh6 X₀ Y' = 0 := by
      rw [hY', detPolar_sub_right, detPolar_smul_right, hE₀, mul_one, sub_self]
    have h2 : detPolarCh6 X₁ Y' = 0 := by
      by_contra h2
      apply hall ((detPolarCh6 X₁ Y')⁻¹ • Y') (by rw [detPolar_smul_right, h1, mul_zero])
      rw [detPolar_smul_right, inv_mul_cancel₀ h2]
    rw [hY', detPolar_sub_right, detPolar_smul_right, sub_eq_zero] at h2
    rw [h2, mul_comm]
  refine ⟨detPolarCh6 X₁ Y • E, Y - detPolarCh6 X₁ Y • E, by abel, ?_, ?_⟩
  · rw [detPolar_smul_right, hE0, mul_zero]
  · rw [detPolar_sub_right, detPolar_smul_right, hE1, mul_one, sub_self]

end Om4Pt

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem inV_perp_sup_eq {K : Type} [Field K] (e : ↥(fsuV T I) ≃* Om4.VM K)
    {X₀ X₁ : Matrix (Fin 2) (Fin 2) K} (hX₀ : X₀ ≠ 0) (hne : ∀ c : K, X₁ ≠ c • X₀) :
    inV e (Om4Pt.perpM X₀) ⊔ inV e (Om4Pt.perpM X₁) = fsuV T I := by
  refine le_antisymm (sup_le (inV_le e _) (inV_le e _)) fun x hx => ?_
  obtain ⟨Y₀, Y₁, hY, h0, h1⟩ :=
    Om4Pt.exists_perp_add hX₀ hne (Multiplicative.toAdd (e ⟨x, hx⟩))
  have hx' : (⟨x, hx⟩ : ↥(fsuV T I)) =
      e.symm (Multiplicative.ofAdd Y₀) * e.symm (Multiplicative.ofAdd Y₁) := by
    apply e.injective
    rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, ← ofAdd_add, ← hY,
      ofAdd_toAdd]
  have e1 : x = ((e.symm (Multiplicative.ofAdd Y₀) : ↥(fsuV T I)) : G) *
      ((e.symm (Multiplicative.ofAdd Y₁) : ↥(fsuV T I)) : G) := by
    have := congrArg Subtype.val hx'
    simpa using this
  rw [e1]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right ?_)
  · refine mem_inV.mpr ⟨(e.symm _).2, ?_⟩
    show e (e.symm (Multiplicative.ofAdd Y₀)) ∈ Om4Pt.perpM X₀
    rw [MulEquiv.apply_symm_apply]
    exact h0
  · refine mem_inV.mpr ⟨(e.symm _).2, ?_⟩
    show e (e.symm (Multiplicative.ofAdd Y₁)) ∈ Om4Pt.perpM X₁
    rw [MulEquiv.apply_symm_apply]
    exact h1

omit [Finite G] in
theorem map_conj_map_conj (X : Subgroup G) (g a : G) :
    (X.map (MulAut.conj g).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      (X.map (MulAut.conj (g⁻¹ * a * g)).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

omit [Finite G] in
theorem mem_normalizer_map_conj {X : Subgroup G} {g y : G}
    (h : g⁻¹ * y * g ∈ Subgroup.normalizer (X : Set G)) :
    y ∈ Subgroup.normalizer ((X.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  have h1 := Ch1Sec3.map_conj_eq_of_mem_normalizer h
  have h2 := Ch1Sec3.map_conj_eq_of_mem_normalizer (Subgroup.inv_mem _ h)
  refine Ch1Sec3.mem_normalizer_of_map_conj_le (le_of_eq ?_) (le_of_eq ?_)
  · rw [map_conj_map_conj, h1]
  · rw [map_conj_map_conj]
    have e : g⁻¹ * y⁻¹ * g = (g⁻¹ * y * g)⁻¹ := by group
    rw [e, h2]

theorem commutatorElement_mul_center {Q : Type*} [Group Q] {a b z₁ z₂ : Q}
    (h₁ : z₁ ∈ Subgroup.center Q) (h₂ : z₂ ∈ Subgroup.center Q) : ⁅z₁ * a, z₂ * b⁆ = ⁅a, b⁆ := by
  have c₁ := Subgroup.mem_center_iff.mp h₁
  have c₂ := Subgroup.mem_center_iff.mp h₂
  rw [commutatorElement_def, commutatorElement_def, ← c₁ a, ← c₂ b, _root_.mul_inv_rev,
    _root_.mul_inv_rev]
  have e3 : z₁ * (b * z₂) = (b * z₂) * z₁ := (c₁ _).symm
  calc a * z₁ * (b * z₂) * (z₁⁻¹ * a⁻¹) * (z₂⁻¹ * b⁻¹)
      = a * (z₁ * (b * z₂)) * z₁⁻¹ * a⁻¹ * (z₂⁻¹ * b⁻¹) := by group
    _ = a * ((b * z₂) * z₁) * z₁⁻¹ * a⁻¹ * (z₂⁻¹ * b⁻¹) := by rw [e3]
    _ = a * b * (z₂ * a⁻¹) * z₂⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * z₂) * z₂⁻¹ * b⁻¹ := by rw [c₂ a⁻¹]
    _ = a * b * a⁻¹ * b⁻¹ := by group

omit [Finite G] in
theorem normalizer_le_normalizer_centralizer (U : Subgroup G) :
    Subgroup.normalizer (U : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (U : Set G) : Set G) := by
  intro h hh
  have key : ∀ g ∈ Subgroup.normalizer (U : Set G), ∀ c ∈ Subgroup.centralizer (U : Set G),
      g * c * g⁻¹ ∈ Subgroup.centralizer (U : Set G) := by
    intro g hg c hc'
    rw [Subgroup.mem_centralizer_iff] at hc' ⊢
    intro u hu
    have hu' : g⁻¹ * u * g⁻¹⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp
      (Subgroup.inv_mem _ hg) u).mp hu
    have h1 := hc' _ hu'
    calc u * (g * c * g⁻¹) = g * ((g⁻¹ * u * g⁻¹⁻¹) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * u * g⁻¹⁻¹)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * u := by group
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨key h hh c, fun hc' => ?_⟩
  have := key h⁻¹ (Subgroup.inv_mem _ hh) _ hc'
  simpa [mul_assoc] using this

namespace Setup

namespace IsCoord

variable {S : Setup T L I n} {K : Type} [Field K] [Fintype K] [CharP K 2]
  {e : ↥(fsuV T I) ≃* Om4.VM K}
  {ψ : ↥(fsuL0 T L) →* SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K}
  (hc : S.IsCoord e ψ)
include hc

variable {X₀ : Matrix (Fin 2) (Fin 2) K}

theorem conj_inv_mem_perp (g : ↥(fsuL0 T L)) {y : G}
    (hy : y ∈ inV e (Om4Pt.perpM (Multiplicative.toAdd
      (Om4.rho (ψ g) (Multiplicative.ofAdd X₀))))) :
    (g : G)⁻¹ * y * (g : G) ∈ inV e (Om4Pt.perpM X₀) := by
  obtain ⟨hyV, hyp⟩ := mem_inV.mp hy
  have hgN : (g : G)⁻¹ ∈ Subgroup.normalizer (fsuV T I : Set G) :=
    Subgroup.inv_mem _ (S.L0_le_normalizer_V g.2)
  have hg' : (g : G)⁻¹ * y * (g : G) ∈ fsuV T I := by
    have := (Subgroup.mem_normalizer_iff.mp hgN y).mp hyV
    simpa using this
  refine mem_inV.mpr ⟨hg', ?_⟩
  have h' : (g : G) * ((g : G)⁻¹ * y * (g : G)) * (g : G)⁻¹ ∈ fsuV T I := by
    simpa [mul_assoc] using hyV
  have key : Multiplicative.toAdd (e ⟨y, hyV⟩) =
      ((ψ g).1 : Matrix (Fin 2) (Fin 2) K) * Multiplicative.toAdd (e ⟨_, hg'⟩) *
        ((ψ g).2 : Matrix (Fin 2) (Fin 2) K)ᵀ := by
    rw [← toAdd_rho, ← hc.e_conj g ⟨_, hg'⟩ h']
    congr 2
    exact Subtype.ext (by group)
  rw [Om4Pt.mem_perpM] at hyp ⊢
  rw [toAdd_rho, toAdd_ofAdd, key, detPolar_rho] at hyp
  exact hyp

theorem isPGroup_of_solvable (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (hK4 : Fintype.card K = 4) (hX : X₀.det ≠ 0)
    {R : Subgroup G} (hRL : R ≤ lPt T L (inV e (Om4Pt.lineM X₀)))
    (hRn : lPt T L (inV e (Om4Pt.lineM X₀)) ≤ Subgroup.normalizer (R : Set G))
    (hRs : Group.IsSolvable ↥R) : IsPGroup 2 ↥R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set LW := lPt T L (inV e (Om4Pt.lineM X₀)) with hLW
  obtain ⟨⟨e5⟩, -⟩ := hc.lPt_quot h37c h38c hK4 hX
  set N := CFSG.pCore 2 ↥LW with hN
  set π : ↥LW →* alternatingGroup (Fin 5) := e5.toMonoidHom.comp (QuotientGroup.mk' N) with hπ
  have hπs : Function.Surjective π :=
    e5.surjective.comp (QuotientGroup.mk'_surjective N)
  have hπk : π.ker = N := by
    ext x
    rw [MonoidHom.mem_ker, hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ e5.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  set R' := R.subgroupOf LW with hR'
  have hR'n : R'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hRL).mpr hRn
  have hR's : Group.IsSolvable ↥R' :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hRL).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hRL).injective
  have himg : (R'.map π).Normal := hR'n.map π hπs
  have hNs : Group.IsSolvable ↥N := by
    have := (CFSG.pCore_isPGroup (p := 2) (G := ↥LW)).isNilpotent
    infer_instance
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (R'.map π) with h | h
  ·
    have hle : R' ≤ N := by
      rw [← hπk]
      exact (Subgroup.map_eq_bot_iff R').mp h
    have hR'p : IsPGroup 2 ↥R' := (CFSG.pCore_isPGroup (p := 2) (G := ↥LW)).to_le hle
    exact hR'p.of_equiv (Subgroup.subgroupOfEquivOfLe hRL)
  ·
    exfalso
    have hs : Group.IsSolvable ↥((R'.map π).comap π) :=
      Xi.isSolvable_comap π (by rw [hπk]; exact hNs) (Group.isSolvable_of_surjective
        (f := π.subgroupMap R') (π.subgroupMap_surjective R'))
    rw [h, Subgroup.comap_top] at hs
    have hLWs : Group.IsSolvable ↥LW :=
      Group.isSolvable_of_surjective (f := (Subgroup.topEquiv (G := ↥LW)).toMonoidHom)
        (Subgroup.topEquiv (G := ↥LW)).surjective
    exact not_isSolvable_of_mem_cComp (hc.mem_cComp_lPt h37c h38c hK4 hX) hLWs

theorem exists_mem_perp_omegaOneCenter
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat)
    (hK4 : Fintype.card K = 4) (hX : X₀.det ≠ 0) {v : G}
    (hv : v ∈ inV e (Om4Pt.lineM X₀)) (hv1 : v ≠ 1)
    (hsyl : IsSylowTwoOf (T ⊓ Subgroup.centralizer ({v} : Set G))
      (fsuM T L ⊓ Subgroup.centralizer ({v} : Set G))) :
    ∃ z ∈ fsuV T I, z ∈ quasithinOmegaOneCenter T ∧ z ≠ 1 ∧ z ∈ inV e (Om4Pt.perpM X₀) ∧
      ∀ hz : z ∈ fsuV T I, (Multiplicative.toAdd (e ⟨z, hz⟩)).det = 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfsu := S.hyp.fsu
  obtain ⟨⟨z, hzV, hzZ⟩, hz1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Vol2.Ch11.SecS.inf_omegaOneCenter_ne_bot' hfsu.sylow.1 S.hV S.fsuV_le_T S.T_le_normalizer_V
      S.fsuV_ne_bot)
  have hz1 : z ≠ 1 := fun h => hz1' (Subtype.ext h)
  have hzTC := E3.omegaOneCenter_le_inf_centralizer T hzZ
  obtain ⟨u, huL0, huTv, huLW, hψu1, hψu2⟩ := hc.exists_mem_inf_lPt h37c h38c hK4 hX hv hv1 hsyl
  have hψu : ψ ⟨u, huL0⟩ ∈ Om4Pt.dgM X₀ := by
    rw [← hc.map_lPt hK4 hX]
    exact ⟨⟨u, huL0⟩, Subgroup.mem_subgroupOf.mpr huLW, rfl⟩
  have hzWp : z ∈ inV e (Om4Pt.perpM X₀) :=
    hc.mem_perp_of_fix hX ⟨u, huL0⟩ hψu hψu1 hψu2 hzV (by
      have := Subgroup.mem_centralizer_iff.mp hzTC.2 u huTv.1
      show u * z * u⁻¹ = z
      rw [this, mul_inv_cancel_right])
  have hzV1 : z ∈ fsuV T I ⊓ Subgroup.centralizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G) :=
    ⟨hzV, Subgroup.centralizer_le inf_le_left hzTC.2⟩
  refine ⟨z, hzV, hzZ, hz1, hzWp, fun hz => ?_⟩
  rw [hc.toAdd_e_eq hzV1, Matrix.det_smul]
  simp [Matrix.det_fin_two_of]

theorem prop941_false (h36 : A36ForSQTK) (h312 : A312ForSQTK)
    (h314 : A314Facts) (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat)
    (h3104 : Stmt3_2_10_four) (h3108 : Stmt3_2_10_eight) (hFa : A314QuasiRankFact)
    (hFb : A314FFCohomFact) (h2 : n = 2) (hX : X₀.det ≠ 0) {v : G}
    (hv : v ∈ inV e (Om4Pt.lineM X₀)) (hv1 : v ≠ 1)
    (hsyl : IsSylowTwoOf (T ⊓ Subgroup.centralizer ({v} : Set G))
      (fsuM T L ⊓ Subgroup.centralizer ({v} : Set G)))
    {Lv : Subgroup G} (hLv : Lv ∈ cComp (Subgroup.centralizer ({v} : Set G)))
    (hlt : lPt T L (inV e (Om4Pt.lineM X₀)) < Lv)
    (hGvLv : Subgroup.centralizer ({v} : Set G) ≤ Subgroup.normalizer (Lv : Set G)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfsu := S.hyp.fsu
  have hK4 : Fintype.card K = 4 := by rw [hc.card, h2]; norm_num
  set W := inV e (Om4Pt.lineM X₀) with hW
  set Wp := inV e (Om4Pt.perpM X₀) with hWp
  set LW := lPt T L W with hLW
  set Gv := Subgroup.centralizer ({v} : Set G) with hGv
  set Tv := T ⊓ Gv with hTv
  set H := Lv ⊔ Tv with hH
  set Z := quasithinOmegaOneCenter T with hZ
  set U := conjClosure Z H with hU
  obtain ⟨hLvM, -, hchar, hWpU⟩ := hc.prop941_setup h36 h312 h314 h37c h38c h3104 hFa h2 hX hv
    hv1 hsyl hLv hlt hGvLv
  have hLvU := hc.prop941_aut h37c h38c h3104 h3108 hFb h2 hX hv hv1 hsyl hLv hlt hGvLv hchar hWpU
  have hvV : v ∈ fsuV T I := inV_le e _ hv
  have hv2 : v ^ 2 = 1 := S.hV.2 v hvV
  have hTvG : IsSylowTwoOf Tv Gv := S.isSylowTwoOf_centralizer h3104 hvV hv1 hsyl
  have hLvG : Lv ≤ Gv := le_of_mem_cComp hLv
  have hHG : H ≤ Gv := sup_le hLvG inf_le_right
  have hvGv : v ∈ Gv := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hOGv : pCoreOf 2 Gv ≠ ⊥ := fun h => hv1 (by
    have := mem_pCoreOf_of_le_centralizer hv2 hv1 hvGv le_rfl
    rwa [h, Subgroup.mem_bot] at this)
  have hsqtk : SQTKGroup ↥Gv :=
    sqtkGroup_of_pCoreOf_ne_bot hfsu.qtke hfsu.simple hfsu.nonabelian hOGv
  have hLWLv : LW ≤ Lv := hlt.le
  have hLWc : LW ∈ cComp LW := hc.mem_cComp_lPt h37c h38c hK4 hX
  have hnormLW : fsuM T L ⊓ Gv ≤ Subgroup.normalizer (LW : Set G) := fun x hx =>
    hc.mem_normalizer_lPt hx.1 hv hv1 (by
      have := Subgroup.mem_centralizer_singleton_iff.mp hx.2
      rw [this, mul_inv_cancel_right])
  have hLWM : LW ≤ fsuM T L := (lPt_le_L0 T L W).trans Setup.L0_le_fsuM
  have hHU : H ≤ Subgroup.normalizer (U : Set G) := le_normalizer_conjClosure Z H
  set Nsol := Lv ⊓ Subgroup.centralizer (U : Set G) with hNsol
  have hNLv : Nsol ≤ Lv := inf_le_left
  have hLvN : Lv ≤ Subgroup.normalizer (Nsol : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx,
      normalizer_le_normalizer_centralizer U (hHU (Subgroup.mem_sup_left hx))⟩
  have hNsub : IsSubnormal Nsol Lv := A4.subnormal_of_normal hNLv
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hNLv).mpr hLvN)
  have hWpU' : Wp ≤ U := hWpU
  have hvWp : v ∈ Wp := inV_line_le_perp (e := e) hv
  have hNne : Nsol ≠ Lv := by
    intro h
    have hLWC : LW ≤ Subgroup.centralizer (Wp : Set G) := fun l hl => by
      have hlN : l ∈ Nsol := h ▸ hLWLv hl
      exact Subgroup.centralizer_le hWpU' hlN.2
    have h1 := hc.perp_le_commutator hK4 hX
    have h3 : ⁅Wp, LW⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro w hw
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      exact (Subgroup.mem_centralizer_iff.mp (hLWC hl) w hw).symm
    exact hv1 (by have := h1 hvWp; rwa [h3, Subgroup.mem_bot] at this)
  have hNsolv : Nsol ≤ solvRad Lv :=
    le_solvRad_of_subnormal_lt hLv hNsub (lt_of_le_of_ne hNLv hNne)
  have hLvU' : Lv ≤ Nsol ⊔ LW := by rw [sup_comm]; exact hLvU
  have hLWN : LW ≤ Subgroup.normalizer (Nsol : Set G) := hLWLv.trans hLvN
  have hO2M : pCoreOf 2 Lv ≤ fsuM T L := by
    have hTvH : IsSylowTwoOf Tv H := A4.isSylowTwoOf_mono hTvG le_sup_right hHG
    have h1 : pCoreOf 2 Lv ≤ pCoreOf 2 H :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 Lv).trans le_sup_left)
        ((hHG.trans hGvLv).trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Lv))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Lv)
    exact (h1.trans (pCoreOf_le_of_isSylowIn hTvH)).trans (inf_le_left.trans Setup.T_le_fsuM)
  by_cases hq : CFSG.IsQuasisimple (↥Lv ⧸ CFSG.pCore 2 ↥Lv)
  ·
    apply hLvM
    set π := QuotientGroup.mk' (CFSG.pCore 2 ↥Lv) with hπ
    have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
    have hNn : (Nsol.subgroupOf Lv).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNLv).mpr hLvN
    have hN'n : ((Nsol.subgroupOf Lv).map π).Normal := hNn.map π hπs
    have hdec : ∀ x : ↥Lv, ∃ c l : ↥Lv, (c : G) ∈ Nsol ∧ (l : G) ∈ LW ∧ x = c * l := by
      intro x
      obtain ⟨c, hc', l, hl, hx⟩ := (Ch1Sec3.mem_sup_iff_of_le_normalizer hLWN).mp (hLvU' x.2)
      exact ⟨⟨c, hNLv hc'⟩, ⟨l, hLWLv hl⟩, hc', hl, Subtype.ext hx⟩
    have hker : ∀ a b : ↥Lv, π a = π b → ((a⁻¹ * b : ↥Lv) : G) ∈ pCoreOf 2 Lv := by
      intro a b hab
      have h1 : a⁻¹ * b ∈ CFSG.pCore 2 ↥Lv := (QuotientGroup.eq).mp hab
      rw [pCoreOf]
      exact Subgroup.mem_map_of_mem Lv.subtype h1
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hN'n with htop | hcen
    · exfalso
      have hO2R : pCoreOf 2 Lv ≤ solvRad Lv := by
        refine le_solvRad_of_subnormal (A4.subnormal_of_normal
          (CFSG.LieType.BorelTits.pCoreOf_le 2 Lv) ((Subgroup.normal_subgroupOf_iff_le_normalizer
            (CFSG.LieType.BorelTits.pCoreOf_le 2 Lv)).mpr
            (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Lv))) ?_
        have := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Lv).isNilpotent
        infer_instance
      have hle : Lv ≤ solvRad Lv := by
        intro x hx
        obtain ⟨c, hcN, hce⟩ : π ⟨x, hx⟩ ∈ (Nsol.subgroupOf Lv).map π :=
          htop ▸ Subgroup.mem_top _
        have h1 := hker c ⟨x, hx⟩ hce
        have e1 : x = (c : G) * ((c⁻¹ * ⟨x, hx⟩ : ↥Lv) : G) := by simp
        rw [e1]
        exact (solvRad Lv).mul_mem (hNsolv (Subgroup.mem_subgroupOf.mp hcN)) (hO2R h1)
      exact not_isSolvable_of_mem_cComp hLv
        ((solvRad_eq_self_iff Lv).mp (le_antisymm (solvRad_le Lv) hle))
    · have hA : (LW.subgroupOf Lv).map π = ⊤ := by
        rw [eq_top_iff, ← hq.1.commutator_eq_top, commutator_def, Subgroup.commutator_le]
        intro a _ b _
        obtain ⟨x, rfl⟩ := hπs a
        obtain ⟨y, rfl⟩ := hπs b
        obtain ⟨c, l, hcN, hlW, rfl⟩ := hdec x
        obtain ⟨c', l', hcN', hlW', rfl⟩ := hdec y
        rw [map_mul, map_mul, commutatorElement_mul_center
          (hcen ⟨c, Subgroup.mem_subgroupOf.mpr hcN, rfl⟩)
          (hcen ⟨c', Subgroup.mem_subgroupOf.mpr hcN', rfl⟩), commutatorElement_def]
        have hl : π l ∈ (LW.subgroupOf Lv).map π := ⟨l, Subgroup.mem_subgroupOf.mpr hlW, rfl⟩
        have hl' : π l' ∈ (LW.subgroupOf Lv).map π := ⟨l', Subgroup.mem_subgroupOf.mpr hlW', rfl⟩
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hl hl')
          (Subgroup.inv_mem _ hl)) (Subgroup.inv_mem _ hl')
      intro x hx
      obtain ⟨l, hl, hle⟩ : π ⟨x, hx⟩ ∈ (LW.subgroupOf Lv).map π := hA ▸ Subgroup.mem_top _
      have h1 := hker l ⟨x, hx⟩ hle
      have e1 : x = (l : G) * ((l⁻¹ * ⟨x, hx⟩ : ↥Lv) : G) := by simp
      rw [e1]
      exact (fsuM T L).mul_mem (hLWM (Subgroup.mem_subgroupOf.mp hl)) (hO2M h1)
  ·
    obtain ⟨X, hXi, hXLv, hNX, hXs, hXK⟩ := exists_isXi_of_cComp hsqtk.1 hTvG hLv hGvLv hOGv hq
    have hGvX : Gv ≤ Subgroup.normalizer (X : Set G) := hGvLv.trans hNX
    have hLvX : Lv ≤ Subgroup.normalizer (X : Set G) := hLvG.trans hGvX
    have hXR : X ≤ solvRad Lv := le_solvRad_of_subnormal (A4.subnormal_of_normal hXLv
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hXLv).mpr hLvX)) hXs
    have hRn : LW ≤ Subgroup.normalizer ((LW ⊓ solvRad Lv : Subgroup G) : Set G) := fun l hl =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hl,
        (Subgroup.normal_subgroupOf_iff_le_normalizer (solvRad_le Lv)).mp (solvRad_normal Lv)
          (hLWLv hl)⟩
    have hRs : Group.IsSolvable ↥(LW ⊓ solvRad Lv) := by
      have := solvRad_isSolvable Lv
      exact Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion (inf_le_right : LW ⊓ solvRad Lv ≤ solvRad Lv))
        (Subgroup.inclusion_injective _)
    have hRp := hc.isPGroup_of_solvable h37c h38c hK4 hX inf_le_left hRn hRs
    have hXN : X ≤ Nsol := by
      calc X = oTwoUpper X := hXi.1
        _ ≤ Nsol := oTwoUpper_le_of_pow_mem fun x hx => by
          obtain ⟨c, hcN, l, hl, rfl⟩ :=
            (Ch1Sec3.mem_sup_iff_of_le_normalizer hLWN).mp (hLvU' (hXLv hx))
          have hlR : l ∈ solvRad Lv := by
            have := (solvRad Lv).mul_mem ((solvRad Lv).inv_mem (hNsolv hcN)) (hXR hx)
            simpa using this
          obtain ⟨k, hk⟩ := hRp ⟨l, hl, hlR⟩
          have hk' : l ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
          refine ⟨k, ?_⟩
          have := Xi.mul_pow_mul_inv_mem hcN (hLWN hl) (2 ^ k)
          rwa [hk', inv_one, mul_one] at this
    have hXU : X ≤ Subgroup.centralizer (U : Set G) := hXN.trans inf_le_right
    obtain ⟨z, hzV, hzZ, hz1, hzWp, hzd⟩ :=
      hc.exists_mem_perp_omegaOneCenter h37c h38c hK4 hX hv hv1 hsyl
    have hzTC := E3.omegaOneCenter_le_inf_centralizer T hzZ
    obtain ⟨hvV', c, hcv⟩ := mem_inV.mp hv
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hv1
      have h1 : e ⟨v, hvV'⟩ = 1 := by
        rw [← ofAdd_toAdd (e _), hcv, zero_smul, ofAdd_zero]
      exact congrArg Subtype.val ((map_eq_one_iff e e.injective).mp h1)
    have hvdef : v = ((e.symm (Multiplicative.ofAdd (c • X₀)) : ↥(fsuV T I)) : G) := by
      have : (⟨v, hvV'⟩ : ↥(fsuV T I)) = e.symm (Multiplicative.ofAdd (c • X₀)) := by
        apply e.injective
        rw [MulEquiv.apply_symm_apply, ← hcv, ofAdd_toAdd]
      exact congrArg Subtype.val this
    have hzp : detPolarCh6 X₀ (Multiplicative.toAdd (e ⟨z, hzV⟩)) = 0 := by
      obtain ⟨hzV', hzp'⟩ := mem_inV.mp hzWp
      exact hzp'
    obtain ⟨g, hgL0, hg1, hg2, -⟩ := hc.exists_mul_mem_L0 hX hc0 hzV hzp (hzd hzV)
    rw [← hvdef] at hg1 hg2
    set X' := X.map (MulAut.conj g).toMonoidHom with hX'
    have hvzU : v * z ∈ U := U.mul_mem (hWpU' hvWp) (by
      have := mem_conjClosure (Subgroup.one_mem H) hzZ
      simpa using this)
    have hXvz : ∀ x ∈ X, x * (v * z) = (v * z) * x := fun x hx =>
      (Subgroup.mem_centralizer_iff.mp (hXU hx) (v * z) hvzU).symm
    have hconj : ∀ y : G, y * (v * z) = (v * z) * y → g⁻¹ * y * g ∈ Gv := by
      intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g⁻¹ * y * g * v = g⁻¹ * (y * (g * v * g⁻¹)) * g := by group
        _ = g⁻¹ * (y * (v * z)) * g := by rw [hg1]
        _ = g⁻¹ * ((v * z) * y) * g := by rw [hy]
        _ = g⁻¹ * (g * v * g⁻¹) * y * g := by rw [hg1]; group
        _ = v * (g⁻¹ * y * g) := by group
    have hX'Gv : X' ≤ Gv := by
      rintro _ ⟨x, hx, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      show g * x * g⁻¹ * v = v * (g * x * g⁻¹)
      calc g * x * g⁻¹ * v = g * (x * (g⁻¹ * v * g)) * g⁻¹ := by group
        _ = g * (x * (v * z)) * g⁻¹ := by rw [hg2]
        _ = g * ((v * z) * x) * g⁻¹ := by rw [hXvz x hx]
        _ = g * (g⁻¹ * v * g) * x * g⁻¹ := by rw [hg2]; group
        _ = v * (g * x * g⁻¹) := by group
    have hXX' : X ≤ Subgroup.normalizer (X' : Set G) := fun x hx =>
      mem_normalizer_map_conj (hGvX (hconj x (hXvz x hx)))
    have hTX' : Tv ≤ Subgroup.normalizer (X' : Set G) := fun t ht => by
      refine mem_normalizer_map_conj (hGvX (hconj t ?_))
      have htv : t * v = v * t := Subgroup.mem_centralizer_singleton_iff.mp ht.2
      have htz : t * z = z * t := Subgroup.mem_centralizer_iff.mp hzTC.2 t ht.1
      calc t * (v * z) = (t * v) * z := by group
        _ = (v * t) * z := by rw [htv]
        _ = v * (t * z) := by group
        _ = v * (z * t) := by rw [htz]
        _ = (v * z) * t := by group
    have hX'X : X' ≤ Subgroup.normalizer (X : Set G) := hX'Gv.trans hGvX
    have hD : X ⊔ X' ≤ Gv := sup_le (hXLv.trans hLvG) hX'Gv
    have hXeq : X' = X := hXi.map_conj_eq g hXX' hX'X hTX' hD hsqtk.1
    set g' : ↥(fsuL0 T L) := ⟨g, hgL0⟩ with hg'
    set X₁ := Multiplicative.toAdd (Om4.rho (ψ g') (Multiplicative.ofAdd X₀)) with hX₁
    have hX₀0 : X₀ ≠ 0 := fun h => hX (by rw [h]; simp)
    have hvzV : v * z ∈ fsuV T I := (fsuV T I).mul_mem hvV hzV
    have hX₁eq : c • X₁ = c • X₀ + Multiplicative.toAdd (e ⟨z, hzV⟩) := by
      have h1 : (g' : G) * ((⟨v, hvV⟩ : ↥(fsuV T I)) : G) * (g' : G)⁻¹ ∈ fsuV T I := by
        show g * v * g⁻¹ ∈ fsuV T I
        rw [hg1]
        exact hvzV
      have h2 := hc.e_conj g' ⟨v, hvV⟩ h1
      have h3 : (⟨(g' : G) * ((⟨v, hvV⟩ : ↥(fsuV T I)) : G) * (g' : G)⁻¹, h1⟩ : ↥(fsuV T I)) =
          ⟨v, hvV⟩ * ⟨z, hzV⟩ := Subtype.ext hg1
      rw [h3, map_mul] at h2
      have h4 := congrArg Multiplicative.toAdd h2
      rw [toAdd_mul, toAdd_rho, hcv] at h4
      have h5 : ((ψ g').1 : Matrix (Fin 2) (Fin 2) K) * (c • X₀) *
            ((ψ g').2 : Matrix (Fin 2) (Fin 2) K)ᵀ =
          c • (((ψ g').1 : Matrix (Fin 2) (Fin 2) K) * X₀ *
            ((ψ g').2 : Matrix (Fin 2) (Fin 2) K)ᵀ) := by
        rw [Matrix.mul_smul, Matrix.smul_mul]
      rw [hX₁, toAdd_rho, toAdd_ofAdd, ← h5, ← h4]
    have hne : ∀ d : K, X₁ ≠ d • X₀ := by
      intro d hd
      have h1 : Multiplicative.toAdd (e ⟨z, hzV⟩) = (c * (d - 1)) • X₀ := by
        rw [hd, smul_smul] at hX₁eq
        have h1' : Multiplicative.toAdd (e ⟨z, hzV⟩) = (c * d) • X₀ - c • X₀ := by
          rw [hX₁eq]
          abel
        rw [h1', ← sub_smul, mul_sub, mul_one]
      have h2 := hzd hzV
      rw [h1, Matrix.det_smul, Fintype.card_fin] at h2
      have h3 : c * (d - 1) = 0 := by
        rcases mul_eq_zero.mp h2 with h | h
        · exact (pow_eq_zero_iff two_ne_zero).mp h
        · exact absurd h hX
      rw [h3, zero_smul] at h1
      apply hz1
      have h4 : e ⟨z, hzV⟩ = 1 := by rw [← ofAdd_toAdd (e _), h1, ofAdd_zero]
      exact congrArg Subtype.val ((map_eq_one_iff e e.injective).mp h4)
    have hXperp : ∀ x ∈ X, ∀ y ∈ inV e (Om4Pt.perpM X₁), x * y = y * x := by
      intro x hx y hy
      have hy2 : g⁻¹ * y * g ∈ Wp := hc.conj_inv_mem_perp g' hy
      have hxX' : x ∈ X' := hXeq.symm ▸ hx
      obtain ⟨x₀, hx₀, rfl⟩ := hxX'
      have hcomm := Subgroup.mem_centralizer_iff.mp (hXU hx₀) _ (hWpU' hy2)
      show g * x₀ * g⁻¹ * y = y * (g * x₀ * g⁻¹)
      calc g * x₀ * g⁻¹ * y = g * (x₀ * (g⁻¹ * y * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * y * g) * x₀) * g⁻¹ := by rw [← hcomm]
        _ = y * (g * x₀ * g⁻¹) := by group
    have hXV : X ≤ Subgroup.centralizer (fsuV T I : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hle : Wp ⊔ inV e (Om4Pt.perpM X₁) ≤ Subgroup.centralizer ({x} : Set G) := sup_le
        (fun w hw => Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp (hXU hx) w (hWpU' hw)))
        (fun w hw => Subgroup.mem_centralizer_singleton_iff.mpr (hXperp x hx w hw).symm)
      rw [inV_perp_sup_eq e hX₀0 hne] at hle
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
    have hXM : X ≤ fsuM T L := fun x hx =>
      S.hNM (Subgroup.centralizer_le_normalizer _ (hXV hx))
    have hXLW : X ≤ Subgroup.normalizer (LW : Set G) := fun x hx =>
      hnormLW ⟨hXM hx, (hXLv.trans hLvG) hx⟩
    have hXLWs : Group.IsSolvable ↥(X ⊓ LW) := by
      have := hXs
      exact Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion (inf_le_left : X ⊓ LW ≤ X)) (Subgroup.inclusion_injective _)
    have hXLWp : IsPGroup 2 ↥(X ⊓ LW) := hc.isPGroup_of_solvable h37c h38c hK4 hX inf_le_right
      (fun l hl => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hLvX (hLWLv hl), Subgroup.le_normalizer hl⟩) hXLWs
    have hXLW2 : X ⊓ LW ≤ pCoreOf 2 X :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
        (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
          ⟨Subgroup.le_normalizer hx, hXLW hx⟩) hXLWp
    have hcomm : ⁅LW, X⁆ ≤ pCoreOf 2 X := by
      rw [Subgroup.commutator_le]
      intro l hl x hx
      refine hXLW2 ⟨?_, ?_⟩
      · rw [commutatorElement_def]
        exact X.mul_mem ((Subgroup.mem_normalizer_iff.mp (hLvX (hLWLv hl)) x).mp hx)
          (X.inv_mem hx)
      · have h1 : x * l⁻¹ * x⁻¹ ∈ LW :=
          (Subgroup.mem_normalizer_iff.mp (hXLW hx) l⁻¹).mp (LW.inv_mem hl)
        have e1 : ⁅l, x⁆ = l * (x * l⁻¹ * x⁻¹) := by rw [commutatorElement_def]; group
        rw [e1]
        exact LW.mul_mem hl h1
    exact not_isSolvable_of_mem_cComp hLWc (hXK LW hLWLv hcomm)

end IsCoord

end Setup

end CFSG.Quasithin.H13.Ch9

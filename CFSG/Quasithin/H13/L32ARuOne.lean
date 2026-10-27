module

public import CFSG.Quasithin.H13.L32AStatements
public import CFSG.Quasithin.H13.L32NInputs
public import CFSG.Quasithin.Vol2.Ch12Sec8OneFlag
public import CFSG.Quasithin.Vol2.Ch10SecAElemAb

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

namespace Hyp147

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem normalizes (h : Hyp147 G T L V) (h13322 : Stmt13_3_2_two) :
    T ≤ Subgroup.normalizer (L : Set G) :=
  (h13322 G T L h.hyp.h13 L h.hyp.h13.faithful).1

theorem conjClosure_eq (h : Hyp147 G T L V) (h13322 : Stmt13_3_2_two) :
    conjClosure L T = L :=
  le_antisymm
    (conjClosure_le fun _ ht l hl =>
      (Subgroup.mem_normalizer_iff.1 (h.normalizes h13322 ht) l).1 hl)
    (le_conjClosure L T)

theorem hyp1223 (h : Hyp147 G T L V) (h13322 : Stmt13_3_2_two) : Hyp1223 G T L V where
  simple := h.fsu.simple
  nonabelian := h.fsu.nonabelian
  qtke := h.fsu.qtke
  sylow := h.fsu.sylow
  notAlt := fun hA => h.hyp.h13.not_excluded (Hyp14310One.qt13Excluded_of_alt hA)
  maximal := h.fsu.maximal
  faithful := h.fsu.faithful
  quasisimple := h.fsu.quasisimple
  normalizes := h.normalizes h13322
  irrPlus := by
    have := h.fsu.irrPlus
    rwa [h.conjClosure_eq h13322] at this

theorem hyp1281One (h : Hyp147 G T L V) (h13322 : Stmt13_3_2_two) (hV : StmtL32NModule) :
    Hyp1281One G T L V 3 where
  hyp := h.hyp1223 h13322
  n_mem := Or.inl rfl
  quot := nonempty_equiv_SL32_of_lieModel h.hyp.linear
  natural := (hV G T L V h.hyp h.fsu).2.2.2.2
  not_linear := fun hL => h.hyp.h13.not_excluded (Or.inr (Or.inl (Or.inl hL)))
  not_alt9 := fun hA => h.hyp.h13.not_excluded (Or.inr (Or.inr (Or.inl hA)))
  not_m24 := fun hM => h.hyp.h13.not_excluded (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl hM))))))

end Hyp147

namespace L32A

theorem det_GL_zmod_two {n : ℕ} (A : GL (Fin n) (ZMod 2)) :
    (A : Matrix (Fin n) (Fin n) (ZMod 2)).det = 1 := by
  have h : Matrix.GeneralLinearGroup.det A = 1 := Subsingleton.elim _ _
  have := congrArg Units.val h
  rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at this

@[expose] noncomputable def glToSL (n : ℕ) :
    GL (Fin n) (ZMod 2) →* Matrix.SpecialLinearGroup (Fin n) (ZMod 2) where
  toFun A := ⟨A, det_GL_zmod_two A⟩
  map_one' := by
    ext i j
    rfl
  map_mul' A B := by
    ext i j
    rfl

theorem coe_glToSL {n : ℕ} (A : GL (Fin n) (ZMod 2)) :
    ((glToSL n A : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) = (A : Matrix (Fin n) (Fin n) (ZMod 2)) := rfl

theorem glToSL_injective (n : ℕ) : Function.Injective (glToSL n) := by
  intro A B h
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  have := congrArg (fun M : Matrix.SpecialLinearGroup (Fin n) (ZMod 2) =>
    (M : Matrix (Fin n) (Fin n) (ZMod 2)) i j) h
  simpa [coe_glToSL] using this

theorem glToSL_surjective (n : ℕ) : Function.Surjective (glToSL n) := fun A =>
  ⟨Matrix.SpecialLinearGroup.toGL A, by ext i j; rfl⟩

theorem mulAutPiEquivGL_symm_apply (d : ℕ) (γ : GL (Fin d) (ZMod 2))
    (x : Multiplicative (Fin d → ZMod 2)) :
    (Vol2.Ch10.SecA.mulAutPiEquivGL d).symm γ x =
      Multiplicative.ofAdd ((γ : Matrix (Fin d) (Fin d) (ZMod 2)).mulVec
        (Multiplicative.toAdd x)) := by
  simp [Vol2.Ch10.SecA.mulAutPiEquivGL, Vol2.Ch10.SecA.mulAutPiEquivLinearEquiv,
    LinearMap.GeneralLinearGroup.generalLinearEquiv]

theorem mulAutPiEquivGL_mulVec (d : ℕ) (φ : MulAut (Multiplicative (Fin d → ZMod 2)))
    (v : Fin d → ZMod 2) :
    ((Vol2.Ch10.SecA.mulAutPiEquivGL d φ : GL (Fin d) (ZMod 2)) :
      Matrix (Fin d) (Fin d) (ZMod 2)).mulVec v =
        Multiplicative.toAdd (φ (Multiplicative.ofAdd v)) := by
  have h := mulAutPiEquivGL_symm_apply d (Vol2.Ch10.SecA.mulAutPiEquivGL d φ)
    (Multiplicative.ofAdd v)
  rw [MulEquiv.symm_apply_apply] at h
  rw [h]
  rfl

variable {G : Type} [Group G]

@[expose] noncomputable def repV {L V : Subgroup G} (hLV : L ≤ Subgroup.normalizer (V : Set G))
    {n : ℕ} (e : ↥V ≃* Multiplicative (Fin n → ZMod 2)) :
    ↥L →* Matrix.SpecialLinearGroup (Fin n) (ZMod 2) :=
  (glToSL n).comp (((MulAut.congr e).trans (Vol2.Ch10.SecA.mulAutPiEquivGL n)).toMonoidHom.comp
    ((conjAct V).comp (Subgroup.inclusion hLV)))

theorem coe_conjAct_apply {V : Subgroup G} (x : Subgroup.normalizer (V : Set G)) (v : ↥V) :
    ((conjAct V x v : ↥V) : G) = (x : G) * v * (x : G)⁻¹ := rfl

theorem repV_mulVec {L V : Subgroup G} (hLV : L ≤ Subgroup.normalizer (V : Set G)) {n : ℕ}
    (e : ↥V ≃* Multiplicative (Fin n → ZMod 2)) (l : ↥L) (v w : ↥V)
    (hw : (w : G) = l * v * (l : G)⁻¹) :
    e w = Multiplicative.ofAdd (((repV hLV e l : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (Multiplicative.toAdd (e v))) := by
  have hc : conjAct V (Subgroup.inclusion hLV l) v = w := by
    apply Subtype.ext
    rw [coe_conjAct_apply, hw]
    rfl
  show e w = Multiplicative.ofAdd (((glToSL n (Vol2.Ch10.SecA.mulAutPiEquivGL n
    (MulAut.congr e (conjAct V (Subgroup.inclusion hLV l)))) :
      Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec
      (Multiplicative.toAdd (e v)))
  rw [coe_glToSL, mulAutPiEquivGL_mulVec, MulAut.congr_apply]
  simp [hc]

theorem repV_surjective {L V : Subgroup G} (hLV : L ≤ Subgroup.normalizer (V : Set G)) {n : ℕ}
    (e : ↥V ≃* Multiplicative (Fin n → ZMod 2)) (hA : autOn L V = ⊤) :
    Function.Surjective (repV hLV e) := by
  intro A
  obtain ⟨γ, rfl⟩ := glToSL_surjective n A
  set φ : MulAut ↥V := ((MulAut.congr e).trans (Vol2.Ch10.SecA.mulAutPiEquivGL n)).symm γ
  have hφ : φ ∈ autOn L V := by rw [hA]; exact Subgroup.mem_top _
  obtain ⟨x, hx, hxφ⟩ := hφ
  refine ⟨⟨(x : G), hx⟩, ?_⟩
  have hinc : Subgroup.inclusion hLV ⟨(x : G), hx⟩ = x := rfl
  show glToSL n (((MulAut.congr e).trans (Vol2.Ch10.SecA.mulAutPiEquivGL n))
    (conjAct V (Subgroup.inclusion hLV ⟨(x : G), hx⟩))) = glToSL n γ
  rw [hinc, hxφ, MulEquiv.apply_symm_apply]

theorem repV_ker {L V : Subgroup G} (hLV : L ≤ Subgroup.normalizer (V : Set G)) {n : ℕ}
    (e : ↥V ≃* Multiplicative (Fin n → ZMod 2)) :
    (repV hLV e).ker = (Subgroup.centralizer (V : Set G)).subgroupOf L := by
  ext l
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
  constructor
  · intro h v hv
    have h1 : conjAct V (Subgroup.inclusion hLV l) = 1 := by
      apply ((MulAut.congr e).trans (Vol2.Ch10.SecA.mulAutPiEquivGL n)).injective
      apply glToSL_injective n
      rw [map_one, map_one]
      exact h
    have h2 := congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hv⟩ : ↥V) : G)) h1
    simp only [coe_conjAct_apply, MulAut.one_apply] at h2
    have h2' : (l : G) * v * (l : G)⁻¹ = v := h2
    calc v * l = (l : G) * v * (l : G)⁻¹ * l := by rw [h2']
      _ = l * v := by group
  · intro h
    have h1 : conjAct V (Subgroup.inclusion hLV l) = 1 := by
      ext v
      rw [coe_conjAct_apply, MulAut.one_apply]
      show (l : G) * v * (l : G)⁻¹ = v
      rw [← h v v.2]
      group
    show glToSL n (((MulAut.congr e).trans (Vol2.Ch10.SecA.mulAutPiEquivGL n))
      (conjAct V (Subgroup.inclusion hLV l))) = 1
    rw [h1, map_one, map_one]

theorem ruOne_of_inputs (h13322 : Stmt13_3_2_two) (hMod : StmtL32NModule)
    (h1433 : Lemma1433Five) (h72 : Lemma14_7_72) (h74 : Lemma14_7_74)
    {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (h : Hyp147 G T L V) :
    RuType.RuOne L := by
  obtain ⟨hS, -, hSt, -, hVZ, hVF, hVC⟩ := h72 G T L V h
  obtain ⟨⟨hML, -⟩, -⟩ := h74 G T L V h
  obtain ⟨hVel, hV8, hLTV, -, hcomm, -⟩ := hMod G T L V h.hyp h.fsu
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hLTV
  have hcore : centerOf (pCoreOf 2 L) = V := by rw [← hS, ← hVZ]
  have hAut : autOn L V = ⊤ := autOn_eq_top_of_hyp1281One (h.hyp1281One h13322 hMod)
  obtain ⟨e⟩ : Nonempty (↥V ≃* Multiplicative (Fin 3 → ZMod 2)) := by
    have := hcomm
    refine Vol2.Ch10.SecA.nonempty_mulEquiv_pi_of_sq_eq_one (fun w => ?_)
      (hV8.trans (by norm_num))
    apply Subtype.ext
    simpa using hVel.2 w w.2
  set θ := repV hLV e with hθ
  have hθs : Function.Surjective θ := repV_surjective hLV e hAut
  have hθker : θ.ker = (pCoreOf 2 L).subgroupOf L := by
    obtain ⟨θ₀, hθ₀, hker₀⟩ := exists_surj_SL32_of_lieModel h.hyp.linear
    have hle : (pCoreOf 2 L).subgroupOf L ≤ θ.ker := by
      rw [hθ, repV_ker]
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hv' : v ∈ centerOf (L32A.sL T L V) := by rw [← hVZ]; exact hv
      have hx' : (x : G) ∈ L32A.sL T L V := by rw [hS]; exact hx
      exact ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hv').2) x hx').symm
    have hcard168 : Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = 168 := by
      rw [Matrix.card_SL_field]
      simp [Fin.prod_univ_three]
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup θ.ker
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup θ₀.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective θ hθs).toEquiv,
      hcard168] at h1
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective θ₀ hθ₀).toEquiv,
      hcard168, hker₀] at h2
    exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm
  rw [hS] at hSt
  obtain ⟨χ, hχker, hχtr, hχsurj, hχint⟩ := hSt θ hθs hθker
  refine
    { center_eq_commutator := by rw [hcore, ← hS]; exact hVC
      center_eq_frattini := by rw [hcore, ← hS]; exact hVF
      center_elem := by rw [hcore]; exact hVel
      modules := ⟨θ, hθs, hθker, ⟨(MulEquiv.subgroupCongr hcore).trans e,
        fun l v w hw => repV_mulVec hLV e l _ _ hw⟩,
        ⟨χ, by rw [hcore]; exact hχker, hχtr, hχsurj, hχint⟩⟩
      eq_normalizer := by
        rw [hcore]
        refine le_antisymm hLV ?_
        rw [h1433 G T L V h.hyp h.fsu]
        exact inf_le_left.trans hML.le }

end L32A

end CFSG.Quasithin.H13

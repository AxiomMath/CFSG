module

public import CFSG.Quasithin.Background.SmithB45MatM12Rep
public import CFSG.Quasithin.Background.SmithB45MatM12Cls
public import CFSG.Quasithin.Background.SmithB45MatFrob
public import CFSG.Quasithin.Background.SmithB45MatMain
public import CFSG.Quasithin.Background.B4Dual
public import CFSG.Quasithin.Background.FFC4Real

public section

namespace CFSG.Quasithin.B45Mat.M12

open CFSG.CharacterTheory.SteinbergBY CFSG.Sporadic.Mathieu CFSG.Blueprint
  CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.A5.M12
  CFSG.Quasithin.Vol2.Ch10.SecA.C10P01 FieldFour Matrix Module

theorem isIrreducible_of_finrank_eq_one {G k V : Type*} [Group G] [Field k] [AddCommGroup V]
    [Module k V] (ρ : Representation k G V) (h : finrank k V = 1) : ρ.IsIrreducible := by
  have hs : IsSimpleModule k V := isSimpleModule_iff_finrank_eq_one.2 h
  have hnt : Nontrivial V := Module.nontrivial_of_finrank_eq_succ h
  have hbt : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro hbt
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have hvtop : v ∈ (⊤ : Subrepresentation ρ) := Submodule.mem_top
    rw [← hbt] at hvtop
    exact hv ((Submodule.mem_bot k).mp hvtop)
  have : Nontrivial (Subrepresentation ρ) := ⟨⟨⊥, ⊤, hbt⟩⟩
  refine ⟨fun U => ?_⟩
  rcases IsSimpleOrder.eq_bot_or_eq_top U.toSubmodule with h0 | h0
  · left
    ext v
    rw [h0]
    rfl
  · right
    ext v
    rw [h0]
    rfl

@[expose] def rep1 : G12 →* Matrix (Fin 1) (Fin 1) (ZMod 2) := 1

theorem isIrreducible_rep1 {K : Type*} [Field K] (φ : ZMod 2 →+* K) :
    (matrixBaseChange φ rep1).IsIrreducible :=
  isIrreducible_of_finrank_eq_one _ (Module.finrank_fin_fun K)

section Closure

variable (k : Type*) [Field k] [IsAlgClosed k] [CharP k 2]

abbrev m12Dim : Fin 6 → ℕ := ![1, 10, 44, 144, 16, 16]


@[expose] noncomputable def m12ClosureRep : ∀ i : Fin 6, Representation k G12 (Fin (m12Dim i) → k)
  | 0 => matrixBaseChange ((toField k).comp ofPrime) rep1
  | 1 => matrixBaseChange ((toField k).comp ofPrime) rep10
  | 2 => matrixBaseChange ((toField k).comp ofPrime) rep44
  | 3 => matrixBaseChange ((toField k).comp ofPrime) rep144
  | 4 => matrixBaseChange (toField k) rep16a
  | 5 => matrixBaseChange (toField k) rep16b

theorem isIrreducible_m12ClosureRep : ∀ i, (m12ClosureRep k i).IsIrreducible := by
  intro i
  fin_cases i
  · exact isIrreducible_rep1 _
  · exact isIrreducible_rep10 _
  · exact isIrreducible_rep44 _
  · exact isIrreducible_rep144 _
  · exact isIrreducible_rep16a _
  · exact isIrreducible_rep16b _

theorem isEmpty_equiv_16 :
    IsEmpty ((matrixBaseChange (toField k) rep16a).Equiv (matrixBaseChange (toField k) rep16b)) :=
  isEmpty_equiv_of_trace_ne (m12a * m12b) (by
    rw [trace_matrixBaseChange, trace_matrixBaseChange, trace_rep16a, trace_rep16b]
    exact fun h => ω_ne_ω₂ ((toField k).injective h))

theorem isEmpty_equiv_m12ClosureRep (i j : Fin 6) (hij : i ≠ j) :
    IsEmpty ((m12ClosureRep k i).Equiv (m12ClosureRep k j)) := by
  by_cases hd : m12Dim i = m12Dim j
  · have hcases : (i = 4 ∧ j = 5) ∨ (i = 5 ∧ j = 4) := by
      revert i j
      decide
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact isEmpty_equiv_16 k
    · exact ⟨fun e => (isEmpty_equiv_16 k).false e.symm⟩
  · exact isEmpty_equiv_of_finrank_ne (by rwa [Module.finrank_fin_fun, Module.finrank_fin_fun])

theorem frob_comp_rep16b :
    (frob.mapMatrix : Matrix (Fin 16) (Fin 16) FieldFour →+* _).toMonoidHom.comp rep16b =
      rep16a := by
  rw [rep16b_eq]
  exact MonoidHom.ext fun _ => Matrix.ext fun _ _ => frob_frob _

theorem m12ClosureRep_complete
    (W : Type*) [AddCommGroup W] [Module k W] (σ : Representation k G12 W)
    (hσ : σ.IsIrreducible) :
    FiniteDimensional k W ∧ ∃ i, Nonempty (σ.Equiv (m12ClosureRep k i)) := by
  have := isIrreducible_m12ClosureRep k
  have := hσ
  exact exists_equiv_of_card_pRegularClass_le 2 _ (m12ClosureRep k)
    (isEmpty_equiv_m12ClosureRep k) (card_pRegularClass_m12.trans (Fintype.card_fin 6).symm.le)
    W σ

end Closure

section Binary


theorem m12_binary_cases (W : Type) [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (τ : Representation (ZMod 2) G12 W) (hτ : τ.IsIrreducible)
    (hW : finrank (ZMod 2) W ≤ 24) :
    Nonempty (τ.Equiv (matrixBaseChange (RingHom.id (ZMod 2)) rep1)) ∨
      Nonempty (τ.Equiv (matrixBaseChange (RingHom.id (ZMod 2)) rep10)) := by
  refine binary_coords_elim W τ hτ fun N hNirr hτN U hU0 hUirr => ?_
  obtain ⟨eτ⟩ := hτN
  let k := AlgebraicClosure (ZMod 2)
  let ψ : ZMod 2 →+* k := (toField k).comp ofPrime
  obtain ⟨-, j, ⟨e⟩⟩ := m12ClosureRep_complete k U.toSubmodule U.toRepresentation hUirr
  have hf := incl_comp_ne_zero U hU0 e
  have hdU : finrank k U.toSubmodule ≤ 24 := by
    have h1 := Submodule.finrank_le U.toSubmodule
    rw [Module.finrank_fin_fun] at h1
    exact h1.trans hW
  have hdimj : finrank k U.toSubmodule = m12Dim j := by
    rw [e.toLinearEquiv.finrank_eq, Module.finrank_fin_fun]
  fin_cases j
  · obtain ⟨e'⟩ := nonempty_equiv_of_intertwining_binary rep1 N (isIrreducible_rep1 _) hNirr ψ _ hf
    exact Or.inl ⟨eτ.trans e'⟩
  · obtain ⟨e'⟩ := nonempty_equiv_of_intertwining_binary rep10 N (isIrreducible_rep10 _) hNirr ψ
      _ hf
    exact Or.inr ⟨eτ.trans e'⟩
  · exfalso
    simp only [m12Dim] at hdimj
    norm_num [hdimj] at hdU
  · exfalso
    simp only [m12Dim] at hdimj
    norm_num [hdimj] at hdU
  · exfalso
    have h32 := two_mul_le_of_frob ψ U hUirr (toField k) (M := rep16a) e
      (by
        rw [← rep16b_eq]
        exact isEmpty_equiv_16 k)
    omega
  · exfalso
    have h32 := two_mul_le_of_frob ψ U hUirr (toField k) (M := rep16b) e
      (by
        rw [frob_comp_rep16b]
        exact ⟨fun e' => (isEmpty_equiv_16 k).false e'.symm⟩)
    omega

end Binary

section Module

variable {W : Type} [CommGroup W] (hV : ∀ w : W, w ^ 2 = 1)

@[expose] def autLin (a : MulAut W) : F2Vec W hV →ₗ[ZMod 2] F2Vec W hV :=
  AddMonoidHom.toZModLinearMap 2
    { toFun := fun v => F2Vec.ofV hV (a (F2Vec.toV hV v))
      map_zero' := by
        rw [F2Vec.toV_zero, map_one, F2Vec.ofV_one]
      map_add' := fun u v => by
        rw [F2Vec.toV_add, map_mul, F2Vec.ofV_mul] }

@[expose] def autRep : MulAut W →* (F2Vec W hV →ₗ[ZMod 2] F2Vec W hV) where
  toFun := autLin hV
  map_one' := LinearMap.ext fun _ => rfl
  map_mul' _ _ := LinearMap.ext fun _ => rfl

variable {L : Subgroup (MulAut W)}

@[expose] def autRepOf (θ : ↥L ≃* G12) : Representation (ZMod 2) G12 (F2Vec W hV) :=
  (autRep hV).comp (L.subtype.comp θ.symm.toMonoidHom)

theorem autRepOf_apply (θ : ↥L ≃* G12) (g : G12) (v : F2Vec W hV) :
    autRepOf hV θ g v = F2Vec.ofV hV ((θ.symm g : MulAut W) (F2Vec.toV hV v)) :=
  rfl

theorem isIrreducible_autRepOf [Nontrivial W] (θ : ↥L ≃* G12)
    (hirr : ∀ U : Subgroup W, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤) :
    (autRepOf hV θ).IsIrreducible := by
  have : Nontrivial (F2Vec W hV) := inferInstanceAs (Nontrivial (Additive W))
  have hbt : (⊥ : Subrepresentation (autRepOf hV θ)) ≠ ⊤ := by
    intro h
    obtain ⟨v, hv⟩ := exists_ne (0 : F2Vec W hV)
    have hvt : v ∈ (⊤ : Subrepresentation (autRepOf hV θ)).toSubmodule := Submodule.mem_top
    rw [← h] at hvt
    exact hv ((Submodule.mem_bot _).mp hvt)
  have : Nontrivial (Subrepresentation (autRepOf hV θ)) := ⟨⟨⊥, ⊤, hbt⟩⟩
  refine ⟨fun U => ?_⟩
  let U' : Subgroup W :=
    { carrier := {w | F2Vec.ofV hV w ∈ U.toSubmodule}
      mul_mem' := fun {a b} ha hb => by
        change F2Vec.ofV hV (a * b) ∈ U.toSubmodule
        rw [F2Vec.ofV_mul]
        exact U.toSubmodule.add_mem ha hb
      one_mem' := by
        change F2Vec.ofV hV 1 ∈ U.toSubmodule
        rw [F2Vec.ofV_one]
        exact U.toSubmodule.zero_mem
      inv_mem' := fun {w} hw => by
        have hinv : w⁻¹ = w := by
          rw [inv_eq_iff_mul_eq_one, ← sq]
          exact hV w
        change F2Vec.ofV hV w⁻¹ ∈ U.toSubmodule
        rw [hinv]
        exact hw }
  have hU' : ∀ g ∈ L, ∀ u ∈ U', g u ∈ U' := by
    intro g hg u hu
    have h1 := U.apply_mem_toSubmodule (θ ⟨g, hg⟩) hu
    change F2Vec.ofV hV ((θ.symm (θ ⟨g, hg⟩) : MulAut W) (F2Vec.toV hV (F2Vec.ofV hV u))) ∈
      U.toSubmodule at h1
    rw [MulEquiv.symm_apply_apply] at h1
    exact h1
  rcases hirr U' hU' with h0 | h0
  · left
    ext v
    constructor
    · intro hv
      have hv' : F2Vec.toV hV v ∈ U' := hv
      rw [h0, Subgroup.mem_bot] at hv'
      have hv0 : v = 0 := by
        rw [← F2Vec.ofV_toV hV v, hv', F2Vec.ofV_one]
      rw [hv0]
      exact Submodule.zero_mem _
    · intro hv
      have hv0 : v = 0 := (Submodule.mem_bot _).mp hv
      rw [hv0]
      exact U.toSubmodule.zero_mem
  · right
    ext v
    constructor
    · intro _
      exact Submodule.mem_top
    · intro _
      have hv' : F2Vec.toV hV v ∈ U' := by
        rw [h0]
        exact Subgroup.mem_top _
      exact hv'

theorem finrank_autRepOf_le [Finite W] (hcard : Nat.card W ≤ 2 ^ 24) :
    finrank (ZMod 2) (F2Vec W hV) ≤ 24 := by
  have h1 : Nat.card (F2Vec W hV) = 2 ^ finrank (ZMod 2) (F2Vec W hV) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have h2 : Nat.card (F2Vec W hV) = Nat.card W := rfl
  have h3 : 2 ^ finrank (ZMod 2) (F2Vec W hV) ≤ 2 ^ 24 := by
    rw [← h1, h2]
    exact hcard
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h3

theorem mulAutMat_mulVec (n : ℕ) (f : MulAut (Multiplicative (Fin n → ZMod 2)))
    (x : Fin n → ZMod 2) :
    mulAutMat n f *ᵥ x = Multiplicative.toAdd (f (Multiplicative.ofAdd x)) := by
  simp only [mulAutMat, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [LinearMap.toMatrix'_mulVec]
  rfl

theorem exists_map_congrHom_eq_range
    (θ : ↥L ≃* G12) (ρ : ↥(m24Fix dodecadE) →* MulAut W10)
    (e : F2Vec W hV ≃ₗ[ZMod 2] (Fin 10 → ZMod 2))
    (he : ∀ g v, e (F2Vec.ofV hV ((θ.symm g : MulAut W) (F2Vec.toV hV v))) =
      mulAutMat 10 (ρ (e12.symm g)) *ᵥ e v) :
    ∃ φ : W ≃* W10, L.map (congrHom φ) = ρ.range := by
  let φ : W ≃* W10 :=
    { toFun := fun w => Multiplicative.ofAdd (e (F2Vec.ofV hV w))
      invFun := fun x => F2Vec.toV hV (e.symm (Multiplicative.toAdd x))
      left_inv := fun w => by simp [F2Vec.toV_ofV]
      right_inv := fun x => by simp [F2Vec.ofV_toV]
      map_mul' := fun a b => by
        simp only [F2Vec.ofV_mul, map_add, ofAdd_add] }
  have hφ : ∀ g : G12, congrHom φ (θ.symm g : MulAut W) = ρ (e12.symm g) := by
    intro g
    refine MulEquiv.ext fun x => ?_
    change Multiplicative.ofAdd (e (F2Vec.ofV hV ((θ.symm g : MulAut W)
      (F2Vec.toV hV (e.symm (Multiplicative.toAdd x)))))) = _
    rw [he, LinearEquiv.apply_symm_apply, mulAutMat_mulVec]
    rfl
  refine ⟨φ, le_antisymm ?_ ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    have hy' : y = (θ.symm (θ ⟨y, hy⟩) : MulAut W) := by rw [MulEquiv.symm_apply_apply]
    rw [hy', hφ]
    exact ⟨_, rfl⟩
  · rintro _ ⟨σ, rfl⟩
    refine ⟨(θ.symm (e12 σ) : MulAut W), (θ.symm (e12 σ)).2, ?_⟩
    rw [hφ, MulEquiv.symm_apply_apply]

end Module

theorem realizes_of_map_congrHom {V W : Type*} [CommGroup V] [CommGroup W] (φ : V ≃* W)
    {L : Subgroup (MulAut V)} {H : Subgroup (MulAut W)} (hLH : L.map (congrHom φ) = H)
    {D : FFModel} (h : D.Realizes H ⊤ ⊥) : D.Realizes L ⊤ ⊥ := by
  obtain ⟨π, hπ⟩ := h
  let e : ↥L ≃* ↥H := ((MulAut.congr φ).subgroupMap L).trans (MulEquiv.subgroupCongr hLH)
  have he : ∀ (g : ↥L) (w : W), φ.symm.toMonoidHom ((e g : MulAut W) w) =
      (g : MulAut V) (φ.symm.toMonoidHom w) := by
    intro g w
    change φ.symm (φ ((g : MulAut V) (φ.symm w))) = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  have h1 := CFSG.Quasithin.FFC.RealizesVia.transport φ.symm.toMonoidHom φ.symm.injective e he hπ
  rw [Subgroup.map_top_of_surjective _ φ.symm.surjective, Subgroup.map_bot] at h1
  exact ⟨_, h1⟩

theorem m12Ten_rhoC12 : M12Ten (rhoC12 (m24Fix dodecadE) m24Fix_le_m24Pair).range ⊤ ⊥ :=
  ⟨dodecadE, dodecadE_mem_golayC, hammingNorm_dodecadE,
    CFSG.Quasithin.H13.A5.M12.realizes_rho_of_coords code12Coords
      (fun _ hσ => preserves_code12 (m24Fix_le_m24Pair hσ))
      ((Subgroup.closure_le _).2 (by
        rintro _ (rfl | rfl)
        · exact allOnes_mem_golayC
        · exact dodecadE_mem_golayC))⟩

end CFSG.Quasithin.B45Mat.M12

namespace CFSG.Quasithin

open CFSG.CharacterTheory.SteinbergBY CFSG.Blueprint CFSG.Sporadic.Mathieu
  CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.A5.M12 CFSG.Quasithin.Vol2.Ch10.SecA.C10P01
  B45Mat B45Mat.M12 Module Matrix

theorem mathieuSmallIrr12_holds :
    MathieuSmallIrr12 := by
  intro W _ _ hW2 L hLiso hirr hcard
  obtain ⟨θ0⟩ := hLiso
  have hV : ∀ w : W, w ^ 2 = 1 := fun w => by
    rw [sq]
    exact hW2 w
  let θ : ↥L ≃* G12 := θ0
  have hcardG : Nat.card G12 = 95040 := card_M12
  have hntW : Nontrivial W := by
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    have : Subsingleton ↥L :=
      ⟨fun x y => Subtype.ext (MulEquiv.ext fun w => Subsingleton.elim _ _)⟩
    have h1 := Nat.card_congr θ.toEquiv
    rw [hcardG, Nat.card_of_subsingleton (1 : ↥L)] at h1
    norm_num at h1
  have hfin : FiniteDimensional (ZMod 2) (F2Vec W hV) := Module.Finite.of_finite
  have hcases := m12_binary_cases (F2Vec W hV) (autRepOf hV θ)
    (isIrreducible_autRepOf hV θ hirr) (finrank_autRepOf_le hV hcard)
  rcases hcases with he | he
  · obtain ⟨e⟩ := he
    exfalso
    have htriv : ∀ g : G12, g = 1 := by
      intro g
      have h1 : ∀ w : W, (θ.symm g : MulAut W) w = w := by
        intro w
        have h2 := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g
          (F2Vec.ofV hV w)
        have h3 : rep1 g = 1 := rfl
        rw [matrixBaseChange_apply, h3, RingHom.coe_id, Matrix.map_id, Matrix.one_mulVec,
          Representation.Equiv.coe_toIntertwiningMap] at h2
        exact Additive.ofMul.injective (e.injective h2)
      have h5 : θ.symm g = 1 := Subtype.ext (MulEquiv.ext h1)
      exact θ.symm.injective (h5.trans (map_one θ.symm).symm)
    have : Subsingleton G12 := ⟨fun x y => (htriv x).trans (htriv y).symm⟩
    rw [Nat.card_of_subsingleton (1 : G12)] at hcardG
    norm_num at hcardG
  · obtain ⟨e⟩ := he
    obtain ⟨φ, hφ⟩ := exists_map_congrHom_eq_range hV θ
      (rhoC12 (m24Fix dodecadE) m24Fix_le_m24Pair) e.toLinearEquiv fun g v => by
        have h1 := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g v
        rw [matrixBaseChange_apply, RingHom.coe_id, Matrix.map_id, rep10_apply] at h1
        rw [Representation.Equiv.toLinearEquiv_apply, Representation.Equiv.toLinearEquiv_apply,
          ← autRepOf_apply]
        exact h1
    obtain ⟨eY, hY, hw, hR⟩ := m12Ten_rhoC12
    exact ⟨eY, hY, hw, realizes_of_map_congrHom φ hφ hR⟩

theorem asB45M12_holds :
    AsB45M12 :=
  asB45M12_of_smallIrr mathieuSmallIrr12_holds

end CFSG.Quasithin

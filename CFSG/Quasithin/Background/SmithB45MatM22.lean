module

public import CFSG.Quasithin.Background.SmithB45MatM22Rep
public import CFSG.Quasithin.Background.SmithB45MatM22Cls
public import CFSG.Quasithin.Background.SmithB45MatMain
public import CFSG.Quasithin.Background.B4Dual
public import CFSG.Quasithin.Background.FFC4Real

public section

namespace CFSG.Quasithin.B45Mat.M22

open CFSG.CharacterTheory.SteinbergBY CFSG.QuasithinUnique.Setup.X1 CFSG.Sporadic.Mathieu
  CFSG.Blueprint CFSG.Monster.B.TwoA CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu FieldFour Matrix
  Module

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

@[expose] def rep1 : G22 →* Matrix (Fin 1) (Fin 1) (ZMod 2) := 1

theorem isIrreducible_rep1 {K : Type*} [Field K] (φ : ZMod 2 →+* K) :
    (matrixBaseChange φ rep1).IsIrreducible :=
  isIrreducible_of_finrank_eq_one _ (Module.finrank_fin_fun K)

section Closure

variable (k : Type*) [Field k] [IsAlgClosed k] [CharP k 2]

abbrev m22Dim : Fin 7 → ℕ := ![1, 10, 10, 34, 98, 70, 70]

@[expose] noncomputable def m22ClosureRep :
    ∀ i : Fin 7, Representation k G22 (Fin (m22Dim i) → k)
  | 0 => matrixBaseChange ((toField k).comp ofPrime) rep1
  | 1 => matrixBaseChange ((toField k).comp ofPrime) rep10a
  | 2 => matrixBaseChange ((toField k).comp ofPrime) rep10b
  | 3 => matrixBaseChange ((toField k).comp ofPrime) rep34
  | 4 => matrixBaseChange ((toField k).comp ofPrime) rep98
  | 5 => matrixBaseChange (toField k) rep70a
  | 6 => matrixBaseChange (toField k) rep70b

theorem isIrreducible_m22ClosureRep : ∀ i, (m22ClosureRep k i).IsIrreducible := by
  intro i
  fin_cases i
  · exact isIrreducible_rep1 _
  · exact isIrreducible_rep10a _
  · exact isIrreducible_rep10b _
  · exact isIrreducible_rep34 _
  · exact isIrreducible_rep98 _
  · exact isIrreducible_rep70a _
  · exact isIrreducible_rep70b _

theorem isEmpty_equiv_m22ClosureRep (i j : Fin 7) (hij : i ≠ j) :
    IsEmpty ((m22ClosureRep k i).Equiv (m22ClosureRep k j)) := by
  have h12 : ((toField k).comp ofPrime) (Matrix.trace (rep10a g7)) ≠
      ((toField k).comp ofPrime) (Matrix.trace (rep10b g7)) := by
    rw [trace_rep10a_g7, trace_rep10b_g7, map_one, map_zero]
    exact zero_ne_one
  have h56 : (toField k) (Matrix.trace (rep70a g11)) ≠ (toField k) (Matrix.trace (rep70b g11)) := by
    rw [trace_rep70a_g11, trace_rep70b_g11]
    exact fun h => ω_ne_ω₂ ((toField k).injective h)
  by_cases hd : m22Dim i = m22Dim j
  · have hcases : (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨ (i = 5 ∧ j = 6) ∨ (i = 6 ∧ j = 5) := by
      revert i j
      decide
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine isEmpty_equiv_of_trace_ne g7 ?_
      change LinearMap.trace k (Fin 10 → k) (matrixBaseChange _ rep10a g7) ≠
        LinearMap.trace k (Fin 10 → k) (matrixBaseChange _ rep10b g7)
      rw [trace_matrixBaseChange, trace_matrixBaseChange]
      exact h12
    · refine isEmpty_equiv_of_trace_ne g7 ?_
      change LinearMap.trace k (Fin 10 → k) (matrixBaseChange _ rep10b g7) ≠
        LinearMap.trace k (Fin 10 → k) (matrixBaseChange _ rep10a g7)
      rw [trace_matrixBaseChange, trace_matrixBaseChange]
      exact h12.symm
    · refine isEmpty_equiv_of_trace_ne g11 ?_
      change LinearMap.trace k (Fin 70 → k) (matrixBaseChange _ rep70a g11) ≠
        LinearMap.trace k (Fin 70 → k) (matrixBaseChange _ rep70b g11)
      rw [trace_matrixBaseChange, trace_matrixBaseChange]
      exact h56
    · refine isEmpty_equiv_of_trace_ne g11 ?_
      change LinearMap.trace k (Fin 70 → k) (matrixBaseChange _ rep70b g11) ≠
        LinearMap.trace k (Fin 70 → k) (matrixBaseChange _ rep70a g11)
      rw [trace_matrixBaseChange, trace_matrixBaseChange]
      exact h56.symm
  · exact isEmpty_equiv_of_finrank_ne (by rwa [Module.finrank_fin_fun, Module.finrank_fin_fun])

theorem m22ClosureRep_complete
    (W : Type*) [AddCommGroup W] [Module k W] (σ : Representation k G22 W)
    (hσ : σ.IsIrreducible) :
    FiniteDimensional k W ∧ ∃ i, Nonempty (σ.Equiv (m22ClosureRep k i)) := by
  have := isIrreducible_m22ClosureRep k
  have := hσ
  exact exists_equiv_of_card_pRegularClass_le 2 _ (m22ClosureRep k)
    (isEmpty_equiv_m22ClosureRep k) (card_pRegularClass_m22.trans (Fintype.card_fin 7).symm.le)
    W σ

end Closure

abbrev m22BinDim : Fin 3 → ℕ := ![1, 10, 10]

@[expose] noncomputable def m22BinRep :
    ∀ i : Fin 3, G22 →* Matrix (Fin (m22BinDim i)) (Fin (m22BinDim i)) (ZMod 2)
  | 0 => rep1
  | 1 => rep10a
  | 2 => rep10b

theorem m22_binary_small
    (W : Type) [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (τ : Representation (ZMod 2) G22 W) (hτ : τ.IsIrreducible)
    (hW : finrank (ZMod 2) W ≤ 33) :
    ∃ i, Nonempty (τ.Equiv (matrixBaseChange (RingHom.id (ZMod 2)) (m22BinRep i))) := by
  refine exists_binary_equiv m22BinRep (fun i => ?_) 33 (fun U _ _ _ σ hσ hU => ?_) W τ hτ hW
  · fin_cases i
    · exact isIrreducible_rep1 _
    · exact isIrreducible_rep10a _
    · exact isIrreducible_rep10b _
  · obtain ⟨-, j, ⟨e⟩⟩ := m22ClosureRep_complete (AlgebraicClosure (ZMod 2)) U σ hσ
    have hdim : finrank (AlgebraicClosure (ZMod 2)) U = m22Dim j := by
      rw [e.toLinearEquiv.finrank_eq, Module.finrank_fin_fun]
    fin_cases j
    · exact ⟨0, ⟨e⟩⟩
    · exact ⟨1, ⟨e⟩⟩
    · exact ⟨2, ⟨e⟩⟩
    all_goals
      exfalso
      simp only [m22Dim] at hdim
      norm_num [hdim] at hU

theorem m22_binary_cases
    (W : Type) [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (τ : Representation (ZMod 2) G22 W) (hτ : τ.IsIrreducible)
    (hW : finrank (ZMod 2) W ≤ 33) :
    Nonempty (τ.Equiv (matrixBaseChange (RingHom.id (ZMod 2)) rep1)) ∨
      Nonempty (τ.Equiv (matrixBaseChange (RingHom.id (ZMod 2)) rep10a)) ∨
      Nonempty (τ.Equiv (matrixBaseChange (RingHom.id (ZMod 2)) rep10b)) := by
  obtain ⟨i, he⟩ := m22_binary_small W τ hτ hW
  fin_cases i
  · exact Or.inl he
  · exact Or.inr (Or.inl he)
  · exact Or.inr (Or.inr he)

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

theorem autRep_apply (a : MulAut W) (v : F2Vec W hV) :
    autRep hV a v = F2Vec.ofV hV (a (F2Vec.toV hV v)) :=
  rfl

theorem mulAutMat_mulVec (n : ℕ) (f : MulAut (Multiplicative (Fin n → ZMod 2)))
    (x : Fin n → ZMod 2) :
    mulAutMat n f *ᵥ x = Multiplicative.toAdd (f (Multiplicative.ofAdd x)) := by
  simp only [mulAutMat, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [LinearMap.toMatrix'_mulVec]
  rfl

theorem exists_map_congrHom_eq_range
    {L : Subgroup (MulAut W)} (θ : ↥L ≃* G22)
    (ρ : ↥mog22 →* MulAut W10) (e : F2Vec W hV ≃ₗ[ZMod 2] (Fin 10 → ZMod 2))
    (he : ∀ g v, e (F2Vec.ofV hV ((θ.symm g : MulAut W) (F2Vec.toV hV v))) =
      mulAutMat 10 (ρ (psiS22 g)) *ᵥ e v) :
    ∃ φ : W ≃* W10, L.map (congrHom φ) = ρ.range := by
  let φ : W ≃* W10 :=
    { toFun := fun w => Multiplicative.ofAdd (e (F2Vec.ofV hV w))
      invFun := fun x => F2Vec.toV hV (e.symm (Multiplicative.toAdd x))
      left_inv := fun w => by simp [F2Vec.toV_ofV]
      right_inv := fun x => by simp [F2Vec.ofV_toV]
      map_mul' := fun a b => by
        simp only [F2Vec.ofV_mul, map_add, ofAdd_add] }
  have hφ : ∀ g : G22, congrHom φ (θ.symm g : MulAut W) = ρ (psiS22 g) := by
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
    have hσ : psiS22 (mog22EquivM22 σ) = σ := mog22EquivM22.symm_apply_apply σ
    refine ⟨(θ.symm (mog22EquivM22 σ) : MulAut W), (θ.symm (mog22EquivM22 σ)).2, ?_⟩
    rw [hφ, hσ]

end Module

section Realize

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

theorem cocode22_rho10 : MathieuCocode22 (rho10 mog22 mog22_le_mog22plus).range ⊤ ⊥ :=
  ⟨0, 1, by decide, CFSG.Quasithin.H13.A5.M12.realizes_rho_of_coords cocode22Coords
    (fun _ hσ => preserves_cocode22 (mog22_le_mog22plus hσ))
    (sup_le golayC_le_coreMod (Subgroup.zpowers_le.mpr (pairVec_mem_core 0 1)))⟩

theorem code22_rhoC10 : MathieuCode22 (rhoC10 mog22 mog22_le_mog22plus).range ⊤ ⊥ :=
  ⟨0, 1, by decide, CFSG.Quasithin.H13.A5.M12.realizes_rho_of_coords code22Coords
    (fun _ hσ => preserves_code22 (mog22_le_mog22plus hσ))
    (Subgroup.zpowers_le.mpr ⟨allOnes_mem_golayC, (mem_pairKer 0 1 _).2 (by decide)⟩)⟩

end Realize

section Rep

variable {W : Type} [CommGroup W] (hV : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}

@[expose] def autRepOf (θ : ↥L ≃* G22) : Representation (ZMod 2) G22 (F2Vec W hV) :=
  (autRep hV).comp (L.subtype.comp θ.symm.toMonoidHom)

theorem autRepOf_apply (θ : ↥L ≃* G22) (g : G22) (v : F2Vec W hV) :
    autRepOf hV θ g v = F2Vec.ofV hV ((θ.symm g : MulAut W) (F2Vec.toV hV v)) :=
  rfl

theorem isIrreducible_autRepOf [Nontrivial W] (θ : ↥L ≃* G22)
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

theorem finrank_autRepOf_le [Finite W] (hcard : Nat.card W ≤ 2 ^ 30) :
    finrank (ZMod 2) (F2Vec W hV) ≤ 33 := by
  have h1 : Nat.card (F2Vec W hV) = 2 ^ finrank (ZMod 2) (F2Vec W hV) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have h2 : Nat.card (F2Vec W hV) = Nat.card W := rfl
  have h3 : 2 ^ finrank (ZMod 2) (F2Vec W hV) ≤ 2 ^ 30 := by
    rw [← h1, h2]
    exact hcard
  have h4 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h3
  omega

end Rep

end CFSG.Quasithin.B45Mat.M22

namespace CFSG.Quasithin

open CFSG.CharacterTheory.SteinbergBY CFSG.Blueprint CFSG.Sporadic.Mathieu
  CFSG.Quasithin.H.Mathieu B45Mat B45Mat.M22 Module Matrix

theorem mathieuSmallIrr22_holds :
    MathieuSmallIrr22 := by
  intro W _ _ hW2 L hLiso hirr hcard
  obtain ⟨θ0⟩ := hLiso
  have hV : ∀ w : W, w ^ 2 = 1 := fun w => by
    rw [sq]
    exact hW2 w
  let θ : ↥L ≃* G22 := θ0
  have hcardG : Nat.card G22 = 443520 := card_M22
  have hntW : Nontrivial W := by
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    have : Subsingleton ↥L :=
      ⟨fun x y => Subtype.ext (MulEquiv.ext fun w => Subsingleton.elim _ _)⟩
    have h1 := Nat.card_congr θ.toEquiv
    rw [hcardG, Nat.card_of_subsingleton (1 : ↥L)] at h1
    norm_num at h1
  have hfin : FiniteDimensional (ZMod 2) (F2Vec W hV) := Module.Finite.of_finite
  have hcases := m22_binary_cases (F2Vec W hV) (autRepOf hV θ)
    (isIrreducible_autRepOf hV θ hirr) (finrank_autRepOf_le hV hcard)
  rcases hcases with he | he | he
  · obtain ⟨e⟩ := he
    exfalso
    have htriv : ∀ g : G22, g = 1 := by
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
    have : Subsingleton G22 := ⟨fun x y => (htriv x).trans (htriv y).symm⟩
    rw [Nat.card_of_subsingleton (1 : G22)] at hcardG
    norm_num at hcardG
  · obtain ⟨e⟩ := he
    right
    obtain ⟨φ, hφ⟩ := exists_map_congrHom_eq_range hV θ (rho10 mog22 mog22_le_mog22plus)
      e.toLinearEquiv fun g v => by
        have h1 := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g v
        rw [matrixBaseChange_apply, RingHom.coe_id, Matrix.map_id, rep10a_apply] at h1
        rw [Representation.Equiv.toLinearEquiv_apply, Representation.Equiv.toLinearEquiv_apply,
          ← autRepOf_apply]
        exact h1
    obtain ⟨x, y, hxy, hR⟩ := cocode22_rho10
    exact ⟨x, y, hxy, realizes_of_map_congrHom φ hφ hR⟩
  · obtain ⟨e⟩ := he
    left
    obtain ⟨φ, hφ⟩ := exists_map_congrHom_eq_range hV θ (rhoC10 mog22 mog22_le_mog22plus)
      e.toLinearEquiv fun g v => by
        have h1 := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g v
        rw [matrixBaseChange_apply, RingHom.coe_id, Matrix.map_id, rep10b_apply] at h1
        rw [Representation.Equiv.toLinearEquiv_apply, Representation.Equiv.toLinearEquiv_apply,
          ← autRepOf_apply]
        exact h1
    obtain ⟨x, y, hxy, hR⟩ := code22_rhoC10
    exact ⟨x, y, hxy, realizes_of_map_congrHom φ hφ hR⟩

theorem asB45M22_holds :
    AsB45M22 :=
  asB45M22_of_smallIrr mathieuSmallIrr22_holds

end CFSG.Quasithin

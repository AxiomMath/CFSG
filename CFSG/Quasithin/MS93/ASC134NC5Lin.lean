module

public import CFSG.Quasithin.MS93.ASIrr
public import CFSG.Quasithin.MS93.ML3Ext2
public import CFSG.Quasithin.MS93.ML3Facts

public section

namespace CFSG.Quasithin.MS93.AS

open Matrix
open CFSG.Assembly.LowTwoRank (StatedSL specialLinearGroupEquivStatedSL
  specialLinearGroupEquivStatedSL_coe)

variable {F : Type} [Field F]

theorem sl3_transitive {x y : Fin 3 → F} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ g : SL3 F, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x = y := by
  obtain ⟨γ, hγ⟩ := statedSL3_transitive x y hx hy
  refine ⟨(specialLinearGroupEquivStatedSL 3 F).symm γ, ?_⟩
  rw [← specialLinearGroupEquivStatedSL_coe 3 F ((specialLinearGroupEquivStatedSL 3 F).symm γ),
    MulEquiv.apply_symm_apply]
  exact hγ

theorem schur_W {f : (Fin 3 → F) →+ (Fin 3 → F)}
    (hf : ∀ (g : SL3 F) (w : Fin 3 → F), f (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w) =
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ f w) :
    ∃ c : F, ∀ w, f w = c • w := by
  set e : Fin 3 → F := Pi.single 0 1 with he
  have he0 : e ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [he] at this
  have hept : e ∈ (pt0 : Submodule F (Fin 3 → F)) := ⟨by simp [he], by simp [he]⟩
  have hfe : f e ∈ (pt0 : Submodule F (Fin 3 → F)) := by
    rw [← fixN_qPt]
    intro g hg
    have hge : ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ e = e :=
      pt0_le_fixN_of_le_sStar qPt_le_sStar hept g hg
    rw [← hf, hge]
  have e0 : e 0 = 1 := by simp [he]
  have e1 : e 1 = 0 := by simp [he]
  have e2 : e 2 = 0 := by simp [he]
  obtain ⟨c, hc⟩ : ∃ c : F, f e = c • e := by
    refine ⟨f e 0, ?_⟩
    funext k
    fin_cases k
    · simp [e0]
    · simp [e1, hfe.1]
    · simp [e2, hfe.2]
  refine ⟨c, fun w => ?_⟩
  by_cases hw : w = 0
  · simp [hw]
  obtain ⟨g, hg⟩ := sl3_transitive he0 hw
  rw [← hg, hf, hc, Matrix.mulVec_smul]

@[expose] def dg (g : SL3 F) (n : Fin 2 → Fin 3 → F) : Fin 2 → Fin 3 → F :=
  fun i => ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ n i

theorem dg_apply (g : SL3 F) (n : Fin 2 → Fin 3 → F) (i : Fin 2) :
    dg g n i = ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ n i := rfl

theorem dg_single (g : SL3 F) (j : Fin 2) (w : Fin 3 → F) :
    dg g (Pi.single j w) = Pi.single j (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w) := by
  funext k
  by_cases hk : k = j
  · subst hk
    simp [dg]
  · simp [dg, hk]

theorem exists_decomp [Finite F] (a : (Fin 2 → Fin 3 → F) ≃+ (Fin 2 → Fin 3 → F))
    (θ : SL3 F → SL3 F) (hθ : ∀ g n, a (dg g n) = dg (θ g) (a n)) :
    ∃ (t : (Fin 3 → F) ≃+ (Fin 3 → F)) (Λ : Matrix (Fin 2) (Fin 2) F),
      (∀ g w, t (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w) =
        ((θ g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ t w) ∧
      ∀ n i, a n i = t (∑ j, Λ i j • n j) := by
  let β : Fin 2 → Fin 2 → ((Fin 3 → F) →+ (Fin 3 → F)) := fun i j =>
    (Pi.evalAddMonoidHom (fun _ => Fin 3 → F) i).comp
      ((a : (Fin 2 → Fin 3 → F) →+ (Fin 2 → Fin 3 → F)).comp
        (AddMonoidHom.single (fun _ => Fin 3 → F) j))
  have hβ : ∀ i j w, β i j w = a (Pi.single j w) i := fun _ _ _ => rfl
  have hsum : ∀ n i, a n i = ∑ j, β i j (n j) := by
    intro n i
    have hn : n = ∑ j, Pi.single j (n j) := (Finset.univ_sum_single n).symm
    conv_lhs => rw [hn]
    rw [map_sum, Finset.sum_apply]
    rfl
  have hint : ∀ i j (g : SL3 F) w, β i j (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w) =
      ((θ g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ β i j w := by
    intro i j g w
    rw [hβ, hβ, ← dg_single, hθ]
    rfl
  obtain ⟨i₀, j₀, w₀, hw₀⟩ : ∃ i j w, β i j w ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    have hz : a (Pi.single 0 (Pi.single 0 1)) = a 0 := by
      funext i
      rw [hsum, map_zero]
      simp [hcon]
    have := congrFun (congrFun (a.injective hz) 0) 0
    simp at this
  set t₀ := β i₀ j₀ with ht₀
  have ht₀inj : Function.Injective t₀ := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    by_contra hw0
    have hall : ∀ z, z ∈ t₀.ker := mem_of_invariant t₀.ker (fun g x hx => by
      rw [AddMonoidHom.mem_ker] at hx ⊢
      rw [ht₀, hint, ← ht₀, hx, Matrix.mulVec_zero]) hw hw0
    exact hw₀ (hall w₀)
  have ht₀bij : Function.Bijective t₀ :=
    ⟨ht₀inj, Finite.injective_iff_surjective.mp ht₀inj⟩
  set t : (Fin 3 → F) ≃+ (Fin 3 → F) := AddEquiv.ofBijective t₀ ht₀bij with ht
  have htt : ∀ w, t w = t₀ w := fun _ => rfl
  have htint : ∀ (g : SL3 F) w, t (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w) =
      ((θ g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ t w := fun g w => by
    rw [htt, htt, ht₀, hint]
  have hblock : ∀ i j, ∃ c : F, ∀ w, β i j w = t (c • w) := by
    intro i j
    let f : (Fin 3 → F) →+ (Fin 3 → F) :=
      (t.symm : (Fin 3 → F) →+ (Fin 3 → F)).comp (β i j)
    obtain ⟨c, hc⟩ := schur_W (f := f) (fun g w => by
      show t.symm (β i j _) = _ *ᵥ t.symm (β i j w)
      rw [hint]
      apply t.injective
      rw [AddEquiv.apply_symm_apply, htint, AddEquiv.apply_symm_apply])
    refine ⟨c, fun w => ?_⟩
    have := hc w
    rw [← this]
    show β i j w = t (t.symm (β i j w))
    rw [AddEquiv.apply_symm_apply]
  choose c hc using hblock
  refine ⟨t, Matrix.of c, htint, fun n i => ?_⟩
  rw [hsum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hc]
  rfl

theorem exists_semilinear [Finite F] (t : (Fin 3 → F) ≃+ (Fin 3 → F)) (θ : SL3 F → SL3 F)
    (ht : ∀ (g : SL3 F) w, t (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w) =
      ((θ g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ t w)
    (hθ : Function.Surjective θ) :
    ∃ σ : F ≃+* F, ∀ (μ : F) w, t (μ • w) = σ μ • t w := by
  have hs : ∀ μ : F, ∃ c : F, ∀ w, t (μ • t.symm w) = c • w := by
    intro μ
    let f : (Fin 3 → F) →+ (Fin 3 → F) :=
      { toFun := fun w => t (μ • t.symm w)
        map_zero' := by simp
        map_add' := fun x y => by simp [smul_add] }
    refine schur_W (f := f) fun g w => ?_
    obtain ⟨g', rfl⟩ := hθ g
    show t (μ • t.symm (_ *ᵥ w)) = _ *ᵥ t (μ • t.symm w)
    have e1 : t.symm (((θ g' : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w) =
        ((g' : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ t.symm w := by
      apply t.injective
      rw [AddEquiv.apply_symm_apply, ht, AddEquiv.apply_symm_apply]
    rw [e1, ← Matrix.mulVec_smul, ht]
  choose s hs using hs
  have hs' : ∀ μ w, t (μ • w) = s μ • t w := fun μ w => by
    have := hs μ (t w)
    rwa [AddEquiv.symm_apply_apply] at this
  have hw₁ : t (Pi.single 0 1) ≠ 0 := by
    intro h
    have h0 : t (Pi.single 0 1) = t 0 := by rw [h, map_zero]
    have := congrFun (t.injective h0) 0
    simp at this
  have hcancel : ∀ c d : F, c • t (Pi.single 0 1) = d • t (Pi.single 0 1) → c = d :=
    fun c d h => smul_left_injective F hw₁ h
  let σ₀ : F →+* F :=
    { toFun := s
      map_one' := hcancel _ _ (by rw [← hs', one_smul, one_smul])
      map_mul' := fun μ ν => hcancel _ _ (by rw [← hs', mul_smul, hs', hs', mul_smul])
      map_zero' := hcancel _ _ (by rw [← hs', zero_smul, zero_smul, map_zero])
      map_add' := fun μ ν => hcancel _ _ (by rw [← hs', add_smul, map_add, hs', hs', add_smul]) }
  have hbij : Function.Bijective σ₀ :=
    ⟨σ₀.injective, Finite.injective_iff_surjective.mp σ₀.injective⟩
  exact ⟨RingEquiv.ofBijective σ₀ hbij, fun μ w => hs' μ w⟩

theorem ringEquiv_eq_of_involutive [Finite F] [CharP F 2] {σ τ : F ≃+* F}
    (hσ : ∀ x, σ (σ x) = x) (hτ : ∀ x, τ (τ x) = x) (hσ1 : ∃ x, σ x ≠ x)
    (hτ1 : ∃ x, τ x ≠ x) : σ = τ := by
  classical
  let _ : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hmap : ∀ (ρ : F ≃+* F) (x : ZMod 2),
      ρ (algebraMap (ZMod 2) F x) = algebraMap (ZMod 2) F x := fun ρ x =>
    congrArg (fun f : ZMod 2 →+* F => f x)
      (Subsingleton.elim ((ρ : F →+* F).comp (algebraMap (ZMod 2) F)) (algebraMap (ZMod 2) F))
  let σ' : F ≃ₐ[ZMod 2] F := AlgEquiv.ofRingEquiv (f := σ) (hmap σ)
  let τ' : F ≃ₐ[ZMod 2] F := AlgEquiv.ofRingEquiv (f := τ) (hmap τ)
  have : Fintype (F ≃ₐ[ZMod 2] F) := Fintype.ofFinite _
  have hsq : ∀ (ρ : F ≃ₐ[ZMod 2] F), (∀ x, ρ (ρ x) = x) → ρ ^ 2 = 1 := fun ρ hρ => by
    ext x
    rw [pow_two, AlgEquiv.mul_apply, hρ]
    rfl
  have hne : ∀ (ρ : F ≃ₐ[ZMod 2] F), (∃ x, ρ x ≠ x) → ρ ≠ 1 := fun ρ ⟨x, hx⟩ h => by
    rw [h] at hx
    exact hx rfl
  have h1 : (1 : F ≃ₐ[ZMod 2] F) ^ 2 = 1 := one_pow 2
  have hσ' := hsq σ' hσ
  have hτ' := hsq τ' hτ
  have hσne := hne σ' hσ1
  have hτne := hne τ' hτ1
  by_contra hστ
  have hστ' : σ' ≠ τ' := fun h => hστ (by
    ext x
    have := congrArg (fun ρ : F ≃ₐ[ZMod 2] F => ρ x) h
    exact this)
  have hle := IsCyclic.card_pow_eq_one_le (α := F ≃ₐ[ZMod 2] F) (n := 2) (by norm_num)
  have hsub : ({1, σ', τ'} : Finset (F ≃ₐ[ZMod 2] F)) ⊆
      ({a | a ^ 2 = 1} : Finset (F ≃ₐ[ZMod 2] F)) := by
    intro ρ hρ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hρ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hρ with rfl | rfl | rfl
    · exact h1
    · exact hσ'
    · exact hτ'
  have hcard : ({1, σ', τ'} : Finset (F ≃ₐ[ZMod 2] F)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hστ']
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => hσne h.symm, fun h => hτne h.symm⟩
  have := (Finset.card_le_card hsub).trans hle
  omega

end CFSG.Quasithin.MS93.AS

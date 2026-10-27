module

public import CFSG.LocalAnalysis.StandardType.ZS.ImpExtAdapted
public import CFSG.LocalAnalysis.StandardType.ZS.ImpExtN4End
import CFSG.LocalAnalysis.StandardType.ZS.MonomialStab
import CFSG.LocalAnalysis.StandardType.ZS.MonomialCard
import CFSG.LocalAnalysis.StandardType.ZS.MonomialBasic
import CFSG.LocalAnalysis.StandardType.ZS.ExcMatricesRefl

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

namespace ImpExtStd

variable [Module.Finite (ZMod p) U] {G H : Subgroup (U ≃ₗ[ZMod p] U)} {d : ℕ}
  {e : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
    (HardMathSupport.Kantor79.commutatorSpace H)}
  {j₀ j₁ : Fin (Module.finrank (ZMod p) U - 1)} {ζ : (ZMod p)ˣ}

private instance zsnc_finite_linearEquiv : Finite (U ≃ₗ[ZMod p] U) := by
  have hU : Finite U := Module.finite_of_finite (ZMod p)
  exact Finite.of_injective (fun e : U ≃ₗ[ZMod p] U => (e : U → U))
    (fun _ _ h => LinearEquiv.ext (congrFun h))

omit [Module.Finite (ZMod p) U] in
private theorem zsnc_diagSign_action {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    {i : Fin n} {g : U ≃ₗ[ZMod p] U}
    (hg : LinearMap.toMatrix f f g.toLinearMap = diagSignMat i) (c : Fin n) :
    g (f c) = (if c = i then (-1 : ZMod p) else 1) • f c := by
  change g.toLinearMap (f c) = (if c = i then (-1 : ZMod p) else 1) • f c
  rw [show g.toLinearMap (f c) = ∑ k, diagSignMat i k c • f k from by
      rw [← Matrix.toLin_toMatrix f f g.toLinearMap, hg, Matrix.toLin_self],
    Finset.sum_eq_single c]
  · simp [diagSignMat]
  · intro k _ hkc; simp [diagSignMat, hkc]
  · intro hc; exact absurd (Finset.mem_univ c) hc

omit [Module.Finite (ZMod p) U] in
private theorem zsnc_smul_index_eq {n : ℕ} (e : Module.Basis (Fin n) (ZMod p) U)
    {c c' : ZMod p} (hc : c ≠ 0) {j j' : Fin n} (h : c • e j = c' • e j') : j = j' := by
  by_contra hne
  have h1 := congrArg (fun w => e.repr w j) h
  simp only [map_smul, Finsupp.smul_apply, e.repr_self, Finsupp.single_apply, smul_eq_mul] at h1
  rw [if_neg (Ne.symm hne)] at h1
  simp at h1
  exact hc h1

omit [Module.Finite (ZMod p) U] in
private theorem zsnc_smul_coeff_eq {n : ℕ} (e : Module.Basis (Fin n) (ZMod p) U)
    {j : Fin n} {c c' : ZMod p} (h : c • e j = c' • e j) : c = c' := by
  have h1 := congrArg (fun w => e.repr w j) h
  simpa [map_smul, Finsupp.smul_apply, e.repr_self, Finsupp.single_apply, smul_eq_mul] using h1

omit [Module.Finite (ZMod p) U] in
private theorem zsnc_reflGen_closure_insert {H : Subgroup (U ≃ₗ[ZMod p] U)}
    {g : U ≃ₗ[ZMod p] U} (hH : ReflGen p H) (hg : IsRefl p g) :
    ReflGen p (Subgroup.closure (insert g (H : Set (U ≃ₗ[ZMod p] U)))) := by
  let X : Subgroup (U ≃ₗ[ZMod p] U) := Subgroup.closure (insert g (H : Set (U ≃ₗ[ZMod p] U)))
  change ReflGen p X
  have hgX : g ∈ X := Subgroup.subset_closure (Set.mem_insert g _)
  have hHX : H ≤ X := fun h hh => Subgroup.subset_closure (Set.mem_insert_of_mem g hh)
  have hSH : H ≤ Subgroup.closure {t : U ≃ₗ[ZMod p] U | t ∈ X ∧ IsRefl p t} := by
    rw [hH]
    refine (Subgroup.closure_le _).mpr ?_
    rintro t ⟨htH, htr⟩
    exact Subgroup.subset_closure ⟨hHX htH, htr⟩
  change X = Subgroup.closure {t : U ≃ₗ[ZMod p] U | t ∈ X ∧ IsRefl p t}
  refine le_antisymm ?_ ((Subgroup.closure_le _).mpr fun _ hx => hx.1)
  change Subgroup.closure (insert g (H : Set (U ≃ₗ[ZMod p] U))) ≤ _
  refine (Subgroup.closure_le _).mpr ?_
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hxH
  · exact Subgroup.subset_closure ⟨hgX, hg⟩
  · exact hSH hxH

omit [Module.Finite (ZMod p) U] in
private theorem zsnc_commutatorSpace_mono {H K : Subgroup (U ≃ₗ[ZMod p] U)} (h : H ≤ K) :
    HardMathSupport.Kantor79.commutatorSpace H ≤ HardMathSupport.Kantor79.commutatorSpace K := by
  rw [HardMathSupport.Kantor79.commutatorSpace, Submodule.span_le]
  rintro w ⟨g, hg, v, rfl⟩
  exact Submodule.subset_span ⟨g, h hg, v, rfl⟩

private def zsnc_trivialModulo (W : Submodule (ZMod p) U) : Subgroup (U ≃ₗ[ZMod p] U) where
  carrier := {g | ∀ v : U, g v - v ∈ W}
  mul_mem' := by
    intro a b ha hb v
    have h1 : a (b v) - b v ∈ W := ha (b v)
    have h2 : b v - v ∈ W := hb v
    have h3 : (a * b) v - v = (a (b v) - b v) + (b v - v) := by
      rw [LinearEquiv.mul_apply]; abel
    rw [h3]; exact W.add_mem h1 h2
  one_mem' := by intro v; simp
  inv_mem' := by
    intro a ha v
    have h1 : a (a⁻¹ v) - a⁻¹ v ∈ W := ha (a⁻¹ v)
    have h2 : a (a⁻¹ v) = v := by simp
    rw [h2] at h1
    have h3 : a⁻¹ v - v = -(v - a⁻¹ v) := by abel
    rw [h3]; exact W.neg_mem h1

omit [Module.Finite (ZMod p) U] in
private theorem zsnc_toMatrix_unitsSMul_diagSign {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    (w : Fin n → (ZMod p)ˣ) {i : Fin n} {g : U ≃ₗ[ZMod p] U}
    (hg : LinearMap.toMatrix f f g.toLinearMap = diagSignMat i) :
    LinearMap.toMatrix (f.unitsSMul w) (f.unitsSMul w) g.toLinearMap = diagSignMat i := by
  ext r c
  rw [toMatrix_unitsSMul_apply, hg]
  by_cases hrc : r = c
  · subst hrc
    rw [diagSignMat, Matrix.diagonal_apply_eq, Units.val_inv_eq_inv_val]
    rw [mul_assoc, mul_comm (if r = i then (-1 : ZMod p) else 1) (w r), ← mul_assoc,
      inv_mul_cancel₀ (w r).ne_zero, one_mul]
  · rw [diagSignMat, Matrix.diagonal_apply_ne _ hrc]
    rw [mul_zero, zero_mul]

private theorem zsnc_diagSign_two_sq :
    (diagSignMat 2 : Matrix (Fin 4) (Fin 4) (ZMod p)) * diagSignMat 2 = 1 := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, diagSignMat]

private theorem zsnc_diagSign_two_det :
    IsUnit (diagSignMat 2 : Matrix (Fin 4) (Fin 4) (ZMod p)).det :=
  isUnit_iff_exists.mpr ⟨_, by rw [← Matrix.det_mul, zsnc_diagSign_two_sq, Matrix.det_one],
    by rw [← Matrix.det_mul, zsnc_diagSign_two_sq, Matrix.det_one]⟩

omit [Module.Finite (ZMod p) U] in
private theorem zsnc_card_le_of_mono (hp : p ≠ 2) (S : ImpExtStd G H d e j₀ j₁ ζ)
    (hn : Module.finrank (ZMod p) U = 4) (hζ : orderOf ζ = 4) : Nat.card H ≤ 192 := by
  rw [← card_movedGroup_of_splitSupport S.splitSupport]
  have hn2 : 2 ≤ Module.finrank (ZMod p) U - 1 := by omega
  have hfr : Module.finrank (ZMod p) U - 1 = 3 := by omega
  rcases S.mono with h | h
  · rw [h, card_gmmn (n := Module.finrank (ZMod p) U - 1) hn2 e S.ne ζ, hζ, hfr]
    norm_num
  · rw [h, card_g2mmn hp (n := Module.finrank (ZMod p) U - 1) hn2 e S.ne ζ, hζ, hfr]
    norm_num

omit [Module.Finite (ZMod p) U] in
private theorem zsnc_false_of_units_prod (hp : p ≠ 2)
    {σ : Fin 3 ≃ Fin (Module.finrank (ZMod p) U - 1)}
    {d : Fin (Module.finrank (ZMod p) U - 1) → (ZMod p)ˣ}
    (hprod : ∏ k, d k = 1)
    (hdval : ∀ i : Fin 3, d (σ i) =
      (if (i.castSucc : Fin 4) = 2 then (-1 : (ZMod p)ˣ) else 1)) : False := by
  have hreindex : (∏ k : Fin (Module.finrank (ZMod p) U - 1), d k) =
      ∏ i : Fin 3, d (σ i) :=
    Fintype.prod_equiv σ.symm d (fun i => d (σ i)) (fun _ => by simp)
  have hprod1 : (∏ i : Fin 3,
      (if (i.castSucc : Fin 4) = 2 then (-1 : (ZMod p)ˣ) else 1)) = 1 := by
    have h2 : (∏ i : Fin 3, d (σ i)) = 1 := by rw [← hreindex]; exact hprod
    calc (∏ i : Fin 3, (if (i.castSucc : Fin 4) = 2 then (-1 : (ZMod p)ˣ) else 1))
        = ∏ i : Fin 3, d (σ i) := Finset.prod_congr rfl (fun i _ => (hdval i).symm)
      _ = 1 := h2
  have h2' : (2 : Fin 3).castSucc = (2 : Fin 4) := by simp
  have hprod2 : (∏ i : Fin 3,
      (if (i.castSucc : Fin 4) = 2 then (-1 : (ZMod p)ˣ) else 1)) = -1 := by
    rw [Fin.prod_univ_three]
    simp [h2']
  have hneg1 : (-1 : (ZMod p)ˣ) = 1 := hprod2.symm.trans hprod1
  have htwo : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hneg : (-1 : ZMod p) ≠ 1 := by
    intro h
    apply htwo
    rw [show (2 : ZMod p) = 1 + 1 by norm_num]
    exact neg_eq_iff_add_eq_zero.mp h
  exact hneg (by simpa using congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hneg1)

omit [Module.Finite (ZMod p) U] in
private theorem zsnc_false_of_normalForm (hp : p ≠ 2)
    {H : Subgroup (U ≃ₗ[ZMod p] U)}
    {e : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H)}
    {d : Fin (Module.finrank (ZMod p) U - 1) → (ZMod p)ˣ}
    {τ : Equiv.Perm (Fin (Module.finrank (ZMod p) U - 1))}
    (hprod : ∏ k, d k = 1)
    {R : HardMathSupport.Kantor79.commutatorSpace H ≃ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace H}
    (haeq : R = diagMap p e d * permMap p e τ)
    (σ : Fin 3 ≃ Fin (Module.finrank (ZMod p) U - 1))
    (hRact : ∀ i : Fin 3, R (e (σ i)) =
      (if (i.castSucc : Fin 4) = 2 then (-1 : ZMod p) else 1) • e (σ i)) : False := by
  have hsi : ∀ i : Fin 3, (d (τ (σ i)) : ZMod p) • e (τ (σ i)) =
      (if (i.castSucc : Fin 4) = 2 then (-1 : ZMod p) else 1) • e (σ i) := by
    intro i
    rw [← hRact i, haeq, LinearEquiv.mul_apply, permMap_apply_basis, diagMap_apply_basis]
  have hidx : ∀ i : Fin 3, τ (σ i) = σ i := fun i =>
    zsnc_smul_index_eq e (d (τ (σ i))).ne_zero (hsi i)
  have hdval : ∀ i : Fin 3, d (σ i) =
      (if (i.castSucc : Fin 4) = 2 then (-1 : (ZMod p)ˣ) else 1) := by
    intro i
    apply Units.ext
    have h := hsi i
    rw [hidx i] at h
    rw [apply_ite (fun u : (ZMod p)ˣ => (u : ZMod p)), Units.val_neg, Units.val_one]
    exact zsnc_smul_coeff_eq e h
  exact zsnc_false_of_units_prod hp hprod hdval

omit [Module.Finite (ZMod p) U] in
private theorem zsnc_false_of_mem_gmmn_diagSign (hp : p ≠ 2)
    {H : Subgroup (U ≃ₗ[ZMod p] U)}
    {e : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H)}
    {j₀ j₁ : Fin (Module.finrank (ZMod p) U - 1)} {ζ : (ZMod p)ˣ} (hne : j₀ ≠ j₁)
    (hH : movedGroup H = gmmn p e j₀ j₁ ζ) {f : Module.Basis (Fin 4) (ZMod p) U}
    (hf : AdaptedBasis H e f) {r : U ≃ₗ[ZMod p] U} (hrH : r ∈ H)
    (hrm : LinearMap.toMatrix f f r.toLinearMap = diagSignMat 2) : False := by
  let V := HardMathSupport.Kantor79.commutatorSpace H
  let φ := restrictHom H V (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
  have hRmem : φ ⟨r, hrH⟩ ∈ gmmn p e j₀ j₁ ζ := by
    rw [← hH]
    exact ⟨⟨r, hrH⟩, rfl⟩
  obtain ⟨d, τ, _hd, hprod, haeq⟩ :=
    exists_eq_diagMap_mul_permMap_of_mem_gmmn e hne hRmem
  obtain ⟨σ, hσ⟩ := hf.1
  choose x hx using hσ
  have hx' : ∀ i : Fin 3, f i.castSucc = (x i : ZMod p) • (e (σ i) : U) :=
    fun i => by simpa [Units.smul_def] using hx i
  have hactU : ∀ c : Fin 4, r (f c) = (if c = 2 then (-1 : ZMod p) else 1) • f c :=
    fun c => zsnc_diagSign_action f hrm c
  have hRact : ∀ i : Fin 3, φ ⟨r, hrH⟩ (e (σ i)) =
      (if (i.castSucc : Fin 4) = 2 then (-1 : ZMod p) else 1) • e (σ i) := by
    intro i
    have heqU : r ((e (σ i) : U)) =
        (if (i.castSucc : Fin 4) = 2 then (-1 : ZMod p) else 1) • (e (σ i) : U) := by
      have h1 : r (f i.castSucc) =
          (if (i.castSucc : Fin 4) = 2 then (-1 : ZMod p) else 1) • f i.castSucc :=
        hactU i.castSucc
      have hcomm : (if (i.castSucc : Fin 4) = 2 then (-1 : ZMod p) else 1) •
          ((x i : ZMod p) • (e (σ i) : U)) =
          (x i : ZMod p) • ((if (i.castSucc : Fin 4) = 2 then (-1 : ZMod p) else 1) •
            (e (σ i) : U)) := by
        rw [smul_smul, smul_smul, mul_comm]
      rw [hx' i, map_smul, hcomm] at h1
      exact (IsUnit.smul_left_cancel (x i).isUnit).mp h1
    have hcoe : ((φ ⟨r, hrH⟩ (e (σ i)) : V) : U) = r ((e (σ i) : U)) := by
      dsimp only [φ]
      rw [restrictHom_apply]
    apply Subtype.ext
    rw [Submodule.coe_smul]
    exact hcoe.trans heqU
  exact zsnc_false_of_normalForm hp hprod haeq σ hRact

omit [Module.Finite (ZMod p) U] in
private theorem zsnc_span_castSucc {H : Subgroup (U ≃ₗ[ZMod p] U)}
    {e : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H)}
    {f : Module.Basis (Fin 4) (ZMod p) U}
    {σ : Fin 3 ≃ Fin (Module.finrank (ZMod p) U - 1)}
    (hf : ∀ i : Fin 3, f i.castSucc = e (σ i)) :
    Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) =
      HardMathSupport.Kantor79.commutatorSpace H := by
  have hrange : Set.range (fun i : Fin 3 => f i.castSucc) =
      Set.range (fun j : Fin (Module.finrank (ZMod p) U - 1) => (e j : U)) := by
    ext w; constructor
    · rintro ⟨i, rfl⟩; exact ⟨σ i, (hf i).symm⟩
    · rintro ⟨j, rfl⟩
      exact ⟨σ.symm j, by
        change f (σ.symm j).castSucc = (e j : U)
        rw [hf (σ.symm j), Equiv.apply_symm_apply]⟩
  have hrangeE : Set.range (fun j : Fin (Module.finrank (ZMod p) U - 1) => (e j : U)) =
      (HardMathSupport.Kantor79.commutatorSpace H).subtype '' Set.range e := by
    ext w; constructor
    · rintro ⟨j, rfl⟩; exact ⟨e j, ⟨j, rfl⟩, rfl⟩
    · rintro ⟨v, ⟨j, rfl⟩, rfl⟩; exact ⟨j, rfl⟩
  rw [hrange, hrangeE, ← Submodule.map_span, e.span_eq, Submodule.map_top,
    Submodule.range_subtype]

theorem exists_nFourData (hp : p ≠ 2) (S : ImpExtStd G H d e j₀ j₁ ζ)
    (hn : Module.finrank (ZMod p) U = 4) (hζ : orderOf ζ = 4) :
    ∃ (f : Module.Basis (Fin 4) (ZMod p) U) (t : ZMod p) (a b c x : U ≃ₗ[ZMod p] U),
      AdaptedBasis H e f ∧ NFourData f t a b c x G ∧ (movedGroup H = g2mmn p e j₀ j₁ ζ →
        ∃ r ∈ G, LinearMap.toMatrix f f r.toLinearMap = diagSignMat 2) := by
  obtain ⟨f, σ, hσ₀, hσ₁, hf, hf₃⟩ := exists_basis_castSucc S hn
  have hadapted : AdaptedBasis H e f := by
    refine ⟨⟨σ, fun i => ⟨1, ?_⟩⟩, hf₃⟩
    simpa using hf i
  obtain ⟨t, a, b, c, ht, ha, hb, hc, haM, hbM, hcM, hdiag⟩ :=
    exists_mem_toMatrix_pijMat hp S hζ hσ₀ hσ₁ hf hf₃
  have hmono : ∀ h ∈ H, IsMonomialIn f h := fun h hh => isMonomialIn_of_mem S hadapted hh
  obtain ⟨x, hxG, hxrefl, hxnotmono, hxnotle⟩ :=
    ImpExtSetting.exists_isRefl_not_isMonomialIn_not_le S.toImpExtSetting f hmono
  have hspan : Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) =
      HardMathSupport.Kantor79.commutatorSpace H := zsnc_span_castSucc hf
  have hcardH : Nat.card H ≤ 192 := zsnc_card_le_of_mono hp S hn hζ
  refine ⟨f, t, a, b, c, x, hadapted, ?_, ?_⟩
  · refine ⟨ht, haM, hbM, hcM, S.H_le ha, S.H_le hb, S.H_le hc, hxG, hxrefl, hxnotmono, ?_,
      S.transvectionFree, ?_, ?_⟩
    · rw [hspan]; exact hxnotle
    · rw [← dmax_eq_four hp S hζ]; exact S.dmax
    · intro X hXG hXrefl hXsplit hd
      have hfr : Module.finrank (ZMod p) U - 1 = 3 := by omega
      have hsplit' : SplitSupport X (Module.finrank (ZMod p) U - 1) := by rwa [hfr]
      have hcardXH : Nat.card X ≤ Nat.card H :=
        ImpExtSetting.card_le_of_orderOf S.toImpExtSetting hXG hXrefl hsplit' ?_
      · intro h336; omega
      · obtain ⟨u, huX, v, hvX, hur, hvr, huv⟩ := hd
        exact ⟨u, huX, v, hvX, hur, hvr, by rw [huv, dmax_eq_four hp S hζ]⟩
  · intro hh
    obtain ⟨r, hrH, hrM⟩ := hdiag hh
    exact ⟨r, S.H_le hrH, hrM⟩

omit [Module.Finite (ZMod p) U] in
private theorem zsnc_movedSpace_le {H : Subgroup (U ≃ₗ[ZMod p] U)}
    {e : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H)}
    {f : Module.Basis (Fin 4) (ZMod p) U} (hf : AdaptedBasis H e f)
    {r : U ≃ₗ[ZMod p] U} (hrm : LinearMap.toMatrix f f r.toLinearMap = diagSignMat 2) :
    HardMathSupport.Kantor79.movedSpace r ≤
      HardMathSupport.Kantor79.commutatorSpace H := by
  obtain ⟨σ, hσ⟩ := hf.1
  have hf2 : f 2 ∈ HardMathSupport.Kantor79.commutatorSpace H := by
    obtain ⟨c, hc⟩ := hσ 2
    have hc' : f (2 : Fin 4) = (c : ZMod p) • (e (σ 2) : U) := by
      simpa [Units.smul_def] using hc
    rw [hc']
    exact Submodule.smul_mem _ _ (e (σ 2)).2
  rw [HardMathSupport.Kantor79.movedSpace]
  rw [← Submodule.map_top ((r : U →ₗ[ZMod p] U) - 1), ← f.span_eq, Submodule.map_span,
    Submodule.span_le]
  rintro w ⟨u, hu, rfl⟩
  obtain ⟨c, rfl⟩ := hu
  have hact : (r : U →ₗ[ZMod p] U) (f c) = (if c = 2 then (-1 : ZMod p) else 1) • f c :=
    zsnc_diagSign_action f hrm c
  rw [LinearMap.sub_apply]
  change (r : U →ₗ[ZMod p] U) (f c) - f c ∈ HardMathSupport.Kantor79.commutatorSpace H
  rw [hact]
  by_cases hc2 : c = 2
  · subst hc2
    simpa using (HardMathSupport.Kantor79.commutatorSpace H).sub_mem
      ((HardMathSupport.Kantor79.commutatorSpace H).smul_mem (-1) hf2) hf2
  · rw [if_neg hc2]; simp

omit [Module.Finite (ZMod p) U] in
private theorem zsnc_commutatorSpace_closure_eq {H : Subgroup (U ≃ₗ[ZMod p] U)}
    {e : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H)}
    {f : Module.Basis (Fin 4) (ZMod p) U} (hf : AdaptedBasis H e f)
    {r : U ≃ₗ[ZMod p] U} (hrm : LinearMap.toMatrix f f r.toLinearMap = diagSignMat 2) :
    HardMathSupport.Kantor79.commutatorSpace
        (Subgroup.closure (insert r (H : Set (U ≃ₗ[ZMod p] U)))) =
      HardMathSupport.Kantor79.commutatorSpace H := by
  have hHleX : H ≤ Subgroup.closure (insert r (H : Set (U ≃ₗ[ZMod p] U))) :=
    fun h hh => Subgroup.subset_closure (Set.mem_insert_of_mem r hh)
  have hrP : r ∈ zsnc_trivialModulo (HardMathSupport.Kantor79.commutatorSpace H) :=
    fun v => zsnc_movedSpace_le hf hrm ⟨v, rfl⟩
  have hVXle : HardMathSupport.Kantor79.commutatorSpace
      (Subgroup.closure (insert r (H : Set (U ≃ₗ[ZMod p] U)))) ≤
      HardMathSupport.Kantor79.commutatorSpace H := by
    rw [commutatorSpace_le_iff]
    intro g hg v
    have hPX : Subgroup.closure (insert r (H : Set (U ≃ₗ[ZMod p] U))) ≤
        zsnc_trivialModulo (HardMathSupport.Kantor79.commutatorSpace H) := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro u (rfl | huH)
      · exact hrP
      · exact fun w => (commutatorSpace_le_iff.mp le_rfl) u huH w
    exact hPX hg v
  exact le_antisymm hVXle (zsnc_commutatorSpace_mono hHleX)

private theorem zsnc_centralizerSpace_closure_eq (S : ImpExtStd G H d e j₀ j₁ ζ)
    {f : Module.Basis (Fin 4) (ZMod p) U} (hf : AdaptedBasis H e f)
    {r : U ≃ₗ[ZMod p] U} (hrm : LinearMap.toMatrix f f r.toLinearMap = diagSignMat 2) :
    centralizerSpace (Subgroup.closure (insert r (H : Set (U ≃ₗ[ZMod p] U)))) =
      centralizerSpace H := by
  have hVH : centralizerSpace H = Submodule.span (ZMod p) {f 3} := by
    refine (Submodule.eq_of_le_of_finrank_eq
      ((Submodule.span_singleton_le_iff_mem _ _).mpr hf.2) ?_).symm
    rw [ImpExtSetting.finrank_centralizerSpace S.toImpExtSetting,
      finrank_span_singleton (f.ne_zero 3)]
  apply le_antisymm
  · intro v hv
    rw [mem_centralizerSpace] at hv ⊢
    intro h hh
    exact hv h (Subgroup.subset_closure (Set.mem_insert_of_mem r hh))
  · intro v hv
    have hrv : r v = v := by
      have hv' : v ∈ centralizerSpace H := hv
      rw [hVH] at hv'
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv'
      rw [← hc, map_smul, zsnc_diagSign_action f hrm 3,
        if_neg (by simp [Fin.ext_iff]), one_smul]
    rw [mem_centralizerSpace] at hv ⊢
    intro g hg
    have hfix : ∀ g ∈ Subgroup.closure (insert r (H : Set (U ≃ₗ[ZMod p] U))), g v = v := by
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem y hy =>
          rcases Set.mem_insert_iff.mp hy with rfl | hyH
          · exact hrv
          · exact hv y hyH
      | one => rfl
      | mul a b ha hb iha ihb => rw [LinearEquiv.mul_apply, ihb, iha]
      | inv a ha iha =>
          calc a⁻¹ v = a⁻¹ (a v) := by rw [iha]
            _ = v := LinearEquiv.symm_apply_apply a v
    exact hfix g hg

theorem false_of_diagSign_mem (hp : p ≠ 2) (S : ImpExtStd G H d e j₀ j₁ ζ)
    (hH : movedGroup H = gmmn p e j₀ j₁ ζ)
    {f : Module.Basis (Fin 4) (ZMod p) U} (hf : AdaptedBasis H e f) {r : U ≃ₗ[ZMod p] U}
    (hr : r ∈ G) (hrm : LinearMap.toMatrix f f r.toLinearMap = diagSignMat 2) : False := by
  have hrrefl : IsRefl p r := isRefl_of_toMatrix_eq_diagSignMat hp f hrm
  have hHleX : H ≤ Subgroup.closure (insert r (H : Set (U ≃ₗ[ZMod p] U))) :=
    fun h hh => Subgroup.subset_closure (Set.mem_insert_of_mem r hh)
  have hrX : r ∈ Subgroup.closure (insert r (H : Set (U ≃ₗ[ZMod p] U))) :=
    Subgroup.subset_closure (Set.mem_insert r (H : Set (U ≃ₗ[ZMod p] U)))
  have hXrefl : ReflGen p (Subgroup.closure (insert r (H : Set (U ≃ₗ[ZMod p] U)))) :=
    zsnc_reflGen_closure_insert S.reflGen_H hrrefl
  have hXG : Subgroup.closure (insert r (H : Set (U ≃ₗ[ZMod p] U))) ≤ G := by
    rw [Subgroup.closure_le]
    rintro g (rfl | hg)
    · exact hr
    · exact S.H_le hg
  have hVX := zsnc_commutatorSpace_closure_eq hf hrm
  have hCX := zsnc_centralizerSpace_closure_eq S hf hrm
  have hsplitX : SplitSupport (Subgroup.closure (insert r (H : Set (U ≃ₗ[ZMod p] U))))
      (Module.finrank (ZMod p) U - 1) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hVX, hCX]; exact S.splitSupport.1
    · rw [hVX]; exact S.splitSupport.2.1
    · intro W hbot hWle hWin
      rw [hVX] at hWle ⊢
      exact S.splitSupport.2.2 W hbot hWle (fun h hh w hw => hWin h (hHleX hh) w hw)
  have hcardXH : Nat.card (Subgroup.closure (insert r (H : Set (U ≃ₗ[ZMod p] U)))) ≤
      Nat.card H :=
    ImpExtSetting.card_le_of_orderOf S.toImpExtSetting hXG hXrefl hsplitX
      (by obtain ⟨u, huH, v, hvH, hur, hvr, huv⟩ := S.dmax_H.2
          exact ⟨u, hHleX huH, v, hHleX hvH, hur, hvr, huv⟩)
  have hHX : H = Subgroup.closure (insert r (H : Set (U ≃ₗ[ZMod p] U))) :=
    Subgroup.eq_of_le_of_card_ge hHleX hcardXH
  have hrH : r ∈ H := by rw [hHX]; exact hrX
  exact zsnc_false_of_mem_gmmn_diagSign hp S.ne hH hf hrH hrm

theorem eq_weylN4 (hp : p ≠ 2) (S : ImpExtStd G H d e j₀ j₁ ζ)
    (hn : Module.finrank (ZMod p) U = 4) (hζ : orderOf ζ = 4)
    (hH : movedGroup H = gmmn p e j₀ j₁ ζ) :
    ∃ (f : Module.Basis (Fin 4) (ZMod p) U) (t : ZMod p), t ^ 2 = -1 ∧
      G = basisClosure f (weylN4Mats t) := by
  obtain ⟨f, t, a, b, c, x, hf, hData, _hdiag⟩ := exists_nFourData hp S hn hζ
  obtain ⟨w, t', a', c', d', _hcase, h', hd'⟩ := NFourData.exists_basis_halfOnes hp hData
  rcases NFourData.eq_weylN4_or_eq_weylEN4 hp h' hd' S.reflGen with hN4 | hEN4
  · exact ⟨f.unitsSMul w, t', h'.sq_t, hN4⟩
  · exfalso
    have hrcl : Matrix.toLinearEquiv (f.unitsSMul w)
        (diagSignMat 2) zsnc_diagSign_two_det ∈ basisClosure (f.unitsSMul w) (weylEN4Mats t') := by
      refine mem_weylEN4_of_toMatrix_diagSign hp (f.unitsSMul w) h'.sq_t ?_
      show LinearMap.toMatrix (f.unitsSMul w) (f.unitsSMul w)
        (Matrix.toLin (f.unitsSMul w) (f.unitsSMul w) (diagSignMat 2)) = diagSignMat 2
      rw [LinearMap.toMatrix_toLin]
    have hrG : Matrix.toLinearEquiv (f.unitsSMul w) (diagSignMat 2) zsnc_diagSign_two_det ∈ G := by
      rw [hEN4]; exact hrcl
    exact false_of_diagSign_mem hp S hH (hf.unitsSMul w) hrG
      (by
        show LinearMap.toMatrix (f.unitsSMul w) (f.unitsSMul w)
          (Matrix.toLin (f.unitsSMul w) (f.unitsSMul w) (diagSignMat 2)) = diagSignMat 2
        rw [LinearMap.toMatrix_toLin])

theorem eq_weylEN4 (hp : p ≠ 2) (S : ImpExtStd G H d e j₀ j₁ ζ)
    (hn : Module.finrank (ZMod p) U = 4) (hζ : orderOf ζ = 4)
    (hH : movedGroup H = g2mmn p e j₀ j₁ ζ) :
    ∃ (f : Module.Basis (Fin 4) (ZMod p) U) (t : ZMod p), t ^ 2 = -1 ∧
      G = basisClosure f (weylEN4Mats t) := by
  obtain ⟨f, t, a, b, c, x, hf, hData, hdiag⟩ := exists_nFourData hp S hn hζ
  obtain ⟨r, hrG, hrm⟩ := hdiag hH
  obtain ⟨w, t', a', c', d', _hcase, h', hd'⟩ := NFourData.exists_basis_halfOnes hp hData
  have hrm' : LinearMap.toMatrix (f.unitsSMul w) (f.unitsSMul w) r.toLinearMap = diagSignMat 2 :=
    zsnc_toMatrix_unitsSMul_diagSign f w hrm
  have hle : G ≤ basisClosure (f.unitsSMul w) (weylEN4Mats t') :=
    NFourData.le_weylEN4 hp h' hd' S.reflGen
  have hN : basisClosure (f.unitsSMul w) (weylN4Mats t') ≤ G := NFourData.weylN4_le h' hd'
  have hle' : basisClosure (f.unitsSMul w) (weylEN4Mats t') ≤ G :=
    weylEN4_le_of_diagSign_mem hp (f.unitsSMul w) h'.sq_t hN hrG hrm'
  exact ⟨f.unitsSMul w, t', h'.sq_t, le_antisymm hle hle'⟩

end ImpExtStd

end CFSG.StandardType.ZS

end

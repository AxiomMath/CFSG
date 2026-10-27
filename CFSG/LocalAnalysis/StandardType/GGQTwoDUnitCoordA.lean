module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBase
public import CFSG.LocalAnalysis.StandardType.GGQTwoDCoxEven
import CFSG.LocalAnalysis.StandardType.GGQTwoDFrameModule
import CFSG.LocalAnalysis.StandardType.GGQTwoDFrameCfg
import CFSG.LocalAnalysis.StandardType.GGQTwoDFrameMain
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitCoordStd

public section

namespace CFSG.StandardType.QTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn.QTwo

open scoped Matrix

variable {G : Type} [Group G] [Finite G]

section InducedDiagonal

variable {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {m : ℕ}
  {ψ : Su F0 2 1 m →* G}

theorem qtwoDB19_diag_mul (c c' : Fin m → F0ˣ) :
    qTwoChartTwoThree_diag (c * c') =
      qTwoChartTwoThree_diag c * qTwoChartTwoThree_diag c' := by
  apply Units.ext
  simp only [Units.val_mul, qTwoChartTwoThree_diag]
  rw [Matrix.diagonal_mul_diagonal]
  congr 1

theorem qtwoDB19_diag_one :
    qTwoChartTwoThree_diag (1 : Fin m → F0ˣ) = 1 := by
  apply Units.ext
  simp only [Units.val_one, qTwoChartTwoThree_diag]
  rw [← Matrix.diagonal_one]
  congr 1

theorem qtwoDB19_diag_inv (c : Fin m → F0ˣ) :
    qTwoChartTwoThree_diag c⁻¹ = (qTwoChartTwoThree_diag c)⁻¹ := by
  have h : qTwoChartTwoThree_diag c * qTwoChartTwoThree_diag c⁻¹ = 1 := by
    rw [← qtwoDB19_diag_mul, mul_inv_cancel, qtwoDB19_diag_one]
  exact eq_inv_of_mul_eq_one_right h

theorem qtwoDB19_induces_mul {b₁ b₂ : G} {c₁ c₂ : Fin m → F0ˣ}
    (h₁ : qTwoChartTwoThree_induces ψ b₁ c₁) (h₂ : qTwoChartTwoThree_induces ψ b₂ c₂) :
    qTwoChartTwoThree_induces ψ (b₁ * b₂) (c₁ * c₂) := by
  intro u
  obtain ⟨u₂, hu₂, hψ₂⟩ := h₂ u
  obtain ⟨u₁, hu₁, hψ₁⟩ := h₁ u₂
  refine ⟨u₁, ?_, ?_⟩
  · rw [hu₁, hu₂, qtwoDB19_diag_mul]
    group
  · rw [hψ₁, hψ₂]
    group

theorem qtwoDB19_induces_inv (hF0 : Nat.card F0 = 4) {b : G} {c : Fin m → F0ˣ}
    (h : qTwoChartTwoThree_induces ψ b c) :
    qTwoChartTwoThree_induces ψ b⁻¹ c⁻¹ := by
  intro v
  obtain ⟨v', hv'⟩ := qTwoChartTwoThree_diag_conj_mem (F0 := F0) hF0 c⁻¹ v
  obtain ⟨w, hw, hwψ⟩ := h v'
  have hwv : w = v := by
    apply Subtype.ext
    rw [hw, hv', qtwoDB19_diag_inv]
    group
  refine ⟨v', ?_, ?_⟩
  · rw [hv', qtwoDB19_diag_inv]
  · rw [← hwv, hwψ]
    group

theorem qtwoDB19_unit_sq_eq_one (hF0 : Nat.card F0 = 4) {x : F0ˣ} (hx : x * x = 1) :
    x = 1 := by
  have hcard : Nat.card F0ˣ = 3 := by rw [Nat.card_units F0, hF0]
  have h2 : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rwa [pow_two])
  have h3 : orderOf x ∣ 3 := by rw [← hcard]; exact orderOf_dvd_natCard x
  have h1 : orderOf x = 1 := Nat.dvd_one.mp (by
    have h := Nat.dvd_gcd h2 h3
    rwa [show Nat.gcd 2 3 = 1 from rfl] at h)
  exact orderOf_eq_one_iff.mp h1

theorem qtwoDB19_diag_apply_eq_of_comm {e : Fin m → F0} {σ : Equiv.Perm (Fin m)}
    {P : Matrix (Fin m) (Fin m) F0} (hP : ∀ i, P *ᵥ Pi.single i 1 = Pi.single (σ i) 1)
    (h : Matrix.diagonal e * P = P * Matrix.diagonal e) (i : Fin m) : e (σ i) = e i := by
  have h1 : P (σ i) i = 1 := by
    have := congrFun (hP i) (σ i)
    rw [Matrix.mulVec_single_one] at this
    simpa using this
  have h2 := congrFun (congrFun h (σ i)) i
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at h2
  rw [h1] at h2
  simpa using h2

theorem qtwoDB19_induces_one_const (hF0 : Nat.card F0 = 4)
    (hker : ψ.ker ≤ Subgroup.center (Su F0 2 1 m)) (hm : 3 ≤ m) {c : Fin m → F0ˣ}
    (h : qTwoChartTwoThree_induces ψ (1 : G) c) : ∃ lam : F0ˣ, ∀ i, c i = lam := by
  classical
  let i0 : Fin m := ⟨0, by omega⟩
  refine ⟨c i0, fun i => ?_⟩
  by_cases hi : i = i0
  · rw [hi]
  · set σ : Equiv.Perm (Fin m) := Equiv.swap i i0 with hσ
    have hσself : σ.symm = σ := by rw [hσ, Equiv.symm_swap]
    set P : Su F0 2 1 m := ggPermSU (K := F0) (f := 1) σ with hPdef
    have hPmat : ((P : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) = σ.permMatrix F0 := rfl
    have hPvec : ∀ k : Fin m, ((P : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ
        Pi.single k 1 = Pi.single (σ k) 1 := by
      intro k
      rw [hPmat, Matrix.permMatrix_mulVec]
      funext x
      simp only [Function.comp_apply, Pi.single_apply]
      have hiff : σ x = k ↔ x = σ k := by
        rw [Equiv.apply_eq_iff_eq_symm_apply, hσself]
      exact if_congr hiff rfl rfl
    obtain ⟨u', hu', hu'ψ⟩ := h P
    have hzmem : u' * P⁻¹ ∈ Subgroup.center (Su F0 2 1 m) := by
      apply hker
      rw [MonoidHom.mem_ker, map_mul, map_inv, hu'ψ]
      simp
    have hzcomm : P * (u' * P⁻¹) = (u' * P⁻¹) * P := Subgroup.mem_center_iff.mp hzmem P
    have hzmat : ((u' * P⁻¹ : Su F0 2 1 m) : GL (Fin m) F0) =
        qTwoChartTwoThree_diag (fun k => c k * (c (σ k))⁻¹) := by
      have h1 : (P : GL (Fin m) F0) * (qTwoChartTwoThree_diag c)⁻¹ * (P : GL (Fin m) F0)⁻¹ =
          qTwoChartTwoThree_diag (fun k => (c (σ k))⁻¹) := by
        have h := qTwoChartTwoThree_perm_conj_diag (u := P) (σ := σ) hPvec c⁻¹
        rw [hσself, qtwoDB19_diag_inv] at h
        simpa [Pi.inv_apply] using h
      calc ((u' * P⁻¹ : Su F0 2 1 m) : GL (Fin m) F0)
          = (u' : GL (Fin m) F0) * (P : GL (Fin m) F0)⁻¹ := rfl
        _ = qTwoChartTwoThree_diag c * (P : GL (Fin m) F0) *
              (qTwoChartTwoThree_diag c)⁻¹ * (P : GL (Fin m) F0)⁻¹ := by rw [hu']
        _ = qTwoChartTwoThree_diag c *
              ((P : GL (Fin m) F0) * (qTwoChartTwoThree_diag c)⁻¹ *
                (P : GL (Fin m) F0)⁻¹) := by group
        _ = qTwoChartTwoThree_diag c * qTwoChartTwoThree_diag (fun k => (c (σ k))⁻¹) := by
              rw [h1]
        _ = qTwoChartTwoThree_diag (fun k => c k * (c (σ k))⁻¹) := by
              rw [← qtwoDB19_diag_mul]
              congr 1
    have hcommmat : Matrix.diagonal (fun k => (c k * (c (σ k))⁻¹ : F0)) *
        ((P : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
        ((P : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
          Matrix.diagonal (fun k => (c k * (c (σ k))⁻¹ : F0)) := by
      have h2 : (u' * P⁻¹ : Su F0 2 1 m) * P = P * (u' * P⁻¹ : Su F0 2 1 m) := hzcomm.symm
      have h3 : ((u' * P⁻¹ : Su F0 2 1 m) : GL (Fin m) F0) * (P : GL (Fin m) F0) =
          (P : GL (Fin m) F0) * ((u' * P⁻¹ : Su F0 2 1 m) : GL (Fin m) F0) :=
        congrArg (fun x : Su F0 2 1 m => (x : GL (Fin m) F0)) h2
      rw [hzmat] at h3
      exact congrArg (fun x : GL (Fin m) F0 => (x : Matrix (Fin m) (Fin m) F0)) h3
    have happ := qtwoDB19_diag_apply_eq_of_comm (e := fun k => (c k * (c (σ k))⁻¹ : F0))
      (σ := σ) (P := ((P : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)) hPvec hcommmat i
    have hσi : σ i = i0 := by rw [hσ]; exact Equiv.swap_apply_left i i0
    have hσi0 : σ i0 = i := by rw [hσ]; exact Equiv.swap_apply_right i i0
    rw [hσi, hσi0] at happ
    have happ' : (c i0 * (c i)⁻¹ : F0ˣ) = c i * (c i0)⁻¹ := by
      apply Units.ext
      exact happ
    have hrel : (c i * (c i0)⁻¹) * (c i * (c i0)⁻¹) = 1 := by
      nth_rewrite 2 [happ'.symm]
      group
    have h5 : c i * (c i0)⁻¹ = 1 := qtwoDB19_unit_sq_eq_one hF0 hrel
    have : c i = c i0 := by
      have := congrArg (fun x : F0ˣ => x * c i0) h5
      simpa [mul_assoc] using this
    exact this

theorem qtwoDB19_induces_div_const (hF0 : Nat.card F0 = 4)
    (hker : ψ.ker ≤ Subgroup.center (Su F0 2 1 m)) (hm : 3 ≤ m) {b : G} {c c' : Fin m → F0ˣ}
    (h : qTwoChartTwoThree_induces ψ b c) (h' : qTwoChartTwoThree_induces ψ b c') :
    ∃ lam : F0ˣ, ∀ i, c' i = lam * c i := by
  have h1 : qTwoChartTwoThree_induces ψ 1 (c * c'⁻¹) := by
    have h2 := qtwoDB19_induces_mul h (qtwoDB19_induces_inv hF0 h')
    simpa using h2
  obtain ⟨lam, hlam⟩ := qtwoDB19_induces_one_const hF0 hker hm h1
  refine ⟨lam⁻¹, fun i => ?_⟩
  have hi : c i * (c' i)⁻¹ = lam := hlam i
  have h2 : c i = lam * c' i := by
    rw [← hi]
    group
  rw [h2]
  group

end InducedDiagonal

section BetaFields

variable {Bs : Subgroup G} {L : Subgroup G} {𝒦 : Finset (Subgroup G)} {m : ℕ} {ι : Type}
  {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
  {β : Additive ↥Bs ≃+ DVec m}

theorem qtwoDB19_ofMul_toMul {α : Type*} [Mul α] (s : Additive α) :
    Additive.ofMul (Additive.toMul s) = s := rfl

theorem qtwoDB19_dEven_le_map (e' : Fin m ≃ ι)
    (hM : M = (ggCoxeterMatrixD m).reindex e')
    (hβ : ∀ (t : Fin m) (s : ↥Bs),
      β (Additive.ofMul (((e (M.simple (e' t)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) s)) =
        dTau m (decide (t.val + 1 = m)) (OrthTorus.simpleLo t) (OrthTorus.simpleHi t)
          (β (Additive.ofMul s))) (hm : 4 ≤ m) :
    dEven m ≤ (ggAutomizerJoin L Bs 𝒦).map (ggLin (p := 3) β) := by
  subst hM
  obtain ⟨ϑ, hϑ⟩ := dEven_equiv (m := m) hm
  have hsimple : ∀ t : Fin m,
      ggLin (p := 3) β (e (((ggCoxeterMatrixD m).reindex e').simple (e' t))) =
        dTau m (decide (t.val + 1 = m)) (OrthTorus.simpleLo t) (OrthTorus.simpleHi t) := by
    intro t
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨s, rfl⟩ := β.surjective v
    rw [← qtwoDB19_ofMul_toMul s, ggLin_apply_ofMul, hβ t (Additive.toMul s)]
  let Ψ : (ggCoxeterMatrixD m).Group →* (DVec m ≃ₗ[ZMod 3] DVec m) :=
    (ggLin (p := 3) β).comp (((ggAutomizerJoin L Bs 𝒦).subtype.comp e.toMonoidHom).comp
      ((CoxeterMatrix.reindexGroupEquiv (M := ggCoxeterMatrixD m) e').symm).toMonoidHom)
  have hΨ : Ψ = (dEven m).subtype.comp ϑ.toMonoidHom := by
    refine (ggCoxeterMatrixD m).toCoxeterSystem.ext_simple fun t => ?_
    show ggLin β (e ((CoxeterMatrix.reindexGroupEquiv (M := ggCoxeterMatrixD m) e').symm
      ((ggCoxeterMatrixD m).simple t))) = _
    rw [CoxeterMatrix.reindexGroupEquiv_symm_apply_simple]
    have h2 : ((dEven m).subtype.comp ϑ.toMonoidHom)
        ((ggCoxeterMatrixD m).toCoxeterSystem.simple t) =
        dTau m (decide (t.val + 1 = m)) (OrthTorus.simpleLo t) (OrthTorus.simpleHi t) := by
      simpa using hϑ t
    rw [h2]
    exact hsimple t
  intro w hw
  let u : (ggCoxeterMatrixD m).Group := ϑ.symm ⟨w, hw⟩
  let a : ↥(ggAutomizerJoin L Bs 𝒦) :=
    e ((CoxeterMatrix.reindexGroupEquiv (M := ggCoxeterMatrixD m) e').symm u)
  have h := congrArg (fun F : (ggCoxeterMatrixD m).Group →* (DVec m ≃ₗ[ZMod 3] DVec m) =>
      F u) hΨ
  simp only [MonoidHom.comp_apply, Subgroup.subtype_apply] at h
  refine Subgroup.mem_map.mpr ⟨a.1, a.2, ?_⟩
  have : Ψ u = w := by simpa [u] using h
  simpa [Ψ, a] using this

theorem qtwoDB19_map_le_dEven (e' : Fin m ≃ ι)
    (hM : M = (ggCoxeterMatrixD m).reindex e')
    (hβ : ∀ (t : Fin m) (s : ↥Bs),
      β (Additive.ofMul (((e (M.simple (e' t)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) s)) =
        dTau m (decide (t.val + 1 = m)) (OrthTorus.simpleLo t) (OrthTorus.simpleHi t)
          (β (Additive.ofMul s))) (hm : 4 ≤ m) :
    (ggAutomizerJoin L Bs 𝒦).map (ggLin (p := 3) β) ≤ dEven m := by
  subst hM
  let Φ : ((ggCoxeterMatrixD m).reindex e').Group →* (DVec m ≃ₗ[ZMod 3] DVec m) :=
    (ggLin (p := 3) β).comp ((ggAutomizerJoin L Bs 𝒦).subtype.comp e.toMonoidHom)
  have hgen : Subgroup.closure (Set.range ((ggCoxeterMatrixD m).reindex e').simple) ≤
      (dEven m).comap Φ := by
    rw [Subgroup.closure_le]
    rintro x ⟨i, rfl⟩
    have hsi : Φ (((ggCoxeterMatrixD m).reindex e').simple i) =
        dTau m (decide ((e'.symm i).val + 1 = m)) (OrthTorus.simpleLo (e'.symm i))
          (OrthTorus.simpleHi (e'.symm i)) := by
      refine LinearEquiv.ext fun v => ?_
      obtain ⟨s, rfl⟩ := β.surjective v
      change ggLin β (e (((ggCoxeterMatrixD m).reindex e').simple i)) (β s) =
        (dTau m (decide ((e'.symm i).val + 1 = m)) (OrthTorus.simpleLo (e'.symm i))
          (OrthTorus.simpleHi (e'.symm i))) (β s)
      rw [← qtwoDB19_ofMul_toMul s, ggLin_apply_ofMul,
        show ((ggCoxeterMatrixD m).reindex e').simple i =
          ((ggCoxeterMatrixD m).reindex e').simple (e' (e'.symm i)) from by
          rw [Equiv.apply_symm_apply],
        hβ (e'.symm i) (Additive.toMul s)]
    change Φ (((ggCoxeterMatrixD m).reindex e').simple i) ∈ dEven m
    rw [hsi]
    exact dTau_mem_dEven m _ (OrthTorus.simpleLo_ne_simpleHi (by omega) (e'.symm i))
  have htop : Subgroup.closure (Set.range ((ggCoxeterMatrixD m).reindex e').simple) = ⊤ :=
    ((ggCoxeterMatrixD m).reindex e').toCoxeterSystem.subgroup_closure_range_simple
  rw [htop] at hgen
  intro g hg
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hg
  obtain ⟨w, hw⟩ := e.surjective ⟨a, ha⟩
  have haw : (↑(e w) : MulAut ↥Bs) = a := congrArg Subtype.val hw
  rw [← haw]
  exact hgen (Subgroup.mem_top w)

theorem qtwoDB19_coxRoot (e' : Fin m ≃ ι) (hM : M = (ggCoxeterMatrixD m).reindex e')
    (hβ : ∀ (t : Fin m) (s : ↥Bs),
      β (Additive.ofMul (((e (M.simple (e' t)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) s)) =
        dTau m (decide (t.val + 1 = m)) (OrthTorus.simpleLo t) (OrthTorus.simpleHi t)
          (β (Additive.ofMul s))) (hm : 4 ≤ m) :
    ∀ r ∈ ggCoxRefl M e, ∃ (sgn : Bool) (a b : Fin m), a ≠ b ∧ ∀ s : ↥Bs,
      β (Additive.ofMul (r s)) = dTau m sgn a b (β (Additive.ofMul s)) := by
  subst hM
  rintro r ⟨w, i, rfl⟩
  have hw : ggLin (p := 3) β (((e w : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)) ∈ dEven m :=
    qtwoDB19_map_le_dEven e' rfl hβ hm
      (Subgroup.mem_map_of_mem (ggLin (p := 3) β) (e w).2)
  have hne : OrthTorus.simpleLo (e'.symm i) ≠ OrthTorus.simpleHi (e'.symm i) :=
    OrthTorus.simpleLo_ne_simpleHi (by omega) (e'.symm i)
  obtain ⟨sgn, a, b, hab, hconj⟩ :=
    dEven_conj_dTau m hw (decide ((e'.symm i).val + 1 = m)) hne
  have hsimple : ggLin (p := 3) β (((e (((ggCoxeterMatrixD m).reindex e').simple i) :
      ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)) =
      dTau m (decide ((e'.symm i).val + 1 = m)) (OrthTorus.simpleLo (e'.symm i))
        (OrthTorus.simpleHi (e'.symm i)) := by
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨s, rfl⟩ := β.surjective v
    rw [← qtwoDB19_ofMul_toMul s, ggLin_apply_ofMul,
      show ((ggCoxeterMatrixD m).reindex e').simple i =
        ((ggCoxeterMatrixD m).reindex e').simple (e' (e'.symm i)) from by
        rw [Equiv.apply_symm_apply],
      hβ (e'.symm i) (Additive.toMul s)]
  have hΦ : ggLin (p := 3) β (((e (w * ((ggCoxeterMatrixD m).reindex e').simple i * w⁻¹) :
      ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)) = dTau m sgn a b := by
    have h1 : ((e (w * ((ggCoxeterMatrixD m).reindex e').simple i * w⁻¹) :
        ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) =
        ((e w : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) *
          ((e (((ggCoxeterMatrixD m).reindex e').simple i) :
            ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) *
          (((e w : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs))⁻¹ := by
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [h1]
    simp only [map_mul, map_inv, hsimple, hconj]
  refine ⟨sgn, a, b, hab, fun s => ?_⟩
  rw [← ggLin_apply_ofMul (p := 3) β _ s, hΦ]

theorem qtwoDB19_cox {B : Subgroup G} {x : G} {D J : Subgroup G}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    (hpres : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e)
    (e' : Fin m ≃ ι) (hM : M = (ggCoxeterMatrixD m).reindex e')
    (hβ : ∀ (t : Fin m) (s : ↥Bs),
      β (Additive.ofMul (((e (M.simple (e' t)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) s)) =
        dTau m (decide (t.val + 1 = m)) (OrthTorus.simpleLo t) (OrthTorus.simpleHi t)
          (β (Additive.ofMul s))) :
    ∀ (sgn : Bool) (a b : Fin m), a ≠ b → ∀ r ∈ ggAutomizerJoin L Bs 𝒦,
      (∀ s : ↥Bs, β (Additive.ofMul (r s)) = dTau m sgn a b (β (Additive.ofMul s))) →
        r ∈ ggCoxRefl M e := by
  subst hM
  intro sgn a b hab r hr hact
  have hrefl : GGIsReflection 3 r := by
    refine ggIsReflection_of_eq_reflection (p := 3) (by decide) β
      (dFormAB_dRootAB m sgn hab) ?_
    refine ggLin_eq_reflection (p := 3) β (dFormAB_dRootAB m sgn hab) fun v => ?_
    obtain ⟨s, rfl⟩ := β.surjective v
    rw [← qtwoDB19_ofMul_toMul s, ggLin_apply_ofMul, hact (Additive.toMul s),
      dTau_apply_vec m sgn hab]
  exact ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres
    (reindexD_M_le_three e') hr hrefl

theorem qtwoDB19_node (e' : Fin m ≃ ι) (hM : M = (ggCoxeterMatrixD m).reindex e')
    (hβ : ∀ (t : Fin m) (s : ↥Bs),
      β (Additive.ofMul (((e (M.simple (e' t)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) s)) =
        dTau m (decide (t.val + 1 = m)) (OrthTorus.simpleLo t) (OrthTorus.simpleHi t)
          (β (Additive.ofMul s))) (hm : 3 ≤ m) :
    ∃ c₀ : Fin m, ∀ i : Fin m, (i : ℕ) ≠ 0 → ∃ (sgn : Bool) (a b : Fin m),
      a ≠ b ∧ a ≠ c₀ ∧ b ≠ c₀ ∧ ∀ s : ↥Bs,
        β (Additive.ofMul (((e (M.simple (e' i)) :
          ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) s)) =
          dTau m sgn a b (β (Additive.ofMul s)) := by
  subst hM
  refine ⟨⟨0, by omega⟩, fun i hi => ?_⟩
  obtain ⟨hlo, hhi⟩ := simpleLo_hi_pos (m := m) hm hi
  exact ⟨decide (i.val + 1 = m), OrthTorus.simpleLo i, OrthTorus.simpleHi i,
    OrthTorus.simpleLo_ne_simpleHi (by omega) i,
    fun h => hlo.ne' (by simpa using congrArg Fin.val h),
    fun h => hhi.ne' (by simpa using congrArg Fin.val h), hβ i⟩

end BetaFields

end CFSG.StandardType.QTwo

end

module

public import CFSG.Quasithin.Background.Harris.KFact2d.Defs
public import CFSG.Quasithin.Vol2.Ch3E213MOLA9
public import CFSG.LieType.Steinberg.CentralExt.SLCentrallyClosed
public import CFSG.ClassicalInvolution.ModelFacts.LinearAutMain
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutLift
public import CFSG.ClassicalInvolution.Q3.Q3WASAut
public import CFSG.Adapters.SpecialLinearPerfect
public import CFSG.Quasithin.EmptyFaithful.SzOneV2d
public import CFSG.Quasithin.Vol2.Ch3E213MOLFacts

public section

namespace CFSG.Quasithin.Background.Harris.KFact2d

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped MatrixGroups commutatorElement

private theorem comm_mul_central_left {G : Type*} [Group G] {a c z : G}
    (hz : z ∈ Subgroup.center G) : ⁅a * z, c⁆ = ⁅a, c⁆ := by
  have h : z * c * z⁻¹ = c := by
    rw [mul_inv_eq_iff_eq_mul]
    exact ((Subgroup.mem_center_iff.mp hz) c).symm
  simp only [commutatorElement_def, mul_inv_rev]
  calc a * z * c * (z⁻¹ * a⁻¹) * c⁻¹ = a * (z * c * z⁻¹) * a⁻¹ * c⁻¹ := by group
    _ = _ := by rw [h]

private theorem comm_mul_central {G : Type*} [Group G] {a b z w : G}
    (hz : z ∈ Subgroup.center G) (hw : w ∈ Subgroup.center G) :
    ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  rw [comm_mul_central_left hz, ← commutatorElement_inv, comm_mul_central_left hw,
    commutatorElement_inv]

private theorem subsingleton_ringEquiv_of_card {K : Type} [Field K] [Finite K] {p : ℕ}
    [Fact p.Prime] (hK : Nat.card K = p) : Subsingleton (K ≃+* K) := by
  have hord : addOrderOf (1 : K) = p := by
    have hdvd : addOrderOf (1 : K) ∣ p := by
      rw [← hK]
      exact addOrderOf_dvd_natCard _
    rcases (Nat.dvd_prime Fact.out).mp hdvd with h | h
    · simp at h
    · exact h
  have htop : AddSubgroup.zmultiples (1 : K) = ⊤ := by
    apply AddSubgroup.eq_top_of_card_eq
    rw [Nat.card_zmultiples, hord, hK]
  refine ⟨fun σ τ => ?_⟩
  ext x
  have hx : x ∈ AddSubgroup.zmultiples (1 : K) := htop ▸ AddSubgroup.mem_top x
  obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
  simp

private theorem exists_lift_sl3 {E : Type} [Group E] {F : Type} [Field F] [Finite F]
    (hF2 : Nat.card F ≠ 2) (hF4 : Nat.card F ≠ 4)
    (θ₀ : SL(3, F) →* E ⧸ Subgroup.center E) :
    ∃ φ : SL(3, F) →* E, ∀ x, (QuotientGroup.mk (φ x) : E ⧸ Subgroup.center E) = θ₀ x := by
  let P : Subgroup (E × SL(3, F)) := MonoidHom.eqLocus
    ((QuotientGroup.mk' (Subgroup.center E)).comp (MonoidHom.fst _ _))
    (θ₀.comp (MonoidHom.snd _ _))
  let ρ : P →* SL(3, F) := (MonoidHom.snd _ _).comp P.subtype
  have hρ : Function.Surjective ρ := by
    intro x
    obtain ⟨e, he⟩ := QuotientGroup.mk_surjective (θ₀ x)
    exact ⟨⟨(e, x), he⟩, rfl⟩
  have hcen : ρ.ker ≤ Subgroup.center P := by
    intro y hy
    obtain ⟨⟨e, x⟩, hmem⟩ := y
    have hx : x = 1 := hy
    subst hx
    have he : e ∈ Subgroup.center E := by
      have h1 : (QuotientGroup.mk e : E ⧸ Subgroup.center E) = θ₀ 1 := hmem
      rw [map_one] at h1
      exact (QuotientGroup.eq_one_iff e).mp h1
    rw [Subgroup.mem_center_iff]
    rintro ⟨⟨e', x'⟩, hmem'⟩
    apply Subtype.ext
    exact Prod.ext (Subgroup.mem_center_iff.mp he e') (by simp)
  obtain ⟨σ, hσ⟩ := CFSG.LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_separating
    (m := 2) le_rfl (CFSG.LieType.Steinberg.CentralExt.SLClosed.separating_of_card le_rfl hF2
      (fun h => hF4 h.2) (fun h => by omega)) hρ hcen
  refine ⟨(MonoidHom.fst _ _).comp (P.subtype.comp σ), fun x => ?_⟩
  have h1 := (σ x).2
  have h2 : ((σ x : P) : E × SL(3, F)).2 = x := hσ x
  have h3 : (QuotientGroup.mk ((σ x : P) : E × SL(3, F)).1 : E ⧸ Subgroup.center E) =
      θ₀ ((σ x : P) : E × SL(3, F)).2 := h1
  rw [h2] at h3
  exact h3

private theorem exists_sl_conj {F : Type} [Field F] (g : GL (Fin 3) F)
    (hg : ∀ x : SL(3, F), ((g * g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (x : Matrix _ _ F) =
      (x : Matrix _ _ F) * ((g * g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) :
    ∃ h : SL(3, F), ∀ x : SL(3, F), (h : Matrix (Fin 3) (Fin 3) F) * (x : Matrix _ _ F) =
      (g : Matrix (Fin 3) (Fin 3) F) * (x : Matrix _ _ F) * ((g⁻¹ : GL (Fin 3) F) : Matrix _ _ F) *
        (h : Matrix (Fin 3) (Fin 3) F) := by
  have hsc : ((g * g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ∈
      Set.range (Matrix.scalar (Fin 3) (α := F)) := by
    refine Matrix.mem_range_scalar_of_commute_transvectionStruct fun t => ?_
    exact (hg ⟨t.toMatrix, t.det⟩).symm
  obtain ⟨l, hl⟩ := hsc
  set d : F := ((g : Matrix (Fin 3) (Fin 3) F)).det with hd_def
  have hd : d ≠ 0 := by
    have : IsUnit d := by
      rw [hd_def, ← Matrix.GeneralLinearGroup.val_det_apply]
      exact (Matrix.GeneralLinearGroup.det g).isUnit
    exact this.ne_zero
  have hdet : d * d = l ^ 3 := by
    have h1 := congrArg Matrix.det hl
    rw [Units.val_mul, Matrix.det_mul] at h1
    simpa [Matrix.scalar_apply, Matrix.det_diagonal, hd_def] using h1.symm
  have hl0 : l ≠ 0 := by
    rintro rfl
    simp at hdet
    exact hd hdet
  let μ : F := (l / d)
  have hdetμ : (μ • (g : Matrix (Fin 3) (Fin 3) F)).det = 1 := by
    rw [Matrix.det_smul]
    simp only [Fintype.card_fin, μ]
    field_simp
    rw [← hdet]
    ring
  refine ⟨⟨μ • (g : Matrix (Fin 3) (Fin 3) F), hdetμ⟩, fun x => ?_⟩
  show μ • (g : Matrix (Fin 3) (Fin 3) F) * (x : Matrix _ _ F) = _ * (μ • (g : Matrix _ _ F))
  have hgi : ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (g : Matrix _ _ F) = 1 :=
    g.inv_mul
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_assoc, hgi, Matrix.mul_one]

theorem f4_psl : ∀ (E : Type) [Group E] [Finite E] (p : ℕ), p.Prime → p ≠ 2 → commutator E = ⊤ →
    Odd (Nat.card (Subgroup.center E)) → IsPSL 3 p 1 (E ⧸ Subgroup.center E) →
    ∀ v : MulAut E, v * v = 1 →
      (¬ ∃ g : E, ∀ x : E, v x * (g * x * g⁻¹)⁻¹ ∈ Subgroup.center E) →
      ∀ c ∈ Subgroup.center E, v c = c⁻¹ := by
  intro E _ _ p hp hp2 hperf _ hPSL v hv hnot c hc
  have : Fact p.Prime := ⟨hp⟩
  have hcardF : Nat.card (GaloisField p 1) = p := by
    simpa using GaloisField.card p 1 one_ne_zero
  obtain ⟨θ₀, hθs, hθk⟩ := CFSG.Quasithin.Ch3E213M.OLA.exists_theta_lin hPSL
  obtain ⟨φ, hφ⟩ := exists_lift_sl3 (F := GaloisField p 1) (by omega)
    (by
      rw [hcardF]
      rintro rfl
      norm_num at hp) θ₀
  have hφk : φ.ker ≤ Subgroup.center SL(3, GaloisField p 1) := fun x hx =>
    hθk (by rw [MonoidHom.mem_ker, ← hφ, MonoidHom.mem_ker.mp hx, QuotientGroup.mk_one])
  have hφs : Function.Surjective φ := by
    have hsup : ∀ e : E, ∃ x, (φ x)⁻¹ * e ∈ Subgroup.center E := by
      intro e
      obtain ⟨x, hx⟩ := hθs (QuotientGroup.mk e)
      refine ⟨x, ?_⟩
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hφ, hx,
        inv_mul_cancel]
    have hcomm : commutator E ≤ φ.range := by
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro a _ b _
      obtain ⟨x, hx⟩ := hsup a
      obtain ⟨y, hy⟩ := hsup b
      have ha : a = φ x * ((φ x)⁻¹ * a) := by group
      have hb : b = φ y * ((φ y)⁻¹ * b) := by group
      rw [ha, hb, comm_mul_central hx hy, ← map_commutatorElement]
      exact ⟨_, rfl⟩
    rw [hperf] at hcomm
    intro e
    exact hcomm (Subgroup.mem_top e)
  have hvv : ∀ y, v (v y) = y := fun y => by
    have := congrArg (fun w : MulAut E => w y) hv
    simpa using this
  have hcl : CFSG.ClassicalInvolution.RouteD.Gaps.LinearAutClassification (GaloisField p 1) 3 := by
    by_cases h3 : p = 3
    · subst h3
      exact CFSG.ClassicalInvolution.Q3.Q3W.linearAutClassification3 le_rfl
    · have h4 : p ≠ 4 := by
        rintro rfl
        norm_num at hp
      exact CFSG.ClassicalInvolution.ModelFacts.LinearAut.linearAutClassification hp2
        (by have := hp.two_le; simpa using (by omega : 5 ≤ p)) le_rfl
  obtain ⟨α, g, ψ, ε, hαθ, hαmat⟩ := hcl E φ hφs hφk v
  have hψ : ψ = RingEquiv.refl _ :=
    have := subsingleton_ringEquiv_of_card hcardF
    Subsingleton.elim _ _
  subst hψ
  have hmap : ∀ M : Matrix (Fin 3) (Fin 3) (GaloisField p 1),
      (RingEquiv.refl (GaloisField p 1)).mapMatrix M = M := fun M => by ext; rfl
  cases ε
  ·
    exfalso
    apply hnot
    simp only [hmap, Bool.false_eq_true, ↓reduceIte] at hαmat
    have hαGL : ∀ y, Matrix.SpecialLinearGroup.toGL (α y) =
        g * Matrix.SpecialLinearGroup.toGL y * g⁻¹ := fun y => Units.ext (by
      rw [Units.val_mul, Units.val_mul]
      exact hαmat y)
    have := CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (K := GaloisField p 1)
      (n := 3) le_rfl
    have hαα : α.comp α = MonoidHom.id _ :=
      CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.hom_eq_of_central_ker_perfect hφk _ _
        fun x => by rw [MonoidHom.comp_apply, hαθ, hαθ, hvv]; rfl
    have hg : ∀ x : SL(3, GaloisField p 1),
        ((g * g : GL (Fin 3) (GaloisField p 1)) : Matrix (Fin 3) (Fin 3) (GaloisField p 1)) *
          (x : Matrix (Fin 3) (Fin 3) (GaloisField p 1)) =
        (x : Matrix (Fin 3) (Fin 3) (GaloisField p 1)) *
          ((g * g : GL (Fin 3) (GaloisField p 1)) : Matrix (Fin 3) (Fin 3) (GaloisField p 1)) := by
      intro x
      have hx : α (α x) = x := DFunLike.congr_fun hαα x
      have hx' : Matrix.SpecialLinearGroup.toGL x =
          g * (g * Matrix.SpecialLinearGroup.toGL x * g⁻¹) * g⁻¹ := by
        rw [← hαGL, ← hαGL, hx]
      have hX : g * g * Matrix.SpecialLinearGroup.toGL x =
          Matrix.SpecialLinearGroup.toGL x * (g * g) :=
        calc g * g * Matrix.SpecialLinearGroup.toGL x
            = (g * (g * Matrix.SpecialLinearGroup.toGL x * g⁻¹) * g⁻¹) * (g * g) := by group
          _ = Matrix.SpecialLinearGroup.toGL x * (g * g) := by rw [← hx']
      have := congrArg Units.val hX
      rw [Units.val_mul, Units.val_mul] at this
      exact this
    obtain ⟨h, hh⟩ := exists_sl_conj g hg
    refine ⟨φ h, fun x => ?_⟩
    obtain ⟨y, rfl⟩ := hφs x
    have hαy : α y = h * y * h⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hh y, hαmat y]
    have hvy : v (φ y) = φ h * φ y * (φ h)⁻¹ := by
      rw [← hαθ, hαy, map_mul, map_mul, map_inv]
    rw [hvy, mul_inv_cancel]
    exact Subgroup.one_mem _
  ·
    obtain ⟨s, rfl⟩ := hφs c
    have hs : s ∈ Subgroup.center SL(3, GaloisField p 1) :=
      hθk (by rw [MonoidHom.mem_ker, ← hφ]; exact (QuotientGroup.eq_one_iff _).mpr hc)
    have hαs : α s = s⁻¹ := by
      obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp (inv_mem hs)
      apply Subtype.ext
      have h1 := hαmat s
      simp only [hmap, ↓reduceIte] at h1
      rw [h1, ← hr, Matrix.scalar_apply, Matrix.diagonal_transpose, ← Matrix.smul_one_eq_diagonal,
        Matrix.mul_smul, Matrix.smul_mul]
      have hgi : (g : Matrix (Fin 3) (Fin 3) (GaloisField p 1)) *
          ((g⁻¹ : GL (Fin 3) (GaloisField p 1)) : Matrix (Fin 3) (Fin 3) (GaloisField p 1)) = 1 :=
        g.mul_inv
      rw [Matrix.mul_one, hgi]
    rw [← hαθ, hαs, map_inv]

end CFSG.Quasithin.Background.Harris.KFact2d

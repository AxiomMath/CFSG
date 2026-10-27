module

public import CFSG.Quasithin.Background.Harris.KFact2d.Defs
public import CFSG.Quasithin.Vol2.Ch3E213MOLA9
public import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutSimilitude
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutMain
public import CFSG.Quasithin.EmptyFaithful.SzOneV2d
public import CFSG.Quasithin.Vol2.Ch3E213MOLFacts

public section

namespace CFSG.Quasithin.Background.Harris.KFact2d

open CFSG.Quasithin CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.ModelFacts.UnitaryAut
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag
open scoped commutatorElement Matrix

section Groups

theorem exists_lift_hom {E G X : Type} [Group E] [Finite E] [Group G] [Finite G] [Group X]
    (hG : ∀ (P : Type) [Group P] [Finite P] (π : P →* G), Function.Surjective π →
      π.ker ≤ Subgroup.center P → ∃ s : G →* P, ∀ g, π (s g) = g)
    (π : E →* X) (hπ : Function.Surjective π) (hπc : π.ker ≤ Subgroup.center E)
    (θ : G →* X) : ∃ φ : G →* E, ∀ x, π (φ x) = θ x := by
  let P : Subgroup (E × G) :=
    { carrier := {z | π z.1 = θ z.2}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, Prod.fst_mul, Prod.snd_mul, map_mul] at ha hb ⊢
        rw [ha, hb]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq, Prod.fst_inv, Prod.snd_inv, map_inv] at ha ⊢
        rw [ha] }
  let η : P →* G := (MonoidHom.snd E G).comp P.subtype
  have hη : Function.Surjective η := by
    intro x
    obtain ⟨e, he⟩ := hπ (θ x)
    exact ⟨⟨(e, x), he⟩, rfl⟩
  have hk : η.ker ≤ Subgroup.center P := by
    rintro ⟨⟨e, x⟩, hmem⟩ hx
    have hx1 : x = 1 := hx
    subst hx1
    have he : e ∈ Subgroup.center E := hπc (by simpa [P] using hmem)
    rw [Subgroup.mem_center_iff]
    rintro ⟨⟨e', y⟩, hz⟩
    refine Subtype.ext (Prod.ext ?_ ?_)
    · exact Subgroup.mem_center_iff.mp he e'
    · simp
  obtain ⟨s, hs⟩ := hG P η hη hk
  refine ⟨(MonoidHom.fst E G).comp (P.subtype.comp s), fun x => ?_⟩
  have h1 : π ((s x : P) : E × G).1 = θ ((s x : P) : E × G).2 := (s x).2
  have h2 : ((s x : P) : E × G).2 = x := hs x
  exact h1.trans (congrArg θ h2)

theorem commutator_mul_center_left {E : Type} [Group E] {a b z : E}
    (hz : z ∈ Subgroup.center E) : ⁅a * z, b⁆ = ⁅a, b⁆ := by
  have h := Subgroup.mem_center_iff.mp hz b
  simp only [commutatorElement_def, mul_inv_rev]
  calc a * z * b * (z⁻¹ * a⁻¹) * b⁻¹ = a * (z * b) * z⁻¹ * a⁻¹ * b⁻¹ := by group
    _ = a * (b * z) * z⁻¹ * a⁻¹ * b⁻¹ := by rw [← h]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem commutator_mul_center_right {E : Type} [Group E] {a b w : E}
    (hw : w ∈ Subgroup.center E) : ⁅a, b * w⁆ = ⁅a, b⁆ := by
  have h := Subgroup.mem_center_iff.mp hw a⁻¹
  simp only [commutatorElement_def, mul_inv_rev]
  calc a * (b * w) * a⁻¹ * (w⁻¹ * b⁻¹) = a * b * (w * a⁻¹) * w⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * w) * w⁻¹ * b⁻¹ := by rw [← h]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem surjective_of_perfect {E G : Type} [Group E] [Group G] (hE : commutator E = ⊤)
    (φ : G →* E) (h : ∀ e : E, ∃ x : G, ∃ z ∈ Subgroup.center E, e = φ x * z) :
    Function.Surjective φ := by
  have hle : commutator E ≤ φ.range := by
    rw [commutator_def, Subgroup.commutator_le]
    rintro a - b -
    obtain ⟨x, z, hz, rfl⟩ := h a
    obtain ⟨y, w, hw, rfl⟩ := h b
    rw [commutator_mul_center_left hz, commutator_mul_center_right hw, ← map_commutatorElement]
    exact ⟨_, rfl⟩
  rw [hE] at hle
  exact MonoidHom.range_eq_top.mp (top_le_iff.mp hle)

end Groups

section Matrix

variable {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]

omit [Finite F] [CharP F p] in
theorem unitaryFieldData_one (hK : Nat.card F = (p ^ 1) ^ 2) : UnitaryFieldData p 1 F :=
  ⟨Fact.out, le_refl 1, by rw [hK, ← pow_mul, mul_comm]⟩

omit [Finite F] in
theorem mat_mul_inv (g : GL (Fin 3) F) :
    (g : Matrix (Fin 3) (Fin 3) F) * ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem sq_comm {n : Type} [Fintype n] [DecidableEq n] {R : Type} [CommRing R]
    (G Gi Y : Matrix n n R) (h1 : Gi * G = 1) (h : G * (G * Y * Gi) * Gi = Y) :
    G * G * Y = Y * (G * G) := by
  have h2 : Gi * (Gi * (G * G)) = 1 := by
    rw [← Matrix.mul_assoc Gi G G, h1, Matrix.one_mul, h1]
  calc G * G * Y = G * G * Y * (Gi * (Gi * (G * G))) := by rw [h2, Matrix.mul_one]
    _ = (G * (G * Y * Gi) * Gi) * (G * G) := by simp only [Matrix.mul_assoc]
    _ = Y * (G * G) := by rw [h]

theorem su3_id_inner (hK : Nat.card F = (p ^ 1) ^ 2) (hp2 : p ≠ 2)
    (α : Su F p 1 3 →* Su F p 1 3) (g : GL (Fin 3) F)
    (h2 : ∀ x : Su F p 1 3, (α x : GL (Fin 3) F) = g * (x : GL (Fin 3) F) * g⁻¹)
    (h3 : ((g : Matrix (Fin 3) (Fin 3) F).map (unitaryInvolution F p 1))ᵀ *
      (g : Matrix (Fin 3) (Fin 3) F) = 1)
    (hαα : ∀ x, α (α x) = x) : ∃ k : Su F p 1 3, ∀ x, α x = k * x * k⁻¹ := by
  have h := unitaryFieldData_one hK
  set σ := unitaryInvolution F p 1 with hσdef
  set G : Matrix (Fin 3) (Fin 3) F := (g : Matrix (Fin 3) (Fin 3) F) with hG
  set Gi : Matrix (Fin 3) (Fin 3) F := ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hGi
  have hGGi : G * Gi = 1 := mat_mul_inv g
  have hGiG : Gi * G = 1 := by
    rw [hG, hGi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hbar : ∀ c, h.bar c = σ c := fun c => by
    rw [hσdef, unitaryInvolution_apply, UnitaryFieldData.bar_apply]
  have hcomm : ∀ y : GL (Fin 3) F, y ∈ unitarySU p 1 F 3 →
      G * G * (y : Matrix (Fin 3) (Fin 3) F) = (y : Matrix (Fin 3) (Fin 3) F) * (G * G) := by
    intro y hy
    set x : Su F p 1 3 := (suEquivUnitarySU F p 1 hK 3).symm ⟨y, hy⟩ with hx
    have hxy : (x : GL (Fin 3) F) = y := coe_suEquivUnitarySU_symm hK _
    have e1 := congrArg (fun z : Su F p 1 3 => (z : GL (Fin 3) F)) (hαα x)
    simp only [h2, hxy] at e1
    have e2 := congrArg (fun z : GL (Fin 3) F => (z : Matrix (Fin 3) (Fin 3) F)) e1
    simp only [Units.val_mul] at e2
    exact sq_comm G Gi _ hGiG e2
  obtain ⟨a, ha⟩ := eq_smul_one_of_commute h hp2 (le_refl 3) (G * G) hcomm
  have hσσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hK
  set d : F := G.det with hd
  have hd0 : d ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det G).mp g.isUnit
    exact this.ne_zero
  have hdet : d * d = a ^ 3 := by
    have := congrArg Matrix.det ha
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one] at this
    simpa using this
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0] at hdet
    simp [hd0] at hdet
  have hNd : σ d * d = 1 := by
    have := congrArg Matrix.det h3
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
    rw [← this, hd]
    congr 1
    exact (RingHom.map_det (σ : F →+* F) G)
  have hNa : σ a * a = 1 := by
    have e1 : ((G * G).map σ)ᵀ * (G * G) = 1 := by
      rw [Matrix.map_mul, Matrix.transpose_mul]
      calc (G.map σ)ᵀ * (G.map σ)ᵀ * (G * G) = (G.map σ)ᵀ * ((G.map σ)ᵀ * G) * G := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h3, Matrix.mul_one, h3]
    rw [ha] at e1
    have e2 := congrFun (congrFun e1 0) 0
    simpa [Matrix.mul_apply, Matrix.one_apply, mul_comm] using e2
  let μ : Fˣ := Units.mk0 (a / d) (div_ne_zero ha0 hd0)
  let k : GL (Fin 3) F := Matrix.GeneralLinearGroup.scalar (Fin 3) μ * g
  have hkmat : (k : Matrix (Fin 3) (Fin 3) F) = (a / d) • G := by
    show (Matrix.GeneralLinearGroup.scalar (Fin 3) μ * g : GL (Fin 3) F).val = _
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
    ext i j
    simp only [μ, Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul,
      Units.val_mk0, G]
  have hk : k ∈ SUid σ 3 := by
    refine ⟨?_, ?_⟩
    · rw [hkmat, Matrix.det_smul]
      simp only [Fintype.card_fin]
      have : (a / d) ^ 3 * d = 1 := by
        field_simp
        rw [← hdet]
        ring
      exact this
    · rw [hkmat]
      have e : ((a / d) • G).map σ = σ (a / d) • G.map σ := by
        ext i j
        simp
      show (((a / d) • G).map σ)ᵀ * ((a / d) • G) = 1
      rw [e, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, h3, smul_smul]
      have : σ (a / d) * (a / d) = 1 := by
        rw [map_div₀, div_mul_div_comm, hNa, hNd, div_one]
      rw [this, one_smul]
  refine ⟨⟨k, hk⟩, fun x => ?_⟩
  apply Subtype.ext
  have hs : ∀ z : GL (Fin 3) F, Matrix.GeneralLinearGroup.scalar (Fin 3) μ * z =
      z * Matrix.GeneralLinearGroup.scalar (Fin 3) μ := fun z =>
    (commute_scalar μ z).eq.symm
  show (α x : GL (Fin 3) F) = k * (x : GL (Fin 3) F) * k⁻¹
  rw [h2 x]
  have e : k * (x : GL (Fin 3) F) * k⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) μ *
      (g * (x : GL (Fin 3) F) * g⁻¹) * (Matrix.GeneralLinearGroup.scalar (Fin 3) μ)⁻¹ := by
    simp only [k, mul_inv_rev]
    group
  rw [e, hs, mul_inv_cancel_right]

theorem su3_bar_scalar
    (α : Su F p 1 3 →* Su F p 1 3) (g : GL (Fin 3) F)
    (h2 : ∀ x : Su F p 1 3, ((α x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (g : Matrix (Fin 3) (Fin 3) F) *
        (unitaryInvolution F p 1).mapMatrix ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
    (x : Su F p 1 3) (c : F)
    (hc : ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) c) :
    α x = x⁻¹ := by
  set σ := unitaryInvolution F p 1 with hσdef
  have hsc : σ.mapMatrix (Matrix.scalar (Fin 3) c) = Matrix.scalar (Fin 3) (σ c) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
  have hX : (Matrix.scalar (Fin 3) (σ c)) * Matrix.scalar (Fin 3) c = 1 := by
    have := x.2.2
    rw [hc] at this
    have e : conjTr σ (Matrix.scalar (Fin 3) c) = Matrix.scalar (Fin 3) (σ c) := by
      rw [conjTr, ← hsc]
      show ((Matrix.scalar (Fin 3) c).map σ)ᵀ = _
      rw [show (Matrix.scalar (Fin 3) c).map σ = σ.mapMatrix (Matrix.scalar (Fin 3) c) from rfl,
        hsc]
      simp [Matrix.scalar_apply]
    rwa [e] at this
  apply eq_inv_of_mul_eq_one_left
  apply Subtype.ext
  apply Units.ext
  show ((α x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * _ = 1
  rw [h2 x, hc, hsc]
  have hs : (g : Matrix (Fin 3) (Fin 3) F) * Matrix.scalar (Fin 3) (σ c) =
      Matrix.scalar (Fin 3) (σ c) * (g : Matrix (Fin 3) (Fin 3) F) :=
    ((Matrix.scalar_commute (σ c) (fun r => Commute.all _ r) _).eq).symm
  rw [hs]
  calc Matrix.scalar (Fin 3) (σ c) * (g : Matrix (Fin 3) (Fin 3) F) *
        ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * Matrix.scalar (Fin 3) c
      = Matrix.scalar (Fin 3) (σ c) *
        ((g : Matrix (Fin 3) (Fin 3) F) * ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) *
          Matrix.scalar (Fin 3) c := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [mat_mul_inv, Matrix.mul_one]; exact hX

theorem su3_perfect_center (hK : Nat.card F = (p ^ 1) ^ 2) (hp5 : 5 ≤ p ^ 1) :
    Group.IsPerfect (Su F p 1 3) ∧ ∀ x ∈ Subgroup.center (Su F p 1 3),
      ∃ c : F, ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) c := by
  have h := unitaryFieldData_one hK
  obtain ⟨hperf, hcen⟩ := isPerfect_and_center_unitarySU h hp5 (le_refl 3)
  set e := suEquivUnitarySU F p 1 hK 3
  refine ⟨Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective, fun x hx => ?_⟩
  have hec : e x ∈ Subgroup.center (unitarySU p 1 F 3) := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro g
    apply e.symm.injective
    rw [map_mul, map_mul, MulEquiv.symm_apply_apply]
    exact hx (e.symm g)
  rw [hcen] at hec
  obtain ⟨c, -, -, hc⟩ := hec
  refine ⟨c, ?_⟩
  have : ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (((e x : unitarySU p 1 F 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := rfl
  rw [this, hc, Matrix.GeneralLinearGroup.coe_scalar]

end Matrix

section Core

variable
  {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]

theorem f4_psu_core {E : Type} [Group E] [Finite E]
    (hK : Nat.card F = (p ^ 1) ^ 2) (hp2 : p ≠ 2) (hp5 : 5 ≤ p ^ 1) (hE : commutator E = ⊤)
    (θ : Su F p 1 3 →* E ⧸ Subgroup.center E) (hθs : Function.Surjective θ)
    (hθk : θ.ker ≤ Subgroup.center (Su F p 1 3)) (v : MulAut E) (hv : v * v = 1)
    (hnot : ¬ ∃ g : E, ∀ x : E, v x * (g * x * g⁻¹)⁻¹ ∈ Subgroup.center E) :
    ∀ c ∈ Subgroup.center E, v c = c⁻¹ := by
  obtain ⟨hperf, hscal⟩ := su3_perfect_center hK hp5
  set ι := suEquivUnitarySU F p 1 hK 3
  let π : E →* E ⧸ Subgroup.center E := QuotientGroup.mk' (Subgroup.center E)
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπk : π.ker ≤ Subgroup.center E := (QuotientGroup.ker_mk' _).le
  have hG : ∀ (P : Type) [Group P] [Finite P] (η : P →* Su F p 1 3), Function.Surjective η →
      η.ker ≤ Subgroup.center P → ∃ s : Su F p 1 3 →* P, ∀ g, η (s g) = g := by
    intro P _ _ η hη hc
    obtain ⟨s, hs⟩ := CFSG.LieType.Steinberg.CentralExt.SUOdd.statedSU_odd_exists_section_of_central
      (F := F) (p := p) (f := 1) hK (le_refl 1) (n := 3) (le_refl 3) (by decide)
      (by simpa using hp2) (π := ι.toMonoidHom.comp η) (ι.surjective.comp hη)
      (by
        intro x hx
        apply hc
        rw [MonoidHom.mem_ker] at hx ⊢
        exact ι.injective (by simpa using hx))
    refine ⟨s.comp ι.toMonoidHom, fun x => ι.injective ?_⟩
    simpa using hs (ι x)
  obtain ⟨φ, hφ⟩ := exists_lift_hom hG π hπs hπk θ
  have hφsurj : Function.Surjective φ := by
    refine surjective_of_perfect hE φ fun e => ?_
    obtain ⟨x, hx⟩ := hθs (π e)
    refine ⟨x, (φ x)⁻¹ * e, hπk ?_, by simp⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hφ, hx, inv_mul_cancel]
  have hφker : φ.ker ≤ Subgroup.center (Su F p 1 3) := fun x hx => by
    apply hθk
    rw [MonoidHom.mem_ker] at hx ⊢
    rw [← hφ, hx, map_one]
  have hφcen : ∀ x, φ x ∈ Subgroup.center E → x ∈ Subgroup.center (Su F p 1 3) := by
    intro x hx
    have := hperf
    refine mem_center_of_commutator_mem_center fun y => hφker ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      ((Subgroup.mem_center_iff.mp hx (φ y)).symm)
  have hvv : ∀ x, v (v x) = x := fun x => DFunLike.congr_fun hv x
  obtain ⟨α, g, ψ, h1, h2, h3, h4⟩ := unitaryAutClassification_isometry_of_card hK hp2 hp5
    (le_refl 3) E φ hφsurj hφker v
  obtain ⟨hψ, hαα⟩ := h4 hvv
  have hαα' : ∀ x, α (α x) = x := fun x => DFunLike.congr_fun hαα x
  rcases hψ with hψ | hψ
  · exfalso
    subst hψ
    obtain ⟨k, hk⟩ := su3_id_inner hK hp2 α g (fun x => by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul]
      exact h2 x) h3 hαα'
    refine hnot ⟨φ k, fun e => ?_⟩
    obtain ⟨x, rfl⟩ := hφsurj e
    rw [← h1, hk, map_mul, map_mul, map_inv, mul_inv_cancel]
    exact Subgroup.one_mem _
  · intro c hc
    obtain ⟨x, rfl⟩ := hφsurj c
    obtain ⟨a, ha⟩ := hscal x (hφcen x hc)
    rw [← h1, su3_bar_scalar α g (fun y => by rw [h2 y, hψ]) x a ha, map_inv]

end Core

section Final


theorem f4_psu : ∀ (E : Type) [Group E] [Finite E] (p : ℕ), p.Prime → p % 4 = 1 →
    commutator E = ⊤ → Odd (Nat.card (Subgroup.center E)) →
    IsPSU 3 p 1 (E ⧸ Subgroup.center E) →
    ∀ v : MulAut E, v * v = 1 →
      (¬ ∃ g : E, ∀ x : E, v x * (g * x * g⁻¹)⁻¹ ∈ Subgroup.center E) →
      ∀ c ∈ Subgroup.center E, v c = c⁻¹ := by
  intro E _ _ p hp hp4 hE _ hU v hv hnot
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hp5 : 5 ≤ p ^ 1 := by
    have := hp.two_le
    rw [pow_one]
    omega
  obtain ⟨F, _, _, _, hK, θ, hθs, hθk⟩ := CFSG.Quasithin.Ch3E213M.OLA.exists_theta_uni hU
  exact f4_psu_core hK hp2 hp5 hE θ hθs hθk v hv hnot

end Final

end CFSG.Quasithin.Background.Harris.KFact2d

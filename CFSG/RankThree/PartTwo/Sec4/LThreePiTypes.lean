module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiFrob

public section

namespace CFSG.RankThree.PartTwo.Sec4

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

@[expose] def Type123 (π : Bool) (q : ℕ) (K : Type) [Field K] (x : GL (Fin 3) K) : ℕ → Prop
  | 1 => ∃ (τ : K) (hτ : τ ^ 3 = 1), τ ≠ 1 ∧ ∃ z ∈ zPi π 3 q K, ∃ g ∈ glPi π 3 q K,
      g⁻¹ * (x * z) * g = diagTau hτ
  | 2 => ∃ e : Kˣ, (e : K) ^ 3 = 1 ∧ e ≠ 1 ∧ ∃ z ∈ zPi π 3 q K, ∃ g ∈ glPi π 3 q K,
      g⁻¹ * (x * z) * g = diagE e
  | 3 => x ∉ zPi π 3 q K ∧ x ^ 3 ∈ zPi π 3 q K ∧ ∀ W : Submodule K (Fin 3 → K),
      (∀ v ∈ W, (x : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤
  | _ => False

theorem trace_inv_conj (g y : GL (Fin 3) K) :
    ((g⁻¹ * y * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace =
      (y : Matrix (Fin 3) (Fin 3) K).trace := by
  rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul,
    mul_inv_cancel, Units.val_one, Matrix.one_mul]

theorem trace_mul_scalar (x : GL (Fin 3) K) (ζ : Kˣ) :
    ((x * GeneralLinearGroup.scalar (Fin 3) ζ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).trace = (ζ : K) * (x : Matrix (Fin 3) (Fin 3) K).trace := by
  rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul,
    smul_eq_mul]

theorem trace_diagTau {τ : K} (hτ : τ ^ 3 = 1) :
    ((diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace = τ + τ ^ 2 + 1 := by
  rw [coe_diagTau_eq_diagonal, trace_diagonal, Fin.sum_univ_three]
  simp

theorem trace_diagE (e : Kˣ) :
    ((diagE e : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace = (e : K) + 2 := by
  rw [coe_diagE, trace_diagonal, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  ring

theorem trace_eq_zero_of_type1 (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {x : GL (Fin 3) K} (hx : Type123 π (p ^ f) K x 1) :
    (x : Matrix (Fin 3) (Fin 3) K).trace = 0 := by
  obtain ⟨τ, hτ, hτ1, z, hz, g, -, hD⟩ := hx
  obtain ⟨ζ, -, rfl⟩ := exists_scalar_of_mem_zPi hK hq hτ hτ1 hz
  have h := trace_inv_conj g (x * GeneralLinearGroup.scalar (Fin 3) ζ)
  rw [hD, trace_diagTau, trace_mul_scalar] at h
  have hs := one_add_tau_add_sq hτ hτ1
  have h0 : (ζ : K) * (x : Matrix (Fin 3) (Fin 3) K).trace = 0 := by
    rw [← h]
    linear_combination hs
  exact (mul_eq_zero.mp h0).resolve_left ζ.ne_zero

theorem trace_ne_zero_of_type2 (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {x : GL (Fin 3) K} (hx : Type123 π (p ^ f) K x 2) :
    (x : Matrix (Fin 3) (Fin 3) K).trace ≠ 0 := by
  obtain ⟨e, he3, he1, z, hz, g, -, hD⟩ := hx
  have h3 := hK.three_ne_zero hq
  have hτ1 : (e : K) ≠ 1 := fun h => he1 (Units.ext h)
  obtain ⟨ζ, -, rfl⟩ := exists_scalar_of_mem_zPi hK hq he3 hτ1 hz
  have h := trace_inv_conj g (x * GeneralLinearGroup.scalar (Fin 3) ζ)
  rw [hD, trace_diagE, trace_mul_scalar] at h
  intro h0
  rw [h0, mul_zero] at h
  have he : (e : K) = -2 := by linear_combination h
  rw [he] at he3
  apply h3
  have h9 : (3 : K) * 3 = 0 := by linear_combination -he3
  exact mul_self_eq_zero.mp h9

theorem not_type123_one_two (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {x : GL (Fin 3) K} (h1 : Type123 π (p ^ f) K x 1) : ¬ Type123 π (p ^ f) K x 2 :=
  fun h2 => trace_ne_zero_of_type2 hK hq h2 (trace_eq_zero_of_type1 hK hq h1)

theorem not_irreducible_of_diag {x z g : GL (Fin 3) K} (hz : z ∈ StatedScalars (Fin 3) K)
    {d : Fin 3 → K} (hD : ((g⁻¹ * (x * z) * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal d) :
    ¬ ∀ W : Submodule K (Fin 3 → K), (∀ v ∈ W, (x : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W) →
      W = ⊥ ∨ W = ⊤ := by
  intro hirr
  obtain ⟨ζ, rfl⟩ := hz
  set v : Fin 3 → K := (g : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single 0 1 with hv
  have hv0 : v ≠ 0 := by
    intro h0
    have := congrArg (fun w => ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w) h0
    simp only [hv, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec, Matrix.mulVec_zero] at this
    have := congrFun this 0
    simp at this
  have hxv : (x : Matrix (Fin 3) (Fin 3) K) *ᵥ v = ((ζ : K)⁻¹ * d 0) • v := by
    have hxz : ((x * GeneralLinearGroup.scalar (Fin 3) ζ : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) * g = g * diagonal d := by
      rw [← hD, ← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    have h1 := congrArg (fun M => M *ᵥ (Pi.single 0 1 : Fin 3 → K)) hxz
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hv] at h1
    have hde : diagonal d *ᵥ (Pi.single 0 1 : Fin 3 → K) = d 0 • Pi.single 0 1 := by
      ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, diagonal]
    rw [hde, Matrix.mulVec_smul, ← hv] at h1
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mulVec] at h1
    rw [mul_smul, ← h1, smul_smul, inv_mul_cancel₀ ζ.ne_zero, one_smul]
  rcases hirr (K ∙ v) (fun w hw => by
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [Matrix.mulVec_smul, hxv, smul_smul]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)) with h | h
  · exact hv0 ((Submodule.span_singleton_eq_bot).mp h)
  · have := finrank_span_singleton (K := K) hv0
    rw [h, finrank_top, Module.finrank_fin_fun] at this
    omega

theorem mem_statedScalars_of_mem_zPi (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {z : GL (Fin 3) K} (hz : z ∈ zPi π 3 (p ^ f) K) :
    z ∈ StatedScalars (Fin 3) K := by
  obtain ⟨ζ, -, rfl⟩ := exists_scalar_of_mem_zPi hK hq hτ hτ1 hz
  exact ⟨ζ, rfl⟩

theorem not_type123_three_of_one (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {x : GL (Fin 3) K} (h1 : Type123 π (p ^ f) K x 1) : ¬ Type123 π (p ^ f) K x 3 := by
  obtain ⟨τ, hτ, hτ1, z, hz, g, -, hD⟩ := h1
  rintro ⟨-, -, hirr⟩
  refine not_irreducible_of_diag (g := g) (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz)
    (d := ![τ, τ ^ 2, 1]) ?_ hirr
  rw [hD, coe_diagTau_eq_diagonal]

theorem not_type123_three_of_two (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {x : GL (Fin 3) K} (h2 : Type123 π (p ^ f) K x 2) : ¬ Type123 π (p ^ f) K x 3 := by
  obtain ⟨e, he3, he1, z, hz, g, -, hD⟩ := h2
  have hτ1 : (e : K) ≠ 1 := fun h => he1 (Units.ext h)
  rintro ⟨-, -, hirr⟩
  refine not_irreducible_of_diag (g := g) (mem_statedScalars_of_mem_zPi hK hq he3 hτ1 hz)
    (d := ![(e : K), 1, 1]) ?_ hirr
  rw [hD, coe_diagE]

theorem type123_exhaust (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {x : GL (Fin 3) K} (hxH : x ∈ glPi π 3 (p ^ f) K) (hxZ : x ∉ zPi π 3 (p ^ f) K)
    (hx3 : x ^ 3 ∈ zPi π 3 (p ^ f) K) :
    Type123 π (p ^ f) K x 1 ∨ Type123 π (p ^ f) K x 2 ∨ Type123 π (p ^ f) K x 3 := by
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨y, ⟨z, hz, rfl⟩, h⟩ := rank3II_4_10_one hK hq hτ hτ1 hxH hxZ hx3
  rcases h with ⟨⟨g, hg, hD⟩, -, -⟩ | ⟨⟨g, hg, e, he, hD⟩, -, -⟩ | ⟨-, hirr, -⟩
  · exact Or.inl ⟨τ, hτ, hτ1, z, hz, g, hg, hD⟩
  · have he3 : (e : K) ^ 3 = 1 := by
      rcases he with he | he <;> rw [he]
      · exact hτ
      · rw [← pow_mul, pow_mul', hτ, one_pow]
    have he1 : e ≠ 1 := by
      rintro rfl
      rw [Units.val_one] at he
      rcases he with he | he
      · exact hτ1 he.symm
      · apply hτ1
        calc τ = τ ^ 3 / τ ^ 2 := by field_simp
          _ = 1 := by rw [hτ, ← he, div_one]
    exact Or.inr (Or.inl ⟨e, he3, he1, z, hz, g, hg, hD⟩)
  · exact Or.inr (Or.inr ⟨hxZ, hx3, hirr⟩)

@[expose] def IsTypeC (π : Bool) (q : ℕ) (K : Type) [Field K] (A : Subgroup (GL (Fin 3) K)) :
    Prop :=
  A ≤ glPi π 3 q K ∧ (∀ a ∈ A, a ^ 3 ∈ StatedScalars (Fin 3) K) ∧
    Nat.card ↥(A.map (QuotientGroup.mk' (StatedScalars (Fin 3) K))) = 9 ∧
    ∃ b : Fin 3 → Fin 3 → K, LinearIndependent K b ∧
      ∀ a ∈ A, ∀ i, ∃ c : K, (a : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = c • b i

@[expose] noncomputable def diagHom : Kˣ × Kˣ × Kˣ →* GL (Fin 3) K where
  toFun abc := diagUnits abc.1 abc.2.1 abc.2.2
  map_one' := by
    apply Units.ext
    rw [coe_diagUnits, Units.val_one, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp
  map_mul' abc abc' := by
    rw [diagUnits_mul]
    rfl

theorem coe_diagHom (abc : Kˣ × Kˣ × Kˣ) :
    ((diagHom abc : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![(abc.1 : K), abc.2.1, abc.2.2] :=
  rfl

theorem diagHom_injective : Function.Injective (diagHom (K := K)) := by
  intro abc abc' h
  have h' := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) h
  simp only [coe_diagHom] at h'
  have h0 := congrFun (congrFun h' 0) 0
  have h1 := congrFun (congrFun h' 1) 1
  have h2 := congrFun (congrFun h' 2) 2
  simp at h0 h1 h2
  exact Prod.ext (Units.ext h0) (Prod.ext (Units.ext h1) (Units.ext h2))

@[expose] def ratioHom : Kˣ × Kˣ × Kˣ →* Kˣ × Kˣ where
  toFun abc := (abc.2.1 * abc.1⁻¹, abc.2.2 * abc.1⁻¹)
  map_one' := by simp
  map_mul' abc abc' := by
    simp only [Prod.fst_mul, Prod.snd_mul, Prod.mk_mul_mk, _root_.mul_inv_rev]
    ext <;> simp only [Units.val_mul] <;> ring

theorem diagHom_mem_statedScalars_iff (abc : Kˣ × Kˣ × Kˣ) :
    diagHom abc ∈ StatedScalars (Fin 3) K ↔ ratioHom abc = 1 := by
  constructor
  · rintro ⟨c, hc⟩
    have h' := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hc
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, coe_diagHom] at h'
    have h0 := congrFun (congrFun h' 0) 0
    have h1 := congrFun (congrFun h' 1) 1
    have h2 := congrFun (congrFun h' 2) 2
    simp at h0 h1 h2
    have e1 : abc.2.1 = abc.1 := Units.ext (h1.symm.trans h0)
    have e2 : abc.2.2 = abc.1 := Units.ext (h2.symm.trans h0)
    simp [ratioHom, e1, e2]
  · intro h
    simp only [ratioHom, MonoidHom.coe_mk, OneHom.coe_mk, Prod.mk_eq_one, mul_inv_eq_one] at h
    refine ⟨abc.1, Units.ext ?_⟩
    rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, coe_diagHom, h.1, h.2]
    congr 1
    funext i
    fin_cases i <;> rfl

@[expose] noncomputable def stdTypeC (K : Type) [Field K] : Subgroup (GL (Fin 3) K) :=
  ((rootsOfUnity 3 K).prod ((rootsOfUnity 3 K).prod (rootsOfUnity 3 K))).map diagHom

theorem card_range_eq_of_ker_eq {E M N : Type*} [Group E] [Group M] [Group N] (ψ : E →* M)
    (χ : E →* N) (h : ψ.ker = χ.ker) : Nat.card ψ.range = Nat.card χ.range :=
  Nat.card_congr ((QuotientGroup.quotientKerEquivRange ψ).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq h).trans (QuotientGroup.quotientKerEquivRange χ))).toEquiv

theorem card_rootsOfUnity_three (hK : PiField π p f K) (hq : ModThree π (p ^ f)) :
    Nat.card (rootsOfUnity 3 K) = 3 := by
  have := hK.finite
  exact CFSG.LinearGroups.card_rootsOfUnity_of_dvd
    (dvd_trans (three_dvd_qSubPi hq) (qSubPi_dvd hK))

theorem card_mu3_prod (hK : PiField π p f K) (hq : ModThree π (p ^ f)) :
    Nat.card ↥((rootsOfUnity 3 K).prod (rootsOfUnity 3 K)) = 9 := by
  rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
    card_rootsOfUnity_three hK hq]

theorem cube_root_mem_qSubPi (hq : ModThree π (p ^ f)) {u : Kˣ}
    (hu : u ∈ rootsOfUnity 3 K) : u ∈ rootsOfUnity (qSubPi π (p ^ f)) K := by
  obtain ⟨k, hk⟩ := three_dvd_qSubPi hq
  rw [mem_rootsOfUnity] at hu ⊢
  rw [hk, pow_mul, hu, one_pow]

theorem diagUnits_mem_glPi (hK : PiField π p f K) {a b c : Kˣ}
    (ha : a ∈ rootsOfUnity (qSubPi π (p ^ f)) K) (hb : b ∈ rootsOfUnity (qSubPi π (p ^ f)) K)
    (hc : c ∈ rootsOfUnity (qSubPi π (p ^ f)) K) : diagUnits a b c ∈ glPi π 3 (p ^ f) K := by
  cases π
  · have h := hK.unitary
    rw [mem_glPi_false h, coe_diagUnits, diagonal_map (map_zero _), diagonal_transpose,
      diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    have hn : ∀ u : Kˣ, u ∈ rootsOfUnity (qSubPi false (p ^ f)) K →
        h.bar (u : K) * u = 1 := fun u hu => by
      have := congrArg Units.val ((mem_rootsOfUnity _ _).mp hu)
      rw [Units.val_pow_eq_pow_val, Units.val_one] at this
      rw [h.bar_apply, ← pow_succ]
      exact this
    funext i
    fin_cases i
    · exact hn a ha
    · exact hn b hb
    · exact hn c hc
  · exact mem_glPi_true _ _

theorem isTypeC_stdTypeC (hK : PiField π p f K) (hq : ModThree π (p ^ f)) :
    IsTypeC π (p ^ f) K (stdTypeC K) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro _ ⟨abc, ⟨ha, hb, hc⟩, rfl⟩
    exact diagUnits_mem_glPi hK (cube_root_mem_qSubPi hq ha) (cube_root_mem_qSubPi hq hb)
      (cube_root_mem_qSubPi hq hc)
  · rintro _ ⟨abc, ⟨ha, hb, hc⟩, rfl⟩
    rw [← map_pow]
    have : abc ^ 3 = 1 := by
      have ha' : abc.1 ∈ rootsOfUnity 3 K := ha
      have hb' : abc.2.1 ∈ rootsOfUnity 3 K := hb
      have hc' : abc.2.2 ∈ rootsOfUnity 3 K := hc
      rw [mem_rootsOfUnity] at ha' hb' hc'
      exact Prod.ext ha' (Prod.ext hb' hc')
    rw [this, map_one]
    exact one_mem _
  ·
    set E := (rootsOfUnity 3 K).prod ((rootsOfUnity 3 K).prod (rootsOfUnity 3 K)) with hE
    have hker : ((QuotientGroup.mk' (StatedScalars (Fin 3) K)).comp
        (diagHom.comp E.subtype)).ker = (ratioHom.comp E.subtype).ker := by
      ext abc
      simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.coe_subtype]
      exact diagHom_mem_statedScalars_iff _
    have h1 : ((QuotientGroup.mk' (StatedScalars (Fin 3) K)).comp
        (diagHom.comp E.subtype)).range = (stdTypeC K).map (QuotientGroup.mk' _) := by
      rw [MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.range_subtype, stdTypeC]
    have h2 : (ratioHom.comp E.subtype).range = (rootsOfUnity 3 K).prod (rootsOfUnity 3 K) := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
      apply le_antisymm
      · rintro _ ⟨abc, ⟨ha, hb, hc⟩, rfl⟩
        have ha' : abc.1 ∈ rootsOfUnity 3 K := ha
        have hb' : abc.2.1 ∈ rootsOfUnity 3 K := hb
        have hc' : abc.2.2 ∈ rootsOfUnity 3 K := hc
        have h1 : abc.2.1 * abc.1⁻¹ ∈ rootsOfUnity 3 K := mul_mem hb' (inv_mem ha')
        have h2 : abc.2.2 * abc.1⁻¹ ∈ rootsOfUnity 3 K := mul_mem hc' (inv_mem ha')
        exact ⟨h1, h2⟩
      · rintro ⟨s, t⟩ ⟨hs, ht⟩
        refine ⟨(1, s, t), ⟨one_mem _, hs, ht⟩, ?_⟩
        simp [ratioHom]
    rw [← h1, card_range_eq_of_ker_eq _ _ hker, h2, card_mu3_prod hK hq]
  · refine ⟨fun i => Pi.single i 1, ?_, ?_⟩
    · have : (fun i => (Pi.single i 1 : Fin 3 → K)) = ⇑(Pi.basisFun K (Fin 3)) :=
        funext fun i => (Pi.basisFun_apply K (Fin 3) i).symm
      rw [this]
      exact (Pi.basisFun K (Fin 3)).linearIndependent
    · rintro _ ⟨abc, -, rfl⟩ i
      refine ⟨![(abc.1 : K), abc.2.1, abc.2.2] i, ?_⟩
      rw [coe_diagHom]
      ext k
      fin_cases i <;> fin_cases k <;> simp [Matrix.mulVec, dotProduct, diagonal]

theorem coe_diagUnits_eq (a b c : Kˣ) :
    ((diagUnits a b c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![(a : K), 0, 0; 0, (b : K), 0; 0, 0, (c : K)] := by
  rw [coe_diagUnits]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem cycThree_conj_diagUnits (a b c : Kˣ) :
    cycThree * diagUnits a b c * cycThree⁻¹ = diagUnits c a b := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, show ((cycThree⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
    !![0, 1, 0; 0, 0, 1; 1, 0, 0] from rfl, coe_cycThree, coe_diagUnits_eq, coe_diagUnits_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]

theorem cycThree_inv_conj_diagUnits (a b c : Kˣ) :
    cycThree⁻¹ * diagUnits a b c * cycThree = diagUnits b c a := by
  have h := cycThree_conj_diagUnits (K := K) b c a
  calc cycThree⁻¹ * diagUnits a b c * cycThree =
      cycThree⁻¹ * (cycThree * diagUnits b c a * cycThree⁻¹) * cycThree := by rw [h]
    _ = diagUnits b c a := by group

theorem diagTau_eq_diagUnits {τ : K} (hτ : τ ^ 3 = 1) (hτ0 : τ ≠ 0) :
    diagTau hτ = diagUnits (Units.mk0 τ hτ0) (Units.mk0 τ hτ0 ^ 2) 1 := by
  apply Units.ext
  rw [coe_diagTau_eq_diagonal, coe_diagUnits]
  simp

theorem type123_of_diag (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {x g : GL (Fin 3) K}
    (hxH : x ∈ glPi π 3 (p ^ f) K) (hg : g ∈ glPi π 3 (p ^ f) K) {l s t : Kˣ}
    (hs : s ∈ rootsOfUnity 3 K) (ht : t ∈ rootsOfUnity 3 K)
    (hx : g⁻¹ * x * g = GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) :
    ((s ≠ 1 ∧ t ≠ 1 ∧ s ≠ t) → Type123 π (p ^ f) K x 1) ∧
      (¬ (s = 1 ∧ t = 1) → ¬ (s ≠ 1 ∧ t ≠ 1 ∧ s ≠ t) → Type123 π (p ^ f) K x 2) := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hcH : cycThree ∈ glPi π 3 (p ^ f) K := slPi_le_glPi hπ (cycThree_mem_slPi hπ)
  have hs3 : (s : K) ^ 3 = 1 := by
    have := congrArg Units.val ((mem_rootsOfUnity _ _).mp hs)
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
  have ht3 : (t : K) ^ 3 = 1 := by
    have := congrArg Units.val ((mem_rootsOfUnity _ _).mp ht)
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
  have hsc : ∀ (u : Kˣ) (A : GL (Fin 3) K),
      A * GeneralLinearGroup.scalar (Fin 3) u = GeneralLinearGroup.scalar (Fin 3) u * A :=
    fun u A => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u A).eq
  have hdH : diagUnits 1 s t ∈ glPi π 3 (p ^ f) K :=
    diagUnits_mem_glPi hK (one_mem _) (cube_root_mem_qSubPi hq hs) (cube_root_mem_qSubPi hq ht)
  have hlH : GeneralLinearGroup.scalar (Fin 3) l ∈ glPi π 3 (p ^ f) K := by
    have : GeneralLinearGroup.scalar (Fin 3) l = g⁻¹ * x * g * (diagUnits 1 s t)⁻¹ := by
      rw [hx, mul_inv_cancel_right]
    rw [this]
    exact mul_mem (mul_mem (mul_mem (inv_mem hg) hxH) hg) (inv_mem hdH)
  have hlT := (scalar_mem_glPi_iff hK l).mp hlH
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hform : ∀ ζ : Kˣ, g⁻¹ * (x * GeneralLinearGroup.scalar (Fin 3) (l⁻¹ * ζ)) * g =
      GeneralLinearGroup.scalar (Fin 3) ζ * diagUnits 1 s t := by
    intro ζ
    calc g⁻¹ * (x * GeneralLinearGroup.scalar (Fin 3) (l⁻¹ * ζ)) * g =
        g⁻¹ * x * (GeneralLinearGroup.scalar (Fin 3) (l⁻¹ * ζ) * g) := by group
      _ = g⁻¹ * x * (g * GeneralLinearGroup.scalar (Fin 3) (l⁻¹ * ζ)) := by rw [hsc]
      _ = g⁻¹ * x * g * GeneralLinearGroup.scalar (Fin 3) (l⁻¹ * ζ) := by group
      _ = GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t *
          GeneralLinearGroup.scalar (Fin 3) (l⁻¹ * ζ) := by rw [hx]
      _ = GeneralLinearGroup.scalar (Fin 3) ζ * diagUnits 1 s t := by
          rw [mul_assoc, hsc (l⁻¹ * ζ) (diagUnits 1 s t), ← mul_assoc, ← map_mul,
            mul_inv_cancel_left]
  have hzZ : ∀ ζ : Kˣ, ζ ∈ rootsOfUnity (qSubPi π (p ^ f)) K →
      GeneralLinearGroup.scalar (Fin 3) (l⁻¹ * ζ) ∈ zPi π 3 (p ^ f) K := fun ζ hζ =>
    scalar_mem_zPi hK hq hτ hτ1 (mul_mem (inv_mem hlT) hζ)
  have hs0 : (s : K) ≠ 0 := s.ne_zero
  refine ⟨fun ⟨hs1, ht1, hst⟩ => ?_, fun h11 hd => ?_⟩
  ·
    have hs1' : (s : K) ≠ 1 := fun h => hs1 (Units.ext h)
    have hts : t = s ^ 2 := by
      rcases cube_root_cases hs3 hs1' ht3 with h | h | h
      · exact absurd (Units.ext h) ht1
      · exact absurd (Units.ext h) (Ne.symm hst)
      · exact Units.ext (by rw [h, Units.val_pow_eq_pow_val])
    refine ⟨s, hs3, hs1', _, hzZ 1 (one_mem _), g * cycThree, mul_mem hg hcH, ?_⟩
    rw [_root_.mul_inv_rev, show cycThree⁻¹ * g⁻¹ * (x * GeneralLinearGroup.scalar (Fin 3)
      (l⁻¹ * 1)) * (g * cycThree) = cycThree⁻¹ * (g⁻¹ * (x * GeneralLinearGroup.scalar (Fin 3)
        (l⁻¹ * 1)) * g) * cycThree by group, hform 1, map_one, one_mul,
      cycThree_inv_conj_diagUnits, hts, diagTau_eq_diagUnits hs3 hs0]
    congr 1 <;> apply Units.ext <;> simp
  ·
    by_cases hs1 : s = 1
    · subst hs1
      have ht1 : t ≠ 1 := fun h => h11 ⟨rfl, h⟩
      refine ⟨t, ht3, ht1, _, hzZ 1 (one_mem _), g * cycThree⁻¹, mul_mem hg (inv_mem hcH), ?_⟩
      rw [_root_.mul_inv_rev, inv_inv, show cycThree * g⁻¹ * (x * GeneralLinearGroup.scalar (Fin 3)
        (l⁻¹ * 1)) * (g * cycThree⁻¹) = cycThree * (g⁻¹ * (x * GeneralLinearGroup.scalar (Fin 3)
          (l⁻¹ * 1)) * g) * cycThree⁻¹ by group, hform 1, map_one, one_mul,
        cycThree_conj_diagUnits]
      rfl
    · by_cases ht1 : t = 1
      · subst ht1
        refine ⟨s, hs3, hs1, _, hzZ 1 (one_mem _), g * cycThree, mul_mem hg hcH, ?_⟩
        rw [_root_.mul_inv_rev, show cycThree⁻¹ * g⁻¹ * (x * GeneralLinearGroup.scalar (Fin 3)
          (l⁻¹ * 1)) * (g * cycThree) = cycThree⁻¹ * (g⁻¹ * (x * GeneralLinearGroup.scalar (Fin 3)
            (l⁻¹ * 1)) * g) * cycThree by group, hform 1, map_one, one_mul,
          cycThree_inv_conj_diagUnits]
        rfl
      ·
        have hst : s = t := by
          by_contra hst
          exact hd ⟨hs1, ht1, hst⟩
        subst hst
        have hsinv3 : ((s⁻¹ : Kˣ) : K) ^ 3 = 1 := by
          rw [Units.val_inv_eq_inv_val, inv_pow, hs3, inv_one]
        have hsinv1 : s⁻¹ ≠ 1 := fun h => hs1 (inv_eq_one.mp h)
        refine ⟨s⁻¹, hsinv3, hsinv1, _, hzZ s⁻¹ (inv_mem (cube_root_mem_qSubPi hq hs)), g, hg, ?_⟩
        rw [hform s⁻¹]
        apply Units.ext
        rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, coe_diagUnits,
          coe_diagE, diagonal_mul_diagonal]
        congr 1
        funext i
        fin_cases i <;> simp

theorem norm_eq_one_of_eigen (h : UnitaryFieldData p f K) (hq : ModThree false (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {c : K} {y g : Matrix (Fin 3) (Fin 3) K}
    (hy : (y.map h.bar)ᵀ * y = 1) (hg : IsUnit g)
    (hyg : y * g = g * diagonal ![c, c * τ, c * τ ^ 2]) : h.bar c * c = 1 := by
  set d : Fin 3 → K := ![c, c * τ, c * τ ^ 2] with hd
  set G := (g.map h.bar)ᵀ * g with hGdef
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  have hbarτ : h.bar τ = τ ^ 2 := by
    rw [h.bar_apply]
    obtain ⟨k, hk⟩ : ∃ k, p ^ f = 3 * k + 2 := ⟨p ^ f / 3, by change p ^ f % 3 = 2 at hq; omega⟩
    rw [hk, pow_add, pow_mul, hτ, one_pow, one_mul]
  have hgdet : g.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det g).mp hg).ne_zero
  have hGdet : G.det ≠ 0 := by
    rw [hGdef, det_mul, det_transpose,
      show (g.map h.bar).det = h.bar g.det from (RingHom.map_det h.bar _).symm]
    exact mul_ne_zero ((map_ne_zero h.bar).mpr hgdet) hgdet
  have hGD : ((diagonal d).map h.bar)ᵀ * G * diagonal d = G := by
    have h1 : (((y * g).map h.bar)ᵀ) * (y * g) = G := by
      rw [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ y, hy,
        Matrix.one_mul]
    rw [hyg, Matrix.map_mul, Matrix.transpose_mul] at h1
    calc ((diagonal d).map h.bar)ᵀ * G * diagonal d =
        ((diagonal d).map h.bar)ᵀ * (g.map h.bar)ᵀ * (g * diagonal d) := by
          rw [hGdef]
          simp only [Matrix.mul_assoc]
      _ = G := h1
  have hentry : ∀ i j, G i j = h.bar (d i) * G i j * d j := by
    intro i j
    have := congrFun (congrFun hGD i) j
    rw [diagonal_map (map_zero _), diagonal_transpose, Matrix.mul_diagonal,
      Matrix.diagonal_mul] at this
    exact this.symm
  have hGh : ∀ i j, h.bar (G j i) = G i j := by
    intro i j
    simp only [hGdef, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum,
      map_mul, h.bar_bar]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hne : ∀ i j, G i j ≠ 0 → h.bar (d i) * d j = 1 := by
    intro i j hij
    have e := hentry i j
    have : G i j * (h.bar (d i) * d j) = G i j * 1 := by
      rw [mul_one]
      calc G i j * (h.bar (d i) * d j) = h.bar (d i) * G i j * d j := by ring
        _ = G i j := e.symm
    exact mul_left_cancel₀ hij this
  have hτne : τ ≠ τ ^ 2 := by
    intro h2
    apply hτ1
    have : τ * τ = τ * 1 := by rw [← sq, ← h2, mul_one]
    exact mul_left_cancel₀ hτ0 this
  have hG01 : G 0 1 = 0 := by
    by_contra h01
    have e1 := hne 0 1 h01
    have e2 := hne 1 0 (by rw [← hGh 1 0]; exact (map_ne_zero h.bar).mpr h01)
    simp only [hd, Matrix.cons_val_zero, Matrix.cons_val_one, map_mul, hbarτ] at e1 e2
    apply hτne
    have hc : h.bar c * c ≠ 0 := by
      intro h0
      rw [show h.bar c * (c * τ) = h.bar c * c * τ by ring, h0, zero_mul] at e1
      exact zero_ne_one e1
    have : h.bar c * c * τ = h.bar c * c * τ ^ 2 := by linear_combination e1 - e2
    exact mul_left_cancel₀ hc this
  have hG02 : G 0 2 = 0 := by
    by_contra h02
    have e1 := hne 0 2 h02
    have e2 := hne 2 0 (by rw [← hGh 2 0]; exact (map_ne_zero h.bar).mpr h02)
    simp only [hd, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons, map_mul, map_pow, hbarτ] at e1 e2
    apply hτne
    have hc : h.bar c * c ≠ 0 := by
      intro h0
      rw [show h.bar c * (c * τ ^ 2) = h.bar c * c * τ ^ 2 by ring, h0, zero_mul] at e1
      exact zero_ne_one e1
    have h4 : τ ^ 4 = τ := by
      calc τ ^ 4 = τ ^ 3 * τ := by ring
        _ = τ := by rw [hτ, one_mul]
    have : h.bar c * c * τ = h.bar c * c * τ ^ 2 := by
      linear_combination e2 - e1 - h.bar c * c * h4
    exact mul_left_cancel₀ hc this
  have hG00 : G 0 0 ≠ 0 := by
    intro h00
    apply hGdet
    rw [Matrix.det_fin_three, h00, hG01, hG02]
    ring
  have := hne 0 0 hG00
  simpa [hd] using this

theorem diagHom_eq_scalar_mul (abc : Kˣ × Kˣ × Kˣ) :
    diagHom abc = GeneralLinearGroup.scalar (Fin 3) abc.1 *
      diagUnits 1 (ratioHom abc).1 (ratioHom abc).2 := by
  apply Units.ext
  rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, coe_diagHom,
    coe_diagUnits, diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp [ratioHom] <;> field_simp

open CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary in
theorem isTypeC_conj_std (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {A : Subgroup (GL (Fin 3) K)} (hA : IsTypeC π (p ^ f) K A) :
    ∃ g ∈ glPi π 3 (p ^ f) K,
      (∀ a ∈ A, ∃ l s t : Kˣ, s ∈ rootsOfUnity 3 K ∧ t ∈ rootsOfUnity 3 K ∧
        g⁻¹ * a * g = GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) ∧
      (∀ s ∈ rootsOfUnity 3 K, ∀ t ∈ rootsOfUnity 3 K, ∃ a ∈ A, ∃ l : Kˣ,
        g⁻¹ * a * g = GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) := by
  have := hK.finite
  obtain ⟨hAH, hA3, hAcard, b, hb, hAb⟩ := hA
  have hP : IsUnit (colMat b) := isUnit_colMat hb
  set P := hP.unit with hPdef
  have hPm : (P : Matrix (Fin 3) (Fin 3) K) = colMat b := IsUnit.unit_spec hP
  have hPinv : ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * colMat b = 1 := by
    rw [← hPm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hdiag : ∀ a ∈ A, ∃ abc : Kˣ × Kˣ × Kˣ, P⁻¹ * a * P = diagHom abc := by
    intro a ha
    choose c hc using hAb a ha
    have hc0 : ∀ i, c i ≠ 0 := by
      intro i h0
      have hbi : b i ≠ 0 := hb.ne_zero i
      have h1 := hc i
      rw [h0, zero_smul] at h1
      apply hbi
      have h2 := congrArg (fun w => ((a⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w) h1
      simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h2
      rwa [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at h2
    refine ⟨(Units.mk0 (c 0) (hc0 0), Units.mk0 (c 1) (hc0 1), Units.mk0 (c 2) (hc0 2)), ?_⟩
    have hmul := mul_colMat_eq hc
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_diagHom, hPm, Matrix.mul_assoc, hmul,
      ← Matrix.mul_assoc, hPinv, Matrix.one_mul]
    congr 1
    funext i
    fin_cases i <;> rfl
  choose θf hθf using hdiag
  let θ : ↥A →* Kˣ × Kˣ × Kˣ := MonoidHom.mk' (fun a => θf a a.2) fun a a' =>
    diagHom_injective (by
      rw [map_mul, ← hθf _ a.2, ← hθf _ a'.2, ← hθf _ (a * a').2, Subgroup.coe_mul]
      group)
  have hθ : ∀ a : ↥A, P⁻¹ * (a : GL (Fin 3) K) * P = diagHom (θ a) := fun a => hθf a a.2
  set ψ := ratioHom.comp θ with hψ
  have hsc : ∀ (u : Kˣ) (B : GL (Fin 3) K),
      B * GeneralLinearGroup.scalar (Fin 3) u = GeneralLinearGroup.scalar (Fin 3) u * B :=
    fun u B => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u B).eq
  have hconjSc : ∀ B : GL (Fin 3) K, P⁻¹ * B * P ∈ StatedScalars (Fin 3) K ↔
      B ∈ StatedScalars (Fin 3) K := by
    intro B
    constructor
    · rintro ⟨u, hu⟩
      refine ⟨u, ?_⟩
      calc GeneralLinearGroup.scalar (Fin 3) u = P * (P⁻¹ * B * P) * P⁻¹ := by
            rw [← hu, hsc u P, mul_inv_cancel_right]
        _ = B := by group
    · rintro ⟨u, rfl⟩
      refine ⟨u, ?_⟩
      rw [hsc u P⁻¹, inv_mul_cancel_right]
  have hker : ψ.ker = ((QuotientGroup.mk' (StatedScalars (Fin 3) K)).comp A.subtype).ker := by
    ext a
    simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.coe_subtype, hψ]
    rw [← diagHom_mem_statedScalars_iff, ← hθ a, hconjSc]
  have hrange9 : Nat.card ψ.range = 9 := by
    rw [card_range_eq_of_ker_eq _ _ hker, MonoidHom.range_comp, Subgroup.range_subtype, hAcard]
  have hle : ψ.range ≤ (rootsOfUnity 3 K).prod (rootsOfUnity 3 K) := by
    rintro _ ⟨a, rfl⟩
    have h3 : ψ a ^ 3 = 1 := by
      have : a ^ 3 ∈ ψ.ker := by
        rw [hker, MonoidHom.mem_ker]
        simp only [MonoidHom.coe_comp, Function.comp_apply, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff, Subgroup.coe_subtype, SubgroupClass.coe_pow]
        exact hA3 a a.2
      rw [← map_pow]
      exact this
    exact ⟨(mem_rootsOfUnity _ _).mpr (by rw [← Prod.pow_fst, h3]; rfl),
      (mem_rootsOfUnity _ _).mpr (by rw [← Prod.pow_snd, h3]; rfl)⟩
  have hrange : ψ.range = (rootsOfUnity 3 K).prod (rootsOfUnity 3 K) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [card_mu3_prod hK hq, hrange9])
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  set τu := Units.mk0 τ hτ0 with hτudef
  have hτu : τu ∈ rootsOfUnity 3 K := (mem_rootsOfUnity _ _).mpr (Units.ext (by simp [hτudef, hτ]))
  obtain ⟨a₀, ha₀⟩ : (τu, τu ^ 2) ∈ ψ.range := by
    rw [hrange]
    exact ⟨hτu, pow_mem hτu 2⟩
  set c := ((θ a₀).1 : K) with hcdef
  have hθa₀ : ((diagHom (θ a₀) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![c, c * τ, c * τ ^ 2] := by
    have h1 := congrArg Prod.fst ha₀
    have h2 := congrArg Prod.snd ha₀
    simp only [hψ, MonoidHom.coe_comp, Function.comp_apply, ratioHom, MonoidHom.coe_mk,
      OneHom.coe_mk] at h1 h2
    have e1 : ((θ a₀).2.1 : K) = c * τ := by
      have := congrArg Units.val h1
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, hτudef, Units.val_mk0] at this
      rw [hcdef, ← this]
      field_simp
    have e2 : ((θ a₀).2.2 : K) = c * τ ^ 2 := by
      have := congrArg Units.val h2
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, hτudef,
        Units.val_mk0] at this
      rw [hcdef, ← this]
      field_simp
    rw [coe_diagHom, e1, e2]
  have hd : (c ≠ c * τ ∧ c ≠ c * τ ^ 2 ∧ c * τ ≠ c * τ ^ 2) := by
    have hc0 : c ≠ 0 := (θ a₀).1.ne_zero
    have hτ2 : τ ^ 2 ≠ 1 := by
      intro h2
      apply hτ1
      calc τ = τ ^ 3 / τ ^ 2 := by field_simp
        _ = 1 := by rw [hτ, h2, div_one]
    have hττ : τ ≠ τ ^ 2 := by
      intro h2
      apply hτ1
      have : τ * τ = τ * 1 := by rw [← sq, ← h2, mul_one]
      exact mul_left_cancel₀ hτ0 this
    refine ⟨fun h => hτ1 ?_, fun h => hτ2 ?_, fun h => hττ ?_⟩
    · exact (mul_left_cancel₀ hc0 (by rw [mul_one]; exact h.symm))
    · exact (mul_left_cancel₀ hc0 (by rw [mul_one]; exact h.symm))
    · exact mul_left_cancel₀ hc0 h
  have hyP : ((a₀ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * P =
      P * diagonal ![c, c * τ, c * τ ^ 2] := by
    rw [← hθa₀, ← hθ a₀, Units.val_mul, Units.val_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      ← Units.val_mul P, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  obtain ⟨g, hgH, hg⟩ : ∃ g ∈ glPi π 3 (p ^ f) K,
      ((a₀ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * g =
        g * diagonal ![c, c * τ, c * τ ^ 2] := by
    cases π
    · have h := hK.unitary
      have : Fact p.Prime := ⟨hK.prime⟩
      have := hK.charP
      set σ := CFSG.LieType.BorelTits.unitaryInvolution K p f
      have hσ : IsUnitaryInvolution σ :=
        isUnitaryInvolution_unitaryInvolution (by rw [hK.card]; rfl)
      have hyH := (mem_glPi_false h).mp (hAH a₀.2)
      have hn := norm_eq_one_of_eigen h hq hτ hτ1 hyH P.isUnit hyP
      have hyu : conjTr σ ((a₀ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((a₀ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
        rw [conjTr_unitaryInvolution_eq hK]
        exact hyH
      have hbarτ : h.bar τ * τ = 1 := by
        rw [h.bar_apply, ← pow_succ]
        exact pow_succ_eq_one_of_modThree hq hτ
      have hdσ : ∀ i, σ (![c, c * τ, c * τ ^ 2] i) * ![c, c * τ, c * τ ^ 2] i = 1 := by
        have hσb : ∀ x, σ x = h.bar x := fun x => by
          rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, h.bar_apply]
        intro i
        fin_cases i
        · change σ c * c = 1
          rw [hσb]
          exact hn
        · change σ (c * τ) * (c * τ) = 1
          rw [hσb, map_mul]
          linear_combination (h.bar τ * τ) * hn + hbarτ
        · change σ (c * τ ^ 2) * (c * τ ^ 2) = 1
          rw [hσb, map_mul, map_pow]
          linear_combination (h.bar τ * τ) ^ 2 * hn + (h.bar τ * τ + 1) * hbarτ
      obtain ⟨g', hg'u, hyg'⟩ := exists_unitary_conj hσ hdσ (Or.inl hd) hyu P.isUnit hyP
      have hg' : IsUnit g' :=
        (Matrix.isUnit_iff_isUnit_det g').mpr (Matrix.isUnit_det_of_left_inverse hg'u)
      refine ⟨hg'.unit, ?_, by rw [IsUnit.unit_spec]; exact hyg'⟩
      rw [mem_glPi_false h, IsUnit.unit_spec, ← conjTr_unitaryInvolution_eq hK]
      exact hg'u
    · exact ⟨P, mem_glPi_true _ _, hyP⟩
  obtain ⟨U, hU⟩ : ∃ U : GL (Fin 3) K, U = P⁻¹ * g := ⟨_, rfl⟩
  have hUD : (U : Matrix (Fin 3) (Fin 3) K) * diagonal ![c, c * τ, c * τ ^ 2] =
      diagonal ![c, c * τ, c * τ ^ 2] * U := by
    have hPa₀ : ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((a₀ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        diagonal ![c, c * τ, c * τ ^ 2] * ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [← hθa₀, ← hθ a₀, Units.val_mul, Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc,
        ← Units.val_mul P, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    rw [hU, Units.val_mul, Matrix.mul_assoc, ← hg, ← Matrix.mul_assoc, hPa₀, Matrix.mul_assoc]
  have hUdiag : (U : Matrix (Fin 3) (Fin 3) K) =
      diagonal fun i => (U : Matrix (Fin 3) (Fin 3) K) i i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · rw [diagonal_apply_ne _ hij]
      apply entry_eq_zero_of_commute_diagonal hUD
      obtain ⟨h01, h02, h12⟩ := hd
      fin_cases i <;> fin_cases j <;>
        first | exact absurd rfl hij | exact h01 | exact h02 | exact h12 | exact Ne.symm h01 |
          exact Ne.symm h02 | exact Ne.symm h12
  have hgA : ∀ a : ↥A, g⁻¹ * (a : GL (Fin 3) K) * g = diagHom (θ a) := by
    intro a
    have hcomm : diagHom (θ a) * U = U * diagHom (θ a) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, coe_diagHom, hUdiag, diagonal_mul_diagonal,
        diagonal_mul_diagonal]
      congr 1
      funext i
      exact mul_comm _ _
    have hgPU : g = P * U := by rw [hU]; group
    calc g⁻¹ * (a : GL (Fin 3) K) * g = U⁻¹ * (P⁻¹ * a * P) * U := by rw [hgPU]; group
      _ = U⁻¹ * (diagHom (θ a) * U) := by rw [hθ a, mul_assoc]
      _ = diagHom (θ a) := by rw [hcomm]; group
  refine ⟨g, hgH, fun a ha => ?_, fun s hs t ht => ?_⟩
  · obtain ⟨hs, ht⟩ := hle ⟨⟨a, ha⟩, rfl⟩
    exact ⟨(θ ⟨a, ha⟩).1, (ψ ⟨a, ha⟩).1, (ψ ⟨a, ha⟩).2, hs, ht, by
      rw [hgA ⟨a, ha⟩, diagHom_eq_scalar_mul]
      rfl⟩
  · obtain ⟨a, ha⟩ : (s, t) ∈ ψ.range := by
      rw [hrange]
      exact ⟨hs, ht⟩
    refine ⟨a, a.2, (θ a).1, ?_⟩
    rw [hgA a, diagHom_eq_scalar_mul]
    have : ratioHom (θ a) = (s, t) := ha
    rw [this]

theorem scalar_mul_diagUnits_eq (x u v : Kˣ) :
    GeneralLinearGroup.scalar (Fin 3) x * diagUnits 1 u v = diagHom (x, x * u, x * v) := by
  apply Units.ext
  rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, coe_diagUnits,
    coe_diagHom, diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp

theorem scalar_mul_diagUnits_mem_iff (x u v : Kˣ) :
    GeneralLinearGroup.scalar (Fin 3) x * diagUnits 1 u v ∈ StatedScalars (Fin 3) K ↔
      u = 1 ∧ v = 1 := by
  rw [scalar_mul_diagUnits_eq, diagHom_mem_statedScalars_iff]
  simp only [ratioHom, MonoidHom.coe_mk, OneHom.coe_mk, Prod.mk_eq_one]
  rw [mul_comm x u, mul_inv_cancel_right, mul_comm x v, mul_inv_cancel_right]

theorem scalar_diagUnits_mul_inv (x u v y u' v' : Kˣ) :
    GeneralLinearGroup.scalar (Fin 3) x * diagUnits 1 u v *
        (GeneralLinearGroup.scalar (Fin 3) y * diagUnits 1 u' v')⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) (x * y⁻¹) * diagUnits 1 (u * u'⁻¹) (v * v'⁻¹) := by
  rw [scalar_mul_diagUnits_eq, scalar_mul_diagUnits_eq, scalar_mul_diagUnits_eq, ← map_inv,
    ← map_mul]
  congr 1
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> apply Units.ext <;>
    simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv, Units.val_mul,
      Units.val_inv_eq_inv_val] <;> ring

theorem scalar_diagUnits_mul (x u v y u' v' : Kˣ) :
    GeneralLinearGroup.scalar (Fin 3) x * diagUnits 1 u v *
        (GeneralLinearGroup.scalar (Fin 3) y * diagUnits 1 u' v') =
      GeneralLinearGroup.scalar (Fin 3) (x * y) * diagUnits 1 (u * u') (v * v') := by
  rw [scalar_mul_diagUnits_eq, scalar_mul_diagUnits_eq, scalar_mul_diagUnits_eq, ← map_mul]
  congr 1
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only [Prod.fst_mul, Prod.snd_mul] <;>
    rw [mul_mul_mul_comm]

theorem inv_conj_mem_statedScalars_iff (g y : GL (Fin 3) K) :
    g⁻¹ * y * g ∈ StatedScalars (Fin 3) K ↔ y ∈ StatedScalars (Fin 3) K := by
  have hsc : ∀ (u : Kˣ) (B : GL (Fin 3) K),
      B * GeneralLinearGroup.scalar (Fin 3) u = GeneralLinearGroup.scalar (Fin 3) u * B :=
    fun u B => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u B).eq
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    calc GeneralLinearGroup.scalar (Fin 3) u = g * (g⁻¹ * y * g) * g⁻¹ := by
          rw [← hu, hsc u g, mul_inv_cancel_right]
      _ = y := by group
  · rintro ⟨u, rfl⟩
    refine ⟨u, ?_⟩
    rw [hsc u g⁻¹, inv_mul_cancel_right]

theorem isTypeC_types (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {A : Subgroup (GL (Fin 3) K)} (hA : IsTypeC π (p ^ f) K A) :
    ∃ a₁ ∈ A, Type123 π (p ^ f) K a₁ 1 ∧ ∀ a ∈ A, a ∉ StatedScalars (Fin 3) K →
      ((Type123 π (p ^ f) K a 1 ↔
          a * a₁⁻¹ ∈ StatedScalars (Fin 3) K ∨ a * a₁ ∈ StatedScalars (Fin 3) K) ∧
        (¬ Type123 π (p ^ f) K a 1 → Type123 π (p ^ f) K a 2)) := by
  have hAH := hA.1
  obtain ⟨g, hgH, hdiag, hsurj⟩ := isTypeC_conj_std hK hq hA
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  set τu := Units.mk0 τ hτ0 with hτudef
  have hτu : τu ∈ rootsOfUnity 3 K := (mem_rootsOfUnity _ _).mpr (Units.ext (by simp [hτudef, hτ]))
  have hτu3 : τu ^ 3 = 1 := (mem_rootsOfUnity _ _).mp hτu
  have hτu1 : τu ≠ 1 := fun h => hτ1 (by rw [← Units.val_mk0 hτ0, ← hτudef, h, Units.val_one])
  have hτu2 : τu ^ 2 ≠ 1 := by
    intro h2
    apply hτu1
    calc τu = τu ^ 3 * (τu ^ 2)⁻¹ := by group
      _ = 1 := by rw [hτu3, h2]; group
  have hτuτu2 : τu ≠ τu ^ 2 := by
    intro h2
    apply hτu1
    calc τu = τu ^ 2 * τu⁻¹ := by group
      _ = 1 := by rw [← h2]; group
  obtain ⟨a₁, ha₁, l₁, hl₁⟩ := hsurj τu hτu (τu ^ 2) (pow_mem hτu 2)
  refine ⟨a₁, ha₁, (type123_of_diag hK hq (hAH ha₁) hgH hτu (pow_mem hτu 2) hl₁).1
    ⟨hτu1, hτu2, hτuτu2⟩, fun a ha haZ => ?_⟩
  obtain ⟨l, s, t, hs, ht, hl⟩ := hdiag a ha
  have hst1 : ¬ (s = 1 ∧ t = 1) := by
    rintro ⟨rfl, rfl⟩
    apply haZ
    rw [← inv_conj_mem_statedScalars_iff g, hl]
    exact (scalar_mul_diagUnits_mem_iff l 1 1).mpr ⟨rfl, rfl⟩
  have htypes := type123_of_diag hK hq (hAH ha) hgH hs ht hl
  have h1iff : Type123 π (p ^ f) K a 1 ↔ (s ≠ 1 ∧ t ≠ 1 ∧ s ≠ t) := by
    constructor
    · intro h1
      by_contra hd
      exact not_type123_one_two hK hq h1 (htypes.2 hst1 hd)
    · exact htypes.1
  have hs3 : s ^ 3 = 1 := (mem_rootsOfUnity _ _).mp hs
  have ht3 : t ^ 3 = 1 := (mem_rootsOfUnity _ _).mp ht
  have hroot : ∀ u : Kˣ, u ^ 3 = 1 → u = 1 ∨ u = τu ∨ u = τu ^ 2 := by
    intro u hu
    have hu' : (u : K) ^ 3 = 1 := by
      have := congrArg Units.val hu
      rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
    rcases cube_root_cases hτ hτ1 hu' with h | h | h
    · exact Or.inl (Units.ext h)
    · exact Or.inr (Or.inl (Units.ext h))
    · exact Or.inr (Or.inr (Units.ext (by rw [h, Units.val_pow_eq_pow_val, hτudef, Units.val_mk0])))
  have hdist : (s ≠ 1 ∧ t ≠ 1 ∧ s ≠ t) ↔ ((s = τu ∧ t = τu ^ 2) ∨ (s = τu ^ 2 ∧ t = τu)) := by
    constructor
    · rintro ⟨hs1, ht1, hst⟩
      rcases hroot s hs3 with h | h | h
      · exact absurd h hs1
      · rcases hroot t ht3 with h' | h' | h'
        · exact absurd h' ht1
        · exact absurd (h.trans h'.symm) hst
        · exact Or.inl ⟨h, h'⟩
      · rcases hroot t ht3 with h' | h' | h'
        · exact absurd h' ht1
        · exact Or.inr ⟨h, h'⟩
        · exact absurd (h.trans h'.symm) hst
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨hτu1, hτu2, hτuτu2⟩
      · exact ⟨hτu2, hτu1, Ne.symm hτuτu2⟩
  have hc1 : a * a₁⁻¹ ∈ StatedScalars (Fin 3) K ↔ (s = τu ∧ t = τu ^ 2) := by
    rw [← inv_conj_mem_statedScalars_iff g, show g⁻¹ * (a * a₁⁻¹) * g =
      (g⁻¹ * a * g) * (g⁻¹ * a₁ * g)⁻¹ by group, hl, hl₁, scalar_diagUnits_mul_inv,
      scalar_mul_diagUnits_mem_iff, mul_inv_eq_one, mul_inv_eq_one]
  have hc2 : a * a₁ ∈ StatedScalars (Fin 3) K ↔ (s = τu ^ 2 ∧ t = τu) := by
    rw [← inv_conj_mem_statedScalars_iff g, show g⁻¹ * (a * a₁) * g =
      (g⁻¹ * a * g) * (g⁻¹ * a₁ * g) by group, hl, hl₁, scalar_diagUnits_mul,
      scalar_mul_diagUnits_mem_iff]
    have e1 : s * τu = 1 ↔ s = τu ^ 2 := by
      rw [mul_eq_one_iff_eq_inv]
      have : τu⁻¹ = τu ^ 2 := by
        rw [inv_eq_iff_mul_eq_one, ← pow_succ', hτu3]
      rw [this]
    have e2 : t * τu ^ 2 = 1 ↔ t = τu := by
      rw [mul_eq_one_iff_eq_inv]
      have : (τu ^ 2)⁻¹ = τu := by
        rw [inv_eq_iff_mul_eq_one, ← pow_succ, hτu3]
      rw [this]
    rw [e1, e2]
  exact ⟨by rw [h1iff, hdist, hc1, hc2], fun hn1 => htypes.2 hst1 fun hd => hn1 (h1iff.mpr hd)⟩

theorem isTypeC_diagonal (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {A : Subgroup (GL (Fin 3) K)} (hA : IsTypeC π (p ^ f) K A) :
    ∃ g ∈ glPi π 3 (p ^ f) K, ∀ a ∈ A, ∃ d₀ d₁ d₂ : Kˣ, g⁻¹ * a * g = diagUnits d₀ d₁ d₂ := by
  obtain ⟨g, hgH, hdiag, -⟩ := isTypeC_conj_std hK hq hA
  refine ⟨g, hgH, fun a ha => ?_⟩
  obtain ⟨l, s, t, -, -, hl⟩ := hdiag a ha
  exact ⟨l, l * s, l * t, by rw [hl, scalar_mul_diagUnits_eq]; rfl⟩

end CFSG.RankThree.PartTwo.Sec4

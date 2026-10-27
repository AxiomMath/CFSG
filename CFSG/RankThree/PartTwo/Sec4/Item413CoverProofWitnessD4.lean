module

public import CFSG.RankThree.PartTwo.Sec21.LangTwisted3ProofD4Even

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open Matrix
open scoped MatrixGroups

section Transport

variable {H X : Type*} [Group H] [Group X]

theorem HasLocalWitness.of_injective_of_fix {β : MulAut H} (h : HasLocalWitness β) (φ : H →* X)
    (hφ : Function.Injective φ) {α : MulAut X} (hα : ∀ x, α (φ x) = φ x) :
    HasLocalWitness α := by
  obtain ⟨y₁, y₂, U, -, -, h₁3, h₂3, hc, h₁1, h₂₁, hU2, hU1, hUy₁, hUy₂, -⟩ := h
  refine ⟨φ y₁, φ y₂, U.map φ, hα y₁, hα y₂, ?_, ?_, ?_, ?_, ?_, hU2.map φ, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, h₁3, map_one]
  · rw [← map_pow, h₂3, map_one]
  · rw [← map_mul, hc, map_mul]
  · intro h
    exact h₁1 (hφ (h.trans (map_one φ).symm))
  · rintro ⟨k, hk⟩
    apply h₂₁
    refine ⟨k, hφ ?_⟩
    rw [map_zpow]
    exact hk
  · intro h
    apply hU1
    rw [eq_bot_iff]
    intro u hu
    have : φ u ∈ U.map φ := ⟨u, hu, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (hφ (this.trans (map_one φ).symm))
  · rintro _ ⟨u, hu, rfl⟩
    exact ⟨y₁ * u * y₁⁻¹, hUy₁ u hu, by simp⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact ⟨y₂ * u * y₂⁻¹, hUy₂ u hu, by simp⟩
  · rintro _ ⟨u, hu, rfl⟩
    rw [hα u]
    exact ⟨u, hu, rfl⟩

end Transport

namespace WitnessPGL

variable {K : Type} [Field K]

@[expose] def diagAB (a b : Kˣ) : GL (Fin 3) K :=
  ⟨!![(a : K), 0, 0; 0, (b : K), 0; 0, 0, 1],
    !![((a⁻¹ : Kˣ) : K), 0, 0; 0, ((b⁻¹ : Kˣ) : K), 0; 0, 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]⟩

theorem coe_diagAB (a b : Kˣ) :
    ((diagAB a b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![(a : K), 0, 0; 0, (b : K), 0; 0, 0, 1] :=
  rfl

@[expose] def diagHom : Kˣ × Kˣ →* GL (Fin 3) K where
  toFun x := diagAB x.1 x.2
  map_one' := by
    ext i j
    rw [coe_diagAB]
    fin_cases i <;> fin_cases j <;> simp
  map_mul' x y := by
    ext i j
    rw [Units.val_mul, coe_diagAB, coe_diagAB, coe_diagAB]
    fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]

theorem coe_diagHom (x : Kˣ × Kˣ) :
    ((diagHom x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![(x.1 : K), 0, 0; 0, (x.2 : K), 0; 0, 0, 1] :=
  rfl

@[expose] def transv (t : K) : GL (Fin 3) K :=
  ⟨!![1, 0, t; 0, 1, 0; 0, 0, 1], !![1, 0, -t; 0, 1, 0; 0, 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]⟩

theorem coe_transv (t : K) :
    ((transv t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = !![1, 0, t; 0, 1, 0; 0, 0, 1] :=
  rfl

@[expose] def transvHom : Multiplicative K →* GL (Fin 3) K where
  toFun t := transv (Multiplicative.toAdd t)
  map_one' := by
    ext i j
    rw [coe_transv]
    fin_cases i <;> fin_cases j <;> simp
  map_mul' s t := by
    ext i j
    rw [Units.val_mul, coe_transv, coe_transv, coe_transv]
    fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, add_comm]

theorem coe_transvHom (t : Multiplicative K) :
    ((transvHom t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![1, 0, Multiplicative.toAdd t; 0, 1, 0; 0, 0, 1] :=
  rfl

theorem diagHom_mul_transvHom (x : Kˣ × Kˣ) (t : Multiplicative K) :
    diagHom x * transvHom t =
      transvHom (Multiplicative.ofAdd ((x.1 : K) * Multiplicative.toAdd t)) * diagHom x := by
  ext i j
  rw [Units.val_mul, Units.val_mul, coe_diagHom, coe_transvHom, coe_transvHom]
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]

theorem eq_of_mk_diagHom_eq {x y : Kˣ × Kˣ}
    (h : ProjGenLinGroup.mk (diagHom x) = ProjGenLinGroup.mk (diagHom y)) : x = y := by
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.1 h
  have e : ∀ i j, ((diagHom x * GeneralLinearGroup.scalar (Fin 3) u : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) i j = ((diagHom y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j :=
    fun i j => by rw [hu]
  have h00 := e 0 0
  have h11 := e 1 1
  have h22 := e 2 2
  simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, coe_diagHom] at h00 h11 h22
  simp [mul_apply, Fin.sum_univ_three] at h00 h11 h22
  have hu1 : u = 1 := h22
  subst hu1
  simp only [Units.val_one, mul_one] at h00 h11
  exact Prod.ext (Units.ext h00) (Units.ext h11)

theorem mk_transvHom_one_ne_one :
    ProjGenLinGroup.mk (transvHom (Multiplicative.ofAdd (1 : K))) ≠ 1 := by
  intro h
  rw [← ProjGenLinGroup.mk_one, ProjGenLinGroup.mk_eq_mk_iff] at h
  obtain ⟨u, hu⟩ := h
  have h02 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 2) hu
  simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, coe_transvHom, Units.val_one] at h02
  simp [mul_apply, Fin.sum_univ_three] at h02

theorem hasLocalWitness_pgl [CharP K 2] {ω : Kˣ} (hω : orderOf ω = 3) :
    HasLocalWitness (1 : MulAut (PGL(3, K))) := by
  have hω3 : ω ^ 3 = 1 := by rw [← hω, pow_orderOf_eq_one]
  have hω1 : ω ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hω
    omega
  set a : Kˣ × Kˣ := (ω, 1) with ha
  set b : Kˣ × Kˣ := (1, ω) with hb
  have ha3 : a ^ 3 = 1 := by rw [ha, Prod.pow_mk, hω3, one_pow, Prod.mk_one_one]
  have hb3 : b ^ 3 = 1 := by rw [hb, Prod.pow_mk, hω3, one_pow, Prod.mk_one_one]
  set U : Subgroup (PGL(3, K)) := (ProjGenLinGroup.mk.comp transvHom).range with hU
  have hconj : ∀ (x : Kˣ × Kˣ) (t : Multiplicative K),
      ProjGenLinGroup.mk (diagHom x) * ProjGenLinGroup.mk (transvHom t) *
          (ProjGenLinGroup.mk (diagHom x))⁻¹ =
        ProjGenLinGroup.mk (transvHom (Multiplicative.ofAdd ((x.1 : K) *
          Multiplicative.toAdd t))) := by
    intro x t
    rw [← map_mul, ← map_inv, ← map_mul, diagHom_mul_transvHom, mul_inv_cancel_right]
  refine ⟨ProjGenLinGroup.mk (diagHom a), ProjGenLinGroup.mk (diagHom b), U, rfl, rfl, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun u hu => hu⟩
  · rw [← map_pow, ← map_pow, ha3, map_one, map_one]
  · rw [← map_pow, ← map_pow, hb3, map_one, map_one]
  · rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, mul_comm a b]
  · intro h
    have h1 : ProjGenLinGroup.mk (diagHom a) = ProjGenLinGroup.mk (diagHom (1 : Kˣ × Kˣ)) := by
      rw [h, map_one, map_one]
    have h2 := congrArg Prod.fst (eq_of_mk_diagHom_eq h1)
    exact hω1 h2
  · rintro ⟨j, hj⟩
    simp only at hj
    rw [← map_zpow, ← map_zpow] at hj
    have h2 := congrArg Prod.snd (eq_of_mk_diagHom_eq hj)
    change (1 : Kˣ) ^ j = ω at h2
    rw [_root_.one_zpow] at h2
    exact hω1 h2.symm
  · rintro ⟨_, t, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    change (ProjGenLinGroup.mk.comp transvHom t) ^ 2 ^ 1 = 1
    have ht : t ^ 2 = 1 := by
      rw [pow_two, ← ofAdd_toAdd (t * t), toAdd_mul, CharTwo.add_self_eq_zero, ofAdd_zero]
    rw [pow_one, MonoidHom.comp_apply, ← map_pow, ← map_pow, ht, map_one, map_one]
  · intro h
    apply mk_transvHom_one_ne_one (K := K)
    have hmem : ProjGenLinGroup.mk (transvHom (Multiplicative.ofAdd (1 : K))) ∈ U :=
      ⟨Multiplicative.ofAdd 1, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact hmem
  · rintro _ ⟨t, rfl⟩
    exact ⟨_, (hconj a t).symm⟩
  · rintro _ ⟨t, rfl⟩
    exact ⟨_, (hconj b t).symm⟩

end WitnessPGL

namespace WitnessD4


variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K}

theorem hasLocalWitness_of_fix_g2 {k : ℕ} (hk : 1 ≤ k) (hK : Nat.card K = (2 ^ (2 * k)) ^ 3)
    (hσ : ∀ c, σ c = c ^ 2 ^ (2 * k)) (α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hα : ∀ g, fieldActor σ σ g = g → α g = g) : HasLocalWitness α := by
  have hK2 : ringChar K = 2 := Sec8.Item8KFactsProof.ringChar_eq_two_of_card hK
  have hkc : Nat.card (fixSubfield σ) = 2 ^ (2 * k) :=
    KFacts.card_fixSubfield_of_cube (by omega) hK hσ
  have : CharP (fixSubfield σ) 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hkc
  obtain ⟨ω, hω⟩ := WitnessG2.exists_orderOf_eq_three hkc
  have hw := WitnessG2.hasLocalWitness_g2FieldHom (K := fixSubfield σ)
    (σ := (1 : fixSubfield σ ≃+* fixSubfield σ)) (one_pow 3) hω
  refine hw.of_injective_of_fix (trialityG2Incl σ hK2) (trialityG2Incl_injective σ hK2)
    fun x => hα _ ?_
  exact (mem_range_trialityG2Incl_iff σ hK2 _).1 ⟨x, rfl⟩

theorem hasLocalWitness_fieldActor {k : ℕ} (hk : 1 ≤ k) (hK : Nat.card K = (2 ^ (2 * k)) ^ 3)
    (hσ : ∀ c, σ c = c ^ 2 ^ (2 * k)) : HasLocalWitness (fieldActor (t := TwistTag.D4) σ σ) :=
  hasLocalWitness_of_fix_g2 hk hK hσ _ fun _ h => h

theorem hasLocalWitness_fieldActor_inv {k : ℕ} (hk : 1 ≤ k)
    (hK : Nat.card K = (2 ^ (2 * k)) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ (2 * k)) :
    HasLocalWitness (fieldActor (t := TwistTag.D4) σ σ)⁻¹ :=
  hasLocalWitness_of_fix_g2 hk hK hσ _ fun g h => by
    rw [MulAut.inv_apply, MulEquiv.symm_apply_eq]
    exact h.symm

end WitnessD4

open WitnessD4 in
theorem inputs47WitnessD4_holds :
    Inputs47WitnessD4 := by
  intro X _ k hX α hα hout
  have hk1 : 1 ≤ 2 * k := hX.1.2.1
  have hk : 1 ≤ k := by omega
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_D4 hX
  rw [← hasLocalWitness_congr_iff e]
  set β := MulAut.congr e α with hβ
  have hβ3 : β ^ 3 = 1 := by rw [hβ, ← map_pow, hα, map_one]
  have hβout : ¬ IsInnerAut β := fun h => hout ((isInnerAut_congr e α).mp h)
  by_cases hstd : IsStdGraphFieldConj σ β
  · obtain ⟨γ, hγ | hγ⟩ := hstd
    · rw [hγ]
      exact (hasLocalWitness_fieldActor hk hK hσ).conj γ
    · rw [hγ]
      exact (hasLocalWitness_fieldActor_inv hk hK hσ).conj γ
  · obtain ⟨K', _, _, hK', ⟨f⟩⟩ :=
      Sec8.kF89D4SecondCentEven_holds (2 * k) (even_two_mul k) hk1 K σ hK hσ β hβ3 hβout hstd
    have : CharP K' 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
        hk1 hK'
    obtain ⟨ω, hω⟩ := WitnessG2.exists_orderOf_eq_three hK'
    set g := f.trans (Sec8.LangTwisted3Proof.projImageGlPiTrueEquiv (2 ^ (2 * k)) K') with hg
    refine (WitnessPGL.hasLocalWitness_pgl hω).of_injective_of_fix
      ((autFix β).subtype.comp g.symm.toMonoidHom)
      ((autFix β).subtype_injective.comp g.symm.injective) fun x => ?_
    exact (g.symm x).2

end CFSG.RankThree.PartTwo.Sec4

module

public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofL364Labels
public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofL364Lift

public section

namespace CFSG.RankThree.PartTwo.Sec4.Res6L364

open CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix

@[expose] noncomputable def glι : GL (Fin 3) F4 →* GL (Fin 3) K64 := Matrix.GeneralLinearGroup.map ι

theorem coe_glι (A : GL (Fin 3) F4) :
    ((glι A : GL (Fin 3) K64) : Matrix (Fin 3) (Fin 3) K64) =
      (A : Matrix (Fin 3) (Fin 3) F4).map ι :=
  rfl

theorem glι_injective : Function.Injective glι := by
  intro A B h
  apply Units.ext
  have h' := congrArg (fun X : GL (Fin 3) K64 => (X : Matrix (Fin 3) (Fin 3) K64)) h
  simp only [coe_glι] at h'
  exact Matrix.map_injective ι_injective h'

@[expose] noncomputable def LGL (y : Lab) : GL (Fin 3) F4 :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (L y) (det_L y)

theorem coe_LGL (y : Lab) : ((LGL y : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) = L y := rfl

@[expose] noncomputable def ρ (y : Lab) : MulAut Y64 := conjAut 3 K64 (glι (LGL y))

@[expose] def ω4u : F4ˣ := Units.mk0 ω4 (by decide)

theorem LGL_mul (y y' : Lab) : LGL y * LGL y' =
    Matrix.GeneralLinearGroup.scalar (Fin 3) (ω4u ^ ((mulLab y y').2 : ℕ)) *
      LGL (mulLab y y').1 := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_LGL, coe_LGL, L_mul, Matrix.GeneralLinearGroup.coe_scalar,
    coe_LGL, Matrix.scalar_apply, smul_eq_diagonal_mul]
  simp [ω4u]

theorem conjAut_glι_scalar (u : F4ˣ) :
    conjAut 3 K64 (glι (Matrix.GeneralLinearGroup.scalar (Fin 3) u)) = 1 := by
  rw [glι, Matrix.GeneralLinearGroup.map_scalar, conjAut_scalar]

theorem ρ_mul (y y' : Lab) : ρ y * ρ y' = ρ (mulLab y y').1 := by
  rw [ρ, ρ, ρ, ← map_mul, ← map_mul, LGL_mul, map_mul, map_mul, conjAut_glι_scalar, one_mul]

theorem ρ_zero : ρ (0, 0, 0) = 1 := by
  have : LGL (0, 0, 0) = 1 := Units.ext (by rw [coe_LGL, L_zero]; rfl)
  rw [ρ, this, map_one, map_one]

theorem ρ_injective : Function.Injective ρ := by
  intro y y' h
  obtain ⟨u, hu⟩ := exists_scalar_of_conjAut_eq h
  have hmat := congrArg (fun X : GL (Fin 3) K64 => (X : Matrix (Fin 3) (Fin 3) K64)) hu
  simp only [Units.val_mul, coe_glι, coe_LGL, Matrix.GeneralLinearGroup.coe_scalar] at hmat
  have hent : ∀ a c : Fin 3, ι (L y a c) = (u : K64) * ι (L y' a c) := by
    intro a c
    have := congrFun (congrFun hmat a) c
    simpa [Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_mul] using this
  obtain ⟨b, hb⟩ := exists_L_ne_zero y'
  set l : F4 := L y 0 b / L y' 0 b with hl
  have hu' : (u : K64) = ι l := by
    rw [hl, map_div₀, hent 0 b, mul_div_assoc, div_self ((map_ne_zero ι).mpr hb), mul_one]
  apply L_inj y y' l
  refine Matrix.ext fun a c => ?_
  rw [Matrix.smul_apply, smul_eq_mul]
  apply ι_injective
  rw [hent, hu', map_mul]

theorem ρ_mul_comm_iff (y y' : Lab) : ρ y * ρ y' = ρ y' * ρ y ↔ comm y y' := by
  rw [ρ_mul, ρ_mul, comm]
  exact ρ_injective.eq_iff

@[expose] noncomputable def GLσ : Subgroup (GL (Fin 3) K64) :=
  MonoidHom.eqLocus mapσ (MonoidHom.id _)

theorem mem_GLσ {A : GL (Fin 3) K64} : A ∈ GLσ ↔ mapσ A = A := Iff.rfl

theorem glι_mem_GLσ (A : GL (Fin 3) F4) : glι A ∈ GLσ := by
  rw [mem_GLσ]
  apply Units.ext
  ext i j
  change σ4 (ι ((A : Matrix (Fin 3) (Fin 3) F4) i j)) = ι ((A : Matrix (Fin 3) (Fin 3) F4) i j)
  exact σ4_ι _

theorem range_glι : glι.range = GLσ := by
  apply le_antisymm
  · rintro _ ⟨A, rfl⟩
    exact glι_mem_GLσ A
  · intro A hA
    rw [mem_GLσ] at hA
    have hfix : ∀ i j, σ4 ((A : Matrix (Fin 3) (Fin 3) K64) i j) =
        (A : Matrix (Fin 3) (Fin 3) K64) i j := by
      intro i j
      have := congrArg (fun X : GL (Fin 3) K64 => (X : Matrix (Fin 3) (Fin 3) K64) i j) hA
      simpa [mapσ, Matrix.GeneralLinearGroup.map] using this
    choose b hb using fun i j => exists_ι_of_σ4_fixed (hfix i j)
    set B : Matrix (Fin 3) (Fin 3) F4 := Matrix.of b with hB
    have hBA : B.map ι = (A : Matrix (Fin 3) (Fin 3) K64) := by
      ext i j; simp [hB, hb]
    have hdet : B.det ≠ 0 := by
      intro h0
      have h1 : (B.map ι).det = 0 := by
        rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
      rw [hBA] at h1
      exact (Matrix.isUnits_det_units A).ne_zero h1
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero B hdet, ?_⟩
    apply Units.ext
    rw [coe_glι]
    exact hBA

theorem card_units_F4 : Nat.card F4ˣ = 3 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_units, card_F4]

theorem card_GLσ : Nat.card GLσ = 181440 := by
  rw [← range_glι, Nat.card_congr (MonoidHom.ofInjective glι_injective).toEquiv.symm,
    Matrix.card_GL_field, card_F4]
  simp [Fin.prod_univ_three]

@[expose] noncomputable def Φ (l : F4ˣ) (y : Lab) : GL (Fin 3) K64 :=
  glι (Matrix.GeneralLinearGroup.scalar (Fin 3) l * LGL y)

theorem inv_mem_of_closed {G : Type*} [Group G] [Finite G] {S : Set G} (h1 : (1 : G) ∈ S)
    (hmul : ∀ a b, a ∈ S → b ∈ S → a * b ∈ S) {x : G} (hx : x ∈ S) : x⁻¹ ∈ S := by
  have hpow : ∀ n : ℕ, x ^ n ∈ S := by
    intro n
    induction n with
    | zero => rw [pow_zero]; exact h1
    | succ n ih => rw [pow_succ]; exact hmul _ _ ih hx
  have hpos := orderOf_pos x
  have : x⁻¹ = x ^ (orderOf x - 1) := by
    rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
  rw [this]; exact hpow _

theorem Φ_mul (l l' : F4ˣ) (y y' : Lab) :
    Φ l y * Φ l' y' = Φ (l * l' * ω4u ^ ((mulLab y y').2 : ℕ)) (mulLab y y').1 := by
  have key : Matrix.GeneralLinearGroup.scalar (Fin 3) l * LGL y *
      (Matrix.GeneralLinearGroup.scalar (Fin 3) l' * LGL y') =
      Matrix.GeneralLinearGroup.scalar (Fin 3) (l * l' * ω4u ^ ((mulLab y y').2 : ℕ)) *
        LGL (mulLab y y').1 := by
    have hc := Matrix.GeneralLinearGroup.scalar_commute (n := Fin 3) l' (LGL y)
    calc Matrix.GeneralLinearGroup.scalar (Fin 3) l * LGL y *
          (Matrix.GeneralLinearGroup.scalar (Fin 3) l' * LGL y')
        = Matrix.GeneralLinearGroup.scalar (Fin 3) l *
            (LGL y * Matrix.GeneralLinearGroup.scalar (Fin 3) l') * LGL y' := by
          simp only [mul_assoc]
      _ = Matrix.GeneralLinearGroup.scalar (Fin 3) l *
            (Matrix.GeneralLinearGroup.scalar (Fin 3) l' * LGL y) * LGL y' := by rw [hc]
      _ = Matrix.GeneralLinearGroup.scalar (Fin 3) l *
            Matrix.GeneralLinearGroup.scalar (Fin 3) l' * (LGL y * LGL y') := by
          simp only [mul_assoc]
      _ = _ := by rw [LGL_mul, ← mul_assoc, ← map_mul, ← map_mul]
  rw [Φ, Φ, Φ, ← map_mul, key]

@[expose] noncomputable def PP : Subgroup (GL (Fin 3) K64) where
  carrier := Set.range (Function.uncurry Φ)
  mul_mem' := by
    rintro _ _ ⟨⟨l, y⟩, rfl⟩ ⟨⟨l', y'⟩, rfl⟩
    exact ⟨⟨_, _⟩, (Φ_mul l l' y y').symm⟩
  one_mem' := ⟨⟨1, (0, 0, 0)⟩, by
    simp only [Function.uncurry_apply_pair, Φ, map_one, one_mul]
    have : LGL (0, 0, 0) = 1 := Units.ext (by rw [coe_LGL, L_zero]; rfl)
    rw [this, map_one]⟩
  inv_mem' := by
    intro x hx
    refine inv_mem_of_closed (S := Set.range (Function.uncurry Φ)) ?_ ?_ hx
    · refine ⟨⟨1, (0, 0, 0)⟩, ?_⟩
      simp only [Function.uncurry_apply_pair, Φ, map_one, one_mul]
      have : LGL (0, 0, 0) = 1 := Units.ext (by rw [coe_LGL, L_zero]; rfl)
      rw [this, map_one]
    · rintro _ _ ⟨⟨l, y⟩, rfl⟩ ⟨⟨l', y'⟩, rfl⟩
      exact ⟨⟨_, _⟩, (Φ_mul l l' y y').symm⟩

theorem Φ_injective : Function.Injective (Function.uncurry Φ) := by
  rintro ⟨l, y⟩ ⟨l', y'⟩ h
  simp only [Function.uncurry_apply_pair, Φ] at h
  have h1 := glι_injective h
  have hmat := congrArg (fun X : GL (Fin 3) F4 => (X : Matrix (Fin 3) (Fin 3) F4)) h1
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, coe_LGL, Matrix.scalar_apply,
    ← smul_eq_diagonal_mul] at hmat
  have hl0 : (l : F4) ≠ 0 := l.ne_zero
  have hyy : y = y' := by
    apply L_inj y y' ((l : F4)⁻¹ * l')
    rw [mul_smul, ← hmat, smul_smul, inv_mul_cancel₀ hl0, one_smul]
  subst hyy
  obtain ⟨b, hb⟩ := exists_L_ne_zero y
  have := congrFun (congrFun hmat 0) b
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  have hll : (l : F4) = l' := mul_right_cancel₀ hb this
  rw [Units.ext hll]

theorem card_PP : Nat.card PP = 81 := by
  have : Nat.card PP = Nat.card (F4ˣ × Lab) := by
    rw [← Nat.card_range_of_injective Φ_injective]
    rfl
  rw [this, Nat.card_prod, card_units_F4]
  simp

theorem PP_le_GLσ : PP ≤ GLσ := by
  rintro _ ⟨⟨l, y⟩, rfl⟩
  exact glι_mem_GLσ _

theorem factorization_181440 : (181440 : ℕ).factorization 3 = 4 := by
  have h : (181440 : ℕ) = 3 ^ 4 * 2240 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem exists_conj_le_PP {E : Subgroup (GL (Fin 3) K64)} (hE : E ≤ GLσ) (hp : IsPGroup 3 E) :
    ∃ g ∈ GLσ, ∀ A ∈ E, g⁻¹ * A * g ∈ PP := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set E' : Subgroup GLσ := E.subgroupOf GLσ with hE'
  have hp' : IsPGroup 3 E' := hp.of_equiv (Subgroup.subgroupOfEquivOfLe hE).symm
  have hcardP : Nat.card (PP.subgroupOf GLσ) = 3 ^ (Nat.card GLσ).factorization 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe PP_le_GLσ).toEquiv, card_PP, card_GLσ,
      factorization_181440]
    norm_num
  set S₀ : Sylow 3 GLσ := Sylow.ofCard (PP.subgroupOf GLσ) hcardP with hS₀
  obtain ⟨S, hS⟩ := hp'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq GLσ S₀ S
  refine ⟨g, g.2, fun A hA => ?_⟩
  have hA' : (⟨A, hE hA⟩ : GLσ) ∈ (S : Subgroup GLσ) := hS hA
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hA'
  have h2 : (g⁻¹ : GLσ) * ⟨A, hE hA⟩ * g ∈ PP.subgroupOf GLσ := by
    simpa [hS₀, MulAut.smul_def, MulAut.conj_apply] using hA'
  rw [Subgroup.mem_subgroupOf] at h2
  simpa using h2

theorem pow_three_of_σ4_fixed {u : K64} (hu : σ4 u = u) (hu0 : u ≠ 0) : u ^ 3 = 1 := by
  rcases eq_of_σ4_fixed hu with rfl | rfl | rfl | rfl
  · exact absurd rfl hu0
  · simp
  · exact omega_cube
  · linear_combination (ω + 2) * omega_sq_add - two_eq_zero

theorem σ4_fixed_of_scalar_mem {u : K64ˣ} (h : Matrix.GeneralLinearGroup.scalar (Fin 3) u ∈ GLσ) :
    σ4 (u : K64) = u := by
  rw [mem_GLσ, mapσ_scalar] at h
  have := congrArg (fun X : GL (Fin 3) K64 => (X : Matrix (Fin 3) (Fin 3) K64) 0 0) h
  simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using this

theorem isPGroup_lifts {E : Subgroup (MulAut Y64)} (hE : CFSG.Assembly.IsElemAbelian 3 E) :
    IsPGroup 3 (((E ⊓ linearAutGroup 3 K64).comap (conjAut 3 K64)) ⊓ GLσ : Subgroup _) := by
  intro A
  refine ⟨2, ?_⟩
  have hA := A.2
  have h1 : conjAut 3 K64 ((A : GL (Fin 3) K64) ^ 3) = 1 := by
    rw [map_pow]; exact hE.2 _ hA.1.1
  obtain ⟨u, hu⟩ := exists_scalar_of_conjAut_eq (h1.trans (map_one _).symm)
  rw [mul_one] at hu
  have hmem : (A : GL (Fin 3) K64) ^ 3 ∈ GLσ := pow_mem hA.2 3
  rw [hu] at hmem
  have hσu := σ4_fixed_of_scalar_mem hmem
  have hu3 : (u : K64) ^ 3 = 1 := pow_three_of_σ4_fixed hσu u.ne_zero
  apply Subtype.ext
  simp only [Subgroup.coe_pow, OneMemClass.coe_one]
  rw [show 3 ^ 2 = 3 * 3 by norm_num, pow_mul, hu, ← map_pow]
  have : u ^ 3 = 1 := Units.ext (by simpa using hu3)
  rw [this, map_one]

theorem exists_conj_labels {E : Subgroup (MulAut Y64)} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hf : fieldAut 3 K64 σ4 ∈ E) :
    ∃ g ∈ GLσ, ∀ a ∈ E ⊓ linearAutGroup 3 K64, ∃ y : Lab,
      (conjAut 3 K64 g)⁻¹ * a * conjAut 3 K64 g = ρ y := by
  obtain ⟨g, hg, hgP⟩ := exists_conj_le_PP (E := ((E ⊓ linearAutGroup 3 K64).comap
    (conjAut 3 K64)) ⊓ GLσ) inf_le_right (isPGroup_lifts hE)
  refine ⟨g, hg, fun a ha => ?_⟩
  obtain ⟨A, hAσ, rfl⟩ := exists_σ_fixed_lift hE.1 hf ha
  obtain ⟨⟨l, y⟩, hly⟩ := hgP A ⟨ha, hAσ⟩
  refine ⟨y, ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul]
  simp only [Function.uncurry_apply_pair] at hly
  rw [← hly, Φ, map_mul, map_mul, conjAut_glι_scalar, one_mul]
  rfl

theorem labels_cases {Q : Subgroup (MulAut Y64)} (hQc : IsMulCommutative Q)
    (h9 : Nat.card Q = 9) (hQρ : ∀ a ∈ Q, ∃ y : Lab, a = ρ y) :
    (ρ t1Lab ∈ Q ∧ ρ t2Lab ∈ Q) ∨ (ρ zLab ∈ Q ∧ ∃ a : Fin 3, ρ (wLab a) ∈ Q) := by
  classical
  set S : Finset Lab := Finset.univ.filter (fun y => ρ y ∈ Q) with hS
  have hcard : S.card = 9 := by
    rw [← h9]
    have e : S ≃ Q :=
      { toFun := fun y => ⟨ρ y, (Finset.mem_filter.mp y.2).2⟩
        invFun := fun a => ⟨Classical.choose (hQρ a a.2), Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, by rw [← Classical.choose_spec (hQρ a a.2)]; exact a.2⟩⟩
        left_inv := fun y => by
          apply Subtype.ext
          exact ρ_injective (Classical.choose_spec (hQρ _ (Finset.mem_filter.mp y.2).2)).symm
        right_inv := fun a => by
          apply Subtype.ext
          exact (Classical.choose_spec (hQρ a a.2)).symm }
    rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  obtain ⟨y₀, hy₀S, hy₀⟩ : ∃ y₀ ∈ S, y₀ ≠ (0, 0, 0) ∧ y₀ ≠ zLab ∧ y₀ ≠ (2, 1, 0) := by
    by_contra hcon
    push Not at hcon
    have hsub : S ⊆ {(0, 0, 0), zLab, (2, 1, 0)} := by
      intro y hy
      by_cases h1 : y = (0, 0, 0)
      · simp [h1]
      by_cases h2 : y = zLab
      · simp [h2]
      have := hcon y hy h1 h2
      simp [this]
    have := Finset.card_le_card hsub
    rw [hcard] at this
    have h3 : ({(0, 0, 0), zLab, (2, 1, 0)} : Finset Lab).card ≤ 3 := Finset.card_le_three
    omega
  obtain ⟨hne0, hnez, hnez2⟩ := hy₀
  have hsub : S ⊆ Finset.univ.filter (comm y₀) := by
    intro y hy
    have hyQ := (Finset.mem_filter.mp hy).2
    have hy₀Q := (Finset.mem_filter.mp hy₀S).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [← ρ_mul_comm_iff]
    exact congrArg Subtype.val (hQc.is_comm.comm ⟨_, hy₀Q⟩ ⟨_, hyQ⟩)
  have hSeq : S = Finset.univ.filter (comm y₀) :=
    Finset.eq_of_subset_of_card_le hsub (by rw [card_comm y₀ hne0 hnez hnez2, hcard])
  have hmem : ∀ y, comm y₀ y → ρ y ∈ Q := by
    intro y hy
    have : y ∈ S := by rw [hSeq]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩
    exact (Finset.mem_filter.mp this).2
  obtain ⟨hz, h⟩ := comm_cases y₀ hne0 hnez hnez2
  rcases h with ⟨h1, h2⟩ | ⟨a, ha⟩
  · exact Or.inl ⟨hmem _ h1, hmem _ h2⟩
  · exact Or.inr ⟨hmem _ hz, a, hmem _ ha⟩

end CFSG.RankThree.PartTwo.Sec4.Res6L364

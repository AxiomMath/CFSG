module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSylow
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial Matrix

theorem exists_odd_regular_of_homs {B R : Type*} [Group B] [Finite B] [Group R] [Finite R]
    {ι : Type*} [Fintype ι] (θ : ι → B →* R) (hsurj : ∀ i, Function.Surjective (θ i))
    (hodd : Odd (Nat.card R)) (hlt : Fintype.card ι < Nat.card R) :
    ∃ b : B, ∃ m : ℕ, Odd m ∧ b ^ m = 1 ∧ ∀ i, θ i b ≠ 1 := by
  classical
  have := Fintype.ofFinite B
  have := Fintype.ofFinite R
  have hker : ∀ i, Nat.card (θ i).ker * Nat.card R = Nat.card B := by
    intro i
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (θ i).ker
    have h2 : Nat.card (B ⧸ (θ i).ker) = Nat.card R :=
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective (θ i) (hsurj i)).toEquiv
    rw [h2] at h1
    rw [h1, mul_comm]
  have hBpos : 0 < Nat.card B := Nat.card_pos
  have hRpos : 0 < Nat.card R := Nat.card_pos
  set bad : Finset B := Finset.univ.biUnion fun i => Finset.univ.filter fun b => θ i b = 1 with hbad
  have hcard_filter : ∀ i, (Finset.univ.filter fun b : B => θ i b = 1).card = Nat.card (θ i).ker := by
    intro i
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun b => by simp [MonoidHom.mem_ker])
  have hbad_le : bad.card * Nat.card R ≤ Fintype.card ι * Nat.card B := by
    calc bad.card * Nat.card R
        ≤ (∑ i, (Finset.univ.filter fun b : B => θ i b = 1).card) * Nat.card R := by
          apply Nat.mul_le_mul_right
          exact Finset.card_biUnion_le
      _ = ∑ i, Nat.card (θ i).ker * Nat.card R := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by rw [hcard_filter i]
      _ = ∑ _i : ι, Nat.card B := Finset.sum_congr rfl fun i _ => hker i
      _ = Fintype.card ι * Nat.card B := by simp
  have hbad_lt : bad.card < Nat.card B := by
    by_contra hge
    push Not at hge
    have h1 : Nat.card B * Nat.card R ≤ bad.card * Nat.card R := Nat.mul_le_mul_right _ hge
    have h2 : Fintype.card ι * Nat.card B < Nat.card R * Nat.card B :=
      Nat.mul_lt_mul_of_pos_right hlt hBpos
    rw [mul_comm (Nat.card R)] at h2
    omega
  have hex : ∃ b : B, b ∉ bad := by
    by_contra hall
    push Not at hall
    have : bad = Finset.univ := Finset.eq_univ_of_forall hall
    rw [this, Finset.card_univ, Nat.card_eq_fintype_card] at hbad_lt
    exact lt_irrefl _ hbad_lt
  obtain ⟨b, hb⟩ := hex
  have hbi : ∀ i, θ i b ≠ 1 := by
    intro i h
    apply hb
    rw [hbad, Finset.mem_biUnion]
    exact ⟨i, Finset.mem_univ _, by simpa using h⟩
  obtain ⟨a, o, ho, hao⟩ := Nat.exists_eq_two_pow_mul_odd hBpos.ne'
  refine ⟨b ^ 2 ^ a, o, ho, ?_, fun i h => ?_⟩
  · rw [← pow_mul, ← hao]
    exact pow_card_eq_one'
  · have h1 : (θ i b) ^ 2 ^ a = 1 := by rw [← map_pow]; exact h
    have h2 : (θ i b) ^ Nat.card R = 1 := pow_card_eq_one'
    have hcop : Nat.Coprime (2 ^ a) (Nat.card R) :=
      Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hodd)
    have h3 : (θ i b) ^ (2 ^ a).gcd (Nat.card R) = 1 := pow_gcd_eq_one.mpr ⟨h1, h2⟩
    rw [hcop, pow_one] at h3
    exact hbi i h3

theorem eq_zero_of_mulVec_eq_of_upper {K : Type*} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (hM : M.IsUpperTriangular) (hd : ∀ i, M i i ≠ 1) (x : Fin n → K) (hx : M.mulVec x = x) :
    x = 0 := by
  classical
  by_contra hne
  have hS : (Finset.univ.filter fun i => x i ≠ 0).Nonempty := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    exact ⟨i, by simpa using hi⟩
  obtain ⟨i, hxi, hmax⟩ : ∃ i, x i ≠ 0 ∧ ∀ j, i < j → x j = 0 := by
    refine ⟨(Finset.univ.filter fun i => x i ≠ 0).max' hS, ?_, ?_⟩
    · have := Finset.max'_mem _ hS
      simpa using this
    · intro j hj
      by_contra hxj
      have : j ∈ Finset.univ.filter fun i => x i ≠ 0 := by simpa using hxj
      exact absurd (Finset.le_max' _ j this) (not_le.mpr hj)
  have h1 : (M.mulVec x) i = M i i * x i := by
    rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single i]
    · intro j _ hji
      rcases lt_or_gt_of_ne hji with h | h
      · rw [hM h, zero_mul]
      · rw [hmax j h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have h2 : M i i * x i = x i := by rw [← h1, hx]
  have h3 : (M i i - 1) * x i = 0 := by rw [sub_mul, h2, one_mul, sub_self]
  rcases mul_eq_zero.mp h3 with h | h
  · exact hd i (sub_eq_zero.mp h)
  · exact hxi h

section Transport

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem exists_regular_twist_of_std (Reg : Γ → Prop) (hReg : ∀ g c, Reg c → Reg (g * c * g⁻¹))
    (Q0 : Sylow 2 Γ)
    (std : ∀ α : Γ ≃* Γ, (∀ x, x ∈ (Q0 : Subgroup Γ) ↔ α x ∈ (Q0 : Subgroup Γ)) →
      ∃ c ∈ Subgroup.normalizer ((Q0 : Subgroup Γ) : Set Γ), ∃ m : ℕ, Odd m ∧ c ^ m = 1 ∧
        Reg c ∧ Reg (α c))
    (Q : Sylow 2 Γ) (α : Γ ≃* Γ) (hα : ∀ x, x ∈ (Q : Subgroup Γ) ↔ α x ∈ (Q : Subgroup Γ)) :
    ∃ c ∈ Subgroup.normalizer ((Q : Subgroup Γ) : Set Γ), ∃ m : ℕ, Odd m ∧ c ^ m = 1 ∧
      Reg c ∧ Reg (α c) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ Q0 Q
  have hmem : ∀ y : Γ, y ∈ (Q : Subgroup Γ) ↔ g⁻¹ * y * g ∈ (Q0 : Subgroup Γ) := by
    intro y
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.smul_def, mul_assoc]
  let α'' : Γ ≃* Γ := (MulAut.conj g).trans (α.trans (MulAut.conj g⁻¹))
  have hα'' : ∀ x, α'' x = g⁻¹ * α (g * x * g⁻¹) * g := by
    intro x
    simp [α'', MulAut.conj_apply]
  have hstd : ∀ x, x ∈ (Q0 : Subgroup Γ) ↔ α'' x ∈ (Q0 : Subgroup Γ) := by
    intro x
    rw [hα'', ← hmem, ← hα, hmem, show g⁻¹ * (g * x * g⁻¹) * g = x by group]
  obtain ⟨c₀, hc₀, m, hm, hcm, hr0, hr1⟩ := std α'' hstd
  have hcN : g * c₀ * g⁻¹ ∈ Subgroup.normalizer ((Q : Subgroup Γ) : Set Γ) := by
    have h : (g * c₀ * g⁻¹) • Q = Q := by
      rw [← hg, ← mul_smul, show g * c₀ * g⁻¹ * g = g * c₀ by group, mul_smul,
        Sylow.smul_eq_iff_mem_normalizer.mpr hc₀]
    exact Sylow.smul_eq_iff_mem_normalizer.mp h
  refine ⟨g * c₀ * g⁻¹, hcN, m, hm, ?_, hReg g c₀ hr0, ?_⟩
  · rw [conj_pow, hcm, mul_one, mul_inv_cancel]
  · have : α (g * c₀ * g⁻¹) = g * α'' c₀ * g⁻¹ := by
      rw [hα'']
      group
    rw [this]
    exact hReg g _ hr1

end Transport

private theorem mem_normalizer_of_preserves {Γ : Type*} [Group Γ] {Q : Subgroup Γ} (α : Γ ≃* Γ)
    (hα : ∀ x, x ∈ Q ↔ α x ∈ Q) {x : Γ} (hx : x ∈ Subgroup.normalizer (Q : Set Γ)) :
    α x ∈ Subgroup.normalizer (Q : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  obtain ⟨z, rfl⟩ := α.surjective h
  rw [← hα, ← map_inv, ← map_mul, ← map_mul, ← hα]
  exact Subgroup.mem_normalizer_iff.mp hx z

theorem exists_restrict_aut {Γ : Type*} [Group Γ] {Q B : Subgroup Γ}
    (hN : Subgroup.normalizer (Q : Set Γ) = B) (α : Γ ≃* Γ) (hα : ∀ x, x ∈ Q ↔ α x ∈ Q) :
    ∃ αB : ↥B →* ↥B, Function.Surjective αB ∧ ∀ b : ↥B, ((αB b : ↥B) : Γ) = α (b : Γ) := by
  have hαB : ∀ x ∈ B, α x ∈ B := by
    intro x hx
    rw [← hN] at hx ⊢
    exact mem_normalizer_of_preserves α hα hx
  have hα' : ∀ x, x ∈ Q ↔ α.symm x ∈ Q := by
    intro y
    rw [hα (α.symm y), α.apply_symm_apply]
  have hαB' : ∀ x ∈ B, α.symm x ∈ B := by
    intro x hx
    rw [← hN] at hx ⊢
    exact mem_normalizer_of_preserves α.symm hα' hx
  refine ⟨(α.toMonoidHom.comp B.subtype).codRestrict _ fun x => hαB x.1 x.2, ?_, fun b => rfl⟩
  intro y
  refine ⟨⟨α.symm y.1, hαB' y.1 y.2⟩, ?_⟩
  apply Subtype.ext
  exact α.apply_symm_apply y.1

section SL3

variable {F : Type} [Field F]

private noncomputable def diagEntrySL3 (i : Fin 3) :
    ↥(LinearFlag.upperTriangular 3 F) →* F where
  toFun A := (A.1 : Matrix (Fin 3) (Fin 3) F) i i
  map_one' := by simp
  map_mul' A B := by
    have hA : (A.1 : Matrix (Fin 3) (Fin 3) F).IsUpperTriangular :=
      LinearFlag.mem_upperTriangular_iff_isUpperTriangular.mp A.2
    have hB : (B.1 : Matrix (Fin 3) (Fin 3) F).IsUpperTriangular :=
      LinearFlag.mem_upperTriangular_iff_isUpperTriangular.mp B.2
    simp only [Subgroup.coe_mul]
    exact LinearFlag.mul_apply_self_of_isUpperTriangular hA hB i

private noncomputable def diagSL3' (d : Fin 3 → Fˣ) (hd : d 0 * d 1 * d 2 = 1) :
    SpecialLinearGroup (Fin 3) F :=
  ⟨Matrix.diagonal fun i => (d i : F), by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    have := congrArg Units.val hd
    simpa using this⟩

private theorem diagSL3'_mem (d : Fin 3 → Fˣ) (hd : d 0 * d 1 * d 2 = 1) :
    diagSL3' d hd ∈ LinearFlag.upperTriangular 3 F := by
  rw [LinearFlag.mem_upperTriangular]
  intro i j hji
  show (Matrix.diagonal fun i => (d i : F)) i j = 0
  rw [Matrix.diagonal_apply_ne _ (ne_of_gt hji)]

private theorem diagEntrySL3_surjective (i : Fin 3) :
    Function.Surjective (diagEntrySL3 (F := F) i).toHomUnits := by
  intro a
  have key : ∀ (d : Fin 3 → Fˣ) (hd : d 0 * d 1 * d 2 = 1), d i = a →
      ∃ A, (diagEntrySL3 (F := F) i).toHomUnits A = a := by
    intro d hd hda
    refine ⟨⟨diagSL3' d hd, diagSL3'_mem d hd⟩, Units.ext ?_⟩
    rw [MonoidHom.coe_toHomUnits]
    show (Matrix.diagonal fun i => (d i : F)) i i = (a : F)
    rw [Matrix.diagonal_apply_eq, hda]
  fin_cases i
  · exact key ![a, a⁻¹, 1] (by simp) rfl
  · exact key ![1, a, a⁻¹] (by simp) rfl
  · exact key ![a⁻¹, 1, a] (by simp) rfl

theorem sl3_std_twist [Finite F] {n' : ℕ} (hn' : 3 ≤ n') (hK : Nat.card F = 2 ^ n')
    (Q0 : Sylow 2 (SpecialLinearGroup (Fin 3) F))
    (hQ0 : (Q0 : Subgroup (SpecialLinearGroup (Fin 3) F)) = LinearFlag.unitriangular 3 F)
    (α : SpecialLinearGroup (Fin 3) F ≃* SpecialLinearGroup (Fin 3) F)
    (hα : ∀ x, x ∈ (Q0 : Subgroup (SpecialLinearGroup (Fin 3) F)) ↔
      α x ∈ (Q0 : Subgroup (SpecialLinearGroup (Fin 3) F))) :
    ∃ c : SpecialLinearGroup (Fin 3) F,
      c ∈ Subgroup.normalizer ((Q0 : Subgroup (SpecialLinearGroup (Fin 3) F)) : Set _) ∧
      ∃ m : ℕ, Odd m ∧ c ^ m = 1 ∧
        (∀ x : Fin 3 → F, (c : Matrix (Fin 3) (Fin 3) F).mulVec x = x → x = 0) ∧
        (∀ x : Fin 3 → F, ((α c : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec x = x →
          x = 0) := by
  have hN : Subgroup.normalizer ((Q0 : Subgroup (SpecialLinearGroup (Fin 3) F)) : Set _) =
      LinearFlag.upperTriangular 3 F := by
    rw [hQ0, LinearFlag.normalizer_unitriangular]
  obtain ⟨αB, hαBs, hαBc⟩ := exists_restrict_aut hN α hα
  let θ : Fin 3 ⊕ Fin 3 → ↥(LinearFlag.upperTriangular 3 F) →* Fˣ :=
    Sum.elim (fun j => (diagEntrySL3 (F := F) j).toHomUnits)
      (fun j => (diagEntrySL3 (F := F) j).toHomUnits.comp αB)
  have hθs : ∀ i, Function.Surjective (θ i) := by
    rintro (j | j)
    · exact diagEntrySL3_surjective j
    · exact (diagEntrySL3_surjective j).comp hαBs
  have hq : 8 ≤ Nat.card F := by
    rw [hK]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n' := Nat.pow_le_pow_right (by norm_num) hn'
  have hcu : Nat.card Fˣ = Nat.card F - 1 := Nat.card_units _
  have hodd : Odd (Nat.card Fˣ) := by
    rw [hcu, hK]
    have h1 : 1 ≤ 2 ^ (n' - 1) := Nat.one_le_two_pow
    have h2 : 2 ^ n' = 2 * 2 ^ (n' - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    exact ⟨2 ^ (n' - 1) - 1, by omega⟩
  have hlt : Fintype.card (Fin 3 ⊕ Fin 3) < Nat.card Fˣ := by
    rw [Fintype.card_sum, Fintype.card_fin, hcu]
    omega
  obtain ⟨b, m, hm, hbm, hb⟩ := exists_odd_regular_of_homs θ hθs hodd hlt
  have hbU : (b : SpecialLinearGroup (Fin 3) F) ∈ LinearFlag.upperTriangular 3 F := b.2
  have hbN : (b : SpecialLinearGroup (Fin 3) F) ∈
      Subgroup.normalizer ((Q0 : Subgroup (SpecialLinearGroup (Fin 3) F)) : Set _) := by
    rw [hN]; exact hbU
  refine ⟨b, hbN, m, hm, congrArg Subtype.val hbm, ?_, ?_⟩
  · refine eq_zero_of_mulVec_eq_of_upper _
      (LinearFlag.mem_upperTriangular_iff_isUpperTriangular.mp hbU) (fun j hj => ?_)
    apply hb (Sum.inl j)
    apply Units.ext
    show ((diagEntrySL3 (F := F) j).toHomUnits b : F) = 1
    rw [MonoidHom.coe_toHomUnits]
    exact hj
  · rw [← hαBc b]
    refine eq_zero_of_mulVec_eq_of_upper _
      (LinearFlag.mem_upperTriangular_iff_isUpperTriangular.mp (αB b).2) (fun j hj => ?_)
    apply hb (Sum.inr j)
    apply Units.ext
    show (((diagEntrySL3 (F := F) j).toHomUnits (αB b)) : F) = 1
    rw [MonoidHom.coe_toHomUnits]
    exact hj

end SL3

section Stated

@[expose] def NoFixedVec {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    (c : GL ι F) : Prop :=
  ∀ x : ι → F, (c : Matrix ι ι F).mulVec x = x → x = 0

theorem NoFixedVec.conj {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    {c : GL ι F} (hc : NoFixedVec c) (g : GL ι F) : NoFixedVec (g * c * g⁻¹) := by
  intro x hx
  set y := ((g⁻¹ : GL ι F) : Matrix ι ι F).mulVec x with hy
  have hgy : ((g : GL ι F) : Matrix ι ι F).mulVec y = x := by
    rw [hy, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hcy : ((c : GL ι F) : Matrix ι ι F).mulVec y = y := by
    have h1 : ((g⁻¹ : GL ι F) : Matrix ι ι F).mulVec
        ((((g * c * g⁻¹ : GL ι F)) : Matrix ι ι F).mulVec x) =
        ((g⁻¹ : GL ι F) : Matrix ι ι F).mulVec x := by rw [hx]
    have e1 : ((g⁻¹ : GL ι F) : Matrix ι ι F) * (((g : GL ι F) : Matrix ι ι F) * (c : Matrix ι ι F) *
        ((g⁻¹ : GL ι F) : Matrix ι ι F)) = (c : Matrix ι ι F) * ((g⁻¹ : GL ι F) : Matrix ι ι F) := by
      calc ((g⁻¹ : GL ι F) : Matrix ι ι F) * (((g : GL ι F) : Matrix ι ι F) * (c : Matrix ι ι F) *
            ((g⁻¹ : GL ι F) : Matrix ι ι F))
          = (((g⁻¹ : GL ι F) : Matrix ι ι F) * ((g : GL ι F) : Matrix ι ι F)) * (c : Matrix ι ι F) *
            ((g⁻¹ : GL ι F) : Matrix ι ι F) := by simp only [Matrix.mul_assoc]
        _ = (c : Matrix ι ι F) * ((g⁻¹ : GL ι F) : Matrix ι ι F) := by
          rw [Units.inv_mul, Matrix.one_mul]
    rw [Matrix.mulVec_mulVec, Units.val_mul, Units.val_mul, e1, ← Matrix.mulVec_mulVec] at h1
    rw [hy]
    exact h1
  have hy0 := hc y hcy
  rw [← hgy, hy0, Matrix.mulVec_zero]

variable {F : Type} [Field F]

theorem statedSL3_regular_twist [Finite F] [CharP F 2] {n' : ℕ} (hn' : 3 ≤ n') (hK : Nat.card F = 2 ^ n')
    (Q : Sylow 2 ↥(StatedSL 3 F)) (α : ↥(StatedSL 3 F) ≃* ↥(StatedSL 3 F))
    (hα : ∀ x, x ∈ (Q : Subgroup ↥(StatedSL 3 F)) ↔ α x ∈ (Q : Subgroup ↥(StatedSL 3 F))) :
    ∃ c : ↥(StatedSL 3 F), c ∈ Subgroup.normalizer ((Q : Subgroup ↥(StatedSL 3 F)) : Set _) ∧
      ∃ m : ℕ, Odd m ∧ c ^ m = 1 ∧ NoFixedVec (c : GL (Fin 3) F) ∧
        NoFixedVec ((α c : ↥(StatedSL 3 F)) : GL (Fin 3) F) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e := specialLinearGroupEquivStatedSL 3 F
  obtain ⟨Q0, hQ0⟩ := LinearFlag.exists_sylow_unitriangular (K := F) 2 (n := 3) (by norm_num)
  let Q0' : Sylow 2 ↥(StatedSL 3 F) :=
    Q0.comapOfInjective e.symm.toMonoidHom e.symm.injective
      (by rw [MonoidHom.range_eq_top.mpr e.symm.surjective]; exact le_top)
  have hmem : ∀ h : ↥(StatedSL 3 F), h ∈ (Q0' : Subgroup ↥(StatedSL 3 F)) ↔
      e.symm h ∈ (Q0 : Subgroup (SpecialLinearGroup (Fin 3) F)) := fun h => Iff.rfl
  refine exists_regular_twist_of_std (fun c : ↥(StatedSL 3 F) => NoFixedVec (c : GL (Fin 3) F))
    (fun g c hc => by
      have := NoFixedVec.conj hc (g : GL (Fin 3) F)
      simpa using this) Q0' ?_ Q α hα
  intro α' hα'
  let αs : SpecialLinearGroup (Fin 3) F ≃* SpecialLinearGroup (Fin 3) F :=
    e.trans (α'.trans e.symm)
  have hαs : ∀ x, x ∈ (Q0 : Subgroup (SpecialLinearGroup (Fin 3) F)) ↔
      αs x ∈ (Q0 : Subgroup (SpecialLinearGroup (Fin 3) F)) := by
    intro x
    have h1 : x ∈ (Q0 : Subgroup (SpecialLinearGroup (Fin 3) F)) ↔
        e x ∈ (Q0' : Subgroup ↥(StatedSL 3 F)) := by rw [hmem, e.symm_apply_apply]
    rw [h1, hα' (e x), hmem]
    rfl
  obtain ⟨c, hcN, m, hm, hcm, hr0, hr1⟩ := sl3_std_twist hn' hK Q0 hQ0 αs hαs
  have hcN' : e c ∈ Subgroup.normalizer ((Q0' : Subgroup ↥(StatedSL 3 F)) : Set _) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [hmem, hmem, map_mul, map_mul, map_inv, e.symm_apply_apply]
    exact Subgroup.mem_normalizer_iff.mp hcN (e.symm h)
  refine ⟨e c, hcN', m, hm, by rw [← map_pow, hcm, map_one], ?_, ?_⟩
  · intro x hx
    exact hr0 x hx
  · intro x hx
    have h2 : α' (e c) = e (αs c) := by
      simp [αs]
    rw [h2] at hx
    exact hr1 x hx

end Stated

section Sp4

variable {F : Type} [Field F]

theorem noFixedVec_of_borel {r : ℕ} (g : ↥(StatedSp r F))
    (hg : g ∈ SymplecticFlag.borelSubgroup r F) (hd : ∀ i, SymplecticFlag.diagEntry g i ≠ 1) :
    NoFixedVec (g : GL (Fin r ⊕ Fin r) F) := by
  intro x hx
  set M := ((g : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) with hM
  have hup := SymplecticFlag.mem_borelSubgroup_iff_reindex.mp hg
  have key : ∀ a, (reindex (SymplecticFlag.flagOrder r) (SymplecticFlag.flagOrder r) M) a a ≠ 1 := by
    intro a
    obtain ⟨y, rfl⟩ := (SymplecticFlag.flagOrder r).surjective a
    simp only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply]
    rcases y with j | j
    · exact hd j
    · obtain ⟨A, C, hA, hdet, -, hgA⟩ := SymplecticFlag.mem_borelSubgroup_iff.mp hg
      have h1 := SymplecticFlag.mul_inv_apply_self_of_isUpperTriangular hA hdet j
      have h2 : M (Sum.inr j) (Sum.inr j) = (A⁻¹) j j := by
        rw [hM, hgA, SymplecticFlag.blockMat, fromBlocks_apply₂₂, transpose_apply]
      rw [h2]
      intro h
      rw [h, mul_one] at h1
      apply hd j
      show M (Sum.inl j) (Sum.inl j) = 1
      rw [hM, hgA, SymplecticFlag.blockMat, fromBlocks_apply₁₁]
      exact h1
  have hv : (reindex (SymplecticFlag.flagOrder r) (SymplecticFlag.flagOrder r) M).mulVec
      (x ∘ (SymplecticFlag.flagOrder r).symm) = x ∘ (SymplecticFlag.flagOrder r).symm := by
    rw [reindex_apply, Matrix.submatrix_mulVec_equiv]
    have : (x ∘ (SymplecticFlag.flagOrder r).symm) ∘ ((SymplecticFlag.flagOrder r).symm).symm = x := by
      funext y
      simp
    rw [this, hx]
  have h0 := eq_zero_of_mulVec_eq_of_upper _ hup key _ hv
  funext y
  have := congrFun h0 (SymplecticFlag.flagOrder r y)
  simpa using this

private noncomputable def diagCharSp4 (j : Fin 2) :
    ↥(SymplecticFlag.borelSubgroup 2 F) →* Fˣ :=
  (Pi.evalMonoidHom (fun _ : Fin 2 => Fˣ) j).comp (SymplecticFlag.diagHom 2 F)

private theorem diagCharSp4_surjective (j : Fin 2) : Function.Surjective (diagCharSp4 (F := F) j) := by
  intro a
  obtain ⟨g, hg⟩ := SymplecticFlag.diagHom_surjective (r := 2) (K := F) (Pi.mulSingle j a)
  refine ⟨g, ?_⟩
  simp [diagCharSp4, hg]

theorem sp4_std_twist [Finite F] {n' : ℕ} (hn' : 3 ≤ n') (hK : Nat.card F = 2 ^ n')
    (Q0 : Sylow 2 ↥(StatedSp 2 F))
    (hQ0 : (Q0 : Subgroup ↥(StatedSp 2 F)) = SymplecticFlag.unipotent 2 F)
    (α : ↥(StatedSp 2 F) ≃* ↥(StatedSp 2 F))
    (hα : ∀ x, x ∈ (Q0 : Subgroup ↥(StatedSp 2 F)) ↔ α x ∈ (Q0 : Subgroup ↥(StatedSp 2 F))) :
    ∃ c : ↥(StatedSp 2 F), c ∈ Subgroup.normalizer ((Q0 : Subgroup ↥(StatedSp 2 F)) : Set _) ∧
      ∃ m : ℕ, Odd m ∧ c ^ m = 1 ∧ NoFixedVec (c : GL (Fin 2 ⊕ Fin 2) F) ∧
        NoFixedVec ((α c : ↥(StatedSp 2 F)) : GL (Fin 2 ⊕ Fin 2) F) := by
  have hN : Subgroup.normalizer ((Q0 : Subgroup ↥(StatedSp 2 F)) : Set _) =
      SymplecticFlag.borelSubgroup 2 F := by
    rw [hQ0, SymplecticHigher.normalizer_unipotent]
  obtain ⟨αB, hαBs, hαBc⟩ := exists_restrict_aut hN α hα
  let θ : Fin 2 ⊕ Fin 2 → ↥(SymplecticFlag.borelSubgroup 2 F) →* Fˣ :=
    Sum.elim (fun j => diagCharSp4 (F := F) j) (fun j => (diagCharSp4 (F := F) j).comp αB)
  have hθs : ∀ i, Function.Surjective (θ i) := by
    rintro (j | j)
    · exact diagCharSp4_surjective j
    · exact (diagCharSp4_surjective j).comp hαBs
  have hq : 8 ≤ Nat.card F := by
    rw [hK]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n' := Nat.pow_le_pow_right (by norm_num) hn'
  have hcu : Nat.card Fˣ = Nat.card F - 1 := Nat.card_units _
  have hodd : Odd (Nat.card Fˣ) := by
    rw [hcu, hK]
    have h1 : 1 ≤ 2 ^ (n' - 1) := Nat.one_le_two_pow
    have h2 : 2 ^ n' = 2 * 2 ^ (n' - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    exact ⟨2 ^ (n' - 1) - 1, by omega⟩
  have hlt : Fintype.card (Fin 2 ⊕ Fin 2) < Nat.card Fˣ := by
    rw [Fintype.card_sum, Fintype.card_fin, hcu]
    omega
  obtain ⟨b, m, hm, hbm, hb⟩ := exists_odd_regular_of_homs θ hθs hodd hlt
  have hbU : (b : ↥(StatedSp 2 F)) ∈ SymplecticFlag.borelSubgroup 2 F := b.2
  have hbN : (b : ↥(StatedSp 2 F)) ∈ Subgroup.normalizer ((Q0 : Subgroup ↥(StatedSp 2 F)) : Set _) := by
    rw [hN]; exact hbU
  refine ⟨b, hbN, m, hm, congrArg Subtype.val hbm, ?_, ?_⟩
  · refine noFixedVec_of_borel _ hbU (fun j hj => ?_)
    apply hb (Sum.inl j)
    apply Units.ext
    show ((SymplecticFlag.diagHom 2 F b j : Fˣ) : F) = 1
    rw [SymplecticFlag.coe_diagHom_apply]
    exact hj
  · rw [← hαBc b]
    refine noFixedVec_of_borel _ (αB b).2 (fun j hj => ?_)
    apply hb (Sum.inr j)
    apply Units.ext
    show ((SymplecticFlag.diagHom 2 F (αB b) j : Fˣ) : F) = 1
    rw [SymplecticFlag.coe_diagHom_apply]
    exact hj

theorem statedSp4_regular_twist [Finite F] [CharP F 2] {n' : ℕ} (hn' : 3 ≤ n')
    (hK : Nat.card F = 2 ^ n') (Q : Sylow 2 ↥(StatedSp 2 F)) (α : ↥(StatedSp 2 F) ≃* ↥(StatedSp 2 F))
    (hα : ∀ x, x ∈ (Q : Subgroup ↥(StatedSp 2 F)) ↔ α x ∈ (Q : Subgroup ↥(StatedSp 2 F))) :
    ∃ c : ↥(StatedSp 2 F), c ∈ Subgroup.normalizer ((Q : Subgroup ↥(StatedSp 2 F)) : Set _) ∧
      ∃ m : ℕ, Odd m ∧ c ^ m = 1 ∧ NoFixedVec (c : GL (Fin 2 ⊕ Fin 2) F) ∧
        NoFixedVec ((α c : ↥(StatedSp 2 F)) : GL (Fin 2 ⊕ Fin 2) F) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q0, hQ0⟩ := SymplecticFlag.exists_sylow_unipotent (K := F) 2 2
  exact exists_regular_twist_of_std (fun c : ↥(StatedSp 2 F) => NoFixedVec (c : GL (Fin 2 ⊕ Fin 2) F))
    (fun g c hc => by
      have := NoFixedVec.conj hc (g : GL (Fin 2 ⊕ Fin 2) F)
      simpa using this) Q0 (fun α' hα' => sp4_std_twist hn' hK Q0 hQ0 α' hα') Q α hα

end Sp4

end CFSG.Quasithin

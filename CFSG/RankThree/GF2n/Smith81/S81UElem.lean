module

public import CFSG.RankThree.GF2n.Smith81.S81UModelData
public import CFSG.LinearAlgebra.SchurElemAbelianTwo
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKLift
public import CFSG.RankThree.GF2n.Smith81.OrthSetup
import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.U6Cube CFSG.RankThree.GF2n.Smith81.A5Cube
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary

section SelfAdjoint

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

@[expose] def nilpOf (e : GL (Fin n) F) : Matrix (Fin n) (Fin n) F :=
  (e : Matrix (Fin n) (Fin n) F) - 1

@[expose] def nilpSpan (E : Subgroup (GL (Fin n) F)) : Submodule F (Matrix (Fin n) (Fin n) F) :=
  Submodule.span F (Set.range fun e : E => nilpOf (e : GL (Fin n) F))

theorem nilpOf_mem_nilpSpan (E : Subgroup (GL (Fin n) F)) (e : E) :
    nilpOf (e : GL (Fin n) F) ∈ nilpSpan E :=
  Submodule.subset_span ⟨e, rfl⟩

private theorem nilpSpan_aux_mat_comm {E : Subgroup (GL (Fin n) F)} (hE : IsElemAbelian 2 E)
    (e e' : E) :
    ((e : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        ((e' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      ((e' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        ((e : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
  rw [← Units.val_mul, ← Units.val_mul, hE.comm e.2 e'.2]

private theorem nilpSpan_aux_mat_sq {E : Subgroup (GL (Fin n) F)} (hE : IsElemAbelian 2 E)
    (e : E) :
    ((e : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        ((e : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
  rw [← Units.val_mul, hE.mul_self_eq_one e.2, Units.val_one]

private theorem nilpSpan_aux_add_self (M : Matrix (Fin n) (Fin n) F) : M + M = 0 := by
  ext i j
  simp only [Matrix.add_apply, Matrix.zero_apply]
  exact CharTwo.add_self_eq_zero _

private theorem nilpSpan_aux_gen_comm {E : Subgroup (GL (Fin n) F)} (hE : IsElemAbelian 2 E)
    (e e' : E) :
    nilpOf (e : GL (Fin n) F) * nilpOf (e' : GL (Fin n) F) =
      nilpOf (e' : GL (Fin n) F) * nilpOf (e : GL (Fin n) F) := by
  have h := nilpSpan_aux_mat_comm hE e e'
  simp only [nilpOf, sub_mul, mul_sub, mul_one, one_mul]
  rw [h]
  abel

theorem nilpSpan_comm {E : Subgroup (GL (Fin n) F)} (hE : IsElemAbelian 2 E)
    {X Y : Matrix (Fin n) (Fin n) F} (hX : X ∈ nilpSpan E) (hY : Y ∈ nilpSpan E) :
    X * Y = Y * X := by
  have hgen : ∀ Z ∈ nilpSpan E, ∀ e : E,
      Z * nilpOf (e : GL (Fin n) F) = nilpOf (e : GL (Fin n) F) * Z := by
    intro Z hZ e
    induction hZ using Submodule.span_induction with
    | mem W hW =>
      obtain ⟨e', rfl⟩ := hW
      exact (nilpSpan_aux_gen_comm hE e e').symm
    | zero => simp
    | add z w _ _ ihz ihw => rw [add_mul, mul_add, ihz, ihw]
    | smul a z _ ih => rw [smul_mul_assoc, ih, mul_smul_comm]
  induction hY using Submodule.span_induction with
  | mem W hW =>
    obtain ⟨e, rfl⟩ := hW
    exact hgen X hX e
  | zero => simp
  | add z w _ _ ihz ihw => rw [mul_add, add_mul, ihz, ihw]
  | smul a z _ ih => rw [mul_smul_comm, smul_mul_assoc, ih]

theorem nilpSpan_mul_mem {E : Subgroup (GL (Fin n) F)}
    {X Y : Matrix (Fin n) (Fin n) F} (hX : X ∈ nilpSpan E) (hY : Y ∈ nilpSpan E) :
    X * Y ∈ nilpSpan E := by
  have hgg : ∀ e e' : E, nilpOf (e : GL (Fin n) F) * nilpOf (e' : GL (Fin n) F) ∈ nilpSpan E := by
    intro e e'
    have key : nilpOf (e : GL (Fin n) F) * nilpOf (e' : GL (Fin n) F) =
        nilpOf ((e * e' : E) : GL (Fin n) F) - nilpOf (e : GL (Fin n) F)
          - nilpOf (e' : GL (Fin n) F) := by
      simp only [nilpOf, Subgroup.coe_mul, Units.val_mul]
      noncomm_ring
    rw [key]
    exact sub_mem (sub_mem (nilpOf_mem_nilpSpan E _) (nilpOf_mem_nilpSpan E _))
      (nilpOf_mem_nilpSpan E _)
  have hgen : ∀ e : E, ∀ Z ∈ nilpSpan E, nilpOf (e : GL (Fin n) F) * Z ∈ nilpSpan E := by
    intro e Z hZ
    induction hZ using Submodule.span_induction with
    | mem W hW =>
      obtain ⟨e', rfl⟩ := hW
      exact hgg e e'
    | zero => simp
    | add z w _ _ ihz ihw => rw [mul_add]; exact add_mem ihz ihw
    | smul a z _ ih => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ ih
  induction hX using Submodule.span_induction with
  | mem W hW =>
    obtain ⟨e, rfl⟩ := hW
    exact hgen e Y hY
  | zero => simp
  | add z w _ _ ihz ihw => rw [add_mul]; exact add_mem ihz ihw
  | smul a z _ ih => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ ih

theorem nilpSpan_sq {E : Subgroup (GL (Fin n) F)} (hE : IsElemAbelian 2 E)
    {X : Matrix (Fin n) (Fin n) F} (hX : X ∈ nilpSpan E) : X * X = 0 := by
  induction hX using Submodule.span_induction with
  | mem W hW =>
    obtain ⟨e, rfl⟩ := hW
    have hee := nilpSpan_aux_mat_sq hE e
    have hsq : ∀ M : Matrix (Fin n) (Fin n) F, (M - 1) * (M - 1) = M * M - (M + M) + 1 :=
      fun M => by noncomm_ring
    unfold nilpOf
    rw [hsq, hee, nilpSpan_aux_add_self, sub_zero, nilpSpan_aux_add_self]
  | zero => simp
  | add z w hz hw ihz ihw =>
    rw [add_mul, mul_add, mul_add, ihz, ihw, nilpSpan_comm hE hz hw, zero_add, add_zero]
    exact nilpSpan_aux_add_self _
  | smul a z _ ih =>
    rw [smul_mul_assoc, mul_smul_comm, ih]
    simp

private theorem matrix_add_self_aux (M : Matrix (Fin n) (Fin n) F) : M + M = 0 :=
  Matrix.ext fun i j => CharTwo.add_self_eq_zero (M i j)

private theorem one_add_mul_aux (X Y : Matrix (Fin n) (Fin n) F) :
    (1 + X) * (1 + Y) = 1 + (X + Y + X * Y) := by
  noncomm_ring

private theorem one_add_sq_zero_aux (X : Matrix (Fin n) (Fin n) F) (h : X * X = 0) :
    (1 + X) * (1 + X) = 1 := by
  rw [one_add_mul_aux, matrix_add_self_aux X, h, add_zero, add_zero]

@[expose] def unitOfSqZero (X : Matrix (Fin n) (Fin n) F) (h : X * X = 0) : GL (Fin n) F where
  val := 1 + X
  inv := 1 + X
  val_inv := by exact one_add_sq_zero_aux X h
  inv_val := by exact one_add_sq_zero_aux X h

theorem unitOfSqZero_val (X : Matrix (Fin n) (Fin n) F) (h : X * X = 0) :
    ((unitOfSqZero X h : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 + X := rfl

@[expose] def oneAdd (S : Submodule F (Matrix (Fin n) (Fin n) F))
    (hmul : ∀ X ∈ S, ∀ Y ∈ S, X * Y ∈ S) (hsq : ∀ X ∈ S, X * X = 0) : Subgroup (GL (Fin n) F) where
  carrier := {g | ∃ X ∈ S, (g : Matrix (Fin n) (Fin n) F) = 1 + X}
  mul_mem' := by
    rintro a b ⟨X, hX, ha⟩ ⟨Y, hY, hb⟩
    refine ⟨X + Y + X * Y, S.add_mem (S.add_mem hX hY) (hmul X hX Y hY), ?_⟩
    rw [Units.val_mul, ha, hb, one_add_mul_aux]
  one_mem' := ⟨0, S.zero_mem, by simp⟩
  inv_mem' := by
    rintro g ⟨X, hX, hg⟩
    have hgg : g * g = 1 := by
      apply Units.ext
      rw [Units.val_mul, hg, Units.val_one]
      exact one_add_sq_zero_aux X (hsq X hX)
    refine ⟨X, hX, ?_⟩
    rw [inv_eq_of_mul_eq_one_right hgg]
    exact hg

theorem unitOfSqZero_mem_oneAdd (S : Submodule F (Matrix (Fin n) (Fin n) F))
    (hmul : ∀ X ∈ S, ∀ Y ∈ S, X * Y ∈ S) (hsq : ∀ X ∈ S, X * X = 0) {X : Matrix (Fin n) (Fin n) F}
    (hX : X ∈ S) : unitOfSqZero X (hsq X hX) ∈ oneAdd S hmul hsq :=
  ⟨X, hX, rfl⟩

theorem isElemAbelian_oneAdd (S : Submodule F (Matrix (Fin n) (Fin n) F))
    (hmul : ∀ X ∈ S, ∀ Y ∈ S, X * Y ∈ S) (hsq : ∀ X ∈ S, X * X = 0)
    (hcomm : ∀ X ∈ S, ∀ Y ∈ S, X * Y = Y * X) : IsElemAbelian 2 (oneAdd S hmul hsq) := by
  refine ⟨⟨⟨fun a b => Subtype.ext (Units.ext ?_)⟩⟩, fun x hx => ?_⟩
  · obtain ⟨X, hX, ha⟩ := a.2
    obtain ⟨Y, hY, hb⟩ := b.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, ha, hb,
      one_add_mul_aux, one_add_mul_aux, hcomm X hX Y hY]
    abel
  · obtain ⟨X, hX, hx'⟩ := hx
    have hxx : x * x = 1 := by
      apply Units.ext
      rw [Units.val_mul, hx', Units.val_one]
      exact one_add_sq_zero_aux X (hsq X hX)
    rw [pow_two]
    exact hxx

private theorem conjTr_smul_aux (σ : F ≃+* F) (c : F) (A : Matrix (Fin n) (Fin n) F) :
    conjTr σ (c • A) = σ c • conjTr σ A := by
  ext i j
  simp [conjTr]

private theorem selfAdjoint_pair_eq {σ : F ≃+* F} {ω : F} (hω : σ ω ≠ ω)
    {a a' b b' : Matrix (Fin n) (Fin n) F} (ha : conjTr σ a = a) (ha' : conjTr σ a' = a')
    (hb : conjTr σ b = b) (hb' : conjTr σ b' = b') (h : a + ω • b = a' + ω • b') :
    a = a' ∧ b = b' := by
  have hc := congrArg (conjTr σ) h
  rw [conjTr_add, conjTr_add, conjTr_smul_aux, conjTr_smul_aux, ha, ha', hb, hb'] at hc
  have h1 : (a - a') + ω • (b - b') = 0 := by
    have e : (a - a') + ω • (b - b') = (a + ω • b) - (a' + ω • b') := by
      rw [smul_sub]; abel
    rw [e, h, sub_self]
  have h2 : (a - a') + σ ω • (b - b') = 0 := by
    have e : (a - a') + σ ω • (b - b') = (a + σ ω • b) - (a' + σ ω • b') := by
      rw [smul_sub]; abel
    rw [e, hc, sub_self]
  have h3 : (ω - σ ω) • (b - b') = 0 := by
    have e : (ω - σ ω) • (b - b') = ((a - a') + ω • (b - b')) - ((a - a') + σ ω • (b - b')) := by
      rw [sub_smul]; abel
    rw [e, h1, h2, sub_self]
  have hb0 : b - b' = 0 := by
    rcases smul_eq_zero.1 h3 with h4 | h4
    · exact absurd (sub_eq_zero.1 h4).symm hω
    · exact h4
  rw [hb0, smul_zero, add_zero] at h1
  exact ⟨sub_eq_zero.1 h1, sub_eq_zero.1 hb0⟩

private theorem unitOfSqZero_inj_aux {X X' : Matrix (Fin n) (Fin n) F} (h : X * X = 0)
    (h' : X' * X' = 0) (e : unitOfSqZero X h = unitOfSqZero X' h') : X = X' := by
  have h1 := congrArg Units.val e
  rw [unitOfSqZero_val, unitOfSqZero_val] at h1
  exact add_left_cancel h1

theorem card_sq_le_card_oneAdd (σ : F ≃+* F) (hne : ∃ c, σ c ≠ c) {E : Subgroup (GL (Fin n) F)}
    (hE : IsElemAbelian 2 E)
    (hsa : ∀ e ∈ E, conjTr σ (e : Matrix (Fin n) (Fin n) F) = (e : Matrix (Fin n) (Fin n) F)) :
    Nat.card E ^ 2 ≤ Nat.card (oneAdd (nilpSpan E) (fun _ hX _ hY => nilpSpan_mul_mem hX hY)
      (fun _ hX => nilpSpan_sq hE hX)) := by
  obtain ⟨ω, hω⟩ := hne
  have hsa' : ∀ e ∈ E, conjTr σ (nilpOf (e : GL (Fin n) F)) = nilpOf (e : GL (Fin n) F) := by
    intro e he
    unfold nilpOf
    rw [conjTr_sub, conjTr_one, hsa e he]
  have hY : ∀ p : ↥E × ↥E,
      nilpOf ((p.1 : GL (Fin n) F)) + ω • nilpOf ((p.2 : GL (Fin n) F)) ∈ nilpSpan E :=
    fun p => Submodule.add_mem _ (nilpOf_mem_nilpSpan E p.1)
      (Submodule.smul_mem _ ω (nilpOf_mem_nilpSpan E p.2))
  let f : ↥E × ↥E → ↥(oneAdd (nilpSpan E) (fun _ hX _ hY => nilpSpan_mul_mem hX hY)
      (fun _ hX => nilpSpan_sq hE hX)) :=
    fun p => ⟨unitOfSqZero _ (nilpSpan_sq hE (hY p)), unitOfSqZero_mem_oneAdd _ _ _ (hY p)⟩
  have hf : Function.Injective f := by
    intro p p' h
    have e0 := congrArg Subtype.val h
    have e : unitOfSqZero (nilpOf ((p.1 : GL (Fin n) F)) + ω • nilpOf ((p.2 : GL (Fin n) F)))
        (nilpSpan_sq hE (hY p)) = unitOfSqZero
          (nilpOf ((p'.1 : GL (Fin n) F)) + ω • nilpOf ((p'.2 : GL (Fin n) F)))
          (nilpSpan_sq hE (hY p')) := e0
    obtain ⟨ha, hb⟩ := selfAdjoint_pair_eq hω (hsa' _ p.1.2) (hsa' _ p'.1.2)
      (hsa' _ p.2.2) (hsa' _ p'.2.2) (unitOfSqZero_inj_aux _ _ e)
    unfold nilpOf at ha hb
    exact Prod.ext (Subtype.ext (Units.ext (sub_left_inj.1 ha)))
      (Subtype.ext (Units.ext (sub_left_inj.1 hb)))
  have hcard := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod] at hcard
  have h2 : Nat.card E ^ 2 = Nat.card E * Nat.card E := by ring
  rw [h2]
  exact hcard

theorem card_sq_le_pow_of_isElemAbelian_conjTr (σ : F ≃+* F) (hne : ∃ c, σ c ≠ c)
    {E : Subgroup (GL (Fin n) F)} (hE : IsElemAbelian 2 E)
    (hsa : ∀ e ∈ E, conjTr σ (e : Matrix (Fin n) (Fin n) F) = (e : Matrix (Fin n) (Fin n) F)) :
    Nat.card E ^ 2 ≤ Nat.card F ^ (n * n / 4) := by
  refine (card_sq_le_card_oneAdd σ hne hE hsa).trans ?_
  exact CFSG.LinearAlgebra.SchurElemAbelianTwo.card_le_pow_of_isElemAbelian_two
    (isElemAbelian_oneAdd _ _ _ fun _ hX _ hY => nilpSpan_comm hE hX hY)

theorem conjTr_eq_of_mem_SUid_of_elemAbelian (σ : F ≃+* F) {E : Subgroup (GL (Fin n) F)}
    (hE : IsElemAbelian 2 E) (hle : E ≤ SUid σ n) :
    ∀ e ∈ E, conjTr σ (e : Matrix (Fin n) (Fin n) F) = (e : Matrix (Fin n) (Fin n) F) := by
  intro e he
  have h1 : conjTr σ (e : Matrix (Fin n) (Fin n) F) * (e : Matrix (Fin n) (Fin n) F) = 1 :=
    (mem_SUid.mp (hle he)).2
  have h2 : (e : Matrix (Fin n) (Fin n) F) * (e : Matrix (Fin n) (Fin n) F) = 1 := by
    rw [← Units.val_mul, IsElemAbelian.mul_self_eq_one hE he, Units.val_one]
  calc conjTr σ (e : Matrix (Fin n) (Fin n) F)
      = conjTr σ (e : Matrix (Fin n) (Fin n) F) *
          ((e : Matrix (Fin n) (Fin n) F) * (e : Matrix (Fin n) (Fin n) F)) := by
        rw [h2, Matrix.mul_one]
    _ = (conjTr σ (e : Matrix (Fin n) (Fin n) F) * (e : Matrix (Fin n) (Fin n) F)) *
          (e : Matrix (Fin n) (Fin n) F) := by
        rw [Matrix.mul_assoc]
    _ = (e : Matrix (Fin n) (Fin n) F) := by
        rw [h1, Matrix.one_mul]

theorem card_sq_le_pow_of_isElemAbelian_SUid {σ : F ≃+* F} (hne : ∃ c, σ c ≠ c)
    {E : Subgroup (GL (Fin n) F)} (hE : IsElemAbelian 2 E) (hle : E ≤ SUid σ n) :
    Nat.card E ^ 2 ≤ Nat.card F ^ (n * n / 4) :=
  card_sq_le_pow_of_isElemAbelian_conjTr σ hne hE (conjTr_eq_of_mem_SUid_of_elemAbelian σ hE hle)

end SelfAdjoint

section FixedField

variable {F : Type} [Field F] [Finite F] [CharP F 2]

private def fσTrace (σ : F ≃+* F) : F →+ F :=
  AddMonoidHom.mk' (fun c => c + σ c) fun a b => by
    simp only [map_add]
    ring

private theorem fσTrace_apply (σ : F ≃+* F) (c : F) : fσTrace σ c = c + σ c := rfl

private theorem mem_ker_fσTrace (σ : F ≃+* F) (c : F) :
    c ∈ (fσTrace σ).ker ↔ σ c = c := by
  rw [AddMonoidHom.mem_ker, fσTrace_apply]
  exact ⟨fun h => (CharTwo.add_eq_zero.mp h).symm, fun h => CharTwo.add_eq_zero.mpr h.symm⟩

private theorem mem_range_fσTrace {σ : F ≃+* F} (hσ : IsUnitaryInvolution σ) (c : F) :
    c ∈ (fσTrace σ).range ↔ σ c = c := by
  rw [AddMonoidHom.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    rw [fσTrace_apply]
    exact hσ.trace_fixed x
  · intro h
    obtain ⟨x, hx⟩ := hσ.trace_surj c h
    exact ⟨x, (fσTrace_apply σ x).trans hx⟩

theorem card_Fσ_sq {σ : F ≃+* F} (hσ : IsUnitaryInvolution σ) :
    Nat.card (Fσ σ) ^ 2 = Nat.card F := by
  have hker : (fσTrace σ).ker = (Fσ σ).toAddSubgroup := by
    ext c
    rw [mem_ker_fσTrace, Subfield.mem_toAddSubgroup, mem_Fσ_iff]
  have hran : (fσTrace σ).range = (Fσ σ).toAddSubgroup := by
    ext c
    rw [mem_range_fσTrace hσ, Subfield.mem_toAddSubgroup, mem_Fσ_iff]
  have hS : Nat.card (Fσ σ).toAddSubgroup = Nat.card (Fσ σ) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ => Subfield.mem_toAddSubgroup)
  have hq : Nat.card (F ⧸ (fσTrace σ).ker) = Nat.card (fσTrace σ).range :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange (fσTrace σ)).toEquiv
  have hF := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (fσTrace σ).ker
  rw [hq, hker, hran, hS] at hF
  rw [hF, sq]

theorem card_Fσ_eq {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2) :
    Nat.card (Fσ (unitaryInvolution F 2 f)) = 2 ^ f := by
  have h := card_Fσ_sq (isUnitaryInvolution_unitaryInvolution hF)
  rw [hF] at h
  exact Nat.pow_left_injective (by norm_num) h

end FixedField

section StatedProjU

variable {F : Type} [Field F] [Finite F] [CharP F 2]

private theorem odd_card_subgroupOf_scalars_aux {K : Type} [Field K] [Finite K] {q d : ℕ}
    (hK : Nat.card K = q ^ 2) (hq : Even q) (hq0 : q ≠ 0) (H : Subgroup (GL (Fin d) K)) :
    Odd (Nat.card ((StatedScalars (Fin d) K).subgroupOf H)) := by
  by_contra hodd
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card ((StatedScalars (Fin d) K).subgroupOf H) :=
    even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hodd)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 x.2
  have hcard : Nat.card Kˣ = q ^ 2 - 1 := by
    classical
    have := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
  have hm : x ^ (q ^ 2 - 1) = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    have hc1 : c ^ (q ^ 2 - 1) = 1 := by rw [← hcard]; exact pow_card_eq_one'
    have : ((x : H) : GL (Fin d) K) ^ (q ^ 2 - 1) = 1 := by
      rw [← hc, ← map_pow, hc1, map_one]
    simpa using this
  have hdvd : orderOf x ∣ q ^ 2 - 1 := orderOf_dvd_of_pow_eq_one hm
  rw [hx] at hdvd
  have hqq : Even (q ^ 2) := hq.pow_of_ne_zero (by norm_num)
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hq0)
  obtain ⟨r, hr⟩ := hqq
  omega

theorem card_le_pow_nine_of_isElemAbelian_statedProjU {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
    {E : Subgroup (StatedProj (StatedSU 6 (2 ^ f) F))} (hE : IsElemAbelian 2 E) :
    Nat.card E ≤ (2 ^ f) ^ 9 := by
  have hf : f ≠ 0 := by
    rintro rfl
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    rw [hF] at h1
    norm_num at h1
  have heven : Even (2 ^ f) := Nat.even_pow.2 ⟨even_two, hf⟩
  have hq0 : (2 : ℕ) ^ f ≠ 0 := pow_ne_zero f two_ne_zero
  have hodd := odd_card_subgroupOf_scalars_aux hF heven hq0 (StatedSU 6 (2 ^ f) F)
  obtain ⟨E₁, hE₁, hcard⟩ := CFSG.QuasithinUnique.Lin2.exists_isElemAbelian_lift
    ((StatedScalars (Fin 6) F).subgroupOf (StatedSU 6 (2 ^ f) F)) hodd hE
  have hE₂ : IsElemAbelian 2 (E₁.map (StatedSU 6 (2 ^ f) F).subtype) := hE₁.map _
  have hle : E₁.map (StatedSU 6 (2 ^ f) F).subtype ≤ SUid (unitaryInvolution F 2 f) 6 := by
    rintro _ ⟨x, -, rfl⟩
    exact (SUid_eq_statedSU hF 6).ge x.2
  have hσ := CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hF
  have h := card_sq_le_pow_of_isElemAbelian_SUid hσ.exists_ne hE₂ hle
  rw [Subgroup.card_map_of_injective (StatedSU 6 (2 ^ f) F).subtype_injective, hcard, hF] at h
  have h9 : (((2 : ℕ) ^ f) ^ 2) ^ (6 * 6 / 4) = (((2 : ℕ) ^ f) ^ 9) ^ 2 := by
    rw [show 6 * 6 / 4 = 9 by norm_num]
    exact pow_right_comm ((2 : ℕ) ^ f) 2 9
  exact (Nat.pow_le_pow_iff_left two_ne_zero).mp (h.trans_eq h9)

end StatedProjU

section ElemBoundU

variable {G : Type} [Group G]

@[expose] def ElemBoundE3UStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B → InCaseE3U M Q Z B → ∀ [(Q.subgroupOf M).Normal], ∀ n : ℕ, Width Q Z n →
      ∀ A : Subgroup (↥M ⧸ Q.subgroupOf M), A ≤ bar M Q (Lgen M (LB M Q B)) →
        IsElemAbelian 2 A → Nat.card A ≤ Nat.card Z ^ (n - 1)

theorem elemBoundE3U_of_uniform
    (hFE1 : Smith24E3UUniformStatement) : ElemBoundE3UStatement := by
  intro G _ _ M Q Z B IH hc h3U _ n hw A hAS hAel
  have hw10 : Width Q Z 10 := by
    obtain ⟨t, -, h⟩ := h3U
    exact h.1
  have hn : n = 10 := width_unique hc.ctx.hyp hw hw10
  subst hn
  obtain ⟨K, _, _, _, γ, M₀, hg⟩ := stroth_globalModelData hc.ctx.hyp
  obtain ⟨F, _, _, _, f, hF, e, ψ, φ, d⟩ := hFE1 G M Q Z B IH hc.toRemCfg h3U K γ M₀ hg
  have hLM : Lgen M (LB M Q B) ≤ M := iSup₂_le fun m hm => by
    calc conjSubgroup m (LB M Q B) ≤ conjSubgroup m M := Subgroup.map_mono hc.ctx.LB_le_M
      _ = M := hc.ctx.conj_M_eq hm
  set θ : ↥(Lgen M (LB M Q B)) →* ↥M ⧸ Q.subgroupOf M :=
    (QuotientGroup.mk' (Q.subgroupOf M)).comp (Subgroup.inclusion hLM) with hθ
  have hker : θ.ker = φ.ker := by
    ext s
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, d.ker s, hθ, MonoidHom.comp_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  have hAθ : A ≤ θ.range := by
    intro a ha
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp (hAS ha)
    exact ⟨⟨m, Subgroup.mem_subgroupOf.mp hm⟩, rfl⟩
  let ee : θ.range ≃* φ.range := (QuotientGroup.quotientKerEquivRange θ).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans (QuotientGroup.quotientKerEquivRange φ))
  set A₁ : Subgroup θ.range := A.subgroupOf θ.range with hA₁
  set A₂ : Subgroup (E3UWspace (unitaryInvolution F 2 f) e ≃ₗ[K]
      E3UWspace (unitaryInvolution F 2 f) e) :=
    (A₁.map ee.toMonoidHom).map φ.range.subtype with hA₂
  have hA₂le : A₂ ≤ (cubeHomU hF e).range := by
    rw [cubeHomU_range, ← d.range]
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  set E := A₂.comap (cubeHomU hF e) with hE
  have hA₁el : IsElemAbelian 2 A₁ := hAel.comap θ.range.subtype_injective
  have hA₂el : IsElemAbelian 2 A₂ := (hA₁el.map _).map _
  have hEel : IsElemAbelian 2 E := hA₂el.comap (cubeHomU_injective hF e)
  have hcardE : Nat.card E = Nat.card A := by
    have h1 : Nat.card E = Nat.card A₂ := by
      rw [← Subgroup.card_map_of_injective (f := cubeHomU hF e) (cubeHomU_injective hF e),
        Subgroup.map_comap_eq_self hA₂le]
    have h2 : Nat.card A₂ = Nat.card A₁ := by
      rw [hA₂, Subgroup.card_map_of_injective φ.range.subtype_injective,
        Subgroup.card_map_of_injective ee.injective]
    have h3 : Nat.card A₁ = Nat.card A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAθ).toEquiv
    rw [h1, h2, h3]
  have hbound := card_le_pow_nine_of_isElemAbelian_statedProjU hF hEel
  have hZ : Nat.card Z = 2 ^ f := by
    rw [← hg.card, ← card_Fσ_eq hF]
    exact Nat.card_congr e.toEquiv
  rw [hcardE, ← hZ] at hbound
  simpa using hbound

end ElemBoundU

end CFSG.RankThree.GF2n.Smith81

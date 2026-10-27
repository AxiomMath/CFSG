module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalCoreLine
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylUnitaryDvd
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryDvdAct
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalResU5FiveReg
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalResU5FiveModel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel
open scoped commutatorElement

theorem conjMatrix_injective_U5Five {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F]
    (A₀ : GL ι F) {Z W : GL ι F}
    (h : TypeA.PGLTor.conjMatrix A₀ Z = TypeA.PGLTor.conjMatrix A₀ W) : Z = W := by
  have hPQ : ((A₀⁻¹ : GL ι F) : Matrix ι ι F) * (A₀ : Matrix ι ι F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  apply Units.ext
  have h1 := congrArg (fun T : Matrix ι ι F =>
    ((A₀⁻¹ : GL ι F) : Matrix ι ι F) * T * (A₀ : Matrix ι ι F)) h
  simp only [TypeA.PGLTor.conjMatrix, ← Matrix.mul_assoc, hPQ, Matrix.one_mul] at h1
  simpa only [Matrix.mul_assoc, hPQ, Matrix.mul_one] using h1

theorem exists_pow_five_of_commute_U5Five {k : Type} [Field k] {ζ : k}
    (hζ : IsPrimitiveRoot ζ 5) {y M : GL (Fin 5) k} (hy : y ^ 5 = 1)
    (hys : y ∉ LargeEvenScalars (Fin 5) k) (hMy : M * y = y * M) {μ : kˣ}
    (hM : M ^ 5 = Matrix.GeneralLinearGroup.scalar (Fin 5) μ) : ∃ c : kˣ, c ^ 5 = μ := by
  classical
  have : NeZero 5 := ⟨by norm_num⟩
  obtain ⟨A₀, hA₀⟩ := TypeA.PGLTor.exists_conj_diagonal hζ ({y} : Set (GL (Fin 5) k))
    (fun x hx z hz => by rw [Set.mem_singleton_iff.mp hx, Set.mem_singleton_iff.mp hz])
    (fun x hx => by rw [Set.mem_singleton_iff.mp hx]; exact hy)
  set δ : Fin 5 → k := fun i => TypeA.PGLTor.conjMatrix A₀ y i i with hδdef
  have hD : TypeA.PGLTor.conjMatrix A₀ y = diagonal δ :=
    TypeA.PGLTor.eq_diagonal_of_offDiag_eq_zero (hA₀ y rfl)
  have hδ0 : δ 0 ≠ 0 := by
    intro h0
    have h1 := TypeA.PGLTor.conjMatrix_pow A₀ y 5
    rw [hy, TypeA.PGLTor.conjMatrix_one, hD, diagonal_pow] at h1
    have h2 := congrFun (congrFun h1 0) 0
    simp only [one_apply_eq, diagonal_apply_eq, Pi.pow_apply, h0] at h2
    norm_num at h2
  have hnc : ∃ j, δ j ≠ δ 0 := by
    by_contra hcon
    push Not at hcon
    apply hys
    have hconst : TypeA.PGLTor.conjMatrix A₀ y =
        TypeA.PGLTor.conjMatrix A₀
          (Matrix.GeneralLinearGroup.scalar (Fin 5) (Units.mk0 (δ 0) hδ0)) := by
      rw [TypeA.PGLTor.conjMatrix_scalar, hD, Units.val_mk0, scalar_apply]
      congr 1
      funext j
      exact hcon j
    rw [conjMatrix_injective_U5Five A₀ hconst, largeEvenScalars_def]
    exact ⟨_, rfl⟩
  obtain ⟨j, hj⟩ := hnc
  have hblock : TypeA.PGLTor.IsBlockDiag δ (TypeA.PGLTor.conjMatrix A₀ M) := by
    apply TypeA.PGLTor.isBlockDiag_of_commute_diagonal
    rw [← hD, ← TypeA.PGLTor.conjMatrix_mul, ← TypeA.PGLTor.conjMatrix_mul, hMy]
  have hMp : TypeA.PGLTor.conjMatrix A₀ M ^ 5 = scalar (Fin 5) (μ : k) := by
    rw [← TypeA.PGLTor.conjMatrix_pow, hM, TypeA.PGLTor.conjMatrix_scalar]
  have hcard : ¬ 5 ∣ Fintype.card {i // δ i = δ 0} := by
    have h1 : 0 < Fintype.card {i // δ i = δ 0} := Fintype.card_pos_iff.mpr ⟨⟨0, rfl⟩⟩
    have h2 : Fintype.card {i // δ i = δ 0} < Fintype.card (Fin 5) :=
      Fintype.card_subtype_lt (p := fun i => δ i = δ 0) (x := j) hj
    rw [Fintype.card_fin] at h2
    omega
  exact TypeA.PGLTor.exists_pow_eq_of_pow_eq_scalar Nat.prime_five
    (M := (TypeA.PGLTor.conjMatrix A₀ M).toSquareBlock δ (δ 0))
    (by rw [← TypeA.PGLTor.toSquareBlock_pow_of_isBlockDiag hblock, hMp,
      TypeA.PGLTor.toSquareBlock_scalar]) hcard

theorem exists_pow_mul_pow_U5Five {k : Type} [Field k] [Finite k] {μ : kˣ}
    (hμ : ∀ c : kˣ, c ^ 5 ≠ μ) (ν : kˣ) : ∃ (j : ℕ) (c : kˣ), c ^ 5 = ν * μ ^ j := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set q : TypeA.PGLTor.PowQuot k 5 := QuotientGroup.mk μ with hq
  have hq1 : q ≠ 1 := by
    intro h
    obtain ⟨c, hc⟩ := TypeA.PGLTor.powQuot_mk_eq_one_iff.mp (hq ▸ h)
    exact hμ c hc
  have hq5 : q ^ 5 = 1 := by
    rw [hq, ← QuotientGroup.mk_pow, TypeA.PGLTor.powQuot_mk_eq_one_iff]
    exact ⟨μ, rfl⟩
  have hord : orderOf q = 5 := orderOf_eq_prime hq5 hq1
  have htop : Subgroup.zpowers q = ⊤ := by
    apply Subgroup.eq_top_of_le_card
    rw [Nat.card_zpowers, hord]
    exact TypeA.PGLTor.card_powQuot_le
  have hmem : (QuotientGroup.mk ν : TypeA.PGLTor.PowQuot k 5)⁻¹ ∈ Subgroup.zpowers q := by
    rw [htop]
    trivial
  have hfin : IsOfFinOrder q := isOfFinOrder_iff_pow_eq_one.mpr ⟨5, by norm_num, hq5⟩
  obtain ⟨j, hj⟩ := (mem_powers_iff_mem_zpowers.mpr hmem :
    (QuotientGroup.mk ν : TypeA.PGLTor.PowQuot k 5)⁻¹ ∈ Submonoid.powers q)
  have hj' : q ^ j = (QuotientGroup.mk ν : TypeA.PGLTor.PowQuot k 5)⁻¹ := hj
  refine ⟨j, ?_⟩
  rw [← TypeA.PGLTor.powQuot_mk_eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_pow, ← hq, hj',
    mul_inv_cancel]

theorem forall_le_of_central_U5Five {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {B : Subgroup G} (hB : IsElemAbelian p B) (hBcard : Nat.card B = p ^ 2)
    (S : G → Subgroup G) (hsymm : ∀ α ∈ B, ∀ β ∈ B, β ∈ S α → α ∈ S β)
    (hself : ∀ α ∈ B, α ∈ S α) {α₀ : G} (hα₀ : α₀ ∈ B) (hα₀1 : α₀ ≠ 1) (h₀ : B ≤ S α₀) :
    ∀ α ∈ B, B ≤ S α := by
  intro α hα
  by_cases hαz : α ∈ Subgroup.zpowers α₀
  · intro β hβ
    have h1 : α₀ ∈ S β := hsymm α₀ hα₀ β hβ (h₀ hβ)
    have h2 : α ∈ S β := (Subgroup.zpowers_le.mpr h1) hαz
    exact hsymm β hβ α hα h2
  · have hle : Subgroup.zpowers α₀ ⊔ Subgroup.zpowers α ≤ S α :=
      sup_le (Subgroup.zpowers_le.mpr (hsymm α₀ hα₀ α hα (h₀ hα)))
        (Subgroup.zpowers_le.mpr (hself α hα))
    have hsupB : Subgroup.zpowers α₀ ⊔ Subgroup.zpowers α ≤ B :=
      sup_le (Subgroup.zpowers_le.mpr hα₀) (Subgroup.zpowers_le.mpr hα)
    have : Fact p.Prime := ⟨hp⟩
    have hord : orderOf α₀ = p := orderOf_eq_prime (hB.2 α₀ hα₀) hα₀1
    have hcard0 : Nat.card (Subgroup.zpowers α₀) = p := by rw [Nat.card_zpowers, hord]
    have hlt : Subgroup.zpowers α₀ < Subgroup.zpowers α₀ ⊔ Subgroup.zpowers α :=
      lt_of_le_of_ne le_sup_left fun h => hαz (h ▸ Subgroup.mem_sup_right
        (Subgroup.mem_zpowers α))
    have hcardlt : p < Nat.card ↥(Subgroup.zpowers α₀ ⊔ Subgroup.zpowers α) :=
      hcard0 ▸ Subgroup.card_lt_of_lt hlt
    have hdvd : Nat.card ↥(Subgroup.zpowers α₀ ⊔ Subgroup.zpowers α) ∣ p ^ 2 :=
      hBcard ▸ Subgroup.card_dvd_of_le hsupB
    obtain ⟨i, hi, hieq⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have hi2 : i = 2 := by
      rcases Nat.lt_or_ge i 2 with h | h
      · interval_cases i
        · rw [hieq, pow_zero] at hcardlt
          exact absurd hcardlt (not_lt.mpr hp.one_lt.le)
        · rw [hieq, pow_one] at hcardlt
          exact absurd hcardlt (lt_irrefl p)
      · omega
    have heq : Subgroup.zpowers α₀ ⊔ Subgroup.zpowers α = B :=
      Subgroup.eq_of_le_of_card_ge hsupB (by rw [hBcard, hieq, hi2])
    rw [← heq]
    exact hle

section Subfield

variable {k : Type} [Field k] [Finite k] {m : ℕ}

theorem exists_root_U5Five (hk : Nat.card k = (2 ^ m) ^ 2) (h5 : 5 ∣ 2 ^ m + 1) :
    ∃ ζ : kˣ, orderOf ζ = 5 ∧ ζ ^ (2 ^ m + 1) = 1 := by
  have := Fact.mk Nat.prime_five
  have hpK : 5 ∣ Nat.card kˣ := by
    rw [Nat.card_units, hk]
    have e : (2 ^ m) ^ 2 - 1 = (2 ^ m + 1) * (2 ^ m - 1) := by
      have := Nat.sq_sub_sq (2 ^ m) 1
      rwa [one_pow] at this
    rw [e]
    exact Dvd.dvd.mul_right h5 _
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 5 hpK
  refine ⟨u, hu, ?_⟩
  obtain ⟨c, hc⟩ := h5
  rw [hc, pow_mul, ← hu, pow_orderOf_eq_one, one_pow]

theorem exists_frame_of_comm_U5Five (h : UnitaryFieldData 2 m k) (hk : Nat.card k = (2 ^ m) ^ 2)
    (h5 : 5 ∣ 2 ^ m + 1) {Ab : Subgroup (MulAut (LargeEvenProj (unitarySU 2 m k 5)))}
    (hAb : IsElemAbelian 5 Ab)
    (hAbI : ∀ α ∈ Ab, α ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 m k 5))
      (LargeEvenGUSet (Fin 5) k (2 ^ m)))
    (hcard : 25 ≤ Nat.card Ab)
    (hcomm : ∀ X Y : Subgroup.normalizer (unitarySU 2 m k 5 : Set (GL (Fin 5) k)),
      TableB.projConj (unitarySU 2 m k 5) X ∈ Ab → TableB.projConj (unitarySU 2 m k 5) Y ∈ Ab →
        (X : GL (Fin 5) k) * Y = Y * X) :
    ∃ P ∈ primeFormUnitary h (idGram k 5), ∀ α ∈ Ab, ∃ (M : GL (Fin 5) k)
      (hM : M ∈ LargeEvenGUSet (Fin 5) k (2 ^ m)),
      ((P⁻¹ * M * P : GL (Fin 5) k) : Matrix (Fin 5) (Fin 5) k).IsDiag ∧
        α = TableB.projConj (unitarySU 2 m k 5) ⟨M, TableBUE.gu_subset_normalizer h hM⟩ := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Finite (MulAut (LargeEvenProj (unitarySU 2 m k 5))) :=
    Finite.of_injective (fun φ : MulAut (LargeEvenProj (unitarySU 2 m k 5)) =>
      (φ : LargeEvenProj (unitarySU 2 m k 5) → LargeEvenProj (unitarySU 2 m k 5)))
      DFunLike.coe_injective
  have hdq : ((5 : ℕ), 2 ^ m) ≠ (3, 2) := fun he => by
    have := congrArg Prod.fst he
    simp only at this
    omega
  have hN := TableBUE.gu_subset_normalizer (d := 5) h
  set NN := Subgroup.normalizer (unitarySU 2 m k 5 : Set (GL (Fin 5) k)) with hNN
  set ρ := TableB.projConj (unitarySU 2 m k 5) with hρ
  have hscal : ∀ X : NN, ρ X = 1 → (X : GL (Fin 5) k) ∈ LargeEvenScalars (Fin 5) k :=
    fun X hX => TableBUE.mem_scalars_of_projConj_eq_one h hk (by norm_num) hdq Nat.prime_five h5 hX
  have hrep : ∀ α ∈ Ab, ∃ (M : GL (Fin 5) k) (hM : M ∈ LargeEvenGUSet (Fin 5) k (2 ^ m)),
      α = ρ ⟨M, hN hM⟩ := fun α hα => TableB.exists_eq_projConj hN (hAbI α hα)
  have hpow5 : ∀ X : NN, ρ X ∈ Ab → ∃ μ : kˣ,
      (X : GL (Fin 5) k) ^ 5 = Matrix.GeneralLinearGroup.scalar (Fin 5) μ := by
    intro X hX
    have h1 : ρ (X ^ 5) = 1 := by rw [map_pow]; exact hAb.2 _ hX
    obtain ⟨μ, hμ⟩ := hscal _ h1
    exact ⟨μ, by rw [hμ]; exact (SubmonoidClass.coe_pow X 5).symm⟩
  obtain ⟨ζ, hζ⟩ := CFSG.RankThree.PartOne.KFU.exists_isPrimitiveRoot h Nat.prime_five h5
  have hnoField : ∀ X : NN, ρ X ∈ Ab → ∃ c : kˣ,
      (X : GL (Fin 5) k) ^ 5 = Matrix.GeneralLinearGroup.scalar (Fin 5) (c ^ 5) := by
    intro X hX
    obtain ⟨μ, hμ⟩ := hpow5 X hX
    by_contra hcon
    push Not at hcon
    have hμ' : ∀ c : kˣ, c ^ 5 ≠ μ := fun c hc => hcon c (by rw [hμ, hc])
    have hX1 : ρ X ≠ 1 := by
      intro h1
      obtain ⟨c, hc⟩ := hscal X h1
      apply hμ' c
      apply TypeA.PGLTor.scalar_injective (ι := Fin 5) (K := k)
      rw [map_pow, hc]
      exact hμ
    obtain ⟨β, hβ, hβz⟩ : ∃ β ∈ Ab, β ∉ Subgroup.zpowers (ρ X) := by
      by_contra hcon'
      push Not at hcon'
      have h1 := Subgroup.card_le_of_le (show Ab ≤ Subgroup.zpowers (ρ X) from hcon')
      rw [Nat.card_zpowers, orderOf_eq_prime (hAb.2 _ hX) hX1] at h1
      omega
    obtain ⟨M₂, hM₂, rfl⟩ := hrep β hβ
    obtain ⟨μ₂, hμ₂⟩ := hpow5 ⟨M₂, hN hM₂⟩ hβ
    obtain ⟨j, c, hc⟩ := exists_pow_mul_pow_U5Five hμ' μ₂
    set Z : NN := ⟨Matrix.GeneralLinearGroup.scalar (Fin 5) c⁻¹,
      TableB.scalar_mem_normalizer _ ⟨c⁻¹, rfl⟩⟩ with hZ
    set Y : NN := Z * ⟨M₂, hN hM₂⟩ * X ^ j with hY
    have hZ1 : ρ Z = 1 := TableB.projConj_of_scalar _ ⟨c⁻¹, rfl⟩
    have hρY : ρ Y = ρ ⟨M₂, hN hM₂⟩ * ρ X ^ j := by
      rw [hY, map_mul, map_mul, hZ1, one_mul, map_pow]
    have hYAb : ρ Y ∈ Ab := hρY ▸ Ab.mul_mem hβ (Ab.pow_mem hX j)
    have hY1 : ρ Y ≠ 1 := by
      intro h1
      apply hβz
      rw [hρY] at h1
      rw [eq_inv_of_mul_eq_one_left h1]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) j)
    have hYs : (Y : GL (Fin 5) k) ∉ LargeEvenScalars (Fin 5) k := by
      intro hs
      apply hY1
      exact TableB.projConj_of_scalar _ hs
    have hXY : (X : GL (Fin 5) k) * Y = Y * X := hcomm X Y hX hYAb
    have hM₂X : M₂ * (X : GL (Fin 5) k) = X * M₂ := hcomm ⟨M₂, hN hM₂⟩ X hβ hX
    have hY5 : (Y : GL (Fin 5) k) ^ 5 = 1 := by
      have e : (Y : GL (Fin 5) k) =
          Matrix.GeneralLinearGroup.scalar (Fin 5) c⁻¹ * (M₂ * (X : GL (Fin 5) k) ^ j) := by
        rw [hY, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_pow, mul_assoc]
      have hcj : Commute M₂ ((X : GL (Fin 5) k) ^ j) := (Commute.pow_right hM₂X j)
      have hμ₂' : M₂ ^ 5 = Matrix.GeneralLinearGroup.scalar (Fin 5) μ₂ := hμ₂
      rw [e, (TypeA.PGLTor.commute_scalar c⁻¹ _).mul_pow, hcj.mul_pow, hμ₂', ← pow_mul,
        mul_comm j 5, pow_mul, hμ, ← map_pow, ← map_pow, ← map_mul, ← map_mul, inv_pow, hc,
        inv_mul_cancel, map_one]
    obtain ⟨c', hc'⟩ := exists_pow_five_of_commute_U5Five hζ hY5 hYs hXY hμ
    exact hμ' c' hc'
  have hUN : ∀ u : GL (Fin 5) k, u ∈ primeFormUnitary h (idGram k 5) → u ∈ NN :=
    fun u hu => hN (TableBUD.mem_guSet_of_mem_primeFormUnitary h hu)
  let H₁ : Subgroup (primeFormUnitary h (idGram k 5)) :=
    { carrier := {u | ρ ⟨(u : GL (Fin 5) k), hUN _ u.2⟩ ∈ Ab ∧ u ^ 5 = 1}
      mul_mem' := by
        rintro u v ⟨hu, hu5⟩ ⟨hv, hv5⟩
        have huv : Commute u v := Subtype.ext (hcomm _ _ hu hv)
        refine ⟨?_, by rw [huv.mul_pow, hu5, hv5, one_mul]⟩
        have e : (⟨((u * v : primeFormUnitary h (idGram k 5)) : GL (Fin 5) k),
            hUN _ (u * v).2⟩ : NN) = ⟨(u : GL (Fin 5) k), hUN _ u.2⟩ *
              ⟨(v : GL (Fin 5) k), hUN _ v.2⟩ := rfl
        rw [e, map_mul]
        exact Ab.mul_mem hu hv
      one_mem' := by
        refine ⟨?_, one_pow 5⟩
        have e : (⟨((1 : primeFormUnitary h (idGram k 5)) : GL (Fin 5) k),
            hUN _ (1 : primeFormUnitary h (idGram k 5)).2⟩ : NN) = 1 := rfl
        rw [e, map_one]
        exact Ab.one_mem
      inv_mem' := by
        rintro u ⟨hu, hu5⟩
        refine ⟨?_, by rw [inv_pow, hu5, inv_one]⟩
        have e : (⟨((u⁻¹ : primeFormUnitary h (idGram k 5)) : GL (Fin 5) k),
            hUN _ u⁻¹.2⟩ : NN) = (⟨(u : GL (Fin 5) k), hUN _ u.2⟩ : NN)⁻¹ := rfl
        rw [e, map_inv]
        exact Ab.inv_mem hu }
  obtain ⟨P, hP⟩ := CFSG.RankThree.PartOne.KFU.exists_unitary_conj_diag h Nat.prime_five h5 H₁
    (fun x hx y hy => Subtype.ext (hcomm _ _ hx.1 hy.1)) (fun x hx => hx.2)
  refine ⟨(P : GL (Fin 5) k), P.2, fun α hα => ?_⟩
  obtain ⟨M, hM, rfl⟩ := hrep α hα
  obtain ⟨c, hc⟩ := hnoField ⟨M, hN hM⟩ hα
  have hc' : M ^ 5 = Matrix.GeneralLinearGroup.scalar (Fin 5) (c ^ 5) := hc
  set u : GL (Fin 5) k := Matrix.GeneralLinearGroup.scalar (Fin 5) c⁻¹ * M with hu
  have hu5 : u ^ 5 = 1 := by
    rw [hu, (TypeA.PGLTor.commute_scalar c⁻¹ M).mul_pow, ← map_pow, hc', ← map_mul, inv_pow,
      inv_mul_cancel, map_one]
  have huU : u ∈ primeFormUnitary h (idGram k 5) :=
    TableBUD.mem_primeFormUnitary_of_pow_eq_one h h5 (by norm_num) hM (c := ((c⁻¹ : kˣ) : k))
      (by rw [hu, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar,
        TableBUD.scalar_mul_eq_smul]) hu5
  have huρ : ρ ⟨u, hUN u huU⟩ = ρ ⟨M, hN hM⟩ := by
    have e : (⟨u, hUN u huU⟩ : NN) = ⟨Matrix.GeneralLinearGroup.scalar (Fin 5) c⁻¹,
        TableB.scalar_mem_normalizer _ ⟨c⁻¹, rfl⟩⟩ * ⟨M, hN hM⟩ := rfl
    rw [e, map_mul, TableB.projConj_of_scalar _ ⟨c⁻¹, rfl⟩, one_mul]
  have huH : (⟨u, huU⟩ : primeFormUnitary h (idGram k 5)) ∈ H₁ :=
    ⟨by rw [show (⟨((⟨u, huU⟩ : primeFormUnitary h (idGram k 5)) : GL (Fin 5) k), _⟩ : NN) =
        ⟨u, hUN u huU⟩ from rfl, huρ]; exact hα,
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hu5)⟩
  have hd := hP _ huH
  refine ⟨M, hM, ?_, rfl⟩
  have e : ((P⁻¹ * ⟨u, huU⟩ * P : primeFormUnitary h (idGram k 5)) : GL (Fin 5) k) =
      (P : GL (Fin 5) k)⁻¹ * u * P := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [e] at hd
  have hM' : (P : GL (Fin 5) k)⁻¹ * M * P =
      Matrix.GeneralLinearGroup.scalar (Fin 5) c * ((P : GL (Fin 5) k)⁻¹ * u * P) := by
    calc (P : GL (Fin 5) k)⁻¹ * M * P
        = (P : GL (Fin 5) k)⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 5) c *
            (Matrix.GeneralLinearGroup.scalar (Fin 5) c⁻¹ * M)) * P := by
          rw [← mul_assoc (Matrix.GeneralLinearGroup.scalar (Fin 5) c), ← map_mul,
            mul_inv_cancel, map_one, one_mul]
      _ = Matrix.GeneralLinearGroup.scalar (Fin 5) c * ((P : GL (Fin 5) k)⁻¹ * u * P) := by
          rw [hu, ← mul_assoc ((P : GL (Fin 5) k)⁻¹),
            ← TypeA.PGLTor.scalar_mul_comm c ((P : GL (Fin 5) k)⁻¹)]
          simp only [mul_assoc]
  rw [hM', Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, TableBUD.scalar_mul_eq_smul]
  exact hd.smul _

theorem card_ge_of_frame_U5Five (h : UnitaryFieldData 2 m k) (hk : Nat.card k = (2 ^ m) ^ 2)
    (h5 : 5 ∣ 2 ^ m + 1) (hcov : LineU.UnitaryCoverAt m 5 k)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* LargeEvenProj (unitarySU 2 m k 5)}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')}
    (hAI : ∀ a ∈ A, ∃ x ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 m k 5))
        (LargeEvenGUSet (Fin 5) k (2 ^ m)), ∀ l : L', x (ψ l) = ψ (a l))
    (hsc : GGTorusSelfCent 5 A) {P : GL (Fin 5) k} (hP : P ∈ primeFormUnitary h (idGram k 5))
    (hframe : ∀ a ∈ TypeA.inducedSub ψ A, ∃ (M : GL (Fin 5) k)
      (hM : M ∈ LargeEvenGUSet (Fin 5) k (2 ^ m)),
      ((P⁻¹ * M * P : GL (Fin 5) k) : Matrix (Fin 5) (Fin 5) k).IsDiag ∧
        a = TableB.projConj (unitarySU 2 m k 5) ⟨M, TableBUE.gu_subset_normalizer h hM⟩) :
    125 ≤ Nat.card A := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨φ, -, hφker, hdiag⟩ :=
    exists_diagModel_of_frame_U5Five h hcov hψ hker hperf hAI hP hframe
  obtain ⟨ζ, hζord, -⟩ := exists_root_U5Five hk h5
  have hζ5 : (ζ : k) ^ 5 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hζord, pow_orderOf_eq_one, Units.val_one]
  have hζprim : IsPrimitiveRoot (ζ : k) 5 :=
    IsPrimitiveRoot.coe_units_iff.mpr (hζord ▸ IsPrimitiveRoot.orderOf ζ)
  have hζ0 : (ζ : k) ≠ 0 := ζ.ne_zero
  set uvec : Fin 5 × Fin 5 × Fin 5 → Fin 5 → k := fun v =>
    ![(ζ : k) ^ (v.1 : ℕ), (ζ : k) ^ (v.2.1 : ℕ), (ζ : k) ^ (v.2.2 : ℕ), 1,
      ((ζ : k) ^ ((v.1 : ℕ) + (v.2.1 : ℕ) + (v.2.2 : ℕ)))⁻¹] with huvec
  have hroot : ∀ e : ℕ, ((ζ : k) ^ e) ^ 5 = 1 := fun e => by
    rw [← pow_mul, mul_comm, pow_mul, hζ5, one_pow]
  have hu5 : ∀ v i, uvec v i ^ 5 = 1 := by
    intro v i
    fin_cases i <;> simp [huvec, hroot, inv_pow]
  have hunorm : ∀ v i, uvec v i ^ (2 ^ m + 1) = 1 := by
    intro v i
    obtain ⟨c, hc⟩ := h5
    rw [hc, pow_mul, hu5, one_pow]
  have hprod : ∀ v, ∏ i, uvec v i = 1 := by
    intro v
    simp [huvec, Fin.prod_univ_five, pow_add]
    field_simp
  choose D hD using fun v => LineU.exists_diagSU h (hunorm v) (hprod v)
  have hmem : ∀ v, MulAut.conj (φ (D v)) ∈ A := fun v =>
    LineU.conj_mem_of_selfCent_U hsc hdiag (hD v) (hu5 v)
  let F : Fin 5 × Fin 5 × Fin 5 → A := fun v => ⟨MulAut.conj (φ (D v)), hmem v⟩
  have hF : Function.Injective F := by
    intro v w hvw
    have h1 : MulAut.conj (φ (D v)) = MulAut.conj (φ (D w)) := congrArg Subtype.val hvw
    set g := (D v)⁻¹ * D w with hg
    have hgy : ∀ y, φ (g * y * g⁻¹) = φ y := by
      intro y
      have h2 := DFunLike.congr_fun h1 (φ y)
      simp only [MulAut.conj_apply] at h2
      rw [hg, map_mul, map_mul, map_inv, map_mul, map_inv]
      calc (φ (D v))⁻¹ * φ (D w) * φ y * ((φ (D v))⁻¹ * φ (D w))⁻¹
          = (φ (D v))⁻¹ * (φ (D w) * φ y * (φ (D w))⁻¹) * φ (D v) := by group
        _ = (φ (D v))⁻¹ * (φ (D v) * φ y * (φ (D v))⁻¹) * φ (D v) := by rw [h2]
        _ = φ y := by group
    obtain ⟨c, hc⟩ := LineU.exists_scalar_of_map_conj_eq_U h (by norm_num) hφker hgy
    have hgmat : ((g : GL (Fin 5) k) : Matrix (Fin 5) (Fin 5) k) =
        diagonal (fun i => (uvec v i)⁻¹ * uvec w i) := by
      rw [hg, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul,
        LineU.coe_inv_diag (hD v), hD w, diagonal_mul_diagonal]
    have hent : ∀ i, (uvec v i)⁻¹ * uvec w i = c := by
      intro i
      have h3 := congrFun (congrFun (hgmat.symm.trans hc) i) i
      simpa using h3
    have hc1 : c = 1 := by
      have h3 := hent 3
      simp [huvec] at h3
      exact h3.symm
    have hcoord : ∀ i, uvec w i = uvec v i := by
      intro i
      have h3 := hent i
      rw [hc1] at h3
      have hv0 : uvec v i ≠ 0 := fun h0 => by
        have := hu5 v i
        rw [h0, zero_pow (by norm_num)] at this
        exact zero_ne_one this
      calc uvec w i = uvec v i * ((uvec v i)⁻¹ * uvec w i) := by
            rw [← mul_assoc, mul_inv_cancel₀ hv0, one_mul]
        _ = uvec v i := by rw [h3, mul_one]
    have hinj : ∀ a b : Fin 5, (ζ : k) ^ (a : ℕ) = (ζ : k) ^ (b : ℕ) → a = b := fun a b hab =>
      Fin.ext (hζprim.pow_inj a.isLt b.isLt hab)
    have e0 := hcoord 0
    have e1 := hcoord 1
    have e2 := hcoord 2
    simp only [huvec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons] at e0 e1 e2
    exact Prod.ext (hinj _ _ e0.symm) (Prod.ext (hinj _ _ e1.symm) (hinj _ _ e2.symm))
  have hcardF := Nat.card_le_card_of_injective F hF
  simpa [Nat.card_eq_fintype_card] using hcardF

theorem false_of_comm_U5Five (h : UnitaryFieldData 2 m k) (hk : Nat.card k = (2 ^ m) ^ 2)
    (h5 : 5 ∣ 2 ^ m + 1) (hcov : LineU.UnitaryCoverAt m 5 k)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* LargeEvenProj (unitarySU 2 m k 5)}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian 5 A)
    (hAI : ∀ a ∈ A, ∃ x ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 m k 5))
        (LargeEvenGUSet (Fin 5) k (2 ^ m)), ∀ l : L', x (ψ l) = ψ (a l))
    (h25 : 25 ≤ Nat.card A) (h125 : Nat.card A < 125) (hsc : GGTorusSelfCent 5 A)
    (hcomm : ∀ X Y : Subgroup.normalizer (unitarySU 2 m k 5 : Set (GL (Fin 5) k)),
      TableB.projConj (unitarySU 2 m k 5) X ∈ TypeA.inducedSub ψ A →
        TableB.projConj (unitarySU 2 m k 5) Y ∈ TypeA.inducedSub ψ A →
          (X : GL (Fin 5) k) * Y = Y * X) : False := by
  have hAb := TypeA.isElemAbelian_inducedSub hψ hA
  have hcardAb : Nat.card (TypeA.inducedSub ψ A) = Nat.card A :=
    TypeA.card_inducedSub hψ hker hperf fun a ha => by
      obtain ⟨x, -, hx⟩ := hAI a ha
      exact ⟨x, hx⟩
  have hAbI : ∀ α ∈ TypeA.inducedSub ψ A, α ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (unitarySU 2 m k 5)) (LargeEvenGUSet (Fin 5) k (2 ^ m)) := by
    intro x hx
    obtain ⟨a, ha, hxa⟩ := TypeA.mem_inducedSub.mp hx
    obtain ⟨y, hy, hya⟩ := hAI a ha
    rw [TypeA.induced_unique ψ hψ hxa hya]
    exact hy
  obtain ⟨P, hP, hframe⟩ :=
    exists_frame_of_comm_U5Five h hk h5 hAb hAbI (hcardAb ▸ h25) hcomm
  have := card_ge_of_frame_U5Five h hk h5 hcov hψ hker hperf hAI hsc hP hframe
  omega

@[expose] def ggRegSetU5Five (k : Type) [Field k] (m : ℕ) :
    Set (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 5) k (2 ^ m)))) :=
  LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 5) k (2 ^ m)))
    {M | M ∈ LargeEvenGUSet (Fin 5) k (2 ^ m) ∧ IsHeisRegU5Five M}

theorem exists_reg_of_heis_U5Five (h : UnitaryFieldData 2 m k) (hk : Nat.card k = (2 ^ m) ^ 2)
    (h5 : 5 ∣ 2 ^ m + 1) (hcov : LineU.UnitaryCoverAt m 5 k)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* LargeEvenProj (unitarySU 2 m k 5)}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian 5 A)
    (hAI : ∀ a ∈ A, ∃ x ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 m k 5))
        (LargeEvenGUSet (Fin 5) k (2 ^ m)), ∀ l : L', x (ψ l) = ψ (a l))
    (h25 : 25 ≤ Nat.card A) (h125 : Nat.card A < 125) (hsc : GGTorusSelfCent 5 A)
    {a₀ : MulAut L'} (ha₀ : a₀ ∈ A) (hne : a₀ ≠ 1) :
    ∃ φ ∈ ggRegSetU5Five k m, ∀ l : L', φ (ψ l) = ψ (a₀ l) := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Finite (MulAut (LargeEvenProj (unitarySU 2 m k 5))) :=
    Finite.of_injective (fun φ : MulAut (LargeEvenProj (unitarySU 2 m k 5)) =>
      (φ : LargeEvenProj (unitarySU 2 m k 5) → LargeEvenProj (unitarySU 2 m k 5)))
      DFunLike.coe_injective
  haveI : Finite (MulAut L') :=
    Finite.of_injective (fun φ : MulAut L' => (φ : L' → L')) DFunLike.coe_injective
  have hdq : ((5 : ℕ), 2 ^ m) ≠ (3, 2) := fun he => by
    have := congrArg Prod.fst he
    simp only at this
    omega
  have hN := TableBUE.gu_subset_normalizer (d := 5) h
  set NN := Subgroup.normalizer (unitarySU 2 m k 5 : Set (GL (Fin 5) k)) with hNN
  set ρ := TableB.projConj (unitarySU 2 m k 5) with hρ
  set Ab := TypeA.inducedSub ψ A with hAbdef
  have hAb : IsElemAbelian 5 Ab := TypeA.isElemAbelian_inducedSub hψ hA
  have hcardAb : Nat.card Ab = Nat.card A :=
    TypeA.card_inducedSub hψ hker hperf fun a ha => by
      obtain ⟨x, -, hx⟩ := hAI a ha
      exact ⟨x, hx⟩
  have hAbI : ∀ α ∈ Ab, α ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (unitarySU 2 m k 5)) (LargeEvenGUSet (Fin 5) k (2 ^ m)) := by
    intro x hx
    obtain ⟨a, ha, hxa⟩ := TypeA.mem_inducedSub.mp hx
    obtain ⟨y, hy, hya⟩ := hAI a ha
    rw [TypeA.induced_unique ψ hψ hxa hya]
    exact hy
  have hscal : ∀ X : NN, ρ X = 1 → (X : GL (Fin 5) k) ∈ LargeEvenScalars (Fin 5) k :=
    fun X hX => TableBUE.mem_scalars_of_projConj_eq_one h hk (by norm_num) hdq Nat.prime_five h5 hX
  have hrep : ∀ α ∈ Ab, ∃ (M : GL (Fin 5) k) (hM : M ∈ LargeEvenGUSet (Fin 5) k (2 ^ m)),
      α = ρ ⟨M, hN hM⟩ := fun α hα => TableB.exists_eq_projConj hN (hAbI α hα)
  have hcard25 : Nat.card Ab = 5 ^ 2 := by
    have hpg : IsPGroup 5 A := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hA.2 _ g.2)⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hpg
    rw [hcardAb, hn]
    rw [hn] at h25 h125
    have h1 : 2 ≤ n := by
      by_contra hlt
      have h3 : 5 ^ n ≤ 5 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [pow_one] at h3
      omega
    have h2 : n < 3 := by
      by_contra hlt
      have h3 : 5 ^ 3 ≤ 5 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at h3
      omega
    have : n = 2 := by omega
    rw [this]
  have hdecomp : ∀ X Y : NN, ρ X = ρ Y →
      ∃ u : kˣ, (X : GL (Fin 5) k) = Matrix.GeneralLinearGroup.scalar (Fin 5) u * Y := by
    intro X Y hXY
    have h1 : ρ (X * Y⁻¹) = 1 := by rw [map_mul, map_inv, hXY, mul_inv_cancel]
    obtain ⟨u, hu⟩ := hscal _ h1
    refine ⟨u, ?_⟩
    have hu' : Matrix.GeneralLinearGroup.scalar (Fin 5) u =
        (X : GL (Fin 5) k) * (Y : GL (Fin 5) k)⁻¹ := hu
    rw [hu', inv_mul_cancel_right]
  have hcs : ∀ (X W : GL (Fin 5) k) (u : kˣ), X * W = W * X →
      X * (Matrix.GeneralLinearGroup.scalar (Fin 5) u * W) =
        (Matrix.GeneralLinearGroup.scalar (Fin 5) u * W) * X := by
    intro X W u hXW
    rw [← mul_assoc, ← TypeA.PGLTor.scalar_mul_comm u X, mul_assoc, hXW, ← mul_assoc]
  let S : MulAut (LargeEvenProj (unitarySU 2 m k 5)) →
      Subgroup (MulAut (LargeEvenProj (unitarySU 2 m k 5))) := fun α =>
    { carrier := {β | β ∈ Ab ∧ ∀ X Y : NN, ρ X = α → ρ Y = β →
        (X : GL (Fin 5) k) * Y = Y * X}
      mul_mem' := by
        rintro β₁ β₂ ⟨hβ₁, h₁⟩ ⟨hβ₂, h₂⟩
        refine ⟨Ab.mul_mem hβ₁ hβ₂, fun X Y hX hY => ?_⟩
        obtain ⟨M₁, hM₁, e₁⟩ := hrep β₁ hβ₁
        obtain ⟨M₂, hM₂, e₂⟩ := hrep β₂ hβ₂
        have hX₁ := h₁ X ⟨M₁, hN hM₁⟩ hX e₁.symm
        have hX₂ := h₂ X ⟨M₂, hN hM₂⟩ hX e₂.symm
        obtain ⟨u, hu⟩ := hdecomp Y (⟨M₁, hN hM₁⟩ * ⟨M₂, hN hM₂⟩)
          (by rw [hY, map_mul, ← e₁, ← e₂])
        rw [hu]
        refine hcs _ _ u ?_
        change (X : GL (Fin 5) k) * (M₁ * M₂) = (M₁ * M₂) * X
        rw [← mul_assoc, hX₁, mul_assoc, hX₂, mul_assoc]
      one_mem' := by
        refine ⟨Ab.one_mem, fun X Y _ hY => ?_⟩
        obtain ⟨u, hu⟩ := hscal Y hY
        rw [← hu]
        exact (TypeA.PGLTor.scalar_mul_comm u (X : GL (Fin 5) k)).symm
      inv_mem' := by
        rintro β ⟨hβ, h₁⟩
        refine ⟨Ab.inv_mem hβ, fun X Y hX hY => ?_⟩
        obtain ⟨M₁, hM₁, e₁⟩ := hrep β hβ
        have hX₁ := h₁ X ⟨M₁, hN hM₁⟩ hX e₁.symm
        obtain ⟨u, hu⟩ := hdecomp Y (⟨M₁, hN hM₁⟩ : NN)⁻¹ (by rw [hY, map_inv, ← e₁])
        rw [hu]
        refine hcs _ _ u ?_
        change (X : GL (Fin 5) k) * M₁⁻¹ = M₁⁻¹ * X
        exact (Commute.inv_right (hX₁ : Commute (X : GL (Fin 5) k) M₁)).eq }
  have hsymm : ∀ α ∈ Ab, ∀ β ∈ Ab, β ∈ S α → α ∈ S β :=
    fun α hα β _ hαβ => ⟨hα, fun X Y hX hY => (hαβ.2 Y X hY hX).symm⟩
  have hself : ∀ α ∈ Ab, α ∈ S α := by
    intro α hα
    refine ⟨hα, fun X Y hX hY => ?_⟩
    obtain ⟨u, hu⟩ := hdecomp Y X (hY.trans hX.symm)
    rw [hu]
    exact hcs _ _ u rfl
  obtain ⟨α₀, -, hα₀⟩ := hAI a₀ ha₀
  have hα₀Ab : α₀ ∈ Ab := TypeA.mem_inducedSub.mpr ⟨a₀, ha₀, hα₀⟩
  have hα₀1 : α₀ ≠ 1 := by
    intro h1
    apply hne
    apply TypeA.mulAut_eq_of_forall ψ hker hperf
    intro l
    rw [← hα₀ l, h1]
    rfl
  have hex : ∃ X Y : NN, ρ X = α₀ ∧ ρ Y ∈ Ab ∧ (X : GL (Fin 5) k) * Y ≠ Y * X := by
    by_contra hcon
    push Not at hcon
    have h₀ : Ab ≤ S α₀ := fun β hβ => ⟨hβ, fun X Y hX hY => hcon X Y hX (hY ▸ hβ)⟩
    have hall := forall_le_of_central_U5Five Nat.prime_five hAb hcard25 S hsymm hself hα₀Ab
      hα₀1 h₀
    exact false_of_comm_U5Five h hk h5 hcov hψ hker hperf hA hAI h25 h125 hsc
      fun X Y hX hY => ((hall _ hX) hY).2 X Y rfl rfl
  obtain ⟨X, Y, hX, hYAb, hXY⟩ := hex
  obtain ⟨M₀, hM₀, hα₀eq⟩ := hrep α₀ hα₀Ab
  obtain ⟨u, hu⟩ := hdecomp X ⟨M₀, hN hM₀⟩ (hX.trans hα₀eq)
  have hM₀Y : M₀ * (Y : GL (Fin 5) k) ≠ Y * M₀ := by
    intro hc
    apply hXY
    rw [hu]
    exact (hcs _ _ u hc.symm).symm
  have hρc : ρ (⟨M₀, hN hM₀⟩ * Y * (⟨M₀, hN hM₀⟩ : NN)⁻¹ * Y⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hα₀eq,
      TableB.IsElemAbelian.comm hAb hα₀Ab hYAb]
    group
  obtain ⟨w, hw⟩ := hscal _ hρc
  have hw' : Matrix.GeneralLinearGroup.scalar (Fin 5) w =
      M₀ * (Y : GL (Fin 5) k) * M₀⁻¹ * (Y : GL (Fin 5) k)⁻¹ := hw
  have hrel : M₀ * (Y : GL (Fin 5) k) =
      Matrix.GeneralLinearGroup.scalar (Fin 5) w * ((Y : GL (Fin 5) k) * M₀) := by
    rw [hw']
    group
  have hw1 : w ≠ 1 := by
    intro h1
    apply hM₀Y
    rw [hrel, h1, map_one, one_mul]
  have hρ5 : ρ (⟨M₀, hN hM₀⟩ ^ 5) = 1 := by
    rw [map_pow, ← hα₀eq]
    exact hAb.2 _ hα₀Ab
  obtain ⟨μ, hμ⟩ := hscal _ hρ5
  have hμ' : M₀ ^ 5 = Matrix.GeneralLinearGroup.scalar (Fin 5) μ := by
    rw [hμ]
    exact (SubmonoidClass.coe_pow (⟨M₀, hN hM₀⟩ : NN) 5).symm
  have hw5 : w ^ 5 = 1 := by
    have hrel' : (Y : GL (Fin 5) k) * M₀ =
        Matrix.GeneralLinearGroup.scalar (Fin 5) w⁻¹ * (M₀ * Y) := by
      rw [hrel, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
    have h1 := TypeA.PGLTor.mul_pow_eq_of_mul_eq (TypeA.PGLTor.commute_scalar w⁻¹ M₀) hrel' 5
    rw [hμ', ← TypeA.PGLTor.scalar_mul_comm μ] at h1
    have h2 : (Matrix.GeneralLinearGroup.scalar (Fin 5) w⁻¹) ^ 5 = 1 := by
      have h3 : 1 * (Matrix.GeneralLinearGroup.scalar (Fin 5) μ * (Y : GL (Fin 5) k)) =
          (Matrix.GeneralLinearGroup.scalar (Fin 5) w⁻¹) ^ 5 *
            (Matrix.GeneralLinearGroup.scalar (Fin 5) μ * Y) := by rw [one_mul]; exact h1
      exact (mul_right_cancel h3).symm
    rw [← map_pow, ← map_one (Matrix.GeneralLinearGroup.scalar (Fin 5))] at h2
    have h4 := TypeA.PGLTor.scalar_injective (ι := Fin 5) (K := k) h2
    rw [inv_pow] at h4
    exact inv_eq_one.mp h4
  have hreg : IsHeisRegU5Five M₀ := by
    refine ⟨⟨μ, hμ'.symm⟩, (Y : GL (Fin 5) k), (w : k), ?_, ?_, ?_⟩
    · intro h1
      exact hw1 (Units.val_eq_one.mp h1)
    · rw [← Units.val_pow_eq_pow_val, hw5, Units.val_one]
    · have h1 := congrArg (fun Z : GL (Fin 5) k => (Z : Matrix (Fin 5) (Fin 5) k)) hrel
      simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar] at h1
      rw [h1, TableBUD.scalar_mul_eq_smul]
  refine ⟨α₀, ⟨M₀, ⟨hM₀, hreg⟩, fun g g' hgg' => ?_⟩, hα₀⟩
  rw [hα₀eq]
  have e : ((unitarySU 2 m k 5).normalizerMonoidHom ⟨M₀, hN hM₀⟩ g :
      ↥(unitarySU 2 m k 5)) = g' := Subtype.ext hgg'.symm
  exact congrArg (LargeEvenProjMk (unitarySU 2 m k 5)) e

end Subfield

section Statement

theorem ggTorusNoLineTwoKX_u5Five {k : Type} [Field k] [Finite k] {m : ℕ}
    (hk : Nat.card k = (2 ^ m) ^ 2) (hm : 1 ≤ m) (h5 : 5 ∣ 2 ^ m + 1) :
    GGTorusNoLineTwoKX 5 (fun j => j ∣ 5) (LargeEvenProj (LargeEvenSUGroup (Fin 5) k (2 ^ m)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 5) k (2 ^ m)))
        (LargeEvenGUSet (Fin 5) k (2 ^ m)))
      (ggRegSetU5Five k m) := by
  intro L' _ _ ψ hψ hker hperf _ A hA hAI h25 hsc
  have h := TableBU.unitaryFieldData_of_card hk hm
  by_cases h125 : 5 ^ 3 ≤ Nat.card A
  · have hline := LineU.noInvariantLineSCr_unitary LineU.unitaryUniversalCover hk hm (d := 5)
      (by norm_num) Nat.prime_five h5 (dvd_refl 5) (by omega)
    have hrk : ggUnitaryTorusRank 5 5 = 2 := by decide
    rw [hrk] at hline
    obtain ⟨W, hW1, hW2⟩ := ggTorusNoLine_of_noInvariantLineSCr Nat.prime_five hline L' ψ hψ hker
      hperf A hA hAI h25 h125 hsc
    exact ⟨W, hW1, fun hN a₀ ha₀ hne => Or.inr (hW2 hN a₀ ha₀ hne)⟩
  · have hcov : LineU.UnitaryCoverAt m 5 k := LineU.unitaryCoverAt hk (by norm_num)
      (fun he => absurd (congrArg Prod.fst he) (by norm_num))
    refine ⟨∅, fun n hn => absurd hn (Set.notMem_empty n), fun _ a₀ ha₀ hne => Or.inl ?_⟩
    exact exists_reg_of_heis_U5Five h hk h5 hcov hψ hker hperf hA hAI (by simpa using h25)
      (by omega) hsc ha₀ hne

end Statement

end CFSG.StandardType

end

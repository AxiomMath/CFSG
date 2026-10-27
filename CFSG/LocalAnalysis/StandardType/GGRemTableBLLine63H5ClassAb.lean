module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5ClassPg
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5FieldBound

public section

namespace CFSG.StandardType.Line63.H5

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.SectionRank.OddCover CFSG.StandardType.LineU CFSG.Assembly CFSG.StandardType
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel

variable {K : Type} [Field K] {n : ℕ}

@[expose] noncomputable def abOf (n : ℕ) {K : Type} [Field K] (MB : Subgroup (GL (Fin 6) K)) :
    Subgroup (MulAut (LargeEvenProj (unitarySU 2 n K 6))) :=
  (MB.subgroupOf (Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))).map
    (TableB.projConj (unitarySU 2 n K 6))

theorem mem_abOf {MB : Subgroup (GL (Fin 6) K)}
    {a : MulAut (LargeEvenProj (unitarySU 2 n K 6))} :
    a ∈ abOf n MB ↔ ∃ (M : GL (Fin 6) K)
      (hM : M ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))), M ∈ MB ∧
        a = TableB.projConj (unitarySU 2 n K 6) ⟨M, hM⟩ := by
  constructor
  · rintro ⟨⟨M, hM⟩, hMB, rfl⟩
    exact ⟨M, hM, hMB, rfl⟩
  · rintro ⟨M, hM, hMB, rfl⟩
    exact ⟨⟨M, hM⟩, hMB, rfl⟩

theorem exists_scalar_mul_of_projConj_eq [Finite K] (hKd : UnitaryFieldData 2 n K)
    (hpq : 3 ∣ 2 ^ n + 1) {M M' : GL (Fin 6) K}
    (hM : M ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    (hM' : M' ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    (h : TableB.projConj (unitarySU 2 n K 6) ⟨M, hM⟩ =
      TableB.projConj (unitarySU 2 n K 6) ⟨M', hM'⟩) :
    ∃ c : Kˣ, M = GeneralLinearGroup.scalar (Fin 6) c * M' := by
  have hK : Nat.card K = (2 ^ n) ^ 2 := by rw [hKd.card, ← pow_mul, mul_comm]
  have hdq : ((6 : ℕ), 2 ^ n) ≠ (3, 2) := fun he => by
    have := congrArg Prod.fst he
    simp only at this
    omega
  have h1 : TableB.projConj (unitarySU 2 n K 6)
      ((⟨M, hM⟩ : Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) *
        (⟨M', hM'⟩ : Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  have h2 := TableBUE.mem_scalars_of_projConj_eq_one hKd hK (by norm_num) hdq Nat.prime_three hpq
    h1
  rw [largeEvenScalars_def] at h2
  obtain ⟨c, hc⟩ := h2
  refine ⟨c, ?_⟩
  have h3 : (M * M'⁻¹ : GL (Fin 6) K) = GeneralLinearGroup.scalar (Fin 6) c := hc.symm
  rw [← h3]
  group

theorem projConj_comm_of_commutator_scalar {M₁ M₂ : GL (Fin 6) K}
    (h₁ : M₁ ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    (h₂ : M₂ ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) {k : Kˣ}
    (hk : M₁ * M₂ * M₁⁻¹ * M₂⁻¹ = GeneralLinearGroup.scalar (Fin 6) k) :
    TableB.projConj (unitarySU 2 n K 6) ⟨M₁, h₁⟩ *
        TableB.projConj (unitarySU 2 n K 6) ⟨M₂, h₂⟩ =
      TableB.projConj (unitarySU 2 n K 6) ⟨M₂, h₂⟩ *
        TableB.projConj (unitarySU 2 n K 6) ⟨M₁, h₁⟩ := by
  have e : (⟨M₁, h₁⟩ * ⟨M₂, h₂⟩ :
      Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) =
      ⟨GeneralLinearGroup.scalar (Fin 6) k, TableB.scalar_mem_normalizer _ ⟨k, rfl⟩⟩ *
        (⟨M₂, h₂⟩ * ⟨M₁, h₁⟩) := by
    apply Subtype.ext
    show M₁ * M₂ = GeneralLinearGroup.scalar (Fin 6) k * (M₂ * M₁)
    rw [← hk]
    group
  rw [← map_mul, ← map_mul, e, map_mul, TableB.projConj_of_scalar _ ⟨k, rfl⟩, one_mul]

theorem isElemAbelian_abOf {MB : Subgroup (GL (Fin 6) K)} (hMB : ActGroup n MB) :
    CFSG.Open.IsElemAbelian 3 (abOf n MB) := by
  refine ⟨⟨⟨?_⟩⟩, ?_⟩
  · rintro ⟨_, M₁, h₁, rfl⟩ ⟨_, M₂, h₂, rfl⟩
    apply Subtype.ext
    obtain ⟨k, hk⟩ := hMB.commutator M₁ h₁ M₂ h₂
    exact projConj_comm_of_commutator_scalar (hMB.mem_normalizer M₁ h₁)
      (hMB.mem_normalizer M₂ h₂) hk
  · rintro _ ⟨⟨M, hM⟩, hMB', rfl⟩
    obtain ⟨k, hk⟩ := hMB.pow_three M hMB'
    rw [← map_pow]
    have e : (⟨M, hM⟩ : Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) ^ 3 =
        ⟨GeneralLinearGroup.scalar (Fin 6) k, TableB.scalar_mem_normalizer _ ⟨k, rfl⟩⟩ :=
      Subtype.ext hk
    rw [e]
    exact TableB.projConj_of_scalar _ ⟨k, rfl⟩

theorem abOf_mem_matConjImage {MB : Subgroup (GL (Fin 6) K)} (hMB : ActGroup n MB)
    {a : MulAut (LargeEvenProj (unitarySU 2 n K 6))} (ha : a ∈ abOf n MB) :
    a ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K 6))
      (LargeEvenGUSet (Fin 6) K (2 ^ n)) := by
  obtain ⟨M, hM, hMB', rfl⟩ := mem_abOf.mp ha
  refine ⟨M, hMB.mem_gu M hMB', fun h h' hrel => ?_⟩
  have e : h' = (unitarySU 2 n K 6).normalizerMonoidHom ⟨M, hM⟩ h := Subtype.ext hrel
  rw [e]
  exact TableB.projConj_mk _ _ _

theorem card_abOf [Finite K] (hKd : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1)
    {MB : Subgroup (GL (Fin 6) K)} (hMB : ActGroup n MB) : 3 ^ 3 ≤ Nat.card (abOf n MB) := by
  have hK : Nat.card K = (2 ^ n) ^ 2 := by rw [hKd.card, ← pow_mul, mul_comm]
  have hdq : ((6 : ℕ), 2 ^ n) ≠ (3, 2) := fun he => by
    have := congrArg Prod.fst he
    simp only at this
    omega
  set NSU := Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) with hNSU
  set N₀ : Subgroup NSU := MB.subgroupOf NSU with hN₀
  set g : N₀ →* MulAut (LargeEvenProj (unitarySU 2 n K 6)) :=
    (TableB.projConj (unitarySU 2 n K 6)).comp N₀.subtype with hg
  have hrange : g.range = abOf n MB := by
    rw [hg, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have hN₀card : Nat.card N₀ = Nat.card MB :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe fun M hM => hMB.mem_normalizer M hM).toEquiv
  have hsc : ∀ y : g.ker, ∃ u : Kˣ,
      GeneralLinearGroup.scalar (Fin 6) u = (((y : N₀) : NSU) : GL (Fin 6) K) := by
    intro y
    have h1 : TableB.projConj (unitarySU 2 n K 6) ((y : N₀) : NSU) = 1 := y.2
    exact TableBUE.mem_scalars_of_projConj_eq_one hKd hK (by norm_num) hdq Nat.prime_three
      hpq h1
  choose fu hfu using hsc
  have hker : Nat.card g.ker ≤ Nat.card Kˣ := by
    refine Nat.card_le_card_of_injective fu fun a b hab => ?_
    exact Subtype.ext (Subtype.ext (Subtype.ext (by rw [← hfu, ← hfu, hab])))
  have h1 := Subgroup.card_ker_mul_card_range g
  rw [hrange, hN₀card] at h1
  have hKpos : 0 < Nat.card Kˣ := Nat.card_pos
  have h2 : Nat.card Kˣ * 27 ≤ Nat.card Kˣ * Nat.card (abOf n MB) := by
    calc Nat.card Kˣ * 27 = 27 * Nat.card Kˣ := mul_comm _ _
      _ ≤ Nat.card MB := hMB.card
      _ = Nat.card g.ker * Nat.card (abOf n MB) := h1.symm
      _ ≤ Nat.card Kˣ * Nat.card (abOf n MB) := Nat.mul_le_mul_right _ hker
  have h3 := Nat.le_of_mul_le_mul_left h2 hKpos
  simpa using h3

theorem isDiag_conj_scalar_mul {P M : GL (Fin 6) K} (c : Kˣ)
    (hD : ((P⁻¹ * M * P : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag) :
    ((P⁻¹ * (GeneralLinearGroup.scalar (Fin 6) c * M) * P : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K).IsDiag := by
  have e : P⁻¹ * (GeneralLinearGroup.scalar (Fin 6) c * M) * P =
      GeneralLinearGroup.scalar (Fin 6) c * (P⁻¹ * M * P) := by
    have h : P⁻¹ * GeneralLinearGroup.scalar (Fin 6) c =
        GeneralLinearGroup.scalar (Fin 6) c * P⁻¹ :=
      (commute_scalar c P⁻¹).eq
    calc P⁻¹ * (GeneralLinearGroup.scalar (Fin 6) c * M) * P
        = (P⁻¹ * GeneralLinearGroup.scalar (Fin 6) c) * (M * P) := by group
      _ = (GeneralLinearGroup.scalar (Fin 6) c * P⁻¹) * (M * P) := by rw [h]
      _ = GeneralLinearGroup.scalar (Fin 6) c * (P⁻¹ * M * P) := by group
  rw [e, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    ← Matrix.smul_eq_diagonal_mul]
  exact hD.smul _

theorem noFrame_abOf [Finite K] (hKd : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1)
    {MB : Subgroup (GL (Fin 6) K)} (hMB : ActGroup n MB)
    (hnofr : ¬ ∃ P ∈ primeFormUnitary hKd (idGram K 6), ∀ M ∈ MB,
      ((P⁻¹ * M * P : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag) :
    ¬ ∃ P ∈ primeFormUnitary hKd (idGram K 6), ∀ a ∈ abOf n MB,
      ∃ (M : GL (Fin 6) K) (hM : M ∈ LargeEvenGUSet (Fin 6) K (2 ^ n)),
      ((P⁻¹ * M * P : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag ∧
        a = TableB.projConj (unitarySU 2 n K 6) ⟨M, TableBUE.gu_subset_normalizer hKd hM⟩ := by
  rintro ⟨P, hP, hPd⟩
  apply hnofr
  refine ⟨P, hP, fun M hM => ?_⟩
  have hMN := hMB.mem_normalizer M hM
  obtain ⟨M', hM'gu, hdiag, heq⟩ := hPd (TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩)
    (mem_abOf.mpr ⟨M, hMN, hM, rfl⟩)
  obtain ⟨c, hc⟩ := exists_scalar_mul_of_projConj_eq hKd hpq hMN
    (TableBUE.gu_subset_normalizer hKd hM'gu) heq
  rw [hc]
  exact isDiag_conj_scalar_mul c hdiag

theorem exists_noncomm_of_fieldType [Finite K] (hKd : UnitaryFieldData 2 n K)
    (hpq : 3 ∣ 2 ^ n + 1) {MB : Subgroup (GL (Fin 6) K)} (hMB : ActGroup n MB)
    {M : GL (Fin 6) K} (hM : M ∈ MB) {l : Kˣ}
    (hM3 : M ^ 3 = GeneralLinearGroup.scalar (Fin 6) l) (hl : ∀ c : Kˣ, c ^ 3 ≠ l) :
    ∃ M₁ ∈ MB, ∃ M₂ ∈ MB, M₁ * M₂ ≠ M₂ * M₁ := by
  by_contra hcon
  push Not at hcon
  have hω : ∃ ω : Kˣ, ω ^ 3 = 1 ∧ ω ≠ 1 := by
    obtain ⟨h3, -⟩ := card_units_dvd_odd hKd hpq
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' 3 h3
    refine ⟨ω, by rw [← hω]; exact pow_orderOf_eq_one ω, fun h1 => ?_⟩
    rw [h1, orderOf_one] at hω
    omega
  have h9 := card_le_nine_of_fieldType hω hM3 hl hM hcon hMB.scalar_mem hMB.pow_three
  have h27 := hMB.card
  have hKpos : 0 < Nat.card Kˣ := Nat.card_pos
  omega

theorem not_commute_of_heis {M₁ M₂ : GL (Fin 6) K} {ζ : Kˣ} (hζ : ζ ≠ 1)
    (h : M₁ * M₂ = GeneralLinearGroup.scalar (Fin 6) ζ * (M₂ * M₁)) : M₁ * M₂ ≠ M₂ * M₁ := by
  intro hc
  rw [hc] at h
  apply hζ
  have h' : (1 : GL (Fin 6) K) * (M₂ * M₁) = GeneralLinearGroup.scalar (Fin 6) ζ * (M₂ * M₁) := by
    rw [one_mul]
    exact h
  exact scalar_six_injective (by rw [map_one]; exact (mul_right_cancel h').symm)

theorem exists_noncomm_of_heis [Finite K] (hKd : UnitaryFieldData 2 n K)
    (hpq : 3 ∣ 2 ^ n + 1) {MB : Subgroup (GL (Fin 6) K)} (hMB : ActGroup n MB)
    {x y : GL (Fin 6) K}
    (hxN : x ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    (hyN : y ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) {ζ : Kˣ}
    (hxA : TableB.projConj (unitarySU 2 n K 6) ⟨x, hxN⟩ ∈ abOf n MB)
    (hyA : TableB.projConj (unitarySU 2 n K 6) ⟨y, hyN⟩ ∈ abOf n MB) (hζ : ζ ≠ 1)
    (hxy : x * y = GeneralLinearGroup.scalar (Fin 6) ζ * (y * x)) :
    ∃ M₁ ∈ MB, ∃ M₂ ∈ MB, M₁ * M₂ ≠ M₂ * M₁ := by
  obtain ⟨x', hx'N, hx'MB, hx'eq⟩ := mem_abOf.mp hxA
  obtain ⟨y', hy'N, hy'MB, hy'eq⟩ := mem_abOf.mp hyA
  obtain ⟨c₁, hc₁⟩ := exists_scalar_mul_of_projConj_eq hKd hpq hx'N hxN hx'eq.symm
  obtain ⟨c₂, hc₂⟩ := exists_scalar_mul_of_projConj_eq hKd hpq hy'N hyN hy'eq.symm
  refine ⟨x', hx'MB, y', hy'MB, not_commute_of_heis hζ ?_⟩
  rw [hc₁, hc₂]
  have e1 : GeneralLinearGroup.scalar (Fin 6) c₁ * x * (GeneralLinearGroup.scalar (Fin 6) c₂ * y) =
      GeneralLinearGroup.scalar (Fin 6) c₁ * GeneralLinearGroup.scalar (Fin 6) c₂ * (x * y) :=
    (commute_scalar c₂ x).mul_mul_mul_comm _ _
  have e2 : GeneralLinearGroup.scalar (Fin 6) c₂ * y * (GeneralLinearGroup.scalar (Fin 6) c₁ * x) =
      GeneralLinearGroup.scalar (Fin 6) c₂ * GeneralLinearGroup.scalar (Fin 6) c₁ * (y * x) :=
    (commute_scalar c₁ y).mul_mul_mul_comm _ _
  have hab : c₁ * c₂ * ζ = ζ * (c₂ * c₁) := by rw [mul_comm c₁ c₂, mul_comm]
  calc GeneralLinearGroup.scalar (Fin 6) c₁ * x * (GeneralLinearGroup.scalar (Fin 6) c₂ * y)
      = GeneralLinearGroup.scalar (Fin 6) c₁ * GeneralLinearGroup.scalar (Fin 6) c₂ * (x * y) :=
        e1
    _ = GeneralLinearGroup.scalar (Fin 6) c₁ * GeneralLinearGroup.scalar (Fin 6) c₂ *
          (GeneralLinearGroup.scalar (Fin 6) ζ * (y * x)) := by rw [hxy]
    _ = GeneralLinearGroup.scalar (Fin 6) (c₁ * c₂ * ζ) * (y * x) := by
        simp only [map_mul, mul_assoc]
    _ = GeneralLinearGroup.scalar (Fin 6) (ζ * (c₂ * c₁)) * (y * x) := by rw [hab]
    _ = GeneralLinearGroup.scalar (Fin 6) ζ *
          (GeneralLinearGroup.scalar (Fin 6) c₂ * GeneralLinearGroup.scalar (Fin 6) c₁ *
            (y * x)) := by simp only [map_mul, mul_assoc]
    _ = GeneralLinearGroup.scalar (Fin 6) ζ *
          (GeneralLinearGroup.scalar (Fin 6) c₂ * y *
            (GeneralLinearGroup.scalar (Fin 6) c₁ * x)) := by rw [e2]

theorem exists_noncomm_of_noFrame [Finite K] (hKd : UnitaryFieldData 2 n K)
    (hpq : 3 ∣ 2 ^ n + 1) {MB : Subgroup (GL (Fin 6) K)} (hMB : ActGroup n MB)
    (hnofr : ¬ ∃ P ∈ primeFormUnitary hKd (idGram K 6), ∀ M ∈ MB,
      ((P⁻¹ * M * P : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag) :
    ∃ M₁ ∈ MB, ∃ M₂ ∈ MB, M₁ * M₂ ≠ M₂ * M₁ := by
  have hK : Nat.card K = (2 ^ n) ^ 2 := by rw [hKd.card, ← pow_mul, mul_comm]
  rcases TableBU63.fieldType_or_heis hKd hK hpq (isElemAbelian_abOf hMB)
    (fun a ha => abOf_mem_matConjImage hMB ha) (card_abOf hKd hpq hMB)
    (noFrame_abOf hKd hpq hMB hnofr) with
    ⟨M, hMN, l, -, hM3, hl, hMA⟩ |
      ⟨x, y, z, hxN, hyN, hzN, ζ, -, -, -, hxA, hyA, -, -, -, -, hζ1, hxy, -, -, -⟩
  · obtain ⟨M', hM'N, hM'MB, heq⟩ := mem_abOf.mp hMA
    obtain ⟨c, hc⟩ := exists_scalar_mul_of_projConj_eq hKd hpq hM'N hMN heq.symm
    refine exists_noncomm_of_fieldType hKd hpq hMB hM'MB (l := c ^ 3 * l) ?_ ?_
    · rw [hc, TableBU63.scalar_mul_pow, hM3, ← map_mul]
    · intro d hd
      apply hl (d * c⁻¹)
      rw [mul_pow, inv_pow, hd, mul_comm (c ^ 3) l, mul_assoc, mul_inv_cancel, mul_one]
  · exact exists_noncomm_of_heis hKd hpq hMB hxN hyN hxA hyA hζ1 hxy

end CFSG.StandardType.Line63.H5

end

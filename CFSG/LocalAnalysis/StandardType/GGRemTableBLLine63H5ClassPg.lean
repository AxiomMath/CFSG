module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5Inner

public section

namespace CFSG.StandardType.Line63.H5

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.SectionRank.OddCover CFSG.StandardType.LineU CFSG.Assembly

variable {K : Type} [Field K] {n : ℕ}

section ActsAs

variable {G : Type} [Group G] {φ : ↥(unitarySU 2 n K 6) →* G}

theorem conjN_mul {D D' : GL (Fin 6) K}
    (hD : D ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    (hD' : D' ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    (hDD' : D * D' ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    (s : ↥(unitarySU 2 n K 6)) : conjN (D * D') hDD' s = conjN D hD (conjN D' hD' s) :=
  Subtype.ext (by simp only [coe_conjN, _root_.mul_inv_rev, mul_assoc])

variable (φ) in
theorem actsAs_one : ActsAs φ 1 (1 : GL (Fin 6) K) := by
  refine ⟨Subgroup.one_mem _, fun s => ?_⟩
  have e : conjN (1 : GL (Fin 6) K) (Subgroup.one_mem _) s = s :=
    Subtype.ext (by rw [coe_conjN]; simp)
  rw [e]
  group

theorem ActsAs.mul {b b' : G} {M M' : GL (Fin 6) K} (h : ActsAs φ b M) (h' : ActsAs φ b' M') :
    ActsAs φ (b * b') (M * M') := by
  obtain ⟨hM, ha⟩ := h
  obtain ⟨hM', ha'⟩ := h'
  have hMM' := Subgroup.mul_mem _ hM hM'
  refine ⟨hMM', fun s => ?_⟩
  rw [conjN_mul hM hM' hMM', ← ha, ← ha']
  group

theorem ActsAs.inv {b : G} {M : GL (Fin 6) K} (h : ActsAs φ b M) : ActsAs φ b⁻¹ M⁻¹ := by
  obtain ⟨hM, ha⟩ := h
  have hMi := Subgroup.inv_mem _ hM
  refine ⟨hMi, fun s => ?_⟩
  have e : conjN M hM (conjN M⁻¹ hMi s) = s :=
    Subtype.ext (by simp only [coe_conjN, _root_.mul_inv_rev, _root_.inv_inv]; group)
  have h1 := ha (conjN M⁻¹ hMi s)
  rw [e] at h1
  rw [← h1]
  group

theorem ActsAs.pow {b : G} {M : GL (Fin 6) K} (h : ActsAs φ b M) (k : ℕ) :
    ActsAs φ (b ^ k) (M ^ k) := by
  induction k with
  | zero => simpa using actsAs_one φ
  | succ k ih => simpa only [pow_succ] using ih.mul h

variable (φ) in
theorem actsAs_scalar (k : Kˣ) : ActsAs φ 1 (GeneralLinearGroup.scalar (Fin 6) k) := by
  have hM : (GeneralLinearGroup.scalar (Fin 6) k : GL (Fin 6) K) ∈
      Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) :=
    CFSG.StandardType.TableB.scalar_mem_normalizer _ ⟨k, rfl⟩
  refine ⟨hM, fun s => ?_⟩
  have e : conjN (GeneralLinearGroup.scalar (Fin 6) k : GL (Fin 6) K) hM s = s := by
    apply Subtype.ext
    rw [coe_conjN, ← (commute_scalar k (s : GL (Fin 6) K)).eq, mul_assoc, mul_inv_cancel,
      mul_one]
  rw [e]
  group

theorem ActsAs.exists_scalar_of_one (hKd : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1)
    (hφ : Function.Injective φ) {M : GL (Fin 6) K} (h : ActsAs φ 1 M) :
    ∃ k : Kˣ, M = GeneralLinearGroup.scalar (Fin 6) k := by
  obtain ⟨hM, ha⟩ := h
  have hcomm : ∀ g ∈ unitarySU 2 n K 6, M * g = g * M := by
    intro g hg
    have h1 := ha ⟨g, hg⟩
    rw [one_mul, inv_one, mul_one] at h1
    have h2 : conjN M hM ⟨g, hg⟩ = ⟨g, hg⟩ := (hφ h1).symm
    have h3 := congrArg Subtype.val h2
    rw [coe_conjN] at h3
    calc M * g = M * g * M⁻¹ * M := by group
      _ = g * M := by rw [h3]
  have hs := TableBUE.mem_scalars_of_commute hKd Nat.prime_three hpq hcomm
  rw [largeEvenScalars_def] at hs
  obtain ⟨k, hk⟩ := hs
  exact ⟨k, hk.symm⟩

theorem ActsAs.exists_scalar_mul (hKd : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1)
    (hφ : Function.Injective φ) {b : G} {M M' : GL (Fin 6) K} (h : ActsAs φ b M)
    (h' : ActsAs φ b M') : ∃ k : Kˣ, M = GeneralLinearGroup.scalar (Fin 6) k * M' := by
  have h1 : ActsAs φ (b * b⁻¹) (M * M'⁻¹) := h.mul h'.inv
  rw [mul_inv_cancel] at h1
  obtain ⟨k, hk⟩ := h1.exists_scalar_of_one hKd hpq hφ
  exact ⟨k, by rw [← hk]; group⟩

end ActsAs

theorem scalar_six_injective :
    Function.Injective (GeneralLinearGroup.scalar (Fin 6) : Kˣ →* GL (Fin 6) K) := by
  intro c c' h
  have h1 : Matrix.scalar (Fin 6) (c : K) = Matrix.scalar (Fin 6) (c' : K) := by
    have := congrArg Units.val h
    simpa only [GeneralLinearGroup.coe_scalar] using this
  exact Units.ext (Matrix.scalar_inj.mp h1)

theorem scalar_mul_mem_gu [Finite K] (hKd : UnitaryFieldData 2 n K) (t : Kˣ) {M : GL (Fin 6) K}
    (hM : M ∈ LargeEvenGUSet (Fin 6) K (2 ^ n)) :
    GeneralLinearGroup.scalar (Fin 6) t * M ∈ LargeEvenGUSet (Fin 6) K (2 ^ n) := by
  obtain ⟨μ, hμ0, hμq, hμ⟩ := hM
  haveI := Fintype.ofFinite K
  have hK : Fintype.card K = (2 ^ n) ^ 2 := by
    rw [← Nat.card_eq_fintype_card, hKd.card, ← pow_mul, mul_comm]
  have hKq : (t : K) ^ (2 ^ n) ^ 2 = t := by
    have := FiniteField.pow_card (t : K)
    rwa [hK] at this
  refine ⟨(t : K) ^ (2 ^ n + 1) * μ, mul_ne_zero (pow_ne_zero _ t.ne_zero) hμ0, ?_, ?_⟩
  · rw [mul_pow, ← pow_mul, hμq]
    congr 1
    calc (t : K) ^ ((2 ^ n + 1) * 2 ^ n) = (t : K) ^ ((2 ^ n) ^ 2) * (t : K) ^ 2 ^ n := by
          rw [← pow_add]
          congr 1
          ring
      _ = (t : K) ^ (2 ^ n + 1) := by rw [hKq, pow_succ, mul_comm]
  · have e : ((GeneralLinearGroup.scalar (Fin 6) t * M : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) = (t : K) • (M : Matrix (Fin 6) (Fin 6) K) := by
      rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        ← Matrix.smul_eq_diagonal_mul]
    rw [e]
    have hmap : ((t : K) • (M : Matrix (Fin 6) (Fin 6) K)).map (· ^ 2 ^ n) =
        ((t : K) ^ 2 ^ n) • (M : Matrix (Fin 6) (Fin 6) K).map (· ^ 2 ^ n) := by
      ext i j
      simp [mul_pow]
    rw [hmap, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hμ, smul_smul, smul_smul]
    congr 1
    rw [pow_succ]

section Centralizer

variable {G : Type} [Group G]

theorem mem_zpowers_of_mem_centralizer {H : Type*} [Group H] [Finite G] {ψ : H →* G}
    (hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer ((ψ.range : Subgroup G) : Set G) →
      IsPGroup 3 S → IsCyclic S)
    {B : Subgroup G} (hB : CFSG.Open.IsElemAbelian 3 B) {x b : G} (hxB : x ∈ B) (hbB : b ∈ B)
    (hx1 : x ≠ 1) (hxC : x ∈ Subgroup.centralizer ((ψ.range : Subgroup G) : Set G))
    (hbC : b ∈ Subgroup.centralizer ((ψ.range : Subgroup G) : Set G)) :
    b ∈ Subgroup.zpowers x := by
  have hx3 : x ^ 3 = 1 := hB.2 x hxB
  have hb3 : b ^ 3 = 1 := hB.2 b hbB
  have hxb : Commute x b := CFSG.StandardType.TableB.IsElemAbelian.comm hB hxB hbB
  set S : Subgroup G := Subgroup.zpowers x ⊔ Subgroup.zpowers b with hS
  have hSab : CFSG.Open.IsElemAbelian 3 S :=
    CFSG.StandardType.TableB.isElemAbelian_sup (isElemAbelian_zpowers hx3)
      (isElemAbelian_zpowers hb3) (fun a ha c hc => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
        exact ((hxb.zpow_left i).zpow_right j).eq)
  have hSp : IsPGroup 3 S := fun g => ⟨1, Subtype.ext (by simpa using hSab.2 g g.2)⟩
  have hSle : S ≤ Subgroup.centralizer ((ψ.range : Subgroup G) : Set G) :=
    sup_le ((Subgroup.zpowers_le).mpr hxC) ((Subgroup.zpowers_le).mpr hbC)
  have hSc : IsCyclic S := hcyc S hSle hSp
  exact mem_zpowers_of_isCyclic_of_pow_three hSc
    (le_sup_left (a := Subgroup.zpowers x) (b := Subgroup.zpowers b) (Subgroup.mem_zpowers x))
    (le_sup_right (a := Subgroup.zpowers x) (b := Subgroup.zpowers b) (Subgroup.mem_zpowers b))
    hx3 hx1 hb3

end Centralizer

structure ActGroup (n : ℕ) {K : Type} [Field K] (MB : Subgroup (GL (Fin 6) K)) : Prop where
  mem_normalizer : ∀ M ∈ MB, M ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))
  scalar_mem : ∀ c : Kˣ, GeneralLinearGroup.scalar (Fin 6) c ∈ MB
  mem_gu : ∀ M ∈ MB, M ∈ LargeEvenGUSet (Fin 6) K (2 ^ n)
  pow_three : ∀ M ∈ MB, ∃ k : Kˣ, M ^ 3 = GeneralLinearGroup.scalar (Fin 6) k
  commutator : ∀ M₁ ∈ MB, ∀ M₂ ∈ MB,
    ∃ k : Kˣ, M₁ * M₂ * M₁⁻¹ * M₂⁻¹ = GeneralLinearGroup.scalar (Fin 6) k
  card : 27 * Nat.card Kˣ ≤ Nat.card MB

section Pairs

variable {G : Type} [Group G]

@[expose] def actPairs (φ : ↥(unitarySU 2 n K 6) →* G) (B : Subgroup G) :
    Subgroup (G × GL (Fin 6) K) where
  carrier := {p | p.1 ∈ B ∧ ActsAs φ p.1 p.2}
  mul_mem' := fun {_ _} hp hq => ⟨B.mul_mem hp.1 hq.1, hp.2.mul hq.2⟩
  one_mem' := ⟨B.one_mem, actsAs_one φ⟩
  inv_mem' := fun {_} hp => ⟨B.inv_mem hp.1, hp.2.inv⟩

theorem exists_actGroup [Finite K] [Finite G] (hKd : UnitaryFieldData 2 n K)
    (hpq : 3 ∣ 2 ^ n + 1) (φ : ↥(unitarySU 2 n K 6) →* G) (hφ : Function.Injective φ)
    {B : Subgroup G} (hB : CFSG.Open.IsElemAbelian 3 B) (hBcard : Nat.card B = 3 ^ 4)
    (hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer ((φ.range : Subgroup G) : Set G) →
      IsPGroup 3 S → IsCyclic S)
    {x : G} (hxB : x ∈ B) (hx1 : x ≠ 1) (hxC : ∀ s, x * φ s = φ s * x)
    (hact : ∀ b ∈ B, ∃ M, M ∈ LargeEvenGUSet (Fin 6) K (2 ^ n) ∧ ActsAs φ b M) :
    ∃ MB : Subgroup (GL (Fin 6) K), (∀ b ∈ B, ∀ M, ActsAs φ b M → M ∈ MB) ∧
      (∀ M ∈ MB, ∃ b ∈ B, ActsAs φ b M) ∧ ActGroup n MB := by
  classical
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Pg := actPairs φ B with hPg
  set p₁ : Pg →* G := (MonoidHom.fst G (GL (Fin 6) K)).comp Pg.subtype with hp₁
  set p₂ : Pg →* GL (Fin 6) K := (MonoidHom.snd G (GL (Fin 6) K)).comp Pg.subtype with hp₂
  have hmem : ∀ M, M ∈ p₂.range ↔ ∃ b ∈ B, ActsAs φ b M := by
    intro M
    constructor
    · rintro ⟨⟨⟨b, M'⟩, hb, ha⟩, rfl⟩
      exact ⟨b, hb, ha⟩
    · rintro ⟨b, hb, ha⟩
      exact ⟨⟨(b, M), hb, ha⟩, rfl⟩
  have hker1 : Nat.card Kˣ ≤ Nat.card p₁.ker := by
    refine Nat.card_le_card_of_injective
      (fun k : Kˣ => (⟨⟨(1, GeneralLinearGroup.scalar (Fin 6) k), B.one_mem, actsAs_scalar φ k⟩,
        rfl⟩ : p₁.ker)) fun k k' hkk => ?_
    exact scalar_six_injective (congrArg (fun z : p₁.ker => (z.1.1).2) hkk)
  have hrange1 : 3 ^ 4 ≤ Nat.card p₁.range := by
    rw [← hBcard]
    refine Subgroup.card_le_of_le fun b hb => ?_
    obtain ⟨M, -, hM⟩ := hact b hb
    exact ⟨⟨(b, M), hb, hM⟩, rfl⟩
  have hker2 : Nat.card p₂.ker ≤ 3 := by
    have hxC' : x ∈ Subgroup.centralizer ((φ.range : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨s, rfl⟩
      exact (hxC s).symm
    have hzp : ∀ y : p₂.ker, ((y.1 : G × GL (Fin 6) K).1) ∈ Subgroup.zpowers x := by
      intro y
      obtain ⟨⟨⟨b, M⟩, hb, ha⟩, hy⟩ := y
      have hM1 : M = 1 := hy
      subst hM1
      obtain ⟨hMN, hact1⟩ := ha
      refine mem_zpowers_of_mem_centralizer hcyc hB hxB hb hx1 hxC' ?_
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨s, rfl⟩
      have h1 := hact1 s
      have e : conjN (1 : GL (Fin 6) K) hMN s = s := Subtype.ext (by rw [coe_conjN]; simp)
      rw [e] at h1
      calc φ s * b = b * φ s * b⁻¹ * b := by rw [h1]
        _ = b * φ s := by group
    have hinj : Function.Injective
        (fun y : p₂.ker => (⟨(y.1 : G × GL (Fin 6) K).1, hzp y⟩ : Subgroup.zpowers x)) := by
      intro y y' hyy
      have h1 : (y.1 : G × GL (Fin 6) K).1 = (y'.1 : G × GL (Fin 6) K).1 :=
        congrArg Subtype.val hyy
      have h2 : (y.1 : G × GL (Fin 6) K).2 = (y'.1 : G × GL (Fin 6) K).2 := by
        rw [show (y.1 : G × GL (Fin 6) K).2 = 1 from y.2,
          show (y'.1 : G × GL (Fin 6) K).2 = 1 from y'.2]
      exact Subtype.ext (Subtype.ext (Prod.ext h1 h2))
    have h3 : Nat.card (Subgroup.zpowers x) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime (hB.2 x hxB) hx1]
    calc Nat.card p₂.ker ≤ Nat.card (Subgroup.zpowers x) := Nat.card_le_card_of_injective _ hinj
      _ = 3 := h3
  have h1 := Subgroup.card_ker_mul_card_range p₁
  have h2 := Subgroup.card_ker_mul_card_range p₂
  have hKpos : 0 < Nat.card Kˣ := Nat.card_pos
  have hPg81 : 81 * Nat.card Kˣ ≤ Nat.card Pg := by
    rw [← h1]
    calc 81 * Nat.card Kˣ = Nat.card Kˣ * 81 := mul_comm _ _
      _ ≤ Nat.card p₁.ker * Nat.card p₁.range := Nat.mul_le_mul hker1 (by simpa using hrange1)
  have hcard : 27 * Nat.card Kˣ ≤ Nat.card p₂.range := by
    have h4 : 3 * (27 * Nat.card Kˣ) ≤ 3 * Nat.card p₂.range := by
      calc 3 * (27 * Nat.card Kˣ) = 81 * Nat.card Kˣ := by ring
        _ ≤ Nat.card Pg := hPg81
        _ = Nat.card p₂.ker * Nat.card p₂.range := h2.symm
        _ ≤ 3 * Nat.card p₂.range := Nat.mul_le_mul_right _ hker2
    exact Nat.le_of_mul_le_mul_left h4 (by norm_num)
  refine ⟨p₂.range, fun b hb M hM => (hmem M).mpr ⟨b, hb, hM⟩, fun M hM => (hmem M).mp hM, ?_⟩
  refine ⟨fun M hM => ?_, fun c => (hmem _).mpr ⟨1, B.one_mem, actsAs_scalar φ c⟩, fun M hM => ?_,
    fun M hM => ?_, fun M₁ h₁ M₂ h₂ => ?_, hcard⟩
  · obtain ⟨b, -, hMa⟩ := (hmem M).mp hM
    exact hMa.1
  · obtain ⟨b, hb, hMa⟩ := (hmem M).mp hM
    obtain ⟨M', hM'gu, hM'a⟩ := hact b hb
    obtain ⟨k, hk⟩ := hMa.exists_scalar_mul hKd hpq hφ hM'a
    rw [hk]
    exact scalar_mul_mem_gu hKd k hM'gu
  · obtain ⟨b, hb, hMa⟩ := (hmem M).mp hM
    have h3 := hMa.pow 3
    rw [hB.2 b hb] at h3
    obtain ⟨k, hk⟩ := h3.exists_scalar_of_one hKd hpq hφ
    exact ⟨k, hk⟩
  · obtain ⟨b₁, hb₁, ha₁⟩ := (hmem M₁).mp h₁
    obtain ⟨b₂, hb₂, ha₂⟩ := (hmem M₂).mp h₂
    have h3 := ((ha₁.mul ha₂).mul ha₁.inv).mul ha₂.inv
    have hb : b₁ * b₂ * b₁⁻¹ * b₂⁻¹ = 1 := by
      have hc : b₁ * b₂ = b₂ * b₁ := CFSG.StandardType.TableB.IsElemAbelian.comm hB hb₁ hb₂
      rw [hc]
      group
    rw [hb] at h3
    obtain ⟨k, hk⟩ := h3.exists_scalar_of_one hKd hpq hφ
    exact ⟨k, hk⟩

end Pairs

end CFSG.StandardType.Line63.H5

end

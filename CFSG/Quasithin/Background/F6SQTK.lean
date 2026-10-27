module

public import CFSG.Quasithin.Background.F6Faithful
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.Open.SQTKSimpleListTauCeti
public import CFSG.Quasithin.Background.A1bPGroups
public import CFSG.Quasithin.Background.F6Solvable

public section

universe u

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits CFSG.QuasithinUnique Matrix

namespace F6

@[expose] def F613Two : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (G₁ G₂ X : Subgroup D), IsGoldschmidtTriple G₁ G₂ →
    Open.pCore 2 D = ⊥ → X.Normal → twoResidual G₁ ≤ X → ¬ twoResidual G₂ ≤ X →
      Nonempty (↥(twoResidual G₁) ≃* Multiplicative (ZMod 3))

section F613

variable {D : Type u} [Group D] [Finite D] {G₁ G₂ X : Subgroup D}

theorem card_twoResidual_eq_three_of_F613Two (hF : F613Two.{u}) (h : IsGoldschmidtTriple G₁ G₂)
    (hQ : Open.pCore 2 D = ⊥) [hX : X.Normal] (hL₁ : twoResidual G₁ ≤ X)
    (hL₂ : ¬ twoResidual G₂ ≤ X) : Nat.card ↥(twoResidual G₁) = 3 := by
  obtain ⟨e⟩ := hF D G₁ G₂ X h hQ hX hL₁ hL₂
  rw [Nat.card_congr e.toEquiv]
  simp

theorem f6_13_three_of_F613Two (hF : F613Two.{u}) (h : IsGoldschmidtTriple G₁ G₂)
    (hQ : Open.pCore 2 D = ⊥) [X.Normal] (hL₁ : twoResidual G₁ ≤ X)
    (hL₂ : ¬ twoResidual G₂ ≤ X) :
    (IsElemAbelian 2 (pCoreOf 2 G₂) ∧ Nat.card ↥(pCoreOf 2 G₂) ≤ 2 ^ 3) ∧
      (twoResidual G₁ ≤ Subgroup.normalizer (pCoreOf 2 G₂ : Set D) → pCoreOf 2 G₂ = ⊥) ∧
      (pCoreOf 2 G₂ ⊔ twoResidual G₁ ≤
          Subgroup.normalizer (pCoreOf 2 (twoResidual G₂) : Set D) →
        pCoreOf 2 (twoResidual G₂) = ⊥) :=
  f6_13_three h hQ (card_twoResidual_eq_three_of_F613Two hF h hQ hL₁ hL₂)

end F613

section Remark

theorem pPrimeCore_quotient_pPrimeCore (p : ℕ) [Fact p.Prime] {X : Type*} [Group X] [Finite X] :
    CFSG.pPrimeCore p (X ⧸ CFSG.pPrimeCore p X) = ⊥ := by
  set N := CFSG.pPrimeCore p X
  rw [CFSG.pPrimeCore_eq_bot_iff]
  intro K hK hKc
  have hY : (K.comap (QuotientGroup.mk' N)).Normal := hK.comap _
  have hNY : N ≤ K.comap (QuotientGroup.mk' N) := by
    intro x hx
    rw [Subgroup.mem_comap]
    have : (QuotientGroup.mk' N) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [this]
    exact K.one_mem
  have hmap : (K.comap (QuotientGroup.mk' N)).map (QuotientGroup.mk' N) = K :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) K
  have hcard : Nat.card ↥(K.comap (QuotientGroup.mk' N)) = Nat.card ↥K * Nat.card ↥N := by
    have h1 := Subgroup.relIndex_mul_card (H := N) (K := K.comap (QuotientGroup.mk' N))
    rw [inf_eq_left.mpr hNY, ← card_map_mk, hmap] at h1
    exact h1.symm
  have hcop : Nat.Coprime p (Nat.card ↥(K.comap (QuotientGroup.mk' N))) := by
    rw [hcard]
    exact Nat.Coprime.mul_right hKc (CFSG.pPrimeCore_coprime_card (p := p) (G := X))
  have hle : K.comap (QuotientGroup.mk' N) ≤ N := le_pPrimeCore_of_normal hcop
  rw [eq_bot_iff, ← hmap, ← QuotientGroup.map_mk'_self N]
  exact Subgroup.map_mono hle

theorem remark_f6_15 {D X : Type*} [Group D] [Group X] [Finite X]
    (e : D ≃* X ⧸ CFSG.pPrimeCore 3 X) :
    CFSG.pPrimeCore 3 D = ⊥ ∧ Open.pCore 2 D = ⊥ := by
  have : Finite D := Finite.of_equiv _ e.symm.toEquiv
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : CFSG.pPrimeCore 3 D = ⊥ := by
    have hmap := CFSG.pPrimeCore_map_iso 3 e
    rw [pPrimeCore_quotient_pPrimeCore] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hmap
  exact ⟨h3, le_bot_iff.mp (h3 ▸ pCore_le_pPrimeCore)⟩

theorem remark_f6_15_isGoldCase (hlist : GoldschmidtS3List.{u}) {D : Type u} [Group D]
    [Finite D] {X : Type*} [Group X] [Finite X] {G₁ G₂ : Subgroup D}
    (h : IsGoldschmidtTriple G₁ G₂) (e : D ≃* X ⧸ CFSG.pPrimeCore 3 X) :
    IsGoldschmidtAmalgam G₁ G₂ ∧ IsGoldCase G₁ G₂ := by
  have hA : IsGoldschmidtAmalgam G₁ G₂ := ⟨h, (remark_f6_15 e).2⟩
  exact ⟨hA, hlist D G₁ G₂ hA⟩

end Remark

@[expose] def IsL2 (p e : ℕ) (W : Type) [Group W] : Prop :=
  StatedClassicalModel W .PSL 2 p e

@[expose] def IsPGL2 (q : ℕ) (W : Type) [Group W] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q ∧
    Nonempty (W ≃* GL (Fin 2) K ⧸ StatedScalars (Fin 2) K)

@[expose] def IsHatAlt (n : ℕ) (W : Type*) [Group W] : Prop :=
  CFSG.Open.IsQuasisimple W ∧ Nat.card ↥(Subgroup.center W) = 3 ∧
    Nonempty (W ⧸ Subgroup.center W ≃* ↥(alternatingGroup (Fin n)))

@[expose] def IsHatSym (n : ℕ) (W : Type*) [Group W] : Prop :=
  ∃ φ : W →* Equiv.Perm (Fin n), Function.Surjective φ ∧ Nat.card ↥φ.ker = 3 ∧
    IsHatAlt n ↥((alternatingGroup (Fin n)).comap φ)

@[expose] def IsExtendedByMatrixMap {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (H Z₀ : Subgroup (GL ι K)) [(Z₀.subgroupOf H).Normal] (α : Matrix ι ι K → Matrix ι ι K)
    (W : Type*) [Group W] : Prop :=
  ∃ (N : Subgroup W) (e : ↥N ≃* ↥H ⧸ Z₀.subgroupOf H) (t : W) (g : ↥H), N.index = 2 ∧ t ∉ N ∧
    ∀ (n m : ↥N) (A B : ↥H), (m : W) = t * n * t⁻¹ →
      e n = (QuotientGroup.mk A : ↥H ⧸ Z₀.subgroupOf H) →
      ((B : GL ι K) : Matrix ι ι K) = ((g : GL ι K) : Matrix ι ι K) *
          α ((A : GL ι K) : Matrix ι ι K) * (((g : GL ι K)⁻¹ : GL ι K) : Matrix ι ι K) →
      e m = (QuotientGroup.mk B : ↥H ⧸ Z₀.subgroupOf H)

@[expose] def IsL2FieldExt (p : ℕ) (W : Type) [Group W] : Prop :=
  p.Prime ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ 2 ∧
    IsExtendedByMatrixMap (StatedSL 2 K) (StatedScalars (Fin 2) K) (fun A => A.map (· ^ p)) W

@[expose] def IsSLEps3 (p : ℕ) (W : Type) [Group W] : Prop :=
  p.Prime ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K),
    (p % 4 = 1 ∧ Nat.card K = p ∧
      (Nonempty (W ≃* ↥(StatedSL 3 K)) ∨ Nonempty (W ≃* StatedProj (StatedSL 3 K)))) ∨
    (p % 4 = 3 ∧ Nat.card K = p ^ 2 ∧
      (Nonempty (W ≃* ↥(StatedSU 3 p K)) ∨ Nonempty (W ≃* StatedProj (StatedSU 3 p K))))

@[expose] def IsSLEps3GraphExt (p : ℕ) (W : Type) [Group W] : Prop :=
  p.Prime ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K),
    (p % 4 = 1 ∧ Nat.card K = p ∧
      (IsExtendedByMatrixMap (StatedSL 3 K) ⊥ (fun A => (A⁻¹)ᵀ) W ∨
        IsExtendedByMatrixMap (StatedSL 3 K) (StatedScalars (Fin 3) K) (fun A => (A⁻¹)ᵀ) W)) ∨
    (p % 4 = 3 ∧ Nat.card K = p ^ 2 ∧
      (IsExtendedByMatrixMap (StatedSU 3 p K) ⊥ (fun A => (A⁻¹)ᵀ) W ∨
        IsExtendedByMatrixMap (StatedSU 3 p K) (StatedScalars (Fin 3) K) (fun A => (A⁻¹)ᵀ) W))

@[expose] def IsExtensionWith (X : Type*) [Group X] (A : Type*) [Group A]
    (P : Subgroup X → Prop) : Prop :=
  ∃ φ : X →* A, Function.Surjective φ ∧ P φ.ker

@[expose] def IsExtensionOf₃ (X : Type*) [Group X] (A B C : Type*) [Group A] [Group B]
    [Group C] : Prop :=
  ∃ (N : Subgroup X) (_ : N.Normal), Nonempty (↥N ≃* C) ∧ IsExtensionOf (X ⧸ N) A B

@[expose] def InducesOuterAut {D : Type*} [Group D] (x : D) (X : Subgroup D) : Prop :=
  x ∈ Subgroup.normalizer (X : Set D) ∧ ∀ k ∈ X, ∃ y ∈ X, x * y * x⁻¹ ≠ k * y * k⁻¹

section Cases

variable {D : Type} [Group D]

@[expose] def IsF618CaseOne (H₁ H₂ : Subgroup D) : Prop :=
  Nonempty (↥(H₁ ⊓ H₂) ≃* Multiplicative (ZMod 2)) ∧ pCoreOf 2 H₁ = ⊥ ∧ pCoreOf 2 H₂ = ⊥ ∧
    ¬ IsCyclic ↥(Open.pCore 3 D)

@[expose] def IsF618CaseTwo (D : Type*) [Group D] : Prop :=
  Nonempty (D ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) ∨
    IsExtensionWith D (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))
      (fun N => IsPOnePlusTwo 3 ↥N)

@[expose] def IsF618CaseThree (H₁ H₂ : Subgroup D) : Prop :=
  ∃ (p : ℕ) (K Z : Subgroup D), p.Prime ∧ (p % 24 = 11 ∨ p % 24 = 13) ∧ IsL2 p 1 ↥K ∧
    Nat.card ↥Z = 3 ∧ K ⊔ Z = twoResidual ⊤ ∧ K ⊓ Z = ⊥ ∧ (∀ k ∈ K, ∀ z ∈ Z, k * z = z * k) ∧
    Nonempty (↥(H₁ ⊓ H₂) ≃* DihedralGroup 4) ∧ Nonempty (↥H₁ ≃* DihedralGroup 12) ∧
    Nonempty (↥H₂ ≃* Equiv.Perm (Fin 4)) ∧
    ∀ t ∈ H₁ ⊓ H₂, t ∉ K → InducesOuterAut t K ∧ InducesOuterAut t Z

@[expose] def IsF618CaseFour (H₁ H₂ : Subgroup D) : Prop :=
  (∃ p : ℕ, p.Prime ∧ (p % 24 = 11 ∨ p % 24 = 13) ∧ IsL2 p 1 D) ∧
    Nonempty (↥(H₁ ⊓ H₂) ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ∧
    Nonempty (↥H₁ ≃* DihedralGroup 6) ∧ Nonempty (↥H₂ ≃* DihedralGroup 6)

@[expose] def IsF618CaseFive (H₁ H₂ : Subgroup D) : Prop :=
  (∃ q : ℕ, q.Prime ∧ (q % 24 = 11 ∨ q % 24 = 13) ∧ IsPGL2 q D) ∧
    Nonempty (↥(H₁ ⊓ H₂) ≃* DihedralGroup 4) ∧ Nonempty (↥H₁ ≃* DihedralGroup 12) ∧
    Nonempty (↥H₂ ≃* Equiv.Perm (Fin 4))

@[expose] def IsF618CaseSix (H₁ H₂ : Subgroup D) : Prop :=
  (IsHatAlt 6 D ∨ ∃ p e : ℕ, p.Prime ∧ 1 ≤ e ∧ e ≤ 2 ∧ (p ^ e % 16 = 7 ∨ p ^ e % 16 = 9) ∧
      IsL2 p e D) ∧
    Nonempty (↥(H₁ ⊓ H₂) ≃* DihedralGroup 4) ∧
    ((Nonempty (↥H₁ ≃* Equiv.Perm (Fin 4)) ∧ Nonempty (↥H₂ ≃* Equiv.Perm (Fin 4))) ∨
      ((∃ p e : ℕ, p.Prime ∧ 1 ≤ e ∧ e ≤ 2 ∧ (p ^ e % 16 = 7 ∨ p ^ e % 16 = 9) ∧
          (p ^ e % 24 = 1 ∨ p ^ e % 24 = 23) ∧ IsL2 p e D) ∧
        Nonempty (↥H₁ ≃* DihedralGroup 12) ∧ Nonempty (↥H₂ ≃* Equiv.Perm (Fin 4))))

@[expose] def IsF618CaseSeven (H₁ H₂ : Subgroup D) : Prop :=
  (Nonempty (D ≃* ↥(alternatingGroup (Fin 7))) ∨ IsHatAlt 7 D) ∧
    Nonempty (↥(H₁ ⊓ H₂) ≃* DihedralGroup 4) ∧ Nonempty (↥H₁ ≃* Equiv.Perm (Fin 4)) ∧
    IsExtensionOf ↥H₂ (Multiplicative (ZMod 2))
      (Multiplicative (ZMod 3) × (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))

@[expose] def IsF618CaseEight (H₁ H₂ : Subgroup D) : Prop :=
  (IsHatSym 6 D ∨ ∃ p : ℕ, p.Prime ∧ p % 8 = 3 ∧ IsL2FieldExt p D) ∧
    Nonempty (↥(H₁ ⊓ H₂) ≃* Multiplicative (ZMod 2) × DihedralGroup 4) ∧
    Nonempty (↥H₁ ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) ∧
    Nonempty (↥H₂ ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))

@[expose] def IsF618CaseNine (H₁ H₂ : Subgroup D) : Prop :=
  (Nonempty (D ≃* Equiv.Perm (Fin 7)) ∨ IsHatSym 7 D) ∧
    Nonempty (↥(H₁ ⊓ H₂) ≃* Multiplicative (ZMod 2) × DihedralGroup 4) ∧
    Nonempty (↥H₁ ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) ∧
    Nonempty (↥H₂ ≃* Equiv.Perm (Fin 3) × DihedralGroup 4)

@[expose] def IsF618CaseTen (H₁ H₂ : Subgroup D) : Prop :=
  (∃ p : ℕ, (p % 8 = 3 ∨ p % 8 = 5) ∧ IsSLEps3 p D) ∧
    Nonempty (↥(H₁ ⊓ H₂) ≃* Multiplicative (ZMod 4) ≀ᵣ Multiplicative (ZMod 2)) ∧
    IsExtensionWith ↥H₁ (Equiv.Perm (Fin 3))
      (fun N => IsCentralProduct₂ ↥N (Multiplicative (ZMod 4)) (QuaternionGroup 2)) ∧
    IsExtensionOf ↥H₂ (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))

@[expose] def IsF618CaseEleven (H₁ H₂ : Subgroup D) : Prop :=
  (∃ p : ℕ, (p % 8 = 3 ∨ p % 8 = 5) ∧ IsSLEps3GraphExt p D) ∧
    IsExtensionOf ↥(H₁ ⊓ H₂) (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) ∧
    IsExtensionWith ↥H₁ (Equiv.Perm (Fin 3))
      (fun N => IsCentralProduct₂ ↥N (QuaternionGroup 2) (QuaternionGroup 2)) ∧
    IsExtensionOf ↥H₂ (DihedralGroup 6) (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))

@[expose] def IsF618CaseTwelve (H₁ H₂ : Subgroup D) : Prop :=
  IsM12 D ∧
    IsExtensionOf ↥(H₁ ⊓ H₂) (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) ∧
    IsExtensionWith ↥H₁ (Equiv.Perm (Fin 3))
      (fun N => IsCentralProduct₂ ↥N (QuaternionGroup 2) (QuaternionGroup 2)) ∧
    IsExtensionOf ↥H₂ (DihedralGroup 6) (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))

@[expose] def IsF618CaseThirteen (H₁ H₂ : Subgroup D) : Prop :=
  IsAutM12 D ∧
    IsExtensionOf ↥(H₁ ⊓ H₂) (DihedralGroup 4) (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) ∧
    IsExtensionWith ↥H₁ (DihedralGroup 6)
      (fun N => IsCentralProduct₂ ↥N (QuaternionGroup 2) (QuaternionGroup 2)) ∧
    IsExtensionOf₃ ↥H₂ (Multiplicative (ZMod 2))
      (Multiplicative (ZMod 3) × (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))

@[expose] def IsF618CaseOriented (H₁ H₂ : Subgroup D) : Prop :=
  IsF618CaseOne H₁ H₂ ∨ IsF618CaseTwo D ∨ IsF618CaseThree H₁ H₂ ∨ IsF618CaseFour H₁ H₂ ∨
    IsF618CaseFive H₁ H₂ ∨ IsF618CaseSix H₁ H₂ ∨ IsF618CaseSeven H₁ H₂ ∨
    IsF618CaseEight H₁ H₂ ∨ IsF618CaseNine H₁ H₂ ∨ IsF618CaseTen H₁ H₂ ∨
    IsF618CaseEleven H₁ H₂ ∨ IsF618CaseTwelve H₁ H₂ ∨ IsF618CaseThirteen H₁ H₂

@[expose] def F618Conclusion (H₁ H₂ : Subgroup D) : Prop :=
  IsF618CaseOriented H₁ H₂ ∨ IsF618CaseOriented H₂ H₁

theorem f618Conclusion_comm {H₁ H₂ : Subgroup D} : F618Conclusion H₁ H₂ ↔ F618Conclusion H₂ H₁ :=
  or_comm

end Cases

section Orders

theorem IsExtensionOf.card_eq {X A N : Type*} [Group X] [Group A] [Group N] [Finite X]
    (h : IsExtensionOf X A N) : Nat.card X = Nat.card A * Nat.card N := by
  obtain ⟨φ, hφ, ⟨e⟩⟩ := h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv,
    Nat.card_congr e.toEquiv]

variable {D : Type} [Group D] {H₁ H₂ : Subgroup D}

theorem IsF618CaseOne.card_inf (h : IsF618CaseOne H₁ H₂) : Nat.card ↥(H₁ ⊓ H₂) = 2 := by
  obtain ⟨⟨e⟩, -⟩ := h
  rw [Nat.card_congr e.toEquiv]
  simp

theorem IsF618CaseThree.card_inf (h : IsF618CaseThree H₁ H₂) : Nat.card ↥(H₁ ⊓ H₂) = 8 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, ⟨e⟩, -⟩ := h
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]

theorem IsF618CaseFour.card_inf (h : IsF618CaseFour H₁ H₂) : Nat.card ↥(H₁ ⊓ H₂) = 4 := by
  obtain ⟨-, ⟨e⟩, -⟩ := h
  rw [Nat.card_congr e.toEquiv]
  simp

theorem IsF618CaseFive.card_inf (h : IsF618CaseFive H₁ H₂) : Nat.card ↥(H₁ ⊓ H₂) = 8 := by
  obtain ⟨-, ⟨e⟩, -⟩ := h
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]

theorem IsF618CaseSix.card_inf (h : IsF618CaseSix H₁ H₂) : Nat.card ↥(H₁ ⊓ H₂) = 8 := by
  obtain ⟨-, ⟨e⟩, -⟩ := h
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]

theorem IsF618CaseSeven.card_inf (h : IsF618CaseSeven H₁ H₂) : Nat.card ↥(H₁ ⊓ H₂) = 8 := by
  obtain ⟨-, ⟨e⟩, -⟩ := h
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]

theorem IsF618CaseEight.card_inf (h : IsF618CaseEight H₁ H₂) : Nat.card ↥(H₁ ⊓ H₂) = 16 := by
  obtain ⟨-, ⟨e⟩, -⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, DihedralGroup.nat_card]
  simp

theorem IsF618CaseNine.card_inf (h : IsF618CaseNine H₁ H₂) : Nat.card ↥(H₁ ⊓ H₂) = 16 := by
  obtain ⟨-, ⟨e⟩, -⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, DihedralGroup.nat_card]
  simp

theorem IsF618CaseTen.card_inf (h : IsF618CaseTen H₁ H₂) : Nat.card ↥(H₁ ⊓ H₂) = 32 := by
  obtain ⟨-, ⟨e⟩, -⟩ := h
  rw [Nat.card_congr e.toEquiv, RegularWreathProduct.card]
  simp

theorem IsF618CaseEleven.card_inf [Finite D] (h : IsF618CaseEleven H₁ H₂) :
    Nat.card ↥(H₁ ⊓ H₂) = 64 := by
  rw [h.2.1.card_eq, Nat.card_prod, Nat.card_prod]
  simp

theorem IsF618CaseTwelve.card_inf [Finite D] (h : IsF618CaseTwelve H₁ H₂) :
    Nat.card ↥(H₁ ⊓ H₂) = 64 := by
  rw [h.2.1.card_eq, Nat.card_prod, Nat.card_prod]
  simp

theorem IsF618CaseThirteen.card_inf [Finite D] (h : IsF618CaseThirteen H₁ H₂) :
    Nat.card ↥(H₁ ⊓ H₂) = 128 := by
  rw [h.2.1.card_eq, Nat.card_prod, DihedralGroup.nat_card]
  simp

end Orders

@[expose] def TheoremF618 : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (G₁ G₂ : Subgroup D), IsGoldschmidtTriple G₁ G₂ →
    (∃ (X : Type) (_ : Group X) (_ : Finite X), SQTKTauCeti.StronglyQuasithin X ∧
      CFSG.SectionRank.IsKGroupCat X ∧ Nonempty (D ≃* X ⧸ CFSG.pPrimeCore 3 X)) →
    F618Conclusion G₁ G₂

theorem f6_18 (hF : TheoremF618) {X : Type} [Group X] [Finite X]
    (hsq : SQTKTauCeti.StronglyQuasithin X) (hK : CFSG.SectionRank.IsKGroupCat X)
    {G₁ G₂ : Subgroup (X ⧸ CFSG.pPrimeCore 3 X)} (h : IsGoldschmidtTriple G₁ G₂) :
    F618Conclusion G₁ G₂ :=
  hF _ G₁ G₂ h ⟨X, inferInstance, inferInstance, hsq, hK, ⟨MulEquiv.refl _⟩⟩

section In

variable {G : Type} [Group G] [Finite G] {I G₁ G₂ : Subgroup G}

omit [Finite G] in
theorem map_pCoreOf_subgroupOf {H : Subgroup G} (hHI : H ≤ I) :
    (pCoreOf 2 (H.subgroupOf I)).map I.subtype = pCoreOf 2 H := by
  let ψ : ↥(H.subgroupOf I) ≃* ↥H := Subgroup.subgroupOfEquivOfLe hHI
  unfold pCoreOf
  rw [Subgroup.map_map, ← map_pCore_mulEquiv 2 ψ, Subgroup.map_map]
  congr 1

theorem IsGoldschmidtTripleIn.f6_18 (hF : TheoremF618) (h : IsGoldschmidtTripleIn I G₁ G₂)
    (hsq : SQTKTauCeti.StronglyQuasithin ↥I) (hK : CFSG.SectionRank.IsKGroupCat ↥I) :
    ((G₁.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)) ⊓
          (G₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)) =
        (G₁.subgroupOf I ⊓ G₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)) ∧
      IsGoldschmidtAmalgam ((G₁.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)))
        ((G₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))) ∧
      IsAmalgamIso ((G₁.subgroupOf I).map (QuotientGroup.mk' (Open.pCore 2 ↥I)))
        ((G₂.subgroupOf I).map (QuotientGroup.mk' (Open.pCore 2 ↥I)))
        ((G₁.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)))
        ((G₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))) ∧
      F618Conclusion ((G₁.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)))
        ((G₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)))) ∨
    (pCoreOf 2 (G₁.subgroupOf I) = Open.pCore 2 ↥I ∧
      pCoreOf 2 (G₂.subgroupOf I) = Open.pCore 2 ↥I ∧
      Nonempty (↥I ⧸ CFSG.pPrimeCore 3 ↥I ≃* Equiv.Perm (Fin 3)) ∧
      G₁.subgroupOf I ⊔ CFSG.pPrimeCore 3 ↥I = ⊤ ∧
      ¬ IsCyclic ↥((CFSG.pPrimeCore 3 ↥I).map (QuotientGroup.mk' (Open.pCore 2 ↥I)))) := by
  rcases h.goldschmidt_mod_pPrimeCore with ⟨h₁, h₂, h₃⟩ | h'
  · exact Or.inl ⟨h₁, h₂, h₃, F6.f6_18 hF hsq hK h₂.toIsGoldschmidtTriple⟩
  · exact Or.inr h'

theorem IsGoldschmidtTripleIn.f6_18_of_ne (hF : TheoremF618) (h : IsGoldschmidtTripleIn I G₁ G₂)
    (hsq : SQTKTauCeti.StronglyQuasithin ↥I) (hK : CFSG.SectionRank.IsKGroupCat ↥I)
    (hne : pCoreOf 2 G₁ ≠ pCoreOf 2 G₂) :
    IsGoldschmidtAmalgam ((G₁.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)))
        ((G₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))) ∧
      F618Conclusion ((G₁.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)))
        ((G₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))) := by
  rcases h.f6_18 hF hsq hK with ⟨-, h₂, -, h₄⟩ | ⟨e₁, e₂, -⟩
  · exact ⟨h₂, h₄⟩
  · exfalso
    apply hne
    have h₁ : G₁ ≤ I := h.1 ▸ le_sup_left
    have h₂ : G₂ ≤ I := h.1 ▸ le_sup_right
    rw [← map_pCoreOf_subgroupOf h₁, ← map_pCoreOf_subgroupOf h₂, e₁, e₂]

end In

end F6

end CFSG.Quasithin

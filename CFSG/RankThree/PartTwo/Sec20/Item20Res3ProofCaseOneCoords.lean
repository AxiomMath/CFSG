module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res2ProofCaseOne

public section

namespace CFSG.RankThree.PartTwo.Sec20.Res3

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec20
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.CGT.T75N
open CFSG.RankThree.PartTwo.Sec20.Res2
open CFSG.Assembly.RankThreeEven (projSL)

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def vecConj {F : Type} [Field F] (g : SpecialLinearGroup (Fin 3) F) :
    Multiplicative (Fin 3 → F) →* Multiplicative (Fin 3 → F) where
  toFun x := Multiplicative.ofAdd
    (((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
      Multiplicative.toAdd x)
  map_one' := by simp
  map_mul' x y := by simp [Matrix.mulVec_add]

omit [Finite G] in
theorem vecConj_injective {F : Type} [Field F] (g : SpecialLinearGroup (Fin 3) F) :
    Function.Injective (vecConj g) := by
  intro x y h
  have h' : ((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
      Multiplicative.toAdd x =
        ((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
          Multiplicative.toAdd y := congrArg Multiplicative.toAdd h
  have := congrArg (fun v => (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v) h'
  simp only [mulVec_inv_mulVec] at this
  exact Multiplicative.toAdd.injective this

omit [Finite G] in
theorem vecConj_surjective {F : Type} [Field F] (g : SpecialLinearGroup (Fin 3) F) :
    Function.Surjective (vecConj g) := by
  intro y
  refine ⟨Multiplicative.ofAdd ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd y), ?_⟩
  change Multiplicative.ofAdd (((g⁻¹ : SpecialLinearGroup (Fin 3) F) :
    Matrix (Fin 3) (Fin 3) F) *ᵥ _) = y
  rw [toAdd_ofAdd, inv_mulVec_mulVec, ofAdd_toAdd]

omit [Finite G] in
theorem lstab_le_vstab_of_card_two {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) :
    lstab F ≤ vstab F := by
  rintro g ⟨a, ha⟩
  show (g : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 = Pi.single 0 1
  rcases eq_zero_or_eq_one_of_card_two hF a with h | h
  · exfalso
    apply mulVec_e0_ne_zero g
    rw [ha, h, zero_smul]
  · rw [ha, h, one_smul]

theorem caseOne_coords_core {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hT : Ctx20 G A M L N c T) (hTN : T ≤ N)
    (h207 : kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) ≤ N)
    (he : Nonempty (kTwenty M c ⧸ CFSG.pCore 2 (kTwenty M c) ≃* projSL 3 (GaloisField 2 1)))
    (hKN : ¬ kTwenty M c ≤ N)
    (hi : CFSG.Quasithin.IsC134Case 1 (kTwenty M c ⊔ T) (sTwenty M N c T) (kTwenty M c)) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F)
      (α : ↥(kTwenty M c) →* SpecialLinearGroup (Fin 3) F)
      (β : ↥(CFSG.Quasithin.c134Q (kTwenty M c ⊔ T) (kTwenty M c)) →*
        Multiplicative (Fin 3 → F)),
      Nat.card F = 2 ∧ Function.Surjective α ∧
      (∀ k : ↥(kTwenty M c), α k = 1 ↔ (k : G) ∈ CFSG.Open.pCoreOf 2 (kTwenty M c)) ∧
      Function.Injective β ∧ Function.Surjective β ∧
      (∀ (a : ↥(kTwenty M c)) (u v : ↥(CFSG.Quasithin.c134Q (kTwenty M c ⊔ T) (kTwenty M c))),
        (v : G) = a * u * (a : G)⁻¹ →
          Multiplicative.toAdd (β v) =
            (α a : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (β u)) ∧
      (∀ k : ↥(kTwenty M c), (k : G) ∈ N ↔ α k ∈ vstab F) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := he
  obtain ⟨⟨-, -⟩, n', F, _, _, hF, hKQ, α₀, hαs₀, hαk₀, β₀, hβs₀, hβk₀, hβ₀⟩ := hi
  have : CharP F 2 := charP_of_card_eq_prime_pow hF
  have hKM : kTwenty M c ≤ M := kTwenty_le_of_hyp201 hT.toHyp201
  have hMK : M ≤ Subgroup.normalizer (kTwenty M c : Set G) := le_normalizer_normalClosureIn M c
  set α := toSL α₀ with hαdef
  have hαs : Function.Surjective α := toSL_surjective hαs₀
  have hα'k := toSL_eq_one_iff_mem hαk₀
  have hβinj := injective_of_ker_eq β₀ hβk₀
  have hn' : n' = 1 := by
    have hker : α.ker = CFSG.pCore 2 ↥(kTwenty M c) := by
      ext k
      rw [MonoidHom.mem_ker, toSL_eq_one_iff, ← MonoidHom.mem_ker, hαk₀]
    have h1 : Nat.card (SpecialLinearGroup (Fin 3) F) =
        Nat.card (↥(kTwenty M c) ⧸ CFSG.pCore 2 ↥(kTwenty M c)) := by
      rw [← hker]
      exact (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hαs).toEquiv).symm
    have h2 : Nat.card (↥(kTwenty M c) ⧸ CFSG.pCore 2 ↥(kTwenty M c)) =
        Nat.card (SpecialLinearGroup (Fin 3) (GaloisField 2 1)) :=
      Nat.card_congr ((e.trans (projSLEquivStatedSL odd_one)).trans
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 _).symm).toEquiv
    exact eq_of_card_sl3_eq (by rw [Nat.card_eq_fintype_card, hF])
      (GaloisField.card 2 1 one_ne_zero) (h1.trans h2)
  have hF2 : Nat.card F = 2 := by rw [Nat.card_eq_fintype_card, hF, hn', pow_one]
  have hP : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ kTwenty M c) (kTwenty M c) :=
    hT.sylow.inf_of_le_normalizer hKM hMK
  obtain ⟨g, hg⟩ := exists_coords_fixed α hαs hP
  set α' : ↥(kTwenty M c) →* SpecialLinearGroup (Fin 3) F :=
    (MulAut.conj g⁻¹).toMonoidHom.comp α with hα'
  have hα'_apply : ∀ k, α' k = g⁻¹ * α k * g := by
    intro k
    simp [hα']
  set β' : ↥(CFSG.Quasithin.c134Q (kTwenty M c ⊔ T) (kTwenty M c)) →*
      Multiplicative (Fin 3 → F) := (vecConj g).comp β₀ with hβ'
  have hβ'_apply : ∀ q, Multiplicative.toAdd (β' q) =
      ((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        Multiplicative.toAdd (β₀ q) := fun q => rfl
  have hβ₀' : ∀ (a : ↥(kTwenty M c))
      (u v : ↥(CFSG.Quasithin.c134Q (kTwenty M c ⊔ T) (kTwenty M c))),
      (v : G) = a * u * (a : G)⁻¹ →
      Multiplicative.toAdd (β₀ v) =
        (α a : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (β₀ u) := by
    intro a u v huv
    rw [hβ₀ a u v huv, hαdef, coe_toSL]
  have hQ2 : IsPGroup 2 (CFSG.Quasithin.c134Q (kTwenty M c ⊔ T) (kTwenty M c)) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le c134Q_le
  have hK0 : ∀ k : ↥(kTwenty M c), α' k ∈ vstab F →
      (k : G) ∈ Subgroup.centralizer (zTwenty T : Set G) := by
    intro k hk
    rw [hα'_apply] at hk
    have h := centralizer_of_transfer
      (A := CFSG.Quasithin.c134Q (kTwenty M c ⊔ T) (kTwenty M c)) (P := T ⊓ kTwenty M c)
      (Z := (zTwenty T : Set G))
      hKQ (comm_of_injective β₀ hβinj) hQ2 hP
      (fun z hz a ha => (mem_center_pCoreOf_of_mem_zTwenty_core hT hz).2 a (c134Q_le ha))
      (fun z hz p hp => by rw [(mem_and_commute_of_mem_zTwenty hz).2 p hp.1]; group)
      (fun z hz k hk => commutator_mem_c134Q_core hT hz hk) k.2 (fun m hm hmP => by
        have hkm : (k : G) * m * (k : G)⁻¹ ∈
            CFSG.Quasithin.c134Q (kTwenty M c ⊔ T) (kTwenty M c) :=
          (Subgroup.mem_normalizer_iff.mp (hKQ k.2) m).mp hm
        have hfixm : (α k : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (β₀ ⟨m, hm⟩) =
            Multiplicative.toAdd (β₀ ⟨m, hm⟩) := by
          refine hg _ (fun p hp => ?_) k hk
          exact (hβ₀' p ⟨m, hm⟩ ⟨m, hm⟩ (hmP p hp).symm).symm
        have heq : β₀ ⟨_, hkm⟩ = β₀ ⟨m, hm⟩ := by
          apply Multiplicative.toAdd.injective
          rw [hβ₀' k ⟨m, hm⟩ ⟨_, hkm⟩ rfl, hfixm]
        exact congrArg Subtype.val (hβinj heq))
    refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    have := h z hz
    calc z * (k : G) = (k : G) * z * (k : G)⁻¹ * k := by rw [this]
      _ = k * z := by group
  have hTM : T ≤ M := hT.sylow.le
  have hKTM : kTwenty M c ⊔ T ≤ M := sup_le hKM hTM
  have hQT : CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) ≤ T :=
    pCoreOf_le_of_isSylowOf (hT.sylow.of_le le_sup_right hKTM)
  have hOKN : CFSG.Open.pCoreOf 2 (kTwenty M c) ≤ N := by
    refine (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 (kTwenty M c)).trans le_sup_left) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (kTwenty M c))).trans (hQT.trans hTN)
    exact sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (kTwenty M c))
      ((hTM.trans hMK).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (kTwenty M c)))
  have hα'k : ∀ k : ↥(kTwenty M c),
      α' k = 1 ↔ (k : G) ∈ CFSG.Open.pCoreOf 2 (kTwenty M c) := by
    intro k
    rw [hα'_apply, ← hα'k k]
    constructor
    · intro h
      calc α k = g * (g⁻¹ * α k * g) * g⁻¹ := by group
        _ = 1 := by rw [h]; group
    · intro h
      rw [h]
      group
  have hα's : Function.Surjective α' := by
    intro x
    obtain ⟨k, hk⟩ := hαs (g * x * g⁻¹)
    exact ⟨k, by rw [hα'_apply, hk]; group⟩
  have hN : ∀ k : ↥(kTwenty M c), (k : G) ∈ N ↔ α' k ∈ vstab F := by
    intro k
    refine ⟨fun hkN => ?_, fun hk => h207 ⟨k.2, hK0 k hk⟩⟩
    by_contra hkv
    apply hKN
    set IKN := ((kTwenty M c ⊓ N).subgroupOf (kTwenty M c)).map α' with hIKN
    have hvI : vstab F ≤ IKN := by
      intro h hh
      obtain ⟨k', rfl⟩ := hα's h
      exact ⟨k', Subgroup.mem_subgroupOf.mpr ⟨k'.2, h207 ⟨k'.2, hK0 k' hh⟩⟩, rfl⟩
    have hnot : ¬ IKN ≤ lstab F := fun hle =>
      hkv (lstab_le_vstab_of_card_two hF2
        (hle ⟨k, Subgroup.mem_subgroupOf.mpr ⟨k.2, hkN⟩, rfl⟩))
    have htop := eq_top_of_vstab_le hvI hnot
    intro x hx
    have hmem : α' ⟨x, hx⟩ ∈ IKN := htop ▸ Subgroup.mem_top _
    obtain ⟨k', hk', hkk'⟩ := hmem
    have h1 : ((k' : G))⁻¹ * x ∈ CFSG.Open.pCoreOf 2 (kTwenty M c) := by
      have := (hα'k (k'⁻¹ * ⟨x, hx⟩)).mp (by rw [map_mul, map_inv, hkk', inv_mul_cancel])
      simpa using this
    have : x = k' * ((k' : G)⁻¹ * x) := by group
    rw [this]
    exact N.mul_mem (Subgroup.mem_subgroupOf.mp hk').2 (hOKN h1)
  refine ⟨F, inferInstance, inferInstance, α', β', hF2, hα's, hα'k,
    (vecConj_injective g).comp hβinj, (vecConj_surjective g).comp hβs₀, ?_, hN⟩
  intro a u v huv
  rw [hβ'_apply, hβ'_apply, hβ₀' a u v huv, hα'_apply, mulVec_mul_mul, mulVec_inv_mulVec]

end CFSG.RankThree.PartTwo.Sec20.Res3

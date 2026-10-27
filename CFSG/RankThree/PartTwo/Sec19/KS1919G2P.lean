module

public import CFSG.RankThree.PartTwo.Sec19.Step1919EndProof
import CFSG.RankThree.PartTwo.Census.Carrier.G2Even
import CFSG.RankThree.Classical.EvenSurvivingScalarRank

public section

namespace CFSG.RankThree.PartTwo.Sec19

namespace KS1919G2PProof

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

set_option linter.unusedSectionVars false


theorem exists_le_normalizer_of_normalizer_sylow_le {τ : Tag} {K : Type} [Field K] [Finite K]
    {r : ℕ} [Fact r.Prime] [CharP K r] {P : Subgroup (adjointGroup τ K)} (hPtop : P ≠ ⊤)
    (S : Sylow r (adjointGroup τ K))
    (hSP : Subgroup.normalizer ((S : Subgroup (adjointGroup τ K)) : Set (adjointGroup τ K)) ≤ P) :
    ∃ R : Subgroup (adjointGroup τ K), R ≠ ⊥ ∧ IsPGroup r R ∧
      P ≤ Subgroup.normalizer (R : Set (adjointGroup τ K)) := by
  classical
  have hfin : Finite (ModGL τ K) := finite_modGL
  have hUsyl := isPGroup_and_not_dvd_index r (posUnipotent_le_adjointGroup (τ := τ) (K := K))
    (card_posUnipotent (τ := τ) (K := K))
  set SU : Sylow r (adjointGroup τ K) := hUsyl.1.toSylow hUsyl.2 with hSU
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (adjointGroup τ K) SU S
  have hUB : posUnipotent τ K ≤ borelGroup τ K := le_sup_right
  have hBN : borelGroup τ K ≤ Subgroup.normalizer (posUnipotent τ K : Set (ModGL τ K)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUB).1
      (triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.2.2.2.1
  have hmem : ∀ z : adjointGroup τ K, z ∈ (S : Subgroup (adjointGroup τ K)) ↔
      g⁻¹ * z * g ∈ (SU : Subgroup (adjointGroup τ K)) := by
    intro z
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.conj_symm_apply]
  have hSUmem : ∀ z : adjointGroup τ K, z ∈ (SU : Subgroup (adjointGroup τ K)) ↔
      (z : ModGL τ K) ∈ posUnipotent τ K := fun z => Iff.rfl
  have hBP : ∀ b : adjointGroup τ K, (b : ModGL τ K) ∈ borelGroup τ K → g * b * g⁻¹ ∈ P := by
    intro b hb
    apply hSP
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [hmem, hmem]
    have e : g⁻¹ * (g * b * g⁻¹ * y * (g * b * g⁻¹)⁻¹) * g = b * (g⁻¹ * y * g) * b⁻¹ := by
      group
    rw [e, hSUmem, hSUmem]
    have := Subgroup.mem_normalizer_iff.1 (hBN hb) ((g⁻¹ * y * g : adjointGroup τ K) : ModGL τ K)
    simpa using this
  set P₀ : Subgroup (adjointGroup τ K) := P.comap (MulAut.conj g).toMonoidHom with hP₀
  have hP₀mem : ∀ y, y ∈ P₀ ↔ g * y * g⁻¹ ∈ P := fun y => by
    simp [hP₀, MulAut.conj_apply]
  have hP₀top : P₀ ≠ ⊤ := by
    intro h
    apply hPtop
    refine eq_top_iff.2 fun y _ => ?_
    have h1 : g⁻¹ * y * g ∈ P₀ := h ▸ Subgroup.mem_top _
    rw [hP₀mem] at h1
    simpa [mul_assoc] using h1
  set A : Subgroup (ModGL τ K) := P₀.map (adjointGroup τ K).subtype with hA
  have hBA : borelGroup τ K ≤ A := fun b hb =>
    ⟨⟨b, borelGroup_le_adjointGroup' hb⟩, (hP₀mem _).2 (hBP _ hb), rfl⟩
  have hAC : A ≤ adjointGroup τ K := Subgroup.map_subtype_le _
  have hAJ := (borel_overgroup_classification τ K).1 A hBA hAC
  set J : Set (Fin τ.rank) := {i | weylElt τ K i 1 ∈ A} with hJ
  have hJne : J ≠ Set.univ := by
    intro hJu
    apply hP₀top
    have hAeq : A = adjointGroup τ K := by
      rw [hAJ, hJu]
      refine le_antisymm (parabolicSubgroup_le_adjointGroup τ K _) ?_
      rw [(borel_weyl_generation τ K).1]
      unfold parabolicSubgroup
      refine sup_le_sup_left (Subgroup.closure_mono ?_) _
      rintro _ ⟨i, rfl⟩
      exact ⟨i, Set.mem_univ i, rfl⟩
    refine eq_top_iff.2 fun y _ => ?_
    have h1 : (y : ModGL τ K) ∈ A := by
      rw [hAeq]
      exact y.2
    obtain ⟨y', hy', hyy'⟩ := h1
    have h2 : y' = y := Subtype.ext hyy'
    rwa [← h2]
  obtain ⟨hQP, -, -, -, -, -, -, -, -, -, -, -, hpg⟩ := parabolic_root_radical_Levi_factors τ K J
  obtain ⟨-, hQr, hQne⟩ := hpg r
  have hPJN := parabolicSubgroup_le_normalizer_parabolicRadical (τ := τ) (K := K) J
  have hQC : parabolicRadical τ K J ≤ adjointGroup τ K :=
    hQP.trans (parabolicSubgroup_le_adjointGroup τ K J)
  set R₀ : Subgroup (adjointGroup τ K) :=
    (parabolicRadical τ K J).subgroupOf (adjointGroup τ K) with hR₀
  have hR₀ne : R₀ ≠ ⊥ := by
    obtain ⟨q, hq1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 (hQne hJne)
    intro h
    have hq : (⟨(q : ModGL τ K), hQC q.2⟩ : adjointGroup τ K) ∈ R₀ :=
      Subgroup.mem_subgroupOf.2 q.2
    rw [h, Subgroup.mem_bot] at hq
    have hq' : (q : ModGL τ K) = 1 := congrArg Subtype.val hq
    exact hq1 (Subtype.ext hq')
  have hR₀r : IsPGroup r R₀ := hQr.comap_subtype
  have hP₀N : ∀ y ∈ P₀, ∀ z : adjointGroup τ K, z ∈ R₀ ↔ y * z * y⁻¹ ∈ R₀ := by
    intro y hy z
    have hyA : (y : ModGL τ K) ∈ parabolicSubgroup τ K J := by
      rw [← hAJ]
      exact ⟨y, hy, rfl⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.1 (hPJN hyA) z
  refine ⟨R₀.map (MulAut.conj g).toMonoidHom, fun h => hR₀ne ?_, hR₀r.map _, fun x hx => ?_⟩
  · exact (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective).1 h
  · rw [Subgroup.mem_normalizer_iff]
    intro z
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv, MulAut.conj_symm_apply,
      MulAut.conj_symm_apply]
    have hy : g⁻¹ * x * g ∈ P₀ := by
      rw [hP₀mem]
      convert hx using 1
      group
    have e : g⁻¹ * (x * z * x⁻¹) * g = g⁻¹ * x * g * (g⁻¹ * z * g) * (g⁻¹ * x * g)⁻¹ := by
      group
    rw [e]
    exact hP₀N _ hy _

end KS1919G2PProof

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley in
theorem ks1919G2P :
    KS1919G2P := by
  intro X _ _ n hX P hP B hBP hBc hB3
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card]; exact hK)
  have : Finite (ModGL .G2 K) := finite_modGL
  obtain ⟨hPtop, T, hT⟩ := Step1910Proof.isProperParabolic_map e hP
  obtain ⟨R, hR, hR2, hPR⟩ :=
    KS1919G2PProof.exists_le_normalizer_of_normalizer_sylow_le hPtop T hT
  set B' : Subgroup (adjointGroup .G2 K) := B.map e.toMonoidHom with hB'
  have hB'card : Nat.card B' = Nat.card B := Subgroup.card_map_of_injective e.injective
  have hB'R : B' ≤ Subgroup.normalizer (R : Set (adjointGroup .G2 K)) :=
    (Subgroup.map_mono hBP).trans hPR
  have hB'c : ∀ x ∈ B', ∀ y ∈ B', x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hBc x hx y hy]
  have hB'3 : ∀ x ∈ B', x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hB3 x hx, map_one]
  have hEl : CFSG.Open.IsElemAbelian 3 B' :=
    ⟨⟨⟨fun a b => Subtype.ext (hB'c a a.2 b b.2)⟩⟩, hB'3⟩
  have hB'p : IsPGroup 3 B' := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hB'3 _ x.2)⟩
  obtain ⟨k, hk⟩ := hB'p.exists_card_eq
  have h1 : k ≤ CFSG.Open.pRank 3 (Subgroup.normalizer (R : Set (adjointGroup .G2 K))) :=
    CFSG.SectionRank.le_pRank (by norm_num) hB'R hEl hk
  have h2 := CFSG.RankThree.Classical.pRank_le_localRank (p := 3) (by norm_num)
    (G := adjointGroup .G2 K) (X := Subgroup.normalizer (R : Set (adjointGroup .G2 K)))
    ⟨R, hR, hR2, rfl⟩
  have h3 := CFSG.RankThree.PartTwo.Census.Carrier.G2Even.localRank_three_adjointGroup K
  have hk2 : k ≤ 2 := le_trans h1 (le_trans h2 h3)
  rw [← hB'card, hk]
  calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
    _ = 9 := by norm_num

end CFSG.RankThree.PartTwo.Sec19

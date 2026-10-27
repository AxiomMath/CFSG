module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTriDiag
public import CFSG.RankThree.PartOne.K133.KillL2
public import CFSG.RankThree.PartOne.KF.F122D4
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityCommutingSL2
public import CFSG.RankThree.PartOne.S15K.SL2Model
public import CFSG.LieType.Chevalley.TrialityExactFiniteOrder
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.RankThree.PartOne.K133.Moving
public import CFSG.RankThree.PartOne.K133.SylowKill
public import CFSG.RankThree.PartOne.S11c.Sec66D4Tri
public import CFSG.RankThree.PartOne.S11c.Sec66Sp
public import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.RankThree.PartOne.S12.Sec137
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CommutatorNormalizer
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley

namespace TableBExcSmallRest

section SL2

theorem card_le_of_isElemAbelian_sl2 {F : Type} [Field F] [Finite F] [CharP F 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)}
    (hA : IsElemAbelian p A) : Nat.card A ≤ p := by
  have : NeZero (p : F) := ⟨fun h0 => hp2
    ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp ((CharP.cast_eq_zero_iff F 2 p).mp h0)).symm⟩
  have hcyc : IsCyclic A := CFSG.RankThree.PartOne.K133.isCyclic_of_commuting_pow_eq_one_sl2 hp A
    (fun _ hx _ hy => TableB.IsElemAbelian.comm hA hx hy) hA.2
  exact TableB.card_le_of_isCyclic hp.pos hcyc hA.2

theorem card_le_sq_of_isElemAbelian_prod {K₁ K₂ : Type} [Field K₁] [Finite K₁] [CharP K₁ 2]
    [Field K₂] [Finite K₂] [CharP K₂ 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K₁ × Matrix.SpecialLinearGroup (Fin 2) K₂)}
    (hE : IsElemAbelian p E) : Nat.card E ≤ p ^ 2 := by
  have h1 := card_le_of_isElemAbelian_sl2 hp hp2 (TableB.isElemAbelian_map hE (MonoidHom.fst _ _))
  have h2 := card_le_of_isElemAbelian_sl2 hp hp2 (TableB.isElemAbelian_map hE (MonoidHom.snd _ _))
  have : Finite (E.map (MonoidHom.fst _ _)) := Subtype.finite
  have : Finite (E.map (MonoidHom.snd _ _)) := Subtype.finite
  have hinj : Function.Injective (fun e : E =>
      ((⟨e.1.1, Subgroup.mem_map_of_mem _ e.2⟩ : E.map (MonoidHom.fst _ _)),
        (⟨e.1.2, Subgroup.mem_map_of_mem _ e.2⟩ : E.map (MonoidHom.snd _ _)))) := by
    intro x y hxy
    simp only [Prod.mk.injEq] at hxy
    exact Subtype.ext (Prod.ext (congrArg Subtype.val hxy.1) (congrArg Subtype.val hxy.2))
  calc Nat.card E ≤ Nat.card (E.map (MonoidHom.fst _ _) × E.map (MonoidHom.snd _ _)) :=
        Nat.card_le_card_of_injective _ hinj
    _ = Nat.card (E.map (MonoidHom.fst _ _)) * Nat.card (E.map (MonoidHom.snd _ _)) :=
        Nat.card_prod _ _
    _ ≤ p * p := Nat.mul_le_mul h1 h2
    _ = p ^ 2 := (sq p).symm

theorem card_le_sq_of_prod_sl2 {K₁ K₂ : Type} [Field K₁] [Finite K₁] [CharP K₁ 2]
    [Field K₂] [Finite K₂] [CharP K₂ 2] {C : Type} [Group C] [Finite C]
    (μ : Matrix.SpecialLinearGroup (Fin 2) K₁ × Matrix.SpecialLinearGroup (Fin 2) K₂ →* C)
    (hμ : Function.Injective μ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hord : (Nat.card C).factorization p =
      (Nat.card (Matrix.SpecialLinearGroup (Fin 2) K₁)).factorization p +
        (Nat.card (Matrix.SpecialLinearGroup (Fin 2) K₂)).factorization p)
    {E : Subgroup C} (hE : IsElemAbelian p E) : Nat.card E ≤ p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain PH : Sylow p
      (Matrix.SpecialLinearGroup (Fin 2) K₁ × Matrix.SpecialLinearGroup (Fin 2) K₂) := default
  have hP₀card : Nat.card ((PH : Subgroup _).map μ) = p ^ (Nat.card C).factorization p := by
    rw [Subgroup.card_map_of_injective hμ, Sylow.card_eq_multiplicity PH, Nat.card_prod,
      Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply, hord]
  let S : Sylow p C := Sylow.ofCard _ hP₀card
  obtain ⟨Q, hEQ⟩ := (TableB.isPGroup_of_isElemAbelian hE).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C Q S
  have hmem : ∀ e ∈ E, g * e * g⁻¹ ∈ (PH : Subgroup _).map μ := by
    intro e he
    have h1 : g * e * g⁻¹ ∈ ((g • Q : Sylow p C) : Subgroup C) := by
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul e (MulAut.conj g) (Q : Subgroup C) (hEQ he)
    rw [hg] at h1
    exact h1
  set E₁ := E.map (MulAut.conj g).toMonoidHom with hE₁
  have hE₁ab : IsElemAbelian p E₁ := TableB.isElemAbelian_map hE _
  set E' := E₁.comap μ with hE'
  have hE'ab : IsElemAbelian p E' := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hμ ?_)⟩⟩, fun x hx => hμ ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hE₁ab a.2 b.2
    · rw [map_pow, map_one]
      exact hE₁ab.2 _ hx
  have hle : E₁ ≤ μ.range := by
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨y, -, hy⟩ := Subgroup.mem_map.mp (hmem e he)
    exact ⟨y, hy⟩
  have hcard : Nat.card E' = Nat.card E := by
    have h1 : E'.map μ = E₁ := by
      rw [hE', Subgroup.map_comap_eq, inf_eq_right.mpr hle]
    rw [← Subgroup.card_map_of_injective hμ, h1, hE₁,
      Subgroup.card_map_of_injective (MulAut.conj g).injective]
  rw [← hcard]
  exact card_le_sq_of_isElemAbelian_prod hp hp2 hE'ab

end SL2

theorem factorization_card_triD4 {q p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hq : 2 ≤ q)
    (hpq : ¬ p ∣ q) (hd : p ∣ q ^ 2 - 1) :
    (q ^ 12 * (q ^ 2 - 1) * (q ^ 6 - 1) * (q ^ 8 + q ^ 4 + 1)).factorization p =
      (q ^ 3 * ((q ^ 3) ^ 2 - 1)).factorization p + (q * (q ^ 2 - 1)).factorization p := by
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hmod : q ^ 2 ≡ 1 [MOD p] := ((Nat.modEq_iff_dvd' h1).2 hd).symm
  have h4 : q ^ 4 ≡ 1 [MOD p] := by
    simpa [← pow_mul] using hmod.pow 2
  have h8 : q ^ 8 ≡ 1 [MOD p] := by
    simpa [← pow_mul] using hmod.pow 4
  have hmod8 : q ^ 8 + q ^ 4 + 1 ≡ 3 [MOD p] := (h8.add h4).add_right 1
  have hp3 : ¬ p ∣ q ^ 8 + q ^ 4 + 1 := by
    intro h
    have h3 : p ∣ 3 := Nat.modEq_zero_iff_dvd.1 ((Nat.modEq_zero_iff_dvd.2 h).symm.trans hmod8).symm
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  have hq0 : ¬ p ∣ q ^ 8 := fun h => hpq (hp.dvd_of_dvd_pow h)
  have e : q ^ 12 * (q ^ 2 - 1) * (q ^ 6 - 1) * (q ^ 8 + q ^ 4 + 1) =
      (q ^ 3 * ((q ^ 3) ^ 2 - 1)) * (q * (q ^ 2 - 1)) * (q ^ 8 * (q ^ 8 + q ^ 4 + 1)) := by
    rw [show (q ^ 3) ^ 2 = q ^ 6 by ring]
    ring
  have hA : q ^ 3 * ((q ^ 3) ^ 2 - 1) ≠ 0 := by
    have : 1 < (q ^ 3) ^ 2 := Nat.one_lt_pow (by norm_num) (Nat.one_lt_pow (by norm_num) (by omega))
    have : 0 < (q ^ 3) ^ 2 - 1 := by omega
    positivity
  have hB : q * (q ^ 2 - 1) ≠ 0 := by
    have : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
    have : 0 < q ^ 2 - 1 := by omega
    positivity
  have hC : q ^ 8 * (q ^ 8 + q ^ 4 + 1) ≠ 0 := by positivity
  rw [e, Nat.factorization_mul (mul_ne_zero hA hB) hC, Nat.factorization_mul hA hB,
    Finsupp.add_apply, Finsupp.add_apply]
  have hz : (q ^ 8 * (q ^ 8 + q ^ 4 + 1)).factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (fun h => by
      rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact hq0 h
      · exact hp3 h)
  rw [hz, add_zero]

theorem dvd_or_of_largeEvenSplit_triD4 {p : ℕ} {lab : LargeEvenLabel} (ht : lab.tag = .triD4)
    (hs : LargeEvenSplit p lab) : p ∣ 2 ^ lab.n - 1 ∨ (lab.n = 1 ∧ p = 3) := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hs ⊢
  subst ht
  rcases hs with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, h⟩ | h
  · exact absurd h id
  · exact absurd rfl h
  · exact Or.inl h
  · exact Or.inr h

section TriD4


theorem card_le_sq_D4_split {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hd : p ∣ (2 ^ f) ^ 2 - 1)
    {E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} (hE : IsElemAbelian p E) :
    Nat.card E ≤ p ^ 2 := by
  classical
  have hp2 : p ≠ 2 := by omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega : 1 ≤ 3 * f) hK3
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have : Fintype K := Fintype.ofFinite K
  have hσ3 : σ ^ 3 = 1 := by
    ext c
    have h3 : σ (σ (σ c)) = c := by
      rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul]
      have hpc := FiniteField.pow_card c
      rw [Fintype.card_eq_nat_card, hK] at hpc
      rw [show 2 ^ f * (2 ^ f * 2 ^ f) = (2 ^ f) ^ 3 by ring]
      exact hpc
    rw [ringEquiv_pow_three_apply, h3]
    rfl
  obtain ⟨ι, η, hι, hη, hcomm⟩ := triality_D4_commuting_faithful_extension_and_fixed_SL2 K σ hσ3
  have hkc : Nat.card (fixSubfield σ) = 2 ^ f :=
    CFSG.RankThree.PartOne.card_fixSubfield_cube_row Nat.prime_two hf hK σ hσ
  have hq2 : 2 ≤ 2 ^ f :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hpq : ¬ p ∣ 2 ^ f := fun h =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  have : CharP (fixSubfield σ) 2 := inferInstance
  let μ : SL2 K × SL2 (fixSubfield σ) →* graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    MonoidHom.noncommCoprod ι η (fun A B => hcomm A B)
  have hμapply : ∀ A B, μ (A, B) = ι A * η B := fun A B => rfl
  have hμ : Function.Injective μ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨A, B⟩ hAB
    rw [hμapply] at hAB
    have hA : ι A = (η B)⁻¹ := eq_inv_of_mul_eq_one_left hAB
    have hAc : A ∈ Subgroup.center (SL2 K) := by
      rw [Subgroup.mem_center_iff]
      intro A'
      apply hι
      rw [map_mul, map_mul, hA]
      exact (Commute.inv_right (hcomm A' B : Commute (ι A') (η B))).eq
    rw [CFSG.RankThree.PartOne.S15K.center_sl2_eq_bot, Subgroup.mem_bot] at hAc
    subst hAc
    rw [map_one, one_mul] at hAB
    have hB : B = 1 := (injective_iff_map_eq_one η).1 hη B hAB
    subst hB
    rfl
  have hCcard := (triality_both_orientations_exact_finite_order 2 f Nat.prime_two hf K hK 1
    (Or.inl rfl) σ.toRingHom (fun c => by rw [pow_one]; exact hσ c)).1
  have hord : (Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).factorization p =
      (Nat.card (SL2 K)).factorization p + (Nat.card (SL2 (fixSubfield σ))).factorization p := by
    rw [hCcard, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two K,
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two (fixSubfield σ), hK, hkc]
    exact factorization_card_triD4 hp hp5 hq2 hpq hd
  exact card_le_sq_of_prod_sl2 μ hμ hp hp2 hord hE

@[expose] def GGTriD4ThreeRankInput : Prop :=
  ∀ n : ℕ, 1 ≤ n → (3 ∣ 2 ^ n - 1 ∨ n = 1) → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = (2 ^ n) ^ 3 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ 2 ^ n) →
    ∀ E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), IsElemAbelian 3 E →
      Nat.card E < 3 ^ 3

theorem nonempty_triD4_equiv {n : ℕ} (hn : 1 ≤ n) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) :
    Nonempty (LargeEvenCenterQuot (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n) ≃*
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  obtain ⟨-, -, -, -, -, -, -, ⟨e₂⟩⟩ :=
    even_triality_exact_automorphism_normal_form hn K hK σ hσ
  obtain ⟨e₁⟩ := centerQuot_twistedH_equiv K .D4 n σ.toRingHom hσ
  exact ⟨e₁.trans e₂⟩

theorem largeEvenLabelAll_card_lt_triD4 {p : ℕ} (h3 : p = 3 → GGTriD4ThreeRankInput)
    {lab : LargeEvenLabel} (hp : p.Prime) (hlab : LargeEvenInLambda2 lab)
    (ht : lab.tag = .triD4) (hs : LargeEvenSplit p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 := by
  have hsplit := dvd_or_of_largeEvenSplit_triD4 ht hs
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hlab hsplit
  subst ht
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  refine ⟨K, i1, i2, hK, hq, fun X hXI hX => ?_⟩
  have : CharP K 2 := charP_two_of_card (m := n * 3) (by rw [hK, pow_mul])
  set σ := iterateFrobeniusEquiv K 2 n with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => by
    rw [hσdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  obtain ⟨e⟩ := nonempty_triD4_equiv hn K hK σ hσ
  obtain ⟨-, -, -, -, -, -, hZC, -⟩ := even_triality_exact_automorphism_normal_form hn K hK σ hσ
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have : Finite (LargeEvenCenterQuot (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n)) :=
    Finite.of_equiv _ e.symm.toEquiv
  have hI := chevIDImage_subset_inn_triD4 hn K hK
  have hbound : ∀ E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      IsElemAbelian p E → Nat.card E < p ^ 3 := by
    intro E hE
    by_cases hp3 : p = 3
    · subst hp3
      refine h3 rfl n hn ?_ K hK σ hσ E hE
      rcases hsplit with h | h
      · exact Or.inl h
      · exact Or.inr h.1
    · have hpn : p ∣ 2 ^ n - 1 := by
        rcases hsplit with h | h
        · exact h
        · exact absurd h.2 hp3
      have hp2 : p ≠ 2 := ne_two_of_dvd_two_pow_sub_one hn hpn
      have hp5 : 5 ≤ p := by
        have h2 := hp.two_le
        have h4 : p ≠ 4 := by
          rintro rfl
          exact absurd hp (by decide)
        omega
      have hd : p ∣ (2 ^ n) ^ 2 - 1 := by
        have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        have e2 : (2 ^ n) ^ 2 - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
          zify [h1, Nat.one_le_pow 2 (2 ^ n) h1]
          ring
        rw [e2]
        exact dvd_mul_of_dvd_left hpn _
      exact (card_le_sq_D4_split hn K hK σ hσ hp hp5 hd hE).trans_lt
        (Nat.pow_lt_pow_right hp.one_lt (by norm_num))
  refine card_lt_of_subset_inn (center_eq_bot_of_mulEquiv e hZC)
    (fun A hA => card_lt_of_mulEquiv e hbound hA) (fun φ hφ => ?_) hX
  obtain ⟨r, hr⟩ := hI (hXI hφ)
  exact ⟨r, hr⟩

end TriD4

end TableBExcSmallRest

end CFSG.StandardType

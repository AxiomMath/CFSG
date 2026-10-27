module

public import CFSG.Quasithin.H13.NQBlockTwoPrimeExceptional
public import CFSG.RankThree.Chevalley.SteinbergCFExceptionalModelCover
public import CFSG.Quasithin.H13.QRCEvenRankTwoOddCyclic
public import CFSG.Quasithin.SteinbergCDLargeReeOddCyclic
public import CFSG.LieType.Ree.LargeReeModelSchreier
public import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped Pointwise

theorem eq_five_of_sq_dvd_card_tits {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h : p ^ 2 ∣ 17971200) : p = 5 := by
  have e : (17971200 : ℕ) = 2 ^ 11 * 3 ^ 3 * 5 ^ 2 * 13 := by norm_num
  rw [e] at h
  have h1 : p ∣ 2 ^ 11 * 3 ^ 3 * 5 ^ 2 * 13 := (dvd_pow_self p two_ne_zero).trans h
  have hq : ∀ q : ℕ, q.Prime → p ∣ q → p = q := fun q hq hpq =>
    (Nat.prime_dvd_prime_iff_eq hp hq).1 hpq
  rcases (Nat.Prime.dvd_mul hp).1 h1 with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h1 | h1
    · rcases (Nat.Prime.dvd_mul hp).1 h1 with h1 | h1
      · have := hq 2 Nat.prime_two (hp.dvd_of_dvd_pow h1)
        omega
      · have := hq 3 Nat.prime_three (hp.dvd_of_dvd_pow h1)
        omega
    · exact hq 5 (by norm_num) (hp.dvd_of_dvd_pow h1)
  · have := hq 13 (by norm_num) h1
    subst this
    exact absurd h (by norm_num)

theorem exists_ringEquiv_pow_eq_one_of_frobenius' {K : Type} [Field K] {q m : ℕ}
    (hK : Nat.card K = q ^ m) (hq : 0 < q) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ q) :
    ∃ σ' : K ≃+* K, σ'.toRingHom = σ ∧ σ' ^ m = 1 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hq m).ne')
  have : Fintype K := Fintype.ofFinite K
  set σ' : K ≃+* K :=
    RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  have hσ' : ∀ c, σ' c = σ c := fun _ => rfl
  have hpow : ∀ n : ℕ, ∀ c, (σ' ^ n) c = c ^ (q ^ n) := by
    intro n
    induction n with
    | zero => intro c; rw [pow_zero, pow_zero, pow_one, RingAut.one_apply]
    | succ n ih =>
      intro c
      rw [pow_succ σ' n, RingAut.mul_apply, ih, hσ', hσ, ← pow_mul, ← pow_succ']
  refine ⟨σ', RingHom.ext hσ', RingEquiv.ext fun c => ?_⟩
  rw [hpow, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card, RingAut.one_apply]

section ExceptionalExclusions

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag

variable {S : Type} [Group S] [Finite S] [IsSimpleGroup S]

theorem isCyclic_of_even_exceptional_model
    (hnab : ∃ a b : S, a * b ≠ b * a) {T B : Subgroup S} (hT : quasithinIsSylowTwo T)
    (hB : B ∈ cComp (B ⊔ T)) (hBq : ¬ CFSG.IsQuasisimple (↥B ⧸ CFSG.pCore 2 ↥B))
    (hmod : (∃ f : ℕ, 2 ≤ f ∧ ChevalleyExceptionalModel S .G2 2 f) ∨
      (∃ f : ℕ, 1 ≤ f ∧ ChevalleyExceptionalModel S .trialityD4 2 f) ∨
      (∃ a : ℕ, 1 ≤ a ∧ ReeTitsModel S .twistedF4 2 (2 * a + 1)))
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {E : Subgroup S} (hEB : E ≤ B) (hE : IsPGroup r E) :
    IsCyclic E := by
  have hBperf : Group.IsPerfect B := Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp hB)
  have hBT := sup_lt_top_of_not_quasisimple hnab hB hBq
  rcases hmod with ⟨f, hf2, hG2⟩ | ⟨f, hf1, hD4⟩ | ⟨a, ha, hF4⟩
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hG2
    have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hK
    let D : RootWeightDatum K := .ordinary .G2
    have e' : S ≃* D.group := e.trans (CFSG.RankThree.Chevalley.adjointQuotientEquiv .G2 K)
    exact isCyclic_of_proper_sylow_overgroup_transport e'
      (fun T' B' hT' hB'Γ hB'p hB'T r hr hr2 E' hE'B hE' =>
        (QRC.even_rank_two_proper_Sylow_overgroup_perfect_subgroups_have_cyclic_odd_subgroups
          (k := K)).2.2 D rfl T' B' hT' hB'Γ hB'p hB'T r hr hr2 E' hE'B hE')
      hT hBperf hBT hr hr2 hEB hE
  · obtain ⟨-, K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hD4
    obtain ⟨E0⟩ := CFSG.RankThree.Chevalley.nonempty_derivedCentralQuotient_equiv .D4
      Nat.prime_two hf1 K hK σ hσ
    have hK' : Nat.card K = 2 ^ (f * TwistTag.D4.order) := by rw [hK, ← pow_mul]
    have ht0 : 0 < TwistTag.D4.order := by decide
    have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (Nat.mul_pos hf1 ht0) hK'
    obtain ⟨σ', hσσ, hσ1⟩ := exists_ringEquiv_pow_eq_one_of_frobenius'
      hK (pow_pos two_pos f) σ hσ
    subst hσσ
    let D : RootWeightDatum K := .fixed .D4 σ' hσ1
    have e' : S ≃* D.group := e.trans E0
    exact isCyclic_of_proper_sylow_overgroup_transport e'
      (fun T' B' hT' hB'Γ hB'p hB'T r hr hr2 E' hE'B hE' =>
        (QRC.even_rank_two_proper_Sylow_overgroup_perfect_subgroups_have_cyclic_odd_subgroups
          (k := K)).2.2 D rfl T' B' hT' hB'Γ hB'p hB'T r hr hr2 E' hE'B hE')
      hT hBperf hBT hr hr2 hEB hE
  · obtain ⟨-, -, -, hp2, -, hiso⟩ := ReeTag.large_Ree_model_Schreier _ 2 (2 * a + 1) hF4
    obtain ⟨-, a', hfa', K, _, _, hK, hw⟩ := hF4
    have ha' : a' = a := by omega
    subst ha'
    have : CharP K ReeTag.F4.prime :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        Nat.prime_two (by omega) hK
    obtain ⟨θ⟩ := hiso a' K hfa' hK hw
    exact isCyclic_of_proper_sylow_overgroup_transport θ
      (fun T' B' hT' _ hB'p hB'T r hr hr2 E' hE'B hE' =>
        SteinbergCD.large_Ree_proper_sylow_overgroup_perfect_odd_cyclic ha hK hT' hB'p hB'T hr hr2
          hE'B hE')
      hT hBperf hBT hr hr2 hEB hE

end ExceptionalExclusions

section OnePrime

variable {K : Type} [Group K] [Finite K]

theorem quasisimple_ambient_local_Ccomponent_supports_at_most_one_original_rank_two_prime_of
    (hCat : QTESylow.StmtCatalogNoncyclicPrimeSylowProduct) (hPL3 : PrimeLinearThreeAmbientPrime)
    (hK : CFSG.SectionRank.IsSQTKCat K) (hQ : CFSG.IsQuasisimple (K ⧸ CFSG.pCore 2 K))
    {T A : Subgroup K} (hT : quasithinIsSylowTwo T) (hA : A ∈ cComp (A ⊔ T))
    (hAq : ¬ CFSG.IsQuasisimple (↥A ⧸ CFSG.pCore 2 ↥A)) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp5 : 5 ≤ p) (hq5 : 5 ≤ q) {Xp Xq : Subgroup K}
    (hXpA : Xp ≤ A) (hXpn : (Xp.subgroupOf A).Normal) (hTXp : T ≤ normalizer (Xp : Set K))
    (hXp2 : ∀ (N : Subgroup Xp) [N.Normal], IsPGroup 2 (Xp ⧸ N) → N = ⊤)
    (hXpp : IsPGroup p (Xp ⧸ CFSG.pCore 2 Xp)) (hXpr : CFSG.pRank p (Xp ⧸ CFSG.pCore 2 Xp) = 2)
    (hXqA : Xq ≤ A) (hXqn : (Xq.subgroupOf A).Normal) (hTXq : T ≤ normalizer (Xq : Set K))
    (hXq2 : ∀ (N : Subgroup Xq) [N.Normal], IsPGroup 2 (Xq ⧸ N) → N = ⊤)
    (hXqp : IsPGroup q (Xq ⧸ CFSG.pCore 2 Xq)) (hXqr : CFSG.pRank q (Xq ⧸ CFSG.pCore 2 Xq) = 2) :
    p = q := by
  by_contra hpq
  have halt := two_original_prime_witnesses_force_exceptional_simple_ambient_quotient_of hCat hPL3
    hK hQ hT hA hAq hp hq hp5 hq5 hpq hXpA hXpn hTXp hXp2 hXpp hXpr hXqA hXqn hTXq hXq2 hXqp hXqr
  obtain ⟨⟨hsimple, hnab⟩, -, -, -, hTb, hAb, hAbq, -⟩ :=
    NQTerm.quasisimple_two_core_ambient_simple_quotient_retains_original_local_witnesses hK hQ hT
      hA hAq
  have := hsimple
  obtain ⟨hXpB, -, -, -, -, Up, hUpX, hUp, hUpnc, -⟩ :=
    ambient_witness_data hK hQ hT hA hAq hp hp5 hXpA hXpn hTXp hXp2 hXpp hXpr
  obtain ⟨-, -, -, -, -, Uq, -, hUq, hUqnc, -⟩ :=
    ambient_witness_data hK hQ hT hA hAq hq hq5 hXqA hXqn hTXq hXq2 hXqp hXqr
  rcases halt with hG2 | hD4 | hF4 | hTits
  · exact hUpnc (isCyclic_of_even_exceptional_model hnab hTb hAb hAbq (Or.inl hG2) hp
      (by omega) (hUpX.trans hXpB) hUp)
  · exact hUpnc (isCyclic_of_even_exceptional_model hnab hTb hAb hAbq (Or.inr (Or.inl hD4)) hp
      (by omega) (hUpX.trans hXpB) hUp)
  · exact hUpnc (isCyclic_of_even_exceptional_model hnab hTb hAb hAbq (Or.inr (Or.inr hF4)) hp
      (by omega) (hUpX.trans hXpB) hUp)
  · obtain ⟨eT⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv (h := hTits)
    have hcard := (Nat.card_congr eT.toEquiv).trans CFSG.Sporadic.Schreier.Tits.card_titsD
    have h5p : p = 5 := eq_five_of_sq_dvd_card_tits hp hp5 (by
      rw [← hcard]
      exact (sq_dvd_card_of_not_isCyclic' hp hUp hUpnc).trans (Subgroup.card_subgroup_dvd_card Up))
    have h5q : q = 5 := eq_five_of_sq_dvd_card_tits hq hq5 (by
      rw [← hcard]
      exact (sq_dvd_card_of_not_isCyclic' hq hUq hUqnc).trans (Subgroup.card_subgroup_dvd_card Uq))
    exact hpq (h5p.trans h5q.symm)


theorem stmtQuasisimpleAmbientOneRankTwoPrime_of
    (hCat : QTESylow.StmtCatalogNoncyclicPrimeSylowProduct) (hPL3 : PrimeLinearThreeAmbientPrime) :
    StmtQuasisimpleAmbientOneRankTwoPrime :=
  fun _ _ _ hK hQ _ _ hT hA hAq _ _ hp hq hp5 hq5 _ _ hXpA hXpn hTXp hXp2 hXpp hXpr hXqA hXqn hTXq
    hXq2 hXqp hXqr =>
    quasisimple_ambient_local_Ccomponent_supports_at_most_one_original_rank_two_prime_of hCat hPL3
      hK hQ hT hA hAq hp hq hp5 hq5 hXpA hXpn hTXp hXp2 hXpp hXpr hXqA hXqn hTXq hXq2 hXqp hXqr

end OnePrime

end CFSG.Quasithin.H13.NQBlock

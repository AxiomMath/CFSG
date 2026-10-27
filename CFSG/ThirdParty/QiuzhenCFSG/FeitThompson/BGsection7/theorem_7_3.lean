module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection7.theorem_7_2
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj

namespace CFSG
end CFSG
open CFSG
/-! # Theorem 7.3 from BG Section 7 -/

open scoped Pointwise

section

variable {G : Type*} [Group G] [Finite G]

private theorem CFSG.primeRank_le_card {R : Type*} [Group R] [Finite R] (q : ℕ) :
    primeRank q R ≤ Nat.card R := by
  let S : Set ℕ :=
    {n : ℕ | ∃ A : Subgroup R, IsPGroup q A ∧ IsMulCommutative A ∧ n ≤ generatorRank A}
  have hSbdd : BddAbove S := by
    refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨A, _hAq, _hAcomm, hnA⟩
    exact le_trans hnA (le_trans (generatorRank_le_card_local (H := A)) (Subgroup.card_le_card_group A))
  by_cases hS : S.Nonempty
  · have hsSup_mem : sSup S ∈ S := Nat.sSup_mem hS hSbdd
    rcases hsSup_mem with ⟨A, _hAq, _hAcomm, hsSup_le⟩
    rw [primeRank]
    exact le_trans hsSup_le (le_trans (generatorRank_le_card_local (H := A)) (Subgroup.card_le_card_group A))
  · have hSempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    have hSet :
        {n : ℕ | ∃ A : Subgroup R, IsPGroup q A ∧ IsMulCommutative A ∧ n ≤ generatorRank A} =
          ∅ := by
      simpa [S] using hSempty
    rw [primeRank, hSet]
    simp

private theorem CFSG.exists_pSubgroup_two_le_generatorRank_of_one_lt_groupRank
    {R : Type*} [Group R] [Finite R] (hrank : 1 < groupRank R) :
    ∃ p : Nat.Primes, ∃ B : Subgroup R,
      IsPGroup p.val B ∧ IsMulCommutative B ∧ 2 ≤ generatorRank B := by
  let S : Set ℕ := {n : ℕ | ∃ q : ℕ, Nat.Prime q ∧ n ≤ primeRank q R}
  have hrank' : 1 < sSup S := by
    simpa [groupRank, S] using hrank
  have hSbdd : BddAbove S := by
    refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨q, _hqprime, hnq⟩
    exact le_trans hnq (primeRank_le_card (R := R) q)
  have hSnonempty : S.Nonempty := by
    by_contra hS
    have hSempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    have : ¬ 1 < sSup S := by simp [hSempty]
    exact this hrank'
  have hsSup_mem : sSup S ∈ S := Nat.sSup_mem hSnonempty hSbdd
  rcases hsSup_mem with ⟨q, hqprime, hsSup_le⟩
  have hqrank : 1 < primeRank q R := lt_of_lt_of_le hrank' hsSup_le
  let T : Set ℕ :=
    {n : ℕ | ∃ B : Subgroup R, IsPGroup q B ∧ IsMulCommutative B ∧ n ≤ generatorRank B}
  have hqrank' : 1 < sSup T := by
    simpa [primeRank, T] using hqrank
  have hTbdd : BddAbove T := by
    refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨B, _hBq, _hBcomm, hnB⟩
    exact le_trans hnB (le_trans (generatorRank_le_card_local (H := B)) (Subgroup.card_le_card_group B))
  have hTnonempty : T.Nonempty := by
    by_contra hT
    have hTempty : T = ∅ := Set.not_nonempty_iff_eq_empty.mp hT
    have : ¬ 1 < sSup T := by simp [hTempty]
    exact this hqrank'
  have htSup_mem : sSup T ∈ T := Nat.sSup_mem hTnonempty hTbdd
  rcases htSup_mem with ⟨B, hBq, hBcomm, htSup_le⟩
  refine ⟨⟨q, hqprime⟩, B, hBq, hBcomm, ?_⟩
  exact Nat.succ_le_of_lt (lt_of_lt_of_le hqrank' htSup_le)

public theorem CFSG.theorem_7_3
    {G : Type*} [Group G] [Finite G] [IsMinCE G]
    {A : Subgroup G} (hA : Hypothesis7_1 A)
    {q : Nat.Primes} (hq : q ∉ subgroupPrimeSet A)
    (hcenterRank : 2 ≤ groupRank (Subgroup.center A))
    (hqCent : q ∈ subgroupPrimeSet (Subgroup.centralizer (A : Set G))) :
    ConjugationActionTransitiveOn (section7K A)
      (section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes)) := by
  intro Q₁ hQ₁ Q₂ hQ₂
  have hQ₁fam : Q₁ ∈ section7HFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes) :=
    section7HStarFamily.mem_family hQ₁
  have hQ₂fam : Q₂ ∈ section7HFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes) :=
    section7HStarFamily.mem_family hQ₂
  letI : Fact q.val.Prime := ⟨q.2⟩
  let C : Subgroup G := Subgroup.centralizer (A : Set G)
  let S₀ : Sylow q.val C := Classical.choice (Sylow.nonempty (p := q.val) (G := C))
  have hS₀_ne_bot : (S₀ : Subgroup C) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card (G := C) (p := q.val) S₀ hqCent
  let S : Subgroup G := (S₀ : Subgroup C).map C.subtype
  have hS_le_C : S ≤ C := by
    simpa [S, C] using (Subgroup.map_subtype_le (H := C) (K := (S₀ : Subgroup C)))
  have hS_ne_bot : S ≠ ⊥ := by
    intro hSbot
    exact hS₀_ne_bot <|
      (Subgroup.map_eq_bot_iff_of_injective
        (H := (S₀ : Subgroup C)) (f := C.subtype) C.subtype_injective).1 (by
          simpa [S] using hSbot)
  have hS_q : IsPGroup q.val S := by
    simpa [S] using IsPGroup.map (p := q.val) (H := (S₀ : Subgroup C)) S₀.isPGroup' C.subtype
  have hSfam : S ∈ section7HFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes) := by
    refine ⟨le_top, isPiSubgroup_singleton_of_isPGroup hS_q, ?_⟩
    exact (le_centralizer_of_le_centralizer hS_le_C).trans (centralizer_le_normalizer S)
  obtain ⟨R, hR, hS_le_R⟩ := exists_mem_section7HStarFamily_of_mem_family hSfam
  have hRfam : R ∈ section7HFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes) :=
    section7HStarFamily.mem_family hR
  have hR_ne_bot : R ≠ ⊥ := ne_bot_of_le_ne_bot hS_ne_bot hS_le_R
  have hQ₁_ne_bot : Q₁ ≠ ⊥ := by
    intro hQ₁bot
    have hRbot : R = ⊥ := by
      have hQ₁_le_R : Q₁ ≤ R := by
        simp [hQ₁bot]
      have hR_eq_Q₁ := hQ₁.2 R hQ₁_le_R hRfam
      rw [hQ₁bot] at hR_eq_Q₁
      exact hR_eq_Q₁
    exact hR_ne_bot hRbot
  have hQ₂_ne_bot : Q₂ ≠ ⊥ := by
    intro hQ₂bot
    have hRbot : R = ⊥ := by
      have hQ₂_le_R : Q₂ ≤ R := by
        simp [hQ₂bot]
      have hR_eq_Q₂ := hQ₂.2 R hQ₂_le_R hRfam
      rw [hQ₂bot] at hR_eq_Q₂
      exact hR_eq_Q₂
    exact hR_ne_bot hRbot
  letI : Nontrivial ↥Q₁ := Q₁.nontrivial_iff_ne_bot.mpr hQ₁_ne_bot
  letI : Nontrivial ↥Q₂ := Q₂.nontrivial_iff_ne_bot.mpr hQ₂_ne_bot
  have hcenterRank' : 1 < groupRank (Subgroup.center A) :=
    lt_of_lt_of_le (by decide : 1 < 2) hcenterRank
  obtain ⟨p, B, hBp, hBcomm, hBrank⟩ :=
    exists_pSubgroup_two_le_generatorRank_of_one_lt_groupRank
      (R := Subgroup.center A) hcenterRank'
  letI : Fact p.val.Prime := ⟨p.2⟩
  letI : CommGroup B := IsMulCommutative.instCommGroup
  letI : Fact (IsPGroup p.val B) := ⟨hBp⟩
  have hB_noncyc : ¬ IsCyclic B := not_isCyclic_of_two_le_generatorRank hBrank
  have hB_ne_bot : B ≠ ⊥ := by
    intro hBbot
    apply hB_noncyc
    subst hBbot
    infer_instance
  have hpA : p ∈ subgroupPrimeSet A :=
    prime_mem_subgroupPrimeSet_of_nontrivial_center_pSubgroup (A := A) hBp hB_ne_bot
  have hp_ne_q : p ≠ q := by
    intro hpq
    exact hq (hpq ▸ hpA)
  have hpval_ne_qval : p.val ≠ q.val := by
    intro hpq
    apply hp_ne_q
    exact Subtype.ext hpq
  have hQ₁q : IsPGroup q.val Q₁ := isPGroup_of_isPiSubgroup_singleton hQ₁fam.2.1
  have hQ₂q : IsPGroup q.val Q₂ := isPGroup_of_isPiSubgroup_singleton hQ₂fam.2.1
  obtain ⟨n₁, hQ₁card⟩ := hQ₁q.exists_card_eq
  obtain ⟨n₂, hQ₂card⟩ := hQ₂q.exists_card_eq
  let ιBA : B →* A := (Subgroup.center A).subtype.comp B.subtype
  haveI : Subgroup.Normalizes A Q₁ := ⟨hQ₁fam.2.2⟩
  letI : MulDistribMulAction (↥B) (↥Q₁) := MulDistribMulAction.compHom (↥Q₁) ιBA
  have hcopBQ₁ : Nat.Coprime p.val (Nat.card Q₁) := by
    rw [hQ₁card]
    simpa using Nat.coprime_pow_primes 1 n₁ p.2 q.2 hpval_ne_qval
  have hBQ₁fix_top :
      (⨆ (x : B) (_ : x ≠ 1), fixedPointSubgroup (↥(Subgroup.zpowers x)) ↥Q₁) = ⊤ := by
    simpa using proposition_1_16_a (G := ↥Q₁) (A := B) p.val hcopBQ₁ hB_noncyc
  obtain ⟨x₁, hx₁_ne, hx₁Q₁fix_nonbot⟩ :=
    exists_nontrivial_zpowers_fixedPoint_nonbot (A := B) (G := ↥Q₁) hBQ₁fix_top
  let x₁Center : Subgroup.center A := x₁
  let x₁A : A := x₁Center
  let x₁G : G := x₁A
  let H₁ : Subgroup G := Subgroup.centralizer ({x₁G} : Set G)
  have hAH₁ : A ≤ H₁ := by
    simpa [H₁, x₁G, x₁A] using le_centralizer_singleton_of_mem_center (A := A) x₁Center
  have hx₁G_ne : x₁G ≠ 1 := by
    intro hx₁G_eq
    apply hx₁_ne
    apply Subtype.ext
    simpa [x₁G, x₁A, x₁Center] using hx₁G_eq
  have hH₁proper : H₁ ≠ ⊤ :=
    centralizer_singleton_ne_top_of_ne_one (G := G) (z := x₁G) hx₁G_ne
  have hH₁Q₁ : H₁ ⊓ Q₁ ≠ ⊥ := by
    rcases Subgroup.ne_bot_iff_exists_ne_one.mp hx₁Q₁fix_nonbot with ⟨x, hxne⟩
    let x₁gen : Subgroup.zpowers x₁ := ⟨x₁, Subgroup.mem_zpowers x₁⟩
    have hxx₁fix := x.2 x₁gen
    change x₁A • (x : Q₁) = (x : Q₁) at hxx₁fix
    have hxconj : x₁G * (x : G) * x₁G⁻¹ = (x : G) := by
      simpa [x₁gen, x₁G, x₁A, x₁Center, ιBA,
        Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hQ₁fam.2.2] using
        congrArg Subtype.val hxx₁fix
    have hxcomm : (x : G) * x₁G = x₁G * (x : G) := by
      have hxcomm' : x₁G * (x : G) = (x : G) * x₁G := by
        have := congrArg (fun t : G => t * x₁G) hxconj
        simpa [mul_assoc] using this
      exact hxcomm'.symm
    have hxH₁ : (x : G) ∈ H₁ := by
      change (x : G) ∈ Subgroup.centralizer ({x₁G} : Set G)
      exact Subgroup.mem_centralizer_singleton_iff.mpr hxcomm
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr ?_
    refine ⟨⟨(x : G), ⟨hxH₁, (x : Q₁).2⟩⟩, ?_⟩
    intro hxone
    apply hxne
    apply Subtype.ext
    apply Subtype.ext
    simpa using congrArg Subtype.val hxone
  have hS_le_H₁ : S ≤ H₁ := by
    intro s hs
    change s ∈ Subgroup.centralizer ({x₁G} : Set G)
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (hS_le_C hs) x₁G x₁A.property).symm
  have hH₁R : H₁ ⊓ R ≠ ⊥ := by
    refine ne_bot_of_le_ne_bot hS_ne_bot ?_
    intro s hs
    exact ⟨hS_le_H₁ hs, hS_le_R hs⟩
  obtain ⟨f, hf⟩ := lemma_7_1 hA hq hQ₁ hR hAH₁ hH₁proper hH₁Q₁ hH₁R
  haveI : Subgroup.Normalizes A Q₂ := ⟨hQ₂fam.2.2⟩
  letI : MulDistribMulAction (↥B) (↥Q₂) := MulDistribMulAction.compHom (↥Q₂) ιBA
  have hcopBQ₂ : Nat.Coprime p.val (Nat.card Q₂) := by
    rw [hQ₂card]
    simpa using Nat.coprime_pow_primes 1 n₂ p.2 q.2 hpval_ne_qval
  have hBQ₂fix_top :
      (⨆ (x : B) (_ : x ≠ 1), fixedPointSubgroup (↥(Subgroup.zpowers x)) ↥Q₂) = ⊤ := by
    simpa using proposition_1_16_a (G := ↥Q₂) (A := B) p.val hcopBQ₂ hB_noncyc
  obtain ⟨x₂, hx₂_ne, hx₂Q₂fix_nonbot⟩ :=
    exists_nontrivial_zpowers_fixedPoint_nonbot (A := B) (G := ↥Q₂) hBQ₂fix_top
  let x₂Center : Subgroup.center A := x₂
  let x₂A : A := x₂Center
  let x₂G : G := x₂A
  let H₂ : Subgroup G := Subgroup.centralizer ({x₂G} : Set G)
  have hAH₂ : A ≤ H₂ := by
    simpa [H₂, x₂G, x₂A] using le_centralizer_singleton_of_mem_center (A := A) x₂Center
  have hx₂G_ne : x₂G ≠ 1 := by
    intro hx₂G_eq
    apply hx₂_ne
    apply Subtype.ext
    simpa [x₂G, x₂A, x₂Center] using hx₂G_eq
  have hH₂proper : H₂ ≠ ⊤ :=
    centralizer_singleton_ne_top_of_ne_one (G := G) (z := x₂G) hx₂G_ne
  have hH₂Q₂ : H₂ ⊓ Q₂ ≠ ⊥ := by
    rcases Subgroup.ne_bot_iff_exists_ne_one.mp hx₂Q₂fix_nonbot with ⟨x, hxne⟩
    let x₂gen : Subgroup.zpowers x₂ := ⟨x₂, Subgroup.mem_zpowers x₂⟩
    have hxx₂fix := x.2 x₂gen
    change x₂A • (x : Q₂) = (x : Q₂) at hxx₂fix
    have hxconj : x₂G * (x : G) * x₂G⁻¹ = (x : G) := by
      simpa [x₂gen, x₂G, x₂A, x₂Center, ιBA,
        Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hQ₂fam.2.2] using
        congrArg Subtype.val hxx₂fix
    have hxcomm : (x : G) * x₂G = x₂G * (x : G) := by
      have hxcomm' : x₂G * (x : G) = (x : G) * x₂G := by
        have := congrArg (fun t : G => t * x₂G) hxconj
        simpa [mul_assoc] using this
      exact hxcomm'.symm
    have hxH₂ : (x : G) ∈ H₂ := by
      change (x : G) ∈ Subgroup.centralizer ({x₂G} : Set G)
      exact Subgroup.mem_centralizer_singleton_iff.mpr hxcomm
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr ?_
    refine ⟨⟨(x : G), ⟨hxH₂, (x : Q₂).2⟩⟩, ?_⟩
    intro hxone
    apply hxne
    apply Subtype.ext
    apply Subtype.ext
    simpa using congrArg Subtype.val hxone
  have hS_le_H₂ : S ≤ H₂ := by
    intro s hs
    change s ∈ Subgroup.centralizer ({x₂G} : Set G)
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (hS_le_C hs) x₂G x₂A.property).symm
  have hH₂R : H₂ ⊓ R ≠ ⊥ := by
    refine ne_bot_of_le_ne_bot hS_ne_bot ?_
    intro s hs
    exact ⟨hS_le_H₂ hs, hS_le_R hs⟩
  obtain ⟨g, hg⟩ := lemma_7_1 hA hq hR hQ₂ hAH₂ hH₂proper hH₂R hH₂Q₂
  refine ⟨g * f, ?_⟩
  calc
    Q₂ = R.conjBy (g : G) := hg
    _ = (Q₁.conjBy (f : G)).conjBy (g : G) := by rw [hf]
    _ = Q₁.conjBy ((g : G) * (f : G)) := by rw [Subgroup.conjBy_conjBy]
    _ = Q₁.conjBy ((g * f : section7K A) : G) := by simp

end

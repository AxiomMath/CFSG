module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailRecogAbstract
public import CFSG.RankThree.GF2n.Stroth80.Sec7ArtinOrders
public import CFSG.GH74.Orders.Sporadic
public import CFSG.Adapters.StatedSmallProjOrders

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

@[expose] def Tim77Cor2AlphaExtra (X : Type) [Group X] : Prop :=
  (∃ m : ℕ, 1 ≤ m ∧ CFSG.Blueprint.LieModel X .G2 0 2 m) ∨
  StatedClassicalModel X .PSU 3 3 1 ∨
  (∃ m : ℕ, 1 ≤ m ∧ CFSG.Blueprint.LieModel X .trialityD4 0 2 m) ∨
  CFSG.Blueprint.NativeSporadic.IsSporadic X .J2

@[expose] def OutSolvableAlphaStatement : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Tim77Cor2AlphaExtra X → (∃ a b : X, a * b ≠ b * a) →
    ∀ P : Subgroup (MulAut X), commutator ↥P = ⊤ →
      P ≤ (MulAut.conj : X →* MulAut X).range

@[expose] def RadicalTwoSubgroupRankTwoStatement : Prop :=
  ∀ (X : Type) [Group X] [Finite X],
    ((∃ m : ℕ, 1 ≤ m ∧ CFSG.Blueprint.LieModel X .G2 0 2 m) ∨
      (∃ m : ℕ, 1 ≤ m ∧ CFSG.Blueprint.LieModel X .trialityD4 0 2 m)) →
    ∀ U : Subgroup X, U ≠ ⊥ → IsPGroup 2 U →
      inSubgroup (pCore 2) (Subgroup.normalizer (U : Set X)) = U →
      ∀ S : Subgroup (↥(Subgroup.normalizer (U : Set X)) ⧸
          U.subgroupOf (Subgroup.normalizer (U : Set X))),
        S.Normal → IsQuasisimple S →
          ∃ (s : ℕ) (K : Type) (_ : Field K) (_ : Finite K), 2 ≤ s ∧ Nat.card K = 2 ^ s ∧
            ∃ Z' : Subgroup S, Z' ≤ Subgroup.center S ∧ ∃ _ : Z'.Normal,
              Nonempty ((S ⧸ Z') ≃* StatedProj (StatedSL 2 K))

theorem alphaList_cases {X : Type} [Group X] (h : Tim77Cor2AlphaList X) :
    ListGroup X ∨ Tim77Cor2AlphaExtra X := by
  rcases h with ⟨m, hm, hmodel⟩ | ⟨m, hm, hmodel⟩ | h | ⟨m, hm, hmodel⟩ | hA | h
  · exact Or.inl (Or.inl ⟨3, m, by norm_num, hm, hmodel⟩)
  · exact Or.inr (Or.inl ⟨m, hm, hmodel⟩)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨m, hm, hmodel⟩)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨6, le_rfl, by norm_num, hA⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

theorem Tim77Cor2AlphaList.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : Tim77Cor2AlphaList X) : Tim77Cor2AlphaList Y := by
  rcases h with ⟨m, hm, hmodel⟩ | ⟨m, hm, hmodel⟩ | h | ⟨m, hm, hmodel⟩ | hA | h
  · exact Or.inl ⟨m, hm, statedClassicalModel_of_mulEquiv e hmodel⟩
  · exact Or.inr (Or.inl ⟨m, hm, CFSG.Blueprint.LieModel.of_mulEquiv e hmodel⟩)
  · exact Or.inr (Or.inr (Or.inl (statedClassicalModel_of_mulEquiv e h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨m, hm, CFSG.Blueprint.LieModel.of_mulEquiv e hmodel⟩)))
  · obtain ⟨φ⟩ := hA
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e.symm.trans φ⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (isSporadic_of_mulEquiv e h)))))

theorem alphaList_of_isCoveringOf {H : Type} [Group H]
    (hcov : IsCoveringOf Tim77Cor2AlphaList H) (hZ : Subgroup.center H = ⊥) :
    Tim77Cor2AlphaList H := by
  obtain ⟨-, Z, hZc, hZn, hlist⟩ := hcov
  have hZbot : Z = ⊥ := le_bot_iff.mp (hZ ▸ hZc)
  subst hZbot
  exact Tim77Cor2AlphaList.of_mulEquiv QuotientGroup.quotientBot hlist

theorem exists_quasisimple_section_of_radical {X : Type} [Group X] [Finite X]
    (K' : Type) [Field K'] [Finite K'] (U P : Subgroup X)
    (hPn : P ≤ Subgroup.normalizer (U : Set X))
    (hPN : ∀ k ∈ Subgroup.normalizer (U : Set X), k ∈ Subgroup.normalizer (P : Set X))
    (hPU : ∃ _ : (U.subgroupOf P).Normal,
      Nonempty ((↥P ⧸ U.subgroupOf P) ≃* StatedProj (StatedSL 4 K'))) :
    ∃ S : Subgroup (↥(Subgroup.normalizer (U : Set X)) ⧸
        U.subgroupOf (Subgroup.normalizer (U : Set X))),
      S.Normal ∧ IsQuasisimple S ∧ Nonempty (↥S ≃* StatedProj (StatedSL 4 K')) := by
  classical
  obtain ⟨hnUP, ⟨ePU⟩⟩ := hPU
  let N1 : Subgroup X := Subgroup.normalizer (U : Set X)
  let ψ : ↥P →* (↥N1 ⧸ U.subgroupOf N1) :=
    (QuotientGroup.mk' (U.subgroupOf N1)).comp (Subgroup.inclusion hPn)
  have hψmk : ∀ p : ↥P, ψ p = QuotientGroup.mk (⟨(p : X), hPn p.2⟩ : ↥N1) := fun p => rfl
  have hker : ψ.ker = U.subgroupOf P := by
    ext p
    rw [MonoidHom.mem_ker, hψmk, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf]
  haveI hnUP' : (U.subgroupOf P).Normal := hnUP
  let S : Subgroup (↥N1 ⧸ U.subgroupOf N1) := ψ.range
  have hSnormal : S.Normal := by
    refine ⟨fun s hs g => ?_⟩
    obtain ⟨p, rfl⟩ := hs
    obtain ⟨g0, rfl⟩ := QuotientGroup.mk_surjective g
    have hmem : (g0 : X) * (p : X) * (g0 : X)⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp (hPN _ g0.2) (p : X)).mp p.2
    refine ⟨⟨(g0 : X) * (p : X) * (g0 : X)⁻¹, hmem⟩, ?_⟩
    simp only [hψmk]
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    apply congrArg QuotientGroup.mk
    apply Subtype.ext
    simp
  let eS : ↥P ⧸ U.subgroupOf P ≃* ↥S :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange ψ)
  obtain ⟨hsimp4, hnab4⟩ := statedProj_statedSL_four_simple_nonabelian K'
  let eS' : ↥S ≃* StatedProj (StatedSL 4 K') := eS.symm.trans ePU
  haveI : IsSimpleGroup (StatedProj (StatedSL 4 K')) := hsimp4
  haveI : IsSimpleGroup ↥S := eS'.isSimpleGroup
  have hnabS : ∃ a b : ↥S, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab4
    exact ⟨eS'.symm a, eS'.symm b, fun h => hab (eS'.symm.injective (by simpa using h))⟩
  obtain ⟨hq, -⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnabS
  exact ⟨S, hSnormal, hq, ⟨eS'⟩⟩

theorem rankTwo_false_of_radical (hRad2 : RadicalTwoSubgroupRankTwoStatement)
    (hArtin : ArtinLinearOrdersStatement) {X : Type} [Group X] [Finite X]
    (hX : (∃ m : ℕ, 1 ≤ m ∧ CFSG.Blueprint.LieModel X .G2 0 2 m) ∨
      (∃ m : ℕ, 1 ≤ m ∧ CFSG.Blueprint.LieModel X .trialityD4 0 2 m))
    (K' : Type) [Field K'] [Finite K'] (hK' : ∃ g : ℕ, 1 ≤ g ∧ Nat.card K' = 2 ^ g)
    (U P : Subgroup X) (hU1 : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hrad : inSubgroup (pCore 2) (Subgroup.normalizer (U : Set X)) = U)
    (hPn : P ≤ Subgroup.normalizer (U : Set X))
    (hPN : ∀ k ∈ Subgroup.normalizer (U : Set X), k ∈ Subgroup.normalizer (P : Set X))
    (hPU : ∃ _ : (U.subgroupOf P).Normal,
      Nonempty ((↥P ⧸ U.subgroupOf P) ≃* StatedProj (StatedSL 4 K'))) : False := by
  classical
  obtain ⟨S, hSn, hSq, ⟨eS⟩⟩ := exists_quasisimple_section_of_radical K' U P hPn hPN hPU
  obtain ⟨s, K, _, _, hs2, hKs, Z', hZ'c, hZ'n, ⟨eZ⟩⟩ := hRad2 X hX U hU1 hU2 hrad S hSn hSq
  obtain ⟨hsimp4, hnab4⟩ := statedProj_statedSL_four_simple_nonabelian K'
  haveI : IsSimpleGroup (StatedProj (StatedSL 4 K')) := hsimp4
  haveI : IsSimpleGroup ↥S := eS.isSimpleGroup
  haveI hnt : Nontrivial (StatedProj (StatedSL 2 K)) := by
    haveI := CFSG.LinearGroups.linear_projective_nontrivial (K := K) (n := 2) (by norm_num)
    exact (projectiveSpecialLinearGroupEquivStatedProj 2 K).injective.nontrivial
  have hZ'bot : Z' = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top Z' with h | h
    · exact h
    · exfalso
      subst h
      haveI : Subsingleton (↥S ⧸ (⊤ : Subgroup ↥S)) := QuotientGroup.subsingleton_quotient_top
      haveI : Subsingleton (StatedProj (StatedSL 2 K)) := eZ.surjective.subsingleton
      exact not_subsingleton _ ‹_›
  subst hZ'bot
  let eSK : ↥S ≃* StatedProj (StatedSL 2 K) := QuotientGroup.quotientBot.symm.trans eZ
  have hcard : Nat.card (StatedProj (StatedSL 4 K')) = Nat.card (StatedProj (StatedSL 2 K)) :=
    Nat.card_congr (eS.symm.trans eSK).toEquiv
  obtain ⟨g, hg1, hg⟩ := hK'
  have hK4 : 4 ≤ Nat.card K := by
    rw [hKs]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs2
  have h := hArtin 4 2 K' K (by norm_num) (by norm_num) ⟨g, hg1, hg⟩ ⟨s, by omega, hKs⟩
    (by omega) (by omega) hcard
  rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, -, h3, -⟩ <;> omega

theorem card_L4_ge {K : Type} [Field K] [Finite K] (hK : 4 ≤ Nat.card K) :
    246758400 ≤ Nat.card (StatedProj (StatedSL 4 K)) := by
  have h := card_statedProj_statedSL_mul_gcd (K := K) (a := 4) (by norm_num)
  have hI : Finset.Icc 2 4 = {2, 3, 4} := by decide
  rw [hI, Finset.prod_insert (by simp), Finset.prod_insert (by simp), Finset.prod_singleton,
    show 4 * (4 - 1) / 2 = 6 by norm_num] at h
  obtain ⟨n, hn⟩ : ∃ n, n = Nat.card K := ⟨_, rfl⟩
  rw [← hn] at h hK
  have hn6 : 4096 ≤ n ^ 6 := by
    calc 4096 = 4 ^ 6 := by norm_num
      _ ≤ n ^ 6 := Nat.pow_le_pow_left hK 6
  have h2 : 15 ≤ n ^ 2 - 1 := by
    have : 16 ≤ n ^ 2 := by nlinarith
    omega
  have h3 : 63 ≤ n ^ 3 - 1 := by
    have : 64 ≤ n ^ 3 := by nlinarith [Nat.pow_le_pow_left hK 3]
    omega
  have h4 : 255 ≤ n ^ 4 - 1 := by
    have : 256 ≤ n ^ 4 := by nlinarith [Nat.pow_le_pow_left hK 4]
    omega
  have hprod : 987033600 ≤ n ^ 6 * ((n ^ 2 - 1) * ((n ^ 3 - 1) * (n ^ 4 - 1))) := by
    calc 987033600 = 4096 * (15 * (63 * 255)) := by norm_num
      _ ≤ _ := Nat.mul_le_mul hn6 (Nat.mul_le_mul h2 (Nat.mul_le_mul h3 h4))
  have hg : Nat.gcd 4 (n - 1) ≤ 4 := Nat.gcd_le_left _ (by norm_num)
  by_contra hlt
  push Not at hlt
  have : Nat.card (StatedProj (StatedSL 4 K)) * Nat.gcd 4 (n - 1) < 987033600 := by
    calc Nat.card (StatedProj (StatedSL 4 K)) * Nat.gcd 4 (n - 1)
        ≤ Nat.card (StatedProj (StatedSL 4 K)) * 4 := Nat.mul_le_mul_left _ hg
      _ < 987033600 := by omega
  omega

theorem card_alphaExtra_small {X : Type} [Group X]
    (h : StatedClassicalModel X .PSU 3 3 1 ∨ CFSG.Blueprint.NativeSporadic.IsSporadic X .J2) :
    Nat.card X < 246758400 := by
  rcases h with h | h
  · have h1 := CFSG.Open.StatedAPI.card_mul_gcd_of_statedClassicalModel_psu_three h
    norm_num at h1
    omega
  · rw [CFSG.GH74.card_of_isSporadic_J2 h]
    norm_num

theorem caseOne_tail
    (hOut : OutSolvableListStatement) (hOutA : OutSolvableAlphaStatement)
    (hRank : TwoRankSporadicAltStatement) (hBorel : BorelRankOneSolvableStatement)
    (hArtin : ArtinLinearOrdersStatement) (hRad : RadicalTwoSubgroupLinearStatement)
    (hRad2 : RadicalTwoSubgroupRankTwoStatement)
    {Y : Type} [Group Y] [Finite Y] (q : ℕ) (hq4 : 4 ≤ q) (hq2 : ∃ g : ℕ, q = 2 ^ g)
    (V L N R K Gs : Subgroup Y) [hGsn : Gs.Normal]
    (hO2 : ∀ P : Subgroup Y, P.Normal → IsPGroup 2 P → P = ⊥)
    (hO : ∀ P : Subgroup Y, P.Normal → Odd (Nat.card P) → P = ⊥)
    (hC : ∀ c : Y, (∀ s ∈ Gs, c * s = s * c) → c = 1)
    (hKV : ∀ g ∈ normalizer (V : Set Y), g ∈ K)
    (hVGs : V ≤ Gs) (hVL : V ≤ L) (hLN : L ≤ N) (hNR : N ≤ R) (hRK : R ≤ K)
    (hN2 : IsPGroup 2 N)
    (hpc : ∀ P : Subgroup Y, P ≤ K → (∀ k ∈ K, k ∈ normalizer (P : Set Y)) → IsPGroup 2 P →
      P ≤ N)
    (hNn : ∀ k ∈ K, k ∈ normalizer (N : Set Y)) (hRn : ∀ k ∈ K, k ∈ normalizer (R : Set Y))
    (hLn : ∀ k ∈ K, k ∈ normalizer (L : Set Y))
    (hZN : ∀ x ∈ N, (∀ n ∈ N, x * n = n * x) → x ∈ V)
    (hVc : ∀ v ∈ V, ∀ n ∈ N, v * n = n * v)
    (hVcard : Nat.card V = q) (hNcard : Nat.card N = q ^ 9) (hL64 : 2 ^ 6 < Nat.card L)
    (hLab : IsElemAbelian 2 L)
    (hX : ListGroup ↥Gs ∨ (Tim77Cor2AlphaExtra ↥Gs ∧ ∃ a b : ↥Gs, a * b ≠ b * a))
    (K₀ : Type) [Field K₀] [Finite K₀] (hK₀ : Nat.card K₀ = q)
    (hRN : ∃ _ : (N.subgroupOf R).Normal,
      Nonempty ((↥R ⧸ N.subgroupOf R) ≃* StatedProj (StatedSL 4 K₀)))
    (hy : ∃ y ∈ R, orderOf y = 3 ∧ ∀ x ∈ N, y * x = x * y → x ∈ V) :
    ∃ (K₁ : Type) (_ : Field K₁) (_ : Finite K₁), Nat.card K₁ = q ∧
      Nonempty (↥(generalizedFitting Y) ≃* StatedProj (StatedSL 6 K₁)) := by
  classical
  obtain ⟨hnormNR, ⟨eRN⟩⟩ := hRN
  have hVne : V ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hVcard
    omega
  have hLne : L ≠ ⊥ := fun h => hVne (le_bot_iff.mp (h ▸ hVL))
  have hCGs := hC
  obtain ⟨hsimp4, hnab4⟩ := statedProj_statedSL_four_simple_nonabelian K₀
  haveI : IsSimpleGroup (StatedProj (StatedSL 4 K₀)) := hsimp4
  have hperf4 : Group.IsPerfect (StatedProj (StatedSL 4 K₀)) :=
    isPerfect_of_simple_nonabelian hnab4
  have hperfRN : commutator (↥R ⧸ N.subgroupOf R) = ⊤ :=
    (Group.IsPerfect.ofSurjective (f := eRN.symm.toMonoidHom) eRN.symm.surjective
      (G := StatedProj (StatedSL 4 K₀))).commutator_eq_top
  obtain ⟨E, hER, hEperf, hEN, hEn⟩ := exists_perfect_sup_eq hNR hperfRN
  have hEGs : E ≤ Gs := by
    rcases hX with hlist | ⟨hextra, hnab⟩
    · exact perfect_le_of_out_solvable hCGs (hOut ↥Gs hlist) hEperf
    · exact perfect_le_of_out_solvable hCGs (fun P hP => hOutA ↥Gs hextra hnab P hP) hEperf
  have hEne : E ≠ ⊥ := by
    intro h
    have hRN' : R ≤ N := by
      rw [← hEN, h, bot_sup_eq]
    haveI : Subsingleton (↥R ⧸ N.subgroupOf R) := by
      have : N.subgroupOf R = ⊤ := Subgroup.subgroupOf_eq_top.mpr hRN'
      rw [this]
      exact QuotientGroup.subsingleton_quotient_top
    obtain ⟨a, b, hab⟩ := hnab4
    exact hab (by
      have := Subsingleton.elim (eRN.symm a) (eRN.symm b)
      have h2 := eRN.symm.injective this
      rw [h2])
  obtain ⟨y, hyR, hy3, hyC⟩ := hy
  have hyGs : y ∈ Gs := mem_of_orderOf_three hEGs hN2 hy3 (by rw [hEN]; exact hyR)
  have hNGs : N ≤ Gs :=
    le_normal_of_coprime_element hN2 hy3 (hNn y (hRK hyR)) hyGs hyC hVGs
  have hRGs : R ≤ Gs := by rw [← hEN]; exact sup_le hEGs hNGs
  have hLGs : L ≤ Gs := hLN.trans hNGs
  have hKN : normalizer (N : Set Y) = K := by
    refine le_antisymm (fun g hg => hKV g ?_) (fun k hk => ?_)
    · exact normalizer_le_normalizer_of_center (hVL.trans hLN) hZN hVc hg
    · exact hNn k hk
  have hNK : N ≤ K := hNR.trans hRK
  have hrad : inSubgroup (pCore 2) (normalizer ((N.subgroupOf Gs : Subgroup ↥Gs) : Set ↥Gs)) =
      N.subgroupOf Gs := by
    rw [← Subgroup.subgroupOf_normalizer_eq hNGs, hKN]
    have h1 : K.subgroupOf Gs = (K ⊓ Gs).subgroupOf Gs := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rw [h1, inSubgroup_pCore_subgroupOf inf_le_right,
      inSubgroup_pCore_inf_eq hNGs hNK hNn hN2 hpc]
  have hU1 : N.subgroupOf Gs ≠ ⊥ := by
    intro h
    have h1 : N = ⊥ := by
      have hd : Disjoint N Gs := Subgroup.subgroupOf_eq_bot.mp h
      exact hd.eq_bot_of_le hNGs
    exact hVne (le_bot_iff.mp (h1 ▸ (hVL.trans hLN)))
  have hU2 : IsPGroup 2 ↥(N.subgroupOf Gs) :=
    hN2.of_equiv (Subgroup.subgroupOfEquivOfLe hNGs).symm
  have hZ : Nat.card ↥(Subgroup.center ↥(N.subgroupOf Gs)) = q := by
    rw [← hVcard, ← natCard_center_eq_of_center (hVL.trans hLN) hZN hVc]
    exact Nat.card_congr (Subgroup.centerCongr (Subgroup.subgroupOfEquivOfLe hNGs)).toEquiv
  have hcard : Nat.card ↥(N.subgroupOf Gs) = q ^ 9 := by
    rw [← hNcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNGs).toEquiv
  have hUP : N.subgroupOf Gs ≤ R.subgroupOf Gs := fun x hx => hNR hx
  have hPn : R.subgroupOf Gs ≤ normalizer ((N.subgroupOf Gs : Subgroup ↥Gs) : Set ↥Gs) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hNGs, hKN]
    exact fun x hx => hRK hx
  have hPN : ∀ k ∈ normalizer ((N.subgroupOf Gs : Subgroup ↥Gs) : Set ↥Gs),
      k ∈ normalizer ((R.subgroupOf Gs : Subgroup ↥Gs) : Set ↥Gs) := by
    intro k hk
    rw [← Subgroup.subgroupOf_normalizer_eq hNGs, hKN] at hk
    have hkK : (k : Y) ∈ K := hk
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have := (Subgroup.mem_normalizer_iff.mp (hRn _ hkK) (x : Y))
    exact this
  have hPU := nonempty_quot_equiv_subgroupOf hRGs hNR ⟨eRN⟩
  rcases hX with hlist | ⟨hextra, -⟩
  ·
    obtain ⟨r, K1, hKf, hKfin, hr3, hK2, ⟨e⟩⟩ := exists_psl_of_listGroup hBorel hRank hlist hEGs
      hEperf hEne (fun k hk => hLn k (hRK (hER hk))) hLGs hLab hL64 hLne
    have hflag := flag_type_of_radical_equiv hRad hArtin r K1 hr3 hK2 e q hq4 K₀ hK₀ hq2
      (N.subgroupOf Gs) (R.subgroupOf Gs) hU1 hU2 hrad hZ hcard hUP hPn hPN hPU
    obtain ⟨hr6, hKq⟩ := hflag
    subst hr6
    haveI : IsSimpleGroup (StatedProj (StatedSL 6 K1)) :=
      CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL K1 (d := 6) (by norm_num)
        (Or.inl (by norm_num)) (Or.inl (by norm_num))
    haveI hsimpGs : IsSimpleGroup ↥Gs := e.isSimpleGroup
    have hnabGs : ∃ a ∈ Gs, ∃ b ∈ Gs, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hnab4
      obtain ⟨x0, hx0⟩ := QuotientGroup.mk_surjective (eRN.symm a)
      obtain ⟨y0, hy0⟩ := QuotientGroup.mk_surjective (eRN.symm b)
      refine ⟨x0, hRGs x0.2, y0, hRGs y0.2, fun h => hab ?_⟩
      have h2 : x0 * y0 = y0 * x0 := Subtype.ext h
      have h3 : eRN.symm a * eRN.symm b = eRN.symm b * eRN.symm a := by
        rw [← hx0, ← hy0, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h2]
      have h4 := congrArg eRN h3
      simpa using h4
    have hFG : generalizedFitting Y = Gs := fstar_eq_of_simple hsimpGs hnabGs hCGs hO2 hO
    exact ⟨K1, hKf, hKfin, hKq, ⟨(MulEquiv.subgroupCongr hFG).trans e⟩⟩
  · exfalso
    obtain ⟨g, hg⟩ := hq2
    have hg1 : 1 ≤ g := by
      rcases Nat.eq_zero_or_pos g with h0 | h0
      · rw [h0] at hg
        omega
      · exact h0
    have hKg : ∃ g : ℕ, 1 ≤ g ∧ Nat.card K₀ = 2 ^ g := ⟨g, hg1, by rw [hK₀, hg]⟩
    have hsmallRN : 246758400 ≤ Nat.card (↥R ⧸ N.subgroupOf R) := by
      rw [Nat.card_congr eRN.toEquiv]
      exact card_L4_ge (by rw [hK₀]; exact hq4)
    have hRle : Nat.card (↥R ⧸ N.subgroupOf R) ≤ Nat.card ↥Gs :=
      (Nat.card_le_card_of_surjective _ (QuotientGroup.mk_surjective (s := N.subgroupOf R))).trans
        (Subgroup.card_le_of_le hRGs)
    rcases hextra with hG2 | hU3 | hD4 | hJ2
    · exact rankTwo_false_of_radical hRad2 hArtin (Or.inl hG2) K₀ hKg (N.subgroupOf Gs)
        (R.subgroupOf Gs) hU1 hU2 hrad hPn hPN hPU
    · have := card_alphaExtra_small (Or.inl hU3)
      omega
    · exact rankTwo_false_of_radical hRad2 hArtin (Or.inr hD4) K₀ hKg (N.subgroupOf Gs)
        (R.subgroupOf Gs) hU1 hU2 hrad hPn hPN hPU
    · have := card_alphaExtra_small (Or.inr hJ2)
      omega

end CFSG.RankThree.GF2n.Stroth80

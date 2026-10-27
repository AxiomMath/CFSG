module

public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement Pointwise

private theorem permThree_card : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
  rw [Nat.card_perm, Nat.card_fin]
  decide

private theorem altThree_card : Nat.card (alternatingGroup (Fin 3)) = 3 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

private theorem permThree_center : Subgroup.center (Equiv.Perm (Fin 3)) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have h : ∀ y : Equiv.Perm (Fin 3), y ∈ Subgroup.center (Equiv.Perm (Fin 3)) → y = 1 := by
    decide
  exact h x hx

private theorem isPGroup_alt_three : IsPGroup 3 (alternatingGroup (Fin 3)) := by
  refine IsPGroup.of_card (n := 1) ?_
  rw [altThree_card]
  norm_num

private theorem pCore_two_perm_three : pCore 2 (Equiv.Perm (Fin 3)) = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := pCore 2 (Equiv.Perm (Fin 3))
  have hNnormal : N.Normal := pCore_normal
  have hNp : IsPGroup 2 N := pCore_isPGroup
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hNp
  have hdvd : Nat.card N ∣ 6 := by
    rw [← permThree_card]
    exact Subgroup.card_subgroup_dvd_card N
  have hk1 : k ≤ 1 := by
    by_contra h
    have hk2 : 2 ≤ k := by omega
    have h4 : 4 ∣ 2 ^ k := dvd_trans (by norm_num : 4 ∣ 2 ^ 2) (pow_dvd_pow 2 hk2)
    rw [← hk] at h4
    have h46 : 4 ∣ 6 := h4.trans hdvd
    omega
  have hcardNle : Nat.card N ≤ 2 := by
    rw [hk]
    calc 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
      _ = 2 := by norm_num
  by_contra hNne
  have hNcard_ne : Nat.card N ≠ 1 := fun h1 => hNne (Subgroup.card_eq_one.mp h1)
  have hNcard : Nat.card N = 2 := by
    have := Nat.card_pos (α := N)
    omega
  have hNcenter : N ≤ Subgroup.center (Equiv.Perm (Fin 3)) := by
    intro n hn
    rw [Subgroup.mem_center_iff]
    intro g
    by_cases hn1 : n = 1
    · simp [hn1]
    · have hconj : g * n * g⁻¹ ∈ N := hNnormal.conj_mem n hn g
      have hconj_ne : g * n * g⁻¹ ≠ 1 := by
        intro h
        apply hn1
        have := congrArg (fun x => g⁻¹ * x * g) h
        simpa [mul_assoc] using this
      obtain ⟨z, hz_ne, hzu⟩ := (Nat.card_eq_two_iff' (1 : N)).mp hNcard
      have h1 : (⟨n, hn⟩ : N) = z := hzu ⟨n, hn⟩ (by simpa using hn1)
      have h2 : (⟨g * n * g⁻¹, hconj⟩ : N) = z := hzu _ (by simpa using hconj_ne)
      have heq : n = g * n * g⁻¹ := congrArg Subtype.val (h1.trans h2.symm)
      have hng : n * g = g * n := by
        calc n * g = (g * n * g⁻¹) * g := congrArg (fun x => x * g) heq
          _ = g * n := by group
      exact hng.symm
  have hle : N ≤ ⊥ := by
    rw [← permThree_center]
    exact hNcenter
  exact hNne (le_bot_iff.mp hle)

private theorem factorization_two_six : (6 : ℕ).factorization 2 = 1 := by
  rw [show (6 : ℕ) = 2 ^ 1 * 3 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num),
    Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  simp

private theorem card_quotient_pCore_two_perm_three :
    Nat.card ((Equiv.Perm (Fin 3)) ⧸ pCore 2 (Equiv.Perm (Fin 3))) = 6 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (pCore 2 (Equiv.Perm (Fin 3)))
  rw [permThree_card] at h
  have h1 : Nat.card (pCore 2 (Equiv.Perm (Fin 3))) = 1 := by
    rw [pCore_two_perm_three, Subgroup.card_bot]
  rw [h1, mul_one] at h
  exact h.symm

private theorem oTwoPTwo_perm_three : CFSG.Quasithin.E1.oTwoPTwo (Equiv.Perm (Fin 3)) 3 = ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine CFSG.Quasithin.E1.oTwoPTwo_eq_top_of_series
    (N₂ := ⊥) (N₂p := alternatingGroup (Fin 3)) ?_ ?_ ?_
  · exact IsPGroup.of_card (n := 0) (by simp)
  · intro x hx
    refine ⟨1, ?_⟩
    have hx3 : x ^ 3 = 1 := by
      have h := pow_card_eq_one' (x := (⟨x, hx⟩ : alternatingGroup (Fin 3)))
      rw [altThree_card] at h
      exact congrArg Subtype.val h
    simpa [hx3]
  · intro q
    refine ⟨1, ?_⟩
    have hqcard : Nat.card ((Equiv.Perm (Fin 3)) ⧸ alternatingGroup (Fin 3)) = 2 := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (alternatingGroup (Fin 3))
      rw [permThree_card, altThree_card] at h
      omega
    have hq2 : q ^ 2 ∈ alternatingGroup (Fin 3) := by
      have h := pow_card_eq_one' (x := (QuotientGroup.mk' (alternatingGroup (Fin 3)) q))
      rw [hqcard] at h
      rw [← QuotientGroup.eq_one_iff (N := alternatingGroup (Fin 3)) (q ^ 2)]
      simpa using h
    simpa using hq2

private theorem commutator_alt_three_of_card_two {B : Subgroup (Equiv.Perm (Fin 3))}
    (hB : Nat.card B = 2) : ⁅alternatingGroup (Fin 3), B⁆ = alternatingGroup (Fin 3) := by
  classical
  set A := alternatingGroup (Fin 3)
  have hle : ⁅A, B⁆ ≤ A := Subgroup.commutator_le_left A B
  have hBnt : Nontrivial B := Finite.one_lt_card_iff_nontrivial.1 (by rw [hB]; norm_num)
  obtain ⟨b, hbne⟩ := exists_ne (1 : B)
  have hb : (b : Equiv.Perm (Fin 3)) ∈ B := b.2
  have hb1 : (b : Equiv.Perm (Fin 3)) ≠ 1 := fun h => hbne (Subtype.ext h)
  have hb2 : (b : Equiv.Perm (Fin 3)) * (b : Equiv.Perm (Fin 3)) = 1 := by
    have h := pow_card_eq_one' (x := b)
    rw [hB] at h
    simpa [pow_two] using congrArg Subtype.val h
  set c : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2
  have hcA : c ∈ A := by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide
  have hcne : ⁅c, (b : Equiv.Perm (Fin 3))⁆ ≠ 1 := by
    have h : ∀ y : Equiv.Perm (Fin 3), y * y = 1 → y ≠ 1 → ⁅c, y⁆ ≠ 1 := by
      decide
    exact h _ hb2 hb1
  have hne : ⁅A, B⁆ ≠ ⊥ := by
    intro hbot
    have hmem : ⁅c, (b : Equiv.Perm (Fin 3))⁆ ∈ ⁅A, B⁆ :=
      Subgroup.commutator_mem_commutator hcA hb
    rw [hbot] at hmem
    exact hcne (Subgroup.mem_bot.mp hmem)
  have hdvd : Nat.card ↥(⁅A, B⁆) ∣ 3 := by
    have h1 : Nat.card ((⁅A, B⁆).subgroupOf A) ∣ Nat.card ↥A :=
      Subgroup.card_subgroup_dvd_card _
    rw [altThree_card] at h1
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at h1
  have hcard : Nat.card ↥(⁅A, B⁆) = 3 := by
    have hne1 : Nat.card ↥(⁅A, B⁆) ≠ 1 := fun h1 => hne (Subgroup.card_eq_one.mp h1)
    rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _ hdvd with h1 | h3
    · exact absurd h1 hne1
    · exact h3
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, altThree_card])

private theorem mk_pCore_two_perm_three_injective :
    Function.Injective (QuotientGroup.mk' (pCore 2 (Equiv.Perm (Fin 3)))) := by
  rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
  exact pCore_two_perm_three

private theorem pCore_three_quotient_perm_three :
    pCore 3 ((Equiv.Perm (Fin 3)) ⧸ pCore 2 (Equiv.Perm (Fin 3))) =
      (alternatingGroup (Fin 3)).map
        (QuotientGroup.mk' (pCore 2 (Equiv.Perm (Fin 3)))) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set A := alternatingGroup (Fin 3)
  set π := QuotientGroup.mk' (pCore 2 (Equiv.Perm (Fin 3)))
  have hAle : A.map π ≤ pCore 3 ((Equiv.Perm (Fin 3)) ⧸ pCore 2 (Equiv.Perm (Fin 3))) := by
    refine CFSG.LieType.BorelTits.le_pCore 3 ?_ ?_
    · exact (inferInstance : A.Normal).map π (QuotientGroup.mk'_surjective _)
    · exact isPGroup_alt_three.map _
  have hcardAbar : Nat.card (A.map π) = 3 := by
    rw [Subgroup.card_map_of_injective mk_pCore_two_perm_three_injective]
    exact altThree_card
  have hcardp : Nat.card (pCore 3 ((Equiv.Perm (Fin 3)) ⧸ pCore 2 (Equiv.Perm (Fin 3)))) ≤ 3 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp
      (CFSG.pCore_isPGroup (p := 3) (G := (Equiv.Perm (Fin 3)) ⧸ pCore 2 (Equiv.Perm (Fin 3))))
    have hdvd : Nat.card (pCore 3 ((Equiv.Perm (Fin 3)) ⧸ pCore 2 (Equiv.Perm (Fin 3)))) ∣ 6 := by
      rw [← card_quotient_pCore_two_perm_three]
      exact Subgroup.card_subgroup_dvd_card _
    have hk1 : k ≤ 1 := by
      by_contra h
      have hk2 : 2 ≤ k := by omega
      have h9 : 9 ∣ 3 ^ k := dvd_trans (by norm_num : 9 ∣ 3 ^ 2) (pow_dvd_pow 3 hk2)
      rw [← hk] at h9
      have h96 : 9 ∣ 6 := h9.trans hdvd
      omega
    rw [hk]
    calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
      _ = 3 := by norm_num
  exact (Subgroup.eq_of_le_of_card_ge hAle (by rw [hcardAbar]; exact hcardp)).symm

private theorem eOne_perm_three_of_card_two {B : Subgroup (Equiv.Perm (Fin 3))}
    (hB : Nat.card B = 2) : CFSG.Quasithin.E1.EOne (Equiv.Perm (Fin 3)) B := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set A := alternatingGroup (Fin 3)
  set π := QuotientGroup.mk' (pCore 2 (Equiv.Perm (Fin 3)))
  have hcomm : ⁅A.map π, B.map π⁆ = A.map π := by
    rw [← Subgroup.map_commutator, commutator_alt_three_of_card_two hB]
  refine ⟨3, Nat.prime_three, by norm_num, oTwoPTwo_perm_three, ?_, ?_, ?_⟩
  · rw [pCore_three_quotient_perm_three]
    intro h
    have hcard : Nat.card (A.map π) = 3 := by
      rw [Subgroup.card_map_of_injective mk_pCore_two_perm_three_injective]
      exact altThree_card
    rw [h, Subgroup.card_bot] at hcard
    omega
  · rw [pCore_three_quotient_perm_three]
    show A.map π = ⁅A.map π, CFSG.Quasithin.E1.barO2 (Equiv.Perm (Fin 3)) B⁆
    rw [show CFSG.Quasithin.E1.barO2 (Equiv.Perm (Fin 3)) B = B.map π from rfl]
    exact hcomm.symm
  · show Nat.card (CFSG.Quasithin.E1.barO2 (Equiv.Perm (Fin 3)) B) = 2
    rw [show CFSG.Quasithin.E1.barO2 (Equiv.Perm (Fin 3)) B = B.map π from rfl]
    rw [Subgroup.card_map_of_injective mk_pCore_two_perm_three_injective]
    exact hB

private theorem card_eq_six_of_mulEquiv_perm_three {Q : Type} [Group Q] [Finite Q]
    (e : Q ≃* Equiv.Perm (Fin 3)) : Nat.card Q = 6 := by
  rw [Nat.card_congr e.toEquiv]
  exact permThree_card

private theorem card_isSylowOf_two_top {Q : Type} [Group Q] [Finite Q]
    (e : Q ≃* Equiv.Perm (Fin 3)) {T : Subgroup Q}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) : Nat.card T = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := CFSG.ABGLocalTools.IsSylowOf.card_eq hT
  rw [Subgroup.card_top, card_eq_six_of_mulEquiv_perm_three e, factorization_two_six] at h
  simpa using h

private theorem mem_invColl_of_isSylow_two {Q : Type} [Group Q] [Finite Q]
    (e : Q ≃* Equiv.Perm (Fin 3)) {T : Subgroup Q}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤)
    {Ω : Set (Subgroup Q)} (hΩ : CFSG.Quasithin.E1.IsInvColl ⊤ Ω)
    (hΩne : Ω.Nonempty) (hΩnt : ∀ A ∈ Ω, A ≠ ⊥) : T ∈ Ω := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardQ : Nat.card Q = 6 := card_eq_six_of_mulEquiv_perm_three e
  have hfac : (Nat.card Q).factorization 2 = 1 := by
    rw [hcardQ]
    exact factorization_two_six
  have hcardT : Nat.card T = 2 := card_isSylowOf_two_top e hT
  have hTne : T ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcardT
    omega
  obtain ⟨t, htT, ht1⟩ : ∃ t ∈ T, t ≠ 1 := by
    by_contra h
    push Not at h
    exact hTne ((Subgroup.eq_bot_iff_forall T).mpr h)
  have htorder : orderOf t = 2 := by
    refine orderOf_eq_prime ?_ ht1
    have h := pow_card_eq_one' (x := (⟨t, htT⟩ : T))
    rw [hcardT] at h
    simpa using congrArg Subtype.val h
  have hAcard : ∀ A : Subgroup Q, A ∈ Ω → Nat.card A = 2 := by
    intro A hA
    have hAel : CFSG.Open.IsElemAbelian 2 A := hΩ.isElemAbelian A hA
    have hAp : IsPGroup 2 A := CFSG.Open.IsElemAbelian.isPGroup hAel
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hAp
    have hdvd : Nat.card A ∣ 6 := by
      rw [← hcardQ]
      exact Subgroup.card_subgroup_dvd_card A
    have hk1 : k ≤ 1 := by
      by_contra h
      have hk2 : 2 ≤ k := by omega
      have h4 : 4 ∣ 2 ^ k := dvd_trans (by norm_num : 4 ∣ 2 ^ 2) (pow_dvd_pow 2 hk2)
      rw [← hk] at h4
      have h46 : 4 ∣ 6 := h4.trans hdvd
      omega
    have hAle : Nat.card A ≤ 2 := by
      rw [hk]
      calc 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
        _ = 2 := by norm_num
    have hAne := hΩnt A hA
    have hAcardne : Nat.card A ≠ 1 := fun h1 => hAne (Subgroup.card_eq_one.mp h1)
    have hpos := Nat.card_pos (α := A)
    omega
  obtain ⟨A, hAΩ⟩ := hΩne
  have hAel : CFSG.Open.IsElemAbelian 2 A := hΩ.isElemAbelian A hAΩ
  have hAne := hΩnt A hAΩ
  obtain ⟨a, haA, ha1⟩ : ∃ a ∈ A, a ≠ 1 := by
    by_contra h
    push Not at h
    exact hAne ((Subgroup.eq_bot_iff_forall A).mpr h)
  have haorder : orderOf a = 2 := by
    refine orderOf_eq_prime ?_ ha1
    simpa using hAel.2 a haA
  let PA : Sylow 2 Q := Sylow.ofCard A (by rw [hAcard A hAΩ, hfac]; norm_num)
  let PT : Sylow 2 Q := Sylow.ofCard T (by rw [hcardT, hfac]; norm_num)
  have hPA : (PA : Subgroup Q) = A := Sylow.coe_ofCard _ _
  have hPT : (PT : Subgroup Q) = T := Sylow.coe_ofCard _ _
  haveI : MulAction.IsPretransitive Q (Sylow 2 Q) := Sylow.isPretransitive_of_finite
  obtain ⟨g, hg⟩ := (inferInstance : MulAction.IsPretransitive Q (Sylow 2 Q)).exists_smul_eq PA PT
  have hmap : T = A.map (MulAut.conj g).toMonoidHom := by
    rw [← hPT, ← hPA, ← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  rw [hmap]
  simpa [CFSG.Quasithin.A1b.conjSub] using
    (hΩ.conj A hAΩ g (Subgroup.mem_top g))

private theorem isEP_top_self_of_mulEquiv_perm_three {Q : Type} [Group Q] [Finite Q]
    (e : Q ≃* Equiv.Perm (Fin 3)) {T : Subgroup Q}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) :
    CFSG.LocalAnalysis.UniquenessCase.UC22.F12.IsEP 1 (⊤ : Subgroup Q) T T ⊤ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardT : Nat.card T = 2 := card_isSylowOf_two_top e hT
  let e' : (↥(⊤ : Subgroup Q)) ≃* Equiv.Perm (Fin 3) := Subgroup.topEquiv.trans e
  have hEOne : CFSG.Quasithin.E1.EOne (↥(⊤ : Subgroup Q)) (T.subgroupOf ⊤) := by
    refine (CFSG.Quasithin.E1.eOne_map e' (T.subgroupOf ⊤)).mpr ?_
    refine eOne_perm_three_of_card_two ?_
    rw [Subgroup.card_map_of_injective e'.injective]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_top : T ≤ ⊤)).toEquiv, hcardT]
  have hEOneCopy := hEOne
  obtain ⟨p, hp, hp2, hoTwo, hne, hcomm, hcardbar⟩ := hEOneCopy
  refine ⟨le_top, ?_, ?_, Or.inl ⟨hEOne, ?_⟩⟩
  · rw [inf_top_eq]
    exact CFSG.Quasithin.E1.tauOf_le ⊤ T T
  · rw [inf_top_eq]
    exact CFSG.ABGLocalTools.isSylowOf_iff.mp hT
  · rw [hcardbar]
    norm_num

private theorem eGenP_top_of_isSylow_two {Q : Type} [Group Q] [Finite Q]
    (e : Q ≃* Equiv.Perm (Fin 3)) {T : Subgroup Q}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤)
    {Ω : Set (Subgroup Q)} (hΩ : CFSG.Quasithin.E1.IsInvColl ⊤ Ω)
    (hΩne : Ω.Nonempty) (hΩnt : ∀ A ∈ Ω, A ≠ ⊥) :
    CFSG.LocalAnalysis.UniquenessCase.UC22.F12.eGenP 1 (⊤ : Subgroup Q) T Ω = ⊤ := by
  have hTmem : T ∈ Ω := mem_invColl_of_isSylow_two e hT hΩ hΩne hΩnt
  have hIsEP : CFSG.LocalAnalysis.UniquenessCase.UC22.F12.IsEP 1 (⊤ : Subgroup Q) T T ⊤ :=
    isEP_top_self_of_mulEquiv_perm_three e hT
  refine le_antisymm le_top ?_
  refine le_iSup₂_of_le T hTmem ?_
  refine le_iSup_of_le (le_refl T) ?_
  exact le_iSup₂_of_le ⊤ hIsEP le_rfl

theorem inF_one_top_of_mulEquiv_perm_three {Q : Type} [Group Q] [Finite Q]
    (e : Q ≃* Equiv.Perm (Fin 3)) :
    CFSG.LocalAnalysis.UniquenessCase.UC22.F12.InF 1 (⊤ : Subgroup Q) := by
  unfold CFSG.LocalAnalysis.UniquenessCase.UC22.F12.InF
  intro T hT
  unfold CFSG.LocalAnalysis.UniquenessCase.UC22.F12.InFFor
  intro Ω hΩ hΩne hΩnt
  rw [eGenP_top_of_isSylow_two e hT hΩ hΩne hΩnt, Subgroup.coe_top]
  exact Set.univ_mul ⟨1, T.one_mem⟩

theorem inFSq_one_of_bar2_perm_three {G : Type} [Group G] [Finite G] (L : Subgroup G)
    (h : Nonempty (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L ≃* Equiv.Perm (Fin 3))) :
    CFSG.LocalAnalysis.WeakClosure81.InFSq 1 L := by
  obtain ⟨e⟩ := h
  exact inF_one_top_of_mulEquiv_perm_three e


private theorem inF_of_odd_order {Q : Type} [Group Q] [Finite Q] (j : ℕ)
    (hodd : Odd (Nat.card Q)) :
    CFSG.LocalAnalysis.UniquenessCase.UC22.F12.InF j (⊤ : Subgroup Q) := by
  unfold CFSG.LocalAnalysis.UniquenessCase.UC22.F12.InF
  intro T hT
  unfold CFSG.LocalAnalysis.UniquenessCase.UC22.F12.InFFor
  intro Ω hΩ hΩne hΩnt
  exfalso
  obtain ⟨A, hAΩ⟩ := hΩne
  have hAel : CFSG.Open.IsElemAbelian 2 A := hΩ.isElemAbelian A hAΩ
  have hA2 : IsPGroup 2 A := CFSG.Open.IsElemAbelian.isPGroup hAel
  have hAne : A ≠ ⊥ := hΩnt A hAΩ
  have h2A : 2 ∣ Nat.card A := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA2
    have hkpos : 0 < k := by
      by_contra hk0
      have hkzero : k = 0 := by omega
      rw [hkzero, pow_zero] at hk
      exact hAne (Subgroup.card_eq_one.mp hk)
    have h2 : 2 ∣ 2 ^ k := dvd_trans (by norm_num : 2 ∣ 2) (pow_dvd_pow 2 hkpos)
    rw [hk]
    exact h2
  have h2Q : 2 ∣ Nat.card Q := h2A.trans (Subgroup.card_subgroup_dvd_card A)
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2Q)

theorem inFSq_of_odd_card_bar2 {G : Type} [Group G] [Finite G] (j : ℕ) (H : Subgroup G)
    (hodd : Odd (Nat.card (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 H))) :
    CFSG.LocalAnalysis.WeakClosure81.InFSq j H := by
  exact inF_of_odd_order j hodd

end CFSG.LocalAnalysis.WeakClosure81

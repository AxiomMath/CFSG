module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight56U14CoverDefs
import CFSG.LargeExtraspecial.A2ModOrdCard
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
import CFSG.GroupTheory.SupCommute
import CFSG.RankThree.PartOne.K133.Count
import CFSG.LocalAnalysis.AGLEmbedding.A15ComponentsAux
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65Z0
import all CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSpor)

private theorem covbarrank_exists_minimal {B : Type} [Group B] [Finite B] {K : Subgroup B}
    [K.Normal] (hK : K ≠ ⊥) :
    ∃ S : Subgroup B, S.Normal ∧ S ≠ ⊥ ∧ S ≤ K ∧
      ∀ M : Subgroup B, M.Normal → M ≤ S → M = ⊥ ∨ M = S := by
  obtain ⟨S, ⟨hSn, hS1, hSK⟩, hmin⟩ :=
    (Set.toFinite {M : Subgroup B | M.Normal ∧ M ≠ ⊥ ∧ M ≤ K}).exists_minimal
      ⟨K, inferInstance, hK, le_rfl⟩
  refine ⟨S, hSn, hS1, hSK, fun M hM hle => ?_⟩
  by_cases hM1 : M = ⊥
  · exact Or.inl hM1
  · exact Or.inr (le_antisymm hle (hmin ⟨hM, hM1, hle.trans hSK⟩ hle))

private theorem covbarrank_three_dvd {B : Type} [Group B] (ho3 : CFSG.pPrimeCore 3 B = ⊥)
    {U : Subgroup B} (hU : U.Normal) (hne : U ≠ ⊥) : 3 ∣ Nat.card U := by
  by_contra h
  exact hne (CFSG.pPrimeCore_eq_bot_iff.mp ho3 U hU
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h))

private theorem covbarrank_no_pair {B : Type} [Group B] [Finite B] {K : Subgroup B}
    (h1 : CFSG.Open.pRank 3 K = 1) {a b : B} (ha : a ∈ K) (hb : b ∈ K)
    (hao : orderOf a = 3) (hbo : orderOf b = 3) (hab : a * b = b * a)
    (hne : a ∉ Subgroup.zpowers b) : False := by
  have ha3 : a ^ 3 = 1 := by rw [← hao]; exact pow_orderOf_eq_one a
  have hb3 : b ^ 3 = 1 := by rw [← hbo]; exact pow_orderOf_eq_one b
  have hcomm : ∀ y ∈ Subgroup.zpowers b, y * a = a * y := by
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_left (show Commute b a from hab.symm) n).eq
  have hel : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers b ⊔ Subgroup.zpowers a) := by
    refine CFSG.Open.IsElemAbelian.sup_of_commute (CFSG.Open.isElemAbelian_zpowers hb3)
      (CFSG.Open.isElemAbelian_zpowers ha3) ?_
    intro x hx w hw
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact (Commute.zpow_zpow (show Commute b a from hab.symm) n m).eq
  have hcard : Nat.card (Subgroup.zpowers b ⊔ Subgroup.zpowers a : Subgroup B) = 3 ^ 2 := by
    rw [CFSG.RankThree.PartOne.K133.card_sup_zpowers (Y := Subgroup.zpowers b) (b := a)
      Nat.prime_three hao hcomm hne, Nat.card_zpowers, hbo]
    norm_num
  have hle : Subgroup.zpowers b ⊔ Subgroup.zpowers a ≤ K :=
    sup_le (Subgroup.zpowers_le.2 hb) (Subgroup.zpowers_le.2 ha)
  have := CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) hle hel hcard
  omega

private theorem covbarrank_factor_pair {B : Type} [Group B] {S : Subgroup B} {r : ℕ}
    {T : Fin r → Subgroup B} {e : ((i : Fin r) → ↥(T i)) ≃* ↥S}
    (he : ∀ (i : Fin r) (x : (j : Fin r) → ↥(T j)), (∀ j, j ≠ i → x j = 1) →
      ((e x : ↥S) : B) = ((x i : ↥(T i)) : B))
    {i j : Fin r} (hij : i ≠ j) {a b : B} (ha : a ∈ T i) (hb : b ∈ T j) :
    a * b = b * a ∧ (a ∈ T j → a = 1) := by
  classical
  have hsingle : ∀ (k : Fin r) (c : B) (hc : c ∈ T k),
      ((e (Pi.mulSingle k (⟨c, hc⟩ : ↥(T k))) : ↥S) : B) = c := by
    intro k c hc
    rw [he k _ (fun l hl => Pi.mulSingle_eq_of_ne hl _)]
    simp
  refine ⟨?_, fun haj => ?_⟩
  · have hc : Commute (Pi.mulSingle i (⟨a, ha⟩ : ↥(T i)) : (k : Fin r) → ↥(T k))
        (Pi.mulSingle j (⟨b, hb⟩ : ↥(T j))) := Pi.mulSingle_commute hij _ _
    have h := congrArg (fun x => ((e x : ↥S) : B)) hc.eq
    simpa only [map_mul, Subgroup.coe_mul, hsingle] using h
  · have h : Pi.mulSingle i (⟨a, ha⟩ : ↥(T i)) = Pi.mulSingle j (⟨a, haj⟩ : ↥(T j)) :=
      e.injective (Subtype.ext ((hsingle i a ha).trans (hsingle j a haj).symm))
    have h2 := congrFun h i
    rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hij] at h2
    exact congrArg Subtype.val h2

private theorem covbarrank_simple {B : Type} [Group B] [Finite B] {K S : Subgroup B}
    (ho3 : CFSG.pPrimeCore 3 B = ⊥) (h1 : CFSG.Open.pRank 3 K = 1)
    (hSn : S.Normal) (hS1 : S ≠ ⊥) (hSK : S ≤ K)
    (hmin : ∀ M : Subgroup B, M.Normal → M ≤ S → M = ⊥ ∨ M = S) :
    IsSimpleGroup ↥S := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨r, T, hr, hTS, hTs, hTc, -, e, he⟩ :=
    CFSG.LocalCores.minimal_normal_simple_factors hSn hS1 hmin
  have hcard : ∀ i j, Nat.card (T i) = Nat.card (T j) := by
    intro i j
    obtain ⟨g, hg⟩ := hTc i j
    rw [hg]
    exact (Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective).symm
  have h3 : ∀ i, 3 ∣ Nat.card (T i) := by
    have hS3 : 3 ∣ ∏ i, Nat.card (T i) := by
      rw [← Nat.card_pi, Nat.card_congr e.toEquiv]
      exact covbarrank_three_dvd ho3 hSn hS1
    obtain ⟨i, -, hi⟩ := (Nat.prime_three.prime.dvd_finset_prod_iff _).mp hS3
    exact fun j => (hcard j i) ▸ hi
  have hr1 : r = 1 := by
    by_contra hne
    let i₀ : Fin r := ⟨0, by omega⟩
    let i₁ : Fin r := ⟨1, by omega⟩
    have hij : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥(T i₀)) 3 (h3 i₀)
    obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥(T i₁)) 3 (h3 i₁)
    have hpair := covbarrank_factor_pair he hij a.2 b.2
    have hao : orderOf (a : B) = 3 := by rw [Subgroup.orderOf_coe]; exact ha
    have hbo : orderOf (b : B) = 3 := by rw [Subgroup.orderOf_coe]; exact hb
    refine covbarrank_no_pair h1 (hSK (hTS i₀ a.2)) (hSK (hTS i₁ b.2)) hao hbo hpair.1 ?_
    intro hmem
    have haj : (a : B) ∈ T i₁ := (Subgroup.zpowers_le.2 b.2) hmem
    have h1' := hpair.2 haj
    rw [h1', orderOf_one] at hao
    omega
  subst hr1
  have hST : S ≤ T 0 := by
    intro s hs
    obtain ⟨x, hx⟩ := e.surjective ⟨s, hs⟩
    have h := he 0 x (fun j hj => absurd (Subsingleton.elim j 0) hj)
    rw [hx] at h
    have hs' : s = ((x 0 : ↥(T 0)) : B) := h
    rw [hs']
    exact (x 0).2
  have hTeq : T 0 = S := le_antisymm (hTS 0) hST
  rw [← hTeq]
  exact hTs 0

private theorem covbarrank_abelian_false {B : Type} [Group B] [Finite B] {Z K S : Subgroup B}
    (h1 : CFSG.Open.pRank 3 K = 1) (hZ : Nat.card Z = 3) (hZK : Z ≤ K) (hZn : ¬ Z.Normal)
    (hSn : S.Normal) (hSK : S ≤ K) (hSs : IsSimpleGroup ↥S) (h3 : 3 ∣ Nat.card S)
    (hcomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := hSn
  let : CommGroup ↥S := { (inferInstance : Group ↥S) with
    mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  have hp : (Nat.card S).Prime := IsSimpleGroup.prime_card
  have hS3 : Nat.card S = 3 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3).symm
  have : IsCyclic ↥S := isCyclic_of_prime_card hS3
  have hmul : Nat.card (MulAut ↥S) = 2 := by
    rw [IsCyclic.card_mulAut, hS3, Nat.totient_prime Nat.prime_three]
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := ↥S) 3 h3
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥Z) 3 (by simp [hZ])
  have hso : orderOf (s : B) = 3 := by rw [Subgroup.orderOf_coe]; exact hs
  have hzo : orderOf (z : B) = 3 := by rw [Subgroup.orderOf_coe]; exact hz
  have hact : (MulAut.conjNormal (H := S) (z : B)) = 1 := by
    have h2 : ∀ g : MulAut ↥S, g ^ 2 = 1 := fun g => hmul ▸ pow_card_eq_one'
    have h3' : (MulAut.conjNormal (H := S) (z : B)) ^ 3 = 1 := by
      rw [← map_pow, ← hzo, pow_orderOf_eq_one, map_one]
    generalize MulAut.conjNormal (H := S) (z : B) = g at h3' ⊢
    calc g = g ^ 3 * (g ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3', h2, inv_one, mul_one]
  have hzs : (z : B) * (s : B) = (s : B) * z := by
    have h := congrArg (fun g : MulAut ↥S => ((g s : ↥S) : B)) hact
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h
  refine covbarrank_no_pair h1 (hSK s.2) (hZK z.2) hso hzo hzs.symm ?_
  intro hmem
  have hzcard : Nat.card (Subgroup.zpowers (z : B)) = 3 := by rw [Nat.card_zpowers, hzo]
  have hscard : Nat.card (Subgroup.zpowers (s : B)) = 3 := by rw [Nat.card_zpowers, hso]
  have hZeq : Subgroup.zpowers (z : B) = Z :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 z.2) (le_of_eq (by rw [hZ, hzcard]))
  have hSeq : Subgroup.zpowers (s : B) = S :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 s.2) (le_of_eq (by rw [hS3, hscard]))
  have hSZ : S ≤ Z := by
    rw [← hSeq, ← hZeq]
    exact Subgroup.zpowers_le.2 hmem
  exact hZn ((Subgroup.eq_of_le_of_card_ge hSZ (le_of_eq (by rw [hS3, hZ]))) ▸ hSn)

private theorem covbarrank_center {B : Type} [Group B] [Finite B] {Z K S : Subgroup B}
    (ho3 : CFSG.pPrimeCore 3 B = ⊥) (h1 : CFSG.Open.pRank 3 K = 1) (hZ : Nat.card Z = 3)
    (hZK : Z ≤ K) (hZn : ¬ Z.Normal) (hSn : S.Normal) (hS1 : S ≠ ⊥) (hSK : S ≤ K)
    (hmin : ∀ M : Subgroup B, M.Normal → M ≤ S → M = ⊥ ∨ M = S) :
    IsSimpleGroup ↥S ∧ S ⊓ Subgroup.centralizer (S : Set B) = ⊥ := by
  have hSs := covbarrank_simple ho3 h1 hSn hS1 hSK hmin
  refine ⟨hSs, ?_⟩
  have := hSn
  rcases hmin (S ⊓ Subgroup.centralizer (S : Set B)) inferInstance inf_le_left with h | h
  · exact h
  · refine (covbarrank_abelian_false h1 hZ hZK hZn hSn hSK hSs
      (covbarrank_three_dvd ho3 hSn hS1) fun a ha b hb => ?_).elim
    have hmem : a ∈ S ⊓ Subgroup.centralizer (S : Set B) := by
      rw [h]
      exact ha
    exact (Subgroup.mem_centralizer_iff.mp hmem.2 b hb).symm

private theorem covbarrank_le_sup {B : Type} [Group B] [Finite B] (hSch : UCK.KSch)
    {S L : Subgroup B} [S.Normal] (hS : IsSimpleGroup ↥S) (hSk : CFSG.Open.IsKGroup ↥S)
    (hL : ⁅L, L⁆ = L) : L ≤ S ⊔ Subgroup.centralizer (S : Set B) :=
  CFSG.AGLEmbedding.perfect_le_sup_centralizer_of_outer (hSch ↥S hS hSk) hL
    (by rw [Subgroup.normalizer_eq_top_iff.mpr ‹S.Normal›]; exact le_top)

private theorem covbarrank_proj {G : Type} [Group G] {A C Q : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a) (hdisj : A ⊓ C = ⊥) (hQ : Q ≤ A ⊔ C) :
    ∃ ψ : ↥Q →* G, (∀ q, ψ q ∈ A) ∧ ∀ q : ↥Q, ψ q = 1 → (q : G) ∈ C := by
  have hdec : ∀ q : ↥Q, ∃ a ∈ A, ∃ c ∈ C, a * c = (q : G) := fun q =>
    (CFSG.mem_sup_of_commute fun a ha c hc => hcomm a ha c hc).mp (hQ q.2)
  have huniq : ∀ {a a' c c' : G}, a ∈ A → a' ∈ A → c ∈ C → c' ∈ C → a * c = a' * c' →
      a = a' := by
    intro a a' c c' ha ha' hc hc' h
    have h1 : a'⁻¹ * a = c' * c⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * c) * c⁻¹ := by group
        _ = a'⁻¹ * (a' * c') * c⁻¹ := by rw [h]
        _ = c' * c⁻¹ := by group
    have hmem : a'⁻¹ * a ∈ A ⊓ C :=
      ⟨A.mul_mem (A.inv_mem ha') ha, h1 ▸ C.mul_mem hc' (C.inv_mem hc)⟩
    rw [hdisj, Subgroup.mem_bot] at hmem
    exact (inv_mul_eq_one.mp hmem).symm
  choose a ha c hc hac using hdec
  refine ⟨MonoidHom.mk' a fun q₁ q₂ => ?_, ha, fun q hq => ?_⟩
  · refine huniq (ha (q₁ * q₂)) (A.mul_mem (ha q₁) (ha q₂)) (hc (q₁ * q₂))
      (C.mul_mem (hc q₁) (hc q₂)) ?_
    have h21 := hcomm (a q₂) (ha q₂) (c q₁) (hc q₁)
    calc a (q₁ * q₂) * c (q₁ * q₂) = (q₁ : G) * q₂ := hac _
      _ = (a q₁ * c q₁) * (a q₂ * c q₂) := by rw [hac, hac]
      _ = a q₁ * (c q₁ * a q₂) * c q₂ := by group
      _ = a q₁ * (a q₂ * c q₁) * c q₂ := by rw [← h21]
      _ = a q₁ * a q₂ * (c q₁ * c q₂) := by group
  · have h1 : a q = 1 := hq
    have h2 := hac q
    rw [h1, one_mul] at h2
    rw [← h2]
    exact hc q

open scoped commutatorElement in
private theorem covbarrank_image {G : Type} [Group G] [Finite G] {Q : Subgroup G}
    (hQ : CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP 3 1 ↥Q)
    (ψ : ↥Q →* G) (hker : ∀ q : ↥Q, ψ q = 1 → q ∈ Subgroup.center ↥Q) :
    ∃ E : Subgroup G, E ≤ ψ.range ∧ CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have hQ' := hQ
  unfold CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP at hQ'
  obtain ⟨hcard, hexp, hcomm, hcenter⟩ := hQ'
  by_cases hker1 : ψ.ker = ⊥
  · obtain ⟨E₀, hE₀Q, hE₀, hE₀card⟩ := exists_elemAbelian_nine_le_of_isExtraspecialExpP hQ
    have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).1 hker1
    refine ⟨(E₀.subgroupOf Q).map ψ, Subgroup.map_le_range ψ _, ?_, ?_⟩
    · exact CFSG.SectionRank.isElemAbelian_map (hE₀.comap Q.subtype_injective) ψ
    · rw [Subgroup.card_map_of_injective hinj,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₀Q).toEquiv, hE₀card]
  · have hle : ψ.ker ≤ Subgroup.center ↥Q := fun q hq => hker q hq
    have hdvd : Nat.card ψ.ker ∣ Nat.card (Subgroup.center ↥Q) := Subgroup.card_dvd_of_le hle
    rw [hcenter] at hdvd
    have hkc : ψ.ker = Subgroup.center ↥Q := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd (Subgroup.card_eq_one.mp h) hker1
      · exact Subgroup.eq_of_le_of_card_ge hle (by rw [h, hcenter])
    refine ⟨ψ.range, le_rfl, ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
    · obtain ⟨a', ha'⟩ := a.2
      obtain ⟨b', hb'⟩ := b.2
      have hc : ⁅a', b'⁆ ∈ ψ.ker := by
        rw [hkc, ← hcomm, _root_.commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      have hψ : ⁅ψ a', ψ b'⁆ = 1 := by
        rw [← map_commutatorElement]
        exact hc
      exact Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, ← ha', ← hb']
        exact commutatorElement_eq_one_iff_mul_comm.mp hψ)
    · obtain ⟨q, rfl⟩ := hx
      have h3 : q ^ 3 = 1 := hexp ▸ Monoid.pow_exponent_eq_one q
      rw [← map_pow, h3, map_one]
    · have h27 : Nat.card ↥Q = 27 := by rw [hcard]; norm_num
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, h27, hkc,
        hcenter] at h1
      omega

private theorem covbarrank_two_le {G : Type} [Group G] [Finite G] {A C Q : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a) (hdisj : A ⊓ C = ⊥) (hQ : Q ≤ A ⊔ C)
    (hext : CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP 3 1 ↥Q)
    (hker : ∀ q ∈ Q, q ∈ C → ∀ q' ∈ Q, q' * q = q * q') :
    ∃ E : Subgroup G, E ≤ A ∧ CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨ψ, hψA, hψC⟩ := covbarrank_proj hcomm hdisj hQ
  obtain ⟨E, hE, hel, hcard⟩ := covbarrank_image hext ψ fun q hq => by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hker q q.2 (hψC q hq) g g.2)
  refine ⟨E, fun x hx => ?_, hel, hcard⟩
  obtain ⟨q, rfl⟩ := hE hx
  exact hψA q

theorem false_of_coverBar_rankOne {B : Type} [Group B] [Finite B] {Z Q L N : Subgroup B}
    (hB : CoverBar Z Q L N) (hSch : UCK.KSch)
    (h1 : CFSG.Open.pRank 3 (normalClosure (Z : Set B)) = 1) : False := by
  have hZQ : Z ≤ Q := by
    rw [hB.zq, ZOf]
    exact inf_le_left
  have hZne : Z ≠ ⊥ := by
    intro h
    have := hB.zcard
    rw [h, Subgroup.card_bot] at this
    omega
  have hZK : Z ≤ normalClosure (Z : Set B) := Subgroup.le_normalClosure
  have hZn : ¬ Z.Normal := by
    intro hn
    have hKZ : normalClosure (Z : Set B) ≤ Z := Subgroup.normalClosure_le_normal fun x hx => hx
    exact hB.kn (hKZ.trans (Subgroup.le_normalizer.trans (hB.nq Z hZQ hZne)))
  have hKne : normalClosure (Z : Set B) ≠ ⊥ := fun h => hZne (le_bot_iff.mp (hZK.trans h.le))
  obtain ⟨S, hSn, hS1, hSK, hmin⟩ := covbarrank_exists_minimal hKne
  obtain ⟨hSs, hSc⟩ := covbarrank_center hB.o3 h1 hB.zcard hZK hZn hSn hS1 hSK hmin
  have := hSn
  have hLS : L ≤ S ⊔ Subgroup.centralizer (S : Set B) :=
    covbarrank_le_sup hSch hSs (hB.kgroup.subgroup S) (Subgroup.isPerfect_iff.mp hB.lq.1)
  have hZC : ¬ Z ≤ Subgroup.centralizer (S : Set B) := by
    intro hZC
    have hSC : S ≤ Subgroup.centralizer (S : Set B) :=
      hSK.trans (Subgroup.normalClosure_le_normal hZC)
    have hSbot := le_inf (le_refl S) hSC
    rw [hSc] at hSbot
    exact hS1 (le_bot_iff.mp hSbot)
  have hLC : ¬ L ≤ Subgroup.centralizer (S : Set B) := fun h => hZC ((hZQ.trans hB.ql).trans h)
  have hLCc : (Subgroup.centralizer (S : Set B)).subgroupOf L ≤ Subgroup.center ↥L := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hB.lq
      (N := (Subgroup.centralizer (S : Set B)).subgroupOf L) inferInstance with h | h
    · exact absurd (Subgroup.subgroupOf_eq_top.mp h) hLC
    · exact h
  have hker : ∀ q ∈ Q, q ∈ Subgroup.centralizer (S : Set B) → ∀ q' ∈ Q, q' * q = q * q' := by
    intro q hq hqC q' hq'
    have hmem : (⟨q, hB.ql hq⟩ : ↥L) ∈ (Subgroup.centralizer (S : Set B)).subgroupOf L := hqC
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp (hLCc hmem) ⟨q', hB.ql hq'⟩)
  obtain ⟨E, hES, hE, hcard⟩ := covbarrank_two_le
    (fun a ha c hc => Subgroup.mem_centralizer_iff.mp hc a ha) hSc (hB.ql.trans hLS) hB.qext hker
  have h2 := CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) (hES.trans hSK) hE
    (k := 2) (by rw [hcard]; norm_num)
  omega

private theorem covbarnot_proj {G : Type} [Group G] {A C Q : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a) (hdisj : A ⊓ C = ⊥) (hQ : Q ≤ A ⊔ C) :
    ∃ ψ : ↥Q →* G, (∀ q, ψ q ∈ A) ∧ ∀ q : ↥Q, ψ q = 1 → (q : G) ∈ C := by
  have hdec : ∀ q : ↥Q, ∃ a ∈ A, ∃ c ∈ C, a * c = (q : G) := fun q =>
    (CFSG.mem_sup_of_commute fun a ha c hc => hcomm a ha c hc).mp (hQ q.2)
  have huniq : ∀ {a a' c c' : G}, a ∈ A → a' ∈ A → c ∈ C → c' ∈ C → a * c = a' * c' →
      a = a' := by
    intro a a' c c' ha ha' hc hc' h
    have h1 : a'⁻¹ * a = c' * c⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * c) * c⁻¹ := by group
        _ = a'⁻¹ * (a' * c') * c⁻¹ := by rw [h]
        _ = c' * c⁻¹ := by group
    have hmem : a'⁻¹ * a ∈ A ⊓ C :=
      ⟨A.mul_mem (A.inv_mem ha') ha, h1 ▸ C.mul_mem hc' (C.inv_mem hc)⟩
    rw [hdisj, Subgroup.mem_bot] at hmem
    exact (inv_mul_eq_one.mp hmem).symm
  choose a ha c hc hac using hdec
  refine ⟨MonoidHom.mk' a fun q₁ q₂ => ?_, ha, fun q hq => ?_⟩
  · refine huniq (ha (q₁ * q₂)) (A.mul_mem (ha q₁) (ha q₂)) (hc (q₁ * q₂))
      (C.mul_mem (hc q₁) (hc q₂)) ?_
    have h21 := hcomm (a q₂) (ha q₂) (c q₁) (hc q₁)
    calc a (q₁ * q₂) * c (q₁ * q₂) = (q₁ : G) * q₂ := hac _
      _ = (a q₁ * c q₁) * (a q₂ * c q₂) := by rw [hac, hac]
      _ = a q₁ * (c q₁ * a q₂) * c q₂ := by group
      _ = a q₁ * (a q₂ * c q₁) * c q₂ := by rw [← h21]
      _ = a q₁ * a q₂ * (c q₁ * c q₂) := by group
  · have h1 : a q = 1 := hq
    have h2 := hac q
    rw [h1, one_mul] at h2
    rw [← h2]
    exact hc q

open scoped commutatorElement in
private theorem covbarnot_image {G : Type} [Group G] [Finite G] {Q : Subgroup G}
    (hQ : CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP 3 1 ↥Q)
    (ψ : ↥Q →* G) (hker : ∀ q : ↥Q, ψ q = 1 → q ∈ Subgroup.center ↥Q) :
    ∃ E : Subgroup G, E ≤ ψ.range ∧ CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have hQ' := hQ
  unfold CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP at hQ'
  obtain ⟨hcard, hexp, hcomm, hcenter⟩ := hQ'
  by_cases hker1 : ψ.ker = ⊥
  · obtain ⟨E₀, hE₀Q, hE₀, hE₀card⟩ := exists_elemAbelian_nine_le_of_isExtraspecialExpP hQ
    have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).1 hker1
    refine ⟨(E₀.subgroupOf Q).map ψ, Subgroup.map_le_range ψ _, ?_, ?_⟩
    · exact CFSG.SectionRank.isElemAbelian_map (hE₀.comap Q.subtype_injective) ψ
    · rw [Subgroup.card_map_of_injective hinj,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₀Q).toEquiv, hE₀card]
  · have hle : ψ.ker ≤ Subgroup.center ↥Q := fun q hq => hker q hq
    have hdvd : Nat.card ψ.ker ∣ Nat.card (Subgroup.center ↥Q) := Subgroup.card_dvd_of_le hle
    rw [hcenter] at hdvd
    have hkc : ψ.ker = Subgroup.center ↥Q := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd (Subgroup.card_eq_one.mp h) hker1
      · exact Subgroup.eq_of_le_of_card_ge hle (by rw [h, hcenter])
    refine ⟨ψ.range, le_rfl, ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
    · obtain ⟨a', ha'⟩ := a.2
      obtain ⟨b', hb'⟩ := b.2
      have hc : ⁅a', b'⁆ ∈ ψ.ker := by
        rw [hkc, ← hcomm, _root_.commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      have hψ : ⁅ψ a', ψ b'⁆ = 1 := by
        rw [← map_commutatorElement]
        exact hc
      exact Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, ← ha', ← hb']
        exact commutatorElement_eq_one_iff_mul_comm.mp hψ)
    · obtain ⟨q, rfl⟩ := hx
      have h3 : q ^ 3 = 1 := hexp ▸ Monoid.pow_exponent_eq_one q
      rw [← map_pow, h3, map_one]
    · have h27 : Nat.card ↥Q = 27 := by rw [hcard]; norm_num
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, h27, hkc,
        hcenter] at h1
      omega

private theorem covbarnot_two_le {G : Type} [Group G] [Finite G] {A C Q : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a) (hdisj : A ⊓ C = ⊥) (hQ : Q ≤ A ⊔ C)
    (hext : CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP 3 1 ↥Q)
    (hker : ∀ q ∈ Q, q ∈ C → ∀ q' ∈ Q, q' * q = q * q') :
    ∃ E : Subgroup G, E ≤ A ∧ CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨ψ, hψA, hψC⟩ := covbarnot_proj hcomm hdisj hQ
  obtain ⟨E, hE, hel, hcard⟩ := covbarnot_image hext ψ fun q hq => by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hker q q.2 (hψC q hq) g g.2)
  refine ⟨E, fun x hx => ?_, hel, hcard⟩
  obtain ⟨q, rfl⟩ := hE hx
  exact hψA q

private theorem covbarnot_ker {B : Type} [Group B] {Q L X : Subgroup B} [X.Normal]
    (hlq : CFSG.IsQuasisimple ↥L) (hQL : Q ≤ L) (hX : ¬ L ≤ X) :
    ∀ q ∈ Q, q ∈ X → ∀ q' ∈ Q, q' * q = q * q' := by
  intro q hq hqX q' hq'
  have hLX : X.subgroupOf L ≤ Subgroup.center ↥L := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hlq (N := X.subgroupOf L)
      inferInstance with h | h
    · exact absurd (Subgroup.subgroupOf_eq_top.mp h) hX
    · exact h
  have hmem : (⟨q, hQL hq⟩ : ↥L) ∈ X.subgroupOf L := hqX
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp (hLX hmem) ⟨q', hQL hq'⟩)

private theorem covbarnot_inf_centralizer {B : Type} [Group B] {K : Subgroup B}
    (hc : Subgroup.center ↥K = ⊥) : K ⊓ Subgroup.centralizer (K : Set B) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hmem : (⟨x, hx.1⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 g g.2)
  rw [hc, Subgroup.mem_bot] at hmem
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hmem)

private theorem covbarnot_rank {B : Type} [Group B] [Finite B] {K E₁ E₂ : Subgroup B}
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup B) ≤ 3)
    (hKC : K ⊓ Subgroup.centralizer (K : Set B) = ⊥) (hE₁K : E₁ ≤ K)
    (hE₂C : E₂ ≤ Subgroup.centralizer (K : Set B))
    (hE₁ : CFSG.Open.IsElemAbelian 3 E₁) (hE₂ : CFSG.Open.IsElemAbelian 3 E₂)
    (hc₁ : Nat.card E₁ = 9) (hc₂ : Nat.card E₂ = 9) : False := by
  have hcomm : ∀ x ∈ E₁, ∀ y ∈ E₂, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp (hE₂C hy) x (hE₁K hx)
  have hdisj : E₁ ⊓ E₂ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ K ⊓ Subgroup.centralizer (K : Set B) := ⟨hE₁K hx.1, hE₂C hx.2⟩
    rwa [hKC] at hx'
  have hel : CFSG.Open.IsElemAbelian 3 (E₁ ⊔ E₂) := hE₁.sup_of_commute hE₂ hcomm
  have hcard : Nat.card ↥(E₁ ⊔ E₂) = 3 ^ 4 := by
    rw [CFSG.RankThree.PartOne.K133.card_sup_of_commute_disjoint hcomm hdisj, hc₁, hc₂]
    norm_num
  have h4 := CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) (le_top : E₁ ⊔ E₂ ≤ ⊤) hel hcard
  omega

theorem false_of_coverBar_not_le {B : Type} [Group B] [Finite B] {Z Q L N : Subgroup B}
    (hB : CoverBar Z Q L N) (hOut : KFactK332TypesOut)
    (hK : LieModel ↥(normalClosure (Z : Set B)) .PSU 3 3 1 ∨
      (∃ r f : ℕ, r.Prime ∧ LieModel ↥(normalClosure (Z : Set B)) .G2 0 r f) ∨
      IsSpor ↥(normalClosure (Z : Set B)) .J2)
    (hLK : ¬ L ≤ normalClosure (Z : Set B)) : False := by
  set K : Subgroup B := normalClosure (Z : Set B) with hKdef
  have hKn : K.Normal := Subgroup.normalClosure_normal
  have hZQ : Z ≤ Q := by
    rw [hB.zq, ZOf]
    exact inf_le_left
  have hZne : Z ≠ ⊥ := by
    intro h
    have := hB.zcard
    rw [h, Subgroup.card_bot] at this
    omega
  obtain ⟨⟨z, hzZ⟩, hz1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZne
  have hz1 : z ≠ 1 := fun h => hz1' (Subtype.ext h)
  have hzK : z ∈ K := Subgroup.subset_normalClosure hzZ
  obtain ⟨hc, hsolv⟩ := hOut ↥K hK
  have hKC : K ⊓ Subgroup.centralizer (K : Set B) = ⊥ := covbarnot_inf_centralizer hc
  have hLC : ¬ L ≤ Subgroup.centralizer (K : Set B) := by
    intro h
    have hz : z ∈ K ⊓ Subgroup.centralizer (K : Set B) := ⟨hzK, h ((hZQ.trans hB.ql) hzZ)⟩
    rw [hKC, Subgroup.mem_bot] at hz
    exact hz1 hz
  have hLS : L ≤ K ⊔ Subgroup.centralizer (K : Set B) :=
    CFSG.AGLEmbedding.perfect_le_sup_centralizer_of_outer hsolv
      (Subgroup.isPerfect_iff.mp hB.lq.1)
      (by rw [Subgroup.normalizer_eq_top_iff.mpr hKn]; exact le_top)
  obtain ⟨E₁, hE₁K, hE₁, hc₁⟩ := covbarnot_two_le (A := K)
    (C := Subgroup.centralizer (K : Set B)) (Q := Q)
    (fun a ha c hc => Subgroup.mem_centralizer_iff.mp hc a ha) hKC (hB.ql.trans hLS) hB.qext
    (covbarnot_ker hB.lq hB.ql hLC)
  obtain ⟨E₂, hE₂C, hE₂, hc₂⟩ := covbarnot_two_le (A := Subgroup.centralizer (K : Set B))
    (C := K) (Q := Q) (fun a ha c hc => (Subgroup.mem_centralizer_iff.mp ha c hc).symm)
    (by rw [inf_comm]; exact hKC) (by rw [sup_comm]; exact hB.ql.trans hLS) hB.qext
    (covbarnot_ker hB.lq hB.ql hLK)
  exact covbarnot_rank hB.rank hKC hE₁K hE₂C hE₁ hE₂ hc₁ hc₂

private theorem covbarsmall_five_dvd {X : Type} [Group X] [Finite X] (h : IsCoverShape X) :
    5 ∣ Nat.card X := by
  have h5 : 5 ∣ Nat.card (X ⧸ Subgroup.center X) := by
    rcases h.2.2 with ha | ha | ha
    · obtain ⟨e⟩ := ha
      rw [Nat.card_congr e.toEquiv,
        CFSG.RankThree.PartTwo.KFacts.KS14.card_alternatingGroup_fin (by norm_num)]
      norm_num [Nat.factorial]
    · obtain ⟨e⟩ := ha
      rw [Nat.card_congr e.toEquiv,
        CFSG.RankThree.PartTwo.KFacts.KS14.card_alternatingGroup_fin (by norm_num)]
      norm_num [Nat.factorial]
    · obtain ⟨e⟩ := ha
      rw [Nat.card_congr e.toEquiv]
      change 5 ∣ Nat.card ↥CFSG.Blueprint.NativeSporadic.M22
      rw [CFSG.RankThree.PartTwo.KFacts.KS14.card_nativeM22]
      norm_num
  exact h5.trans ⟨Nat.card (Subgroup.center X),
    Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X)⟩

private theorem covbarsmall_zpowers {B : Type} [Group B] [Finite B] {Z : Subgroup B}
    (hZ : Nat.card Z = 3) : ∃ z : B, z ∈ Z ∧ orderOf z = 3 ∧ Subgroup.zpowers z = Z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥Z) 3 (by simp [hZ])
  have hzo : orderOf (z : B) = 3 := by rw [Subgroup.orderOf_coe]; exact hz
  refine ⟨z, z.2, hzo, Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 z.2)
    (le_of_eq ?_)⟩
  rw [hZ, Nat.card_zpowers, hzo]

private theorem covbarsmall_le_cent {B : Type} [Group B] {Z L K : Subgroup B} {z : B}
    (hlcz : L ≤ Subgroup.centralizer (Z : Set B)) (hzZ : z ∈ Z) (hzK : z ∈ K) :
    L.subgroupOf K ≤ Subgroup.centralizer ({(⟨z, hzK⟩ : ↥K)} : Set ↥K) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hlcz (Subgroup.mem_subgroupOf.mp hx)) z hzZ)

private theorem covbarsmall_norm {B : Type} [Group B] {Z L K : Subgroup B} {z : B}
    (hlcz : L ≤ Subgroup.centralizer (Z : Set B))
    (hlnorm : (L.subgroupOf (Subgroup.centralizer (Z : Set B))).Normal)
    (hzK : z ∈ K) (hZ : Subgroup.zpowers z = Z) :
    ((L.subgroupOf K).subgroupOf
      (Subgroup.centralizer ({(⟨z, hzK⟩ : ↥K)} : Set ↥K))).Normal := by
  refine ⟨fun l hl n => ?_⟩
  have hn : (((n : ↥K) : B)) ∈ Subgroup.centralizer (Z : Set B) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [← hZ] at hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hc : (⟨z, hzK⟩ : ↥K) * (n : ↥K) = (n : ↥K) * ⟨z, hzK⟩ :=
      Subgroup.mem_centralizer_iff.mp n.2 _ (Set.mem_singleton _)
    exact (Commute.zpow_left (show Commute z ((n : ↥K) : B) from congrArg Subtype.val hc) k).eq
  have hl' : (((l : ↥K) : B)) ∈ L := Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hl)
  have hmem := hlnorm.conj_mem ⟨((l : ↥K) : B), hlcz hl'⟩ hl' ⟨((n : ↥K) : B), hn⟩
  exact hmem

theorem false_of_coverBar_u33 {B : Type} [Group B] [Finite B] {Z Q L N : Subgroup B}
    (hB : CoverBar Z Q L N)
    (hK : LieModel ↥(normalClosure (Z : Set B)) .PSU 3 3 1)
    (hLK : L ≤ normalClosure (Z : Set B)) : False := by
  have hLd : Nat.card ↥L ∣ Nat.card ↥(normalClosure (Z : Set B)) := Subgroup.card_dvd_of_le hLK
  rw [CFSG.LargeExtraspecial.A2Mod.Ord.card_of_lieModel_PSU33 hK] at hLd
  have h5 := (covbarsmall_five_dvd hB.lcov).trans hLd
  omega

theorem false_of_coverBar_g2 {B : Type} [Group B] [Finite B] {Z Q L N : Subgroup B}
    (hB : CoverBar Z Q L N) (hG2 : KFactG2CentCover)
    (hK : ∃ r f : ℕ, r.Prime ∧ LieModel ↥(normalClosure (Z : Set B)) .G2 0 r f)
    (hLK : L ≤ normalClosure (Z : Set B)) : False := by
  obtain ⟨r, f, hr, hmod⟩ := hK
  obtain ⟨z, hzZ, hzo, hZ⟩ := covbarsmall_zpowers hB.zcard
  have hzK : z ∈ normalClosure (Z : Set B) := Subgroup.subset_normalClosure hzZ
  have hZQ : Z ≤ Q := by
    rw [hB.zq, ZOf]
    exact inf_le_left
  have hzL : z ∈ L := hB.ql (hZQ hzZ)
  have hord : orderOf (⟨z, hzK⟩ : ↥(normalClosure (Z : Set B))) = 3 := by
    rw [← Subgroup.orderOf_coe]
    exact hzo
  exact hG2 ↥(normalClosure (Z : Set B)) r f hr hmod ⟨z, hzK⟩ hord
    (L.subgroupOf (normalClosure (Z : Set B))) (covbarsmall_le_cent hB.lcz hzZ hzK)
    (covbarsmall_norm hB.lcz hB.lnorm hzK hZ) hzL
    (IsCoverShape.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLK).symm hB.lcov)

private theorem covbarj2_factorization : (604800 : ℕ).factorization 3 = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Nat.factorization_def _ Nat.prime_three]
  have h : (604800 : ℕ) = 3 ^ 3 * 22400 := by norm_num
  rw [h, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

private theorem covbarj2_card_q {B : Type} [Group B] {Q : Subgroup B}
    (hQ : CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP 3 1 ↥Q) :
    Nat.card ↥Q = 27 := by
  unfold CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP at hQ
  rw [hQ.1]
  norm_num

private theorem covbarj2_sylow {B : Type} [Group B] [Finite B] {Q K : Subgroup B}
    (hQK : Q ≤ K) (hK : Nat.card K = 604800) (hQ : Nat.card Q = 27) :
    CFSG.ABGLocalTools.IsSylowOf 3 (Q.subgroupOf K) ⊤ ∧ Q.subgroupOf K ≠ ⊥ := by
  have hcard : Nat.card ↥(Q.subgroupOf K) = 27 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQK).toEquiv, hQ]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨CFSG.ABGLocalTools.isSylowOf_of_card le_top ?_, ?_⟩
  · rw [hcard, Subgroup.card_top, hK, covbarj2_factorization]
    norm_num
  · intro h
    rw [h, Subgroup.card_bot] at hcard
    omega

private theorem covbarj2_rank {B : Type} [Group B] [Finite B] {Q K : Subgroup B}
    (hQK : Q ≤ K)
    (hQ : CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP 3 1 ↥Q) :
    1 < CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) := by
  obtain ⟨E, hEQ, hE, hcard⟩ := exists_elemAbelian_nine_le_of_isExtraspecialExpP hQ
  have h2 := CFSG.SectionRank.le_pRank (p := 3) (by norm_num : 1 < 3)
    (le_top : E.subgroupOf K ≤ ⊤) (hE.comap K.subtype_injective) (k := 2)
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hEQ.trans hQK)).toEquiv, hcard]; norm_num)
  omega

private theorem covbarj2_gamma_le {B : Type} [Group B] [Finite B] {Q N : Subgroup B}
    (K : Subgroup B)
    (hnq : ∀ A : Subgroup B, A ≤ Q → A ≠ ⊥ → Subgroup.normalizer (A : Set B) ≤ N) :
    CFSG.Open.rankThreeGamma 1 3 (Q.subgroupOf K) ≤ N.subgroupOf K := by
  refine CFSG.HardMathSupport.Solomon.Proving.GLBCore_le_of_forall fun A hAQ hA => ?_
  have hne : A ≠ ⊥ := by
    rintro rfl
    obtain ⟨E, hEA, -, hEc⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) (⊥ : Subgroup ↥K)
    rw [le_bot_iff.mp hEA, Subgroup.card_bot] at hEc
    have h3 : 3 ≤ 3 ^ CFSG.Open.pRank 3 (⊥ : Subgroup ↥K) :=
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hA
    omega
  have hle : A.map K.subtype ≤ Q := by
    rintro _ ⟨a, ha, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hAQ ha)
  have hne' : A.map K.subtype ≠ ⊥ := fun h =>
    hne ((Subgroup.map_eq_bot_iff_of_injective A K.subtype_injective).mp h)
  intro y hy
  exact hnq _ hle hne' (Subgroup.le_normalizer_map K.subtype (Subgroup.mem_map_of_mem K.subtype hy))

theorem false_of_coverBar_j2 {B : Type} [Group B] [Finite B] {Z Q L N : Subgroup B}
    (hB : CoverBar Z Q L N) (hΓ : KFactGammaStrong) (hJ : KFactJ2NoStrong)
    (hK : IsSpor ↥(normalClosure (Z : Set B)) .J2)
    (hLK : L ≤ normalClosure (Z : Set B)) : False := by
  have hQK : Q ≤ normalClosure (Z : Set B) := hB.ql.trans hLK
  have hKcard : Nat.card ↥(normalClosure (Z : Set B)) = 604800 :=
    CFSG.RankThree.PartTwo.KFacts.KS14.card_eq_of_j2 hK
  obtain ⟨hsyl, hne⟩ := covbarj2_sylow hQK hKcard (covbarj2_card_q hB.qext)
  have hrank := covbarj2_rank hQK hB.qext
  have hKg : CFSG.Open.IsKGroup ↥(normalClosure (Z : Set B)) := hB.kgroup.subgroup _
  have hΓtop : CFSG.Open.rankThreeGamma 1 3 (Q.subgroupOf (normalClosure (Z : Set B))) = ⊤ := by
    by_contra h
    exact hJ _ hKg hK hrank _ (hΓ _ 3 Nat.prime_three _ hsyl hne h)
  have hle := covbarj2_gamma_le (normalClosure (Z : Set B)) hB.nq
  rw [hΓtop] at hle
  apply hB.kn
  intro x hx
  exact Subgroup.mem_subgroupOf.mp (hle (Subgroup.mem_top (⟨x, hx⟩ : ↥(normalClosure (Z : Set B)))))

theorem false_of_coverBar {B : Type} [Group B] [Finite B] {Z Q L N : Subgroup B}
    (hB : CoverBar Z Q L N) (hK : K332OutBar (normalClosure (Z : Set B)))
    (hSch : UCK.KSch) (hG2 : KFactG2CentCover) (hOut : KFactK332TypesOut)
    (hΓ : KFactGammaStrong) (hJ : KFactJ2NoStrong) : False := by
  rcases hK with h1 | hu | hg | hj
  · exact false_of_coverBar_rankOne hB hSch h1
  · by_cases hLK : L ≤ normalClosure (Z : Set B)
    · exact false_of_coverBar_u33 hB hu hLK
    · exact false_of_coverBar_not_le hB hOut (Or.inl hu) hLK
  · by_cases hLK : L ≤ normalClosure (Z : Set B)
    · exact false_of_coverBar_g2 hB hG2 hg hLK
    · exact false_of_coverBar_not_le hB hOut (Or.inr (Or.inl hg)) hLK
  · by_cases hLK : L ≤ normalClosure (Z : Set B)
    · exact false_of_coverBar_j2 hB hΓ hJ hj hLK
    · exact false_of_coverBar_not_le hB hOut (Or.inr (Or.inr hj)) hLK

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

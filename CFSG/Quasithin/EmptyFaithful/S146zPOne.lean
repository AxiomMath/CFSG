module

public import CFSG.Quasithin.EmptyFaithful.S1469Inputs
public import CFSG.Quasithin.Vol2.Ch1Eight
public import CFSG.Quasithin.Vol2.Ch1Rank
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourSylow

public section

namespace CFSG.Quasithin

namespace P1469One

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem normalizer_le_normalizer_centralizer' {D : Subgroup G} :
    Subgroup.normalizer (D : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (D : Set G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (D : Set G), ∀ c ∈ Subgroup.centralizer (D : Set G),
      g * c * g⁻¹ ∈ Subgroup.centralizer (D : Set G) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have hd' : g⁻¹ * d * g ∈ D := by
      simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) d).mp hd
    have h1 := (Subgroup.mem_centralizer_iff.mp hc) _ hd'
    calc d * (g * c * g⁻¹) = g * ((g⁻¹ * d * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * d * g)) * g⁻¹ := by rw [h1]
      _ = (g * c * g⁻¹) * d := by group
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨key g hg c, fun h => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hg) _ h
  simpa [mul_assoc] using this

omit [Finite G] in
theorem mul_mem_of_relIndex_two {T N : Subgroup G} (hTN : (T ⊓ N).relIndex T = 2) {p p' : G}
    (hp : p ∈ T) (hp' : p' ∈ T) (hiff : p ∈ N ↔ p' ∈ N) : p' * p ∈ N := by
  by_cases hpN : p ∈ N
  · exact N.mul_mem (hiff.mp hpN) hpN
  · have hp'N : p' ∉ N := fun h => hpN (hiff.mpr h)
    have hidx : ((T ⊓ N).subgroupOf T).index = 2 := hTN
    obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.mp hidx
    have hxor : ∀ b : ↥T, b ∉ (T ⊓ N).subgroupOf T → b * a ∈ (T ⊓ N).subgroupOf T := fun b hb =>
      (ha b).elim (fun h => h.1) (fun h => absurd h.1 hb)
    have hpH : (⟨p, hp⟩ : ↥T) ∉ (T ⊓ N).subgroupOf T := fun h =>
      hpN (Subgroup.mem_subgroupOf.mp h).2
    have hp'H : (⟨p', hp'⟩ : ↥T) ∉ (T ⊓ N).subgroupOf T := fun h =>
      hp'N (Subgroup.mem_subgroupOf.mp h).2
    have h1 := ((T ⊓ N).subgroupOf T).mul_mem (hxor _ hp'H)
      (((T ⊓ N).subgroupOf T).inv_mem (hxor _ hpH))
    have h2 := ((T ⊓ N).subgroupOf T).mul_mem h1 (Subgroup.sq_mem_of_index_two hidx ⟨p, hp⟩)
    have e : (⟨p', hp'⟩ : ↥T) * a * ((⟨p, hp⟩ : ↥T) * a)⁻¹ * (⟨p, hp⟩ : ↥T) ^ 2 =
        ⟨p', hp'⟩ * ⟨p, hp⟩ := by group
    rw [e] at h2
    exact (Subgroup.mem_subgroupOf.mp h2).2

omit [Finite G] in
theorem blockProduct_le_normalizer_centralizer {I S K₁ K₂ : Subgroup G}
    (h : IsBlockProduct I S 2 ![K₁, K₂]) :
    I ≤ Subgroup.normalizer
      ((S ⊓ Subgroup.centralizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) : Subgroup G) : Set G) := by
  obtain ⟨-, -, -, -, hI, -, hperm⟩ := h
  set D : Subgroup G := S ⊓ Subgroup.centralizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) with hD
  have hKD : ∀ x ∈ K₁ ⊔ K₂, x ∈ Subgroup.centralizer (D : Set G) := fun x hx => by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact ((Subgroup.mem_centralizer_iff.mp hd.2) x hx).symm
  have hle : ∀ i : Fin 2, ∀ s ∈ S, B6.conjSub s (![K₁, K₂] i) ≤ K₁ ⊔ K₂ := by
    intro i s hs
    obtain ⟨j, hj⟩ := hperm s hs i
    rw [hj]
    fin_cases j
    · exact le_sup_left
    · exact le_sup_right
  have key : ∀ s ∈ S, B6.conjSub s (K₁ ⊔ K₂) ≤ K₁ ⊔ K₂ := by
    intro s hs
    rw [(B6.conjSub s).map_sup]
    exact sup_le (hle 0 s hs) (hle 1 s hs)
  have hSK : ∀ s ∈ S, s ∈ Subgroup.normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) := fun s hs =>
    B6.mem_normalizer_of_conjSub_le (key s hs) (key s⁻¹ (S.inv_mem hs))
  have hSN : ∀ s ∈ S, s ∈ Subgroup.normalizer (D : Set G) := fun s hs =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hs, normalizer_le_normalizer_centralizer' (hSK s hs)⟩
  rw [hI]
  refine sup_le hSN (iSup_le fun i x hx => ?_)
  have hx' : x ∈ K₁ ⊔ K₂ := by
    fin_cases i
    · exact (le_sup_left : K₁ ≤ K₁ ⊔ K₂) hx
    · exact (le_sup_right : K₂ ≤ K₁ ⊔ K₂) hx
  exact Subgroup.centralizer_le_normalizer _ (hKD x hx')

omit [Finite G] in
theorem pCoreOf_normalizer_ne_bot {D : Subgroup G} (hD : D ≠ ⊥) (h2 : IsPGroup 2 D) :
    pCoreOf 2 (Subgroup.normalizer (D : Set G)) ≠ ⊥ := by
  intro hbot
  apply hD
  have h1 : D ≤ pCoreOf 2 (Subgroup.normalizer (D : Set G)) :=
    le_pCoreOf_of_le_normalizer Subgroup.le_normalizer le_rfl h2
  exact le_bot_iff.mp (hbot ▸ h1)

omit [Finite G] in
theorem le_of_eq_sup_of_relIndex_two {X Y W P T N : Subgroup G} (hYX : Y ≤ X) (hY : oTwoUpper Y = Y)
    (hX : X = W ⊔ P) (hWN : W ≤ N) (hPT : P ≤ T) (hPX : X ≤ Subgroup.normalizer (P : Set G))
    (hTN : (T ⊓ N).relIndex T = 2) : Y ≤ N := by
  have hWP : W ≤ Subgroup.normalizer (P : Set G) := (hX ▸ le_sup_left : W ≤ X).trans hPX
  have hsq : ∀ x ∈ X, x ^ 2 ∈ N := by
    intro x hx
    have hx' : x ∈ ((W ⊔ P : Subgroup G) : Set G) := hX ▸ hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right W P hWP] at hx'
    obtain ⟨w, hw, p, hp, rfl⟩ := hx'
    have hp' : w⁻¹ * p * w ∈ P := by
      simpa using (Subgroup.mem_normalizer_iff.mp (hWP (W.inv_mem hw)) p).mp hp
    have hiff : p ∈ N ↔ w⁻¹ * p * w ∈ N := by
      constructor
      · intro h
        exact N.mul_mem (N.mul_mem (N.inv_mem (hWN hw)) h) (hWN hw)
      · intro h
        have := N.mul_mem (N.mul_mem (hWN hw) h) (N.inv_mem (hWN hw))
        simpa [mul_assoc] using this
    have h1 := mul_mem_of_relIndex_two hTN (hPT hp) (hPT hp') hiff
    have e : (w * p) ^ 2 = w * w * ((w⁻¹ * p * w) * p) := by rw [pow_two]; group
    rw [e]
    exact N.mul_mem (N.mul_mem (hWN hw) (hWN hw)) h1
  refine hY.symm.le.trans ((Subgroup.closure_le _).mpr fun x hx => ?_)
  obtain ⟨m, hm⟩ := hx.2
  have hpow : x ^ (2 * m + 1) = 1 := hm ▸ pow_orderOf_eq_one x
  have e : x = (x ^ 2) ^ (m + 1) := by
    rw [← pow_mul, show 2 * (m + 1) = (2 * m + 1) + 1 by ring, pow_succ, hpow, one_mul]
  rw [SetLike.mem_coe, e]
  exact N.pow_mem (hsq x (hYX hx.1)) _

theorem exists_cComp_two_conjugates (hQ : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h128 : Lemma128One) {H S B : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) (hS : IsSylowTwoOf S H)
    (hBH : B ≤ H) (hB : quasithinIsLocal S B) {t : G} (ht : t ∈ S)
    (hne : B.map (MulAut.conj t).toMonoidHom ≠ B) :
    ∃ K ∈ cComp H, B ≤ K ∧ Set.ncard (conjSubgroupsBy H K) = 2 := by
  obtain ⟨K, hK, hBK⟩ :=
    lemma_1_2_4_exists hQ hs hnab h37 h39 hH hS hBH (mem_lFamily_of_isLocal hB)
  refine ⟨K, hK, hBK, ?_⟩
  have hKloc : quasithinIsLocal S K := isLocal_of_mem_cComp_of_sylow hS hH hK
  have hKt := (lemma_1_2_8_one_conj hQ hs hnab h37 h128 hB hKloc hBK ht hne).1
  rcases lemma_1_2_1_three hQ hs hnab h37 h38 hH hK with hn | ⟨hcard, -⟩
  · exfalso
    refine hKt ?_
    have hNK : H ≤ Subgroup.normalizer (K : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (le_of_mem_cComp hK)).mp hn
    exact A38.map_conj_eq_iff.mpr (hNK (hS.1 ht))
  · exact hcard

theorem exists_orderOf_three_of_isAltType_five {K : Subgroup G} (hK : IsAltType K 5) :
    ∃ x ∈ K, orderOf x = 3 := by
  obtain ⟨α, hα, -, -⟩ := hK
  have h60 : Nat.card (alternatingGroup (Fin 5)) ∣ Nat.card K := Subgroup.card_dvd_of_surjective hα
  have hc : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  have h3 : 3 ∣ Nat.card K := (by norm_num : 3 ∣ 60).trans (hc ▸ h60)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
  exact ⟨x, x.2, (Subgroup.orderOf_coe x).trans hx⟩

theorem three_dvd_card_modPCore_of_isAltType_five {K L : Subgroup G} (hK : IsAltType K 5)
    (hKL : K ≤ L) : 3 ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hxK, hx3⟩ := exists_orderOf_three_of_isAltType_five hK
  have hxL : x ∈ L := hKL hxK
  have hx3' : orderOf (⟨x, hxL⟩ : ↥L) = 3 := by rw [Subgroup.orderOf_mk]; exact hx3
  have hq : orderOf (QuotientGroup.mk (⟨x, hxL⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) = 3 := by
    apply orderOf_eq_prime
    · rw [← QuotientGroup.mk_pow, ← hx3', pow_orderOf_eq_one]; rfl
    · intro h
      have hmem : (⟨x, hxL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := (QuotientGroup.eq_one_iff _).1 h
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨_, hmem⟩
      have hdvd : 3 ∣ 2 ^ k := hx3' ▸ orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hk)
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd) (by norm_num)
  rw [← hq]
  exact orderOf_dvd_natCard _

omit [Finite G] in
theorem ne_of_commutator_eq_bot {A B : Subgroup G} (hA : A ≠ ⊥) (hp : ⁅A, A⁆ = A) (h : ⁅A, B⁆ = ⊥) :
    A ≠ B := by
  rintro rfl
  exact hA (hp.symm.trans h)

theorem le_centralizer_of_mem_cComp {H L K D : Subgroup G} (hL : L ∈ cComp H)
    (hLD : L ≤ Subgroup.normalizer (D : Set G)) (hKL : K ≤ L) (hK : K ≠ ⊥) (hKp : ⁅K, K⁆ = K)
    (hKD : K ≤ Subgroup.centralizer (D : Set G)) : L ≤ Subgroup.centralizer (D : Set G) := by
  by_contra hne
  have hlt : L ⊓ Subgroup.centralizer (D : Set G) < L :=
    lt_of_le_of_ne inf_le_left fun h => hne (h ▸ inf_le_right)
  have hnorm : ((L ⊓ Subgroup.centralizer (D : Set G)).subgroupOf L).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
    intro l hl
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hl, normalizer_le_normalizer_centralizer' (hLD hl)⟩
  have hsub : IsSubnormal (L ⊓ Subgroup.centralizer (D : Set G)) L :=
    A3.subnormal_of_normal inf_le_left hnorm
  have hbot := perfectCore_eq_bot_of_subnormal_lt hL hsub hlt
  have hle := le_perfectCore_of_perfect (le_inf hKL hKD) hKp
  exact hK (le_bot_iff.mp (hbot ▸ hle))

omit [Finite G] in
theorem conjClosure_le_centralizer {L H D : Subgroup G} (hH : H ≤ Subgroup.normalizer (D : Set G))
    (hL : L ≤ Subgroup.centralizer (D : Set G)) :
    conjClosure L H ≤ Subgroup.centralizer (D : Set G) := by
  refine conjClosure_le fun h hh z hz => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  have hd' : h⁻¹ * d * h ∈ D := by
    simpa using (Subgroup.mem_normalizer_iff.mp (hH (H.inv_mem hh)) d).mp hd
  have key := (Subgroup.mem_centralizer_iff.mp (hL hz)) _ hd'
  calc d * (h * z * h⁻¹) = h * ((h⁻¹ * d * h) * z) * h⁻¹ := by group
    _ = h * (z * (h⁻¹ * d * h)) * h⁻¹ := by rw [key]
    _ = (h * z * h⁻¹) * d := by group

theorem le_closure_three_of_autOn_card {Y H V : Subgroup G} (hY : oTwoUpper Y = Y) (hYH : Y ≤ H)
    (hYV : Y ≤ Subgroup.normalizer (V : Set G))
    (hc : pCoreOf 2 Y = Y ⊓ Subgroup.centralizer (V : Set G)) (hcard : Nat.card (autOn Y V) = 3) :
    Y ≤ Subgroup.closure {x : G | x ∈ H ∧ ∃ k : ℕ, orderOf x = 3 ^ k} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine hY.symm.le.trans ((Subgroup.closure_le _).mpr fun x hx =>
    Subgroup.subset_closure ⟨hYH hx.1, ?_⟩)
  have hxY : x ∈ Y := hx.1
  have hmem : A4.actionOn V Y hYV ⟨x, hxY⟩ ∈ autOn Y V := (A4.mem_autOn_iff hYV).mpr ⟨_, rfl⟩
  have ha3 : (A4.actionOn V Y hYV ⟨x, hxY⟩) ^ 3 = 1 := by
    have h1 := pow_card_eq_one' (x := (⟨_, hmem⟩ : ↥(autOn Y V)))
    rw [hcard] at h1
    exact congrArg Subtype.val h1
  have hker : x ^ 3 ∈ pCoreOf 2 Y := by
    rw [hc]
    refine ⟨Y.pow_mem hxY 3, ?_⟩
    have h1 : A4.actionOn V Y hYV ((⟨x, hxY⟩ : ↥Y) ^ 3) = 1 := by rw [map_pow]; exact ha3
    exact (A4.actionOn_eq_one_iff hYV _).mp h1
  have hx3 : x ^ 3 = 1 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp (LieType.BorelTits.pCoreOf_isPGroup 2 Y) ⟨x ^ 3, hker⟩
    have hk' : orderOf (x ^ 3) = 2 ^ k := (Subgroup.orderOf_coe _).trans hk
    have hodd : Odd (orderOf (x ^ 3)) := hx.2.of_dvd_nat (orderOf_pow_dvd 3)
    rw [hk'] at hodd
    have hk0 : k = 0 := by
      by_contra hne
      exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, hne⟩)
    rw [hk0, pow_zero] at hk'
    exact orderOf_eq_one_iff.mp hk'
  rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hx3) with h | h
  · exact ⟨0, by simp [h]⟩
  · exact ⟨1, by simp [h]⟩

theorem input1469A5DOne_of_stages (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h128 : Lemma128One) (h122 : Lemma122A) : Input1469A5DOne := by
  intro G _ _ T M H u I K₁ K₂ ρ c hf hD hLT
  have S : Setting146 G T M := c.ctx.setting
  set D : Subgroup G := dOf1469 T I K₁ K₂ with hDdef
  set N : Subgroup G := Subgroup.normalizer (D : Set G) with hNdef
  have hDle : D ≤ T ⊓ I := inf_le_left
  have hIN : I ≤ N := blockProduct_le_normalizer_centralizer c.blocks
  obtain ⟨-, hTN, hSyl⟩ := c.obs_a D hDle hD hIN
  have hrel : (T ⊓ I).relIndex T = 2 := by
    rw [hf.d]
    exact c.ctx.hu.index_two
  have hD2 : IsPGroup 2 D := S.hyp.sylow.1.to_le (hDle.trans inf_le_left)
  have hNcore : pCoreOf 2 N ≠ ⊥ := pCoreOf_normalizer_ne_bot hD hD2
  have hTIN : T ⊓ I ≤ N := by
    rw [← hTN]
    exact inf_le_right
  have hYN : yOfL22 T M ≤ N := by
    refine le_of_eq_sup_of_relIndex_two (X := yOfL22 T M ⊔ T)
      (P := pCoreOf 2 (yOfL22 T M ⊔ T)) (T := T) le_sup_left (oTwoUpper_yOfL22 T M) hLT ?_ ?_ ?_ ?_
    · exact sup_le ((oTwoUpper_le _).trans inf_le_right) hTIN
    · exact pCoreOf_two_le_of_sylowIn le_sup_right S.hyp.sylow.1
        (isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow le_sup_right).2.2
    · exact LieType.BorelTits.le_normalizer_pCoreOf (r := 2) _
    · rw [hTN]
      exact hrel
  have hK1blk : IsBlock2 I K₁ := (c.blocks.2.2.1 0).1
  have hK1 : K₁ ∈ cComp I :=
    L238.mem_cComp_of_isChi0Block_nonsolvable hK1blk (Or.inr c.a5.1)
  have hK1I : K₁ ≤ I := hK1blk.2.1
  have hIcore : pCoreOf 2 I ≠ ⊥ := by
    intro hbot
    apply hD
    have h1 : D ≤ pCoreOf 2 I := by
      rw [hf.g2]
      exact le_sup_left
    exact le_bot_iff.mp (hbot ▸ h1)
  have hloc : quasithinIsLocal (T ⊓ I) K₁ :=
    isLocal_of_mem_cComp_of_sylow c.ctx.minPar.isSylow hIcore hK1
  have hcomm : ⁅K₁, K₂⁆ = ⊥ := c.blocks.2.2.2.1 0 1 (by decide)
  have hK12 : K₁ ≠ K₂ :=
    ne_of_commutator_eq_bot (ne_bot_of_mem_cComp hK1) (perfect_of_mem_cComp hK1) hcomm
  obtain ⟨t, htS, ht⟩ := c.blocks.2.2.2.2.2.1 0 1
  have hne : K₁.map (MulAut.conj t).toMonoidHom ≠ K₁ := fun h => hK12 (h.symm.trans ht)
  obtain ⟨K, hKc, hK1K, hKcard⟩ := exists_cComp_two_conjugates S.hyp.qtke S.hyp.simple
    S.hyp.nonabelian h37 h38 h39 h128 hNcore hSyl (hK1I.trans hIN) hloc htS hne
  have hK3 : 3 ∣ Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) :=
    three_dvd_card_modPCore_of_isAltType_five c.a5.1 hK1K
  have hK1D : K₁ ≤ Subgroup.centralizer (D : Set G) := by
    intro x hx d hd
    exact ((Subgroup.mem_centralizer_iff.mp hd.2) x ((le_sup_left : K₁ ≤ K₁ ⊔ K₂) hx)).symm
  have hKD : K ≤ Subgroup.centralizer (D : Set G) :=
    le_centralizer_of_mem_cComp hKc (le_of_mem_cComp hKc) hK1K (ne_bot_of_mem_cComp hK1)
      (perfect_of_mem_cComp hK1) hK1D
  have hcl := h122 G S.hyp.simple S.hyp.qtke S.hyp.nonabelian N K hNcore hKc 3 Nat.prime_three
    (by norm_num) hKcard hK3
  have hYM : yOfL22 T M ≤ Subgroup.normalizer ((VZ T M : Subgroup G) : Set G) :=
    (yOfL22_le T M).trans (le_normalizer_conjClosure _ M)
  have hYcl : yOfL22 T M ≤ Subgroup.closure {x : G | x ∈ N ∧ ∃ k : ℕ, orderOf x = 3 ^ k} :=
    le_closure_three_of_autOn_card (oTwoUpper_yOfL22 T M) hYN hYM S.facts.y_oTwo S.facts.y_card
  have hYD : yOfL22 T M ≤ Subgroup.centralizer (D : Set G) :=
    hYcl.trans (hcl ▸ conjClosure_le_centralizer le_rfl hKD)
  intro hbot
  apply hD
  refine le_bot_iff.mp (hbot ▸ le_inf (hDle.trans inf_le_left) fun d hd y hy => ?_)
  exact ((Subgroup.mem_centralizer_iff.mp (hYD hy)) d hd).symm

end P1469One

end CFSG.Quasithin

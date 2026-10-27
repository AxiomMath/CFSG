module

public import CFSG.Blueprint.LieModelAPI
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.StatementsEleven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.StatementsNineFifteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightPrelim
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsTwentyEight
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.QuotInfBar2
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21b
public import CFSG.LocalAnalysis.UniquenessCase.UC22S218N
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.GroupTheory.CoprimeFixedPointOrder
public import CFSG.Quasithin.H13.KGFactLieOutAbL
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Timmesfeld.Bridge.RootSetsConn3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem kOutDiagSp4 {X : Type} [Group X] [Finite X] {a : ℕ} (h : IsSp4 X a)
    (α β : MulAut X) : α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : X →* MulAut X).range := by
  have hm : StatedClassicalModel X .PSp 2 2 a := h.statedClassicalModel (by decide)
  have hcyc : IsCyclic (Outer X) :=
    CFSG.Quasithin.H13.KGInsp4316.outer_cyclic_psp4 hm
  obtain ⟨g, hg⟩ :=
    CFSG.Quasithin.H13.KGLieOut.inner_of_outer_comm
      (CFSG.Quasithin.H13.KGInsp4316.comm_of_isCyclic hcyc) α β
  exact ⟨g, hg.symm⟩

theorem orderOf_odd_and_squarefree_of_mem_calB1 {T M L A : Subgroup G}
    (hA : A ∈ calB1 T M L) {x : G} (hx : x ∈ A) :
    Odd (orderOf x) ∧ Squarefree (orderOf x) := by
  refine ⟨?_, Ctx23L.orderOf_squarefree_of_mem_calB1 hA hx⟩
  obtain ⟨-, hAcomm, B, C, hBmem, -, hCodd, -, hAeq, -, -, -⟩ := hA
  rw [hAeq] at hx hAcomm
  haveI : IsMulCommutative ↥(B ⊔ C) := hAcomm
  have hBcent : B ≤ Subgroup.centralizer (C : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have h := IsMulCommutative.is_comm.comm
      (⟨b, Subgroup.mem_sup_left hb⟩ : ↥(B ⊔ C))
      (⟨c, Subgroup.mem_sup_right hc⟩ : ↥(B ⊔ C))
    exact congrArg Subtype.val h.symm
  have hBC : B ≤ Subgroup.normalizer (C : Set G) :=
    hBcent.trans (Subgroup.centralizer_le_normalizer (C : Set G))
  have hxmem : x ∈ (B : Set G) * (C : Set G) := by
    have hx' : x ∈ ((B ⊔ C : Subgroup G) : Set G) := hx
    rwa [Subgroup.coe_mul_of_left_le_normalizer_right B C hBC] at hx'
  obtain ⟨b, hbB, c, hcC, hbc⟩ := hxmem
  have hcomm : Commute b c := by
    have h := IsMulCommutative.is_comm.comm
      (⟨b, Subgroup.mem_sup_left hbB⟩ : ↥(B ⊔ C))
      (⟨c, Subgroup.mem_sup_right hcC⟩ : ↥(B ⊔ C))
    exact congrArg Subtype.val h
  have hbo : Odd (orderOf b) :=
    hBmem.2.2.2.1.of_dvd_nat (Subgroup.orderOf_dvd_natCard B hbB)
  have hco : Odd (orderOf c) := hCodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard C hcC)
  rw [← hbc]
  exact (hbo.mul hco).of_dvd_nat hcomm.orderOf_mul_dvd_mul_orderOf

theorem exists_prime_order_zpowers_of_not_mem {H K : Type} [Group H] [Finite H] [Group K]
    (φ : H →* K) (N : Subgroup K) (b : H) (hSq : Squarefree (orderOf b)) (hb : φ b ∉ N) :
    ∃ b' ∈ Subgroup.zpowers b, (orderOf b').Prime ∧ φ b' ∉ N := by
  by_contra hcon
  push Not at hcon
  have hle : Subgroup.closure {y : H | y ∈ Subgroup.zpowers b ∧ (orderOf y).Prime} ≤
      N.comap φ := by
    refine (Subgroup.closure_le (N.comap φ)).mpr ?_
    rintro y ⟨hy, hyp⟩
    exact hcon y hy hyp
  exact hb (hle (CFSG.GroupTheory.mem_closure_prime_powers_of_squarefree hSq))

private theorem le_normalizer_of_subgroupOf_normal {M L : Subgroup G} (hLM : L ≤ M)
    (hN : (L.subgroupOf M).Normal) : M ≤ Subgroup.normalizer (L : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hN

theorem isSU3_bar2_of_isU3 {K : Subgroup G} (hq : CFSG.Open.IsQuasisimple (Bar2 K)) {a : ℕ}
    (h : IsU3 (BarInf K ⧸ Subgroup.center (BarInf K)) a) : IsSU3 (Bar2 K) a := by
  refine ⟨hq, ?_⟩
  exact CFSG.Blueprint.LieModel.of_mulEquiv (quotInfEquivBar2 hq) h

private theorem card_solvableRadical_eq_card_pCore_mul_center {K : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (Bar2 K)) :
    Nat.card (CFSG.solvableRadical ↥K) =
      Nat.card (CFSG.pCore 2 ↥K) * Nat.card (Subgroup.center (Bar2 K)) := by
  classical
  haveI : (CFSG.pCore 2 ↥K).Normal := CFSG.pCore_normal
  have hle : CFSG.pCore 2 ↥K ≤ CFSG.solvableRadical ↥K := CFSG.pCore_le_solvableRadical 2 ↥K
  let S : Subgroup ↥K := CFSG.solvableRadical ↥K
  let T : Subgroup ↥S := (CFSG.pCore 2 ↥K).subgroupOf S
  let f : ↥S →* Bar2 K := (QuotientGroup.mk' (CFSG.pCore 2 ↥K)).comp S.subtype
  have hker : f.ker = T := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact QuotientGroup.eq_one_iff (S.subtype y)
  have hrange : f.range = Subgroup.center (Bar2 K) := by
    have h1 : f.range = S.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.1, y.2, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨y, hy⟩, rfl⟩
    rw [h1]
    exact uc22p21k_map_solvableRadical_eq_center hq
  have h1 : Nat.card ↥S = Nat.card (↥S ⧸ T) * Nat.card T :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup T
  have h2 : Nat.card (↥S ⧸ T) = Nat.card (Subgroup.center (Bar2 K)) := by
    rw [← hker, ← hrange]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  have h3 : Nat.card T = Nat.card (CFSG.pCore 2 ↥K) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [h1, h2, h3, Nat.mul_comm]

private theorem not_dvd_card_solvableRadical {K : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (Bar2 K)) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hr3 : r ≠ 3) (hZ3 : Nat.card (Subgroup.center (Bar2 K)) ∣ 3) :
    ¬ r ∣ Nat.card (CFSG.solvableRadical ↥K) := by
  intro hdvd
  rw [card_solvableRadical_eq_card_pCore_mul_center hq] at hdvd
  rcases hr.dvd_mul.mp hdvd with h | h
  · obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).exists_card_eq
    rw [hk] at h
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h))
  · exact hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp (h.trans hZ3))

private theorem exists_prime_induced_not_mem {D : Data G} {Ch : Choice2011 G}
    {c : Ctx21 D Ch} {L : Subgroup G}
    (N : Subgroup (MulAut (BarInf L ⧸ Subgroup.center (BarInf L))))
    {b : G} (hbB : b ∈ c.B) (hbN : b ∈ normalizer (L : Set G))
    (hSq : Squarefree (orderOf b)) (hOdd : Odd (orderOf b))
    (hθN : inducedQuotInfAut L b hbN ∉ N) :
    ∃ (b' : G) (_ : b' ∈ c.B) (hb'N : b' ∈ normalizer (L : Set G)),
      (orderOf b').Prime ∧ Odd (orderOf b') ∧ inducedQuotInfAut L b' hb'N ∉ N ∧
        orderOf (inducedQuotInfAut L b' hb'N) = orderOf b' := by
  classical
  let bN : ↥(Subgroup.normalizer (L : Set G)) := ⟨b, hbN⟩
  have hbSq : Squarefree (orderOf bN) := by
    rw [show orderOf bN = orderOf b from (Subgroup.orderOf_coe bN).symm]; exact hSq
  have hbφ : inducedQuotInfAutHom L bN ∉ N := hθN
  obtain ⟨b₀, hb₀mem, hb₀pr, hb₀N⟩ :=
    exists_prime_order_zpowers_of_not_mem (inducedQuotInfAutHom L) N bN hbSq hbφ
  have hb₀G : ((b₀ : ↥(Subgroup.normalizer (L : Set G))) : G) ∈ Subgroup.zpowers b := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb₀mem
    have h1 : ((b₀ : ↥(Subgroup.normalizer (L : Set G))) : G) = b ^ k := by
      rw [← hk, Subgroup.coe_zpow]
    rw [h1]
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
  have hodd : Odd (orderOf ((b₀ : ↥(Subgroup.normalizer (L : Set G))) : G)) := by
    refine hOdd.of_dvd_nat ?_
    rw [← Nat.card_zpowers, ← Nat.card_zpowers b]
    exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hb₀G)
  refine ⟨((b₀ : ↥(Subgroup.normalizer (L : Set G))) : G),
    (Subgroup.zpowers_le.mpr hbB) hb₀G, b₀.2, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe]; exact hb₀pr
  · exact hodd
  · exact hb₀N
  · rw [Subgroup.orderOf_coe]
    have hdvd : orderOf (inducedQuotInfAut L ((b₀ : _) : G) b₀.2) ∣ orderOf b₀ := by
      have h := orderOf_inducedQuotInfAut_dvd L (x := ((b₀ : _) : G)) b₀.2
      simpa [Subgroup.orderOf_coe] using h
    have hne : inducedQuotInfAut L ((b₀ : _) : G) b₀.2 ≠ 1 := by
      intro h1
      have h2 : inducedQuotInfAutHom L b₀ = 1 := h1
      exact hb₀N (h2 ▸ N.one_mem)
    have hne1 : orderOf (inducedQuotInfAut L ((b₀ : _) : G) b₀.2) ≠ 1 := fun h1 =>
      hne (orderOf_eq_one_iff.mp h1)
    rcases (Nat.dvd_prime hb₀pr).mp hdvd with h | h
    · exact absurd h hne1
    · exact h

private theorem false_of_conj_eq_inv {X : Type} [Group X] (N : Subgroup (MulAut X))
    {θ μ : MulAut X} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hθr : orderOf θ = r)
    (hμ : μ * θ * μ⁻¹ = θ⁻¹) (hN : μ * θ * μ⁻¹ * θ⁻¹ ∈ N) (hθN : θ ∉ N) : False := by
  rw [hμ] at hN
  obtain ⟨k, hk⟩ := hr.odd_of_ne_two hr2
  have hordg : orderOf (θ⁻¹) = r := by rw [orderOf_inv, hθr]
  have hpow : (θ⁻¹) = ((θ⁻¹) ^ 2) ^ (k + 1) := by
    have h1 : 2 * (k + 1) = orderOf (θ⁻¹) + 1 := by omega
    rw [← pow_mul, h1, pow_succ, pow_orderOf_eq_one, one_mul]
  have hmem : (θ⁻¹) ∈ N := by
    rw [hpow]
    exact N.pow_mem (by simpa [pow_two] using hN) (k + 1)
  exact hθN (by simpa using N.inv_mem hmem)

private theorem exists_orderOf_three_mem_centralizer {L : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (Bar2 L)) {b : G} (hbN : b ∈ normalizer (L : Set G))
    {r : ℕ} (hr : r.Prime) (hbr : orderOf b = r)
    (hcop : ¬ r ∣ Nat.card (CFSG.solvableRadical ↥L))
    {x : BarInf L ⧸ Subgroup.center (BarInf L)} (hx3 : orderOf x = 3)
    (hxfix : inducedQuotInfAut L b hbN x = x) :
    ∃ y : ↥L, (y : G) ∈ Subgroup.centralizer ({b} : Set G) ∧ orderOf (y : G) = 3 := by
  classical
  let ρ : MulAut ↥L := (Subgroup.normalizerMonoidHom L) ⟨b, hbN⟩
  have hcomm : ∀ l : ↥L, piBarInf L (ρ l) = inducedQuotInfAut L b hbN (piBarInf L l) := by
    intro l
    have hcoe : ((ρ l : ↥L) : G) = b * (l : G) * b⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨b, hbN⟩ l
    rw [inducedQuotInfAut_piBarInf]
    exact congrArg (piBarInf L) (Subtype.ext hcoe)
  have hρ : orderOf ρ ∣ r := by
    have h1 : orderOf ρ ∣ orderOf (⟨b, hbN⟩ : ↥(Subgroup.normalizer (L : Set G))) :=
      orderOf_map_dvd (Subgroup.normalizerMonoidHom L) ⟨b, hbN⟩
    have h2 : orderOf (⟨b, hbN⟩ : ↥(Subgroup.normalizer (L : Set G))) = orderOf b :=
      (Subgroup.orderOf_coe (⟨b, hbN⟩ : ↥(Subgroup.normalizer (L : Set G)))).symm
    rwa [h2, hbr] at h1
  have hcop' : ¬ r ∣ Nat.card (piBarInf L).ker := by rwa [piBarInf_ker hq]
  obtain ⟨y, hyord, hyfix⟩ :=
    CFSG.GroupTheory.exists_orderOf_eq_fixed_of_coprime_ker (piBarInf L)
      (piBarInf_surjective L) ρ (inducedQuotInfAut L b hbN) hcomm hr hρ hcop' hx3 hxfix
  have hconj : b * (y : G) * b⁻¹ = (y : G) := by
    have h1 : ((ρ y : ↥L) : G) = b * (y : G) * b⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨b, hbN⟩ y
    rw [← h1, hyfix]
  refine ⟨y, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    calc (y : G) * b = ((b * (y : G)) * b⁻¹) * b := by rw [hconj]
      _ = b * (y : G) := by group
  · simpa [Subgroup.orderOf_coe] using hyord

private theorem false_of_inverted {L : Subgroup G}
    (N : Subgroup (MulAut (BarInf L ⧸ Subgroup.center (BarInf L))))
    {b m : G} (hbN : b ∈ normalizer (L : Set G)) (hmN : m ∈ normalizer (L : Set G)) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hbr : orderOf b = r)
    (hθN : inducedQuotInfAut L b hbN ∉ N)
    (hcommN : ∀ α β : MulAut (BarInf L ⧸ Subgroup.center (BarInf L)),
      α * β * α⁻¹ * β⁻¹ ∈ N) (hmb : m * b * m⁻¹ = b⁻¹) : False := by
  have hθr : orderOf (inducedQuotInfAut L b hbN) = r := by
    have hdvd : orderOf (inducedQuotInfAut L b hbN) ∣ r := by
      have h := orderOf_inducedQuotInfAut_dvd L (x := b) hbN
      rwa [hbr] at h
    have hne : inducedQuotInfAut L b hbN ≠ 1 := fun h1 => hθN (h1 ▸ N.one_mem)
    have hne1 : orderOf (inducedQuotInfAut L b hbN) ≠ 1 := fun h1 =>
      hne (orderOf_eq_one_iff.mp h1)
    rcases (Nat.dvd_prime hr).mp hdvd with h | h
    · exact absurd h hne1
    · exact h
  have hμ : inducedQuotInfAut L m hmN * inducedQuotInfAut L b hbN *
      (inducedQuotInfAut L m hmN)⁻¹ = (inducedQuotInfAut L b hbN)⁻¹ := by
    have hEq : (⟨m, hmN⟩ : ↥(Subgroup.normalizer (L : Set G))) * ⟨b, hbN⟩ *
        ⟨m, hmN⟩⁻¹ = ⟨b⁻¹, (Subgroup.normalizer (L : Set G)).inv_mem hbN⟩ := by
      ext
      show m * b * m⁻¹ = b⁻¹
      exact hmb
    have h := congrArg (inducedQuotInfAutHom L) hEq
    rw [map_mul, map_mul, map_inv] at h
    rw [show (⟨b⁻¹, (Subgroup.normalizer (L : Set G)).inv_mem hbN⟩ :
        ↥(Subgroup.normalizer (L : Set G))) = (⟨b, hbN⟩)⁻¹ from rfl,
      map_inv (inducedQuotInfAutHom L) (⟨b, hbN⟩ : ↥(Subgroup.normalizer (L : Set G)))] at h
    simpa [inducedQuotInfAut] using h
  exact false_of_conj_eq_inv N hr hr2 hθr hμ (hcommN _ _) hθN

private theorem false_of_three_element {D : Data G} {Ch : Choice2011 G} {c : Ctx21 D Ch}
    {L : Subgroup G} (hL : L ∈ calC D.M) (hLN : (L.subgroupOf D.M).Normal)
    (N : Subgroup (MulAut (BarInf L ⧸ Subgroup.center (BarInf L))))
    {b : G} (hbB : b ∈ c.B) (hbN : b ∈ normalizer (L : Set G)) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hbr : orderOf b = r)
    (hθN : inducedQuotInfAut L b hbN ∉ N)
    (hcommN : ∀ α β : MulAut (BarInf L ⧸ Subgroup.center (BarInf L)),
      α * β * α⁻¹ * β⁻¹ ∈ N)
    (hsp3 : IsStronglyPEmbedded 3 D.M)
    (hcop : ¬ r ∣ Nat.card (CFSG.solvableRadical ↥L)) (h1930 : H1930 D)
    {x : BarInf L ⧸ Subgroup.center (BarInf L)} (hx3 : orderOf x = 3)
    (hxfix : inducedQuotInfAut L b hbN x = x) : False := by
  classical
  have hq : CFSG.Open.IsQuasisimple (Bar2 L) := hL.2.2
  obtain ⟨y, hycent, hyord⟩ :=
    exists_orderOf_three_mem_centralizer hq hbN hr hbr hcop hx3 hxfix
  let Y : Subgroup G := Subgroup.zpowers (y : G)
  have hYcard : Nat.card Y = 3 := by
    rw [show Y = Subgroup.zpowers (y : G) from rfl, Nat.card_zpowers, hyord]
  have hYle : Y ≤ D.M := (Subgroup.zpowers_le.mpr y.2).trans hL.1.le
  have hYne : Y ≠ ⊥ := by
    intro hbot
    have hyY : (y : G) ∈ Y := Subgroup.mem_zpowers (y : G)
    rw [hbot] at hyY
    have hy1 : (y : G) = 1 := by simpa using hyY
    rw [hy1, orderOf_one] at hyord
    omega
  have hYp : IsPGroup 3 ↥Y := IsPGroup.of_card (n := 1) (by rw [hYcard, pow_one])
  have hYuniq : Y ∈ uniqueSet D.M :=
    mem_uniqueSet_of_isStronglyPEmbedded (by norm_num) hsp3 hYle hYne hYp
  have hYcent : Y ≤ Subgroup.centralizer ({b} : Set G) := Subgroup.zpowers_le.mpr hycent
  have hYnorm : Y ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
    have h1 : Subgroup.centralizer ({b} : Set G) =
        Subgroup.centralizer (Subgroup.zpowers b : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact (h1 ▸ hYcent).trans (Subgroup.centralizer_le_normalizer _)
  have hAne : Subgroup.zpowers b ≠ ⊥ := by
    intro hbot
    have hb : b ∈ Subgroup.zpowers b := Subgroup.mem_zpowers b
    rw [hbot] at hb
    have hb1 : b = 1 := by simpa using hb
    rw [hb1, orderOf_one] at hbr
    exact hr.ne_one hbr.symm
  have hInv := s21_10 D Ch h1930 c (Subgroup.zpowers b) hAne
    (Subgroup.zpowers_le.mpr hbB) Y hYne ⟨3, by norm_num, hYp⟩ hYnorm hYuniq
  obtain ⟨m, hmM, hm⟩ := hInv
  have hmb : m * b * m⁻¹ = b⁻¹ := hm b (Subgroup.mem_zpowers b)
  have hmN : m ∈ Subgroup.normalizer (L : Set G) :=
    le_normalizer_of_subgroupOf_normal hL.1.le hLN hmM
  exact false_of_inverted N hbN hmN hr hr2 hbr hθN hcommN hmb

private theorem false_of_isSp4_shape {D : Data G} {Ch : Choice2011 G}
    (h218 : S21_8N D Ch) (hField : KFieldCent) (h1930 : H1930 D)
    {c : Ctx21 D Ch} {L : Subgroup G} (hL : L ∈ calC D.M) (hLN : (L.subgroupOf D.M).Normal)
    {b : G} (hbB : b ∈ c.B) (hbN : b ∈ normalizer (L : Set G))
    {θ : MulAut (BarInf L ⧸ Subgroup.center (BarInf L))} (hInd : InducedQuotInf L b θ)
    (hbsq : Squarefree (orderOf b)) (hbodd : Odd (orderOf b)) {a : ℕ}
    (hSp4X : IsSp4 (BarInf L ⧸ Subgroup.center (BarInf L)) a)
    (hnotInn : θ ∉ (MulAut.conj : (BarInf L ⧸ Subgroup.center (BarInf L)) →*
      MulAut (BarInf L ⧸ Subgroup.center (BarInf L))).range) : False := by
  classical
  have hq : CFSG.Open.IsQuasisimple (Bar2 L) := hL.2.2
  have hZ : Subgroup.center (BarInf L) = ⊥ := center_barInf_eq_bot hq
  have hθeq : θ = inducedQuotInfAut L b hbN :=
    inducedQuotInf_unique L hbN hInd (inducedQuotInf_inducedQuotInfAut L b hbN)
  obtain ⟨b', hb'B, hb'N, hb'pr, hb'odd, hθ'N, hθ'ord⟩ :=
    exists_prime_induced_not_mem (D := D) (Ch := Ch) (c := c)
      ((MulAut.conj : (BarInf L ⧸ Subgroup.center (BarInf L)) →*
        MulAut (BarInf L ⧸ Subgroup.center (BarInf L))).range) hbB hbN hbsq hbodd
      (by rw [← hθeq]; exact hnotInn)
  have hr2 : orderOf b' ≠ 2 := by obtain ⟨k, hk⟩ := hb'odd; omega
  obtain ⟨hdiv, x, hx3, hxfix⟩ :=
    hField.1 _ a (orderOf b') hSp4X hb'pr hr2 _ hθ'ord hθ'N
  have hnotpow : ¬ IsPowTwo a := by
    rintro ⟨k, rfl⟩
    have h2 : orderOf b' ∣ 2 := hb'pr.dvd_of_dvd_pow hdiv
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hb'pr Nat.prime_two).mp h2)
  have hSp4bar : IsSp4 (BarInf L) a := CFSG.Blueprint.LieModel.of_quotient_center hZ hSp4X
  have ha2 : 2 ≤ a := by
    have h1 : 1 ≤ a := hSp4X.admissible.2.1
    have h2 : a ≠ 1 := fun h => hSp4X.admissible.2.2.2 (by rw [h]; norm_num)
    omega
  have h4 : 4 ≤ 2 ^ a := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha2
  have hne : 2 ^ a - 1 ≠ 1 := by omega
  obtain ⟨s, hs, hsdvd⟩ := Nat.exists_prime_and_dvd hne
  obtain ⟨⟨hSp4bar2, -, -⟩, ⟨-, hk1⟩, -⟩ :=
    h218 h1930 c L hL a hSp4bar hnotpow s hs hsdvd
  have hsp3 : IsStronglyPEmbedded 3 D.M := by
    have hk1' : kParam D.M = 1 := by simpa [Data.k] using hk1
    by_contra h
    rw [kParam, if_neg h] at hk1'
    omega
  have hcop : ¬ orderOf b' ∣ Nat.card (CFSG.solvableRadical ↥L) := by
    have hc : Subgroup.center (Bar2 L) = ⊥ := center_eq_bot_of_isSp4 hq hSp4bar2
    have hO : CFSG.solvableRadical ↥L = CFSG.pCore 2 ↥L :=
      solvableRadical_eq_pCore_of_center_bar2_eq_bot hq hc
    rw [hO]
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
    rw [hk]
    intro hdvd
    have h2 : orderOf b' ∣ 2 := hb'pr.dvd_of_dvd_pow hdvd
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hb'pr Nat.prime_two).mp h2)
  exact false_of_three_element hL hLN
    ((MulAut.conj : (BarInf L ⧸ Subgroup.center (BarInf L)) →*
      MulAut (BarInf L ⧸ Subgroup.center (BarInf L))).range)
    hb'B hb'N hb'pr hr2 rfl hθ'N
    (fun α β => kOutDiagSp4 hSp4X α β) hsp3 hcop h1930 hx3 hxfix

private theorem false_of_isU3_shape {D : Data G} {Ch : Choice2011 G}
    (hσ : UC6S846.SigmaStd D) (h219 : S21_9NFull D Ch) (hCen : UCK.U3Center)
    (hOutU3 : KOutDiagU3) (hField : KFieldCent) (h1930 : H1930 D)
    {c : Ctx21 D Ch} {L : Subgroup G} (hL : L ∈ calC D.M) (hLN : (L.subgroupOf D.M).Normal)
    {b : G} (hbB : b ∈ c.B) (hbN : b ∈ normalizer (L : Set G))
    {θ : MulAut (BarInf L ⧸ Subgroup.center (BarInf L))} (hInd : InducedQuotInf L b θ)
    (hbsq : Squarefree (orderOf b)) (hbodd : Odd (orderOf b)) {a : ℕ}
    (hU3X : IsU3 (BarInf L ⧸ Subgroup.center (BarInf L)) a)
    (hnotDiag : θ ∉ CFSG.ASVolI.ChA.innDiagSubgroup
      (BarInf L ⧸ Subgroup.center (BarInf L))) : False := by
  classical
  have hq : CFSG.Open.IsQuasisimple (Bar2 L) := hL.2.2
  have hθeq : θ = inducedQuotInfAut L b hbN :=
    inducedQuotInf_unique L hbN hInd (inducedQuotInf_inducedQuotInfAut L b hbN)
  obtain ⟨b', hb'B, hb'N, hb'pr, hb'odd, hθ'N, hθ'ord⟩ :=
    exists_prime_induced_not_mem (D := D) (Ch := Ch) (c := c)
      (CFSG.ASVolI.ChA.innDiagSubgroup (BarInf L ⧸ Subgroup.center (BarInf L)))
      hbB hbN hbsq hbodd (by rw [← hθeq]; exact hnotDiag)
  have hr2 : orderOf b' ≠ 2 := by obtain ⟨k, hk⟩ := hb'odd; omega
  obtain ⟨hdiv, x, hx3, hxfix⟩ :=
    hField.2 _ a (orderOf b') hU3X hb'pr hr2 _ hθ'ord hθ'N
  have hnotpow : ¬ IsPowTwo a := by
    rintro ⟨k, rfl⟩
    have h2 : orderOf b' ∣ 2 := hb'pr.dvd_of_dvd_pow hdiv
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hb'pr Nat.prime_two).mp h2)
  have hSU : IsSU3 (Bar2 L) a := isSU3_bar2_of_isU3 hq hU3X
  obtain ⟨hmod, hsig, -⟩ := h219 h1930 c L hL hLN a hSU hnotpow
  have h3sig : 3 ∈ D.sig := by rw [hsig.1]; exact Set.mem_singleton 3
  have hsp3 : IsStronglyPEmbedded 3 D.M :=
    UC6S846.sp_of_mem_sig hσ (UC6S846.not_solvable_of_mem_calC hL) h3sig
  have hr3 : orderOf b' ≠ 3 := by
    intro h
    have h3a : 3 ∣ a := h ▸ hdiv
    have h3 : a % 3 = 0 := Nat.mod_eq_zero_of_dvd h3a
    rcases hmod with h6 | h6 <;> omega
  have hZ3 : Nat.card (Subgroup.center (Bar2 L)) ∣ 3 := hCen (Bar2 L) a hSU
  have hcop : ¬ orderOf b' ∣ Nat.card (CFSG.solvableRadical ↥L) :=
    not_dvd_card_solvableRadical hq hb'pr hr2 hr3 hZ3
  exact false_of_three_element hL hLN
    (CFSG.ASVolI.ChA.innDiagSubgroup (BarInf L ⧸ Subgroup.center (BarInf L)))
    hb'B hb'N hb'pr hr2 rfl hθ'N
    (fun α β => hOutU3 _ a hU3X α β) hsp3 hcop h1930 hx3 hxfix

theorem s21_11N_W2111 {D : Data G} {Ch : Choice2011 G}
    (hσ : UC6S846.SigmaStd D) (h218 : S21_8N D Ch) (h219 : S21_9NFull D Ch)
    (hCen : UCK.U3Center) (hOutU3 : KOutDiagU3) (hField : KFieldCent) :
    S21_11N D Ch W2111 := by
  intro h1930 c L hL hLN b hbB hbN θ hInd hW
  obtain ⟨hbodd, hbsq⟩ := orderOf_odd_and_squarefree_of_mem_calB1 c.hB hbB
  rcases hW with ⟨⟨a, hSp4X⟩, hnotInn⟩ | ⟨⟨a, hU3X⟩, hnotDiag⟩
  · exact (false_of_isSp4_shape h218 hField h1930 hL hLN hbB hbN hInd hbsq hbodd
      hSp4X hnotInn).elim
  · exact (false_of_isU3_shape hσ h219 hCen hOutU3 hField h1930 hL hLN hbB hbN hInd hbsq
      hbodd hU3X hnotDiag).elim

end CFSG.LocalAnalysis.UniquenessCase.UC22

end

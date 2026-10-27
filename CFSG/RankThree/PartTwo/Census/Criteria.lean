module

public import CFSG.RankThree.PartTwo.Census.Interface
import CFSG.Milestones.LC_GL_local_rank_bounds
import CFSG.LieType.BorelTits.Basic
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Assembly CFSG.Assembly.RankThreeEven

section Transport

variable {G H : Type} [Group G] [Group H]

theorem isTwoLocal_map_mulEquiv {K : Subgroup G} (hK : IsTwoLocal K) (e : G ≃* H) :
    IsTwoLocal (K.map e.toMonoidHom) := by
  obtain ⟨P, hP, hP2, rfl⟩ := hK
  refine ⟨P.map e.toMonoidHom, ?_, hP2.map _, (Subgroup.map_equiv_normalizer_eq P e)⟩
  rwa [Ne, Subgroup.map_eq_bot_iff_of_injective P e.injective]

theorem pCoreOf_map_mulEquiv (e : G ≃* H) (K : Subgroup G) :
    pCoreOf 2 (K.map e.toMonoidHom) = (pCoreOf 2 K).map e.toMonoidHom :=
  CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 e K

theorem isCharTwoType_of_mulEquiv (e : G ≃* H) (hG : IsCharTwoType G) : IsCharTwoType H := by
  intro K hK x hx
  set K' : Subgroup G := K.map e.symm.toMonoidHom
  have hK' : IsTwoLocal K' := isTwoLocal_map_mulEquiv hK e.symm
  have hcore : pCoreOf 2 K' = (pCoreOf 2 K).map e.symm.toMonoidHom := pCoreOf_map_mulEquiv e.symm K
  have hmem : e.symm x ∈ K' ⊓ Subgroup.centralizer (pCoreOf 2 K' : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨⟨x, (Subgroup.mem_inf.mp hx).1, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff, hcore]
    rintro _ ⟨y, hy, rfl⟩
    have hxy := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 y hy
    change e.symm y * e.symm x = e.symm x * e.symm y
    rw [← map_mul, ← map_mul, hxy]
  have h := hG K' hK' hmem
  rw [hcore] at h
  obtain ⟨y, hy, hyx⟩ := h
  have : y = x := e.symm.injective hyx
  exact this ▸ hy

theorem isCharTwoType_congr (e : G ≃* H) : IsCharTwoType G ↔ IsCharTwoType H :=
  ⟨isCharTwoType_of_mulEquiv e, isCharTwoType_of_mulEquiv e.symm⟩

variable [Finite G] [Finite H]

theorem localRank_le_of_mulEquiv (e : G ≃* H) {p : ℕ} (hp : p.Prime) :
    localRank p G ≤ localRank p H := by
  apply csSup_le'
  rintro _ ⟨K, hK, rfl⟩
  calc Assembly.pRank p K ≤ Assembly.pRank p (K.map e.toMonoidHom) :=
        CFSG.RankThreeEvenClassification.Helpers.pRank_le_map_of_injective p hp e.toMonoidHom
          e.injective K
    _ ≤ localRank p H :=
        CFSG.RankThreeEvenClassification.Helpers.pRank_le_twoLocalRank p hp _
          (isTwoLocal_map_mulEquiv hK e)

theorem localRank_eq_of_mulEquiv (e : G ≃* H) {p : ℕ} (hp : p.Prime) :
    localRank p G = localRank p H :=
  le_antisymm (localRank_le_of_mulEquiv e hp) (localRank_le_of_mulEquiv e.symm hp)

end Transport

end CFSG.RankThree.PartTwo.Census

namespace CFSG.RankThree.PartTwo.TheoremFourHyp

open CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.PartTwo.Census

variable {G H : Type} [Group G] [Finite G] [Group H]

theorem false_of_not_isCharTwoType (h : TheoremFourHyp G) (e : G ≃* H)
    (hH : ¬ IsCharTwoType H) : False :=
  hH (isCharTwoType_of_mulEquiv e h.charTwoType)

theorem false_of_four_le_localRank [Finite H] (h : TheoremFourHyp G) (e : G ≃* H) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hH : 4 ≤ localRank p H) : False := by
  have hle := ((CFSG.Milestones.lc_gl_local_rank_bounds G).1 p hp hp2).2
  rw [h.evenRank_eq, localRank_eq_of_mulEquiv e hp] at hle
  omega

theorem false_of_three_le_localRank [Finite H] (h : TheoremFourHyp G) (e : G ≃* H) {q : ℕ}
    (hq : q.Prime) (hq3 : 3 < q) (hH : 3 ≤ localRank q H) : False := by
  have hlt := h.localRank_lt q hq hq3
  rw [localRank_eq_of_mulEquiv e hq] at hlt
  omega

theorem false_of_localRank_three_le_two [Finite H] (h : TheoremFourHyp G) (e : G ≃* H)
    (hH : localRank 3 H ≤ 2) : False := by
  have h3 := h.localRank_three
  rw [localRank_eq_of_mulEquiv e Nat.prime_three] at h3
  omega

theorem false_of_commute (h : TheoremFourHyp G) (e : G ≃* H) (hH : ∀ a b : H, a * b = b * a) :
    False := by
  obtain ⟨a, b, hab⟩ := h.nonabelian
  exact hab (e.injective (by rw [map_mul, map_mul, hH]))

end CFSG.RankThree.PartTwo.TheoremFourHyp

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Assembly CFSG.Assembly.RankThreeEven

section Witness

variable {H : Type} [Group H] [Finite H]

theorem le_localRank_of_le_normalizer {p k : ℕ} (hp : p.Prime) {P E : Subgroup H} (hP : P ≠ ⊥)
    (hP2 : IsPGroup 2 P) (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ k)
    (hEP : E ≤ Subgroup.normalizer (P : Set H)) : k ≤ localRank p H := by
  have h1 : k ≤ Assembly.pRank p (Subgroup.normalizer (P : Set H)) :=
    le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove p hp _) ⟨E, hEP, hE, hc⟩
  exact h1.trans (CFSG.RankThreeEvenClassification.Helpers.pRank_le_twoLocalRank p hp _
    ⟨P, hP, hP2, rfl⟩)

theorem le_localRank_of_commute_involution {p k : ℕ} (hp : p.Prime) {t : H} (ht : orderOf t = 2)
    {E : Subgroup H} (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ k)
    (hEt : ∀ x ∈ E, x * t = t * x) : k ≤ localRank p H := by
  have ht1 : t ≠ 1 := by
    rintro rfl
    simp at ht
  have hP : Subgroup.zpowers t ≠ ⊥ := by
    rwa [Ne, Subgroup.zpowers_eq_bot]
  have hP2 : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  refine le_localRank_of_le_normalizer hp hP hP2 hE hc fun x hx => ?_
  refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
  rintro _ ⟨n, rfl⟩
  exact (Commute.zpow_left (hEt x hx).symm n).eq

end Witness

section UpperBound

variable {H : Type} [Group H] [Finite H]

theorem localRank_le_of_pRank_le {p k : ℕ} (hp : p.Prime)
    (h : Assembly.pRank p (⊤ : Subgroup H) ≤ k) :
    localRank p H ≤ k :=
  (CFSG.RankThreeEvenClassification.Helpers.twoLocalRank_le_pRank p hp H).trans h

theorem pRank_le_two_of_not_dvd {p : ℕ} (hp : p.Prime) (h : ¬ p ^ 3 ∣ Nat.card H) :
    Assembly.pRank p (⊤ : Subgroup H) ≤ 2 := by
  by_contra hlt
  have hdvd : p ^ Assembly.pRank p (⊤ : Subgroup H) ∣ Nat.card (⊤ : Subgroup H) :=
    CFSG.RankThreeEvenClassification.Helpers.prime_power_pRank_dvd_card p hp ⊤
  rw [Subgroup.card_top] at hdvd
  exact h ((pow_dvd_pow p (by omega)).trans hdvd)

theorem pRank_le_two_of_nonabelian {p : ℕ} (hp : p.Prime) (h4 : ¬ p ^ 4 ∣ Nat.card H)
    {S : Subgroup H} (hS : Nat.card S = p ^ 3) (hnc : ∃ a ∈ S, ∃ b ∈ S, a * b ≠ b * a) :
    Assembly.pRank p (⊤ : Subgroup H) ≤ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hlt
  obtain ⟨E, -, hE, hEc⟩ : ∃ E : Subgroup H, E ≤ ⊤ ∧ IsElemAbelian p E ∧
      Nat.card E = p ^ Assembly.pRank p (⊤ : Subgroup H) :=
    CFSG.RankThreeEvenClassification.Helpers.pRank_attained p hp ⊤
  have hdvd : p ^ Assembly.pRank p (⊤ : Subgroup H) ∣ Nat.card H := by
    rw [← hEc]
    exact Subgroup.card_subgroup_dvd_card E
  have hr : Assembly.pRank p (⊤ : Subgroup H) = 3 := by
    by_contra hne
    exact h4 ((pow_dvd_pow p (by omega)).trans hdvd)
  rw [hr] at hEc hdvd
  have hH0 : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card H).factorization p = 3 := by
    have h3 := (hp.pow_dvd_iff_le_factorization hH0).mp hdvd
    have h4' : ¬ 4 ≤ (Nat.card H).factorization p := fun h =>
      h4 ((hp.pow_dvd_iff_le_factorization hH0).mpr h)
    omega
  let SE : Sylow p H := Sylow.ofCard E (by rw [hEc, hfac])
  let SS : Sylow p H := Sylow.ofCard S (by rw [hS, hfac])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H SE SS
  have hSeq : (S : Subgroup H) = E.map (MulAut.conj g).toMonoidHom := by
    have h1 : ((g • SE : Sylow p H) : Subgroup H) = (SS : Subgroup H) := by rw [hg]
    rw [Sylow.coe_subgroup_smul] at h1
    exact h1.symm
  obtain ⟨a, ha, b, hb, hab⟩ := hnc
  rw [hSeq] at ha hb
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  apply hab
  have hcomm : a' * b' = b' * a' :=
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩)
  change (MulAut.conj g) a' * (MulAut.conj g) b' = (MulAut.conj g) b' * (MulAut.conj g) a'
  rw [← map_mul, ← map_mul, hcomm]

theorem localRank_three_le_one_of_forall_ne
    (h : ∀ a t : H, orderOf a = 3 → orderOf t = 2 → a * t ≠ t * a) : localRank 3 H ≤ 1 := by
  by_contra hlt
  obtain ⟨L, hL, hLr⟩ := CFSG.RankThreeEvenClassification.Helpers.twoLocalRank_attained 3
    Nat.prime_three H (by change 0 < localRank 3 H; omega)
  change Assembly.pRank 3 L = localRank 3 H at hLr
  obtain ⟨E, hEL, hE, hEc⟩ : ∃ E : Subgroup H, E ≤ L ∧ IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ Assembly.pRank 3 L :=
    CFSG.RankThreeEvenClassification.Helpers.pRank_attained 3 Nat.prime_three L
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨A', hA'⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) 3 (n := 2)
    (by rw [hEc]; exact pow_dvd_pow 3 (by omega))
  set A : Subgroup H := A'.map E.subtype
  have hAE : A ≤ E := Subgroup.map_subtype_le A'
  have hAc : Nat.card A = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective E.subtype_injective, hA']
  have hpower : ∀ a : A, a ^ 3 = 1 := fun a => Subtype.ext (hE.2 a (hAE a.2))
  obtain ⟨P, hP, hP2, rfl⟩ := hL
  have hcomp : ¬ 3 ∣ Nat.card P := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP2
    rw [hk]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane
    3 Nat.prime_three A P hpower hAc hcomp (hAE.trans hEL)
  obtain ⟨a, ha1, ha⟩ : ∃ a : A, a ≠ 1 ∧
      P ⊓ Subgroup.centralizer ({(a : H)} : Set H) ≠ ⊥ := by
    by_contra hno
    push Not at hno
    apply hP
    rw [hgen]
    exact iSup_eq_bot.mpr fun a => iSup_eq_bot.mpr fun ha => hno a ha
  set X := P ⊓ Subgroup.centralizer ({(a : H)} : Set H)
  have hX2 : IsPGroup 2 X := hP2.to_le inf_le_left
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ∣ Nat.card X := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hX2
    rcases k with _ | k
    · exact (ha ((Subgroup.eq_bot_iff_card X).mpr (by simpa using hk))).elim
    · rw [hk, pow_succ]
      exact dvd_mul_left 2 _
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hta : (t : H) * a = a * t :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp t.2).2
  have hao : orderOf (a : H) = 3 := by
    apply orderOf_eq_prime
    · exact congrArg Subtype.val (hpower a)
    · exact fun h1 => ha1 (Subtype.ext h1)
  exact h a t hao (by rw [Subgroup.orderOf_coe]; exact ht) hta.symm

end UpperBound

section NotCharTwo

variable {H : Type} [Group H]

theorem conj_mem_pCoreOf {L : Subgroup H} {g x : H} (hg : g ∈ L) (hx : x ∈ pCoreOf 2 L) :
    g * x * g⁻¹ ∈ pCoreOf 2 L :=
  (Subgroup.mem_normalizer_iff.mp
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L hg) x).mp hx

theorem isPGroup_pCoreOf [Finite H] (L : Subgroup H) : IsPGroup 2 (pCoreOf 2 L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L

theorem commutatorElement_mem_inf_pCoreOf {L K : Subgroup H} (hKL : K ≤ L)
    (hKn : ∀ g ∈ L, ∀ k ∈ K, g * k * g⁻¹ ∈ K) {k x : H} (hk : k ∈ K)
    (hx : x ∈ pCoreOf 2 L) : k * x * k⁻¹ * x⁻¹ ∈ K ⊓ pCoreOf 2 L := by
  have hxL : x ∈ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L hx
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have h1 : x * k⁻¹ * x⁻¹ ∈ K := hKn x hxL k⁻¹ (K.inv_mem hk)
    have h2 : k * (x * k⁻¹ * x⁻¹) ∈ K := K.mul_mem hk h1
    simpa only [mul_assoc] using h2
  · exact (pCoreOf 2 L).mul_mem (conj_mem_pCoreOf (hKL hk) hx) ((pCoreOf 2 L).inv_mem hx)

theorem conj_mem_inf_pCoreOf {L K : Subgroup H} (hKL : K ≤ L) {g n : H} (hg : g ∈ K)
    (hn : n ∈ K ⊓ pCoreOf 2 L) : g * n * g⁻¹ ∈ K ⊓ pCoreOf 2 L := by
  obtain ⟨hnK, hnQ⟩ := Subgroup.mem_inf.mp hn
  exact Subgroup.mem_inf.mpr ⟨K.mul_mem (K.mul_mem hg hnK) (K.inv_mem hg),
    conj_mem_pCoreOf (hKL hg) hnQ⟩

theorem not_isCharTwoType_of_normal_subgroup [Finite H] {L K : Subgroup H}
    (hL : IsTwoLocal L) (hKL : K ≤ L) (hKn : ∀ g ∈ L, ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (hK2 : ∀ N : Subgroup H, N ≤ K → (∀ g ∈ K, ∀ n ∈ N, g * n * g⁻¹ ∈ N) → IsPGroup 2 N →
      N = ⊥)
    (hK1 : K ≠ ⊥) : ¬ IsCharTwoType H := by
  intro hchar
  have hN : K ⊓ pCoreOf 2 L = ⊥ :=
    hK2 _ inf_le_left (fun g hg n hn => conj_mem_inf_pCoreOf hKL hg hn)
      ((isPGroup_pCoreOf L).to_le inf_le_right)
  have hKC : K ≤ L ⊓ Subgroup.centralizer (pCoreOf 2 L : Set H) := by
    intro k hk
    refine Subgroup.mem_inf.mpr ⟨hKL hk, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    have hmem := commutatorElement_mem_inf_pCoreOf hKL hKn hk hx
    rw [hN, Subgroup.mem_bot] at hmem
    have h1 : k * x * k⁻¹ = x := mul_inv_eq_one.mp hmem
    calc x * k = k * x * k⁻¹ * k := by rw [h1]
      _ = k * x := by group
  apply hK1
  rw [eq_bot_iff, ← hN]
  exact le_inf le_rfl (hKC.trans (hchar L hL))

theorem not_isCharTwoType_of_perfect_normal_subgroup [Finite H] {L K : Subgroup H}
    (hL : IsTwoLocal L) (hKL : K ≤ L) (hKn : ∀ g ∈ L, ∀ k ∈ K, g * k * g⁻¹ ∈ K) (hperf : ⁅K, K⁆ = K)
    (hK2 : ∀ N : Subgroup H, N ≤ K → (∀ g ∈ K, ∀ n ∈ N, g * n * g⁻¹ ∈ N) → IsPGroup 2 N →
      N ≤ Subgroup.centralizer (K : Set H))
    (hK : ¬ IsPGroup 2 K) : ¬ IsCharTwoType H := by
  intro hchar
  set Q := pCoreOf 2 L
  have hNc : K ⊓ Q ≤ Subgroup.centralizer (K : Set H) :=
    hK2 _ inf_le_left (fun g hg n hn => conj_mem_inf_pCoreOf hKL hg hn)
      ((isPGroup_pCoreOf L).to_le inf_le_right)
  have hKQ : ⁅K, Q⁆ ≤ K ⊓ Q :=
    Subgroup.commutator_le.mpr fun k hk x hx => commutatorElement_mem_inf_pCoreOf hKL hKn hk hx
  have h1 : ⁅⁅K, Q⁆, K⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hKQ.trans hNc)
  have h2 : ⁅⁅Q, K⁆, K⁆ = ⊥ := by rwa [Subgroup.commutator_comm Q K]
  have h3 : ⁅⁅K, K⁆, Q⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  rw [hperf] at h3
  have hKC : K ≤ L ⊓ Subgroup.centralizer (Q : Set H) :=
    le_inf hKL (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3)
  exact hK ((isPGroup_pCoreOf L).to_le (hKC.trans (hchar L hL)))

theorem not_isCharTwoType_of_perfect_subnormal_subgroup [Finite H] {L K J : Subgroup H}
    (hL : IsTwoLocal L) (hKL : K ≤ L) (hKn : ∀ g ∈ L, ∀ k ∈ K, g * k * g⁻¹ ∈ K) (hJK : J ≤ K)
    (hJn : ∀ g ∈ K, ∀ j ∈ J, g * j * g⁻¹ ∈ J) (hperf : ⁅J, J⁆ = J)
    (hJ2 : ∀ N : Subgroup H, N ≤ J → (∀ g ∈ J, ∀ n ∈ N, g * n * g⁻¹ ∈ N) → IsPGroup 2 N →
      N ≤ Subgroup.centralizer (J : Set H))
    (hJ : ¬ IsPGroup 2 J) : ¬ IsCharTwoType H := by
  intro hchar
  set Q := pCoreOf 2 L
  set N := K ⊓ Q
  have hJN : ⁅J, N⁆ ≤ J ⊓ N := by
    refine Subgroup.commutator_le.mpr fun j hj n hn => ?_
    obtain ⟨hnK, hnQ⟩ := Subgroup.mem_inf.mp hn
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h1 : n * j⁻¹ * n⁻¹ ∈ J := hJn n hnK j⁻¹ (J.inv_mem hj)
      have h2 : j * (n * j⁻¹ * n⁻¹) ∈ J := J.mul_mem hj h1
      simpa only [commutatorElement_def, mul_assoc] using h2
    · have h1 : j * n * j⁻¹ ∈ N := conj_mem_inf_pCoreOf hKL (hJK hj) hn
      exact N.mul_mem h1 (N.inv_mem hn)
  have hJNc : J ⊓ N ≤ Subgroup.centralizer (J : Set H) := by
    refine hJ2 _ inf_le_left (fun g hg x hx => ?_) ((isPGroup_pCoreOf L).to_le
      (inf_le_right.trans inf_le_right))
    obtain ⟨hxJ, hxN⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr ⟨J.mul_mem (J.mul_mem hg hxJ) (J.inv_mem hg),
      conj_mem_inf_pCoreOf hKL (hJK hg) hxN⟩
  have h1 : ⁅⁅J, N⁆, J⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hJN.trans hJNc)
  have h2 : ⁅⁅N, J⁆, J⁆ = ⊥ := by rwa [Subgroup.commutator_comm N J]
  have hJN1 : ⁅J, N⁆ = ⊥ := by
    have h3 : ⁅⁅J, J⁆, N⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
    rwa [hperf] at h3
  have hJQ : ⁅J, Q⁆ ≤ N :=
    Subgroup.commutator_le.mpr fun j hj x hx =>
      commutatorElement_mem_inf_pCoreOf hKL hKn (hJK hj) hx
  have h4 : ⁅⁅J, Q⁆, J⁆ = ⊥ := by
    refine le_bot_iff.mp ?_
    calc ⁅⁅J, Q⁆, J⁆ ≤ ⁅N, J⁆ := Subgroup.commutator_mono hJQ le_rfl
      _ = ⁅J, N⁆ := Subgroup.commutator_comm N J
      _ = ⊥ := hJN1
  have h5 : ⁅⁅Q, J⁆, J⁆ = ⊥ := by rwa [Subgroup.commutator_comm Q J]
  have h6 : ⁅⁅J, J⁆, Q⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h4 h5
  rw [hperf] at h6
  have hJC : J ≤ L ⊓ Subgroup.centralizer (Q : Set H) :=
    le_inf (hJK.trans hKL) (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h6)
  exact hJ ((isPGroup_pCoreOf L).to_le (hJC.trans (hchar L hL)))

theorem pCoreOf_le_of_card [Finite H] {L S : Subgroup H} (hSL : S ≤ L)
    (hc : Nat.card S = 2 ^ (Nat.card L).factorization 2) : pCoreOf 2 L ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let SL : Sylow 2 L := Sylow.ofCard (S.subgroupOf L) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSL).toEquiv, hc])
  have : (CFSG.Open.pCore 2 L).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hle : CFSG.Open.pCore 2 L ≤ (SL : Subgroup L) :=
    IsPGroup.le_sylow_of_normal (CFSG.LieType.BorelTits.pCore_isPGroup 2) SL
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hy' := hle (by exact hy)
  change y ∈ S.subgroupOf L at hy'
  exact hy'

theorem not_isCharTwoType_of_sylow_inf [Finite H] {L S₁ S₂ : Subgroup H} {x : H}
    (hL : IsTwoLocal L) (hS₁ : S₁ ≤ L) (hS₂ : S₂ ≤ L)
    (hc₁ : Nat.card S₁ = 2 ^ (Nat.card L).factorization 2)
    (hc₂ : Nat.card S₂ = 2 ^ (Nat.card L).factorization 2) (hxL : x ∈ L) (hx1 : x ≠ 1)
    (hxo : Odd (orderOf x)) (hxc : ∀ s ∈ S₁ ⊓ S₂, x * s = s * x) : ¬ IsCharTwoType H := by
  intro hchar
  have hQ : pCoreOf 2 L ≤ S₁ ⊓ S₂ := le_inf (pCoreOf_le_of_card hS₁ hc₁)
    (pCoreOf_le_of_card hS₂ hc₂)
  have hxQ : x ∈ pCoreOf 2 L :=
    hchar L hL (Subgroup.mem_inf.mpr
      ⟨hxL, Subgroup.mem_centralizer_iff.mpr fun s hs => (hxc s (hQ hs)).symm⟩)
  obtain ⟨k, hk⟩ := (isPGroup_pCoreOf L) ⟨x, hxQ⟩
  have hk' : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hdvd : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hcop : (orderOf x).Coprime (2 ^ k) := Nat.Coprime.pow_right k hxo.coprime_two_right
  exact hx1 (orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd))

theorem card_eq_two_pow_factorization_of_le [Finite H] {L S : Subgroup H} (hSL : S ≤ L)
    (hc : Nat.card S = 2 ^ (Nat.card H).factorization 2) :
    Nat.card S = 2 ^ (Nat.card L).factorization 2 := by
  have hH0 : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have hL0 : Nat.card L ≠ 0 := Nat.card_pos.ne'
  have h1 : 2 ^ (Nat.card H).factorization 2 ∣ Nat.card L := by
    rw [← hc]
    exact Subgroup.card_dvd_of_le hSL
  have h2 : (Nat.card H).factorization 2 ≤ (Nat.card L).factorization 2 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization hL0).mp h1
  have h3 : (Nat.card L).factorization 2 ≤ (Nat.card H).factorization 2 :=
    (Nat.factorization_le_iff_dvd hL0 hH0).mpr (Subgroup.card_subgroup_dvd_card L) 2
  rw [hc, le_antisymm h2 h3]

end NotCharTwo

end CFSG.RankThree.PartTwo.Census

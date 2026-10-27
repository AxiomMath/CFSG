module

public import CFSG.Walter.Bender1970.S4.RankTools
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.QCoreConjugate
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.Walter.Bender1970.S4.FStar

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Bender42

theorem benderM_eq_of_typePP
    (hG : BenderCounterexample G) {t : G} (ht : orderOf t = 2)
    {H : Subgroup G} (hH : H ∈ benderM t) (T : Sylow 2 G) (htT : t ∈ (T : Subgroup G))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hπ : 2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf H)))
    (hQ2 : 2 ≤ rank (qCoreOf H p)) {V : Subgroup G} (hVQ : V ≤ qCoreOf H p)
    (hVel : CFSG.Open.IsElemAbelian p V) (hVcard : Nat.card V = p ^ 2)
    (hVC : ∀ v ∈ V, v ≠ 1 → Subgroup.centralizer ({v} : Set G) ≤ H) {s : G}
    (hs : orderOf s = 2) (hsT : s ∈ (T : Subgroup G))
    (hsV : V ≤ Subgroup.centralizer ({s} : Set G)) : benderM s = {H} := by
  by_contra hne
  obtain ⟨M, hM, hMH⟩ := hG.exists_mem_benderM_ne hs hne
  have htQ := hG.qCoreOf_le_centralizer_of_mem_benderM ht hH hp hp2
  have habc : Bender39Conditions t H T V p := by
    refine Or.inr (Or.inl ⟨fun v hv hv1 => ⟨?_, hVC v hv hv1⟩, hVel, hVcard⟩)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.mp (htQ (hVQ hv))).symm
  have h := (bender1970_3_9 hG ht hH T htT hp hp2 hVQ hs hsT hM hMH hπ
    (hsV.trans (centralizer_le_of_mem_benderM hM)) habc).2.2 hsV
  omega

theorem false_of_isKleinFour
    (hG : BenderCounterexample G) {t : G} (ht : orderOf t = 2)
    {H : Subgroup G} (hH : H ∈ benderM t) (T : Sylow 2 G) (htT : t ∈ (T : Subgroup G))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hπ : 2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf H)))
    (hQ2 : 2 ≤ rank (qCoreOf H p)) {R : Subgroup G} (hRT : R ≤ T)
    (hRr : rank R = rank (T : Subgroup G) - 1) {v : G} (hvQ : v ∈ qCoreOf H p)
    (hvR : v ∈ Subgroup.centralizer (R : Set G))
    (hvC : Subgroup.centralizer ({v} : Set G) ≤ H) {W : Subgroup G} (hWT : W ≤ T)
    (hW : IsKleinFour W) (hWC : ∀ w ∈ W, w ≠ 1 → Subgroup.centralizer ({w} : Set G) ≤ H) :
    False := by
  have htQ := hG.qCoreOf_le_centralizer_of_mem_benderM ht hH hp hp2
  have hVQ : Subgroup.zpowers v ≤ qCoreOf H p := Subgroup.zpowers_le.mpr hvQ
  have hCV := centralizer_zpowers_eq' v
  have habc : Bender39Conditions t H T (Subgroup.zpowers v) p := by
    refine Or.inr (Or.inr ⟨?_, by rw [hCV]; exact hvC, W, hWT, hW, hWC⟩)
    rw [hCV, Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.mp (htQ hvQ)).symm
  obtain ⟨s, hsR, hs, hsH⟩ := bender1970_3_3 hG ht hH T htT hRT hRr
  obtain ⟨M, hM, hMH⟩ := hG.exists_mem_benderM_ne hs hsH
  have hVs : Subgroup.zpowers v ≤ Subgroup.centralizer ({s} : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.mp hvR) s hsR).symm
  have h := (bender1970_3_9 hG ht hH T htT hp hp2 hVQ hs (hRT hsR) hM hMH hπ
    (hVs.trans (centralizer_le_of_mem_benderM hM)) habc).2.2 hVs
  omega

theorem rank_qCoreOf_le_two
    (hG : BenderCounterexample G) {t : G} (ht : orderOf t = 2)
    {H : Subgroup G} (hH : H ∈ benderM t) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    rank (qCoreOf H p) ≤ 2 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have := hG.isSimpleGroup
  by_contra h3
  push Not at h3
  obtain ⟨T, htT⟩ := exists_sylow_two_mem ht
  set Q := qCoreOf H p with hQdef
  have hQp : IsPGroup p Q := qCoreOf_isPGroup H p
  have htQ : Q ≤ Subgroup.centralizer ({t} : Set G) :=
    hG.qCoreOf_le_centralizer_of_mem_benderM ht hH hp hp2
  have hHco := isCoatom_of_mem_benderM hH
  have hTH := hG.sylow_le_of_mem_benderM T htT hH
  have hTab := hG.hasAbelianSylowTwo T
  have hcommT : ∀ x ∈ (T : Subgroup G), ∀ y ∈ (T : Subgroup G), x * y = y * x :=
    fun x hx y hy => congrArg Subtype.val (hTab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hQ1 : Q ≠ ⊥ := by
    intro h
    have : rank Q ≤ 1 :=
      rank_le_one_of_card_le hp hQp (by rw [h, Subgroup.card_bot]; exact hp.one_lt.le)
    omega
  have hQ2 : 2 ≤ rank Q := by omega
  have hπ : 2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf H)) := by
    refine two_le_card_primesOfOrder (Ne.symm hp2) ?_ (mem_primesOfOrder_of_qCoreOf_ne_bot hp hQ1)
    show 2 ∈ (Nat.card (generalizedFittingSubgroupOf H)).primeFactors
    rw [Nat.mem_primeFactors]
    refine ⟨Nat.prime_two, ?_, Nat.card_pos.ne'⟩
    have h := Subgroup.orderOf_dvd_natCard _ (bender1970_4_1 hG ht hH)
    rwa [ht] at h
  obtain ⟨P, hPQ, hPcyc, hPexp, hPN, hPZ⟩ :=
    exists_noncyclic_exponent_le_upperCentral hp hp2 hQp (not_isCyclic_of_two_le_rank hp hQp hQ2)
  have hPp : IsPGroup p P := hQp.to_le hPQ
  have hP1 : P ≠ ⊥ := by
    have : Nontrivial P := Nontrivial.of_not_isCyclic hPcyc
    exact (Subgroup.nontrivial_iff_ne_bot P).mp this
  have hHN : H ≤ Subgroup.normalizer (Q : Set G) :=
    le_normalizer_of_isNormalIn (qCoreOf_normal_in H p)
  have hTP : (T : Subgroup G) ≤ Subgroup.normalizer (P : Set G) := hTH.trans (hHN.trans hPN)
  have hPodd : Odd (Nat.card P) := by
    obtain ⟨k, hk⟩ := hPp.exists_card_eq
    rw [hk]
    exact (hp.odd_of_ne_two hp2).pow
  have hPC : ∀ v ∈ P, v ≠ 1 → Subgroup.centralizer ({v} : Set G) ≤ H := by
    intro v hv hv1
    obtain ⟨E, hEQ, hE, hE3, hvE⟩ :=
      exists_isElemAbelian_rank_three_mem hp hQp (by omega) (hPQ hv) (hPexp v hv) (hPZ v hv)
    exact bender1970_3_7 hG ht hH hp hp2 htQ hEQ hE hE3 hvE hv1
  set A := omegaOneOfComm 2 (T : Subgroup G) hcommT with hAdef
  have hAT : A ≤ T := omegaOneOfComm_le _ hcommT
  have hZPN : (T : Subgroup G) ≤
      Subgroup.normalizer ((P ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) : Set G) :=
    fun x hx => mem_normalizer_inf (hTP hx) (Bender35.mem_normalizer_centralizer (hTP hx))
  have hZPodd : Odd (Nat.card (P ⊓ Subgroup.centralizer (P : Set G) : Subgroup G)) :=
    Odd.of_dvd_nat hPodd (Subgroup.card_dvd_of_le inf_le_left)
  have hZP1 : P ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥ :=
    inf_centralizer_ne_bot_of_isPGroup hp hPp hPp Subgroup.le_normalizer hP1
  obtain ⟨B₁, hB₁, hB₁'⟩ : ∃ B₁ : Subgroup A, B₁.index = 2 ∧
      ¬ (P ⊓ Subgroup.centralizer (P : Set G)) ⊓
        Subgroup.centralizer ((B₁.map A.subtype : Subgroup G) : Set G) ≤ ⊥ := by
    by_contra hcon
    push Not at hcon
    exact hZP1 (le_bot_iff.mp (le_of_forall_hyperplane hcommT htT ht hZPN hZPodd hcon))
  obtain ⟨v₁', hv₁'1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (fun h => hB₁' (le_of_eq h))
  set v₁ : G := (v₁' : G) with hv₁def
  have hv₁1 : v₁ ≠ 1 := fun h => hv₁'1 (Subtype.ext h)
  have hv₁P : v₁ ∈ P := v₁'.2.1.1
  have hv₁Z : v₁ ∈ Subgroup.centralizer (P : Set G) := v₁'.2.1.2
  have hv₁R : v₁ ∈ Subgroup.centralizer ((B₁.map A.subtype : Subgroup G) : Set G) := v₁'.2.2
  have hPv₁ : ¬ P ≤ Subgroup.zpowers v₁ := by
    intro h
    apply hPcyc
    have : IsCyclic (P.subgroupOf (Subgroup.zpowers v₁)) := Subgroup.isCyclic _
    exact (Subgroup.subgroupOfEquivOfLe h).isCyclic.mp this
  obtain ⟨B₂, hB₂, hB₂'⟩ : ∃ B₂ : Subgroup A, B₂.index = 2 ∧
      ¬ P ⊓ Subgroup.centralizer ((B₂.map A.subtype : Subgroup G) : Set G) ≤
        Subgroup.zpowers v₁ := by
    by_contra hcon
    push Not at hcon
    exact hPv₁ (le_of_forall_hyperplane hcommT htT ht hTP hPodd hcon)
  obtain ⟨v₂, ⟨hv₂P, hv₂R⟩, hv₂v₁⟩ := Set.not_subset.mp hB₂'
  have hv₁p : v₁ ^ p = 1 := hPexp v₁ hv₁P
  have hv₂p : v₂ ^ p = 1 := hPexp v₂ hv₂P
  have hv₁o : orderOf v₁ = p := orderOf_eq_prime hv₁p hv₁1
  have hv₂1 : v₂ ≠ 1 := fun h => hv₂v₁ (h ▸ Subgroup.one_mem _)
  have hv₂o : orderOf v₂ = p := orderOf_eq_prime hv₂p hv₂1
  set V₂ := Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂ with hV₂def
  have h12 : Subgroup.zpowers v₁ ≤
      Subgroup.centralizer ((Subgroup.zpowers v₂ : Subgroup G) : Set G) := by
    rw [centralizer_zpowers_eq', Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.mp hv₁Z) v₂ hv₂P).symm
  have hV₂el : CFSG.Open.IsElemAbelian p V₂ :=
    isElemAbelian_sup (isElemAbelian_zpowers hv₁p) (isElemAbelian_zpowers hv₂p) h12
  have hdisj : Disjoint (Subgroup.zpowers v₁) (Subgroup.zpowers v₂) := by
    rw [disjoint_iff]
    set I := Subgroup.zpowers v₁ ⊓ Subgroup.zpowers v₂ with hI
    have hI1 : I ≤ Subgroup.zpowers v₁ := inf_le_left
    have hdvd : Nat.card I ∣ p := by
      rw [← hv₁o, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le hI1
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · exact Subgroup.eq_bot_of_card_eq I h
    · exfalso
      apply hv₂v₁
      have h1 : I = Subgroup.zpowers v₁ :=
        Subgroup.eq_of_le_of_card_ge hI1 (by rw [h, Nat.card_zpowers, hv₁o])
      have h2 : Subgroup.zpowers v₁ ≤ Subgroup.zpowers v₂ := h1 ▸ inf_le_right
      have h3 : Subgroup.zpowers v₁ = Subgroup.zpowers v₂ :=
        Subgroup.eq_of_le_of_card_ge h2 (by rw [Nat.card_zpowers, Nat.card_zpowers, hv₁o, hv₂o])
      rw [h3]
      exact Subgroup.mem_zpowers v₂
  have hV₂card : Nat.card V₂ = p ^ 2 := by
    rw [hV₂def, card_sup_eq_mul_of_disjoint_of_le_normalizer _ _
      (le_trans (by
        rw [centralizer_zpowers_eq', Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp hv₁Z) v₂ hv₂P)
        (Subgroup.centralizer_le_normalizer _)) hdisj,
      Nat.card_zpowers, Nat.card_zpowers, hv₁o, hv₂o, pow_two]
  have hV₂P : V₂ ≤ P := sup_le (Subgroup.zpowers_le.mpr hv₁P) (Subgroup.zpowers_le.mpr hv₂P)
  have hV₂Q : V₂ ≤ Q := hV₂P.trans hPQ
  have hV₂C : ∀ v ∈ V₂, v ≠ 1 → Subgroup.centralizer ({v} : Set G) ≤ H :=
    fun v hv hv1 => hPC v (hV₂P hv) hv1
  have hV₂1 : V₂ ≠ ⊥ := fun h => hv₁1 (by
    have : v₁ ∈ V₂ := (le_sup_left : Subgroup.zpowers v₁ ≤ V₂) (Subgroup.mem_zpowers v₁)
    rw [h] at this
    exact Subgroup.mem_bot.mp this)
  set R₁ := B₁.map A.subtype with hR₁def
  have hR₁T : R₁ ≤ T := (Subgroup.map_subtype_le B₁).trans hAT
  have hR₁r : rank R₁ = rank (T : Subgroup G) - 1 := rank_hyperplane T.isPGroup' hcommT B₁ hB₁
  have hb : ∀ s ∈ (T : Subgroup G), orderOf s = 2 →
      V₂ ≤ Subgroup.centralizer ({s} : Set G) → benderM s = {H} := fun s hsT hs hsV =>
    benderM_eq_of_typePP hG ht hH T htT hp hp2 hπ hQ2 hV₂Q hV₂el hV₂card hV₂C hs hsT hsV
  have hc : ∀ W ≤ (T : Subgroup G), IsKleinFour W →
      (∀ w ∈ W, w ≠ 1 → Subgroup.centralizer ({w} : Set G) ≤ H) → False :=
    fun W hWT hW hWC => false_of_isKleinFour hG ht hH T htT hp hp2 hπ hQ2 hR₁T hR₁r (hPQ hv₁P)
      hv₁R (hPC v₁ hv₁P hv₁1) hWT hW hWC
  set W₀ := (T : Subgroup G) ⊓ Subgroup.centralizer (V₂ : Set G) with hW₀def
  have huniq : ∀ a ∈ W₀, ∀ b ∈ W₀, a ^ 2 = 1 → b ^ 2 = 1 → a ≠ 1 → b ≠ 1 → a = b := by
    intro a ha b hb' ha2 hb2 ha1 hb1
    by_contra hab
    have hcomm : Commute a b := congrArg Subtype.val (hTab.is_comm.comm ⟨a, ha.1⟩ ⟨b, hb'.1⟩)
    have haa : a * a = 1 := by rw [← pow_two]; exact ha2
    have hbb : b * b = 1 := by rw [← pow_two]; exact hb2
    have hW := isKleinFour_kleinFourOfCommutingInvolutions a b haa hbb ha1 hb1 hab hcomm
    have hWW₀ : kleinFourOfCommutingInvolutions a b haa hbb hcomm ≤ W₀ := by
      intro y hy
      change y ∈ ({a * b, a, b, 1} : Set G) at hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact W₀.mul_mem ha hb'
      · exact ha
      · exact hb'
      · exact W₀.one_mem
    refine hc _ (hWW₀.trans inf_le_left) hW fun w hw hw1 => ?_
    have hwW₀ := hWW₀ hw
    have hw2 : orderOf w = 2 := by
      refine orderOf_eq_prime ?_ hw1
      have h := Monoid.pow_exponent_eq_one
        (⟨w, hw⟩ : kleinFourOfCommutingInvolutions a b haa hbb hcomm)
      rw [hW.exponent_two] at h
      exact congrArg Subtype.val h
    have hwV : V₂ ≤ Subgroup.centralizer ({w} : Set G) := fun v hv => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hwW₀.2) v hv
    have hHw : H ∈ benderM w := by rw [hb w hwW₀.1 hw2 hwV]; rfl
    exact centralizer_le_of_mem_benderM hHw
  have hr3 : rank (T : Subgroup G) = 3 := by
    have hlow := hG.three_le_rank_sylow T
    set W := (B₁ ⊓ B₂).map A.subtype with hWdef
    have hWW₀ : W ≤ W₀ := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨hAT x.2, ?_⟩
      show (x : G) ∈ Subgroup.centralizer (V₂ : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hle : V₂ ≤ Subgroup.centralizer ({(x : G)} : Set G) := by
        refine sup_le ?_ ?_
        · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
          exact ((Subgroup.mem_centralizer_iff.mp hv₁R) x ⟨x, hx.1, rfl⟩).symm
        · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
          exact ((Subgroup.mem_centralizer_iff.mp hv₂R) x ⟨x, hx.2, rfl⟩).symm
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hv)
    have hWsq : ∀ x ∈ W, x ^ 2 = 1 := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2.2
    have hW2 : Nat.card W ≤ 2 := by
      by_contra hlt
      push Not at hlt
      obtain ⟨a, haW, ha1, -⟩ := exists_mem_ne_one_ne (Q := W) hlt 1
      obtain ⟨b, hbW, hb1, hba⟩ := exists_mem_ne_one_ne (Q := W) hlt a
      exact hba (huniq b (hWW₀ hbW) a (hWW₀ haW) (hWsq b hbW) (hWsq a haW) hb1 ha1)
    have hidx : (B₁ ⊓ B₂).index ≤ 4 := (Subgroup.index_inf_le).trans (by rw [hB₁, hB₂])
    have hcardA : Nat.card A = 2 ^ CFSG.Open.pRank 2 (T : Subgroup G) :=
      card_omegaOneOfComm Nat.prime_two _ hcommT T.isPGroup'
    have h1 := (B₁ ⊓ B₂).card_mul_index
    rw [hcardA, ← Subgroup.card_map_of_injective A.subtype_injective, ← hWdef] at h1
    have h8 : 2 ^ CFSG.Open.pRank 2 (T : Subgroup G) ≤ 2 ^ 3 := by
      rw [← h1]
      calc Nat.card W * (B₁ ⊓ B₂).index ≤ 2 * 4 := Nat.mul_le_mul hW2 hidx
        _ = 2 ^ 3 := by norm_num
    have h3' := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h8
    rw [rank_eq_pRank_of_isPGroup Nat.prime_two T.isPGroup'] at hlow ⊢
    omega
  have hHt : benderM t = {H} := hb t htT ht (hV₂Q.trans htQ)
  have hO2 : qCoreOf H 2 ≤ W₀ := le_inf (qCoreOf_two_le_sylow T hTH)
    ((qCoreOf_centralizer_of_ne H hp Nat.prime_two hp2).trans (Subgroup.centralizer_le hV₂Q))
  have hKW : ∀ K : Subgroup G, IsComponentOf K H → (T : Subgroup G) ⊓ K ≤ W₀ := fun K hK =>
    le_inf inf_le_left (inf_le_right.trans ((le_sSup (s := {E : Subgroup G | IsComponentOf E H})
      hK).trans ((componentLayerOf_le_centralizer_fitting H).trans (Subgroup.centralizer_le
        (hV₂Q.trans (qCoreOf_le_fittingSubgroupOf H p hp))))))
  have htZ : ∀ h ∈ H, h * t * h⁻¹ = t := mem_center_of_forall_eq
    (hG.isAStar_of_isCoatom hHco) T hTH hTab huniq hO2 hKW ht (bender1970_4_1 hG ht hH)
  have hHC : H ≤ Subgroup.centralizer ({t} : Set G) := fun h hh => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc h * t = h * t * h⁻¹ * h := by group
      _ = t * h := by rw [htZ h hh]
  obtain ⟨s, hsR, hs, hsH⟩ := bender1970_3_3 hG ht hH T htT hR₁T hR₁r
  have hsT := hR₁T hsR
  obtain ⟨n, -, hns⟩ := exists_conj_of_rank_eq_three hG.nonabelian T hTab hr3 htT hsT ht hs
  obtain ⟨M, hM, hMH⟩ := hG.exists_mem_benderM_ne hs hsH
  have hMeq : M = H.map (MulAut.conj n).toMonoidHom := by
    have h := benderM_conj_eq_singleton n hHt
    rw [hns] at h
    rw [h] at hM
    exact hM
  have htM : t ∈ M := hG.sylow_le_of_mem_benderM T hsT hM htT
  have hv₁s : v₁ ∈ Subgroup.centralizer ({s} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.mp hv₁R) s hsR).symm
  have hv₁M : v₁ ∈ M := centralizer_le_of_mem_benderM hM hv₁s
  have hQM : qCoreOf M p ≤ Subgroup.centralizer ({t} : Set G) := by
    have hcopp : Nat.Coprime p (orderOf t) := by
      rw [ht]
      exact (Nat.coprime_primes hp Nat.prime_two).mpr hp2
    have hv₁p' : IsPGroup p (Subgroup.zpowers v₁) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hv₁o, pow_one])
    have hMN := le_normalizer_of_isNormalIn (qCoreOf_normal_in M p)
    have hT1 := bender1970_1_1_thompson p hp (Subgroup.zpowers v₁) (Subgroup.zpowers t)
      (qCoreOf M p) hv₁p' (qCoreOf_isPGroup M p) (Bender35.pResidualOf_zpowers_eq hp hcopp)
      (Subgroup.zpowers_le.mpr (hMN hv₁M)) (Subgroup.zpowers_le.mpr (hMN htM))
      (by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer, centralizer_zpowers_eq',
          Subgroup.zpowers_le]
        exact htQ (hPQ hv₁P))
      (by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer, centralizer_zpowers_eq',
          centralizer_zpowers_eq']
        intro x hx
        exact hHC (hPC v₁ hv₁P hv₁1 hx.2))
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (hT1 (Subgroup.mem_zpowers t))) x hx
  have hQMH : qCoreOf M p ≤ H := hQM.trans (centralizer_le_of_mem_benderM hH)
  set V' := V₂.map (MulAut.conj n).toMonoidHom with hV'def
  have hQM' : qCoreOf M p = Q.map (MulAut.conj n).toMonoidHom := by
    rw [hMeq]
    exact qCoreOf_conjugateSubgroup H n p
  have hV'Q : V' ≤ qCoreOf M p := by
    rw [hQM']
    exact Subgroup.map_mono hV₂Q
  have hV'el : CFSG.Open.IsElemAbelian p V' := isElemAbelian_map_conj hV₂el n
  have hV'card : Nat.card V' = p ^ 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj n).injective, hV₂card]
  have hV'1 : V' ≠ ⊥ := by
    rw [hV'def, Ne, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj n).injective]
    exact hV₂1
  have habc' : Bender39Conditions s M T V' p := by
    refine Or.inr (Or.inl ⟨?_, hV'el, hV'card⟩)
    rintro _ ⟨v, hv, rfl⟩ hv1
    have hv1' : v ≠ 1 := fun h => hv1 (by rw [h, map_one])
    refine ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        ← hns]
      have htv : t * v = v * t := (Subgroup.mem_centralizer_singleton_iff.mp (htQ (hV₂Q hv))).symm
      calc n * t * n⁻¹ * (n * v * n⁻¹) = n * (t * v) * n⁻¹ := by group
        _ = n * (v * t) * n⁻¹ := by rw [htv]
        _ = n * v * n⁻¹ * (n * t * n⁻¹) := by group
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← map_conj_centralizer_singleton, hMeq]
      exact Subgroup.map_mono (hV₂C v hv hv1')
  have hQM1 : qCoreOf M p ≠ ⊥ := fun h => hV'1 (le_bot_iff.mp (h ▸ hV'Q))
  have hπM := two_le_card_primes_of_benderM hG ht hH hs hM hp hp2 hπ hQM1
  have h := (bender1970_3_9 hG hs hM T hsT hp hp2 hV'Q ht htT hH (Ne.symm hMH) hπM
    (hV'Q.trans hQMH) habc').2.2 (hV'Q.trans hQM)
  have h2 : 2 ≤ rank (qCoreOf M p) := le_rank hp hV'Q hV'el hV'card
  omega

end Bender42

theorem le_qCoreOf_of_le_fittingSubgroupOf {H E : Subgroup G} {q : ℕ} (hq : q.Prime)
    (hEF : E ≤ CFSG.fittingSubgroupOf H) (hE : IsPGroup q E) : E ≤ qCoreOf H q := by
  have : Fact q.Prime := ⟨hq⟩
  intro x hx
  obtain ⟨x', hx'F, rfl⟩ := hEF hx
  obtain ⟨k, hk⟩ := hE ⟨_, hx⟩
  have hk' : x' ^ q ^ k = 1 := Subtype.ext (by
    have := congrArg Subtype.val hk
    simpa using this)
  exact ⟨x', mem_pCore_of_mem_normal_nilpotent hq CFSG.fittingSubgroup_normal
    CFSG.fittingSubgroup_nilpotent hx'F hk', rfl⟩

theorem bender1970_4_2
    (hG : BenderCounterexample G) {t : G} (ht : orderOf t = 2)
    {H : Subgroup G} (hH : H ∈ benderM t) : rank (oddCoreOf (CFSG.fittingSubgroupOf H)) ≤ 2 := by
  set F := CFSG.fittingSubgroupOf H with hFdef
  have hOF : oddCoreOf F ≤ F := Subgroup.map_subtype_le _
  have hodd : Odd (Nat.card (oddCoreOf F)) := odd_card_oddCoreOf F
  refine rank_le fun q hq => ?_
  by_cases hq2 : q = 2
  · subst hq2
    refine (CFSG.SectionRank.pRank_le hq.one_lt fun E hEX hE => ?_).trans (Nat.zero_le 2)
    rw [pow_zero]
    have hEp : IsPGroup 2 E := fun x => ⟨1, by rw [pow_one]; exact Subtype.ext (hE.2 x x.2)⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := hEp.exists_card_eq
    have hdvd : 2 ^ k ∣ Nat.card (oddCoreOf F) := hk ▸ Subgroup.card_dvd_of_le hEX
    rcases k with _ | k
    · rw [hk, pow_zero]
    · exfalso
      exact (Nat.not_even_iff_odd.mpr hodd)
        (even_iff_two_dvd.mpr ((dvd_pow_self 2 (Nat.succ_ne_zero k)).trans hdvd))
  · have : Fact q.Prime := ⟨hq⟩
    refine le_trans ?_ ((pRank_le_rank hq _).trans
      (Bender42.rank_qCoreOf_le_two hG ht hH hq hq2))
    refine CFSG.SectionRank.pRank_le hq.one_lt fun E hEX hE => ?_
    have hEp : IsPGroup q E := fun x => ⟨1, by rw [pow_one]; exact Subtype.ext (hE.2 x x.2)⟩
    obtain ⟨k, hk⟩ := hEp.exists_card_eq
    rw [hk]
    exact Nat.pow_le_pow_right hq.pos
      (CFSG.SectionRank.le_pRank hq.one_lt (le_qCoreOf_of_le_fittingSubgroupOf hq
        (hEX.trans hOF) hEp) hE hk)

end CFSG.Walter

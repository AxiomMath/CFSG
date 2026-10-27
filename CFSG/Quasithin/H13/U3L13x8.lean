module

public import CFSG.Quasithin.H13.U3L14D4
public import CFSG.Quasithin.H13.U3L14D6
public import CFSG.Quasithin.H13.U3FrameKernel
public import CFSG.Quasithin.H13.U3L15Core
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.Quasithin.Background.C1PackS15348
public import CFSG.Quasithin.EmptyFaithful.S152UGen2
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm318

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def Stmt13_3_4K : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L K X : Subgroup G), QTH13 G T L →
    quasithinIsFaithfulLocal T K → T ≤ X → X ≤ normalizer (K : Set G) →
    ¬ normalizer (K : Set G) ≤
      X ⊔ centralizerMod (pCoreOf 2 K) (normalizer (K : Set G)) K →
    ∀ p : ℕ, p.Prime →
      p ∣ (centralizerMod (pCoreOf 2 K) (normalizer (K : Set G)) K).relIndex X → p = 2 ∨ p = 3

theorem even_not_prime_of_qt13Five {Q : Type} [Group Q] [Finite Q] (h : QT13Five Q) :
    2 ∣ Nat.card (Q ⧸ center Q) ∧ ¬ (Nat.card (Q ⧸ center Q)).Prime := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center Q)
  have hz := card_center_le_three_of_qt13Five h
  have hz0 : 0 < Nat.card (center Q) := Nat.card_pos
  have hc := card_of_qt13Five h
  have h2 : 2 ∣ Nat.card (Q ⧸ center Q) := by
    interval_cases hzc : Nat.card (center Q) <;> rcases hc with hc | hc | hc | hc | hc <;>
      omega
  refine ⟨h2, fun hp => ?_⟩
  have h3 : Nat.card (Q ⧸ center Q) = 2 := (hp.eq_one_or_self_of_dvd 2 h2).resolve_left
    (by norm_num) |>.symm
  rw [h3] at h1
  interval_cases hzc : Nat.card (center Q) <;> rcases hc with hc | hc | hc | hc | hc <;> omega

theorem le_commutator_inf_sup_pCoreOf {T K : Subgroup G} (hT : IsSylowTwoOf T (K ⊔ T))
    (hTK : T ≤ normalizer (K : Set G)) (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (heven : 2 ∣ Nat.card ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ center (↥K ⧸ CFSG.pCore 2 ↥K)))
    (hnp : ¬ (Nat.card ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ center (↥K ⧸ CFSG.pCore 2 ↥K))).Prime) :
    K ≤ ⁅K, T ⊓ K⁆ ⊔ pCoreOf 2 K := by
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  have hS : IsSylowTwoOf (T ⊓ K) K :=
    isSylowTwoOf_inf_of_le_normalizer hT le_sup_left (sup_le le_normalizer hTK)
  have hKS : K ⊔ (T ⊓ K) = K := sup_eq_left.2 inf_le_right
  have hCn : (⁅K, T ⊓ K⁆.subgroupOf K).Normal := by
    have := normal_subgroupOf_commutator_sup (H₁ := K) (H₂ := T ⊓ K)
    rwa [hKS] at this
  have hNn : ((⁅K, T ⊓ K⁆.subgroupOf K).map π).Normal :=
    hCn.map π (QuotientGroup.mk'_surjective _)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hNn with htop | hcen
  · intro k hk
    have hk' : π ⟨k, hk⟩ ∈ (⁅K, T ⊓ K⁆.subgroupOf K).map π := htop ▸ mem_top _
    obtain ⟨n, hn, hnk⟩ := hk'
    have h1 : n⁻¹ * ⟨k, hk⟩ ∈ CFSG.pCore 2 ↥K := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      have : (QuotientGroup.mk n : ↥K ⧸ CFSG.pCore 2 ↥K) = QuotientGroup.mk ⟨k, hk⟩ := hnk
      rw [this, inv_mul_cancel]
    have e : k = n * ((n⁻¹ * ⟨k, hk⟩ : ↥K) : G) := by simp
    rw [e]
    exact mul_mem (mem_sup_left (mem_subgroupOf.1 hn)) (mem_sup_right (coe_mem_pCoreOf_iff.2 h1))
  · exfalso
    obtain ⟨-, hsimp, -⟩ := hq
    set Q := ↥K ⧸ CFSG.pCore 2 ↥K
    set ψ := QuotientGroup.mk' (center Q) with hψ
    have hna : ¬ ∀ a b : Q ⧸ center Q, a * b = b * a := by
      intro hc
      let _ : CommGroup (Q ⧸ center Q) :=
        { (inferInstance : Group (Q ⧸ center Q)) with mul_comm := hc }
      exact hnp (IsSimpleGroup.prime_card (α := Q ⧸ center Q))
    have hZ : center (Q ⧸ center Q) = ⊥ := center_eq_bot_of_simple_noncomm hna
    have hSZ : ∀ s : ↥K, (s : G) ∈ T ⊓ K → ψ (π s) = 1 := by
      intro s hs
      have hc : ψ (π s) ∈ center (Q ⧸ center Q) := by
        rw [mem_center_iff]
        intro g
        obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective (center Q) g
        obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) q
        have hks : π ⁅k, s⁆ ∈ center Q := by
          exact hcen ⟨⁅k, s⁆, mem_subgroupOf.2 (commutator_mem_commutator k.2 hs), rfl⟩
        have h1 : ψ (π ⁅k, s⁆) = 1 := by
          rw [hψ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
          exact hks
        rw [map_commutatorElement, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
          at h1
        exact h1
      rw [hZ, mem_bot] at hc
      exact hc
    have hsurj : Function.Surjective (ψ.comp π) :=
      (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
    have hbot : ((T ⊓ K).subgroupOf K).map (ψ.comp π) = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨s, hs, rfl⟩
      exact (mem_bot).2 (hSZ s (mem_subgroupOf.1 hs))
    have hdvd := index_map_dvd ((T ⊓ K).subgroupOf K) hsurj
    rw [hbot, index_bot] at hdvd
    exact hS.2.2 (heven.trans hdvd)

theorem oTwoUpper_le_of_sup {C S : Subgroup G} (hS : IsPGroup 2 S)
    (hSC : S ≤ normalizer (C : Set G)) : oTwoUpper (C ⊔ S) ≤ C :=
  oTwoUpper_le_of_pow_mem
    (B6.isTwoQuotient_of_sup_eq (C := C) (D := C ⊔ S) hS (sup_le le_normalizer hSC)
      (sup_comm S C))

theorem not_le_sup_centralizerMod (h1332 : Stmt13_3_2) {T L K H Y : Subgroup G}
    (hH13 : QTH13 G T L) (hK : quasithinIsFaithfulLocal T K) (hH : InH T H)
    (hHK : ¬ H ≤ normalizer (K : Set G)) (hYH : Y ≤ H) (hHY : H ≤ normalizer (Y : Set G))
    (hYK : Y ≤ normalizer (K : Set G)) :
    ¬ K ≤ Y ⊔ centralizerMod (pCoreOf 2 K) (normalizer (K : Set G)) K := by
  intro hle
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h5, ⟨hTK, -, hMK, huniq⟩, ⟨⟨VK, hVK⟩, hallK⟩, -⟩ := h1332 G T L hH13 K hK
  have hq := (hallK VK hVK).2.2.1.quasisimple
  obtain ⟨heven, hnp⟩ := even_not_prime_of_qt13Five h5
  have hU : IsUniqueM (K ⊔ T) (normalizer (K : Set G)) :=
    ⟨⟨hMK, sup_le le_normalizer hTK⟩, fun M' hM' => huniq M' hM'.1 hM'.2⟩
  have hstar := pCoreOf_sup_eq_bot_of_isUniqueM hU hHK
  have hsyl : IsSylowTwoOf T ⊤ := by
    refine ⟨le_top, hH13.sylow.1, ?_⟩
    show ¬ 2 ∣ T.relIndex ⊤
    rw [relIndex_top_right]
    exact hH13.sylow.2
  have hsylT : IsSylowTwoOf T (K ⊔ T) := isSylowTwoOf_of_le hsyl le_sup_right
  have hTY : T ≤ normalizer (Y : Set G) := hH.1.trans hHY
  have hYC : Y ≤ normalizer
      (centralizerMod (pCoreOf 2 K) (normalizer (K : Set G)) K : Set G) :=
    le_normalizer_centralizerMod
      (hYK.trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
      (hYK.trans le_normalizer) hYK
  have hcomm : ⁅K, T ⊓ K⁆ ≤ (K ⊓ Y) ⊔ pCoreOf 2 K := by
    rw [commutator_le]
    intro k hk s hs
    obtain ⟨c, hc, y, hy, rfl⟩ := exists_mul_of_mem_sup hYC (sup_comm Y _ ▸ hle hk)
    have hsK : s ∈ K := (mem_inf.1 hs).2
    have hu : y * s * y⁻¹ ∈ K := (mem_normalizer_iff.1 (hYK hy) s).1 hsK
    have ho : c * (y * s * y⁻¹) * c⁻¹ * (y * s * y⁻¹)⁻¹ ∈ pCoreOf 2 K :=
      (mem_centralizerMod.1 hc).2.2 _ hu
    have hwK : y * s * y⁻¹ * s⁻¹ ∈ K := mul_mem hu (inv_mem hsK)
    have hwY : y * s * y⁻¹ * s⁻¹ ∈ Y := by
      have h1 : s * y⁻¹ * s⁻¹ ∈ Y :=
        (mem_normalizer_iff.1 (hTY (mem_inf.1 hs).1) _).1 (inv_mem hy)
      have e : y * s * y⁻¹ * s⁻¹ = y * (s * y⁻¹ * s⁻¹) := by group
      rw [e]
      exact mul_mem hy h1
    have e : ⁅c * y, s⁆ = (c * (y * s * y⁻¹) * c⁻¹ * (y * s * y⁻¹)⁻¹) * (y * s * y⁻¹ * s⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (mem_sup_right ho) (mem_sup_left (mem_inf.2 ⟨hwK, hwY⟩))
  have hK1 : K ≤ (K ⊓ Y) ⊔ pCoreOf 2 K :=
    (le_commutator_inf_sup_pCoreOf hsylT hTK hq heven hnp).trans (sup_le hcomm le_sup_right)
  have hO2T : pCoreOf 2 K ≤ T :=
    (pCoreOf_le_pCoreOf_sup hTK).trans (pCoreOf_two_le_of_isSylowTwoOf hsylT)
  have hO2N : pCoreOf 2 K ≤ normalizer ((K ⊓ Y : Subgroup G) : Set G) := fun o ho =>
    inf_normalizer_le_normalizer_inf
      ⟨le_normalizer (LieType.BorelTits.pCoreOf_le 2 K ho), hTY (hO2T ho)⟩
  have hKY : K ≤ K ⊓ Y := by
    calc K = oTwoUpper K := eq_oTwoUpper_of_perfect hK.1.2.1.2.1
      _ ≤ oTwoUpper ((K ⊓ Y) ⊔ pCoreOf 2 K) := oTwoUpper_mono hK1
      _ ≤ K ⊓ Y := oTwoUpper_le_of_sup (LieType.BorelTits.pCoreOf_isPGroup 2 K) hO2N
  have hKH : K ≤ H := (hKY.trans inf_le_right).trans hYH
  rw [sup_eq_right.2 (sup_le hKH hH.1)] at hstar
  exact hH.2 hstar

theorem isTwoThreeGroup_of (h1332 : Stmt13_3_2) (h1334K : Stmt13_3_4K) {T L K H Y : Subgroup G}
    (hH13 : QTH13 G T L) (hK : quasithinIsFaithfulLocal T K) (hH : InH T H)
    (hHK : ¬ H ≤ normalizer (K : Set G)) (hYH : Y ≤ H) (hHY : H ≤ normalizer (Y : Set G))
    (hYK : Y ≤ normalizer (K : Set G)) : A6.IsTwoThreeGroup Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨hTK, -, hMK, huniq⟩, -, -⟩ := h1332 G T L hH13 K hK
  have hU : IsUniqueM (K ⊔ T) (normalizer (K : Set G)) :=
    ⟨⟨hMK, sup_le le_normalizer hTK⟩, fun M' hM' => huniq M' hM'.1 hM'.2⟩
  have hstar := pCoreOf_sup_eq_bot_of_isUniqueM hU hHK
  have hTY : T ≤ normalizer (Y : Set G) := hH.1.trans hHY
  set C := centralizerMod (pCoreOf 2 K) (normalizer (K : Set G)) K with hCdef
  have hNC : ∀ {X : Subgroup G}, X ≤ normalizer (K : Set G) → X ≤ normalizer (C : Set G) :=
    fun hX => le_normalizer_centralizerMod
      (hX.trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
      (hX.trans le_normalizer) hX
  have hYTK : Y ⊔ T ≤ normalizer (K : Set G) := sup_le hYK hTK
  have hnot : ¬ normalizer (K : Set G) ≤ (Y ⊔ T) ⊔ C := by
    intro hN
    apply not_le_sup_centralizerMod h1332 hH13 hK hH hHK hYH hHY hYK
    have hYCN : T ≤ normalizer ((Y ⊔ C : Subgroup G) : Set G) := fun t ht =>
      inf_normalizer_le_normalizer_sup _ _ ⟨hTY ht, hNC hTK ht⟩
    have hD : (Y ⊔ T) ⊔ C = (Y ⊔ C) ⊔ T := by
      rw [sup_assoc, sup_comm T C, ← sup_assoc]
    calc K = oTwoUpper K := eq_oTwoUpper_of_perfect hK.1.2.1.2.1
      _ ≤ oTwoUpper ((Y ⊔ C) ⊔ T) := oTwoUpper_mono (hD ▸ le_normalizer.trans hN)
      _ ≤ Y ⊔ C := oTwoUpper_le_of_sup hH13.sylow.1 hYCN
  have hprimes := h1334K G T L K (Y ⊔ T) hH13 hK le_sup_right hYTK hnot
  have hYC6 : ∀ y ∈ Y, Nat.Coprime (orderOf y) 6 → y ∈ C := by
    intro y hy hy6
    have hn : (C.subgroupOf (Y ⊔ T)).Normal := ⟨fun n hn g => by
      rw [mem_subgroupOf] at hn ⊢
      simpa using (mem_normalizer_iff.1 (hNC hYTK g.2) n).1 hn⟩
    have h1 : y ^ (C.subgroupOf (Y ⊔ T)).index ∈ C := by
      have := Subgroup.pow_index_mem (C.subgroupOf (Y ⊔ T)) (⟨y, mem_sup_left hy⟩ : ↥(Y ⊔ T))
      rw [mem_subgroupOf] at this
      simpa using this
    have hcop : Nat.Coprime (C.subgroupOf (Y ⊔ T)).index (orderOf y) := by
      refine Nat.coprime_of_dvd fun k hk hkm hky => ?_
      have hk23 := hprimes k hk hkm
      have h6 : k ∣ 6 := by rcases hk23 with rfl | rfl <;> norm_num
      have := Nat.dvd_gcd hky h6
      rw [hy6] at this
      exact hk.one_lt.ne' (Nat.dvd_one.1 this)
    exact (zpowers_le.2 h1) (A4.mem_zpowers_pow_of_coprime hcop)
  set S6 : Set G := {y | y ∈ Y ∧ Nat.Coprime (orderOf y) 6} with hS6
  set Y₀ : Subgroup G := closure S6 with hY₀
  have hodd : ∀ y ∈ S6, Odd (orderOf y) := fun y hy =>
    Nat.coprime_two_left.mp (Nat.Coprime.coprime_dvd_right (by norm_num : 2 ∣ 6) hy.2).symm
  have hY₀Y : Y₀ ≤ Y := (closure_le _).2 fun y hy => hy.1
  have hY₀C : Y₀ ≤ C := (closure_le _).2 fun y hy => hYC6 y hy.1 hy.2
  have hconj : ∀ g : G, (∀ s ∈ S6, g * s * g⁻¹ ∈ Y₀) → ∀ x ∈ Y₀, g * x * g⁻¹ ∈ Y₀ := by
    intro g hg x hx
    have hle : Y₀ ≤ Y₀.comap (MulAut.conj g).toMonoidHom := (closure_le _).2 fun s hs => hg s hs
    exact hle hx
  have hnorm : ∀ {A : Subgroup G}, (∀ g ∈ A, ∀ s ∈ S6, g * s * g⁻¹ ∈ Y₀) →
      A ≤ normalizer (Y₀ : Set G) := by
    intro A hA g hg
    rw [mem_normalizer_iff]
    intro x
    refine ⟨hconj g (hA g hg) x, fun hx => ?_⟩
    have := hconj g⁻¹ (hA g⁻¹ (inv_mem hg)) _ hx
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rwa [e] at this
  have hHY₀ : H ≤ normalizer (Y₀ : Set G) := hnorm fun g hg s hs => subset_closure
    ⟨(mem_normalizer_iff.1 (hHY hg) s).1 hs.1, by
      have := MulEquiv.orderOf_eq (MulAut.conj g) s
      rw [MulAut.conj_apply] at this
      rw [this]
      exact hs.2⟩
  have hO2T : pCoreOf 2 K ≤ T := (pCoreOf_le_pCoreOf_sup hTK).trans
    (pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_le (by
      refine ⟨le_top, hH13.sylow.1, ?_⟩
      show ¬ 2 ∣ T.relIndex ⊤
      rw [relIndex_top_right]
      exact hH13.sylow.2) le_sup_right))
  have hKY₀ : K ≤ normalizer (Y₀ : Set G) := hnorm fun k hk s hs => by
    have hsC : s⁻¹ ∈ C := inv_mem (hYC6 s hs.1 hs.2)
    have ho : s⁻¹ * k * s⁻¹⁻¹ * k⁻¹ ∈ pCoreOf 2 K := (mem_centralizerMod.1 hsC).2.2 k hk
    have hmem : k * s * k⁻¹ ∈ Y₀ ⊔ pCoreOf 2 K := by
      have e : k * s * k⁻¹ = s * (s⁻¹ * k * s⁻¹⁻¹ * k⁻¹) := by group
      rw [e]
      exact mul_mem (mem_sup_left (subset_closure hs)) (mem_sup_right ho)
    have hord : Odd (orderOf (k * s * k⁻¹)) := by
      have := MulEquiv.orderOf_eq (MulAut.conj k) s
      rw [MulAut.conj_apply] at this
      rw [this]
      exact hodd s hs
    exact oTwoUpper_le_of_sup (LieType.BorelTits.pCoreOf_isPGroup 2 K)
      ((hO2T.trans hH.1).trans hHY₀) (mem_oTwoUpper_of_odd hmem hord)
  have hO2 : pCoreOf 2 Y₀ = ⊥ := by
    rw [eq_bot_iff, ← hstar]
    refine LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (((LieType.BorelTits.pCoreOf_le 2 Y₀).trans (hY₀Y.trans hYH)).trans le_sup_right) ?_
      (LieType.BorelTits.pCoreOf_isPGroup 2 Y₀)
    exact (sup_le (sup_le hKY₀ (hH.1.trans hHY₀)) hHY₀).trans
      (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀)
  have hCT : CharTwo H := by
    obtain ⟨P, hP⟩ := exists_sylow_of_quasithinIsSylowTwo hH13.sylow
    subst hP
    exact CFSG.Quasithin.charTwo_of_inH hH13.qtke.2.1 P hH
  have hY₀2 : oTwoUpper Y₀ = Y₀ :=
    le_antisymm (oTwoUpper_le Y₀) ((closure_le _).2 fun y hy =>
      mem_oTwoUpper_of_odd (subset_closure hy) (hodd y hy))
  have hY₀1 : Y₀ = ⊥ := by
    by_contra hne
    exact C1Pack153.pCoreOf_ne_bot_of_normal hCT (hY₀Y.trans hYH) hHY₀ hne hY₀2 hO2
  intro p hp hpY
  by_contra hne
  push Not at hne
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) p hpY
  have hy' : orderOf (y : G) = p := by rw [Subgroup.orderOf_coe]; exact hy
  have hcop : Nat.Coprime (orderOf (y : G)) 6 := by
    rw [hy', show (6 : ℕ) = 2 * 3 by norm_num]
    exact Nat.Coprime.mul_right ((Nat.coprime_primes hp Nat.prime_two).2 hne.1)
      ((Nat.coprime_primes hp Nat.prime_three).2 hne.2)
  have h1 : (y : G) ∈ Y₀ := subset_closure ⟨y.2, hcop⟩
  rw [hY₀1, mem_bot] at h1
  rw [h1, orderOf_one] at hy'
  exact hp.one_lt.ne hy'

theorem stmt13_3_8_of (h1332 : Stmt13_3_2) (h1334K : Stmt13_3_4K) : A6.Stmt13_3_8 := by
  intro G _ _ T L K H Y hH13 hK hH hHK _ hYH hHY hYK
  exact ⟨not_le_sup_centralizerMod h1332 hH13 hK hH hHK hYH hHY hYK,
    isTwoThreeGroup_of h1332 h1334K hH13 hK hH hHK hYH hHY hYK⟩

end CFSG.Quasithin.H13.U3

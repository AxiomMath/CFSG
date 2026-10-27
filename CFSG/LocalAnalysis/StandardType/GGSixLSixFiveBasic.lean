module

public import CFSG.LocalAnalysis.StandardType.GGSixStepOneSmallImage

public section

namespace CFSG.StandardType

open CFSG.Assembly

open scoped commutatorElement

section General

variable {G : Type} [Group G]

theorem ggExists_mul_of_mem_sup_of_le_normalizer {H N : Subgroup G}
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) {g : G} (hg : g ∈ H ⊔ N) :
    ∃ h ∈ H, ∃ n ∈ N, h * n = g := by
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right H N hHN
  have hg' : g ∈ ((H ⊔ N : Subgroup G) : Set G) := hg
  rw [hset] at hg'
  obtain ⟨h, hh, n, hn, rfl⟩ := hg'
  exact ⟨h, hh, n, hn, rfl⟩

theorem ggEq_one_of_mem_odd_of_mem_two [Finite G] {O P : Subgroup G}
    (hO : Odd (Nat.card O)) (hP : IsPGroup 2 P) {g : G} (hgO : g ∈ O) (hgP : g ∈ P) : g = 1 := by
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  obtain ⟨m, hm⟩ := (hP.to_le (Subgroup.zpowers_le.mpr hgP)).exists_card_eq
  have h1 : Nat.card (Subgroup.zpowers g) ∣ Nat.card O :=
    Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hgO)
  rw [hm] at h1
  have hm0 : m = 0 := by
    by_contra hm0
    exact (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr ((dvd_pow_self 2 hm0).trans h1))
  rw [hm0, pow_zero, Nat.card_zpowers, orderOf_eq_one_iff] at hm
  exact hm

theorem ggIsTwoLocal_centralizer_of_orderOf_two {r : G} (hr : orderOf r = 2) :
    IsTwoLocal (Subgroup.centralizer ({r} : Set G)) := by
  have hr1 : r ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hr
    exact absurd hr (by norm_num)
  refine ⟨Subgroup.zpowers r, fun h => hr1 (Subgroup.zpowers_eq_bot.mp h), ?_, ?_⟩
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hr, pow_one])
  · refine le_antisymm (fun g hg => ?_) (fun g hg => ?_)
    · refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      exact hg
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have hmem : g * r * g⁻¹ ∈ Subgroup.zpowers r :=
        (Subgroup.mem_normalizer_iff.mp hg r).mp (Subgroup.mem_zpowers r)
      have hsq : r ^ 2 = 1 := hr ▸ pow_orderOf_eq_one r
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hk' : r ^ k = r ^ (k % 2) := by
        rw [← zpow_mod_orderOf, hr]
        norm_num
      have hcases : k % 2 = 0 ∨ k % 2 = 1 := by omega
      rcases hcases with h0 | h1
      · exfalso
        rw [hk', h0, zpow_zero] at hk
        apply hr1
        have := congrArg (fun y => g⁻¹ * y * g) hk
        simpa [mul_assoc] using this.symm
      · rw [hk', h1, zpow_one] at hk
        calc g * r = g * r * g⁻¹ * g := by group
          _ = r * g := by rw [← hk]

theorem ggLe_pCoreOf_two_of_charTwo (hG : IsCharTwoType G) {r : G} (hr : orderOf r = 2)
    {R : Subgroup G} (hRr : R ≤ Subgroup.centralizer ({r} : Set G))
    (hRP : R ≤ Subgroup.centralizer (pCoreOf 2 (Subgroup.centralizer ({r} : Set G)) : Set G)) :
    R ≤ pCoreOf 2 (Subgroup.centralizer ({r} : Set G)) :=
  (le_inf hRr hRP).trans (hG _ (ggIsTwoLocal_centralizer_of_orderOf_two hr))

theorem ggLe_centralizer_of_generation_le [Finite G] {q : ℕ} [Fact q.Prime] {R Q S : Subgroup G}
    (hR : IsElemAbelian q R) (hRc : q ^ 2 ≤ Nat.card R) (hQ : ¬ q ∣ Nat.card Q)
    (hRQ : R ≤ Subgroup.normalizer (Q : Set G))
    (hS : ∀ a ∈ R, a ≠ 1 →
      S ≤ Subgroup.centralizer ((Q ⊓ Subgroup.centralizer {a} : Subgroup G) : Set G)) :
    S ≤ Subgroup.centralizer (Q : Set G) := by
  have : CFSG.IsElementaryAbelian q ↥R := ggIsElementaryAbelian hR
  let : MulDistribMulAction ↥R ↥Q := MulDistribMulAction.compHom ↥Q (Subgroup.inclusion hRQ)
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := q) (A := ↥R) (H := ↥Q)
    hRc hQ
  have hC : (⊤ : Subgroup ↥Q) ≤ (Subgroup.centralizer (S : Set G)).subgroupOf Q := by
    rw [← hgen]
    refine iSup₂_le fun a ha => ?_
    intro y hy
    have hfix := (CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff a y).1 hy
    have hc : (a : G) * y * (a : G)⁻¹ = y := congrArg Subtype.val hfix
    have ha1 : (a : G) ≠ 1 := fun h => ha (Subtype.ext h)
    have hyC : (y : G) ∈ Q ⊓ Subgroup.centralizer {(a : G)} := by
      refine Subgroup.mem_inf.mpr ⟨y.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (y : G) * a = (a : G) * y * (a : G)⁻¹ * a := by rw [hc]
        _ = a * y := by rw [inv_mul_cancel_right]
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    intro s hs
    exact ((Subgroup.mem_centralizer_iff.mp (hS a a.2 ha1 hs)) y hyC).symm
  intro s hs
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have := hC (Subgroup.mem_top (⟨y, hy⟩ : ↥Q))
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at this
  exact (this s hs).symm

end General

section Cover

variable {G : Type} [Group G] [Finite G]

theorem ggEq_sup_pPrimeCoreOf_of_centralizes {p : ℕ} [Fact p.Prime]
    {Y A J : Subgroup G} {x : G} (hA : LargeEvenPComponent p Y A) (hJA : J ≤ A)
    (hJ : IsComponentOf J (Y ⊓ Subgroup.centralizer {x})) (hpJ : p ∣ Nat.card J)
    (hxA : x ∈ Subgroup.normalizer (A : Set G)) (hxp : x ^ p = 1)
    (hxc : ⁅A, Subgroup.zpowers x⁆ ≤ LargeEvenPPrimeCoreOf p A) :
    A = J ⊔ LargeEvenPPrimeCoreOf p A := by
  set π := QuotientGroup.mk' (LargeEvenPPrimeCore p ↥Y) with hπ
  have hAY : A ≤ Y := hA.1
  have hJY : J ≤ Y := hJ.1.trans inf_le_left
  have hA₀Y : LargeEvenPPrimeCoreOf p A ≤ LargeEvenPPrimeCoreOf p Y :=
    ggPPrimeCoreOf_le_of_isSubnormal hA.2.1
  have hĀ : IsComponentOf ((A.subgroupOf Y).map π) ⊤ := hA.2.2.1
  have hCA : ((A ⊓ Subgroup.centralizer {x}).subgroupOf Y).map π = (A.subgroupOf Y).map π := by
    refine le_antisymm (Subgroup.map_mono (Subgroup.subgroupOf_mono Y inf_le_left)) ?_
    rintro _ ⟨⟨a, haY⟩, ha, rfl⟩
    have ha' : a ∈ A := ha
    obtain ⟨c, hc, hca⟩ := ggExists_centralizer_mul (Subgroup.map_subtype_le _)
      (ggNormalizer_le_normalizer_pPrimeCoreOf p A hxA) hxp
      ((Nat.Prime.coprime_iff_not_dvd Fact.out).mp (ggPPrimeCoreOf_coprime A)) hxc ha'
    refine ⟨⟨c, hAY (Subgroup.mem_inf.mp hc).1⟩, Subgroup.mem_subgroupOf.mpr hc, ?_⟩
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    obtain ⟨w, hw, hwe⟩ := hA₀Y hca
    have : (⟨c, hAY (Subgroup.mem_inf.mp hc).1⟩ : ↥Y)⁻¹ * ⟨a, haY⟩ = w :=
      Subtype.ext (by simpa using hwe.symm)
    rw [this]
    exact hw
  have hJC : IsSubnormal J (A ⊓ Subgroup.centralizer {x}) :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hJ
      (le_inf hJA (hJ.1.trans inf_le_right)) (inf_le_inf_right _ hAY)).2.1
  have hJCi := ggIsSubnormal_map_quotient p (Y := Y) hJC
  rw [hCA] at hJCi
  have hJtop : IsSubnormal ((J.subgroupOf Y).map π) ⊤ :=
    CFSG.LocalAnalysis.ComponentInitial.assembly_isSubnormal_trans hJCi hĀ.2.1
  have hJĀ : (J.subgroupOf Y).map π ≤ (A.subgroupOf Y).map π :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono Y hJA)
  have hJJ : ⁅J, J⁆ = J := commutator_self_eq_of_isQuasisimple hJ.2.2
  have himgJJ : ⁅(J.subgroupOf Y).map π, (J.subgroupOf Y).map π⁆ = (J.subgroupOf Y).map π := by
    rw [← Subgroup.map_commutator, ← ggSubgroupOf_commutator hJY hJY, hJJ]
  have heq : (J.subgroupOf Y).map π = (A.subgroupOf Y).map π := by
    rcases isComponentOf_le_or_commutator_eq_bot hĀ hJtop with h | h
    · exact le_antisymm hJĀ h
    · exfalso
      have hbot : (J.subgroupOf Y).map π = ⊥ := by
        rw [← himgJJ, eq_bot_iff, ← h]
        exact Subgroup.commutator_mono hJĀ le_rfl
      have hJW := ggLe_pPrimeCoreOf_of_map_eq_bot p hJY hbot
      exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mp
        ((ggPPrimeCoreOf_coprime Y).coprime_dvd_right (Subgroup.card_dvd_of_le hJW)) hpJ
  have hcore : A ⊓ LargeEvenPPrimeCoreOf p Y ≤ LargeEvenPPrimeCoreOf p A := by
    refine ggLe_pPrimeCoreOf inf_le_left (fun g hg => ggMem_normalizer_inf_of
      (Subgroup.le_normalizer hg) ?_) ?_
    · exact ggNormalizer_le_normalizer_pPrimeCoreOf p Y (Subgroup.le_normalizer (hAY hg))
    · exact (ggPPrimeCoreOf_coprime Y).coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
  refine le_antisymm (fun a ha => ?_) (sup_le hJA (Subgroup.map_subtype_le _))
  have hmem : π ⟨a, hAY ha⟩ ∈ (J.subgroupOf Y).map π := heq ▸ ⟨⟨a, hAY ha⟩, ha, rfl⟩
  obtain ⟨⟨j, hjY⟩, hj, hjeq⟩ := hmem
  have hj' : j ∈ J := hj
  have hw : (⟨j, hjY⟩ : ↥Y)⁻¹ * ⟨a, hAY ha⟩ ∈ LargeEvenPPrimeCore p ↥Y := by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hjeq
    exact QuotientGroup.eq.mp hjeq
  have hwY : j⁻¹ * a ∈ LargeEvenPPrimeCoreOf p Y := ⟨_, hw, by simp⟩
  have hwA : j⁻¹ * a ∈ LargeEvenPPrimeCoreOf p A :=
    hcore ⟨A.mul_mem (A.inv_mem (hJA hj')) ha, hwY⟩
  have ha_eq : a = j * (j⁻¹ * a) := by group
  rw [ha_eq]
  exact Subgroup.mul_mem_sup hj' hwA

theorem ggEq_of_le_of_eq_sup_pPrimeCoreOf {p : ℕ} [Fact p.Prime] {Y A J K : Subgroup G}
    (hA : IsSubnormal A Y) (hJA : J ≤ A) (hAeq : A = J ⊔ LargeEvenPPrimeCoreOf p A)
    (hJ : CFSG.Assembly.IsQuasisimple ↥J) (hpJ : p ∣ Nat.card J)
    (hK : CFSG.Assembly.IsQuasisimple ↥K) (hJK : J ≤ K) (hKY : K ≤ Y) : K = J := by
  have hAK : IsSubnormal (A ⊓ K) K := by
    have h := ggIsSubnormal_inf hA K
    rwa [inf_eq_right.mpr hKY] at h
  have hKc : IsComponentOf K K := ⟨le_rfl, IsSubnormal.refl K, hK⟩
  have hKA : K ≤ A := by
    rcases isComponentOf_le_or_commutator_eq_bot hKc hAK with h | h
    · exact h.trans inf_le_left
    · exfalso
      apply commutator_ne_bot_of_isQuasisimple hJ
      exact le_bot_iff.mp ((Subgroup.commutator_mono hJK (le_inf hJA hJK)).trans h.le)
  set O := LargeEvenPPrimeCoreOf p A with hO
  have hNO : A ≤ Subgroup.normalizer (O : Set G) := fun a ha =>
    ggNormalizer_le_normalizer_pPrimeCoreOf p A (Subgroup.le_normalizer ha)
  have hKO : K ≤ Subgroup.normalizer ((K ⊓ O : Subgroup G) : Set G) := fun k hk =>
    ggMem_normalizer_inf_of (Subgroup.le_normalizer hk) (hNO (hKA hk))
  rcases ggLe_center_or_eq_of_normalized hK inf_le_left hKO with hc | heq
  ·
    have hKN : K ≤ Subgroup.normalizer (J : Set G) := by
      intro k hk
      have hk' : k ∈ J ⊔ O := hAeq ▸ hKA hk
      obtain ⟨j, hj, o, ho, rfl⟩ :=
        ggExists_mul_of_mem_sup_of_le_normalizer (fun j hj => hNO (hJA hj)) hk'
      have hoK : o ∈ K := by
        have ho' : o = j⁻¹ * (j * o) := by group
        rw [ho']
        exact K.mul_mem (K.inv_mem (hJK hj)) hk
      have hoC : o ∈ Subgroup.centralizer (K : Set G) := hc ⟨hoK, ho⟩
      have hoJ : o ∈ Subgroup.normalizer (J : Set G) :=
        Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hJK hoC)
      exact Subgroup.mul_mem _ (Subgroup.le_normalizer hj) hoJ
    rcases ggLe_center_or_eq_of_normalized hK hJK hKN with h | h
    · exfalso
      apply commutator_ne_bot_of_isQuasisimple hJ
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact h.trans (Subgroup.centralizer_le hJK)
    · exact h.symm
  · exfalso
    have hJO : J ≤ O := hJK.trans (heq ▸ inf_le_right)
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mp
      ((ggPPrimeCoreOf_coprime A).coprime_dvd_right (Subgroup.card_dvd_of_le hJO)) hpJ

end Cover

section RootFour

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ggIsPGroup_pCoreOf_two (H : Subgroup G) : IsPGroup 2 ↥(pCoreOf 2 H) :=
  (Dichotomy.CentralizerContainment.pCore_isPGroup_assembly 2 _).map H.subtype

theorem ggLe_pCoreOf_two_of_generation (hG : IsCharTwoType G) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {D R : Subgroup G} {r : G} (hr : orderOf r = 2) (hD : IsElemAbelian p D)
    (hDc : Nat.card D = p ^ 2) (hDr : D ≤ Subgroup.centralizer ({r} : Set G))
    (hRr : R ≤ Subgroup.centralizer ({r} : Set G))
    (hRe : ∀ e ∈ D, e ≠ 1 → ∃ O : Subgroup G, Odd (Nat.card O) ∧
      ⁅R, pCoreOf 2 (Subgroup.centralizer ({r} : Set G)) ⊓ Subgroup.centralizer {e}⁆ ≤ O) :
    R ≤ pCoreOf 2 (Subgroup.centralizer ({r} : Set G)) := by
  set P := pCoreOf 2 (Subgroup.centralizer ({r} : Set G)) with hPdef
  have hP2 : IsPGroup 2 ↥P := ggIsPGroup_pCoreOf_two _
  have hPp : ¬ p ∣ Nat.card P := by
    obtain ⟨k, hk⟩ := hP2.exists_card_eq
    rw [hk]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp
      ((Fact.out : p.Prime).dvd_of_dvd_pow h))
  have hDP : D ≤ Subgroup.normalizer (P : Set G) := fun d hd => mem_normalizer_pCoreOf (hDr hd)
  have hS : ∀ e ∈ D, e ≠ 1 →
      R ≤ Subgroup.centralizer ((P ⊓ Subgroup.centralizer {e} : Subgroup G) : Set G) := by
    intro e he he1 s hs
    obtain ⟨O, hO, hRO⟩ := hRe e he he1
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have hcO : ⁅s, c⁆ ∈ O := hRO (Subgroup.commutator_mem_commutator hs hc)
    have hcP : ⁅s, c⁆ ∈ P :=
      ggCommutatorElement_mem_right (Subgroup.mem_inf.mp hc).1 (mem_normalizer_pCoreOf (hRr hs))
    have h1 := ggEq_one_of_mem_odd_of_mem_two hO hP2 hcO hcP
    rw [commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  have hRP : R ≤ Subgroup.centralizer (P : Set G) :=
    ggLe_centralizer_of_generation hD hDc hPp hDP hS
  exact ggLe_pCoreOf_two_of_charTwo hG hr hRr hRP

theorem ggLe_centralizer_of_le_pCoreOf_two {J R E : Subgroup G}
    (hJ : CFSG.Assembly.IsQuasisimple ↥J) (hRJ : R ≤ J) (hR : IsElemAbelian 2 R)
    (hR4 : 4 ≤ Nat.card R) (hRZ : ¬ R ≤ Subgroup.centralizer (J : Set G))
    (hJE : J ≤ Subgroup.normalizer (E : Set G)) (hE : Odd (Nat.card E))
    (hRP : ∀ r ∈ R, r ≠ 1 → R ≤ pCoreOf 2 (Subgroup.centralizer ({r} : Set G))) :
    E ≤ Subgroup.centralizer (J : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRcomm : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hR.1.is_comm.comm (⟨a, ha⟩ : ↥R) ⟨b, hb⟩)
  have hRF : ∀ r ∈ R, r ≠ 1 →
      R ≤ Subgroup.centralizer ((E ⊓ Subgroup.centralizer {r} : Subgroup G) : Set G) := by
    intro r hr hr1 s hs
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    obtain ⟨hfE, hfr⟩ := Subgroup.mem_inf.mp hf
    have hcE : ⁅s, f⁆ ∈ E := ggCommutatorElement_mem_right hfE (hJE (hRJ hs))
    have hcP : ⁅s, f⁆ ∈ pCoreOf 2 (Subgroup.centralizer ({r} : Set G)) :=
      ggCommutatorElement_mem_left (hRP r hr hr1 hs) (mem_normalizer_pCoreOf hfr)
    have h1 := ggEq_one_of_mem_odd_of_mem_two hE (ggIsPGroup_pCoreOf_two _) hcE hcP
    rw [commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  have hE2 : ¬ 2 ∣ Nat.card E := fun h => (Nat.not_even_iff_odd.mpr hE) (even_iff_two_dvd.mpr h)
  have hR4' : 2 ^ 2 ≤ Nat.card R := by rw [show (2 : ℕ) ^ 2 = 4 by norm_num]; exact hR4
  have hRE : R ≤ Subgroup.centralizer (E : Set G) :=
    ggLe_centralizer_of_generation_le hR hR4' hE2 (hRJ.trans hJE) hRF
  have hJN : J ≤ Subgroup.normalizer
      ((J ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) : Set G) := fun j hj =>
    ggMem_normalizer_inf_of (Subgroup.le_normalizer hj)
      (normalizer_le_normalizer_centralizer E (hJE hj))
  rcases ggLe_center_or_eq_of_normalized hJ inf_le_left hJN with h | h
  · exact absurd ((le_inf hRJ hRE).trans h) hRZ
  · rw [Subgroup.le_centralizer_iff]
    exact h.symm.le.trans inf_le_right

end RootFour

end CFSG.StandardType

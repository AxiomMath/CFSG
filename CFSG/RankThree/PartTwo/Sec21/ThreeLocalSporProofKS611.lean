module

public import CFSG.RankThree.PartTwo.Sec6.Item611Res4ProofUPlus
public import CFSG.RankThree.PartTwo.Sec21.ThreeLocalSporProofMcL
public import CFSG.RankThree.PartTwo.Sec21.ThreeLocalSporProofG2
import CFSG.RankThree.PartTwo.Sec6.BThreeCensusOrders
import CFSG.Models.PGLSimple

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)

open CFSG.Sporadic.Schreier (mclP)

@[expose] def KCentCharThreeL43 : Prop :=
  ∀ z : projSL 4 (GaloisField 3 1), orderOf z = 3 →
    IsCharacteristicP 3 ↥(Subgroup.centralizer ({z} : Set (projSL 4 (GaloisField 3 1))))

@[expose] def KCentCharThreeU43 : Prop :=
  ∀ z : projSU 4 3 1, orderOf z = 3 →
    IsCharacteristicP 3 ↥(Subgroup.centralizer ({z} : Set (projSU 4 3 1)))

namespace ThreeLocalSporProof

theorem sq_conj_eq_of_mem_zpowers {X : Type*} [Group X] {k x : X} (hk : orderOf k = 3)
    (hx : x * k * x⁻¹ ∈ Subgroup.zpowers k) : x ^ 2 * k * (x ^ 2)⁻¹ = k := by
  have hk3 : k ^ 3 = 1 := by rw [← hk, pow_orderOf_eq_one]
  have hk1 : k ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hk
    omega
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hmod : k ^ n = k ^ (n % 3) := by
    rw [← zpow_mod_orderOf, hk]
    rfl
  have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  have hconj : ∀ y : X, x * y * x⁻¹ = (MulAut.conj x) y := fun y => rfl
  rcases hcases with h0 | h1 | h2
  · exfalso
    rw [hmod, h0, zpow_zero] at hn
    apply hk1
    have h : k = x⁻¹ * (x * k * x⁻¹) * x := by group
    rw [← hn, mul_one, inv_mul_cancel] at h
    exact h
  · rw [hmod, h1, zpow_one] at hn
    calc x ^ 2 * k * (x ^ 2)⁻¹ = x * (x * k * x⁻¹) * x⁻¹ := by
          rw [pow_two, mul_inv_rev]; group
      _ = k := by rw [← hn, ← hn]
  · rw [hmod, h2] at hn
    have hk2 : k ^ (2 : ℤ) = k⁻¹ := by
      rw [show (2 : ℤ) = 3 - 1 by norm_num, zpow_sub, zpow_one]
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by rfl, zpow_natCast, hk3, one_mul]
    rw [hk2] at hn
    calc x ^ 2 * k * (x ^ 2)⁻¹ = x * (x * k * x⁻¹) * x⁻¹ := by
          rw [pow_two, mul_inv_rev]; group
      _ = x * k⁻¹ * x⁻¹ := by rw [← hn]
      _ = (x * k * x⁻¹)⁻¹ := by group
      _ = k := by rw [← hn, inv_inv]

theorem le_center_of_normal_card_three {X : Type*} [Group X] {K : Subgroup X} (hKn : K.Normal)
    (hK3 : Nat.card K = 3) (hs : IsSimpleGroup (X ⧸ K)) (h3 : ∃ g : X ⧸ K, orderOf g = 3) :
    K ≤ Subgroup.center X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKcyc : IsCyclic K := isCyclic_of_prime_card hK3
  obtain ⟨k, hk⟩ := hKcyc.exists_generator
  have hko : orderOf (k : X) = 3 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hk, hK3]
  have hKz : K = Subgroup.zpowers (k : X) := by
    apply le_antisymm
    · intro y hy
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hk ⟨y, hy⟩)
      exact ⟨n, by simpa using congrArg Subtype.val hn⟩
    · rw [Subgroup.zpowers_le]
      exact k.2
  set C := Subgroup.centralizer (K : Set X) with hC
  have hsq : ∀ x : X, x ^ 2 ∈ C := by
    intro x
    have hxk : x * (k : X) * x⁻¹ ∈ Subgroup.zpowers (k : X) := by
      rw [← hKz]
      exact hKn.conj_mem _ k.2 x
    have h := sq_conj_eq_of_mem_zpowers hko hxk
    rw [hC, hKz, Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hcomm : Commute (x ^ 2) (k : X) := by
      change x ^ 2 * k = k * x ^ 2
      calc x ^ 2 * (k : X) = x ^ 2 * k * (x ^ 2)⁻¹ * x ^ 2 := by group
        _ = k * x ^ 2 := by rw [h]
    exact (hcomm.zpow_right n).eq.symm
  have hCn : C.Normal := Subgroup.normal_centralizer
  have hCbn : (C.map (QuotientGroup.mk' K)).Normal :=
    hCn.map (QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K)
  rcases hs.eq_bot_or_eq_top_of_normal (C.map (QuotientGroup.mk' K)) with hbot | htop
  · exfalso
    obtain ⟨g, hg⟩ := h3
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K g
    have hx2 : (QuotientGroup.mk' K x) ^ 2 = 1 := by
      rw [← map_pow]
      have : QuotientGroup.mk' K (x ^ 2) ∈ C.map (QuotientGroup.mk' K) := ⟨_, hsq x, rfl⟩
      rw [hbot] at this
      exact this
    have := orderOf_dvd_of_pow_eq_one hx2
    rw [hg] at this
    norm_num at this
  · have hCtop : C = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : QuotientGroup.mk' K x ∈ C.map (QuotientGroup.mk' K) := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨c, hc, hcx⟩ := hx
      have hKC : K ≤ C := by
        intro a ha
        rw [hC, Subgroup.mem_centralizer_iff]
        intro b hb
        rw [hKz] at ha hb
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
        exact zpow_mul_comm (k : X) n m
      have hmem : c⁻¹ * x ∈ K := by
        rw [← QuotientGroup.eq]
        exact hcx
      have := C.mul_mem hc (hKC hmem)
      rwa [mul_inv_cancel_left] at this
    intro a ha
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ C := by rw [hCtop]; exact Subgroup.mem_top g
    exact (Subgroup.mem_centralizer_iff.mp hg a ha).symm

theorem ks611Conclusion_of_surjective {X Xb : Type*} [Group X] [Group Xb] [Finite X]
    (π : X →* Xb) (hπ : Function.Surjective π) (hZ : π.ker ≤ Subgroup.center X)
    (hp : IsPGroup 3 π.ker) (hc : Nat.card π.ker ≤ 3)
    (hXb : ∀ z : Xb, orderOf z = 3 → IsCharacteristicP 3 ↥(Subgroup.centralizer ({z} : Set Xb)))
    (Y : Subgroup X) (hY : CFSG.Assembly.IsElemAbelian 3 Y) (h9 : 9 ≤ Nat.card Y) :
    Subgroup.centralizer (Y : Set X) ⊓
        Subgroup.centralizer
          (inSubgroup (CFSG.pCore 3) (Subgroup.centralizer (Y : Set X)) : Set X) ≤
      inSubgroup (CFSG.pCore 3) (Subgroup.centralizer (Y : Set X)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hYK : ¬ Y ≤ π.ker := fun hle => by
    have := Subgroup.card_le_of_le hle
    omega
  exact inf_centralizer_le_of_isCharacteristicP
    (isCharacteristicP_centralizer_of_surjective π hπ hZ hp hXb hY hYK)

theorem ks611Conclusion_of_mulEquiv {X Xb : Type*} [Group X] [Group Xb] [Finite X] (e : X ≃* Xb)
    (hXb : ∀ z : Xb, orderOf z = 3 → IsCharacteristicP 3 ↥(Subgroup.centralizer ({z} : Set Xb)))
    (Y : Subgroup X) (hY : CFSG.Assembly.IsElemAbelian 3 Y) (h9 : 9 ≤ Nat.card Y) :
    Subgroup.centralizer (Y : Set X) ⊓
        Subgroup.centralizer
          (inSubgroup (CFSG.pCore 3) (Subgroup.centralizer (Y : Set X)) : Set X) ≤
      inSubgroup (CFSG.pCore 3) (Subgroup.centralizer (Y : Set X)) := by
  have hker : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr e.injective
  refine ks611Conclusion_of_surjective e.toMonoidHom e.surjective (by rw [hker]; exact bot_le)
    (by rw [hker]; exact IsPGroup.of_bot) (by rw [hker, Subgroup.card_bot]; omega) hXb Y hY h9

theorem ks611Conclusion_of_quot {X Xb : Type*} [Group X] [Group Xb] [Finite X] {K : Subgroup X}
    [K.Normal] (hKZ : K ≤ Subgroup.center X) (hK3 : Nat.card K = 3) (e : X ⧸ K ≃* Xb)
    (hXb : ∀ z : Xb, orderOf z = 3 → IsCharacteristicP 3 ↥(Subgroup.centralizer ({z} : Set Xb)))
    (Y : Subgroup X) (hY : CFSG.Assembly.IsElemAbelian 3 Y) (h9 : 9 ≤ Nat.card Y) :
    Subgroup.centralizer (Y : Set X) ⊓
        Subgroup.centralizer
          (inSubgroup (CFSG.pCore 3) (Subgroup.centralizer (Y : Set X)) : Set X) ≤
      inSubgroup (CFSG.pCore 3) (Subgroup.centralizer (Y : Set X)) := by
  have hker : (e.toMonoidHom.comp (QuotientGroup.mk' K)).ker = K := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff e e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  refine ks611Conclusion_of_surjective (e.toMonoidHom.comp (QuotientGroup.mk' K))
    (e.surjective.comp (QuotientGroup.mk'_surjective K)) (by rw [hker]; exact hKZ)
    (by rw [hker]; exact IsPGroup.of_card (n := 1) (by rw [hK3, pow_one]))
    (by rw [hker, hK3]) hXb Y hY h9

theorem isSimpleGroup_projSU_four_three : IsSimpleGroup (projSU 4 3 1) :=
  CFSG.PGLModel.isSimpleGroup_projSU_of_admissible ⟨Nat.prime_three, le_rfl, by norm_num, by decide⟩

theorem exists_orderOf_eq_three_projSU : ∃ g : projSU 4 3 1, orderOf g = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (projSU 4 3 1) :=
    Nat.finite_of_card_ne_zero (by rw [BThreeCensus.card_projSU_four_three]; norm_num)
  refine exists_prime_orderOf_dvd_card' 3 ?_
  rw [BThreeCensus.card_projSU_four_three]
  norm_num

end ThreeLocalSporProof

open ThreeLocalSporProof

section Certs

theorem ks611CentChar3_of (hL : KCentCharThreeL43) (hU : KCentCharThreeU43) : KS611CentChar3 := by
  intro X _ _ hX Y hY h9
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ht₁, -, ho₁, -, -, -, -, -, -, -⟩ :=
    CFSG.Sporadic.Recognition.McLAS.mclP_order_three_classes
      CFSG.Sporadic.Recognition.McLAS.threeFacts_cert
  rcases hX with ⟨K, hKn, hK3, hU4 | hMc⟩ | hG | hMc | hL4 | hU4
  ·
    obtain ⟨e⟩ := hU4
    have hKZ : K ≤ Subgroup.center X := by
      refine le_center_of_normal_card_three hKn hK3
        (@MulEquiv.isSimpleGroup _ _ _ _ isSimpleGroup_projSU_four_three e) ?_
      obtain ⟨g, hg⟩ := exists_orderOf_eq_three_projSU
      exact ⟨e.symm g, by rw [MulEquiv.orderOf_eq, hg]⟩
    exact ks611Conclusion_of_quot hKZ hK3 e hU Y hY h9
  ·
    obtain ⟨e⟩ := hMc
    have hKZ : K ≤ Subgroup.center X := by
      refine le_center_of_normal_card_three hKn hK3
        (@MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.McL.isSimpleGroup_McL e) ?_
      refine ⟨(e.trans CFSG.Sporadic.Schreier.mclPermEquiv).symm ⟨_, ht₁⟩, ?_⟩
      rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
      exact ho₁
    exact ks611Conclusion_of_quot hKZ hK3 (e.trans CFSG.Sporadic.Schreier.mclPermEquiv)
      centCharThree_mclP Y hY h9
  ·
    obtain ⟨K, _, _, _, ⟨e⟩⟩ := exists_mulEquiv_G2 hG
    exact ks611Conclusion_of_mulEquiv e centCharThree_adjointGroup_G2 Y hY h9
  ·
    obtain ⟨e⟩ := hMc
    exact ks611Conclusion_of_mulEquiv (e.trans CFSG.Sporadic.Schreier.mclPermEquiv)
      centCharThree_mclP Y hY h9
  ·
    obtain ⟨e⟩ := hL4
    exact ks611Conclusion_of_mulEquiv e hL Y hY h9
  ·
    obtain ⟨e⟩ := hU4
    exact ks611Conclusion_of_mulEquiv e hU Y hY h9

end Certs

namespace ThreeLocalSporProof

theorem exists_normal_pGroup_of_card_two_three {H : Type*} [Group H] [Finite H] {a b : ℕ}
    (hH : Nat.card H = 2 ^ a * 3 ^ b)
    (hab : a ≤ 1 ∧ 3 ≤ b ∨ a = 2 ∧ 4 ≤ b ∨ a = 3 ∧ 5 ≤ b) :
    ∃ Q : Subgroup H, Q.Normal ∧ IsPGroup 3 Q ∧ 27 ≤ Nat.card Q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 3 H))
  have hfac : (2 ^ a * 3 ^ b).factorization 3 = b := by
    rw [Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_three, Nat.Prime.factorization_pow Nat.prime_two]
    simp
  have hS : Nat.card S = 3 ^ b := by
    rw [Sylow.card_eq_multiplicity, hH, hfac]
  have hidx : (S : Subgroup H).index = 2 ^ a := by
    have h1 := (S : Subgroup H).card_mul_index
    rw [hS, hH, mul_comm (2 ^ a)] at h1
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  have : (S : Subgroup H).FiniteIndex := ⟨by rw [hidx]; positivity⟩
  refine ⟨(S : Subgroup H).normalCore, inferInstance,
    S.isPGroup'.to_le (Subgroup.normalCore_le _), ?_⟩
  have hdvd : (S : Subgroup H).normalCore.index ∣ (2 ^ a).factorial := by
    have h1 := Subgroup.index_normalCore_dvd_factorial_index (S : Subgroup H)
    rwa [hidx] at h1
  have hQS : Nat.card (S : Subgroup H).normalCore ∣ 3 ^ b := by
    rw [← hS]
    exact Subgroup.card_dvd_of_le (Subgroup.normalCore_le _)
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hQS
  have hmul := (S : Subgroup H).normalCore.card_mul_index
  rw [hH, hk'] at hmul
  have hidx' : (S : Subgroup H).normalCore.index = 2 ^ a * 3 ^ (b - k) := by
    have h1 : 3 ^ k * (2 ^ a * 3 ^ (b - k)) = 2 ^ a * 3 ^ b := by
      rw [mul_left_comm, ← pow_add, Nat.add_sub_cancel' hk]
    exact Nat.eq_of_mul_eq_mul_left (by positivity) (hmul.trans h1.symm)
  have h3dvd : 3 ^ (b - k) ∣ (2 ^ a).factorial :=
    (Dvd.intro_left _ hidx'.symm).trans hdvd
  rw [hk']
  rcases hab with ⟨ha, hb⟩ | ⟨rfl, hb⟩ | ⟨rfl, hb⟩
  · have hle : (2 ^ a).factorial ∣ 2 := by
      interval_cases a <;> decide
    have h0 : b - k = 0 := by
      by_contra hne
      have : 3 ∣ 3 ^ (b - k) := dvd_pow_self 3 hne
      have := (this.trans h3dvd).trans hle
      omega
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  · have h1 : b - k ≤ 1 := by
      by_contra hlt
      have : 3 ^ 2 ∣ 3 ^ (b - k) := Nat.pow_dvd_pow 3 (by omega)
      have := this.trans h3dvd
      norm_num [Nat.factorial] at this
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  · have h2 : b - k ≤ 2 := by
      by_contra hlt
      have : 3 ^ 3 ∣ 3 ^ (b - k) := Nat.pow_dvd_pow 3 (by omega)
      have := this.trans h3dvd
      norm_num [Nat.factorial] at this
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem centCharThree_of_classData {X : Type*} [Group X] [Finite X]
    (h3 : ∀ z : X, orderOf z = 3 → ∃ a b : ℕ,
      Nat.card ↥(Subgroup.centralizer ({z} : Set X)) = 2 ^ a * 3 ^ b ∧
        (a ≤ 1 ∧ 3 ≤ b ∨ a = 2 ∧ 4 ≤ b ∨ a = 3 ∧ 5 ≤ b))
    (h2 : ∀ t : X, orderOf t = 2 → ¬ 27 ∣ Nat.card ↥(Subgroup.centralizer ({t} : Set X)))
    (z : X) (hz : orderOf z = 3) :
    IsCharacteristicP 3 ↥(Subgroup.centralizer ({z} : Set X)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, b, hcard, hab⟩ := h3 z hz
  obtain ⟨Q, hQn, hQp, hQ27⟩ := exists_normal_pGroup_of_card_two_three hcard hab
  refine isCharacteristicP_of_normal_pGroup hQn hQp fun x hxp hx3 hcomm => ?_
  have hdvd : orderOf x ∣ 2 ^ a * 3 ^ b * 5 ^ 0 := by
    rw [pow_zero, mul_one, ← hcard]
    exact orderOf_dvd_natCard x
  rcases prime_dvd_two_three_five hxp hdvd with h2' | h3' | h5'
  ·
    have hx2 : orderOf (x : X) = 2 := by rw [Subgroup.orderOf_coe, h2']
    apply h2 x hx2
    have hle : Q.map (Subgroup.centralizer ({z} : Set X)).subtype ≤
        Subgroup.centralizer ({(x : X)} : Set X) := by
      rintro _ ⟨q, hq, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val (hcomm q hq)).symm
    have h1 := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective (Subgroup.centralizer ({z} : Set X)).subtype_injective]
      at h1
    obtain ⟨k, hk⟩ := hQp.exists_card_eq
    have hk3 : 3 ≤ k := by
      by_contra hlt
      have : 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h27 : 27 ∣ Nat.card Q := by
      rw [hk, show (27 : ℕ) = 3 ^ 3 by norm_num]
      exact Nat.pow_dvd_pow 3 hk3
    exact h27.trans h1
  · exact hx3 h3'
  · rw [h5', pow_zero, mul_one] at hdvd
    rcases (Nat.Prime.dvd_mul Nat.prime_five).mp hdvd with h | h
    · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_five Nat.prime_two).mp
        (Nat.prime_five.dvd_of_dvd_pow h)
      omega
    · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_five Nat.prime_three).mp
        (Nat.prime_five.dvd_of_dvd_pow h)
      omega

end ThreeLocalSporProof

@[expose] def KL43ThreeClassData : Prop :=
  (∀ z : projSL 4 (GaloisField 3 1), orderOf z = 3 → ∃ a b : ℕ,
      Nat.card ↥(Subgroup.centralizer ({z} : Set (projSL 4 (GaloisField 3 1)))) = 2 ^ a * 3 ^ b ∧
        (a ≤ 1 ∧ 3 ≤ b ∨ a = 2 ∧ 4 ≤ b ∨ a = 3 ∧ 5 ≤ b)) ∧
    ∀ t : projSL 4 (GaloisField 3 1), orderOf t = 2 →
      ¬ 27 ∣ Nat.card ↥(Subgroup.centralizer ({t} : Set (projSL 4 (GaloisField 3 1))))

@[expose] def KU43ThreeClassData : Prop :=
  (∀ z : projSU 4 3 1, orderOf z = 3 → ∃ a b : ℕ,
      Nat.card ↥(Subgroup.centralizer ({z} : Set (projSU 4 3 1))) = 2 ^ a * 3 ^ b ∧
        (a ≤ 1 ∧ 3 ≤ b ∨ a = 2 ∧ 4 ≤ b ∨ a = 3 ∧ 5 ≤ b)) ∧
    ∀ t : projSU 4 3 1, orderOf t = 2 →
      ¬ 27 ∣ Nat.card ↥(Subgroup.centralizer ({t} : Set (projSU 4 3 1)))

theorem kCentCharThreeL43_of (h : KL43ThreeClassData) : KCentCharThreeL43 := by
  have : Finite (Matrix.ProjGenLinGroup (Fin 4) (GaloisField 3 1)) := by
    unfold Matrix.ProjGenLinGroup
    infer_instance
  exact centCharThree_of_classData h.1 h.2

theorem kCentCharThreeU43_of (h : KU43ThreeClassData) : KCentCharThreeU43 := by
  have : Finite (projSU 4 3 1) :=
    Nat.finite_of_card_ne_zero (by rw [BThreeCensus.card_projSU_four_three]; norm_num)
  exact centCharThree_of_classData h.1 h.2

end CFSG.RankThree.PartTwo.Sec6

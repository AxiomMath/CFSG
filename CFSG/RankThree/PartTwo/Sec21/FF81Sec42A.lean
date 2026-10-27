module

import CFSG.RankThree.PartTwo.Sec21.FF81Sec43T
import CFSG.RankThree.PartTwo.Sec21.FF81HoltHyp4
import CFSG.RankThree.PartTwo.Sec21.FF81J
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79
open scoped Pointwise

section Generic

variable {H : Type} [Group H] [Finite H]

theorem le_opp_of_normalizes {S Q : Subgroup H} (hQS : Q ≤ S)
    (hN : ∀ s ∈ S, ∀ q ∈ Q, s * q * s⁻¹ ∈ Q) (hco : Nat.Coprime 3 (Nat.card Q)) :
    Q ≤ Opp 3 S := by
  intro q hq
  have hnorm : (Q.subgroupOf S).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hN g g.2 n hn⟩
  have hco' : Nat.Coprime 3 (Nat.card (Q.subgroupOf S)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQS).toEquiv]; exact hco
  have hle : Q.subgroupOf S ≤ CFSG.pPrimeCore 3 ↥S := le_sSup ⟨hnorm, hco'⟩
  exact ⟨⟨q, hQS hq⟩, hle (Subgroup.mem_subgroupOf.mpr hq), rfl⟩

theorem opp_le (K : Subgroup H) : Opp 3 K ≤ K := Subgroup.map_subtype_le _

theorem coprime_card_opp (K : Subgroup H) : Nat.Coprime 3 (Nat.card (Opp 3 K)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Opp, CFSG.inSubgroup, Subgroup.card_map_of_injective K.subtype_injective]
  exact CFSG.pPrimeCore_coprime_card

theorem conj_mem_opp_of_mem_nor {K : Subgroup H} {g o : H} (hg : g ∈ Nor K)
    (ho : o ∈ Opp 3 K) : g * o * g⁻¹ ∈ Opp 3 K := by
  have hON := CFSG.pPrimeCore_normal (p := 3) (G := ↥K)
  have hle : conjBy g (Opp 3 K) ≤ Opp 3 K := by
    refine le_opp_of_normalizes ?_ ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hg y).mp (opp_le K hy)
    · intro s hs q hq
      rw [mem_conjBy_iff] at hq ⊢
      have hs' : g⁻¹ * s * g ∈ K := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) s).mp hs
        rwa [inv_inv] at this
      have := inSubgroup_conj_mem hON hs' hq
      rw [show g⁻¹ * (s * q * s⁻¹) * g = (g⁻¹ * s * g) * (g⁻¹ * q * g) * (g⁻¹ * s * g)⁻¹ by
        group]
      exact this
    · rw [card_conjBy]; exact coprime_card_opp K
  exact hle ⟨o, ho, rfl⟩

theorem conjBy_opp (g : H) (K : Subgroup H) : conjBy g (Opp 3 K) = Opp 3 (conjBy g K) := by
  have key : ∀ (g : H) (K : Subgroup H), conjBy g (Opp 3 K) ≤ Opp 3 (conjBy g K) := by
    intro g K
    have hON := CFSG.pPrimeCore_normal (p := 3) (G := ↥K)
    refine le_opp_of_normalizes ?_ ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact ⟨y, opp_le K hy, rfl⟩
    · intro s hs q hq
      rw [mem_conjBy_iff] at hs hq ⊢
      have := inSubgroup_conj_mem hON hs hq
      rw [show g⁻¹ * (s * q * s⁻¹) * g = (g⁻¹ * s * g) * (g⁻¹ * q * g) * (g⁻¹ * s * g)⁻¹ by
        group]
      exact this
    · rw [card_conjBy]; exact coprime_card_opp K
  refine le_antisymm (key g K) ?_
  have h := key g⁻¹ (conjBy g K)
  rw [conjBy_inv_conjBy] at h
  calc Opp 3 (conjBy g K) = conjBy g (conjBy g⁻¹ (Opp 3 (conjBy g K))) :=
        (conjBy_conjBy_inv _ _).symm
    _ ≤ conjBy g (Opp 3 K) := Subgroup.map_mono h

theorem exists_two_subgroup_of_even {A O : Subgroup H} (hA : IsPGroup 3 A)
    (hO : Nat.Coprime 3 (Nat.card O)) (hAO : A ≤ Nor O) (h2 : 2 ∣ Nat.card O) :
    ∃ S : Subgroup H, S ≤ O ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧ A ≤ Nor S := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : ↥A →* MulAut ↥O := O.normalizerMonoidHom.comp (Subgroup.inclusion hAO)
  let _ : MulAction ↥A (Sylow 2 ↥O) := MulAction.compHom (Sylow 2 ↥O) φ
  have hndvd : ¬ 3 ∣ Nat.card (Sylow 2 ↥O) := by
    have h1 : Nat.card (Sylow 2 ↥O) ∣ Nat.card ↥O :=
      (Sylow.card_dvd_index (default : Sylow 2 ↥O)).trans (Subgroup.index_dvd_card _)
    intro h3
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hO (h3.trans h1)
  obtain ⟨P₀, hP₀⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 2 ↥O) hndvd
  have hfix : ∀ (h : ↥A) (x : ↥O), x ∈ (P₀ : Subgroup ↥O) → φ h x ∈ (P₀ : Subgroup ↥O) := by
    intro h x hx
    have e : φ h • P₀ = P₀ := MulAction.mem_fixedPoints.mp hP₀ h
    have hmem : (φ h) • x ∈ (φ h) • (P₀ : Subgroup ↥O) :=
      Subgroup.smul_mem_pointwise_smul x (φ h) _ hx
    rw [← Sylow.pointwise_smul_def, e] at hmem
    exact hmem
  have key : ∀ k ∈ A, ∀ x ∈ (P₀ : Subgroup ↥O).map O.subtype, k * x * k⁻¹ ∈
      (P₀ : Subgroup ↥O).map O.subtype := by
    intro k hk x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨φ ⟨k, hk⟩ y, hfix ⟨k, hk⟩ y hy, ?_⟩
    simp [φ]
  refine ⟨(P₀ : Subgroup ↥O).map O.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · intro h0
    have hne := P₀.ne_bot_of_dvd_card h2
    apply hne
    rw [eq_bot_iff]
    intro y hy
    have : (y : H) ∈ (P₀ : Subgroup ↥O).map O.subtype := ⟨y, hy, rfl⟩
    rw [h0, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  · exact P₀.isPGroup'.of_equiv (Subgroup.equivMapOfInjective _ O.subtype O.subtype_injective)
  · intro k hk
    exact Subgroup.mem_normalizer_fintype fun x hx => key k hk x hx

end Generic

section Central

variable {C : Type} [Group C] [Finite C] (x : C)

theorem zpowers_normal_of_central (hx : ∀ c : C, c * x = x * c) :
    (Subgroup.zpowers x).Normal := ⟨fun n hn g => by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
  have : g * x ^ k = x ^ k * g := (Commute.zpow_right (show Commute g x from hx g) k).eq
  rw [this, mul_inv_cancel_right]
  exact Subgroup.zpow_mem_zpowers x k⟩

variable {x}

theorem orderOf_dvd_three_of_mem_zpowers (hx3 : x ^ 3 = 1) {y : C}
    (hy : y ∈ Subgroup.zpowers x) : orderOf y ∣ 3 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  refine orderOf_dvd_of_pow_eq_one ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]

theorem eq_one_of_mem_zpowers_of_coprime (hx3 : x ^ 3 = 1) {y : C}
    (hy : y ∈ Subgroup.zpowers x) (hco : Nat.Coprime 3 (orderOf y)) : y = 1 :=
  orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm hco)
    (orderOf_dvd_three_of_mem_zpowers hx3 hy))

theorem exists_hall_of_central [(Subgroup.zpowers x).Normal] (hx : ∀ c : C, c * x = x * c)
    (hx3 : x ^ 3 = 1) (Q : Subgroup (C ⧸ Subgroup.zpowers x)) (hQ : Nat.Coprime 3 (Nat.card Q)) :
    ∃ K : Subgroup C, Nat.Coprime 3 (Nat.card K) ∧
      (∀ k ∈ K, (QuotientGroup.mk k : C ⧸ Subgroup.zpowers x) ∈ Q) ∧
      (∀ c : C, (QuotientGroup.mk c : C ⧸ Subgroup.zpowers x) ∈ Q →
        ∃ k ∈ K, ∃ z ∈ Subgroup.zpowers x, c = k * z) ∧
      (∀ c : C, (QuotientGroup.mk c : C ⧸ Subgroup.zpowers x) ∈ Q →
        Nat.Coprime 3 (orderOf c) → c ∈ K) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z := Subgroup.zpowers x
  set π : C →* C ⧸ Z := QuotientGroup.mk' Z
  set P : Subgroup C := Q.comap π
  have hZP : ∀ z ∈ Z, z ∈ P := fun z hz => by
    show (z : C ⧸ Z) ∈ Q
    rw [(QuotientGroup.eq_one_iff z).mpr hz]; exact Q.one_mem
  have h3Z : ∀ y : C, y ∈ P → (∃ k : ℕ, y ^ (3 ^ k) = 1) → y ∈ Z := by
    rintro y hy ⟨k, hk⟩
    have hyQ : (⟨π y, hy⟩ : Q) ^ (3 ^ k) = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      show π y ^ 3 ^ k = 1
      rw [← map_pow, hk, map_one])
    have h1 : orderOf (⟨π y, hy⟩ : Q) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hyQ
    have h2 : orderOf (⟨π y, hy⟩ : Q) ∣ Nat.card Q := orderOf_dvd_natCard _
    have h3 : orderOf (⟨π y, hy⟩ : Q) = 1 :=
      Nat.Coprime.eq_one_of_dvd ((Nat.Coprime.pow_left k hQ).coprime_dvd_left h1) h2
    rw [orderOf_eq_one_iff] at h3
    have : π y = 1 := by simpa using congrArg Subtype.val h3
    exact (QuotientGroup.eq_one_iff y).mp this
  obtain ⟨P₃⟩ : Nonempty (Sylow 3 P) := inferInstance
  have hP₃Z : ∀ p ∈ (P₃ : Subgroup P), (p : C) ∈ Z := by
    intro p hp
    obtain ⟨k, hk⟩ := P₃.isPGroup' ⟨p, hp⟩
    exact h3Z p p.2 ⟨k, by simpa using congrArg (fun z : (P₃ : Subgroup P) => ((z : P) : C)) hk⟩
  have hcentral : ∀ z ∈ Z, ∀ c : C, c * z = z * c := by
    intro z hz c
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (Commute.zpow_right (show Commute c x from hx c) k).eq
  have hPc : Subgroup.normalizer (P₃ : Set P) ≤ Subgroup.centralizer (P₃ : Set P) := by
    intro g _
    refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
    exact Subtype.ext (hcentral _ (hP₃Z h hh) g).symm
  set φ := MonoidHom.transferSylow P₃ hPc
  have hcop : Nat.Coprime 3 (Nat.card φ.ker) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      (MonoidHom.not_dvd_card_ker_transferSylow P₃ hPc)
  have hker : ∀ d : P, d ∈ φ.ker ↔ Nat.Coprime 3 (orderOf d) := by
    intro d
    constructor
    · intro hd
      rw [← Subgroup.orderOf_mk (H := φ.ker) d hd]
      exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_natCard _) hcop
    · intro hd
      have hpd : orderOf (φ d) ∣ orderOf d := orderOf_map_dvd φ d
      obtain ⟨k, hk⟩ := P₃.isPGroup' (φ d)
      have hpk : orderOf (φ d) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
      have hc : Nat.Coprime (orderOf (φ d)) (orderOf d) :=
        (Nat.Coprime.pow_left k hd).coprime_dvd_left hpk
      exact MonoidHom.mem_ker.mpr (orderOf_eq_one_iff.mp (hc.eq_one_of_dvd hpd))
  have hcompl := MonoidHom.ker_transferSylow_isComplement' P₃ hPc
  refine ⟨φ.ker.map P.subtype, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective P.subtype_injective]; exact hcop
  · rintro _ ⟨k, -, rfl⟩
    exact k.2
  · intro c hc
    have hc' : c ∈ P := hc
    obtain ⟨⟨⟨k, hk⟩, ⟨p, hp⟩⟩, hkp, -⟩ := hcompl.existsUnique (⟨c, hc'⟩ : P)
    refine ⟨k, ⟨k, hk, rfl⟩, p, hP₃Z p hp, ?_⟩
    simpa using (congrArg Subtype.val hkp).symm
  · intro c hc hco
    have hc' : c ∈ P := hc
    refine ⟨⟨c, hc'⟩, (hker _).mpr (by rwa [Subgroup.orderOf_mk]), rfl⟩

end Central

end CFSG.RankThree.PartTwo.Sec21.FF81

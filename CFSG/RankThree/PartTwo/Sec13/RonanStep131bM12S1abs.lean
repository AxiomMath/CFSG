module

public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12MovesPlan2
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped Pointwise

theorem s1abs_relIndex_sup {G : Type} [Group G] (N P : Subgroup G)
    (h : N ≤ Subgroup.normalizer (P : Set G)) :
    P.relIndex (N ⊔ P) = P.relIndex N := by
  haveI : (P.subgroupOf (N ⊔ P)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  have key := Subgroup.relIndex_sup_right (H := N.subgroupOf (N ⊔ P))
    (K := P.subgroupOf (N ⊔ P))
  have hsup : N.subgroupOf (N ⊔ P) ⊔ P.subgroupOf (N ⊔ P) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (le_sup_left : N ≤ N ⊔ P) (le_sup_right : P ≤ N ⊔ P),
      Subgroup.subgroupOf_self]
  rw [hsup, Subgroup.relIndex_top_right,
    Subgroup.relIndex_subgroupOf (H := P) (K := N) (L := N ⊔ P) le_sup_left] at key
  exact key

theorem s1abs_isSylowOf {G : Type} [Group G] [Finite G] {B M Q : Subgroup G}
    (hMB : M ≤ B) (hQ : IsMaxThreeSub B Q) (hQM : Q ≤ M) :
    CFSG.ABGLocalTools.IsSylowOf 3 Q M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQ3 : IsPGroup 3 (Q.subgroupOf M) := hQ.1.comap_subtype
  obtain ⟨S, hS⟩ := hQ3.exists_le_sylow
  have hP : CFSG.ABGLocalTools.IsSylowOf 3 ((S : Subgroup M).map M.subtype) M := ⟨S, rfl⟩
  have hQP : Q ≤ (S : Subgroup M).map M.subtype := by
    intro x hx
    have hmem : (⟨x, hQM hx⟩ : M) ∈ Q.subgroupOf M := Subgroup.mem_subgroupOf.mpr hx
    exact Subgroup.mem_map_of_mem M.subtype (hS hmem)
  have hPB : (S : Subgroup M).map M.subtype ≤ B := (Subgroup.map_subtype_le _).trans hMB
  have hPQ : (S : Subgroup M).map M.subtype = Q := hQ.2.2 _ hP.isPGroup hPB hQP
  rw [hPQ] at hP
  exact hP

theorem s1abs_inf_eq_bot {G : Type} [Group G] [Finite G] {Θ P : Subgroup G}
    (hΘ : ¬ 3 ∣ Nat.card Θ) (hP : IsPGroup 3 P) : P ⊓ Θ = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hR : IsPGroup 3 (P ⊓ Θ : Subgroup G) := hP.to_inf_left
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hR
  have hdvd : Nat.card (P ⊓ Θ : Subgroup G) ∣ Nat.card Θ :=
    Subgroup.card_dvd_of_le inf_le_right
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [h0, pow_zero] at hn
    exact (Subgroup.card_eq_one (H := P ⊓ Θ)).1 hn
  · exfalso
    apply hΘ
    rw [hn] at hdvd
    exact (dvd_pow_self 3 hpos.ne').trans hdvd

theorem s1abs_le_normalizer {G : Type} [Group G] {Θ Y K : Subgroup G} (hΘK : Θ ≤ K)
    (hcomm : ∀ k ∈ K, ∀ y ∈ Y, k * y * k⁻¹ * y⁻¹ ∈ Θ) :
    Y ≤ Subgroup.normalizer (K : Set G) := by
  have key : ∀ y ∈ Y, ∀ k ∈ K, y * k * y⁻¹ ∈ K := by
    intro y hy k hk
    have hc : k * y * k⁻¹ * y⁻¹ ∈ K := hΘK (hcomm k hk y hy)
    have e : y * k * y⁻¹ = (k * y * k⁻¹ * y⁻¹)⁻¹ * k := by group
    rw [e]
    exact K.mul_mem (K.inv_mem hc) hk
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact key y hy h hh
  · intro hh
    have h1 := key y⁻¹ (Y.inv_mem hy) (y * h * y⁻¹) hh
    have e2 : y⁻¹ * (y * h * y⁻¹) * y⁻¹⁻¹ = h := by group
    rw [e2] at h1
    exact h1

theorem s1abs_holds : S1abs := by
  intro G _ _ B Y K Θ F Q b hQmax hFQ hQC hQN hYB hKN hNYK hQYK hcomm hΘY hΘK hYKΘ hΘ3 hY27
    _hYex hFe hFmax hbF hFdec hFK
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQ3 : IsPGroup 3 Q := hQmax.1
  have hQB : Q ≤ B := hQmax.2.1
  have hYN : Y ≤ Subgroup.normalizer (K : Set G) := s1abs_le_normalizer hΘK hcomm
  have hQNK : Q ≤ Subgroup.normalizer (K : Set G) := hQN.trans hNYK
  obtain ⟨T, hT⟩ : ∃ T : Subgroup G, T = Y ⊓ (Q ⊔ K) := ⟨_, rfl⟩
  have hTY : T ≤ Y := by rw [hT]; exact inf_le_left
  have hTQK : T ≤ Q ⊔ K := by rw [hT]; exact inf_le_right
  have hTN : T ≤ Subgroup.normalizer (K : Set G) := hTY.trans hYN
  have hQYT : Q ⊓ Y ≤ T := by
    rw [hT]; exact le_inf inf_le_right (inf_le_left.trans le_sup_left)
  have hΘT : Θ ≤ T := by
    rw [hT]; exact le_inf hΘY (hΘK.trans le_sup_right)
  have hKT : K ⊓ T = Θ :=
    le_antisymm ((le_inf (inf_le_right.trans hTY) inf_le_left).trans hYKΘ) (le_inf hΘK hΘT)
  have hTK : T ⊔ K = Q ⊔ K := by
    refine le_antisymm (sup_le hTQK le_sup_right) ?_
    refine sup_le ?_ le_sup_right
    intro q hq
    have hqYK : q ∈ (Y ⊔ K : Subgroup G) := hQYK hq
    have hmul : q ∈ (Y : Set G) * (K : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left Y K hKN]
      exact hqYK
    obtain ⟨y, hy, k, hk, hyk⟩ := Set.mem_mul.mp hmul
    have hyQK : y ∈ Q ⊔ K := by
      have hy' : y = q * k⁻¹ := by rw [← hyk]; group
      rw [hy']
      exact Subgroup.mul_mem _ ((le_sup_left : Q ≤ Q ⊔ K) hq)
        ((le_sup_right : K ≤ Q ⊔ K) (Subgroup.inv_mem _ hk))
    have hyT : y ∈ T := by
      rw [hT]; exact Subgroup.mem_inf.mpr ⟨hy, hyQK⟩
    rw [← hyk]
    exact Subgroup.mul_mem _ ((le_sup_left : T ≤ T ⊔ K) hyT) ((le_sup_right : K ≤ T ⊔ K) hk)
  have hmQ : K.relIndex (Q ⊔ K) = K.relIndex Q := s1abs_relIndex_sup Q K hQNK
  have hmT : K.relIndex (T ⊔ K) = K.relIndex T := s1abs_relIndex_sup T K hTN
  rw [hTK] at hmT
  have hm : K.relIndex Q = K.relIndex T := hmQ.symm.trans hmT
  have hQcard : Nat.card Q = K.relIndex Q * Nat.card (Q ⊓ K : Subgroup G) := by
    rw [inf_comm]
    exact (Subgroup.relIndex_mul_card K Q).symm
  have hTcard : Nat.card T = K.relIndex T * Nat.card Θ := by
    have h := Subgroup.relIndex_mul_card K T
    rw [hKT] at h
    exact h.symm
  have hQYcard : Nat.card T =
      (Q ⊓ Y : Subgroup G).relIndex T * Nat.card (Q ⊓ Y : Subgroup G) := by
    have h := Subgroup.relIndex_mul_card (Q ⊓ Y : Subgroup G) T
    rw [inf_eq_left.mpr hQYT] at h
    exact h.symm
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 3 Q (Q ⊔ Y) :=
    s1abs_isSylowOf (sup_le hQB hYB) hQmax le_sup_left
  have hSylY : CFSG.ABGLocalTools.IsSylowOf 3 (Q ⊓ Y) Y :=
    hSyl.inf_of_le_normalizer le_sup_right (sup_le hQN Subgroup.le_normalizer)
  have hnd : ¬ 3 ∣ (Q ⊓ Y : Subgroup G).relIndex Y :=
    ((CFSG.ABGLocalTools.isSylowOf_iff).1 hSylY).2.2
  have hsdvd : (Q ⊓ Y : Subgroup G).relIndex T ∣ (Q ⊓ Y : Subgroup G).relIndex Y :=
    ⟨T.relIndex Y, (Subgroup.relIndex_mul_relIndex (Q ⊓ Y : Subgroup G) T Y hQYT hTY).symm⟩
  have hs3 : ¬ 3 ∣ (Q ⊓ Y : Subgroup G).relIndex T := fun h => hnd (h.trans hsdvd)
  have hQY3 : IsPGroup 3 (Q ⊓ Y : Subgroup G) := hQ3.to_inf_left
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hQ3
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hQY3
  have hmdvd : K.relIndex Q ∣ 3 ^ n := by
    rw [← hn, hQcard]
    exact dvd_mul_right _ _
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hmdvd
  have heq : K.relIndex Q * Nat.card Θ =
      (Q ⊓ Y : Subgroup G).relIndex T * Nat.card (Q ⊓ Y : Subgroup G) := by
    rw [hm]
    exact hTcard.symm.trans hQYcard
  have heq2 : 3 ^ i * Nat.card Θ = (Q ⊓ Y : Subgroup G).relIndex T * 3 ^ a := by
    rw [← hi, heq, ha]
  have hcopΘ : Nat.Coprime 3 (Nat.card Θ) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hΘ3
  have hcops : Nat.Coprime 3 ((Q ⊓ Y : Subgroup G).relIndex T) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hs3
  have hia : i = a := by
    have h1 : 3 ^ a ∣ 3 ^ i := by
      have h : 3 ^ a ∣ 3 ^ i * Nat.card Θ := by
        rw [heq2]; exact dvd_mul_left _ _
      exact (Nat.Coprime.pow_left a hcopΘ).dvd_of_dvd_mul_right h
    have h2 : 3 ^ i ∣ 3 ^ a := by
      have h : 3 ^ i ∣ (Q ⊓ Y : Subgroup G).relIndex T * 3 ^ a := by
        rw [← heq2]; exact dvd_mul_right _ _
      exact (Nat.Coprime.pow_left i hcops).dvd_of_dvd_mul_left h
    exact le_antisymm ((Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h2)
      ((Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h1)
  have hmQY : K.relIndex Q = Nat.card (Q ⊓ Y : Subgroup G) := by
    rw [hi, ha, hia]
  have hQprod : Nat.card Q = Nat.card (Q ⊓ Y : Subgroup G) * Nat.card (Q ⊓ K : Subgroup G) := by
    rw [hQcard, hmQY]
  obtain ⟨μ, hμ⟩ : ∃ μ : (Q ⊓ Y : Subgroup G) × (Q ⊓ K : Subgroup G) → Q,
      ∀ pk, ((μ pk : Q) : G) = (pk.1 : G) * (pk.2 : G) :=
    ⟨fun pk => ⟨(pk.1 : G) * (pk.2 : G),
      Q.mul_mem (Subgroup.mem_inf.mp pk.1.2).1 (Subgroup.mem_inf.mp pk.2.2).1⟩,
      fun pk => rfl⟩
  have hμinj : Function.Injective μ := by
    rintro ⟨⟨p, hpQY⟩, ⟨k, hkQK⟩⟩ ⟨⟨p', hpQY'⟩, ⟨k', hkQK'⟩⟩ hpk
    have hpk' : p * k = p' * k' := by
      have h := congrArg Subtype.val hpk
      rw [hμ, hμ] at h
      exact h
    have hu : p'⁻¹ * p = k' * k⁻¹ := by
      calc p'⁻¹ * p = p'⁻¹ * (p * k) * k⁻¹ := by group
        _ = p'⁻¹ * (p' * k') * k⁻¹ := by rw [hpk']
        _ = k' * k⁻¹ := by group
    have huQ : p'⁻¹ * p ∈ Q :=
      Q.mul_mem (Q.inv_mem (Subgroup.mem_inf.mp hpQY').1) (Subgroup.mem_inf.mp hpQY).1
    have huK : p'⁻¹ * p ∈ K := by
      rw [hu]
      exact K.mul_mem (Subgroup.mem_inf.mp hkQK').2 (K.inv_mem (Subgroup.mem_inf.mp hkQK).2)
    have huY : p'⁻¹ * p ∈ Y :=
      Y.mul_mem (Y.inv_mem (Subgroup.mem_inf.mp hpQY').2) (Subgroup.mem_inf.mp hpQY).2
    have huΘ : p'⁻¹ * p ∈ Θ := hYKΘ (Subgroup.mem_inf.mpr ⟨huY, huK⟩)
    have huQΘ : p'⁻¹ * p ∈ Q ⊓ Θ := Subgroup.mem_inf.mpr ⟨huQ, huΘ⟩
    rw [s1abs_inf_eq_bot hΘ3 hQ3, Subgroup.mem_bot, inv_mul_eq_one] at huQΘ
    subst huQΘ
    have hkk : k = k' := mul_left_cancel hpk'
    subst hkk
    rfl
  have hcardμ : Nat.card ((Q ⊓ Y : Subgroup G) × (Q ⊓ K : Subgroup G)) = Nat.card Q := by
    rw [Nat.card_prod, hQprod]
  have hμsurj : Function.Surjective μ :=
    ((Nat.bijective_iff_injective_and_card μ).2 ⟨hμinj, hcardμ⟩).2
  have hdecomp : ∀ x ∈ Q, ∃ p ∈ Q ⊓ Y, ∃ k ∈ Q ⊓ K, p * k = x := by
    intro x hx
    obtain ⟨pk, hpk⟩ := hμsurj ⟨x, hx⟩
    refine ⟨(pk.1 : G), pk.1.2, (pk.2 : G), pk.2.2, ?_⟩
    have h := congrArg Subtype.val hpk
    rw [hμ] at h
    exact h
  have hcommQ : ∀ p ∈ Q ⊓ Y, ∀ k ∈ Q ⊓ K, p * k = k * p := by
    intro p hp k hk
    have hkQ : k ∈ Q := (Subgroup.mem_inf.mp hk).1
    have hkK : k ∈ K := (Subgroup.mem_inf.mp hk).2
    have hpQ : p ∈ Q := (Subgroup.mem_inf.mp hp).1
    have hpY : p ∈ Y := (Subgroup.mem_inf.mp hp).2
    have hc : k * p * k⁻¹ * p⁻¹ ∈ Θ := hcomm k hkK p hpY
    have hcQ : k * p * k⁻¹ * p⁻¹ ∈ Q :=
      Q.mul_mem (Q.mul_mem (Q.mul_mem hkQ hpQ) (Q.inv_mem hkQ)) (Q.inv_mem hpQ)
    have h1 : k * p * k⁻¹ * p⁻¹ ∈ Q ⊓ Θ := Subgroup.mem_inf.mpr ⟨hcQ, hc⟩
    rw [s1abs_inf_eq_bot hΘ3 hQ3, Subgroup.mem_bot] at h1
    have h2 : k * p * k⁻¹ = p := mul_inv_eq_one.mp h1
    calc p * k = (k * p * k⁻¹) * k := by rw [h2]
      _ = k * p := by group
  have hkpow : ∀ p ∈ Q ⊓ Y, ∀ k ∈ Q ⊓ K, (p * k) ^ 3 = k ^ 3 := by
    intro p hp k hk
    have hp3 : p ^ 3 = 1 := (hY27 (Q ⊓ Y) inf_le_right hQY3).2 p hp
    have hcomm' : Commute p k := hcommQ p hp k hk
    rw [hcomm'.mul_pow, hp3, one_mul]
  have hkF : ∀ k ∈ Q ⊓ K, k ^ 3 = 1 → k ∈ Subgroup.zpowers b := by
    intro k hk hk3
    have hkQ : k ∈ Q := (Subgroup.mem_inf.mp hk).1
    have hkK : k ∈ K := (Subgroup.mem_inf.mp hk).2
    have hbk : b * k = k * b := (Subgroup.mem_centralizer_singleton_iff.mp (hQC hkQ)).symm
    have hCF : F ≤ Subgroup.centralizer ({k} : Set G) := by
      calc F = Subgroup.zpowers b ⊔ (F ⊓ Y) := hFdec
        _ ≤ Subgroup.centralizer ({k} : Set G) := by
          refine sup_le ?_ ?_
          · rw [Subgroup.zpowers_le]
            exact Subgroup.mem_centralizer_singleton_iff.mpr hbk
          · intro a ha
            have haQ : a ∈ Q := hFQ (Subgroup.mem_inf.mp ha).1
            have hac : a * k = k * a :=
              hcommQ a (Subgroup.mem_inf.mpr ⟨haQ, (Subgroup.mem_inf.mp ha).2⟩) k hk
            exact Subgroup.mem_centralizer_singleton_iff.mpr hac
    have hcentr : ∀ a ∈ F, a * k = k * a := fun a ha =>
      Subgroup.mem_centralizer_singleton_iff.mp (hCF ha)
    have hkF' : k ∈ F := by
      by_contra hkF0
      obtain ⟨hE, -⟩ :=
        CFSG.RankThree.PartTwo.Sec5.isElemAbelian_sup_zpowers hFe hkF0 hk3 hcentr
      have hEq : F ⊔ Subgroup.zpowers k = F := hFmax _ hE le_sup_left
      have hk_mem : k ∈ F ⊔ Subgroup.zpowers k :=
        (le_sup_right : Subgroup.zpowers k ≤ F ⊔ Subgroup.zpowers k) (Subgroup.mem_zpowers k)
      rw [hEq] at hk_mem
      exact hkF0 hk_mem
    exact hFK (Subgroup.mem_inf.mpr ⟨hkF', hkK⟩)
  have hexists : ∀ x : {x : G // x ∈ Q ∧ x ^ 3 = 1},
      ∃ pk : (Q ⊓ Y : Subgroup G) × (Subgroup.zpowers b),
        (pk.1 : G) * (pk.2 : G) = (x : G) := by
    rintro ⟨x, hxQ, hx3⟩
    obtain ⟨p, hp, k, hk, hpk⟩ := hdecomp x hxQ
    have hk3 : k ^ 3 = 1 := by
      have h := hkpow p hp k hk
      rw [hpk, hx3] at h
      exact h.symm
    exact ⟨⟨⟨p, hp⟩, ⟨k, hkF k hk hk3⟩⟩, hpk⟩
  choose g hg using hexists
  have hginj : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    rw [← hg x, ← hg y, hxy]
  have hb3 : b ^ 3 = 1 := hFe.2 b hbF
  have hzb : Nat.card (Subgroup.zpowers b) ≤ 3 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hb3)
  have hQY27 : Nat.card (Q ⊓ Y : Subgroup G) ≤ 27 := (hY27 (Q ⊓ Y) inf_le_right hQY3).1
  have hcardle : Nat.card {x : G // x ∈ Q ∧ x ^ 3 = 1} ≤
      Nat.card ((Q ⊓ Y : Subgroup G) × (Subgroup.zpowers b)) :=
    Nat.card_le_card_of_injective g hginj
  rw [Nat.card_prod] at hcardle
  calc Nat.card {x : G // x ∈ Q ∧ x ^ 3 = 1}
      ≤ Nat.card (Q ⊓ Y : Subgroup G) * Nat.card (Subgroup.zpowers b) := hcardle
    _ ≤ 27 * 3 := Nat.mul_le_mul hQY27 hzb
    _ = 81 := by norm_num

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b

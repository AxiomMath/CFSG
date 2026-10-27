module

public import CFSG.Walter.W67.Section5.Torus
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorNontrivial
public import CFSG.Dihedral.DisconnectedInvolutionGraph.CoprimeSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorOrbit
public import CFSG.Walter.W67.Section5.Real3

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups
open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G]

namespace Sec53

theorem exists_index_two {X : Subgroup G} {t : G} (htX : t ∈ X) (ht : orderOf t = 2)
    (hX : ∀ W : Subgroup G, W ≤ X → IsPGroup 2 W → Nat.card W ≤ 2) :
    ∃ O : Subgroup G, O ≤ X ∧ Odd (Nat.card O) ∧ Nat.card X = 2 * Nat.card O ∧
      (∀ x ∈ X, Odd (orderOf x) → x ∈ O) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 X) := inferInstance
  have h2X : 2 ∣ Nat.card X := by
    have h1 := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr htX)
    rwa [Nat.card_zpowers, ht] at h1
  have hP2 : Nat.card P = 2 := by
    apply le_antisymm
    · have hle := hX ((P : Subgroup X).map X.subtype) (Subgroup.map_subtype_le _)
        (P.isPGroup'.map _)
      rwa [Subgroup.card_map_of_injective X.subtype_injective] at hle
    · exact Nat.le_of_dvd Nat.card_pos (P.dvd_card_of_dvd_card h2X)
  have hP : Subgroup.normalizer (P : Set X) ≤ Subgroup.centralizer (P : Set X) := by
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyn : n * y * n⁻¹ ∈ (P : Subgroup X) := (Subgroup.mem_normalizer_iff.mp hn y).mp hy
    by_cases hy1 : y = 1
    · rw [hy1, mul_one, one_mul]
    · have hoy : orderOf y = 2 := by
        have hdvd : orderOf y ∣ 2 := by
          rw [← hP2]
          exact Subgroup.orderOf_dvd_natCard _ hy
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) hy1
        · exact h
      have hzp : Subgroup.zpowers y = (P : Subgroup X) := by
        apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hy)
        rw [hP2, Nat.card_zpowers, hoy]
      have hyn' : n * y * n⁻¹ ∈ Subgroup.zpowers y := by rw [hzp]; exact hyn
      rcases eq_one_or_eq_of_mem_zpowers hoy hyn' with h | h
      · exfalso
        apply hy1
        have := congrArg (fun w => n⁻¹ * w * n) h
        simpa [mul_assoc] using this
      · calc y * n = n * y * n⁻¹ * n := by rw [h]
          _ = n * y := by group
  set O' := (MonoidHom.transferSylow P hP).ker
  have hcomp := MonoidHom.ker_transferSylow_isComplement' P hP
  have hO'odd : ¬ 2 ∣ Nat.card O' := MonoidHom.not_dvd_card_ker_transferSylow P hP
  have hcard : Nat.card O' * 2 = Nat.card X := by
    rw [← hP2]
    exact hcomp.card_mul_card
  refine ⟨O'.map X.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective X.subtype_injective]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hO'odd)
  · rw [Subgroup.card_map_of_injective X.subtype_injective, ← hcard, mul_comm]
  · intro x hx hodd
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    have hQ : Nat.card (X ⧸ O') = 2 := by
      have := Subgroup.card_eq_card_quotient_mul_card_subgroup O'
      have hpos : 0 < Nat.card O' := Nat.card_pos
      rw [← hcard] at this
      exact (Nat.eq_of_mul_eq_mul_right hpos (by rw [← this]; ring))
    set z : X ⧸ O' := ((⟨x, hx⟩ : X) : X ⧸ O')
    have hz2 : z ^ 2 = 1 := by
      have := pow_card_eq_one' (x := z)
      rwa [hQ] at this
    obtain ⟨k, hk⟩ := hodd
    have hzo : z ^ (2 * k + 1) = 1 := by
      rw [← hk, ← QuotientGroup.mk_pow]
      have : (⟨x, hx⟩ : X) ^ orderOf x = 1 := Subtype.ext (by simp [pow_orderOf_eq_one])
      rw [this, QuotientGroup.mk_one]
    rw [pow_succ, pow_mul, hz2, one_pow, one_mul] at hzo
    exact (QuotientGroup.eq_one_iff _).mp hzo

theorem commutator_mem_of_index_two {C O N : Subgroup G} (hOC : O ≤ C) (hCN : C ≤ N)
    (hidx : Nat.card C = 2 * Nat.card O)
    (hNC : ∀ n ∈ N, ∀ c ∈ C, n * c * n⁻¹ ∈ C) (hNO : ∀ n ∈ N, ∀ o ∈ O, n * o * n⁻¹ ∈ O)
    (hcomm : ∀ n ∈ N, ∀ m ∈ N, n * m * n⁻¹ * m⁻¹ ∈ C)
    {n x : G} (hn : n ∈ N) (hx : x ∈ N) (hodd : Odd (orderOf x)) :
    n * x * n⁻¹ * x⁻¹ ∈ O := by
  set O' := O.subgroupOf C
  have hO'n : O'.Normal := by
    constructor
    intro a ha c
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    exact hNO c (hCN c.2) a ha
  have hO'card : Nat.card O' = Nat.card O :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOC).toEquiv
  have hQ : Nat.card (C ⧸ O') = 2 := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup O'
    rw [hO'card, hidx] at this
    have hpos : 0 < Nat.card O := Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_right hpos this.symm)
  let χ : C → C ⧸ O' := fun c => (c : C ⧸ O')
  have hχ1 : ∀ c : C, χ c = 1 ↔ (c : G) ∈ O := fun c => by
    simp only [χ, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf
  have hsq : ∀ q : C ⧸ O', q * q = 1 := fun q => by
    have := pow_card_eq_one' (x := q)
    rwa [hQ, pow_two] at this
  have htwo : ∀ a b : C ⧸ O', a ≠ 1 → b ≠ 1 → a = b := by
    intro a b ha hb
    by_contra hab
    have h3 : Nat.card ({1, a, b} : Set (C ⧸ O')) = 3 := by
      rw [Nat.card_coe_set_eq, Set.ncard_insert_of_notMem, Set.ncard_pair hab]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun h => ha h.symm, fun h => hb h.symm⟩
    have hle := Nat.card_mono (Set.toFinite (Set.univ : Set (C ⧸ O')))
      (Set.subset_univ ({1, a, b} : Set (C ⧸ O')))
    rw [h3, Nat.card_univ, hQ] at hle
    omega
  have hconj : ∀ y (hy : y ∈ N) (c : C), χ ⟨y * c * y⁻¹, hNC y hy c c.2⟩ = χ c := by
    intro y hy c
    by_cases hc : (c : G) ∈ O
    · rw [(hχ1 c).mpr hc, hχ1]
      exact hNO y hy c hc
    · have h1 : χ c ≠ 1 := fun h => hc ((hχ1 c).mp h)
      have h2 : χ ⟨y * c * y⁻¹, hNC y hy c c.2⟩ ≠ 1 := by
        intro h
        apply hc
        have := hNO y⁻¹ (N.inv_mem hy) _ ((hχ1 _).mp h)
        simpa [mul_assoc] using this
      exact htwo _ _ h2 h1
  set c := n * x * n⁻¹ * x⁻¹
  have hcC : c ∈ C := hcomm n hn x hx
  have key : ∀ k : ℕ, ∃ p : C, (c * x) ^ k = (p : G) * x ^ k ∧ χ p = χ ⟨c, hcC⟩ ^ k := by
    intro k
    induction k with
    | zero => exact ⟨1, by simp, by simp [χ]⟩
    | succ k ih =>
      obtain ⟨p, hp, hχp⟩ := ih
      have hxk : x ^ k ∈ N := N.pow_mem hx k
      refine ⟨p * ⟨x ^ k * c * (x ^ k)⁻¹, hNC _ hxk c hcC⟩, ?_, ?_⟩
      · rw [pow_succ, hp]
        simp only [Subgroup.coe_mul]
        group
      · have := hconj (x ^ k) hxk ⟨c, hcC⟩
        simp only [χ, QuotientGroup.mk_mul] at this ⊢
        rw [this, pow_succ, ← hχp]
  obtain ⟨p, hp, hχp⟩ := key (orderOf x)
  have hcx : c * x = n * x * n⁻¹ := by simp [c]
  have hp1 : (p : G) = 1 := by
    rw [pow_orderOf_eq_one, mul_one, hcx, conj_pow, pow_orderOf_eq_one] at hp
    simpa using hp.symm
  have hχp1 : χ p = 1 := (hχ1 p).mpr (by rw [hp1]; exact one_mem _)
  obtain ⟨k, hk⟩ := hodd
  rw [hχp1, hk, pow_succ, pow_mul, pow_two, hsq, one_pow, one_mul] at hχp
  exact (hχ1 _).mp hχp.symm

theorem mem_normalizer_of_conj_le {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

omit [Finite G] in
theorem exists_zpow_of_mem_normalizer {b n : G}
    (hn : n ∈ Subgroup.normalizer (Subgroup.zpowers b : Set G)) :
    ∃ k : ℤ, ∀ y ∈ Subgroup.zpowers b, n * y * n⁻¹ = y ^ k := by
  have hb : n * b * n⁻¹ ∈ Subgroup.zpowers b :=
    (Subgroup.mem_normalizer_iff.mp hn b).mp (Subgroup.mem_zpowers b)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
  refine ⟨k, fun y hy => ?_⟩
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← conj_zpow, ← hk, ← zpow_mul, ← zpow_mul, mul_comm]

omit [Finite G] in
theorem commutator_mem_centralizer {b n m : G}
    (hn : n ∈ Subgroup.normalizer (Subgroup.zpowers b : Set G))
    (hm : m ∈ Subgroup.normalizer (Subgroup.zpowers b : Set G)) :
    n * m * n⁻¹ * m⁻¹ ∈ Subgroup.centralizer ({b} : Set G) := by
  obtain ⟨k₁, hk₁⟩ := exists_zpow_of_mem_normalizer (Subgroup.inv_mem _ hn)
  obtain ⟨k₂, hk₂⟩ := exists_zpow_of_mem_normalizer (Subgroup.inv_mem _ hm)
  have hb : ∀ i : ℤ, b ^ i ∈ Subgroup.zpowers b := fun i => Subgroup.zpow_mem _
    (Subgroup.mem_zpowers b) i
  rw [Subgroup.mem_centralizer_singleton_iff]
  have e1 : (m⁻¹ * n⁻¹) * b * (m⁻¹ * n⁻¹)⁻¹ = (b ^ k₁) ^ k₂ := by
    rw [show (m⁻¹ * n⁻¹) * b * (m⁻¹ * n⁻¹)⁻¹ = m⁻¹ * (n⁻¹ * b * n⁻¹⁻¹) * m⁻¹⁻¹ by group,
      hk₁ b (Subgroup.mem_zpowers b), hk₂ _ (hb k₁)]
  have e2 : (n⁻¹ * m⁻¹) * b * (n⁻¹ * m⁻¹)⁻¹ = (b ^ k₂) ^ k₁ := by
    rw [show (n⁻¹ * m⁻¹) * b * (n⁻¹ * m⁻¹)⁻¹ = n⁻¹ * (m⁻¹ * b * m⁻¹⁻¹) * n⁻¹⁻¹ by group,
      hk₂ b (Subgroup.mem_zpowers b), hk₁ _ (hb k₂)]
  have e3 : (m⁻¹ * n⁻¹) * b * (m⁻¹ * n⁻¹)⁻¹ = (n⁻¹ * m⁻¹) * b * (n⁻¹ * m⁻¹)⁻¹ := by
    rw [e1, e2, ← zpow_mul, ← zpow_mul, mul_comm]
  calc n * m * n⁻¹ * m⁻¹ * b
      = (m⁻¹ * n⁻¹)⁻¹ * ((n⁻¹ * m⁻¹) * b * (n⁻¹ * m⁻¹)⁻¹) * (n⁻¹ * m⁻¹) := by group
    _ = (m⁻¹ * n⁻¹)⁻¹ * ((m⁻¹ * n⁻¹) * b * (m⁻¹ * n⁻¹)⁻¹) * (n⁻¹ * m⁻¹) := by rw [← e3]
    _ = b * (n * m * n⁻¹ * m⁻¹) := by group

end Sec53

namespace Frame

variable {h : Hyp G} (fr : Frame h)

include fr in
theorem mul_self_of_isPGroup {x : G} (hx : IsPGroup 2 (Subgroup.zpowers x)) : x * x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S', hS'⟩ := hx.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G fr.S S'
  have hxS : x ∈ (S' : Subgroup G) := hS' (Subgroup.mem_zpowers x)
  rw [← hg, Sylow.coe_subgroup_smul] at hxS
  obtain ⟨y, hy, rfl⟩ := hxS
  have h1 := fr.mul_self_of_mem_S hy
  change g * y * g⁻¹ * (g * y * g⁻¹) = 1
  rw [show g * y * g⁻¹ * (g * y * g⁻¹) = g * (y * y) * g⁻¹ by group, h1]
  group

end Frame

namespace Std

variable (s : Std G)

theorem card_K_inf_centralizer (h4 : s.q % 4 = 3) {t : G} (ht : t ∈ s.K) (h2 : orderOf t = 2) :
    Nat.card (s.K ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) = s.q + 1 := by
  set F := GaloisField s.p s.f
  set ι := psl2Emb s.iso
  have hι : Function.Injective ι := PSL2Sub.emb_injective s.iso
  obtain ⟨t', rfl⟩ := PSL2Sub.exists_emb_eq s.iso ht
  have ht' : orderOf t' = 2 := by
    rw [← orderOf_injective ι hι t']
    exact h2
  have hset : s.K ⊓ Subgroup.centralizer ({ι t'} : Set G) =
      (Subgroup.centralizer ({t'} : Set PSL(2, F))).map ι := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxK, hxc⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨y, rfl⟩ := PSL2Sub.exists_emb_eq s.iso hxK
      refine Subgroup.mem_map.mpr ⟨y, ?_, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hxc ⊢
      apply hι
      rw [map_mul, map_mul]
      exact hxc
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      refine Subgroup.mem_inf.mpr ⟨PSL2Sub.emb_mem s.iso y, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
      rw [← map_mul, ← map_mul, hy]
  have hF : Nat.card F = s.p ^ s.f := GaloisField.card s.p s.f s.f_pos.ne'
  rw [hset, Subgroup.card_map_of_injective hι]
  exact ((psl2_centralizer_involution F hF s.odd_p s.f_pos ht').2 h4).1

end Std

open CFSG.ProperTwoGeneratedCore CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator in
theorem lemma_5_3_of
    (h22 : S_lemma_2_2) :
    ∀ (G : Type) [Group G] [Finite G] (s : Std G), s.p = 3 → ∀ (f5 : Frame5 s) {b : G}, b ∈ f5.B →
      b ≠ 1 →
      (Nat.card (Subgroup.normalizer (Subgroup.zpowers b : Set G))).factorization 3 ≤
        (Nat.card s.fr.E).factorization 3 := by
  intro G _ _ s hp f5 b hb hb1
  have h4 := s.q_mod_four hp
  set N := Subgroup.normalizer (Subgroup.zpowers b : Set G) with hNdef
  set Cb := Subgroup.centralizer ({b} : Set G) with hCbdef
  have hbK : b ∈ s.K := f5.B_le hb
  have hob : orderOf b ∣ Nat.card f5.B := Subgroup.orderOf_dvd_natCard _ hb
  have hBodd : Odd (Nat.card f5.B) := by
    have h := f5.card_B
    rw [Nat.odd_iff]
    omega
  have hnoinv : ∀ m ∈ s.K, m * m = 1 → m * b = b * m → m = 1 := by
    intro m hmK hmm hmb
    by_contra hm1
    have hom : orderOf m = 2 := by
      have hdvd : orderOf m ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, hmm])
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hm1
      · exact h
    have hcard := s.card_K_inf_centralizer h4 hmK hom
    have hbC : b ∈ s.K ⊓ Subgroup.centralizer ({m} : Set G) :=
      ⟨hbK, Subgroup.mem_centralizer_singleton_iff.mpr hmb.symm⟩
    have hob2 : orderOf b ∣ s.q + 1 := by
      rw [← hcard]
      exact Subgroup.orderOf_dvd_natCard _ hbC
    have hdvd2 : orderOf b ∣ Nat.card f5.B := hob
    have hB := f5.card_B
    have h1 : orderOf b ∣ 2 := by
      have hq1 : orderOf b ∣ s.q - 1 := by
        rw [← hB]
        exact Dvd.dvd.mul_left hdvd2 2
      have := Nat.dvd_sub hob2 hq1
      rwa [show s.q + 1 - (s.q - 1) = 2 by omega] at this
    have hodd : Odd (orderOf b) := Odd.of_dvd_nat hBodd hdvd2
    have : orderOf b = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
      · exact h
      · rw [h] at hodd
        exact absurd hodd (by decide)
    exact hb1 (orderOf_eq_one_iff.mp this)
  have hJ2 : ∀ w ∈ Cb, w ∈ s.H → w * w = 1 → w ∈ Subgroup.zpowers s.J := by
    intro w hwC hwH hww
    obtain ⟨j, hj, m, hm, rfl⟩ := s.fr.exists_decomp_H_JM hwH
    have hjc : ∀ y ∈ s.K ⊔ s.fr.E, j * y = y * j := fun y hy => s.fr.commute_of_mem_KE hj hy
    have hjj : j * j = 1 := by
      rcases eq_one_or_eq_of_mem_zpowers s.orderOf_J hj with rfl | rfl
      · exact mul_one 1
      · exact s.J_mul_J
    have hmm : m * m = 1 := by
      calc m * m = (j * j)⁻¹ * (j * (j * m) * m) := by group
        _ = (j * j)⁻¹ * (j * (m * j) * m) := by rw [hjc m hm]
        _ = (j * j)⁻¹ * ((j * m) * (j * m)) := by group
        _ = 1 := by rw [hww, hjj]; group
    have hmK := s.fr.mem_K_of_mem_KE_of_mul_self hm hmm
    have hmb : m * b = b * m := by
      have hwb : j * m * b = b * (j * m) := Subgroup.mem_centralizer_singleton_iff.mp hwC
      have hjb : j * b = b * j := hjc b (Subgroup.mem_sup_left hbK)
      calc m * b = j⁻¹ * (j * m * b) := by group
        _ = j⁻¹ * (b * (j * m)) := by rw [hwb]
        _ = j⁻¹ * ((b * j) * m) := by group
        _ = j⁻¹ * ((j * b) * m) := by rw [hjb]
        _ = b * m := by group
    rw [hnoinv m hmK hmm hmb, mul_one]
    exact hj
  have hJCb : s.J ∈ Cb :=
    Subgroup.mem_centralizer_singleton_iff.mpr (s.commute_J (s.K_le_H hbK)).symm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsub2 : ∀ W : Subgroup G, W ≤ Cb → s.J ∈ W → IsPGroup 2 W →
      W ≤ Subgroup.zpowers s.J := by
    intro W hWC hJW hW w hw
    have hWab := s.toHyp.isMulCommutative_of_isPGroup hW
    have hwH : w ∈ s.H := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := congrArg Subtype.val (hWab.is_comm.comm ⟨w, hw⟩ ⟨s.J, hJW⟩)
      exact this
    have hww : w * w = 1 := s.fr.mul_self_of_isPGroup
      (hW.to_le (Subgroup.zpowers_le.mpr hw))
    exact hJ2 w (hWC hw) hwH hww
  have h2sub : ∀ W : Subgroup G, W ≤ Cb → IsPGroup 2 W → Nat.card W ≤ 2 := by
    intro W hWC hW
    set J' : Cb := ⟨s.J, hJCb⟩
    have hJ'p : IsPGroup 2 (Subgroup.zpowers J') := by
      apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers, Subgroup.orderOf_mk, s.orderOf_J, pow_one]
    obtain ⟨S₂, hS₂⟩ := hJ'p.exists_le_sylow
    have hS₂card : Nat.card S₂ ≤ 2 := by
      have hle := hsub2 ((S₂ : Subgroup Cb).map Cb.subtype) (Subgroup.map_subtype_le _)
        ⟨J', hS₂ (Subgroup.mem_zpowers J'), rfl⟩ (S₂.isPGroup'.map _)
      have := Subgroup.card_le_of_le hle
      rwa [Subgroup.card_map_of_injective Cb.subtype_injective, Nat.card_zpowers,
        s.orderOf_J] at this
    have hW' : IsPGroup 2 (W.subgroupOf Cb) :=
      hW.comap_of_injective Cb.subtype Cb.subtype_injective
    obtain ⟨S₁, hS₁⟩ := hW'.exists_le_sylow
    have h1 : Nat.card S₁ = Nat.card S₂ := by
      rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
    calc Nat.card W = Nat.card (W.subgroupOf Cb) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWC).toEquiv).symm
      _ ≤ Nat.card S₁ := Subgroup.card_le_of_le hS₁
      _ = Nat.card S₂ := h1
      _ ≤ 2 := hS₂card
  obtain ⟨O, hOC, hOodd, hOidx, hOmem⟩ := Sec53.exists_index_two hJCb s.orderOf_J h2sub
  have hCbN : Cb ≤ N := by
    intro c hc
    apply Sec53.mem_normalizer_of_conj_le
    intro y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← conj_zpow, show c * b * c⁻¹ = b by
      rw [(Subgroup.mem_centralizer_singleton_iff.mp hc), mul_inv_cancel_right]]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) i
  have hNCb : ∀ n ∈ N, ∀ c ∈ Cb, n * c * n⁻¹ ∈ Cb := by
    intro n hn c hc
    obtain ⟨k, hk⟩ := Sec53.exists_zpow_of_mem_normalizer (Subgroup.inv_mem _ hn)
    have hbk := hk b (Subgroup.mem_zpowers b)
    rw [inv_inv] at hbk
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcb : c * b ^ k = b ^ k * c :=
      (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp hc) k).eq
    calc n * c * n⁻¹ * b = n * c * (n⁻¹ * b * n) * n⁻¹ := by group
      _ = n * (c * b ^ k) * n⁻¹ := by rw [hbk]; group
      _ = n * (b ^ k * c) * n⁻¹ := by rw [hcb]
      _ = (n * b ^ k * n⁻¹) * (n * c * n⁻¹) := by group
      _ = b * (n * c * n⁻¹) := by rw [← hbk]; group
  have hNO : ∀ n ∈ N, ∀ o ∈ O, n * o * n⁻¹ ∈ O := by
    intro n hn o ho
    refine hOmem _ (hNCb n hn o (hOC ho)) ?_
    rw [orderOf_conj_mul]
    exact Odd.of_dvd_nat hOodd (Subgroup.orderOf_dvd_natCard O ho)
  have hcommO : ∀ n ∈ N, ∀ x ∈ N, Odd (orderOf x) → n * x * n⁻¹ * x⁻¹ ∈ O :=
    fun n hn x hx hodd => Sec53.commutator_mem_of_index_two hOC hCbN hOidx hNCb hNO
      (fun n hn m hm => Sec53.commutator_mem_centralizer hn hm) hn hx hodd
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 N) := inferInstance
  set PG := (P : Subgroup N).map N.subtype with hPGdef
  have hPGN : PG ≤ N := Subgroup.map_subtype_le _
  have hPG3 : IsPGroup 3 PG := P.isPGroup'.map _
  have hPGcard : Nat.card PG = 3 ^ (Nat.card N).factorization 3 := by
    rw [Subgroup.card_map_of_injective N.subtype_injective, Sylow.card_eq_multiplicity]
  set M := O ⊔ PG with hMdef
  have hPGnO : PG ≤ Subgroup.normalizer (O : Set G) := fun x hx =>
    Sec53.mem_normalizer_of_conj_le fun o ho => hNO x (hPGN hx) o ho
  have hMN : ∀ n ∈ N, n ∈ Subgroup.normalizer (M : Set G) := by
    intro n hn
    apply Sec53.mem_normalizer_of_conj_le
    intro y hy
    obtain ⟨o, ho, p, hp, rfl⟩ := (mem_sup_iff_of_le_normalizer hPGnO).mp hy
    have hpodd : Odd (orderOf p) := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hPG3) ⟨p, hp⟩
      rw [Subgroup.orderOf_mk] at hk
      rw [hk]
      exact Odd.pow (by decide)
    have h1 := hcommO n hn p (hPGN hp) hpodd
    have e : n * (o * p) * n⁻¹ = (n * o * n⁻¹) * (n * p * n⁻¹ * p⁻¹) * p := by group
    rw [e]
    exact M.mul_mem (M.mul_mem (Subgroup.mem_sup_left (hNO n hn o ho))
      (Subgroup.mem_sup_left h1)) (Subgroup.mem_sup_right hp)
  have hMle : M ≤ N := sup_le (hOC.trans hCbN) hPGN
  have hModd : ¬ 2 ∣ Nat.card M := by
    have hON : (O.subgroupOf M).Normal := by
      constructor
      intro a ha m
      rw [Subgroup.mem_subgroupOf] at ha ⊢
      exact hNO m (hMle m.2) a ha
    let π : PG.subgroupOf M →* M ⧸ O.subgroupOf M :=
      (QuotientGroup.mk' (O.subgroupOf M)).comp (PG.subgroupOf M).subtype
    have hπ : Function.Surjective π := by
      intro q
      obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨o, ho, p, hp, rfl⟩ := (mem_sup_iff_of_le_normalizer hPGnO).mp hy
      refine ⟨⟨⟨p, Subgroup.mem_sup_right hp⟩, hp⟩, ?_⟩
      change ((⟨p, _⟩ : M) : M ⧸ O.subgroupOf M) = ((⟨o * p, hy⟩ : M) : M ⧸ O.subgroupOf M)
      rw [QuotientGroup.eq]
      change (p⁻¹ * (o * p)) ∈ O
      rw [show p⁻¹ * (o * p) = p⁻¹ * o * p⁻¹⁻¹ by group]
      exact hNO p⁻¹ (N.inv_mem (hPGN hp)) o ho
    have hdvd1 : Nat.card (M ⧸ O.subgroupOf M) ∣ Nat.card PG := by
      have := Subgroup.card_dvd_of_surjective hπ
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv] at this
    have hOM : Nat.card (O.subgroupOf M) = Nat.card O :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
    have hL := Subgroup.card_eq_card_quotient_mul_card_subgroup (O.subgroupOf M)
    rw [hOM] at hL
    rw [hL]
    intro h2
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h
    · rw [hPGcard] at hdvd1
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_two (h.trans hdvd1)) (by decide)
    · exact (Nat.not_even_iff_odd.mpr hOodd) (even_iff_two_dvd.mpr h)
  obtain ⟨T₁, hT₁K, hT₁T₁, hT₁1, hT₁inv⟩ := f5.exists_inverting_involution
  have hoT₁ : orderOf T₁ = 2 := by
    have hdvd : orderOf T₁ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, hT₁T₁])
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hT₁1
    · exact h
  have hT₁N : T₁ ∈ N := by
    apply Sec53.mem_normalizer_of_conj_le
    intro y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← conj_zpow, hT₁inv b hb, inv_zpow']
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) _
  have hJN : s.J ∈ N := hCbN hJCb
  have hJT : Commute s.J T₁ := (s.commute_J (s.K_le_H hT₁K)).symm
  have hJneT : T₁ ≠ s.J := fun h => s.J_not_mem_K (h ▸ hT₁K)
  obtain ⟨-, hVcard, -⟩ := commuting_distinct_involutions_four_group s.orderOf_J hoT₁ hJT hJneT
  set V := Subgroup.zpowers s.J ⊔ Subgroup.zpowers T₁ with hVdef
  have hVN : V ≤ N := sup_le (Subgroup.zpowers_le.mpr hJN) (Subgroup.zpowers_le.mpr hT₁N)
  have hVM : V ≤ Subgroup.normalizer (M : Set G) := fun v hv => hMN v (hVN hv)
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hVcard]; norm_num)
  let := JT.conjAct V M hVM
  obtain ⟨Q, hQinv⟩ := DisconnectedInvolutionGraph.Helpers.coprime_pgroup_exists_invariant_sylow
    (A := V) 2 3 hV2 hModd
  set QG := (Q : Subgroup M).map M.subtype with hQGdef
  have hQGcard : Nat.card QG = 3 ^ (Nat.card M).factorization 3 := by
    rw [Subgroup.card_map_of_injective M.subtype_injective, Sylow.card_eq_multiplicity]
  have hQGodd : Odd (Nat.card QG) := by
    rw [hQGcard]
    exact Odd.pow (by decide)
  have hQG3 : ∀ y ∈ QG, y ^ (3 ^ (Nat.card M).factorization 3) = 1 := by
    intro y hy
    rw [← hQGcard]
    have := pow_card_eq_one' (x := (⟨y, hy⟩ : QG))
    exact congrArg Subtype.val this
  have hQGN : ∀ v ∈ V, v ∈ Subgroup.normalizer (QG : Set G) := by
    intro v hv
    apply Sec53.mem_normalizer_of_conj_le
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨_, hQinv ⟨v, hv⟩ y hy, rfl⟩
  have hcent : ∀ u t : G, orderOf u = 2 → t ∈ Subgroup.centralizer ({u} : Set G) →
      t * t = 1 → t ∈ Subgroup.normalizer (QG : Set G) →
      ∀ y ∈ QG ⊓ Subgroup.centralizer ({u} : Set G), y * t = t * y := by
    intro u t hu htu htt htN y hy
    obtain ⟨hyQ, hyu⟩ := Subgroup.mem_inf.mp hy
    by_contra hyt
    set z := y⁻¹ * (t * y * t⁻¹)
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
    have hzQ : z ∈ QG := QG.mul_mem (QG.inv_mem hyQ)
      ((Subgroup.mem_normalizer_iff.mp htN y).mp hyQ)
    have hzu : z ∈ Subgroup.centralizer ({u} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hyu)
        (Subgroup.mul_mem _ (Subgroup.mul_mem _ htu hyu) (Subgroup.inv_mem _ htu))
    have hz1 : z ≠ 1 := by
      intro h
      apply hyt
      have : t * y * t⁻¹ = y := by
        have := congrArg (fun w => y * w) h
        simpa [z] using this
      calc y * t = t * y * t⁻¹ * t := by rw [this]
        _ = t * y := by group
    have hzinv : t * z * t⁻¹ = z⁻¹ := by
      simp only [z]
      rw [htinv]
      calc t * (y⁻¹ * (t * y * t)) * t = t * y⁻¹ * t * y * (t * t) := by group
        _ = t * y⁻¹ * t * y := by rw [htt, mul_one]
        _ = (y⁻¹ * (t * y * t))⁻¹ := by simp only [mul_inv_rev, inv_inv, htinv]; group
    exact s.no_real_three h22 hp hu hzu htu hz1 (hQG3 z hzQ) htt hzinv
  have hJT1 : (s.J * T₁) * (s.J * T₁) = 1 := by
    calc s.J * T₁ * (s.J * T₁) = (s.J * s.J) * (T₁ * T₁) := by
          rw [show s.J * T₁ * (s.J * T₁) = s.J * (T₁ * s.J) * T₁ by group, ← hJT.eq]; group
      _ = 1 := by rw [s.J_mul_J, hT₁T₁, one_mul]
  have hoJT : orderOf (s.J * T₁) = 2 := by
    have hdvd : orderOf (s.J * T₁) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, hJT1])
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exfalso
      have h1 := orderOf_eq_one_iff.mp h
      apply hJneT
      calc T₁ = s.J⁻¹ * (s.J * T₁) := by group
        _ = s.J := by rw [h1, mul_one, s.J_inv]
    · exact h
  have hJV : s.J ∈ V := Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hT₁V : T₁ ∈ V := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hJcJT : s.J ∈ Subgroup.centralizer ({s.J * T₁} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [show s.J * T₁ * s.J = s.J * (T₁ * s.J) by group, ← hJT.eq]
  have hT₁cJ : T₁ ∈ Subgroup.centralizer ({s.J} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hJT.eq.symm
  have hJcT₁ : s.J ∈ Subgroup.centralizer ({T₁} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hJT.eq
  have hQGcen : QG ≤ Subgroup.centralizer ({s.J} : Set G) ⊓
      Subgroup.centralizer ({T₁} : Set G) := by
    have hgen := four_group_odd_centralizer_generation QG s.J T₁ s.orderOf_J hoT₁ hJT
      hJneT.symm hQGodd (by
        rw [denominatorFourGroup_eq]
        exact fun v hv => hQGN v hv)
    rw [hgen]
    refine sup_le (sup_le ?_ ?_) ?_
    · intro y hy
      refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hy).2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcent s.J T₁ s.orderOf_J hT₁cJ hT₁T₁ (hQGN T₁ hT₁V) y hy
    · intro y hy
      refine Subgroup.mem_inf.mpr ⟨?_, (Subgroup.mem_inf.mp hy).2⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcent T₁ s.J hoT₁ hJcT₁ s.J_mul_J (hQGN s.J hJV) y hy
    · intro y hy
      have hyJ := hcent (s.J * T₁) s.J hoJT hJcJT s.J_mul_J (hQGN s.J hJV) y hy
      have hyJT := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hy).2
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr hyJ,
        Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc y * T₁ = s.J⁻¹ * ((s.J * y) * T₁) := by group
        _ = s.J⁻¹ * ((y * s.J) * T₁) := by rw [hyJ]
        _ = s.J⁻¹ * (y * (s.J * T₁)) := by group
        _ = s.J⁻¹ * ((s.J * T₁) * y) := by rw [hyJT]
        _ = T₁ * y := by group
  have hQGKE : QG ≤ s.K ⊔ s.fr.E := by
    intro y hy
    refine s.fr.mem_KE_of_odd ((hQGcen hy).1) ?_
    exact Odd.of_dvd_nat hQGodd (Subgroup.orderOf_dvd_natCard QG hy)
  have hQGK : QG ⊓ s.K = ⊥ := by
    have hle : QG ⊓ s.K ≤ s.K ⊓ Subgroup.centralizer ({T₁} : Set G) :=
      fun y hy => Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hy).2,
        (hQGcen (Subgroup.mem_inf.mp hy).1).2⟩
    have hcard := s.card_K_inf_centralizer h4 hT₁K hoT₁
    have hdvd1 : Nat.card (QG ⊓ s.K : Subgroup G) ∣ s.q + 1 := by
      rw [← hcard]
      exact Subgroup.card_dvd_of_le hle
    have hdvd2 : Nat.card (QG ⊓ s.K : Subgroup G) ∣ 3 ^ (Nat.card M).factorization 3 := by
      rw [← hQGcard]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hq : s.q = 3 ^ s.f := by rw [Hyp.q, hp]
    have hcop : Nat.Coprime (3 ^ (Nat.card M).factorization 3) (s.q + 1) := by
      apply Nat.Coprime.pow_left
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three, hq]
      intro h3
      have h3f : 3 ∣ 3 ^ s.f := dvd_pow_self 3 s.f_pos.ne'
      have := (Nat.dvd_add_right h3f).mp h3
      norm_num at this
    have h1 : Nat.card (QG ⊓ s.K : Subgroup G) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop hdvd2 hdvd1
    exact Subgroup.eq_bot_of_card_eq _ h1
  have hQGE : Nat.card QG ∣ Nat.card s.fr.E := by
    set KE := s.K ⊔ s.fr.E
    have hKn : (s.K.subgroupOf KE).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
      exact sup_le (Subgroup.le_normalizer) s.fr.E_le_normalizer_K
    let π : KE →* KE ⧸ s.K.subgroupOf KE := QuotientGroup.mk' _
    have hEbij : Function.Bijective (π.comp (Subgroup.inclusion (le_sup_right :
        s.fr.E ≤ KE))) := by
      constructor
      · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
        intro e he
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at he
        have hk : ((Subgroup.inclusion (le_sup_right : s.fr.E ≤ KE) e : KE) : G) ∈ s.K :=
          (QuotientGroup.eq_one_iff (N := s.K.subgroupOf KE) _).mp he
        have : (e : G) ∈ s.K ⊓ s.fr.E := Subgroup.mem_inf.mpr ⟨hk, e.2⟩
        rw [s.fr.K_inf_E, Subgroup.mem_bot] at this
        rw [Subgroup.mem_bot]
        exact Subtype.ext this
      · intro q
        obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective q
        obtain ⟨k, hk, e, he, rfl⟩ :=
          (mem_sup_iff_of_le_normalizer s.fr.E_le_normalizer_K).mp hy
        refine ⟨⟨e, he⟩, ?_⟩
        change ((⟨e, _⟩ : KE) : KE ⧸ s.K.subgroupOf KE) = ((⟨k * e, hy⟩ : KE) : KE ⧸ _)
        rw [QuotientGroup.eq]
        change e⁻¹ * (k * e) ∈ s.K
        exact (Subgroup.mem_normalizer_iff.mp (s.fr.E_le_normalizer_K (s.fr.E.inv_mem he)) k).mp
          hk |> fun h => by simpa [mul_assoc] using h
    have hQinj : Function.Injective (π.comp (Subgroup.inclusion hQGKE)) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro y hy
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hy
      have hk : ((Subgroup.inclusion hQGKE y : KE) : G) ∈ s.K :=
        (QuotientGroup.eq_one_iff (N := s.K.subgroupOf KE) _).mp hy
      have : (y : G) ∈ QG ⊓ s.K := Subgroup.mem_inf.mpr ⟨y.2, hk⟩
      rw [hQGK, Subgroup.mem_bot] at this
      rw [Subgroup.mem_bot]
      exact Subtype.ext this
    have h1 := Subgroup.card_dvd_of_injective _ hQinj
    rwa [← Nat.card_eq_of_bijective _ hEbij] at h1
  have hNpos : Nat.card N ≠ 0 := Nat.card_pos.ne'
  have hMpos : Nat.card M ≠ 0 := Nat.card_pos.ne'
  have hEpos : Nat.card s.fr.E ≠ 0 := Nat.card_pos.ne'
  calc (Nat.card N).factorization 3 ≤ (Nat.card M).factorization 3 := by
        rw [← Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hMpos, ← hPGcard]
        exact Subgroup.card_dvd_of_le le_sup_right
    _ ≤ (Nat.card s.fr.E).factorization 3 := by
        rw [← Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hEpos, ← hQGcard]
        exact hQGE

end CFSG.Walter.W67

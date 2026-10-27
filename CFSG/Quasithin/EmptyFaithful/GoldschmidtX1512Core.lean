module

public import CFSG.Quasithin.EmptyFaithful.Der6ACore

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace Der6A

variable {G : Type} [Group G]

section Finite

variable [Finite G]

theorem core1512Four_gen {T H V A X : Subgroup G} (hT : quasithinIsSylowTwo T) (hTH : T ≤ H)
    (hVP : V ≤ pCoreOf 2 H) (hU : IsElemAbelian 2 (conjClosure V H))
    (hA : IsMinOffender T H V A)
    (c1 : Nat.card A ^ 2 * Nat.card ↥(conjClosure V H ⊓ Subgroup.centralizer (A : Set G)) =
      Nat.card ↥(A ⊓ pCoreOf 2 H) ^ 2 * Nat.card (conjClosure V H))
    (c2 : Nat.card (conjClosure V H) *
        Nat.card ↥(A ⊓ pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure V H : Set G)) ^ 2 =
      Nat.card ↥(A ⊓ pCoreOf 2 H) ^ 2 *
        Nat.card ↥(conjClosure V H ⊓ Subgroup.centralizer (A : Set G)))
    (hfix : conjClosure V H ⊓ Subgroup.centralizer (A : Set G) =
      conjClosure V H ⊓ Subgroup.centralizer ((A ⊓ pCoreOf 2 H : Subgroup G) : Set G))
    (hXP : pCoreOf 2 H ≤ X) (hXH : X ≤ H) (hAX : A ≤ X) (hAQ : ¬ A ≤ pCoreOf 2 X)
    (hQT : pCoreOf 2 X ≤ T) (hP1 : (A ⊓ pCoreOf 2 X).relIndex A = 2)
    (hP2 : ∀ N : Subgroup G, N ≤ X → (N.subgroupOf X).Normal → ∀ a ∈ A, a ∈ N →
      a ∉ pCoreOf 2 X → ∀ x ∈ X, ∃ n ∈ N, n⁻¹ * x ∈ pCoreOf 2 X)
    (hHX : H = oTwoUpper X ⊔ T) :
    ⁅omegaOneCenterOf (thompsonJi T 1), oTwoUpper H⁆ = ⊥ := by
  classical
  have hAmax : IsMaxElemAbelian T A := hA.1
  have hAe : IsElemAbelian 2 A := hAmax.2.1
  have hSyl : IsSylowTwoOf T H := isSylowTwoOf_of_le151 hT hTH
  have hPT : pCoreOf 2 H ≤ T := pCoreOf_two_le_of_isSylowTwoOf hSyl
  have hHN : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hUP : conjClosure V H ≤ pCoreOf 2 H := conjClosure_le fun h hh z hz =>
    (Subgroup.mem_normalizer_iff.mp (hHN hh) z).mp (hVP hz)
  have hPQ : pCoreOf 2 H ≤ pCoreOf 2 X :=
    le_pCoreOf_of_le_normalizer 2 hXP (hXH.trans hHN) (pCoreOf_isPGroup 2 H)
  by_cases hrank : 1 < CFSG.Open.pRank 2 T
  swap
  ·
    have hJ : thompsonJi T 1 = ⊥ := by
      refine eq_bot_iff.mpr (iSup₂_le fun B hB => ?_)
      obtain ⟨-, -, hBc⟩ := hB
      have hle : Nat.card B * 2 ^ 1 ≤ 2 ^ 1 := by
        rw [hBc]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have : Nat.card B ≤ 1 := by norm_num at hle; omega
      exact (Subgroup.eq_bot_of_card_le B this).le
    have hE : omegaOneCenterOf (⊥ : Subgroup G) = ⊥ :=
      eq_bot_iff.mpr ((Subgroup.closure_le _).mpr fun x hx => hx.1.1)
    rw [hJ, hE]
    exact Subgroup.commutator_bot_left _
  obtain ⟨hA0e, hA0c⟩ := exists_A0 hAmax hUP hPT hU c1 c2
  have hA0P : conjClosure V H ⊔ (A ⊓ pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure V H : Set G)) ≤
      pCoreOf 2 H := sup_le hUP (inf_le_left.trans inf_le_right)
  have hQp : IsPGroup 2 (pCoreOf 2 X) := pCoreOf_isPGroup 2 X
  have hTE : T ≤ Subgroup.normalizer (omegaOneCenterOf (thompsonJi T 1) : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_omegaOneCenter_J1 T)
  by_cases hEW : ⁅omegaOneCenterOf (thompsonJi T 1), oTwoUpper X⁆ = ⊥
  ·
    exact commutator_eq_bot_of_le_centralizer
      (oTwoUpper_le_centralizer_of_sup hHX hT.1 (le_centralizer_of_commutator_eq_bot hEW) hTE)
  · exfalso
    set U := conjClosure V H with hUdef
    set P := pCoreOf 2 H with hPdef
    set Q := pCoreOf 2 X with hQdef
    set CB := A ⊓ P ⊓ Subgroup.centralizer (U : Set G) with hCBdef
    set A0 := U ⊔ CB with hA0def
    have hA0T : A0 ≤ T := hA0P.trans hPT
    have hA0Q : A0 ≤ Q := hA0P.trans hPQ
    have hA0max : IsMaxElemAbelian T A0 :=
      ⟨hA0T, hA0e, fun B hB hBe => by rw [hA0c]; exact hAmax.2.2 B hB hBe⟩
    have hA0maxQ : IsMaxElemAbelian Q A0 :=
      ⟨hA0Q, hA0e, fun B hB hBe => hA0max.2.2 B (hB.trans hQT) hBe⟩
    have hrQ : CFSG.Open.pRank 2 Q = CFSG.Open.pRank 2 T := by
      have h1 := (isMaxElemAbelian_iff_corank_zero.mp hA0max).2.2
      have h2 := (isMaxElemAbelian_iff_corank_zero.mp hA0maxQ).2.2
      rw [pow_zero, mul_one] at h1 h2
      exact Nat.pow_right_injective le_rfl (h2.symm.trans h1)
    have hrQ1 : 1 < CFSG.Open.pRank 2 Q := hrQ ▸ hrank
    have hEA0 : omegaOneCenterOf (thompsonJi T 1) ≤ A0 :=
      omegaOneCenter_J1_le_of_isMax hrank hA0max
    have hDA0 : omegaOneCenterOf (thompsonJi Q 1) ≤ A0 :=
      omegaOneCenter_J1_le_of_isMax hrQ1 hA0maxQ
    have hED : omegaOneCenterOf (thompsonJi T 1) ≤ omegaOneCenterOf (thompsonJi Q 1) :=
      omegaOneCenter_J1_le_J1 hQT hrQ hrQ1 hEA0 hA0Q
    have hXQ : X ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf 2 X
    have hXD : X ≤ Subgroup.normalizer (omegaOneCenterOf (thompsonJi Q 1) : Set G) :=
      hXQ.trans (normalizer_le_normalizer_omegaOneCenter_J1 Q)
    have hDW : ⁅omegaOneCenterOf (thompsonJi Q 1), oTwoUpper X⁆ ≠ ⊥ := fun h =>
      hEW (le_bot_iff.mp ((Subgroup.commutator_mono hED le_rfl).trans h.le))
    have hDA : ⁅omegaOneCenterOf (thompsonJi Q 1), A⁆ ≠ ⊥ := by
      intro hDA0'
      have hAC : A ≤ Subgroup.centralizer (omegaOneCenterOf (thompsonJi Q 1) : Set G) :=
        le_centralizer_of_commutator_eq_bot hDA0'
      obtain ⟨a, haA, haQ⟩ := Set.not_subset.mp hAQ
      have hNn : ((X ⊓ Subgroup.centralizer (omegaOneCenterOf (thompsonJi Q 1) : Set G)).subgroupOf
          X).Normal :=
        ⟨fun x hx g => by
          rw [Subgroup.mem_subgroupOf] at hx ⊢
          exact conj_mem_inf_centralizer hXD g.2 hx⟩
      have hex := hP2 _ inf_le_left hNn a haA ⟨hAX haA, hAC haA⟩ haQ
      have hXle : X ≤ (X ⊓ Subgroup.centralizer (omegaOneCenterOf (thompsonJi Q 1) : Set G)) ⊔
          Q := fun x hx => by
        obtain ⟨n, hn, hq⟩ := hex x hx
        have hx' : x = n * (n⁻¹ * x) := by group
        rw [hx']
        exact Subgroup.mul_mem_sup hn hq
      have hle := oTwoUpper_le_of_normal_sup
        (N := X ⊓ Subgroup.centralizer (omegaOneCenterOf (thompsonJi Q 1) : Set G)) (S := Q)
        inf_le_left hNn hQp (pCoreOf_le 2 X) hXle
      exact hDW (commutator_eq_bot_of_le_centralizer (hle.trans inf_le_right))
    obtain ⟨d, hdD, hdA⟩ : ∃ d ∈ omegaOneCenterOf (thompsonJi Q 1),
        d ∉ Subgroup.centralizer (A : Set G) := by
      by_contra hcon
      push Not at hcon
      exact hDA (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun d hd => hcon d hd)
    have hAcard : Nat.card A * 2 ^ 0 = 2 ^ CFSG.Open.pRank 2 T :=
      (isMaxElemAbelian_iff_corank_zero.mp hAmax).2.2
    have hAcard' : Nat.card A = 2 ^ CFSG.Open.pRank 2 T := by simpa using hAcard
    have hidx : (A ⊓ Q).relIndex A = 2 := hP1
    have hBXcard : Nat.card A = 2 * Nat.card ↥(A ⊓ Q) := by
      have := Subgroup.relIndex_mul_card (A ⊓ Q) A
      rw [inf_of_le_left inf_le_left, hidx] at this
      exact this.symm
    have hBXpos : 0 < Nat.card ↥(A ⊓ Q) := Nat.card_pos
    have hBXJ : A ⊓ Q ≤ thompsonJi Q 1 :=
      le_iSup₂_of_le (f := fun (B : Subgroup G) (_ : IsElemAbelianCorank Q 1 B) => B) (A ⊓ Q)
        ⟨inf_le_right, B2F.isElemAbelian_mono inf_le_left hAe, by
          rw [hrQ, ← hAcard', hBXcard]; ring⟩ le_rfl
    have hDBX : ∀ d ∈ omegaOneCenterOf (thompsonJi Q 1), ∀ b ∈ A ⊓ Q, d * b = b * d :=
      fun d hd b hb =>
        (Subgroup.mem_centralizer_iff.mp (omegaOneCenterOf_le_centralizer _ hd) b (hBXJ hb)).symm
    have hDe : IsElemAbelian 2 (omegaOneCenterOf (thompsonJi Q 1)) :=
      B2F.isElemAbelian_mono hDA0 hA0e
    have hBXe : IsElemAbelian 2 (A ⊓ Q) := B2F.isElemAbelian_mono inf_le_left hAe
    have hDBe : IsElemAbelian 2 (omegaOneCenterOf (thompsonJi Q 1) ⊔ (A ⊓ Q)) :=
      B2F.isElemAbelian_sup_of_commute hDe hBXe hDBX
    have hDBT : omegaOneCenterOf (thompsonJi Q 1) ⊔ (A ⊓ Q) ≤ T :=
      sup_le (hDA0.trans hA0T) (inf_le_left.trans hAmax.1)
    have hdBX : d ∉ A ⊓ Q := fun h => hdA (Subgroup.mem_centralizer_iff.mpr fun a ha =>
      B2F.isElemAbelian_comm hAe ha h.1)
    have hDBcard : Nat.card ↥(omegaOneCenterOf (thompsonJi Q 1) ⊔ (A ⊓ Q)) = Nat.card A := by
      have hle : Nat.card ↥(omegaOneCenterOf (thompsonJi Q 1) ⊔ (A ⊓ Q)) ≤ Nat.card A :=
        hAmax.2.2 _ hDBT hDBe
      obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le
        (le_sup_right : A ⊓ Q ≤ omegaOneCenterOf (thompsonJi Q 1) ⊔ (A ⊓ Q))
      have hk2 : 2 ≤ k := by
        by_contra hlt
        have hlt' : k < 2 := not_le.mp hlt
        interval_cases k
        · have h0 : Nat.card ↥(omegaOneCenterOf (thompsonJi Q 1) ⊔ (A ⊓ Q)) = 0 := by
            rw [hk, mul_zero]
          exact absurd h0 Nat.card_pos.ne'
        · have heq : A ⊓ Q = omegaOneCenterOf (thompsonJi Q 1) ⊔ (A ⊓ Q) :=
            Subgroup.eq_of_le_of_card_ge le_sup_right (le_of_eq (by rw [hk, mul_one]))
          exact hdBX (by rw [heq]; exact Subgroup.mem_sup_left hdD)
      have hge : Nat.card A ≤ Nat.card ↥(omegaOneCenterOf (thompsonJi Q 1) ⊔ (A ⊓ Q)) := by
        rw [hk, hBXcard]
        calc 2 * Nat.card ↥(A ⊓ Q) ≤ k * Nat.card ↥(A ⊓ Q) := Nat.mul_le_mul_right _ hk2
          _ = Nat.card ↥(A ⊓ Q) * k := Nat.mul_comm _ _
      exact le_antisymm hle hge
    have hDBmax : IsMaxElemAbelian T (omegaOneCenterOf (thompsonJi Q 1) ⊔ (A ⊓ Q)) :=
      ⟨hDBT, hDBe, fun B hB hBe => (hAmax.2.2 B hB hBe).trans hDBcard.ge⟩
    have hBXP : A ⊓ Q ≤ P := by
      by_contra hnot
      have hnotP : ¬ IsMaxElemAbelian P (omegaOneCenterOf (thompsonJi Q 1) ⊔ (A ⊓ Q)) :=
        fun h => hnot (le_sup_right.trans h.1)
      have hmin' := hA.2.2.1 _ hDBmax hnotP
      have hsup : (omegaOneCenterOf (thompsonJi Q 1) ⊔ (A ⊓ Q)) ⊔ P = (A ⊓ Q) ⊔ P := by
        apply le_antisymm
        · exact sup_le (sup_le ((hDA0.trans hA0P).trans le_sup_right) le_sup_left) le_sup_right
        · exact sup_le (le_sup_right.trans le_sup_left) le_sup_right
      rw [hsup] at hmin'
      have hAN : A ≤ Subgroup.normalizer (P : Set G) := (hAmax.1.trans hTH).trans hHN
      have hBN : A ⊓ Q ≤ Subgroup.normalizer (P : Set G) := inf_le_left.trans hAN
      have e1 := S143.card_sup_mul_card_inf_of_le_normalizer hAN
      have e2 := S143.card_sup_mul_card_inf_of_le_normalizer hBN
      rw [sup_comm P A, inf_comm P A] at e1
      rw [sup_comm P (A ⊓ Q)] at e2
      have hinf : P ⊓ (A ⊓ Q) = A ⊓ P := by
        apply le_antisymm
        · rintro x ⟨hxP, hxA, -⟩
          exact ⟨hxA, hxP⟩
        · rintro x ⟨hxA, hxP⟩
          exact ⟨hxP, hxA, hPQ hxP⟩
      rw [hinf] at e2
      have hbpos : 0 < Nat.card ↥(A ⊓ P) := Nat.card_pos
      have hPpos : 0 < Nat.card P := Nat.card_pos
      have hmul : Nat.card P * Nat.card A ≤ Nat.card P * Nat.card ↥(A ⊓ Q) := by
        calc Nat.card P * Nat.card A = Nat.card ↥(A ⊔ P) * Nat.card ↥(A ⊓ P) := e1.symm
          _ ≤ Nat.card ↥(A ⊓ Q ⊔ P) * Nat.card ↥(A ⊓ P) := Nat.mul_le_mul_right _ hmin'
          _ = Nat.card P * Nat.card ↥(A ⊓ Q) := e2
      have := Nat.le_of_mul_le_mul_left hmul hPpos
      omega
    have hBXeq : A ⊓ Q = A ⊓ P := le_antisymm (le_inf inf_le_left hBXP) (inf_le_inf_left A hPQ)
    have hdA0 : d ∈ U ⊔ CB := hDA0 hdD
    obtain ⟨u, huU, c, hcCB, hdeq⟩ := exists_mul_of_mem_sup_of_commute (C := CB)
      (fun u hu c hc => Subgroup.mem_centralizer_iff.mp hc.2 u hu) hdA0
    have hcB : c ∈ A ⊓ P := ⟨hcCB.1.1, hcCB.1.2⟩
    have huB : u ∈ Subgroup.centralizer ((A ⊓ P : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have h1 : d * b = b * d := hDBX d hdD b (hBXeq ▸ hb)
      have h2 : c * b = b * c := B2F.isElemAbelian_comm hAe hcB.1 hb.1
      have key : u * b * c = b * u * c := by
        calc u * b * c = u * (b * c) := by group
          _ = u * (c * b) := by rw [← h2]
          _ = (u * c) * b := by group
          _ = d * b := by rw [hdeq]
          _ = b * d := h1
          _ = b * (u * c) := by rw [hdeq]
          _ = b * u * c := by group
      exact (mul_right_cancel key).symm
    have huA : u ∈ Subgroup.centralizer (A : Set G) := by
      have hmem : u ∈ U ⊓ Subgroup.centralizer ((A ⊓ P : Subgroup G) : Set G) := ⟨huU, huB⟩
      rw [← hfix] at hmem
      exact hmem.2
    apply hdA
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hua : a * u = u * a := Subgroup.mem_centralizer_iff.mp huA a ha
    have hca : a * c = c * a := B2F.isElemAbelian_comm hAe ha hcB.1
    rw [← hdeq]
    calc a * (u * c) = (a * u) * c := by group
      _ = (u * a) * c := by rw [hua]
      _ = u * (a * c) := by group
      _ = u * (c * a) := by rw [hca]
      _ = u * c * a := by group

end Finite

end Der6A

end CFSG.Quasithin

module

public import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Complement

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup
open scoped Pointwise

theorem index_modEq_one_of_star {A : Type} [Group A] [Finite A] {B M : Subgroup A} {p : ℕ}
    [Fact p.Prime] (hB : IsPGroup p B) (hBM : B ≤ M)
    (hstar : ∀ g : A, (∀ b ∈ B, g⁻¹ * b * g ∈ M) → g ∈ M) : M.index ≡ 1 [MOD p] := by
  classical
  let mulAct : MulAction ↥B (A ⧸ M) := MulAction.compHom (A ⧸ M) B.subtype
  have hfix : MulAction.fixedPoints ↥B (A ⧸ M) = {(↑(1 : A) : A ⧸ M)} := by
    ext x
    constructor
    · intro hx
      revert hx
      refine QuotientGroup.induction_on x (fun g hx => ?_)
      have hb : ∀ b : ↥B, b • (↑g : A ⧸ M) = ↑g :=
        fun b => (MulAction.mem_fixedPoints.mp hx) b
      have hmem : ∀ b ∈ B, g⁻¹ * b * g ∈ M := by
        intro b hbB
        let b' : ↥B := ⟨b⁻¹, B.inv_mem hbB⟩
        have h : b' • (↑g : A ⧸ M) = ↑g := hb b'
        change (b' : A) • (↑g : A ⧸ M) = ↑g at h
        rw [MulAction.Quotient.smul_mk, smul_eq_mul] at h
        have h' : ((b' : A) * g)⁻¹ * g ∈ M := QuotientGroup.eq.mp h
        have he : g⁻¹ * b * g = ((b' : A) * g)⁻¹ * g := by
          rw [show (b' : A) = b⁻¹ from rfl]
          group
        rwa [he]
      have hgM : g ∈ M := hstar g hmem
      rw [Set.mem_singleton_iff, QuotientGroup.eq]
      simpa using M.inv_mem hgM
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx, MulAction.mem_fixedPoints]
      intro b
      change ((b : ↥B) : A) • (↑(1 : A) : A ⧸ M) = ↑(1 : A)
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
      rw [QuotientGroup.eq]
      have hbM : ((b : ↥B) : A) ∈ M := hBM b.2
      simpa using M.inv_mem hbM
  have hcard := IsPGroup.card_modEq_card_fixedPoints (p := p) (G := ↥B) hB (A ⧸ M)
  rw [hfix, Nat.card_coe_set_eq, Set.ncard_singleton] at hcard
  rw [Subgroup.index_eq_card]
  exact hcard

private lemma map_normalizer_subgroupOf_eq_inf {A : Type} [Group A] {L T : Subgroup A}
    (hTL : T ≤ L) :
    (Subgroup.normalizer ((T.subgroupOf L : Subgroup ↥L) : Set ↥L)).map L.subtype =
      Subgroup.normalizer (T : Set A) ⊓ L := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨?_, y.2⟩
    have hy' : ∀ t : ↥L, t ∈ T.subgroupOf L ↔ y * t * y⁻¹ ∈ T.subgroupOf L :=
      Subgroup.mem_normalizer_iff.mp hy
    change L.subtype y ∈ Subgroup.normalizer (T : Set A)
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · intro ht
      exact (hy' ⟨t, hTL ht⟩).mp (by rwa [Subgroup.mem_subgroupOf])
    · intro ht
      have htL : t ∈ L := by
        have h1 : y⁻¹ * (y * t * y⁻¹) * y ∈ L :=
          L.mul_mem (L.mul_mem (L.inv_mem y.2) (hTL ht)) y.2
        simpa [mul_assoc] using h1
      have hmem : (y * (⟨t, htL⟩ : ↥L) * y⁻¹) ∈ T.subgroupOf L := by
        rw [Subgroup.mem_subgroupOf]
        simpa using ht
      exact (hy' ⟨t, htL⟩).mpr hmem
  · rintro ⟨hxN, hxL⟩
    refine ⟨⟨x, hxL⟩, ?_, rfl⟩
    have hxN' : ∀ t : A, t ∈ T ↔ x * t * x⁻¹ ∈ T :=
      Subgroup.mem_normalizer_iff.mp hxN
    change (⟨x, hxL⟩ : ↥L) ∈ Subgroup.normalizer ((T.subgroupOf L : Subgroup ↥L) : Set ↥L)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using hxN' (y : A)

theorem index_normalizer_eq_mul_seven {A : Type} [Group A] [Finite A] {L T B : Subgroup A}
    [L.Normal] (hTL : T ≤ L) (hLB : L ⊔ B = ⊤) (hB7 : Nat.card B = 7) (hBL : ¬ B ≤ L)
    (hBT : B ≤ normalizer (T : Set A)) :
    (T.subgroupOf (normalizer (T : Set A))).index =
      ((T.subgroupOf L).subgroupOf
        (normalizer ((T.subgroupOf L : Subgroup ↥L) : Set ↥L))).index * 7 := by
  classical
  set N : Subgroup A := Subgroup.normalizer (T : Set A) with hN
  set Tn : Subgroup ↥N := T.subgroupOf N with hTn
  set T' : Subgroup ↥L := T.subgroupOf L with hT'
  set NL : Subgroup ↥L := Subgroup.normalizer ((T' : Subgroup ↥L) : Set ↥L) with hNL
  set TnL : Subgroup ↥NL := T'.subgroupOf NL with hTnL
  have hTN : T ≤ N := Subgroup.le_normalizer
  have hBN : B ≤ N := hBT
  have hmapNL : NL.map L.subtype = N ⊓ L := by
    rw [hN, hNL, hT']
    exact map_normalizer_subgroupOf_eq_inf hTL
  have hcardNL : Nat.card NL = Nat.card ↥(N ⊓ L) := by
    rw [← hmapNL]
    exact (Subgroup.card_map_of_injective (Subgroup.subtype_injective L)).symm
  have hBinfL : B ⊓ L = ⊥ := by
    have hdvd : Nat.card ↥(B ⊓ L) ∣ Nat.card ↥B := Subgroup.card_dvd_of_le inf_le_left
    rw [hB7] at hdvd
    rcases (Nat.dvd_prime (by decide : Nat.Prime 7)).mp hdvd with h1 | h7
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      apply hBL
      have heq : B ⊓ L = B := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h7, hB7])
      rw [← heq]
      exact inf_le_right
  have hNsup : N = (N ⊓ L) ⊔ B := by
    refine le_antisymm ?_ (sup_le inf_le_left hBN)
    intro n hn
    have hn_top : n ∈ L ⊔ B := by rw [hLB]; exact Subgroup.mem_top n
    rw [Subgroup.mem_sup_of_normal_left] at hn_top
    obtain ⟨l, hlL, b, hbB, hlb⟩ := hn_top
    have hbN : b ∈ N := hBN hbB
    have hlN : l ∈ N := by
      have hln : l = n * b⁻¹ := by rw [← hlb]; group
      rw [hln]
      exact N.mul_mem hn (N.inv_mem hbN)
    have hnlb : n = l * b := hlb.symm
    rw [hnlb]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hlN, hlL⟩)
      (Subgroup.mem_sup_right hbB)
  have hBnormA : B ≤ Subgroup.normalizer ((N ⊓ L : Subgroup A) : Set A) := by
    intro b hb
    have hLnorm : L.Normal := inferInstance
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxN, hxL⟩
      refine ⟨N.mul_mem (N.mul_mem (hBN hb) hxN) (N.inv_mem (hBN hb)), ?_⟩
      exact hLnorm.conj_mem x hxL b
    · rintro ⟨hxN, hxL⟩
      have hbN : b ∈ N := hBN hb
      refine ⟨?_, ?_⟩
      · have heq : x = b⁻¹ * (b * x * b⁻¹) * b := by group
        rw [heq]
        exact N.mul_mem (N.mul_mem (N.inv_mem hbN) hxN) hbN
      · have heq : x = b⁻¹ * (b * x * b⁻¹) * b := by group
        rw [heq]
        simpa using hLnorm.conj_mem _ hxL b⁻¹
  have hBnormN : B.subgroupOf N ≤
      Subgroup.normalizer (((N ⊓ L).subgroupOf N : Subgroup ↥N) : Set ↥N) := by
    intro b hb
    have hbA : (b : A) ∈ B := Subgroup.mem_subgroupOf.mp hb
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using (Subgroup.mem_normalizer_iff.mp (hBnormA hbA)) (x : A)
  have hinf' : B.subgroupOf N ⊓ (N ⊓ L).subgroupOf N = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    have hxB : (x : A) ∈ B := Subgroup.mem_subgroupOf.mp hx1
    have hxNL : (x : A) ∈ N ⊓ L := Subgroup.mem_subgroupOf.mp hx2
    have hxBL : (x : A) ∈ B ⊓ L := ⟨hxB, hxNL.2⟩
    rw [hBinfL] at hxBL
    simpa using hxBL
  have hsup' : B.subgroupOf N ⊔ (N ⊓ L).subgroupOf N = ⊤ := by
    rw [sup_comm, ← Subgroup.subgroupOf_sup inf_le_left hBN, ← hNsup,
      Subgroup.subgroupOf_self]
  have hmul' : ((↑(B.subgroupOf N) : Set ↥N) * (↑((N ⊓ L).subgroupOf N) : Set ↥N)) =
      Set.univ := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right (B.subgroupOf N)
      ((N ⊓ L).subgroupOf N) hBnormN, hsup']
    rfl
  have hcard0 := Subgroup.IsComplement'.card_mul_card
    (Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hinf') hmul')
  rw [show Nat.card ↥(B.subgroupOf N) = Nat.card B from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN).toEquiv, hB7,
    show Nat.card ↥((N ⊓ L).subgroupOf N) = Nat.card ↥(N ⊓ L) from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at hcard0
  have hcardN : Nat.card N = Nat.card ↥(N ⊓ L) * 7 := by
    rw [← hcard0, mul_comm]
  have hcardTn : Nat.card ↥Tn = Nat.card T := by
    rw [hTn]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv
  have hcardTnL : Nat.card ↥TnL = Nat.card T := by
    rw [hTnL, hT']
    exact Nat.card_congr
      ((Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer :
        T.subgroupOf L ≤ Subgroup.normalizer ((T.subgroupOf L : Subgroup ↥L) : Set ↥L))).trans
        (Subgroup.subgroupOfEquivOfLe hTL)).toEquiv
  have hidxTn : Tn.index * Nat.card T = Nat.card N := by
    rw [← hcardTn]
    exact Subgroup.index_mul_card Tn
  have hidxTnL : TnL.index * Nat.card T = Nat.card NL := by
    rw [← hcardTnL]
    exact Subgroup.index_mul_card TnL
  have hmain : Tn.index * Nat.card T = (TnL.index * 7) * Nat.card T := by
    calc Tn.index * Nat.card T = Nat.card N := hidxTn
      _ = Nat.card ↥(N ⊓ L) * 7 := hcardN
      _ = (TnL.index * Nat.card ↥TnL) * 7 := by
        rw [← hcardNL, ← Subgroup.index_mul_card TnL]
      _ = (TnL.index * 7) * Nat.card T := by rw [hcardTnL]; ring
  have hmain' : Nat.card T * Tn.index = Nat.card T * (TnL.index * 7) := by
    rw [mul_comm (Nat.card T) Tn.index, mul_comm (Nat.card T) (TnL.index * 7)]
    exact hmain
  have : Nonempty ↥T := ⟨⟨1, T.one_mem⟩⟩
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hmain'

private lemma sylow_card_eq_prime_sq {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (h2 : p ^ 2 ∣ Nat.card G) (h3 : ¬ p ^ 3 ∣ Nat.card G) :
    Nat.card ↥(↑P : Subgroup G) = p ^ 2 := by
  have hp1 : 1 < p := (Fact.out : Nat.Prime p).one_lt
  obtain ⟨k, hk⟩ := IsPGroup.exists_card_eq (p := p) P.isPGroup'
  have hdvd : Nat.card ↥(↑P : Subgroup G) ∣ Nat.card G := by
    have h := Subgroup.card_dvd_of_le (le_top : (↑P : Subgroup G) ≤ ⊤)
    rwa [Subgroup.card_top] at h
  have h2' : p ^ 2 ∣ p ^ k := hk ▸ (Sylow.pow_dvd_card_of_pow_dvd_card P h2)
  have hk2 : 2 ≤ k :=
    (Nat.pow_le_pow_iff_right hp1).mp (Nat.le_of_dvd (by positivity) h2')
  have hk3 : k ≤ 2 := by
    by_contra h
    have hlt : 2 < k := not_le.mp h
    exact h3 ((pow_dvd_pow p (by omega)).trans (hk ▸ hdvd))
  rw [hk, show k = 2 from le_antisymm hk3 hk2]

theorem normalizer_le_of_index_eq_147 {A : Type} [Group A] [Finite A] {T B M : Subgroup A}
    (hT8 : Nat.card T = 8) (hidx : (T.subgroupOf (normalizer (T : Set A))).index = 147)
    (hBT : B ≤ normalizer (T : Set A)) (hB7 : Nat.card B = 7) (hTM : T ≤ M) (hBM : B ≤ M)
    (hstar : ∀ g : A, (∀ b ∈ B, g⁻¹ * b * g ∈ M) → g ∈ M) : normalizer (T : Set A) ≤ M := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  set N : Subgroup A := Subgroup.normalizer (T : Set A) with hN
  set Tn : Subgroup ↥N := T.subgroupOf N with hTn
  change N ≤ M
  have hTN : T ≤ N := Subgroup.le_normalizer
  have hBN : B ≤ N := hBT
  have hTnn : Tn.Normal := by
    rw [hTn, hN]
    exact Subgroup.normal_in_normalizer
  let π : ↥N →* ↥N ⧸ Tn := QuotientGroup.mk' Tn
  have hQ : Nat.card (↥N ⧸ Tn) = 147 := by
    rw [← Subgroup.index_eq_card]
    simpa [hTn, hN] using hidx
  have hcardTn : Nat.card ↥Tn = 8 := by
    rw [hTn]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv).trans hT8
  have hNcard : Nat.card ↥N = 1176 := by
    have h := Subgroup.index_mul_card Tn
    rw [Subgroup.index_eq_card, hQ, hcardTn] at h
    omega
  have hB1p : IsPGroup 7 ↥(B.subgroupOf N) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN).toEquiv, hB7]
    norm_num
  obtain ⟨P, hB1P⟩ := IsPGroup.exists_le_sylow (P := B.subgroupOf N) hB1p
  let Psub : Subgroup ↥N := ↑P
  have hPcard : Nat.card ↥Psub = 49 := by
    have h := sylow_card_eq_prime_sq P (p := 7) ?_ ?_
    · simpa using h
    · rw [hNcard]; norm_num
    · rw [hNcard]; norm_num
  have hPcomm : ∀ x y : ↥Psub, x * y = y * x := by
    apply IsPGroup.commutative_of_card_eq_prime_sq (p := 7)
    rw [hPcard]; norm_num
  have hPleM : Psub.map N.subtype ≤ M := by
    rintro x ⟨xN, hxP, rfl⟩
    apply hstar (xN : A)
    intro b hb
    have hbN : b ∈ N := hBN hb
    have hbP : (⟨b, hbN⟩ : ↥N) ∈ Psub :=
      hB1P (Subgroup.mem_subgroupOf.mpr hb)
    have hc : (⟨xN, hxP⟩ : ↥Psub) * (⟨⟨b, hbN⟩, hbP⟩ : ↥Psub) =
        (⟨⟨b, hbN⟩, hbP⟩ : ↥Psub) * ⟨xN, hxP⟩ := hPcomm _ _
    have hcA : (xN : A) * b = b * (xN : A) := by
      have := congrArg (fun z : ↥Psub => ((z : ↥N) : A)) hc
      simpa using this
    have he : (xN : A)⁻¹ * b * (xN : A) = b := by
      rw [mul_assoc, ← hcA, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [he]
    exact hBM hb
  have hPinfTn : Psub ⊓ Tn = ⊥ := by
    apply Subgroup.inf_eq_bot_of_coprime
    rw [hPcard, hcardTn]
    norm_num
  let φ : ↥Psub →* ↥N ⧸ Tn := π.comp Psub.subtype
  have hπPcard : Nat.card ↥(Psub.map π) = 49 := by
    have hinj : Function.Injective φ := by
      intro x y hxy
      have hmem : ((x⁻¹ * y : ↥Psub) : ↥N) ∈ Tn := by
        have hxy' : π (x : ↥N) = π (y : ↥N) := hxy
        have h1 : (π (x : ↥N))⁻¹ * π (y : ↥N) = 1 := by
          rw [hxy']
          exact inv_mul_cancel _
        have h2 : π ((x⁻¹ * y : ↥Psub) : ↥N) = 1 := by
          rw [show ((x⁻¹ * y : ↥Psub) : ↥N) = (x : ↥N)⁻¹ * (y : ↥N) from rfl]
          exact h1
        exact (QuotientGroup.eq_one_iff _).mp h2
      have hbot : ((x⁻¹ * y : ↥Psub) : ↥N) ∈ (⊥ : Subgroup ↥N) := by
        rw [← hPinfTn]
        exact ⟨(x⁻¹ * y).2, hmem⟩
      have hone : ((x⁻¹ * y : ↥Psub) : ↥N) = 1 := by simpa using hbot
      have h1 : x⁻¹ * y = 1 := Subtype.ext hone
      exact inv_mul_eq_one.mp h1
    have hsub : Subgroup.map Psub.subtype (⊤ : Subgroup ↥Psub) = Psub := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hrange : φ.range = Psub.map π := by
      rw [MonoidHom.range_eq_map, ← Subgroup.map_map, hsub]
    have hcard := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [hrange] at hcard
    rw [← hcard]
    exact hPcard
  have hπPp : IsPGroup 7 ↥(Psub.map π) := by
    rw [IsPGroup.iff_card]
    exact ⟨2, by rw [hπPcard]; norm_num⟩
  obtain ⟨Pq, hPq⟩ := IsPGroup.exists_le_sylow (P := Psub.map π) hπPp
  have hPqcard : Nat.card ↥(↑Pq : Subgroup (↥N ⧸ Tn)) = 49 := by
    have h : Nat.card ↥(↑Pq : Subgroup (↥N ⧸ Tn)) = 7 ^ 2 :=
      sylow_card_eq_prime_sq Pq (by rw [hQ]; norm_num) (by rw [hQ]; norm_num)
    simpa using h
  have hPqindex : (↑Pq : Subgroup (↥N ⧸ Tn)).index = 3 := by
    have h := Subgroup.index_mul_card (↑Pq : Subgroup (↥N ⧸ Tn))
    rw [hPqcard, hQ] at h
    omega
  have hdvd3 : Nat.card (Sylow 7 (↥N ⧸ Tn)) ∣ 3 := by
    have h := Sylow.card_dvd_index Pq
    rwa [hPqindex] at h
  have hone : Nat.card (Sylow 7 (↥N ⧸ Tn)) = 1 := by
    rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hdvd3 with h1 | h3
    · exact h1
    · exfalso
      have hmod : Nat.card (Sylow 7 (↥N ⧸ Tn)) ≡ 1 [MOD 7] := card_sylow_modEq_one 7 _
      rw [h3, Nat.ModEq] at hmod
      norm_num at hmod
  have : Subsingleton (Sylow 7 (↥N ⧸ Tn)) := (Nat.card_eq_one_iff_unique.mp hone).1
  have hPqeq : Psub.map π = ↑Pq := by
    refine Subgroup.eq_of_le_of_card_ge hPq ?_
    rw [hPqcard, hπPcard]
  have hPqnormal : (Psub.map π).Normal := hPqeq ▸ Sylow.normal_of_subsingleton Pq
  intro g hg
  apply hstar g
  intro b hb
  have hbN : b ∈ N := hBN hb
  have hyN : g⁻¹ * b * g ∈ N := N.mul_mem (N.mul_mem (N.inv_mem hg) hbN) hg
  let yN : ↥N := ⟨g⁻¹ * b * g, hyN⟩
  have hb7 : b ^ 7 = 1 := by
    have h := Subgroup.orderOf_dvd_natCard B hb
    rw [hB7] at h
    exact orderOf_dvd_iff_pow_eq_one.mp h
  have hy7A : (g⁻¹ * b * g) ^ 7 = 1 := by
    rw [show g⁻¹ * b * g = (MulAut.conj g⁻¹) b by rw [MulAut.conj_apply]; group]
    rw [← map_pow, hb7, map_one]
  have hyN7 : yN ^ 7 = 1 := by
    apply Subtype.ext
    change N.subtype (yN ^ 7) = 1
    rw [map_pow]
    exact hy7A
  have hπy7 : (π yN) ^ 7 = 1 := by
    rw [← map_pow, hyN7, map_one]
  have hord : orderOf (π yN) ∣ 7 := orderOf_dvd_iff_pow_eq_one.mpr hπy7
  have hIsP : IsPGroup 7 ↥(Subgroup.zpowers (π yN)) := by
    rw [IsPGroup.iff_card]
    rw [Nat.card_zpowers]
    rcases (Nat.dvd_prime (by decide : Nat.Prime 7)).mp hord with h | h
    · exact ⟨0, by rw [h, pow_zero]⟩
    · exact ⟨1, by rw [h, pow_one]⟩
  obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow (P := Subgroup.zpowers (π yN)) hIsP
  have hSPq : S = Pq := Subsingleton.elim S Pq
  have hmemπ : π yN ∈ Psub.map π := by
    rw [hPqeq, ← hSPq]
    exact hS (Subgroup.mem_zpowers _)
  obtain ⟨pN, hpP, hpπ⟩ := Subgroup.mem_map.mp hmemπ
  have hmemTn : pN⁻¹ * yN ∈ Tn := by
    have hpπ' : (↑pN : ↥N ⧸ Tn) = ↑yN := by simpa [π] using hpπ
    exact QuotientGroup.eq.mp hpπ'
  have hyNsup : yN ∈ Psub ⊔ Tn := by
    have heq : yN = pN * (pN⁻¹ * yN) := by group
    rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hpP) (Subgroup.mem_sup_right hmemTn)
  have hsupM : (Psub ⊔ Tn).map N.subtype ≤ M := by
    rw [Subgroup.map_sup]
    refine sup_le hPleM ?_
    rw [hTn, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTN]
    exact hTM
  have hyM : (yN : A) ∈ M := hsupM (Subgroup.mem_map.mpr ⟨yN, hyNsup, rfl⟩)
  simpa using hyM

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

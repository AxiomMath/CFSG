module

import CFSG.LocalAnalysis.ComponentClassification.Quasisimple
public import CFSG.Quasithin.Background.B1MoreNineC
public import CFSG.Quasithin.Background.B1MoreSevenA

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B1Red

section Group

variable {Ω : Type*} [Group Ω]

theorem sq_mem_of_mem_sup {L A : Subgroup Ω} (hn : A ≤ Subgroup.normalizer (L : Set Ω))
    (hA2 : ∀ a ∈ A, a ^ 2 = 1) : ∀ x ∈ L ⊔ A, x ^ 2 ∈ L := by
  intro x hx
  obtain ⟨l, hl, a, ha, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hn).1 hx
  have h : a * a = 1 := by rw [← pow_two]; exact hA2 a ha
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right h
  have e : (l * a) ^ 2 = l * (a * l * a⁻¹) := by
    rw [pow_two, ha']
    group
  rw [e]
  exact L.mul_mem hl (B19Aux.conj_mem_of_le_normalizer hn ha hl)

theorem mem_of_sq_mem_of_odd {L : Subgroup Ω} {x : Ω} (hx2 : x ^ 2 ∈ L)
    (ho : Odd (orderOf x)) : x ∈ L := by
  have hcop : Nat.Coprime 2 (orderOf x) := Nat.coprime_two_left.2 ho
  exact (Subgroup.zpowers_le.2 hx2) (A4.mem_zpowers_pow_of_coprime hcop)

theorem commutator_le_inf_of_normalizes {N L : Subgroup Ω}
    (hNL : ∀ n ∈ N, ∀ l ∈ L, n * l * n⁻¹ ∈ L) (hLN : ∀ l ∈ L, ∀ n ∈ N, l * n * l⁻¹ ∈ N) :
    ⁅N, L⁆ ≤ N ⊓ L := by
  rw [Subgroup.commutator_le]
  intro n hn l hl
  refine ⟨?_, ?_⟩
  · have h1 := hLN l hl n⁻¹ (N.inv_mem hn)
    have e : n * l * n⁻¹ * l⁻¹ = n * (l * n⁻¹ * l⁻¹) := by group
    show n * l * n⁻¹ * l⁻¹ ∈ N
    rw [e]
    exact N.mul_mem hn h1
  · have h1 := hNL n hn l hl
    show n * l * n⁻¹ * l⁻¹ ∈ L
    exact L.mul_mem h1 (L.inv_mem hl)

theorem commute_of_normal_not_le {N L : Subgroup Ω} (hL : CFSG.Open.IsQuasisimple ↥L)
    (hNL : ∀ n ∈ N, ∀ l ∈ L, n * l * n⁻¹ ∈ L) (hLN : ∀ l ∈ L, ∀ n ∈ N, l * n * l⁻¹ ∈ N)
    (hne : ¬ L ≤ N) : ∀ n ∈ N, ∀ l ∈ L, n * l = l * n := by
  have hnorm : ((N ⊓ L).subgroupOf L).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    refine ⟨?_, ?_⟩
    · have := hLN (g : Ω) g.2 x hx.1
      simpa using this
    · exact L.mul_mem (L.mul_mem g.2 hx.2) (L.inv_mem g.2)
  have hproper : (N ⊓ L).subgroupOf L ≠ ⊤ := by
    intro h
    apply hne
    intro l hl
    have : (⟨l, hl⟩ : L) ∈ (N ⊓ L).subgroupOf L := by rw [h]; trivial
    rw [Subgroup.mem_subgroupOf] at this
    exact this.1
  have hc := CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hL _ hproper
  have hcentral : N ⊓ L ≤ Subgroup.centralizer (L : Set Ω) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hx' : (⟨x, hx.2⟩ : L) ∈ (N ⊓ L).subgroupOf L := hx
    have := Subgroup.mem_center_iff.mp (hc hx') ⟨l, hl⟩
    exact congrArg Subtype.val this
  have hcomm := commutator_le_inf_of_normalizes hNL hLN
  have hperf : Group.IsPerfect ↥L := ⟨hL.1⟩
  have h1 : ⁅⁅L, N⁆, L⁆ = ⊥ := by
    rw [Subgroup.commutator_comm L N, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact (hcomm.trans hcentral)
  have h2 : ⁅L, N⁆ = ⊥ :=
    CFSG.ComponentClassification.Quasisimple.perfect_double_commutator L N h1
  intro n hn l hl
  have h3 : ⁅l, n⁆ ∈ (⊥ : Subgroup Ω) := h2 ▸ Subgroup.commutator_mem_commutator hl hn
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h3
  exact h3.symm

theorem odd_orderOf_of_nilpotent_normal [Finite Ω] {Y N : Subgroup Ω} (hNY : N ≤ Y)
    (hn : ∀ y ∈ Y, ∀ x ∈ N, y * x * y⁻¹ ∈ N) [Group.IsNilpotent ↥N] (hO2 : pCoreOf 2 Y = ⊥) :
    ∀ x ∈ N, Odd (orderOf x) := by
  intro x hx
  by_contra hev
  have h2 : 2 ∣ orderOf x := by
    rcases Nat.even_or_odd (orderOf x) with h | h
    · exact even_iff_two_dvd.1 h
    · exact absurd h hev
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : 2 ∣ Nat.card ↥N := by
    refine h2.trans ?_
    have := orderOf_dvd_natCard (⟨x, hx⟩ : ↥N)
    rwa [Subgroup.orderOf_mk] at this
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 hcard
  have hyp : IsPGroup 2 ↥(Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy]; simp)
  obtain ⟨P, hP⟩ := hyp.exists_le_sylow
  have hyP : y ∈ (P : Subgroup ↥N) := hP (Subgroup.mem_zpowers y)
  have hPn : (P : Subgroup ↥N).Normal := inferInstance
  have : (P : Subgroup ↥N).Characteristic := Sylow.characteristic_of_normal P hPn
  let N' : Subgroup Ω := (P : Subgroup ↥N).map N.subtype
  have hNG : N' ≤ Y := (Subgroup.map_subtype_le _).trans hNY
  have hGnorm : Y ≤ Subgroup.normalizer (N : Set Ω) := le_normalizer_of_conj hn
  have hnormN : Y ≤ Subgroup.normalizer (N' : Set Ω) := fun g hg =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (H := N) _ (hGnorm hg)
  have hpN : IsPGroup 2 ↥N' := P.isPGroup'.map N.subtype
  have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hNG hnormN hpN
  rw [hO2] at hle
  have hy1 : ((y : ↥N) : Ω) ∈ N' := Subgroup.mem_map_of_mem _ hyP
  have hy0 : y = 1 := Subtype.ext (Subgroup.mem_bot.1 (hle hy1))
  rw [hy0, orderOf_one] at hy
  exact absurd hy (by norm_num)

theorem perfect_le_oTwoUpper' [Finite Ω] {K X : Subgroup Ω} (hKX : K ≤ X)
    (hK : Group.IsPerfect ↥K) : K ≤ oTwoUpper X := by
  set M := oTwoUpper X with hM
  have hMn : (M.subgroupOf K).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoUpper X (hKX g.2)) n).mp hn⟩
  have hQ : IsPGroup 2 (↥K ⧸ M.subgroupOf K) := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper X (hKX y.2)
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hk
  have hperf : Group.IsPerfect (↥K ⧸ M.subgroupOf K) :=
    Group.IsPerfect.ofSurjective (G := K) (G' := ↥K ⧸ M.subgroupOf K)
      (f := QuotientGroup.mk' (M.subgroupOf K)) (QuotientGroup.mk'_surjective _)
  have hnil : Group.IsNilpotent (↥K ⧸ M.subgroupOf K) := hQ.isNilpotent
  have hsub : Subsingleton (↥K ⧸ M.subgroupOf K) := by
    by_contra h
    have : Nontrivial (↥K ⧸ M.subgroupOf K) := not_subsingleton_iff_nontrivial.1 h
    exact Group.IsPerfect.not_isNilpotent _ hnil
  intro k hk
  have h1 : (⟨k, hk⟩ : K) ∈ M.subgroupOf K := by
    have := Subsingleton.elim (QuotientGroup.mk (⟨k, hk⟩ : K) : ↥K ⧸ M.subgroupOf K) 1
    rwa [QuotientGroup.eq_one_iff] at this
  exact h1

theorem oTwoUpper_eq_of_perfect [Finite Ω] {L : Subgroup Ω} (hL : Group.IsPerfect ↥L) :
    oTwoUpper L = L :=
  le_antisymm (oTwoUpper_le L) (perfect_le_oTwoUpper' le_rfl hL)

theorem quasithinGenFitting_eq_of_two_quot [Finite Ω] {Y L : Subgroup Ω} (hLY : L ≤ Y)
    (hn : ∀ y ∈ Y, ∀ l ∈ L, y * l * y⁻¹ ∈ L) (hL : CFSG.Open.IsQuasisimple ↥L)
    (h2 : ∀ y ∈ Y, y ^ 2 ∈ L) (hO2 : pCoreOf 2 Y = ⊥) : quasithinGenFitting Y = L := by
  apply le_antisymm
  · unfold quasithinGenFitting
    refine sup_le (sSup_le ?_) (sSup_le ?_)
    · rintro N ⟨hNY, hNn, hNnil⟩ x hx
      have hn' : ∀ y ∈ Y, ∀ z ∈ N, y * z * y⁻¹ ∈ N := by
        intro y hy z hz
        have := hNn.conj_mem ⟨z, hNY hz⟩ (by rw [Subgroup.mem_subgroupOf]; exact hz) ⟨y, hy⟩
        rw [Subgroup.mem_subgroupOf] at this
        simpa using this
      have hodd := odd_orderOf_of_nilpotent_normal hNY hn' hO2 x hx
      exact mem_of_sq_mem_of_odd (h2 x (hNY hx)) hodd
    · rintro K ⟨hKY, -, hKq⟩ k hk
      have hperf : Group.IsPerfect ↥K := ⟨hKq.1⟩
      have h1 : K ≤ oTwoUpper Y := perfect_le_oTwoUpper' hKY hperf
      have h3 : oTwoUpper Y ≤ L :=
        oTwoUpper_le_of_pow_mem fun y hy => ⟨1, by simpa using h2 y hy⟩
      exact h3 (h1 hk)
  · refine le_sup_of_le_right (le_sSup ⟨hLY, ?_, hL⟩)
    refine IsSubnormal.step hLY ?_ (IsSubnormal.refl _)
    exact (Subgroup.normal_subgroupOf_iff hLY).2 fun l y hl hy => hn y hy l hl

theorem allTwoChiefFactorsCentral_of_quasisimple [Finite Ω] {L : Subgroup Ω}
    (hL : CFSG.Open.IsQuasisimple ↥L) : AllTwoChiefFactorsCentral L := by
  rintro A B ⟨hBA, hAL, hAn, hBn, -, hA2⟩
  have hAnorm : (A.subgroupOf L).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hAn
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hL (A.subgroupOf L)
    with hc | htop
  · have : ⁅A, L⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro a ha l hl
      have hmem : (⟨a, hAL ha⟩ : L) ∈ A.subgroupOf L := ha
      have := Subgroup.mem_center_iff.mp (hc hmem) ⟨l, hl⟩
      have h1 : l * a = a * l := congrArg Subtype.val this
      show a * l * a⁻¹ * l⁻¹ ∈ (⊥ : Subgroup Ω)
      rw [Subgroup.mem_bot, ← commutatorElement_def, commutatorElement_eq_one_iff_mul_comm]
      exact h1.symm
    rw [this]
    exact bot_le
  · exfalso
    have hLA : L ≤ A := by
      intro l hl
      have : (⟨l, hl⟩ : L) ∈ A.subgroupOf L := by rw [htop]; trivial
      exact this
    have hperf : Group.IsPerfect ↥L := ⟨hL.1⟩
    have h1 : L ≤ oTwoUpper L := perfect_le_oTwoUpper' le_rfl hperf
    have h2 : oTwoUpper L ≤ B := oTwoUpper_le_of_pow_mem fun a ha => hA2 a (hLA ha)
    exact absurd (hAL.trans (h1.trans h2)) (not_le_of_gt hBA)

end Group

end B1Red

end CFSG.Quasithin

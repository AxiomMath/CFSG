module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aShC
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppEPerm
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport
public import CFSG.Quasithin.Background.G2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS

open CFSG.Open

variable {G : Type} [Group G]

theorem card_eq_four_and_le_index {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]
    (hY : Nat.card Y = 60) {R : Subgroup Y} (hR : IsPGroup 2 R) (hRi : ¬ 2 ∣ R.index) :
    Nat.card ↥R = 4 ∧ 5 ≤ (Subgroup.normalizer (R : Set Y)).index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hR.exists_card_eq
  have hmul := R.card_mul_index
  rw [hY, hk] at hmul
  have hk6 : k < 6 := by
    by_contra hk6
    have : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpos : 0 < R.index := Nat.pos_of_ne_zero (fun h => by rw [h] at hmul; omega)
    have := Nat.le_of_dvd (by norm_num) (Dvd.intro _ hmul)
    omega
  have h4 : Nat.card ↥R = 4 := by
    rw [hk]
    interval_cases k <;> omega
  refine ⟨h4, ?_⟩
  set N := Subgroup.normalizer (R : Set Y) with hN
  have hRN : R ≤ N := Subgroup.le_normalizer
  have hdvd : 4 ∣ Nat.card ↥N := h4 ▸ Subgroup.card_dvd_of_le hRN
  have hNmul := N.card_mul_index
  rw [hY] at hNmul
  have hNtop : N ≠ ⊤ := by
    intro htop
    have hRn : R.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal R with h | h
    · rw [h, Subgroup.card_bot] at h4
      omega
    · rw [h, Subgroup.card_top, hY] at h4
      omega
  have hcore : N.normalCore = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N.normalCore with h | h
    · exact h
    · exact absurd (eq_top_iff.mpr (h ▸ N.normalCore_le)) hNtop
  have hfact := N.index_normalCore_dvd_factorial_index
  rw [hcore, Subgroup.index_bot, hY] at hfact
  obtain ⟨m, hm⟩ := hdvd
  have hi15 : N.index ∣ 15 := ⟨m, by rw [hm] at hNmul; linarith⟩
  have hmem : N.index ∈ Nat.divisors 15 := Nat.mem_divisors.mpr ⟨hi15, by norm_num⟩
  rw [show Nat.divisors 15 = {1, 3, 5, 15} by decide] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h
  · exact absurd (Subgroup.index_eq_one.mp h) hNtop
  · rw [h] at hfact
    exact absurd hfact (by norm_num [Nat.factorial])
  · omega
  · omega

theorem card_inf_normalizer_le [Finite G] {J P : Subgroup G}
    (hJ : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (↥J ⧸ CFSG.pCore 2 ↥J ≃* Matrix.SpecialLinearGroup (Fin 2) F))
    (hP : QuasithinUnique.IsSylowTwoOf P J) :
    Nat.card ↥(J ⊓ Subgroup.normalizer (P : Set G)) ≤ 3 * Nat.card ↥P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hJ
  have := Fintype.ofFinite F
  have hSL : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
    CFSG.QuasithinUnique.AppE.sl2_isSimpleGroup (n := 2) le_rfl
      (by rw [← Nat.card_eq_fintype_card, hF]; norm_num)
  have hsimp : IsSimpleGroup (↥J ⧸ CFSG.pCore 2 ↥J) := e.isSimpleGroup
  have hcard : Nat.card (↥J ⧸ CFSG.pCore 2 ↥J) = 60 := by
    rw [Nat.card_congr e.toEquiv, C11P9A.card_SL2_four hF]
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥J) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  set P' := P.subgroupOf J with hP'
  have hQP : CFSG.pCore 2 ↥J ≤ P' := by
    intro x hx
    rw [hP', Subgroup.mem_subgroupOf]
    refine pCoreOf_two_le_of_isSylowTwoOf hP ⟨x, ?_, rfl⟩
    assumption
  have hker : π.ker = CFSG.pCore 2 ↥J := QuotientGroup.ker_mk' _
  set N' := (J ⊓ Subgroup.normalizer (P : Set G)).subgroupOf J with hN'
  have hN'P : N' ≤ Subgroup.normalizer (P' : Set ↥J) := by
    intro x hx
    rw [hN', Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [hP', Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using Subgroup.mem_normalizer_iff.mp hx.2 y
  have hQN : CFSG.pCore 2 ↥J ≤ N' := by
    intro x hx
    rw [hN', Subgroup.mem_subgroupOf]
    exact ⟨x.2, Subgroup.le_normalizer ((Subgroup.mem_subgroupOf).mp (hQP hx))⟩
  have hP'2 : IsPGroup 2 ↥P' := hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hP.1).symm
  have hPi : (P'.map π).index = P'.index := Subgroup.index_map_eq _ hπs (by rw [hker]; exact hQP)
  have hNi : (N'.map π).index = N'.index := Subgroup.index_map_eq _ hπs (by rw [hker]; exact hQN)
  obtain ⟨h4, h5⟩ := card_eq_four_and_le_index hcard (hP'2.map π) (by rw [hPi]; exact hP.2.2)
  have hle : N'.map π ≤ Subgroup.normalizer ((P'.map π : Subgroup _) : Set _) :=
    (Subgroup.map_mono hN'P).trans (Subgroup.le_normalizer_map π)
  have hdvd := Subgroup.index_dvd_of_le hle
  rw [hNi] at hdvd
  have hN5 : 5 ≤ N'.index :=
    h5.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) hdvd)
  have hP15 : P'.index = 15 := by
    have h := (P'.map π).card_mul_index
    rw [h4, hcard] at h
    omega
  have h1 := P'.card_mul_index
  have h2 := N'.card_mul_index
  rw [hP15] at h1
  have hcN : Nat.card ↥N' = Nat.card ↥(J ⊓ Subgroup.normalizer (P : Set G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hcP : Nat.card ↥P' = Nat.card ↥P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP.1).toEquiv
  rw [← hcN, ← hcP]
  nlinarith

theorem inf_normalizer_eq_sup [Finite G] {J P C : Subgroup G}
    (hJ : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (↥J ⧸ CFSG.pCore 2 ↥J ≃* Matrix.SpecialLinearGroup (Fin 2) F))
    (hP : QuasithinUnique.IsSylowTwoOf P J) (hCJ : C ≤ J)
    (hCP : C ≤ Subgroup.normalizer (P : Set G)) (hC : Nat.card ↥C = 3) :
    J ⊓ Subgroup.normalizer (P : Set G) = C ⊔ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : C ⊔ P ≤ J ⊓ Subgroup.normalizer (P : Set G) :=
    sup_le (le_inf hCJ hCP) (le_inf hP.1 Subgroup.le_normalizer)
  obtain ⟨k, hk⟩ := hP.2.1.exists_card_eq
  have hd : P ⊓ C = ⊥ := disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard (by
    rw [hk, hC]
    exact Nat.Coprime.pow_left _ (by norm_num)))
  have hcard : Nat.card ↥(C ⊔ P) = Nat.card ↥P * 3 := by
    rw [C11P9A.card_sup_eq_mul hCP hd, hC]
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hcard]
  have := card_inf_normalizer_le hJ hP
  omega

theorem charTwo_of_le [Finite G] {H X : Subgroup G} (hH : QuasithinUnique.CharTwo H)
    (hXH : X ≤ H) (hOX : pCoreOf 2 H ≤ X) : QuasithinUnique.CharTwo X :=
  CFSG.QuasithinUnique.CharTwo.of_pCoreOf_le hH hXH hOX

theorem commutator_eq_bot_of_perfect {A L : Subgroup G} (hL : ⁅L, L⁆ = L)
    (h : ⁅⁅A, L⁆, L⁆ = ⊥) : ⁅A, L⁆ = ⊥ := by
  have h1 : ⁅⁅L, A⁆, L⁆ = ⊥ := by rw [Subgroup.commutator_comm L A]; exact h
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h
  rw [hL] at h3
  rw [Subgroup.commutator_comm]
  exact h3

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS

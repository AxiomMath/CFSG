module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeInputs
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.CGT.Timmesfeld75 (IsTI)

variable {G : Type} [Group G] [Finite G]

theorem pRank_ctilde_le_two (D : Data G) (h61 : UC6.R6_1 D) {V₀ V : Subgroup G}
    (hH : F11.Hyp11 D V₀ V) {p : ℕ} (hp : p ∈ D.sig) :
    CFSG.Open.pRank p (F11.CTilde D.M V₀ V) ≤ 2 := by
  have hpP : p.Prime := (D.sig_prime p hp).1
  have hp2 : p ≠ 2 := (D.sig_prime p hp).2
  haveI : Fact p.Prime := ⟨hpP⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨E, hEC, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hpP.one_lt (F11.CTilde D.M V₀ V)
  have hEM : E ≤ D.M := hEC.trans uc22p22q_ctilde_le
  obtain ⟨hV, -, -, hcase⟩ := uc22p22q_hyp11_unpack D hH
  by_cases h4 : Nat.card V₀ ≤ 4
  · exact absurd (uc22p22q_pRank_ctilde_le_one D h61 hH h4 hp) (by omega)
  · have hV₀bot : V₀ ≠ ⊥ := by
      intro h
      apply h4
      rw [h, Subgroup.card_bot]
      norm_num
    obtain ⟨hV₀, -, -⟩ := hcase.resolve_left hV₀bot
    have hV₀exp : ∀ d ∈ V₀, d ^ 2 = 1 := hV₀.2.2.2.2
    have h8 : 8 ≤ Nat.card V₀ := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (uc22p22e_isPGroup_of_elem hV₀.2.2.2)
      rw [hk] at h4 ⊢
      have h3 : 3 ≤ k := by
        by_contra h3'
        exact h4 (by
          simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : k ≤ 2))
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num : 0 < 2) h3
    have hnotV1 : ¬ InCalV1 D.M D.T V₀ := (hH.2.2 h8).1
    by_cases hF2 : p ^ 2 ≤ Nat.card ↥(E ⊓ centralizer (V₀ : Set G))
    · have hFel : IsElemAbelian p (E ⊓ centralizer (V₀ : Set G)) :=
        uc22p22n_isElemAbelian_of_le inf_le_left hE
      have hFnc : ¬ IsCyclic ↥(E ⊓ centralizer (V₀ : Set G)) :=
        uc22p22n_not_isCyclic_of_card hpP hFel hF2
      have hFV : (E ⊓ centralizer (V₀ : Set G)) ≤ centralizer (V : Set G) := by
        intro e he
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        have he0 : ∀ d ∈ V₀, e * d * e⁻¹ = d := by
          intro d hd
          have h := Subgroup.mem_centralizer_iff.mp he.2 d hd
          rw [← h, mul_assoc, mul_inv_cancel, mul_one]
        have h1 := uc22p22q_conj_eq_of_trivial_action hpP hp2 hV₀exp (hE.2 e he.1) he0
          ((uc22p22q_mem_ctilde.1 (hEC he.1)).2.2 v hv)
        exact (mul_inv_eq_iff_eq_mul.1 h1).symm
      exact hH.2.1 (uc22p22n_isTI_of_noncyclic D h61 hp hV (inf_le_left.trans hEM)
        (uc22p22e_isPGroup_of_elem hFel) hFnc hFV)
    · have hFcard : Nat.card ↥(E ⊓ centralizer (V₀ : Set G)) ≤ p := by
        obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp
          (uc22p22e_isPGroup_of_elem (uc22p22n_isElemAbelian_of_le inf_le_left hE))
        rw [hj] at hF2 ⊢
        have hj1 : j ≤ 1 := by
          by_contra hj1'
          exact hF2 (Nat.pow_le_pow_right hpP.pos (by omega : 2 ≤ j))
        calc p ^ j ≤ p ^ 1 := Nat.pow_le_pow_right hpP.pos hj1
          _ = p := pow_one p
      obtain ⟨P, hPE, hPF, hcardP⟩ := uc22p22nb_exists_complement hpP hE inf_le_left hFcard
      have hPel : IsElemAbelian p P := uc22p22n_isElemAbelian_of_le hPE hE
      have hPp : IsPGroup p P := uc22p22e_isPGroup_of_elem hPel
      have hPF' : P ⊓ centralizer (V₀ : Set G) = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have h1 : x ∈ P ⊓ (E ⊓ centralizer (V₀ : Set G)) := ⟨hx.1, hPE hx.1, hx.2⟩
        rwa [hPF] at h1
      have hp2P : p ^ 2 ≤ Nat.card P := by
        have hE3 : p ^ 3 ≤ Nat.card E := by
          rw [hEcard]
          exact Nat.pow_le_pow_right hpP.pos (by omega)
        have h5 : p * p ^ 2 ≤ p * Nat.card P := by
          calc p * p ^ 2 = p ^ 3 := by ring
            _ ≤ Nat.card E := hE3
            _ ≤ p * Nat.card P := hcardP
        exact Nat.le_of_mul_le_mul_left h5 hpP.pos
      have hPc : ¬ IsCyclic P := uc22p22n_not_isCyclic_of_card hpP hPel hp2P
      exact hnotV1 (uc22p22nc_inCalV1_of_good D h61 hp hV₀ (hPE.trans hEM) hPp hPc hPF')

theorem pRank_sub_two_le {p : ℕ} (hp : p.Prime) {M C : Subgroup G}
    [(C.subgroupOf M).Normal] (hC : CFSG.Open.pRank p C ≤ 2) :
    CFSG.Open.pRank p M - 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (↥M ⧸ C.subgroupOf M)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, hEM, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt M
  set r := CFSG.Open.pRank p M with hr
  let π : ↥M →* ↥M ⧸ C.subgroupOf M := QuotientGroup.mk' (C.subgroupOf M)
  have hE' : IsElemAbelian p (E.subgroupOf M) :=
    CFSG.RankThreeCoreUniqueness.Helpers.elementary_transport p E (E.subgroupOf M)
      (Subgroup.subgroupOfEquivOfLe hEM).symm hE
  let ρ : ↥(E.subgroupOf M) →* ↥M ⧸ C.subgroupOf M := π.comp (E.subgroupOf M).subtype
  have hk : Nat.card ρ.ker * Nat.card ρ.range = Nat.card (E.subgroupOf M) :=
    Subgroup.card_ker_mul_card_range ρ
  have hEcard : Nat.card (E.subgroupOf M) = p ^ r := by
    rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM).toEquiv
  have hrange : ρ.range = (E.subgroupOf M).map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hrel : IsElemAbelian p ρ.range := by
    rw [hrange]
    exact CFSG.SectionRank.isElemAbelian_map hE' π
  obtain ⟨k, hk'⟩ := IsPGroup.iff_card.mp (uc22p22e_isPGroup_of_elem hrel)
  have hkle : k ≤ CFSG.Open.pRank p (⊤ : Subgroup (↥M ⧸ C.subgroupOf M)) :=
    CFSG.SectionRank.le_pRank hp.one_lt le_top hrel hk'
  have hker : Nat.card ρ.ker ≤ p ^ 2 := by
    have hEC : IsElemAbelian p (E ⊓ C) := uc22p22n_isElemAbelian_of_le inf_le_left hE
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (uc22p22e_isPGroup_of_elem hEC)
    have hj1 : j ≤ 2 := (CFSG.SectionRank.le_pRank hp.one_lt inf_le_right hEC hj).trans hC
    have hmem : ∀ e : ↥ρ.ker, (((e.1 : ↥(E.subgroupOf M)) : ↥M) : G) ∈ E ⊓ C := by
      intro e
      refine ⟨e.1.2, ?_⟩
      have h2 : π ((e.1 : ↥(E.subgroupOf M)) : ↥M) = 1 := e.2
      exact Subgroup.mem_subgroupOf.1
        ((QuotientGroup.eq_one_iff (N := C.subgroupOf M) ((e.1 : ↥(E.subgroupOf M)) : ↥M)).1 h2)
    have hf : Function.Injective (fun e : ↥ρ.ker => (⟨_, hmem e⟩ : ↥(E ⊓ C))) := by
      intro e₁ e₂ h
      have h' := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext (Subtype.ext h'))
    have hcard_le := Nat.card_le_card_of_injective _ hf
    rw [hj] at hcard_le
    exact hcard_le.trans (Nat.pow_le_pow_right hp.pos hj1)
  have h1 : p ^ r ≤ p ^ 2 * p ^ k := by
    rw [← hEcard, ← hk, hk']
    exact Nat.mul_le_mul_right _ hker
  have h2 : r ≤ k + 2 := by
    apply (Nat.pow_le_pow_iff_right hp.one_lt).1
    rw [pow_add]
    calc p ^ r ≤ p ^ 2 * p ^ k := h1
      _ = p ^ k * p ^ 2 := Nat.mul_comm _ _
  omega

theorem r1111_153_holds (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) : R1111_153 D := by
  intro V₀ V hH _ p hp
  refine ⟨pRank_sub_two_le (D.sig_prime p hp).1 (pRank_ctilde_le_two D h61 hH hp), ?_⟩
  have := hx.three_le p hp
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

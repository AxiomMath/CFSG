module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154UElem

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s16h_le_commutator_of_not_centralizes {A : Type*} [Group A] {Mb Lb : Subgroup A}
    {p : ℕ} (hp : p.Prime) (hLb : Nat.card ↥Lb = p) (hLM : Lb ≤ Mb)
    (hχ : ¬ ∀ n ∈ Mb, n ∈ normalizer (Lb : Set A) → ∀ l ∈ Lb, n * l = l * n) :
    Lb ≤ ⁅Mb, Mb⁆ := by
  haveI : Fact p.Prime := ⟨hp⟩
  simp only [not_forall] at hχ
  obtain ⟨n, hnM, hnN, l, hl, hne⟩ := hχ
  have hcL : n * l * n⁻¹ * l⁻¹ ∈ Lb :=
    Lb.mul_mem ((Subgroup.mem_normalizer_iff.1 hnN l).1 hl) (Lb.inv_mem hl)
  have hc1 : (⟨n * l * n⁻¹ * l⁻¹, hcL⟩ : ↥Lb) ≠ 1 := by
    intro h1
    apply hne
    have h2 : n * l * n⁻¹ * l⁻¹ = 1 := congrArg Subtype.val h1
    have h3 : n * l * n⁻¹ = l := mul_inv_eq_one.1 h2
    calc n * l = n * l * n⁻¹ * n := by group
      _ = l * n := by rw [h3]
  have hcomm : n * l * n⁻¹ * l⁻¹ ∈ ⁅Mb, Mb⁆ := by
    have := Subgroup.commutator_mem_commutator hnM (hLM hl)
    rwa [commutatorElement_def] at this
  intro x hx
  have hx' : (⟨x, hx⟩ : ↥Lb) ∈ Subgroup.zpowers (⟨n * l * n⁻¹ * l⁻¹, hcL⟩ : ↥Lb) := by
    rw [zpowers_eq_top_of_prime_card hLb hc1]
    exact Subgroup.mem_top _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hx'
  have hxk : x = (n * l * n⁻¹ * l⁻¹) ^ k := by
    have := congrArg Subtype.val hk
    simpa using this.symm
  rw [hxk]
  exact (⁅Mb, Mb⁆).zpow_mem hcomm k

theorem s16h_condU2_of_chi_ne (D : Data G) (hSig : UC6S846.SigmaStd D)
    (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D) (h77 : F07.R77Eq D) (h869 : F08.R869 D)
    (h111 : F11.R111 D) (h112 : F11.R112 D) (hThin : ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) (h127 : R127 D)
    (hσ : D.sig = D.sig1) {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hc : Conc4_136 D V₀ V h.hyp151.isElemAbelian L) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hLp : IsCyclicOrd ↥(lBar V₀ V h.hyp151.isElemAbelian L) p)
    (hχ : ¬ ∀ n ∈ Mbar D.M V₀ V h.hyp151.isElemAbelian,
      n ∈ normalizer ((lBar V₀ V h.hyp151.isElemAbelian L : Subgroup _) : Set _) →
        ∀ l ∈ lBar V₀ V h.hyp151.isElemAbelian L, n * l = l * n) :
    s16h_CondU2 D V₀ V L h.hyp151.isElemAbelian := by
  have hV := h.hyp151.isElemAbelian
  have hLM : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV h.hyp151.le
  have hd := s16h_le_commutator_of_not_centralizes hp hLp.2 hLM hχ
  have hcomm : IsMulCommutative ↥(lBar V₀ V hV L) := by
    haveI := hLp.1
    infer_instance
  refine s16h_condU2_of_central_derived D hSig h61 h63 h77 h869 h111 h112 hThin hCyc h127 hσ h
    hc hp hp2 (B := lBar V₀ V hV L) le_rfl ?_ ⟨hcomm, ?_⟩ ?_ hd
  · intro h0
    have h1 : Nat.card ↥(lBar V₀ V hV L) = 1 := by
      rw [h0]
      exact Subgroup.card_bot
    rw [hLp.2] at h1
    exact hp.one_lt.ne' h1
  · intro x hx
    have := pow_card_eq_one' (G := ↥(lBar V₀ V hV L)) (x := ⟨x, hx⟩)
    rw [hLp.2] at this
    exact congrArg Subtype.val this
  · intro b hb l hl
    exact congrArg Subtype.val (hcomm.is_comm.comm ⟨b, hb⟩ ⟨l, hl⟩)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

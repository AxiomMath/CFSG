module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38M3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3SixteenOrd
public import CFSG.Open.GeneralizedFittingSelfCentralizing
public import CFSG.ClassicalInvolution.Q3.Q3TLTShapeAb

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem r1613g_card_le_nine_of_elemAbelian {H : Type} [Group H] [Finite H] {F : Subgroup H}
    [F.Normal] (hF : centralizer (F : Set H) ≤ F) (hE : IsElemAbelianOfRank 3 2 ↥F)
    {E : Subgroup H} (hE3 : IsElemAbelian 3 E) : Nat.card E ≤ 9 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := hE3.1
  have hFcard : Nat.card F = 9 := by
    rw [s16c167_card_isElemAbelianOfRank hE]
    norm_num
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥E) ⟨y, hy⟩)
  by_cases hFE : F ≤ E
  · have hEF : E ≤ F := fun x hx =>
      hF (Subgroup.mem_centralizer_iff.2 fun f hf => hcomm f (hFE hf) x hx)
    calc Nat.card E ≤ Nat.card F := Subgroup.card_le_of_le hEF
      _ = 9 := hFcard
  · have hA3 : Nat.card ↥(E ⊓ F) ≤ 3 := by
      have hdvd : Nat.card ↥(E ⊓ F) ∣ 9 := hFcard ▸ Subgroup.card_dvd_of_le inf_le_right
      have hne : Nat.card ↥(E ⊓ F) ≠ 9 := by
        intro h9
        have hEq : E ⊓ F = F := Subgroup.eq_of_le_of_card_ge inf_le_right (by omega)
        exact hFE (hEq ▸ inf_le_left)
      have hle : Nat.card ↥(E ⊓ F) ≤ 9 := Nat.le_of_dvd (by norm_num) hdvd
      generalize Nat.card ↥(E ⊓ F) = n at hdvd hne hle ⊢
      interval_cases n <;> omega
    let ψ : ↥E →* MulAut ↥F := (MulAut.conjNormal : H →* MulAut ↥F).comp E.subtype
    have hker : ∀ x : ↥E, x ∈ ψ.ker → (x : H) ∈ F := by
      intro x hx
      apply hF
      rw [MonoidHom.mem_ker] at hx
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      have h2 : (x : H) * f * (x : H)⁻¹ = f := by
        have h := congrArg (fun e : MulAut ↥F => ((e ⟨f, hf⟩ : ↥F) : H)) hx
        simpa only [ψ, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.one_apply,
          MulAut.conjNormal_apply, Subtype.coe_mk] using h
      calc f * (x : H) = (x : H) * f * (x : H)⁻¹ * (x : H) := by rw [h2]
        _ = (x : H) * f := by group
    have hkerCard : Nat.card ↥ψ.ker ≤ Nat.card ↥(E ⊓ F) := by
      refine Nat.card_le_card_of_injective
        (fun x => (⟨(x : ↥E).1, (x : ↥E).2, hker x x.2⟩ : ↥(E ⊓ F))) ?_
      intro x y h
      have h2 := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext h2)
    have hrange : Nat.card ↥ψ.range ≤ 3 := by
      have hp : IsPGroup 3 ↥E := fun g =>
        ⟨1, Subtype.ext (by simpa using hE3.2 (g : H) g.2)⟩
      have hp' : IsPGroup 3 ↥ψ.range :=
        hp.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
      obtain ⟨n, hn⟩ := hp'.exists_card_eq
      have hdvd : Nat.card ↥ψ.range ∣ Nat.card (MulAut ↥F) := Subgroup.card_subgroup_dvd_card _
      rw [s16c167_card_mulAut_E9 hE, hn] at hdvd
      by_contra hlt
      have hn2 : 2 ≤ n := by
        by_contra h
        have h3 : 3 ^ n ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have h9 : 3 ^ 2 ∣ 48 := (pow_dvd_pow 3 hn2).trans hdvd
      omega
    have h1 : Nat.card ↥ψ.ker * Nat.card ↥ψ.range = Nat.card E := by
      rw [← Subgroup.card_mul_index ψ.ker, Subgroup.index_ker]
    calc Nat.card E = Nat.card ↥ψ.ker * Nat.card ↥ψ.range := h1.symm
      _ ≤ 3 * 3 := Nat.mul_le_mul (hkerCard.trans hA3) hrange
      _ = 9 := by norm_num

variable {G : Type} [Group G] [Finite G]

theorem r1613g_pRank_Mbar_le_two_of_case168_8 (D : Data G) {V₀ V : Subgroup G}
    (hV : IsElemAbelian 2 V) (h8 : Case168_8 D V₀ V hV) :
    CFSG.Open.pRank 3 (Mbar D.M V₀ V hV) ≤ 2 := by
  classical
  haveI : Finite (MulAut (Vtil V₀ V hV)) := MulEquiv.finite_left
  let Mb : Subgroup (MulAut (Vtil V₀ V hV)) := Mbar D.M V₀ V hV
  let F₀ : Subgroup ↥Mb := genFittingFStar ↥Mb
  haveI : Finite ↥Mb := Subtype.finite
  have hnorm : F₀.Normal := CFSG.ClassicalInvolution.Q3.genFittingFStar_isNormal
  have hself : centralizer (F₀ : Set ↥Mb) ≤ F₀ :=
    CFSG.Open.Open.generalized_fitting_self_centralizing ↥Mb
  obtain ⟨e'⟩ := h8.1
  let e₀ : ↥F₀ ≃* Multiplicative (Fin 2 → ZMod 3) :=
    (Subgroup.equivMapOfInjective F₀ Mb.subtype Mb.subtype_injective).trans e'
  have h1 : CFSG.Open.pRank 3 Mb = CFSG.Open.pRank 3 (⊤ : Subgroup ↥Mb) :=
    CFSG.SectionRank.pRank_eq_pRank_top_subgroup Mb
  show CFSG.Open.pRank 3 Mb ≤ 2
  rw [h1]
  refine CFSG.SectionRank.pRank_le (by norm_num) fun E _ hE => ?_
  have h9 := r1613g_card_le_nine_of_elemAbelian hself ⟨e₀⟩ hE
  simpa using h9

theorem r1613g_not_case168_8_of_four (D : Data G) (hext : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h4 : 3 < CFSG.Open.evenRank G) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) : ¬ Case168_8 D V₀ V hV := by
  intro hc
  have hsig : D.sig = {3} := hc.2.2
  have h3sig : 3 ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 3
  have h16 : Hyp16 D V₀ V := hS.setting.hyp16
  have hP : PairFacts D.M V₀ V := h16.hyp125.pairFacts
  have hb := r1613g_pRank_Mbar_le_two_of_case168_8 D hV hc
  have ha : CFSG.Open.pRank 3 (F11.CTilde D.M V₀ V) ≤ 1 :=
    uc22p22q_pRank_ctilde_le_one D h61 (Hyp125.hyp11 h127 h16.hyp125)
      (Sixteen21.card_le_four_of_hyp16 h16) h3sig
  have hadd := r38m3_pRank_le_add hV hP Nat.prime_three
  have h4' := hext.four_le h4 3 h3sig
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

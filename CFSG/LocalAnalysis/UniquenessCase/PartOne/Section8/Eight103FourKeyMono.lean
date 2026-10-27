module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight103FourKeyAbstract
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open scoped Pointwise

private lemma card_map_le_prime_sq_mul_card_map_inf {G X : Type*} [Group G] [Group X]
    [Finite G] {p : ℕ} [Fact p.Prime] (c : G →* MulAut X) (hker : Nat.card c.ker = p)
    {T D R1 : Subgroup G} (hR1T : R1 ≤ T) (hkD : c.ker ≤ D) (hDi : D.relIndex T ≤ p ^ 2)
    (hkerR1 : c.ker ≤ R1) :
    Nat.card ↥(R1.map c) ≤ p ^ 2 * Nat.card ↥((R1 ⊓ D).map c) := by
  classical
  let E : Subgroup G := R1 ⊓ D
  have hE_card : Nat.card ↥E = Nat.card ↥(E.map c) * p := by
    let f : E →* MulAut X := c.comp E.subtype
    have hfker : f.ker = c.ker.subgroupOf E := by
      ext x
      rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, MonoidHom.mem_ker]
      rfl
    have hfr : f.range = E.map c := by
      rw [show f = c.comp E.subtype from rfl, MonoidHom.range_comp,
        Subgroup.range_subtype]
    have h := Subgroup.card_ker_mul_card_range f
    rw [hfker, hfr,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_inf hkerR1 hkD)).toEquiv,
      hker] at h
    rw [← h, Nat.mul_comm]
  have hR1_card : Nat.card ↥R1 = Nat.card ↥(R1.map c) * p := by
    let f : R1 →* MulAut X := c.comp R1.subtype
    have hfker : f.ker = c.ker.subgroupOf R1 := by
      ext x
      rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, MonoidHom.mem_ker]
      rfl
    have hfr : f.range = R1.map c := by
      rw [show f = c.comp R1.subtype from rfl, MonoidHom.range_comp,
        Subgroup.range_subtype]
    have h := Subgroup.card_ker_mul_card_range f
    rw [hfker, hfr, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerR1).toEquiv,
      hker] at h
    rw [← h, Nat.mul_comm]
  have hrel : E.relIndex R1 ≤ p ^ 2 := by
    have hDfin : D.FiniteIndex := Subgroup.finiteIndex_of_finite
    have hDrel : D.IsFiniteRelIndex T := Subgroup.isFiniteRelIndex_of_finiteIndex
    rw [show E = R1 ⊓ D from rfl, Subgroup.inf_relIndex_left]
    exact (Subgroup.relIndex_le_of_le_right hR1T Subgroup.relIndex_ne_zero).trans hDi
  have hR1_formula : Nat.card ↥R1 = E.relIndex R1 * Nat.card ↥E := by
    have h := Subgroup.relIndex_mul_card E R1
    rw [show E ⊓ R1 = E from inf_eq_left.mpr inf_le_left] at h
    exact h.symm
  have hmul : Nat.card ↥(R1.map c) * p = (E.relIndex R1 * Nat.card ↥(E.map c)) * p := by
    calc Nat.card ↥(R1.map c) * p = Nat.card ↥R1 := hR1_card.symm
      _ = E.relIndex R1 * Nat.card ↥E := hR1_formula
      _ = E.relIndex R1 * (Nat.card ↥(E.map c) * p) := by rw [hE_card]
      _ = (E.relIndex R1 * Nat.card ↥(E.map c)) * p := by ring
  show Nat.card ↥(R1.map c) ≤ p ^ 2 * Nat.card ↥(E.map c)
  rw [Nat.eq_of_mul_eq_mul_right (Fact.out : p.Prime).pos hmul]
  exact Nat.mul_le_mul_right _ hrel

private lemma card_map_le_prime_sq_of_not_le {G X : Type*} [Group G] [Group X]
    [Finite G] {p : ℕ} [Fact p.Prime] (c : G →* MulAut X) (hker : Nat.card c.ker = p)
    {Q T R1 : Subgroup G} (hTi : T.relIndex Q ≤ p)
    (hTy : ∀ y ∈ Q, y ∉ T → ∀ E : Subgroup G, E ≤ T →
      (∀ s ∈ E, s * y * s⁻¹ * y⁻¹ ∈ c.ker) → Nat.card E ≤ p ^ 2)
    (hR1Q : R1 ≤ Q) (hR1T : ¬ R1 ≤ T) (hkerR1 : c.ker ≤ R1)
    (hcomm : ∀ a ∈ R1, ∀ b ∈ R1, c a * c b = c b * c a) :
    Nat.card ↥(R1.map c) ≤ p ^ 2 := by
  classical
  obtain ⟨y, hyR1, hyT⟩ : ∃ y ∈ R1, y ∉ T := by
    by_contra h
    apply hR1T
    intro x hx
    by_contra hxT
    exact h ⟨x, hx, hxT⟩
  let E : Subgroup G := T ⊓ R1
  have hET : E ≤ T := inf_le_left
  have hcomm' : ∀ s ∈ E, s * y * s⁻¹ * y⁻¹ ∈ c.ker := by
    intro s hs
    rw [MonoidHom.mem_ker]
    have hc := hcomm s hs.2 y hyR1
    simp only [map_mul, map_inv]
    rw [hc]
    group
  have hEcard : Nat.card ↥E ≤ p ^ 2 := hTy y (hR1Q hyR1) hyT E hET hcomm'
  have hrel : T.relIndex R1 ≤ p := by
    have hTfin : T.FiniteIndex := Subgroup.finiteIndex_of_finite
    have hTrel : T.IsFiniteRelIndex Q := Subgroup.isFiniteRelIndex_of_finiteIndex
    exact (Subgroup.relIndex_le_of_le_right hR1Q Subgroup.relIndex_ne_zero).trans hTi
  have hR1_formula : Nat.card ↥R1 = T.relIndex R1 * Nat.card ↥E := by
    have h := Subgroup.relIndex_mul_card T R1
    rw [show T ⊓ R1 = E from rfl] at h
    exact h.symm
  have hR1_card : Nat.card ↥R1 = Nat.card ↥(R1.map c) * p := by
    let f : R1 →* MulAut X := c.comp R1.subtype
    have hfker : f.ker = c.ker.subgroupOf R1 := by
      ext x
      rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, MonoidHom.mem_ker]
      rfl
    have hfr : f.range = R1.map c := by
      rw [show f = c.comp R1.subtype from rfl, MonoidHom.range_comp,
        Subgroup.range_subtype]
    have h := Subgroup.card_ker_mul_card_range f
    rw [hfker, hfr, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerR1).toEquiv,
      hker] at h
    rw [← h, Nat.mul_comm]
  have hmul : Nat.card ↥(R1.map c) * p ≤ p ^ 2 * p := by
    calc Nat.card ↥(R1.map c) * p = Nat.card ↥R1 := hR1_card.symm
      _ = T.relIndex R1 * Nat.card ↥E := hR1_formula
      _ ≤ p * p ^ 2 := Nat.mul_le_mul hrel hEcard
      _ = p ^ 2 * p := by ring
  exact Nat.le_of_mul_le_mul_right hmul (Fact.out : p.Prime).pos

theorem u45KeyDvdConcl_of_monomial {X G : Type*} [Group X] [Finite X] [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (c : G →* MulAut X) (hc : ∀ α : MulAut X, α ^ p = 1 → α ∈ c.range)
    (hker : Nat.card c.ker = p) {Q T D : Subgroup G} (hQ : IsPGroup p Q) (hQi : ¬ p ∣ Q.index)
    (hTi : T.relIndex Q ≤ p)
    (hTy : ∀ y ∈ Q, y ∉ T → ∀ E : Subgroup G, E ≤ T →
      (∀ s ∈ E, s * y * s⁻¹ * y⁻¹ ∈ c.ker) → Nat.card E ≤ p ^ 2)
    (hkD : c.ker ≤ D) (hDi : D.relIndex T ≤ p ^ 2)
    {S₀ : Subgroup X} (hS₀ : IsPGroup 3 S₀) (hS₀i : ¬ 3 ∣ S₀.index)
    (hDS : ∀ d ∈ D, ∀ s ∈ S₀, c d s = s) :
    U45KeyDvdConcl X p := by
  classical
  intro R hR
  have hRle : R ≤ c.range := fun α hα => hc α (hR.2 α hα)
  let Rt : Subgroup G := R.comap c
  have hRt_map : Rt.map c = R := Subgroup.map_comap_eq_self hRle
  have hker_le_Rt : c.ker ≤ Rt := by
    intro x hx
    exact Subgroup.mem_comap.mpr (by rw [MonoidHom.mem_ker.mp hx]; exact R.one_mem)
  have hcardRt : Nat.card Rt = Nat.card R * p := by
    let f : Rt →* MulAut X := c.comp Rt.subtype
    have hfker : f.ker = c.ker.subgroupOf Rt := by
      ext x
      rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, MonoidHom.mem_ker]
      rfl
    have hfr : f.range = R := by
      rw [show f = c.comp Rt.subtype from rfl, MonoidHom.range_comp,
        Subgroup.range_subtype, hRt_map]
    have h := Subgroup.card_ker_mul_card_range f
    rw [hfker, hfr, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker_le_Rt).toEquiv,
      hker] at h
    rw [← h, Nat.mul_comm]
  have hRtpg : IsPGroup p Rt := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hR.isPGroup
    refine IsPGroup.of_card (n := n + 1) ?_
    rw [hcardRt, hn, pow_succ]
  let Qs : Sylow p G := hQ.toSylow hQi
  have hQs : (Qs : Subgroup G) = Q := IsPGroup.toSylow_coe hQ hQi
  obtain ⟨P, hRtP⟩ := hRtpg.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Qs
  let R1 : Subgroup G := Rt.map (MulAut.conj g).toMonoidHom
  have hR1_le_Q : R1 ≤ Q := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hset : MulAut.conj g • (P : Set G) = (Q : Set G) := by
      rw [← Sylow.coe_smul, hg]
      exact congrArg (fun S : Subgroup G => (S : Set G)) hQs
    have hmem : MulAut.conj g • y ∈ MulAut.conj g • (P : Set G) :=
      Set.smul_mem_smul_set (hRtP hy)
    rwa [hset, MulAut.smul_def] at hmem
  have hR1_card : Nat.card R1 = Nat.card R * p := by
    rw [show R1 = Rt.map (MulAut.conj g).toMonoidHom from rfl,
      Subgroup.card_map_of_injective (MulAut.conj g).injective, hcardRt]
  have hcomp : c.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (c g)).toMonoidHom.comp c := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      map_mul, map_inv]
  have hR1_map_card : Nat.card ↥(R1.map c) = Nat.card R := by
    rw [show R1 = Rt.map (MulAut.conj g).toMonoidHom from rfl, Subgroup.map_map, hcomp,
      ← Subgroup.map_map Rt (MulAut.conj (c g)).toMonoidHom c, hRt_map]
    exact Subgroup.card_map_of_injective (MulAut.conj (c g)).injective
  have hker_le_R1 : c.ker ≤ R1 := by
    intro x hx
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, ?_, ?_⟩
    · exact hker_le_Rt (by simpa using (MonoidHom.normal_ker c).conj_mem x hx g⁻¹)
    · change MulAut.conj g (g⁻¹ * x * g) = x
      rw [MulAut.conj_apply]
      group
  have hcR1 : R1.map c = R.map (MulAut.conj (c g)).toMonoidHom := by
    calc R1.map c = Rt.map (c.comp (MulAut.conj g).toMonoidHom) := by
          rw [show R1 = Rt.map (MulAut.conj g).toMonoidHom from rfl, Subgroup.map_map]
      _ = Rt.map ((MulAut.conj (c g)).toMonoidHom.comp c) := by rw [hcomp]
      _ = (Rt.map c).map (MulAut.conj (c g)).toMonoidHom :=
          (Subgroup.map_map Rt (MulAut.conj (c g)).toMonoidHom c).symm
      _ = R.map (MulAut.conj (c g)).toMonoidHom := by rw [hRt_map]
  have hcommute : ∀ a ∈ R1, ∀ b ∈ R1, c a * c b = c b * c a := by
    intro a ha b hb
    have ha_img : c a ∈ R.map (MulAut.conj (c g)).toMonoidHom := by
      rw [← hcR1]; exact Subgroup.mem_map_of_mem c ha
    have hb_img : c b ∈ R.map (MulAut.conj (c g)).toMonoidHom := by
      rw [← hcR1]; exact Subgroup.mem_map_of_mem c hb
    obtain ⟨a', ha', haeq⟩ := Subgroup.mem_map.mp ha_img
    obtain ⟨b', hb', hbeq⟩ := Subgroup.mem_map.mp hb_img
    have hRcomm : IsMulCommutative R := hR.1
    have hval : a' * b' = b' * a' :=
      congrArg Subtype.val (mul_comm' (⟨a', ha'⟩ : R) ⟨b', hb'⟩)
    rw [← haeq, ← hbeq, ← map_mul, ← map_mul, hval]
  by_cases hR1T : R1 ≤ T
  · let E : Subgroup G := R1 ⊓ D
    let C1 : Subgroup (MulAut X) := E.map c
    have hE_le_D : E ≤ D := inf_le_right
    have hker_le_E : c.ker ≤ E := le_inf hker_le_R1 hkD
    have hE_card : Nat.card ↥E = Nat.card ↥C1 * p := by
      let f : E →* MulAut X := c.comp E.subtype
      have hfker : f.ker = c.ker.subgroupOf E := by
        ext x
        rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, MonoidHom.mem_ker]
        rfl
      have hfr : f.range = C1 := by
        rw [show f = c.comp E.subtype from rfl, MonoidHom.range_comp,
          Subgroup.range_subtype]
      have h := Subgroup.card_ker_mul_card_range f
      rw [hfker, hfr, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker_le_E).toEquiv,
        hker] at h
      rw [← h, Nat.mul_comm]
    have hC1_le : C1 ≤ R.map (MulAut.conj (c g)).toMonoidHom := by
      rw [← hcR1]
      exact Subgroup.map_mono (f := c) inf_le_left
    have hR_card : Nat.card R ≤ p ^ 2 * Nat.card C1 := by
      have hbound := card_map_le_prime_sq_mul_card_map_inf c hker hR1T hkD hDi hker_le_R1
      rw [hR1_map_card] at hbound
      exact hbound
    let C : Subgroup (MulAut X) := C1.map (MulAut.conj ((c g)⁻¹)).toMonoidHom
    have hC_le_R : C ≤ R := by
      intro x hx
      obtain ⟨β, hβ, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨ρ, hρ, rfl⟩ := Subgroup.mem_map.mp (hC1_le hβ)
      have hinv : (MulAut.conj ((c g)⁻¹)) ((MulAut.conj (c g)) ρ) = ρ := by
        rw [MulAut.conj_apply, MulAut.conj_apply]
        group
      change (MulAut.conj ((c g)⁻¹)) ((MulAut.conj (c g)) ρ) ∈ R
      rw [hinv]
      exact hρ
    have hC_card : Nat.card C = Nat.card C1 :=
      Subgroup.card_map_of_injective (MulAut.conj ((c g)⁻¹)).injective
    have hC_fix : ∀ α ∈ C, ∀ s ∈ S₀.map (((c g)⁻¹).toMonoidHom), α s = s := by
      intro α hα s hs
      obtain ⟨β, hβ, rfl⟩ := Subgroup.mem_map.mp hα
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hβ
      obtain ⟨s₀, hs₀, rfl⟩ := Subgroup.mem_map.mp hs
      have hβs : c e s₀ = s₀ := hDS e (hE_le_D he) s₀ hs₀
      change (MulAut.conj ((c g)⁻¹)) (c e) (((c g)⁻¹) s₀) = ((c g)⁻¹) s₀
      rw [MulAut.conj_apply, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply,
        inv_inv, MulAut.inv_apply, MulEquiv.apply_symm_apply, hβs]
    refine ⟨S₀.map (((c g)⁻¹).toMonoidHom), hS₀.map _, ?_, C, hC_le_R, hC_fix, ?_⟩
    · rw [Subgroup.index_map_of_bijective (((c g)⁻¹).bijective)]
      exact hS₀i
    · rw [hC_card]
      exact hR_card
  · have hR_card : Nat.card R ≤ p ^ 2 := by
      have hbound := card_map_le_prime_sq_of_not_le c hker hTi hTy hR1_le_Q hR1T
        hker_le_R1 hcommute
      rwa [hR1_map_card] at hbound
    refine ⟨S₀, hS₀, hS₀i, ⊥, bot_le, ?_, ?_⟩
    · intro α hα s hs
      rw [Subgroup.mem_bot.mp hα]
      rfl
    · rw [Subgroup.card_bot, mul_one]
      exact hR_card

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end

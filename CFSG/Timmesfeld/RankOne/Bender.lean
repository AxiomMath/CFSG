module

public import CFSG.Timmesfeld.RankOne.Hua
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.Suzuki
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_10_12

public section

namespace CFSG.Timmesfeld

open RankOne
open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.PFchapter1section1
open CFSG.BenderSuzuki.PFAppendixIII
open scoped LinearAlgebra.Projectivization

namespace RankOne

theorem exists_orderOf_eq_four_suzuki {k : ℕ} (hk : k ≠ 0) :
    ∃ x : SuzukiMatrixGroup k, orderOf x = 4 := by
  let K := BinaryGaloisField (2 * k + 1)
  let pi : K ≃+* K := iterateFrobeniusEquiv K 2 (k + 1)
  have hpi : ∀ x : K, pi x = x ^ (2 ^ (k + 1)) := fun x =>
    iterateFrobeniusEquiv_def K 2 (k + 1) x
  have hpi_sq : ∀ x : K, pi (pi x) = x ^ 2 :=
    External.binaryGaloisField_tits_formula_sq k pi hpi
  rcases External.huppert_blackburn_XI_3_1 k (Nat.pos_of_ne_zero hk) pi hpi_sq with
    ⟨-, -, -, -, ⟨x, hx⟩, -⟩
  have hle : Subgroup.closure {A | ∃ a b : K, A = SuzukiRootGL k a b} ≤ SuzukiMatrixGroup k := by
    apply Subgroup.closure_mono
    rintro _ ⟨a, b, rfl⟩
    exact Or.inl ⟨a, b, rfl⟩
  refine ⟨Subgroup.inclusion hle x, ?_⟩
  rw [orderOf_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle), hx]

theorem mem_of_mul_self_eq_one {X : Type*} [Group X] {L : Subgroup X} [L.Normal] [Finite X]
    (hodd : Odd (Nat.card (X ⧸ L))) {x : X} (hx : x * x = 1) : x ∈ L := by
  rw [← QuotientGroup.eq_one_iff]
  have h2 : orderOf (x : X ⧸ L) ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_two, ← QuotientGroup.mk_mul, hx, QuotientGroup.mk_one]
  have hodd' : Odd (orderOf (x : X ⧸ L)) := Odd.of_dvd_nat hodd (orderOf_dvd_natCard _)
  have h1 : orderOf (x : X ⧸ L) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h1 | h1
    · exact h1
    · rw [h1] at hodd'
      exact absurd hodd' (by decide)
  exact orderOf_eq_one_iff.1 h1

end RankOne

variable {X : Type} [Group X]

namespace IsElemAbRankOne

variable {A B : Subgroup X} (h : IsElemAbRankOne A B)
include h

theorem commute_of_isPGroup [Finite X] {P : Subgroup X} (hP : IsPGroup 2 P) {x y : X}
    (hx : x ∈ P) (hy : y ∈ P) : Commute x y := by
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X h.sylow S
  have hx' : x ∈ (S : Subgroup X) := hS hx
  have hy' : y ∈ (S : Subgroup X) := hS hy
  rw [← hg, Sylow.coe_subgroup_smul, coe_sylow] at hx' hy'
  exact h.commute_of_mem_map_conj hx' hy'

theorem orderOf_ne_four [Finite X] (x : X) : orderOf x ≠ 4 := by
  intro h4
  have hp : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, h4]; norm_num)
  have hxx := h.mul_self_of_isPGroup hp
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, hxx])
  rw [h4] at hdvd
  norm_num at hdvd

theorem eq_top_of_odd_index {L : Subgroup X} [L.Normal] [Finite X]
    (hodd : Odd (Nat.card (X ⧸ L))) : L = ⊤ := by
  rw [eq_top_iff, ← h.gen]
  refine sup_le (fun a ha => ?_) (fun b hb => ?_)
  · exact RankOne.mem_of_mul_self_eq_one hodd (h.sq a ha)
  · exact RankOne.mem_of_mul_self_eq_one hodd (h.symm.sq b hb)

theorem twoRankAtLeastTwo [Finite X] (hq : 4 ≤ Nat.card A) : TwoRankAtLeastTwo X := by
  obtain ⟨m, -, hm⟩ := h.exists_card_eq
  have hm2 : 2 ≤ m := by
    by_contra hlt
    interval_cases m <;> simp_all
  have hdvd : 2 ^ 2 ∣ Nat.card A := by
    rw [hm]
    exact pow_dvd_pow 2 hm2
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := A) 2 hdvd
  refine ⟨K.map A.subtype, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective A.subtype_injective, hK]
    norm_num
  · rintro ⟨x, hx⟩
    apply Subtype.ext
    obtain ⟨y, -, rfl⟩ := hx
    change (y : X) ^ 2 = 1
    rw [pow_two]
    exact h.sq _ y.2

theorem hypothesisA [Finite X] (hfaith : FaithfulSMul X (Point A)) (hq : 4 ≤ Nat.card A)
    {b : X} (hb : b ∈ B) (hb1 : b ≠ 1) :
    HypothesisA X (Point A) (MulAction.stabilizer X (Point.base A))
      (MulAction.stabilizer X (Point.base A) ⊓
        rightConjugate (MulAction.stabilizer X (Point.base A)) b) A b := by
  set H := MulAction.stabilizer X (Point.base A) with hH
  have hHN : H = Subgroup.normalizer (A : Set X) := Point.stabilizer_base
  have hbb : b * b = 1 := h.symm.sq b hb
  set ω₁ : Point A := b⁻¹ • Point.base A with hω₁def
  have hω₁ : ω₁ ≠ Point.base A := by
    intro heq
    have : A.map (MulAut.conj b⁻¹).toMonoidHom = A := congrArg Point.val heq
    exact hb1 (inv_eq_one.1 (h.symm.eq_one_of_map_conj_eq (B.inv_mem hb) this))
  have hD : H ⊓ rightConjugate H b = H ⊓ MulAction.stabilizer X ω₁ := by
    rw [hH, rightConjugate_stabilizer]
  have hAH : A ≤ H := by
    rw [hHN]
    exact fun a ha => map_conj_eq_self_iff.1 (map_conj_of_mem ha)
  have htrans : ∀ C D : Point A, C ≠ Point.base A → D ≠ Point.base A →
      ∃ a ∈ A, a • C = D := by
    intro C D hC hD
    obtain ⟨c, hc, rfl⟩ := h.exists_pt hC
    obtain ⟨d, hd, rfl⟩ := h.exists_pt hD
    exact ⟨d * c⁻¹, A.mul_mem hd (A.inv_mem hc), by rw [h.smul_pt, inv_mul_cancel_right]⟩
  refine ⟨⟨h.isMultiplyPretransitive, ⟨Point.base A, rfl⟩, ⟨hb1, by rw [pow_two, hbb]⟩, ?_, rfl,
    hAH, inf_le_left, ?_, ?_, ?_, ?_, ?_⟩, hfaith, h.twoRankAtLeastTwo hq⟩
  ·
    intro hbH
    rw [hHN, ← map_conj_eq_self_iff] at hbH
    exact hb1 (h.symm.eq_one_of_map_conj_eq hb hbH)
  ·
    rw [hHN]
    exact Subgroup.normal_in_normalizer
  ·
    rw [hD, Subgroup.disjoint_def]
    intro x hxA hxD
    by_contra hx1
    exact hω₁ (h.eq_base_of_smul_eq hxA hx1 (Subgroup.mem_inf.1 hxD).2)
  ·
    refine le_antisymm (sup_le hAH inf_le_left) fun g hg => ?_
    have hgω : g • ω₁ ≠ Point.base A := by
      intro heq
      apply hω₁
      have hgb : g • Point.base A = Point.base A := hg
      rw [← hgb] at heq
      exact smul_left_cancel g heq
    obtain ⟨a, ha, haeq⟩ := htrans ω₁ (g • ω₁) hω₁ hgω
    have hmem : a⁻¹ * g ∈ H ⊓ rightConjugate H b := by
      rw [hD]
      refine Subgroup.mem_inf.2 ⟨H.mul_mem (H.inv_mem (hAH ha)) hg, ?_⟩
      rw [MulAction.mem_stabilizer_iff, mul_smul, ← haeq, inv_smul_smul]
    have : g = a * (a⁻¹ * g) := by group
    rw [this]
    exact Subgroup.mul_mem_sup ha hmem
  ·
    obtain ⟨m, hm1, hm⟩ := h.exists_card_eq
    rw [hm]
    exact Nat.even_pow.2 ⟨even_two, by omega⟩
  ·
    rw [hD]
    obtain ⟨a₀, ha₀, hω₁eq⟩ := h.exists_pt hω₁
    have e1 : H = (MulAction.stabilizer X (Point.base A)).map (MulAut.conj a₀).toMonoidHom := by
      rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj, smul_base_of_mem ha₀]
    have e2 : MulAction.stabilizer X ω₁ =
        (MulAction.stabilizer X (h.pt 1)).map (MulAut.conj a₀).toMonoidHom := by
      rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj, h.smul_pt, mul_one, ← hω₁eq]
    rw [e1, e2, ← Subgroup.map_inf_eq _ _ _ (MulAut.conj a₀).injective,
      Subgroup.card_map_of_injective (MulAut.conj a₀).injective, Point.stabilizer_base,
      h.stabilizer_pt_one]
    exact h.odd_card_normalizer_inf

theorem exists_mulEquiv_psl2_of_faithful [Finite X] (hfaith : FaithfulSMul X (Point A))
    (hq : 4 ≤ Nat.card A) :
    ∃ n : ℕ, 2 ≤ n ∧ Nat.card A = 2 ^ n ∧ Nonempty (X ≃* PSL2BinaryMatrixGroup n) := by
  classical
  obtain ⟨b, hb, hb1⟩ := h.symm.exists_ne_one
  obtain ⟨L, hLn, q, hLodd, ⟨f, hqf⟩, hq2, hmodel⟩ :=
    suzuki _ _ _ b (h.hypothesisA hfaith hq hb hb1)
  have hLtop : L = ⊤ := h.eq_top_of_odd_index hLodd
  let eT : X ≃* L := Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hLtop.symm)
  rcases hmodel with ⟨k, hk0, -, eL, -, eΩ, -, -⟩ | ⟨k, hk0, -, hsz⟩ |
    ⟨E, hEfield, hEfin, J, hJ, hEcard, hfix, hpsu⟩
  ·
    have hcard : Nat.card A = 2 ^ k := by
      have h1 := Nat.card_congr eΩ
      rw [h.card_point, Projectivization.card_of_finrank_two _ _ (Module.finrank_fin_fun _),
        GaloisField.card 2 k hk0] at h1
      omega
    refine ⟨k, ?_, hcard, ⟨eT.trans eL⟩⟩
    by_contra hlt
    interval_cases k <;> simp_all
  ·
    exfalso
    obtain ⟨eL, -⟩ := hsz
    obtain ⟨x, hx⟩ := RankOne.exists_orderOf_eq_four_suzuki hk0
    apply h.orderOf_ne_four ((eT.trans eL).symm x)
    rw [MulEquiv.orderOf_eq, hx]
  ·
    exfalso
    let _ := hEfield
    obtain ⟨eL, -⟩ := hpsu
    let e : X ≃* ProjectiveSpecialUnitaryMatrixGroup J := eT.trans eL
    rcases External.huppert_II_10_12 J q hEcard hfix hJ with
      ⟨-, -, -, -, -, -, ⟨R, -, -, -, -, -, -, -, hRcard, -, hcommcard, -⟩, -⟩
    have hRp : IsPGroup 2 R := IsPGroup.of_card (n := f * 3) (by rw [hRcard, hqf, ← pow_mul])
    have hRX : IsPGroup 2 (R.map e.symm.toMonoidHom) := hRp.map _
    have hcomm : ∀ x y : R, x * y = y * x := by
      intro x y
      apply Subtype.ext
      apply e.symm.injective
      have := h.commute_of_isPGroup hRX ⟨x, x.2, rfl⟩ ⟨y, y.2, rfl⟩
      simpa using this.eq
    have hcenter : Subgroup.center R = ⊤ := by
      rw [eq_top_iff]
      intro z _
      rw [Subgroup.mem_center_iff]
      intro g
      exact hcomm g z
    rw [(commutator_eq_bot_iff_center_eq_top R).2 hcenter, Subgroup.card_bot] at hcommcard
    omega

end IsElemAbRankOne

end CFSG.Timmesfeld

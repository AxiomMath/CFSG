module

public import CFSG.RankThree.GF2n.Smith81.S81NLift2
public import CFSG.RankThree.GF2n.Smith81.S81NTheta
public import CFSG.RankThree.GF2n.Smith81.OrthStmt

public section

namespace CFSG.RankThree.GF2n.Smith81.E3LCond

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G] {M Q Z X : Subgroup G} {x : G} {K : Type} [Field K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ}

section ThmA
variable [Finite G] [CharP K 2]

theorem isConj_of_rootPt (hD : GlobalModelData M Q Z γ M₀) (hs : Sit M Q Z X x) {d : G}
    (hdQ : d ∈ Q) (hd0 : M₀.π d ≠ 0) (hroot : RootPt M₀ (M₀.π d)) : IsConj x d := by
  rcases hroot with h0 | ⟨A, hA, hAQ, -, a, haA, hae⟩
  · exact absurd h0 hd0
  obtain ⟨g, rfl⟩ := hA
  have haQ : a ∈ Q := hAQ haA
  have haZ : a ∉ Z := fun h => hd0 (by rw [← hae]; exact (M₀.π_ker a haQ).mpr h)
  obtain ⟨w, hw⟩ : ∃ w : G, w = a⁻¹ * d := ⟨_, rfl⟩
  have hwZ : w ∈ Z := by rw [hw]; exact (Tim79.QuadModel.pi_eq_iff M₀ haQ hdQ).mp hae
  have hdw : a * w = d := by rw [hw, mul_inv_cancel_left]
  obtain ⟨q, -, hq⟩ := GM.exists_comm hD haQ haZ hwZ
  have hwsq : w ^ 2 = 1 := Z_sq hs.hyp hwZ
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hwsq)
  have hqa : q * a * q⁻¹ = w⁻¹ * a := by
    rw [← hq, commutatorElement_def]
    group
  have hqd : q * a * q⁻¹ = d := by
    rw [hqa, hwinv, Z_central hs.hyp hwZ haQ, hdw]
  obtain ⟨z, hz⟩ : ∃ z : G, z = g⁻¹ * a * g := ⟨_, rfl⟩
  have hzZ : z ∈ Z := by rw [hz]; exact mem_conjSubgroup.mp haA
  have hza : g * z * g⁻¹ = a := by rw [hz]; group
  have hz1 : z ≠ 1 := by
    intro h1
    apply haZ
    have ha1 : a = 1 := by rw [← hza, h1, mul_one, mul_inv_cancel]
    rw [ha1]
    exact Z.one_mem
  obtain ⟨g', hX⟩ := hs.conj
  have hxX : x ∈ conjSubgroup g' Z := by rw [← hX]; exact hs.mem
  obtain ⟨z', hz'⟩ : ∃ z' : G, z' = g'⁻¹ * x * g' := ⟨_, rfl⟩
  have hz'Z : z' ∈ Z := by rw [hz']; exact mem_conjSubgroup.mp hxX
  have hz'1 : z' ≠ 1 := by
    intro h1
    apply hs.ne_one
    have hxz' : g' * z' * g'⁻¹ = x := by rw [hz']; group
    rw [← hxz', h1, mul_one, mul_inv_cancel]
  obtain ⟨m, -, hm⟩ := Z_isConj hs.hyp hzZ hz1 hz'Z hz'1
  have hAd : IsConj a d := isConj_iff.mpr ⟨q, hqd⟩
  have hzaC : IsConj z a := isConj_iff.mpr ⟨g, hza⟩
  have hzz' : IsConj z z' := isConj_iff.mpr ⟨m, hm⟩
  have hxz'C : IsConj x z' := isConj_iff.mpr ⟨g'⁻¹, by rw [inv_inv]; exact hz'.symm⟩
  exact (hAd.symm.trans (hzaC.symm.trans (hzz'.trans hxz'C.symm))).symm

@[expose] def piSub (M₀ : Tim79.QuadModel Q Z K γ) (D : Subgroup G) (hDQ : D ≤ Q) :
    AddSubgroup M₀.E where
  carrier := {e | ∃ d ∈ D, M₀.π d = e}
  add_mem' := by
    rintro _ _ ⟨d₁, hd₁, rfl⟩ ⟨d₂, hd₂, rfl⟩
    exact ⟨d₁ * d₂, D.mul_mem hd₁ hd₂, M₀.π_mul d₁ (hDQ hd₁) d₂ (hDQ hd₂)⟩
  zero_mem' := ⟨1, D.one_mem, Tim79.QuadModel.pi_one M₀⟩
  neg_mem' := by
    rintro _ ⟨d, hd, rfl⟩
    exact ⟨d⁻¹, D.inv_mem hd, Tim79.QuadModel.pi_inv M₀ (hDQ hd)⟩

theorem mem_piSub {D : Subgroup G} {hDQ : D ≤ Q} {e : M₀.E} :
    e ∈ piSub M₀ D hDQ ↔ ∃ d ∈ D, M₀.π d = e := Iff.rfl

private theorem conj_H0_fix {c : G} (hc : c ∈ H0 M Z) {w : G} (hw : w ∈ Z) :
    c * w * c⁻¹ = w := by
  have h1 : w * c = c * w := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 w hw
  rw [← h1, mul_inv_cancel_right]

private theorem pi_conj_H0_eq (hs : Sit M Q Z X x) {c : G} (hc : c ∈ H0 M Z) {d y : G}
    (hdQ : d ∈ Q) (hyQ : y ∈ Q) (h : M₀.π d = M₀.π y) :
    M₀.π (c * d * c⁻¹) = M₀.π (c * y * c⁻¹) := by
  have hcM : c ∈ M := (Subgroup.mem_inf.mp hc).1
  have hcd : c * d * c⁻¹ ∈ Q := conj_mem_Q hs.hyp hcM hdQ
  have hcy : c * y * c⁻¹ ∈ Q := conj_mem_Q hs.hyp hcM hyQ
  have hw : d⁻¹ * y ∈ Z := (Tim79.QuadModel.pi_eq_iff M₀ hdQ hyQ).mp h
  refine (Tim79.QuadModel.pi_eq_iff M₀ hcd hcy).mpr ?_
  have e : (c * d * c⁻¹)⁻¹ * (c * y * c⁻¹) = c * (d⁻¹ * y) * c⁻¹ := by group
  rw [e, conj_H0_fix hc hw]
  exact hw

private theorem hfus_of_caseI (hs : Sit M Q Z X x) (hI : CaseI Q Z x) :
    ∀ z ∈ Z, IsConj x (x * z) := by
  intro z hz
  obtain ⟨q, -, hqz⟩ := hI z hz
  have hxz : x * z = z * x := mul_inv_eq_iff_eq_mul.mp (hs.x_cent (smith_1_12 hs) z hz)
  refine isConj_iff.mpr ⟨q, ?_⟩
  calc q * x * q⁻¹ = ⁅q, x⁆ * x := by rw [commutatorElement_def]; group
    _ = z * x := by rw [hqz]
    _ = x * z := hxz.symm

theorem e3l28_root_of_model12 (hs : Sit M Q Z X x) (hD : GlobalModelData M Q Z γ M₀)
    (Tx : XAct M₀ x)
    (hP1 : Cs Tx ≤ Submodule.span K {e | e ∈ Cs Tx ∧ RootPt M₀ e})
    (hQf : ∀ r ∈ Rs Tx, M₀.Qf r = 0)
    (Ufam : Set G) (hU0 : ∀ u ∈ Ufam, u ∈ H0 M Z) (hUx : ∀ u ∈ Ufam, ⁅u, x⁆ ∈ Q)
    (hUC : ∀ u ∈ Ufam, ∀ w ∈ Q, M₀.π w ∈ Cs Tx → M₀.π (u * w * u⁻¹) - M₀.π w ∈ Rs Tx)
    (hUfix : ∀ e ∈ Cs Tx, (∀ u ∈ Ufam, ∀ w ∈ Q, M₀.π w = e → M₀.π (u * w * u⁻¹) = e) →
      e ∈ Rs Tx)
    (hP2 : ∀ S : AddSubgroup M₀.E, S ≠ ⊥ → (∀ s ∈ S, s ∈ Rs Tx) →
      (∀ a b : G, a ∈ H0 M Z → b ∈ H0 M Z → ⁅a, x⁆ ∈ Q → ⁅b, x⁆ ∈ Q → ∀ y ∈ Q,
        M₀.π y ∈ S → M₀.π (⁅a, b⁆ * y * ⁅a, b⁆⁻¹) ∈ S) →
      ∃ e ∈ S, e ≠ 0 ∧ RootPt M₀ e)
    (hne : Q ⊓ QB X ≠ ⊥) : ∃ v : G, IsConj x v ∧ v ∈ Q ∧ v ∈ QB X := by
  rcases theta_dichotomy hD hs Tx hP1 with hI | hII
  · by_cases hJ : Jx Q X x = ⊥
    · exact absurd (caseI_D_bot hD hs Tx hI hJ hQf Ufam hU0 hUx hUC hUfix) hne
    · exact smith28_of_fused hs hJ (hfus_of_caseI hs hI)
  · obtain ⟨⟨d, hd⟩, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    have hd1' : d ≠ 1 := fun h => hd1 (Subtype.ext h)
    have hd0 : M₀.π d ≠ 0 := fun h0 => hd1' (D_eq_one_of_pi_eq_zero hs hd h0)
    have hS0 : piSub M₀ (Q ⊓ QB X) inf_le_left ≠ ⊥ := by
      intro hS
      have hmem : M₀.π d ∈ piSub M₀ (Q ⊓ QB X) inf_le_left :=
        mem_piSub.mpr ⟨d, hd, rfl⟩
      rw [hS, AddSubgroup.mem_bot] at hmem
      exact hd0 hmem
    have hSR : ∀ s ∈ piSub M₀ (Q ⊓ QB X) inf_le_left, s ∈ Rs Tx := by
      intro s hs'
      obtain ⟨d₀, hd₀, rfl⟩ := mem_piSub.mp hs'
      exact caseII_piD_le_R hD hs Tx hII hd₀
    have hstab : ∀ a b : G, a ∈ H0 M Z → b ∈ H0 M Z → ⁅a, x⁆ ∈ Q → ⁅b, x⁆ ∈ Q → ∀ y ∈ Q,
        M₀.π y ∈ piSub M₀ (Q ⊓ QB X) inf_le_left →
        M₀.π (⁅a, b⁆ * y * ⁅a, b⁆⁻¹) ∈ piSub M₀ (Q ⊓ QB X) inf_le_left := by
      intro a b ha0 hb0 hax hbx y hyQ hyS
      obtain ⟨d₀, hd₀, hπy⟩ := mem_piSub.mp hyS
      obtain ⟨d', hd', hπ'⟩ := commInv_piD hD hs Tx hII ha0 hax hb0 hbx hd₀
      have hcH : ⁅a, b⁆ ∈ H0 M Z := by
        rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem ha0 hb0) (inv_mem ha0)) (inv_mem hb0)
      refine mem_piSub.mpr ⟨d', hd', ?_⟩
      rw [hπ']
      exact pi_conj_H0_eq hs hcH (Subgroup.mem_inf.mp hd₀).1 hyQ hπy
    obtain ⟨e, heS, he0, hroot⟩ := hP2 _ hS0 hSR hstab
    obtain ⟨d', hd', rfl⟩ := mem_piSub.mp heS
    exact ⟨d', isConj_of_rootPt hD hs (Subgroup.mem_inf.mp hd').1 he0 hroot,
      (Subgroup.mem_inf.mp hd').1, (Subgroup.mem_inf.mp hd').2⟩

theorem e3l28_root_of_k3 [Finite K] (hs : Sit M Q Z X x) (hD : GlobalModelData M Q Z γ M₀)
    (Tx : XAct M₀ x) (hCR : Cs Tx ≤ Rs Tx) (hQ3 : ∃ r ∈ Rs Tx, M₀.Qf r ≠ 0)
    (hne : Q ⊓ QB X ≠ ⊥) : ∃ v : G, IsConj x v ∧ v ∈ Q ∧ v ∈ QB X := by
  have hI : CaseI Q Z x := caseI_of_Qf_ne hD hs Tx hQ3
  obtain ⟨⟨d, hd⟩, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hd1' : d ≠ 1 := fun h => hd1 (Subtype.ext h)
  have hR : M₀.π d ∈ Rs Tx := hCR (D_pi_mem_Cs hs Tx hd)
  have hdJ : d ∈ Jx Q X x := piD_mem_Jx hs Tx hI hd hR
  have hJ : Jx Q X x ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.mem_bot] at hdJ
    exact hd1' hdJ
  exact smith28_of_fused hs hJ (hfus_of_caseI hs hI)

end ThmA
end CFSG.RankThree.GF2n.Smith81.E3LCond

module

public import CFSG.RankThree.GF2n.Smith81.S81BNF
public import CFSG.RankThree.GF2n.Smith81.OrthStmt

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.A5Cube

variable {G : Type} [Group G]

@[expose] def E3L28CondStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B → InCaseE3L M Q Z B → ∀ (X : Subgroup G) (x : G), Sit M Q Z X x →
      Q ⊓ QB X ≠ ⊥ → ∃ v : G, IsConj x v ∧ v ∈ Q ∧ v ∈ QB X

private theorem exists_conj_of_isZConjugate' {Z A X : Subgroup G} (hA : IsZConjugate Z A)
    (hX : IsZConjugate Z X) : ∃ g : G, X = conjSubgroup g A := by
  obtain ⟨y, rfl⟩ := hA
  obtain ⟨g₀, rfl⟩ := hX
  refine ⟨g₀ * y⁻¹, ?_⟩
  rw [← conjSubgroup_mul, inv_mul_cancel_right]

private theorem exists_sit_of_isConj' {M Q Z : Subgroup G} (H : StrothHyp M Q Z) {z x : G}
    (hz : z ∈ Z) (hz1 : z ≠ 1) (hzx : IsConj z x) (hM : x ∈ M) (hQ : x ∉ Q) :
    ∃ X : Subgroup G, Sit M Q Z X x := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp hzx
  exact ⟨_, Sit.of_conj H hz hz1 hM hQ⟩

theorem smith212ENonfusedE3L_of_cond
    (hFE1 : Smith24E3LUniformStatement) (hTacit : ETacitE3LStatement) (h34 : Stroth34Statement)
    (h28a : Smith28aE3LStatement) (hcond : E3L28CondStatement) :
    Smith212ENonfusedE3LStatement := by
  intro G _ _ M Q Z B IH hc h3L z hz hz1 x hxM hxQ hzx w hw hw1 hfus
  have H : StrothHyp M Q Z := hc.ctx.hyp
  have hZQ : Z ≤ Q := H.Z_normal.1
  obtain ⟨X, hs⟩ := exists_sit_of_isConj' H hz hz1 hzx hxM hxQ
  have hQX : Q ⊓ QB X ≠ ⊥ := h28a G M Q Z B IH hc h3L X x hs
  obtain ⟨A, hAc, hAQ, hAZ, hAX, hAXne, -⟩ :=
    smith29_of_exists hs (hcond G M Q Z B IH hc h3L X x hs hQX)
  obtain ⟨y, hAy, hQBA, -⟩ := hAc.QB_eq H
  have hcA : SmithECfg (conjSubgroup y M) (conjSubgroup y Q) A (conjSubgroup y B) := by
    rw [hAy]
    exact hc.conj y
  have h3LA : InCaseE3L (conjSubgroup y M) (conjSubgroup y Q) A (conjSubgroup y B) := by
    rw [hAy]
    exact h3L.conj y
  have hHA := hcA.ctx.hyp
  have hXz : IsZConjugate Z X := hs.conj
  have hZz : IsZConjugate Z Z := IsZConjugate.self Z
  have hXQ : X ≤ QB A := (hAc.le_QB_iff H hXz).mpr hAX
  have hZQA : Z ≤ QB A := (hAc.le_QB_iff H hZz).mpr (by rw [H.QB_Z]; exact hAQ)
  have hx1 : x ≠ 1 := hs.ne_one
  have hxw1 : x * w ≠ 1 := by
    intro h
    apply hxQ
    rw [eq_inv_of_mul_eq_one_left h]
    exact Q.inv_mem (hZQ hw)
  obtain ⟨D, hDz, hxwD⟩ := exists_isZConjugate_mem hz (hzx.trans hfus)
  have hDQ : D ≤ QB A :=
    hAc.le_QB_of_mem H hDz hxw1 hxwD ((QB A).mul_mem (hXQ hs.mem) (hZQA hw))
  have hDA : D ≠ A := by
    intro h
    have h1 : x * w ∈ Q := hAQ (h ▸ hxwD)
    apply hxQ
    simpa using Q.mul_mem h1 (Q.inv_mem (hZQ hw))
  have hXc : Ctx (conjSubgroup y M) (conjSubgroup y Q) A X :=
    ⟨hHA, exists_conj_of_isZConjugate' hAc hXz, by rw [← hQBA]; exact hXQ, hAXne.symm⟩
  have hZc : Ctx (conjSubgroup y M) (conjSubgroup y Q) A Z :=
    ⟨hHA, exists_conj_of_isZConjugate' hAc hZz, by rw [← hQBA]; exact hZQA, hAZ.symm⟩
  have hDc : Ctx (conjSubgroup y M) (conjSubgroup y Q) A D :=
    ⟨hHA, exists_conj_of_isZConjugate' hAc hDz, by rw [← hQBA]; exact hDQ, hDA⟩
  have hne : Z ⊔ A ≠ X ⊔ A := by
    intro h
    have hx' : x ∈ Z ⊔ A := h ▸ (Subgroup.mem_sup_left hs.mem : x ∈ X ⊔ A)
    exact hxQ ((sup_le hZQ hAQ : Z ⊔ A ≤ Q) hx')
  have hZX : Z ≤ QB X :=
    le_QB_of_sum_mem_E3L hFE1 hTacit h34 IH hcA h3LA hXc hZc hDc hs.mem hw hx1 hw1 hxwD hxw1 hne
  have hbot := Z_inf_QB_eq_bot hs (smith_1_12 hs)
  have hmem : w ∈ Z ⊓ QB X := ⟨hw, hZX hw⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hw1 hmem

end CFSG.RankThree.GF2n.Smith81

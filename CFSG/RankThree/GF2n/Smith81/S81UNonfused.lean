module

public import CFSG.RankThree.GF2n.Smith81.S81BTacitFree
public import CFSG.RankThree.GF2n.Smith81.S81UCond
public import CFSG.RankThree.GF2n.Smith81.S81UMinusc
public import CFSG.RankThree.GF2n.Smith81.S81UConj
public import CFSG.RankThree.GF2n.Smith81.S81BConj

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom

variable {G : Type} [Group G]

theorem le_QB_of_sum_mem_E3U [Finite G]
    (hFE1 : Smith24E3UUniformStatement)
    (hTacit : ETacitE3UStatement) (h34 : Stroth34Statement)
    {M Q Z B : Subgroup G} (IH : Smith1981Below (Nat.card G)) (hc : SmithECfg M Q Z B)
    (h3U : InCaseE3U M Q Z B) {X Y D : Subgroup G} (hX : Ctx M Q Z X) (hY : Ctx M Q Z Y)
    (hD : Ctx M Q Z D) {x y : G} (hx : x ∈ X) (hy : y ∈ Y) (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hxy : x * y ∈ D) (hxy1 : x * y ≠ 1) (hne : Y ⊔ Z ≠ X ⊔ Z) : Y ≤ QB X := by
  obtain ⟨K, _, _, _, γ, M₀, hg⟩ := stroth_globalModelData hc.ctx.hyp
  obtain ⟨F, _, _, _, f, hF, e, ψ, φ, d⟩ := hFE1 G M Q Z B IH hc.toRemCfg h3U K γ M₀ hg
  have hw : Width Q Z 10 := by
    obtain ⟨t, -, h⟩ := h3U
    exact h.1
  have hTac := hTacit G M Q Z B IH hc h3U X hX
  have hcard : Nat.card ↥(Q ⊓ QB X) = Nat.card Z ^ (10 + 1) :=
    (stroth_3_5 h34 hX hw (by norm_num) hTac.1 hTac.2).2.2.2
  obtain ⟨hMG, hML⟩ := u6MinuscStatement_holds F f hF K e
  exact d.le_QB_of_sum_mem hg hMG hML hX hY hD hcard hx hy hx1 hy1 hxy hxy1 hne

private theorem exists_conj_of_isZConjugate_U {Z A X : Subgroup G} (hA : IsZConjugate Z A)
    (hX : IsZConjugate Z X) : ∃ g : G, X = conjSubgroup g A := by
  obtain ⟨y, rfl⟩ := hA
  obtain ⟨g₀, rfl⟩ := hX
  refine ⟨g₀ * y⁻¹, ?_⟩
  rw [← conjSubgroup_mul, inv_mul_cancel_right]

private theorem exists_sit_of_isConj_U {M Q Z : Subgroup G} (H : StrothHyp M Q Z) {z x : G}
    (hz : z ∈ Z) (hz1 : z ≠ 1) (hzx : IsConj z x) (hM : x ∈ M) (hQ : x ∉ Q) :
    ∃ X : Subgroup G, Sit M Q Z X x := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp hzx
  exact ⟨_, Sit.of_conj H hz hz1 hM hQ⟩

theorem smith212ENonfusedE3U_of_cond
    (hFE1 : Smith24E3UUniformStatement)
    (hTacit : ETacitE3UStatement) (h34 : Stroth34Statement)
    (h28a : Smith28aE3UStatement) (hcond : E3U28CondStatement) :
    Smith212ENonfusedE3UStatement := by
  intro G _ _ M Q Z B IH hc h3U z hz hz1 x hxM hxQ hzx w hw hw1 hfus
  have H : StrothHyp M Q Z := hc.ctx.hyp
  have hZQ : Z ≤ Q := H.Z_normal.1
  obtain ⟨X, hs⟩ := exists_sit_of_isConj_U H hz hz1 hzx hxM hxQ
  have hQX : Q ⊓ QB X ≠ ⊥ := h28a G M Q Z B IH hc h3U X x hs
  obtain ⟨A, hAc, hAQ, hAZ, hAX, hAXne, -⟩ :=
    smith29_of_exists hs (hcond G M Q Z B IH hc h3U X x hs hQX)
  obtain ⟨y, hAy, hQBA, -⟩ := hAc.QB_eq H
  have hcA : SmithECfg (conjSubgroup y M) (conjSubgroup y Q) A (conjSubgroup y B) := by
    rw [hAy]
    exact hc.conj y
  have h3UA : InCaseE3U (conjSubgroup y M) (conjSubgroup y Q) A (conjSubgroup y B) := by
    rw [hAy]
    exact h3U.conj y
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
    ⟨hHA, exists_conj_of_isZConjugate_U hAc hXz, by rw [← hQBA]; exact hXQ, hAXne.symm⟩
  have hZc : Ctx (conjSubgroup y M) (conjSubgroup y Q) A Z :=
    ⟨hHA, exists_conj_of_isZConjugate_U hAc hZz, by rw [← hQBA]; exact hZQA, hAZ.symm⟩
  have hDc : Ctx (conjSubgroup y M) (conjSubgroup y Q) A D :=
    ⟨hHA, exists_conj_of_isZConjugate_U hAc hDz, by rw [← hQBA]; exact hDQ, hDA⟩
  have hne : Z ⊔ A ≠ X ⊔ A := by
    intro h
    have hx' : x ∈ Z ⊔ A := h ▸ (Subgroup.mem_sup_left hs.mem : x ∈ X ⊔ A)
    exact hxQ ((sup_le hZQ hAQ : Z ⊔ A ≤ Q) hx')
  have hZX : Z ≤ QB X :=
    le_QB_of_sum_mem_E3U hFE1 hTacit h34 IH hcA h3UA hXc hZc hDc hs.mem hw hx1 hw1 hxwD hxw1 hne
  have hbot := Z_inf_QB_eq_bot hs (smith_1_12 hs)
  have hmem : w ∈ Z ⊓ QB X := ⟨hw, hZX hw⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hw1 hmem

end CFSG.RankThree.GF2n.Smith81

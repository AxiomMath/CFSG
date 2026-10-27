
module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
public import CFSG.Quasithin.Background.A3Structure36BBasic

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.A36B

theorem map_center_mulEquiv' {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') :
    (Subgroup.center G).map e.toMonoidHom = Subgroup.center G' := by
  ext h
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro h'
    obtain ⟨g', rfl⟩ := e.surjective h'
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hg g']
  · intro hh
    refine ⟨e.symm h, Subgroup.mem_center_iff.2 fun g => e.injective ?_, by simp⟩
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_center_iff.1 hh (e g)

theorem isQuasisimple_of_mulEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (h : CFSG.IsQuasisimple G) : CFSG.IsQuasisimple G' :=
  h.of_mulEquiv e.symm

theorem isPOnePlusTwo_of_mulEquiv {p : ℕ} {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : IsPOnePlusTwo p G) : IsPOnePlusTwo p H := by
  obtain ⟨hext, hcard, hpow⟩ := h
  have hcen := map_center_mulEquiv' e
  let eQ : G ⧸ Subgroup.center G ≃* H ⧸ Subgroup.center H := QuotientGroup.congr _ _ e hcen
  have hel : CFSG.IsElementaryAbelian p (G ⧸ Subgroup.center G) :=
    CFSG.IsExtraspecial.quotient_elementary_abelian p G
  have hnt : Nontrivial (G ⧸ Subgroup.center G) := CFSG.IsExtraspecial.quotient_nontrivial p G
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [← hcen, Subgroup.card_map_of_injective e.injective]
    exact CFSG.IsExtraspecial.center_order_p p G
  · refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
    · apply eQ.symm.injective
      rw [map_mul, map_mul]
      exact mul_comm' _ _
    · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun a => eQ.symm.injective ?_
      rw [map_pow, map_one]
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.1 hel.exponent_dvd_p _
  · exact eQ.injective.nontrivial
  · rw [← hcard]
    exact (Nat.card_congr e.toEquiv).symm
  · intro x
    apply e.symm.injective
    rw [map_pow, map_one]
    exact hpow _

def multFinTwoEquiv (n : ℕ) :
    Multiplicative (Fin 2 → ZMod n) ≃* Multiplicative (ZMod n) × Multiplicative (ZMod n) where
  toFun f := (Multiplicative.ofAdd (Multiplicative.toAdd f 0),
    Multiplicative.ofAdd (Multiplicative.toAdd f 1))
  invFun p := Multiplicative.ofAdd ![Multiplicative.toAdd p.1, Multiplicative.toAdd p.2]
  left_inv f := by
    ext i
    fin_cases i <;> rfl
  right_inv p := by
    refine Prod.ext ?_ ?_ <;> rfl
  map_mul' f g := by
    refine Prod.ext ?_ ?_ <;> rfl

theorem eq_of_isSL2 {p q : ℕ} (hp : p.Prime) (hq : q.Prime) {G : Type} [Group G]
    (h1 : IsSL2 p G) (h2 : IsSL2 q G) : p = q := by
  have := Fact.mk hp
  have := Fact.mk hq
  obtain ⟨e1⟩ := h1
  obtain ⟨e2⟩ := h2
  have hcard := Nat.card_congr (e1.symm.trans e2).toEquiv
  rw [CFSG.GorensteinWalter.sl2_card_formula (ZMod p), CFSG.GorensteinWalter.sl2_card_formula
    (ZMod q), Nat.card_zmod, Nat.card_zmod] at hcard
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have hp4 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
  have hq4 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq.pos
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have h3 : p * (p ^ 2 - 1) < q * (q ^ 2 - 1) := by
      have h4 : p ^ 2 - 1 < q ^ 2 - 1 := by
        have : p ^ 2 < q ^ 2 := Nat.pow_lt_pow_left hlt (by norm_num)
        omega
      exact Nat.mul_lt_mul'' hlt h4
    omega
  · have h3 : q * (q ^ 2 - 1) < p * (p ^ 2 - 1) := by
      have h4 : q ^ 2 - 1 < p ^ 2 - 1 := by
        have : q ^ 2 < p ^ 2 := Nat.pow_lt_pow_left hlt (by norm_num)
        omega
      exact Nat.mul_lt_mul'' hlt h4
    omega

variable {X : Type} [Group X]

theorem subnormal_eq_top_or_le_radical (h : A36BHyp X) {K : Subgroup X} (hK : K.IsSubnormal) :
    K = ⊤ ∨ K ≤ CFSG.solvableRadical X := by
  induction hK with
  | top => exact Or.inl rfl
  | step H K hle _ hN ih =>
    rcases ih with rfl | hKO
    · have hHn : H.Normal := by
        have := (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hN
        rw [top_le_iff, Subgroup.normalizer_eq_top_iff] at this
        exact this
      by_cases hHtop : H = ⊤
      · exact Or.inl hHtop
      · exact Or.inr (normal_le_radical h hHtop)
    · exact Or.inr (hle.trans hKO)

theorem layer_le_fitting (h : A36BHyp X) : CFSG.layer X ≤ CFSG.fittingSubgroup X := by
  have hfin : Finite X := h.finite
  refine sSup_le fun K hK => ?_
  exfalso
  obtain ⟨hQ, hsub⟩ := hK
  rcases subnormal_eq_top_or_le_radical h hsub with rfl | hle
  · have hQX : CFSG.IsQuasisimple X := isQuasisimple_of_mulEquiv Subgroup.topEquiv hQ
    have hnt : Nontrivial X := CFSG.LocalCores.isQuasisimple_nontrivial hQX
    have hperf : Group.IsPerfect X := hQX.1
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hQX
      (inferInstance : (CFSG.fittingSubgroup X).Normal) with htop | hcen
    · have hnil : Group.IsNilpotent (⊤ : Subgroup X) := htop ▸ inferInstance
      have : Group.IsNilpotent X := Group.nilpotent_of_mulEquiv (Subgroup.topEquiv)
      exact Group.IsPerfect.not_isNilpotent X this
    · exact h.noncentral hcen
  · have hsolvO : Group.IsSolvable ↥(CFSG.solvableRadical X) := A3.solvableRadical_isSolvable
    have hsolv : Group.IsSolvable ↥K :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
        (Subgroup.inclusion_injective _)
    have hnt : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hQ
    have hperf : Group.IsPerfect ↥K := hQ.1
    exact Group.IsPerfect.not_isSolvable ↥K hsolv

theorem generalizedFitting_eq_fitting (h : A36BHyp X) :
    CFSG.generalizedFitting X = CFSG.fittingSubgroup X :=
  sup_eq_left.2 (layer_le_fitting h)

end CFSG.Quasithin.A36B

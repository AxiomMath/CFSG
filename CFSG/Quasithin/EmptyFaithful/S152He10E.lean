module

public import CFSG.Quasithin.EmptyFaithful.S152He10D
public import CFSG.Quasithin.EmptyFaithful.S152He10A
public import CFSG.Quasithin.EmptyFaithful.S152He10B
public import CFSG.Quasithin.EmptyFaithful.S152He9N

public section

namespace CFSG.Quasithin.He10

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.He9
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem isChi0Block_of_sylow (hK : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h36 : A36ForSQTK) (h129 : ASC129StatementUsed G)
    {G₀ R M₁ L : Subgroup G} (hyp : HypC23 G₀ R M₁) (hchar : CharTwo G₀) (hne : pCoreOf 2 G₀ ≠ ⊥)
    (hL : L ∈ cComp G₀) (hRL : R ≤ Subgroup.normalizer (L : Set G)) (hnot : ¬ L ≤ M₁)
    (hsyl : IsSylowTwoOf R (R ⊔ L)) : IsChi0Block (R ⊔ L) L := by
  rcases isChi0Block_or_all_A3 h129 hyp hchar hL hRL hsyl with h | ⟨r, Lb, hLb, hprod⟩
  · exact h
  · exact absurd (le_of_all_A3 hK hs hnab h36 hyp hne hL hRL hsyl Lb hLb hprod) hnot

@[expose] def Input15204A314 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S K L : Subgroup G), IsSQTKIn X → IsSylowTwoOf S X →
    L ∈ cComp X → IsChi0Block X L → K ∈ lFamily S → K ≤ L →
    Nonempty (OTwoQuot K ≃* ↥(alternatingGroup (Fin 5))) → K = L

theorem pow_five_of_odd {T Mc M H K₁ K₂ : Subgroup G} {π : ↥H →* W5}
    (c : Ctx15204 T Mc M H K₁ K₂ π) : ∀ y ∈ yOf152 T Mc M, Odd (orderOf y) → y ^ 5 = 1 := by
  intro y hy hodd
  have hmul := Subgroup.relIndex_mul_card (H := pCoreOf 2 (yOf152 T Mc M)) (K := yOf152 T Mc M)
  rw [c.y.relIndex_five, inf_eq_left.mpr (pCoreOf_le 2 _)] at hmul
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 ((pCoreOf_isPGroup 2 (yOf152 T Mc M)))
  rw [ha] at hmul
  have hdvd : orderOf y ∣ 5 * 2 ^ a := by
    have := orderOf_dvd_natCard (⟨y, hy⟩ : ↥(yOf152 T Mc M))
    rw [← hmul, Subgroup.orderOf_mk] at this
    exact this
  have hcop : Nat.Coprime (orderOf y) (2 ^ a) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)
  exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_right hdvd)

theorem input15204BranchA_of_a314 (h36 : A36ForSQTK)
    (h129 : ∀ (G : Type) [Group G] [Finite G], ASC129StatementUsed G)
    (hA314 : Input15204A314) : Input15204BranchA := by
  intro G _ _ T Mc M H K₁ K₂ π c Lc tail hsyl
  have hK := c.hs.qtfe
  have hLG : Lc ≤ g0Of T Mc M K₁ := le_of_mem_cComp tail.comp
  have hNG : g0Of T Mc M K₁ ≤ Subgroup.normalizer (Lc : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLG).1 tail.normal
  have hRL : rOf T Mc M K₁ ≤ Subgroup.normalizer (Lc : Set G) := tail.hyp.radical.1.trans hNG
  have hχ := isChi0Block_of_sylow hK.qtke hK.simple hK.nonabelian h36 (h129 G) tail.hyp
    tail.charTwo tail.ne_bot tail.comp hRL tail.not_le hsyl
  have hχ' : IsChi0Block (g0Of T Mc M K₁) Lc :=
    ⟨⟨hχ.1.1, hLG, (isSubnormal_iff_subgroupOf hLG).mp (subnormal_of_mem_cComp tail.comp)⟩, hχ.2⟩
  have hB : K₁ ∈ lFamily (sOf T K₁) :=
    cComp_mem_of_le c.wr.comp₁ le_sup_left (sup_le c.wr.le₁ (S_le_T.trans c.hT.1))
  have hKL : K₁ = Lc := hA314 G (g0Of T Mc M K₁) (sOf T K₁) K₁ Lc tail.hyp.sqtk tail.sylow
    tail.comp hχ' hB tail.le c.quot_K₁
  subst hKL
  have hYK : yOf152 T Mc M ≤ Subgroup.normalizer (K₁ : Set G) := Y_le_G₀.trans hNG
  have hRK : IsSylowTwoOf (rOf T Mc M K₁ ⊓ K₁) K₁ :=
    A4.isSylowTwoOf_inf_normal hsyl le_sup_right (sup_le hRL Subgroup.le_normalizer)
  exact commutator_le_of_five (K := K₁) K₁_le_G₀ tail.normal c.quot_K₁ R_isPGroup Y_le_G₀
    Y_le_normalizer_R hYK hRK (yOf152_eq_oTwoUpper T Mc M) (pow_five_of_odd c)

end CFSG.Quasithin.He10

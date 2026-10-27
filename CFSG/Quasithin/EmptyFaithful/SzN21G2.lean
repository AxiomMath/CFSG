module

public import CFSG.Quasithin.EmptyFaithful.SzN21Sp4
public import CFSG.Quasithin.EmptyFaithful.A38c4G2Center
public import CFSG.Quasithin.EmptyFaithful.LRed3Four
public import CFSG.Quasithin.EmptyFaithful.SBd8G2
public import CFSG.Quasithin.EmptyFaithful.SzN20E

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.QuasithinUnique.Setup.X6 CFSG.Quasithin.SteinbergBS CFSG.Quasithin.SBd8

namespace SzN21

section Pair

@[expose] def pairHom (G : Type) [CommGroup G] : G × G →* (Fin 2 → G) where
  toFun p := ![p.1, p.2]
  map_one' := by
    ext i
    fin_cases i <;> rfl
  map_mul' p q := by
    ext i
    fin_cases i <;> rfl

theorem pairHom_injective (G : Type) [CommGroup G] : Function.Injective (pairHom G) := by
  intro p q h
  exact Prod.ext (congrFun h 0) (congrFun h 1)

end Pair

section Torus

variable {F : Type} [Field F]

theorem torusGroup_le_adjoint : torusGroup Tag.G2 F ≤ adjointGroup Tag.G2 F :=
  torusGroup_le_borelGroup.trans borelGroup_le_adjointGroup'

@[expose] noncomputable def torusG2 (F : Type) [Field F] : Fˣ × Fˣ →* ↥(adjointGroup Tag.G2 F) :=
  (Subgroup.inclusion (torusGroup_le_adjoint (F := F))).comp
    ((torusCoordHom Tag.G2 F).comp (pairHom Fˣ))

theorem torusG2_injective : Function.Injective (torusG2 F) := by
  intro p q h
  have h1 : torusCoordHom Tag.G2 F (pairHom Fˣ p) = torusCoordHom Tag.G2 F (pairHom Fˣ q) :=
    Subgroup.inclusion_injective (torusGroup_le_adjoint (F := F)) h
  exact pairHom_injective Fˣ (torusCoordHom_injective_of_mul_eq_one cartan_mul_cartanInv_G2 h1)

end Torus

section G2

variable
  {F : Type} [Field F]

theorem torusG2_mem_normalizer [Finite F] (p : Fˣ × Fˣ) :
    torusG2 F p ∈ Subgroup.normalizer
      (((posUnipotent Tag.G2 F).subgroupOf (adjointGroup Tag.G2 F) :
        Subgroup ↥(adjointGroup Tag.G2 F)) : Set ↥(adjointGroup Tag.G2 F)) := by
  rw [g2Std_normalizer_eq, Subgroup.mem_subgroupOf]
  exact torusGroup_le_borelGroup (torusCoordHom Tag.G2 F (pairHom Fˣ p)).2

theorem rbProp_posUnipotent_G2 [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n) :
    RBProp ((posUnipotent Tag.G2 F).subgroupOf (adjointGroup Tag.G2 F)) := by
  have hF4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    apply g2Std_normalizer_ne_top hF4
    rw [h0]
    exact Subgroup.normalizer_eq_top_iff.mpr inferInstance
  · intro R hUR hRs
    exact g2Std_solvable_overgroup_le_normalizer hF4 R hUR hRs
  · rintro ⟨y, hy, hy3⟩
    have hdvd : 3 ∣ Nat.card ↥(Subgroup.normalizer
        (((posUnipotent Tag.G2 F).subgroupOf (adjointGroup Tag.G2 F) :
          Subgroup ↥(adjointGroup Tag.G2 F)) : Set ↥(adjointGroup Tag.G2 F))) := by
      have := orderOf_dvd_natCard (⟨y, hy⟩ : ↥(Subgroup.normalizer
        (((posUnipotent Tag.G2 F).subgroupOf (adjointGroup Tag.G2 F) :
          Subgroup ↥(adjointGroup Tag.G2 F)) : Set ↥(adjointGroup Tag.G2 F))))
      rwa [Subgroup.orderOf_mk, hy3] at this
    rw [g2Std_card_normalizer, mul_comm] at hdvd
    obtain ⟨ω, hω⟩ := exists_units_orderThree_of_dvd (three_dvd_sub_one_of_dvd_mul hF hdvd)
    exact exists_elemAbelian_nine (torusG2 F) torusG2_injective torusG2_mem_normalizer hω |>
      fun ⟨E, hE, hE3, hEe, hEc⟩ => ⟨E, hE, hE3, hEe, hEc⟩

theorem rankTwoBorel_g2 (hG2 : FactG2Cayley) {Ω : Type} [Group Ω] {X S : Subgroup Ω}
    {K : Type} [Field K] [Finite K] {e : ℕ} (hK : Nat.card K = 2 ^ e) (he : 2 ≤ e)
    (iso : ↥X ≃* ↥(CFSG.Open.quasithinG2 K)) (hS : IsSylowTwoOf S X) :
    S ≠ ⊥ ∧
      (∀ R : Subgroup Ω, S ≤ R → R ≤ X → Group.IsSolvable ↥R →
        R ≤ Subgroup.normalizer (S : Set Ω)) ∧
      ((∃ y ∈ Subgroup.normalizer (S : Set Ω) ⊓ X, orderOf y = 3) →
        ∃ E : Subgroup Ω, E ≤ Subgroup.normalizer (S : Set Ω) ⊓ X ∧ IsPGroup 3 E ∧
          (∀ x ∈ E, x ^ 3 = 1) ∧ Nat.card E = 9) := by
  have hcp : CharP K 2 := CFSG.Quasithin.Vol2.KGNat.charP_two_of_card (by omega) hK
  have h4 : 2 < Nat.card K := by
    rw [hK]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  obtain ⟨c, hc0, hc1⟩ := CFSG.Quasithin.Vol2.KGNat.exists_ne_zero_ne_one (K := K) h4
  have hZ : Subgroup.center ↥(CFSG.Open.quasithinG2 K) = ⊥ := by
    rw [CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup]
    exact CFSG.Quasithin.A318Excl.center_cayleyGroup_eq_bot hc0 hc1
  have hG : IsG2 2 e ↥(CFSG.Open.quasithinG2 K) :=
    IsG2.of_mulEquiv ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)
      (hG2 K e he hK)
  have hX : IsG2 2 e ↥X := IsG2.of_mulEquiv iso.symm hG
  obtain ⟨-, F', hFf, hFfin, hFcp, hF', ⟨ψ₀⟩⟩ := exists_mulEquiv_G2_model hX
  have : Finite (ModGL Tag.G2 F') := finite_modGL
  exact rankTwoBorel_of_model ψ₀ hS g2Std_isSylowTwoOf (rbProp_posUnipotent_G2 hF' he)

theorem rankTwoBorel_holds (hG2 : FactG2Cayley) : SzN20.RankTwoBorel := by
  intro Ω _ _ X S e he hfam hS
  rcases hfam with ⟨K, hKf, hKfin, hK, ⟨iso⟩⟩ | ⟨K, hKf, hKfin, hK, ⟨iso⟩⟩ |
    ⟨K, hKf, hKfin, hK, ⟨iso⟩⟩
  · exact rankTwoBorel_sl3 hK he iso hS
  · exact rankTwoBorel_sp4 hK he iso hS
  · exact rankTwoBorel_g2 hG2 hK he iso hS

end G2

end SzN21

end CFSG.Quasithin

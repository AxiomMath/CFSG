module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4Y1Gen
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4D1Base
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4D1Cv
public import CFSG.Quasithin.EmptyFaithful.T1515Der2

public section

namespace CFSG.Quasithin.S15223P4.Y1

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]
  {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}

theorem card_N (c : P4Ctx T Mc M H B₀ I X) :
    Nat.card ↥(M ⊓ I) = 6 * Nat.card ↥(M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) := by
  have hMV := le_normalizer_V154 T Mc M
  set ρ := A4.actionOn (V154 T Mc M) M hMV with hρ
  have hkerC : ρ.ker = (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)).subgroupOf M := by
    ext x
    rw [MonoidHom.mem_ker, A4.actionOn_eq_one_iff hMV x, Subgroup.mem_subgroupOf]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have hker : ρ.ker ≤ (M ⊓ I).subgroupOf M := by
    rw [hkerC]
    intro x hx
    exact ⟨x.2, (cv_le_inf152 c.setting c.inputs hx).2⟩
  have e1 := D1.card_eq_card_map_mul_card_ker' ρ (Q := (M ⊓ I).subgroupOf M) hker
  have h1 : ((M ⊓ I).subgroupOf M).map ρ = autOn (M ⊓ I) (V154 T Mc M) :=
    (SBd8.autOn_eq_map_actionOn hMV inf_le_left).symm
  rw [h1, D1.card_autOn_inf c, hkerC] at e1
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : M ⊓ I ≤ M)).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left :
      M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) ≤ M)).toEquiv] at e1
  exact e1

theorem inf_le_inf_N (c : P4Ctx T Mc M H B₀ I X) : X ⊓ M ≤ M ⊓ I := fun _ hx =>
  ⟨hx.2, c.X_le_I hx.1⟩

theorem le_normalizer_inf (hN : D1.P4N1 T Mc M H B₀ I X) :
    M ⊓ I ≤ Subgroup.normalizer ((X ⊓ M : Subgroup G) : Set G) := fun _ hg =>
  Subgroup.inf_normalizer_le_normalizer_inf ⟨hN.normal hg.2, Subgroup.le_normalizer hg.1⟩

theorem not_dvd_relIndex (c : P4Ctx T Mc M H B₀ I X) (hN : D1.P4N1 T Mc M H B₀ I X)
    (h3 : IsThreePrimeGroup (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G))) :
    ¬ 3 ∣ (X ⊓ M).relIndex (M ⊓ I) := by
  intro hdvd
  have h3' : ¬ 3 ∣ Nat.card ↥(M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) := h3
  have e := Subgroup.relIndex_mul_card (H := X ⊓ M) (K := M ⊓ I)
  rw [inf_of_le_left (inf_le_inf_N c), card_N c] at e
  have h3K : 3 ∣ Nat.card ↥(X ⊓ M) := ⟨_, hN.card_MX⟩
  have h9 : 9 ∣ 6 * Nat.card ↥(M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) := by
    rw [← e]
    exact Nat.mul_dvd_mul hdvd h3K
  omega

theorem mem_inf_of_orderOf (c : P4Ctx T Mc M H B₀ I X) (hN : D1.P4N1 T Mc M H B₀ I X)
    (h3 : IsThreePrimeGroup (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G))) {x : G}
    (hx : x ∈ M ⊓ I) {k : ℕ} (hk : orderOf x = 3 ^ k) : x ∈ X ⊓ M :=
  mem_of_orderOf_pow_of_not_dvd_relIndex (inf_le_inf_N c) (le_normalizer_inf hN) Nat.prime_three
    (not_dvd_relIndex c hN h3) hx hk

theorem pow_three_of_orderOf (c : P4Ctx T Mc M H B₀ I X) (hN : D1.P4N1 T Mc M H B₀ I X) {x : G}
    (hx : x ∈ X ⊓ M) {k : ℕ} (hk : orderOf x = 3 ^ k) : x ^ 3 = 1 := by
  have hdvd := Subgroup.orderOf_dvd_natCard (X ⊓ M) hx
  rw [hN.card_MX] at hdvd
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2)).mp
    (c.sylow.isPGroup.to_le (inf_le_left : sOf152 T Mc M B₀ ⊓ X ≤ sOf152 T Mc M B₀))
  rw [ha, hk] at hdvd
  have hcop : Nat.Coprime (3 ^ k) (2 ^ a) := Nat.Coprime.pow k a (by norm_num)
  have h3k : orderOf x ∣ 3 := by
    rw [hk]
    exact hcop.dvd_of_dvd_mul_right hdvd
  exact orderOf_dvd_iff_pow_eq_one.mp h3k

theorem oPrimeResidualOf_le_inf (c : P4Ctx T Mc M H B₀ I X) (hN : D1.P4N1 T Mc M H B₀ I X)
    (h3 : IsThreePrimeGroup (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G))) :
    oPrimeResidualOf 3 (M ⊓ I) ≤ X ⊓ M :=
  oPrimeResidualOf_le_of_forall fun _ hx _ hk => mem_inf_of_orderOf c hN h3 hx hk

theorem S_le_normalizer (c : P4Ctx T Mc M H B₀ I X) :
    sOf152 T Mc M B₀ ≤ Subgroup.normalizer (oPrimeResidualOf 3 (M ⊓ I) : Set G) :=
  c.S_le_N.trans (Subgroup.le_normalizer.trans (normalizer_le_normalizer_oPrimeResidualOf1516 3 _))

theorem exists_orderOf_three (hN : D1.P4N1 T Mc M H B₀ I X) :
    ∃ y ∈ X ⊓ M, orderOf y = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3MX : 3 ∣ Nat.card ↥(X ⊓ M) := ⟨_, hN.card_MX⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(X ⊓ M)) 3 h3MX
  exact ⟨y, y.2, by rw [← hy, Subgroup.orderOf_coe]⟩

end CFSG.Quasithin.S15223P4.Y1

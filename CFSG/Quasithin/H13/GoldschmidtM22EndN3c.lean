module

public import CFSG.Quasithin.H13.GoldschmidtM22EndN3b
public import CFSG.Quasithin.H13.GoldschmidtM22EndN3a

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

structure Case2 (L V : Subgroup G) (g : G) : Prop where
  relIndex_four : ((conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) ⊓
    Subgroup.centralizer (V : Set G)).relIndex
      (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) = 4
  elemAbelianMod : IsElemAbelianMod (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G))
    ((conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) ⊓ Subgroup.centralizer (V : Set G))
  not_le : ¬ autOn (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) V ≤ autOn L V
  exists_D : ∃ D : Subgroup G, D ≤ V ⊔ conjSubgroup V g ∧
    V ⊔ conjSubgroup V g ≤ Subgroup.normalizer (D : Set G) ∧ E2.IsExtraspecialPlus 2 D ∧
    ∃ φ : ↥(V ⊔ conjSubgroup V g) →* Equiv.Perm (Fin 3), Function.Surjective φ ∧
      φ.ker = D.subgroupOf (V ⊔ conjSubgroup V g)
  inter_eq : V ⊓ conjSubgroup V g =
    ⁅conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G),
      V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G)⁆
  card_inter : Nat.card ↥(V ⊓ conjSubgroup V g) = 2
  pCore_le : pCoreOf 2 (V ⊔ conjSubgroup V g) ≤ oTwoUpper (V ⊔ conjSubgroup V g)

theorem case2_of_hyps (h626 : Stmt6_2_6) (h : Hyp6Sec2 G T M L V) (g : G)
    (hA : (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)).relIndex (conjSubgroup V g) = 2)
    (hU : (V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G)).relIndex V = 2)
    (hnot : ¬ IsPGroup 2 ↥(V ⊔ conjSubgroup V g)) : Case2 L V g := by
  rcases h626 G T M L V h g hA hU with ⟨-, -, -, -, hpg⟩ | h2
  · exact absurd hpg hnot
  · exact ⟨h2.1, h2.2.1, h2.2.2.1, h2.2.2.2.1, h2.2.2.2.2.1, h2.2.2.2.2.2.1, h2.2.2.2.2.2.2⟩

namespace PsiData

variable (P : PsiData T L V 3) (h : Hyp6Sec2 G T M L V)

include P h in
theorem exists_pair (hZ : Nat.card (quasithinOmegaOneCenter T) = 2) (h6210 : Stmt6_2_10) :
    ∃ a g : ↥(HH T), (a : G) ∈ V ∧ (a : G) ∉ CHU T L V ∧ ¬ Commute (P.ψ g) (P.ψ a) := by
  obtain ⟨a, haV, haC⟩ := exists_a h hZ h6210
  have hτ2 := Equiv.Perm.card_support_eq_two.mpr (P.swap_norm a haV haC).1
  obtain ⟨ρ, hρ⟩ := perm3_exists_noncomm _ hτ2
  obtain ⟨g, hg⟩ := P.surj ρ
  refine ⟨a, g, haV, haC, fun hc => hρ ?_⟩
  rw [← hg]
  exact hc

include P h in
theorem case2 (hZ : Nat.card (quasithinOmegaOneCenter T) = 2) (h621 : Stmt6_2_1)
    (h626 : Stmt6_2_6) (h6210 : Stmt6_2_10) (h6211 : Stmt6_2_11) (a g : ↥(HH T))
    (haV : (a : G) ∈ V) (haC : (a : G) ∉ CHU T L V) (hg : ¬ Commute (P.ψ g) (P.ψ a)) :
    Case2 L V (g : G) := by
  have hτ2 : (P.ψ a).support.card = 2 :=
    Equiv.Perm.card_support_eq_two.mpr (P.swap_norm a haV haC).1
  have hg' : P.ψ g * P.ψ a ≠ P.ψ a * P.ψ g := fun hc => hg hc
  obtain ⟨hn1, hn2⟩ := perm3_noncomm_conj _ _ hτ2 hg'
  have hnc₁ : ¬ Commute (P.ψ (g⁻¹ * a * g)) (P.ψ a) := by
    rw [map_mul, map_mul, map_inv]
    exact hn1
  have hnc₂ : ¬ Commute (P.ψ (g * a * g⁻¹)) (P.ψ a) := by
    rw [map_mul, map_mul, map_inv]
    exact hn2
  obtain ⟨hA, hU⟩ := hyp626_of_noncomm P h hZ h621 h6210 h6211 a g haV haC hnc₁ hnc₂
  refine case2_of_hyps h626 h (g : G) hA hU fun hpg => ?_
  have hc₁V : ((g⁻¹ * a * g : ↥(HH T)) : G) ∈ conjSubgroup V (g : G) := by
    refine mem_conjSubgroup_iff.mpr ?_
    have e : (g : G) * ((g : G)⁻¹ * (a : G) * (g : G)) * (g : G)⁻¹ = (a : G) := by group
    exact e ▸ haV
  have hmem : (a : G) * ((g⁻¹ * a * g : ↥(HH T)) : G) ∈ V ⊔ conjSubgroup V (g : G) :=
    Subgroup.mul_mem_sup haV hc₁V
  obtain ⟨k, hk⟩ := hpg ⟨(a : G) * ((g⁻¹ * a * g : ↥(HH T)) : G), hmem⟩
  have hk' : (a * (g⁻¹ * a * g) : ↥(HH T)) ^ 2 ^ k = 1 :=
    Subtype.ext (by simpa using congrArg Subtype.val hk)
  have hψk : (P.ψ a * ((P.ψ g)⁻¹ * P.ψ a * P.ψ g)) ^ 2 ^ k = 1 := by
    have := congrArg P.ψ hk'
    simpa [map_mul, map_inv, map_pow] using this
  obtain ⟨h3, h1⟩ := perm3_prod_order _ _ hτ2 hg'
  have hord : orderOf (P.ψ a * ((P.ψ g)⁻¹ * P.ψ a * P.ψ g)) = 3 := orderOf_eq_prime h3 h1
  have hdvd : 3 ∣ 2 ^ k := hord ▸ orderOf_dvd_of_pow_eq_one hψk
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
  omega

end PsiData

end CFSG.Quasithin.H13.GM22

module

public import CFSG.RankThree.GF2n.Stroth80.Sec35

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement


theorem sec7H_conj {G : Type} [Group G] [Finite G] (x : G) (V Z B' : Subgroup G)
    (hxV : conjSubgroup x V = V) (hxZ : conjSubgroup x Z = Z) :
    (V ⊓ QB (conjSubgroup x B')) ⊔ Z = conjSubgroup x ((V ⊓ QB B') ⊔ Z) := by
  rw [conjSubgroup_sup', conjSubgroup_inf, hxV, hxZ, QB_conj]

theorem sec7H_inf_conj_le {G : Type} [Group G] {V Z Q : Subgroup G} (hZV : Z ≤ V)
    (hVQ : ∀ v ∈ V, ∀ q ∈ Q, ⁅v, q⁆ ∈ Z) {p : G} (hp : p ∈ Q) (T : Subgroup G) :
    V ⊓ conjSubgroup p T ≤ (V ⊓ T) ⊔ Z := by
  intro v hv
  obtain ⟨hvV, hvT⟩ := Subgroup.mem_inf.mp hv
  have hy : p⁻¹ * v * p ∈ T := CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mp hvT
  have hz : ⁅v⁻¹, p⁻¹⁆ ∈ Z := hVQ v⁻¹ (V.inv_mem hvV) p⁻¹ (Q.inv_mem hp)
  have hyeq : p⁻¹ * v * p = v * ⁅v⁻¹, p⁻¹⁆ := by
    simp only [commutatorElement_def]
    group
  have hyV : p⁻¹ * v * p ∈ V := by
    rw [hyeq]
    exact V.mul_mem hvV (hZV hz)
  have hdec : p⁻¹ * v * p * (⁅v⁻¹, p⁻¹⁆)⁻¹ = v := by
    simp only [commutatorElement_def]
    group
  have hmem : p⁻¹ * v * p * (⁅v⁻¹, p⁻¹⁆)⁻¹ ∈ (V ⊓ T) ⊔ Z :=
    Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨hyV, hy⟩) (Z.inv_mem hz)
  rwa [hdec] at hmem

theorem sec7H_eq_of_le_ZB {G : Type} [Group G] [Finite G] {M Q Z B' B'' : Subgroup G}
    (hc' : Ctx M Q Z B') (hc'' : Ctx M Q Z B'') (V : Subgroup G) (hZV : Z ≤ V)
    (hVQ : ∀ v ∈ V, ∀ p ∈ Q, ⁅v, p⁆ ∈ Z) (hle : B'' ≤ Z ⊔ B') :
    (V ⊓ QB B'') ⊔ Z = (V ⊓ QB B') ⊔ Z := by
  obtain ⟨p, hpQ, hp⟩ := hc'.exists_conj_of_le_ZB hc'' hle
  have hQB : QB B'' = conjSubgroup p (QB B') := by
    rw [← hp, QB_conj]
  have hQB' : QB B' = conjSubgroup p⁻¹ (QB B'') := by
    rw [hQB, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  refine le_antisymm (sup_le ?_ le_sup_right) (sup_le ?_ le_sup_right)
  · rw [hQB]
    exact sec7H_inf_conj_le hZV hVQ hpQ (QB B')
  · rw [hQB']
    exact sec7H_inf_conj_le hZV hVQ (Q.inv_mem hpQ) (QB B'')

end CFSG.RankThree.GF2n.Stroth80

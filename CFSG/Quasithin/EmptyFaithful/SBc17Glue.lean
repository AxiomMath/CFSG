module

public import CFSG.Quasithin.EmptyFaithful.SBc17BlkTop
public import CFSG.Quasithin.EmptyFaithful.S1469CaseA0
public import CFSG.Quasithin.EmptyFaithful.SBc17W
public import CFSG.Quasithin.EmptyFaithful.SBc14Pair
public import CFSG.Quasithin.EmptyFaithful.SBc17FixG1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

namespace SBc17

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem false_of_inner_l2_block (S : Setting146 G T M) {K₂ J : Subgroup G} {n : ℕ} (hn : 1 < n)
    (hshort : IsShort2 J) (hlin : IsLin2Type J n) (hB : IsBorelOfBlock J (J ⊓ g12_14615 T K₂))
    (hZB : quasithinOmegaOneCenter T ≤ J ⊓ g12_14615 T K₂) (hJX : J ≤ g2_14615 K₂)
    (hJle : ¬ J ≤ g12_14615 T K₂) : False := by
  obtain ⟨z, hz, hz1⟩ := S.exists_ne_one_Z
  have hG₁ : mcOf T = Subgroup.centralizer ({z} : Set G) := S.mcOf_eq_centralizer hz hz1
  have hzB : z ∈ (J ⊓ g12_14615 T K₂) ⊓
      Subgroup.centralizer ((J ⊓ g12_14615 T K₂ : Subgroup G) : Set G) := by
    refine ⟨hZB hz, Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩
    have hb' : b ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [← hG₁]
      exact hb.2.1
    exact (Subgroup.mem_centralizer_iff.mp hb' z (Set.mem_singleton z)).symm
  have hzJ := centralizer_block_of_borel_proved hn hshort hlin hB hzB
  have hJG₁ : J ≤ mcOf T := by
    intro x hx
    rw [hG₁, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (Subgroup.mem_centralizer_iff.mp hzJ x hx).symm
  exact hJle (le_inf hJG₁ hJX)


section Outer

variable {p : ℕ} {H : Subgroup G} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem false_of_outer_l2_block (h36 : A36ForSQTK) (S : Setting146 G T M) {PQ : Subgroup G}
    (hp5 : p = 5) (hred : IsRedCE T M H PQ p) (hdec : IsDecP T M H p H₀ H₁ H₂ t)
    (hCz : conjClosure (oTwoUpper H) (mcOf T) = oTwoUpper H) {J : Subgroup G}
    (hX : SQTKGroup ↥(g2_14615 (oTwoUpper H₂))) (hJc : J ∈ cComp (g2_14615 (oTwoUpper H₂)))
    (hJq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J))
    (hK₂N : oTwoUpper H₂ ≤ Subgroup.normalizer (J : Set G))
    (hK₂c : ⁅J, oTwoUpper H₂⁆ ≤ pCoreOf 2 J) (hKJ : oTwoUpper H ≤ Subgroup.normalizer (J : Set G))
    {n : ℕ} (hn : 1 < n) (hlin : IsLin2Type J n)
    (hB : IsBorelOfBlock J (J ⊓ g12_14615 T (oTwoUpper H₂)))
    (hout : ∃ k ∈ oTwoUpper H₁ ⊔ oTwoUpper H₂, orderOf k = 5 ∧ k ∉ innerSub J) : False := by
  obtain ⟨k, hkK, hk5, hkn⟩ := hout
  have hKX : oTwoUpper H = oTwoUpper H₁ ⊔ oTwoUpper H₂ := hdec.oTwoUpper_eq S hred
  have hkK' : k ∈ oTwoUpper H := hKX ▸ hkK
  have hW := isPGroup_oTwoUpper_inf_of_not_innerSub h36 S hp5 hred hdec hCz hX hJc hJq hK₂N hK₂c hKJ
    (fun h => hkn (h hkK))
  have hKG := mcOf_le_normalizer_oTwoUpper hCz
  have hkJ : k ∈ Subgroup.normalizer (J : Set G) := hKJ hkK'
  refine hkn (mem_innerSub_of_commutator_two_proved hn hlin hB hkJ hW ?_ ?_)
  · intro b hb
    exact SBc14.mem_normalizer_inf (hKG hb.2.1) (Subgroup.le_normalizer hb.1)
  · intro b hb
    have hbN : b ∈ Subgroup.normalizer (oTwoUpper H : Set G) := hKG hb.2.1
    refine ⟨?_, ?_⟩
    · have h1 : b * k * b⁻¹ ∈ oTwoUpper H := (Subgroup.mem_normalizer_iff.mp hbN k).mp hkK'
      exact (oTwoUpper H).mul_mem h1 ((oTwoUpper H).inv_mem hkK')
    · have h2 : k * b⁻¹ * k⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp hkJ b⁻¹).mp (J.inv_mem hb.1)
      have e : ⁅b, k⁆ = b * (k * b⁻¹ * k⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact J.mul_mem hb.1 h2

end Outer

end SBc17

end CFSG.Quasithin

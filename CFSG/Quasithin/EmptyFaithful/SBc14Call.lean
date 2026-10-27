module

public import CFSG.Quasithin.EmptyFaithful.SBc14Top
public import CFSG.Quasithin.EmptyFaithful.S146P11
public import CFSG.Quasithin.EmptyFaithful.SBc13J1Main
public import CFSG.Quasithin.EmptyFaithful.SBc13J3
public import CFSG.Quasithin.EmptyFaithful.SBc13JRaMain
public import CFSG.Quasithin.EmptyFaithful.SBc13JM5Main
public import CFSG.Quasithin.EmptyFaithful.S146C26Solv

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

namespace SBc14

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ K₁ K₂ : Subgroup G}
  {t s : G}

theorem callSite_facts (h5 : Stage1461Five) (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (hmax : PMaximal T M p) (hdec : IsDecP T M H p H₀ H₁ H₂ t)
    (hctx : Ctx15 T M H p H₁) (hset : Setup14615 T M H H₁ H₂ K₁ K₂ s)
    (hG₂ : ¬ g2_14615 K₂ ≤ mcOf T) :
    HypC23 (g2_14615 K₂) (pCoreOf 2 (mcOf T)) (g12_14615 T K₂) ∧ CharTwo (g2_14615 K₂) ∧
      pCoreOf 2 (g2_14615 K₂) ≤ g12_14615 T K₂ := by
  obtain ⟨hHyp, -⟩ := hypC23_of_ctx S h5 hred hdec hset hG₂
  have hchar := charTwo_g2 S h5 hred hdec hset
  have hFchar : CharTwo (oTwoFIn (g2_14615 K₂)) := charTwo_oTwoFIn_of_charTwo hchar
  have hA3 : Input14615A3P :=
    input14615A3P_proved (input14615HypP_proved h5) (input14615KzP_proved h5)
  have hF₂ : oTwoFIn (g2_14615 K₂) ≤ g12_14615 T K₂ := by
    obtain ⟨r, Lb, hLb, hprod⟩ := c2_6_two_solv_P16 hHyp hFchar
    have hLbM : ∀ i, Lb i ≤ g12_14615 T K₂ := fun i =>
      hA3 G T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hctx K₁ K₂ s hset hG₂ (Lb i) (hLb i).1
        (hLb i).2
    intro x hx
    obtain ⟨m, hm, y, hy, hxy⟩ := hprod x hx
    rw [hxy]
    refine (g12_14615 T K₂).mul_mem hm.1 (Subgroup.list_prod_mem _ fun z hz => ?_)
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    exact hLbM i (hy i)
  exact ⟨hHyp, hchar, C2Six.pCoreOf_le_oTwoFIn.trans hF₂⟩

theorem input14615JP_proved (h5 : Stage1461Five) (h36 : A36ForSQTK) (h38 : A38ForSQTK) :
    Input14615JP := by
  intro G _ _ T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hctx K₁ K₂ s hset hG₂ J hJc hJq hJle
  obtain ⟨hHyp, -, hPcore⟩ := callSite_facts h5 S hred hmax hdec hctx hset hG₂
  have hp5 : p = 5 := hctx.1
  have hp : p.Prime := hred.prime
  have hX : SQTKGroup ↥(g2_14615 K₂) := hHyp.sqtk
  have hK₂G₁ : K₂ ≤ mcOf T := hset.le_mcOf S hred
  have hK₂X : K₂ ≤ g2_14615 K₂ := Subgroup.le_normalizer
  have hK₂₁₂ : K₂ ≤ g12_14615 T K₂ := le_inf hK₂G₁ hK₂X
  have hJK₂ : ¬ J ≤ K₂ := fun h => hJle (h.trans hK₂₁₂)
  have hJX : J ≤ g2_14615 K₂ := le_of_mem_cComp hJc
  have hJperf : ⁅J, J⁆ = J := perfect_of_mem_cComp hJc
  have hK₂N : K₂ ≤ Subgroup.normalizer (J : Set G) :=
    SBc13.normalizer_le_of_normal_of_not_le hK₂X le_rfl hJc hJK₂
  have hK₂c : ⁅J, K₂⁆ ≤ pCoreOf 2 J :=
    SBc13.commutator_le_pCore_of_normal hK₂X le_rfl hJc hJq hJK₂
  have hKz5 : K₁ ⊔ K₂ ≤ Subgroup.closure {x | x ∈ K₁ ⊔ K₂ ∧ orderOf x = 5} := by
    have := kz_le_closure_five_14615 S hdec hp5 hset
    rwa [hset.kz] at this
  have hKodd : K₁ ⊔ K₂ ≤ oTwoUpper (K₁ ⊔ K₂) :=
    hKz5.trans ((Subgroup.closure_le _).mpr fun x hx =>
      Subgroup.subset_closure ⟨hx.1, by rw [hx.2]; decide⟩)
  have hKzG₂ : K₁ ⊔ K₂ ≤ g2_14615 K₂ := by
    rw [← hset.kz]
    exact kz_le_g2_14615 hdec hset
  have hKzN : K₁ ⊔ K₂ ≤ Subgroup.normalizer (J : Set G) :=
    SBc13.le_normalizer_of_odd_gen h38 hX hJc hKzG₂ hKodd
  have hK₁N : K₁ ≤ Subgroup.normalizer (J : Set G) := le_sup_left.trans hKzN
  have hWG : pCoreOf 2 J ≤ mcOf T :=
    (SBc13.pCoreOf_le_pCoreOf_of_subnormal hJc).trans (hPcore.trans inf_le_left)
  have hnc : ¬ ⁅J, K₁⁆ ≤ pCoreOf 2 J := by
    intro h1
    apply SBc13.not_commutator_kz_le_pCore S h5 hp5 hred hdec hset hJX hJle hWG
    refine Subgroup.commutator_le.mpr fun x hx k hk => ?_
    have hk' : k ∈ ((K₁ ⊔ K₂ : Subgroup G) : Set G) := hk
    rw [Subgroup.coe_mul_of_left_le_normalizer_right K₁ K₂ (le_sup_left.trans hKzG₂)] at hk'
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := Set.mem_mul.mp hk'
    have e : ⁅x, k₁ * k₂⁆ = ⁅x, k₁⁆ * (k₁ * ⁅x, k₂⁆ * k₁⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    refine (pCoreOf 2 J).mul_mem (h1 (Subgroup.commutator_mem_commutator hx hk₁)) ?_
    have hn : k₁ ∈ Subgroup.normalizer (pCoreOf 2 J : Set G) :=
      normalizer_le_normalizer_pCoreOf 2 J (hK₁N hk₁)
    exact (Subgroup.mem_normalizer_iff.mp hn _).mp
      (hK₂c (Subgroup.commutator_mem_commutator hx hk₂))
  refine ⟨SBc13.commutator_eq_of_not_le_pCore hJperf hJq hK₁N hnc, ?_⟩
  obtain ⟨k, hkK, hk5'⟩ := hdec.swap.exists_order_p_P14 hp hred.odd
  have hk5 : orderOf k = 5 := by rw [hk5', hp5]
  have hk₂ : k ∈ K₂ := hset.oTwo₂ hkK
  exact (BlueprintB2.pRank_eq_open_pRank 5 J).le.trans
    (SBc13.pRank_le_one_of_commutes h36 hX hJc hJq (hK₂X hk₂) hk5 (hK₂N hk₂) fun x hx =>
      hK₂c (Subgroup.commutator_mem_commutator hx hk₂))

end SBc14

end CFSG.Quasithin

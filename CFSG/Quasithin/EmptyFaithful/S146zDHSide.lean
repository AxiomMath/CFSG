module

public import CFSG.Quasithin.EmptyFaithful.S146zDPerf
public import CFSG.Quasithin.Vol2.Ch1Comm

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace CFSG.Quasithin.ThreeD

section HSide

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem perfect_le_Kp (S : Setting146 G T M) (c23 : Conc14623 T M)
    {K Kp U₁ U₂ : Subgroup G} {s : G} (cK : ThreeC.CCtx T M K U₁ U₂ s)
    (hKp : Kp ∈ cComp (mcOf T)) (hcomps : ∀ L ∈ cComp (mcOf T), L = K ∨ L = Kp)
    (hkz : perfectCore (mcOf T) = K ⊔ Kp)
    (hc22K : ⁅⁅uOfL22 T M, K⁆, Kp⁆ = ⊥) (hc22Kp : ⁅⁅uOfL22 T M, Kp⁆, K⁆ = ⊥)
    {a : G} (ha : a ∈ U₁ ⊔ U₂) (haZ : a ∉ Zz)
    {P : Subgroup G} (hPH : P ≤ mcOf T) (hP : ⁅P, P⁆ = P)
    (hfix : ∀ p ∈ P, p * a * p⁻¹ = a) : P ≤ Kp := by
  classical
  have hK := cK.hKc
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hUab : IsElemAbelian 2 (uOfL22 T M) := S.lemma_14_5_15_two hG
  have hUc : ∀ x ∈ uOfL22 T M, ∀ y ∈ uOfL22 T M, x * y = y * x := fun x hx y hy =>
    isElemAbelian_comm hUab hx hy
  have hHU : mcOf T ≤ Subgroup.normalizer (uOfL22 T M : Set G) := le_normalizer_conjClosure _ _
  have hUN : uOfL22 T M ≤ Subgroup.normalizer (Zz : Set G) := S.conjClosure_le_normalizer_Z hG
  have hKH : K ≤ mcOf T := le_of_mem_cComp hK
  have hKpH : Kp ≤ mcOf T := le_of_mem_cComp hKp
  have hHZ : mcOf T ≤ Subgroup.normalizer (Zz : Set G) := fun h hh => by
    rw [S.normalizer_Z]; exact hh
  have hZc : mcOf T ≤ Subgroup.centralizer (Zz : Set G) := by
    rw [← normalizer_eq_centralizer_of_card_eq_two S.card_Z]; exact hHZ
  have hspan : cCompSpan (mcOf T) ≤ K ⊔ Kp := sSup_le fun L hL => by
    rcases hcomps L hL with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  have hnormK : cCompSpan (mcOf T) ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_cCompSpan hK)).mp
      (cComp_normal_span_of_le hK).2
  have hnormKp : cCompSpan (mcOf T) ≤ Subgroup.normalizer (Kp : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_cCompSpan hKp)).mp
      (cComp_normal_span_of_le hKp).2
  have hKspan : K ≤ cCompSpan (mcOf T) := le_cCompSpan hK
  have hKpspan : Kp ≤ cCompSpan (mcOf T) := le_cCompSpan hKp
  have hsupspan : K ⊔ Kp ≤ cCompSpan (mcOf T) := sup_le hKspan hKpspan
  have hKpcent : Kp ≤ Subgroup.centralizer ((U₁ ⊔ U₂ : Subgroup G) : Set G) := by
    rw [← cK.hsup]
    refine Subgroup.le_centralizer_iff.mpr (sup_le ?_ ?_)
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc22K
    · exact fun z hz => Subgroup.mem_centralizer_iff.mpr fun k hk =>
        (Subgroup.mem_centralizer_iff.mp (hZc (hKpH hk)) z hz).symm
  have hKcentp : K ≤ Subgroup.centralizer ((⁅uOfL22 T M, Kp⁆ ⊔ Zz : Subgroup G) : Set G) := by
    refine Subgroup.le_centralizer_iff.mpr (sup_le ?_ ?_)
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc22Kp
    · exact fun z hz => Subgroup.mem_centralizer_iff.mpr fun k hk =>
        (Subgroup.mem_centralizer_iff.mp (hZc (hKH hk)) z hz).symm
  have hPKp : P ≤ K ⊔ Kp := by
    have := le_perfectCore_of_perfect hPH hP
    rwa [hkz] at this
  have hPK : P ≤ Subgroup.normalizer (K : Set G) := hPKp.trans (hsupspan.trans hnormK)
  have hKp₁ : Kp ≤ Subgroup.centralizer (U₁ : Set G) :=
    hKpcent.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left))
  have hPU₁ : P ≤ Subgroup.normalizer (U₁ : Set G) :=
    hPKp.trans (sup_le cK.hSec.KU fun k hk => Subgroup.centralizer_le_normalizer _ (hKp₁ hk))
  have hPZ : P ≤ Subgroup.normalizer (Zz : Set G) := hPH.trans hHZ
  have hPU : P ≤ Subgroup.normalizer (uOfL22 T M : Set G) := hPH.trans hHU
  have hfixZ : ∀ p ∈ P, p * a * p⁻¹ * a⁻¹ ∈ Zz := fun p hp => by
    rw [hfix p hp]; simp
  have htriv := cK.perf_trivial_UK S hP hPK hPU hPZ hPU₁ ha haZ hfixZ
  have hKKp : K ≤ Subgroup.normalizer (Kp : Set G) := hKspan.trans hnormKp
  have hpQ : ∀ p ∈ P, p ∈ pCoreOf 2 (mcOf T) ⊔ Kp := by
    intro p hp
    have hp' : p ∈ ((K ⊔ Kp : Subgroup G) : Set G) := hPKp hp
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hKKp] at hp'
    obtain ⟨k, hk, kp, hkp, rfl⟩ := Set.mem_mul.mp hp'
    suffices hkQ : k ∈ pCoreOf 2 (mcOf T) from Subgroup.mul_mem_sup hkQ hkp
    rw [← S.lemma_14_5_15_four hG]
    refine ⟨hKH hk, hHZ (hKH hk), fun u hu => ?_⟩
    obtain ⟨a', ha', b, hb, c, hc, rfl⟩ := exists_decomp_two S c23 hcomps hK hKp hu
    have hEU : ∀ x ∈ uOfL22 T M, k * x * k⁻¹ ∈ uOfL22 T M := fun x hx =>
      (Subgroup.mem_normalizer_iff.mp (hHU (hKH hk)) x).mp hx
    have ha'U : a' ∈ uOfL22 T M := commutator_sup_le_U (T := T) (M := M) hKH ha'
    have hbU : b ∈ uOfL22 T M := commutator_sup_le_U (T := T) (M := M) hKpH hb
    have hcU : c ∈ uOfL22 T M := cuOf_le T M hc
    have hbcU : b * c ∈ uOfL22 T M := (uOfL22 T M).mul_mem hbU hcU
    have hexp : k * (a' * (b * c)) * k⁻¹ * (a' * (b * c))⁻¹ =
        (k * a' * k⁻¹ * a'⁻¹) * ((k * b * k⁻¹ * b⁻¹) * (k * c * k⁻¹ * c⁻¹)) := by
      rw [comm_mul_of_abelian hUc hEU ha'U hbcU, comm_mul_of_abelian hUc hEU hbU hcU]
    rw [hexp]
    have h1 : k * a' * k⁻¹ * a'⁻¹ ∈ Zz := by
      have ha'UK : a' ∈ U₁ ⊔ U₂ := cK.hsup ▸ ha'
      have h2 := htriv (k * kp) hp a' ha'UK
      have h3 : kp * a' * kp⁻¹ = a' := by
        have := Subgroup.mem_centralizer_iff.mp (hKpcent hkp) a' ha'UK
        calc kp * a' * kp⁻¹ = (a' * kp) * kp⁻¹ := by rw [this]
          _ = a' := by group
      have e : (k * kp) * a' * (k * kp)⁻¹ * a'⁻¹ = k * (kp * a' * kp⁻¹) * k⁻¹ * a'⁻¹ := by group
      rw [e, h3] at h2
      exact h2
    have h2 : k * b * k⁻¹ * b⁻¹ ∈ Zz := by
      have := Subgroup.mem_centralizer_iff.mp (hKcentp hk) b hb
      have e1 : k * b * k⁻¹ * b⁻¹ = 1 := by
        calc k * b * k⁻¹ * b⁻¹ = (b * k) * k⁻¹ * b⁻¹ := by rw [this]
          _ = 1 := by group
      rw [e1]; exact Subgroup.one_mem _
    have h3 : k * c * k⁻¹ * c⁻¹ ∈ Zz := by
      have := (mem_cuOf.mp hc).2.2 k (hKH hk)
      have e1 : k * c * k⁻¹ * c⁻¹ = (c * k * c⁻¹ * k⁻¹)⁻¹ := by group
      rw [e1]; exact Subgroup.inv_mem _ this
    exact Subgroup.mul_mem _ h1 (Subgroup.mul_mem _ h2 h3)
  have hQN : Kp ≤ Subgroup.normalizer (pCoreOf 2 (mcOf T) : Set G) :=
    hKpH.trans (le_normalizer_pCoreOf 2 (mcOf T))
  have hcore := (cComp_commutator_perfectCore hKp (pCoreOf_le 2 (mcOf T))
    (isSolvable_pCoreOf_two (mcOf T)) hQN).2
  have hPcore : P ≤ perfectCore (Kp ⊔ pCoreOf 2 (mcOf T)) :=
    le_perfectCore_of_perfect (fun p hp => by rw [sup_comm]; exact hpQ p hp) hP
  rwa [hcore] at hPcore

end HSide

end CFSG.Quasithin.ThreeD

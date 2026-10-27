module

public import CFSG.Quasithin.EmptyFaithful.S143Setting
public import CFSG.Quasithin.EmptyFaithful.S143Pre

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G}

theorem normalizer_Z_eq_centralizer_of_hyp (h : Hyp1281Two G T M L) :
    Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) =
      Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
  le_antisymm (normalizer_le_centralizer_of_card_two h.card_omegaOneCenter)
    (Subgroup.centralizer_le_normalizer _)

theorem uOfL22_le_T_of_hyp (h : Hyp1281Two G T M L) : uOfL22 T M ≤ T := by
  have := (h.almostSpecialHyp h.isHz_normalizer).G22_three.1
  rw [normalizer_Z_eq_centralizer_of_hyp h] at this
  exact this

theorem sylow_LT_of_hyp (h : Hyp1281Two G T M L) : IsSylowTwoOf T (L ⊔ T) :=
  (h.almostSpecialHyp h.isHz_normalizer).sylow_LT

theorem sylow_M_of_hyp (h : Hyp1281Two G T M L) : IsSylowTwoOf T M := by
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo h.sylow
  have := isSylowTwoOf_of_sylow S (hS ▸ h.inM.2 : (S : Subgroup G) ≤ M)
  rwa [hS] at this

theorem sylow_G1_of_hyp (h : Hyp1281Two G T M L) :
    IsSylowTwoOf T (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) := by
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo h.sylow
  have hle : T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    Subgroup.le_centralizer_iff.mp ((quasithinOmegaOneCenter_le_center T).trans inf_le_right)
  have := isSylowTwoOf_of_sylow S (hS ▸ hle :
    (S : Subgroup G) ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
  rwa [hS] at this

theorem normal_i2_of_hyp (h : Hyp1281Two G T M (yOfL22 T M)) :
    M ≤ Subgroup.normalizer (iTwo T M : Set G) := by
  refine h.sup_inf_normalizer_eq.symm.le.trans (sup_le (le_normalizer_conjClosure _ _) fun c hc => ?_)
  obtain ⟨hcM, hcZ⟩ := hc
  have hcH : c ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
    rw [← normalizer_Z_eq_centralizer_of_hyp h]; exact hcZ
  have hcU : ∀ u ∈ uOfL22 T M, c * u * c⁻¹ ∈ uOfL22 T M := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure (VZ T M)
      (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) hcH) u).mp hu
  have hcL : ∀ l ∈ yOfL22 T M, c * l * c⁻¹ ∈ yOfL22 T M := fun l hl =>
    (Subgroup.mem_normalizer_iff.mp (h.normal hcM) l).mp hl
  have hcU' : ∀ u ∈ uOfL22 T M, c⁻¹ * u * c⁻¹⁻¹ ∈ uOfL22 T M := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure (VZ T M)
      (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) (inv_mem hcH)) u).mp hu
  have hcL' : ∀ l ∈ yOfL22 T M, c⁻¹ * l * c⁻¹⁻¹ ∈ yOfL22 T M := fun l hl =>
    (Subgroup.mem_normalizer_iff.mp (h.normal (inv_mem hcM)) l).mp hl
  unfold iTwo
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨fun hx => conj_mem_conjClosure hcU hcL hx, fun hx => by
    have := conj_mem_conjClosure hcU' hcL' hx
    simpa [mul_assoc] using this⟩

theorem rOf_le_T_of_hyp (h : Hyp1281Two G T M (yOfL22 T M)) : rOf T M ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm : M ≤ Subgroup.normalizer (rOf T M : Set G) :=
    (normal_i2_of_hyp h).trans (normalizer_le_normalizer_pCoreOf 2 (iTwo T M))
  have hRM : rOf T M ≤ M := by
    refine (pCoreOf_le 2 (iTwo T M)).trans ?_
    refine conjClosure_le fun l hl u hu => ?_
    have hUM : u ∈ M := h.inM.2 (uOfL22_le_T_of_hyp h hu)
    exact M.mul_mem (M.mul_mem (yOfL22_le T M hl) hUM) (M.inv_mem (yOfL22_le T M hl))
  have hRO : rOf T M ≤ pCoreOf 2 M :=
    le_pCoreOf_of_le_normalizer 2 hRM hnorm (pCoreOf_isPGroup 2 (iTwo T M))
  exact hRO.trans (pCoreOf_two_le_of_isSylowTwoOf (sylow_M_of_hyp h))

theorem qOf_le_T_of_hyp (h : Hyp1281Two G T M L) : qOf T ≤ T :=
  pCoreOf_two_le_of_isSylowTwoOf (sylow_G1_of_hyp h)

theorem rq_le_of_hyp (h : Hyp1281Two G T M (yOfL22 T M)) : rOf T M ⊔ qOf T ≤ T :=
  sup_le (rOf_le_T_of_hyp h) (qOf_le_T_of_hyp h)

end S143

end CFSG.Quasithin

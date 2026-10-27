module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.L82.Local

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace L82

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {r : ℕ} {S : Subgroup G} {E K : Subgroup G}

theorem smear_le
    (h : Counterexample p A θ) (hr : InPiTheta A θ r) (hS : IsSr p A θ r S)
    (hB : TypeB p A θ E K) {b : G} (hb : b ∈ A) (hbE : b ∉ E) {J₁ : Subgroup G}
    (hJ₁ : J₁ ∈ lcal (thetaOf θ E)) : smear J₁ (Subgroup.zpowers b) ≤ thetaOf θ A ⊔ zOf S := by
  have hE := hB.mem
  have hEA : E ≤ A := hE.1
  have hE0 : E ≠ ⊥ := h.ne_bot_of_mem_E1 hE
  have hb1 : b ≠ 1 := fun h1 => hbE (h1 ▸ one_mem E)
  have hF := h.zpowers_mem_E1 hb hb1
  have hFA : Subgroup.zpowers b ≤ A := Subgroup.zpowers_le.mpr hb
  have hFE : Subgroup.zpowers b ≠ E := fun heq => hbE (heq ▸ Subgroup.mem_zpowers b)
  have hθ := h.isFunctor.thetaOf_zpowers hb hb1
  have hΩE : IsRegFam A (kOf (thetaOf θ E)) (lcal (thetaOf θ E)) E := by
    have := isRegFam_lcal_kOf h hEA hE0
    rwa [hB.bN_eq E hE, sup_idem] at this
  have hFN : Subgroup.zpowers b ⊓ E = ⊥ := by
    rw [inf_comm]
    exact inf_eq_bot_of_not_le h.prime (h.card_zpowers hb hb1)
      (fun hle => hbE (hle (Subgroup.mem_zpowers b)))
  obtain ⟨e⟩ := hΩE.nonempty_mulEquiv_smear hFA hFN hJ₁
  obtain ⟨-, -, hs, hnc⟩ := mem_lcal_iff.mp hJ₁
  have hsimple : IsSimpleGroup ↥(smear J₁ (Subgroup.zpowers b)) := e.isSimpleGroup
  have hnonab : ¬ IsMulCommutative ↥(smear J₁ (Subgroup.zpowers b)) := fun hc =>
    hnc ((isMulCommutative_congr e).mp hc)
  have hFstar := inSubgroup_generalizedFitting_eq_self hsimple hnonab
  have hKS := h.kSetting_thetaOf hE.1 hE0
  have hKA := h.kDown_thetaOf hE.1 hE0
  have hcomp : smear J₁ (Subgroup.zpowers b) ∈ lcal (thetaOf θ E ⊓
      Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G)) := by
    rw [T515f.lcal_inf_centralizer_eq hKS hKA hFA]
    exact ⟨J₁, hJ₁, hFstar.symm⟩
  have hΩ : IsRegFam A (θ b) (lcal (θ b)) (E ⊔ Subgroup.zpowers b) := by
    have := h.isRegFam_line_of_typeB hB.toTypeBCore hF hFE
    rwa [hθ] at this
  have hne : ∀ L ∈ lcal (θ b), L ⊓ Subgroup.centralizer (E : Set G) ≠ ⊥ := by
    intro L hL hbot
    have hLE := mem_lcalA_of_mem_lcal h hB hb hbE hL
    have hEL : E ≤ Subgroup.normalizer (L : Set G) :=
      le_sup_left.trans ((hΩ.stabilizer L hL).symm.le.trans inf_le_right)
    apply hLE.2
    rw [smear_eq_inf_centralizer hEL, hbot]
    infer_instance
  have hfam := hΩ.inf_centralizer_family h.elemAbelian.1 hEA le_sup_left hne
  have hV : thetaOf θ E ⊓ Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G) =
      θ b ⊓ Subgroup.centralizer (E : Set G) := by
    rw [h.thetaOf_line_inf_centralizer hE hFA, ← hθ, h.thetaOf_line_inf_centralizer hF hEA,
      sup_comm]
  rw [hV] at hcomp
  obtain ⟨_, ⟨J, hJ, rfl⟩, hΦ⟩ := (mem_lcal_iff_of_isDirectProduct hfam.isDirectProduct).mp hcomp
  have hEJ : E ≤ Subgroup.normalizer (J : Set G) :=
    le_sup_left.trans ((hΩ.stabilizer J hJ).symm.le.trans inf_le_right)
  refine (le_inSubgroup_generalizedFitting_of_mem_lcal hΦ).trans ?_
  rw [← smear_eq_inf_centralizer hEJ]
  exact fitting_smear_le h hr hS hB hb hbE hJ

theorem kOf_inf_centralizer_le
    (h : Counterexample p A θ) (hr : InPiTheta A θ r)
    (hS : IsSr p A θ r S) (hB : TypeB p A θ E K) {b : G} (hb : b ∈ A) (hbE : b ∉ E) :
    kOf (thetaOf θ E) ⊓ Subgroup.centralizer {b} ≤ thetaOf θ A ⊔ zOf S := by
  have hE := hB.mem
  have hEA : E ≤ A := hE.1
  have hE0 : E ≠ ⊥ := h.ne_bot_of_mem_E1 hE
  have hb1 : b ≠ 1 := fun h1 => hbE (h1 ▸ one_mem E)
  have hFA : Subgroup.zpowers b ≤ A := Subgroup.zpowers_le.mpr hb
  have hΩE : IsRegFam A (kOf (thetaOf θ E)) (lcal (thetaOf θ E)) E := by
    have := isRegFam_lcal_kOf h hEA hE0
    rwa [hB.bN_eq E hE, sup_idem] at this
  have hFN : Subgroup.zpowers b ⊓ E = ⊥ := by
    rw [inf_comm]
    exact inf_eq_bot_of_not_le h.prime (h.card_zpowers hb hb1)
      (fun hle => hbE (hle (Subgroup.mem_zpowers b)))
  have hfam := hΩE.smear_family h.elemAbelian.1 hFA hFN
  rw [← centralizer_zpowers_eq_singleton, ← hfam.isDirectProduct.sSup_eq]
  refine sSup_le ?_
  rintro _ ⟨J₁, hJ₁, rfl⟩
  exact smear_le h hr hS hB hb hbE hJ₁

end L82

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

module

public import CFSG.Quasithin.Vol2.Ch11SecGBasic
public import CFSG.Quasithin.Vol2.Ch11SecGFacts
public import CFSG.Quasithin.Vol2.Ch11SecD551B
public import CFSG.Quasithin.Vol2.Ch11SecGAmal

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecG

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G]

theorem conjSub_eq_conjSubgroup (g : G) (X : Subgroup G) : conjSub g X = conjSubgroup X g⁻¹ := by
  ext x
  rw [mem_conjSub, mem_conjSubgroup_iff, inv_inv]

theorem commutator_le_of_le_normalizer {V X : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (V : Set G)) : ⁅V, X⁆ ≤ V := by
  rw [Subgroup.commutator_le]
  intro v hv x hx
  rw [commutatorElement_def]
  have h1 : x * v⁻¹ * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hX hx) _).mp (V.inv_mem hv)
  have h2 := V.mul_mem hv h1
  simpa [mul_assoc] using h2

theorem conjSub_le_conjClosure {V N : Subgroup G} {g : G} (hg : g ∈ N) :
    conjSub g V ≤ conjClosure V N := fun x hx => by
  have e : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
  rw [e]
  exact mem_conjClosure hg (mem_conjSub.mp hx)

variable [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem false_of_even (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0) (h1141 : Stmt11_4_1)
    (h1151 : Stmt11_5_1) (h1157 : Stmt11_5_7) (hCE : CommEndStableFact) (hR1 : R1CommFact)
    (hPt : PointConjFact) (h : Hyp11 G T L I n) {V₁ H₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁)
    (hamal : AmalgamHypV (L ⊔ T ⊔ H₁) (L ⊔ T) H₁ T (fsuV T I))
    (hR : pCoreOf 2 ((L ⊔ T) ⊓ H₁) ≤ ROf T L V₁)
    (hb : Even (critDist (L ⊔ T ⊔ H₁) (L ⊔ T) H₁ (fsuV T I))) :
    False := by
  set V := fsuV T I with hVdef
  have hset := SecD.natSetting11_of h1102 h1141 h hV₁
  have hkind := h1151 G T L I n h
  obtain ⟨V₃, hV₃, -⟩ := (h1110 G T L I n h).1 3 (by norm_num) (by norm_num)
  obtain ⟨y, hA, hB, hne'⟩ := exists_even_pair hamal (SecA.fsuV_ne_bot h) hb
  set A := conjSub y V with hAdef
  have hAR : A ≤ ROf T L V₁ := hA.trans hR
  have hBR : conjSub y⁻¹ V ≤ ROf T L V₁ := hB.trans hR
  obtain ⟨W, hWV, hWA⟩ : ∃ W : Subgroup G, W ≤ V ∧ ⁅W, A⁆ = V₁ := by
    rcases hR1 G T L I n V₁ V₃ hset hkind hV₁ hV₃ A hAR hne' with h1 | h1
    · exact ⟨V, le_rfl, h1⟩
    · exact ⟨V₃, SecA.IsVi.le_fsuV hV₃, h1⟩
  have hXR : conjSub y⁻¹ W ≤ ROf T L V₁ := (conjSub_mono _ hWV).trans hBR
  have hP : ⁅V, conjSub y⁻¹ W⁆ = conjSub y⁻¹ V₁ := by
    have e : V = conjSub y⁻¹ A := (conjSub_conjSub_inv y V).symm
    rw [← hWA, Subgroup.commutator_comm W A, ← conjSub_commutator, ← e]
  have hstab := hCE G T L I n V₁ hset hkind hV₁ _ hXR
  rw [hP] at hstab
  have hPV : conjSub y⁻¹ V₁ ≤ V := by
    rw [← hP]
    exact commutator_le_of_le_normalizer
      (hXR.trans ((SecD.ROf_le_T h V₁).trans (SecA.T_le_normalizer_fsuV T I)))
  have hcard : Nat.card (conjSub y⁻¹ V₁) = 2 ^ n := by
    rw [card_conjSub]
    have h1 := SecA.IsVi.relIndex_eq hV₁
    rw [hset.cV, Subgroup.relIndex_bot_left, mul_one] at h1
    exact h1
  obtain ⟨l, hl, hPl⟩ := hPt G T L I n V₁ _ hset hkind hV₁ hPV hstab hcard
  have hgN : y * l⁻¹ ∈ Subgroup.normalizer (V₁ : Set G) := by
    have e1 : conjSub l⁻¹ V₁ = conjSub y⁻¹ V₁ := by rw [conjSub_eq_conjSubgroup, inv_inv, hPl]
    apply mem_normalizer_of_conjSub_eq
    rw [conjSub_mul, e1, conjSub_inv_conjSub]
  have hAg : A = conjSub (y * l⁻¹) V := by
    rw [conjSub_mul, F7.conjSub_eq_of_mem_normalizer
      (inv_mem (SecA.L_le_normalizer_fsuV h hl))]
  have hab := h1157 G T L I n V₁ h hV₁
  apply hne'
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact le_centralizer_of_le_abelian hab (le_conjClosure _ _)
    (hAg ▸ conjSub_le_conjClosure hgN)

end CFSG.Quasithin.Vol2.Ch11.SecG

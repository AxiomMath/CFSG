module

public import CFSG.Quasithin.H13.L32AL2Ia
public import CFSG.Quasithin.H13.L32A53c

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

abbrev l0 (T L V : Subgroup G) (z' : G) : Subgroup G :=
  l1 T L V ⊓ Subgroup.centralizer (vY T V z' : Set G)

abbrev lY (T L V : Subgroup G) (z' : G) : Subgroup G := oTwoUpper (l0 T L V z')

omit [Finite G] in
theorem mem_normalizer_centralizer {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G) := by
  have key : ∀ k : G, k ∈ Subgroup.normalizer (X : Set G) →
      ∀ c ∈ Subgroup.centralizer (X : Set G), k * c * k⁻¹ ∈ Subgroup.centralizer (X : Set G) := by
    intro k hk c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro x hx
    have hx' : k⁻¹ * x * k ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hk) x).mp hx
      rwa [inv_inv] at this
    have h1 := hc _ hx'
    calc x * (k * c * k⁻¹) = k * ((k⁻¹ * x * k) * c) * k⁻¹ := by group
      _ = k * (c * (k⁻¹ * x * k)) * k⁻¹ := by rw [h1]
      _ = k * c * k⁻¹ * x := by group
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨key g hg c, fun hc => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hc
  rwa [show g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c by group] at this

omit [Finite G] in
theorem mem_normalizer_inf {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro x
  simp only [Subgroup.mem_inf]
  rw [hA x, hB x]

omit [Finite G] in
theorem le_normalizer_of_conj {H K : Subgroup G} (h : ∀ g ∈ H, ∀ k ∈ K, g * k * g⁻¹ ∈ K) :
    H ≤ Subgroup.normalizer (K : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨h g hg k, fun hk => ?_⟩
  have := h g⁻¹ (H.inv_mem hg) _ hk
  rwa [show g⁻¹ * (g * k * g⁻¹) * g⁻¹⁻¹ = k by group] at this

namespace IData

variable {T L V TY : Subgroup G} {z z' : G} (D : IData T L V TY z z')
include D

theorem TY_le_normalizer_l0 (h1332 : Stmt13_3_2) :
    TY ≤ Subgroup.normalizer (l0 T L V z' : Set G) := fun _ ht =>
  mem_normalizer_inf (Setting147.T_le_N_l1 D.S h1332 (D.hTY ht))
    (mem_normalizer_centralizer (D.hTYV ht))

theorem pCoreOf_a114Y_le_normalizer_l0 (h1332 : Stmt13_3_2) :
    pCoreOf 2 (a114Y z z') ≤ Subgroup.normalizer (l0 T L V z' : Set G) :=
  D.hO2Y0.trans (D.TY_le_normalizer_l0 h1332)

theorem a114Y_le_normalizer_l0_sup (h1332 : Stmt13_3_2) :
    a114Y z z' ≤ Subgroup.normalizer ((l0 T L V z' ⊔ pCoreOf 2 (a114Y z z') : Subgroup G) :
      Set G) := by
  obtain ⟨-, -, hcomm, -⟩ := a114_three D.hA
  have hQN := D.pCoreOf_a114Y_le_normalizer_l0 h1332
  refine le_normalizer_of_conj fun y hy k hk => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hQN).1 hk
  have hya : y * a * y⁻¹ * a⁻¹ ∈ pCoreOf 2 (a114Y z z') :=
    hcomm (Subgroup.commutator_mem_commutator hy (Subgroup.mem_inf.mp ha).2)
  have hyb : y * b * y⁻¹ ∈ pCoreOf 2 (a114Y z z') :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hy) b).mp hb
  have e : y * (a * b) * y⁻¹ = (y * a * y⁻¹ * a⁻¹) * a * (y * b * y⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right hya)
    (Subgroup.mem_sup_left ha)) (Subgroup.mem_sup_right hyb)

theorem oTwoUpper_l0_sup (h1332 : Stmt13_3_2) :
    oTwoUpper (l0 T L V z' ⊔ pCoreOf 2 (a114Y z z')) = lY T L V z' := by
  refine le_antisymm ?_ (oTwoUpper_mono le_sup_left)
  have h1 := L32A.oTwoUpper_sup_le_of_two (pCoreOf_isPGroup 2 (a114Y z z'))
    (D.pCoreOf_a114Y_le_normalizer_l0 h1332)
  rw [oTwoUpper, Subgroup.closure_le]
  rintro x ⟨hx, ho⟩
  exact mem_oTwoUpper_of_odd (h1 (mem_oTwoUpper_of_odd hx ho)) ho

theorem a114Y_le_normalizer_lY (h1332 : Stmt13_3_2) :
    a114Y z z' ≤ Subgroup.normalizer (lY T L V z' : Set G) := by
  have h := (D.a114Y_le_normalizer_l0_sup h1332).trans
    (normalizer_le_normalizer_oTwoUpper (l0 T L V z' ⊔ pCoreOf 2 (a114Y z z')))
  rwa [D.oTwoUpper_l0_sup h1332] at h

theorem exists_x : ∃ x ∈ lY T L V z', x ∈ l1 T L V ∧ orderOf x = 3 ∧
    x ∈ Subgroup.centralizer (vY T V z' : Set G) := by
  obtain ⟨x, hx, hx3, hxc⟩ := D.hx3
  exact ⟨x, mem_oTwoUpper_of_odd ⟨hx, hxc⟩ (by rw [hx3]; decide), hx, hx3, hxc⟩

theorem isSylowTwoOf_inf : IsSylowTwoOf (TY ⊓ a114Y z z') (a114Y z z') := by
  have hYN : a114Y z z' ⊔ TY ≤ Subgroup.normalizer (a114Y z z' : Set G) :=
    sup_le Subgroup.le_normalizer ((D.hTYV).trans (a114_two D.hA).2.2)
  exact A4.isSylowTwoOf_inf_normal D.hSyl le_sup_left hYN

theorem a114Y_le_sup : a114Y z z' ≤ oTwoUpper (a114Y z z') ⊔ TY := by
  have h := sup_twoResidual_eq D.isSylowTwoOf_inf
  rw [F6.twoResidual_eq_oTwoUpper] at h
  exact h.symm.le.trans (sup_le (inf_le_left.trans le_sup_right) le_sup_left)

end IData

end CFSG.Quasithin.H13.L32A.L2

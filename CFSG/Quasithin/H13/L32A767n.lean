module

public import CFSG.Quasithin.H13.L32A767i

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem V_le_L_of (h : Hyp147 G T L V) (h13322 : Stmt13_3_2_two) : V ≤ L := by
  have hirr := (h.hyp1223 h13322).irrPlus
  have hVT : V ≤ T := (V_le_pCoreOf_LT h h13322).trans
    (EscapingLocal.pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_of_le h le_sup_right))
  rw [← hirr.2.2.2.1]
  rw [Subgroup.commutator_le]
  intro v hv l hl
  rw [commutatorElement_def]
  exact mul_mem ((Subgroup.mem_normalizer_iff.mp (h.normalizes h13322 (hVT hv)) l).mp hl)
    (inv_mem hl)

theorem exists_basis_l1_of (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) :
    ∃ (V₂ : Subgroup G) (z a b x y : G), A6.IsV2 T V V₂ ∧
      z ∈ fsuV1 T V ∧ z ≠ 1 ∧ a ∈ V₂ ∧ a ∉ fsuV1 T V ∧ b ∈ V ∧ b ∉ V₂ ∧
      x ∈ L₁Of L (fsuV1 T V) ∧ y ∈ L₁Of L (fsuV1 T V) ∧ x * a * x⁻¹ = b ∧
      x * b * x⁻¹ = a * b ∧ y * a * y⁻¹ = z * a := by
  have h13322 := stmt13_3_2_two_of h1332
  obtain ⟨V₂, hV2⟩ := h.exists_V2 h13322 hMod h1222
  have : IsMulCommutative ↥V := (hMod G T L V h.hyp h.fsu).1.1
  have S14 := h.set14 h1222 h1332 h1334 hV2
  have hUe := isElemAbelian_fsuU_of h hMod
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    F7.isElemAbelian_comm hUe (le_conjClosure V _ ha) (le_conjClosure V _ hb)
  have hV2' : ∀ a ∈ V, a * a = 1 := fun a ha => by
    rw [← pow_two]
    exact F7.isElemAbelian_pow_eq_one hUe (le_conjClosure V _ ha)
  obtain ⟨z, a, b, hz0, hz1, ha, haV, hb, hbV⟩ := S14.exists_basis
  have hzV₂ : z ∈ V₂ := hV2.1 hz0
  have hzV : z ∈ V := (Subgroup.mem_inf.mp hz0).1
  have haV' : a ∈ V := hV2.2.1 ha
  obtain ⟨x₁, hx₁L, hx₁3, hx₁z, hx₁a, hx₁b⟩ := S14.exists_rot hzV haV' hb
    (fun h => haV (h ▸ one_mem _)) (fun h => hbV (h ▸ one_mem _))
    (fun h => haV (h ▸ hz0)) (fun h => hbV (h ▸ hzV₂)) (fun h => hbV (h ▸ ha))
    (fun h => hbV (h ▸ mul_mem hzV₂ ha))
  obtain ⟨x₂, hx₂L, hx₂3, hx₂z, hx₂a, hx₂b⟩ := S14.exists_rot hzV haV' (mul_mem hzV hb)
    (fun h => haV (h ▸ one_mem _))
    (fun h => hbV (by
      rw [eq_inv_of_mul_eq_one_right h]
      exact inv_mem hzV₂))
    (fun h => haV (h ▸ hz0))
    (fun h => hbV (by
      have : b = 1 := by
        calc b = z⁻¹ * (z * b) := by group
          _ = 1 := by rw [h, inv_mul_cancel]
      rw [this]
      exact one_mem _))
    (fun h => hbV (by
      have : b = z⁻¹ * a := by
        calc b = z⁻¹ * (z * b) := by group
          _ = z⁻¹ * a := by rw [← h]
      rw [this]
      exact mul_mem (inv_mem hzV₂) ha))
    (fun h => hbV (by
      have : b = a := by
        calc b = z⁻¹ * (z * b) := by group
          _ = z⁻¹ * (z * a) := by rw [h]
          _ = a := by group
      rw [this]
      exact ha))
  have hx₁L1 : x₁ ∈ L₁Of L (fsuV1 T V) :=
    Subgroup.subset_closure ⟨⟨hx₁L, S14.mem_g1 hz0 hz1 hx₁z⟩, 3, by decide, hx₁3⟩
  have hx₂L1 : x₂ ∈ L₁Of L (fsuV1 T V) :=
    Subgroup.subset_closure ⟨⟨hx₂L, S14.mem_g1 hz0 hz1 hx₂z⟩, 3, by decide, hx₂3⟩
  have hx₁z' : x₁⁻¹ * z * x₁ = z := by
    calc x₁⁻¹ * z * x₁ = x₁⁻¹ * (x₁ * z * x₁⁻¹) * x₁ := by rw [hx₁z]
      _ = z := by group
  have hx₁b' : x₁⁻¹ * b * x₁ = a := by
    calc x₁⁻¹ * b * x₁ = x₁⁻¹ * (x₁ * a * x₁⁻¹) * x₁ := by rw [hx₁a]
      _ = a := by group
  have hya : (x₁⁻¹ * x₂) * a * (x₁⁻¹ * x₂)⁻¹ = z * a := by
    calc (x₁⁻¹ * x₂) * a * (x₁⁻¹ * x₂)⁻¹ = x₁⁻¹ * (x₂ * a * x₂⁻¹) * x₁ := by group
      _ = x₁⁻¹ * (z * b) * x₁ := by rw [hx₂a]
      _ = (x₁⁻¹ * z * x₁) * (x₁⁻¹ * b * x₁) := by group
      _ = z * a := by rw [hx₁z', hx₁b']
  exact ⟨V₂, z, a, b, x₁, x₁⁻¹ * x₂, hV2, hz0, hz1, ha, haV, hb, hbV, hx₁L1,
    mul_mem (inv_mem hx₁L1) hx₂L1, hx₁a, hx₁b, hya⟩

theorem v_le_l1_of (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) : V ≤ L₁Of L (fsuV1 T V) := by
  have h13322 := stmt13_3_2_two_of h1332
  obtain ⟨-, -, -, hV1, -⟩ := hMod G T L V h.hyp h.fsu
  have hVL : ∀ {v : G}, v ∈ V → v ∈ L := fun hv => V_le_L_of h h13322 hv
  have hcomm : ∀ {x g : G}, x ∈ L₁Of L (fsuV1 T V) → g ∈ L →
      g ∈ Subgroup.normalizer (fsuV1 T V : Set G) → x * g * x⁻¹ * g⁻¹ ∈ L₁Of L (fsuV1 T V) := by
    intro x g hx hgL hgN
    rw [show x * g * x⁻¹ * g⁻¹ = x * (g * x⁻¹ * g⁻¹) by group]
    exact mul_mem hx ((Subgroup.mem_normalizer_iff.mp
      (le_normalizer_oTwoRes _ (Subgroup.mem_inf.mpr ⟨hgL, hgN⟩)) _).mp (inv_mem hx))
  obtain ⟨V₂, z, a, b, x, y, hV2, hz0, hz1, ha, haV, hb, hbV, hxL1, hyL1, hxa, hxb, hya⟩ :=
    exists_basis_l1_of h hMod h1222 h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V h.hyp h.fsu).1.1
  have S14 := h.set14 h1222 h1332 h1334 hV2
  have hUe := isElemAbelian_fsuU_of h hMod
  have hVN : ∀ v ∈ V, v ∈ Subgroup.normalizer (fsuV1 T V : Set G) := fun v hv => by
    rw [normalizer_eq_centralizer_of_card_two hV1, Subgroup.mem_centralizer_iff]
    intro w hw
    exact F7.isElemAbelian_comm hUe (le_conjClosure V _ (Subgroup.mem_inf.mp hw).1)
      (le_conjClosure V _ hv)
  have haV' : a ∈ V := hV2.2.1 ha
  have hz : z ∈ L₁Of L (fsuV1 T V) := by
    have h := hcomm hyL1 (hVL haV') (hVN a haV')
    rwa [hya, mul_inv_cancel_right] at h
  have ha1 : a ∈ L₁Of L (fsuV1 T V) := by
    have h := hcomm hxL1 (hVL hb) (hVN b hb)
    rwa [hxb, mul_inv_cancel_right] at h
  have hb1 : b ∈ L₁Of L (fsuV1 T V) := by
    have h := hcomm hxL1 (hVL haV') (hVN a haV')
    rw [hxa] at h
    have := mul_mem h ha1
    rwa [inv_mul_cancel_right] at this
  have hV1 : fsuV1 T V ≤ L₁Of L (fsuV1 T V) := fun v hv => by
    rcases S14.eq_of_mem_V1 hz0 hz1 hv with rfl | rfl
    · exact one_mem _
    · exact hz
  have hV2le : V₂ ≤ L₁Of L (fsuV1 T V) := fun v hv => by
    rcases S14.mem_V2 ha haV hv with h | h
    · exact hV1 h
    · rw [show v = a⁻¹ * (a * v) by group]
      exact mul_mem (inv_mem ha1) (hV1 h)
  intro v hv
  rcases S14.mem_V hb hbV hv with h | h
  · exact hV2le h
  · rw [show v = b⁻¹ * (b * v) by group]
    exact mul_mem (inv_mem hb1) (hV2le h)

theorem v_le_kz (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) : V ≤ kz T V :=
  (v_le_l1_of h hMod h1222 h1332 h1334).trans (l1_le_kz h hMod)

end CFSG.Quasithin.H13.L32A

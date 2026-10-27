module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLoc442F
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.QuasithinUnique CFSG.Quasithin

section Fix

variable {G : Type} [Group G] {X Y V U R K P : Subgroup G} {z t : G}

theorem mem_normalizer_sup_zpowers {W : Subgroup G} {u c : G}
    (hc : c ∈ Subgroup.normalizer (W : Set G)) (hcu : c⁻¹ * u * c = u) :
    c ∈ Subgroup.normalizer ((W ⊔ Subgroup.zpowers u : Subgroup G) : Set G) := by
  rw [← conjSubgroup_eq_iff_mem_normalizer] at hc ⊢
  have h : conjSubgroup (W ⊔ Subgroup.zpowers u) c =
      conjSubgroup W c ⊔ conjSubgroup (Subgroup.zpowers u) c := by
    unfold conjSubgroup
    exact Subgroup.map_sup _ _ _
  have h2 : conjSubgroup (Subgroup.zpowers u) c = Subgroup.zpowers u := by
    unfold conjSubgroup
    rw [MonoidHom.map_zpowers]
    congr 1
    simpa [MulAut.conj_apply] using hcu
  rw [h, hc, h2]

theorem Loc442UCore.fix_core [Finite G] (D : Loc442UCore X Y V U R K P z t) {W : Subgroup G}
    (hWU : W ≤ U) (htW : t ∈ W)
    (hmax : ∀ W', Qual X Y U t W' → W ≤ W' → W' ≤ W) {u g : G} (hu : u ∈ U) (huW : u ∉ W)
    (hg : g ∈ nS Y W) (hgu : g⁻¹ * u * g ∈ X) : g ∈ X := by
  have hUX : U ≤ X := D.U_V.trans D.V_X
  have hPW : P ≤ Subgroup.normalizer (W : Set G) :=
    le_normalizer_of_comm fun y hy w hw => D.P_U y hy w (hWU hw)
  have hUW : U ≤ Subgroup.normalizer (W : Set G) :=
    le_normalizer_of_comm fun a ha w hw => D.V_ab a (D.U_V ha) w (D.U_V (hWU hw))
  have hunX : u ∈ nS X W := ⟨hUW hu, hUX hu⟩
  have hgu' : g⁻¹ * u * g ∈ nS X W := ⟨(Subgroup.normalizer (W : Set G)).mul_mem
    ((Subgroup.normalizer (W : Set G)).mul_mem ((Subgroup.normalizer (W : Set G)).inv_mem hg.1)
      (hUW hu)) hg.1, hgu⟩
  obtain ⟨x, hx, hxe⟩ := D.fusion_nS hPW hunX (D.V_sq u (D.U_V hu)) hg hgu'
  have hcu : (g * x⁻¹)⁻¹ * u * (g * x⁻¹) = u := by
    have : (g * x⁻¹)⁻¹ * u * (g * x⁻¹) = x * (g⁻¹ * u * g) * x⁻¹ := by group
    rw [this, hxe]
    group
  have hcN : g * x⁻¹ ∈ nS Y W :=
    (nS Y W).mul_mem hg ((nS Y W).inv_mem ⟨hx.1, D.XY hx.2⟩)
  have hWW₁ : W < W ⊔ Subgroup.zpowers u := by
    refine lt_of_le_of_ne le_sup_left fun h => huW ?_
    rw [h]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
  have hW₁U : W ⊔ Subgroup.zpowers u ≤ U := sup_le hWU (Subgroup.zpowers_le.mpr hu)
  have hcW₁ := mem_normalizer_sup_zpowers hcN.1 hcu
  have hnlt : ¬ nS X (W ⊔ Subgroup.zpowers u) < nS Y (W ⊔ Subgroup.zpowers u) := fun hlt =>
    not_le_of_gt hWW₁ (hmax _ ⟨Subgroup.mem_sup_left htW, hW₁U, hlt⟩ hWW₁.le)
  have hle : nS X (W ⊔ Subgroup.zpowers u) ≤ nS Y (W ⊔ Subgroup.zpowers u) :=
    fun y hy => ⟨hy.1, D.XY hy.2⟩
  have heq : nS Y (W ⊔ Subgroup.zpowers u) ≤ nS X (W ⊔ Subgroup.zpowers u) := by
    rcases lt_or_eq_of_le hle with h | h
    · exact absurd h hnlt
    · exact h.ge
  have hcX : g * x⁻¹ ∈ X := (heq ⟨hcW₁, hcN.2⟩).2
  have : g = (g * x⁻¹) * x := by group
  rw [this]
  exact X.mul_mem hcX hx.2

theorem Loc442UCore.nS_U_le (D : Loc442UCore X Y V U R K P z t) {W : Subgroup G} (hWU : W < U)
    (hmax : ∀ W', Qual X Y U t W' → W ≤ W' → W' ≤ W) : nS Y U ≤ X := by
  have hXN : X ≤ nS Y U := fun x hx => ⟨D.X_le_normalizer_U hx, D.XY hx⟩
  have hnlt : ¬ X < nS Y U := fun hlt => not_le_of_gt hWU (hmax U ⟨D.t_U, le_rfl, by
    rw [show nS X U = X from inf_eq_right.mpr D.X_le_normalizer_U]
    exact hlt⟩ hWU.le)
  rcases lt_or_eq_of_le hXN with h | h
  · exact absurd h hnlt
  · exact h.ge

end Fix

end CFSG.Quasithin.H13.F431.Un

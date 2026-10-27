module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3RVertex
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3UFix

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D}

theorem GoldHyp.inf_conjSub_le_pCoreOf_left (h : GoldHyp A B) {c : D} (hcA : c ∈ A)
    (hcB : c ∉ B) : A ⊓ B ⊓ conjSub c (A ⊓ B) ≤ pCoreOf 2 A := by
  have := h.symm.inf_conjSub_le_pCoreOf_right hcA hcB
  rwa [inf_comm B A] at this

end GoldAmL

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

omit [Finite D] in
theorem conjSub_eq_self_of_forall_comm {g : D} {X : Subgroup D} (hc : ∀ x ∈ X, g * x * g⁻¹ = x) :
    conjSub g X = X := by
  have hgc : g ∈ Subgroup.centralizer (X : Set D) := Subgroup.mem_centralizer_iff.mpr fun x hx => by
    calc x * g = (g * x * g⁻¹) * g := by rw [hc x hx]
      _ = g * x := by group
  exact conjSub_eq_of_mem_normalizer (Subgroup.centralizer_le_normalizer (X : Set D) hgc)

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem mem_ballStab_one_of_fix_two_A {u v w : CosetGeom (A ⊔ B) A B} (hu : vtype u = false)
    (hv : (graph (A ⊔ B) A B).Adj u v) (hw : (graph (A ⊔ B) A B).Adj u w) (hvw : v ≠ w) {x : D}
    (hxu : x ∈ stab u) (hxv : x ∈ stab v) (hxw : x ∈ stab w) : x ∈ ballStab 1 u := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₀ hu
  have hadj : (graph (A ⊔ B) A B).Adj (γ₀ (A ⊔ B) A B) (γ₁ (A ⊔ B) A B) :=
    adj_γ₀_γ₁ (G₀ := A ⊔ B) (G₁ := A) (G₂ := B)
  have hv0 : (graph (A ⊔ B) A B).Adj (γ₀ (A ⊔ B) A B) (g⁻¹ • v) := by
    have := (smul_adj g⁻¹).mpr hv
    rwa [inv_smul_smul] at this
  have hw0 : (graph (A ⊔ B) A B).Adj (γ₀ (A ⊔ B) A B) (g⁻¹ • w) := by
    have := (smul_adj g⁻¹).mpr hw
    rwa [inv_smul_smul] at this
  obtain ⟨k, hk0, hk1⟩ := exists_stab_smul_eq hadj hv0
  obtain ⟨k', hk0', hk1'⟩ := exists_stab_smul_eq hadj hw0
  have hkA : (k : D) ∈ A := by
    have := mem_stab_of_smul_eq hk0
    rwa [stab_γ₀ (le_sup_left : A ≤ A ⊔ B)] at this
  have hkA' : (k' : D) ∈ A := by
    have := mem_stab_of_smul_eq hk0'
    rwa [stab_γ₀ (le_sup_left : A ≤ A ⊔ B)] at this
  have hcA : ((k⁻¹ * k' : ↥(A ⊔ B)) : D) ∈ A := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    exact A.mul_mem (A.inv_mem hkA) hkA'
  have hcB : ((k⁻¹ * k' : ↥(A ⊔ B)) : D) ∉ B := fun hB => hvw (by
    have e0 : (k⁻¹ * k' : ↥(A ⊔ B)) • γ₁ (A ⊔ B) A B = γ₁ (A ⊔ B) A B :=
      smul_γ₁_of_mem (le_sup_right : B ≤ A ⊔ B) hB
    have e1 : k' • γ₁ (A ⊔ B) A B = k • γ₁ (A ⊔ B) A B := by
      have : k' = k * (k⁻¹ * k') := by group
      rw [this, mul_smul, e0]
    have e2 : g⁻¹ • v = g⁻¹ • w := by rw [← hk1, ← hk1', e1]
    exact smul_left_cancel g⁻¹ e2)
  obtain rfl : v = (g * k) • γ₁ (A ⊔ B) A B := by rw [mul_smul, hk1, smul_inv_smul]
  obtain rfl : w = (g * k') • γ₁ (A ⊔ B) A B := by rw [mul_smul, hk1', smul_inv_smul]
  rw [stab_smul, stab_γ₀ (le_sup_left : A ≤ A ⊔ B), mem_conjSub] at hxu
  rw [stab_smul, stab_γ₁ (le_sup_right : B ≤ A ⊔ B), mem_conjSub] at hxv hxw
  rw [ballStab_smul, mem_conjSub]
  set y : D := ((g * k : ↥(A ⊔ B)) : D)⁻¹ * x * ((g * k : ↥(A ⊔ B)) : D) with hy
  have hyB : y ∈ B := hxv
  have hyA : y ∈ A := by
    have e : y = (k : D)⁻¹ * ((g : D)⁻¹ * x * g) * k := by
      simp only [hy, Subgroup.coe_mul]
      group
    rw [e]
    exact A.mul_mem (A.mul_mem (A.inv_mem hkA) hxu) hkA
  have hyc : ((k⁻¹ * k' : ↥(A ⊔ B)) : D)⁻¹ * y * ((k⁻¹ * k' : ↥(A ⊔ B)) : D) ∈ B := by
    have e : ((k⁻¹ * k' : ↥(A ⊔ B)) : D)⁻¹ * y * ((k⁻¹ * k' : ↥(A ⊔ B)) : D) =
        ((g * k' : ↥(A ⊔ B)) : D)⁻¹ * x * ((g * k' : ↥(A ⊔ B)) : D) := by
      simp only [hy, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact hxw
  have hycA : ((k⁻¹ * k' : ↥(A ⊔ B)) : D)⁻¹ * y * ((k⁻¹ * k' : ↥(A ⊔ B)) : D) ∈ A :=
    A.mul_mem (A.mul_mem (A.inv_mem hcA) hyA) hcA
  have hQ : y ∈ pCoreOf 2 A := h.gold.inf_conjSub_le_pCoreOf_left hcA hcB
    ⟨⟨hyA, hyB⟩, mem_conjSub.mpr ⟨hycA, hyc⟩⟩
  have hQ' : (g : D)⁻¹ * x * g ∈ pCoreOf 2 A := by
    have e : (g : D)⁻¹ * x * g = (k : D) * y * (k : D)⁻¹ := by
      simp only [hy, Subgroup.coe_mul]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 A hkA) y).mp hQ
  have hle := pCoreOf_stab_le_ballStab_one h.gold.amalgamHyp (γ₀ (A ⊔ B) A B)
  rw [stab_γ₀ (le_sup_left : A ≤ A ⊔ B)] at hle
  exact hle hQ'

theorem eq_of_Vv_eq {v α α' : CosetGeom (A ⊔ B) A B} (hv : vtype v = true)
    (hα : (graph (A ⊔ B) A B).Adj v α) (hα' : (graph (A ⊔ B) A B).Adj v α')
    (hVV : Vv V α = Vv V α') : α = α' := by
  by_contra hne
  have hαt : vtype α = false := vtype_eq_false_of_adj hα hv
  have hle : Vv V α ≤ Zv z v := fun c hc =>
    h.mem_Zv_of_mem_Vv_of_mem_Vv hv hα hα' hne hc (by rw [← hVV]; exact hc)
  have h1 := Subgroup.card_le_of_le hle
  rw [h.card_Vv_A hαt, h.card_Zv hv] at h1
  omega

theorem mem_stab_of_centralizes_Vv {u s : CosetGeom (A ⊔ B) A B} (hu : vtype u = true)
    (hs : (graph (A ⊔ B) A B).Adj u s) {g : D} (hg : g ∈ stab u)
    (hc : ∀ x ∈ Vv V s, g * x * g⁻¹ = x) : g ∈ stab s := by
  have hgG : g ∈ A ⊔ B := stab_le _ hg
  lift g to ↥(A ⊔ B) using hgG with g'
  have hgu : g' • u = u := smul_eq_of_mem_stab hg
  have hadj : (graph (A ⊔ B) A B).Adj u (g' • s) := by
    have := (smul_adj g').mpr hs
    rwa [hgu] at this
  have hVV : Vv V s = Vv V (g' • s) := by
    rw [Vv_smul h.natural.reduced.2.1 g' s, conjSub_eq_self_of_forall_comm hc]
  exact mem_stab_of_smul_eq (h.eq_of_Vv_eq hu hs hadj hVV).symm

theorem mem_stab_of_centralizes_Zv {u s : CosetGeom (A ⊔ B) A B} (hu : vtype u = false)
    (hs : (graph (A ⊔ B) A B).Adj u s) {g : D} (hg : g ∈ stab u)
    (hc : ∀ x ∈ Zv z s, g * x * g⁻¹ = x) : g ∈ stab s := by
  have hgG : g ∈ A ⊔ B := stab_le _ hg
  lift g to ↥(A ⊔ B) using hgG with g'
  have hgu : g' • u = u := smul_eq_of_mem_stab hg
  have hadj : (graph (A ⊔ B) A B).Adj u (g' • s) := by
    have := (smul_adj g').mpr hs
    rwa [hgu] at this
  have hzz : Zv z s = Zv z (g' • s) := by
    rw [Zv_smul h.normalizes_zpowers g' s, conjSub_eq_self_of_forall_comm hc]
  exact mem_stab_of_smul_eq (h.eq_of_Zv_eq hu hs hadj hzz).symm

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin

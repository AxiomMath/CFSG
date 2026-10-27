module

public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.CharTwoLocal

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open
open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace FourteenFive

theorem mem_zpowers_iff_of_mul_self_eq_one {v x : G} (hv : v * v = 1) :
    x ∈ zpowers v ↔ x = 1 ∨ x = v := by
  constructor
  · intro hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hv2 : v ^ (2 : ℤ) = 1 := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two, hv]
    rw [zpow_eq_zpow_emod k hv2]
    rcases Int.emod_two_eq_zero_or_one k with h | h <;> simp [h]
  · intro hx
    rcases hx with hx | hx
    · rw [hx]
      exact Subgroup.one_mem _
    · rw [hx]
      exact Subgroup.mem_zpowers v

theorem mem_sup_zpowers_iff {V E : Subgroup G} (hV : IsElemAbelian 2 V) (hE : E ≤ V)
    {v₂ : G} (hv₂ : v₂ ∈ V) {x : G} :
    x ∈ E ⊔ zpowers v₂ ↔ ∃ e ∈ E, x = e ∨ x = e * v₂ := by
  have hv₂2 : v₂ * v₂ = 1 := hV.mul_self_eq_one hv₂
  have hcomm : ∀ f ∈ E, v₂ * f = f * v₂ := fun f hf => hV.comm hv₂ (hE hf)
  let S : Subgroup G :=
    { carrier := {x | ∃ e ∈ E, x = e ∨ x = e * v₂}
      one_mem' := ⟨1, E.one_mem, Or.inl rfl⟩
      mul_mem' := by
        rintro x y ⟨e, he, hx | hx⟩ ⟨f, hf, hy | hy⟩
        · rw [hx, hy]
          exact ⟨e * f, E.mul_mem he hf, Or.inl rfl⟩
        · rw [hx, hy]
          exact ⟨e * f, E.mul_mem he hf, Or.inr (by rw [mul_assoc])⟩
        · rw [hx, hy]
          refine ⟨e * f, E.mul_mem he hf, Or.inr ?_⟩
          calc (e * v₂) * f = e * (v₂ * f) := mul_assoc ..
            _ = e * (f * v₂) := by rw [hcomm f hf]
            _ = (e * f) * v₂ := (mul_assoc e f v₂).symm
        · rw [hx, hy]
          refine ⟨e * f, E.mul_mem he hf, Or.inl ?_⟩
          calc (e * v₂) * (f * v₂) = e * (v₂ * (f * v₂)) := mul_assoc ..
            _ = e * ((v₂ * f) * v₂) := by rw [← mul_assoc v₂ f v₂]
            _ = e * ((f * v₂) * v₂) := by rw [hcomm f hf]
            _ = e * (f * (v₂ * v₂)) := by rw [mul_assoc f v₂ v₂]
            _ = e * f := by rw [hv₂2, mul_one]
      inv_mem' := by
        rintro x ⟨e, he, hx | hx⟩
        · rw [hx]
          exact ⟨e⁻¹, E.inv_mem he, Or.inl rfl⟩
        · rw [hx]
          refine ⟨e⁻¹, E.inv_mem he, Or.inr ?_⟩
          rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hv₂2]
          exact hcomm e⁻¹ (E.inv_mem he) }
  have hES : E ≤ S := fun e he => ⟨e, he, Or.inl rfl⟩
  have hvS : v₂ ∈ S := ⟨1, E.one_mem, Or.inr (by rw [one_mul])⟩
  have hsup : E ⊔ zpowers v₂ ≤ S := sup_le hES (Subgroup.zpowers_le.2 hvS)
  constructor
  · intro hx
    exact hsup hx
  · rintro ⟨e, he, hx | hx⟩
    · rw [hx]
      exact Subgroup.mem_sup_left he
    · rw [hx]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left he)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers v₂))

theorem sup_zpowers_inf_eq {V V₀ E : Subgroup G} (hV : IsElemAbelian 2 V) (hV₀ : V₀ ≤ V)
    (hE : E ≤ V) (hV₀E : V₀ ⊓ E = ⊥) {v₂ : G} (hv₂ : v₂ ∈ V₀) :
    (E ⊔ zpowers v₂) ⊓ V₀ = zpowers v₂ := by
  have hv₂V : v₂ ∈ V := hV₀ hv₂
  have hv₂2 : v₂ * v₂ = 1 := hV.mul_self_eq_one hv₂V
  apply le_antisymm
  · rintro x ⟨hx, hx₀⟩
    obtain ⟨e, he, hx' | hx'⟩ := (mem_sup_zpowers_iff hV hE hv₂V).1 hx
    · have he₀ : e ∈ V₀ := by rwa [hx'] at hx₀
      have hebot : e ∈ V₀ ⊓ E := ⟨he₀, he⟩
      rw [hV₀E] at hebot
      have he1 : e = 1 := by simpa using hebot
      rw [hx', he1]
      exact Subgroup.one_mem _
    · have hx₀' : e * v₂ ∈ V₀ := by rwa [hx'] at hx₀
      have he₀ : e ∈ V₀ := by
        have h := V₀.mul_mem hx₀' hv₂
        rwa [mul_assoc, hv₂2, mul_one] at h
      have hebot : e ∈ V₀ ⊓ E := ⟨he₀, he⟩
      rw [hV₀E] at hebot
      have he1 : e = 1 := by simpa using hebot
      rw [hx', he1, one_mul]
      exact Subgroup.mem_zpowers v₂
  · exact le_inf le_sup_right (Subgroup.zpowers_le.2 hv₂)

theorem mem_sup_inf_iff {V V₀ E E' : Subgroup G} (hV : IsElemAbelian 2 V) (hV₀ : V₀ ≤ V)
    (hE : E ≤ V) (hV₀E : V₀ ⊓ E = ⊥) {e : G} (he : e ∈ E) :
    e ∈ V₀ ⊔ (E ⊓ E') ↔ e ∈ E' := by
  constructor
  · intro hx
    have hV₀norm : V₀ ≤ Subgroup.normalizer ((E ⊓ E' : Subgroup G) : Set G) := fun x hx =>
      Subgroup.centralizer_le_normalizer _ (by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact hV.comm (hE hy.1) (hV₀ hx))
    have hx' : e ∈ ((V₀ ⊔ (E ⊓ E') : Subgroup G) : Set G) := hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right V₀ (E ⊓ E') hV₀norm] at hx'
    obtain ⟨v₀, hv₀, e₁, he₁, hve⟩ := hx'
    have hve' : e = v₀ * e₁ := hve.symm
    have hv₀E : v₀ ∈ E := by
      have h := E.mul_mem (hve' ▸ he) (E.inv_mem he₁.1)
      rwa [mul_assoc, mul_inv_cancel, mul_one] at h
    have hv₀bot : v₀ ∈ V₀ ⊓ E := ⟨hv₀, hv₀E⟩
    rw [hV₀E] at hv₀bot
    have hv₀one : v₀ = 1 := by simpa using hv₀bot
    rw [hve', hv₀one, one_mul]
    exact he₁.2
  · intro hx
    exact Subgroup.mem_sup_right ⟨he, hx⟩

theorem relIndex_sup_inf_eq_two {V V₀ E E' : Subgroup G} (hV : IsElemAbelian 2 V)
    (hV₀ : V₀ ≤ V) (hE : E ≤ V) (hV₀E : V₀ ⊓ E = ⊥) (hsup : V₀ ⊔ E = V) {v₂ : G}
    (hv₂ : v₂ ∈ V₀) (hEE' : ∀ e ∈ E, e ∉ E' → e * v₂ ∈ E') {e₀ : G} (he₀ : e₀ ∈ E)
    (he₀' : e₀ ∉ E') : (V₀ ⊔ (E ⊓ E')).relIndex V = 2 := by
  have hv₂V : v₂ ∈ V := hV₀ hv₂
  have hv₂2 : v₂ * v₂ = 1 := hV.mul_self_eq_one hv₂V
  have hV₀norm : V₀ ≤ Subgroup.normalizer (E : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _ (by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact hV.comm (hE hy) (hV₀ hx))
  have hmul_mem : ∀ e ∈ E, e ∉ E' → e * e₀ ∈ E ⊓ E' := by
    intro e he he'
    have hev : e * v₂ ∈ E' := hEE' e he he'
    have h₀v : e₀ * v₂ ∈ E' := hEE' e₀ he₀ he₀'
    have hprod : (e * v₂) * (e₀ * v₂) ∈ E' := E'.mul_mem hev h₀v
    have heq : (e * v₂) * (e₀ * v₂) = e * e₀ := by
      calc (e * v₂) * (e₀ * v₂) = e * (v₂ * (e₀ * v₂)) := mul_assoc ..
        _ = e * ((v₂ * e₀) * v₂) := by rw [← mul_assoc v₂ e₀ v₂]
        _ = e * ((e₀ * v₂) * v₂) := by rw [hV.comm hv₂V (hE he₀)]
        _ = e * (e₀ * (v₂ * v₂)) := by rw [mul_assoc e₀ v₂ v₂]
        _ = e * e₀ := by rw [hv₂2, mul_one]
    exact ⟨E.mul_mem he he₀, heq ▸ hprod⟩
  have hmul_notmem : ∀ e ∈ E ⊓ E', e * e₀ ∉ E' := by
    intro e he hee'
    have he' : e ∈ E' := he.2
    have h : e₀ = e⁻¹ * (e * e₀) := by group
    have h₀E' : e₀ ∈ E' := by
      rw [h]
      exact E'.mul_mem (E'.inv_mem he') hee'
    exact he₀' h₀E'
  have hmemW : ∀ x ∈ E, x ∈ V₀ ⊔ (E ⊓ E') ↔ x ∈ E ⊓ E' := by
    intro x hx
    constructor
    · intro hxW
      exact ⟨hx, (mem_sup_inf_iff hV hV₀ hE hV₀E hx).1 hxW⟩
    · intro hxE
      exact Subgroup.mem_sup_right hxE
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨e₀, hE he₀⟩, fun b => ?_⟩
  have hb_mem : (b : G) ∈ ((V₀ ⊔ E : Subgroup G) : Set G) := by
    rw [hsup]
    exact b.2
  rw [Subgroup.coe_mul_of_left_le_normalizer_right V₀ E hV₀norm] at hb_mem
  obtain ⟨v₀, hv₀, e, he, hbe⟩ := hb_mem
  have hbe' : (b : G) = v₀ * e := hbe.symm
  have hbW : (b : G) ∈ V₀ ⊔ (E ⊓ E') ↔ e ∈ E ⊓ E' := by
    rw [hbe']
    constructor
    · intro h
      have hxW : e ∈ V₀ ⊔ (E ⊓ E') := by
        have hvinv : v₀⁻¹ ∈ V₀ ⊔ (E ⊓ E') := Subgroup.mem_sup_left (V₀.inv_mem hv₀)
        have hh : v₀⁻¹ * (v₀ * e) ∈ V₀ ⊔ (E ⊓ E') := Subgroup.mul_mem _ hvinv h
        rwa [← mul_assoc, inv_mul_cancel, one_mul] at hh
      exact (hmemW e he).1 hxW
    · intro heE
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hv₀) ((hmemW e he).2 heE)
  have hba : (↑(b * (⟨e₀, hE he₀⟩ : V)) : G) ∈ V₀ ⊔ (E ⊓ E') ↔
      e * e₀ ∈ E ⊓ E' := by
    have hcoe : (↑(b * (⟨e₀, hE he₀⟩ : V)) : G) = v₀ * (e * e₀) := by
      rw [Subgroup.coe_mul, hbe', mul_assoc]
    rw [hcoe]
    constructor
    · intro h
      have hxW : e * e₀ ∈ V₀ ⊔ (E ⊓ E') := by
        have hvinv : v₀⁻¹ ∈ V₀ ⊔ (E ⊓ E') := Subgroup.mem_sup_left (V₀.inv_mem hv₀)
        have hh : v₀⁻¹ * (v₀ * (e * e₀)) ∈ V₀ ⊔ (E ⊓ E') := Subgroup.mul_mem _ hvinv h
        rwa [← mul_assoc, inv_mul_cancel, one_mul] at hh
      exact (hmemW (e * e₀) (E.mul_mem he he₀)).1 hxW
    · intro heE
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hv₀)
        ((hmemW (e * e₀) (E.mul_mem he he₀)).2 heE)
  have hxor : Xor (e * e₀ ∈ E ⊓ E') (e ∈ E ⊓ E') := by
    by_cases he' : e ∈ E'
    · have hnot : e * e₀ ∉ E ⊓ E' := fun h => hmul_notmem e ⟨he, he'⟩ h.2
      exact Or.inr ⟨⟨he, he'⟩, hnot⟩
    · exact Or.inl ⟨hmul_mem e he he', fun h => he' h.2⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hba, hbW]
  exact hxor

end FourteenFive

end CFSG.LocalAnalysis.WeakClosure81

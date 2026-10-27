module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab7Fx
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab7Crit

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmLab6
  CFSG.Quasithin.F6.GoldAmLab7

namespace F6

namespace GoldAmLab8

variable {D : Type*} [Group D] {A B : Subgroup D} {V V₂ : Subgroup D} {z c : D}

structure Doubled (A B : Subgroup D) (z : D) (V : Subgroup D) (c : D) (V₂ : Subgroup D) :
    Prop where
  sys : TwoSys A B z V c V₂
  hz : ∀ y ∈ B, y * z * y⁻¹ = z
  hc : ∀ a ∈ A, a * c * a⁻¹ = c

@[expose] def IsLab (V V₂ : Subgroup D) (v : CosetGeom (A ⊔ B) A B) (t : D) : Prop :=
  t ≠ 1 ∧ ∃ u, (graph (A ⊔ B) A B).Adj u v ∧ t ∈ Fx V V₂ u v

variable [Finite D]

theorem IsLab.mem_of_adj (d : Doubled A B z V c V₂) {v u' : CosetGeom (A ⊔ B) A B} {t : D}
    (hl : IsLab V V₂ v t) (hu' : (graph (A ⊔ B) A B).Adj u' v) : t ∈ Fx V V₂ u' v := by
  obtain ⟨-, u, hu, ht⟩ := hl
  exact fx_mem_of_adj d.sys d.hz d.hc hu hu' ht

theorem IsLab.cent (d : Doubled A B z V c V₂) {v : CosetGeom (A ⊔ B) A B} {t : D}
    (hl : IsLab V V₂ v t) {g : D} (hg : g ∈ stab v) : g * t * g⁻¹ = t := by
  obtain ⟨-, u, hu, ht⟩ := hl
  exact fx_cent d.sys d.hz d.hc hu ht hg

omit [Finite D] in
theorem IsLab.smul (d : Doubled A B z V c V₂) {v : CosetGeom (A ⊔ B) A B} {t : D}
    (hl : IsLab V V₂ v t) (g : ↥(A ⊔ B)) : IsLab V V₂ (g • v) ((g : D) * t * (g : D)⁻¹) := by
  have hA : A ≤ Subgroup.normalizer (V : Set D) := d.sys.nat.reduced.2.1
  have hB : B ≤ Subgroup.normalizer (V₂ : Set D) := d.sys.nat₂.reduced.2.1
  obtain ⟨ht1, u, hu, ht⟩ := hl
  refine ⟨fun e => ht1 ?_, g • u, (smul_adj g).mpr hu, ?_⟩
  · have e1 : t = (g : D)⁻¹ * ((g : D) * t * (g : D)⁻¹) * g := by group
    rw [e1, e]
    group
  · rw [mem_Fx_smul hA hB]
    have e : (g : D)⁻¹ * ((g : D) * t * (g : D)⁻¹) * g = t := by group
    rw [e]
    exact ht

theorem IsLab.smul_of_mem_stab (d : Doubled A B z V c V₂) {x y : CosetGeom (A ⊔ B) A B}
    {t : D} (hx : IsLab V V₂ x t) (hy : IsLab V V₂ y t) (g : ↥(A ⊔ B))
    (hg : (g : D) ∈ stab x) : IsLab V V₂ (g • y) t := by
  have := hy.smul d g
  rwa [hx.cent d hg] at this

theorem eq_of_isLab (d : Doubled A B z V c V₂) {x y m : CosetGeom (A ⊔ B) A B} {t : D}
    (hx : IsLab V V₂ x t) (hy : IsLab V V₂ y t) (hm : (graph (A ⊔ B) A B).Adj m y)
    (g : ↥(A ⊔ B)) (hg : (g : D) ∈ stab x) (hgm : g • m = m) : g • y = y := by
  by_contra hne
  have hgy := hx.smul_of_mem_stab d hy g hg
  have hadj : (graph (A ⊔ B) A B).Adj m (g • y) := by
    have := (smul_adj g).mpr hm
    rwa [hgm] at this
  have t1 := hy.mem_of_adj d hm
  have t3 := hgy.mem_of_adj d hadj
  exact hy.1 (fx_inf_fx_eq_one d.sys hm hadj (Ne.symm hne) t1 t3)

theorem exists_isLab_pair (h : TwoSys A B z V c V₂) {x y p q : CosetGeom (A ⊔ B) A B}
    (hq : (graph (A ⊔ B) A B).Adj y q) (hp : (graph (A ⊔ B) A B).Adj p x)
    (hxq : Nm A B V V₂ x ≤ ballStab 1 q) (hyp : Nm A B V V₂ y ≤ ballStab 1 p)
    (hnot : ¬ Nm A B V V₂ x ≤ ballStab 1 y) : ∃ t, IsLab V V₂ p t ∧ IsLab V V₂ q t := by
  obtain ⟨t, ht1, htp, htq⟩ := exists_commutator2 h hq hp hxq hyp hnot
  exact ⟨t, ⟨ht1, x, hp.symm, htp⟩, ⟨ht1, y, hq, htq⟩⟩

end GoldAmLab8

end F6

end CFSG.Quasithin

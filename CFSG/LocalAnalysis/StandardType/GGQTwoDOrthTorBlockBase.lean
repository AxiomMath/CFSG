module

public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.LocalAnalysis.SectionRank.SignLines

public section

namespace CFSG.StandardType.QTwo

open TauCeti.QuadraticMap QuadraticMap CFSG.RankThree.Classical2
open scoped commutatorElement

section Block

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]


variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

@[expose] def torFix (W : Submodule k V) : Subgroup (V ≃ₗ[k] V) where
  carrier := {g | ∀ v ∈ W, g v = v}
  mul_mem' := fun {g h} hg hh v hv => by
    change g (h v) = v
    rw [hh v hv, hg v hv]
  one_mem' := fun v _ => rfl
  inv_mem' := fun {g} hg v hv => by
    change g.symm v = v
    rw [LinearEquiv.symm_apply_eq]
    exact (hg v hv).symm

@[expose] def torV₀ (t : V ≃ₗ[k] V) : Submodule k V :=
  LinearMap.ker ((t : V →ₗ[k] V) - LinearMap.id)

@[expose] def torV₁ (t : V ≃ₗ[k] V) : Submodule k V :=
  LinearMap.range ((t : V →ₗ[k] V) - LinearMap.id)

@[expose] def torE₀ (Q : QuadraticForm k V) (t : V ≃ₗ[k] V) : Subgroup (V ≃ₗ[k] V) :=
  orthogonalGroup Q ⊓ torFix (torV₁ t)

@[expose] def torE₁ (Q : QuadraticForm k V) (t : V ≃ₗ[k] V) : Subgroup (V ≃ₗ[k] V) :=
  orthogonalGroup Q ⊓ torFix (torV₀ t) ⊓ Subgroup.centralizer {t}

@[expose] def torP₀ (Q : QuadraticForm k V) (t : V ≃ₗ[k] V) : Subgroup (V ≃ₗ[k] V) :=
  ⁅torE₀ Q t, torE₀ Q t⁆

@[expose] def torP₁ (Q : QuadraticForm k V) (t : V ≃ₗ[k] V) : Subgroup (V ≃ₗ[k] V) :=
  ⁅torE₁ Q t, torE₁ Q t⁆

variable (Q : QuadraticForm k V) {t : V ≃ₗ[k] V}

private lemma plh_three_smul (x : V) : (3 : k) • x = x + x + x := by
  rw [show (3 : k) = 2 + 1 by norm_num, add_smul, two_smul, one_smul]

theorem torV_isCompl (ht3 : t ^ 3 = 1) (h3 : (3 : k) ≠ 0) : IsCompl (torV₀ t) (torV₁ t) := by
  have hτ3 : ((t : V →ₗ[k] V)) ^ 3 = 1 := by
    have h := map_pow (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := k) (M := V)) t 3
    rw [ht3, map_one] at h
    exact h.symm
  have hdisj : Disjoint (torV₀ t) (torV₁ t) := by
    rw [Submodule.disjoint_def]
    intro x hx0 hx1
    rw [torV₀, LinearMap.mem_ker] at hx0
    rw [torV₁, LinearMap.mem_range] at hx1
    obtain ⟨z, hz⟩ := hx1
    have htx : (t : V →ₗ[k] V) x = x := by
      simpa [LinearMap.sub_apply, LinearMap.id_apply] using sub_eq_zero.mp hx0
    have h3x : (3 : k) • x = 0 := by
      have hA : ((1 : V →ₗ[k] V) + (t : V →ₗ[k] V) +
          (t : V →ₗ[k] V) * (t : V →ₗ[k] V)) x = 0 := by
        have hzero : ((1 : V →ₗ[k] V) + (t : V →ₗ[k] V) +
            (t : V →ₗ[k] V) * (t : V →ₗ[k] V)) *
              ((t : V →ₗ[k] V) - (1 : V →ₗ[k] V)) = 0 := by
          have h : ((1 : V →ₗ[k] V) + (t : V →ₗ[k] V) +
              (t : V →ₗ[k] V) * (t : V →ₗ[k] V)) *
                ((t : V →ₗ[k] V) - (1 : V →ₗ[k] V)) =
                  ((t : V →ₗ[k] V)) ^ 3 - (1 : V →ₗ[k] V) := by
            noncomm_ring
          rw [h, hτ3]
          simp
        have hthis := congrArg (fun f : V →ₗ[k] V => f z) hzero
        have hz' : ((t : V →ₗ[k] V) - (1 : V →ₗ[k] V)) z = x := hz
        simpa [Module.End.mul_apply, hz'] using hthis
      have hB : ((1 : V →ₗ[k] V) + (t : V →ₗ[k] V) +
          (t : V →ₗ[k] V) * (t : V →ₗ[k] V)) x = (3 : k) • x := by
        have hτ2x : ((t : V →ₗ[k] V) * (t : V →ₗ[k] V)) x = x := by
          rw [Module.End.mul_apply, htx, htx]
        rw [LinearMap.add_apply, LinearMap.add_apply, Module.End.one_apply, htx, hτ2x]
        rw [plh_three_smul x]
      rw [← hB, hA]
    exact (smul_eq_zero.mp h3x).resolve_left h3
  refine ⟨hdisj, ?_⟩
  rw [codisjoint_iff, Submodule.eq_top_iff']
  intro v
  have h0 : ((1 : V →ₗ[k] V) + (t : V →ₗ[k] V) +
      (t : V →ₗ[k] V) * (t : V →ₗ[k] V)) v ∈ torV₀ t := by
    rw [torV₀, LinearMap.mem_ker]
    have hzero : ((t : V →ₗ[k] V) - (1 : V →ₗ[k] V)) *
        ((1 : V →ₗ[k] V) + (t : V →ₗ[k] V) +
          (t : V →ₗ[k] V) * (t : V →ₗ[k] V)) = 0 := by
      have h : ((t : V →ₗ[k] V) - (1 : V →ₗ[k] V)) *
          ((1 : V →ₗ[k] V) + (t : V →ₗ[k] V) +
            (t : V →ₗ[k] V) * (t : V →ₗ[k] V)) =
              ((t : V →ₗ[k] V)) ^ 3 - (1 : V →ₗ[k] V) := by
        noncomm_ring
      rw [h, hτ3]
      simp
    have hthis := congrArg (fun f : V →ₗ[k] V => f v) hzero
    simpa [Module.End.mul_apply] using hthis
  have h1 : (((1 : V →ₗ[k] V) - (t : V →ₗ[k] V)) *
      ((t : V →ₗ[k] V) + 2)) v ∈ torV₁ t := by
    rw [torV₁, LinearMap.mem_range]
    refine ⟨-((((t : V →ₗ[k] V)) + 2) v), ?_⟩
    rw [map_neg]
    have h : ((t : V →ₗ[k] V) - (LinearMap.id : V →ₗ[k] V)) ((((t : V →ₗ[k] V)) + 2) v) =
        -(((1 : V →ₗ[k] V) - (t : V →ₗ[k] V)) ((((t : V →ₗ[k] V)) + 2) v)) := by
      rw [← neg_sub (LinearMap.id : V →ₗ[k] V) (t : V →ₗ[k] V), LinearMap.neg_apply]
        <;> rfl
    rw [h, neg_neg, Module.End.mul_apply]
  have h3v : (3 : k) • v =
      ((1 : V →ₗ[k] V) + (t : V →ₗ[k] V) +
        (t : V →ₗ[k] V) * (t : V →ₗ[k] V)) v +
          (((1 : V →ₗ[k] V) - (t : V →ₗ[k] V)) *
            ((t : V →ₗ[k] V) + 2)) v := by
    have hthree : (3 : V →ₗ[k] V) =
        ((1 : V →ₗ[k] V) + (t : V →ₗ[k] V) +
          (t : V →ₗ[k] V) * (t : V →ₗ[k] V)) +
            ((1 : V →ₗ[k] V) - (t : V →ₗ[k] V)) * ((t : V →ₗ[k] V) + 2) := by
      noncomm_ring <;> simp [nsmul_one]
    have hthree_apply : (3 : V →ₗ[k] V) v = (3 : k) • v := by
      rw [show (3 : V →ₗ[k] V) = 3 • (1 : V →ₗ[k] V) from (nsmul_one 3).symm,
        LinearMap.smul_apply, Module.End.one_apply]
      exact (Nat.cast_smul_eq_nsmul k 3 v).symm
    have hthis := congrArg (fun f : V →ₗ[k] V => f v) hthree
    rw [hthree_apply] at hthis
    simpa only [LinearMap.add_apply] using hthis
  have hmem : (3 : k) • v ∈ torV₀ t ⊔ torV₁ t := by
    rw [h3v]
    exact Submodule.add_mem_sup h0 h1
  have hv : v = (3 : k)⁻¹ • (3 : k) • v := by
    rw [smul_smul, inv_mul_cancel₀ h3, one_smul]
  rw [hv]
  exact Submodule.smul_mem _ _ hmem

theorem torV_orth (ht : t ∈ orthogonalGroup Q) {u w : V} (hu : u ∈ torV₀ t)
    (hw : w ∈ torV₁ t) : polar Q u w = 0 := by
  rw [torV₀, LinearMap.mem_ker] at hu
  rw [torV₁, LinearMap.mem_range] at hw
  obtain ⟨z, hz⟩ := hw
  have htu : t u = u := by
    simpa [LinearMap.sub_apply, LinearMap.id_apply] using sub_eq_zero.mp hu
  have hz' : w = t z - z := by
    simpa [LinearMap.sub_apply, LinearMap.id_apply] using hz.symm
  have hkey : polar Q u (t z) = polar Q u z := by
    have h := polar_apply_of_mem_orthogonalGroup ht u z
    rwa [htu] at h
  rw [hz', polar_sub_right, hkey, sub_self]

theorem plh_torV₀_map_of_commute {g : V ≃ₗ[k] V} (hg : g * t = t * g) :
    ∀ v ∈ torV₀ t, g v ∈ torV₀ t := by
  intro v hv
  rw [torV₀, LinearMap.mem_ker] at hv ⊢
  have hcomm : ∀ x : V, g (t x) = t (g x) := by
    intro x
    have h := congrArg (fun e : V ≃ₗ[k] V => e x) hg
    simpa [LinearEquiv.mul_apply] using h
  have htv : t v = v := by
    simpa [LinearMap.sub_apply, LinearMap.id_apply] using sub_eq_zero.mp hv
  have hgv : t (g v) = g v := ((hcomm v).symm).trans (congrArg g htv)
  rw [LinearMap.sub_apply, LinearMap.id_apply]
  change t (g v) - g v = 0
  rw [hgv, sub_self]

theorem plh_torV₁_map_of_commute {g : V ≃ₗ[k] V} (hg : g * t = t * g) :
    ∀ v ∈ torV₁ t, g v ∈ torV₁ t := by
  rintro v ⟨z, hz⟩
  have hcomm : ∀ x : V, g (t x) = t (g x) := by
    intro x
    have h := congrArg (fun e : V ≃ₗ[k] V => e x) hg
    simpa [LinearEquiv.mul_apply] using h
  have hz' : t z - z = v := by
    simpa [LinearMap.sub_apply, LinearMap.id_apply] using hz
  refine ⟨g z, ?_⟩
  rw [LinearMap.sub_apply, LinearMap.id_apply]
  change t (g z) - g z = g v
  rw [← hcomm z, ← map_sub, hz']

private lemma plh_torV₀_map_of_mem_torE₀ (ht : t ∈ orthogonalGroup Q) (ht3 : t ^ 3 = 1)
    (h3 : (3 : k) ≠ 0) (hQ : (polarBilin Q).Nondegenerate) {a : V ≃ₗ[k] V}
    (ha : a ∈ torE₀ Q t) {v : V} (hv : v ∈ torV₀ t) : a v ∈ torV₀ t := by
  have hcompl := torV_isCompl ht3 h3
  have havmem : a v ∈ torV₀ t ⊔ torV₁ t := by
    rw [hcompl.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨v₀, hv₀, v₁, hv₁, hsum⟩ := Submodule.mem_sup.mp havmem
  suffices v₁ = 0 by
    have : a v = v₀ := by rw [← hsum, this, add_zero]
    rw [this]
    exact hv₀
  have horth₁ : ∀ w ∈ torV₁ t, polar Q v₁ w = 0 := by
    intro w hw
    have hthis : polar Q (a v) w = 0 := by
      have hainv : a⁻¹ ∈ torE₀ Q t := (torE₀ Q t).inv_mem ha
      have hfix : a (a⁻¹ w) = w := by simp
      rw [← hfix, polar_apply_of_mem_orthogonalGroup ha.1 v (a⁻¹ w)]
      have hw' : a⁻¹ w = w := hainv.2 w hw
      rw [hw']
      exact torV_orth Q ht hv hw
    have hsum' : polar Q (a v) w = polar Q v₀ w + polar Q v₁ w := by
      rw [← hsum, polar_add_left]
    rw [hsum', torV_orth Q ht hv₀ hw, zero_add] at hthis
    exact hthis
  have horth₀ : ∀ w ∈ torV₀ t, polar Q v₁ w = 0 := by
    intro w hw
    rw [polar_comm]
    exact torV_orth Q ht hw hv₁
  have hall : ∀ y : V, polar Q v₁ y = 0 := by
    intro y
    have hymem : y ∈ torV₀ t ⊔ torV₁ t := by
      rw [hcompl.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨y₀, hy₀, y₁, hy₁, hy⟩ := Submodule.mem_sup.mp hymem
    rw [← hy, polar_add_right, horth₀ y₀ hy₀, horth₁ y₁ hy₁, add_zero]
  exact hQ.1 v₁ fun y => by rw [polarBilin_apply_apply]; exact hall y

private lemma plh_torV₁_map_of_mem_torE₁ {b : V ≃ₗ[k] V} (hb : b ∈ torE₁ Q t) {v : V}
    (hv : v ∈ torV₁ t) : b v ∈ torV₁ t := by
  have hcomm : b * t = t * b :=
    ((Subgroup.mem_centralizer_iff.mp hb.2) t (by simp)).symm
  exact plh_torV₁_map_of_commute hcomm v hv

theorem plh_mem_sup_iff_of_commute {G : Type*} [Group G] {A B : Subgroup G}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} :
    x ∈ A ⊔ B ↔ ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  constructor
  · intro hx
    rw [Subgroup.sup_eq_closure] at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with hy | hy
      · exact ⟨y, hy, 1, B.one_mem, by simp⟩
      · exact ⟨1, A.one_mem, y, hy, by simp⟩
    | one => exact ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
    | mul y z hy hz ihy ihz =>
      obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := ihy
      obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := ihz
      refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, b₁ * b₂, B.mul_mem hb₁ hb₂, ?_⟩
      rw [mul_assoc a₁ a₂ (b₁ * b₂), ← mul_assoc a₂ b₁ b₂, hc a₂ ha₂ b₁ hb₁]
      group
    | inv y hy ihy =>
      obtain ⟨a, ha, b, hb, rfl⟩ := ihy
      exact ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb,
        by rw [mul_inv_rev, hc a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb)]⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact Subgroup.mul_mem_sup ha hb

theorem plh_conj_mem_of_mem_sup_of_commute {G : Type*} [Group G] {A B : Subgroup G}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {g : G} (hg : g ∈ A ⊔ B) {n : G} (hn : n ∈ A) :
    g * n * g⁻¹ ∈ A := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (plh_mem_sup_iff_of_commute hc).1 hg
  have hbn : b * n = n * b := (hc n hn b hb).symm
  have heq : a * b * n * (a * b)⁻¹ = a * n * a⁻¹ := by
    rw [mul_inv_rev]
    calc a * b * n * (b⁻¹ * a⁻¹) = a * (b * n) * b⁻¹ * a⁻¹ := by group
      _ = a * (n * b) * b⁻¹ * a⁻¹ := by rw [hbn]
      _ = a * n * a⁻¹ := by group
  rw [heq]
  exact A.mul_mem (A.mul_mem ha hn) (A.inv_mem ha)

theorem torE₀_commute_torE₁ (ht : t ∈ orthogonalGroup Q) (ht3 : t ^ 3 = 1) (h3 : (3 : k) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) {a b : V ≃ₗ[k] V} (ha : a ∈ torE₀ Q t)
    (hb : b ∈ torE₁ Q t) : a * b = b * a := by
  have hcompl := torV_isCompl ht3 h3
  refine LinearEquiv.toLinearMap_injective ?_
  rw [LinearEquiv.coe_toLinearMap_mul, LinearEquiv.coe_toLinearMap_mul]
  apply LinearMap.ext_on_codisjoint hcompl.codisjoint
  · intro v hv
    have hbv : b v = v := hb.1.2 v hv
    have hav₀ : a v ∈ torV₀ t := plh_torV₀_map_of_mem_torE₀ Q ht ht3 h3 hQ ha hv
    have hbav : b (a v) = a v := hb.1.2 (a v) hav₀
    change a (b v) = b (a v)
    rw [hbv, hbav]
  · intro v hv
    have hav : a v = v := ha.2 v hv
    have hbv₁ : b v ∈ torV₁ t := plh_torV₁_map_of_mem_torE₁ Q hb hv
    have habv : a (b v) = b v := ha.2 (b v) hbv₁
    change a (b v) = b (a v)
    rw [hav, habv]

theorem torE₀_le_centralizer (ht : t ∈ orthogonalGroup Q) (ht3 : t ^ 3 = 1) (h3 : (3 : k) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) : torE₀ Q t ≤ Subgroup.centralizer {t} := by
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  rw [hh]
  have hcompl := torV_isCompl ht3 h3
  have htv₀ : ∀ v ∈ torV₀ t, t v = v := by
    intro v hv
    rw [torV₀, LinearMap.mem_ker] at hv
    simpa [LinearMap.sub_apply, LinearMap.id_apply] using sub_eq_zero.mp hv
  refine LinearEquiv.toLinearMap_injective ?_
  rw [LinearEquiv.coe_toLinearMap_mul, LinearEquiv.coe_toLinearMap_mul]
  apply LinearMap.ext_on_codisjoint hcompl.codisjoint
  · intro v hv
    have htv : t v = v := htv₀ v hv
    have hav₀ : a v ∈ torV₀ t := plh_torV₀_map_of_mem_torE₀ Q ht ht3 h3 hQ ha hv
    have htav : t (a v) = a v := htv₀ (a v) hav₀
    change t (a v) = a (t v)
    rw [htv, htav]
  · intro v hv
    have hav : a v = v := ha.2 v hv
    obtain ⟨z, hz⟩ := hv
    have hz' : t z - z = v := by
      simpa [LinearMap.sub_apply, LinearMap.id_apply] using hz
    have htv₁ : t v ∈ torV₁ t := by
      refine ⟨t z, ?_⟩
      rw [LinearMap.sub_apply, LinearMap.id_apply]
      change t (t z) - t z = t v
      rw [← map_sub, hz']
    have ha_tv : a (t v) = t v := ha.2 (t v) htv₁
    change t (a v) = a (t v)
    rw [hav, ha_tv]

theorem torE₁_le_centralizer : torE₁ Q t ≤ Subgroup.centralizer {t} :=
  inf_le_right


end Block

end CFSG.StandardType.QTwo

end

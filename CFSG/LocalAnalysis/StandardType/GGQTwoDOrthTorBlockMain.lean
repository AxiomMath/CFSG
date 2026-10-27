module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthTorBlockBase

public section

namespace CFSG.StandardType.QTwo

open TauCeti.QuadraticMap QuadraticMap CFSG.RankThree.Classical2
open scoped commutatorElement

section Block

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

variable (Q : QuadraticForm k V) {t : V ≃ₗ[k] V}

theorem centralizer_le_torE (ht : t ∈ orthogonalGroup Q) (ht3 : t ^ 3 = 1) (h3 : (3 : k) ≠ 0) :
    orthogonalGroup Q ⊓ Subgroup.centralizer {t} ≤ torE₀ Q t ⊔ torE₁ Q t := by
  intro c hc
  obtain ⟨hcO, hccen⟩ := Subgroup.mem_inf.1 hc
  have hcomm : c * t = t * c :=
    ((Subgroup.mem_centralizer_iff.mp hccen) t (by simp)).symm
  have hcompl := torV_isCompl ht3 h3
  have hcV₀ : ∀ v ∈ torV₀ t, c v ∈ torV₀ t := plh_torV₀_map_of_commute hcomm
  have hcV₁ : ∀ v ∈ torV₁ t, c v ∈ torV₁ t := plh_torV₁_map_of_commute hcomm
  have hcomminv : c⁻¹ * t = t * c⁻¹ :=
    (show Commute c t from hcomm).inv_left.eq
  have hcV₀inv : ∀ v ∈ torV₀ t, c⁻¹ v ∈ torV₀ t := plh_torV₀_map_of_commute hcomminv
  have hcV₁inv : ∀ v ∈ torV₁ t, c⁻¹ v ∈ torV₁ t := plh_torV₁_map_of_commute hcomminv
  let π : V →ₗ[k] V := (torV₀ t).projection (torV₁ t) hcompl
  have hπ₀ : ∀ v ∈ torV₀ t, π v = v := fun v hv =>
    Submodule.projection_apply_of_mem_left hcompl hv
  have hπ₁ : ∀ v ∈ torV₁ t, π v = 0 := fun v hv =>
    Submodule.projection_apply_of_mem_right hcompl hv
  let c₀lm : V →ₗ[k] V := (c : V →ₗ[k] V) * π + ((1 : V →ₗ[k] V) - π)
  let c₁lm : V →ₗ[k] V := π + (c : V →ₗ[k] V) * ((1 : V →ₗ[k] V) - π)
  let d₀lm : V →ₗ[k] V := ((c⁻¹ : V ≃ₗ[k] V) : V →ₗ[k] V) * π + ((1 : V →ₗ[k] V) - π)
  let d₁lm : V →ₗ[k] V := π + ((c⁻¹ : V ≃ₗ[k] V) : V →ₗ[k] V) * ((1 : V →ₗ[k] V) - π)
  have c₀_V₀ : ∀ v ∈ torV₀ t, c₀lm v = c v := by
    intro v hv
    change ((c : V →ₗ[k] V) * π + ((1 : V →ₗ[k] V) - π)) v = c v
    rw [LinearMap.add_apply, Module.End.mul_apply, LinearMap.sub_apply,
      Module.End.one_apply, hπ₀ v hv, sub_self, add_zero] <;> rfl
  have c₀_V₁ : ∀ v ∈ torV₁ t, c₀lm v = v := by
    intro v hv
    change ((c : V →ₗ[k] V) * π + ((1 : V →ₗ[k] V) - π)) v = v
    rw [LinearMap.add_apply, Module.End.mul_apply, LinearMap.sub_apply,
      Module.End.one_apply, hπ₁ v hv, map_zero, zero_add, sub_zero] <;> rfl
  have c₁_V₀ : ∀ v ∈ torV₀ t, c₁lm v = v := by
    intro v hv
    change (π + (c : V →ₗ[k] V) * ((1 : V →ₗ[k] V) - π)) v = v
    rw [LinearMap.add_apply, Module.End.mul_apply, LinearMap.sub_apply,
      Module.End.one_apply, hπ₀ v hv, sub_self, map_zero, add_zero] <;> rfl
  have c₁_V₁ : ∀ v ∈ torV₁ t, c₁lm v = c v := by
    intro v hv
    change (π + (c : V →ₗ[k] V) * ((1 : V →ₗ[k] V) - π)) v = c v
    rw [LinearMap.add_apply, Module.End.mul_apply, LinearMap.sub_apply,
      Module.End.one_apply, hπ₁ v hv, sub_zero, zero_add] <;> rfl
  have d₀_V₀ : ∀ v ∈ torV₀ t, d₀lm v = c⁻¹ v := by
    intro v hv
    change (((c⁻¹ : V ≃ₗ[k] V) : V →ₗ[k] V) * π + ((1 : V →ₗ[k] V) - π)) v = c⁻¹ v
    rw [LinearMap.add_apply, Module.End.mul_apply, LinearMap.sub_apply,
      Module.End.one_apply, hπ₀ v hv, sub_self, add_zero] <;> rfl
  have d₀_V₁ : ∀ v ∈ torV₁ t, d₀lm v = v := by
    intro v hv
    change (((c⁻¹ : V ≃ₗ[k] V) : V →ₗ[k] V) * π + ((1 : V →ₗ[k] V) - π)) v = v
    rw [LinearMap.add_apply, Module.End.mul_apply, LinearMap.sub_apply,
      Module.End.one_apply, hπ₁ v hv, map_zero, zero_add, sub_zero] <;> rfl
  have d₁_V₀ : ∀ v ∈ torV₀ t, d₁lm v = v := by
    intro v hv
    change (π + ((c⁻¹ : V ≃ₗ[k] V) : V →ₗ[k] V) * ((1 : V →ₗ[k] V) - π)) v = v
    rw [LinearMap.add_apply, Module.End.mul_apply, LinearMap.sub_apply,
      Module.End.one_apply, hπ₀ v hv, sub_self, map_zero, add_zero] <;> rfl
  have d₁_V₁ : ∀ v ∈ torV₁ t, d₁lm v = c⁻¹ v := by
    intro v hv
    change (π + ((c⁻¹ : V ≃ₗ[k] V) : V →ₗ[k] V) * ((1 : V →ₗ[k] V) - π)) v = c⁻¹ v
    rw [LinearMap.add_apply, Module.End.mul_apply, LinearMap.sub_apply,
      Module.End.one_apply, hπ₁ v hv, sub_zero, zero_add] <;> rfl
  have hcomp₀ : c₀lm.comp d₀lm = LinearMap.id := by
    apply LinearMap.ext_on_codisjoint hcompl.codisjoint
    · intro v hv
      rw [LinearMap.comp_apply, LinearMap.id_apply, d₀_V₀ v hv,
        c₀_V₀ (c⁻¹ v) (hcV₀inv v hv)]
      simp
    · intro v hv
      rw [LinearMap.comp_apply, LinearMap.id_apply, d₀_V₁ v hv, c₀_V₁ v hv]
  have hcomp₀' : d₀lm.comp c₀lm = LinearMap.id := by
    apply LinearMap.ext_on_codisjoint hcompl.codisjoint
    · intro v hv
      rw [LinearMap.comp_apply, LinearMap.id_apply, c₀_V₀ v hv,
        d₀_V₀ (c v) (hcV₀ v hv)]
      simp
    · intro v hv
      rw [LinearMap.comp_apply, LinearMap.id_apply, c₀_V₁ v hv, d₀_V₁ v hv]
  have hcomp₁ : c₁lm.comp d₁lm = LinearMap.id := by
    apply LinearMap.ext_on_codisjoint hcompl.codisjoint
    · intro v hv
      rw [LinearMap.comp_apply, LinearMap.id_apply, d₁_V₀ v hv, c₁_V₀ v hv]
    · intro v hv
      rw [LinearMap.comp_apply, LinearMap.id_apply, d₁_V₁ v hv,
        c₁_V₁ (c⁻¹ v) (hcV₁inv v hv)]
      simp
  have hcomp₁' : d₁lm.comp c₁lm = LinearMap.id := by
    apply LinearMap.ext_on_codisjoint hcompl.codisjoint
    · intro v hv
      rw [LinearMap.comp_apply, LinearMap.id_apply, c₁_V₀ v hv, d₁_V₀ v hv]
    · intro v hv
      rw [LinearMap.comp_apply, LinearMap.id_apply, c₁_V₁ v hv,
        d₁_V₁ (c v) (hcV₁ v hv)]
      simp
  let c₀ : V ≃ₗ[k] V := LinearEquiv.ofLinearMap c₀lm d₀lm hcomp₀ hcomp₀'
  let c₁ : V ≃ₗ[k] V := LinearEquiv.ofLinearMap c₁lm d₁lm hcomp₁ hcomp₁'
  have hc₀O : c₀ ∈ orthogonalGroup Q := by
    rw [mem_orthogonalGroup_iff]
    intro v
    have hv : v ∈ torV₀ t ⊔ torV₁ t := by
      rw [hcompl.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨v₀, hv₀, v₁, hv₁, hvsum⟩ := Submodule.mem_sup.mp hv
    have hc₀v : c₀ v = c v₀ + v₁ := by
      rw [← hvsum, map_add]
      congr 1
      · change c₀lm v₀ = c v₀
        exact c₀_V₀ v₀ hv₀
      · change c₀lm v₁ = v₁
        exact c₀_V₁ v₁ hv₁
    rw [hc₀v, ← hvsum]
    simp only [QuadraticMap.map_add]
    rw [torV_orth Q ht (hcV₀ v₀ hv₀) hv₁, torV_orth Q ht hv₀ hv₁,
      mem_orthogonalGroup_iff.mp hcO v₀]
  have hc₀fix : c₀ ∈ torFix (torV₁ t) := fun v hv => by
    change c₀lm v = v
    exact c₀_V₁ v hv
  have hc₀E₀ : c₀ ∈ torE₀ Q t := ⟨hc₀O, hc₀fix⟩
  have hc₁O : c₁ ∈ orthogonalGroup Q := by
    rw [mem_orthogonalGroup_iff]
    intro v
    have hv : v ∈ torV₀ t ⊔ torV₁ t := by
      rw [hcompl.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨v₀, hv₀, v₁, hv₁, hvsum⟩ := Submodule.mem_sup.mp hv
    have hc₁v : c₁ v = v₀ + c v₁ := by
      rw [← hvsum, map_add]
      congr 1
      · change c₁lm v₀ = v₀
        exact c₁_V₀ v₀ hv₀
      · change c₁lm v₁ = c v₁
        exact c₁_V₁ v₁ hv₁
    rw [hc₁v, ← hvsum]
    simp only [QuadraticMap.map_add]
    rw [torV_orth Q ht hv₀ (hcV₁ v₁ hv₁), torV_orth Q ht hv₀ hv₁,
      mem_orthogonalGroup_iff.mp hcO v₁]
  have hc₁fix : c₁ ∈ torFix (torV₀ t) := fun v hv => by
    change c₁lm v = v
    exact c₁_V₀ v hv
  have hc₁cen : c₁ * t = t * c₁ := by
    refine LinearEquiv.toLinearMap_injective ?_
    rw [LinearEquiv.coe_toLinearMap_mul, LinearEquiv.coe_toLinearMap_mul]
    apply LinearMap.ext_on_codisjoint hcompl.codisjoint
    · intro v hv
      have htv : t v = v := by
        have hv' : v ∈ torV₀ t := hv
        rw [torV₀, LinearMap.mem_ker] at hv'
        simpa [LinearMap.sub_apply, LinearMap.id_apply] using sub_eq_zero.mp hv'
      have hc₁v : c₁ v = v := by
        change c₁lm v = v
        exact c₁_V₀ v hv
      change c₁ (t v) = t (c₁ v)
      rw [htv, hc₁v, htv]
    · intro v hv
      have htv₁ : t v ∈ torV₁ t := plh_torV₁_map_of_commute (g := t) rfl v hv
      have hc₁tv : c₁ (t v) = c (t v) := by
        change c₁lm (t v) = c (t v)
        exact c₁_V₁ (t v) htv₁
      have hc₁v : c₁ v = c v := by
        change c₁lm v = c v
        exact c₁_V₁ v hv
      have hctv : t (c v) = c (t v) := by
        have h := congrArg (fun e : V ≃ₗ[k] V => e v) hcomm
        have h' : c (t v) = t (c v) := by simpa [LinearEquiv.mul_apply] using h
        exact h'.symm
      change c₁ (t v) = t (c₁ v)
      rw [hc₁tv, hc₁v, hctv]
  have hc₁E₁ : c₁ ∈ torE₁ Q t :=
    ⟨⟨hc₁O, hc₁fix⟩, Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact hc₁cen.symm⟩
  have heq : c = c₀ * c₁ := by
    refine LinearEquiv.toLinearMap_injective ?_
    rw [LinearEquiv.coe_toLinearMap_mul]
    apply LinearMap.ext_on_codisjoint hcompl.codisjoint
    · intro v hv
      have hc₁v : c₁ v = v := by
        change c₁lm v = v
        exact c₁_V₀ v hv
      have hc₀v : c₀ v = c v := by
        change c₀lm v = c v
        exact c₀_V₀ v hv
      change c v = c₀ (c₁ v)
      rw [hc₁v, hc₀v]
    · intro v hv
      have hc₁v : c₁ v = c v := by
        change c₁lm v = c v
        exact c₁_V₁ v hv
      have hcv₁ : c v ∈ torV₁ t := hcV₁ v hv
      have hc₀cv : c₀ (c v) = c v := by
        change c₀lm (c v) = c v
        exact c₀_V₁ (c v) hcv₁
      change c v = c₀ (c₁ v)
      rw [hc₁v, hc₀cv]
  have hmem : c₀ * c₁ ∈ torE₀ Q t ⊔ torE₁ Q t := Subgroup.mul_mem_sup hc₀E₀ hc₁E₁
  rwa [← heq] at hmem

theorem torE₀_normal (ht : t ∈ orthogonalGroup Q) (ht3 : t ^ 3 = 1) (h3 : (3 : k) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) :
    ((torE₀ Q t).subgroupOf (orthogonalGroup Q ⊓ Subgroup.centralizer {t})).Normal := by
  have hle : torE₀ Q t ≤ orthogonalGroup Q ⊓ Subgroup.centralizer {t} :=
    fun a ha => ⟨ha.1, torE₀_le_centralizer Q ht ht3 h3 hQ ha⟩
  refine (Subgroup.normal_subgroupOf_iff hle).mpr ?_
  intro h k hh hk
  exact plh_conj_mem_of_mem_sup_of_commute
    (fun a ha b hb => torE₀_commute_torE₁ Q ht ht3 h3 hQ ha hb)
    (centralizer_le_torE Q ht ht3 h3 hk) hh

theorem torE₁_normal (ht : t ∈ orthogonalGroup Q) (ht3 : t ^ 3 = 1) (h3 : (3 : k) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) :
    ((torE₁ Q t).subgroupOf (orthogonalGroup Q ⊓ Subgroup.centralizer {t})).Normal := by
  have hle : torE₁ Q t ≤ orthogonalGroup Q ⊓ Subgroup.centralizer {t} :=
    fun a ha => ⟨ha.1.1, ha.2⟩
  refine (Subgroup.normal_subgroupOf_iff hle).mpr ?_
  intro h k hh hk
  have hk' : k ∈ torE₁ Q t ⊔ torE₀ Q t := by
    have hk'' := centralizer_le_torE Q ht ht3 h3 hk
    rwa [sup_comm] at hk''
  exact plh_conj_mem_of_mem_sup_of_commute
    (fun a ha b hb => (torE₀_commute_torE₁ Q ht ht3 h3 hQ hb ha).symm) hk' hh

theorem torP₀_normal (ht : t ∈ orthogonalGroup Q) (ht3 : t ^ 3 = 1) (h3 : (3 : k) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) :
    ((torP₀ Q t).subgroupOf (orthogonalGroup Q ⊓ Subgroup.centralizer {t})).Normal := by
  have hle : torP₀ Q t ≤ orthogonalGroup Q ⊓ Subgroup.centralizer {t} := by
    refine le_inf ?_ ?_
    · exact (Subgroup.commutator_mono
        (inf_le_left : torE₀ Q t ≤ orthogonalGroup Q)
        (inf_le_left : torE₀ Q t ≤ orthogonalGroup Q)).trans
          (Subgroup.commutator_le_self (orthogonalGroup Q))
    · exact (Subgroup.commutator_le_self (torE₀ Q t)).trans
        (torE₀_le_centralizer Q ht ht3 h3 hQ)
  refine (Subgroup.normal_subgroupOf_iff hle).mpr ?_
  intro h k hh hk
  have hE0le : torE₀ Q t ≤ orthogonalGroup Q ⊓ Subgroup.centralizer {t} :=
    fun a ha => ⟨ha.1, torE₀_le_centralizer Q ht ht3 h3 hQ ha⟩
  have hconj : ∀ e ∈ torE₀ Q t, k * e * k⁻¹ ∈ torE₀ Q t := fun e he =>
    (Subgroup.normal_subgroupOf_iff hE0le).mp (torE₀_normal Q ht ht3 h3 hQ) e k he hk
  have hmap : (torP₀ Q t).map (MulAut.conj k).toMonoidHom ≤ torP₀ Q t := by
    have hKE : (torE₀ Q t).map (MulAut.conj k).toMonoidHom ≤ torE₀ Q t := by
      rintro x ⟨e, he, rfl⟩
      exact hconj e he
    calc (torP₀ Q t).map (MulAut.conj k).toMonoidHom
        = ⁅(torE₀ Q t).map (MulAut.conj k).toMonoidHom,
            (torE₀ Q t).map (MulAut.conj k).toMonoidHom⁆ := by
          rw [torP₀, Subgroup.map_commutator]
      _ ≤ ⁅torE₀ Q t, torE₀ Q t⁆ := Subgroup.commutator_mono hKE hKE
      _ = torP₀ Q t := rfl
  exact hmap ⟨h, hh, rfl⟩

theorem torP₁_normal (ht : t ∈ orthogonalGroup Q) (ht3 : t ^ 3 = 1) (h3 : (3 : k) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) :
    ((torP₁ Q t).subgroupOf (orthogonalGroup Q ⊓ Subgroup.centralizer {t})).Normal := by
  have hle : torP₁ Q t ≤ orthogonalGroup Q ⊓ Subgroup.centralizer {t} := by
    refine le_inf ?_ ?_
    · exact (Subgroup.commutator_mono
        ((inf_le_left.trans inf_le_left) : torE₁ Q t ≤ orthogonalGroup Q)
        ((inf_le_left.trans inf_le_left) : torE₁ Q t ≤ orthogonalGroup Q)).trans
          (Subgroup.commutator_le_self (orthogonalGroup Q))
    · exact (Subgroup.commutator_le_self (torE₁ Q t)).trans (torE₁_le_centralizer Q)
  refine (Subgroup.normal_subgroupOf_iff hle).mpr ?_
  intro h k hh hk
  have hE1le : torE₁ Q t ≤ orthogonalGroup Q ⊓ Subgroup.centralizer {t} :=
    fun a ha => ⟨ha.1.1, ha.2⟩
  have hconj : ∀ e ∈ torE₁ Q t, k * e * k⁻¹ ∈ torE₁ Q t := fun e he =>
    (Subgroup.normal_subgroupOf_iff hE1le).mp (torE₁_normal Q ht ht3 h3 hQ) e k he hk
  have hmap : (torP₁ Q t).map (MulAut.conj k).toMonoidHom ≤ torP₁ Q t := by
    have hKE : (torE₁ Q t).map (MulAut.conj k).toMonoidHom ≤ torE₁ Q t := by
      rintro x ⟨e, he, rfl⟩
      exact hconj e he
    calc (torP₁ Q t).map (MulAut.conj k).toMonoidHom
        = ⁅(torE₁ Q t).map (MulAut.conj k).toMonoidHom,
            (torE₁ Q t).map (MulAut.conj k).toMonoidHom⁆ := by
          rw [torP₁, Subgroup.map_commutator]
      _ ≤ ⁅torE₁ Q t, torE₁ Q t⁆ := Subgroup.commutator_mono hKE hKE
      _ = torP₁ Q t := rfl
  exact hmap ⟨h, hh, rfl⟩

theorem torP₀_le (ht : t ∈ orthogonalGroup Q) (ht3 : t ^ 3 = 1) (h3 : (3 : k) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) :
    torP₀ Q t ≤ orthDerived Q ⊓ Subgroup.centralizer {t} := by
  refine le_inf ?_ ?_
  · exact Subgroup.commutator_mono inf_le_left inf_le_left
  · exact (Subgroup.commutator_le_self (torE₀ Q t)).trans
      (torE₀_le_centralizer Q ht ht3 h3 hQ)

theorem torP₁_le : torP₁ Q t ≤ orthDerived Q ⊓ Subgroup.centralizer {t} := by
  refine le_inf ?_ ?_
  · exact Subgroup.commutator_mono (inf_le_left.trans inf_le_left)
      (inf_le_left.trans inf_le_left)
  · exact (Subgroup.commutator_le_self (torE₁ Q t)).trans (torE₁_le_centralizer Q)

theorem torP_commute (ht : t ∈ orthogonalGroup Q) (ht3 : t ^ 3 = 1) (h3 : (3 : k) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) {a b : V ≃ₗ[k] V} (ha : a ∈ torP₀ Q t)
    (hb : b ∈ torP₁ Q t) : a * b = b * a :=
  torE₀_commute_torE₁ Q ht ht3 h3 hQ
    (Subgroup.commutator_le_self (torE₀ Q t) ha)
    (Subgroup.commutator_le_self (torE₁ Q t) hb)

theorem perfect_le_torP (ht : t ∈ orthogonalGroup Q) (ht3 : t ^ 3 = 1) (h3 : (3 : k) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) {J : Subgroup (V ≃ₗ[k] V)}
    (hJ : J ≤ orthogonalGroup Q ⊓ Subgroup.centralizer {t}) (hperf : ⁅J, J⁆ = J) :
    J ≤ torP₀ Q t ⊔ torP₁ Q t := by
  have hcomm : ∀ a ∈ torE₀ Q t, ∀ b ∈ torE₁ Q t, a * b = b * a :=
    fun a ha b hb => torE₀_commute_torE₁ Q ht ht3 h3 hQ ha hb
  have hJ' : J ≤ torE₀ Q t ⊔ torE₁ Q t := hJ.trans (centralizer_le_torE Q ht ht3 h3)
  have hle : ⁅J, J⁆ ≤ torP₀ Q t ⊔ torP₁ Q t := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := (plh_mem_sup_iff_of_commute hcomm).1 (hJ' hx)
    obtain ⟨a', ha', b', hb', rfl⟩ := (plh_mem_sup_iff_of_commute hcomm).1 (hJ' hy)
    have hb'b : ⁅b, b'⁆ ∈ torE₁ Q t :=
      Subgroup.commutator_le_self (torE₁ Q t) (Subgroup.commutator_mem_commutator hb hb')
    have ha'a : ⁅a, a'⁆ ∈ torE₀ Q t :=
      Subgroup.commutator_le_self (torE₀ Q t) (Subgroup.commutator_mem_commutator ha ha')
    have hbc : Commute b a' := (torE₀_commute_torE₁ Q ht ht3 h3 hQ ha' hb).symm
    have had : Commute a b' := torE₀_commute_torE₁ Q ht ht3 h3 hQ ha hb'
    have hcbd : Commute a' ⁅b, b'⁆ := torE₀_commute_torE₁ Q ht ht3 h3 hQ ha' hb'b
    have habd : Commute a ⁅b, b'⁆ := torE₀_commute_torE₁ Q ht ht3 h3 hQ ha hb'b
    have hcomm2 : Commute ⁅a, a'⁆ ⁅b, b'⁆ := torE₀_commute_torE₁ Q ht ht3 h3 hQ ha'a hb'b
    rw [TauCeti.commutatorElement_mul_mul_eq_mul_of_commute hbc had hcbd habd hcomm2]
    exact Subgroup.mul_mem_sup (Subgroup.commutator_mem_commutator ha ha')
      (Subgroup.commutator_mem_commutator hb hb')
  rwa [← hperf]

end Block

end CFSG.StandardType.QTwo

end

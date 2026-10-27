module

public import CFSG.Sporadic.Schreier.J1Centralizer
public import CFSG.Sporadic.Schreier.MathieuOddCoreTransport
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Blueprint

@[expose] noncomputable def j1CentEquiv
    (t : NativeSporadic.J1) :
    Subgroup.centralizer ({t} : Set NativeSporadic.J1) ≃*
      centralizerIn j1P (j1PermEquiv t : Equiv.Perm (Fin 3080)) :=
  ((MulEquiv.subgroupMap j1PermEquiv _).trans
    (MulEquiv.subgroupCongr (map_centralizer_equiv j1PermEquiv t))).trans
    ((Subgroup.equivMapOfInjective _ j1P.subtype j1P.subtype_injective).trans
      (MulEquiv.subgroupCongr (map_centralizer_subtype j1P (j1PermEquiv t))))

theorem normal_subgroupOf_of_card {M : Type*} [Group M] {K C : Subgroup M} (hKC : K ≤ C)
    {k : ℕ} (hk : 0 < k) (hK : Nat.card K = k) (hC : Nat.card C = 2 * k) :
    (K.subgroupOf C).Normal := by
  apply Subgroup.normal_of_index_eq_two
  have h := Subgroup.card_mul_index (K.subgroupOf C)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKC).toEquiv, hK, hC] at h
  exact Nat.eq_of_mul_eq_mul_left hk (by rw [h, mul_comm])

theorem qt_unique_j1_involution_centralizer_normal_simple_subgroup
    (t : NativeSporadic.J1)
    (ht : orderOf t = 2) :
    ∃ K : Subgroup (Subgroup.centralizer ({t} : Set NativeSporadic.J1)),
      K.Normal ∧ IsSimpleGroup K ∧ Nat.card K = 60 ∧ (∃ x y : K, x * y ≠ y * x) ∧
        CFSG.IsComponent K := by
  set u : Equiv.Perm (Fin 3080) := ((j1PermEquiv t : j1P) : Equiv.Perm (Fin 3080))
  have hu : u ∈ j1P := (j1PermEquiv t).2
  have hou : orderOf u = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact ht
  obtain ⟨hC, -, K, hKC, hK60, hKs, x, hx, y, hy, hxy⟩ := j1P_involution_centralizer u hu hou
  set C := centralizerIn j1P u
  set Φ := j1CentEquiv t
  have hnC : (K.subgroupOf C).Normal :=
    normal_subgroupOf_of_card hKC (by norm_num) hK60 (by rw [hC])
  set K' := (K.subgroupOf C).comap Φ.toMonoidHom
  have hK'n : K'.Normal := Subgroup.Normal.comap hnC _
  have hmap : K'.map Φ.toMonoidHom = K.subgroupOf C :=
    Subgroup.map_comap_eq_self_of_surjective Φ.surjective _
  let e : K' ≃* K := ((Subgroup.equivMapOfInjective K' Φ.toMonoidHom Φ.injective).trans
    (MulEquiv.subgroupCongr hmap)).trans (Subgroup.subgroupOfEquivOfLe hKC)
  have hs : IsSimpleGroup K' := MulEquiv.isSimpleGroup e
  have hne : e.symm ⟨x, hx⟩ * e.symm ⟨y, hy⟩ ≠ e.symm ⟨y, hy⟩ * e.symm ⟨x, hx⟩ := by
    intro h
    apply hxy
    have h' := congrArg e h
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h'
    exact congrArg Subtype.val h'
  refine ⟨K', hK'n, hs, by rw [Nat.card_congr e.toEquiv, hK60], ⟨_, _, hne⟩, ?_, ?_⟩
  · exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup ⟨_, _, hne⟩).1
  · exact hK'n.isSubnormal

end CFSG.Sporadic.Schreier

module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.L514.Setup

public section

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L69

variable {Γ : Type*} [Group Γ]

theorem map_conj_eq_self_iff {J : Subgroup Γ} {a : Γ} :
    J.map (MulAut.conj a).toMonoidHom = J ↔ a ∈ Subgroup.normalizer (J : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff'']
  constructor
  · intro h x
    exact (show x ∈ J ↔ x ∈ J.map (MulAut.conj a).toMonoidHom by rw [h]).trans
      L514.mem_map_conj_iff
  · intro h
    ext x
    rw [L514.mem_map_conj_iff, ← h x]

theorem map_conj_one (J : Subgroup Γ) : J.map (MulAut.conj (1 : Γ)).toMonoidHom = J := by
  ext x
  rw [L514.mem_map_conj_iff]
  simp

theorem mem_normalizer_map_conj {J : Subgroup Γ} {v c : Γ}
    (hv : v ∈ Subgroup.normalizer (J : Set Γ)) (hvc : v * c = c * v) :
    v ∈ Subgroup.normalizer ((J.map (MulAut.conj c).toMonoidHom : Subgroup Γ) : Set Γ) := by
  rw [← map_conj_eq_self_iff] at hv ⊢
  rw [L514.map_conj_map_conj, hvc, ← L514.map_conj_map_conj, hv]

theorem mem_centralizer_map_conj {J : Subgroup Γ} {v c : Γ}
    (hv : v ∈ Subgroup.centralizer (J : Set Γ)) (hvc : v * c = c * v) :
    v ∈ Subgroup.centralizer ((J.map (MulAut.conj c).toMonoidHom : Subgroup Γ) : Set Γ) := by
  rw [Subgroup.mem_centralizer_iff] at hv ⊢
  rintro _ ⟨y, hy, rfl⟩
  have hc : Commute v c := hvc
  have hy' : Commute v y := (hv y hy).symm
  exact ((hc.mul_right hy').mul_right hc.inv_right).eq.symm

theorem mem_normalizer_sup {S T : Subgroup Γ} {a : Γ}
    (hS : a ∈ Subgroup.normalizer (S : Set Γ)) (hT : a ∈ Subgroup.normalizer (T : Set Γ)) :
    a ∈ Subgroup.normalizer ((S ⊔ T : Subgroup Γ) : Set Γ) := by
  rw [← map_conj_eq_self_iff] at hS hT ⊢
  rw [Subgroup.map_sup, hS, hT]

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L69

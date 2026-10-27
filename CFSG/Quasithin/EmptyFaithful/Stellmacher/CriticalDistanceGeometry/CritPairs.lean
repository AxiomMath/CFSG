module

public import CFSG.Quasithin.EmptyFaithful.SzF53BasE

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S152X CFSG.Quasithin.F7

namespace F53

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

open CosetGeom

theorem zvCentral_of_comm (hA : F53Amalgam H M S) {α β α' : Geo H M} (hc : IsCritData α β α')
    (h1 : ⁅Zv α, Zv α'⁆ = ⊥) : Zv β ≤ centerOf (stab β) := by
  have hle : Zv α ≤ stab α' :=
    Zv_le_stab_of_dist_le hA (by rw [hc.dist_eq, hc.bAt_eq])
  have hZ : Zv α' = quasithinOmegaOneCenter (stab α') := by
    rcases centralizer_Zv_dichotomy hA α' with hQ | hZ
    · exfalso
      apply hc.not_le
      rw [← hQ]
      exact le_inf hle (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1)
    · exact hZ
  have hαβ : vtype α ≠ vtype β := vtype_ne_of_adj hc.adj
  have hty : vtype α' = vtype β := by
    by_contra hne
    have hv : vtype α = vtype α' := by
      cases h1 : vtype α <;> cases h2 : vtype α' <;> cases h3 : vtype β <;> simp_all
    have hb' : bAt α' = bMin H M := by
      rw [← bAt_eq_of_vtype_eq hv]; exact hc.bAt_eq
    have h12 := centralizer_Zv_eq_Qv_of_bAt hA hb'
    have hcen : stab α' ≤ Subgroup.centralizer (Zv α' : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hz' : z ∈ centerOf (stab α') := omegaOneCenter_le_centerOf_self _ (hZ ▸ hz)
      exact ((Subgroup.mem_centralizer_iff.mp hz'.2) x hx).symm
    have : stab α' ⊓ Subgroup.centralizer (Zv α' : Set G) = stab α' := inf_eq_left.mpr hcen
    rw [this] at h12
    exact pCoreOf_ne_stab hA α' h12.symm
  have hZβ := Zv_central_of_conj hA hty hZ
  rw [hZβ]
  exact omegaOneCenter_le_centerOf_self _

theorem comm_ne_bot_of_not_central (hA : F53Amalgam H M S) {α β α' : Geo H M}
    (hc : IsCritData α β α') (hn : ¬ Zv β ≤ centerOf (stab β)) : ⁅Zv α, Zv α'⁆ ≠ ⊥ :=
  fun h => hn (zvCentral_of_comm hA hc h)

theorem not_le_Qv_of_comm_ne (hA : F53Amalgam H M S) {α α' : Geo H M}
    (h : ⁅Zv α, Zv α'⁆ ≠ ⊥) : ¬ Zv α' ≤ Qv α := by
  intro hle
  apply h
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact fun x hx => Subgroup.centralizer_le hle ((Zv_le_centerOf_Qv hA α hx).2)

theorem Zv_le_stab_of_comm_ne (hA : F53Amalgam H M S) {α β α' : Geo H M} (hc : IsCritData α β α')
    (h : ⁅Zv α, Zv α'⁆ ≠ ⊥) : bAt α' = bMin H M ∧ Zv α' ≤ stab α := by
  have hcp : IsCritPair₁ α α' := ⟨hc.not_le, hc.dist_eq⟩
  obtain ⟨-, hα'⟩ := crit_bAt_eq hA hcp h
  refine ⟨hα', Zv_le_stab_of_dist_le hA ?_⟩
  rw [CosetGeom.dist_comm, hc.dist_eq, hα']

theorem exists_critData_symm (hA : F53Amalgam H M S) {α β α' : Geo H M} (hc : IsCritData α β α')
    (h : ⁅Zv α, Zv α'⁆ ≠ ⊥) : ∃ β' : Geo H M, IsCritData α' β' α := by
  obtain ⟨hα', -⟩ := Zv_le_stab_of_comm_ne hA hc h
  have hb := bMin_pos hA
  obtain ⟨β', hβ', hd⟩ := exists_adj_dist_eq hA.amalgam.gen (α := α) (δ := α') (d := bMin H M - 1)
    (by rw [hc.dist_eq]; omega)
  refine ⟨β', hβ', hα', ?_, ?_, not_le_Qv_of_comm_ne hA h⟩
  · rw [CosetGeom.dist_comm, hc.dist_eq]
  · rw [CosetGeom.dist_comm, hd]; omega

end F53

end CFSG.Quasithin

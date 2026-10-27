module

public import CFSG.LargeExtraspecial.S12DWSetting
public import CFSG.LargeExtraspecial.O62Normalizer
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson

open Subgroup Module QuadraticMap CFSG.Open CFSG.LargeExtraspecial
open CFSG.RankThree.OrthogonalInvolutions CFSG.GroupTheory.WeirSylow

section Orthogonal

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem natCard_orthogonalGroup_of_finrank_eight (hQ : Q.polarBilin.Nondegenerate)
    (h8 : finrank (ZMod 2) V = 8) :
    (IsPlusType Q ∧ Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 348364800) ∨
      (¬ IsPlusType Q ∧ Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 394813440) := by
  have hdim : finrank (ZMod 2) V = 2 * (3 + 1) := by rw [h8]
  by_cases hp : IsPlusType Q
  · refine Or.inl ⟨hp, ?_⟩
    have h := natCard_orthogonalGroup_of_type hQ hdim (ε := 1) (Or.inl ⟨rfl, hp⟩)
    rw [Nat.card_zmod] at h
    have h2 : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) = 348364800 :=
      h.trans (by decide)
    exact_mod_cast h2
  · refine Or.inr ⟨hp, ?_⟩
    have h := natCard_orthogonalGroup_of_type hQ hdim (ε := -1) (Or.inr ⟨rfl, hp⟩)
    rw [Nat.card_zmod] at h
    have h2 : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) = 394813440 :=
      h.trans (by decide)
    exact_mod_cast h2

theorem isPlusType_and_map_eq_omegaGroup_of_card (hQ : Q.polarBilin.Nondegenerate)
    (h8 : finrank (ZMod 2) V = 8) (H : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hH : Nat.card H = 174182400) :
    IsPlusType Q ∧ H.map (TauCeti.QuadraticMap.orthogonalGroup Q).subtype = omegaGroup Q hQ := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  have hdvd : 174182400 ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) :=
    hH ▸ Subgroup.card_subgroup_dvd_card H
  have hO : IsPlusType Q ∧ Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 348364800 := by
    rcases natCard_orthogonalGroup_of_finrank_eight hQ h8 with h | ⟨-, h⟩
    · exact h
    · rw [h] at hdvd
      exact absurd hdvd (by norm_num)
  refine ⟨hO.1, ?_⟩
  have hidx : H.index = 2 := by
    have h1 := Subgroup.card_mul_index H
    rw [hH, hO.2] at h1
    omega
  have : H.Normal := Subgroup.normal_of_index_eq_two hidx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardq : Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q ⧸ H) = 2 := by
    rw [← Subgroup.index_eq_card]
    exact hidx
  have : IsCyclic (TauCeti.QuadraticMap.orthogonalGroup Q ⧸ H) := isCyclic_of_prime_card hcardq
  have hcomm : _root_.commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ H :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp IsCyclic.isMulCommutative
  rw [CFSG.RankThree.Literature.FSmith.commutator_orthogonalGroup_eq_subgroupOf hQ (by omega)]
    at hcomm
  have hle : omegaGroup Q hQ ≤ H.map (TauCeti.QuadraticMap.orthogonalGroup Q).subtype :=
    fun g hg =>
    ⟨⟨g, omegaGroup_le Q hQ hg⟩, hcomm hg, rfl⟩
  have hΩ : Nat.card (omegaGroup Q hQ) = 174182400 := by
    have h := S12DW.card_orthogonalGroup_eq hQ
    rw [hO.2] at h
    omega
  have hcard : Nat.card (H.map (TauCeti.QuadraticMap.orthogonalGroup Q).subtype) = 174182400 := by
    rw [Subgroup.card_map_of_injective (TauCeti.QuadraticMap.orthogonalGroup Q).subtype_injective,
      hH]
  have : Finite (H.map (TauCeti.QuadraticMap.orthogonalGroup Q).subtype) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hΩ])).symm

end Orthogonal

section Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem finrank_Qt_of_width_four (hw : S.width = 4) : finrank (ZMod 2) S.Qt = 8 := by
  rw [S.finrank_Qt_eq_two_mul_width, hw]

theorem map_Mbar_eq_omega_of_card (hw : S.width = 4) (hM : Nat.card S.Mbar = 174182400) :
    S.Mbar.map S.O.subtype = timmesfeldOmega S.q := by
  rw [s12_timmesfeldOmega_eq S.q S.q_nondegenerate]
  exact (isPlusType_and_map_eq_omegaGroup_of_card S.q_nondegenerate (finrank_Qt_of_width_four S hw)
    S.Mbar hM).2

theorem isPlusType_of_card (hw : S.width = 4) (hM : Nat.card S.Mbar = 174182400) :
    IsPlusType S.q :=
  (isPlusType_and_map_eq_omegaGroup_of_card S.q_nondegenerate (finrank_Qt_of_width_four S hw)
    S.Mbar hM).1

theorem isConj_of_mem_QG_of_omega (h5 : 5 ≤ finrank (ZMod 2) S.Qt)
    (hΩ : S.Mbar.map S.O.subtype = timmesfeldOmega S.q) {g : G}
    (hg : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) {u : G} (hu : u ∈ S.QG)
    (hu2 : orderOf u = 2) : IsConj S.z u := by
  by_cases huz : u = S.z
  · rw [huz]
  set u₀ := g * S.z * g⁻¹ with hu₀
  have hu₀sq : u₀ ^ 2 = 1 := by
    rw [hu₀, conj_pow, S.z_sq]
    group
  have hu₀1 : u₀ ≠ 1 := by
    rw [hu₀]
    intro h
    apply S.z_ne_one
    calc S.z = g⁻¹ * (g * S.z * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have husq : u ^ 2 = 1 := by rw [← hu2, pow_orderOf_eq_one]
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu2
    exact absurd hu2 (by norm_num)
  have hcl₀ : S.cl u₀ ≠ 0 := by
    rw [Ne, S.cl_eq_zero_iff hg]
    exact fun h => h.elim hu₀1 hne
  have hcl : S.cl u ≠ 0 := by
    rw [Ne, S.cl_eq_zero_iff hu]
    exact fun h => h.elim hu1 huz
  have hq : S.q (S.cl u₀) = S.q (S.cl u) := by
    rw [(S.q_cl_eq_zero_iff hg).2 hu₀sq, (S.q_cl_eq_zero_iff hu).2 husq]
  obtain ⟨γ, hγ, hγu⟩ :=
    CFSG.LargeExtraspecial.O62.exists_mem_omegaGroup_apply_eq S.q_nondegenerate h5 hcl₀ hcl hq
  rw [← s12_timmesfeldOmega_eq, ← hΩ] at hγ
  obtain ⟨_, ⟨m, rfl⟩, rfl⟩ := hγ
  have hm := S.ρ_cl m hg
  change ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl u₀) = S.cl u at hγu
  rw [hm] at hγu
  have hv : (m : G) * u₀ * (m : G)⁻¹ ∈ S.QG := S.conj_mem_QG m.2 hg
  set v := (m : G) * u₀ * (m : G)⁻¹ with hvdef
  have hconj : ∀ c : G, c * v * c⁻¹ = u → IsConj S.z u := fun c hc =>
    isConj_iff.2 ⟨c * (m : G) * g, by rw [← hc, hvdef, hu₀]; group⟩
  rcases (S.cl_eq_cl_iff hv hu).1 hγu with h1 | h1
  · exact hconj 1 (by rw [h1]; group)
  ·
    have hclv : S.cl v ≠ 0 := by rw [hγu]; exact hcl
    obtain ⟨w, hw⟩ : ∃ w, S.q.polarBilin (S.cl v) w ≠ 0 := by
      by_contra! hall
      exact hclv (S.q_nondegenerate.1 _ hall)
    obtain ⟨y, hy, rfl⟩ := S.exists_cl w
    rw [polarBilin_apply_apply, Ne, S.polar_cl_eq_zero_iff hv hy] at hw
    have hyv : y * v * y⁻¹ * v⁻¹ = S.z := by
      rcases S.commutator_eq_one_or_z hy hv with h | h
      · exact absurd (by
          calc v * y = (y * v * y⁻¹ * v⁻¹)⁻¹ * (y * v) := by group
            _ = y * v := by rw [h, inv_one, one_mul]) hw
      · exact h
    refine hconj y ?_
    rw [h1, S.z_comm_QG hv, ← hyv]
    group

end Setting

end CFSG.Sporadic.Co1Patterson

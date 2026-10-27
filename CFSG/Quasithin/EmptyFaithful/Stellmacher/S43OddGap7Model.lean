module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddGap7ModelCond

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod Equiv
open CFSG.LieType.BorelTits
open scoped commutatorElement

namespace F53.Stellmacher.S43

open CosetGeom

namespace Odd

namespace Gap7

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace Model

namespace Data

variable {ρ : Geo H M} (d : Data ρ)

omit [Finite G] in
theorem Yv_nb (h : Perm (Fin 5)) : Yv (d.nb h) = conjSub (dictLift d.D h : G) (Yv d.δ₀) :=
  Three.Yv_smul _ _

omit [Finite G] in
theorem Vst_nb (h : Perm (Fin 5)) :
    Vst (d.nb h) = conjSub (dictLift d.D h : G) (Vst d.δ₀) := by
  unfold Vst nb
  rw [Vn_smul, Qv_smul, conjSub_commutator]

theorem pt_mul_mem_Qv (hy : Hyp S ρ) (h h' : Perm (Fin 5)) :
    d.pt h * d.pt (h * S5g) ∈ Qv (d.nb h') := by
  obtain ⟨y, hy0, hyc⟩ := finite_lemma d.form (d.formHyp hy) (d.pcond hy) (d.k2cond hy) h h' h'
    (Or.inl rfl)
  have e1 := congrArg d.D.φ hyc
  have e2 : d.D.φ (orth.act h' y) =
      (dictLift d.D h' : G) * d.D.φ y * (dictLift d.D h' : G)⁻¹ := by
    rw [← d.D.act_eq, ψ_dictLift]
  rw [map_mul, d.φ_form hy, d.φ_form hy, e2] at e1
  have hW := d.pt_mem_Wn hy h
  have hW' := d.pt_mem_Wn hy (h * S5g)
  have e3 : ⁅d.pt h * d.pt (h * S5g), d.pt h'⁆ =
      ⁅d.pt h, d.pt h'⁆ * ⁅d.pt (h * S5g), d.pt h'⁆ := by
    rw [comm_mul_left_eq, hy.conj_eq_self (hy.Wn_le_Qv hW) (d.comm_pt_mem hy (h * S5g) h'),
      hy.Zv_comm (d.comm_pt_mem hy (h * S5g) h') (d.comm_pt_mem hy h h')]
  have hY : ⁅d.pt h * d.pt (h * S5g), d.pt h'⁆ ∈ Yv (d.nb h') := by
    rw [e3, e1, d.Yv_nb h', d.Yv_eq hy]
    exact mul_mem_conjSub (Subgroup.mem_map_of_mem _ hy0)
  exact hy.mem_Qv_of_comm_mem_Yv (d.nb_mem h') ((Wn ρ).mul_mem hW hW') (d.pt_mem_nb h')
    (d.pt_not_mem hy h') hY

theorem Vst_nb_le (hy : Hyp S ρ) (h h' : Perm (Fin 5)) : Vst (d.nb h) ≤ Qv (d.nb h') := by
  rw [d.Vst_nb h, conjSub_le_iff]
  have hZQ := hy.Zv_le_Qv_nbr (d.nb_mem h')
  refine (d.Vst_le hy).trans (sup_le ?_ ?_)
  · rw [Subgroup.closure_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_conjSub, inv_inv]
    obtain ⟨z1, hz1, e1⟩ := d.pt_conj hy (dictLift d.D h) 1
    obtain ⟨z2, hz2, e2⟩ := d.pt_conj hy (dictLift d.D h) S5g
    rw [ψ_dictLift, mul_one] at e1
    rw [ψ_dictLift] at e2
    have f1 : (dictLift d.D h : G) * d.pt 1 * (dictLift d.D h : G)⁻¹ = z1⁻¹ * d.pt h := by
      rw [e1]; group
    have f2 : (dictLift d.D h : G) * d.pt S5g * (dictLift d.D h : G)⁻¹ =
        z2⁻¹ * d.pt (h * S5g) := by
      rw [e2]; group
    have e : (dictLift d.D h : G) * (d.pt 1 * d.pt S5g) * (dictLift d.D h : G)⁻¹ =
        (z1⁻¹ * z2⁻¹) * (d.pt h * d.pt (h * S5g)) := by
      calc (dictLift d.D h : G) * (d.pt 1 * d.pt S5g) * (dictLift d.D h : G)⁻¹ =
            ((dictLift d.D h : G) * d.pt 1 * (dictLift d.D h : G)⁻¹) *
              ((dictLift d.D h : G) * d.pt S5g * (dictLift d.D h : G)⁻¹) := by group
        _ = z1⁻¹ * (d.pt h * z2⁻¹) * d.pt (h * S5g) := by rw [f1, f2]; group
        _ = z1⁻¹ * (z2⁻¹ * d.pt h) * d.pt (h * S5g) := by
            rw [hy.cen (d.pt_mem_Qv hy h) ((Zv ρ).inv_mem hz2)]
        _ = (z1⁻¹ * z2⁻¹) * (d.pt h * d.pt (h * S5g)) := by group
    rw [e]
    exact (Qv _).mul_mem ((Qv _).mul_mem (hZQ ((Zv ρ).inv_mem hz1)) (hZQ ((Zv ρ).inv_mem hz2)))
      (d.pt_mul_mem_Qv hy h h')
  · rw [← conjSub_le_iff, F1.conjSub_eq_of_mem_normalizer
      (stab_le_normalizer_Zv hy.hA ρ (dictLift d.D h).2)]
    exact hZQ

theorem exists_nb_eq (hy : Hyp S ρ) {δ : Geo H M} (hδ : δ ∈ nbrs ρ) : ∃ h, d.nb h = δ := by
  obtain ⟨g, hg, hgδ⟩ := stab_transitive_on_nbrs d.hδ₀ hδ
  refine ⟨d.D.ψ ⟨(g : G), hg⟩, ?_⟩
  obtain ⟨q, hq, hqe⟩ := exists_eq_mul_of_ψ_eq d.D (a := ⟨(g : G), hg⟩)
    (b := dictLift d.D (d.D.ψ ⟨(g : G), hg⟩)) (ψ_dictLift d.D _).symm
  have hqH : q ∈ H ⊔ M := stab_le ρ (pCoreOf_le 2 _ hq)
  have e : (⟨(dictLift d.D (d.D.ψ ⟨(g : G), hg⟩) : G), stab_le ρ (dictLift d.D _).2⟩ :
      ↥(H ⊔ M)) = g * ⟨q, hqH⟩ := Subtype.ext hqe
  unfold nb
  have hqs : ((⟨q, hqH⟩ : ↥(H ⊔ M)) : G) ∈ stab d.δ₀ := hy.Qv_le_stab_nbr d.hδ₀ hq
  rw [e, mul_smul, smul_eq_of_mem_stab hqs, hgδ]

end Data

end Model

theorem Vst_le_Qv (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α ρ : Geo H M}
    (hs : Sit43 α) (h3 : bMin H M = 3) (hρ : vtype ρ = false)
    (hS : ∀ δ ∈ nbrs ρ, Nat.card (Vn δ) = 2 ^ 6) {δ δ' : Geo H M} (hδ : δ ∈ nbrs ρ)
    (hδ' : δ' ∈ nbrs ρ) : Vst δ ≤ Qv δ' := by
  have hy : Model.Hyp S ρ := ⟨hA, h26, hs.of_vtype_false hρ, h3, hS⟩
  obtain ⟨d⟩ := Model.exists_data hy
  obtain ⟨h, rfl⟩ := d.exists_nb_eq hy hδ
  obtain ⟨h', rfl⟩ := d.exists_nb_eq hy hδ'
  exact d.Vst_nb_le hy h h'

end Gap7

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin

module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Stmt2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35E10C
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35E10E

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.A10

open S35.Std S35.E10

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem zv_le_of_noLam (hne : ∀ δ δ' : Geo H M, ¬ Lam δ δ') {δ δ' : Geo H M}
    (hp : S34.PD δ δ') : Zv δ ≤ Vn δ' := by
  by_contra h
  exact hne δ δ' ⟨hp, h⟩

theorem contra_of_B_le_Qv (hS : Sit H M S) (hT : ClaimT H M)
    {β α' m γ' α : Geo H M} (hp : S34.PD β α') (hb : Back H M β α' m γ') (hα : α ∈ nbrs β)
    (hWQ : Wl α ≤ Qv γ') {B : Subgroup G} (hBQ : B ≤ Qv β)
    (hW8 : ⁅Wb β ⊓ stab α', B⁆ ≤ Zv α' ⊔ ⁅Vn β, B⁆) (hZB : ⁅B, Zv α⁆ ≠ ⊥) : False := by
  obtain ⟨x, hxB, hxQ⟩ := exists_not_mem_Qv hS hZB
  have hxα : x ∈ stab α := Qv_le_stab hS hα (hBQ hxB)
  have hvβ := hp.vδ
  refine final_contra hS hT hp hb hα hWQ hxα hxQ fun e he => ?_
  have he' : e ∈ Wb β ⊓ stab α' := ⟨Wl_le_Wb hS hvβ hα he.1, he.2⟩
  have h3 := hW8 (Subgroup.commutator_mem_commutator he' hxB)
  have h4 : ⁅Vn β, B⁆ ≤ Zv β :=
    (Subgroup.commutator_mono le_rfl hBQ).trans (comm_Vn_Qv hS hvβ).le
  have e1 : x * e * x⁻¹ * e⁻¹ = ⁅e, x⁆⁻¹ := by rw [commutatorElement_def]; group
  rw [e1]
  exact (Zv α' ⊔ Zv β).inv_mem (sup_le_sup_left h4 _ h3)

theorem crit_facts (hS : Sit H M S) {α β α' : Geo H M} (hc : IsCritData α β α')
    (hα : vtype α = true) :
    S34.PD β α' ∧ α ∈ nbrs β ∧ Zv α ≤ Vn β ∧ ¬ Zv α ≤ Qv α' :=
  ⟨(Zv_not_le_Qv_crit hS hc hα).2.2.2.2, hc.adj.symm, (Zv_not_le_Qv_crit hS hc hα).2.2.1,
    hc.not_le⟩

theorem claim10A (hS : Sit H M S) : S35.II.Claim10A H M := by
  intro hne α β α' m γ' hc hα hb _ _ hW
  obtain ⟨hp, hαβ, -, hαZ⟩ := crit_facts hS hc hα
  exact hW (Wl_le_Qv_of_lam_empty hS (fun _ _ hpd => zv_le_of_noLam hne hpd) hp hb hαβ hαZ)

theorem claim10B (hS : Sit H M S) (h8a : Claim8a H M) (hT : ClaimT H M) :
    S35.II.Claim10B H M := by
  intro hne α β α' m γ' hc hα hb hTr _ hW hQ
  obtain ⟨hp, hαβ, -, hαZ⟩ := crit_facts hS hc hα
  obtain ⟨A, B, hA, hB, hAB, hVA, hW8, hZB⟩ := h8a β α' hp hTr
  exact contra_of_B_le_Qv hS hT hp hb hαβ hW (hB.trans hQ) hW8 (hZB α hαβ hαZ)

theorem not_Wb_le_stab (hS : Sit H M S) (hN : S35.II.NoTrivialAct H M) {β α' : Geo H M}
    (hp : S34.PD β α') {x : G} (hx : x ∈ Vn α') (hxQ : x ∉ Qv β)
    (hK : ∀ h ∈ Wb β ⊓ stab α', ⁅h, x⁆ ∈ Vn β) : ¬ Wb β ≤ stab α' := by
  intro hW
  refine hxQ (hN β hp.vδ x ((PD_Vn_le_stab hS hp).2 hx) fun w hw => ?_)
  have h := hK w ⟨hw, hW hw⟩
  rw [← Subgroup.inv_mem_iff, ← commutatorElement_inv]
  simpa using h

theorem claim10C (hS : Sit H M S) (h9 : S35.II.Claim9T H M) (h8a : Claim8a H M)
    (hT : ClaimT H M) (hN : S35.II.NoTrivialAct H M) (h7 : S35.II.Lemma7s H M) :
    S35.II.Claim10C H M := by
  intro hne α β α' m γ' hc hα hb hTr hTh hW hQ
  obtain ⟨hp, hαβ, -, hαZ⟩ := crit_facts hS hc hα
  obtain ⟨hvm, -, -, -, -, -⟩ := back_facts hS hp hb
  have hvβ := hp.vδ
  have hpd : S34.PD α' β :=
    ⟨hp.vδ', hvβ, by rw [CosetGeom.dist_comm]; exact hp.dist_eq, hQ⟩
  have hZ : Zv α' ≤ Vn β := zv_le_of_noLam hne hpd
  obtain ⟨A, B, hA, hB, hAB, hVA, hW8, hZB⟩ := h8a β α' hp hTr
  have hWm : Wb β ⊓ stab m ≤ Wb β ⊓ stab α' :=
    fun w hw => ⟨hw.1, Wb_inf_stab_le hS hvm (mem_nbrs_symm.mp hb.1) hZ hw⟩
  have hK2 : (Wb β ⊓ stab α').relIndex (Wb β) ≤ 2 :=
    (Subgroup.relIndex_le_of_le_left hWm Subgroup.index_ne_zero_of_finite).trans
      (h9 β α' m γ' hp hb hTh)
  by_cases hBQ : B ≤ Qv β
  · exact contra_of_B_le_Qv hS hT hp hb hαβ hW hBQ hW8 (hZB α hαβ hαZ)
  · obtain ⟨x, hxB, hxQ⟩ : ∃ x ∈ B, x ∉ Qv β := by
      by_contra hcon
      push Not at hcon
      exact hBQ hcon
    have hxV : x ∈ Vn α' := hB hxB
    have hBst : B ≤ stab β := hB.trans (PD_Vn_le_stab hS hp).2
    have hK : ∀ h ∈ Wb β ⊓ stab α', ⁅h, x⁆ ∈ Vn β := by
      intro h hh
      have h2 := hW8 (Subgroup.commutator_mem_commutator hh hxB)
      exact (sup_le hZ (comm_Vn_le hBst)) h2
    refine h7 β α' hp hTr hZ x hxV hxQ (Wb β ⊓ stab α') ?_ inf_le_left hK2 hK
      (not_Wb_le_stab hS hN hp hxV hxQ hK)
    exact le_inf (Vn_le_Wb_self hS hvβ) (PD_Vn_le_stab hS hp).1

end S35.A10

end F53.Stellmacher

end CFSG.Quasithin

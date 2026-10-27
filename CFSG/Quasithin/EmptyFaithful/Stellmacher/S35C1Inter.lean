module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53
open scoped commutatorElement

namespace S35.C1

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

@[expose] def Iv (l : Geo H M) : Subgroup G := ⨅ ρ ∈ nbrs l, Vn ρ

omit [Finite G] in
theorem Iv_le_Vn {l ρ : Geo H M} (hρ : ρ ∈ nbrs l) : Iv l ≤ Vn ρ :=
  iInf₂_le (f := fun (ρ : Geo H M) (_ : ρ ∈ nbrs l) => Vn ρ) ρ hρ

omit [Finite G] in
theorem stab_le_normalizer_Iv (l : Geo H M) :
    stab l ≤ Subgroup.normalizer (Iv l : Set G) := by
  have key : ∀ g ∈ stab l, ∀ x ∈ Iv l, g * x * g⁻¹ ∈ Iv l := by
    intro g hg x hx
    obtain ⟨hgX, hgfix⟩ := mem_stab.mp hg
    simp only [Iv, Subgroup.mem_iInf] at hx ⊢
    intro ε hε
    set g' : ↥(H ⊔ M) := ⟨g, hgX⟩
    have hε' : g'⁻¹ • ε ∈ nbrs l := by
      have : (graph (H ⊔ M) H M).Adj (g'⁻¹ • l) (g'⁻¹ • ε) := (smul_adj g'⁻¹).mpr hε
      rwa [show g'⁻¹ • l = l by rw [inv_smul_eq_iff, hgfix]] at this
    have hx' := hx _ hε'
    have e : Vn ε = conjSub (g' : G) (Vn (g'⁻¹ • ε)) := by
      rw [← Vn_smul, smul_inv_smul]
    rw [e, mem_conjSub]
    simpa [g', mul_assoc] using hx'
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem smul_eq_third (hS : Sit H M S) {l δ δ' δ'' : Geo H M} (hl : vtype l = true)
    (hδ : δ ∈ nbrs l) (hδ' : δ' ∈ nbrs l) (hδ'' : δ'' ∈ nbrs l) (h1 : δ ≠ δ') (h2 : δ ≠ δ'')
    (h3 : δ' ≠ δ'') {q : ↥(H ⊔ M)} (hqδ : (q : G) ∈ Qv δ) (hqν : (q : G) ∉ Qv l) :
    q • δ' = δ'' := by
  have hqδs : (q : G) ∈ stab δ := pCoreOf_le 2 _ hqδ
  have hqls : (q : G) ∈ stab l := Std.Qv_le_stab hS (Std.mem_nbrs_symm.mpr hδ) hqδ
  have hqδfix : q • δ = δ := smul_eq_of_mem_stab hqδs
  have hmem : q • δ' ∈ nbrs l := Std.smul_mem_nbrs_of_stab hqls hδ'
  have hne1 : q • δ' ≠ δ := by
    intro h
    rw [← hqδfix] at h
    exact h1 (MulAction.injective q h).symm
  have hne2 : q • δ' ≠ δ' := by
    intro h
    exact hqν (Std.mem_Qv_of_fix_two hS hl hδ hδ' h1 hqls hqδs (mem_stab_of_smul_eq h))
  obtain ⟨ε, -, -, -, hall⟩ := Std.nbrs_S3_third hS hl hδ hδ' h1
  have e : δ'' = ε := by
    rcases hall δ'' hδ'' with h' | h' | h'
    · exact absurd h'.symm h2
    · exact absurd h'.symm h3
    · exact h'
  rcases hall _ hmem with h | h | h
  · exact absurd h hne1
  · exact absurd h hne2
  · rw [h, e]

theorem Vn_inf_Vn_eq_Iv (hS : Sit H M S) {l β δ : Geo H M} (hl : vtype l = true)
    (hβ : β ∈ nbrs l) (hδ : δ ∈ nbrs l) (hne : β ≠ δ) : Vn β ⊓ Vn δ = Iv l := by
  refine le_antisymm ?_ (le_inf (Iv_le_Vn hβ) (Iv_le_Vn hδ))
  intro x hx
  obtain ⟨δ'', hδ'', h2, h3, hall⟩ := Std.nbrs_S3_third hS hl hβ hδ hne
  have hvβ := Std.vtype_nbr_S3 hl hβ
  have hx'' : x ∈ Vn δ'' := by
    obtain ⟨q, hqβ, hqν⟩ := Set.not_subset.mp (Std.Q_not_le hS hvβ (Std.mem_nbrs_symm.mpr hβ))
    have hqX : q ∈ H ⊔ M := stab_le β (pCoreOf_le 2 _ hqβ)
    set q' : ↥(H ⊔ M) := ⟨q, hqX⟩
    have hsw : q' • δ = δ'' := smul_eq_third hS hl hβ hδ hδ'' hne h2.symm h3.symm hqβ hqν
    have h1 : q * x * q⁻¹ ∈ Vn δ'' := by
      rw [← hsw, Vn_smul, mem_conjSub]
      simpa [q', mul_assoc] using hx.2
    have h2' : ⁅x⁻¹, q⁆ ∈ Zv β :=
      S34.comm_Vn_Qv_le hS.glob hvβ (Subgroup.commutator_mem_commutator ((Vn β).inv_mem hx.1) hqβ)
    have hZ : Zv β ≤ Vn δ'' :=
      (Std.Zv_le_Zv_of_nbr hS hvβ (Std.mem_nbrs_symm.mpr hβ)).trans
        (Std.Zv_le_Vn (Std.mem_nbrs_symm.mpr hδ''))
    have e : x = (q * x * q⁻¹) * ⁅x⁻¹, q⁆⁻¹ := by
      rw [commutatorElement_def]; group
    rw [e]
    exact (Vn δ'').mul_mem h1 ((Vn δ'').inv_mem (hZ h2'))
  simp only [Iv, Subgroup.mem_iInf]
  intro ε hε
  rcases hall ε hε with rfl | rfl | rfl
  · exact hx.1
  · exact hx.2
  · exact hx''

theorem inter_eq (hS : Sit H M S) {β l δ δ' : Geo H M} (hβ : vtype β = false) (hl : l ∈ nbrs β)
    (hlδ : l ∈ nbrs δ) (hδβ : δ ≠ β) (hlδ' : l ∈ nbrs δ') (hδ'β : δ' ≠ β) :
    Vn β ⊓ Vn δ = Vn β ⊓ Vn δ' := by
  have hlt := Std.vtype_nbr_S5 hβ hl
  rw [Vn_inf_Vn_eq_Iv hS hlt (Std.mem_nbrs_symm.mpr hl) (Std.mem_nbrs_symm.mpr hlδ) hδβ.symm,
    Vn_inf_Vn_eq_Iv hS hlt (Std.mem_nbrs_symm.mpr hl) (Std.mem_nbrs_symm.mpr hlδ') hδ'β.symm]

theorem inter_eq' (hS : Sit H M S) {β l δ δ' : Geo H M} (hβ : vtype β = false) (hl : l ∈ nbrs β)
    (hlδ : l ∈ nbrs δ) (hδβ : δ ≠ β) (hlδ' : l ∈ nbrs δ') (hδδ' : δ ≠ δ') :
    Vn β ⊓ Vn δ = Vn δ ⊓ Vn δ' := by
  have hlt := Std.vtype_nbr_S5 hβ hl
  rw [Vn_inf_Vn_eq_Iv hS hlt (Std.mem_nbrs_symm.mpr hl) (Std.mem_nbrs_symm.mpr hlδ) hδβ.symm,
    Vn_inf_Vn_eq_Iv hS hlt (Std.mem_nbrs_symm.mpr hlδ) (Std.mem_nbrs_symm.mpr hlδ') hδδ']

omit [Finite G] in
theorem Zv_le_inter {β l δ : Geo H M} (hl : l ∈ nbrs β) (hlδ : l ∈ nbrs δ) :
    Zv l ≤ Vn β ⊓ Vn δ :=
  le_inf (Std.Zv_le_Vn hl) (Std.Zv_le_Vn hlδ)

theorem stab_le_normalizer_inter (hS : Sit H M S) {β l δ : Geo H M} (hβ : vtype β = false)
    (hl : l ∈ nbrs β) (hlδ : l ∈ nbrs δ) (hδβ : δ ≠ β) :
    stab l ≤ Subgroup.normalizer ((Vn β ⊓ Vn δ : Subgroup G) : Set G) := by
  rw [Vn_inf_Vn_eq_Iv hS (Std.vtype_nbr_S5 hβ hl) (Std.mem_nbrs_symm.mpr hl)
    (Std.mem_nbrs_symm.mpr hlδ) hδβ.symm]
  exact stab_le_normalizer_Iv l

end S35.C1

end F53.Stellmacher

end CFSG.Quasithin

module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Notation

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.Std

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem Vn_le_Wb {β ρ : Geo H M} (h : dist ρ β = 2) : Vn ρ ≤ Wb β :=
  le_iSup₂_of_le (f := fun (ρ : Geo H M) (_ : dist ρ β = 2) => Vn ρ) ρ h le_rfl

omit [Finite G] in
theorem Vn_le_Wl {l ρ : Geo H M} (h : ρ ∈ nbrs l) : Vn ρ ≤ Wl l :=
  le_iSup₂_of_le (f := fun (ρ : Geo H M) (_ : ρ ∈ nbrs l) => Vn ρ) ρ h le_rfl

omit [Finite G] in
theorem Wb_le {β : Geo H M} {K : Subgroup G} (h : ∀ ρ : Geo H M, dist ρ β = 2 → Vn ρ ≤ K) :
    Wb β ≤ K := iSup₂_le h

omit [Finite G] in
theorem Wl_le {l : Geo H M} {K : Subgroup G} (h : ∀ ρ ∈ nbrs l, Vn ρ ≤ K) : Wl l ≤ K :=
  iSup₂_le h

omit [Finite G] in
theorem vtype_eq_of_nbrs {l a b : Geo H M} (ha : a ∈ nbrs l) (hb : b ∈ nbrs l) :
    vtype a = vtype b := by
  have h1 := vtype_ne_of_adj (show (graph (H ⊔ M) H M).Adj l a from ha)
  have h2 := vtype_ne_of_adj (show (graph (H ⊔ M) H M).Adj l b from hb)
  cases hl : vtype l <;> cases ha' : vtype a <;> cases hb' : vtype b <;> simp_all

theorem dist_eq_two_iff {β ρ : Geo H M} :
    dist ρ β = 2 ↔ ∃ l ∈ nbrs β, ρ ∈ nbrs l ∧ ρ ≠ β := by
  constructor
  · intro h
    obtain ⟨μ, hμ, hd⟩ := exists_nbr_dist_succ (δ := ρ) (ρ := β) (d := 1) (by omega)
    have hμβ : μ ∈ nbrs β := by
      have : (graph (H ⊔ M) H M).Adj μ β := dist_eq_one_iff_adj.mp hd
      exact this.symm
    refine ⟨μ, hμβ, mem_nbrs_symm.mp hμ, fun h' => ?_⟩
    rw [h', CosetGeom.dist_self] at h
    omega
  · rintro ⟨l, hl, hρ, hne⟩
    have hle : dist ρ β ≤ 2 := by
      have := dist_le_dist_nbr (mem_nbrs_symm.mp hl) ρ
      have h1 : dist ρ l = 1 := by
        rw [CosetGeom.dist_comm]; exact dist_eq_one_iff_adj.mpr hρ
      omega
    have h0 : dist ρ β ≠ 0 := fun h => hne ((dist_eq_zero_iff rfl).mp h)
    have h1 : dist ρ β ≠ 1 := fun h => by
      have hadj := dist_eq_one_iff_adj.mp h
      exact vtype_ne_of_adj hadj (vtype_eq_of_nbrs hρ (mem_nbrs_symm.mp hl))
    omega

theorem exists_two_others (hS : Sit H M S) {l β : Geo H M} (hl : vtype l = true)
    (hβ : β ∈ nbrs l) :
    ∃ δ δ' : Geo H M, δ ∈ nbrs l ∧ δ' ∈ nbrs l ∧ δ ≠ β ∧ δ' ≠ β ∧ δ ≠ δ' := by
  obtain ⟨a, b, c, h, hab, hac, hbc⟩ := nbrs_S3 hS hl
  rw [h] at hβ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hβ
  have ma : a ∈ nbrs l := by rw [h]; simp
  have mb : b ∈ nbrs l := by rw [h]; simp
  have mc : c ∈ nbrs l := by rw [h]; simp
  rcases hβ with rfl | rfl | rfl
  · exact ⟨b, c, mb, mc, hab.symm, hac.symm, hbc⟩
  · exact ⟨a, c, ma, mc, hab, hbc.symm, hac⟩
  · exact ⟨a, b, ma, mb, hac, hbc, hab⟩

theorem Vn_le_Wb_self (hS : Sit H M S) {β : Geo H M} (hβ : vtype β = false) :
    Vn β ≤ Wb β := by
  refine iSup₂_le fun l hl => ?_
  have hlt := vtype_nbr_S5 hβ hl
  obtain ⟨δ, δ', hδ, hδ', hδβ, hδ'β, hne⟩ := exists_two_others hS hlt (mem_nbrs_symm.mp hl)
  have hsup := (Zv_ne hS hlt hδ hδ' hne).2.1
  rw [← hsup]
  refine sup_le ?_ ?_
  · refine (Zv_le_Vn_S5 hS (vtype_nbr_S3 hlt hδ)).trans (Vn_le_Wb ?_)
    exact dist_eq_two_iff.mpr ⟨l, hl, hδ, hδβ⟩
  · refine (Zv_le_Vn_S5 hS (vtype_nbr_S3 hlt hδ')).trans (Vn_le_Wb ?_)
    exact dist_eq_two_iff.mpr ⟨l, hl, hδ', hδ'β⟩

theorem Wb_eq_iSup_Wl (hS : Sit H M S) {β : Geo H M} (hβ : vtype β = false) :
    Wb β = ⨆ (l : Geo H M) (_ : l ∈ nbrs β), Wl l := by
  apply le_antisymm
  · refine Wb_le fun ρ hρ => ?_
    obtain ⟨l, hl, hρl, -⟩ := dist_eq_two_iff.mp hρ
    exact (Vn_le_Wl hρl).trans
      (le_iSup₂_of_le (f := fun (l : Geo H M) (_ : l ∈ nbrs β) => Wl l) l hl le_rfl)
  · refine iSup₂_le fun l hl => Wl_le fun ρ hρ => ?_
    by_cases h : ρ = β
    · subst h
      exact Vn_le_Wb_self hS hβ
    · exact Vn_le_Wb (dist_eq_two_iff.mpr ⟨l, hl, hρ, h⟩)

theorem Wb_le_Ql (hS : Sit H M S) {β l : Geo H M} (hl : l ∈ nbrs β) : Wb β ≤ Qv l := by
  refine Wb_le fun ρ hρ => Vn_le_Qv_dist hS ?_
  have := dist_le_dist_nbr hl ρ
  have := hS.b5
  omega

theorem Wb_le_Qv (hS : Sit H M S) (β : Geo H M) : Wb β ≤ Qv β := by
  refine Wb_le fun ρ hρ => Vn_le_Qv_dist hS ?_
  have := hS.b5
  omega

omit [Finite G] in
theorem comm_iSup {ι : Type*} {p : ι → Prop} (A : ι → Subgroup G) (B : Subgroup G)
    (h : ∀ i, p i → ∀ a ∈ A i, ∀ b ∈ B, a * b = b * a) :
    ∀ x ∈ (⨆ i, ⨆ _ : p i, A i), ∀ b ∈ B, x * b = b * x := by
  have : (⨆ i, ⨆ _ : p i, A i) ≤ Subgroup.centralizer (B : Set G) :=
    iSup₂_le fun i hi a ha => Subgroup.mem_centralizer_iff.mpr fun b hb => (h i hi a ha b hb).symm
  intro x hx b hb
  exact (Subgroup.mem_centralizer_iff.mp (this hx) b hb).symm

theorem comm_Vn_Wb (hS : Sit H M S) (β : Geo H M) : ⁅Vn β, Wb β⁆ = ⊥ := by
  have key : ∀ x ∈ Wb β, ∀ b ∈ Vn β, x * b = b * x :=
    comm_iSup (p := fun ρ => dist ρ β = 2) Vn (Vn β) fun ρ hρ a ha b hb =>
      Vn_commute_dist hS (by have := hS.b5; omega) a ha b hb
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact key w hw a ha

theorem Wb_comm_of_b7 (hS : Sit H M S) (h7 : 7 ≤ bMin H M) (β : Geo H M) :
    ∀ x ∈ Wb β, ∀ y ∈ Wb β, x * y = y * x := by
  have step : ∀ ρ : Geo H M, dist ρ β = 2 → ∀ x ∈ Wb β, ∀ b ∈ Vn ρ, x * b = b * x := by
    intro ρ hρ
    exact comm_iSup (p := fun ρ' => dist ρ' β = 2) Vn (Vn ρ) fun ρ' hρ' a ha b hb =>
      Vn_commute_dist hS (by
        have h1 := dist_triangle rfl ρ' β ρ
        rw [CosetGeom.dist_comm β ρ] at h1
        omega) a ha b hb
  exact comm_iSup (p := fun ρ => dist ρ β = 2) Vn (Wb β) fun ρ hρ a ha b hb =>
    (step ρ hρ b hb a ha).symm

theorem Wl_comm (hS : Sit H M S) (l : Geo H M) : ∀ x ∈ Wl l, ∀ y ∈ Wl l, x * y = y * x := by
  have step : ∀ ρ ∈ nbrs l, ∀ x ∈ Wl l, ∀ b ∈ Vn ρ, x * b = b * x := by
    intro ρ hρ
    exact comm_iSup (p := fun ρ' => ρ' ∈ nbrs l) Vn (Vn ρ) fun ρ' hρ' a ha b hb =>
      Vn_commute_dist hS (by
        have h1 := dist_le_dist_nbr hρ' ρ
        have e := CosetGeom.dist_comm ρ' ρ
        have h2 : dist ρ l = 1 := by
          rw [CosetGeom.dist_comm]; exact dist_eq_one_iff_adj.mpr hρ
        have := hS.b5
        omega) a ha b hb
  exact comm_iSup (p := fun ρ => ρ ∈ nbrs l) Vn (Wl l) fun ρ hρ a ha b hb =>
    (step ρ hρ b hb a ha).symm

omit [Finite G] in
theorem Wl_normal (l : Geo H M) : stab l ≤ Subgroup.normalizer (Wl l : Set G) :=
  S34.stab_le_normalizer_Wtri l

omit [Finite G] in
theorem Wb_normal (β : Geo H M) : stab β ≤ Subgroup.normalizer (Wb β : Set G) := by
  have key : ∀ x ∈ stab β, conjSub x (Wb β) ≤ Wb β := by
    intro x hx
    obtain ⟨hmem, hfix⟩ := mem_stab.mp hx
    unfold Wb
    simp only [conjSub_iSup]
    refine iSup₂_le fun ρ hρ => ?_
    have := Vn_smul (⟨x, hmem⟩ : ↥(H ⊔ M)) ρ
    simp only at this
    rw [← this]
    refine Vn_le_Wb ?_
    have h := dist_smul (⟨x, hmem⟩ : ↥(H ⊔ M)) ρ β
    rw [hfix, hρ] at h
    exact h
  intro x hx
  refine mem_normalizer_of_conjSub_eq (le_antisymm (key x hx) ?_)
  rw [le_conjSub_iff]
  exact key x⁻¹ (inv_mem hx)

end S35.Std

end F53.Stellmacher

end CFSG.Quasithin

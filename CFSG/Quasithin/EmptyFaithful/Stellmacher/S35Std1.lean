module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Sit

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.Std

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem mem_nbrs_symm {a b : Geo H M} : a ∈ nbrs b ↔ b ∈ nbrs a :=
  ⟨fun h => SimpleGraph.Adj.symm (show (graph (H ⊔ M) H M).Adj b a from h),
    fun h => SimpleGraph.Adj.symm (show (graph (H ⊔ M) H M).Adj a b from h)⟩

omit [Finite G] in
theorem vtype_nbr_S3 {l m : Geo H M} (hl : vtype l = true) (hm : m ∈ nbrs l) :
    vtype m = false := vtype_false_of_mem_nbrs_true hm hl

omit [Finite G] in
theorem vtype_nbr_S5 {δ l : Geo H M} (hδ : vtype δ = false) (hl : l ∈ nbrs δ) :
    vtype l = true := vtype_true_of_mem_nbrs_false hl hδ

theorem ncard_nbrs_S3 (hS : Sit H M S) {l : Geo H M} (hl : vtype l = true) :
    (nbrs l).ncard = 3 := by
  rw [← Nat.card_coe_set_eq]
  exact card_nbrs_true hS.glob.amalg hl

theorem nbrs_S3 (hS : Sit H M S) {l : Geo H M} (hl : vtype l = true) :
    ∃ β δ δ' : Geo H M, nbrs l = {β, δ, δ'} ∧ β ≠ δ ∧ β ≠ δ' ∧ δ ≠ δ' := by
  obtain ⟨x, y, z, hxy, hxz, hyz, h⟩ := Set.ncard_eq_three.mp (ncard_nbrs_S3 hS hl)
  exact ⟨x, y, z, h, hxy, hxz, hyz⟩

theorem nbrs_S3_third (hS : Sit H M S) {l β δ : Geo H M} (hl : vtype l = true)
    (hβ : β ∈ nbrs l) (hδ : δ ∈ nbrs l) (hne : β ≠ δ) :
    ∃ δ'' : Geo H M, δ'' ∈ nbrs l ∧ δ'' ≠ β ∧ δ'' ≠ δ ∧
      ∀ m ∈ nbrs l, m = β ∨ m = δ ∨ m = δ'' := by
  have h3 := ncard_nbrs_S3 hS hl
  have hfin : (nbrs l).Finite := Set.toFinite _
  obtain ⟨δ'', hm, h1, h2⟩ : ∃ δ'' ∈ nbrs l, δ'' ≠ β ∧ δ'' ≠ δ := by
    by_contra hcon
    have hsub : nbrs l ⊆ {β, δ} := fun m hm => by
      by_contra h
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at h
      exact hcon ⟨m, hm, h.1, h.2⟩
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_pair hne] at this
    omega
  refine ⟨δ'', hm, h1, h2, ?_⟩
  have hsub : ({β, δ, δ''} : Set (Geo H M)) ⊆ nbrs l := by
    intro m hm'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm'
    rcases hm' with rfl | rfl | rfl <;> assumption
  have hc : ({β, δ, δ''} : Set (Geo H M)).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨β, δ, δ'', hne, h1.symm, h2.symm, rfl⟩
  have heq := Set.eq_of_subset_of_ncard_le hsub (by omega) hfin
  intro m hm'
  have : m ∈ ({β, δ, δ''} : Set (Geo H M)) := by rw [heq]; exact hm'
  simpa using this

theorem Zv_le_Zv_of_nbr (hS : Sit H M S) {δ l : Geo H M} (hδ : vtype δ = false)
    (hl : l ∈ nbrs δ) : Zv δ ≤ Zv l :=
  S34.Zv_le_Zv_nbr hS.glob hδ hl

omit [Finite G] in
theorem Zv_le_Vn {δ l : Geo H M} (hl : l ∈ nbrs δ) : Zv l ≤ Vn δ :=
  le_iSup₂_of_le (f := fun (ν : Geo H M) (_ : ν ∈ nbrs δ) => Zv ν) l hl le_rfl

theorem Zv_ne (hS : Sit H M S) {l ρ σ : Geo H M} (hl : vtype l = true) (hρ : ρ ∈ nbrs l)
    (hσ : σ ∈ nbrs l) (hne : ρ ≠ σ) :
    Zv ρ ≠ Zv σ ∧ Zv ρ ⊔ Zv σ = Zv l ∧ Zv ρ ⊓ Zv σ = ⊥ := by
  obtain ⟨hsup, hinf⟩ := EmptyFaithful.Stellmacher.OrdinaryProofs.Zv_sup_eq_and_inf_eq_bot
    hS.glob.amalg hl (hS.glob.crit l hl) hρ hσ hne (hS.glob.central ρ (vtype_nbr_S3 hl hρ))
  refine ⟨fun h => ?_, hsup, hinf⟩
  rw [← h, inf_idem] at hinf
  exact Zv_ne_bot hS.glob.amalg ρ hinf

theorem stab_inf_eq (hS : Sit H M S) {δ l : Geo H M} (hδ : vtype δ = false) (hl : l ∈ nbrs δ) :
    stab δ ⊓ stab l = Qv δ ⊔ Qv l := by
  have h := hS.glob.prod l δ (show (graph (H ⊔ M) H M).Adj l δ from mem_nbrs_symm.mpr hl)
    (vtype_nbr_S5 hδ hl)
  rw [inf_comm, ← h]
  exact sup_comm _ _

theorem relIndex_Qv (hS : Sit H M S) {δ l : Geo H M} (hδ : vtype δ = false) (hl : l ∈ nbrs δ) :
    (Qv δ ⊓ Qv l).relIndex (Qv δ) = 2 := by
  have hn : Qv δ ≤ Subgroup.normalizer (Qv l : Set G) :=
    (Qv_le_stab_of_mem_nbrs hS.glob.amalg hl).trans (le_normalizer_pCoreOf 2 (stab l))
  rw [relIndex_inf_eq_relIndex_sup hn, ← stab_inf_eq hS hδ hl]
  exact EmptyFaithful.Stellmacher.OrdinaryProofs.relIndex_Qv_inf hS.glob.amalg hl
    (vtype_nbr_S5 hδ hl)

theorem Q_not_le (hS : Sit H M S) {δ l : Geo H M} (hδ : vtype δ = false) (hl : l ∈ nbrs δ) :
    ¬ Qv δ ≤ Qv l := by
  intro h
  have := relIndex_Qv hS hδ hl
  rw [inf_eq_left.mpr h, Subgroup.relIndex_self] at this
  omega

theorem Qv_le_stab (hS : Sit H M S) {δ μ : Geo H M} (hμ : μ ∈ nbrs δ) : Qv δ ≤ stab μ :=
  Qv_le_stab_of_mem_nbrs hS.glob.amalg hμ

theorem mem_Qv_iff (hS : Sit H M S) (δ : Geo H M) {x : G} :
    x ∈ Qv δ ↔ x ∈ stab δ ∧ ∀ m ∈ nbrs δ, x ∈ stab m := by
  rw [← Qv_eq_ballStab_one hS.glob.amalg, mem_ballStab]
  constructor
  · intro h
    exact ⟨h δ (by simp [CosetGeom.dist_self]), fun m hm => h m (dist_eq_one_iff_adj.mpr hm).le⟩
  · rintro ⟨h0, h1⟩ m hm
    rcases (dist_le_one_iff rfl).mp hm with rfl | hadj
    · exact h0
    · exact h1 m hadj

omit [Finite G] in
theorem smul_mem_nbrs_of_stab {g : ↥(H ⊔ M)} {l m : Geo H M} (hg : (g : G) ∈ stab l)
    (hm : m ∈ nbrs l) : g • m ∈ nbrs l := by
  have := (smul_adj g).mpr (show (graph (H ⊔ M) H M).Adj l m from hm)
  rwa [smul_eq_of_mem_stab hg] at this

omit [Finite G] in
theorem smul_mem_nbrs_iff' (g : ↥(H ⊔ M)) {a b : Geo H M} : g • a ∈ nbrs (g • b) ↔ a ∈ nbrs b :=
  smul_adj g

theorem mem_Qv_of_fix_two (hS : Sit H M S) {l β δ : Geo H M} (hl : vtype l = true)
    (hβ : β ∈ nbrs l) (hδ : δ ∈ nbrs l) (hne : β ≠ δ) {x : G} (hx : x ∈ stab l)
    (hxβ : x ∈ stab β) (hxδ : x ∈ stab δ) : x ∈ Qv l := by
  obtain ⟨δ'', h3, h1, h2, hall⟩ := nbrs_S3_third hS hl hβ hδ hne
  let g : ↥(H ⊔ M) := ⟨x, stab_le l hx⟩
  have hgβ : g • β = β := smul_eq_of_mem_stab hxβ
  have hgδ : g • δ = δ := smul_eq_of_mem_stab hxδ
  have hg3 : g • δ'' ∈ nbrs l := smul_mem_nbrs_of_stab hx h3
  have hfix : g • δ'' = δ'' := by
    rcases hall _ hg3 with h | h | h
    · exact absurd (MulAction.injective g (h.trans hgβ.symm)) h1
    · exact absurd (MulAction.injective g (h.trans hgδ.symm)) h2
    · exact h
  refine (mem_Qv_iff hS l).mpr ⟨hx, fun m hm => ?_⟩
  rcases hall m hm with rfl | rfl | rfl
  · exact hxβ
  · exact hxδ
  · exact mem_stab_of_smul_eq hfix

theorem swap_nbrs (hS : Sit H M S) {β l δ δ'' : Geo H M} (hβ : vtype β = false)
    (hl : l ∈ nbrs β) (hδ : l ∈ nbrs δ) (hne : δ ≠ β) (hδ'' : δ'' ∈ nbrs l) (hne'' : δ'' ≠ β) :
    ∃ g : ↥(H ⊔ M), (g : G) ∈ stab β ⊓ stab l ∧ g • δ = δ'' ∧ (δ'' ≠ δ → (g : G) ∉ Qv l) := by
  have hlt := vtype_nbr_S5 hβ hl
  have hδl : δ ∈ nbrs l := mem_nbrs_symm.mp hδ
  have hβl : β ∈ nbrs l := mem_nbrs_symm.mp hl
  by_cases h : δ'' = δ
  · exact ⟨1, ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩, by simp [h], fun h' => absurd h h'⟩
  obtain ⟨x, hx, hxQ⟩ : ∃ x ∈ stab β ⊓ stab l, x ∉ Qv l := by
    by_contra hcon
    push Not at hcon
    have hidx := EmptyFaithful.Stellmacher.OrdinaryProofs.relIndex_Qv_inf hS.glob.amalg hl hlt
    rw [Subgroup.relIndex_eq_one.mpr (fun y hy => hcon y hy)] at hidx
    omega
  obtain ⟨δ3, h3, h1, h2, hall⟩ := nbrs_S3_third hS hlt hβl hδl (Ne.symm hne)
  let g : ↥(H ⊔ M) := ⟨x, stab_le l hx.2⟩
  have hgβ : g • β = β := smul_eq_of_mem_stab hx.1
  have hgδ : g • δ ∈ nbrs l := smul_mem_nbrs_of_stab hx.2 hδl
  have hgδ'' : g • δ'' ∈ nbrs l := smul_mem_nbrs_of_stab hx.2 hδ''
  have e3 : δ'' = δ3 := by
    rcases hall _ hδ'' with h' | h' | h'
    · exact absurd h' hne''
    · exact absurd h' h
    · exact h'
  have hnb : g • δ ≠ β := fun h' => hne (MulAction.injective g (h'.trans hgβ.symm))
  have hnb'' : g • δ'' ≠ β := fun h' => hne'' (MulAction.injective g (h'.trans hgβ.symm))
  refine ⟨g, hx, ?_, fun _ => hxQ⟩
  rcases hall _ hgδ with h' | h' | h'
  · exact absurd h' hnb
  · exfalso
    apply hxQ
    have hgδ2 : g • δ'' = δ'' := by
      rcases hall _ hgδ'' with h'' | h'' | h''
      · exact absurd h'' hnb''
      · exact absurd (MulAction.injective g (h''.trans h'.symm)) h
      · rw [h'', e3]
    exact mem_Qv_of_fix_two hS hlt hβl hδl (Ne.symm hne) hx.2 hx.1
      (mem_stab_of_smul_eq h')
  · rw [h', e3]

theorem stab_inf_arc (hS : Sit H M S) {β l δ : Geo H M} (hβ : vtype β = false)
    (hl : l ∈ nbrs β) (hδ : l ∈ nbrs δ) (hne : δ ≠ β) :
    stab β ⊓ stab l ⊓ stab δ = Qv l := by
  have hlt := vtype_nbr_S5 hβ hl
  have hδl : δ ∈ nbrs l := mem_nbrs_symm.mp hδ
  have hβl : β ∈ nbrs l := mem_nbrs_symm.mp hl
  apply le_antisymm
  · intro x hx
    exact mem_Qv_of_fix_two hS hlt hβl hδl (Ne.symm hne) hx.1.2 hx.1.1 hx.2
  · exact le_inf (le_inf (Qv_le_stab hS hβl) (pCoreOf_le 2 _)) (Qv_le_stab hS hδl)

theorem arc_trans (hS : Sit H M S) {β l δ β' l' δ' : Geo H M} (hβ : vtype β = false)
    (hl : l ∈ nbrs β) (hδ : l ∈ nbrs δ) (hne : δ ≠ β) (hβ' : vtype β' = false)
    (hl' : l' ∈ nbrs β') (hδ' : l' ∈ nbrs δ') (hne' : δ' ≠ β') :
    ∃ g : ↥(H ⊔ M), g • β = β' ∧ g • l = l' ∧ g • δ = δ' := by
  obtain ⟨g0, hg0⟩ := exists_smul_of_vtype_eq (hβ.trans hβ'.symm)
  have hg0l : g0 • l ∈ nbrs β' := by rw [hg0]; exact (smul_adj g0).mpr hl
  obtain ⟨g1, hg1, hg1l⟩ := stab_transitive_on_nbrs hg0l hl'
  have hg1β : g1 • β' = β' := smul_eq_of_mem_stab hg1
  have hδ1 : g1 • (g0 • δ) ∈ nbrs l' := by
    rw [← hg1l]
    exact (smul_adj g1).mpr ((smul_adj g0).mpr (mem_nbrs_symm.mp hδ))
  have hne1 : g1 • (g0 • δ) ≠ β' := by
    intro h
    rw [← hg1β, hg0] at h
    exact hne (MulAction.injective g0 (MulAction.injective g1 h))
  obtain ⟨x, hx, hxδ, -⟩ := swap_nbrs hS hβ' hl' (mem_nbrs_symm.mpr hδ1) hne1
    (mem_nbrs_symm.mp hδ') hne'
  refine ⟨x * (g1 * g0), ?_, ?_, ?_⟩
  · have : x • β' = β' := smul_eq_of_mem_stab hx.1
    rw [mul_smul, mul_smul, ← hg0, hg1β, this]
  · have : x • l' = l' := smul_eq_of_mem_stab hx.2
    rw [mul_smul, mul_smul, hg1l, this]
  · rw [mul_smul, mul_smul, hxδ]

end S35.Std

end F53.Stellmacher

end CFSG.Quasithin

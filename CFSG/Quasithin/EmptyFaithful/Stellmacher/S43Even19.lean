module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43EvenDefs
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseE2

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43.Even

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod CosetGeom
open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem conj_eq_of_mem_centralizer {g : G} {K : Subgroup G}
    (h : g ∈ Subgroup.centralizer (K : Set G)) {y : G} (hy : y ∈ K) : g * y * g⁻¹ = y := by
  have := Subgroup.mem_centralizer_iff.mp h y hy
  rw [mul_inv_eq_iff_eq_mul]
  exact this.symm

omit [Finite G] in
theorem mem_centralizer_of_conj_eq {g : G} {K : Subgroup G}
    (h : ∀ y ∈ K, g * y * g⁻¹ = y) : g ∈ Subgroup.centralizer (K : Set G) := by
  refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
  have := h y hy
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this.symm

theorem mem_Qv_of_centralizes_comm (hA : F53Amalgam H M S) {α : Geo H M} (hs : Sit43 α)
    {ν β : Geo H M} (hν : vtype ν = false) (hβ : β ∈ nbrs ν) {g : G}
    (hg : g ∈ stab ν ⊓ stab β)
    (hc : ∀ y ∈ ⁅Zv ν, stab ν ⊓ stab β⁆, g * y * g⁻¹ = y) : g ∈ Qv ν := by
  obtain ⟨D⟩ := (hs.of_vtype_false hν).exists_dict hA hβ
  set x : ↥(stab ν) := ⟨g, hg.1⟩ with hx
  have h1 : D.ψ x ∈ S5Syl := (D.mem_S_iff x).mp hg
  have h2 : D.ψ x = 1 := by
    refine S29.eq_one_of_fixes_commW_sylow orth (Or.inl rfl) h1 fun y hy => ?_
    have hφ : D.φ y ∈ ⁅Zv ν, stab ν ⊓ stab β⁆ := by
      rw [D.comm_eq]
      exact ⟨y, hy, rfl⟩
    apply D.inj
    rw [D.act_eq x y]
    exact hc _ hφ
  exact (D.ker_iff x).mp h2

theorem smul_eq_of_centralizes_Vst (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α : Geo H M}
    (hs : Sit43 α) {β : Geo H M} (hβ : β ∈ nbrs α) (g : ↥(H ⊔ M)) (hgβ : (g : G) ∈ stab β)
    (hgV : (g : G) ∈ Subgroup.centralizer (Vst β : Set G)) {ν : Geo H M} (hν : ν ∈ nbrs β) :
    g • ν = ν := by
  by_contra hne
  have hβv : vtype β = true := Sit43.vtype_true_of_adj hs.vα hβ
  have hν' : g • ν ∈ nbrs β := smul_mem_nbrs_of_mem_stab g hgβ hν
  have hle : ⁅Zv ν, Qv β⁆ ≤ Yv β := by
    rw [← hs.inf_Zv_eq_Yv hA h26 hβv hν hν' (Ne.symm hne)]
    refine le_inf (hs.comm_le_Zv hA h26 hβv hν) fun x hx => ?_
    have hxV : x ∈ Vst β := Subgroup.commutator_mono (Sit43.Zv_le_Vn_nbrs hν) le_rfl hx
    have h1 := conj_eq_of_mem_centralizer hgV hxV
    have h2 : x ∈ Zv ν := hs.comm_le_Zv hA h26 hβv hν hx
    rw [Zv_smul, mem_conjSub]
    have h3 : (g : G)⁻¹ * x * g = x := by
      have := congrArg (fun y => (g : G)⁻¹ * y * g) h1
      simpa [mul_assoc] using this.symm
    rw [h3]
    exact h2
  have h8 := hs.card_comm_Qv hA h26 hβv hν
  have h4 := hs.card_Yv hA h26 hβv
  have := Subgroup.card_le_of_le hle
  omega

theorem C_le_Cst (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α : Geo H M} (hs : Sit43 α)
    {β : Geo H M} (hβ : β ∈ nbrs α) :
    stab α ⊓ stab β ⊓ Subgroup.centralizer (Vst β : Set G) ≤ Cst β := by
  intro g hg
  obtain ⟨⟨hgα, hgβ⟩, hgV⟩ := hg
  have hβv : vtype β = true := Sit43.vtype_true_of_adj hs.vα hβ
  have hgH : g ∈ H ⊔ M := stab_le β hgβ
  have hfix := fun {ν : Geo H M} (hν : ν ∈ nbrs β) =>
    smul_eq_of_centralizes_Vst hA h26 hs hβ ⟨g, hgH⟩ hgβ hgV hν
  have hgQ : g ∈ Qv β := by
    rw [Qv_eq_iInf hA β]
    exact Subgroup.mem_iInf.mpr fun w => Subgroup.mem_iInf.mpr fun hw =>
      ⟨hgβ, mem_stab_of_smul_eq (hfix hw)⟩
  refine ⟨hgQ, ?_⟩
  have hVn : Vn β ≤ Subgroup.centralizer ({g} : Set G) := by
    refine iSup₂_le fun ν hν => ?_
    have hνv : vtype ν = false := Sit43.vtype_false_of_adj hβv hν
    have hgν : g ∈ stab ν ⊓ stab β := ⟨Qv_le_stab_of_mem_nbrs hA hν hgQ, hgβ⟩
    have hgQν : g ∈ Qv ν := by
      refine mem_Qv_of_centralizes_comm hA hs hνv (nbrs_symm hν) hgν fun y hy => ?_
      rw [← hs.comm_Qv_eq hA h26 hβv hν] at hy
      exact conj_eq_of_mem_centralizer hgV (Subgroup.commutator_mono (Sit43.Zv_le_Vn_nbrs hν)
        le_rfl hy)
    intro y hy
    have := Subgroup.mem_centralizer_iff.mp (Qv_le_centralizer_Zv hA ν hgQν) y hy
    exact Subgroup.mem_centralizer_iff.mpr fun z hz => by
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact this.symm
  exact Subgroup.mem_centralizer_iff.mpr fun y hy => by
    have := hVn hy
    exact (Subgroup.mem_centralizer_iff.mp this g rfl).symm

theorem Cst_le_C (hA : F53Amalgam H M S) {α β : Geo H M} (hβ : β ∈ nbrs α) :
    Cst β ≤ stab α ⊓ stab β ⊓ Subgroup.centralizer (Vst β : Set G) := by
  intro g hg
  obtain ⟨hgQ, hgC⟩ := hg
  refine ⟨⟨Qv_le_stab_of_mem_nbrs hA (nbrs_symm hβ) hgQ, pCoreOf_le 2 _ hgQ⟩, ?_⟩
  refine mem_centralizer_of_conj_eq fun y hy => ?_
  have hn := stab_le_normalizer_Vn (G := G) β (pCoreOf_le 2 _ hgQ)
  have hyV : y ∈ Vn β := by
    refine Subgroup.commutator_le.mpr (fun a ha b hb => ?_) hy
    have h1 := (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn (G := G) β
      (pCoreOf_le 2 _ hb)) a⁻¹).mp (Subgroup.inv_mem _ ha)
    rw [commutatorElement_def]
    have h2 : a * (b * a⁻¹ * b⁻¹) ∈ Vn β := Subgroup.mul_mem _ ha h1
    simpa [mul_assoc] using h2
  exact conj_eq_of_mem_centralizer hgC hyV

theorem C_eq (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α : Geo H M} (hs : Sit43 α)
    {β : Geo H M} (hβ : β ∈ nbrs α) :
    stab α ⊓ stab β ⊓ Subgroup.centralizer (Vst β : Set G) = Cst β :=
  le_antisymm (C_le_Cst hA h26 hs hβ) (Cst_le_C hA hβ)

theorem Mcent_le_Cst (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α : Geo H M} (hs : Sit43 α)
    {β : Geo H M} (hβ : β ∈ nbrs α) : Mcent α ≤ Cst β := by
  intro g hg
  obtain ⟨hgQ, hgW⟩ := hg
  have hle : Vst β ≤ Wcomm α :=
    Subgroup.commutator_mono (hs.Vn_le_Wn hA h26 hβ) (Qv_le_stab_of_mem_nbrs hA (nbrs_symm hβ))
  rw [← C_eq hA h26 hs hβ]
  exact ⟨⟨pCoreOf_le 2 _ hgQ, Qv_le_stab_of_mem_nbrs hA hβ hgQ⟩,
    mem_centralizer_of_conj_eq fun y hy => conj_eq_of_mem_centralizer hgW (hle hy)⟩

theorem Mcent_le_centralizer_Wn (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α : Geo H M}
    (hs : Sit43 α) : Mcent α ≤ Subgroup.centralizer (Wn α : Set G) := by
  intro g hg
  have hW : Wn α ≤ Subgroup.centralizer ({g} : Set G) := by
    rw [Sit43.Wn_eq_iSup_Vn hA h26 hs hs.vα]
    refine iSup₂_le fun δ hδ y hy => ?_
    have := (Mcent_le_Cst hA h26 hs hδ hg).2
    exact Subgroup.mem_centralizer_iff.mpr fun z hz => by
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact (Subgroup.mem_centralizer_iff.mp this y hy).symm
  exact Subgroup.mem_centralizer_iff.mpr fun y hy => by
    exact (Subgroup.mem_centralizer_iff.mp (hW hy) g rfl).symm

theorem out19 (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α : Geo H M} (hs : Sit43 α)
    {β : Geo H M} (hβ : β ∈ nbrs α) : Out19 α β where
  C_eq := C_eq hA h26 hs hβ
  M_le_C := Mcent_le_Cst hA h26 hs hβ
  M_le_centralizer := Mcent_le_centralizer_Wn hA h26 hs

end CFSG.Quasithin.F53.Stellmacher.S43.Even

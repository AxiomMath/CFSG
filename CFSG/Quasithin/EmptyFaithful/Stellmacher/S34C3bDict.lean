module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S34C3bMod

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53 Equiv S42B1

namespace S34

namespace C3b

open CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs (secData_secModule card_Zv_eq_sq)

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}
variable {δ μ : Geo H M}

omit [Finite G] in
theorem Zv_le_Vn_nbr (hμ : μ ∈ nbrs δ) : Zv μ ≤ Vn δ :=
  le_iSup₂_of_le (f := fun (ν : Geo H M) (_ : ν ∈ nbrs δ) => Zv ν) μ hμ le_rfl

theorem comm_mem_Zv (hG : Glob H M S) (hδ : vtype δ = false) (hμ : μ ∈ nbrs δ) {a z : G}
    (ha : a ∈ stab δ ⊓ stab μ) (hz : z ∈ Zv μ) : a * z * a⁻¹ * z⁻¹ ∈ Zv δ := by
  have h1 := Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers a) hz
  rw [Subgroup.commutator_comm] at h1
  have h2 := aon_edge hG hδ hμ (g := a) ⟨ha.2, ha.1⟩
  have h3 : ⁅Zv μ, Subgroup.zpowers a⁆ ≤ Zv δ := by
    by_cases hq : a ∈ Qv μ
    · rw [h2.1 hq]; exact bot_le
    · rw [h2.2 hq]
  have h4 := h3 h1
  rwa [commutatorElement_def] at h4

namespace C3Data

variable (D : C3Data δ μ)

noncomputable abbrev mod : Model 5 := secModule D.sec D.θ D.surj D.ker_le

theorem mem_fixSecIn_iff {A : Subgroup G} (hA : A ≤ stab δ) {x : G} :
    x ∈ fixSecIn A (Cb δ) (Vn δ) ↔
      ∃ hx : x ∈ Vn δ, D.sec.proj ⟨x, hx⟩ ∈ fixW D.mod ((A.subgroupOf (stab δ)).map D.θ) := by
  have := D.sec.normal_subgroupOf
  have hsd := secData_secModule D.sec D.θ D.surj D.ker_le
  constructor
  · intro h
    have hx : x ∈ Vn δ := ((X1512.mem_fixSecIn D.sec.le).mp h).1
    exact ⟨hx, (secData_mem_fixW_iff hsd D.sec.le hA (u := D.sec.proj ⟨x, hx⟩) (x := ⟨x, hx⟩)
      rfl).mpr h⟩
  · rintro ⟨hx, h⟩
    exact (secData_mem_fixW_iff hsd D.sec.le hA (u := D.sec.proj ⟨x, hx⟩) (x := ⟨x, hx⟩)
      rfl).mp h

theorem fixSecIn_eq_of_fixW_eq {A B : Subgroup G} (hA : A ≤ stab δ) (hB : B ≤ stab δ)
    (h : fixW D.mod ((A.subgroupOf (stab δ)).map D.θ) =
      fixW D.mod ((B.subgroupOf (stab δ)).map D.θ)) :
    fixSecIn A (Cb δ) (Vn δ) = fixSecIn B (Cb δ) (Vn δ) := by
  ext x
  rw [D.mem_fixSecIn_iff hA, D.mem_fixSecIn_iff hB, h]

theorem relIndex_fixSecIn {A : Subgroup G} (hA : A ≤ stab δ) :
    (fixSecIn A (Cb δ) (Vn δ)).relIndex (Vn δ) =
      (fixW D.mod ((A.subgroupOf (stab δ)).map D.θ)).index := by
  have := D.sec.normal_subgroupOf
  exact (secData_secModule D.sec D.θ D.surj D.ker_le).relIndex_fixSecIn D.sec.le hA

@[expose] noncomputable def Zbar (hμ : μ ∈ nbrs δ) : Subgroup D.mod.W :=
  (D.sec.proj.comp (Subgroup.inclusion (Zv_le_Vn_nbr hμ))).range

theorem mem_Zbar (hμ : μ ∈ nbrs δ) {w : D.mod.W} :
    w ∈ D.Zbar hμ ↔ ∃ z : G, ∃ hz : z ∈ Zv μ, D.sec.proj ⟨z, Zv_le_Vn_nbr hμ hz⟩ = w := by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, z.2, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z, hz⟩, rfl⟩

theorem card_Zbar (hG : Glob H M S) (hδ : vtype δ = false) (hμ : μ ∈ nbrs δ) :
    Nat.card (D.Zbar hμ) = Nat.card (Zv δ) := by
  set f : ↥(Zv μ) →* D.mod.W := D.sec.proj.comp (Subgroup.inclusion (Zv_le_Vn_nbr hμ)) with hf
  have hker : f.ker = (Cb δ).subgroupOf (Zv μ) := by
    ext z
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact D.sec.proj_eq_one_iff ⟨z, Zv_le_Vn_nbr hμ z.2⟩
  have hkcard : Nat.card f.ker = Nat.card (Zv δ) := by
    rw [hker, ← Subgroup.inf_subgroupOf_right]
    refine (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).trans ?_
    rw [Cb_inf_Zv_eq hG hδ hμ]
  have hvμ : vtype μ = true := by
    cases h : vtype μ
    · exact absurd (hδ.trans h.symm) (vtype_ne_of_adj (show (graph (H ⊔ M) H M).Adj δ μ from hμ))
    · rfl
  have hsq := card_Zv_eq_sq hG.amalg hvμ (show (graph (H ⊔ M) H M).Adj μ δ from (nbrs_symm hμ))
    (hG.central δ hδ)
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, hkcard, hsq] at h1
  have hpos : 0 < Nat.card (Zv δ) := Nat.card_pos
  have h2 : Nat.card f.range = Nat.card (D.Zbar hμ) := rfl
  rw [← h2]
  nlinarith [h1, hpos]

theorem Zbar_le_fixW (hG : Glob H M S) (hδ : vtype δ = false) (hμ : μ ∈ nbrs δ) :
    D.Zbar hμ ≤ fixW D.mod S5Syl := by
  intro w hw
  obtain ⟨z, hz, rfl⟩ := (D.mem_Zbar hμ).mp hw
  intro σ hσ
  rw [← D.map_syl] at hσ
  obtain ⟨a, ha, rfl⟩ := hσ
  have haE : (a : G) ∈ stab δ ⊓ stab μ := Subgroup.mem_subgroupOf.mp ha
  refine (secModule_act_proj D.sec D.θ D.surj D.ker_le a ⟨z, Zv_le_Vn_nbr hμ hz⟩).trans ?_
  refine (D.sec.proj_eq_proj_iff _ _).mpr ?_
  have h4 := Zv_le_Cb hG hδ (comm_mem_Zv hG hδ hμ haE (Subgroup.inv_mem _ hz))
  convert h4 using 1
  simp [IsSec.conjN, mul_assoc]

theorem eq_top_of_Zbar_le (hμ : μ ∈ nbrs δ) (U : Subgroup D.mod.W) (hU : IsInvSub D.mod ⊤ U)
    (hZU : D.Zbar hμ ≤ U) : U = ⊤ := by
  have := D.sec.normal_subgroupOf
  set U' : Subgroup G := (U.comap D.sec.proj).map (Vn δ).subtype with hU'
  have hmem : ∀ x : G, x ∈ U' ↔ ∃ hx : x ∈ Vn δ, D.sec.proj ⟨x, hx⟩ ∈ U := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hx, h⟩
      exact ⟨⟨x, hx⟩, h, rfl⟩
  have hinv : ∀ k ∈ stab δ, ∀ x ∈ U', k * x * k⁻¹ ∈ U' := by
    intro k hk' x hx
    obtain ⟨hxV, hxU⟩ := (hmem x).mp hx
    refine (hmem _).mpr ⟨D.sec.conj_mem_N ⟨k, hk'⟩ ⟨x, hxV⟩, ?_⟩
    have h1 := hU (D.θ ⟨k, hk'⟩) (Subgroup.mem_top _) _ hxU
    rw [secModule_act_proj D.sec D.θ D.surj D.ker_le] at h1
    exact h1
  have hZμ : Zv μ ≤ U' := fun z hz =>
    (hmem z).mpr ⟨Zv_le_Vn_nbr hμ hz, hZU ((D.mem_Zbar hμ).mpr ⟨z, hz, rfl⟩)⟩
  have hVU : Vn δ ≤ U' := by
    refine iSup₂_le fun ν hν => ?_
    obtain ⟨g, hgδ, hgν⟩ := stab_transitive_on_nbrs hμ hν
    have hν' : Zv ν = conjSub (g : G) (Zv μ) := by rw [← hgν]; exact Zv_smul g μ
    intro x hx
    rw [hν', mem_conjSub] at hx
    have h1 := hinv (g : G) hgδ _ (hZμ hx)
    have e : (g : G) * ((g : G)⁻¹ * x * (g : G)) * (g : G)⁻¹ = x := by group
    rwa [e] at h1
  rw [eq_top_iff]
  intro w _
  obtain ⟨v, rfl⟩ := D.sec.proj_surjective w
  exact ((hmem _).mp (hVU v.2)).2

end C3Data

end C3b

end S34

end F53.Stellmacher

end CFSG.Quasithin

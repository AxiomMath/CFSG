module

public import CFSG.Quasithin.EmptyFaithful.SzF53Defs
public import CFSG.Quasithin.EmptyFaithful.SzF53BasFin
public import CFSG.Quasithin.EmptyFaithful.SzF53BasGeo
public import CFSG.Quasithin.EmptyFaithful.S1422Local
public import CFSG.Quasithin.EmptyFaithful.S152FinShape

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S152X CFSG.Quasithin.F7

namespace F53

variable {G : Type} [Group G] [Finite G]

abbrev Geo (H M : Subgroup G) : Type := CosetGeom (H ⊔ M) H M

open CosetGeom

variable {H M S : Subgroup G}

theorem amalgamSymm (hA : F53Amalgam H M S) : AmalgamHyp (H ⊔ M) M H S where
  gen := sup_comm _ _
  charTwo := hA.charTwo_right
  sylow₁ := hA.amalgam.sylow₂
  sylow₂ := hA.amalgam.sylow₁
  o2_trivial := hA.amalgam.o2_trivial

@[expose] noncomputable def oTwoQuotConjSub' (a : G) (X : Subgroup G) :
    OTwoQuot X ≃* OTwoQuot (conjSub a X) :=
  QuotientGroup.congr (CFSG.Open.pCore 2 ↥X) (CFSG.Open.pCore 2 ↥(conjSub a X))
    ((MulAut.conj a).subgroupMap X) (map_pCore_mulEquiv 2 _)

omit [Finite G] in
theorem charTwo_conjSub (a : G) {X : Subgroup G} (h : CharTwo X) : CharTwo (conjSub a X) := by
  unfold CharTwo at h ⊢
  rw [pCoreOf_conjSub, conjSub_centralizer, ← conjSub_inf]
  exact conjSub_mono a h

theorem edge_conj (hA : F53Amalgam H M S) {δ μ : Geo H M} (h : μ ∈ nbrs δ) :
    ∃ g : ↥(H ⊔ M),
      ((stab δ = conjSub (g : G) H ∧ stab μ = conjSub (g : G) M) ∨
        (stab δ = conjSub (g : G) M ∧ stab μ = conjSub (g : G) H)) ∧
      stab δ ⊓ stab μ = conjSub (g : G) S := by
  have h₁ := hA.amalgam.le₁
  have h₂ := hA.amalgam.le₂
  obtain ⟨g, ⟨h0, h1⟩ | ⟨h0, h1⟩⟩ := exists_smul_edge
    (show (graph (H ⊔ M) H M).Adj δ μ from h)
  · refine ⟨g, Or.inl ⟨?_, ?_⟩, ?_⟩
    · rw [← h0, stab_smul, stab_γ₀ h₁]
    · rw [← h1, stab_smul, stab_γ₁ h₂]
    · rw [← h0, ← h1, stab_smul, stab_smul, stab_γ₀ h₁, stab_γ₁ h₂, ← conjSub_inf, hA.inf_eq]
  · refine ⟨g, Or.inr ⟨?_, ?_⟩, ?_⟩
    · rw [← h1, stab_smul, stab_γ₁ h₂]
    · rw [← h0, stab_smul, stab_γ₀ h₁]
    · rw [← h0, ← h1, stab_smul, stab_smul, stab_γ₀ h₁, stab_γ₁ h₂, inf_comm, ← conjSub_inf,
        hA.inf_eq]

theorem sylow_stab_inf_left (hA : F53Amalgam H M S) {δ μ : Geo H M} (h : μ ∈ nbrs δ) :
    IsSylowTwoOf (stab δ ⊓ stab μ) (stab δ) := by
  obtain ⟨g, hg, he⟩ := edge_conj hA h
  rw [he]
  rcases hg with ⟨h1, -⟩ | ⟨h1, -⟩
  · rw [h1]; exact isSylowTwoOf_conj hA.amalgam.sylow₁ _
  · rw [h1]; exact isSylowTwoOf_conj hA.amalgam.sylow₂ _

theorem sylow_stab_inf_right (hA : F53Amalgam H M S) {δ μ : Geo H M} (h : μ ∈ nbrs δ) :
    IsSylowTwoOf (stab δ ⊓ stab μ) (stab μ) := by
  have h' : δ ∈ nbrs μ := SimpleGraph.Adj.symm (show (graph (H ⊔ M) H M).Adj δ μ from h)
  rw [inf_comm]
  exact sylow_stab_inf_left hA h'

theorem charTwo_stab (hA : F53Amalgam H M S) (δ : Geo H M) : CharTwo (stab δ) := by
  cases hv : vtype δ with
  | false =>
    obtain ⟨g, hg⟩ := exists_smul_eq_γ₀ hv
    rw [hg, stab_smul, stab_γ₀ hA.amalgam.le₁]
    exact charTwo_conjSub _ hA.amalgam.charTwo
  | true =>
    obtain ⟨g, hg⟩ := exists_smul_eq_γ₁ hv
    rw [hg, stab_smul, stab_γ₁ hA.amalgam.le₂]
    exact charTwo_conjSub _ hA.charTwo_right

theorem quot_stab_five (hA : F53Amalgam H M S) {δ : Geo H M} (hv : vtype δ = false) :
    Nonempty (OTwoQuot (stab δ) ≃* Equiv.Perm (Fin 5)) := by
  obtain ⟨g, hg⟩ := exists_smul_eq_γ₀ hv
  obtain ⟨φ⟩ := hA.quot_left
  rw [hg, stab_smul, stab_γ₀ hA.amalgam.le₁]
  exact ⟨(oTwoQuotConjSub' (g : G) H).symm.trans φ⟩

theorem quot_stab_three (hA : F53Amalgam H M S) {δ : Geo H M} (hv : vtype δ = true) :
    Nonempty (OTwoQuot (stab δ) ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨g, hg⟩ := exists_smul_eq_γ₁ hv
  obtain ⟨φ⟩ := hA.quot_right
  rw [hg, stab_smul, stab_γ₁ hA.amalgam.le₂]
  exact ⟨(oTwoQuotConjSub' (g : G) M).symm.trans φ⟩

theorem card_oTwoQuot_five (hA : F53Amalgam H M S) : Nat.card (OTwoQuot H) = 2 ^ 3 * 15 := by
  obtain ⟨φ⟩ := hA.quot_left
  rw [Nat.card_congr φ.toEquiv, S152Fin.card_Perm_five]; norm_num

theorem card_oTwoQuot_three (hA : F53Amalgam H M S) : Nat.card (OTwoQuot M) = 2 ^ 1 * 3 := by
  obtain ⟨φ⟩ := hA.quot_right
  rw [Nat.card_congr φ.toEquiv, Nat.card_perm]
  simp [Nat.factorial]

theorem index_S_H (hA : F53Amalgam H M S) : (S.subgroupOf H).index = 15 :=
  index_sylow_eq_of_card_quot hA.amalgam.sylow₁ (by decide) (card_oTwoQuot_five hA)

theorem index_S_M (hA : F53Amalgam H M S) : (S.subgroupOf M).index = 3 :=
  index_sylow_eq_of_card_quot hA.amalgam.sylow₂ (by decide) (card_oTwoQuot_three hA)

theorem inf_normalizer_M (hA : F53Amalgam H M S) : M ⊓ Subgroup.normalizer (S : Set G) = S :=
  inf_normalizer_eq_of_card_quot hA.amalgam.sylow₂ le_rfl Nat.prime_three (by decide)
    (card_oTwoQuot_three hA)

theorem exists_hom_five (hA : F53Amalgam H M S) :
    ∃ φ : ↥H →* Equiv.Perm (Fin 5), Function.Surjective φ ∧ φ.ker ≤ S.subgroupOf H ∧
      Nat.card ((S.subgroupOf H).map φ) = 8 ∧
      ∀ y : ↥H, φ y ∈ (S.subgroupOf H).map φ ↔ (y : G) ∈ S := by
  obtain ⟨e⟩ := hA.quot_left
  let φ : ↥H →* Equiv.Perm (Fin 5) :=
    (e : OTwoQuot H →* Equiv.Perm (Fin 5)).comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H))
  have hφs : Function.Surjective φ := fun p => by
    obtain ⟨q, rfl⟩ := e.surjective p
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨x, rfl⟩
  have hφker : ∀ x : ↥H, φ x = 1 ↔ (x : G) ∈ pCoreOf 2 H := by
    intro x
    have hx : φ x = e (QuotientGroup.mk x) := rfl
    rw [hx, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff, F1.mem_pCore_iff_coe]
  have hker : φ.ker ≤ S.subgroupOf H := fun y hy =>
    isSylowTwoOf_pCoreOf_le hA.amalgam.sylow₁ ((hφker y).mp hy)
  have hidx : ((S.subgroupOf H).map φ).index = 15 := by
    rw [Subgroup.index_map_eq (S.subgroupOf H) hφs hker]; exact index_S_H hA
  have hcard : Nat.card ((S.subgroupOf H).map φ) = 8 := by
    have h1 := ((S.subgroupOf H).map φ).card_mul_index
    rw [hidx, card_perm5] at h1
    omega
  refine ⟨φ, hφs, hker, hcard, fun y => ?_⟩
  constructor
  · rintro ⟨s, hs, hsy⟩
    have h1 : s⁻¹ * y ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hsy, inv_mul_cancel]
    have h2 : ((s⁻¹ * y : ↥H) : G) ∈ S := hker h1
    have h3 : (y : G) = (s : G) * ((s⁻¹ * y : ↥H) : G) := by simp
    rw [h3]
    exact S.mul_mem hs h2
  · intro hy
    exact ⟨y, hy, rfl⟩

theorem inf_normalizer_H (hA : F53Amalgam H M S) : H ⊓ Subgroup.normalizer (S : Set G) = S := by
  obtain ⟨φ, hφs, hker, hcard, hmem⟩ := exists_hom_five hA
  have hN := normalizer_eq_of_card_eight _ hcard
  refine le_antisymm ?_ (le_inf hA.amalgam.sylow₁.1 Subgroup.le_normalizer)
  rintro x ⟨hxH, hxN⟩
  have hxD : φ ⟨x, hxH⟩ ∈
      Subgroup.normalizer (((S.subgroupOf H).map φ : Subgroup (Equiv.Perm (Fin 5))) :
        Set (Equiv.Perm (Fin 5))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro d
    obtain ⟨y, rfl⟩ := hφs d
    rw [← map_inv, ← map_mul, ← map_mul, hmem, hmem]
    have := (Subgroup.mem_normalizer_iff.mp hxN) (y : G)
    simpa using this
  rw [hN] at hxD
  exact (hmem _).mp hxD

omit [Finite G] in
theorem relIndex_conjSub (g : G) (A B : Subgroup G) :
    (conjSub g A).relIndex (conjSub g B) = A.relIndex B :=
  Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) A B
    (MulEquiv.injective (MulAut.conj g))

theorem card_nbrs_false (hA : F53Amalgam H M S) {δ : Geo H M} (hv : vtype δ = false) :
    Nat.card (nbrs δ) = 15 := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₀ hv
  have hμ : g • γ₁ (H ⊔ M) H M ∈ nbrs (g • γ₀ (H ⊔ M) H M) := (smul_adj g).mpr adj_γ₀_γ₁
  rw [CosetGeom.card_nbrs_eq_relIndex_geom hμ, stab_smul, stab_smul, stab_γ₀ hA.amalgam.le₁,
    stab_γ₁ hA.amalgam.le₂, ← conjSub_inf, hA.inf_eq, relIndex_conjSub]
  exact index_S_H hA

theorem card_nbrs_true (hA : F53Amalgam H M S) {δ : Geo H M} (hv : vtype δ = true) :
    Nat.card (nbrs δ) = 3 := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₁ hv
  have hμ : g • γ₀ (H ⊔ M) H M ∈ nbrs (g • γ₁ (H ⊔ M) H M) :=
    (smul_adj g).mpr adj_γ₀_γ₁.symm
  rw [CosetGeom.card_nbrs_eq_relIndex_geom hμ, stab_smul, stab_smul, stab_γ₀ hA.amalgam.le₁,
    stab_γ₁ hA.amalgam.le₂, inf_comm, ← conjSub_inf, hA.inf_eq, relIndex_conjSub]
  exact index_S_M hA

end F53

end CFSG.Quasithin

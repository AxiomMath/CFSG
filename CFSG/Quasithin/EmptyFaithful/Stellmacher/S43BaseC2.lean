module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseModC2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open CFSG.LieType.BorelTits Equiv
open scoped commutatorElement

namespace F53.Stellmacher.S43

open CosetGeom

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace Sit43

variable {α : Geo H M}

theorem exists_dict5 (hA : F53Amalgam H M S) (hs : Sit43 α) {δ : Geo H M} (hδ : δ ∈ nbrs α) :
    Nonempty (Dict5 (stab α) (stab α ⊓ stab δ) (Zv α)) :=
  nonempty_dict5 (quot_stab_five hA hs.vα) (sylow_stab_inf_left hA hδ) hs.orth

theorem relIndex_Qv_stab_five (hA : F53Amalgam H M S) (hs : Sit43 α) {δ : Geo H M}
    (hδ : δ ∈ nbrs α) : (Qv α).relIndex (stab α) = 120 := by
  obtain ⟨D⟩ := hs.exists_dict5 hA hδ
  have hb : D.bar (stab α) = ⊤ := D.bar_eq_of_iff fun x => by simp [x.2]
  have h := D.card_bar (K := stab α) le_rfl
  rw [hb, Subgroup.card_top, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin,
    inf_of_le_left (pCoreOf_le 2 _)] at h
  exact h.symm.trans (by decide)

theorem relIndex_Qv_edge_stab (hA : F53Amalgam H M S) (hs : Sit43 α) {δ : Geo H M}
    (hδ : δ ∈ nbrs α) : (Qv α).relIndex (stab α ⊓ stab δ) = 8 := by
  obtain ⟨D⟩ := hs.exists_dict5 hA hδ
  have hQS : Qv α ≤ stab α ⊓ stab δ := le_inf (pCoreOf_le 2 _) (Qv_le_stab_of_mem_nbrs hA hδ)
  have h := D.card_bar (K := stab α ⊓ stab δ) inf_le_left
  rw [D.bar_S, card_S5Syl, show pCoreOf 2 (stab α) ⊓ (stab α ⊓ stab δ) = Qv α from
    inf_eq_left.mpr hQS] at h
  exact h.symm

theorem sup_Qv_eq_stab (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    {δ : Geo H M} (hδ : δ ∈ nbrs α) {X : Subgroup G} (hX : X ≤ stab α)
    (h : Qv δ ⊔ X ⊔ Qv α = stab α) : Qv δ ⊔ X = stab α := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U : Subgroup G := Qv δ ⊔ X with hU
  have hQδα : Qv δ ≤ stab α := Qv_le_stab_of_mem_nbrs hA (nbrs_symm hδ)
  have hUα : U ≤ stab α := sup_le hQδα hX
  have hQαn : stab α ≤ Subgroup.normalizer (Qv α : Set G) := le_normalizer_pCoreOf 2 (stab α)
  have h2 : (Qv δ).relIndex (Qv α) = 2 := hs.relIndex_Qv_Qv hA h26 hs.vα hδ
  have hU2 : U.relIndex (Qv α) ∣ 2 := h2 ▸ Subgroup.relIndex_dvd_of_le_left _ le_sup_left
  rcases (Nat.dvd_prime Nat.prime_two).mp hU2 with h1 | h2'
  · have hQU : Qv α ≤ U := Subgroup.relIndex_eq_one.mp h1
    apply le_antisymm (sup_le hQδα hX) 
    rw [← h]
    exact sup_le le_rfl hQU
  · exfalso
    have hQαδ : Qv α ≤ stab α ⊓ stab δ :=
      le_inf (pCoreOf_le 2 _) (Qv_le_stab_of_mem_nbrs hA hδ)
    have hBA : Qv δ ⊓ Qv α ≤ U ⊓ Qv α := inf_le_inf_right _ le_sup_left
    have hAQ : U ⊓ Qv α ≤ Qv α := inf_le_right
    have hAB : U ⊓ Qv α ≤ Qv δ := by
      have e := Subgroup.relIndex_mul_relIndex _ _ _ hBA hAQ
      rw [Subgroup.inf_relIndex_right, Subgroup.inf_relIndex_right, h2, h2'] at e
      have e1 : (Qv δ ⊓ Qv α).relIndex (U ⊓ Qv α) = 1 := by omega
      exact (Subgroup.relIndex_eq_one.mp e1).trans inf_le_left
    have hUQ : (Qv α).relIndex U = 120 := by
      rw [← relIndex_sup_of_le_normalizer (hUα.trans hQαn), h]
      exact hs.relIndex_Qv_stab_five hA hδ
    have hQδ : (Qv α).relIndex (Qv δ) = 8 := by
      rw [← relIndex_sup_of_le_normalizer (hQδα.trans hQαn), sup_comm,
        hs.sup_Qv_edge hA h26 hs.vα hδ]
      exact hs.relIndex_Qv_edge_stab hA hδ
    have hAQδ : (U ⊓ Qv α).relIndex (Qv δ) = 8 := by
      have : U ⊓ Qv α = Qv α ⊓ Qv δ := by
        apply le_antisymm
        · exact le_inf inf_le_right hAB
        · exact le_inf (inf_le_right.trans le_sup_left) inf_le_left
      rw [this, Subgroup.inf_relIndex_right]
      exact hQδ
    have hmul := Subgroup.relIndex_mul_relIndex (U ⊓ Qv α) (Qv δ) U hAB
      (le_sup_left : Qv δ ≤ U)
    rw [hAQδ, Subgroup.inf_relIndex_left, hUQ] at hmul
    have hodd : ¬ 2 ∣ (Qv δ).relIndex U := by omega
    have hsyl : IsSylowTwoOf (Qv δ ⊓ U) U := by
      rw [inf_of_le_left (le_sup_left : Qv δ ≤ U)]
      exact ⟨le_sup_left, pCoreOf_isPGroup 2 (stab δ), hodd⟩
    have hZδ : Zv δ ≤ Qv α := (hs.Zv_le_Zv_nbr hA h26 (vtype_true_of_adj hs.vα hδ)
      (nbrs_symm hδ)).trans (Zv_le_Qv hA α)
    have hzle : Zv δ ≤ pCoreOf 2 U :=
      (le_inf hZδ (Zv_le_Qv hA δ |>.trans le_sup_left) : Zv δ ≤ Qv α ⊓ U).trans
        (pCoreOf_inf_le hUα)
    have hgen : U ⊔ (stab α ⊓ stab δ) = stab α :=
      le_antisymm (sup_le hUα inf_le_left) (h ▸ sup_le_sup_left hQαδ U)
    have hZ := h26 hs.b1 α δ U ⟨hδ, hUα, hsyl, hzle, hgen⟩ le_sup_left
    rw [hs.centerOf_eq_bot hA h26 hs.vα hδ, le_bot_iff] at hZ
    exact Zv_ne_bot hA α hZ

end Sit43

@[expose] def Mab (α δ : Geo H M) : Subgroup G :=
  ⨆ (K : Subgroup G) (_ : K ≤ stab α ∧ stab α ⊓ stab δ ≤ K ∧ K ≠ stab α), K

omit [Finite G] in
theorem le_Mab {α δ : Geo H M} {K : Subgroup G} (h1 : K ≤ stab α) (h2 : stab α ⊓ stab δ ≤ K)
    (h3 : K ≠ stab α) : K ≤ Mab α δ :=
  le_iSup₂_of_le (f := fun (K : Subgroup G) (_ : K ≤ stab α ∧ stab α ⊓ stab δ ≤ K ∧
    K ≠ stab α) => K) K ⟨h1, h2, h3⟩ le_rfl

omit [Finite G] in
theorem Mab_le_stab (α δ : Geo H M) : Mab α δ ≤ stab α :=
  iSup₂_le fun _ hK => hK.1

namespace Sit43

variable {α : Geo H M}

omit [Finite G] in
theorem mem_Mab_iff {δ : Geo H M} (D : Dict5 (stab α) (stab α ⊓ stab δ) (Zv α))
    (x : ↥(stab α)) : (x : G) ∈ Mab α δ ↔ D.ψ x 4 = 4 := by
  have hSle : stab α ⊓ stab δ ≤ stab α := inf_le_left
  have hMt : Mab α δ = ((MulAction.stabilizer (Perm (Fin 5)) (4 : Fin 5)).comap D.ψ).map
      (stab α).subtype := by
    apply le_antisymm
    · refine iSup₂_le fun K hK => ?_
      obtain ⟨hKα, hSK, hKne⟩ := hK
      have hbar : S5Syl ≤ D.bar K := by
        rw [← D.bar_S]
        exact Subgroup.map_mono fun y hy => hSK hy
      have hQK : pCoreOf 2 (stab α) ≤ K := (D.Q_le).trans hSK
      have hne : D.bar K ≠ ⊤ := by
        intro htop
        apply hKne
        refine le_antisymm hKα fun y hy => ?_
        exact (D.mem_iff_of_Q_le hQK ⟨y, hy⟩).mpr (htop ▸ Subgroup.mem_top _)
      have hle := (le_stab_four_or_eq_top hbar).resolve_right hne
      intro y hy
      refine ⟨⟨y, hKα hy⟩, ?_, rfl⟩
      exact hle ⟨⟨y, hKα hy⟩, hy, rfl⟩
    · apply le_Mab (Subgroup.map_subtype_le _)
      · intro y hy
        refine ⟨⟨y, hSle hy⟩, ?_, rfl⟩
        exact S5Syl_le_stab_four (D.ψ_mem_S5Syl (S := stab α ⊓ stab δ) hy)
      · intro heq
        have hall : ∀ σ : Perm (Fin 5), σ 4 = 4 := by
          intro σ
          obtain ⟨z, rfl⟩ := D.surj σ
          obtain ⟨w, hw, hwz⟩ := heq.ge z.2
          have : w = z := Subtype.ext hwz
          subst this
          exact hw
        have := hall (Equiv.swap 0 4)
        simp at this
  rw [hMt]
  constructor
  · rintro ⟨w, hw, hwz⟩
    have : w = x := Subtype.ext hwz
    subst this
    exact hw
  · intro h
    exact ⟨x, h, rfl⟩

theorem stab_inf_le_Mab (hA : F53Amalgam H M S) (hs : Sit43 α) {δ : Geo H M} (hδ : δ ∈ nbrs α) :
    stab α ⊓ stab δ ≤ Mab α δ := by
  obtain ⟨D⟩ := hs.exists_dict5 hA hδ
  intro y hy
  exact (mem_Mab_iff D ⟨y, hy.1⟩).mpr
    (S5Syl_le_stab_four (D.ψ_mem_S5Syl (S := stab α ⊓ stab δ) hy))

theorem Qv_le_Mab (hA : F53Amalgam H M S) (hs : Sit43 α) {δ : Geo H M} (hδ : δ ∈ nbrs α) :
    Qv α ≤ Mab α δ :=
  (le_inf (pCoreOf_le 2 _) (Qv_le_stab_of_mem_nbrs hA hδ)).trans (hs.stab_inf_le_Mab hA hδ)

theorem relIndex_Mab (hA : F53Amalgam H M S) (hs : Sit43 α) {δ : Geo H M} (hδ : δ ∈ nbrs α) :
    (Mab α δ).relIndex (stab α) = 5 := by
  obtain ⟨D⟩ := hs.exists_dict5 hA hδ
  have e : (Mab α δ).subgroupOf (stab α) =
      (MulAction.stabilizer (Perm (Fin 5)) (4 : Fin 5)).comap D.ψ := by
    ext x
    rw [Subgroup.mem_subgroupOf, mem_Mab_iff D x, Subgroup.mem_comap, MulAction.mem_stabilizer_iff,
      Perm.smul_def]
  rw [Subgroup.relIndex, e, Subgroup.index_comap_of_surjective _ D.surj,
    MulAction.index_stabilizer_of_transitive]
  simp

theorem Mab_ne_stab (hA : F53Amalgam H M S) (hs : Sit43 α) {δ : Geo H M} (hδ : δ ∈ nbrs α) :
    Mab α δ ≠ stab α := by
  intro h
  have h1 := hs.relIndex_Mab hA hδ
  rw [h, Subgroup.relIndex_self] at h1
  omega

theorem Mab_eq_or_eq_stab (hA : F53Amalgam H M S) (hs : Sit43 α) {δ : Geo H M} (hδ : δ ∈ nbrs α)
    {K : Subgroup G} (h1 : Mab α δ ≤ K) (h2 : K ≤ stab α) : K = Mab α δ ∨ K = stab α := by
  by_cases h : K = stab α
  · exact Or.inr h
  · exact Or.inl (le_antisymm (le_Mab h2 ((hs.stab_inf_le_Mab hA hδ).trans h1) h) h1)

theorem sup_Qv_eq_stab_of_not_le (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    {δ : Geo H M} (hδ : δ ∈ nbrs α) {X : Subgroup G} (hX : X ≤ stab α) (hXM : ¬ X ≤ Mab α δ) :
    Qv δ ⊔ X = stab α := by
  have hQδα : Qv δ ≤ stab α := Qv_le_stab_of_mem_nbrs hA (nbrs_symm hδ)
  refine hs.sup_Qv_eq_stab hA h26 hδ hX ?_
  by_contra hne
  have hedge : stab α ⊓ stab δ ≤ Qv δ ⊔ X ⊔ Qv α := by
    rw [← hs.sup_Qv_edge hA h26 hs.vα hδ]
    exact sup_le le_sup_right (le_sup_left.trans le_sup_left)
  have hle : Qv δ ⊔ X ⊔ Qv α ≤ Mab α δ :=
    le_Mab (sup_le (sup_le hQδα hX) (pCoreOf_le 2 _)) hedge hne
  exact hXM (le_sup_right.trans (le_sup_left.trans hle))

theorem sup_Qv_zpowers_eq_stab (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    {δ : Geo H M} (hδ : δ ∈ nbrs α) {x : G} (hx : x ∈ stab α) (hxM : x ∉ Mab α δ) :
    Qv δ ⊔ Subgroup.zpowers x = stab α :=
  hs.sup_Qv_eq_stab_of_not_le hA h26 hδ (by rwa [Subgroup.zpowers_le])
    fun h => hxM (h (Subgroup.mem_zpowers x))

end Sit43

end F53.Stellmacher.S43

end CFSG.Quasithin

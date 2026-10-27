module

public import CFSG.Quasithin.EmptyFaithful.S152FinChief
public import CFSG.Quasithin.EmptyFaithful.S152FinWr

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {G : Type} [Group G]

namespace S152Fin

theorem pCoreOf_subgroupOf (H : Subgroup G) :
    (pCoreOf 2 H).subgroupOf H = CFSG.Open.pCore 2 ↥H := by
  unfold pCoreOf Subgroup.subgroupOf
  exact Subgroup.comap_map_eq_self_of_injective Subtype.val_injective _

theorem card_OTwoQuot (H : Subgroup G) : Nat.card (OTwoQuot H) = (pCoreOf 2 H).relIndex H := by
  unfold Subgroup.relIndex
  rw [pCoreOf_subgroupOf]
  rfl

theorem QuotIsoWith.card_eq {H C J : Subgroup G} {X Y : Type*} [Group X] [Group Y]
    (h : QuotIsoWith H C J X Y) : Nat.card X = (C.subgroupOf H).index := by
  obtain ⟨φ, hφ, hker, -⟩ := h
  rw [← hker, Subgroup.index_ker, φ.range_eq_top_of_surjective hφ, Subgroup.card_top]

theorem cSecIn_le_left (H L N : Subgroup G) : cSecIn H L N ≤ H :=
  (Subgroup.closure_le H).mpr fun _ hx => hx.1

theorem pCoreOf_le_cSecIn [Finite G] {H U L N : Subgroup G} (hU : IsElemAbelian 2 U)
    (hs : IsChiefStep H U L N) : pCoreOf 2 H ≤ cSecIn H L N := by
  intro p hp
  apply Subgroup.subset_closure
  exact ⟨pCoreOf_le 2 H hp, fun x hx => commutator_pCoreOf_le hU hs p hp x hx⟩

theorem card_Perm_five : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
  rw [Nat.card_perm]; simp [Nat.factorial]

theorem card_Wr_five :
    Nat.card (Equiv.Perm (Fin 5) ≀ᵣ Multiplicative (ZMod 2)) = 28800 := by
  rw [RegularWreathProduct.card, card_Perm_five]
  have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_eq_fintype_card]; simp
  rw [h2]
  norm_num

theorem shape_eq_wr
    [Finite G] {H U L N : Subgroup G} (hU : IsElemAbelian 2 U)
    (hs : IsChiefStep H U L N)
    (hq : Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 3) ≀ᵣ Multiplicative (ZMod 2)))
    (hshape : ChiefFactorShape H L N) :
    cSecIn H L N = pCoreOf 2 H ∧
      QuotIsoWith H (cSecIn H L N) (thompsonJ H)
        (Equiv.Perm (Fin 3) ≀ᵣ Multiplicative (ZMod 2))
        (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) ∧ NaturalSnPair 3 H L N := by
  obtain ⟨ι⟩ := hq
  have hQC : pCoreOf 2 H ≤ cSecIn H L N := pCoreOf_le_cSecIn hU hs
  have h72 : (pCoreOf 2 H).relIndex H = 72 := by
    rw [← card_OTwoQuot, Nat.card_congr ι.toEquiv, card_Wr]
  have hQC' : (pCoreOf 2 H).subgroupOf H ≤ (cSecIn H L N).subgroupOf H :=
    fun x hx => hQC hx
  have hdvd : ((cSecIn H L N).subgroupOf H).index ∣ 72 := by
    rw [← h72]
    exact Subgroup.index_dvd_of_le hQC'
  obtain ⟨hNorm, h | h | h | h⟩ := hshape
  ·
    exfalso
    obtain ⟨φ, hφ, hker, -⟩ := h.1
    have hle : CFSG.Open.pCore 2 ↥H ≤ φ.ker := by
      rw [hker, ← pCoreOf_subgroupOf]
      exact hQC'
    let ψ : OTwoQuot H →* Equiv.Perm (Fin 3) := QuotientGroup.lift (CFSG.Open.pCore 2 ↥H) φ hle
    have hψ : Function.Surjective ψ := by
      intro y
      obtain ⟨x, rfl⟩ := hφ y
      exact ⟨QuotientGroup.mk x, rfl⟩
    exact not_exists_surj_Wr_perm3 ⟨ψ.comp ι.symm.toMonoidHom, hψ.comp ι.symm.surjective⟩
  · exfalso
    have := QuotIsoWith.card_eq h.1
    rw [card_Perm_five] at this
    rw [← this] at hdvd
    omega
  · refine ⟨?_, h.1, h.2⟩
    have hc := QuotIsoWith.card_eq h.1
    rw [card_Wr] at hc
    have hrel := Subgroup.relIndex_mul_index hQC'
    have h72' : ((pCoreOf 2 H).subgroupOf H).index = 72 := h72
    rw [← hc, h72'] at hrel
    have h1 : ((pCoreOf 2 H).subgroupOf H).relIndex ((cSecIn H L N).subgroupOf H) = 1 := by
      omega
    have h2 := Subgroup.relIndex_eq_one.mp h1
    refine le_antisymm (fun x hx => ?_) hQC
    have hxH : x ∈ H := cSecIn_le_left H L N hx
    exact h2 (show (⟨x, hxH⟩ : ↥H) ∈ (cSecIn H L N).subgroupOf H from hx)
  · exfalso
    have := QuotIsoWith.card_eq h.1
    rw [card_Wr_five] at this
    rw [← this] at hdvd
    omega

theorem thompsonJ_le_left (H : Subgroup G) : thompsonJ H ≤ H :=
  iSup₂_le fun _ hA => hA.1

theorem relIndex_thompsonJ_sup_pCoreOf {H : Subgroup G}
    (hQ : QuotIsoWith H (pCoreOf 2 H) (thompsonJ H)
      (Equiv.Perm (Fin 3) ≀ᵣ Multiplicative (ZMod 2))
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) :
    (thompsonJ H ⊔ pCoreOf 2 H).relIndex H = 2 := by
  obtain ⟨φ, hφ, hker, ⟨e⟩⟩ := hQ
  have h36 : Nat.card (Subgroup.map φ ((thompsonJ H).subgroupOf H)) = 36 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    have h6 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
      rw [Nat.card_perm]; simp [Nat.factorial]
    rw [h6]
  have hQH : pCoreOf 2 H ≤ H := pCoreOf_le 2 H
  have hsup : (thompsonJ H ⊔ pCoreOf 2 H).subgroupOf H =
      Subgroup.comap φ (Subgroup.map φ ((thompsonJ H).subgroupOf H)) := by
    rw [Subgroup.comap_map_eq, hker, Subgroup.subgroupOf_sup (thompsonJ_le_left H) hQH]
  unfold Subgroup.relIndex
  have hidx := Subgroup.index_comap_of_surjective
    (H := Subgroup.map φ ((thompsonJ H).subgroupOf H)) hφ
  rw [hsup, hidx]
  have h1 := (Subgroup.map φ ((thompsonJ H).subgroupOf H)).card_mul_index
  rw [h36, card_Wr] at h1
  omega

theorem kernel_le_pCoreOf [Finite G] {T M H V : Subgroup G}
    (hU : IsElemAbelian 2 (conjClosure V H)) (hC : Concl319 T M V H True)
    (hq : Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 3) ≀ᵣ Multiplicative (ZMod 2))) :
    H ⊓ Subgroup.centralizer (conjClosure V H : Set G) ≤ pCoreOf 2 H := by
  obtain ⟨L, N, hs, hnc, -⟩ := exists_noncentral_of_series hC.chief (by norm_num : 1 ≤ 2)
  have hshape := hC.shape trivial L N hs hnc
  obtain ⟨hK, -, -⟩ := shape_eq_wr hU hs hq hshape
  rw [← hK]
  rintro x ⟨hxH, hxC⟩
  apply Subgroup.subset_closure
  refine ⟨hxH, fun n hn => ?_⟩
  have h1 := Subgroup.mem_centralizer_iff.mp hxC n (hs.1.1 hn)
  have : x * n * x⁻¹ * n⁻¹ = 1 := by
    rw [← h1]; group
  rw [this]
  exact L.one_mem

end S152Fin

end CFSG.Quasithin

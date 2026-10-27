module

public import Certificates.Data.Th687.MFactsB

public section

namespace CFSG.Sporadic.Th.Max3

theorem nfAt_zero : nfAt (0 : Fin 512) = 1 := by
  rw [nfAt, nfN]
  simp

theorem nfAt_one : nfAt (1 : Fin 512) = Max3.z := by
  rw [nfAt, nfN]
  have h : ∀ i : Fin 8, 1 / 2 ^ (i.val + 1) % 2 = 0 := by
    intro i
    have hlt : 1 < 2 ^ (i.val + 1) :=
      one_lt_pow' (by norm_num) (Nat.succ_ne_zero i.val)
    simp [Nat.div_eq_of_lt hlt]
  simp [h]

theorem nfAt_injective :
    Function.Injective nfAt := by
  have hsurj : Function.Surjective fun k : Fin 512 =>
      (⟨nfAt k, AltQuot.nfAt_mem_Q k⟩ : ↥Max3.Q) := by
    rintro ⟨g, hg⟩
    obtain ⟨k, hk⟩ := InvRep.exists_nfAt_eq hg
    exact ⟨k, Subtype.ext hk⟩
  have hbij : Function.Bijective fun k : Fin 512 =>
      (⟨nfAt k, AltQuot.nfAt_mem_Q k⟩ : ↥Max3.Q) :=
    (Nat.bijective_iff_surjective_and_card _).mpr
      ⟨hsurj, by rw [Nat.card_fin, Max3.card_Q]⟩
  intro k l h
  exact hbij.1 (Subtype.ext h)

end CFSG.Sporadic.Th.Max3

namespace CFSG.Sporadic.Th.Recog

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3
open CFSG.Sporadic.Th.Recog.MFactsBData


private abbrev commSet (g : J) : Set ↥Max3.M :=
  {x | (x : J) ∈ Max3.Q ∧ (x : J) * g = g * (x : J)}

private noncomputable def idx {g : J} (x : ↥(commSet g)) : Fin 512 :=
  Classical.choose (InvRep.exists_nfAt_eq x.2.1)

private theorem nfAt_idx {g : J} (x : ↥(commSet g)) : nfAt (idx x) = (x.1 : J) :=
  Classical.choose_spec (InvRep.exists_nfAt_eq x.2.1)

theorem mem_commFilter_iff {G : Array V4} {g : J} (hG : IsRows G g) (k : Fin 512) :
    k ∈ commFilter G ↔ nfAt k * g = g * nfAt k := by
  have hk := isRows_nfAt k
  constructor
  · intro h
    have h' : eqRows (mulRows G (rowsNfAt k)) (mulRows (rowsNfAt k) G) = true := by
      simpa [commFilter] using h
    exact ((hG.mul hk).eq_of_eqRows (hk.mul hG) h').symm
  · intro h
    have hA : IsRows (mulRows (rowsNfAt k) G) (g * nfAt k) := by
      have := hk.mul hG
      rwa [h] at this
    have hrows : mulRows G (rowsNfAt k) = mulRows (rowsNfAt k) G :=
      (hG.mul hk).rows_eq hA
    simpa [commFilter] using eqRows_iff.mpr hrows

private noncomputable def ofCommFilter {g : J} {G : Array V4} (hG : IsRows G g)
    (k : {k : Fin 512 // k ∈ commFilter G}) : ↥(commSet g) :=
  ⟨⟨nfAt k.1, Max3.Q_le_M (AltQuot.nfAt_mem_Q k.1)⟩,
    ⟨AltQuot.nfAt_mem_Q k.1, (mem_commFilter_iff hG k.1).mp k.2⟩⟩

private noncomputable def commFilterEquiv {g : J} {G : Array V4} (hG : IsRows G g) :
    ↥(commSet g) ≃ {k : Fin 512 // k ∈ commFilter G} where
  toFun x :=
    ⟨idx x, by
      rw [mem_commFilter_iff hG, nfAt_idx]
      exact x.2.2⟩
  invFun := ofCommFilter hG
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    change nfAt (idx x) = (x.1 : J)
    exact nfAt_idx x
  right_inv k := by
    apply Subtype.ext
    apply nfAt_injective
    rw [nfAt_idx]
    rfl

private theorem card_commFilter_subtype (G : Array V4) :
    Nat.card {k : Fin 512 // k ∈ commFilter G} = (commFilter G).length := by
  let S : Set (Fin 512) := {k | k ∈ commFilter G}
  have hnodup : (commFilter G).Nodup := by
    unfold commFilter
    exact (List.nodup_finRange 512).filter _
  have hS : S = ((commFilter G).toFinset : Set (Fin 512)) := by
    ext k
    simp [S]
  change Nat.card ↥S = (commFilter G).length
  rw [Nat.card_coe_set_eq, hS, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnodup]

theorem card_Q_inf_centralizer_eq_length {g : ↥Max3.M} {G : Array V4}
    (hG : IsRows G (g : J)) :
    Nat.card ↥(Max3.Q.subgroupOf Max3.M ⊓
      Subgroup.centralizer ({g} : Set ↥Max3.M)) = (commFilter G).length := by
  have hCT : (Max3.Q.subgroupOf Max3.M ⊓
      Subgroup.centralizer ({g} : Set ↥Max3.M) : Set ↥Max3.M) = commSet (g : J) := by
    ext x
    change x ∈ (Max3.Q.subgroupOf Max3.M ⊓
        Subgroup.centralizer ({g} : Set ↥Max3.M) : Subgroup ↥Max3.M) ↔
      ((x : J) ∈ Max3.Q ∧ (x : J) * (g : J) = (g : J) * (x : J))
    rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hQ, hcomm⟩
      refine ⟨hQ, ?_⟩
      have h := congrArg (fun z : ↥Max3.M => (z : J)) hcomm
      simpa [Subgroup.coe_mul] using h
    · rintro ⟨hQ, hcomm⟩
      refine ⟨hQ, ?_⟩
      apply Subtype.ext
      simpa [Subgroup.coe_mul] using hcomm
  calc Nat.card ↥(Max3.Q.subgroupOf Max3.M ⊓
        Subgroup.centralizer ({g} : Set ↥Max3.M))
      = (Max3.Q.subgroupOf Max3.M ⊓
          Subgroup.centralizer ({g} : Set ↥Max3.M) : Set ↥Max3.M).ncard :=
        Nat.card_coe_set_eq _
    _ = (commSet (g : J)).ncard := by rw [hCT]
    _ = Nat.card ↥(commSet (g : J)) := (Nat.card_coe_set_eq (commSet (g : J))).symm
    _ = Nat.card {k : Fin 512 // k ∈ commFilter G} := Nat.card_congr (commFilterEquiv hG)
    _ = (commFilter G).length := card_commFilter_subtype G

end CFSG.Sporadic.Th.Recog

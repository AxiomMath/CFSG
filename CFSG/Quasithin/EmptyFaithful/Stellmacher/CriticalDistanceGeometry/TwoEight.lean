module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.Steps
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Statements
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Index
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.ThompsonEdge
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.FaithfulY
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.S5Overgroup
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.CritEdgeIndex

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

namespace F53

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

open CosetGeom Equiv

omit [Finite G] in
theorem card_map_eq {A N : Subgroup G} {n : ℕ} (ψ : ↥A →* Perm (Fin n))
    (hker : ∀ x : ↥A, ψ x = 1 ↔ (x : G) ∈ N) (B : Subgroup ↥A) :
    Nat.card (B.map ψ) = N.relIndex (B.map A.subtype) := by
  have h1 : ψ.ker = N.comap A.subtype := by
    ext x; exact (MonoidHom.mem_ker.trans (hker x))
  rw [← Subgroup.relIndex_ker, h1, Subgroup.relIndex_comap]

omit [Finite G] in
theorem exists_lift_of_klein {A N Q T : Subgroup G} (hNQ : N ≤ Q) (hQT : Q ≤ T) (hTA : T ≤ A)
    (ψ : ↥A →* Perm (Fin 5)) (hψ : Function.Surjective ψ)
    (hker : ∀ x : ↥A, ψ x = 1 ↔ (x : G) ∈ N)
    (hT : N.relIndex T = 8) (hQ : N.relIndex Q = 4) (hexp : ∀ g ∈ Q, g ^ 2 ∈ N) :
    ∃ U : Subgroup G, U ≤ A ∧ N ≤ U ∧ Q ≤ U ∧ ¬ 2 ∣ (Q.subgroupOf U).index ∧ U ⊔ T = A := by
  have hQA : Q ≤ A := hQT.trans hTA
  have hNA : N ≤ A := hNQ.trans hQA
  set P : Subgroup (Perm (Fin 5)) := (T.subgroupOf A).map ψ with hPdef
  set R : Subgroup (Perm (Fin 5)) := (Q.subgroupOf A).map ψ with hRdef
  have hPcard : Nat.card P = 8 := by
    rw [hPdef, card_map_eq ψ hker, Subgroup.map_subgroupOf_eq_of_le hTA, hT]
  have hRcard : Nat.card R = 4 := by
    rw [hRdef, card_map_eq ψ hker, Subgroup.map_subgroupOf_eq_of_le hQA, hQ]
  have hRP : R ≤ P := Subgroup.map_mono (fun x hx => hQT hx)
  have hR2 : ∀ r ∈ R, r ^ 2 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hker]
    exact hexp _ hx
  obtain ⟨K, hRK, hodd, hKP⟩ :=
    CFSG.Quasithin.F53.exists_overgroup_of_klein P R hPcard hRP hRcard hR2
  have hkerW : ψ.ker ≤ K.comap ψ := fun x hx => by
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]; exact K.one_mem
  have hNU : N ≤ (K.comap ψ).map A.subtype := fun x hx =>
    ⟨⟨x, hNA hx⟩, by
      show ψ ⟨x, hNA hx⟩ ∈ K
      rw [(hker ⟨x, hNA hx⟩).mpr hx]; exact K.one_mem, rfl⟩
  have hQU : Q ≤ (K.comap ψ).map A.subtype := fun x hx =>
    ⟨⟨x, hQA hx⟩, hRK ⟨⟨x, hQA hx⟩, hx, rfl⟩, rfl⟩
  refine ⟨(K.comap ψ).map A.subtype, Subgroup.map_subtype_le _, hNU, hQU, ?_, ?_⟩
  · have hK : Nat.card K = N.relIndex ((K.comap ψ).map A.subtype) := by
      rw [← card_map_eq ψ hker, Subgroup.map_comap_eq_self_of_surjective hψ]
    have hmul := Subgroup.relIndex_mul_relIndex N Q _ hNQ hQU
    rw [hQ, ← hK] at hmul
    have hc : Nat.card (R.subgroupOf K) = 4 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRK).toEquiv, hRcard]
    have h2 := Subgroup.card_mul_index (R.subgroupOf K)
    rw [hc] at h2
    have : Q.relIndex ((K.comap ψ).map A.subtype) = (R.subgroupOf K).index := by omega
    show ¬ 2 ∣ Q.relIndex _
    rw [this]; exact hodd
  · have hW : K.comap ψ ⊔ T.subgroupOf A = ⊤ := by
      have h1 : (K.comap ψ ⊔ T.subgroupOf A).map ψ = ⊤ := by
        rw [Subgroup.map_sup, Subgroup.map_comap_eq_self_of_surjective hψ]; exact hKP
      have h2 := Subgroup.comap_map_eq ψ (K.comap ψ ⊔ T.subgroupOf A)
      rw [h1, Subgroup.comap_top, sup_eq_left.mpr (hkerW.trans le_sup_left)] at h2
      exact h2.symm
    have := congrArg (Subgroup.map A.subtype) hW
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hTA, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at this
    exact this

end F53

namespace F53.Stellmacher

open CosetGeom

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem sup_Qv_eq_inf_of_vtype_false (hA : F53Amalgam H M S) (h26 : Hss26AAt H M)
    (hmod : Hss28ModAt H M) (hb : 1 < bMin H M) {δ ν : Geo H M} (hν : ν ∈ nbrs δ)
    (hvδ : vtype δ = false) : Qv δ ⊔ Qv ν = stab δ ⊓ stab ν := by
  have hadj : (graph (H ⊔ M) H M).Adj δ ν := hν
  have hvν : vtype ν = true := by
    have := vtype_ne_of_adj hadj
    revert this; cases hvν : vtype ν <;> simp [hvδ]
  rcases CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.Qv_le_or_sup_eq hA hν hvν
    with hle | h
  swap
  · exact h
  exfalso
  have hνδ : δ ∈ nbrs ν := hadj.symm
  have hZν : Zv ν ≤ Qv δ :=
    Zv_le_Qv_of_dist_lt (by
      have h1 : dist ν δ = 1 := dist_eq_one_iff_adj.mpr hadj.symm
      have h2 := bMin_le_bAt (H := H) (M := M) ν
      omega)
  have hJ := not_thompsonJ_le_Qv hA hν hle
  have hfaith := centralizer_omegaOneCenter_Qv hA hν hle hZν
  obtain ⟨hexp, hnc⟩ := hmod δ ν hν hvδ hle hJ hfaith
  obtain ⟨n, ψ, hn, hψ, hker⟩ := exists_quotHom hA δ
  rcases hn with ⟨rfl, -⟩ | ⟨-, hv⟩
  swap
  · simp [hvδ] at hv
  have hQνδ : Qv ν ≤ stab δ ⊓ stab ν := by
    refine le_inf (Qv_le_stab_of_mem_nbrs hA hνδ) ?_
    exact pCoreOf_le 2 _
  have hT : (Qv δ).relIndex (stab δ ⊓ stab ν) = 8 := relIndex_Qv_inf_false hA hν hvδ
  have hQ : (Qv δ).relIndex (Qv ν) = 4 := by
    have h2 : (Qv ν).relIndex (stab δ ⊓ stab ν) = 2 := by
      rw [inf_comm]; exact relIndex_Qv_inf_true hA hνδ hvν
    have hm := Subgroup.relIndex_mul_relIndex (Qv δ) (Qv ν) (stab δ ⊓ stab ν) hle hQνδ
    rw [hT, h2] at hm
    omega
  obtain ⟨U, hUA, hδU, hνU, hodd, hgen⟩ :=
    exists_lift_of_klein hle hQνδ inf_le_left ψ hψ hker hT hQ hexp
  have hpc : Qv δ ≤ pCoreOf 2 U := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact le_pCoreOf_of_le_normalizer 2 hδU
      (hUA.trans (le_normalizer_pCoreOf 2 (stab δ)))
      (pCoreOf_isPGroup 2 (stab δ))
  have hsit : SitSigma δ ν U :=
    { adj := hadj
      le_stab := hUA
      sylow := by
        rw [inf_eq_left.mpr hνU]
        refine ⟨hνU, ?_, ?_⟩
        · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
          exact pCoreOf_isPGroup 2 (stab ν)
        · simpa [inf_eq_left.mpr hνU] using hodd
      zle := hZν.trans hpc
      gen := hgen }
  have hZδ := h26 hb δ ν U hsit hνU
  exact hnc ((omegaOneCenter_le_Zv hA hν).2.1.trans hZδ)

theorem hss28At_of_hss26A_of_mod (hA : F53Amalgam H M S) (h26 : Hss26AAt H M)
    (hmod : Hss28ModAt H M) : Hss28At H M := by
  intro hb α β hαβ _
  cases hv : vtype α
  · exact sup_Qv_eq_inf_of_vtype_false hA h26 hmod hb hαβ hv
  · have hvβ : vtype β = false := by
      have := vtype_ne_of_adj hαβ
      revert this; cases hvβ : vtype β <;> simp [hv]
    have := sup_Qv_eq_inf_of_vtype_false hA h26 hmod hb
      (show α ∈ nbrs β from hαβ.symm) hvβ
    rwa [sup_comm, inf_comm]

end F53.Stellmacher

end CFSG.Quasithin

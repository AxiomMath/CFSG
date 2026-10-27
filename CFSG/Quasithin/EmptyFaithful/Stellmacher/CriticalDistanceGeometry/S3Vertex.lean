module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Reduction

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7

namespace F53

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

open CosetGeom Equiv

theorem perm3_card_le_two_of_isPGroup (K : Subgroup (Perm (Fin 3))) (hK : IsPGroup 2 K) :
    Nat.card K ≤ 2 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hK
  have hdvd : Nat.card K ∣ 6 := card_perm3 ▸ Subgroup.card_subgroup_dvd_card K
  rw [hk] at hdvd ⊢
  have : k ≤ 1 := by
    by_contra h
    push Not at h
    have : 2 ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 h
    have := this.trans hdvd
    omega
  calc 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
    _ = 2 := rfl

theorem perm3_eq_of_le_of_isPGroup (P K : Subgroup (Perm (Fin 3))) (hK : IsPGroup 2 K)
    (hP : P ≤ K) (hne : P ≠ ⊥) : P = K := by
  have h1 : 1 < Nat.card P := (Subgroup.one_lt_card_iff_ne_bot P).mpr hne
  have h2 := perm3_card_le_two_of_isPGroup K hK
  exact Subgroup.eq_of_le_of_card_ge hP (by omega)

theorem perm3_sup_eq_top (P Q : Subgroup (Perm (Fin 3))) (hP : Nat.card P = 2)
    (hQ : Nat.card Q = 2) (hne : P ≠ Q) : P ⊔ Q = ⊤ := by
  have hdvd : Nat.card ↥(P ⊔ Q) ∣ 6 := card_perm3 ▸ Subgroup.card_subgroup_dvd_card _
  have hPd : 2 ∣ Nat.card ↥(P ⊔ Q) := hP ▸ Subgroup.card_dvd_of_le le_sup_left
  have hne2 : Nat.card ↥(P ⊔ Q) ≠ 2 := by
    intro h
    apply hne
    have h1 : P = P ⊔ Q := Subgroup.eq_of_le_of_card_ge le_sup_left (by omega)
    have h2 : Q = P ⊔ Q := Subgroup.eq_of_le_of_card_ge le_sup_right (by omega)
    rw [h1, ← h2]
  have h6 : Nat.card ↥(P ⊔ Q) = 6 := by
    have hle : Nat.card ↥(P ⊔ Q) ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
    obtain ⟨c, hc⟩ := hPd
    have hc3 : c ≤ 3 := by omega
    rw [hc] at hdvd hne2 ⊢
    interval_cases c <;> omega
  exact Subgroup.eq_top_of_card_eq _ (by rw [h6, card_perm3])

theorem inf_normalizer_edge (hA : F53Amalgam H M S) {δ μ : Geo H M} (h : μ ∈ nbrs δ) :
    stab δ ⊓ Subgroup.normalizer ((stab δ ⊓ stab μ : Subgroup G) : Set G) = stab δ ⊓ stab μ := by
  obtain ⟨g, hg, he⟩ := edge_conj hA h
  rw [he]
  rcases hg with ⟨h1, -⟩ | ⟨h1, -⟩
  · rw [h1, conjSub_normalizer, ← conjSub_inf, inf_normalizer_H hA]
  · rw [h1, conjSub_normalizer, ← conjSub_inf, inf_normalizer_M hA]

theorem inf_stab_ne_of_ne (hA : F53Amalgam H M S) {δ μ ν : Geo H M} (hμ : μ ∈ nbrs δ)
    (hν : ν ∈ nbrs δ) (hne : μ ≠ ν) : stab δ ⊓ stab μ ≠ stab δ ⊓ stab ν := by
  intro heq
  obtain ⟨x, hx, hxμ⟩ := stab_transitive_on_nbrs hμ hν
  have hsν : stab ν = conjSub (x : G) (stab μ) := by rw [← hxμ, stab_smul]
  have hnorm : (x : G) ∈ Subgroup.normalizer ((stab δ ⊓ stab μ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have hyμ : y ∈ stab μ := hy.2
      have hyδ : y ∈ stab δ := hy.1
      have : (x : G) * y * (x : G)⁻¹ ∈ stab δ ⊓ stab ν := by
        refine ⟨(stab δ).mul_mem ((stab δ).mul_mem hx hyδ) ((stab δ).inv_mem hx), ?_⟩
        have h3 : (x : G) * y * (x : G)⁻¹ ∈ conjSub (x : G) (stab μ) :=
          mul_mem_conjSub hyμ
        rwa [← hsν] at h3
      rwa [← heq] at this
    · intro hy
      have h1 : y ∈ stab δ := by
        have := (stab δ).mul_mem ((stab δ).mul_mem ((stab δ).inv_mem hx) hy.1) hx
        simpa [mul_assoc] using this
      refine ⟨h1, ?_⟩
      have hy' : (x : G) * y * (x : G)⁻¹ ∈ stab δ ⊓ stab ν := heq ▸ hy
      have h2 : (x : G) * y * (x : G)⁻¹ ∈ conjSub (x : G) (stab μ) := hsν ▸ hy'.2
      have h4 := mem_conjSub.mp h2
      simpa [mul_assoc] using h4
  have := inf_normalizer_edge hA hμ
  have hxT : (x : G) ∈ stab δ ⊓ stab μ := by rw [← this]; exact ⟨hx, hnorm⟩
  exact hne (smul_eq_of_mem_stab hxT.2 ▸ hxμ)


theorem Qv_le_edge (hA : F53Amalgam H M S) {δ μ : Geo H M} (h : μ ∈ nbrs δ) :
    Qv δ ≤ stab δ ⊓ stab μ :=
  isSylowTwoOf_pCoreOf_le (sylow_stab_inf_left hA h)

theorem exists_quotHom_true (hA : F53Amalgam H M S) {α : Geo H M} (hv : vtype α = true) :
    ∃ ψ : ↥(stab α) →* Perm (Fin 3), Function.Surjective ψ ∧
      ∀ x : ↥(stab α), ψ x = 1 ↔ (x : G) ∈ Qv α := by
  obtain ⟨n, ψ, hn, hs, hk⟩ := exists_quotHom hA α
  rcases hn with ⟨-, h⟩ | ⟨rfl, -⟩
  · rw [hv] at h; exact absurd h (by decide)
  · exact ⟨ψ, hs, hk⟩

omit [Finite G] in
theorem isPGroup_map_subgroupOf {α : Geo H M} (ψ : ↥(stab α) →* Perm (Fin 3)) {K : Subgroup G}
    (hK : IsPGroup 2 K) : IsPGroup 2 ((K.subgroupOf (stab α)).map ψ) :=
  (hK.comap_subtype).map ψ

theorem exists_mul_of_isPGroup_of_vtype_true (hA : F53Amalgam H M S) {δ : Geo H M}
    (hv : vtype δ = true) {K Z : Subgroup G} (hK : IsPGroup 2 K) (hKδ : K ≤ stab δ) (hZK : Z ≤ K)
    (hZ : ¬ Z ≤ Qv δ) : ∀ x ∈ K, ∃ a ∈ Z, ∃ q ∈ Qv δ, x = a * q := by
  obtain ⟨ψ, hs, hker⟩ := exists_quotHom_true hA hv
  have hne : (Z.subgroupOf (stab δ)).map ψ ≠ ⊥ := by
    intro hb
    apply hZ
    intro z hz
    have hz' : (⟨z, hZK.trans hKδ |> fun h => h hz⟩ : ↥(stab δ)) ∈ Z.subgroupOf (stab δ) := hz
    have : ψ ⟨z, hZK.trans hKδ |> fun h => h hz⟩ ∈ (Z.subgroupOf (stab δ)).map ψ :=
      ⟨_, hz', rfl⟩
    rw [hb, Subgroup.mem_bot] at this
    exact (hker _).mp this
  have hle : (Z.subgroupOf (stab δ)).map ψ ≤ (K.subgroupOf (stab δ)).map ψ :=
    Subgroup.map_mono fun y hy => hZK hy
  have heq := perm3_eq_of_le_of_isPGroup _ _ (isPGroup_map_subgroupOf ψ hK) hle hne
  intro x hx
  have hxδ : x ∈ stab δ := hKδ hx
  have hmem : ψ ⟨x, hxδ⟩ ∈ (Z.subgroupOf (stab δ)).map ψ := by
    rw [heq]; exact ⟨_, hx, rfl⟩
  obtain ⟨a, ha, hax⟩ := hmem
  refine ⟨(a : G), ha, (a : G)⁻¹ * x, ?_, by group⟩
  have : ψ (a⁻¹ * ⟨x, hxδ⟩) = 1 := by rw [map_mul, map_inv, hax, inv_mul_cancel]
  simpa using (hker _).mp this

theorem sup_Qv_eq_edge (hA : F53Amalgam H M S) {α β : Geo H M} (hv : vtype α = true)
    (hβ : β ∈ nbrs α) {X : Subgroup G} (hX : X ≤ stab α ⊓ stab β) (hXQ : ¬ X ≤ Qv α) :
    X ⊔ Qv α = stab α ⊓ stab β := by
  apply le_antisymm (sup_le hX (Qv_le_edge hA hβ))
  intro x hx
  obtain ⟨a, ha, q, hq, rfl⟩ := exists_mul_of_isPGroup_of_vtype_true hA hv
    (sylow_stab_inf_left hA hβ).2.1 inf_le_left hX hXQ x hx
  exact (X ⊔ Qv α).mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hq)

theorem sup_edges_eq_stab (hA : F53Amalgam H M S) {α β μ : Geo H M} (hv : vtype α = true)
    (hβ : β ∈ nbrs α) (hμ : μ ∈ nbrs α) (hne : β ≠ μ) :
    (stab α ⊓ stab β) ⊔ (stab α ⊓ stab μ) = stab α := by
  obtain ⟨ψ, hs, hker⟩ := exists_quotHom_true hA hv
  have hcard : ∀ {ν : Geo H M}, ν ∈ nbrs α →
      Nat.card (((stab α ⊓ stab ν).subgroupOf (stab α)).map ψ) = 2 := by
    intro ν hν
    set E := stab α ⊓ stab ν with hE
    set E' := E.subgroupOf (stab α) with hE'
    have hkerE : ψ.ker ≤ E' := fun x hx =>
      Qv_le_edge hA hν ((hker x).mp hx)
    have h2 : Nat.card (E'.map ψ) ≤ 2 :=
      perm3_card_le_two_of_isPGroup _ (isPGroup_map_subgroupOf ψ (sylow_stab_inf_left hA hν).2.1)
    have hidx : (E'.map ψ).index = E'.index := Subgroup.index_map_eq E' hs hkerE
    have hodd : ¬ 2 ∣ E'.index := (sylow_stab_inf_left hA hν).2.2
    have h6 := (E'.map ψ).card_mul_index
    rw [card_perm3] at h6
    rw [hidx] at h6
    have hpos : 0 < Nat.card (E'.map ψ) := Nat.card_pos
    have h12 : Nat.card (E'.map ψ) = 1 ∨ Nat.card (E'.map ψ) = 2 := by omega
    rcases h12 with h | h
    · rw [h] at h6; omega
    · exact h
  have hkerE : ∀ {ν : Geo H M}, ν ∈ nbrs α → ψ.ker ≤ ((stab α ⊓ stab ν).subgroupOf (stab α)) :=
    fun hν x hx => Qv_le_edge hA hν ((hker x).mp hx)
  have hdist : ((stab α ⊓ stab β).subgroupOf (stab α)).map ψ ≠
      ((stab α ⊓ stab μ).subgroupOf (stab α)).map ψ := by
    intro h
    apply inf_stab_ne_of_ne hA hβ hμ hne
    have h1 := congrArg (Subgroup.comap ψ) h
    rw [Subgroup.comap_map_eq_self (hkerE hβ), Subgroup.comap_map_eq_self (hkerE hμ)] at h1
    rw [Subgroup.subgroupOf_inj] at h1
    simpa using h1
  have htop := perm3_sup_eq_top _ _ (hcard hβ) (hcard hμ) hdist
  set W := ((stab α ⊓ stab β) ⊔ (stab α ⊓ stab μ)).subgroupOf (stab α) with hW
  have hWtop : W = ⊤ := by
    have h1 : W.map ψ = ⊤ := by
      rw [eq_top_iff, ← htop]
      exact sup_le (Subgroup.map_mono fun y hy => Subgroup.mem_sup_left hy)
        (Subgroup.map_mono fun y hy => Subgroup.mem_sup_right hy)
    rw [← Subgroup.comap_map_eq_self (f := ψ) (H := W) ((hkerE hβ).trans fun y hy => Subgroup.mem_sup_left hy),
      h1, Subgroup.comap_top]
  apply le_antisymm (sup_le inf_le_left inf_le_left)
  intro x hx
  have : (⟨x, hx⟩ : ↥(stab α)) ∈ W := by rw [hWtop]; trivial
  exact this

theorem sup_edge_eq_stab (hA : F53Amalgam H M S) {α β μ : Geo H M} (hv : vtype α = true)
    (hβ : β ∈ nbrs α) (hμ : μ ∈ nbrs α) (hne : β ≠ μ) {X : Subgroup G}
    (hX : X ≤ stab α ⊓ stab β) (hXQ : ¬ X ≤ Qv α) : X ⊔ (stab α ⊓ stab μ) = stab α := by
  apply le_antisymm (sup_le (hX.trans inf_le_left) inf_le_left)
  calc stab α = (stab α ⊓ stab β) ⊔ (stab α ⊓ stab μ) := (sup_edges_eq_stab hA hv hβ hμ hne).symm
    _ = (X ⊔ Qv α) ⊔ (stab α ⊓ stab μ) := by rw [sup_Qv_eq_edge hA hv hβ hX hXQ]
    _ ≤ X ⊔ (stab α ⊓ stab μ) :=
      sup_le (sup_le le_sup_left ((Qv_le_edge hA hμ).trans le_sup_right)) le_sup_right

end F53

end CFSG.Quasithin

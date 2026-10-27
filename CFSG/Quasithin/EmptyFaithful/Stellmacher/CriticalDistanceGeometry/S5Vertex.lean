module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.S3Vertex

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7

namespace F53

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

open CosetGeom Equiv
open scoped Pointwise

theorem exists_sylow_sup_involution_eq_top (t : Perm (Fin 5)) (ht : t ^ 2 = 1) (ht1 : t ≠ 1) :
    ∃ P : Subgroup (Equiv.Perm (Fin 5)), Nat.card P = 8 ∧ P ⊔ Subgroup.zpowers t = ⊤ := by
  have _ := ht
  obtain ⟨p, hp⟩ : ∃ p, t p ≠ p := by
    by_contra h
    push Not at h
    exact ht1 (Equiv.ext h)
  set g : Perm (Fin 5) := swap 4 p with hg
  have hg4 : g 4 = p := by simp [hg]
  set P : Subgroup (Perm (Fin 5)) := D0.map (MulAut.conj g).toMonoidHom with hP
  have hmem : ∀ x, x ∈ P ↔ ∃ y ∈ D0fin, g * y * g⁻¹ = x := by
    intro x
    rw [hP, Subgroup.mem_map]
    simp [MulAut.conj_apply, D0]
  have hcard : Nat.card P = 8 := by
    rw [hP, Subgroup.card_map_of_injective (MulAut.conj g).injective, D0_card]
  refine ⟨P, hcard, ?_⟩
  apply F5b_core P _ hcard p ?_ le_sup_left ?_
  · intro q j hq hj
    have hq' : g⁻¹ q ≠ 4 := by
      intro h
      apply hq
      rw [Perm.inv_def, Equiv.symm_apply_eq] at h
      rw [h, hg4]
    have hj' : g⁻¹ j ≠ 4 := by
      intro h
      apply hj
      rw [Perm.inv_def, Equiv.symm_apply_eq] at h
      rw [h, hg4]
    obtain ⟨d, hd, hdq⟩ := D0_trans (g⁻¹ q) hq' (g⁻¹ j) hj'
    refine ⟨g * d * g⁻¹, (hmem _).mpr ⟨d, hd, rfl⟩, ?_⟩
    have h3 : (g * d * g⁻¹) q = g (d (g⁻¹ q)) := rfl
    rw [h3, hdq]
    simp
  · intro hle
    have := hle (le_sup_right (a := P) (b := Subgroup.zpowers t) (Subgroup.mem_zpowers t))
    exact hp (by simpa [MulAction.mem_stabilizer_iff] using this)

theorem exists_nbr_sup_eq_stab_of_vtype_false (hA : F53Amalgam H M S) {δ : Geo H M}
    (hv : vtype δ = false) {X : Subgroup G} (hX : X ≤ stab δ) (hX2 : IsPGroup 2 X)
    (hXQ : ¬ X ≤ Qv δ) :
    ∃ μ ∈ nbrs δ, X ⊔ (stab δ ⊓ stab μ) = stab δ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, ψ, hn, hsurj, hker⟩ := exists_quotHom hA δ
  have hn5 : n = 5 := by
    rcases hn with ⟨h, _⟩ | ⟨_, h⟩
    · exact h
    · rw [hv] at h; exact absurd h (by decide)
  subst hn5
  set X' : Subgroup ↥(stab δ) := X.subgroupOf (stab δ) with hXdef
  have hXb2 : IsPGroup 2 (X'.map ψ) := (hX2.comap_subtype).map ψ
  obtain ⟨x₀, hx₀X, hx₀Q⟩ := IsConcreteLE.not_le_iff_exists.mp hXQ
  have hx₀s : x₀ ∈ stab δ := hX hx₀X
  have hψx₀ : ψ ⟨x₀, hx₀s⟩ ≠ 1 := fun h => hx₀Q ((hker _).mp h)
  have hψx₀mem : ψ ⟨x₀, hx₀s⟩ ∈ X'.map ψ := ⟨⟨x₀, hx₀s⟩, hx₀X, rfl⟩
  have h2dvd : 2 ∣ Nat.card (X'.map ψ) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hXb2
    rw [hk]
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exfalso
      rw [h0, pow_zero] at hk
      have := Subgroup.eq_bot_of_card_eq _ hk
      rw [this] at hψx₀mem
      exact hψx₀ (by simpa using hψx₀mem)
    · exact dvd_pow_self 2 h0.ne'
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(X'.map ψ)) 2 h2dvd
  set t : Equiv.Perm (Fin 5) := (y : Equiv.Perm (Fin 5)) with ht
  have htord : orderOf t = 2 := by rw [ht, Subgroup.orderOf_coe]; exact hy
  have ht2 : t ^ 2 = 1 := by rw [← htord]; exact pow_orderOf_eq_one t
  have ht1 : t ≠ 1 := by
    intro h; rw [h, orderOf_one] at htord; omega
  have htX : t ∈ X'.map ψ := y.2
  obtain ⟨P, hPc, hPt⟩ := exists_sylow_sup_involution_eq_top t ht2 ht1
  obtain ⟨μ₀, hμ₀⟩ := exists_adj δ
  have hμ₀' : μ₀ ∈ nbrs δ := hμ₀
  have hsyl := sylow_stab_inf_left hA hμ₀'
  set E0 : Subgroup ↥(stab δ) := (stab δ ⊓ stab μ₀).subgroupOf (stab δ) with hE0
  have hker0 : ψ.ker ≤ E0 := by
    intro z hz
    have : (z : G) ∈ Qv δ := (hker z).mp hz
    exact Qv_le_edge hA hμ₀' this
  have hR0 : Nat.card (E0.map ψ) = 8 := by
    have h2 : IsPGroup 2 (E0.map ψ) := (hsyl.2.1.comap_subtype).map ψ
    have hidx : (E0.map ψ).index = E0.index := by
      rw [← Subgroup.index_comap_of_surjective (H := E0.map ψ) hsurj,
        Subgroup.comap_map_eq_self hker0]
    have hodd : ¬ 2 ∣ (E0.map ψ).index := by rw [hidx]; exact hsyl.2.2
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp h2
    have hdvd : Nat.card (E0.map ψ) ∣ 120 := card_perm5 ▸ Subgroup.card_subgroup_dvd_card _
    have hmul := (E0.map ψ).card_mul_index
    rw [card_perm5] at hmul
    rw [hk] at hdvd hmul ⊢
    have hk3 : k ≤ 3 := by
      by_contra h
      push Not at h
      have : 2 ^ 4 ∣ 2 ^ k := pow_dvd_pow 2 h
      have := this.trans hdvd
      omega
    interval_cases k <;> omega
  obtain ⟨hP2, hPs, -⟩ := sylow_of_card_eight P hPc
  obtain ⟨hR2, hRs, -⟩ := sylow_of_card_eight (E0.map ψ) hR0
  obtain ⟨s, hs⟩ := MulAction.exists_smul_eq (Equiv.Perm (Fin 5)) (hR2.toSylow hRs) (hP2.toSylow hPs)
  have hPeq : ∀ z, z ∈ P ↔ ∃ r ∈ E0.map ψ, s * r * s⁻¹ = z := by
    intro z
    have h1 : P = MulAut.conj s • (E0.map ψ) := by
      have := congrArg (fun Q : Sylow 2 (Equiv.Perm (Fin 5)) => (Q : Subgroup (Equiv.Perm (Fin 5)))) hs
      simpa [Sylow.coe_subgroup_smul] using this.symm
    rw [h1, Subgroup.mem_smul_pointwise_iff_exists]
    simp [MulAut.conj_apply]
  obtain ⟨x, rfl⟩ := hsurj s
  let xg : ↥(H ⊔ M) := ⟨(x : G), stab_le δ x.2⟩
  have hxδ : xg • δ = δ := smul_eq_of_mem_stab x.2
  set μ : Geo H M := xg • μ₀ with hμ
  have hμn : μ ∈ nbrs δ := by
    have := (smul_adj xg).mpr hμ₀
    rw [hxδ] at this
    exact this
  have hEμ : stab δ ⊓ stab μ = conjSub (x : G) (stab δ ⊓ stab μ₀) := by
    have h1 : stab δ = stab (xg • δ) := by rw [hxδ]
    rw [conjSub_inf, hμ, stab_smul, ← stab_smul xg δ, hxδ]
  set Eμ : Subgroup ↥(stab δ) := (stab δ ⊓ stab μ).subgroupOf (stab δ) with hEμdef
  have hPle : P ≤ Eμ.map ψ := by
    intro z hz
    obtain ⟨r, ⟨e, he, rfl⟩, rfl⟩ := (hPeq z).mp hz
    refine ⟨x * e * x⁻¹, ?_, by simp⟩
    show ((x * e * x⁻¹ : ↥(stab δ)) : G) ∈ stab δ ⊓ stab μ
    rw [hEμ, mem_conjSub]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have : (x : G)⁻¹ * ((x : G) * (e : G) * (x : G)⁻¹) * (x : G) = (e : G) := by group
    have he' : (e : G) ∈ stab δ ⊓ stab μ₀ := he
    rw [this]; exact he'
  refine ⟨μ, hμn, ?_⟩
  have hYs : X ⊔ (stab δ ⊓ stab μ) ≤ stab δ := sup_le hX inf_le_left
  set Y' : Subgroup ↥(stab δ) := (X ⊔ (stab δ ⊓ stab μ)).subgroupOf (stab δ) with hY'
  have hXY : X' ≤ Y' := fun z hz => (le_sup_left : X ≤ X ⊔ (stab δ ⊓ stab μ)) hz
  have hEY : Eμ ≤ Y' := fun z hz => (le_sup_right : stab δ ⊓ stab μ ≤ X ⊔ (stab δ ⊓ stab μ)) hz
  have htop : (⊤ : Subgroup (Equiv.Perm (Fin 5))) ≤ Y'.map ψ := by
    rw [← hPt]
    exact sup_le (hPle.trans (Subgroup.map_mono hEY))
      ((Subgroup.zpowers_le.mpr htX).trans (Subgroup.map_mono hXY))
  have hkerY : ψ.ker ≤ Y' := fun z hz => hEY (by
    have : (z : G) ∈ Qv δ := (hker z).mp hz
    exact Qv_le_edge hA hμn this)
  have hY'top : Y' = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hz : ψ z ∈ Y'.map ψ := htop trivial
    obtain ⟨w, hw, hwz⟩ := hz
    have : z = w * (w⁻¹ * z) := by simp
    rw [this]
    refine Y'.mul_mem hw (hkerY ?_)
    rw [MonoidHom.mem_ker, map_mul, map_inv, hwz, inv_mul_cancel]
  refine le_antisymm hYs fun g hg => ?_
  have : (⟨g, hg⟩ : ↥(stab δ)) ∈ Y' := by rw [hY'top]; trivial
  exact this

end F53

end CFSG.Quasithin

module

public import CFSG.Sporadic.Co2Rank3.Maximal
public import CFSG.Sporadic.Co2Rank3.Transport

public noncomputable section

namespace CFSG.Sporadic.Co2Rank3

open CFSG.Sporadic.Co2Cert CFSG.Certificates MulAction

@[expose] def co2Reps : Fin 3 → Fin 2300 := ![0, 3, 1]

@[expose] def cosetReps {G : Type*} [Group G] (G₁ : Subgroup G) (u v : G) : Fin 3 → G ⧸ G₁ :=
  fun i => ((![1, u⁻¹, v⁻¹] i : G) : G ⧸ G₁)

theorem co2Reps_cover
    (y : Fin 2300) : ∃ i, ∃ l : co2P0, l • co2Reps i = y := by
  rcases co2P0_cover y with rfl | h | h
  · exact ⟨0, 1, one_smul _ _⟩
  · obtain ⟨l, hl⟩ := mem_orbit_iff.1 h
    exact ⟨1, l, hl⟩
  · obtain ⟨l, hl⟩ := mem_orbit_iff.1 h
    exact ⟨2, l, hl⟩

theorem co2Reps_len
    (i j : Fin 3)
    (h : (orbit co2P0 (co2Reps i)).ncard = (orbit co2P0 (co2Reps j)).ncard) : i = j := by
  have hsz : ∀ k : Fin 3, (orbit co2P0 (co2Reps k)).ncard = ![1, 891, 1408] k := by
    intro k
    fin_cases k
    · simp [co2Reps, orbit_co2P0_zero]
    · simpa [co2Reps] using ncard_co2Delta
    · simpa [co2Reps] using ncard_co2Gamma
  rw [hsz, hsz] at h
  fin_cases i <;> fin_cases j <;> simp at h ⊢

section Recognition

variable {G : Type*} [Group G] {G₁ : Subgroup G} (φ : G₁ ≃* co2P0) {u v : G}

include φ in
theorem cosetReps_stab (hu : ∀ h : G₁, u * h * u⁻¹ ∈ G₁ ↔ (φ h : Equiv.Perm (Fin 2300)) 3 = 3)
    (hv : ∀ h : G₁, v * h * v⁻¹ ∈ G₁ ↔ (φ h : Equiv.Perm (Fin 2300)) 1 = 1) (i : Fin 3)
    (k : G₁) : k • cosetReps G₁ u v i = cosetReps G₁ u v i ↔ φ k • co2Reps i = co2Reps i := by
  have key : ∀ w : G, (k • ((w : G) : G ⧸ G₁) = (w : G ⧸ G₁) ↔ w⁻¹ * k * w ∈ G₁) := by
    intro w
    rw [Subgroup.smul_def, Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq, mul_inv_rev,
      ← G₁.inv_mem_iff]
    simp [mul_assoc]
  fin_cases i
  · simp only [cosetReps, co2Reps, Fin.zero_eta, Matrix.cons_val_zero]
    rw [key]
    simp only [inv_one, one_mul, mul_one, SetLike.coe_mem, true_iff]
    exact mem_stabilizer_iff.1 (φ k).2.2
  · simp only [cosetReps, co2Reps, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [key, inv_inv, hu]
    rfl
  · simp only [cosetReps, co2Reps]
    simp only [Fin.reduceFinMk, Matrix.cons_val]
    rw [key, inv_inv, hv]
    rfl

include φ in
theorem card_quotient_eq
    (hG : Nat.card G = 42305421312000) :
    Nat.card (Fin 2300) = Nat.card (G ⧸ G₁) := by
  have h1 := G₁.card_mul_index
  rw [Nat.card_congr φ.toEquiv, card_co2P0, hG] at h1
  rw [Nat.card_fin]
  change 2300 = G₁.index
  omega

theorem transport_facts (Θ : Fin 2300 ≃ G ⧸ G₁) (hΘ0 : Θ 0 = ((1 : G) : G ⧸ G₁))
    (hΘ : ∀ (k : G₁) (y : Fin 2300), Θ (φ k • y) = k • Θ y) :
    let ρ : G →* Equiv.Perm (Fin 2300) :=
      Θ.symm.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G (G ⧸ G₁))
    (∀ g y, ρ g y = Θ.symm (g • Θ y)) ∧ Function.Injective ρ ∧
      (∀ x : Fin 2300, ∃ h ∈ ρ.range, h • (0 : Fin 2300) = x) ∧
      ρ.range ⊓ stabilizer (Equiv.Perm (Fin 2300)) (0 : Fin 2300) = co2P0 := by
  intro ρ
  have hρ : ∀ g y, ρ g y = Θ.symm (g • Θ y) := fun _ _ => rfl
  have hρk : ∀ k : G₁, ρ k = (φ k : Equiv.Perm (Fin 2300)) := by
    intro k
    ext y
    rw [hρ, ← Subgroup.smul_def, ← hΘ, Equiv.symm_apply_apply]
    rfl
  have hfix : ∀ g, ρ g 0 = 0 ↔ g ∈ G₁ := by
    intro g
    rw [hρ, Equiv.symm_apply_eq, hΘ0, Quotient.smul_coe, smul_eq_mul, mul_one, QuotientGroup.eq,
      mul_one, G₁.inv_mem_iff]
  refine ⟨hρ, ?_, ?_, ?_⟩
  · refine (injective_iff_map_eq_one ρ).2 fun g hg => ?_
    have hg1 : g ∈ G₁ := (hfix g).1 (by rw [hg]; rfl)
    have h2 : (φ ⟨g, hg1⟩ : Equiv.Perm (Fin 2300)) = 1 := by rw [← hρk]; exact hg
    have h3 : φ ⟨g, hg1⟩ = 1 := Subtype.ext h2
    have h4 : (⟨g, hg1⟩ : G₁) = 1 := by rwa [map_eq_one_iff φ φ.injective] at h3
    exact congrArg Subtype.val h4
  · intro x
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (Θ x)
    refine ⟨ρ g, ⟨g, rfl⟩, ?_⟩
    rw [Equiv.Perm.smul_def, hρ, hΘ0, Quotient.smul_coe, smul_eq_mul, mul_one, hg,
      Equiv.symm_apply_apply]
  · ext σ
    rw [Subgroup.mem_inf, mem_stabilizer_iff, Equiv.Perm.smul_def]
    constructor
    · rintro ⟨⟨g, rfl⟩, h0⟩
      have hg1 := (hfix g).1 h0
      rw [show g = ((⟨g, hg1⟩ : G₁) : G) from rfl, hρk]
      exact (φ ⟨g, hg1⟩).2
    · intro hp
      refine ⟨⟨φ.symm ⟨σ, hp⟩, ?_⟩, mem_stabilizer_iff.1 hp.2⟩
      rw [hρk, MulEquiv.apply_symm_apply]

theorem nonempty_mulEquiv_co2
    (hG : Nat.card G = 42305421312000)
    (hu : ∀ h : G₁, u * h * u⁻¹ ∈ G₁ ↔ (φ h : Equiv.Perm (Fin 2300)) 3 = 3)
    (hv : ∀ h : G₁, v * h * v⁻¹ ∈ G₁ ↔ (φ h : Equiv.Perm (Fin 2300)) 1 = 1) :
    Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.Co2) := by
  have : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; norm_num)
  obtain ⟨Θ, hΘz, hΘ⟩ := exists_equiv_of_stabilizers φ co2Reps (cosetReps G₁ u v) co2Reps_cover
    co2Reps_len (cosetReps_stab φ hu hv) (card_quotient_eq φ hG)
  obtain ⟨-, hinj, htr, hstab⟩ := transport_facts φ Θ (hΘz 0) hΘ
  exact ⟨(MonoidHom.ofInjective hinj).trans ((MulEquiv.subgroupCongr
    (eq_co2P_of_stabilizer htr hstab)).trans co2PermEquiv.symm)⟩

theorem exists_not_mem_of_not_mem_normalizer [Finite G₁] {w : G}
    (hw : w ∉ Subgroup.normalizer (G₁ : Set G)) :
    ∃ h : G₁, w * h * w⁻¹ ∉ G₁ := by
  by_contra hall
  push Not at hall
  apply hw
  let c : G₁ → G₁ := fun h => ⟨w * h * w⁻¹, hall h⟩
  have hc : Function.Injective c := fun a b hab => by
    have := congrArg Subtype.val hab
    simp only [c, mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  have hs := Finite.injective_iff_surjective.1 hc
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hall ⟨x, hx⟩, fun hx => ?_⟩
  obtain ⟨h, hh⟩ := hs ⟨w * x * w⁻¹, hx⟩
  have := congrArg Subtype.val hh
  simp only [c, mul_left_inj, mul_right_inj] at this
  rw [← this]
  exact h.2

include φ in
theorem stab_iff_of_maximal {x : Fin 2300} {w : G}
    (hmax : ∀ K : Subgroup (Equiv.Perm (Fin 2300)),
      co2P0 ⊓ stabilizer (Equiv.Perm (Fin 2300)) x ≤ K → K ≤ co2P0 →
        K = co2P0 ⊓ stabilizer (Equiv.Perm (Fin 2300)) x ∨ K = co2P0)
    (hw : ∀ h : G₁, (φ h : Equiv.Perm (Fin 2300)) x = x → w * h * w⁻¹ ∈ G₁)
    (hwn : ∃ h : G₁, w * h * w⁻¹ ∉ G₁) (h : G₁) :
    w * h * w⁻¹ ∈ G₁ ↔ (φ h : Equiv.Perm (Fin 2300)) x = x := by
  let K : Subgroup (Equiv.Perm (Fin 2300)) :=
    ((G₁.comap (MulAut.conj w).toMonoidHom).subgroupOf G₁).map (co2P0.subtype.comp φ.toMonoidHom)
  have hmemK : ∀ k : G₁, (φ k : Equiv.Perm (Fin 2300)) ∈ K ↔ w * k * w⁻¹ ∈ G₁ := by
    intro k
    constructor
    · rintro ⟨k', hk', he⟩
      have : k' = k := φ.injective (Subtype.ext he)
      subst this
      simpa [Subgroup.mem_subgroupOf, MulAut.conj_apply] using hk'
    · intro hk
      exact ⟨k, by simpa [Subgroup.mem_subgroupOf, MulAut.conj_apply] using hk, rfl⟩
  have hK1 : co2P0 ⊓ stabilizer (Equiv.Perm (Fin 2300)) x ≤ K := by
    intro p hp
    have e : (φ (φ.symm ⟨p, hp.1⟩) : Equiv.Perm (Fin 2300)) = p := by
      rw [MulEquiv.apply_symm_apply]
    rw [← e, hmemK]
    exact hw _ (by rw [e]; exact mem_stabilizer_iff.1 hp.2)
  have hK2 : K ≤ co2P0 := by
    rintro _ ⟨k, -, rfl⟩
    exact (φ k).2
  rcases hmax K hK1 hK2 with hK | hK
  · rw [← hmemK, hK]
    exact ⟨fun h' => mem_stabilizer_iff.1 h'.2, fun h' => ⟨(φ h).2, mem_stabilizer_iff.2 h'⟩⟩
  · exfalso
    obtain ⟨k, hk⟩ := hwn
    exact hk ((hmemK k).1 (by rw [hK]; exact (φ k).2))

theorem nonempty_mulEquiv_co2_of_le
    (hG : Nat.card G = 42305421312000)
    (hu : ∀ h : G₁, (φ h : Equiv.Perm (Fin 2300)) 3 = 3 → u * h * u⁻¹ ∈ G₁)
    (hun : u ∉ Subgroup.normalizer (G₁ : Set G))
    (hv : ∀ h : G₁, (φ h : Equiv.Perm (Fin 2300)) 1 = 1 → v * h * v⁻¹ ∈ G₁)
    (hvn : v ∉ Subgroup.normalizer (G₁ : Set G)) :
    Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.Co2) :=
  have : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; norm_num)
  nonempty_mulEquiv_co2 φ hG
    (stab_iff_of_maximal φ (fun _ h1 h2 => co2P03_maximal h1 h2) hu
      (exists_not_mem_of_not_mem_normalizer hun))
    (stab_iff_of_maximal φ (fun _ h1 h2 => co2P01_maximal h1 h2) hv
      (exists_not_mem_of_not_mem_normalizer hvn))

end Recognition

end CFSG.Sporadic.Co2Rank3

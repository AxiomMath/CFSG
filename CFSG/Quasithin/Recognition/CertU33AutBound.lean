module

public import CFSG.Quasithin.Recognition.CertU33AutCover
public import CFSG.Quasithin.Recognition.CertU33DcPG
public import CFSG.Quasithin.Recognition.CertU33Psu

public section

namespace CFSG.Quasithin

open scoped Pointwise
open CFSG.Sporadic.Bridge

@[expose] def permL (σ : Equiv.Perm (Fin 28)) : List ℕ := List.ofFn fun i : Fin 28 => (σ i : ℕ)

theorem repL_permL (σ : Equiv.Perm (Fin 28)) : RepL (permL σ) σ := by
  have hlen : (permL σ).length = 28 := by simp only [permL, List.length_ofFn]
  refine ⟨hlen, fun i => ?_⟩
  have hi : (i : ℕ) < (permL σ).length := by rw [hlen]; exact i.2
  rw [List.getD_eq_getElem _ _ hi]
  simp only [permL, List.getElem_ofFn]

theorem permL_eq_iff {σ τ : Equiv.Perm (Fin 28)} : permL σ = permL τ ↔ σ = τ :=
  ⟨fun h => eq_of_repL (repL_permL σ) (h ▸ repL_permL τ), fun h => h ▸ rfl⟩

theorem compL_permL (σ τ : Equiv.Perm (Fin 28)) : compL (permL σ) (permL τ) = permL (σ * τ) :=
  repL_unique (repL_mul (repL_permL σ) (repL_permL τ)) (repL_permL _)

theorem autId_eq : autId = permL 1 := repL_unique (repL_one 28) (repL_permL 1)

theorem autPow_permL (σ : Equiv.Perm (Fin 28)) (n : ℕ) : autPow (permL σ) n = permL (σ ^ n) :=
  repL_unique (repL_pow (repL_permL σ) n) (repL_permL _)

theorem autRelT_permL {σa σb σs : Equiv.Perm (Fin 28)} :
    autRelT (permL σa) (permL σb) (permL σs) = true ↔
      (σa ^ 4 = 1 ∧ σb ^ 4 = 1 ∧ σs ^ 2 = 1 ∧ σa * σb = σb * σa ∧ σs * σa * σs = σb ∧
        σs * σb * σs = σa) := by
  simp only [autRelT, autPow_permL, autId_eq, compL_permL, Bool.and_eq_true, beq_iff_eq,
    permL_eq_iff, and_assoc]

theorem autRelX_permL {σa σb σs σx : Equiv.Perm (Fin 28)} :
    autRelX (permL σa) (permL σb) (permL σs) (permL σx) = true ↔
      (σx ^ 3 = 1 ∧ σa * σx = σx * σb ∧ σb * σx * σb * σa = σx ∧ (σx * σs) ^ 2 = 1) := by
  simp only [autRelX, autPow_permL, autId_eq, compL_permL, Bool.and_eq_true, beq_iff_eq,
    permL_eq_iff, and_assoc]

theorem autRelY_permL {σa σb σs σy : Equiv.Perm (Fin 28)} :
    autRelY (permL σa) (permL σb) (permL σs) (permL σy) = true ↔
      (σy ^ 3 = 1 ∧ σa * σb * σs * σy * σs * σa * σa = σy ∧
        σs * σa * σa * σy * σb = σy * σa ∧ σs * σy * σs * σa * σy = σa) := by
  simp only [autRelY, autPow_permL, autId_eq, compL_permL, Bool.and_eq_true, beq_iff_eq,
    permL_eq_iff, and_assoc]

theorem u33_genTab_eq
    (k : ℕ) (hk : k < 5) : u33GenTab.getD k [] = permL (u33GenP k) :=
  repL_unique (u33_genTab_rep k hk) (repL_permL _)

theorem u33_relsT_L :
    autRelT (u33GenTab.getD 0 []) (u33GenTab.getD 1 []) (u33GenTab.getD 2 []) = true := by
  decide +kernel

theorem u33_relsX_L :
    autRelX (u33GenTab.getD 0 []) (u33GenTab.getD 1 []) (u33GenTab.getD 2 [])
      (u33GenTab.getD 3 []) = true := by
  decide +kernel

theorem u33_relsY_L :
    autRelY (u33GenTab.getD 0 []) (u33GenTab.getD 1 []) (u33GenTab.getD 2 [])
      (u33GenTab.getD 4 []) = true := by
  decide +kernel

theorem u33P_rels :
    (u33GenP 0 ^ 4 = 1 ∧ u33GenP 1 ^ 4 = 1 ∧ u33GenP 2 ^ 2 = 1 ∧
      u33GenP 0 * u33GenP 1 = u33GenP 1 * u33GenP 0 ∧
      u33GenP 2 * u33GenP 0 * u33GenP 2 = u33GenP 1 ∧
      u33GenP 2 * u33GenP 1 * u33GenP 2 = u33GenP 0) ∧
    (u33GenP 3 ^ 3 = 1 ∧ u33GenP 0 * u33GenP 3 = u33GenP 3 * u33GenP 1 ∧
      u33GenP 1 * u33GenP 3 * u33GenP 1 * u33GenP 0 = u33GenP 3 ∧
      (u33GenP 3 * u33GenP 2) ^ 2 = 1) ∧
    (u33GenP 4 ^ 3 = 1 ∧
      u33GenP 0 * u33GenP 1 * u33GenP 2 * u33GenP 4 * u33GenP 2 * u33GenP 0 * u33GenP 0 =
        u33GenP 4 ∧
      u33GenP 2 * u33GenP 0 * u33GenP 0 * u33GenP 4 * u33GenP 1 = u33GenP 4 * u33GenP 0 ∧
      u33GenP 2 * u33GenP 4 * u33GenP 2 * u33GenP 0 * u33GenP 4 = u33GenP 0) := by
  refine ⟨autRelT_permL.1 ?_, autRelX_permL.1 ?_, autRelY_permL.1 ?_⟩
  · rw [← u33_genTab_eq 0 (by norm_num), ← u33_genTab_eq 1 (by norm_num),
      ← u33_genTab_eq 2 (by norm_num)]
    exact u33_relsT_L
  · rw [← u33_genTab_eq 0 (by norm_num), ← u33_genTab_eq 1 (by norm_num),
      ← u33_genTab_eq 2 (by norm_num), ← u33_genTab_eq 3 (by norm_num)]
    exact u33_relsX_L
  · rw [← u33_genTab_eq 0 (by norm_num), ← u33_genTab_eq 1 (by norm_num),
      ← u33_genTab_eq 2 (by norm_num), ← u33_genTab_eq 4 (by norm_num)]
    exact u33_relsY_L


theorem u33G_rels_map
    {M : Type*} [Group M] (ψ : U33G →* M) :
    (ψ (u33GenPG 0) ^ 4 = 1 ∧ ψ (u33GenPG 1) ^ 4 = 1 ∧ ψ (u33GenPG 2) ^ 2 = 1 ∧
      ψ (u33GenPG 0) * ψ (u33GenPG 1) = ψ (u33GenPG 1) * ψ (u33GenPG 0) ∧
      ψ (u33GenPG 2) * ψ (u33GenPG 0) * ψ (u33GenPG 2) = ψ (u33GenPG 1) ∧
      ψ (u33GenPG 2) * ψ (u33GenPG 1) * ψ (u33GenPG 2) = ψ (u33GenPG 0)) ∧
    (ψ (u33GenPG 3) ^ 3 = 1 ∧ ψ (u33GenPG 0) * ψ (u33GenPG 3) = ψ (u33GenPG 3) * ψ (u33GenPG 1) ∧
      ψ (u33GenPG 1) * ψ (u33GenPG 3) * ψ (u33GenPG 1) * ψ (u33GenPG 0) = ψ (u33GenPG 3) ∧
      (ψ (u33GenPG 3) * ψ (u33GenPG 2)) ^ 2 = 1) ∧
    (ψ (u33GenPG 4) ^ 3 = 1 ∧
      ψ (u33GenPG 0) * ψ (u33GenPG 1) * ψ (u33GenPG 2) * ψ (u33GenPG 4) * ψ (u33GenPG 2) *
        ψ (u33GenPG 0) * ψ (u33GenPG 0) = ψ (u33GenPG 4) ∧
      ψ (u33GenPG 2) * ψ (u33GenPG 0) * ψ (u33GenPG 0) * ψ (u33GenPG 4) * ψ (u33GenPG 1) =
        ψ (u33GenPG 4) * ψ (u33GenPG 0) ∧
      ψ (u33GenPG 2) * ψ (u33GenPG 4) * ψ (u33GenPG 2) * ψ (u33GenPG 0) * ψ (u33GenPG 4) =
        ψ (u33GenPG 0)) := by
  obtain ⟨⟨a1, a2, a3, a4, a5, a6⟩, ⟨b1, b2, b3, b4⟩, ⟨c1, c2, c3, c4⟩⟩ := u33P_rels
  have inj := u33PresHom_injective
  have e : ∀ k, u33PresHom (u33GenPG k) = u33GenP k := u33PresHom_genPG
  have g1 : u33GenPG 0 ^ 4 = 1 := inj (by rw [map_pow, e, map_one]; exact a1)
  have g2 : u33GenPG 1 ^ 4 = 1 := inj (by rw [map_pow, e, map_one]; exact a2)
  have g3 : u33GenPG 2 ^ 2 = 1 := inj (by rw [map_pow, e, map_one]; exact a3)
  have g4 : u33GenPG 0 * u33GenPG 1 = u33GenPG 1 * u33GenPG 0 :=
    inj (by simp only [map_mul, e]; exact a4)
  have g5 : u33GenPG 2 * u33GenPG 0 * u33GenPG 2 = u33GenPG 1 :=
    inj (by simp only [map_mul, e]; exact a5)
  have g6 : u33GenPG 2 * u33GenPG 1 * u33GenPG 2 = u33GenPG 0 :=
    inj (by simp only [map_mul, e]; exact a6)
  have h1 : u33GenPG 3 ^ 3 = 1 := inj (by rw [map_pow, e, map_one]; exact b1)
  have h2 : u33GenPG 0 * u33GenPG 3 = u33GenPG 3 * u33GenPG 1 :=
    inj (by simp only [map_mul, e]; exact b2)
  have h3 : u33GenPG 1 * u33GenPG 3 * u33GenPG 1 * u33GenPG 0 = u33GenPG 3 :=
    inj (by simp only [map_mul, e]; exact b3)
  have h4 : (u33GenPG 3 * u33GenPG 2) ^ 2 = 1 :=
    inj (by simp only [map_pow, map_mul, map_one, e]; exact b4)
  have k1 : u33GenPG 4 ^ 3 = 1 := inj (by rw [map_pow, e, map_one]; exact c1)
  have k2 : u33GenPG 0 * u33GenPG 1 * u33GenPG 2 * u33GenPG 4 * u33GenPG 2 * u33GenPG 0 *
      u33GenPG 0 = u33GenPG 4 := inj (by simp only [map_mul, e]; exact c2)
  have k3 : u33GenPG 2 * u33GenPG 0 * u33GenPG 0 * u33GenPG 4 * u33GenPG 1 =
      u33GenPG 4 * u33GenPG 0 := inj (by simp only [map_mul, e]; exact c3)
  have k4 : u33GenPG 2 * u33GenPG 4 * u33GenPG 2 * u33GenPG 0 * u33GenPG 4 = u33GenPG 0 :=
    inj (by simp only [map_mul, e]; exact c4)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · simpa [map_pow] using congrArg ψ g1
  · simpa [map_pow] using congrArg ψ g2
  · simpa [map_pow] using congrArg ψ g3
  · simpa [map_mul] using congrArg ψ g4
  · simpa [map_mul] using congrArg ψ g5
  · simpa [map_mul] using congrArg ψ g6
  · simpa [map_pow] using congrArg ψ h1
  · simpa [map_mul] using congrArg ψ h2
  · simpa [map_mul] using congrArg ψ h3
  · simpa [map_pow, map_mul] using congrArg ψ h4
  · simpa [map_pow] using congrArg ψ k1
  · simpa [map_mul] using congrArg ψ k2
  · simpa [map_mul] using congrArg ψ k3
  · simpa [map_mul] using congrArg ψ k4


@[expose] noncomputable def u33SylowT
    : Sylow 2 U33G := u33_syl.1.toSylow u33_syl.2

theorem coe_u33SylowT
    : (u33SylowT : Subgroup U33G) = u33Data.T := rfl

theorem map_T_of_mem_stabilizer
    {φ : MulAut U33G}
    (hφ : φ ∈ MulAction.stabilizer (MulAut U33G) u33SylowT) :
    Subgroup.map φ.toMonoidHom u33Data.T = u33Data.T := by
  have h : φ • (u33SylowT : Subgroup U33G) = u33SylowT := by
    rw [← Sylow.pointwise_smul_def]
    exact congrArg (fun Q : Sylow 2 U33G => (Q : Subgroup U33G)) hφ
  rw [coe_u33SylowT] at h
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    have := Subgroup.smul_mem_pointwise_smul t φ u33Data.T ht
    rw [h] at this
    exact this
  · intro hz
    rw [← h] at hz
    obtain ⟨t, ht, htz⟩ := (Subgroup.mem_smul_pointwise_iff_exists z φ u33Data.T).1 hz
    exact ⟨t, ht, htz⟩

theorem map_overgroup_of_map_T
    {φ : MulAut U33G}
    (hT : Subgroup.map φ.toMonoidHom u33Data.T = u33Data.T) (X : Subgroup U33G)
    (hX1 : u33Data.T ≤ X) (hX2 : u33Data.T ≠ X) (hX3 : X ≠ ⊤) :
    Subgroup.map φ.toMonoidHom X = u33Data.A ∨ Subgroup.map φ.toMonoidHom X = u33Data.B := by
  have : Finite U33G := u33Pres_finite_card_le.1
  have hle : u33Data.T ≤ Subgroup.map φ.toMonoidHom X := by
    rw [← hT]
    exact Subgroup.map_mono hX1
  have hc : Nat.card (Subgroup.map φ.toMonoidHom X) = Nat.card X :=
    Subgroup.card_map_of_injective φ.injective
  rcases u33Data.lattice _ hle with h | h | h | h
  · exfalso
    rw [h] at hc
    exact hX2 (Subgroup.eq_of_le_of_card_ge hX1 hc.symm.le)
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    rw [h, Subgroup.card_top] at hc
    exact hX3 (Subgroup.eq_top_of_card_eq X hc.symm)

theorem u33A_ne_top
    : u33Data.A ≠ ⊤ := by
  intro h
  have := u33Data.inf_AB
  rw [h, top_inf_eq] at this
  exact u33Data.T_ne_B this.symm

theorem u33B_ne_top
    : u33Data.B ≠ ⊤ := by
  intro h
  have := u33Data.inf_AB
  rw [h, inf_top_eq] at this
  exact u33Data.T_ne_A this.symm

theorem map_mem_AB_of_map_T
    {φ : MulAut U33G}
    (hT : Subgroup.map φ.toMonoidHom u33Data.T = u33Data.T) {z : U33G}
    (hz : z ∈ u33Data.A ∨ z ∈ u33Data.B) : φ z ∈ u33Data.A ∨ φ z ∈ u33Data.B := by
  rcases hz with hz | hz
  · have h := map_overgroup_of_map_T hT u33Data.A u33Data.T_le_A u33Data.T_ne_A u33A_ne_top
    have hm : φ z ∈ Subgroup.map φ.toMonoidHom u33Data.A := ⟨z, hz, rfl⟩
    rcases h with h | h
    · rw [h] at hm; exact Or.inl hm
    · rw [h] at hm; exact Or.inr hm
  · have h := map_overgroup_of_map_T hT u33Data.B u33Data.T_le_B u33Data.T_ne_B u33B_ne_top
    have hm : φ z ∈ Subgroup.map φ.toMonoidHom u33Data.B := ⟨z, hz, rfl⟩
    rcases h with h | h
    · rw [h] at hm; exact Or.inl hm
    · rw [h] at hm; exact Or.inr hm

theorem permL_Tel
    (i : Fin 32) :
    permL (u33PresHom (u33Data.Tel i)) = u33TelTab.getD i [] := by
  refine repL_unique (repL_permL _) ?_
  have := u33_telTab_rep i i.2
  rwa [← u33Tel_hom] at this

theorem permL_double_coset
    (i₁ i₂ : Fin 32) (j : Fin 14) :
    permL (u33PresHom (u33Data.Tel i₁ * u33Data.D j * u33Data.Tel i₂)) =
      compL (compL (u33TelTab.getD i₁ []) (u33DTab.getD j [])) (u33TelTab.getD i₂ []) := by
  refine repL_unique (repL_permL _) ?_
  have := repL_mul (repL_mul (u33_telTab_rep i₁ i₁.2) (u33_dTab_rep j j.2))
    (u33_telTab_rep i₂ i₂.2)
  rw [map_mul, map_mul]
  have h1 : u33PresHom (u33Data.Tel i₁) = u33Tel u33GenP i₁ := u33Tel_hom i₁
  have h2 : u33PresHom (u33Data.D j) = u33D u33GenP j := u33D_hom j
  have h3 : u33PresHom (u33Data.Tel i₂) = u33Tel u33GenP i₂ := u33Tel_hom i₂
  rw [h1, h2, h3]
  exact this

theorem u33ABTab_length : u33ABTab.length = 160 := by decide +kernel

theorem exists_index_AB
    {z : U33G} (hz : z ∈ u33Data.A ∨ z ∈ u33Data.B) :
    ∃ ix < 160, permL (u33PresHom z) = u33ABTab.getD ix [] := by
  have key : ∀ (j : Fin 14), (j : ℕ) ∈ [0, 1, 2] → ∀ i₁ i₂ : Fin 32,
      ∃ ix < 160, permL (u33PresHom (u33Data.Tel i₁ * u33Data.D j * u33Data.Tel i₂)) =
        u33ABTab.getD ix [] := by
    intro j hj i₁ i₂
    have hmem := u33_ab_cover j hj i₁ i₁.2 i₂ i₂.2
    obtain ⟨ix, hix, h⟩ := List.mem_iff_getElem.1 hmem
    refine ⟨ix, by rwa [u33ABTab_length] at hix, ?_⟩
    rw [permL_double_coset, List.getD_eq_getElem _ _ hix, h]
  rcases hz with hz | hz
  · obtain ⟨j, hj, i₁, i₂, rfl⟩ := (u33Data.mem_A_iff z).1 hz
    refine key j ?_ i₁ i₂
    rcases hj with rfl | rfl <;> simp [u33Data]
  · obtain ⟨j, hj, i₁, i₂, rfl⟩ := (u33Data.mem_B_iff z).1 hz
    refine key j ?_ i₁ i₂
    rcases hj with rfl | rfl <;> simp [u33Data]

@[expose] noncomputable def u33AutTup (φ : MulAut U33G) : List ℕ × List ℕ × List ℕ × List ℕ × List ℕ :=
  (permL (u33PresHom (φ (u33GenPG 0))), permL (u33PresHom (φ (u33GenPG 1))),
    permL (u33PresHom (φ (u33GenPG 2))), permL (u33PresHom (φ (u33GenPG 3))),
    permL (u33PresHom (φ (u33GenPG 4))))

@[expose] def u33AutLists (idx : ℕ × ℕ × ℕ × ℕ × ℕ) :
    List ℕ × List ℕ × List ℕ × List ℕ × List ℕ :=
  (u33TelTab.getD idx.1 [], u33TelTab.getD idx.2.1 [], u33TelTab.getD idx.2.2.1 [],
    u33ABTab.getD idx.2.2.2.1 [], u33ABTab.getD idx.2.2.2.2 [])

theorem u33AutTup_injective
    {φ ψ : MulAut U33G} (h : u33AutTup φ = u33AutTup ψ) : φ = ψ := by
  simp only [u33AutTup, Prod.mk.injEq, permL_eq_iff] at h
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  have hgen : ∀ g ∈ ({u33GenPG 0, u33GenPG 1, u33GenPG 2, u33GenPG 3, u33GenPG 4} : Set U33G),
      φ g = ψ g := by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    exacts [u33PresHom_injective h0, u33PresHom_injective h1, u33PresHom_injective h2,
      u33PresHom_injective h3, u33PresHom_injective h4]
  ext x
  have hx : x ∈ Subgroup.closure
      ({u33GenPG 0, u33GenPG 1, u33GenPG 2, u33GenPG 3, u33GenPG 4} : Set U33G) := by
    rw [u33_gen]; trivial
  exact MonoidHom.eqOn_closure (f := φ.toMonoidHom) (g := ψ.toMonoidHom) hgen hx

theorem mem_u33AutEnum {ia ib is ix iy : ℕ} (ha : ia < 32) (hb : ib < 32) (hs : is < 32)
    (hx : ix < 160) (hy : iy < 160)
    (h1 : (autPow (u33TelTab.getD ia []) 4 == autId && u33TelTab.getD ia [] != autId) = true)
    (h2 : (autPow (u33TelTab.getD ib []) 4 == autId &&
      compL (u33TelTab.getD ia []) (u33TelTab.getD ib []) ==
        compL (u33TelTab.getD ib []) (u33TelTab.getD ia [])) = true)
    (h3 : autRelT (u33TelTab.getD ia []) (u33TelTab.getD ib []) (u33TelTab.getD is []) = true)
    (h4 : autRelX (u33TelTab.getD ia []) (u33TelTab.getD ib []) (u33TelTab.getD is [])
      (u33ABTab.getD ix []) = true)
    (h5 : autRelY (u33TelTab.getD ia []) (u33TelTab.getD ib []) (u33TelTab.getD is [])
      (u33ABTab.getD iy []) = true) :
    (ia, ib, is, ix, iy) ∈ u33AutEnum := by
  unfold u33AutEnum
  simp only [List.mem_flatMap, List.mem_range]
  refine ⟨ia, ha, ?_⟩
  rw [ite_eq_left h1]
  simp only [List.mem_flatMap, List.mem_range]
  refine ⟨ib, hb, ?_⟩
  rw [ite_eq_left h2]
  simp only [List.mem_flatMap, List.mem_range]
  refine ⟨is, hs, ?_⟩
  rw [ite_eq_left h3]
  simp only [List.mem_flatMap, List.mem_range]
  refine ⟨ix, hx, ?_⟩
  rw [ite_eq_left h4]
  simp only [List.mem_flatMap, List.mem_range]
  refine ⟨iy, hy, ?_⟩
  rw [ite_eq_left h5]
  simp

theorem bool_rel_a {σa : Equiv.Perm (Fin 28)} (h : σa ^ 4 = 1) (hne : σa ≠ 1) :
    (autPow (permL σa) 4 == autId && permL σa != autId) = true := by
  simp [autPow_permL, autId_eq, permL_eq_iff, h, hne]

theorem bool_rel_b {σa σb : Equiv.Perm (Fin 28)} (h : σb ^ 4 = 1) (hc : σa * σb = σb * σa) :
    (autPow (permL σb) 4 == autId &&
      compL (permL σa) (permL σb) == compL (permL σb) (permL σa)) = true := by
  simp [autPow_permL, autId_eq, compL_permL, h, hc]

theorem u33AutTup_mem
    {φ : MulAut U33G}
    (hφ : φ ∈ MulAction.stabilizer (MulAut U33G) u33SylowT) :
    ∃ idx ∈ u33AutEnum, u33AutLists idx = u33AutTup φ := by
  have hT := map_T_of_mem_stabilizer hφ
  have hmemT : ∀ t ∈ u33Data.T, φ t ∈ u33Data.T := fun t ht => by
    rw [← hT]
    exact ⟨t, ht, rfl⟩
  have tel : ∀ k < 3, ∃ i < 32, permL (u33PresHom (φ (u33GenPG k))) = u33TelTab.getD i [] := by
    intro k hk
    have hk' : u33GenPG k ∈ u33Data.T := by
      interval_cases k
      · exact u33Data.a_mem_T
      · exact u33Data.b_mem_T
      · exact u33Data.s_mem_T
    obtain ⟨i, hi⟩ := (u33Data.mem_T_iff _).1 (hmemT _ hk')
    exact ⟨i, i.2, by rw [← hi, permL_Tel]⟩
  obtain ⟨ia, hia, ha⟩ := tel 0 (by norm_num)
  obtain ⟨ib, hib, hb⟩ := tel 1 (by norm_num)
  obtain ⟨is, his, hs⟩ := tel 2 (by norm_num)
  obtain ⟨ix, hix, hx⟩ := exists_index_AB (map_mem_AB_of_map_T hT (Or.inl u33Data.x_mem_A))
  obtain ⟨iy, hiy, hy⟩ := exists_index_AB (map_mem_AB_of_map_T hT (Or.inr u33Data.y_mem_B))
  have R := u33G_rels_map (u33PresHom.comp φ.toMonoidHom)
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at R
  obtain ⟨⟨r1, r2, r3, r4, r5, r6⟩, ⟨r7, r8, r9, r10⟩, ⟨r11, r12, r13, r14⟩⟩ := R
  have hne : u33PresHom (φ (u33GenPG 0)) ≠ 1 := by
    intro h
    have h1 : φ (u33GenPG 0) = 1 := u33PresHom_injective (by rw [h, map_one])
    have h2 : u33GenPG 0 = 1 := φ.injective (by rw [h1, map_one])
    exact u33Extra.a_ne_one h2
  refine ⟨(ia, ib, is, ix, iy), ?_, ?_⟩
  · refine mem_u33AutEnum hia hib his hix hiy ?_ ?_ ?_ ?_ ?_
    · rw [← ha]; exact bool_rel_a r1 hne
    · rw [← ha, ← hb]; exact bool_rel_b r2 r4
    · rw [← ha, ← hb, ← hs]; exact autRelT_permL.2 ⟨r1, r2, r3, r4, r5, r6⟩
    · rw [← ha, ← hb, ← hs, ← hx]; exact autRelX_permL.2 ⟨r7, r8, r9, r10⟩
    · rw [← ha, ← hb, ← hs, ← hy]; exact autRelY_permL.2 ⟨r11, r12, r13, r14⟩
  · simp only [u33AutLists, u33AutTup, ← ha, ← hb, ← hs, ← hx, ← hy]
    rfl

theorem card_stabilizer_u33SylowT_le :
    Nat.card (MulAction.stabilizer (MulAut U33G) u33SylowT) ≤ 64 := by
  classical
  let V : Finset (List ℕ × List ℕ × List ℕ × List ℕ × List ℕ) :=
    (u33AutEnum.map u33AutLists).toFinset
  have hV : V.card ≤ 64 := by
    calc V.card ≤ (u33AutEnum.map u33AutLists).length := List.toFinset_card_le _
      _ = 64 := by rw [List.length_map, u33AutEnum_length]
  let f : MulAction.stabilizer (MulAut U33G) u33SylowT → V := fun φ => ⟨u33AutTup φ, by
    obtain ⟨idx, hidx, h⟩ := u33AutTup_mem φ.2
    simp only [V, List.mem_toFinset, List.mem_map]
    exact ⟨idx, hidx, h⟩⟩
  have hf : Function.Injective f := by
    intro φ ψ h
    exact Subtype.ext (u33AutTup_injective (congrArg Subtype.val h))
  calc Nat.card (MulAction.stabilizer (MulAut U33G) u33SylowT) ≤ Nat.card V :=
        Nat.card_le_card_of_injective f hf
    _ = V.card := by simp
    _ ≤ 64 := hV

theorem card_sylow_u33
    : Nat.card (Sylow 2 U33G) = 189 := by
  have : Finite U33G := u33Pres_finite_card_le.1
  have h1 : Nat.card (Sylow 2 U33G) =
      (Subgroup.normalizer ((u33SylowT : Subgroup U33G) : Set U33G)).index :=
    Sylow.card_eq_index_normalizer u33SylowT
  have h2 : Subgroup.normalizer ((u33SylowT : Subgroup U33G) : Set U33G) = u33Data.T :=
    u33Extra.normalizer_T
  rw [h2] at h1
  have h3 := Subgroup.card_mul_index u33Data.T
  rw [u33_card_T, card_u33Pres] at h3
  omega

theorem card_mulAut_u33Pres_le
    : Nat.card (MulAut U33G) ≤ 12096 := by
  have : Finite U33G := u33Pres_finite_card_le.1
  have h1 := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (MulAut U33G) u33SylowT)
  rw [Nat.card_prod] at h1
  have h2 : Nat.card (MulAction.orbit (MulAut U33G) u33SylowT) ≤ 189 := by
    calc Nat.card (MulAction.orbit (MulAut U33G) u33SylowT) ≤ Nat.card (Sylow 2 U33G) :=
          Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
      _ = 189 := card_sylow_u33
  calc Nat.card (MulAut U33G)
      = Nat.card (MulAction.orbit (MulAut U33G) u33SylowT) *
          Nat.card (MulAction.stabilizer (MulAut U33G) u33SylowT) := h1.symm
    _ ≤ 189 * 64 := Nat.mul_le_mul h2 card_stabilizer_u33SylowT_le
    _ = 12096 := by norm_num

theorem card_mulAut_psu3_le
    : Nat.card (MulAut (CFSG.Open.PSU3 3 1)) ≤ 12096 := by
  obtain ⟨e⟩ := u33Pres_mulEquiv_PSU3
  rw [← Nat.card_congr (MulAut.congr e).toEquiv]
  exact card_mulAut_u33Pres_le

end CFSG.Quasithin

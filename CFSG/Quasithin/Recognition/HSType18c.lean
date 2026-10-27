module

public import CFSG.Quasithin.Recognition.HSType18b
public import CFSG.Quasithin.Recognition.HSTypeFactM22

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique MulAction
open CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94
open HSSetting

namespace HSCtx

variable {G : Type} [Group G] [Finite G] (C : HSCtx G)

theorem eq_conj_of_map_eq {K Y : Subgroup G} {X : Subgroup M22}
    (hYX : ∀ y : ↥C.J, (y : G) ∈ Y ↔ C.Ψ y ∈ X) (m : M22)
    (h : (K.subgroupOf C.J).map C.Ψ.toMonoidHom = X.map (MulAut.conj m).toMonoidHom)
    (y : ↥C.J) : (y : G) ∈ K ↔ ((C.Ψ.symm m : G)⁻¹ * y * C.Ψ.symm m) ∈ Y := by
  rw [← C.map_mono_iff K y, h, mem_map_conj_iff]
  have hyJ : ((C.Ψ.symm m : G)⁻¹ * y * C.Ψ.symm m) ∈ C.J :=
    C.J.mul_mem (C.J.mul_mem (C.J.inv_mem (C.Ψ.symm m).2) y.2) (C.Ψ.symm m).2
  have e : (⟨_, hyJ⟩ : ↥C.J) = (C.Ψ.symm m)⁻¹ * y * C.Ψ.symm m := rfl
  rw [hYX ⟨_, hyJ⟩, e, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem exists_conj_L
    {K : Subgroup G} (hKJ : K ≤ C.J) (hK : Nat.card K = 20160) :
    ∃ j ∈ C.J, ∀ y ∈ C.J, y ∈ K ↔ j⁻¹ * y * j ∈ C.L := by
  obtain ⟨-, -, -, -, ⟨-, -, -, -, hc22, -, -⟩, -⟩ := m22_point_hexad_actions
  have hidx : ((K.subgroupOf C.J).map C.Ψ.toMonoidHom).index = 22 := by
    rw [Subgroup.index_map_of_bijective C.Ψ.bijective]
    have h1 := (K.subgroupOf C.J).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKJ).toEquiv, hK, C.card_J] at h1
    omega
  obtain ⟨m, hm⟩ := hc22 _ _ index_stab0 hidx
  refine ⟨C.Ψ.symm m, (C.Ψ.symm m).2, fun y hy => ?_⟩
  exact C.eq_conj_of_map_eq (fun y => C.hΨL y) m hm ⟨y, hy⟩

theorem exists_conj_I0
    {K : Subgroup G} (hKJ : K ≤ C.J) (hK : Nat.card K = 5760) :
    ∃ j ∈ C.J, ∀ y ∈ C.J, y ∈ K ↔ j⁻¹ * y * j ∈ C.I0 := by
  obtain ⟨-, -, -, -, ⟨-, -, -, -, -, hc77, -⟩, -⟩ := m22_point_hexad_actions
  have hidx : ((K.subgroupOf C.J).map C.Ψ.toMonoidHom).index = 77 := by
    rw [Subgroup.index_map_of_bijective C.Ψ.bijective]
    have h1 := (K.subgroupOf C.J).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKJ).toEquiv, hK, C.card_J] at h1
    omega
  obtain ⟨m, hm⟩ := hc77 _ _ (C.index_hexStab C.card_I0) hidx
  refine ⟨C.Ψ.symm m, (C.Ψ.symm m).2, fun y hy => ?_⟩
  exact C.eq_conj_of_map_eq (fun y => C.hΨI y) m hm ⟨y, hy⟩

theorem smul_omega_of_mem {g : G} (hg : g ∈ C.J) :
    g • ((1 : G) : G ⧸ C.J) = ((1 : G) : G ⧸ C.J) := by
  rw [← mem_stabilizer_iff, stabilizer_quotient]
  exact hg

theorem smul_mem_of_L_le
    {c : G} (hcN : c ∈ Subgroup.normalizer (C.M.V2 : Set G)) (hcNN : c ∉ C.M.NN)
    (hcL : c ∈ Subgroup.normalizer (C.L : Set G)) {g : G} (h : ∀ k ∈ C.L, g⁻¹ * k * g ∈ C.J) :
    g • ((1 : G) : G ⧸ C.J) = ((1 : G) : G ⧸ C.J) ∨
      g • ((1 : G) : G ⧸ C.J) ∈ orbit (stabilizer G ((1 : G) : G ⧸ C.J))
        (c • ((1 : G) : G ⧸ C.J)) := by
  have hKJ : C.L.map (MulAut.conj g⁻¹).toMonoidHom ≤ C.J := by
    rintro _ ⟨k, hk, rfl⟩
    have := h k hk
    simpa [MulAut.conj_apply] using this
  have hK : Nat.card ↥(C.L.map (MulAut.conj g⁻¹).toMonoidHom) = 20160 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, C.card_L]
  obtain ⟨j, hj, hjK⟩ := C.exists_conj_L hKJ hK
  have hgj : (g * j)⁻¹ ∈ Subgroup.normalizer (C.L : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun k hk => ?_
    have h1 : g⁻¹ * k * g ∈ C.L.map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [mem_map_conj_iff, inv_inv, show g * (g⁻¹ * k * g) * g⁻¹ = k by group]
      exact hk
    have h2 := (hjK _ (h k hk)).mp h1
    rwa [show j⁻¹ * (g⁻¹ * k * g) * j = (g * j)⁻¹ * k * (g * j)⁻¹⁻¹ by group] at h2
  have hgj' : g * j ∈ Subgroup.normalizer (C.L : Set G) := by
    simpa using (Subgroup.normalizer _).inv_mem hgj
  have hjω : j⁻¹ • ((1 : G) : G ⧸ C.J) = ((1 : G) : G ⧸ C.J) :=
    C.smul_omega_of_mem (C.J.inv_mem hj)
  rcases C.normalizer_L_cases hcN hcNN hcL hgj' with hl | hl
  · left
    rw [show g = g * j * j⁻¹ by group, mul_smul, hjω]
    exact C.smul_omega_of_mem (C.L_le_J hl)
  · right
    have hS : g * j * c⁻¹ ∈ stabilizer G ((1 : G) : G ⧸ C.J) := by
      rw [stabilizer_quotient]
      exact C.L_le_J hl
    rw [show g = (g * j * c⁻¹) * c * j⁻¹ by group, mul_smul, mul_smul, hjω]
    exact mem_orbit _ (⟨_, hS⟩ : ↥(stabilizer G ((1 : G) : G ⧸ C.J)))

theorem smul_mem_of_I0_le
    {d : G} (hd : ∀ n ∈ Subgroup.normalizer (C.I0 : Set G), n ∈ C.I0 ∨ n * d⁻¹ ∈ C.I0)
    {g : G} (h : ∀ k ∈ C.I0, g⁻¹ * k * g ∈ C.J) :
    g • ((1 : G) : G ⧸ C.J) = ((1 : G) : G ⧸ C.J) ∨
      g • ((1 : G) : G ⧸ C.J) ∈ orbit (stabilizer G ((1 : G) : G ⧸ C.J))
        (d • ((1 : G) : G ⧸ C.J)) := by
  have hKJ : C.I0.map (MulAut.conj g⁻¹).toMonoidHom ≤ C.J := by
    rintro _ ⟨k, hk, rfl⟩
    have := h k hk
    simpa [MulAut.conj_apply] using this
  have hK : Nat.card ↥(C.I0.map (MulAut.conj g⁻¹).toMonoidHom) = 5760 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, C.card_I0]
  obtain ⟨j, hj, hjK⟩ := C.exists_conj_I0 hKJ hK
  have hgj : (g * j)⁻¹ ∈ Subgroup.normalizer (C.I0 : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun k hk => ?_
    have h1 : g⁻¹ * k * g ∈ C.I0.map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [mem_map_conj_iff, inv_inv, show g * (g⁻¹ * k * g) * g⁻¹ = k by group]
      exact hk
    have h2 := (hjK _ (h k hk)).mp h1
    rwa [show j⁻¹ * (g⁻¹ * k * g) * j = (g * j)⁻¹ * k * (g * j)⁻¹⁻¹ by group] at h2
  have hgj' : g * j ∈ Subgroup.normalizer (C.I0 : Set G) := by
    simpa using (Subgroup.normalizer _).inv_mem hgj
  have hjω : j⁻¹ • ((1 : G) : G ⧸ C.J) = ((1 : G) : G ⧸ C.J) :=
    C.smul_omega_of_mem (C.J.inv_mem hj)
  rcases hd _ hgj' with hl | hl
  · left
    rw [show g = g * j * j⁻¹ by group, mul_smul, hjω]
    exact C.smul_omega_of_mem (C.I0_le_J hl)
  · right
    have hS : g * j * d⁻¹ ∈ stabilizer G ((1 : G) : G ⧸ C.J) := by
      rw [stabilizer_quotient]
      exact C.I0_le_J hl
    rw [show g = (g * j * d⁻¹) * d * j⁻¹ by group, mul_smul, mul_smul, hjω]
    exact mem_orbit _ (⟨_, hS⟩ : ↥(stabilizer G ((1 : G) : G ⧸ C.J)))

theorem card_quot_eq_or_ge
    (hF : FactM22SubgroupIndex) :
    Nat.card (G ⧸ C.J) = 100 ∨ 276 ≤ Nat.card (G ⧸ C.J) := by
  classical
  obtain ⟨c, hcN, hcNN, hc1, hc2⟩ := C.exists_c
  have hcL := C.mem_normalizer_of_swap hc1 hc2
  have hcJ := C.not_mem_normalizer_J hc1 hcL
  obtain ⟨d, hdI, hdJ, hd⟩ := C.exists_d
  have hdJ' : d ∉ Subgroup.normalizer (C.J : Set G) := fun h =>
    hdJ (C.mem_J_of_mem_normalizer hcN hcNN hcL hcJ h)
  set ω : G ⧸ C.J := ((1 : G) : G ⧸ C.J) with hωdef
  have hS : stabilizer G ω = C.J := stabilizer_quotient C.J
  set Δ := orbit (stabilizer G ω) (c • ω) with hΔdef
  set Γ := orbit (stabilizer G ω) (d • ω) with hΓdef
  have hΔ : Δ.ncard = 22 :=
    C.ncard_orbit_eq c (C.inf_conj_c hcL hcJ) (by rw [C.card_L, C.card_J])
  have hΓ : Γ.ncard = 77 :=
    C.ncard_orbit_eq d (C.inf_conj_d hdI hdJ') (by rw [C.card_I0, C.card_J])
  have hω : orbit (stabilizer G ω) ω = {ω} :=
    CFSG.Sporadic.Recognition.HSWales.orbit_stabilizer_self ω
  have hdisj : ∀ x y : G ⧸ C.J, orbit (stabilizer G ω) x ≠ orbit (stabilizer G ω) y →
      Disjoint (orbit (stabilizer G ω) x) (orbit (stabilizer G ω) y) := by
    intro x y hne
    rw [Set.disjoint_left]
    intro p hpx hpy
    apply hne
    rw [← orbit_eq_iff.mpr hpx, ← orbit_eq_iff.mpr hpy]
  have hωΔ : Disjoint ({ω} : Set (G ⧸ C.J)) Δ := by
    rw [← hω]
    refine hdisj _ _ fun he => ?_
    have := congrArg Set.ncard he
    rw [hω, Set.ncard_singleton, ← hΔdef, hΔ] at this
    omega
  have hωΓ : Disjoint ({ω} : Set (G ⧸ C.J)) Γ := by
    rw [← hω]
    refine hdisj _ _ fun he => ?_
    have := congrArg Set.ncard he
    rw [hω, Set.ncard_singleton, ← hΓdef, hΓ] at this
    omega
  have hΔΓ : Disjoint Δ Γ := hdisj _ _ fun he => by
    have := congrArg Set.ncard he
    rw [← hΔdef, ← hΓdef, hΔ, hΓ] at this
    omega
  have hΩc : (({ω} : Set (G ⧸ C.J)) ∪ Δ ∪ Γ).ncard = 100 := by
    rw [Set.ncard_union_eq (Disjoint.union_left hωΓ hΔΓ), Set.ncard_union_eq hωΔ,
      Set.ncard_singleton, hΔ, hΓ]
  by_cases hall : ({ω} : Set (G ⧸ C.J)) ∪ Δ ∪ Γ = Set.univ
  · left
    rw [← Set.ncard_univ, ← hall, hΩc]
  right
  obtain ⟨α, hα⟩ : ∃ α, α ∉ ({ω} : Set (G ⧸ C.J)) ∪ Δ ∪ Γ := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hall (Set.eq_univ_of_forall h)
  obtain ⟨g, rfl⟩ : ∃ g : G, g • ω = α := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective α
    exact ⟨g, by rw [hωdef, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]⟩
  have hgω : g • ω ≠ ω := fun h => hα (Or.inl (Or.inl (Set.mem_singleton_iff.mpr h)))
  have hgΔ : g • ω ∉ Δ := fun h => hα (Or.inl (Or.inr h))
  have hgΓ : g • ω ∉ Γ := fun h => hα (Or.inr h)
  set O := orbit (stabilizer G ω) (g • ω) with hOdef
  have hOdisj : Disjoint (({ω} : Set (G ⧸ C.J)) ∪ Δ ∪ Γ) O := by
    have hgO : g • ω ∈ O := mem_orbit_self _
    refine Disjoint.union_left (Disjoint.union_left ?_ ?_) ?_
    · rw [← hω]
      exact hdisj _ _ fun he => hgω (by rw [← Set.mem_singleton_iff, ← hω, he]; exact hgO)
    · exact hdisj _ _ fun he => hgΔ (by rw [hΔdef, he]; exact hgO)
    · exact hdisj _ _ fun he => hgΓ (by rw [hΓdef, he]; exact hgO)
  have hOc : 176 ≤ O.ncard := by
    set K := C.J ⊓ C.J.map (MulAut.conj g).toMonoidHom with hKdef
    have hKJ : K ≤ C.J := inf_le_left
    have hn : Nat.card K * (K.subgroupOf C.J).index = Nat.card C.J := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKJ).toEquiv]
      exact (K.subgroupOf C.J).card_mul_index
    rw [C.ncard_orbit_eq g rfl hn]
    by_contra hlt
    have hidx : ((K.subgroupOf C.J).map C.Ψ.toMonoidHom).index < 176 := by
      rw [Subgroup.index_map_of_bijective C.Ψ.bijective]
      omega
    have hjΔ : ∀ j ∈ C.J, ∀ x ∈ Δ, j • x ∈ Δ := fun j hj x hx => by
      have hjS : j ∈ stabilizer G ω := by rw [hS]; exact hj
      exact mem_orbit_of_mem_orbit (⟨j, hjS⟩ : ↥(stabilizer G ω)) hx
    have hjΓ : ∀ j ∈ C.J, ∀ x ∈ Γ, j • x ∈ Γ := fun j hj x hx => by
      have hjS : j ∈ stabilizer G ω := by rw [hS]; exact hj
      exact mem_orbit_of_mem_orbit (⟨j, hjS⟩ : ↥(stabilizer G ω)) hx
    rcases hF _ hidx with htop | ⟨m, hm⟩ | ⟨m, hm⟩
    ·
      apply hgω
      have hJK : ∀ y ∈ C.J, y ∈ C.J.map (MulAut.conj g).toMonoidHom := fun y hy => by
        have := (C.map_mono_iff K ⟨y, hy⟩).mp (by rw [htop]; exact Subgroup.mem_top _)
        exact this.2
      have hgN : g⁻¹ ∈ Subgroup.normalizer (C.J : Set G) := by
        refine Subgroup.mem_normalizer_fintype fun y hy => ?_
        have := hJK y hy
        rw [mem_map_conj_iff] at this
        simpa using this
      have hg : g ∈ C.J := by
        have := C.mem_J_of_mem_normalizer hcN hcNN hcL hcJ ((Subgroup.normalizer _).inv_mem hgN)
        simpa using this
      exact C.smul_omega_of_mem hg
    ·
      have hK := C.eq_conj_of_map_eq (fun y => C.hΨL y) m hm
      set j : ↥C.J := C.Ψ.symm m with hj
      have h1 : ∀ k ∈ C.L, ((j : G)⁻¹ * g)⁻¹ * k * ((j : G)⁻¹ * g) ∈ C.J := by
        intro k hk
        have hkJ : (j : G) * k * (j : G)⁻¹ ∈ C.J :=
          C.J.mul_mem (C.J.mul_mem j.2 (C.L_le_J hk)) (C.J.inv_mem j.2)
        have h2 := (hK ⟨_, hkJ⟩).mpr (by
          show (j : G)⁻¹ * ((j : G) * k * (j : G)⁻¹) * j ∈ C.L
          rwa [show (j : G)⁻¹ * ((j : G) * k * (j : G)⁻¹) * j = k by group])
        have h3 := (Subgroup.mem_inf.mp h2).2
        rw [mem_map_conj_iff] at h3
        rwa [show ((j : G)⁻¹ * g)⁻¹ * k * ((j : G)⁻¹ * g) =
          g⁻¹ * ((j : G) * k * (j : G)⁻¹) * g by group]
      rcases C.smul_mem_of_L_le hcN hcNN hcL h1 with h4 | h4
      · apply hgω
        rw [show g = (j : G) * ((j : G)⁻¹ * g) by group, mul_smul, h4]
        exact C.smul_omega_of_mem j.2
      · apply hgΔ
        rw [show g = (j : G) * ((j : G)⁻¹ * g) by group, mul_smul]
        exact hjΔ _ j.2 _ h4
    ·
      have hK := C.eq_conj_of_map_eq (fun y => C.hΨI y) m hm
      set j : ↥C.J := C.Ψ.symm m with hj
      have h1 : ∀ k ∈ C.I0, ((j : G)⁻¹ * g)⁻¹ * k * ((j : G)⁻¹ * g) ∈ C.J := by
        intro k hk
        have hkJ : (j : G) * k * (j : G)⁻¹ ∈ C.J :=
          C.J.mul_mem (C.J.mul_mem j.2 (C.I0_le_J hk)) (C.J.inv_mem j.2)
        have h2 := (hK ⟨_, hkJ⟩).mpr (by
          show (j : G)⁻¹ * ((j : G) * k * (j : G)⁻¹) * j ∈ C.I0
          rwa [show (j : G)⁻¹ * ((j : G) * k * (j : G)⁻¹) * j = k by group])
        have h3 := (Subgroup.mem_inf.mp h2).2
        rw [mem_map_conj_iff] at h3
        rwa [show ((j : G)⁻¹ * g)⁻¹ * k * ((j : G)⁻¹ * g) =
          g⁻¹ * ((j : G) * k * (j : G)⁻¹) * g by group]
      rcases C.smul_mem_of_I0_le hd h1 with h4 | h4
      · apply hgω
        rw [show g = (j : G) * ((j : G)⁻¹ * g) by group, mul_smul, h4]
        exact C.smul_omega_of_mem j.2
      · apply hgΓ
        rw [show g = (j : G) * ((j : G)⁻¹ * g) by group, mul_smul]
        exact hjΓ _ j.2 _ h4
  have hle : ((({ω} : Set (G ⧸ C.J)) ∪ Δ ∪ Γ) ∪ O).ncard ≤ Nat.card (G ⧸ C.J) := by
    rw [← Set.ncard_univ]
    exact Set.ncard_le_ncard (Set.subset_univ _)
  rw [Set.ncard_union_eq hOdisj, hΩc] at hle
  omega

end HSCtx

end CFSG.Quasithin.HSType

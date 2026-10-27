module

public import CFSG.Quasithin.Recognition.HSType18a
public import CFSG.Sporadic.Recognition.HSWales

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique MulAction
open CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94
open HSSetting

namespace HSCtx

variable {G : Type} [Group G] [Finite G] (C : HSCtx G)

theorem inf_conj_c
    {c : G} (hcL : c ∈ Subgroup.normalizer (C.L : Set G))
    (hcJ : c ∉ Subgroup.normalizer (C.J : Set G)) :
    C.J ⊓ C.J.map (MulAut.conj c).toMonoidHom = C.L := by
  have hLc : C.L ≤ C.J.map (MulAut.conj c).toMonoidHom := by
    intro k hk
    rw [mem_map_conj_iff]
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hcL) k).mp hk
    rw [inv_inv] at this
    exact C.L_le_J this
  rcases C.eq_J_of_L_le (le_inf C.L_le_J hLc)
    (inf_le_left : C.J ⊓ C.J.map (MulAut.conj c).toMonoidHom ≤ C.J) with h | h
  · exact h
  · exfalso
    apply hcJ
    have hle : C.J ≤ C.J.map (MulAut.conj c).toMonoidHom := fun y hy => by
      have : y ∈ C.J ⊓ C.J.map (MulAut.conj c).toMonoidHom := by rw [h]; exact hy
      exact this.2
    have heq : C.J.map (MulAut.conj c).toMonoidHom = C.J := (Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj c).injective])).symm
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    rw [← heq]
    exact ⟨y, hy, rfl⟩

theorem inf_conj_d
    {d : G} (hdI : d ∈ Subgroup.normalizer (C.I0 : Set G))
    (hdJ : d ∉ Subgroup.normalizer (C.J : Set G)) :
    C.J ⊓ C.J.map (MulAut.conj d).toMonoidHom = C.I0 := by
  have hIc : C.I0 ≤ C.J.map (MulAut.conj d).toMonoidHom := by
    intro k hk
    rw [mem_map_conj_iff]
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hdI) k).mp hk
    rw [inv_inv] at this
    exact C.I0_le_J this
  rcases C.eq_J_of_I0_le (le_inf C.I0_le_J hIc)
    (inf_le_left : C.J ⊓ C.J.map (MulAut.conj d).toMonoidHom ≤ C.J) with h | h
  · exact h
  · exfalso
    apply hdJ
    have hle : C.J ≤ C.J.map (MulAut.conj d).toMonoidHom := fun y hy => by
      have : y ∈ C.J ⊓ C.J.map (MulAut.conj d).toMonoidHom := by rw [h]; exact hy
      exact this.2
    have heq : C.J.map (MulAut.conj d).toMonoidHom = C.J := (Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj d).injective])).symm
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    rw [← heq]
    exact ⟨y, hy, rfl⟩

theorem ncard_orbit_eq (x : G) {K : Subgroup G}
    (hK : C.J ⊓ C.J.map (MulAut.conj x).toMonoidHom = K) {n : ℕ}
    (hn : Nat.card K * n = Nat.card C.J) :
    (orbit (stabilizer G ((1 : G) : G ⧸ C.J)) (x • ((1 : G) : G ⧸ C.J))).ncard = n := by
  rw [← index_stabilizer]
  have hstab : stabilizer (stabilizer G ((1 : G) : G ⧸ C.J)) (x • ((1 : G) : G ⧸ C.J)) =
      (stabilizer G (x • ((1 : G) : G ⧸ C.J))).subgroupOf (stabilizer G ((1 : G) : G ⧸ C.J)) := by
    ext s
    rfl
  have hS : stabilizer G ((1 : G) : G ⧸ C.J) = C.J := stabilizer_quotient C.J
  rw [hstab, stabilizer_smul_eq_stabilizer_map_conj, hS]
  have h1 := ((C.J.map (MulAut.conj x).toMonoidHom).subgroupOf C.J).card_mul_index
  have hc : Nat.card ↥((C.J.map (MulAut.conj x).toMonoidHom).subgroupOf C.J) = Nat.card K := by
    rw [← Subgroup.inf_subgroupOf_right,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, inf_comm, hK]
  rw [hc] at h1
  have hpos : 0 < Nat.card K := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans hn.symm)

theorem nonempty_mulEquiv_hs_of_card
    (hcard : Nat.card (G ⧸ C.J) = 100) : Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.HS) := by
  classical
  obtain ⟨c, hcN, hcNN, hc1, hc2⟩ := C.exists_c
  have hcL := C.mem_normalizer_of_swap hc1 hc2
  have hcJ := C.not_mem_normalizer_J hc1 hcL
  obtain ⟨d, hdI, hdJ, -⟩ := C.exists_d
  have hdJ' : d ∉ Subgroup.normalizer (C.J : Set G) := fun h =>
    hdJ (C.mem_J_of_mem_normalizer hcN hcNN hcL hcJ h)
  set ω : G ⧸ C.J := ((1 : G) : G ⧸ C.J) with hωdef
  have hS : stabilizer G ω = C.J := stabilizer_quotient C.J
  have hfaith : FaithfulSMul G (G ⧸ C.J) := by
    refine ⟨fun {g₁ g₂} hg => ?_⟩
    have hx : ∀ y : G, y * (g₂⁻¹ * g₁) * y⁻¹ ∈ C.J := by
      intro y
      rw [← hS, mem_stabilizer_iff]
      have h1 : (g₂⁻¹ * g₁) • (y⁻¹ • ω) = y⁻¹ • ω := by
        rw [mul_smul, hg, ← mul_smul, inv_mul_cancel, one_smul]
      calc (y * (g₂⁻¹ * g₁) * y⁻¹) • ω = y • ((g₂⁻¹ * g₁) • (y⁻¹ • ω)) := by
            simp only [mul_smul]
        _ = y • (y⁻¹ • ω) := by rw [h1]
        _ = ω := smul_inv_smul y ω
    have := C.eq_one_of_forall_conj_mem hcJ hx
    rw [inv_mul_eq_one] at this
    exact this.symm
  have : Fintype (G ⧸ C.J) := Fintype.ofFinite _
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
  have hΔΓ : Disjoint (({ω} : Set (G ⧸ C.J)) ∪ Δ) Γ := by
    refine Disjoint.union_left ?_ (hdisj _ _ fun he => ?_)
    · rw [← hω]
      refine hdisj _ _ fun he => ?_
      have := congrArg Set.ncard he
      rw [hω, Set.ncard_singleton, ← hΓdef, hΓ] at this
      omega
    · have := congrArg Set.ncard he
      rw [← hΔdef, ← hΓdef, hΔ, hΓ] at this
      omega
  have hunion : ({ω} : Set (G ⧸ C.J)) ∪ Δ ∪ Γ = Set.univ := by
    refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_ (Set.toFinite _)
    rw [Set.ncard_univ, hcard, Set.ncard_union_eq hΔΓ, Set.ncard_union_eq hωΔ,
      Set.ncard_singleton, hΔ, hΓ]
  have horb : Set.range (orbit (stabilizer G ω) : G ⧸ C.J → Set (G ⧸ C.J)) = {{ω}, Δ, Γ} := by
    ext O
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, rfl⟩
      have hx : x ∈ ({ω} : Set (G ⧸ C.J)) ∪ Δ ∪ Γ := by rw [hunion]; exact Set.mem_univ x
      rcases hx with (hx | hx) | hx
      · left
        rw [Set.mem_singleton_iff.mp hx, hω]
      · right; left
        exact orbit_eq_iff.mpr hx
      · right; right
        exact orbit_eq_iff.mpr hx
    · rintro (rfl | rfl | rfl)
      · exact ⟨ω, hω⟩
      · exact ⟨c • ω, rfl⟩
      · exact ⟨d • ω, rfl⟩
  have hM : Nonempty (stabilizer G ω ≃* CFSG.Blueprint.NativeSporadic.M22) :=
    ⟨(MulEquiv.subgroupCongr hS).trans C.Ψ⟩
  exact (CFSG.Sporadic.Recognition.HSWales.wales_1969_HS_rank_3_graph_uniqueness.{0, 0, 0, 0}
    hcard ω hM Δ Γ horb hΔ hΓ).2.2

end HSCtx

theorem statementI48_of_card
    (hfact : FactAutL34)
    (hcard : ∀ (G : Type) [Group G] [Finite G], IsTypeHS G → ∀ C : HSCtx G,
      Nat.card (G ⧸ C.J) = 100) :
    StatementI48 := by
  intro G _ _ hG
  obtain ⟨C⟩ := exists_hsCtx hfact hG
  exact C.nonempty_mulEquiv_hs_of_card (hcard G hG C)

end CFSG.Quasithin.HSType

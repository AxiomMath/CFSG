module

public import CFSG.Milestones.ASVolI.F48.D43.Gen
public import CFSG.Milestones.ASVolI.F48.D43.Defs
public import Certificates.Certificate7800
public import Certificates.Certificate7801
public import CFSG.LieType.Chevalley.TrialityExactFiniteOrder

public section

namespace CFSG.ASVolI

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.F3.Native CFSG.Sporadic.Fi23.Native CFSG.Sporadic.ON.Native
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

attribute [local irreducible] burnsideF48d_KeysHex burnsideF48d_TabsHex burnsideF48d_GensHex
  burnsideF48d_PhiHex burnsideF48d_limbs burnsideF48d_colTab

theorem burnsideF48d_rep_unique {T : Table} {g h : Equiv.Perm (Fin 26572)} (hg : Rep 26572 T g)
    (hh : Rep 26572 T h) : g = h := by
  apply Equiv.ext
  intro i
  apply Fin.ext
  have h1 := hg i.val i.isLt
  have h2 := hh i.val i.isLt
  rw [idx_of_lt _ i.isLt] at h1 h2
  simpa using h1.symm.trans h2

theorem burnsideF48d_perm_eq {T : Table} {g : Equiv.Perm (Fin 26572)} (hg : Rep 26572 T g) :
    burnsideF48d_perm T = g :=
  burnsideF48d_rep_unique (Classical.epsilon_spec (p := fun g => Rep 26572 T g) ⟨g, hg⟩) hg

theorem burnsideF48d_ap_toT {a : Array ℕ} {i : ℕ} (hi : i < a.size) (ha : a[i]! < 2 ^ 32) :
    ap (burnsideF48d_toT a) i = a[i]! := by
  unfold ap burnsideF48d_toT
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_map, ← getElem!_pos a i hi,
    UInt32.toNat_ofNat', Nat.mod_eq_of_lt ha]

theorem burnsideF48d_rep_of_apply {a : Array ℕ} (ha : a.size = 26572) {g : Equiv.Perm (Fin 26572)}
    (hg : ∀ p : Fin 26572, ((g p : Fin 26572) : ℕ) = a[p.val]!) : Rep 26572 (burnsideF48d_toT a) g := by
  intro p hp
  have he : ((g ⟨p, hp⟩ : Fin 26572) : ℕ) = a[p]! := hg ⟨p, hp⟩
  rw [burnsideF48d_ap_toT (by rw [ha]; exact hp)
    (by rw [← he]; exact lt_trans (Fin.isLt _) (by norm_num)), idx_of_lt _ hp]
  exact he.symm

theorem burnsideF48d_phi_rep :
    ∃ e : Equiv.Perm (Fin 26572), Rep 26572 (burnsideF48d_toT (burnsideF48d_phi ())) e := by
  obtain ⟨e, he⟩ := Certificates.certificate7801
  refine ⟨e, burnsideF48d_rep_of_apply ?_ he⟩
  simp only [burnsideF48d_phi, CFSG.Monster.B.Co2.Native.hexTable, Array.size_ofFn]

section Action

variable {K : Type} [Field K] [CharP K 3] (σ : K →+* K) (ω : K)
variable (hK : Nat.card K = 27) (hσ : ∀ c, σ c = c ^ 3) (hω : ω ^ 3 = ω + 1)

include hK hσ hω in
theorem burnsideF48d_g_mem_C0 (k : Fin 8) :
    ((burnsideF48d_g σ ω k : adjointGroup d4 K) : ModGL d4 K) ∈
      graphFixedRootGroup TwistTag.D4 K σ := by
  rw [burnsideF48d_C0_eq σ ω hK hσ hω]
  exact Subgroup.subset_closure ⟨k, rfl⟩

@[expose] noncomputable def burnsideF48d_gC (k : Fin 8) : ↥(graphFixedRootGroup TwistTag.D4 K σ) :=
  ⟨_, burnsideF48d_g_mem_C0 σ ω hK hσ hω k⟩

include hK hσ hω in
theorem burnsideF48d_exists_ρ8 : ∃ ρ : ↥(Subgroup.closure (Set.range fun k : Fin 8 =>
      ((burnsideF48d_g σ ω k : adjointGroup d4 K) : ModGL d4 K))) →* Equiv.Perm (Fin 26572),
    ∀ k (p : Fin 26572), ((ρ ⟨_, Subgroup.subset_closure ⟨k, rfl⟩⟩ p : Fin 26572) : ℕ) =
      (burnsideF48d_gen k)[p.val]! :=
  Certificates.certificate7800 K ω hK hω _ fun k => burnsideF48d_g_val σ ω hσ hω k

@[expose] noncomputable def burnsideF48d_ρ :
    ↥(graphFixedRootGroup TwistTag.D4 K σ) →* Equiv.Perm (Fin 26572) :=
  (Classical.choose (burnsideF48d_exists_ρ8 σ ω hK hσ hω)).comp
    (MulEquiv.subgroupCongr (burnsideF48d_C0_eq σ ω hK hσ hω)).toMonoidHom

include hK hσ hω in
theorem burnsideF48d_rep_ρ_g (k : Fin 8) :
    Rep 26572 (burnsideF48d_toT (burnsideF48d_gen k)) (burnsideF48d_ρ σ ω hK hσ hω
      (burnsideF48d_gC σ ω hK hσ hω k)) := by
  refine burnsideF48d_rep_of_apply ?_ fun p => ?_
  · simp only [burnsideF48d_gen, CFSG.Monster.B.Co2.Native.hexTable, Array.size_ofFn]
  · exact (Classical.choose_spec (burnsideF48d_exists_ρ8 σ ω hK hσ hω)) k p

include hK hσ hω in
theorem burnsideF48d_ρ_g (k : Fin 8) :
    burnsideF48d_ρ σ ω hK hσ hω (burnsideF48d_gC σ ω hK hσ hω k) = burnsideF48d_γ k :=
  (burnsideF48d_perm_eq (burnsideF48d_rep_ρ_g σ ω hK hσ hω k)).symm

include hK hσ hω in
theorem burnsideF48d_range_ρ : (burnsideF48d_ρ σ ω hK hσ hω).range = burnsideF48d_X := by
  apply le_antisymm
  · rintro _ ⟨⟨g, hg⟩, rfl⟩
    have hgS := hg
    rw [burnsideF48d_C0_eq σ ω hK hσ hω] at hgS
    induction hgS using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      have : (⟨_, hg⟩ : ↥(graphFixedRootGroup TwistTag.D4 K σ)) = burnsideF48d_gC σ ω hK hσ hω k :=
        rfl
      rw [this, burnsideF48d_ρ_g]
      exact burnsideF48d_γ_mem k
    | one =>
      have : (⟨1, hg⟩ : ↥(graphFixedRootGroup TwistTag.D4 K σ)) = 1 := rfl
      rw [this, map_one]
      exact burnsideF48d_X.one_mem
    | mul x y hx hy ihx ihy =>
      have hx' : x ∈ graphFixedRootGroup TwistTag.D4 K σ := by
        rw [burnsideF48d_C0_eq σ ω hK hσ hω]; exact hx
      have hy' : y ∈ graphFixedRootGroup TwistTag.D4 K σ := by
        rw [burnsideF48d_C0_eq σ ω hK hσ hω]; exact hy
      have : (⟨x * y, hg⟩ : ↥(graphFixedRootGroup TwistTag.D4 K σ)) = ⟨x, hx'⟩ * ⟨y, hy'⟩ := rfl
      rw [this, map_mul]
      exact burnsideF48d_X.mul_mem (ihx hx') (ihy hy')
    | inv x hx ihx =>
      have hx' : x ∈ graphFixedRootGroup TwistTag.D4 K σ := by
        rw [burnsideF48d_C0_eq σ ω hK hσ hω]; exact hx
      have : (⟨x⁻¹, hg⟩ : ↥(graphFixedRootGroup TwistTag.D4 K σ)) = (⟨x, hx'⟩)⁻¹ := rfl
      rw [this, map_inv]
      exact burnsideF48d_X.inv_mem (ihx hx')
  · rw [burnsideF48d_X, Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    exact ⟨_, burnsideF48d_ρ_g σ ω hK hσ hω k⟩

include hK hσ in
theorem burnsideF48d_card_C0 :
    Nat.card ↥(graphFixedRootGroup TwistTag.D4 K σ) = 20560831566912 := by
  have h := (CFSG.LieType.Chevalley.triality_both_orientations_exact_finite_order 3 1
    Nat.prime_three le_rfl K (by rw [hK]; norm_num) 1 (Or.inl rfl) σ
    (fun c => by rw [hσ]; norm_num)).1
  rw [h]
  norm_num

include hK hσ hω in
theorem burnsideF48d_card_X_le : Nat.card ↥burnsideF48d_X ≤ 20560831566912 := by
  haveI : Finite ↥(graphFixedRootGroup TwistTag.D4 K σ) :=
    Nat.finite_of_card_ne_zero (by rw [burnsideF48d_card_C0 σ hK hσ]; norm_num)
  rw [← burnsideF48d_card_C0 σ hK hσ, ← burnsideF48d_range_ρ σ ω hK hσ hω]
  exact Nat.card_le_card_of_surjective _ (burnsideF48d_ρ σ ω hK hσ hω).rangeRestrict_surjective

end Action

end CFSG.ASVolI

module

public import CFSG.Quasithin.Background.B4L3Coord
public import CFSG.Quasithin.Vol2.Ch10SecV1A
public import CFSG.Quasithin.Vol2.Ch10SecV1B

public section

namespace CFSG.Quasithin.Vol2.Ch10.V1C

open CFSG.Quasithin

variable {V : Type*} [CommGroup V] {G : Subgroup (MulAut V)} {W₂ W₁ : Subgroup V}
  (D : L3Data G W₂ W₁)
include D

theorem rho_invol {x : L3.Γ} (hx : L3.IsInvol x) (v : V) : D.rho x (D.rho x v) = v := by
  rw [← MulAut.mul_apply, ← map_mul, hx.1, map_one, MulAut.one_apply]

theorem rho_sq {x : L3.Γ} (hx : L3.IsInvol x) : D.rho x ^ 2 = 1 := by
  rw [← map_pow, pow_two, hx.1, map_one]

theorem rho_ne_one {x : L3.Γ} (hx : L3.IsInvol x) : D.rho x ≠ 1 := fun h =>
  hx.2 (D.rho_injective (by rw [h, map_one]))

theorem card_conj_t [Finite V] {x : L3.Γ} (hx : L3.IsInvol x) {W K : Subgroup V}
    (hW : ∀ g ∈ G, ∀ w ∈ W, g w ∈ W) (hK : K ≤ fixV G) :
    Nat.card ↥(W.map (commHom (D.rho x)) ⊔ K) =
      Nat.card ↥(W.map (commHom (D.rho L3.x12)) ⊔ K) := by
  obtain ⟨g, hg, hgx⟩ := D.exists_conj (D.rho_mem L3.x12) (rho_sq D L3.x12_invol)
    (rho_ne_one D L3.x12_invol) (D.rho_mem x) (rho_sq D hx) (rho_ne_one D hx)
  rw [← hgx]
  exact card_map_conj (hW g hg) (hW g⁻¹ (G.inv_mem hg)) (fun _ hk => hK hk g hg)

theorem fix_bound [Finite V] {W K : Subgroup V} (hW : ∀ g ∈ G, ∀ w ∈ W, g w ∈ W)
    (hK : K ≤ fixV G) (h : Nat.card ↥(W.map (commHom (D.rho L3.x12)) ⊔ K) ≤ 2 * Nat.card K) :
    ∃ X : Subgroup V, X ≤ W ∧ Nat.card W ≤ 8 * Nat.card X ∧
      ∀ x ∈ X, ∀ g ∈ G, g x * x⁻¹ ∈ K := by
  refine ⟨fixRel (D.rho L3.x12) W K ⊓ fixRel (D.rho L3.x23) W K ⊓ fixRel (D.rho L3.x31) W K,
    inf_le_left.trans (inf_le_left.trans inf_le_left), card_le_eight_mul h ?_ ?_, ?_⟩
  · rwa [card_conj_t D L3.x23_invol hW hK]
  · rwa [card_conj_t D L3.x31_invol hW hK]
  · rintro x ⟨⟨⟨-, h₁⟩, ⟨-, h₂⟩⟩, ⟨-, h₃⟩⟩
    exact mem_of_mem_fixRel (fun S => D.le_of_gens) (D.rho_mem _) (D.rho_mem _) (D.rho_mem _)
      hK h₁ h₂ h₃

theorem comm_bound [Finite V] {W K : Subgroup V} (hW : ∀ g ∈ G, ∀ w ∈ W, g w ∈ W)
    (hKW : K ≤ W) (hK : K ≤ fixV G)
    (h : Nat.card ↥(W.map (commHom (D.rho L3.x12)) ⊔ K) ≤ 2 * Nat.card K) :
    Nat.card ↥(commSub W G ⊔ K) ≤ 8 * Nat.card K :=
  card_commSub_sup_le (fun S => D.le_of_gens) (D.rho_mem _) (D.rho_mem _) (D.rho_mem _)
    (rho_invol D L3.x12_invol) (rho_invol D L3.x23_invol) (rho_invol D L3.x31_invol) hW hKW h
    (by rwa [card_conj_t D L3.x23_invol hW hK]) (by rwa [card_conj_t D L3.x31_invol hW hK])

theorem sq_bound [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {W K : Subgroup V}
    (hW : ∀ g ∈ G, ∀ w ∈ W, g w ∈ W) (hKW : K ≤ W) (hK : K ≤ fixV G) :
    Nat.card ↥(W.map (commHom (D.rho L3.x12)) ⊔ K) ^ 2 ≤ Nat.card W * Nat.card K :=
  sq_card_le hV (rho_invol D L3.x12_invol) (hW _ (D.rho_mem _)) hKW
    (fun _ hk => hK hk _ (D.rho_mem _))

theorem exists_mem_commV (n : L3.Vec) :
    ∃ u ∈ commV G, ∃ hu : u ∈ W₂, D.β ⟨u, hu⟩ = Multiplicative.ofAdd n := by
  obtain ⟨γ, v, hv⟩ := L3.act_allcomm n
  obtain ⟨w, hw⟩ := D.β_surj (Multiplicative.ofAdd v)
  have hγw : D.rho γ (w : V) ∈ W₂ := D.inv_U _ (D.rho_mem γ) _ w.2
  refine ⟨D.rho γ w * (w : V)⁻¹, Subgroup.subset_closure ⟨D.rho γ, D.rho_mem γ, w, rfl⟩,
    W₂.mul_mem hγw (W₂.inv_mem w.2), ?_⟩
  have e : (⟨D.rho γ w * (w : V)⁻¹, W₂.mul_mem hγw (W₂.inv_mem w.2)⟩ : ↥W₂) =
      ⟨D.rho γ w, hγw⟩ * w⁻¹ := rfl
  rw [e, map_mul, map_inv, D.β_rho γ w w.2 hγw]
  simp only [Subtype.coe_eta, hw, toAdd_ofAdd, ← hv, ofAdd_sub, div_eq_mul_inv]
  rfl

theorem card_commV [Finite V] (hUW : commV G ≤ W₂) :
    Nat.card (commV G) = 8 * Nat.card ↥(commV G ⊓ W₁) := by
  let ψ : ↥(commV G) →* Multiplicative L3.Vec := D.β.comp (Subgroup.inclusion hUW)
  have h := B1More.card_map_mul_card_inf_ker (⊤ : Subgroup ↥(commV G)) ψ
  have h1 : (⊤ : Subgroup ↥(commV G)).map ψ = ⊤ := by
    rw [Subgroup.map_top, MonoidHom.range_eq_top]
    intro m
    obtain ⟨u, hu, huW, hβ⟩ := exists_mem_commV D (Multiplicative.toAdd m)
    exact ⟨⟨u, hu⟩, by rw [ofAdd_toAdd] at hβ; exact hβ⟩
  have h2 : Nat.card ↥((⊤ : Subgroup ↥(commV G)) ⊓ ψ.ker) = Nat.card ↥(commV G ⊓ W₁) := by
    refine Nat.card_congr ⟨fun u => ⟨u.1.1, u.1.2, (D.ker_β _).1 u.2.2⟩,
      fun z => ⟨⟨z.1, z.2.1⟩, trivial, (D.ker_β ⟨z.1, hUW z.2.1⟩).2 z.2.2⟩, ?_, ?_⟩
    · intro u
      rfl
    · intro z
      rfl
  rw [h1, h2, Subgroup.card_top, Subgroup.card_top, L3Data.card_vec] at h
  exact h.symm

theorem mem_of_forall {u : V} (hu : u ∈ W₂) (h : ∀ g ∈ G, g u * u⁻¹ ∈ W₁) : u ∈ W₁ := by
  apply (D.ker_β ⟨u, hu⟩).1
  by_contra hne
  have hne' : Multiplicative.toAdd (D.β ⟨u, hu⟩) ≠ 0 := fun h0 =>
    hne (by rw [← ofAdd_toAdd (D.β ⟨u, hu⟩), h0, ofAdd_zero])
  obtain ⟨γ, hγ⟩ := L3.act_nofix _ hne'
  apply hγ
  have hγu : D.rho γ u ∈ W₂ := D.inv_U _ (D.rho_mem γ) _ hu
  have hk : D.β (⟨D.rho γ u, hγu⟩ * ⟨u, hu⟩⁻¹) = 1 :=
    (D.ker_β _).2 (h _ (D.rho_mem γ))
  rw [map_mul, map_inv, D.β_rho γ u hu hγu] at hk
  have h2 := congrArg Multiplicative.toAdd (mul_inv_eq_one.mp hk)
  rwa [toAdd_ofAdd] at h2

end CFSG.Quasithin.Vol2.Ch10.V1C

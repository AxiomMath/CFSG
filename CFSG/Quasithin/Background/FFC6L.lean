module

public import CFSG.Quasithin.Background.StabSubBasics
public import CFSG.Quasithin.Background.FFC4Five

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Assembly.LowTwoRank Equiv Equiv.Perm

namespace B59

section Finite5

theorem card_comm_odd_le : ∀ σ : Perm (Fin 5), (σ ≠ 1 ∧ σ * σ = 1 ∧ sign σ = -1) →
    ((Finset.univ.filter (fun m : Fin 5 → ZMod 2 => ∑ i, m i = 0)).image
      (fun m : Fin 5 → ZMod 2 => fun i => m (σ⁻¹ i) - m i)).card ≤ 2 := by
  decide +kernel

theorem card_fix_pair_le : ∀ σ τ : Perm (Fin 5), (σ ≠ 1 ∧ τ ≠ 1 ∧ σ ≠ τ ∧ σ * σ = 1 ∧ τ * τ = 1 ∧
    σ * τ = τ * σ ∧ sign σ = -1) →
    (Finset.univ.filter (fun m : Fin 5 → ZMod 2 => ∑ i, m i = 0 ∧ (∀ i, m (σ⁻¹ i) = m i) ∧
      ∀ i, m (τ⁻¹ i) = m i)).card ≤ 4 := by
  decide +kernel

theorem card_cent_odd : ∀ σ : Perm (Fin 5), (σ ≠ 1 ∧ σ * σ = 1 ∧ sign σ = -1) →
    (Finset.univ.filter (fun τ : Perm (Fin 5) => τ * σ = σ * τ)).card = 12 := by
  decide +kernel

@[expose] noncomputable def commS (σ : Perm (Fin 5)) : Finset (G6.PermMod 5) :=
  ((Finset.univ.filter (fun m : Fin 5 → ZMod 2 => ∑ i, m i = 0)).image
    (fun m : Fin 5 → ZMod 2 => fun i => m (σ⁻¹ i) - m i)).image Multiplicative.ofAdd

theorem card_commS_le {σ : Perm (Fin 5)} (h1 : σ ≠ 1) (h2 : σ * σ = 1) (h3 : sign σ = -1) :
    (commS σ).card ≤ 2 :=
  Finset.card_image_le.trans (card_comm_odd_le σ ⟨h1, h2, h3⟩)

theorem mem_commS {σ : Perm (Fin 5)} {y : G6.PermMod 5} (hy : y ∈ G6.coreMod 5) :
    G6.permAct 5 σ y * y⁻¹ ∈ commS σ := by
  refine Finset.mem_image.2 ⟨fun i => Multiplicative.toAdd y (σ⁻¹ i) - Multiplicative.toAdd y i,
    Finset.mem_image.2 ⟨Multiplicative.toAdd y, Finset.mem_filter.2 ⟨Finset.mem_univ _, hy⟩, rfl⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  funext i
  simp [G6.permAct_apply, sub_eq_add_neg]
  exact (by decide : ∀ x : ZMod 2, x = -x) _

theorem card_fixS₂_le_four {σ τ : Perm (Fin 5)} (h1 : σ ≠ 1) (h2 : τ ≠ 1) (h3 : σ ≠ τ) (h4 : σ * σ = 1)
    (h5 : τ * τ = 1) (h6 : σ * τ = τ * σ) (h7 : sign σ = -1) : (fixS₂ σ τ).card ≤ 4 :=
  Finset.card_image_le.trans (card_fix_pair_le σ τ ⟨h1, h2, h3, h4, h5, h6, h7⟩)

theorem card_centralizer_odd {σ : Perm (Fin 5)} (h1 : σ ≠ 1) (h2 : σ * σ = 1) (h3 : sign σ = -1) :
    Nat.card ↥(Subgroup.centralizer ({σ} : Set (Perm (Fin 5)))) = 12 := by
  have e : ↥(Subgroup.centralizer ({σ} : Set (Perm (Fin 5)))) ≃
      {τ : Perm (Fin 5) // τ * σ = σ * τ} :=
    Equiv.subtypeEquivRight fun τ => Subgroup.mem_centralizer_singleton_iff
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact card_cent_odd σ ⟨h1, h2, h3⟩

end Finite5

section General

variable {M : Type*} [CommGroup M]

@[expose] def commMap (a : MulAut M) : M →* M where
  toFun w := a w * w⁻¹
  map_one' := by simp
  map_mul' x y := by
    rw [map_mul, mul_inv]
    simp [mul_comm, mul_left_comm, mul_assoc]

theorem commMap_apply (a : MulAut M) (w : M) : commMap a w = a w * w⁻¹ := rfl

theorem mem_fixV_zpowers {a : MulAut M} {w : M} : w ∈ fixV (Subgroup.zpowers a) ↔ a w = w :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

theorem ker_commMap (a : MulAut M) : (commMap a).ker = fixV (Subgroup.zpowers a) := by
  ext w
  rw [MonoidHom.mem_ker, commMap_apply, mem_fixV_zpowers, mul_inv_eq_one]

theorem isElemAbelian2_zpowers {s : MulAut M} (hs : s ^ 2 = 1) :
    IsElemAbelian2 (Subgroup.zpowers s) :=
  CFSG.Quasithin.StabLat.isElemAbelian2_zpowers hs

theorem card_le_of_inj_maps_into {G P : Type*} [Group G] [Group P] (q : G →* P) (K : Subgroup G)
    (hq : ∀ k ∈ K, q k = 1 → k = 1) (S : Finset P) (hS : ∀ k ∈ K, q k ∈ S) :
    Nat.card K ≤ S.card := by
  classical
  have h4 : Nat.card K ≤ Nat.card (S : Set P) := by
    refine Nat.card_le_card_of_injective (fun x => (⟨q x, hS x x.2⟩ : (S : Set P))) ?_
    intro x y hxy
    have h' : q (x : G) = q (y : G) := congrArg (fun z : (S : Set P) => (z : P)) hxy
    have h1 : q ((x : G) * (y : G)⁻¹) = 1 := by rw [map_mul, map_inv, h', mul_inv_cancel]
    have h2 := hq _ (K.mul_mem x.2 (K.inv_mem y.2)) h1
    exact Subtype.ext (mul_inv_eq_one.1 h2)
  simpa using h4

end General

end B59

end FFC

end CFSG.Quasithin

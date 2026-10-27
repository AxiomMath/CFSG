module

public import CFSG.Quasithin.H13.NQCatA314Gen
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE68SporAsm
public import CFSG.Quasithin.EmptyFaithful.S151S9TLat
public import CFSG.Quasithin.Background.A312SporGen
public import CFSG.Quasithin.Background.A3Structure314Defs

public section

namespace CFSG.Quasithin.H13.NQCat.A314D

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat CFSG.Quasithin.E6.Spor
  CFSG.Quasithin.S151S9T CFSG.Quasithin.S151S9T.LatAux CFSG.Quasithin.E2P.SporB
open scoped Pointwise

theorem centralizer_eq_member {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)]
    [FaithfulSMul Γ (Fin n)] {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab]
    (C : LatCtx Γ n Lab) {Ls : Array ℕ} (hL : C.D.Om.map (fun o => o.lbl.size) = Ls)
    {z₀ : Γ} (hZ : C.S ⊓ Subgroup.centralizer (C.S : Set Γ) = Subgroup.zpowers z₀)
    (hnc : ¬ ∀ g : Γ, g * z₀ = z₀ * g) {q : ℕ}
    (huniq : ∀ j < Ls.size, Ls[j]! = Ls[q]! → j = q)
    (hmax : ∀ j < Ls.size, C.Y q ≤ C.Y j → j = q) {r m : ℕ} (hR : RWit C z₀ r m)
    (hmq : m = Ls[q]!) : Subgroup.centralizer ({z₀} : Set Γ) = C.Y q := by
  obtain ⟨us, uTabs, OH, -, -, hus, hucomm, hOH, hOHm, -⟩ := hR
  have hHcard := card_gen hus hOH
  rw [hOHm] at hHcard
  have hHle := genOver_le_centralizer C hZ hucomm
  have hne : Subgroup.centralizer ({z₀} : Set Γ) ≠ ⊤ := fun h => hnc fun g =>
    Subgroup.mem_centralizer_singleton_iff.mp (h ▸ Subgroup.mem_top g)
  have hSH := S_le_genOver C us
  have hHq : genOver C us = C.Y q := by
    rcases lat_cases C hL hSH with ⟨j, hj, hjeq⟩ | htop
    · have h1 := lat_card C hL j hj
      rw [← hjeq, hHcard, hmq] at h1
      have h2 : Ls[j]! = Ls[q]! :=
        (Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos _) h1).symm
      rw [hjeq, huniq j hj h2]
    · exfalso
      exact hne (top_le_iff.mp (htop ▸ hHle))
  rcases lat_cases C hL (hSH.trans hHle) with ⟨j, hj, hjeq⟩ | htop
  · have : C.Y q ≤ C.Y j := by rw [← hHq, ← hjeq]; exact hHle
    rw [hjeq, hmax j hj this]
  · exact absurd htop hne

theorem exists_eq_centralizer_of_unique {Γ P : Type} [Group Γ] [Finite Γ] [Group P] [Finite P]
    (φ : P ≃* Γ) {S₀ : Subgroup Γ} (hS₀ : IsSylowTwoOf S₀ ⊤) {z₀ : Γ}
    (hz₀ : z₀ ∈ S₀ ⊓ Subgroup.centralizer (S₀ : Set Γ))
    (huniq : ∀ Z : Subgroup Γ, S₀ ≤ Z →
      Nat.card Z = Nat.card (Subgroup.centralizer ({z₀} : Set Γ)) →
        Z = Subgroup.centralizer ({z₀} : Set Γ))
    {T X : Subgroup P} (hT : IsSylowTwoOf T ⊤) (hTX : T ≤ X)
    (hX : Nat.card X = Nat.card (Subgroup.centralizer ({z₀} : Set Γ))) :
    ∃ z : P, z ∈ T ∧ (∀ t ∈ T, t * z = z * t) ∧ orderOf z = orderOf z₀ ∧
      X = Subgroup.centralizer ({z} : Set P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let US : Sylow 2 Γ := hS₀.2.1.toSylow (by
    have := hS₀.2.2
    have e : (S₀.subgroupOf ⊤).index = S₀.index := Subgroup.relIndex_top_right _
    rwa [e] at this)
  have hTi : ¬ 2 ∣ T.index := by
    have := hT.2.2
    have e : (T.subgroupOf ⊤).index = T.index := Subgroup.relIndex_top_right _
    rwa [e] at this
  let TS : Sylow 2 Γ := (hT.2.1.toSylow hTi).mapSurjective (f := φ.toMonoidHom) φ.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ TS US
  let ψ : P ≃* Γ := φ.trans (MulAut.conj g)
  have hST : S₀ = T.map ψ.toMonoidHom := by
    have h1 : (US : Subgroup Γ) = S₀ := rfl
    rw [← h1, ← hg, Sylow.coe_subgroup_smul]
    show (T.map φ.toMonoidHom).map (MulAut.conj g).toMonoidHom = T.map ψ.toMonoidHom
    rw [Subgroup.map_map]
    rfl
  have hXc : X.map ψ.toMonoidHom = Subgroup.centralizer ({z₀} : Set Γ) :=
    huniq _ (hST ▸ Subgroup.map_mono hTX)
      ((Subgroup.card_map_of_injective ψ.injective).trans hX)
  refine ⟨ψ.symm z₀, ?_, ?_, ?_, ?_⟩
  · have h1 : z₀ ∈ T.map ψ.toMonoidHom := hST ▸ hz₀.1
    obtain ⟨t, ht, hte⟩ := h1
    have : ψ.symm z₀ = t := by
      rw [← hte]
      exact ψ.symm_apply_apply t
    rw [this]
    exact ht
  · intro t ht
    apply ψ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    have h1 : ψ t ∈ S₀ := hST ▸ Subgroup.mem_map_of_mem _ ht
    exact Subgroup.mem_centralizer_iff.mp hz₀.2 _ h1
  · exact MulEquiv.orderOf_eq ψ.symm z₀
  · ext x
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hx
      have h1 : ψ x ∈ Subgroup.centralizer ({z₀} : Set Γ) :=
        hXc ▸ Subgroup.mem_map_of_mem _ hx
      rw [Subgroup.mem_centralizer_singleton_iff] at h1
      apply ψ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact h1
    · intro hx
      have h1 : ψ x ∈ X.map ψ.toMonoidHom := by
        rw [hXc, Subgroup.mem_centralizer_singleton_iff]
        have := congrArg ψ hx
        rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
      obtain ⟨y, hy, hye⟩ := h1
      rwa [← ψ.injective hye]

end CFSG.Quasithin.H13.NQCat.A314D

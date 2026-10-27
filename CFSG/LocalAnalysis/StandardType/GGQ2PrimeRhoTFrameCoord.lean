module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeL81Coords
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeABridge
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofCoxeter

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Open CFSG.Assembly CFSG.StandardType

theorem rhoTFrame_z_coord {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L : Subgroup G} {A : Subgroup (MulAut Bs)} {κ : Fin 7 → (Bs →* Multiplicative (ZMod 3))}
    {m n : Fin 7} (h : CoordCtx B Bs x L A κ m) {g : G} (hg : g ∈ normalizer (Bs : Set G))
    (hl : IsCoordLift Bs κ g (Equiv.swap m n)) (i : Fin 7) :
    κ i ⟨g * x * g⁻¹, (mem_normalizer_iff.1 hg x).1 h.coords.x_mem⟩ =
      if i = n then 1 else ω3 := by
  rw [hl i ⟨x, h.coords.x_mem⟩ ((mem_normalizer_iff.1 hg x).1 h.coords.x_mem), Equiv.symm_swap,
    h.coords.x_coord]
  have e : Equiv.swap m n i = m ↔ i = n := by
    rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]
  simp only [e]

theorem rhoTFrame_exists_lift {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L : Subgroup G} {A : Subgroup (MulAut Bs)} {κ : Fin 7 → (Bs →* Multiplicative (ZMod 3))}
    {m : Fin 7} (h : CoordCtx B Bs x L A κ m) {σ : Equiv.Perm (Fin 7)} (hσ : σ m = m) :
    ∃ l ∈ L, l ∈ normalizer (Bs : Set G) ∧ IsCoordLift Bs κ l σ := by
  obtain ⟨-, -, -, hcomp, -, -, -, -⟩ := ggThmIHyp_unpack h.setting.hyp
  have hcard : Nat.card (ggAutomizer L Bs) = 720 := by
    obtain ⟨E, -⟩ := exists_permEquiv_of_ggWeylOfType_A h.weyl5
    rw [← Nat.card_congr E.toEquiv, Nat.card_perm, Nat.card_fin]
    rfl
  obtain ⟨φ, hφ, hφc⟩ := exists_mem_of_perm_fix h.coords h.AL_le
    (fun φ hφ => ggAutomizer_apply_eq_of_le_centralizer (x := ⟨x, h.coords.x_mem⟩) hcomp.1 hφ)
    hcard σ hσ
  obtain ⟨l, hlL, hlN, hlφ⟩ := mem_ggAutomizer_iff.1 hφ
  refine ⟨l, hlL, hlN, fun j b hgb => ?_⟩
  have e : (⟨l * b * l⁻¹, hgb⟩ : Bs) = φ b := Subtype.ext (hlφ b).symm
  rw [e, hφc]

theorem rhoTFrame_lift_comm {G : Type} [Group G] {Bs : Subgroup G} {A : Subgroup (MulAut Bs)}
    {x : G} {κ : Fin 7 → (Bs →* Multiplicative (ZMod 3))} {m n : Fin 7}
    (hW : WeylCoords Bs A x κ m) {l : G} (hlN : l ∈ normalizer (Bs : Set G))
    {σ : Equiv.Perm (Fin 7)} (hl : IsCoordLift Bs κ l σ) (hσn : σ n = n) {u : G} (hu : u ∈ Bs)
    (hcoord : ∀ i, κ i ⟨u, hu⟩ = if i = n then 1 else ω3) : l * u * l⁻¹ = u := by
  have hlu : l * u * l⁻¹ ∈ Bs := (mem_normalizer_iff.1 hlN u).1 hu
  have e : ∀ i, σ.symm i = n ↔ i = n := fun i => by rw [Equiv.symm_apply_eq σ, hσn]
  have := weylCoords_ext hW (b := ⟨l * u * l⁻¹, hlu⟩) (b' := ⟨u, hu⟩) fun i => by
    rw [hl i ⟨u, hu⟩ hlu, hcoord, hcoord]
    simp only [e]
  exact congrArg Subtype.val this

private theorem rhoTFrame_exists_fresh (m p q : Fin 7) : ∃ a : Fin 7, a ≠ m ∧ a ≠ p ∧ a ≠ q := by
  revert m p q
  decide

theorem rhoTFrame_perm_unique {G : Type} [Group G] {Bs : Subgroup G} {A : Subgroup (MulAut Bs)}
    {x : G} {κ : Fin 7 → (Bs →* Multiplicative (ZMod 3))} {m n : Fin 7}
    (hW : WeylCoords Bs A x κ m) (hn : n ≠ m) {σ σ' : Equiv.Perm (Fin 7)}
    (hσm : σ m = m) (hσn : σ n = n) (hσ'm : σ' m = m) (hσ'n : σ' n = n)
    {φ φ' : Bs → Bs} (hφ : ∀ j b, κ j (φ b) = κ (σ.symm j) b)
    (hφ' : ∀ j b, κ j (φ' b) = κ (σ'.symm j) b)
    (hc : ∀ b : Bs, κ m b = 1 → φ b * (φ' b)⁻¹ ∈ zpowers (⟨x, hW.x_mem⟩ : Bs)) : σ = σ' := by
  by_contra hne
  obtain ⟨j, hj⟩ : ∃ j, σ.symm j ≠ σ'.symm j := by
    by_contra hall
    refine hne ?_
    have h2 : σ.symm = σ'.symm := Equiv.ext fun j => by_contra fun hj => hall ⟨j, hj⟩
    simpa using congrArg Equiv.symm h2
  have hsm : σ.symm m = m := (Equiv.symm_apply_eq σ).2 hσm.symm
  have hsn : σ.symm n = n := (Equiv.symm_apply_eq σ).2 hσn.symm
  have hs'm : σ'.symm m = m := (Equiv.symm_apply_eq σ').2 hσ'm.symm
  have hs'n : σ'.symm n = n := (Equiv.symm_apply_eq σ').2 hσ'n.symm
  have hjm : j ≠ m := by
    rintro rfl
    exact hj (hsm.trans hs'm.symm)
  have hpm : σ.symm j ≠ m := fun h => hjm (((Equiv.symm_apply_eq σ).1 h).trans hσm)
  have hp'm : σ'.symm j ≠ m := fun h => hjm (((Equiv.symm_apply_eq σ').1 h).trans hσ'm)
  obtain ⟨a, ham, hap, hap'⟩ := rhoTFrame_exists_fresh m (σ.symm j) (σ'.symm j)
  obtain ⟨ua, hua⟩ := exists_point hW a
  obtain ⟨up, hup⟩ := exists_point hW (σ.symm j)
  have hb : κ m (ua * up⁻¹) = 1 := by
    rw [map_mul, map_inv, hua, hup, if_neg (Ne.symm ham), if_neg (Ne.symm hpm), mul_inv_cancel]
  obtain ⟨t, ht⟩ := Subgroup.mem_zpowers_iff.1 (hc _ hb)
  have hκ : ∀ i, κ i (φ (ua * up⁻¹)) * (κ i (φ' (ua * up⁻¹)))⁻¹ =
      (if i = m then 1 else ω3) ^ t := fun i => by
    rw [← map_inv, ← map_mul, ← ht, map_zpow, hW.x_coord]
  have h1 : (ω3 : Multiplicative (ZMod 3)) ^ t = 1 := by
    have := hκ n
    rwa [hφ, hφ', hsn, hs'n, mul_inv_cancel, if_neg hn, eq_comm] at this
  have h2 := hκ j
  rw [hφ, hφ', if_neg hjm, h1, mul_inv_eq_one, map_mul, map_mul, map_inv, map_inv, hua, hup,
    hua, hup, if_neg (Ne.symm hap), if_neg (Ne.symm hap'), if_pos rfl,
    if_neg (Ne.symm hj), mul_inv_cancel] at h2
  simp only [inv_one, mul_one] at h2
  exact one_ne_ω3 h2.symm

theorem rhoTFrame_card_stab {m n : Fin 7} (hn : n ≠ m) :
    120 ≤ (Finset.univ.filter fun σ : Equiv.Perm (Fin 7) => σ m = m ∧ σ n = n).card := by
  have h5 : ∀ m n : Fin 7, n ≠ m →
      (Finset.univ.filter fun j : Fin 7 => j ≠ m ∧ j ≠ n).card = 5 := by decide
  have hc : Fintype.card {j : Fin 7 // j ≠ m ∧ j ≠ n} = 5 := by
    rw [Fintype.card_subtype]
    exact h5 m n hn
  have hmem : ∀ σ : Equiv.Perm {j : Fin 7 // j ≠ m ∧ j ≠ n},
      ((Equiv.Perm.subtypeEquivSubtypePerm (fun j : Fin 7 => j ≠ m ∧ j ≠ n) σ :
        {f : Equiv.Perm (Fin 7) // ∀ a, ¬ (a ≠ m ∧ a ≠ n) → f a = a}) : Equiv.Perm (Fin 7)) ∈
          Finset.univ.filter fun σ : Equiv.Perm (Fin 7) => σ m = m ∧ σ n = n := fun σ => by
    have := (Equiv.Perm.subtypeEquivSubtypePerm (fun j : Fin 7 => j ≠ m ∧ j ≠ n) σ).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨this m (by simp), this n (by simp)⟩
  have hinj : Function.Injective fun σ : Equiv.Perm {j : Fin 7 // j ≠ m ∧ j ≠ n} =>
      ((Equiv.Perm.subtypeEquivSubtypePerm (fun j : Fin 7 => j ≠ m ∧ j ≠ n) σ :
        {f : Equiv.Perm (Fin 7) // ∀ a, ¬ (a ≠ m ∧ a ≠ n) → f a = a}) : Equiv.Perm (Fin 7)) :=
    Subtype.val_injective.comp (Equiv.Perm.subtypeEquivSubtypePerm _).injective
  have := Finset.card_le_card_of_injOn (s := Finset.univ) _ (fun σ _ => hmem σ) hinj.injOn
  rw [Finset.card_univ, Fintype.card_perm, hc] at this
  exact this

end CFSG.GGQ2Prime

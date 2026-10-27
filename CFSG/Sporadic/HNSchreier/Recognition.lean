module

public import CFSG.Sporadic.HN.Local.AltAbstract
public import Mathlib

public section

namespace CFSG.Sporadic.HNSchreier

open Equiv CFSG.Sporadic.HN.Local

noncomputable abbrev altPartHom : alternatingGroup (Fin 12) →* Perm Part :=
  natHom.comp (alternatingGroup (Fin 12)).subtype

@[expose] def part0 : Part := ⟨{0, 1, 3, 4, 5, 6}, by decide⟩

@[expose] def cyc012 : Perm (Fin 12) := swap 0 2 * swap 0 1

theorem cyc012_mem : cyc012 ∈ alternatingGroup (Fin 12) := by
  rw [Equiv.Perm.mem_alternatingGroup, cyc012, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
  decide

theorem cyc012_moves : cyc012 • part0 ≠ part0 := by decide +kernel

theorem natHom_injective : Function.Injective (natHom : Perm (Fin 12) →* Perm Part) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  by_contra hne
  have hnt : Nontrivial (natHom : Perm (Fin 12) →* Perm Part).ker :=
    (Subgroup.nontrivial_iff_ne_bot _).2 hne
  have hc : cyc012 ∈ (natHom : Perm (Fin 12) →* Perm Part).ker :=
    Equiv.Perm.alternatingGroup_le_of_normal (by simp) hnt cyc012_mem
  rw [MonoidHom.mem_ker] at hc
  exact cyc012_moves (congrArg (fun σ : Perm Part => σ part0) hc)

theorem natHom_alt_injective : Function.Injective altPartHom :=
  fun _ _ h => Subtype.val_injective (natHom_injective h)

theorem card_eq_of_partition_labels {H : Type*} [Group H] [Finite H] (φ : H →* Perm (Fin 462))
    (x y : H) (hxy : Subgroup.closure ({x, y} : Set H) = ⊤) (lab : Fin 462 → Part)
    (hlab : Function.Injective lab) (p₁ p₂ : Perm (Fin 12))
    (hgen : Subgroup.closure ({p₁, p₂} : Set (Perm (Fin 12))) = alternatingGroup (Fin 12))
    (hx : ∀ k, lab (φ x k) = p₁ • lab k) (hy : ∀ k, lab (φ y k) = p₂ • lab k)
    (hcard : Nat.card H ≤ Nat.factorial 12 / 2) :
    Function.Injective φ ∧ Nat.card H = Nat.factorial 12 / 2 := by
  classical
  have hbij : Function.Bijective lab :=
    (Fintype.bijective_iff_injective_and_card lab).2 ⟨hlab, by simp [card_part]⟩
  let ℓ : Fin 462 ≃ Part := Equiv.ofBijective lab hbij
  let Φ : H →* Perm Part := ℓ.permCongrHom.toMonoidHom.comp φ
  have hΦ_apply : ∀ (h : H) (k : Fin 462), Φ h (lab k) = lab (φ h k) := by
    intro h k
    show ℓ (φ h (ℓ.symm (lab k))) = lab (φ h k)
    have : ℓ.symm (lab k) = k := ℓ.symm_apply_eq.2 rfl
    rw [this]; rfl
  have hΦx : Φ x = natHom p₁ := by
    ext S
    obtain ⟨k, rfl⟩ := hbij.2 S
    rw [hΦ_apply, hx]; rfl
  have hΦy : Φ y = natHom p₂ := by
    ext S
    obtain ⟨k, rfl⟩ := hbij.2 S
    rw [hΦ_apply, hy]; rfl
  have hrange : Φ.range = (alternatingGroup (Fin 12)).map natHom := by
    rw [MonoidHom.range_eq_map, ← hxy, MonoidHom.map_closure, Set.image_pair, hΦx, hΦy, ← hgen,
      MonoidHom.map_closure, Set.image_pair]
  have hcardA : Nat.card ((alternatingGroup (Fin 12)).map natHom) = Nat.factorial 12 / 2 := by
    rw [Subgroup.card_map_of_injective natHom_injective, Nat.card_eq_fintype_card,
      card_alternatingGroup, Fintype.card_fin]
  have hle : Nat.card Φ.range ≤ Nat.card H :=
    Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective Φ)
  rw [hrange, hcardA] at hle
  have heq : Nat.card H = Nat.factorial 12 / 2 := le_antisymm hcard hle
  have hΦinj : Function.Injective Φ := by
    have hb := (MonoidHom.rangeRestrict_surjective Φ).bijective_of_nat_card_le
      (by rw [hrange, hcardA, heq])
    intro a b hab
    exact hb.1 (Subtype.ext hab)
  refine ⟨fun a b hab => hΦinj ?_, heq⟩
  show ℓ.permCongrHom (φ a) = ℓ.permCongrHom (φ b)
  rw [hab]

theorem eq_one_of_commute_alt {π : Perm (Fin 12)}
    (h : ∀ σ ∈ alternatingGroup (Fin 12), π * σ = σ * π) : π = 1 := by
  by_contra hne
  let C := Subgroup.centralizer (alternatingGroup (Fin 12) : Set (Perm (Fin 12)))
  have hπ : π ∈ C := Subgroup.mem_centralizer_iff.2 fun σ hσ => (h σ hσ).symm
  have hnt : Nontrivial C := ⟨⟨⟨π, hπ⟩, 1, fun e => hne (congrArg Subtype.val e)⟩⟩
  have hA : alternatingGroup (Fin 12) ≤ C :=
    Equiv.Perm.alternatingGroup_le_of_normal (by simp) hnt
  have hcen : Subgroup.center (alternatingGroup (Fin 12)) = ⊤ := by
    refine eq_top_iff.2 fun σ _ => Subgroup.mem_center_iff.2 fun τ => Subtype.ext ?_
    exact Subgroup.mem_centralizer_iff.1 (hA σ.2) τ τ.2
  rw [alternatingGroup.center_eq_bot (by simp)] at hcen
  exact bot_ne_top hcen

end CFSG.Sporadic.HNSchreier

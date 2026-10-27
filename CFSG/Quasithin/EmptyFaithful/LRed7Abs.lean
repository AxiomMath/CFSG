module

public import CFSG.Quasithin.EmptyFaithful.LRed7Fin
public import CFSG.Quasithin.EmptyFaithful.ModDPencil

public section

namespace CFSG.Quasithin.LRed7

open CFSG.Quasithin CFSG.Quasithin.ModD

variable
  {M : Type} [Group M] [Finite M]

theorem u33_fixbound (hcard : Nat.card M = 2 ^ 6) (φ : U33G →* MulAut M)
    (hirr : ∀ N : Subgroup M, (∀ g : U33G, ∀ n ∈ N, φ g n ∈ N) → N = ⊥ ∨ N = ⊤)
    {z : M} (hz : z ≠ 1) (hz2 : z ^ 2 = 1) (hzT : ∀ g ∈ u33Data.T, φ g z = z)
    (W : Subgroup M) (hW : Nat.card W = 16) :
    Nat.card {g : U33G // ∀ w ∈ W, φ g w = w} ≤ 2 := by
  classical
  have : Fintype M := Fintype.ofFinite M
  have : Finite U33G := finite_u33
  have hstab := stab_eq_A hcard φ hirr hz hz2 hzT
  have hst : ∀ g, φ g z = z ↔ vHom g 0 = 0 := by
    intro g
    have h : g ∈ stabSub φ z ↔ g ∈ stabπ vHom := by rw [hstab, stab_vHom]
    exact h.trans mem_stabπ
  obtain ⟨ε, hε1, hε2, hε3⟩ := exists_label φ z vHom 0 hst
  have hsurj : ∀ j, ∃ g, ε (φ g z) = j := fun j => by
    obtain ⟨g, hg⟩ := vHom_trans j
    exact ⟨g, by rw [hε1]; exact hg⟩
  have horb : ∀ m, m ≠ 1 → ∃ g, φ g z = m :=
    orbit_eq_ne_one φ hz (by rw [hcard]; simp) ε hε2 hsurj
  set Wne : Finset M := (Finset.univ.filter fun w => w ∈ W).erase 1 with hWne
  have hWcard : (Finset.univ.filter fun w => w ∈ W).card = 16 := by
    rw [← hW, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hWne15 : Wne.card = 15 := by
    rw [hWne, Finset.card_erase_of_mem (by simp), hWcard]
  have hWne1 : ∀ w ∈ Wne, w ≠ 1 := fun w hw => (Finset.mem_erase.mp hw).1
  have hWneW : ∀ w ∈ Wne, w ∈ W := fun w hw => by simpa using (Finset.mem_erase.mp hw).2
  set P : Finset (Fin 63) := Wne.image ε with hP
  have hP15 : P.card = 15 := by
    rw [hP, Finset.card_image_of_injOn, hWne15]
    intro a ha b hb hab
    exact hε2 a b (horb a (hWne1 a ha)) (horb b (hWne1 b hb)) hab
  refine le_trans ?_ (fix_card_le P hP15)
  refine Nat.card_le_card_of_injective (fun g => ⟨g.1, fun p hp => ?_⟩) ?_
  · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hp
    have h1 := hε3 g.1 w (horb w (hWne1 w hw))
    rw [g.2 w (hWneW w hw)] at h1
    exact h1.symm
  · intro a b hab
    have h' := congrArg Subtype.val hab
    exact Subtype.ext h'

end CFSG.Quasithin.LRed7

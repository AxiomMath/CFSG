module

public import Mathlib.GroupTheory.NoncommPiCoprod

public section

namespace CFSG.StandardType

theorem q2_block_projection {H : Type} [Group H] {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : ι → Subgroup H) (C : Subgroup H) [Finite ↥C] (hle : ∀ i, G i ≤ C)
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ G i, ∀ y ∈ G j, Commute x y)
    (hsup : ⨆ i, G i = C) (hcard : Nat.card ↥C = ∏ i, Nat.card ↥(G i)) (k : ι) :
    ∃ π : ↥C →* ↥(G k),
      (∀ (x : H) (hx : x ∈ G k), π ⟨x, hle k hx⟩ = ⟨x, hx⟩) ∧
      ∀ i, i ≠ k → ∀ (x : H) (hx : x ∈ G i), π ⟨x, hle i hx⟩ = 1 := by
  classical
  haveI : ∀ i, Finite ↥(G i) := fun i =>
    Finite.of_injective (fun x : ↥(G i) => (⟨x.1, hle i x.2⟩ : ↥C))
      (fun a b h => Subtype.ext (congrArg (fun z : ↥C => z.1) h))
  have hcomm' : Pairwise fun i j => ∀ (x y : H), x ∈ G i → y ∈ G j → Commute x y :=
    fun i j hij x y hx hy => hcomm i j hij x hx y hy
  let φH : ((i : ι) → ↥(G i)) →* H := Subgroup.noncommPiCoprod (G := H) (H := G) hcomm'
  have hrange : φH.range = ⨆ i, G i := by
    simpa [φH] using (Subgroup.noncommPiCoprod_range (G := H) (H := G) (hcomm := hcomm'))
  let φ : ((i : ι) → ↥(G i)) →* ↥C :=
    φH.codRestrict C fun x => by
      have hx : φH x ∈ φH.range := ⟨x, rfl⟩
      rwa [hrange, hsup] at hx
  have hφsurj : Function.Surjective φ := by
    intro y
    have hy : (y : H) ∈ φH.range := by rw [hrange, hsup]; exact y.2
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  have hcard' : Nat.card ((i : ι) → ↥(G i)) = Nat.card ↥C := by
    rw [Nat.card_pi, ← hcard]
  haveI : Fintype ↥C := Fintype.ofFinite _
  haveI : ∀ i, Fintype ↥(G i) := fun i => Fintype.ofFinite _
  have hcardF : Fintype.card ((i : ι) → ↥(G i)) = Fintype.card ↥C := by
    simpa only [Nat.card_eq_fintype_card] using hcard'
  have hbij : Function.Bijective φ := by
    rw [Fintype.bijective_iff_surjective_and_card]
    exact ⟨hφsurj, hcardF⟩
  let e : ((i : ι) → ↥(G i)) ≃* ↥C := MulEquiv.ofBijective φ hbij
  let π : ↥C →* ↥(G k) :=
    (Pi.evalMonoidHom (fun i => ↥(G i)) k).comp e.symm.toMonoidHom
  have hmulSingle : ∀ (i : ι) (x : H) (hx : x ∈ G i),
      φ (Pi.mulSingle i (⟨x, hx⟩ : ↥(G i))) = ⟨x, hle i hx⟩ := by
    intro i x hx
    apply Subtype.ext
    change φH (Pi.mulSingle i (⟨x, hx⟩ : ↥(G i))) = x
    exact Subgroup.noncommPiCoprod_mulSingle (G := H) (H := G) (hcomm := hcomm')
      i (⟨x, hx⟩ : ↥(G i))
  have hsymm : ∀ (i : ι) (x : H) (hx : x ∈ G i),
      e.symm ⟨x, hle i hx⟩ = Pi.mulSingle i (⟨x, hx⟩ : ↥(G i)) := by
    intro i x hx
    have h : e (Pi.mulSingle i (⟨x, hx⟩ : ↥(G i))) = ⟨x, hle i hx⟩ := hmulSingle i x hx
    rw [← h, MulEquiv.symm_apply_apply]
  refine ⟨π, ?_, ?_⟩
  · intro x hx
    change (Pi.evalMonoidHom (fun i => ↥(G i)) k) (e.symm ⟨x, hle k hx⟩) = ⟨x, hx⟩
    rw [hsymm k x hx]
    simp
  · intro i hik x hx
    change (Pi.evalMonoidHom (fun i => ↥(G i)) k) (e.symm ⟨x, hle i hx⟩) = 1
    rw [hsymm i x hx]
    simp [Pi.mulSingle_eq_of_ne, hik]

end CFSG.StandardType

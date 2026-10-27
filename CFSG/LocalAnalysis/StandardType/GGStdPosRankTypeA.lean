module

public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaCard

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open

theorem ggKGPos_card_le_of_typeA (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {p n f : ℕ} (hp : p.Prime) {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hInn : GGInnerDiagOn Bs X)
    (hmod : StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSL (n + 1) 2 f)
    (hpf : p ∣ 2 ^ f - 1) :
    Nat.card ↥Bs ≤ p ^ n * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := by
  have hmark := ggInnerDiagOn_relabel hRig hInn (largeEvenInLambda2_typeA hmod)
    (ggHasLabel_typeA hmod)
  have hmark' := largeEvenMarking_and_labelAll (S := fun lab' => lab' = ⟨.A, n, f⟩)
    (P' := fun R _ I _ => ∀ Y : Subgroup (MulAut R), (Y : Set (MulAut R)) ⊆ I →
      IsElemAbelian p Y → Nat.card Y ≤ p ^ n)
    (fun lab' _ h' => by rw [h']; exact largeEvenLabelAll_rank_typeA hp hpf)
    (fun lab' _ _ _ _ _ hPmark => hPmark.1) hmark
  obtain ⟨hX, lab', -, hraw'⟩ := hmark'
  obtain ⟨R, _, I, _, -, -, θ, hPθ⟩ := largeEvenRawDatum_exists hraw'
  obtain ⟨⟨-, hN, hind⟩, hrank⟩ := hPθ
  have hXI : (((ggBeta X θ hN).range : Subgroup (MulAut R)) : Set (MulAut R)) ⊆ I := by
    rintro _ ⟨b, rfl⟩
    exact ggBeta_mem X θ hN hind b
  have hle := hrank _ hXI (isElemAbelian_range_ggBeta θ hBs hN)
  have hker : (ggBeta X θ hN).ker = (Bs ⊓ Subgroup.centralizer (X : Set G)).subgroupOf Bs := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h1
      exact ⟨b.2, mem_centralizer_of_ggLAut_eq_one X θ hX (g := ⟨b, hN b.2⟩) h1⟩
    · rintro ⟨-, hc⟩
      exact ggLAut_eq_one_of_mem_centralizer X θ (g := ⟨b, hN b.2⟩) hc
  have hcardker : Nat.card (ggBeta X θ hN).ker =
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have h2 := TableB.card_range_mul_card_ker (ggBeta X θ hN)
  rw [hcardker] at h2
  calc Nat.card ↥Bs = Nat.card (ggBeta X θ hN).range *
        Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := h2.symm
    _ ≤ p ^ n * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := Nat.mul_le_mul_right _ hle

end CFSG.StandardType

end

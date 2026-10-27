module

public import CFSG.Monster.GMS.Leech.Count
public import CFSG.Monster.GMS.Facts.Section4Coh
import CFSG.Monster.GMS.LeechCohGroup
import CFSG.Monster.GMS.Griess13.ChecksUniqueness

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

namespace LeechCoh

variable {G : Type*} [Group G] {z : G}

theorem image_mono (L : LeechSystem z) {D M : Subgroup G} (h : M ≤ D) : L.image M ≤ L.image D := by
  intro x hx
  obtain ⟨c, hc, rfl⟩ := L.mem_image.1 hx
  exact L.mem_image.2 ⟨c, h hc, rfl⟩

theorem card_le_eight_mul [Finite G] (L : LeechSystem z)
    {D M : Subgroup G} (hD : D ≤ Subgroup.centralizer ({z} : Set G)) (hMD : M ≤ D)
    (hu : ∀ s ∈ M, ∀ s' ∈ M, orderOf s = 2 → orderOf s' = 2 → s = s') :
    Nat.card M ≤ 8 * Nat.card (L.image D) := by
  have hfin : Finite Co1 := Finite.of_surjective L.φ L.φ_surj
  have h1 := L.card_eq_card_image_mul M (hMD.trans hD)
  have h2 : Nat.card (L.image M) ≤ Nat.card (L.image D) :=
    Subgroup.card_le_of_le (image_mono L hMD)
  have h3 : Nat.card ↥(leechQ z ⊓ M) ≤ 8 := by
    refine card_le_eight (leechQ z ⊓ M) (fun g hg => ?_) (fun s hs s' hs' h h' => ?_)
    · rcases L.extraspecial.sq g (Subgroup.mem_inf.mp hg).1 with h | h
      · rw [h, one_mul]
      · rw [h, L.z_mul_self]
    · exact hu s (Subgroup.mem_inf.mp hs).2 s' (Subgroup.mem_inf.mp hs').2 h h'
  calc Nat.card M = Nat.card (L.image M) * Nat.card ↥(leechQ z ⊓ M) := h1
    _ ≤ Nat.card (L.image D) * 8 := Nat.mul_le_mul h2 h3
    _ = 8 * Nat.card (L.image D) := mul_comm _ _

theorem card_image_threeC (L : LeechSystem z) {b x : G} (hk : LeechOddType z b x 1) :
    Nat.card (L.image (Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer {b} ⊓
      Subgroup.centralizer {x})) = 181440 := by
  obtain ⟨-, hQ, hH⟩ := hk
  set D : Subgroup G := Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer {b} ⊓
    Subgroup.centralizer {x} with hD
  have hDz : D ≤ Subgroup.centralizer ({z} : Set G) := inf_le_left.trans inf_le_left
  have hQD : leechQ z ⊓ D = leechQ z ⊓ Subgroup.centralizer {b} ⊓ Subgroup.centralizer {x} := by
    ext g
    simp only [hD, Subgroup.mem_inf]
    constructor
    · rintro ⟨hg, ⟨-, hb⟩, hx⟩
      exact ⟨⟨hg, hb⟩, hx⟩
    · rintro ⟨⟨hg, hb⟩, hx⟩
      exact ⟨hg, ⟨L.mem_centralizer hg, hb⟩, hx⟩
  have h := L.card_eq_card_image_mul D hDz
  rw [hH, hQD, hQ] at h
  omega

end LeechCoh

theorem threeCTripleCore_of
    {d₀ : B} {G : Type} [Group G] [Finite G] {a z₀ : G}
    (hG : GMSF1Type d₀ a z₀) : ThreeCTripleCore a z₀ := by
  intro b x w _ hx hw hwC M hM hu
  obtain ⟨L⟩ := exists_leechSystem co1ModuleUniqueness (hG.2.of_isConj hw)
  have hk : LeechOddType w b x 1 := hx.2 w hwC hw
  have hD := LeechCoh.card_image_threeC L hk
  have hMD : M ≤ Subgroup.centralizer ({w} : Set G) ⊓ Subgroup.centralizer {b} ⊓
      Subgroup.centralizer {x} := by
    intro g hg
    have h := Subgroup.mem_inf.mp (hM hg)
    have h' := Subgroup.mem_inf.mp h.1
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨h.2, h'.1⟩, h'.2⟩
  have := LeechCoh.card_le_eight_mul L (inf_le_left.trans inf_le_left) hMD hu
  rw [hD] at this
  exact this.trans (by unfold threeCLineBound; omega)

end CFSG.Monster.GMS

module

public import CFSG.Quasithin.Background.B1MoreTenD
public import CFSG.Quasithin.Background.B69Cent

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B69

variable {V : Type} [CommGroup V] [Finite V]

@[expose] def blk (X L : Subgroup (MulAut V)) : Subgroup (MulAut V) :=
  L ⊔ ⨆ (A : Subgroup (MulAut V)) (_ : IsFFStarMin X A ∧ ⁅L, A⁆ = L), A

omit [Finite V] in
theorem le_blk_self {X L : Subgroup (MulAut V)} : L ≤ blk X L := le_sup_left

omit [Finite V] in
theorem le_blk_of {X L A : Subgroup (MulAut V)} (hA : IsFFStarMin X A) (hLA : ⁅L, A⁆ = L) :
    A ≤ blk X L :=
  le_sup_of_le_right (le_iSup₂_of_le (f := fun (A : Subgroup (MulAut V))
    (_ : IsFFStarMin X A ∧ ⁅L, A⁆ = L) => A) A ⟨hA, hLA⟩ le_rfl)

omit [Finite V] in
theorem blk_le_iff {X L H : Subgroup (MulAut V)} :
    blk X L ≤ H ↔ L ≤ H ∧ ∀ A : Subgroup (MulAut V), IsFFStarMin X A → ⁅L, A⁆ = L → A ≤ H := by
  unfold blk
  rw [sup_le_iff, iSup₂_le_iff]
  exact and_congr_right fun _ => ⟨fun h A hA hLA => h A ⟨hA, hLA⟩, fun h A hA => h A hA.1 hA.2⟩

omit [Finite V] in
theorem isFFStarMin_conjSub {X A : Subgroup (MulAut V)} (hA : IsFFStarMin X A) {g : MulAut V}
    (hg : g ∈ X) : IsFFStarMin X (B6.conjSub g A) := by
  have e : ∀ A : Subgroup (MulAut V), B6.conjSub g A = B1.conjAut g A := fun A =>
    Subgroup.ext fun x => by rw [B6.mem_conjSub, B1.mem_conjAut]
  rw [e]
  refine ⟨B1.isFFStarOffender_conjAut hA.1 hg, fun B hB hBA => ?_⟩
  have hB' : IsFFStarOffender X (B1.conjAut g⁻¹ B) :=
    B1.isFFStarOffender_conjAut hB (X.inv_mem hg)
  have hBA' : FFLe X (B1.conjAut g⁻¹ B) A := by
    have := B1.ffLe_conjAut hBA (X.inv_mem hg)
    rwa [B1.conjAut_inv_conjAut] at this
  have := hA.2 _ hB' hBA'
  rw [← B1.conjAut_conjAut_inv g B, this]

omit [Finite V] in
theorem commutator_conjSub (g : MulAut V) (L A : Subgroup (MulAut V)) :
    ⁅B6.conjSub g L, B6.conjSub g A⁆ = B6.conjSub g ⁅L, A⁆ := by
  show ⁅L.map (MulAut.conj g).toMonoidHom, A.map (MulAut.conj g).toMonoidHom⁆ =
    (⁅L, A⁆).map (MulAut.conj g).toMonoidHom
  rw [Subgroup.map_commutator]

omit [Finite V] in
theorem conjSub_inv_conjSub (g : MulAut V) (L : Subgroup (MulAut V)) :
    B6.conjSub g⁻¹ (B6.conjSub g L) = L := by
  rw [← B6.conjSub_mul, inv_mul_cancel, B6.conjSub_one]

omit [Finite V] in
theorem conjSub_conjSub_inv (g : MulAut V) (L : Subgroup (MulAut V)) :
    B6.conjSub g (B6.conjSub g⁻¹ L) = L := by
  rw [← B6.conjSub_mul, mul_inv_cancel, B6.conjSub_one]

omit [Finite V] in
theorem conjSub_blk {X L : Subgroup (MulAut V)} {g : MulAut V} (hg : g ∈ X) :
    B6.conjSub g (blk X L) = blk X (B6.conjSub g L) := by
  unfold blk
  simp only [OrderIso.map_sup, OrderIso.map_iSup]
  congr 1
  apply le_antisymm
  · refine iSup₂_le fun A hA => le_iSup₂_of_le (B6.conjSub g A)
      ⟨isFFStarMin_conjSub hA.1 hg, ?_⟩ le_rfl
    rw [commutator_conjSub, hA.2]
  · refine iSup₂_le fun A' hA' => ?_
    refine le_iSup₂_of_le (B6.conjSub g⁻¹ A')
      ⟨isFFStarMin_conjSub hA'.1 (X.inv_mem hg), ?_⟩ (conjSub_conjSub_inv g A').ge
    have h1 := commutator_conjSub g⁻¹ (B6.conjSub g L) A'
    rw [hA'.2, conjSub_inv_conjSub] at h1
    exact h1

omit [Finite V] in
theorem blk_le_X {X L : Subgroup (MulAut V)} (hL : CFSG.Open.IsComponentOf L X) : blk X L ≤ X :=
  blk_le_iff.2 ⟨hL.1, fun _ hA _ => hA.1.1⟩

omit [Finite V] in
theorem blk_le_ffJ {X L : Subgroup (MulAut V)} (hL : CFSG.Open.IsComponentOf L X)
    (hact : ∃ A, IsFFStarMin X A ∧ ⁅L, A⁆ = L) : blk X L ≤ ffJ X := by
  obtain ⟨A₀, hA₀, hLA₀⟩ := hact
  exact blk_le_iff.2 ⟨B1Red.K_le_ffJ hL.1 hA₀.1 hLA₀, fun _ hA _ => B6.le_ffJ hA.1⟩

theorem commV_mem_irrPlus (hV : ∀ v : V, v ^ 2 = 1) {X T M A L : Subgroup (MulAut V)}
    (hctx : ShapeCtx X T M) (hA : IsFFStarMin X A) (hL : CFSG.Open.IsComponentOf L X)
    (hLA : ⁅L, A⁆ = L) : commV L ∈ IrrPlus L (⊤ : Subgroup V) := by
  obtain ⟨W, hW⟩ := exists_irrPlus hL.2.2
  obtain ⟨hcV, -⟩ := commV_eq_of_shape hV hA hL.2.2 hLA hW (hctx A L hA hL hLA W hW)
  rw [hcV]
  exact hW

theorem blk_le_centQuot (hV : ∀ v : V, v ^ 2 = 1) {X T M L : Subgroup (MulAut V)}
    (hctx : ShapeCtx X T M) (hL : CFSG.Open.IsComponentOf L X)
    (hact : ∃ A, IsFFStarMin X A ∧ ⁅L, A⁆ = L) : blk X L ≤ centQuot (commV L) := by
  obtain ⟨A₀, hA₀, hLA₀⟩ := hact
  obtain ⟨W, hW⟩ := exists_irrPlus hL.2.2
  have key : ∀ A : Subgroup (MulAut V), IsFFStarMin X A → ⁅L, A⁆ = L →
      commV L = W ∧ A ≤ centQuot W ∧ L ≤ centQuot W := fun A hA hLA => by
    obtain ⟨h1, -, -, h4, h5⟩ := commV_eq_of_shape hV hA hL.2.2 hLA hW (hctx A L hA hL hLA W hW)
    exact ⟨h1, h4, h5⟩
  obtain ⟨hc, -, hLc⟩ := key A₀ hA₀ hLA₀
  rw [hc]
  exact blk_le_iff.2 ⟨hLc, fun A hA hLA => (key A hA hLA).2.1⟩

omit [Finite V] in
theorem commV_blk_eq {X L : Subgroup (MulAut V)} (h : blk X L ≤ centQuot (commV L)) :
    commV (blk X L) = commV L := by
  apply le_antisymm
  · rw [commV_eq_commSub, commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, v, -, rfl⟩
    exact h hx v
  · rw [commV_eq_commSub, commV_eq_commSub]
    exact commSub_mono le_rfl le_blk_self

theorem blk_le_centSub (hV : ∀ v : V, v ^ 2 = 1) (hP4 : AsB15Part4) {X T M L L' : Subgroup (MulAut V)}
    (hctx : ShapeCtx X T M) (hL : CFSG.Open.IsComponentOf L X) (hL' : CFSG.Open.IsComponentOf L' X)
    (hact' : ∃ A, IsFFStarMin X A ∧ ⁅L', A⁆ = L') (hne : L ≠ L') :
    blk X L ≤ centSub (commV L') := by
  obtain ⟨A₀, hA₀, hLA₀⟩ := hact'
  have hI : commV L' ∈ IrrPlus L' (⊤ : Subgroup V) := commV_mem_irrPlus hV hctx hA₀ hL' hLA₀
  refine blk_le_iff.2 ⟨?_, fun A hA hLA => ?_⟩
  · intro l hl w hw
    exact comm_trivial_on_commV hV hL.2.2 (L := L') (components_mul_comm_of_ne hL' hL hne.symm) hI
      l hl w hw
  · intro a ha w hw
    exact trivial_on_commV_of_offender hV hP4 hctx hA hL' hL hLA hne.symm hI a ha w hw

theorem blk_commute (hV : ∀ v : V, v ^ 2 = 1) (hP4 : AsB15Part4) {X T M L L' : Subgroup (MulAut V)}
    (hctx : ShapeCtx X T M) (hL : CFSG.Open.IsComponentOf L X) (hL' : CFSG.Open.IsComponentOf L' X)
    (hne : L ≠ L') : ∀ x ∈ blk X L, ∀ y ∈ blk X L', x * y = y * x := by
  have h1 : ∀ A : Subgroup (MulAut V), IsFFStarMin X A → ⁅L, A⁆ = L →
      blk X L' ≤ Subgroup.centralizer (A : Set (MulAut V)) := by
    intro A hA hLA
    refine blk_le_iff.2 ⟨fun y hy => ?_, fun A' hA' hLA' a' ha' => ?_⟩
    · refine Subgroup.mem_centralizer_iff.2 fun a ha => ?_
      exact (mul_comm_of_commutator_eq_bot (commutator_eq_bot_of_ne hV hP4 hctx hA hL hLA hL' hne)
        y hy a ha).symm
    · refine Subgroup.mem_centralizer_iff.2 fun a ha => ?_
      exact offenders_commute hV hP4 hctx hA hA' hL hLA hL' hLA' hne a ha a' ha'
  have h2 : blk X L' ≤ Subgroup.centralizer (L : Set (MulAut V)) := by
    refine blk_le_iff.2 ⟨fun y hy => ?_, fun A' hA' hLA' a' ha' => ?_⟩
    · exact Subgroup.mem_centralizer_iff.2 fun l hl =>
        (components_mul_comm_of_ne hL hL' hne y hy l hl).symm
    · exact Subgroup.mem_centralizer_iff.2 fun l hl =>
        mul_comm_of_commutator_eq_bot
          (commutator_eq_bot_of_ne hV hP4 hctx hA' hL' hLA' hL hne.symm) l hl a' ha'
  have h3 : blk X L ≤ Subgroup.centralizer (blk X L' : Set (MulAut V)) := by
    refine blk_le_iff.2 ⟨?_, fun A hA hLA => ?_⟩
    · exact Subgroup.le_centralizer_iff.2 h2
    · exact Subgroup.le_centralizer_iff.2 (h1 A hA hLA)
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.1 (h3 hx) y hy).symm

end B69

end CFSG.Quasithin

module

public import CFSG.Timmesfeld.Transvection.OddSU3Chord
public import CFSG.Timmesfeld.Transvection.FrameResidue
public import CFSG.Timmesfeld.Transvection.GenerateRel
import CFSG.Timmesfeld.Transvection.OddSU3Torus
import CFSG.Timmesfeld.Transvection.LineStabTorus
import CFSG.Timmesfeld.Transvection.ShortRootProduct
import CFSG.Timmesfeld.Transvection.ShortRootTorus
import CFSG.Timmesfeld.Transvection.RankThreeA2Coords
import CFSG.Timmesfeld.Transvection.Small
import CFSG.CGT.PushingUpLit.SYMB.ProdCard

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg
open CFSG.LocalAnalysis.UniquenessCase CFSG.LieType.BorelTits
open CFSG.Timmesfeld.Transvection.Pres

variable {H : Type} [Group H] {Δ : Set (Subgroup H)} {r : ℕ} {P Q : Fin r → Subgroup H}
  {k : Fin r} {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

theorem SURelations.HasFrameImages.map_su3Top_of_suLong {σ : F ≃+* F}
    {R : SURelations r σ H} (hR : R.HasFrameImages Δ P Q) (j : Fin r) {θ : SU σ 3 →* H}
    (hθ : ∀ c, σ c = c →
      θ (suLong σ (Sum.inl (0 : Fin (3 / 2))) c) = R.ξL (Sum.inl j) c ∧
        θ (suLong σ (Sum.inr (0 : Fin (3 / 2))) c) = R.ξL (Sum.inr j) c) :
    (su3Top σ).map θ = P j ∧ (su3Bot σ).map θ = Q j := by
  constructor
  · apply le_antisymm
    · rintro - ⟨x, hx, rfl⟩
      obtain ⟨c, hc, rfl⟩ := (mem_su3Top_iff (σ := σ)).1 hx
      rw [(hθ c hc).1]
      exact (hR.long (Sum.inl j) _).2 ⟨c, hc, rfl⟩
    · intro y hy
      obtain ⟨c, hc, rfl⟩ := (hR.long (Sum.inl j) y).1 (by simpa [framePt] using hy)
      exact ⟨suLong σ (Sum.inl (0 : Fin (3 / 2))) c,
        (mem_su3Top_iff (σ := σ)).2 ⟨c, hc, rfl⟩, (hθ c hc).1⟩
  · apply le_antisymm
    · rintro - ⟨x, hx, rfl⟩
      obtain ⟨c, hc, rfl⟩ := (mem_su3Bot_iff (σ := σ)).1 hx
      rw [(hθ c hc).2]
      exact (hR.long (Sum.inr j) _).2 ⟨c, hc, rfl⟩
    · intro y hy
      obtain ⟨c, hc, rfl⟩ := (hR.long (Sum.inr j) y).1 (by simpa [framePt] using hy)
      exact ⟨suLong σ (Sum.inr (0 : Fin (3 / 2))) c,
        (mem_su3Bot_iff (σ := σ)).2 ⟨c, hc, rfl⟩, (hθ c hc).2⟩

theorem commuting_map_heis_of_ne {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) {θ : SU σ 3 →* H}
    (hθr : θ.range = residueGroup Δ P Q k) {i : Fin r} (hik : i ≠ k) :
    Commuting ((UC22.uc22pwsu3X hσ).map θ) (P i ⊔ Q i) :=
  (commuting_residueGroup (Δ := Δ) (P := P) (Q := Q) hik).mono
    ((Subgroup.map_le_range θ _).trans hθr.le) le_rfl

theorem map_heis_le_lineStab (h : TransvectionHyp H Δ) (hML : MeetsLines Δ)
    (hFn : Nat.card F = (2 ^ n) ^ 2) (hn : 2 ≤ n) {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    {A E : Subgroup H} (hA : A ∈ Δ) (hE : E ∈ Δ) (hEA : Opposite E A)
    (hθt : (su3Top (unitaryInvolution F 2 n)).map θ = A)
    (hθb : (su3Bot (unitaryInvolution F 2 n)).map θ = E) {C : Subgroup H} (hC : C ∈ Δ)
    (hCA : C ≠ A) (hAC : Commuting A C) :
    (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ ≤ lineStab Δ A C := by
  haveI := h.finite
  obtain ⟨s, hs, hsA, -, hK⟩ := exists_torus_map_heis hFn hn hθt hθb
  exact le_lineStab_of_forall_eq_commutatorElement h.cls h.points hML hA hE hEA hC hCA hAC hs
    hsA (fun y hy => conjSub_eq_of_mem_map_heis (unitaryInvolution_involutive hFn) hθt hy) hK

theorem IsFrame.sup_le_lineStab (h : TransvectionHyp H Δ) (hML : MeetsLines Δ)
    (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsFrame Δ P Q) (hFn : Nat.card F = (2 ^ n) ^ 2)
    (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n) {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθt : (su3Top (unitaryInvolution F 2 n)).map θ = P k)
    (hθb : (su3Bot (unitaryInvolution F 2 n)).map θ = Q k) {i : Fin r} (hik : i ≠ k)
    {C : Subgroup H} (hC : C ∈ Δ) (hCP : C ≠ P k) (hPC : Commuting (P k) C) :
    (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ ⊔
        (shortRootGroup Δ (P k) (Q k) (Q i) (P i) ⊔
          shortRootGroup Δ (P k) (Q k) (P i) (Q i) ⊔ P k) ≤ lineStab Δ (P k) C := by
  haveI := h.finite
  refine sup_le ?_ (sup_le (sup_le ?_ ?_) ?_)
  · exact map_heis_le_lineStab h hML hFn (by
      by_contra hlt
      have h2 : 2 ^ n ≤ 2 := by
        simpa using Nat.pow_le_pow_right (by norm_num) (by omega : n ≤ 1)
      have hq' := hq (P k) (hF.memP k)
      have hcard' := hcard (P k) (hF.memP k)
      omega) (hF.memP k) (hF.memQ k) (hF.opposite k).symm hθt hθb hC hCP hPC
  · exact PairFrame.shortRootGroup_le_lineStab ((hF.toPairFrame (Ne.symm hik)).flip')
      h.cls h.points hML (hq (P k) (hF.memP k)) hC hCP hPC
  · exact PairFrame.shortRootGroup_le_lineStab (hF.toPairFrame (Ne.symm hik))
      h.cls h.points hML (hq (P k) (hF.memP k)) hC hCP hPC
  · exact (le_lineGroup (left_mem_lineOf (hF.memP k))).trans
      (lineGroup_le_lineStab h.cls (hF.memP k) hC hPC)

theorem IsFrame.commuting_map_heis_shortRootGroup (h : TransvectionHyp H Δ)
    (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsFrame Δ P Q)
    (hFn : Nat.card F = (2 ^ n) ^ 2) (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n)
    {θ : SU (unitaryInvolution F 2 n) 3 →* H} (hθr : θ.range = residueGroup Δ P Q k)
    (hθt : (su3Top (unitaryInvolution F 2 n)).map θ = P k)
    (hθb : (su3Bot (unitaryInvolution F 2 n)).map θ = Q k) {i : Fin r} (hik : i ≠ k) :
    Commuting ((UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ)
        (shortRootGroup Δ (P k) (Q k) (Q i) (P i)) ∧
      Commuting ((UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ)
        (shortRootGroup Δ (P k) (Q k) (P i) (Q i)) := by
  haveI := h.finite
  have hn : 2 ≤ n := by
    by_contra hlt
    have h2 : 2 ^ n ≤ 2 := by
      simpa using Nat.pow_le_pow_right (by norm_num) (by omega : n ≤ 1)
    have hq' := hq (P k) (hF.memP k)
    have hcard' := hcard (P k) (hF.memP k)
    omega
  obtain ⟨s, hs, hsA, hsE, hK⟩ := exists_torus_map_heis hFn hn hθt hθb
  have hKD : Commuting ((UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ)
      (P i ⊔ Q i) :=
    commuting_map_heis_of_ne (unitaryInvolution_involutive hFn) hθr hik
  have hKA : ∀ y ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ,
      conjSub (P k) y = P k := fun y hy =>
    conjSub_eq_of_mem_map_heis (unitaryInvolution_involutive hFn) hθt hy
  have hthick : ThickLines Δ := thickLines_of_meetsLines h.cls h.center hML
  constructor
  · have hc := PairFrame.commuting_shortRootGroup_of_forall_eq_commutatorElement
      ((hF.toPairFrame (Ne.symm hik)).flip') h.cls h.points hML hthick
      (hq (P k) (hF.memP k)) hs hsA hsE hKA (by simpa [sup_comm] using hKD) hK
    simpa using hc
  · have hc := PairFrame.commuting_shortRootGroup_of_forall_eq_commutatorElement
      (hF.toPairFrame (Ne.symm hik)) h.cls h.points hML hthick
      (hq (P k) (hF.memP k)) hs hsA hsE hKA hKD hK
    simpa using hc

theorem IsFrame.commuting_map_heis_sup (h : TransvectionHyp H Δ) (hML : MeetsLines Δ)
    (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsFrame Δ P Q) (hFn : Nat.card F = (2 ^ n) ^ 2)
    (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n) {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθr : θ.range = residueGroup Δ P Q k)
    (hθt : (su3Top (unitaryInvolution F 2 n)).map θ = P k)
    (hθb : (su3Bot (unitaryInvolution F 2 n)).map θ = Q k) {i : Fin r} (hik : i ≠ k) :
    Commuting ((UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ)
      (shortRootGroup Δ (P k) (Q k) (Q i) (P i) ⊔
        shortRootGroup Δ (P k) (Q k) (P i) (Q i) ⊔ P k) := by
  obtain ⟨h1, h2⟩ :=
    IsFrame.commuting_map_heis_shortRootGroup h hML hq hF hFn hcard hθr hθt hθb hik
  have h3 : Commuting ((UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ) (P k) := by
    rw [← hθt]
    exact commuting_map_heis_map_su3Top (unitaryInvolution_involutive hFn) θ
  exact (h1.sup_right h2).sup_right h3

theorem IsFrame.map_heis_inf_sup_shortRootGroup (h : TransvectionHyp H Δ)
    (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsFrame Δ P Q) (hFn : Nat.card F = (2 ^ n) ^ 2)
    {θ : SU (unitaryInvolution F 2 n) 3 →* H} (hθr : θ.range = residueGroup Δ P Q k)
    (hθt : (su3Top (unitaryInvolution F 2 n)).map θ = P k) {i : Fin r} (hik : i ≠ k) :
    (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ ⊓
        (shortRootGroup Δ (P k) (Q k) (Q i) (P i) ⊔
          shortRootGroup Δ (P k) (Q k) (P i) (Q i) ⊔ P k) = P k := by
  haveI := h.finite
  refine le_antisymm ?_ ?_
  · intro w hw
    have hw' : w ∈ shortRootGroup Δ (Q i) (P i) (P k) (Q k) ⊔
        shortRootGroup Δ (P i) (Q i) (P k) (Q k) ⊔ P k := by
      simpa [shortRootGroup_swap_pairs (Q i) (P i) (P k) (Q k),
        shortRootGroup_swap_pairs (P i) (Q i) (P k) (Q k)] using hw.2
    have hKD : Commuting ((UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ)
        (P i ⊔ Q i) :=
      commuting_map_heis_of_ne (unitaryInvolution_involutive hFn) hθr hik
    have hwA : conjSub (P i) w = P i :=
      conjSub_of_forall_commute fun a ha => hKD w hw.1 a (Subgroup.mem_sup_left ha)
    have hwE : conjSub (Q i) w = Q i :=
      conjSub_of_forall_commute fun a ha => hKD w hw.1 a (Subgroup.mem_sup_right ha)
    exact (hF.toPairFrame hik).mem_of_mem_sup_of_conjSub_eq h.cls h.points
      (hq (P i) (hF.memP i)) hw' hwA hwE
  · refine le_inf ?_ le_sup_right
    rw [← hθt]
    exact Subgroup.map_mono (su3Top_le_X (unitaryInvolution_involutive hFn))

theorem IsFrame.card_sup_shortRootGroup (h : TransvectionHyp H Δ)
    (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsFrame Δ P Q) {i : Fin r} (hik : i ≠ k) :
    Nat.card ↥(shortRootGroup Δ (P k) (Q k) (Q i) (P i) ⊔
        shortRootGroup Δ (P k) (Q k) (P i) (Q i) ⊔ P k) =
      Nat.card ↥(shortRootGroup Δ (P k) (Q k) (Q i) (P i)) *
        Nat.card ↥(shortRootGroup Δ (P k) (Q k) (P i) (Q i)) * Nat.card (P k) := by
  haveI := h.finite
  have hcard := (hF.toPairFrame hik).card_sup_shortRootGroup h.cls h.points
    (hq (P i) (hF.memP i))
  simpa [shortRootGroup_swap_pairs (Q i) (P i) (P k) (Q k),
    shortRootGroup_swap_pairs (P i) (Q i) (P k) (Q k)] using hcard

theorem IsFrame.card_map_heis_sup_mul (h : TransvectionHyp H Δ) (hML : MeetsLines Δ)
    (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsFrame Δ P Q) (hFn : Nat.card F = (2 ^ n) ^ 2)
    (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n) {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθr : θ.range = residueGroup Δ P Q k)
    (hθt : (su3Top (unitaryInvolution F 2 n)).map θ = P k)
    (hθb : (su3Bot (unitaryInvolution F 2 n)).map θ = Q k) {i : Fin r} (hik : i ≠ k) :
    Nat.card ↥((UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ ⊔
        (shortRootGroup Δ (P k) (Q k) (Q i) (P i) ⊔
          shortRootGroup Δ (P k) (Q k) (P i) (Q i) ⊔ P k)) * Nat.card (P k) =
      Nat.card ↥((UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ) *
        Nat.card ↥(shortRootGroup Δ (P k) (Q k) (Q i) (P i) ⊔
          shortRootGroup Δ (P k) (Q k) (P i) (Q i) ⊔ P k) := by
  haveI := h.finite
  have hcomm := IsFrame.commuting_map_heis_sup h hML hq hF hFn hcard hθr hθt hθb hik
  have hprod := CFSG.CGT.PushingUpLit.SYMB.card_sup_mul_card_inf_of_commute
    (C := (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ)
    (D := shortRootGroup Δ (P k) (Q k) (Q i) (P i) ⊔
      shortRootGroup Δ (P k) (Q k) (P i) (Q i) ⊔ P k)
    (fun c hc d hd => (hcomm c hc d hd).eq)
  rwa [IsFrame.map_heis_inf_sup_shortRootGroup h hq hF hFn hθr hθt hik] at hprod

theorem commuting_residueGroup_lineGroup {a b : Fin r ⊕ Fin r} (ha : idx a ≠ k)
    (hb : idx b ≠ k) :
    Commuting (residueGroup Δ P Q k) (lineGroup Δ (framePt P Q a) (framePt P Q b)) := by
  have hXa : ∀ X ∈ frameResidue Δ P Q k, Commuting X (framePt P Q a) := by
    intro X hX
    rcases a with j | j
    · simpa [framePt] using (hX.2 j (by simpa [idx] using ha)).1
    · simpa [framePt] using (hX.2 j (by simpa [idx] using ha)).2
  have hXb : ∀ X ∈ frameResidue Δ P Q k, Commuting X (framePt P Q b) := by
    intro X hX
    rcases b with j | j
    · simpa [framePt] using (hX.2 j (by simpa [idx] using hb)).1
    · simpa [framePt] using (hX.2 j (by simpa [idx] using hb)).2
  refine (commuting_iff_le_centralizer (A := residueGroup Δ P Q k)
    (B := lineGroup Δ (framePt P Q a) (framePt P Q b))).2 ?_
  refine iSup₂_le fun C hC => ?_
  refine (commuting_iff_le_centralizer (A := residueGroup Δ P Q k) (B := C)).1 ?_
  refine Commuting.symm ?_
  refine (commuting_iff_le_centralizer (A := C) (B := residueGroup Δ P Q k)).2 ?_
  refine iSup₂_le fun X hX => ?_
  exact (commuting_iff_le_centralizer (A := C) (B := X)).1
    (Commuting.symm (hC.2 X hX.1 (hXa X hX) (hXb X hX)))

end CFSG.Timmesfeld.Transvection

module

public import CFSG.Timmesfeld.Transvection.OddPairs
public import CFSG.Timmesfeld.Transvection.OddResidueBlockPrev
import CFSG.Timmesfeld.Transvection.OddLocal
import CFSG.Timmesfeld.Transvection.OddPairsModel

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.Timmesfeld.Transvection.Pres

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ} (hFn : Nat.card F = (2 ^ n) ^ 2)
  {r : ℕ} (hr : 2 ≤ r) {H : Type} [Group H] {Δ : Set (Subgroup H)}
  {P Q : Fin (2 * r / 2) → Subgroup H} (hm : 4 ≤ 2 * r)

theorem cPrevIdx_ne_cLastIdx {r : ℕ} (hr : 2 ≤ r) :
    cPrevIdx r hr ≠ cLastIdx r hr := by
  intro h
  have hval := congrArg Fin.val h
  simp only [cPrevIdx, cLastIdx, Fin.val_mk] at hval
  omega

private theorem long_last_of_comp_su3Chord
    {R : SURelations (2 * r / 2) (unitaryInvolution F 2 n) H}
    {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθc : θ.comp (su3Chord (unitaryInvolution F 2 n)) = R.lastBlock hFn (even_two_mul r) hm) :
    ∀ c, unitaryInvolution F 2 n c = c →
      (R.toHom hFn (even_two_mul r) hm) (suLong (unitaryInvolution F 2 n)
          (Sum.inl (cLastIdx r hr)) c) =
        θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) c) ∧
      (R.toHom hFn (even_two_mul r) hm) (suLong (unitaryInvolution F 2 n)
          (Sum.inr (cLastIdx r hr)) c) =
        θ (suLong (unitaryInvolution F 2 n) (Sum.inr (0 : Fin (3 / 2))) c) := by
  intro c hc
  constructor
  · have h1 : θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) c) =
        R.ξL (Sum.inl (cLastIdx r hr)) c := by
      have h := congrArg (fun f : SU (unitaryInvolution F 2 n) 2 →* H =>
        f (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (2 / 2))) c)) hθc
      simp only [MonoidHom.comp_apply] at h
      rw [su3Chord_suLong_inl, R.lastBlock_suLong_inl hFn (even_two_mul r) hm hc] at h
      exact h
    rw [h1]
    exact R.toHom_suLong hFn (even_two_mul r) hm (Sum.inl (cLastIdx r hr)) hc
  · have h1 : θ (suLong (unitaryInvolution F 2 n) (Sum.inr (0 : Fin (3 / 2))) c) =
        R.ξL (Sum.inr (cLastIdx r hr)) c := by
      have h := congrArg (fun f : SU (unitaryInvolution F 2 n) 2 →* H =>
        f (suLong (unitaryInvolution F 2 n) (Sum.inr (0 : Fin (2 / 2))) c)) hθc
      simp only [MonoidHom.comp_apply] at h
      rw [su3Chord_suLong_inr, R.lastBlock_suLong_inr hFn (even_two_mul r) hm hc] at h
      exact h
    rw [h1]
    exact R.toHom_suLong hFn (even_two_mul r) hm (Sum.inr (cLastIdx r hr)) hc

private theorem commute_short_of_hasFrameImages
    {R : SURelations (2 * r / 2) (unitaryInvolution F 2 n) H} (hR : R.HasFrameImages Δ P Q)
    {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθr : θ.range = residueGroup Δ P Q (cLastIdx r hr)) :
    ∀ i : Fin (2 * r / 2), i.val + 3 ≤ r →
      ∀ x ∈ CFSG.LieType.CurtisTits.rankOne (CFSG.LieType.Universal.Unitary.rootGroup
        (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn) (2 * r)) i,
        ∀ A, Commute ((R.toHom hFn (even_two_mul r) hm) x) (θ A) := by
  intro i hi x hx A
  have hk : i.val + 1 < 2 * r / 2 := by omega
  have hne_i : i ≠ cLastIdx r hr := by
    intro h
    have hval := congrArg Fin.val h
    simp only [cLastIdx, Fin.val_mk] at hval
    omega
  have hne_s : (⟨i.val + 1, hk⟩ : Fin (2 * r / 2)) ≠ cLastIdx r hr := by
    intro h
    have hval := congrArg Fin.val h
    simp only [cLastIdx, Fin.val_mk] at hval
    omega
  have hθA : ∀ A, θ A ∈ residueGroup Δ P Q (cLastIdx r hr) := by
    intro A
    rw [← hθr]
    exact ⟨A, rfl⟩
  have hle : CFSG.LieType.CurtisTits.rankOne (CFSG.LieType.Universal.Unitary.rootGroup
      (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn) (2 * r)) i ≤
      (Subgroup.centralizer (residueGroup Δ P Q (cLastIdx r hr))).comap
        (R.toHom hFn (even_two_mul r) hm) := by
    rw [CFSG.LieType.CurtisTits.rankOne]
    refine sup_le ?_ ?_
    · intro y hy
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
      intro g hg
      obtain ⟨c, rfl⟩ := (mem_rootGroup_iff_suElt (unitaryInvolution_involutive hFn)
        (even_two_mul r) (idx_short hk) (toStd_single_short hk) y).1 hy
      rw [R.toHom_suElt hFn (even_two_mul r) hm (idx_short hk) c]
      have hmem : R.ξ (Sum.inl i) (Sum.inr ⟨i.val + 1, hk⟩) c ∈
          shortRootGroup Δ (framePt P Q (Sum.inl i))
            (framePt P Q (Sum.inr i))
            (framePt P Q (Sum.inr ⟨i.val + 1, hk⟩))
            (framePt P Q (Sum.inl ⟨i.val + 1, hk⟩)) :=
        (hR.short (Sum.inl i) (Sum.inr ⟨i.val + 1, hk⟩) (idx_short hk) _).2 ⟨c, rfl⟩
      have hline := shortRootGroup_le_lineGroup (Δ := Δ)
        (framePt P Q (Sum.inl i)) (framePt P Q (Sum.inr i))
        (framePt P Q (Sum.inr ⟨i.val + 1, hk⟩))
        (framePt P Q (Sum.inl ⟨i.val + 1, hk⟩)) hmem
      exact (commuting_residueGroup_lineGroup (Δ := Δ) (P := P) (Q := Q)
        (k := cLastIdx r hr) (a := Sum.inl i) (b := Sum.inr ⟨i.val + 1, hk⟩)
        hne_i hne_s) g hg _ hline
    · intro y hy
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
      intro g hg
      obtain ⟨c, rfl⟩ := (mem_rootGroup_iff_suElt (unitaryInvolution_involutive hFn)
        (even_two_mul r) (idx_short' hk) (toStd_neg_single_short hk) y).1 hy
      rw [R.toHom_suElt hFn (even_two_mul r) hm (idx_short' hk) c]
      have hmem : R.ξ (Sum.inl ⟨i.val + 1, hk⟩) (Sum.inr i) c ∈
          shortRootGroup Δ (framePt P Q (Sum.inl ⟨i.val + 1, hk⟩))
            (framePt P Q (Sum.inr ⟨i.val + 1, hk⟩))
            (framePt P Q (Sum.inr i)) (framePt P Q (Sum.inl i)) :=
        (hR.short (Sum.inl ⟨i.val + 1, hk⟩) (Sum.inr i) (idx_short' hk) _).2 ⟨c, rfl⟩
      have hline := shortRootGroup_le_lineGroup (Δ := Δ)
        (framePt P Q (Sum.inl ⟨i.val + 1, hk⟩))
        (framePt P Q (Sum.inr ⟨i.val + 1, hk⟩))
        (framePt P Q (Sum.inr i)) (framePt P Q (Sum.inl i)) hmem
      exact (commuting_residueGroup_lineGroup (Δ := Δ) (P := P) (Q := Q)
        (k := cLastIdx r hr) (a := Sum.inl ⟨i.val + 1, hk⟩) (b := Sum.inr i)
        hne_s hne_i) g hg _ hline
  have hc := hle hx
  exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_comap.1 hc) (θ A) (hθA A)).symm

private theorem commute_prev_of_hasFrameImages
    {R : SURelations (2 * r / 2) (unitaryInvolution F 2 n) H} (hR : R.HasFrameImages Δ P Q)
    {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθr : θ.range = residueGroup Δ P Q (cLastIdx r hr)) :
    ∀ c, unitaryInvolution F 2 n c = c → ∀ A,
      Commute ((R.toHom hFn (even_two_mul r) hm) (suLong (unitaryInvolution F 2 n)
        (Sum.inl (cPrevIdx r hr)) c)) (θ A) ∧
      Commute ((R.toHom hFn (even_two_mul r) hm) (suLong (unitaryInvolution F 2 n)
        (Sum.inr (cPrevIdx r hr)) c)) (θ A) := by
  intro c hc A
  have hne : cPrevIdx r hr ≠ cLastIdx r hr := cPrevIdx_ne_cLastIdx hr
  have hθA : θ A ∈ residueGroup Δ P Q (cLastIdx r hr) := by
    rw [← hθr]
    exact ⟨A, rfl⟩
  have hcomm := commuting_residueGroup (Δ := Δ) (P := P) (Q := Q)
    (k := cLastIdx r hr) (i := cPrevIdx r hr) hne
  constructor
  · have hmem : R.ξL (Sum.inl (cPrevIdx r hr)) c ∈ P (cPrevIdx r hr) := by
      have h := (hR.long (Sum.inl (cPrevIdx r hr))
        (R.ξL (Sum.inl (cPrevIdx r hr)) c)).2 ⟨c, hc, rfl⟩
      simpa using h
    rw [R.toHom_suLong hFn (even_two_mul r) hm (Sum.inl (cPrevIdx r hr)) hc]
    exact (hcomm (θ A) hθA (R.ξL (Sum.inl (cPrevIdx r hr)) c)
      (Subgroup.mem_sup_left hmem)).symm
  · have hmem : R.ξL (Sum.inr (cPrevIdx r hr)) c ∈ Q (cPrevIdx r hr) := by
      have h := (hR.long (Sum.inr (cPrevIdx r hr))
        (R.ξL (Sum.inr (cPrevIdx r hr)) c)).2 ⟨c, hc, rfl⟩
      simpa using h
    rw [R.toHom_suLong hFn (even_two_mul r) hm (Sum.inr (cPrevIdx r hr)) hc]
    exact (hcomm (θ A) hθA (R.ξL (Sum.inr (cPrevIdx r hr)) c)
      (Subgroup.mem_sup_right hmem)).symm

theorem SURelations.HasFrameImages.oddFrameCompatible_toHom
    {R : SURelations (2 * r / 2) (unitaryInvolution F 2 n) H} (hR : R.HasFrameImages Δ P Q)
    {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθr : θ.range = residueGroup Δ P Q (cLastIdx r hr))
    (hθc : θ.comp (su3Chord (unitaryInvolution F 2 n)) = R.lastBlock hFn (even_two_mul r) hm) :
    OddFrameCompatible hFn hr (R.toHom hFn (even_two_mul r) hm) θ :=
  ⟨long_last_of_comp_su3Chord hFn hr hm hθc,
    commute_short_of_hasFrameImages hFn hr hm hR hθr,
    commute_prev_of_hasFrameImages hFn hr hm hR hθr⟩

theorem SURelations.HasFrameImages.exists_oddFrameMap_toHom_ne_one
    {R : SURelations (2 * r / 2) (unitaryInvolution F 2 n) H} (hR : R.HasFrameImages Δ P Q)
    {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hd : OddFrameCompatible hFn hr (R.toHom hFn (even_two_mul r) hm) θ)
    (hP : P (cLastIdx r hr) ≠ ⊥) :
    ∃ k : Fin ((2 * r + 1) / 2), ∃ x : (Unitary.rootDatum hFn (2 * r + 1)).rootGroup
      (Pi.single k 1), oddFrameMap hFn hr (R.toHom hFn (even_two_mul r) hm) θ _ x ≠ 1 := by
  obtain ⟨g, hg, hg1⟩ := (Subgroup.bot_or_exists_ne_one (P (cLastIdx r hr))).resolve_left hP
  obtain ⟨c, hc, hgc⟩ := (hR.long (Sum.inl (cLastIdx r hr)) g).1 (by simpa using hg)
  refine hd.exists_oddFrameMap_ne_one hc ?_
  rw [R.toHom_suLong hFn (even_two_mul r) hm (Sum.inl (cLastIdx r hr)) hc, hgc]
  exact hg1

theorem SURelations.HasFrameImages.map_rootGroup_unitaryLongRoot_eq
    {R : SURelations (2 * r / 2) (unitaryInvolution F 2 n) H} (hR : R.HasFrameImages Δ P Q)
    {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hd : OddFrameCompatible hFn hr (R.toHom hFn (even_two_mul r) hm) θ)
    {Φ : SU (unitaryInvolution F 2 n) (2 * r + 1) →* H}
    (hΦ : ∀ x : (Unitary.rootDatum hFn (2 * r + 1)).rootGroup
      (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1),
      Φ x = oddFrameMap hFn hr (R.toHom hFn (even_two_mul r) hm) θ _ x)
    (h : 2 ≤ 2 * r + 1) :
    ((Unitary.rootDatum hFn (2 * r + 1)).rootGroup (unitaryLongRoot (2 * r + 1) h)).map Φ =
      P (cLastIdx r hr) := by
  rw [hd.map_rootGroup_unitaryLongRoot hΦ h
    (Nat.le_mul_of_pos_right 2 (Nat.lt_of_lt_of_le Nat.two_pos hr))]
  ext g
  exact (R.mem_map_rootGroup_unitaryLongRoot hFn (even_two_mul r) hm g).trans
    (hR.long (Sum.inl (cLastIdx r hr)) g).symm

theorem IsMaxFrame.su3_residue_oddPrevLift (hΔ : IsRootClass Δ) (hF : IsMaxFrame Δ P Q)
    (hns : ¬IsSmallFrame Δ P Q (cLastIdx r hr))
    {R : SURelations (2 * r / 2) (unitaryInvolution F 2 n) H} (hR : R.HasFrameImages Δ P Q)
    {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθr : θ.range = residueGroup Δ P Q (cLastIdx r hr))
    (hθc : θ.comp (su3Chord (unitaryInvolution F 2 n)) = R.lastBlock hFn (even_two_mul r) hm)
    (hθmem : ∀ X : Subgroup H, X ∈ frameResidue Δ P Q (cLastIdx r hr) ↔
      ∃ g, X = (conjSub (su3Top (unitaryInvolution F 2 n)) g).map θ) :
    (oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ).range =
        residueGroup Δ P Q (cPrevIdx r hr) ∧
      ¬IsSmallFrame Δ P Q (cPrevIdx r hr) ∧
      (∀ X : Subgroup H, X ∈ frameResidue Δ P Q (cPrevIdx r hr) ↔
        ∃ g, X = (conjSub (su3Top (unitaryInvolution F 2 n)) g).map
          (oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ)) ∧
      ∀ c, unitaryInvolution F 2 n c = c →
        oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ
            (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) c) =
          R.ξL (Sum.inl (cPrevIdx r hr)) c ∧
        oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ
            (suLong (unitaryInvolution F 2 n) (Sum.inr (0 : Fin (3 / 2))) c) =
          R.ξL (Sum.inr (cPrevIdx r hr)) c := by
  exact hF.su3_residue_prev (even_two_mul r) hm hΔ hns hFn R hR hθr hθc hθmem
    (ζ := ⟨1, one_mem_traceZero⟩) one_ne_zero

end CFSG.Timmesfeld.Transvection

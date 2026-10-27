module

import CFSG.Timmesfeld.Transvection.OddSU3Torus
import CFSG.LocalAnalysis.UniquenessCase.Lie.SU3
public import CFSG.Timmesfeld.Transvection.OddCPart
public import CFSG.Timmesfeld.Transvection.OddResidueTrans
public import CFSG.Timmesfeld.Transvection.OddSU3Chord

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg
open CFSG.LocalAnalysis.UniquenessCase CFSG.LieType.CurtisTits CFSG.LieType.BorelTits
open CFSG.Timmesfeld.Transvection.Pres

variable {H : Type} [Group H] {Δ : Set (Subgroup H)} {r : ℕ} {P Q : Fin r → Subgroup H}
  {k : Fin r} {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}


private theorem toHom_conj_levelWeyl {m : ℕ} (hFn : Nat.card F = (2 ^ n) ^ 2)
    (he : Even m) (hm : 4 ≤ m)
    (R : SURelations (m / 2) (unitaryInvolution F 2 n) H)
    {ζ : traceZero (unitaryInvolution F 2 n)} (hζ : (ζ : F) ≠ 0)
    {j : Fin (m / 2)} (hj : j.val + 1 < m / 2)
    (a : Fin (m / 2) ⊕ Fin (m / 2)) {c : F}
    (hc : unitaryInvolution F 2 n c = c) :
    R.toHom hFn he hm
        (levelWeyl (unitaryInvolution_involutive hFn) ζ j) * R.ξL a c *
        (R.toHom hFn he hm
          (levelWeyl (unitaryInvolution_involutive hFn) ζ j))⁻¹ =
      R.ξL (Sum.map (Equiv.swap j ⟨j.val + 1, hj⟩)
        (Equiv.swap j ⟨j.val + 1, hj⟩) a) c := by
  rw [← R.toHom_suLong hFn he hm a hc, ← map_inv, ← map_mul, ← map_mul]
  rw [levelWeyl_conj_suLong (unitaryInvolution_involutive hFn) hζ hj a c,
    R.toHom_suLong hFn he hm _ hc]

private theorem su3_residue_prev_basic {m : ℕ} (he : Even m) (hm : 4 ≤ m)
    {P Q : Fin (m / 2) → Subgroup H} (hΔ : IsRootClass Δ) (hF : IsMaxFrame Δ P Q)
    (hns : ¬ IsSmallFrame Δ P Q ⟨m / 2 - 1, by omega⟩)
    (hFn : Nat.card F = (2 ^ n) ^ 2)
    (R : SURelations (m / 2) (unitaryInvolution F 2 n) H)
    (hR : R.HasFrameImages Δ P Q)
    {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθr : θ.range = residueGroup Δ P Q ⟨m / 2 - 1, by omega⟩)
    (hθmem : ∀ X : Subgroup H, X ∈ frameResidue Δ P Q ⟨m / 2 - 1, by omega⟩ ↔
        ∃ g, X = (conjSub (su3Top (unitaryInvolution F 2 n)) g).map θ)
    {ζ : traceZero (unitaryInvolution F 2 n)} (hζ : (ζ : F) ≠ 0) :
    let m' : Fin (m / 2) := ⟨m / 2 - 2, by omega⟩
    let θ' := (MulAut.conj (R.toHom hFn he hm
      (levelWeyl (unitaryInvolution_involutive hFn) ζ m'))).toMonoidHom.comp θ
    θ'.range = residueGroup Δ P Q m' ∧ ¬ IsSmallFrame Δ P Q m' ∧
      (∀ X, X ∈ frameResidue Δ P Q m' ↔
        ∃ g, X = (conjSub (su3Top (unitaryInvolution F 2 n)) g).map θ') := by
  classical
  let σ := unitaryInvolution F 2 n
  have hσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hFn
  let last : Fin (m / 2) := ⟨m / 2 - 1, by omega⟩
  let m' : Fin (m / 2) := ⟨m / 2 - 2, by omega⟩
  have hm' : m'.val + 1 < m / 2 := by
    simp only [m']
    omega
  have hlast : (⟨m'.val + 1, hm'⟩ : Fin (m / 2)) = last := by
    apply Fin.ext
    simp only [last, m']
    omega
  let w : H := R.toHom hFn he hm
    (levelWeyl (unitaryInvolution_involutive hFn) ζ m')
  let θ' : SU σ 3 →* H := (MulAut.conj w).toMonoidHom.comp θ
  have hP : ∀ i, conjSub (P i) w = P (Equiv.swap m' last i) := by
    intro i
    have hconj := (SURelations.HasFrameImages.conjSub_levelWeyl hFn he hm R hR hζ hm' i).1
    simpa [w, hlast] using hconj
  have hQ : ∀ i, conjSub (Q i) w = Q (Equiv.swap m' last i) := by
    intro i
    have hconj := (SURelations.HasFrameImages.conjSub_levelWeyl hFn he hm R hR hζ hm' i).2
    simpa [w, hlast] using hconj
  obtain ⟨hr, hmem⟩ := conj_comp_of_perm (k := last) (g := w) hP hQ hΔ hθr hθmem
  have hπlast : Equiv.swap m' last last = m' := by simp
  have hsmall : ¬ IsSmallFrame Δ P Q m' := by
    have hiff := isSmallFrame_perm_iff (k := last) (g := w) hP hQ hΔ hF.toIsFrame
    rw [hπlast] at hiff
    exact fun h => hns (hiff.mp h)
  refine ⟨?_, hsmall, ?_⟩
  · simpa [θ', hπlast] using hr
  · intro X
    simpa [hπlast] using hmem X

private theorem su3_residue_prev_points {m : ℕ} (he : Even m) (hm : 4 ≤ m)
    (hFn : Nat.card F = (2 ^ n) ^ 2)
    (R : SURelations (m / 2) (unitaryInvolution F 2 n) H)
    {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθc : θ.comp (su3Chord (unitaryInvolution F 2 n)) = R.lastBlock hFn he hm)
    {ζ : traceZero (unitaryInvolution F 2 n)} (hζ : (ζ : F) ≠ 0) :
    let m' : Fin (m / 2) := ⟨m / 2 - 2, by omega⟩
    let θ' := (MulAut.conj (R.toHom hFn he hm
      (levelWeyl (unitaryInvolution_involutive hFn) ζ m'))).toMonoidHom.comp θ
    ∀ c, unitaryInvolution F 2 n c = c →
      θ' (suLong (unitaryInvolution F 2 n) (Sum.inl 0) c) = R.ξL (Sum.inl m') c ∧
      θ' (suLong (unitaryInvolution F 2 n) (Sum.inr 0) c) = R.ξL (Sum.inr m') c := by
  classical
  let σ := unitaryInvolution F 2 n
  have hσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hFn
  let last : Fin (m / 2) := ⟨m / 2 - 1, by omega⟩
  let m' : Fin (m / 2) := ⟨m / 2 - 2, by omega⟩
  have hm' : m'.val + 1 < m / 2 := by
    simp only [m']
    omega
  have hlast : (⟨m'.val + 1, hm'⟩ : Fin (m / 2)) = last := by
    apply Fin.ext
    simp only [last, m']
    omega
  let w : H := R.toHom hFn he hm
    (levelWeyl (unitaryInvolution_involutive hFn) ζ m')
  let θ' : SU σ 3 →* H := (MulAut.conj w).toMonoidHom.comp θ
  have hroot_inl : ∀ c, σ c = c →
      θ (suLong σ (Sum.inl 0) c) = R.ξL (Sum.inl last) c := by
    intro c hc
    have h := congrArg (fun f : SU σ 2 →* H => f (suLong σ (Sum.inl 0) c)) hθc
    simp only [MonoidHom.comp_apply, σ] at h
    rw [su3Chord_suLong_inl, R.lastBlock_suLong_inl hFn he hm hc] at h
    simpa [last] using h
  have hroot_inr : ∀ c, σ c = c →
      θ (suLong σ (Sum.inr 0) c) = R.ξL (Sum.inr last) c := by
    intro c hc
    have h := congrArg (fun f : SU σ 2 →* H => f (suLong σ (Sum.inr 0) c)) hθc
    simp only [MonoidHom.comp_apply, σ] at h
    rw [su3Chord_suLong_inr, R.lastBlock_suLong_inr hFn he hm hc] at h
    simpa [last] using h
  have hpt_inl : ∀ c, σ c = c →
      θ' (suLong σ (Sum.inl 0) c) = R.ξL (Sum.inl m') c := by
    intro c hc
    have hconj := toHom_conj_levelWeyl (F := F) (n := n) hFn he hm R hζ hm'
      (Sum.inl last) hc
    calc θ' (suLong σ (Sum.inl 0) c) = w * θ (suLong σ (Sum.inl 0) c) * w⁻¹ := by
          simp [θ', MulAut.conj_apply]
      _ = w * R.ξL (Sum.inl last) c * w⁻¹ := by rw [hroot_inl c hc]
      _ = R.ξL (Sum.inl m') c := by
          simpa [w, hlast] using hconj
  have hpt_inr : ∀ c, σ c = c →
      θ' (suLong σ (Sum.inr 0) c) = R.ξL (Sum.inr m') c := by
    intro c hc
    have hconj := toHom_conj_levelWeyl (F := F) (n := n) hFn he hm R hζ hm'
      (Sum.inr last) hc
    calc θ' (suLong σ (Sum.inr 0) c) = w * θ (suLong σ (Sum.inr 0) c) * w⁻¹ := by
          simp [θ', MulAut.conj_apply]
      _ = w * R.ξL (Sum.inr last) c * w⁻¹ := by rw [hroot_inr c hc]
      _ = R.ξL (Sum.inr m') c := by
          simpa [w, hlast] using hconj
  exact fun c hc => ⟨hpt_inl c hc, hpt_inr c hc⟩

theorem IsMaxFrame.su3_residue_prev {m : ℕ} (he : Even m) (hm : 4 ≤ m)
    {P Q : Fin (m / 2) → Subgroup H} (hΔ : IsRootClass Δ) (hF : IsMaxFrame Δ P Q)
    (hns : ¬ IsSmallFrame Δ P Q ⟨m / 2 - 1,
      Nat.sub_lt (Nat.div_pos (Nat.le_trans (Nat.le_add_right 2 2) hm) Nat.two_pos)
        Nat.zero_lt_one⟩)
    (hFn : Nat.card F = (2 ^ n) ^ 2)
    (R : SURelations (m / 2) (unitaryInvolution F 2 n) H)
    (hR : R.HasFrameImages Δ P Q)
    {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθr : θ.range = residueGroup Δ P Q ⟨m / 2 - 1,
      Nat.sub_lt (Nat.div_pos (Nat.le_trans (Nat.le_add_right 2 2) hm) Nat.two_pos)
        Nat.zero_lt_one⟩)
    (hθc : θ.comp (su3Chord (unitaryInvolution F 2 n)) = R.lastBlock hFn he hm)
    (hθmem : ∀ X : Subgroup H, X ∈ frameResidue Δ P Q ⟨m / 2 - 1,
        Nat.sub_lt (Nat.div_pos (Nat.le_trans (Nat.le_add_right 2 2) hm) Nat.two_pos)
          Nat.zero_lt_one⟩ ↔
        ∃ g, X = (conjSub (su3Top (unitaryInvolution F 2 n)) g).map θ)
    {ζ : traceZero (unitaryInvolution F 2 n)} (hζ : (ζ : F) ≠ 0) :
    let m' : Fin (m / 2) := ⟨m / 2 - 2,
      Nat.sub_lt (Nat.div_pos (Nat.le_trans (Nat.le_add_right 2 2) hm) Nat.two_pos)
        Nat.two_pos⟩
    let θ' := (MulAut.conj (R.toHom hFn he hm
      (levelWeyl (unitaryInvolution_involutive hFn) ζ m'))).toMonoidHom.comp θ
    θ'.range = residueGroup Δ P Q m' ∧ ¬ IsSmallFrame Δ P Q m' ∧
      (∀ X, X ∈ frameResidue Δ P Q m' ↔
        ∃ g, X = (conjSub (su3Top (unitaryInvolution F 2 n)) g).map θ') ∧
      ∀ c, unitaryInvolution F 2 n c = c →
        θ' (suLong (unitaryInvolution F 2 n) (Sum.inl 0) c) = R.ξL (Sum.inl m') c ∧
        θ' (suLong (unitaryInvolution F 2 n) (Sum.inr 0) c) = R.ξL (Sum.inr m') c := by
  obtain ⟨hr, hsmall, hmem⟩ :=
    su3_residue_prev_basic (F := F) (n := n) he hm hΔ hF hns hFn R hR hθr hθmem hζ
  exact ⟨hr, hsmall, hmem,
    su3_residue_prev_points (F := F) (n := n) he hm hFn R hθc hζ⟩

section AllCertificates


private theorem exists_mem_map_heis_conjSub_Q (h : TransvectionHyp H Δ)
    (hFn : Nat.card F = (2 ^ n) ^ 2)
    {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθt : (su3Top (unitaryInvolution F 2 n)).map θ = P k)
    (hθb : (su3Bot (unitaryInvolution F 2 n)).map θ = Q k)
    (hmem : ∀ X : Subgroup H, X ∈ frameResidue Δ P Q k ↔
      ∃ g, X = (conjSub (su3Top (unitaryInvolution F 2 n)) g).map θ)
    {X : Subgroup H} (hX : X ∈ frameResidue Δ P Q k) (hXP : X ≠ P k) :
    ∃ b ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ,
      conjSub (Q k) b = X := by
  classical
  haveI : Finite H := h.finite
  have hσ : ∀ c, unitaryInvolution F 2 n (unitaryInvolution F 2 n c) = c :=
    unitaryInvolution_involutive hFn
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hFn
  obtain ⟨g, hg⟩ := (hmem X).1 hX
  have hSg_ne : conjSub (su3Top (unitaryInvolution F 2 n)) g ≠
      su3Top (unitaryInvolution F 2 n) := by
    intro heq
    apply hXP
    rw [hg, heq, hθt]
  have hbruhat := UC22.uc22pwsu3_bruhat hσ (UC22.uc22pwsu3_hnorm hFn)
    (rankOne_three_eq_top hFn) hζ g
  rcases hbruhat with ⟨hh, hhh, u, hu, rfl⟩ | ⟨u, hu, hh, hhh, v, hv, rfl⟩
  · exact absurd (by
      rw [conjSub_mul, conjSub_su3Top_of_mem_X hσ hu,
        conjSub_su3Top_of_mem_H hσ hhh]) hSg_ne
  · refine ⟨θ u, Subgroup.mem_map_of_mem θ hu, ?_⟩
    have hconj : conjSub (su3Top (unitaryInvolution F 2 n))
        (u * UC22.uc22pwsu3W hσ ζ * hh * v) =
        conjSub (su3Bot (unitaryInvolution F 2 n)) u := by
      rw [conjSub_mul, conjSub_su3Top_of_mem_X hσ hv,
        conjSub_mul, conjSub_su3Top_of_mem_H hσ hhh,
        conjSub_mul, conjSub_su3Top_W hσ hζ]
    calc conjSub (Q k) (θ u) =
        (conjSub (su3Bot (unitaryInvolution F 2 n)) u).map θ := by
          rw [← hθb, ModelRank.conjSub_map θ
            (su3Bot (unitaryInvolution F 2 n)) u]
      _ = (conjSub (su3Top (unitaryInvolution F 2 n))
            (u * UC22.uc22pwsu3W hσ ζ * hh * v)).map θ := by rw [hconj]
      _ = X := by rw [← hg]

private theorem card_residue_ne (h : TransvectionHyp H Δ) (hML : MeetsLines Δ)
    (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsMaxFrame Δ P Q)
    (hns : ¬ IsSmallFrame Δ P Q k) (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n) :
    Nat.card {X : Subgroup H // X ∈ frameResidue Δ P Q k ∧ X ≠ P k} = (2 ^ n) ^ 3 := by
  have hP : P k ∈ frameResidue Δ P Q k := hF.toIsFrame.memP_frameResidue k
  have hR := hF.ncard_frameResidue_eq h hML hq hns
  have hPcard : Nat.card (P k) = 2 ^ n := hcard (P k) (hF.memP k)
  rw [show Nat.card {X : Subgroup H // X ∈ frameResidue Δ P Q k ∧ X ≠ P k} =
      (frameResidue Δ P Q k \ {P k}).ncard from Nat.card_coe_set_eq _]
  rw [Set.ncard_sdiff_singleton_of_mem hP, hR, hPcard]
  omega

theorem IsMaxFrame.existsUnique_conjSub_heis (h : TransvectionHyp H Δ) (hML : MeetsLines Δ)
    (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsMaxFrame Δ P Q)
    (hns : ¬ IsSmallFrame Δ P Q k) (hFn : Nat.card F = (2 ^ n) ^ 2)
    (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n)
    {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθr : θ.range = residueGroup Δ P Q k) (hθk : Odd (Nat.card θ.ker))
    (hθt : (su3Top (unitaryInvolution F 2 n)).map θ = P k)
    (hθb : (su3Bot (unitaryInvolution F 2 n)).map θ = Q k)
    (hmem : ∀ X : Subgroup H, X ∈ frameResidue Δ P Q k ↔
      ∃ g, X = (conjSub (su3Top (unitaryInvolution F 2 n)) g).map θ)
    {X : Subgroup H} (hX : X ∈ frameResidue Δ P Q k) (hXP : X ≠ P k) :
    ∃! b, b ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ ∧
      conjSub (Q k) b = X := by
  classical
  haveI : Finite H := h.finite
  have hσ : ∀ c, unitaryInvolution F 2 n (unitaryInvolution F 2 n c) = c :=
    unitaryInvolution_involutive hFn
  let Xh : Subgroup (SU (unitaryInvolution F 2 n) 3) :=
    UC22.uc22pwsu3X hσ
  let B : Subgroup H := Xh.map θ
  have hB_le : B ≤ residueGroup Δ P Q k := by
    have hBrange : B ≤ θ.range := Subgroup.map_le_range θ Xh
    rwa [hθr] at hBrange
  have hQ : Q k ∈ frameResidue Δ P Q k := hF.toIsFrame.memQ_frameResidue k
  have hnormP : ∀ b ∈ B, conjSub (P k) b = P k := by
    rintro b ⟨x, hx, rfl⟩
    rw [← hθt, ModelRank.conjSub_map θ (su3Top (unitaryInvolution F 2 n)) x,
      conjSub_su3Top_of_mem_X hσ hx, hθt]
  have hneq : ∀ b ∈ B, conjSub (Q k) b ≠ P k := by
    intro b hbB hbP
    have hPB : conjSub (P k) b = P k := hnormP b hbB
    have hPBinv : conjSub (P k) b⁻¹ = P k :=
      hnormP b⁻¹ (Subgroup.inv_mem _ hbB)
    have hQeqP : Q k = P k := by
      calc Q k = conjSub (conjSub (Q k) b) b⁻¹ :=
            (Aux.conjSub_conjSub_inv (Q k) b).symm
        _ = conjSub (P k) b⁻¹ := by rw [hbP]
        _ = P k := hPBinv
    exact (hF.opposite k).1 hQeqP.symm
  let f : ↥B → {X : Subgroup H // X ∈ frameResidue Δ P Q k ∧ X ≠ P k} :=
    fun b => ⟨conjSub (Q k) (b : H), conjSub_mem_frameResidue h.cls hQ (hB_le b.2),
      hneq b b.2⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨X, hX, hXP⟩
    obtain ⟨b, hbB, hbX⟩ :=
      exists_mem_map_heis_conjSub_Q h hFn hθt hθb hmem hX hXP
    exact ⟨⟨b, hbB⟩, Subtype.ext hbX⟩
  have hcardB : Nat.card ↥B = (2 ^ n) ^ 3 := card_map_heis_of_odd hFn hθk
  have hcardT : Nat.card {X : Subgroup H // X ∈ frameResidue Δ P Q k ∧ X ≠ P k} =
      (2 ^ n) ^ 3 := card_residue_ne h hML hq hF hns hcard
  have hbij : Function.Bijective f :=
    hsurj.bijective_of_nat_card_le (by rw [hcardB, hcardT])
  have hex : ∃ b ∈ B, conjSub (Q k) b = X :=
    exists_mem_map_heis_conjSub_Q h hFn hθt hθb hmem hX hXP
  obtain ⟨b₀, hb₀B, hb₀X⟩ := hex
  refine ⟨b₀, ⟨hb₀B, hb₀X⟩, ?_⟩
  intro b hb
  have hbB : b ∈ B := hb.1
  have hbX : conjSub (Q k) b = X := hb.2
  have hfb : f ⟨b, hbB⟩ = f ⟨b₀, hb₀B⟩ := by
    apply Subtype.ext
    exact hbX.trans hb₀X.symm
  exact congrArg Subtype.val (hbij.1 hfb)

end AllCertificates

end CFSG.Timmesfeld.Transvection

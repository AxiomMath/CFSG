module

public import CFSG.Timmesfeld.Transvection.OddHeisFrameBasics
public import CFSG.Timmesfeld.Transvection.RelBuildField
public import Certificates.Certificate43
public import Certificates.Certificate82
public import Certificates.Certificate83
public import Certificates.Certificate84
public import Certificates.Certificate85
public import Certificates.Certificate86
public import Certificates.Certificate87
public import Certificates.Certificate88
public import Certificates.Certificate89
public import Certificates.Certificate90
public import Certificates.Certificate91
public import Certificates.Certificate92
public import Certificates.Certificate93
public import Certificates.Certificate94
public import Certificates.Certificate95
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.Timmesfeld.Transvection.OddHeisAut
import CFSG.Timmesfeld.Transvection.OddHeisTorusComm
import CFSG.Timmesfeld.Transvection.OddHeisTorusDiag
import CFSG.Timmesfeld.Transvection.OddHeisWeylDecomp
import CFSG.Timmesfeld.Transvection.OddLocal
import CFSG.Timmesfeld.Transvection.OddModelShortTorus
import CFSG.Timmesfeld.Transvection.RelBuildNorm
import CFSG.Timmesfeld.Transvection.OddPairsFrame
import CFSG.Timmesfeld.Transvection.OddTranslationsMeet
import CFSG.LinearAlgebra.LinearGroups.CoordinateData
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
import CFSG.Permutation.BurnsideSchur
import CFSG.Timmesfeld.Moufang.Three
import CFSG.Timmesfeld.Transvection.OddResidueBlock

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.Timmesfeld.Transvection.Pres CFSG.LocalAnalysis.UniquenessCase
open CFSG.LieType.Universal.Unitary.SUExtras (toStd_last_odd)
open CFSG.LieType.Universal.Symplectic.SpExtras (wt)
open scoped commutatorElement

private theorem exists_heisValid_one {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hFn : Nat.card F = (2 ^ n) ^ 2) :
    ∃ v : F, v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n (1 : F) * 1 = 0 := by
  obtain ⟨v, hv⟩ := exists_add_unitaryInvolution_eq hFn (a := (1 : F)) (by rw [map_one])
  exact ⟨v, by rw [hv, map_one, mul_one, CharTwo.add_self_eq_zero]⟩

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ} (hFn : Nat.card F = (2 ^ n) ^ 2)
  {r : ℕ} (hr : 2 ≤ r) {H : Type} [Group H] {Δ : Set (Subgroup H)}
  {P Q : Fin (2 * r / 2) → Subgroup H} (hm : 4 ≤ 2 * r)

local notation "σ" => unitaryInvolution F 2 n

local notation "heis₃" => suHeis σ (unitaryInvolution_involutive hFn)
  (Nat.not_even_iff_odd.mpr (Exists.intro 1 rfl) : ¬ Even 3) (Sum.inl (0 : Fin (3 / 2)))

local notation "valid" u:max v:max => v + σ v + σ u * u = 0

local notation "P'" => cPrevIdx r hr

local notation "L'" => cLastIdx r hr


theorem IsMaxFrame.exists_conj_weyl_map_suHeis
    (h : TransvectionHyp H Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsMaxFrame Δ P Q)
    (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n)
    {R : SURelations (2 * r / 2) (unitaryInvolution F 2 n) H} (hR : R.HasFrameImages Δ P Q)
    {θ : SU (unitaryInvolution F 2 n) 3 →* H} (hθr : θ.range = residueGroup Δ P Q (cLastIdx r hr))
    (hθo : Odd (Nat.card θ.ker))
    (hθc : θ.comp (su3Chord (unitaryInvolution F 2 n)) = R.lastBlock hFn (even_two_mul r) hm)
    (hd : OddFrameCompatible hFn hr (R.toHom hFn (even_two_mul r) hm) θ)
    {c : F} (hc : c ≠ 0) :
    ∃ κ : F, unitaryInvolution F 2 n κ * κ = unitaryInvolution F 2 n c * c ∧
      ∀ u v : F, v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0 →
        ((R.toHom hFn (even_two_mul r) hm
            (levelWeyl (unitaryInvolution_involutive hFn) (Subtype.mk 1 one_mem_traceZero)
              (cPrevIdx r hr)))⁻¹ *
          (R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c *
            R.ξ (Sum.inl (cLastIdx r hr)) (Sum.inr (cPrevIdx r hr)) (-c⁻¹) *
            R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c)) *
          θ (suHeis (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
            (Nat.not_even_iff_odd.mpr ⟨1, rfl⟩) (Sum.inl (0 : Fin (3 / 2))) u v) *
          ((R.toHom hFn (even_two_mul r) hm
            (levelWeyl (unitaryInvolution_involutive hFn) (Subtype.mk 1 one_mem_traceZero)
              (cPrevIdx r hr)))⁻¹ *
          (R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c *
            R.ξ (Sum.inl (cLastIdx r hr)) (Sum.inr (cPrevIdx r hr)) (-c⁻¹) *
            R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c))⁻¹ =
        θ (suHeis (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
            (Nat.not_even_iff_odd.mpr ⟨1, rfl⟩) (Sum.inl (0 : Fin (3 / 2)))
            (κ * u) (unitaryInvolution F 2 n c * c * v)) := by
  have hn : 2 ≤ n := by
    by_contra hlt
    have h2 : 2 ^ n ≤ 2 := by
      simpa using Nat.pow_le_pow_right (by norm_num) (by omega : n ≤ 1)
    have hq' := hq (P L') (hF.memP L')
    have hcard' := hcard (P L') (hF.memP L')
    omega
  obtain ⟨t, ρ, hρ, hρσ, ht, hgt⟩ :=
    hR.exists_commute_conj_map_suHeis h.cls.root hn hθr hθo hd
  obtain ⟨hg, hμ⟩ :=
    hR.conj_weyl_mul_map_heis (hFn := hFn) (hr := hr) (hm := hm)
      h.cls.root hθr hθo hθc hd hc
  exact exists_conj_map_suHeis_eq_of_commute (hFn := hFn) (θ := θ) hθo
    (g := (R.toHom hFn (even_two_mul r) hm
            (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩ P'))⁻¹ *
          (R.ξ (Sum.inl P') (Sum.inr L') c * R.ξ (Sum.inl L') (Sum.inr P') (-c⁻¹) *
            R.ξ (Sum.inl P') (Sum.inr L') c))
    (t := t) hg (μ := σ c * c) hμ hρ hρσ ht (hgt c hc).symm

local notation "Ym" => shortRootGroup Δ (P P') (Q P') (Q L') (P L')
local notation "Yp" => shortRootGroup Δ (P P') (Q P') (P L') (Q L')
local notation "Ym'" => shortRootGroup Δ (P L') (Q L') (Q P') (P P')
local notation "Yp'" => shortRootGroup Δ (P L') (Q L') (P P') (Q P')

private noncomputable abbrev weylPrev (R : SURelations (2 * r / 2) σ H) : H :=
  R.toHom hFn (even_two_mul r) hm
    (levelWeyl (unitaryInvolution_involutive hFn) (Subtype.mk 1 one_mem_traceZero) P')

private noncomputable abbrev shortWeyl (R : SURelations (2 * r / 2) σ H) (c : F) : H :=
  R.ξ (Sum.inl P') (Sum.inr L') c * R.ξ (Sum.inl L') (Sum.inr P') (-c⁻¹) *
    R.ξ (Sum.inl P') (Sum.inr L') c

private lemma map_heis_sup_inf_map_heis_sup_le_prev_last
    (h : TransvectionHyp H Δ) (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A)
    (hF : IsMaxFrame Δ P Q) (hns : ¬ IsSmallFrame Δ P Q L')
    (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n)
    {R : SURelations (2 * r / 2) σ H} (hR : R.HasFrameImages Δ P Q)
    {θ : SU σ 3 →* H} (hθr : θ.range = residueGroup Δ P Q L')
    (hθo : Odd (Nat.card θ.ker))
    (hθc : θ.comp (su3Chord σ) = R.lastBlock hFn (even_two_mul r) hm)
    (hθmem : ∀ X : Subgroup H, X ∈ frameResidue Δ P Q L' ↔
      ∃ g, X = (conjSub (su3Top σ) g).map θ) :
    ((UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map
          (oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ) ⊔
        (Ym ⊔
          Yp ⊔ P P')) ⊓
      ((UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ ⊔
        (shortRootGroup Δ (P L') (Q L') (Q P') (P P') ⊔
          shortRootGroup Δ (P L') (Q L') (P P') (Q P') ⊔ P L')) ≤
      Yp := by
  obtain ⟨hθ'r, -, hθ'mem, -⟩ :=
    IsMaxFrame.su3_residue_oddPrevLift hFn hr hm h.cls.root hF hns hR hθr hθc hθmem
  obtain ⟨hθ'o, hθ't, hθ'b⟩ :=
    IsMaxFrame.oddPrevLift_normalized hFn hr hm h.cls.root hF hns hR hθr hθo hθc hθmem
  obtain ⟨hθt, hθb⟩ := hR.map_su3Top_su3Bot_of_comp hFn hr hm hθc
  exact hF.map_heis_sup_inf_map_heis_sup_le (i := L') (k := P')
    h hML hq hFn hcard hθ'r hθ't hθ'b (Ne.symm (cPrevIdx_ne_cLastIdx hr)) hns
    (θ' := θ) hθr hθo hθt hθb hθmem

private lemma heis_fst_eq_of_mul_shortRootGroup_eq
    {R : SURelations (2 * r / 2) σ H} (hR : R.HasFrameImages Δ P Q)
    {θ' : SU σ 3 →* H} (hθ'r : θ'.range = residueGroup Δ P Q P')
    (hθ'o : Odd (Nat.card θ'.ker))
    (hbot : residueGroup Δ P Q P' ⊓
      Yp = ⊥)
    {A B A' B' w w' : F} (hV : valid A B) (hV' : valid A' B')
    (h : θ' (heis₃ A B) * R.ξ (Sum.inl P') (Sum.inl L') w =
      θ' (heis₃ A' B') * R.ξ (Sum.inl P') (Sum.inl L') w') : A = A' := by
  have hidx : idx (Sum.inl P' : Fin (2 * r / 2) ⊕ Fin (2 * r / 2)) ≠
      idx (Sum.inl L') := by
    simpa using cPrevIdx_ne_cLastIdx hr
  have hzw : R.ξ (Sum.inl P') (Sum.inl L') w ∈
      Yp :=
    (hR.short (Sum.inl P') (Sum.inl L') hidx _).2 ⟨w, rfl⟩
  have hzw' : R.ξ (Sum.inl P') (Sum.inl L') w' ∈
      Yp :=
    (hR.short (Sum.inl P') (Sum.inl L') hidx _).2 ⟨w', rfl⟩
  have hmA : θ' (heis₃ A B) ∈ residueGroup Δ P Q P' := by
    rw [← hθ'r]
    exact Subgroup.map_le_range θ' _
      (Subgroup.mem_map_of_mem θ' (suHeis_three_mem_uc22pwsu3X hFn A B))
  have hmA' : θ' (heis₃ A' B') ∈ residueGroup Δ P Q P' := by
    rw [← hθ'r]
    exact Subgroup.map_le_range θ' _
      (Subgroup.mem_map_of_mem θ' (suHeis_three_mem_uc22pwsu3X hFn A' B'))
  have h1 : (θ' (heis₃ A' B'))⁻¹ * θ' (heis₃ A B) =
      R.ξ (Sum.inl P') (Sum.inl L') w' *
        (R.ξ (Sum.inl P') (Sum.inl L') w)⁻¹ := by
    calc (θ' (heis₃ A' B'))⁻¹ * θ' (heis₃ A B)
        = (θ' (heis₃ A' B'))⁻¹ * (θ' (heis₃ A B) *
            R.ξ (Sum.inl P') (Sum.inl L') w) *
            (R.ξ (Sum.inl P') (Sum.inl L') w)⁻¹ := by group
      _ = (θ' (heis₃ A' B'))⁻¹ * (θ' (heis₃ A' B') *
            R.ξ (Sum.inl P') (Sum.inl L') w') *
            (R.ξ (Sum.inl P') (Sum.inl L') w)⁻¹ := by rw [h]
      _ = R.ξ (Sum.inl P') (Sum.inl L') w' *
            (R.ξ (Sum.inl P') (Sum.inl L') w)⁻¹ := by group
  have hmem : (θ' (heis₃ A' B'))⁻¹ * θ' (heis₃ A B) ∈
      residueGroup Δ P Q P' ⊓
        Yp :=
    ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hmA') hmA,
      h1 ▸ Subgroup.mul_mem _ hzw' (Subgroup.inv_mem _ hzw)⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  have heq : θ' (heis₃ A B) = θ' (heis₃ A' B') := by
    calc θ' (heis₃ A B)
        = θ' (heis₃ A' B') *
            ((θ' (heis₃ A' B'))⁻¹ * θ' (heis₃ A B)) := by group
      _ = θ' (heis₃ A' B') := by rw [hmem, mul_one]
  exact (eq_and_eq_of_map_suHeis_eq hFn hθ'o hV hV' heq).1

private lemma exists_commutator_eq_heis_mul
    (h : TransvectionHyp H Δ) (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A)
    (hF : IsMaxFrame Δ P Q) (hns : ¬ IsSmallFrame Δ P Q L')
    (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n)
    {R : SURelations (2 * r / 2) σ H} (hR : R.HasFrameImages Δ P Q)
    {θ : SU σ 3 →* H} (hθr : θ.range = residueGroup Δ P Q L')
    (hθo : Odd (Nat.card θ.ker))
    (hθc : θ.comp (su3Chord σ) = R.lastBlock hFn (even_two_mul r) hm)
    (hθmem : ∀ X : Subgroup H, X ∈ frameResidue Δ P Q L' ↔
      ∃ g, X = (conjSub (su3Top σ) g).map θ)
    (hd : OddFrameCompatible hFn hr (R.toHom hFn (even_two_mul r) hm) θ)
    (hmeet :
      ((UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map
            (oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ) ⊔
          (Ym ⊔
            Yp ⊔ P P')) ⊓
        ((UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ ⊔
          (shortRootGroup Δ (P L') (Q L') (Q P') (P P') ⊔
            shortRootGroup Δ (P L') (Q L') (P P') (Q P') ⊔ P L')) ≤
      Yp)
    {κ : F → F} (hκ0 : κ 0 = 0)
    (hconj : ∀ s : F, s ≠ 0 → ∀ u v : F, valid u v →
      ((weylPrev hFn hr hm R)⁻¹ * shortWeyl hr R s) * θ (heis₃ u v) *
          ((weylPrev hFn hr hm R)⁻¹ * shortWeyl hr R s)⁻¹ =
        θ (heis₃ (κ s * u) (σ s * s * v)))
    (s u v : F) (hV : valid u v) :
    ∃ w : F, ⁅R.ξ (Sum.inl P') (Sum.inr L') s, θ (heis₃ u v)⁆ =
      oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ
        (heis₃ (κ s * u) (σ s * s * v)) * R.ξ (Sum.inl P') (Sum.inl L') w := by
  have hidx : idx (Sum.inl P' : Fin (2 * r / 2) ⊕ Fin (2 * r / 2)) ≠
      idx (Sum.inl L') := by
    simpa using cPrevIdx_ne_cLastIdx hr
  by_cases hs : s = 0
  · subst hs
    have hheis : heis₃ (κ 0 * u) (σ (0 : F) * 0 * v) = 1 := by
      rw [hκ0, zero_mul, map_zero, zero_mul, zero_mul, suHeis_zero_left, suLong_zero]
    refine ⟨0, ?_⟩
    rw [hheis, map_one, R.map_zero (a := Sum.inl P') (b := Sum.inl L') hidx, mul_one,
      R.map_zero (a := Sum.inl P') (b := Sum.inr L') (by simpa using hidx),
      commutatorElement_one_left]
  · have hDx : ((weylPrev hFn hr hm R)⁻¹ * shortWeyl hr R s) * θ (heis₃ u v) *
        ((weylPrev hFn hr hm R)⁻¹ * shortWeyl hr R s)⁻¹ ∈
        (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ :=
      (hR.conj_weyl_mul_map_heis (hFn := hFn) (hr := hr) (hm := hm)
        h.cls.root hθr hθo hθc hd hs).1 (heis₃ u v) (suHeis_three_mem_uc22pwsu3X hFn u v)
    obtain ⟨w, hw⟩ :=
      IsMaxFrame.commutatorElement_ξ_eq_mul (hFn := hFn) (hr := hr) (hm := hm)
        h hML hq hF hns hcard hR hθr hθo hθc hθmem hmeet
        (c := s) (x := θ (heis₃ u v))
        (Subgroup.mem_map_of_mem θ (suHeis_three_mem_uc22pwsu3X hFn u v)) hDx
    refine ⟨w, ?_⟩
    rw [hw, hconj s hs u v hV, ← oddPrevLift_apply (hFn := hFn) (hr := hr)
      (Ψ₀ := R.toHom hFn (even_two_mul r) hm) (θ := θ)]

private lemma conj_shortRoot_zroot
    {R : SURelations (2 * r / 2) σ H}
    {θ' : SU σ 3 →* H}
    (hL : ∀ c : F, σ c = c → R.ξL (Sum.inl P') c = θ' (heis₃ 0 c)) {s w : F} :
    R.ξ (Sum.inl P') (Sum.inr L') s * R.ξ (Sum.inl P') (Sum.inl L') w *
        (R.ξ (Sum.inl P') (Sum.inr L') s)⁻¹ =
      θ' (heis₃ 0 (s * σ w + σ s * w)) * R.ξ (Sum.inl P') (Sum.inl L') w := by
  have hidx : idx (Sum.inl P' : Fin (2 * r / 2) ⊕ Fin (2 * r / 2)) ≠
      idx (Sum.inr L') := by
    simpa using cPrevIdx_ne_cLastIdx hr
  have hcσ : σ (s * σ w + σ s * w) = s * σ w + σ s * w := by
    rw [map_add, map_mul, map_mul, unitaryInvolution_involutive hFn,
      unitaryInvolution_involutive hFn]
    ring
  have hLc : R.ξL (Sum.inl P') (s * σ w + σ s * w) =
      θ' (heis₃ 0 (s * σ w + σ s * w)) := hL _ hcσ
  calc R.ξ (Sum.inl P') (Sum.inr L') s * R.ξ (Sum.inl P') (Sum.inl L') w *
        (R.ξ (Sum.inl P') (Sum.inr L') s)⁻¹
      = ⁅R.ξ (Sum.inl P') (Sum.inr L') s, R.ξ (Sum.inl P') (Sum.inl L') w⁆ *
          R.ξ (Sum.inl P') (Sum.inl L') w := by
        rw [commutatorElement_def]
        group
    _ = R.ξL (Sum.inl P') (s * σ w + σ s * w) *
          R.ξ (Sum.inl P') (Sum.inl L') w := by
        simpa using R.trace (Sum.inl P') (Sum.inr L') hidx s w
    _ = _ := by rw [hLc]

private lemma heis_mul_three {A B C D X : F} (hA : valid A B) (h0 : valid (0 : F) C)
    (hAC : valid A (B + C)) (hX : valid X D) :
    heis₃ A B * heis₃ 0 C * heis₃ X D =
      heis₃ (A + X) ((B + C) + D - A * σ X) := by
  rw [suHeis_mul (unitaryInvolution_involutive hFn) (Nat.not_even_iff_odd.mpr ⟨1, rfl⟩ : ¬ Even 3)
    hA h0]
  simp only [map_zero, mul_zero, sub_zero, add_zero]
  rw [suHeis_mul (unitaryInvolution_involutive hFn) (Nat.not_even_iff_odd.mpr ⟨1, rfl⟩ : ¬ Even 3)
    hAC hX]

private lemma conj_mul_heis_eq {G : Type*} [Group G] {y zs zs' Xs Xs' L : G}
    (hyX' : Commute y Xs') (hzX : Commute zs' Xs) (hconjZ : y * zs' * y⁻¹ = L * zs') :
    y * (Xs' * zs') * y⁻¹ * (Xs * zs) = (Xs' * L * Xs) * (zs' * zs) := by
  calc y * (Xs' * zs') * y⁻¹ * (Xs * zs)
      = Xs' * (y * zs' * y⁻¹) * (Xs * zs) := by
        rw [show y * (Xs' * zs') * y⁻¹ * (Xs * zs) =
          (y * Xs') * zs' * y⁻¹ * (Xs * zs) by group, hyX'.eq]
        group
    _ = Xs' * (L * zs') * (Xs * zs) := by rw [hconjZ]
    _ = (Xs' * L * Xs) * (zs' * zs) := by
        rw [show Xs' * (L * zs') * (Xs * zs) = (Xs' * L) * (zs' * Xs) * zs by group,
          hzX.eq]
        group

private lemma heisConjScalar_hmain
    {R : SURelations (2 * r / 2) σ H} (hR : R.HasFrameImages Δ P Q)
    {θ θ' : SU σ 3 →* H}
    (hL : ∀ c : F, σ c = c → R.ξL (Sum.inl P') c = θ' (heis₃ 0 c))
    (hBPY : Commuting ((UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ')
      (Ym))
    (hBPZ : Commuting ((UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ')
      (Yp))
    {κ : F → F} (hκN : ∀ s, σ (κ s) * κ s = σ s * s)
    {v : F} (hv : valid (1 : F) v) {w : F → F}
    (hw : ∀ t : F, ⁅R.ξ (Sum.inl P') (Sum.inr L') t, θ (heis₃ (1 : F) v)⁆ =
      θ' (heis₃ (κ t * 1) (σ t * t * v)) * R.ξ (Sum.inl P') (Sum.inl L') (w t))
    (s s' : F) :
    θ' (heis₃ (κ (s + s') * 1) (σ (s + s') * (s + s') * v)) *
        R.ξ (Sum.inl P') (Sum.inl L') (w (s + s')) =
      θ' (heis₃ (κ s' * 1 + κ s * 1)
        (((σ s' * s' * v) + (s * σ (w s') + σ s * w s')) + σ s * s * v -
          (κ s' * 1) * σ (κ s * 1))) *
        R.ξ (Sum.inl P') (Sum.inl L') (w s' + w s) := by
  let y : H := R.ξ (Sum.inl P') (Sum.inr L') s
  let zs : H := R.ξ (Sum.inl P') (Sum.inl L') (w s)
  let zs' : H := R.ξ (Sum.inl P') (Sum.inl L') (w s')
  let Xs : H := θ' (heis₃ (κ s * 1) (σ s * s * v))
  let Xs' : H := θ' (heis₃ (κ s' * 1) (σ s' * s' * v))
  let L : H := θ' (heis₃ 0 (s * σ (w s') + σ s * w s'))
  have hws : ⁅y, θ (heis₃ (1 : F) v)⁆ = Xs * zs := by
    simpa only [y, Xs, zs] using hw s
  have hws' : ⁅R.ξ (Sum.inl P') (Sum.inr L') s', θ (heis₃ (1 : F) v)⁆ = Xs' * zs' := by
    simpa only [Xs', zs'] using hw s'
  have hconjZ : y * zs' * y⁻¹ = L * zs' := by
    simpa only [y, zs', L] using conj_shortRoot_zroot hFn hr hL (s := s) (w := w s')
  have hV' : valid (κ s' * 1) (σ s' * s' * v) :=
    Pres.heis_smul_valid (unitaryInvolution_involutive hFn) hv (hκN s')
  have hV : valid (κ s * 1) (σ s * s * v) :=
    Pres.heis_smul_valid (unitaryInvolution_involutive hFn) hv (hκN s)
  have hcσ : σ (s * σ (w s') + σ s * w s') = s * σ (w s') + σ s * w s' := by
    rw [map_add, map_mul, map_mul, unitaryInvolution_involutive hFn,
      unitaryInvolution_involutive hFn]
    ring
  have hV0 : valid (0 : F) (s * σ (w s') + σ s * w s') := Pres.heis_zero_left_valid hcσ
  have hVc : valid (κ s' * 1) ((σ s' * s' * v) + (s * σ (w s') + σ s * w s')) := by
    simpa using Pres.heis_add_valid (unitaryInvolution_involutive hFn) hV' hV0
  have hXLX : Xs' * L * Xs = θ' (heis₃ (κ s' * 1 + κ s * 1)
      (((σ s' * s' * v) + (s * σ (w s') + σ s * w s')) + σ s * s * v -
        (κ s' * 1) * σ (κ s * 1))) := by
    have hprod := heis_mul_three hFn (A := κ s' * 1) (B := σ s' * s' * v)
      (C := s * σ (w s') + σ s * w s') (D := σ s * s * v) (X := κ s * 1)
      hV' hV0 hVc hV
    simp only [Xs', L, Xs]
    rw [← hprod, map_mul, map_mul]
  have hy : y ∈ Ym := by
    simp only [y]
    exact (hR.short (Sum.inl P') (Sum.inr L')
      (by simpa using cPrevIdx_ne_cLastIdx hr) _).2 ⟨s, rfl⟩
  have hzs' : zs' ∈ Yp := by
    simp only [zs']
    exact (hR.short (Sum.inl P') (Sum.inl L')
      (by simpa using cPrevIdx_ne_cLastIdx hr) _).2 ⟨w s', rfl⟩
  have hX : Xs ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ' := by
    simp only [Xs]
    exact Subgroup.mem_map_of_mem θ' (suHeis_three_mem_uc22pwsu3X hFn _ _)
  have hX' : Xs' ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ' := by
    simp only [Xs']
    exact Subgroup.mem_map_of_mem θ' (suHeis_three_mem_uc22pwsu3X hFn _ _)
  have hyX' : Commute y Xs' := (hBPY Xs' hX' y hy).symm
  have hzX : Commute zs' Xs := (hBPZ Xs hX zs' hzs').symm
  have hstep := conj_mul_heis_eq (zs := zs) hyX' hzX hconjZ
  have hcalc : ⁅R.ξ (Sum.inl P') (Sum.inr L') (s + s'), θ (heis₃ (1 : F) v)⁆ =
      θ' (heis₃ (κ s' * 1 + κ s * 1)
        (((σ s' * s' * v) + (s * σ (w s') + σ s * w s')) + σ s * s * v -
          (κ s' * 1) * σ (κ s * 1))) *
        R.ξ (Sum.inl P') (Sum.inl L') (w s' + w s) := by
    rw [R.add (Sum.inl P') (Sum.inr L') (by simpa using cPrevIdx_ne_cLastIdx hr) s s',
      commutatorElement_mul_left_eq_conj_mul, hws', hws, hstep, hXLX]
    simp only [zs', zs]
    rw [← R.add (Sum.inl P') (Sum.inl L') (by simpa using cPrevIdx_ne_cLastIdx hr)
      (w s') (w s)]
  rw [← hw (s + s'), hcalc]

private lemma heisConjScalar_add
    {R : SURelations (2 * r / 2) σ H} (hR : R.HasFrameImages Δ P Q)
    {θ θ' : SU σ 3 →* H}
    (hL : ∀ c : F, σ c = c → R.ξL (Sum.inl P') c = θ' (heis₃ 0 c))
    (hθ'r : θ'.range = residueGroup Δ P Q P') (hθ'o : Odd (Nat.card θ'.ker))
    (hbot : residueGroup Δ P Q P' ⊓
      Yp = ⊥)
    (hBPY : Commuting ((UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ')
      (Ym))
    (hBPZ : Commuting ((UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ')
      (Yp))
    {κ : F → F} (hκN : ∀ s, σ (κ s) * κ s = σ s * s)
    (hcomm : ∀ s u v : F, valid u v → ∃ w : F,
      ⁅R.ξ (Sum.inl P') (Sum.inr L') s, θ (heis₃ u v)⁆ =
        θ' (heis₃ (κ s * u) (σ s * s * v)) * R.ξ (Sum.inl P') (Sum.inl L') w) :
    ∀ s s' : F, κ (s + s') = κ s + κ s' := by
  intro s s'
  obtain ⟨v, hv⟩ := exists_heisValid_one hFn
  choose w hw using fun t => hcomm t 1 v hv
  have hmain := heisConjScalar_hmain hFn hr hR hL hBPY hBPZ hκN hv hw s s'
  have hV' : valid (κ s' * 1) (σ s' * s' * v) :=
    Pres.heis_smul_valid (unitaryInvolution_involutive hFn) hv (hκN s')
  have hV : valid (κ s * 1) (σ s * s * v) :=
    Pres.heis_smul_valid (unitaryInvolution_involutive hFn) hv (hκN s)
  have hcσ : σ (s * σ (w s') + σ s * w s') = s * σ (w s') + σ s * w s' := by
    rw [map_add, map_mul, map_mul, unitaryInvolution_involutive hFn,
      unitaryInvolution_involutive hFn]
    ring
  have hV0 : valid (0 : F) (s * σ (w s') + σ s * w s') := Pres.heis_zero_left_valid hcσ
  have hVc : valid (κ s' * 1) ((σ s' * s' * v) + (s * σ (w s') + σ s * w s')) := by
    simpa using Pres.heis_add_valid (unitaryInvolution_involutive hFn) hV' hV0
  have hVs : valid (κ (s + s') * 1) (σ (s + s') * (s + s') * v) :=
    Pres.heis_smul_valid (unitaryInvolution_involutive hFn) hv (hκN (s + s'))
  have hVright : valid (κ s' * 1 + κ s * 1)
      (((σ s' * s' * v) + (s * σ (w s') + σ s * w s')) + σ s * s * v -
        (κ s' * 1) * σ (κ s * 1)) := by
    simpa using Pres.heis_add_valid (unitaryInvolution_involutive hFn) hVc hV
  have hfirst := heis_fst_eq_of_mul_shortRootGroup_eq hFn hr hR hθ'r hθ'o hbot
    hVs hVright hmain
  simpa [mul_one, add_comm] using hfirst

private lemma oddPrevLift_data
    (h : TransvectionHyp H Δ) (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A)
    (hF : IsMaxFrame Δ P Q) (hns : ¬ IsSmallFrame Δ P Q L')
    (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n)
    {R : SURelations (2 * r / 2) σ H} (hR : R.HasFrameImages Δ P Q)
    {θ : SU σ 3 →* H} (hθr : θ.range = residueGroup Δ P Q L')
    (hθo : Odd (Nat.card θ.ker))
    (hθc : θ.comp (su3Chord σ) = R.lastBlock hFn (even_two_mul r) hm)
    (hθmem : ∀ X : Subgroup H, X ∈ frameResidue Δ P Q L' ↔
      ∃ g, X = (conjSub (su3Top σ) g).map θ)
    (hd : OddFrameCompatible hFn hr (R.toHom hFn (even_two_mul r) hm) θ) :
    (oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ).range =
        residueGroup Δ P Q P' ∧
      Odd (Nat.card (oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ).ker) ∧
      residueGroup Δ P Q P' ⊓ Yp = ⊥ ∧
      Commuting ((UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map
        (oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ))
        (Ym) ∧
      Commuting ((UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map
        (oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ))
        (Yp) ∧
      (∀ c : F, σ c = c → R.ξL (Sum.inl P') c =
        oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ (heis₃ 0 c)) := by
  obtain ⟨hθ'r, -, hθ'mem, -⟩ :=
    IsMaxFrame.su3_residue_oddPrevLift hFn hr hm h.cls.root hF hns hR hθr hθc hθmem
  obtain ⟨hθ'o, hθ't, hθ'b⟩ :=
    IsMaxFrame.oddPrevLift_normalized hFn hr hm h.cls.root hF hns hR hθr hθo hθc hθmem
  obtain ⟨hθt, hθb⟩ := hR.map_su3Top_su3Bot_of_comp hFn hr hm hθc
  have hbot : residueGroup Δ P Q P' ⊓
      Yp = ⊥ :=
    hF.residueGroup_inf_shortRootGroup_eq_bot (k := L') (i := P')
      h hML hq hns hFn hcard hθr hθo hθt hθb hθmem (cPrevIdx_ne_cLastIdx hr)
  have hBP := IsFrame.commuting_map_heis_shortRootGroup h hML hq hF.toIsFrame hFn hcard
    hθ'r hθ't hθ'b (Ne.symm (cPrevIdx_ne_cLastIdx hr))
  have hL : ∀ c : F, σ c = c → R.ξL (Sum.inl P') c =
      oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ (heis₃ 0 c) :=
    fun c hc => (OddFrameCompatible.ξL_inl_eq_map_suHeis (hFn := hFn) (hr := hr)
      (hm := hm) hd hc).2
  exact ⟨hθ'r, hθ'o, hbot, hBP.1, hBP.2, hL⟩

private lemma heisConjScalar_one
    {R : SURelations (2 * r / 2) σ H}
    {θ : SU σ 3 →* H} (hθo : Odd (Nat.card θ.ker))
    {κ : F → F} (hκN : ∀ s, σ (κ s) * κ s = σ s * s)
    (hconj : ∀ s : F, s ≠ 0 → ∀ u v : F, valid u v →
      ((weylPrev hFn hr hm R)⁻¹ * shortWeyl hr R s) * θ (heis₃ u v) *
          ((weylPrev hFn hr hm R)⁻¹ * shortWeyl hr R s)⁻¹ =
        θ (heis₃ (κ s * u) (σ s * s * v))) :
    κ 1 = 1 := by
  obtain ⟨v, hv⟩ := exists_heisValid_one hFn
  have hconjW := hconj 1 one_ne_zero 1 v hv
  have hW : weylPrev hFn hr hm R = shortWeyl hr R 1 := by
    simp only [weylPrev, shortWeyl]
    exact SURelations.toHom_levelWeyl_cPrevIdx (R := R) hFn hr hm
  rw [hW, inv_mul_cancel, one_mul, inv_one, mul_one] at hconjW
  have hV' : valid (κ 1 * 1) (σ 1 * 1 * v) :=
    Pres.heis_smul_valid (unitaryInvolution_involutive hFn) hv (hκN 1)
  have heq := (eq_and_eq_of_map_suHeis_eq hFn hθo hv hV' hconjW).1
  simpa using heq.symm

private lemma exists_tw_commutator_eq
    (h : TransvectionHyp H Δ) (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A)
    (hF : IsMaxFrame Δ P Q) (hns : ¬ IsSmallFrame Δ P Q L')
    (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n)
    {R : SURelations (2 * r / 2) σ H} (hR : R.HasFrameImages Δ P Q)
    {θ : SU σ 3 →* H} (hθr : θ.range = residueGroup Δ P Q L')
    (hθo : Odd (Nat.card θ.ker))
    (hθc : θ.comp (su3Chord σ) = R.lastBlock hFn (even_two_mul r) hm)
    (hθmem : ∀ X : Subgroup H, X ∈ frameResidue Δ P Q L' ↔
      ∃ g, X = (conjSub (su3Top σ) g).map θ)
    (hd : OddFrameCompatible hFn hr (R.toHom hFn (even_two_mul r) hm) θ)
    (hmeet :
      ((UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map
            (oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ) ⊔
          (Ym ⊔ Yp ⊔ P P')) ⊓
        ((UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ ⊔
          (Ym' ⊔ Yp' ⊔ P L')) ≤ Yp)
    (hθ'r : (oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ).range =
      residueGroup Δ P Q P')
    (hθ'o : Odd (Nat.card (oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ).ker))
    (hbot : residueGroup Δ P Q P' ⊓ Yp = ⊥)
    (hBPY : Commuting ((UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map
      (oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ)) Ym)
    (hBPZ : Commuting ((UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map
      (oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ)) Yp)
    (hL : ∀ c : F, σ c = c → R.ξL (Sum.inl P') c =
      oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ (heis₃ 0 c)) :
    ∃ e : Bool, ∀ s u v : F, valid u v → ∃ w : F,
      ⁅R.ξ (Sum.inl P') (Sum.inr L') s, θ (heis₃ u v)⁆ =
        oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ
          (heis₃ (RelBuild.tw (unitaryInvolution F 2 n) e s * u) (σ s * s * v)) *
          R.ξ (Sum.inl P') (Sum.inl L') w := by
  classical
  have hmeet := map_heis_sup_inf_map_heis_sup_le_prev_last hFn hr hm h hML hq hF hns
    hcard hR hθr hθo hθc hθmem
  obtain ⟨hθ'r, hθ'o, hbot, hBPY, hBPZ, hL⟩ :=
    oddPrevLift_data hFn hr hm h hML hq hF hns hcard hR hθr hθo hθc hθmem hd
  have hex : ∀ s : F, s ≠ 0 → ∃ κ : F, σ κ * κ = σ s * s ∧
      ∀ u v : F, valid u v →
        ((weylPrev hFn hr hm R)⁻¹ * shortWeyl hr R s) * θ (heis₃ u v) *
            ((weylPrev hFn hr hm R)⁻¹ * shortWeyl hr R s)⁻¹ =
          θ (heis₃ (κ * u) (σ s * s * v)) :=
    fun s hs => hF.exists_conj_weyl_map_suHeis hFn hr hm h hq hcard hR hθr hθo hθc hd hs
  let κ : F → F := fun s => if hs : s = 0 then 0 else Classical.choose (hex s hs)
  have hκ0 : κ 0 = 0 := by simp [κ]
  have hκN : ∀ s, σ (κ s) * κ s = σ s * s := by
    intro s
    by_cases hs : s = 0
    · subst hs
      simp [κ]
    · simp only [κ, dif_neg hs]
      exact (Classical.choose_spec (hex s hs)).1
  have hconj : ∀ s : F, s ≠ 0 → ∀ u v : F, valid u v →
      ((weylPrev hFn hr hm R)⁻¹ * shortWeyl hr R s) * θ (heis₃ u v) *
          ((weylPrev hFn hr hm R)⁻¹ * shortWeyl hr R s)⁻¹ =
        θ (heis₃ (κ s * u) (σ s * s * v)) := by
    intro s hs u v hV
    simp only [κ, dif_neg hs]
    exact (Classical.choose_spec (hex s hs)).2 u v hV
  have hcomm : ∀ s u v : F, valid u v → ∃ w : F,
      ⁅R.ξ (Sum.inl P') (Sum.inr L') s, θ (heis₃ u v)⁆ =
        oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ
          (heis₃ (κ s * u) (σ s * s * v)) * R.ξ (Sum.inl P') (Sum.inl L') w :=
    fun s u v hV => exists_commutator_eq_heis_mul hFn hr hm h hML hq hF hns hcard hR
      hθr hθo hθc hθmem hd hmeet hκ0 hconj s u v hV
  have hadd := heisConjScalar_add hFn hr hR hL hθ'r hθ'o hbot hBPY hBPZ hκN hcomm
  have hκ1 : κ 1 = 1 := heisConjScalar_one hFn hr hm hθo hκN hconj
  have hN : ∀ s : F, unitaryInvolution F 2 n (κ s) * κ s =
      1 * (unitaryInvolution F 2 n s * s) := fun s => by simpa using hκN s
  obtain ⟨e, he⟩ := RelBuild.exists_tw_of_add_of_norm (φ := κ) hadd (m := 1) hN
  refine ⟨e, ?_⟩
  intro s u v hV
  obtain ⟨w, hw⟩ := hcomm s u v hV
  refine ⟨w, ?_⟩
  rw [hw, he s, hκ1, one_mul]

theorem IsMaxFrame.exists_tw_commutatorElement_ξ_map_suHeis
    (h : TransvectionHyp H Δ) (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A)
    (hF : IsMaxFrame Δ P Q) (hns : ¬ IsSmallFrame Δ P Q (cLastIdx r hr))
    (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n)
    {R : SURelations (2 * r / 2) (unitaryInvolution F 2 n) H} (hR : R.HasFrameImages Δ P Q)
    {θ : SU (unitaryInvolution F 2 n) 3 →* H} (hθr : θ.range = residueGroup Δ P Q (cLastIdx r hr))
    (hθo : Odd (Nat.card θ.ker))
    (hθc : θ.comp (su3Chord (unitaryInvolution F 2 n)) = R.lastBlock hFn (even_two_mul r) hm)
    (hθmem : ∀ X : Subgroup H, X ∈ frameResidue Δ P Q (cLastIdx r hr) ↔
      ∃ g, X = (conjSub (su3Top (unitaryInvolution F 2 n)) g).map θ)
    (hd : OddFrameCompatible hFn hr (R.toHom hFn (even_two_mul r) hm) θ) :
    ∃ e : Bool, ∀ s u v : F,
      v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0 → ∃ w : F,
      ⁅R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) s,
          θ (suHeis (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
            (Nat.not_even_iff_odd.mpr ⟨1, rfl⟩) (Sum.inl (0 : Fin (3 / 2))) u v)⁆ =
        oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ
            (suHeis (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
              (Nat.not_even_iff_odd.mpr ⟨1, rfl⟩) (Sum.inl (0 : Fin (3 / 2)))
              (RelBuild.tw (unitaryInvolution F 2 n) e s * u)
              (unitaryInvolution F 2 n s * s * v)) *
          R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inl (cLastIdx r hr)) w := by
  have hmeet := map_heis_sup_inf_map_heis_sup_le_prev_last hFn hr hm h hML hq hF hns
    hcard hR hθr hθo hθc hθmem
  obtain ⟨hθ'r, hθ'o, hbot, hBPY, hBPZ, hL⟩ :=
    oddPrevLift_data hFn hr hm h hML hq hF hns hcard hR hθr hθo hθc hθmem hd
  exact exists_tw_commutator_eq hFn hr hm h hML hq hF hns hcard hR hθr hθo hθc hθmem hd hmeet
    hθ'r hθ'o hbot hBPY hBPZ hL

end CFSG.Timmesfeld.Transvection

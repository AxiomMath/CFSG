module

public import CFSG.Timmesfeld.Transvection.OddPairs
public import CFSG.Timmesfeld.Transvection.PresSU
public import CFSG.Timmesfeld.Transvection.FrameResidue
public import CFSG.Timmesfeld.Transvection.OddModelHeis
public import CFSG.Timmesfeld.Transvection.GenerateRel
import CFSG.Timmesfeld.Transvection.OddSU3Chord
import CFSG.Timmesfeld.Transvection.OddCPart
import CFSG.Timmesfeld.Transvection.LineGroup
import CFSG.Timmesfeld.Transvection.RelBuildNorm
import CFSG.Timmesfeld.Transvection.OddPairsFrame
import CFSG.Timmesfeld.Transvection.OddModelShortTorus
import CFSG.Timmesfeld.Transvection.OddHeisFrameBasics
public import CFSG.Timmesfeld.ARS.ConfigTransfer
public import CFSG.Timmesfeld.ARS.LinearMain
public import CFSG.Timmesfeld.ARS.Sec8Levi
public import CFSG.Timmesfeld.Special.TwoCore
public import CFSG.Timmesfeld.Transvection.PlaneGroup
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
  CFSG.LieType.BorelTits CFSG.Timmesfeld.Transvection.Pres
open scoped commutatorElement

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ} {hFn : Nat.card F = (2 ^ n) ^ 2}
  {r : ℕ} {hr : 2 ≤ r} {H : Type} [Group H] {Δ : Set (Subgroup H)}
  {P Q : Fin (2 * r / 2) → Subgroup H} {hm : 4 ≤ 2 * r}


variable {R : SURelations (2 * r / 2) (unitaryInvolution F 2 n) H}
variable {θ : SU (unitaryInvolution F 2 n) 3 →* H}

local notation "yroot " c:max => R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c

local notation "ybar " c:max => R.ξ (Sum.inl (cLastIdx r hr)) (Sum.inr (cPrevIdx r hr)) c

local notation "zroot " c:max => R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inl (cLastIdx r hr)) c

local notation "llong " c:max => R.ξL (Sum.inl (cLastIdx r hr)) c

local notation "lprev " c:max => R.ξL (Sum.inl (cPrevIdx r hr)) c

private theorem suHeis_three_congr {hm₁ hm₂ : ¬ Even 3} (a : Fin (3 / 2) ⊕ Fin (3 / 2))
    (u v : F) :
    suHeis (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn) hm₁ a u v =
      suHeis (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn) hm₂ a u v := by
  rw [show hm₁ = hm₂ from Subsingleton.elim _ _]

private noncomputable def heis3 (hFn : Nat.card F = (2 ^ n) ^ 2) (u v : F) :
    SU (unitaryInvolution F 2 n) 3 :=
  suHeis (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
    (Nat.not_even_two_mul_add_one 1 : ¬ Even 3) (Sum.inl (0 : Fin (3 / 2))) u v

private noncomputable def heis3' (hFn : Nat.card F = (2 ^ n) ^ 2) (u v : F) :
    SU (unitaryInvolution F 2 n) 3 :=
  suHeis (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
    (Nat.not_even_iff_odd.mpr ⟨1, rfl⟩) (Sum.inl (0 : Fin (3 / 2))) u v

private theorem heis3_eq_heis3' (hFn : Nat.card F = (2 ^ n) ^ 2) (u v : F) :
    heis3 hFn u v = heis3' hFn u v :=
  suHeis_three_congr (hFn := hFn) _ _ _

private theorem norm_pow_three {b : F} (hb : unitaryInvolution F 2 n b * b = 1) :
    unitaryInvolution F 2 n (b ^ 3) * b ^ 3 = 1 := by
  rw [map_pow, ← mul_pow, hb, one_pow]

private theorem norm_pow_six {b : F} (hb : unitaryInvolution F 2 n b * b = 1) :
    unitaryInvolution F 2 n (b ^ 6) * b ^ 6 = 1 := by
  rw [map_pow, ← mul_pow, hb, one_pow]

private theorem valid_mul_pow_three {b u v : F} (hb : unitaryInvolution F 2 n b * b = 1)
    (h : v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0) :
    v + unitaryInvolution F 2 n v +
      unitaryInvolution F 2 n (b ^ 3 * u) * (b ^ 3 * u) = 0 := by
  calc v + unitaryInvolution F 2 n v +
        unitaryInvolution F 2 n (b ^ 3 * u) * (b ^ 3 * u)
      = v + unitaryInvolution F 2 n v +
          (unitaryInvolution F 2 n (b ^ 3) * b ^ 3) * (unitaryInvolution F 2 n u * u) := by
        rw [map_mul]
        ring
    _ = v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u := by
        rw [norm_pow_three hb, one_mul]
    _ = 0 := h

private theorem heis_action_of_conj {b : F} {h : SU (unitaryInvolution F 2 n) 3}
    (hb : unitaryInvolution F 2 n b * b = 1)
    (hheis : ∀ u v : F, v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0 →
      h * heis3 hFn u v * h⁻¹ = heis3 hFn (b ^ 3 * u) v)
    {u v : F} (huv : v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0) :
    (θ h * θ h) * θ (heis3 hFn u v) * (θ h * θ h)⁻¹ = θ (heis3 hFn (b ^ 6 * u) v) := by
  have h1 : θ h * θ (heis3 hFn u v) * (θ h)⁻¹ = θ (heis3 hFn (b ^ 3 * u) v) := by
    rw [← map_inv, ← map_mul, ← map_mul, hheis u v huv]
  have h2 : θ h * θ (heis3 hFn (b ^ 3 * u) v) * (θ h)⁻¹ =
      θ (heis3 hFn (b ^ 3 * (b ^ 3 * u)) v) := by
    rw [← map_inv, ← map_mul, ← map_mul, hheis _ v (valid_mul_pow_three hb huv)]
  have hmul : b ^ 3 * (b ^ 3 * u) = b ^ 6 * u := by
    rw [← mul_assoc, ← pow_add]
  rw [hmul] at h2
  calc (θ h * θ h) * θ (heis3 hFn u v) * (θ h * θ h)⁻¹
      = θ h * (θ h * θ (heis3 hFn u v) * (θ h)⁻¹) * (θ h)⁻¹ := by group
    _ = θ h * θ (heis3 hFn (b ^ 3 * u) v) * (θ h)⁻¹ := by rw [h1]
    _ = θ (heis3 hFn (b ^ 6 * u) v) := h2

private theorem idx_prev_last :
    Pres.idx (Sum.inl (cPrevIdx r hr) : Fin (2 * r / 2) ⊕ Fin (2 * r / 2)) ≠
      Pres.idx (Sum.inr (cLastIdx r hr)) := by
  simpa using cPrevIdx_ne_cLastIdx hr

private theorem idx_last_prev :
    Pres.idx (Sum.inl (cLastIdx r hr) : Fin (2 * r / 2) ⊕ Fin (2 * r / 2)) ≠
      Pres.idx (Sum.inr (cPrevIdx r hr)) := by
  simpa using (cPrevIdx_ne_cLastIdx hr).symm

private theorem idx_prev_prev :
    Pres.idx (Sum.inl (cPrevIdx r hr) : Fin (2 * r / 2) ⊕ Fin (2 * r / 2)) ≠
      Pres.idx (Sum.inl (cLastIdx r hr)) := by
  simpa using cPrevIdx_ne_cLastIdx hr

private theorem yroot_add (s t : F) : yroot (s + t) = yroot s * yroot t :=
  R.add (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) idx_prev_last s t

private theorem ybar_add (s t : F) : ybar (s + t) = ybar s * ybar t :=
  R.add (Sum.inl (cLastIdx r hr)) (Sum.inr (cPrevIdx r hr)) idx_last_prev s t

private theorem zroot_zero : zroot (0 : F) = 1 :=
  R.map_zero (a := Sum.inl (cPrevIdx r hr)) (b := Sum.inl (cLastIdx r hr)) idx_prev_prev

private theorem zroot_add (s t : F) : zroot (s + t) = zroot s * zroot t :=
  R.add (Sum.inl (cPrevIdx r hr)) (Sum.inl (cLastIdx r hr)) idx_prev_prev s t

private theorem zroot_self (s : F) : zroot s * zroot s = 1 := by
  rw [← zroot_add, CharTwo.add_self_eq_zero, zroot_zero]

private theorem llong_zero : llong (0 : F) = 1 := R.mapL_zero _

private theorem llong_add {s t : F} (hs : unitaryInvolution F 2 n s = s)
    (ht : unitaryInvolution F 2 n t = t) : llong (s + t) = llong s * llong t :=
  R.addL _ s t hs ht

private theorem llong_self {s : F} (hs : unitaryInvolution F 2 n s = s) :
    llong s * llong s = 1 := by
  rw [← llong_add hs hs, CharTwo.add_self_eq_zero, llong_zero]

private theorem lprev_zero : lprev (0 : F) = 1 := R.mapL_zero _

private theorem lprev_add {s t : F} (hs : unitaryInvolution F 2 n s = s)
    (ht : unitaryInvolution F 2 n t = t) : lprev (s + t) = lprev s * lprev t :=
  R.addL _ s t hs ht

private theorem lprev_self {s : F} (hs : unitaryInvolution F 2 n s = s) :
    lprev s * lprev s = 1 := by
  rw [← lprev_add hs hs, CharTwo.add_self_eq_zero, lprev_zero]

private theorem shortLong_prev {s t : F} (ht : unitaryInvolution F 2 n t = t) :
    ⁅yroot s, llong t⁆ = zroot (s * t) * lprev (unitaryInvolution F 2 n s * s * t) :=
  R.shortLong (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) idx_prev_last s t ht

private theorem shortLong_last {s t : F} (ht : unitaryInvolution F 2 n t = t) :
    ⁅ybar s, lprev t⁆ =
      zroot (unitaryInvolution F 2 n (s * t)) *
        llong (unitaryInvolution F 2 n s * s * t) := by
  have h := R.shortLong (Sum.inl (cLastIdx r hr)) (Sum.inr (cPrevIdx r hr))
    idx_last_prev s t ht
  simp only [Sum.swap_inr] at h
  rw [R.swap (Sum.inl (cPrevIdx r hr)) (Sum.inl (cLastIdx r hr))
    idx_prev_prev (s * t)] at h
  simpa using h

private theorem trace_prev (s t : F) :
    ⁅yroot s, zroot t⁆ =
      lprev (s * unitaryInvolution F 2 n t + unitaryInvolution F 2 n s * t) :=
  R.trace (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) idx_prev_last s t

private theorem commLS_LP_y {s : F} (hs : unitaryInvolution F 2 n s = s) (t : F) :
    ⁅lprev s, yroot t⁆ = 1 :=
  R.commLS (Sum.inl (cPrevIdx r hr)) (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr))
    idx_prev_last (by simp)
    (by
      simp only [Sum.swap_inl, ne_eq, Sum.inr.injEq]
      exact Ne.symm (cPrevIdx_ne_cLastIdx hr))
    s t hs

private theorem conjSub_shortRootGroup_of_four (hΔ : IsRootClass Δ) {A B C D : Subgroup H}
    {g : H} (hA : conjSub A g = A) (hB : conjSub B g = B) (hC : conjSub C g = C)
    (hD : conjSub D g = D) :
    conjSub (shortRootGroup Δ A B C D) g = shortRootGroup Δ A B C D := by
  rw [← shortRootGroup_conjSub hΔ A B C D g, hA, hB, hC, hD]

private theorem commute_framePt_last (hR : R.HasFrameImages Δ P Q)
    (hd : OddFrameCompatible hFn hr (R.toHom hFn (even_two_mul r) hm) θ)
    {h : SU (unitaryInvolution F 2 n) 3}
    (hlong : ∀ (a : Fin (3 / 2) ⊕ Fin (3 / 2)) (c : F),
      h * suLong (unitaryInvolution F 2 n) a c * h⁻¹ = suLong (unitaryInvolution F 2 n) a c) :
    (∀ x ∈ P (cLastIdx r hr), Commute (θ h) x) ∧
      ∀ x ∈ Q (cLastIdx r hr), Commute (θ h) x := by
  have hPL : ∀ c : F, unitaryInvolution F 2 n c = c →
      Commute (θ h) (θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) c)) := by
    intro c hc
    have hh : θ h * θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) c) *
        (θ h)⁻¹ = θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) c) := by
      rw [← map_inv, ← map_mul, ← map_mul, hlong]
    exact mul_inv_eq_iff_eq_mul.1 hh
  have hQL : ∀ c : F, unitaryInvolution F 2 n c = c →
      Commute (θ h) (θ (suLong (unitaryInvolution F 2 n) (Sum.inr (0 : Fin (3 / 2))) c)) := by
    intro c hc
    have hh : θ h * θ (suLong (unitaryInvolution F 2 n) (Sum.inr (0 : Fin (3 / 2))) c) *
        (θ h)⁻¹ = θ (suLong (unitaryInvolution F 2 n) (Sum.inr (0 : Fin (3 / 2))) c) := by
      rw [← map_inv, ← map_mul, ← map_mul, hlong]
    exact mul_inv_eq_iff_eq_mul.1 hh
  constructor
  · intro x hx
    obtain ⟨c, hc, rfl⟩ := (hR.long (Sum.inl (cLastIdx r hr)) x).1 hx
    rw [← R.toHom_suLong hFn (even_two_mul r) hm (Sum.inl (cLastIdx r hr)) hc,
      (hd.long_last c hc).1]
    exact hPL c hc
  · intro x hx
    obtain ⟨c, hc, rfl⟩ := (hR.long (Sum.inr (cLastIdx r hr)) x).1 hx
    rw [← R.toHom_suLong hFn (even_two_mul r) hm (Sum.inr (cLastIdx r hr)) hc,
      (hd.long_last c hc).2]
    exact hQL c hc

private theorem commute_framePt_prev
    (hθr : θ.range = residueGroup Δ P Q (cLastIdx r hr)) {h : SU (unitaryInvolution F 2 n) 3} :
    (∀ x ∈ P (cPrevIdx r hr), Commute (θ h) x) ∧
      ∀ x ∈ Q (cPrevIdx r hr), Commute (θ h) x := by
  have ht : θ h ∈ residueGroup Δ P Q (cLastIdx r hr) := by
    rw [← hθr]
    exact ⟨h, rfl⟩
  have hcomm := commuting_residueGroup (Δ := Δ) (P := P) (Q := Q)
    (k := cLastIdx r hr) (i := cPrevIdx r hr)
    (cPrevIdx_ne_cLastIdx hr)
  exact ⟨fun x hx => hcomm (θ h) ht x (Subgroup.mem_sup_left hx),
    fun x hx => hcomm (θ h) ht x (Subgroup.mem_sup_right hx)⟩

private theorem llong_eq_one (hθo : Odd (Nat.card θ.ker))
    (hd : OddFrameCompatible hFn hr (R.toHom hFn (even_two_mul r) hm) θ) {c : F}
    (hc : unitaryInvolution F 2 n c = c) (h : llong c = 1) : c = 0 := by
  have hzero : heis3 hFn 0 0 = 1 := by
    rw [heis3, suHeis_zero_left, suLong_zero]
  have hc4 : llong c = θ (heis3 hFn 0 c) :=
    (OddFrameCompatible.ξL_inl_eq_map_suHeis hFn hr hm hd hc).1
  have h2 : θ (heis3 hFn 0 c) = θ (heis3 hFn 0 0) := by
    rw [← hc4, h, hzero, map_one]
  rw [heis3_eq_heis3' hFn 0 c, heis3_eq_heis3' hFn 0 0] at h2
  have hcc : c + unitaryInvolution F 2 n c + unitaryInvolution F 2 n (0 : F) * 0 = 0 := by
    rw [hc, CharTwo.add_self_eq_zero]
    simp
  have hc0 : (0 : F) + unitaryInvolution F 2 n (0 : F) + unitaryInvolution F 2 n (0 : F) * 0 = 0 :=
    by simp
  exact (Pres.eq_and_eq_of_map_suHeis_eq hFn hθo hcc hc0 h2).2

private theorem lprev_eq_one (hθo : Odd (Nat.card θ.ker))
    (hd : OddFrameCompatible hFn hr (R.toHom hFn (even_two_mul r) hm) θ) {c : F}
    (hc : unitaryInvolution F 2 n c = c) (h : lprev c = 1) : c = 0 := by
  have hker0 : (oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ).ker = θ.ker :=
    MonoidHom.ker_comp_of_injective θ _ (MulAut.conj _).injective
  have hker : Odd (Nat.card (oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ).ker) := by
    rw [hker0]
    exact hθo
  have hzero : heis3 hFn 0 0 = 1 := by
    rw [heis3, suHeis_zero_left, suLong_zero]
  have hc4 : lprev c = oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ (heis3 hFn 0 c) :=
    (OddFrameCompatible.ξL_inl_eq_map_suHeis hFn hr hm hd hc).2
  have h2 : oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ (heis3 hFn 0 c) =
      oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ (heis3 hFn 0 0) := by
    rw [← hc4, h, hzero, map_one]
  rw [heis3_eq_heis3' hFn 0 c, heis3_eq_heis3' hFn 0 0] at h2
  have hcc : c + unitaryInvolution F 2 n c + unitaryInvolution F 2 n (0 : F) * 0 = 0 := by
    rw [hc, CharTwo.add_self_eq_zero]
    simp
  have hc0 : (0 : F) + unitaryInvolution F 2 n (0 : F) + unitaryInvolution F 2 n (0 : F) * 0 = 0 :=
    by simp
  exact (Pres.eq_and_eq_of_map_suHeis_eq hFn hker hcc hc0 h2).2

private theorem yroot_inj (hθo : Odd (Nat.card θ.ker))
    (hd : OddFrameCompatible hFn hr (R.toHom hFn (even_two_mul r) hm) θ) {s t : F}
    (h : yroot s = yroot t) : s = t :=
  SURelations.eq_of_ξ_eq R (unitaryInvolution_involutive hFn) (exists_unitaryInvolution_ne hFn)
    idx_prev_last (fun u hu => lprev_eq_one hθo hd hu) h

private theorem zroot_inj (hθo : Odd (Nat.card θ.ker))
    (hd : OddFrameCompatible hFn hr (R.toHom hFn (even_two_mul r) hm) θ) {s t : F}
    (h : zroot s = zroot t) : s = t :=
  SURelations.eq_of_ξ_eq R (unitaryInvolution_involutive hFn) (exists_unitaryInvolution_ne hFn)
    idx_prev_prev (fun u hu => lprev_eq_one hθo hd hu) h

private theorem ybar_inj (hθo : Odd (Nat.card θ.ker))
    (hd : OddFrameCompatible hFn hr (R.toHom hFn (even_two_mul r) hm) θ) {s t : F}
    (h : ybar s = ybar t) : s = t :=
  SURelations.eq_of_ξ_eq R (unitaryInvolution_involutive hFn) (exists_unitaryInvolution_ne hFn)
    idx_last_prev (fun u hu => llong_eq_one hθo hd hu) h

private theorem zroot_eq_lprev_eq_one (hθo : Odd (Nat.card θ.ker))
    (hd : OddFrameCompatible hFn hr (R.toHom hFn (even_two_mul r) hm) θ) {u v : F}
    (hv : unitaryInvolution F 2 n v = v) (h : zroot u = lprev v) : u = 0 ∧ v = 0 := by
  have hzero : ∀ s : F, s * unitaryInvolution F 2 n u + unitaryInvolution F 2 n s * u = 0 := by
    intro s
    have hc1 : Commute (lprev v) (yroot s) :=
      commutatorElement_eq_one_iff_mul_comm.1 (commLS_LP_y hv s)
    have h1 : ⁅yroot s, lprev v⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2 hc1.symm
    rw [← h, trace_prev s u] at h1
    refine lprev_eq_one hθo hd ?_ h1
    rw [map_add, map_mul, map_mul, unitaryInvolution_involutive hFn,
      unitaryInvolution_involutive hFn, add_comm]
  have hκ : unitaryInvolution F 2 n u = 0 := by
    refine RelBuild.eq_zero_of_trace_mul (σ := unitaryInvolution F 2 n)
      (exists_unitaryInvolution_ne hFn) fun x => ?_
    calc unitaryInvolution F 2 n u * x +
          unitaryInvolution F 2 n (unitaryInvolution F 2 n u * x)
        = x * unitaryInvolution F 2 n u + unitaryInvolution F 2 n x * u := by
          rw [map_mul, unitaryInvolution_involutive hFn, mul_comm]
          ring
      _ = 0 := hzero x
  have hu : u = 0 := (map_eq_zero (unitaryInvolution F 2 n)).1 hκ
  refine ⟨hu, ?_⟩
  have h1 : lprev v = 1 := by rw [← h, hu, zroot_zero]
  exact lprev_eq_one hθo hd hv h1

private theorem zroot_mul_lprev_inj (hθo : Odd (Nat.card θ.ker))
    (hd : OddFrameCompatible hFn hr (R.toHom hFn (even_two_mul r) hm) θ) {a β a' β' : F}
    (hβ : unitaryInvolution F 2 n β = β) (hβ' : unitaryInvolution F 2 n β' = β')
    (h : zroot a * lprev β = zroot a' * lprev β') : a = a' ∧ β = β' := by
  have h1 : lprev β = zroot a * zroot a' * lprev β' := by
    have := congrArg (fun g => zroot a * g) h
    simpa [← mul_assoc, zroot_self] using this
  have h2 : zroot a * zroot a' * lprev (β + β') = 1 := by
    have h3 := congrArg (fun g => g * lprev β) h1
    rw [lprev_self hβ] at h3
    calc zroot a * zroot a' * lprev (β + β')
        = zroot a * zroot a' * (lprev β' * lprev β) := by
          rw [add_comm, lprev_add hβ' hβ]
      _ = (zroot a * zroot a' * lprev β') * lprev β := by group
      _ = 1 := h3.symm
  have hββ' : unitaryInvolution F 2 n (β + β') = β + β' := by rw [map_add, hβ, hβ']
  have h5 : zroot a * zroot a' = zroot a * zroot a' * (lprev (β + β') * lprev (β + β')) := by
    rw [lprev_self hββ', mul_one]
  have h3 : zroot (a + a') = lprev (β + β') := by
    rw [zroot_add, h5, ← mul_assoc (zroot a * zroot a') (lprev (β + β')) (lprev (β + β')),
      h2, one_mul]
  obtain ⟨haa, hbb⟩ := zroot_eq_lprev_eq_one hθo hd hββ' h3
  exact ⟨CharTwo.add_eq_zero.1 haa, CharTwo.add_eq_zero.1 hbb⟩

private theorem zroot_eq_llong_eq_one (hθo : Odd (Nat.card θ.ker))
    (hd : OddFrameCompatible hFn hr (R.toHom hFn (even_two_mul r) hm) θ) {u v : F}
    (hv : unitaryInvolution F 2 n v = v) (h : zroot u = llong v) : u = 0 ∧ v = 0 := by
  have hkey : ∀ s : F, lprev (s * unitaryInvolution F 2 n u + unitaryInvolution F 2 n s * u) =
      zroot (s * v) * lprev (unitaryInvolution F 2 n s * s * v) := by
    intro s
    rw [← trace_prev s u, h, ← shortLong_prev (s := s) (t := v) hv]
  have h1 : lprev (unitaryInvolution F 2 n u + u) = zroot v * lprev v := by
    simpa using hkey 1
  have h2 : zroot (0 : F) * lprev (unitaryInvolution F 2 n u + u) = zroot v * lprev v := by
    rw [h1, zroot_zero, one_mul]
  have hfix : unitaryInvolution F 2 n (unitaryInvolution F 2 n u + u) =
      unitaryInvolution F 2 n u + u := by
    rw [map_add, unitaryInvolution_involutive hFn, add_comm]
  obtain ⟨hv0, -⟩ := zroot_mul_lprev_inj hθo hd hfix hv h2
  have hvz : v = 0 := hv0.symm
  refine ⟨?_, hvz⟩
  have h3 : zroot u = 1 := by rw [h, hvz, llong_zero]
  exact zroot_inj hθo hd (by rw [h3, zroot_zero])

private theorem zroot_mul_llong_inj (hθo : Odd (Nat.card θ.ker))
    (hd : OddFrameCompatible hFn hr (R.toHom hFn (even_two_mul r) hm) θ) {a β a' β' : F}
    (hβ : unitaryInvolution F 2 n β = β) (hβ' : unitaryInvolution F 2 n β' = β')
    (h : zroot a * llong β = zroot a' * llong β') : a = a' ∧ β = β' := by
  have h1 : llong β = zroot a * zroot a' * llong β' := by
    have := congrArg (fun g => zroot a * g) h
    simpa [← mul_assoc, zroot_self] using this
  have h3 : llong β * llong β' = (zroot a * zroot a' * llong β') * llong β' :=
    congrArg (fun g => g * llong β') h1
  have h4 : (zroot a * zroot a' * llong β') * llong β' = zroot a * zroot a' := by
    rw [mul_assoc (zroot a * zroot a') (llong β') (llong β'), llong_self hβ', mul_one]
  have h2 : zroot (a + a') = llong (β + β') := by
    rw [zroot_add, llong_add hβ hβ']
    exact (h3.trans h4).symm
  have hββ' : unitaryInvolution F 2 n (β + β') = β + β' := by rw [map_add, hβ, hβ']
  obtain ⟨haa, hbb⟩ := zroot_eq_llong_eq_one hθo hd hββ' h2
  exact ⟨CharTwo.add_eq_zero.1 haa, CharTwo.add_eq_zero.1 hbb⟩

private theorem exists_conj_maps (hΔ : IsRootClass Δ) (hR : R.HasFrameImages Δ P Q)
    (hθr : θ.range = residueGroup Δ P Q (cLastIdx r hr)) (hθo : Odd (Nat.card θ.ker))
    (hd : OddFrameCompatible hFn hr (R.toHom hFn (even_two_mul r) hm) θ)
    {h : SU (unitaryInvolution F 2 n) 3}
    (hlong : ∀ (a : Fin (3 / 2) ⊕ Fin (3 / 2)) (c : F),
      h * suLong (unitaryInvolution F 2 n) a c * h⁻¹ = suLong (unitaryInvolution F 2 n) a c) :
    ∃ χ χ' χz : F → F,
      (∀ s, θ h * yroot s * (θ h)⁻¹ = yroot (χ s)) ∧
      (∀ s, θ h * ybar s * (θ h)⁻¹ = ybar (χ' s)) ∧
      (∀ s, θ h * zroot s * (θ h)⁻¹ = zroot (χz s)) ∧
      (∀ s t, χ (s + t) = χ s + χ t) ∧
      (∀ s t, χ' (s + t) = χ' s + χ' t) := by
  obtain ⟨hPL, hQL⟩ := commute_framePt_last hR hd hlong
  obtain ⟨hPP, hQP⟩ := commute_framePt_prev (Δ := Δ) (P := P) (Q := Q) (θ := θ) hθr
  have hPL' : conjSub (P (cLastIdx r hr)) (θ h) = P (cLastIdx r hr) :=
    conjSub_of_forall_commute hPL
  have hQL' : conjSub (Q (cLastIdx r hr)) (θ h) = Q (cLastIdx r hr) :=
    conjSub_of_forall_commute hQL
  have hPP' : conjSub (P (cPrevIdx r hr)) (θ h) = P (cPrevIdx r hr) :=
    conjSub_of_forall_commute hPP
  have hQP' : conjSub (Q (cPrevIdx r hr)) (θ h) = Q (cPrevIdx r hr) :=
    conjSub_of_forall_commute hQP
  set Gy := shortRootGroup Δ (framePt P Q (Sum.inl (cPrevIdx r hr)))
    (framePt P Q (Sum.swap (Sum.inl (cPrevIdx r hr)))) (framePt P Q (Sum.inr (cLastIdx r hr)))
    (framePt P Q (Sum.swap (Sum.inr (cLastIdx r hr)))) with hGydef
  set Gyb := shortRootGroup Δ (framePt P Q (Sum.inl (cLastIdx r hr)))
    (framePt P Q (Sum.swap (Sum.inl (cLastIdx r hr)))) (framePt P Q (Sum.inr (cPrevIdx r hr)))
    (framePt P Q (Sum.swap (Sum.inr (cPrevIdx r hr)))) with hGybdef
  set Gz := shortRootGroup Δ (framePt P Q (Sum.inl (cPrevIdx r hr)))
    (framePt P Q (Sum.swap (Sum.inl (cPrevIdx r hr)))) (framePt P Q (Sum.inl (cLastIdx r hr)))
    (framePt P Q (Sum.swap (Sum.inl (cLastIdx r hr)))) with hGzdef
  have hGy : conjSub Gy (θ h) = Gy := by
    rw [hGydef]
    exact conjSub_shortRootGroup_of_four hΔ hPP' hQP' hQL' hPL'
  have hGyb : conjSub Gyb (θ h) = Gyb := by
    rw [hGybdef]
    exact conjSub_shortRootGroup_of_four hΔ hPL' hQL' hQP' hPP'
  have hGz : conjSub Gz (θ h) = Gz := by
    rw [hGzdef]
    exact conjSub_shortRootGroup_of_four hΔ hPP' hQP' hPL' hQL'
  have hexY : ∀ s : F, ∃ s' : F, yroot s' = θ h * yroot s * (θ h)⁻¹ := by
    intro s
    have hmem : θ h * yroot s * (θ h)⁻¹ ∈ Gy := by
      have h1 := conj_mem_conjSub (θ h)
        ((hR.short (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) idx_prev_last _).2
          ⟨s, rfl⟩)
      rwa [hGy] at h1
    exact (hR.short (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) idx_prev_last _).1 hmem
  choose χ hχ using hexY
  have hexYb : ∀ s : F, ∃ s' : F, ybar s' = θ h * ybar s * (θ h)⁻¹ := by
    intro s
    have hmem : θ h * ybar s * (θ h)⁻¹ ∈ Gyb := by
      have h1 := conj_mem_conjSub (θ h)
        ((hR.short (Sum.inl (cLastIdx r hr)) (Sum.inr (cPrevIdx r hr)) idx_last_prev _).2
          ⟨s, rfl⟩)
      rwa [hGyb] at h1
    exact (hR.short (Sum.inl (cLastIdx r hr)) (Sum.inr (cPrevIdx r hr)) idx_last_prev _).1 hmem
  choose χ' hχ' using hexYb
  have hexZ : ∀ s : F, ∃ s' : F, zroot s' = θ h * zroot s * (θ h)⁻¹ := by
    intro s
    have hmem : θ h * zroot s * (θ h)⁻¹ ∈ Gz := by
      have h1 := conj_mem_conjSub (θ h)
        ((hR.short (Sum.inl (cPrevIdx r hr)) (Sum.inl (cLastIdx r hr)) idx_prev_prev _).2
          ⟨s, rfl⟩)
      rwa [hGz] at h1
    exact (hR.short (Sum.inl (cPrevIdx r hr)) (Sum.inl (cLastIdx r hr)) idx_prev_prev _).1 hmem
  choose χz hχz using hexZ
  have hχadd : ∀ s t : F, χ (s + t) = χ s + χ t := by
    intro s t
    refine yroot_inj hθo hd ?_
    rw [yroot_add, hχ (s + t), hχ s, hχ t, yroot_add]
    group
  have hχ'add : ∀ s t : F, χ' (s + t) = χ' s + χ' t := by
    intro s t
    refine ybar_inj hθo hd ?_
    rw [ybar_add, hχ' (s + t), hχ' s, hχ' t, ybar_add]
    group
  exact ⟨χ, χ', χz, fun s => (hχ s).symm, fun s => (hχ' s).symm,
    fun s => (hχz s).symm, hχadd, hχ'add⟩

private theorem conj_maps_norm (hR : R.HasFrameImages Δ P Q) (hθo : Odd (Nat.card θ.ker))
    (hd : OddFrameCompatible hFn hr (R.toHom hFn (even_two_mul r) hm) θ)
    {h : SU (unitaryInvolution F 2 n) 3}
    (hPP : ∀ x ∈ P (cPrevIdx r hr), Commute (θ h) x)
    (hPL : ∀ x ∈ P (cLastIdx r hr), Commute (θ h) x) {χ χ' χz : F → F}
    (hχ : ∀ s, θ h * yroot s * (θ h)⁻¹ = yroot (χ s))
    (hχ' : ∀ s, θ h * ybar s * (θ h)⁻¹ = ybar (χ' s))
    (hχz : ∀ s, θ h * zroot s * (θ h)⁻¹ = zroot (χz s)) :
    (∀ s, unitaryInvolution F 2 n (χ s) * χ s = unitaryInvolution F 2 n s * s) ∧
      (∀ s, unitaryInvolution F 2 n (χ' s) * χ' s = unitaryInvolution F 2 n s * s) ∧
      ∀ s, χ (unitaryInvolution F 2 n s) = unitaryInvolution F 2 n (χ' s) := by
  have hconj : ∀ a b : H,
      θ h * ⁅a, b⁆ * (θ h)⁻¹ = ⁅θ h * a * (θ h)⁻¹, θ h * b * (θ h)⁻¹⁆ := by
    intro a b
    rw [commutatorElement_def, commutatorElement_def]
    group
  have hconjP : ∀ t : F, unitaryInvolution F 2 n t = t → θ h * lprev t * (θ h)⁻¹ = lprev t := by
    intro t ht
    rw [(hPP _ ((hR.long (Sum.inl (cPrevIdx r hr)) _).2 ⟨t, ht, rfl⟩)).eq]
    group
  have hconjL : ∀ t : F, unitaryInvolution F 2 n t = t → θ h * llong t * (θ h)⁻¹ = llong t := by
    intro t ht
    rw [(hPL _ ((hR.long (Sum.inl (cLastIdx r hr)) _).2 ⟨t, ht, rfl⟩)).eq]
    group
  have hfix : ∀ s : F, unitaryInvolution F 2 n (unitaryInvolution F 2 n s * s) =
      unitaryInvolution F 2 n s * s := fun s => by
    rw [map_mul, unitaryInvolution_involutive hFn, mul_comm]
  have key1 : ∀ s : F, zroot (χz s) * lprev (unitaryInvolution F 2 n s * s) =
      zroot (χ s) * lprev (unitaryInvolution F 2 n (χ s) * χ s) := by
    intro s
    have h2 : θ h * ⁅yroot s, llong (1 : F)⁆ * (θ h)⁻¹ = ⁅yroot (χ s), llong (1 : F)⁆ := by
      rw [hconj, hχ s, hconjL 1 (map_one _)]
    rw [shortLong_prev (t := 1) (by simp), shortLong_prev (t := 1) (by simp),
      mul_one, mul_one, mul_one, mul_one] at h2
    rw [show θ h * (zroot s * lprev (unitaryInvolution F 2 n s * s)) * (θ h)⁻¹ =
      (θ h * zroot s * (θ h)⁻¹) *
        (θ h * lprev (unitaryInvolution F 2 n s * s) * (θ h)⁻¹) from by group,
      hχz s, hconjP _ (hfix s)] at h2
    exact h2
  have key2 : ∀ s : F, zroot (χz (unitaryInvolution F 2 n s)) *
      llong (unitaryInvolution F 2 n s * s) =
      zroot (unitaryInvolution F 2 n (χ' s)) *
        llong (unitaryInvolution F 2 n (χ' s) * χ' s) := by
    intro s
    have h2 : θ h * ⁅ybar s, lprev (1 : F)⁆ * (θ h)⁻¹ = ⁅ybar (χ' s), lprev (1 : F)⁆ := by
      rw [hconj, hχ' s, hconjP 1 (map_one _)]
    rw [shortLong_last (t := 1) (by simp), shortLong_last (t := 1) (by simp),
      mul_one, mul_one, mul_one, mul_one] at h2
    rw [show θ h * (zroot (unitaryInvolution F 2 n s) *
        llong (unitaryInvolution F 2 n s * s)) * (θ h)⁻¹ =
      (θ h * zroot (unitaryInvolution F 2 n s) * (θ h)⁻¹) *
        (θ h * llong (unitaryInvolution F 2 n s * s) * (θ h)⁻¹) from by group,
      hχz _, hconjL _ (hfix s)] at h2
    exact h2
  have hZ : ∀ s : F, χz s = χ s := fun s =>
    (zroot_mul_lprev_inj hθo hd (hfix s) (hfix (χ s)) (key1 s)).1
  refine ⟨fun s => (zroot_mul_lprev_inj hθo hd (hfix s) (hfix (χ s)) (key1 s)).2.symm,
    fun s => (zroot_mul_llong_inj hθo hd (hfix s) (hfix (χ' s)) (key2 s)).2.symm, ?_⟩
  intro s
  have h1 := (zroot_mul_llong_inj hθo hd (hfix s) (hfix (χ' s)) (key2 s)).1
  rw [← hZ (unitaryInvolution F 2 n s)]
  exact h1

private theorem exists_scalar_action (hΔ : IsRootClass Δ) (hR : R.HasFrameImages Δ P Q)
    (hθr : θ.range = residueGroup Δ P Q (cLastIdx r hr)) (hθo : Odd (Nat.card θ.ker))
    (hd : OddFrameCompatible hFn hr (R.toHom hFn (even_two_mul r) hm) θ)
    {h : SU (unitaryInvolution F 2 n) 3}
    (hlong : ∀ (a : Fin (3 / 2) ⊕ Fin (3 / 2)) (c : F),
      h * suLong (unitaryInvolution F 2 n) a c * h⁻¹ = suLong (unitaryInvolution F 2 n) a c) :
    ∃ κ κ' : F, κ ≠ 0 ∧ unitaryInvolution F 2 n κ * κ = 1 ∧ κ' = κ⁻¹ ∧
      (∀ s : F, (θ h * θ h) * yroot s * (θ h * θ h)⁻¹ = yroot (κ * s)) ∧
      ∀ s : F, (θ h * θ h) * ybar s * (θ h * θ h)⁻¹ = ybar (κ' * s) := by
  obtain ⟨hPL, -⟩ := commute_framePt_last hR hd hlong
  obtain ⟨hPP, -⟩ := commute_framePt_prev (Δ := Δ) (P := P) (Q := Q) (θ := θ) hθr
  obtain ⟨χ, χ', χz, hχ, hχ', hχz, hχadd, hχ'add⟩ :=
    exists_conj_maps hΔ hR hθr hθo hd hlong
  obtain ⟨hN, hN', hσ⟩ := conj_maps_norm hR hθo hd hPP hPL hχ hχ' hχz
  obtain ⟨e, he⟩ := RelBuild.exists_tw_of_add_of_norm (σ := unitaryInvolution F 2 n) (φ := χ)
    hχadd (m := 1) (by intro s; rw [one_mul]; exact hN s)
  obtain ⟨e', he'⟩ := RelBuild.exists_tw_of_add_of_norm (σ := unitaryInvolution F 2 n) (φ := χ')
    hχ'add (m := 1) (by intro s; rw [one_mul]; exact hN' s)
  have hrel : ∀ u : F, χ 1 * RelBuild.tw (unitaryInvolution F 2 n) e u =
      unitaryInvolution F 2 n (χ' 1) * RelBuild.tw (unitaryInvolution F 2 n) e' u := by
    intro u
    obtain ⟨s, rfl⟩ := (unitaryInvolution F 2 n).surjective u
    have h := hσ s
    rwa [he (unitaryInvolution F 2 n s), he' s, map_mul, RelBuild.σ_tw] at h
  have hκ0 : χ 1 = unitaryInvolution F 2 n (χ' 1) := by
    have h := hrel 1
    simpa using h
  have hκ1ne : χ 1 ≠ 0 := by
    intro h0
    have h1 := hN 1
    rw [h0, map_zero, zero_mul] at h1
    simpa using h1
  have hee : e = e' := by
    refine RelBuild.eq_of_tw_eq (exists_unitaryInvolution_ne hFn) fun u => ?_
    have h := hrel u
    rw [hκ0] at h
    exact mul_left_cancel₀ (by rw [← hκ0]; exact hκ1ne) h
  set κ : F := χ 1 * RelBuild.tw (unitaryInvolution F 2 n) e (χ 1) with hκdef
  set κ' : F := χ' 1 * RelBuild.tw (unitaryInvolution F 2 n) e' (χ' 1) with hκ'def
  have hχχ : ∀ s : F, χ (χ s) = κ * s := by
    intro s
    rw [he (χ s), he s, RelBuild.tw_mul,
      RelBuild.tw_tw_self (unitaryInvolution_involutive hFn), ← mul_assoc, ← hκdef]
  have hχ'χ' : ∀ s : F, χ' (χ' s) = κ' * s := by
    intro s
    rw [he' (χ' s), he' s, RelBuild.tw_mul,
      RelBuild.tw_tw_self (unitaryInvolution_involutive hFn), ← mul_assoc, ← hκ'def]
  have hNκ : unitaryInvolution F 2 n κ * κ = 1 := by
    have h1 : unitaryInvolution F 2 n (χ (χ 1)) * χ (χ 1) =
        unitaryInvolution F 2 n (1 : F) * 1 := (hN (χ 1)).trans (hN 1)
    rw [hχχ 1, mul_one] at h1
    simpa using h1
  have hσκ' : unitaryInvolution F 2 n κ' = κ := by
    have h1 : unitaryInvolution F 2 n (χ' (χ' 1)) = χ (unitaryInvolution F 2 n (χ' 1)) :=
      (hσ (χ' 1)).symm
    rw [he' (χ' 1), ← hκ'def, ← hκ0, he (χ 1), ← hκdef] at h1
    exact h1
  have hκ'inv : κ' = κ⁻¹ := by
    have h1 : unitaryInvolution F 2 n (unitaryInvolution F 2 n κ') =
        unitaryInvolution F 2 n κ := by rw [hσκ']
    rw [unitaryInvolution_involutive hFn] at h1
    rw [h1, inv_eq_of_mul_eq_one_left hNκ]
  have hκ0ne : κ ≠ 0 := by
    intro h0
    rw [h0] at hNκ
    simpa using hNκ
  refine ⟨κ, κ', hκ0ne, hNκ, hκ'inv, ?_, ?_⟩
  · intro s
    rw [show (θ h * θ h) * yroot s * (θ h * θ h)⁻¹ =
      θ h * (θ h * yroot s * (θ h)⁻¹) * (θ h)⁻¹ from by group, hχ s, hχ (χ s), hχχ]
  · intro s
    rw [show (θ h * θ h) * ybar s * (θ h * θ h)⁻¹ =
      θ h * (θ h * ybar s * (θ h)⁻¹) * (θ h)⁻¹ from by group, hχ' s, hχ' (χ' s), hχ'χ']

private theorem commute_weyl_torus (hΔ : IsRootClass Δ) (hR : R.HasFrameImages Δ P Q)
    (hθr : θ.range = residueGroup Δ P Q (cLastIdx r hr)) (hθo : Odd (Nat.card θ.ker))
    (hd : OddFrameCompatible hFn hr (R.toHom hFn (even_two_mul r) hm) θ)
    {h : SU (unitaryInvolution F 2 n) 3}
    (hlong : ∀ (a : Fin (3 / 2) ⊕ Fin (3 / 2)) (c : F),
      h * suLong (unitaryInvolution F 2 n) a c * h⁻¹ = suLong (unitaryInvolution F 2 n) a c)
    {c : F} (hc : c ≠ 0) :
    Commute (θ h * θ h) (((R.toHom hFn (even_two_mul r) hm)
        (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
          (cPrevIdx r hr)))⁻¹ *
      (yroot c * ybar (-c⁻¹) * yroot c)) := by
  obtain ⟨κ, κ', hκne, hNκ, hκ'inv, hactY, hactYb⟩ :=
    exists_scalar_action hΔ hR hθr hθo hd hlong
  have hk : (cPrevIdx r hr).val + 1 < 2 * r / 2 := by
    simp only [cPrevIdx, Fin.val_mk]
    omega
  set t : H := θ h * θ h with ht
  set W : H := (R.toHom hFn (even_two_mul r) hm)
    (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩ (cPrevIdx r hr))
    with hWdef
  set wc : H := yroot c * ybar (-c⁻¹) * yroot c with hwcdef
  have hΨ : ∀ u : F, (R.toHom hFn (even_two_mul r) hm)
      (shortWeyl (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
        (lowIdx_ne_succ hk) (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _) u) =
      yroot u * ybar (-u⁻¹) * yroot u :=
    fun u => SURelations.toHom_shortWeyl_cPrevIdx (R := R) hFn hr hm hk u
  have hW : W = yroot 1 * ybar (-1⁻¹) * yroot 1 :=
    hWdef.trans (SURelations.toHom_levelWeyl_cPrevIdx (R := R) hFn hr hm)
  have hwu : ∀ u : F, u ≠ 0 → t * (yroot u * ybar (-u⁻¹) * yroot u) * t⁻¹ =
      yroot (κ * u) * ybar (-(κ * u)⁻¹) * yroot (κ * u) := by
    intro u hu
    have h1 : κ' * (-u⁻¹) = -(κ * u)⁻¹ := by
      rw [hκ'inv, mul_neg, neg_inj, mul_inv_rev, mul_comm]
    rw [ht]
    rw [show (θ h * θ h) * (yroot u * ybar (-u⁻¹) * yroot u) * (θ h * θ h)⁻¹ =
      ((θ h * θ h) * yroot u * (θ h * θ h)⁻¹) *
        ((θ h * θ h) * ybar (-u⁻¹) * (θ h * θ h)⁻¹) *
        ((θ h * θ h) * yroot u * (θ h * θ h)⁻¹) from by group,
      hactY u, hactYb (-u⁻¹), h1]
  have hB4 : (shortWeyl (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
        (lowIdx_ne_succ hk) (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _) κ)⁻¹ *
      shortWeyl (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
        (lowIdx_ne_succ hk) (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _) (κ * c) =
      (shortWeyl (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
        (lowIdx_ne_succ hk) (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _) 1)⁻¹ *
      shortWeyl (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
        (lowIdx_ne_succ hk) (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _) c :=
    shortWeyl_inv_mul_shortWeyl_mul (unitaryInvolution_involutive hFn) (lowIdx_ne_succ hk)
      (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _) hκne hc
  have hmain : t * (W⁻¹ * wc) * t⁻¹ = W⁻¹ * wc := by
    rw [show t * (W⁻¹ * wc) * t⁻¹ = (t * W * t⁻¹)⁻¹ * (t * wc * t⁻¹) from by group]
    rw [hW, hwcdef, hwu 1 one_ne_zero, hwu c hc]
    rw [← hΨ (κ * 1), ← hΨ (κ * c), ← hΨ 1, ← hΨ c, mul_one]
    rw [← map_inv, ← map_mul, hB4, map_mul, map_inv]
  exact mul_inv_eq_iff_eq_mul.1 hmain

theorem SURelations.HasFrameImages.exists_commute_conj_map_suHeis
    (hΔ : IsRootClass Δ) {R : SURelations (2 * r / 2) (unitaryInvolution F 2 n) H}
    (hR : R.HasFrameImages Δ P Q) {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hn : 2 ≤ n)
    (hθr : θ.range = residueGroup Δ P Q (cLastIdx r hr)) (hθo : Odd (Nat.card θ.ker))
    (hd : OddFrameCompatible hFn hr (R.toHom hFn (even_two_mul r) hm) θ) :
    ∃ t : H, ∃ ρ : F, ρ ≠ 1 ∧ unitaryInvolution F 2 n ρ * ρ = 1 ∧
      (∀ u v : F, v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0 →
        t * θ (suHeis (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
          (Nat.not_even_two_mul_add_one 1 : ¬ Even 3) (Sum.inl (0 : Fin (3 / 2))) u v) * t⁻¹ =
        θ (suHeis (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
          (Nat.not_even_two_mul_add_one 1 : ¬ Even 3) (Sum.inl (0 : Fin (3 / 2))) (ρ * u) v)) ∧
      ∀ c : F, c ≠ 0 → Commute t (((R.toHom hFn (even_two_mul r) hm)
        (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
          (cPrevIdx r hr)))⁻¹ *
        (R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c *
          R.ξ (Sum.inl (cLastIdx r hr)) (Sum.inr (cPrevIdx r hr)) (-c⁻¹) *
          R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c)) := by
  obtain ⟨b, hb, hb6⟩ := RelBuild.exists_norm_eq_one_pow_six_ne_one hFn hn
  obtain ⟨h, hheis, hlong⟩ := Pres.exists_conj_suHeis_eq_pow_three hFn hb
  have hheis' : ∀ u v : F, v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0 →
      h * suHeis (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
        (Nat.not_even_two_mul_add_one 1 : ¬ Even 3) (Sum.inl (0 : Fin (3 / 2))) u v * h⁻¹ =
      suHeis (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
        (Nat.not_even_two_mul_add_one 1 : ¬ Even 3) (Sum.inl (0 : Fin (3 / 2))) (b ^ 3 * u) v := by
    intro u v huv
    have h1 := hheis u v huv
    rwa [suHeis_three_congr (hFn := hFn) (hm₂ := Nat.not_even_two_mul_add_one 1)
        (Sum.inl (0 : Fin (3 / 2))) u v,
      suHeis_three_congr (hFn := hFn) (hm₂ := Nat.not_even_two_mul_add_one 1)
        (Sum.inl (0 : Fin (3 / 2))) (b ^ 3 * u) v] at h1
  exact ⟨θ h * θ h, b ^ 6, hb6, norm_pow_six hb,
    fun u v huv => heis_action_of_conj (hFn := hFn) hb hheis' huv,
    fun c hc => commute_weyl_torus hΔ hR hθr hθo hd hlong hc⟩

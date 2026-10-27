module

public import CFSG.Timmesfeld.Bridge.OddRootNoSz
public import CFSG.Timmesfeld.Bridge.OddRootSzMainSetup
import CFSG.Timmesfeld.Bridge.OddRootSzMainTrivial
import CFSG.Timmesfeld.Bridge.OddRootSzMainQ
import CFSG.Timmesfeld.Bridge.OddRootOrbit
import CFSG.GroupTheory.Commutator.ThreeSubgroupsModNormal

public section

namespace CFSG.Timmesfeld.Bridge.OddRoot

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
  CFSG.Timmesfeld.Bridge.OddTransp
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {D : Set G} {d e : G} {E : Set G} {n : ℕ}

private theorem szZ_commute_closure (E : Set G) :
    ∀ z ∈ szZ E, ∀ q ∈ Subgroup.closure E, Commute z q := by
  intro z hz q hq
  have hzc : z ∈ Subgroup.centralizer (Subgroup.closure E : Set G) := by
    rw [Subgroup.centralizer_closure]
    exact hz.2
  exact (Subgroup.mem_centralizer_iff.mp hzc q hq).symm

private theorem SzCfg.closure_le_normalizer_szZ (c : SzCfg G D d E e n) :
    Subgroup.closure E ≤ Subgroup.normalizer (szZ E : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    exact c.conj_mem_szZ hh hz
  · intro hz
    have hz' : h⁻¹ * (h * z * h⁻¹) * h ∈ szZ E := by
      simpa only [inv_inv] using c.conj_mem_szZ (Subgroup.inv_mem _ hh) hz
    have hEq : h⁻¹ * (h * z * h⁻¹) * h = z := by group
    rwa [hEq] at hz'

private theorem SzCfg.mul_commutator_eq (c : SzCfg G D d E e n) {y u w : G}
    (hy : y ∈ szQ E) (hu : u ∈ szQ E) (hw : w ∈ szQ E) :
    (w * y⁻¹ * u⁻¹ * w⁻¹ * y) * u =
      ⁅y⁻¹, u⁻¹⁆ * ⁅w, u⁻¹⁆ * ⁅w, y⁻¹⁆ := by
  have hz1 : ⁅y⁻¹, u⁻¹⁆ ∈ szZ E :=
    c.commutator_mem_szZ ((szQ E).inv_mem hy) ((szQ E).inv_mem hu)
  have hz2 : ⁅w, u⁻¹⁆ ∈ szZ E :=
    c.commutator_mem_szZ hw ((szQ E).inv_mem hu)
  have hz3 : ⁅w, y⁻¹⁆ ∈ szZ E := c.commutator_mem_szZ hw ((szQ E).inv_mem hy)
  have hZcomm := szZ_commute_closure E
  have hA : y⁻¹ * u⁻¹ = ⁅y⁻¹, u⁻¹⁆ * (u⁻¹ * y⁻¹) := by
    rw [commutatorElement_def]
    group
  have hB : w * u⁻¹ = ⁅w, u⁻¹⁆ * (u⁻¹ * w) := by
    rw [commutatorElement_def]
    group
  have hC : w * y⁻¹ * w⁻¹ * y = ⁅w, y⁻¹⁆ := by
    rw [commutatorElement_def, inv_inv]
  have hD : u⁻¹ * ⁅w, y⁻¹⁆ = ⁅w, y⁻¹⁆ * u⁻¹ :=
    (hZcomm _ hz3 u (szQ_le_closure E hu)).inv_right.eq.symm
  calc
    (w * y⁻¹ * u⁻¹ * w⁻¹ * y) * u
        = w * (y⁻¹ * u⁻¹) * w⁻¹ * y * u := by group
    _ = w * (⁅y⁻¹, u⁻¹⁆ * (u⁻¹ * y⁻¹)) * w⁻¹ * y * u := by rw [hA]
    _ = ⁅y⁻¹, u⁻¹⁆ * (w * (u⁻¹ * y⁻¹) * w⁻¹ * y * u) := by
      rw [← mul_assoc w ⁅y⁻¹, u⁻¹⁆ (u⁻¹ * y⁻¹)]
      rw [show w * ⁅y⁻¹, u⁻¹⁆ = ⁅y⁻¹, u⁻¹⁆ * w from
        (hZcomm _ hz1 w (szQ_le_closure E hw)).eq.symm]
      group
    _ = ⁅y⁻¹, u⁻¹⁆ * ((w * u⁻¹) * y⁻¹ * w⁻¹ * y * u) := by group
    _ = ⁅y⁻¹, u⁻¹⁆ * ((⁅w, u⁻¹⁆ * (u⁻¹ * w)) * y⁻¹ * w⁻¹ * y * u) := by
      rw [hB]
    _ = ⁅y⁻¹, u⁻¹⁆ * (⁅w, u⁻¹⁆ * (u⁻¹ * (w * y⁻¹ * w⁻¹ * y) * u)) := by
      group
    _ = ⁅y⁻¹, u⁻¹⁆ * (⁅w, u⁻¹⁆ * (u⁻¹ * ⁅w, y⁻¹⁆ * u)) := by rw [hC]
    _ = ⁅y⁻¹, u⁻¹⁆ * (⁅w, u⁻¹⁆ * ⁅w, y⁻¹⁆) := by rw [hD]; group
    _ = ⁅y⁻¹, u⁻¹⁆ * ⁅w, u⁻¹⁆ * ⁅w, y⁻¹⁆ := by group

private theorem SzCfg.conj_commutator_eq_mul (c : SzCfg G D d E e n) {s y t u w : G}
    (hy : y ∈ szQ E) (htE : t ∈ E) (hu : u = ⁅s, y⁆)
    (hw : w = t⁻¹ * (s * t * s⁻¹))
    (huQ : u ∈ szQ E) (hwQ : w ∈ szQ E) (huCommt : Commute u t) :
    ⁅s, ⁅y, t⁆⁆ =
      (⁅y⁻¹, u⁻¹⁆ * ⁅w, u⁻¹⁆ * ⁅w, y⁻¹⁆) * ⁅u, y⁆ := by
  have hPu := c.mul_commutator_eq hy huQ hwQ
  have hz1 : ⁅y⁻¹, u⁻¹⁆ ∈ szZ E :=
    c.commutator_mem_szZ ((szQ E).inv_mem hy) ((szQ E).inv_mem huQ)
  have hz2 : ⁅w, u⁻¹⁆ ∈ szZ E := c.commutator_mem_szZ hwQ ((szQ E).inv_mem huQ)
  have hz3 : ⁅w, y⁻¹⁆ ∈ szZ E := c.commutator_mem_szZ hwQ ((szQ E).inv_mem hy)
  have hZcomm := szZ_commute_closure E
  have hZzt : Commute (⁅y⁻¹, u⁻¹⁆ * ⁅w, u⁻¹⁆ * ⁅w, y⁻¹⁆) t :=
    ((hZcomm _ hz1 t (Subgroup.subset_closure htE)).mul_left
      (hZcomm _ hz2 t (Subgroup.subset_closure htE))).mul_left
        (hZcomm _ hz3 t (Subgroup.subset_closure htE))
  have hZzy : Commute (⁅y⁻¹, u⁻¹⁆ * ⁅w, u⁻¹⁆ * ⁅w, y⁻¹⁆) y :=
    ((hZcomm _ hz1 y (szQ_le_closure E hy)).mul_left
      (hZcomm _ hz2 y (szQ_le_closure E hy))).mul_left
        (hZcomm _ hz3 y (szQ_le_closure E hy))
  have hZzu : Commute (⁅y⁻¹, u⁻¹⁆ * ⁅w, u⁻¹⁆ * ⁅w, y⁻¹⁆) u :=
    ((hZcomm _ hz1 u (szQ_le_closure E huQ)).mul_left
      (hZcomm _ hz2 u (szQ_le_closure E huQ))).mul_left
        (hZcomm _ hz3 u (szQ_le_closure E huQ))
  have hconj : s * ⁅y, t⁆ * s⁻¹ = ⁅u * y, t * w⁆ := by
    rw [commutatorElement_def, hu, hw]
    group
  have hEq : ⁅s, ⁅y, t⁆⁆ = ⁅u * y, t * w⁆ * ⁅y, t⁆⁻¹ := by
    change s * ⁅y, t⁆ * s⁻¹ * ⁅y, t⁆⁻¹ = ⁅u * y, t * w⁆ * ⁅y, t⁆⁻¹
    rw [hconj]
  have hMain : ⁅u * y, t * w⁆ * ⁅y, t⁆⁻¹ =
      u * y * t * (w * y⁻¹ * u⁻¹ * w⁻¹ * y) * t⁻¹ * y⁻¹ := by
    rw [commutatorElement_def, commutatorElement_def]
    group
  have hP : w * y⁻¹ * u⁻¹ * w⁻¹ * y =
      (⁅y⁻¹, u⁻¹⁆ * ⁅w, u⁻¹⁆ * ⁅w, y⁻¹⁆) * u⁻¹ := by
    calc w * y⁻¹ * u⁻¹ * w⁻¹ * y
        = ((w * y⁻¹ * u⁻¹ * w⁻¹ * y) * u) * u⁻¹ := by group
      _ = (⁅y⁻¹, u⁻¹⁆ * ⁅w, u⁻¹⁆ * ⁅w, y⁻¹⁆) * u⁻¹ := by rw [hPu]
  have hstep : u * y * t * (⁅y⁻¹, u⁻¹⁆ * ⁅w, u⁻¹⁆ * ⁅w, y⁻¹⁆ * u⁻¹) *
        t⁻¹ * y⁻¹ =
      (⁅y⁻¹, u⁻¹⁆ * ⁅w, u⁻¹⁆ * ⁅w, y⁻¹⁆) * ⁅u, y⁆ := by
    have ht : t * (⁅y⁻¹, u⁻¹⁆ * ⁅w, u⁻¹⁆ * ⁅w, y⁻¹⁆) * t⁻¹ =
        ⁅y⁻¹, u⁻¹⁆ * ⁅w, u⁻¹⁆ * ⁅w, y⁻¹⁆ := by
      rw [show t * (⁅y⁻¹, u⁻¹⁆ * ⁅w, u⁻¹⁆ * ⁅w, y⁻¹⁆) =
        (⁅y⁻¹, u⁻¹⁆ * ⁅w, u⁻¹⁆ * ⁅w, y⁻¹⁆) * t from hZzt.eq.symm]
      group
    have hu' : t * u⁻¹ * t⁻¹ = u⁻¹ := by
      rw [show t * u⁻¹ = u⁻¹ * t from (huCommt.inv_left).eq.symm]
      group
    have hzuy : u * y * (⁅y⁻¹, u⁻¹⁆ * ⁅w, u⁻¹⁆ * ⁅w, y⁻¹⁆) * u⁻¹ * y⁻¹ =
        (⁅y⁻¹, u⁻¹⁆ * ⁅w, u⁻¹⁆ * ⁅w, y⁻¹⁆) * (u * y * u⁻¹ * y⁻¹) := by
      rw [show u * y * (⁅y⁻¹, u⁻¹⁆ * ⁅w, u⁻¹⁆ * ⁅w, y⁻¹⁆) =
        (⁅y⁻¹, u⁻¹⁆ * ⁅w, u⁻¹⁆ * ⁅w, y⁻¹⁆) * (u * y) from
          (hZzu.mul_right hZzy).eq.symm]
      group
    calc
      u * y * t * (⁅y⁻¹, u⁻¹⁆ * ⁅w, u⁻¹⁆ * ⁅w, y⁻¹⁆ * u⁻¹) * t⁻¹ * y⁻¹
          = u * y * (t * (⁅y⁻¹, u⁻¹⁆ * ⁅w, u⁻¹⁆ * ⁅w, y⁻¹⁆) * t⁻¹) *
              (t * u⁻¹ * t⁻¹) * y⁻¹ := by group
      _ = u * y * (⁅y⁻¹, u⁻¹⁆ * ⁅w, u⁻¹⁆ * ⁅w, y⁻¹⁆) * u⁻¹ * y⁻¹ := by
        rw [ht, hu']
      _ = (⁅y⁻¹, u⁻¹⁆ * ⁅w, u⁻¹⁆ * ⁅w, y⁻¹⁆) * ⁅u, y⁆ := by
        rw [hzuy]
        rfl
  rw [hEq, hMain, hP, hstep]

private theorem SzCfg.conj_commutator_mem_szZ (c : SzCfg G D d E e n)
    (P : Sylow 2 (SzBar E)) (hP : e ∈ szS E P)
    {s y t : G} (hs : s ∈ szS E P) (hy : y ∈ szQ E) (ht : t ∈ szComp E e) :
    ⁅s, ⁅y, t⁆⁆ ∈ szZ E := by
  let u : G := ⁅s, y⁆
  let w : G := t⁻¹ * (s * t * s⁻¹)
  have hsH : s ∈ Subgroup.closure E := szN_le_closure E P (szS_le_szN E P hs)
  have htE : t ∈ E := ht.1
  have htS : t ∈ szS E P := (c.mem_szS_iff_commute P c.e_mem htE hP).mpr ht.2
  have huQ : u ∈ szQ E := by
    have himage : (fun x => s * x * s⁻¹) '' E = E :=
      Subgroup.mem_normalizer_iff_conj_image_eq.mp
        (closure_le_normalizer_of_isMaxOrbit c.hyp.setup c.maxOrbit hsH)
    have h1 : s * y * s⁻¹ ∈ szQ E := conj_mem_szQ himage hy
    have h2 : y⁻¹ ∈ szQ E := (szQ E).inv_mem hy
    have h3 : s * y * s⁻¹ * y⁻¹ ∈ szQ E := (szQ E).mul_mem h1 h2
    simpa [u, commutatorElement_def] using h3
  have huCommE : Commute u e := by
    simpa [u, commutatorElement_def] using c.commute_commutator_szS P hP hs hy
  have huCommt : Commute u t :=
    (c.commute_iff_of_mem_comp c.e_mem ht huQ).mp huCommE
  have hwQ : w ∈ szQ E := by
    simpa [w] using c.inv_mul_conj_mem_szQ P htE htS hs
  have hEq := c.conj_commutator_eq_mul (s := s) (y := y) (t := t) (u := u) (w := w)
    hy htE rfl rfl huQ hwQ huCommt
  rw [hEq]
  have hz1 : ⁅y⁻¹, u⁻¹⁆ ∈ szZ E :=
    c.commutator_mem_szZ ((szQ E).inv_mem hy) ((szQ E).inv_mem huQ)
  have hz2 : ⁅w, u⁻¹⁆ ∈ szZ E := c.commutator_mem_szZ hwQ ((szQ E).inv_mem huQ)
  have hz3 : ⁅w, y⁻¹⁆ ∈ szZ E := c.commutator_mem_szZ hwQ ((szQ E).inv_mem hy)
  have hZZ : ⁅y⁻¹, u⁻¹⁆ * ⁅w, u⁻¹⁆ * ⁅w, y⁻¹⁆ ∈ szZ E :=
    (szZ E).mul_mem ((szZ E).mul_mem hz1 hz2) hz3
  exact (szZ E).mul_mem hZZ (c.commutator_mem_szZ huQ hy)

private theorem SzCfg.commutator_centralizer_szQ_le_szZ (c : SzCfg G D d E e n)
    (P : Sylow 2 (SzBar E)) (hP : e ∈ szS E P) :
    ⁅szQ E ⊓ Subgroup.centralizer ({e} : Set G), szS E P⁆ ≤ szZ E := by
  let Q := szQ E
  let Z := szZ E
  let W : Set G := {w | ∃ t ∈ szComp E e, ∃ x ∈ Q, w = x * t * x⁻¹ * t⁻¹}
  have hHnorm : Subgroup.closure E ≤ Subgroup.normalizer (Z : Set G) :=
    c.closure_le_normalizer_szZ
  have hWleH : Subgroup.closure W ≤ Subgroup.closure E := by
    rw [Subgroup.closure_le]
    rintro w ⟨t, ht, x, hx, rfl⟩
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _
        (Subgroup.mul_mem _ (szQ_le_closure E hx) (Subgroup.subset_closure ht.1))
        (Subgroup.inv_mem _ (szQ_le_closure E hx)))
      (Subgroup.inv_mem _ (Subgroup.subset_closure ht.1))
  have hUnorm : Subgroup.closure (W ∪ (Z : Set G)) ≤ Subgroup.normalizer (Z : Set G) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq]
    exact sup_le (hWleH.trans hHnorm) Subgroup.le_normalizer
  have hSH : szS E P ≤ Subgroup.closure E := (szS_le_szN E P).trans (szN_le_closure E P)
  have hSnorm : Subgroup.closure (szS E P : Set G) ≤ Subgroup.normalizer (Z : Set G) := by
    rw [Subgroup.closure_eq]
    exact hSH.trans hHnorm
  have hstep : ∀ w ∈ W ∪ (Z : Set G), ∀ s ∈ szS E P, ⁅w, s⁆ ∈ Z := by
    intro w hw s hs
    rcases hw with hwW | hwZ
    · obtain ⟨t, ht, x, hx, rfl⟩ := hwW
      have h1 : ⁅s, ⁅x, t⁆⁆ ∈ Z := c.conj_commutator_mem_szZ P hP hs hx ht
      have h2 : ⁅⁅x, t⁆, s⁆ ∈ Z := by
        rw [← commutatorElement_inv]
        exact Z.inv_mem h1
      simpa [commutatorElement_def] using h2
    · have hzc : w ∈ Subgroup.centralizer (Subgroup.closure E : Set G) := by
        rw [Subgroup.centralizer_closure]
        exact hwZ.2
      have hcomm : Commute w s :=
        (Subgroup.mem_centralizer_iff.mp hzc s (hSH hs)).symm
      rw [commutatorElement_eq_one_iff_commute.mpr hcomm]
      exact Z.one_mem
  have hclosed := OddLocal.commutator_closure_le (S := W ∪ (Z : Set G))
    (T := (szS E P : Set G)) (N := Z) hUnorm hSnorm hstep
  rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq] at hclosed
  refine (Subgroup.commutator_mono ?_ le_rfl).trans hclosed
  intro x hx
  exact c.mem_closure_sup_szZ c.e_mem hx.1
    (Subgroup.mem_centralizer_singleton_iff.mp hx.2)

private theorem SzCfg.commutator_szQ_commutator_szS_le_szZ (c : SzCfg G D d E e n)
    (P : Sylow 2 (SzBar E)) (hP : e ∈ szS E P) :
    ⁅szQ E, ⁅szS E P, szS E P⁆⁆ ≤ szZ E := by
  have hSC : ⁅szS E P, szQ E⁆ ≤ szQ E ⊓ Subgroup.centralizer ({e} : Set G) := by
    rw [Subgroup.commutator_le]
    intro s hs y hy
    have hsH : s ∈ Subgroup.closure E := szN_le_closure E P (szS_le_szN E P hs)
    have himage : (fun x => s * x * s⁻¹) '' E = E :=
      Subgroup.mem_normalizer_iff_conj_image_eq.mp
        (closure_le_normalizer_of_isMaxOrbit c.hyp.setup c.maxOrbit hsH)
    refine ⟨?_, ?_⟩
    · exact (szQ E).mul_mem (conj_mem_szQ himage hy) ((szQ E).inv_mem hy)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (c.commute_commutator_szS P hP hs hy).eq
  have hCS : ⁅szQ E ⊓ Subgroup.centralizer ({e} : Set G), szS E P⁆ ≤ szZ E :=
    c.commutator_centralizer_szQ_le_szZ P hP
  have h1 : ⁅⁅szS E P, szQ E⁆, szS E P⁆ ≤ szZ E :=
    (Subgroup.commutator_mono hSC le_rfl).trans hCS
  have h2 : ⁅⁅szQ E, szS E P⁆, szS E P⁆ ≤ szZ E := by
    rw [Subgroup.commutator_comm (szQ E) (szS E P)]
    exact h1
  have hM : Subgroup.closure E ≤ Subgroup.normalizer (szZ E : Set G) :=
    c.closure_le_normalizer_szZ
  have hAM : szS E P ≤ Subgroup.closure E := (szS_le_szN E P).trans (szN_le_closure E P)
  have hBM : szQ E ≤ Subgroup.closure E := szQ_le_closure E
  have hNM : szZ E ≤ Subgroup.closure E :=
    (show szZ E ≤ szQ E from inf_le_left).trans (szQ_le_closure E)
  have h3 := CFSG.GroupTheory.commutator_commutator_le_of_rotate_normal
    (M := Subgroup.closure E) (A := szS E P) (B := szQ E) (N := szZ E)
    hAM hBM hNM hM h1 h2
  rw [Subgroup.commutator_comm (szQ E) (⁅szS E P, szS E P⁆)]
  exact h3

private theorem SzCfg.commutator_szS_mem_szQ (c : SzCfg G D d E e n)
    (P : Sylow 2 (SzBar E)) (hP : e ∈ szS E P) {s s' : G}
    (hs : s ∈ szS E P) (hs' : s' ∈ szS E P) :
    s * s' * s⁻¹ * s'⁻¹ ∈ szQ E := by
  let s'' : G := s * s' * s⁻¹ * s'⁻¹
  have hs''S : s'' ∈ szS E P := by
    dsimp [s'']
    exact (szS E P).mul_mem ((szS E P).mul_mem ((szS E P).mul_mem hs hs')
      ((szS E P).inv_mem hs)) ((szS E P).inv_mem hs')
  have hs''H : s'' ∈ Subgroup.closure E := szN_le_closure E P (szS_le_szN E P hs''S)
  have hs''SS : s'' ∈ ⁅szS E P, szS E P⁆ := by
    dsimp [s'']
    exact Subgroup.commutator_mem_commutator hs hs'
  have hQSS := c.commutator_szQ_commutator_szS_le_szZ P hP
  obtain ⟨f, hfE, hfne⟩ := c.exists_not_commute c.e_mem
  have hfe : ¬ Commute e f := fun h => hfne h.symm
  obtain ⟨Pf, hfPf⟩ := c.exists_szS hfE
  obtain ⟨y, hyQ, hyf, hyZ⟩ := c.exists_commute_not_mem_szZ hfE
  have hyy : ⁅s'', y⁆ ∈ szZ E := by
    have h1 : ⁅y, s''⁆ ∈ szZ E :=
      hQSS (Subgroup.commutator_mem_commutator hyQ hs''SS)
    simpa [commutatorElement_inv] using (szZ E).inv_mem h1
  have hsy : s'' * y * s''⁻¹ = ⁅s'', y⁆ * y := by
    rw [commutatorElement_def]
    group
  have hz'' : Commute ⁅s'', y⁆ s'' := szZ_commute_closure E _ hyy s'' hs''H
  have hzy : Commute ⁅s'', y⁆ y := szZ_commute_closure E _ hyy y (szQ_le_closure E hyQ)
  have hsy' : s''⁻¹ * y * s'' = ⁅s'', y⁆⁻¹ * y := by
    have h1 : s''⁻¹ * (s'' * y * s''⁻¹) * s'' = y := by group
    have h2 : s''⁻¹ * (⁅s'', y⁆ * y) * s'' =
        ⁅s'', y⁆ * (s''⁻¹ * y * s'') := by
      rw [← mul_assoc s''⁻¹ ⁅s'', y⁆ y]
      rw [show s''⁻¹ * ⁅s'', y⁆ = ⁅s'', y⁆ * s''⁻¹ from hz''.inv_right.eq.symm]
      group
    have h3 : ⁅s'', y⁆ * (s''⁻¹ * y * s'') = y := by
      rw [← h2, ← hsy, h1]
    calc s''⁻¹ * y * s''
        = ⁅s'', y⁆⁻¹ * (⁅s'', y⁆ * (s''⁻¹ * y * s'')) := by group
      _ = ⁅s'', y⁆⁻¹ * y := by rw [h3]
  have hzf : Commute ⁅s'', y⁆ f :=
    szZ_commute_closure E _ hyy f (Subgroup.subset_closure hfE)
  have hcomm1 : Commute (s''⁻¹ * y * s'') f := by
    rw [hsy']
    exact (hzf.inv_left).mul_left hyf
  have hcommYF' : Commute y (s'' * f * s''⁻¹) := by
    have h := hcomm1.conj s''
    convert h using 1
    group
  have hf'E : s'' * f * s''⁻¹ ∈ E := c.conj_mem hs''H hfE
  have hff' : Commute f (s'' * f * s''⁻¹) := by
    by_contra h
    exact hyZ (c.mem_szZ_of_commute hfE hf'E h hyQ hyf hcommYF')
  have hf'S : s'' * f * s''⁻¹ ∈ szS E Pf :=
    (c.mem_szS_iff_commute Pf hfE hf'E hfPf).mpr hff'.symm
  have hs''N : s'' ∈ szN E Pf :=
    c.mem_szN_of_conj_mem Pf hfE hfPf hs''H hf'S
  have hne : P ≠ Pf := by
    intro hEq
    have hfP : f ∈ szS E P := by
      rw [hEq]
      exact hfPf
    exact hfe ((c.mem_szS_iff_commute P c.e_mem hfE hP).mp hfP).symm
  have hQ : s'' ∈ szQ E := c.mem_szQ_of_mem_szN hne hs''S hs''N
  simpa [s''] using hQ

theorem not_szCfg : ¬ SzCfg G D d E e n := by
  intro c
  obtain ⟨P, hP⟩ := c.exists_szS c.e_mem
  obtain ⟨s, hs, s', hs', hnc⟩ := c.exists_not_commute_szS P
  exact hnc (c.commutator_szS_mem_szQ P hP hs hs')

theorem szMainStmt : SzMainStmt := by
  intro G _ _ D h _ d hd E hE e he _ _ _ hrE _ _ _ n hn hiso
  exact not_szCfg (G := G) (D := D) (d := d) (E := E) (e := e) (n := n)
    ⟨h, hd, hE, he, hrE, hn, hiso⟩

end CFSG.Timmesfeld.Bridge.OddRoot

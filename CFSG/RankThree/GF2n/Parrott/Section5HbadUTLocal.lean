module

public import CFSG.RankThree.GF2n.Parrott.SpinHbadUTFacts
public import CFSG.RankThree.GF2n.Parrott.Section5HbadUTCoord
public import CFSG.RankThree.GF2n.Parrott.LiftSquare
public import CFSG.RankThree.GF2n.Parrott.ActionZSimplicity

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped Matrix

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "Mat8" => Matrix (Fin 8) (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)

variable {G : Type} [Group G] [Finite G] {z : G}

section Spin

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

section Y

variable {y : G} (hyH : y ∈ H z) (hy : y * y = 1)
  (hq : qH (z := z) D ⟨y, hyH⟩ = uA * tA)
include hyH hq

theorem commute_of_mem_centerIn_of_utA (h : Tim79a.ParrottHyp z) {ζ : G}
    (hζ : ζ ∈ centerIn (J z)) : ζ * y = y * ζ := by
  have hQ : qH (z := z) D ⟨y, hyH⟩ ∈
      QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := hq ▸ utA_mem_QP45
  have h1 : conjZ z ⟨y, hyH⟩ = 1 :=
    conjZ_eq_one_of_mem_Q (z := z) D h ⟨y, hyH⟩ hQ
  exact Subgroup.mem_centralizer_singleton_iff.mp
    (centerIn_le_centralizer_of_conjZ_eq_one (z := z) h1 hζ)

theorem hbadCoord_conj_mul_inv_of_utA (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) {k : G} (hk : k ∈ J z) :
    k * y * k⁻¹ * y⁻¹ ∈ J z ∧
      hbadCoord h P (k * y * k⁻¹ * y⁻¹) =
        hbadCoord h P k + ((rhoA (uA * tA) : GL8) : Mat8) *ᵥ hbadCoord h P k := by
  have hX : y * k⁻¹ * y⁻¹ ∈ J z :=
    H_conj_mem_J (z := z) ⟨y, hyH⟩ ((J z).inv_mem hk)
  refine ⟨?_, ?_⟩
  · simpa only [mul_assoc] using (J z).mul_mem hk hX
  · have h1 := hbadCoord_mul (h := h) (P := P) hk hX
    have h2 := hbadCoord_conj (z := z) D h P hP hyH ((J z).inv_mem hk)
    have h3 := hbadCoord_inv (h := h) (P := P) hk
    rw [show k * y * k⁻¹ * y⁻¹ = k * (y * k⁻¹ * y⁻¹) by group]
    rw [h1, h2, h3, hq]

include hy

theorem commute_iff_of_utA (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) {k : G} (hk : k ∈ J z) :
    k * y = y * k ↔ ((rhoA (uA * tA) : GL8) : Mat8) *ᵥ hbadCoord h P k = hbadCoord h P k := by
  constructor
  · intro hky
    have hx1 : k * y * k⁻¹ * y⁻¹ = 1 := by rw [hky]; group
    have hc1 : hbadCoord h P (k * y * k⁻¹ * y⁻¹) = 0 := by
      rw [hx1]
      exact (hbadCoord_eq_zero_iff h P (one_mem (J z))).mpr (one_mem _)
    have h2 := (hbadCoord_conj_mul_inv_of_utA (D := D) (hyH := hyH) (hq := hq) (h := h) (P := P) (hP := hP) (hk := hk)).2
    rw [hc1] at h2
    have hneg := eq_neg_of_add_eq_zero_right h2.symm
    rwa [show -hbadCoord h P k = hbadCoord h P k from
      (eq_neg_of_add_eq_zero_left (ZModModule.add_self (hbadCoord h P k))).symm] at hneg
  · intro hfix
    obtain ⟨m', hm'⟩ := spin_exists_eq_mul_utA_add (hbadCoord h P k) hfix
    obtain ⟨l, hl, hlm⟩ := exists_hbadCoord_eq h P m'
    set x := l * y * l⁻¹ * y⁻¹ with hxdef
    obtain ⟨hxJ, hxc⟩ := hbadCoord_conj_mul_inv_of_utA (D := D) (hyH := hyH) (hq := hq) (h := h) (P := P) (hP := hP) (hk := hl)
    have hxc' : hbadCoord h P x = hbadCoord h P k := by
      rw [hxc, hlm, add_comm, hm']
    set ζ := x⁻¹ * k with hζdef
    have hζJ : ζ ∈ J z := (J z).mul_mem ((J z).inv_mem hxJ) hk
    have hζc : hbadCoord h P ζ = 0 := by
      rw [hζdef, hbadCoord_mul h P ((J z).inv_mem hxJ) hk,
        hbadCoord_inv h P hxJ, hxc', ZModModule.add_self]
    have hζZ : ζ ∈ centerIn (J z) := (hbadCoord_eq_zero_iff h P hζJ).mp hζc
    have hq0 : q (hbadCoord h P x) = 0 := by
      rw [hxc']
      exact spin_q_eq_zero_of_utA (hbadCoord h P k) hfix
    have hxx : x * x = 1 := (mul_self_eq_one_iff_hbadCoord (D := D) (h := h) (P := P) (hP := hP) (hk := hxJ)).mpr hq0
    have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
    have hconj : y * x * y⁻¹ = x⁻¹ := by
      rw [hxdef, hyinv]
      simp only [mul_inv_rev, inv_inv, hyinv]
      calc y * (l * y * l⁻¹ * y) * y
          = (y * (l * y * l⁻¹)) * (y * y) := by group
        _ = y * (l * y * l⁻¹) := by rw [hy, mul_one]
        _ = y * (l * (y * l⁻¹)) := by group
    have hcomm_xy : x * y = y * x := by
      have h := congrArg (fun t => t * y) hconj
      have h' : y * x = x⁻¹ * y := by simpa [mul_assoc] using h
      simpa [hxinv, mul_assoc] using h'.symm
    have hζy : ζ * y = y * ζ :=
      commute_of_mem_centerIn_of_utA (D := D) (hyH := hyH) (hq := hq) (h := h) (hζ := hζZ)
    have hk_eq : k = x * ζ := by
      rw [hζdef]
      group
    rw [hk_eq]
    have hfinal : x * ζ * y = y * (x * ζ) := by
      calc x * ζ * y = x * (ζ * y) := by group
        _ = x * (y * ζ) := by rw [hζy]
        _ = y * x * ζ := by rw [← mul_assoc, hcomm_xy]
        _ = y * (x * ζ) := by group
    exact hfinal

theorem mul_self_eq_one_of_utA (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) {k : G} (hk : k ∈ J z)
    (hky : k * y = y * k) : k * k = 1 := by
  have hfix : ((rhoA (uA * tA) : GL8) : Mat8) *ᵥ hbadCoord h P k = hbadCoord h P k :=
    (commute_iff_of_utA (D := D) (hyH := hyH) (hy := hy) (hq := hq) (h := h) (P := P)
      (hP := hP) (hk := hk)).mp hky
  exact (mul_self_eq_one_iff_hbadCoord (D := D) (h := h) (P := P) (hP := hP) (hk := hk)).mpr
    (spin_q_eq_zero_of_utA (hbadCoord h P k) hfix)

theorem commute_of_utA (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) {k l : G} (hk : k ∈ J z)
    (hl : l ∈ J z) (hky : k * y = y * k) (hly : l * y = y * l) : k * l = l * k := by
  have hfixk : ((rhoA (uA * tA) : GL8) : Mat8) *ᵥ hbadCoord h P k = hbadCoord h P k :=
    (commute_iff_of_utA (D := D) (hyH := hyH) (hy := hy) (hq := hq) (h := h) (P := P)
      (hP := hP) (hk := hk)).mp hky
  have hfixl : ((rhoA (uA * tA) : GL8) : Mat8) *ᵥ hbadCoord h P l = hbadCoord h P l :=
    (commute_iff_of_utA (D := D) (hyH := hyH) (hy := hy) (hq := hq) (h := h) (P := P)
      (hP := hP) (hk := hl)).mp hly
  have hfixsum :
      ((rhoA (uA * tA) : GL8) : Mat8) *ᵥ (hbadCoord h P k + hbadCoord h P l) =
        hbadCoord h P k + hbadCoord h P l := by
    rw [Matrix.mulVec_add, hfixk, hfixl]
  have hb : b (hbadCoord h P k) (hbadCoord h P l) = 0 := by
    simp [b, spin_q_eq_zero_of_utA _ hfixsum, spin_q_eq_zero_of_utA _ hfixk,
      spin_q_eq_zero_of_utA _ hfixl]
  exact (commute_iff_hbadCoord (D := D) (h := h) (P := P) (hP := hP) (hk := hk) (hl := hl)).mpr hb

theorem card_J_inf_centralizer_of_utA (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) :
    Nat.card ↥(J z ⊓ centralizer ({y} : Set G)) = 64 := by
  let C : Subgroup G := J z ⊓ centralizer ({y} : Set G)
  have hCZ : centerIn (J z) ≤ C := by
    intro ζ hζ
    exact Subgroup.mem_inf.mpr
      ⟨(inf_le_left : centerIn (J z) ≤ J z) hζ,
        Subgroup.mem_centralizer_singleton_iff.mpr
          (commute_of_mem_centerIn_of_utA (D := D) (hyH := hyH) (hq := hq) (h := h)
            (hζ := hζ))⟩
  let φ : ↥C →* Multiplicative V :=
    { toFun := fun c => Multiplicative.ofAdd (hbadCoord h P (c : G))
      map_one' := by
        have h1 : hbadCoord h P ((1 : ↥C) : G) = 0 :=
          (hbadCoord_eq_zero_iff h P (one_mem (J z))).mpr (one_mem _)
        show Multiplicative.ofAdd (hbadCoord h P ((1 : ↥C) : G)) = 1
        rw [h1]
        simp
      map_mul' := by
        intro a b
        show Multiplicative.ofAdd (hbadCoord h P ((a * b : ↥C) : G)) =
          Multiplicative.ofAdd (hbadCoord h P (a : G)) *
            Multiplicative.ofAdd (hbadCoord h P (b : G))
        rw [show ((a * b : ↥C) : G) = (a : G) * (b : G) from rfl,
          hbadCoord_mul h P a.2.1 b.2.1]
        simp }
  have hker_eq : φ.ker = (centerIn (J z)).subgroupOf C := by
    ext c
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hc
      have hc' : hbadCoord h P (c : G) = 0 := by
        have hh := congrArg Multiplicative.toAdd hc
        simpa [φ] using hh
      exact (hbadCoord_eq_zero_iff h P c.2.1).mp hc'
    · intro hc
      have hc' : hbadCoord h P (c : G) = 0 := (hbadCoord_eq_zero_iff h P c.2.1).mpr hc
      change Multiplicative.ofAdd (hbadCoord h P (c : G)) = 1
      rw [hc']
      simp
  have hker : Nat.card ↥φ.ker = 4 := by
    rw [hker_eq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCZ).toEquiv, card_centerIn_J h]
  have hle1 : Nat.card ↥φ.range ≤
      Nat.card {w : V // ((rhoA (uA * tA) : GL8) : Mat8) *ᵥ w = w} := by
    refine Nat.card_le_card_of_injective
      (fun a : ↥φ.range => ⟨Multiplicative.toAdd a.1, ?_⟩) ?_
    · obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp a.2
      have hcy : (c : G) * y = y * (c : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp c.2.2
      have hfixc : ((rhoA (uA * tA) : GL8) : Mat8) *ᵥ hbadCoord h P (c : G) =
          hbadCoord h P (c : G) :=
        (commute_iff_of_utA (D := D) (hyH := hyH) (hy := hy) (hq := hq) (h := h)
          (P := P) (hP := hP) (hk := c.2.1)).mp hcy
      rw [← hc]
      change ((rhoA (uA * tA) : GL8) : Mat8) *ᵥ hbadCoord h P ((c : ↥C) : G) =
        hbadCoord h P ((c : ↥C) : G)
      exact hfixc
    · intro a b hab
      apply Subtype.ext
      exact Multiplicative.toAdd.injective
        (congrArg (fun t : {w : V // ((rhoA (uA * tA) : GL8) : Mat8) *ᵥ w = w} => (t : V)) hab)
  have hle2 : Nat.card {w : V // ((rhoA (uA * tA) : GL8) : Mat8) *ᵥ w = w} ≤
      Nat.card ↥φ.range := by
    refine Nat.card_le_card_of_injective
      (fun w => ⟨Multiplicative.ofAdd w.1, ?_⟩) ?_
    · obtain ⟨k, hk, hkw⟩ := exists_hbadCoord_eq h P w.1
      have hky : k * y = y * k :=
        (commute_iff_of_utA (D := D) (hyH := hyH) (hy := hy) (hq := hq) (h := h)
          (P := P) (hP := hP) (hk := hk)).mpr (by rw [hkw]; exact w.2)
      have hkC : k ∈ C :=
        Subgroup.mem_inf.mpr ⟨hk, Subgroup.mem_centralizer_singleton_iff.mpr hky⟩
      exact MonoidHom.mem_range.mpr ⟨⟨k, hkC⟩, by
        show Multiplicative.ofAdd (hbadCoord h P k) = Multiplicative.ofAdd w.1
        rw [hkw]⟩
    · intro w w' hww
      apply Subtype.ext
      exact Multiplicative.ofAdd.injective
        (congrArg (fun t : ↥φ.range => (t : Multiplicative V)) hww)
  have hrange : Nat.card ↥φ.range = 16 := by
    apply le_antisymm
    · calc Nat.card ↥φ.range ≤
          Nat.card {w : V // ((rhoA (uA * tA) : GL8) : Mat8) *ᵥ w = w} := hle1
        _ = 16 := card_spin_fixed_utA
    · calc 16 = Nat.card {w : V // ((rhoA (uA * tA) : GL8) : Mat8) *ᵥ w = w} :=
            card_spin_fixed_utA.symm
        _ ≤ Nat.card ↥φ.range := hle2
  have hcard := Subgroup.card_ker_mul_card_range φ
  have h64 : Nat.card ↥C = 64 := by
    rw [← hcard, hker, hrange]
  simpa [C] using h64

theorem exists_eq_conj_mul_of_utA (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) {g : G} (hgH : g ∈ H z)
    (hgq : qH (z := z) D ⟨g, hgH⟩ = uA * tA) (hg : g * g = 1) :
    ∃ k ∈ J z, ∃ ζ ∈ centerIn (J z), g = k * y * k⁻¹ * ζ := by
  have hfixcard : fixCard (((rhoA (uA * tA) : GL8) : Mat8)) = 16 := by
    rw [fixCard, ← Nat.card_eq_fintype_card]
    exact card_spin_fixed_utA
  have hdim : fixDimV h ⟨y, hyH⟩ = 4 := by
    apply Nat.pow_right_injective (a := 2) le_rfl
    change 2 ^ fixDimV h ⟨y, hyH⟩ = 2 ^ 4
    rw [two_pow_fixDimV_eq_of_conj_rep (z := z) D h rhoA P hP ⟨y, hyH⟩, hq, hfixcard]
  have hc : y⁻¹ * g ∈ J z := by
    have hH : y⁻¹ * g ∈ H z := (H z).mul_mem ((H z).inv_mem hyH) hgH
    refine (Subgroup.mem_subgroupOf (H := J z) (K := H z)
      (h := (⟨y⁻¹ * g, hH⟩ : ↥(H z)))).mp ?_
    rw [J_mem_iff (z := z) D]
    have hsplit : (qH (z := z) D) ⟨y⁻¹ * g, hH⟩ =
        ((qH (z := z) D) ⟨y, hyH⟩)⁻¹ * (qH (z := z) D) ⟨g, hgH⟩ := by
      rw [show (⟨y⁻¹ * g, hH⟩ : ↥(H z)) = ⟨y, hyH⟩⁻¹ * ⟨g, hgH⟩ from rfl, map_mul, map_inv]
    rw [hsplit, hq, hgq, inv_mul_cancel]
  have h1 : y * y ∈ centerIn (J z) := by rw [hy]; exact one_mem _
  have h2 : g * g ∈ centerIn (J z) := by rw [hg]; exact one_mem _
  obtain ⟨k', hk'J, e, heZ, hke⟩ :=
    exists_conj_mul_centerIn_of_fixDimV_eq_four (z := z) h hyH hc hdim h1 h2
  refine ⟨k'⁻¹, (J z).inv_mem hk'J, e, heZ, ?_⟩
  have hek : k' * e = e * k' :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp heZ).2 k' hk'J
  have hfin : g = k'⁻¹ * y * k' * e := by
    calc g = k'⁻¹ * (k' * g * k'⁻¹) * k' := by group
      _ = k'⁻¹ * (y * e) * k' := by rw [hke]
      _ = k'⁻¹ * y * k' * e := by
          rw [show k'⁻¹ * (y * e) * k' = k'⁻¹ * (y * (e * k')) by group,
            show e * k' = k' * e from hek.symm]
          group
  simpa using hfin

theorem exists_eq_conj_mul_inv_mul_of_utA (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) {n : G} (hn : n ∈ J z)
    (hny : n * y = y * n) (hnZ : n ∉ centerIn (J z)) :
    ∃ k ∈ J z, ∃ ζ ∈ centerIn (J z), n = k * y * k⁻¹ * y⁻¹ * ζ ∧
      k * y * k⁻¹ * y⁻¹ ∉ centerIn (J z) := by
  have hfixn : ((rhoA (uA * tA) : GL8) : Mat8) *ᵥ hbadCoord h P n = hbadCoord h P n :=
    (commute_iff_of_utA (D := D) (hyH := hyH) (hy := hy) (hq := hq) (h := h)
      (P := P) (hP := hP) (hk := hn)).mp hny
  obtain ⟨m', hm'⟩ := spin_exists_eq_mul_utA_add (hbadCoord h P n) hfixn
  obtain ⟨k, hk, hkm⟩ := exists_hbadCoord_eq h P m'
  obtain ⟨hxJ, hxc⟩ := hbadCoord_conj_mul_inv_of_utA (D := D) (hyH := hyH) (hq := hq)
    (h := h) (P := P) (hP := hP) (hk := hk)
  have hxc' : hbadCoord h P (k * y * k⁻¹ * y⁻¹) = hbadCoord h P n := by
    rw [hxc, hkm, add_comm, hm']
  set x := k * y * k⁻¹ * y⁻¹ with hxdef
  set ζ := x⁻¹ * n with hζdef
  have hζJ : ζ ∈ J z := (J z).mul_mem ((J z).inv_mem hxJ) hn
  have hζc : hbadCoord h P ζ = 0 := by
    rw [hζdef, hbadCoord_mul h P ((J z).inv_mem hxJ) hn,
      hbadCoord_inv h P hxJ, hxc', ZModModule.add_self]
  have hζZ : ζ ∈ centerIn (J z) := (hbadCoord_eq_zero_iff h P hζJ).mp hζc
  have hn_eq : n = x * ζ := by
    rw [hζdef]
    group
  refine ⟨k, hk, ζ, hζZ, ?_, ?_⟩
  · simpa [hxdef] using hn_eq
  · intro hxZ
    exact hnZ (by rw [hn_eq]; exact (centerIn (J z)).mul_mem hxZ hζZ)

theorem card_le_of_forall_mem_centerIn_of_utA
    (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    (B : Subgroup G) (hBC : B ≤ H z ⊓ centralizer ({y} : Set G))
    (hBn : ∀ c ∈ H z ⊓ centralizer ({y} : Set G), ∀ c' ∈ B, c * c' * c⁻¹ ∈ B) (hzB : z ∉ B)
    (hBJ : ∀ n ∈ B, n ∈ J z → n ∈ centerIn (J z)) :
    Nat.card B ≤ 32 := by
  have hBH : B ≤ H z := hBC.trans inf_le_left
  let φ : ↥B →* A45 := (qH (z := z) D).comp (Subgroup.inclusion hBH)
  let K : Subgroup G := φ.ker.map B.subtype
  have hKcard : Nat.card ↥K = Nat.card ↥φ.ker :=
    Subgroup.card_map_of_injective (K := φ.ker) (f := B.subtype) B.subtype_injective
  have hKZ : K ≤ centerIn (J z) := by
    intro n hn
    obtain ⟨x, hxker, rfl⟩ := Subgroup.mem_map.mp hn
    have hxJ : (x : G) ∈ J z := by
      refine (Subgroup.mem_subgroupOf (H := J z) (K := H z)
        (h := (⟨x, hBH x.2⟩ : ↥(H z)))).mp ?_
      rw [J_mem_iff (z := z) D]
      have hx1 : (qH (z := z) D) (Subgroup.inclusion hBH x) = 1 :=
        MonoidHom.mem_ker.mp hxker
      have hincl : (Subgroup.inclusion hBH x : ↥(H z)) = ⟨x, hBH x.2⟩ := Subtype.ext rfl
      rwa [hincl] at hx1
    exact hBJ (x : G) x.2 hxJ
  have hKne : Nat.card ↥K ≠ 4 := by
    intro hK4
    have hKeq : K = centerIn (J z) := by
      apply Subgroup.eq_of_le_of_card_ge hKZ
      rw [hK4, card_centerIn_J h]
    have hzK : z ∈ K := by
      rw [hKeq]
      exact Subgroup.mem_inf.mpr ⟨z_mem_J h, z_centralizes_J h⟩
    exact hzB (Subgroup.map_subtype_le (H := B) φ.ker hzK)
  have hker : Nat.card ↥φ.ker ≤ 2 := by
    have hdvd : Nat.card ↥φ.ker ∣ 4 := by
      have h1 : Nat.card ↥K ∣ Nat.card ↥(centerIn (J z)) := Subgroup.card_dvd_of_le hKZ
      rw [hKcard, card_centerIn_J h] at h1
      exact h1
    have hne : Nat.card ↥φ.ker ≠ 4 := by
      intro h4
      exact hKne (by rw [hKcard, h4])
    set N := Nat.card ↥φ.ker with hN
    have hdvd' : N ∣ 4 := by simpa [hN] using hdvd
    have hne' : N ≠ 4 := by simpa [hN] using hne
    have hle : N ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd'
    rcases Nat.lt_or_ge N 3 with hlt | hge
    · omega
    · interval_cases N
      · norm_num at hdvd'
      · exact absurd rfl hne'
  have hrange : Nat.card ↥φ.range ≤ 16 := by
    have hle : Nat.card ↥φ.range ≤
        Nat.card {a : A45 // a * (uA * tA) = (uA * tA) * a ∧
          ∀ w : V, ((rhoA (uA * tA) : GL8) : Mat8) *ᵥ w = w →
            ((rhoA a : GL8) : Mat8) *ᵥ w = w} := by
      refine Nat.card_le_card_of_injective
        (fun a : ↥φ.range => ⟨(a : A45), ?_, ?_⟩) ?_
      · obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp a.2
        have hcH : (c : G) ∈ H z := (hBC c.2).1
        have hcy : (c : G) * y = y * (c : G) :=
          Subgroup.mem_centralizer_singleton_iff.mp (hBC c.2).2
        have hcyH : (⟨(c : G), hcH⟩ : ↥(H z)) * ⟨y, hyH⟩ =
            ⟨y, hyH⟩ * ⟨(c : G), hcH⟩ := by
          apply Subtype.ext
          simpa using hcy
        have hcomm : (qH (z := z) D) ⟨(c : G), hcH⟩ * (uA * tA) =
            (uA * tA) * (qH (z := z) D) ⟨(c : G), hcH⟩ := by
          calc (qH (z := z) D) ⟨(c : G), hcH⟩ * (uA * tA)
              = (qH (z := z) D) ⟨(c : G), hcH⟩ * (qH (z := z) D) ⟨y, hyH⟩ := by rw [hq]
            _ = (qH (z := z) D) (⟨(c : G), hcH⟩ * ⟨y, hyH⟩) := by rw [map_mul]
            _ = (qH (z := z) D) (⟨y, hyH⟩ * ⟨(c : G), hcH⟩) := by rw [hcyH]
            _ = (qH (z := z) D) ⟨y, hyH⟩ * (qH (z := z) D) ⟨(c : G), hcH⟩ := by rw [map_mul]
            _ = (uA * tA) * (qH (z := z) D) ⟨(c : G), hcH⟩ := by rw [hq]
        have hval : (a : A45) = (qH (z := z) D) ⟨(c : G), hcH⟩ := by
          rw [hc.symm]
          exact congrArg (qH (z := z) D) (Subtype.ext rfl)
        rw [hval]
        exact hcomm
      · intro w hw
        obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp a.2
        have hcH : (c : G) ∈ H z := (hBC c.2).1
        have hval : (a : A45) = (qH (z := z) D) ⟨(c : G), hcH⟩ := by
          rw [hc.symm]
          exact congrArg (qH (z := z) D) (Subtype.ext rfl)
        obtain ⟨e, heJ, hew⟩ := exists_hbadCoord_eq h P w
        have hey : e * y = y * e :=
          (commute_iff_of_utA (D := D) (hyH := hyH) (hy := hy) (hq := hq) (h := h)
            (P := P) (hP := hP) (hk := heJ)).mpr (by rw [hew]; exact hw)
        have heC : e ∈ H z ⊓ centralizer ({y} : Set G) :=
          Subgroup.mem_inf.mpr ⟨J_le_H heJ,
            Subgroup.mem_centralizer_singleton_iff.mpr hey⟩
        have hece : e * (c : G) * e⁻¹ ∈ B := hBn e heC (c : G) c.2
        have hceJ : (c : G) * e⁻¹ * (c : G)⁻¹ ∈ J z :=
          H_conj_mem_J (z := z) ⟨(c : G), hcH⟩ ((J z).inv_mem heJ)
        have hcommJ : e * (c : G) * e⁻¹ * (c : G)⁻¹ ∈ J z := by
          have h := (J z).mul_mem heJ hceJ
          simpa [mul_assoc] using h
        have hcommB : e * (c : G) * e⁻¹ * (c : G)⁻¹ ∈ B :=
          B.mul_mem hece (B.inv_mem c.2)
        have hζZ : e * (c : G) * e⁻¹ * (c : G)⁻¹ ∈ centerIn (J z) :=
          hBJ _ hcommB hcommJ
        have hζc : hbadCoord h P (e * (c : G) * e⁻¹ * (c : G)⁻¹) = 0 :=
          (hbadCoord_eq_zero_iff h P hcommJ).mpr hζZ
        have hconjcoord : hbadCoord h P ((c : G) * e * (c : G)⁻¹) =
            ((rhoA ((qH (z := z) D) ⟨(c : G), hcH⟩) : GL8) : Mat8) *ᵥ
              hbadCoord h P e :=
          hbadCoord_conj (z := z) D h P hP hcH heJ
        have hce_eq : (c : G) * e * (c : G)⁻¹ =
            (e * (c : G) * e⁻¹ * (c : G)⁻¹)⁻¹ * e := by group
        have hcoord : hbadCoord h P ((c : G) * e * (c : G)⁻¹) = w := by
          rw [hce_eq, hbadCoord_mul h P ((J z).inv_mem hcommJ) heJ,
            hbadCoord_inv h P hcommJ, hζc, hew]
          simp
        have hfix : ((rhoA ((qH (z := z) D) ⟨(c : G), hcH⟩) : GL8) : Mat8) *ᵥ w = w := by
          calc ((rhoA ((qH (z := z) D) ⟨(c : G), hcH⟩) : GL8) : Mat8) *ᵥ w
              = ((rhoA ((qH (z := z) D) ⟨(c : G), hcH⟩) : GL8) : Mat8) *ᵥ
                  hbadCoord h P e := by rw [hew]
            _ = hbadCoord h P ((c : G) * e * (c : G)⁻¹) := hconjcoord.symm
            _ = w := hcoord
        rw [hval]
        exact hfix
      · intro a b hab
        apply Subtype.ext
        exact congrArg (fun t : {a : A45 // a * (uA * tA) = (uA * tA) * a ∧
          ∀ w : V, ((rhoA (uA * tA) : GL8) : Mat8) *ᵥ w = w →
            ((rhoA a : GL8) : Mat8) *ᵥ w = w} => (t : A45)) hab
    calc Nat.card ↥φ.range ≤ Nat.card {a : A45 // a * (uA * tA) = (uA * tA) * a ∧
          ∀ w : V, ((rhoA (uA * tA) : GL8) : Mat8) *ᵥ w = w →
            ((rhoA a : GL8) : Mat8) *ᵥ w = w} := hle
      _ ≤ 16 := card_utA_fix_le
  have hcard := Subgroup.card_ker_mul_card_range φ
  calc Nat.card ↥B = Nat.card ↥φ.ker * Nat.card ↥φ.range := hcard.symm
    _ ≤ 2 * 16 := Nat.mul_le_mul hker hrange
    _ = 32 := by norm_num

end Y

end Spin

end CFSG.RankThree.GF2n.Parrott

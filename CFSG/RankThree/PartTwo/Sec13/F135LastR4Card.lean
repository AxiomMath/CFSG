module

public import CFSG.RankThree.PartTwo.Sec13.F135LastParts
public import CFSG.Foundations.HigherElementaryThompson

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

open scoped IsMulCommutative in
theorem r4c_card_eq_pow_of_pRank {A : Type} [Group A] [Finite A] {p k : ℕ} [hp : Fact p.Prime]
    [IsElementaryAbelian p A] (hk : CFSG.pRank p A = k) : Nat.card A = p ^ k := by
  have hA : Nat.card A = Nat.card (Additive A) := Nat.card_congr Additive.ofMul
  have hV := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive A)
  rw [Nat.card_zmod, ← hA] at hV
  have hpr := CFSG.pRank_eq_of_card_eq_pow hp.out.one_lt hV
  rw [hV, ← hk, hpr]

theorem r4c_exists_gen {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime] {Y : Subgroup G}
    (hY : Nat.card Y = p) (hexp : ∀ x ∈ Y, x ^ p = 1) : ∃ y ∈ Y, Subgroup.zpowers y = Y := by
  have hnt : Nontrivial Y := by
    rw [← Finite.one_lt_card_iff_nontrivial, hY]
    exact hp.out.one_lt
  obtain ⟨x, hx⟩ := exists_ne (1 : Y)
  have hx1 : (x : G) ≠ 1 := fun h => hx (Subtype.ext h)
  refine ⟨(x : G), x.2, ?_⟩
  apply Subgroup.eq_of_le_of_card_ge
  · exact Subgroup.zpowers_le.mpr x.2
  · have h1 : orderOf (x : G) = p := orderOf_eq_prime (hexp _ x.2) hx1
    exact le_of_eq (by rw [Nat.card_zpowers, h1, hY])

theorem r4c_comm_mem_frattini {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {D : Subgroup G} [Fact (IsPGroup p ↥D)] (a b : ↥D) : ⁅a, b⁆ ∈ frattini ↥D := by
  have h1 : ⁅a, b⁆ ∈ _root_.commutator ↥D :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
  exact CFSG.commutator_le_frattini_of_isPGroup (R := ↥D) (p := p) h1

theorem r4c_central {G : Type} [Group G] {D : Subgroup G}
    (hΦc : ∀ x ∈ (frattini ↥D).map D.subtype, ∀ d ∈ D, x * d = d * x)
    {c : ↥D} (hc : c ∈ frattini ↥D) (a : ↥D) : c * a = a * c :=
  Subtype.ext (hΦc (c : G) (Subgroup.mem_map_of_mem D.subtype hc) (a : G) a.2)

theorem r4c_map_mul {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {D : Subgroup G}
    [Fact (IsPGroup p ↥D)]
    (hΦc : ∀ x ∈ (frattini ↥D).map D.subtype, ∀ d ∈ D, x * d = d * x) (y' a b : ↥D) :
    ⁅y', a * b⁆ = ⁅y', a⁆ * ⁅y', b⁆ := by
  have hc := r4c_central hΦc (r4c_comm_mem_frattini (p := p) y' b) a
  have key : ⁅y', a * b⁆ = ⁅y', a⁆ * (a * ⁅y', b⁆ * a⁻¹) := by
    simp only [commutatorElement_def]
    group
  have hconj : a * ⁅y', b⁆ * a⁻¹ = ⁅y', b⁆ := by
    rw [← hc, mul_inv_cancel_right]
  rw [key, hconj]

theorem r4c_quot_le_ker {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {D : Subgroup G}
    [Fact (IsPGroup p ↥D)] (ψ : ↥D →* ↥D) (hrange : ψ.range ≤ frattini ↥D) :
    Nat.card (↥D ⧸ frattini ↥D) ≤ Nat.card ψ.ker := by
  have h1 : Nat.card ψ.ker * ψ.ker.index = Nat.card ↥D :=
    Subgroup.card_mul_index (H := ψ.ker)
  rw [Subgroup.index_ker] at h1
  have h2 : Nat.card ↥D = Nat.card (↥D ⧸ frattini ↥D) * Nat.card ↥(frattini ↥D) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have h3 : Nat.card ψ.range ≤ Nat.card ↥(frattini ↥D) := Subgroup.card_le_of_le hrange
  have hpos : 0 < Nat.card ↥(frattini ↥D) := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc Nat.card (↥D ⧸ frattini ↥D) * Nat.card ↥(frattini ↥D) = Nat.card ↥D := h2.symm
    _ = Nat.card ψ.ker * Nat.card ψ.range := h1.symm
    _ ≤ Nat.card ψ.ker * Nat.card ↥(frattini ↥D) := Nat.mul_le_mul le_rfl h3

theorem r4c_ker_map {G : Type} [Group G] {D Y : Subgroup G} {y : G} (hyD : y ∈ D)
    (hgen : Subgroup.zpowers y = Y) (ψ : ↥D →* ↥D)
    (hψ : ∀ d : ↥D, ψ d = ⁅(⟨y, hyD⟩ : ↥D), d⁆) :
    ψ.ker.map D.subtype = D ⊓ cM Y := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : ψ x = 1 := hx
    rw [hψ, commutatorElement_eq_one_iff_mul_comm] at hx'
    have hxy : y * (x : G) = (x : G) * y := congrArg Subtype.val hx'
    refine Subgroup.mem_inf.mpr ⟨x.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro h hh
    have hh' : h ∈ Subgroup.zpowers y := by rw [hgen]; exact hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh'
    exact (show Commute y (x : G) from hxy).zpow_left k
  · intro hg
    obtain ⟨hgD, hgc⟩ := Subgroup.mem_inf.mp hg
    refine ⟨⟨g, hgD⟩, ?_, rfl⟩
    show ψ ⟨g, hgD⟩ = 1
    rw [hψ, commutatorElement_eq_one_iff_mul_comm]
    apply Subtype.ext
    have hyY : y ∈ (Y : Set G) := by rw [← hgen]; exact Subgroup.mem_zpowers y
    exact Subgroup.mem_centralizer_iff.mp hgc y hyY

theorem r4c_card_eq_of_map {G : Type} [Group G] {D Y : Subgroup G} (K : Subgroup ↥D)
    (h : K.map D.subtype = D ⊓ cM Y) : Nat.card (eOf D Y) = Nat.card K := by
  unfold eOf
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : D ⊓ cM Y ≤ cM Y)).toEquiv,
    ← h]
  exact (Nat.card_congr (K.equivMapOfInjective D.subtype D.subtype_injective).toEquiv).symm

theorem r4_card_eOf {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {D Y : Subgroup G}
    (hD : IsPGroup p D) (hexp : ∀ x ∈ D, x ^ p = 1)
    (hΦc : ∀ x ∈ (frattini ↥D).map D.subtype, ∀ d ∈ D, x * d = d * x)
    (hYD : Y ≤ D) (hY : Nat.card Y = p) (hrank : 4 ≤ CFSG.pRank p (↥D ⧸ frattini ↥D)) :
    p ^ 4 ≤ Nat.card (eOf D Y) := by
  haveI : Fact (IsPGroup p ↥D) := ⟨hD⟩
  have hQcard : p ^ 4 ≤ Nat.card (↥D ⧸ frattini ↥D) := by
    haveI := CFSG.isElementaryAbelian_quotient_frattini (R := ↥D) (p := p)
    rw [r4c_card_eq_pow_of_pRank (p := p) (A := ↥D ⧸ frattini ↥D) (k := CFSG.pRank p (↥D ⧸ frattini ↥D)) rfl]
    exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hrank
  obtain ⟨y, hyY, hgen⟩ := r4c_exists_gen hY (fun x hx => hexp x (hYD hx))
  have hyD : y ∈ D := hYD hyY
  let ψ : ↥D →* ↥D :=
    MonoidHom.mk' (fun d : ↥D => ⁅(⟨y, hyD⟩ : ↥D), d⁆) (r4c_map_mul (p := p) hΦc ⟨y, hyD⟩)
  have hψ : ∀ d : ↥D, ψ d = ⁅(⟨y, hyD⟩ : ↥D), d⁆ := fun d => rfl
  have hrange : ψ.range ≤ frattini ↥D := by
    intro x hx
    obtain ⟨d, rfl⟩ := MonoidHom.mem_range.mp hx
    rw [hψ]
    exact r4c_comm_mem_frattini (p := p) _ _
  calc p ^ 4 ≤ Nat.card (↥D ⧸ frattini ↥D) := hQcard
    _ ≤ Nat.card ψ.ker := r4c_quot_le_ker (p := p) ψ hrange
    _ = Nat.card (eOf D Y) := (r4c_card_eq_of_map ψ.ker (r4c_ker_map hyD hgen ψ hψ)).symm

end CFSG.RankThree.PartTwo.Sec13.F135Last

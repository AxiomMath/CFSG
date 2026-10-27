module

public import CFSG.RankThree.PartTwo.Sec13.F135LastDefs
public import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG Subgroup
open scoped commutatorElement

universe u

theorem l9_odd_involution_fixed {S : Type u} [Finite S] (τ : S → S) (hτ : ∀ s, τ (τ s) = s)
    (hodd : Odd (Nat.card S)) : ∃ s, τ s = s := by
  haveI : Fintype S := Fintype.ofFinite S
  have hndvd : ¬ 2 ∣ Fintype.card S := by
    rw [← Nat.card_eq_fintype_card]
    intro h
    have h1 := Nat.odd_iff.1 hodd
    omega
  let e : Equiv.Perm S := Function.Involutive.toPerm τ hτ
  have he : e ^ (2 ^ 1) = 1 := by
    ext s
    rw [pow_one, pow_two, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    exact hτ s
  obtain ⟨s, hs⟩ := Equiv.Perm.exists_fixed_point_of_prime hndvd he
  exact ⟨s, hs⟩

theorem l9_fibre_odd {P : Type u} [Group P] [Finite P] (Q : Subgroup P) (hQ : IsPGroup 3 Q)
    (v : Q ⧸ frattini Q) :
    Odd (Nat.card {y : Q // (QuotientGroup.mk y : Q ⧸ frattini Q) = v}) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 (hQ.to_subgroup (frattini Q))
  obtain ⟨y₀, hy₀⟩ := QuotientGroup.mk_surjective v
  have hmem : ∀ n : frattini Q, (QuotientGroup.mk (y₀ * n.1) : Q ⧸ frattini Q) = v := by
    intro n
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n.1).2 n.2, mul_one, hy₀]
  have hcard : Nat.card (frattini Q) =
      Nat.card {y : Q // (QuotientGroup.mk y : Q ⧸ frattini Q) = v} := by
    refine Nat.card_eq_of_bijective (fun n : frattini Q => ⟨y₀ * n.1, hmem n⟩) ⟨?_, ?_⟩
    · intro n₁ n₂ h
      have h' : y₀ * n₁.1 = y₀ * n₂.1 := congrArg Subtype.val h
      exact Subtype.ext (mul_left_cancel h')
    · intro s
      have hmem' : y₀⁻¹ * s.1 ∈ frattini Q := by
        refine (QuotientGroup.eq_one_iff (y₀⁻¹ * s.1)).1 ?_
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hy₀, s.2, inv_mul_cancel]
      exact ⟨⟨y₀⁻¹ * s.1, hmem'⟩, Subtype.ext (mul_inv_cancel_left y₀ s.1)⟩
  rw [← hcard, hm]
  exact Odd.pow ⟨1, by norm_num⟩

theorem l9_lift_fixed {P : Type u} [Group P] [Finite P] (hP : IsPGroup 3 P) (Q : Subgroup P)
    {K : Type u} [Group K] (φ : K →* MulAut P) (ψ : K →* MulAut (Q ⧸ frattini Q))
    (hcompat : ∀ k : K, ∀ x : Q, ∃ x' : Q, (x' : P) = φ k (x : P) ∧
      ψ k (QuotientGroup.mk x) = QuotientGroup.mk x')
    (t : K) (ht : t * t = 1) (v : Q ⧸ frattini Q) (hv : ψ t v = v) :
    ∃ y : Q, (QuotientGroup.mk y : Q ⧸ frattini Q) = v ∧ φ t (y : P) = (y : P) := by
  choose σ hσP hσV using hcompat t
  have h1 : φ t * φ t = 1 := by rw [← map_mul, ht, map_one]
  have hφφ : ∀ x : P, φ t (φ t x) = x := fun x => by
    simpa using congrArg (fun g : MulAut P => g x) h1
  have hσσ : ∀ x : Q, σ (σ x) = x := by
    intro x
    apply Subtype.ext
    rw [hσP (σ x), hσP x, hφφ]
  have hτmem : ∀ s : {y : Q // (QuotientGroup.mk y : Q ⧸ frattini Q) = v},
      (QuotientGroup.mk (σ s.1) : Q ⧸ frattini Q) = v := by
    intro s
    rw [← hσV s.1, s.2, hv]
  obtain ⟨a, ha⟩ := l9_odd_involution_fixed
    (S := {y : Q // (QuotientGroup.mk y : Q ⧸ frattini Q) = v})
    (fun s => ⟨σ s.1, hτmem s⟩) (fun s => Subtype.ext (hσσ s.1))
    (l9_fibre_odd Q (hP.to_subgroup Q) v)
  refine ⟨a.1, a.2, ?_⟩
  have h2 : σ a.1 = a.1 := congrArg Subtype.val ha
  have h3 := hσP a.1
  rw [h2] at h3
  exact h3.symm

theorem l9_fix_mem {P : Type u} [Group P] {K : Type u} [Group K] (Q : Subgroup P)
    (φ : K →* MulAut P) (ψ : K →* MulAut (Q ⧸ frattini Q))
    (hcompat : ∀ k : K, ∀ x : Q, ∃ x' : Q, (x' : P) = φ k (x : P) ∧
      ψ k (QuotientGroup.mk x) = QuotientGroup.mk x')
    (t : K) (x : Q) (hx : φ t (x : P) = (x : P)) :
    ψ t (QuotientGroup.mk x) = QuotientGroup.mk x := by
  obtain ⟨x', hP', hV'⟩ := hcompat t x
  have hxx : x' = x := Subtype.ext (hP'.trans hx)
  rw [hV', hxx]

theorem l9_pRank_le {P : Type u} [Group P] [Finite P] {C F : Subgroup P} (h : C ≤ F) :
    CFSG.pRank 3 ↥C ≤ CFSG.pRank 3 ↥F := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top 3 ↥C, CFSG.SectionRank.pRank_eq_open_pRank_top 3 ↥F]
  exact CFSG.SectionRank.pRank_top_le_of_injective (by norm_num) (Subgroup.inclusion h)
    (Subgroup.inclusion_injective h)

theorem l9_card_le_of_surj {G : Type u} [Group G] [Finite G] {A : Type u} [Group A]
    (hA : ∀ a b : A, a * b = b * a) (f : G →* A) (hf : Function.Surjective f) :
    Nat.card A ≤ Nat.card (G ⧸ commutator G) := by
  have hker : commutator G ≤ f.ker := by
    rw [_root_.commutator_def]
    refine Subgroup.commutator_le.2 fun x _ y _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hA _ _)
  let g : G ⧸ commutator G →* A := QuotientGroup.lift (commutator G) f hker
  have hg : Function.Surjective g := by
    intro a
    obtain ⟨x, rfl⟩ := hf a
    exact ⟨(x : G ⧸ commutator G), QuotientGroup.lift_mk (commutator G) hker x⟩
  exact Nat.card_le_card_of_surjective g hg

theorem l9_card_quot_le {G : Type u} [Group G] [Finite G] (hG : IsPGroup 3 G)
    (hexp : ∀ x : G, x ^ 3 = 1) (hclass : commutator G ≤ Subgroup.center G)
    (hrank : CFSG.pRank 3 G ≤ 3) : Nat.card (G ⧸ commutator G) ≤ 3 ^ 4 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hG
  have h4 : CFSG.pRank 3 (G ⧸ commutator G) ≤ 4 :=
    (CFSG.RankThree.PartTwo.class_two_small_rank_order_bounds hG hexp hclass).2.2 hrank
  have hdvd : Nat.card (G ⧸ commutator G) ∣ 3 ^ n := by
    rw [← hn]
    exact Subgroup.card_quotient_dvd_card _
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have hkr := (CFSG.RankThree.PartTwo.quotient_commutator_rank Nat.prime_three hexp hk).2
  have hk4 : k ≤ 4 := by
    rw [← hkr]
    exact h4
  rw [hk]
  exact Nat.pow_le_pow_right (by norm_num) hk4

theorem card_fixed_le {P : Type u} [Group P] [Finite P] (hP : IsPGroup 3 P) (Q : Subgroup P)
    (hQexp : ∀ x ∈ Q, x ^ 3 = 1) (hQcl : ∀ x ∈ Q, ∀ y ∈ Q, ∀ z ∈ Q, ⁅⁅x, y⁆, z⁆ = 1)
    {K : Type u} [Group K] (φ : K →* MulAut P) (ψ : K →* MulAut (Q ⧸ frattini Q))
    (hcompat : ∀ k : K, ∀ x : Q, ∃ x' : Q, (x' : P) = φ k (x : P) ∧
      ψ k (QuotientGroup.mk x) = QuotientGroup.mk x')
    (t : K) (ht : t * t = 1) (hrank : CFSG.pRank 3 (fixedSubgroup (φ t)) ≤ 3) :
    Nat.card (fixedSubgroup (ψ t)) ≤ 3 ^ 4 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQ : IsPGroup 3 Q := hP.to_subgroup Q
  have hVab : IsMulCommutative (Q ⧸ frattini Q) :=
    (CFSG.GroupTheory.frattini_elementary_quotient hQ).2.1
  obtain ⟨C, hCdef⟩ : ∃ C : Subgroup P, C = Q ⊓ fixedSubgroup (φ t) := ⟨_, rfl⟩
  have hmemC : ∀ x : P, x ∈ C ↔ x ∈ Q ∧ φ t x = x := fun x => by
    rw [hCdef, Subgroup.mem_inf, mem_fixedSubgroup]
  have hCQ : C ≤ Q := fun x hx => ((hmemC x).1 hx).1
  have hCF : C ≤ fixedSubgroup (φ t) := fun x hx =>
    (mem_fixedSubgroup _ _).2 ((hmemC x).1 hx).2
  have hCexp : ∀ x : C, x ^ 3 = 1 := by
    intro x
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hQexp _ ((hmemC x.1).1 x.2).1
  have hCclass : commutator C ≤ Subgroup.center C := by
    rw [_root_.commutator_def]
    refine Subgroup.commutator_le.2 fun x _ y _ => ?_
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hc : ((⁅x, y⁆ : C) : P) = ⁅(x : P), (y : P)⁆ := by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hc]
    exact (commutatorElement_eq_one_iff_mul_comm.1
      (hQcl _ ((hmemC x.1).1 x.2).1 _ ((hmemC y.1).1 y.2).1 _ ((hmemC g.1).1 g.2).1)).symm
  have hCP : IsPGroup 3 C := hP.to_subgroup C
  have hCrank : CFSG.pRank 3 C ≤ 3 := (l9_pRank_le hCF).trans hrank
  have hb := l9_card_quot_le hCP hCexp hCclass hCrank
  let f0 : C →* (Q ⧸ frattini Q) := (QuotientGroup.mk' (frattini Q)).comp (Subgroup.inclusion hCQ)
  have hfix : ∀ c : C, f0 c ∈ fixedSubgroup (ψ t) := fun c =>
    (mem_fixedSubgroup _ _).2
      (l9_fix_mem Q φ ψ hcompat t (Subgroup.inclusion hCQ c) ((hmemC c.1).1 c.2).2)
  let f : C →* fixedSubgroup (ψ t) :=
    { toFun := fun c => ⟨f0 c, hfix c⟩
      map_one' := Subtype.ext (map_one f0)
      map_mul' := fun a b => Subtype.ext (map_mul f0 a b) }
  have hsurj : Function.Surjective f := by
    intro a
    have ha : ψ t a.1 = a.1 := (mem_fixedSubgroup _ _).1 a.2
    obtain ⟨y, hyv, hyφ⟩ := l9_lift_fixed hP Q φ ψ hcompat t ht a.1 ha
    have hyC : y.1 ∈ C := (hmemC y.1).2 ⟨y.2, hyφ⟩
    exact ⟨⟨y.1, hyC⟩, Subtype.ext hyv⟩
  have hAcomm : ∀ a b : fixedSubgroup (ψ t), a * b = b * a := by
    intro a b
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact hVab.is_comm.comm _ _
  exact (l9_card_le_of_surj hAcomm f hsurj).trans hb

end CFSG.RankThree.PartTwo.Sec13.F135Last

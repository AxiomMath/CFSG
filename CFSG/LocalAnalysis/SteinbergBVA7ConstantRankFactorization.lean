module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.PGroupBasics
public import CFSG.Foundations.Basic

public section

namespace CFSG.LocalAnalysis.SteinbergBV

open Subgroup CFSG
open scoped commutatorElement Pointwise

variable {G : Type*} [Group G]

namespace ConstantRank

theorem mem_conjugate_iff_conj {X : Subgroup G} {g y : G} :
    y ∈ CFSG.conjugate X g ↔ g * y * g⁻¹ ∈ X := by
  rw [CFSG.conjugate]
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa [mul_assoc] using hz
  · intro h
    exact ⟨g * y * g⁻¹, h, by simp [mul_assoc]⟩

theorem conjugate_eq_self_of_mem_normalizer {X : Subgroup G} {g : G}
    (hg : g ∈ normalizer (X : Set G)) : CFSG.conjugate X g = X := by
  ext y
  rw [mem_conjugate_iff_conj]
  exact ((mem_normalizer_iff.1 hg) y).symm

theorem mem_normalizer_of_conjugate_eq {X : Subgroup G} {g : G}
    (h : CFSG.conjugate X g = X) : g ∈ normalizer (X : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  have h1 := mem_conjugate_iff_conj (X := X) (g := g) (y := y)
  rwa [h] at h1

theorem conjugate_inf (H K : Subgroup G) (g : G) :
    CFSG.conjugate (H ⊓ K) g = CFSG.conjugate H g ⊓ CFSG.conjugate K g :=
  Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective

theorem conjugate_centralizer (H : Subgroup G) (g : G) :
    CFSG.conjugate (centralizer (H : Set G)) g = centralizer (CFSG.conjugate H g : Set G) := by
  ext y
  rw [mem_conjugate_iff_conj, mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro hy h hh
    rw [SetLike.mem_coe, mem_conjugate_iff_conj] at hh
    have h1 := hy _ hh
    calc h * y = g⁻¹ * ((g * h * g⁻¹) * (g * y * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * y * g⁻¹) * (g * h * g⁻¹)) * g := by rw [h1]
      _ = y * h := by group
  · intro hy h hh
    have hh' : g⁻¹ * h * g ∈ (CFSG.conjugate H g : Set G) := by
      rw [SetLike.mem_coe, mem_conjugate_iff_conj]
      simpa [mul_assoc] using hh
    have h1 := hy _ hh'
    calc h * (g * y * g⁻¹) = g * ((g⁻¹ * h * g) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * h * g)) * g⁻¹ := by rw [h1]
      _ = g * y * g⁻¹ * h := by group

theorem conjugate_centralizer_singleton (y g : G) :
    CFSG.conjugate (centralizer ({y} : Set G)) g = centralizer ({g⁻¹ * y * g} : Set G) := by
  ext z
  rw [mem_conjugate_iff_conj, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc z * (g⁻¹ * y * g) = g⁻¹ * ((g * z * g⁻¹) * y) * g := by group
      _ = g⁻¹ * (y * (g * z * g⁻¹)) * g := by rw [h]
      _ = g⁻¹ * y * g * z := by group
  · intro h
    calc g * z * g⁻¹ * y = g * (z * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * z) * g⁻¹ := by rw [h]
      _ = y * (g * z * g⁻¹) := by group

theorem relIndex_conjugate (H K : Subgroup G) (g : G) :
    (CFSG.conjugate H g).relIndex (CFSG.conjugate K g) = H.relIndex K :=
  Subgroup.relIndex_map_map_of_injective H K (MulAut.conj g⁻¹).injective

theorem le_normalizer_inf_centralizer {S W : Subgroup G} (hS : S ≤ normalizer (W : Set G)) :
    S ≤ normalizer ((S ⊓ centralizer (W : Set G) : Subgroup G) : Set G) := by
  have key : ∀ s ∈ S, ∀ y ∈ S ⊓ centralizer (W : Set G),
      s * y * s⁻¹ ∈ S ⊓ centralizer (W : Set G) := by
    intro s hs y hy
    obtain ⟨hyS, hyC⟩ := mem_inf.1 hy
    refine mem_inf.2 ⟨mul_mem (mul_mem hs hyS) (inv_mem hs), mem_centralizer_iff.2 fun w hw => ?_⟩
    have hw' : s⁻¹ * w * s⁻¹⁻¹ ∈ W := (mem_normalizer_iff.1 (hS (inv_mem hs)) w).1 hw
    rw [inv_inv] at hw'
    have h1 := mem_centralizer_iff.1 hyC _ hw'
    calc w * (s * y * s⁻¹) = s * ((s⁻¹ * w * s) * y) * s⁻¹ := by group
      _ = s * (y * (s⁻¹ * w * s)) * s⁻¹ := by rw [h1]
      _ = s * y * s⁻¹ * w := by group
  intro s hs
  rw [mem_normalizer_iff]
  intro y
  refine ⟨key s hs y, fun h => ?_⟩
  have := key s⁻¹ (inv_mem hs) _ h
  rwa [show s⁻¹ * (s * y * s⁻¹) * s⁻¹⁻¹ = y by group] at this

theorem le_normalizer_inf {S H K : Subgroup G} (hH : S ≤ normalizer (H : Set G))
    (hK : S ≤ normalizer (K : Set G)) : S ≤ normalizer ((H ⊓ K : Subgroup G) : Set G) := by
  intro s hs
  rw [mem_normalizer_iff]
  intro y
  rw [mem_inf, mem_inf, mem_normalizer_iff.1 (hH hs) y, mem_normalizer_iff.1 (hK hs) y]

theorem centralizer_sup_eq_inf (H K : Subgroup G) :
    centralizer ((H ⊔ K : Subgroup G) : Set G) =
      centralizer (H : Set G) ⊓ centralizer (K : Set G) := by
  apply le_antisymm
  · exact le_inf (centralizer_le (SetLike.coe_subset_coe.2 le_sup_left))
      (centralizer_le (SetLike.coe_subset_coe.2 le_sup_right))
  · intro y hy
    obtain ⟨hyH, hyK⟩ := mem_inf.1 hy
    have hle : H ⊔ K ≤ centralizer {y} :=
      sup_le (fun h hh => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hyH h hh))
        (fun k hk => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hyK k hk))
    exact mem_centralizer_iff.2 fun z hz => mem_centralizer_singleton_iff.1 (hle hz)

theorem relIndex_sup_of_le_normalizer {H K : Subgroup G} (hH : H ≤ normalizer (K : Set G)) :
    K.relIndex (H ⊔ K) = K.relIndex H := by
  have hK : K ≤ normalizer (K : Set G) := le_normalizer
  have h := Subgroup.relIndex_sup_right (H.subgroupOf (normalizer (K : Set G)))
    (K.subgroupOf (normalizer (K : Set G)))
  rw [← Subgroup.subgroupOf_sup hH hK, Subgroup.relIndex_subgroupOf (sup_le hH hK),
    Subgroup.relIndex_subgroupOf hH] at h
  exact h

theorem eq_of_relIndex_le [Finite G] {K L M : Subgroup G} (hKL : K ≤ L) (hLM : L ≤ M)
    (h : K.relIndex M ≤ K.relIndex L) : L = M := by
  have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hKL hLM
  have h0 : K.relIndex L ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 : L.relIndex M ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h2 : L.relIndex M ≤ 1 := by
    by_contra hcon
    push Not at hcon
    have : K.relIndex L * 2 ≤ K.relIndex L * L.relIndex M := Nat.mul_le_mul_left _ hcon
    omega
  exact le_antisymm hLM (Subgroup.relIndex_eq_one.1 (by omega))

theorem index_sup_of_constant_rank [Finite G] {S W B : Subgroup G} (hBS : B ≤ S)
    (hBN : B ≤ normalizer ((S ⊓ centralizer (W : Set G) : Subgroup G) : Set G)) {q : ℕ}
    (hq : (S ⊓ centralizer (W : Set G)).relIndex S = q) {w : G} (hw : w ∈ W)
    (hwq : (B ⊓ centralizer {w}).relIndex B = q) :
    (B ⊓ centralizer (W : Set G)).relIndex B = q ∧ B ⊔ (S ⊓ centralizer (W : Set G)) = S := by
  have hne : ∀ H L : Subgroup G, H.relIndex L ≠ 0 := fun H L => Subgroup.index_ne_zero_of_finite
  have h1 : B ⊓ centralizer (W : Set G) ≤ B ⊓ centralizer {w} :=
    inf_le_inf_left B (centralizer_le (Set.singleton_subset_iff.2 hw))
  have h2 : (B ⊓ centralizer (W : Set G)).relIndex B =
      (S ⊓ centralizer (W : Set G)).relIndex B := by
    have e : B ⊓ centralizer (W : Set G) = (S ⊓ centralizer (W : Set G)) ⊓ B :=
      le_antisymm (le_inf (le_inf (inf_le_left.trans hBS) inf_le_right) inf_le_left)
        (le_inf inf_le_right (inf_le_left.trans inf_le_right))
    rw [e, Subgroup.inf_relIndex_right]
  have h3 : (S ⊓ centralizer (W : Set G)).relIndex B ≤ q :=
    hq ▸ Subgroup.relIndex_le_of_le_right hBS (hne _ _)
  have h4 : q ≤ (B ⊓ centralizer (W : Set G)).relIndex B :=
    hwq ▸ Subgroup.relIndex_le_of_le_left h1 (hne _ _)
  have heq : (B ⊓ centralizer (W : Set G)).relIndex B = q := le_antisymm (h2 ▸ h3) h4
  refine ⟨heq, eq_of_relIndex_le le_sup_right (sup_le hBS inf_le_left) ?_⟩
  rw [relIndex_sup_of_le_normalizer hBN, hq, ← h2, heq]

@[expose] def commPowSet (p : ℕ) (X : Subgroup G) : Set G :=
  {y | (∃ a ∈ X, ∃ b ∈ X, y = ⁅a, b⁆) ∨ ∃ a ∈ X, y = a ^ p}

theorem frattini_map_eq_closure [Finite G] {p : ℕ} [Fact p.Prime] {X : Subgroup G}
    (hX : IsPGroup p X) : (frattini X).map X.subtype = closure (commPowSet p X) := by
  obtain ⟨-, hcomm, hpow⟩ := SectionRank.Ccomm.frattini_quotient_elementary hX
  apply le_antisymm
  ·
    set N : Subgroup X := (closure (commPowSet p X)).comap X.subtype with hN
    have hcomm_mem : ∀ a b : X, ⁅a, b⁆ ∈ N := fun a b =>
      subset_closure (Or.inl ⟨a, a.2, b, b.2, rfl⟩)
    have hN' : N.Normal := ⟨fun n hn g => by
      have e : g * n * g⁻¹ = ⁅g, n⁆ * n := by rw [commutatorElement_def]; group
      rw [e]
      exact mul_mem (hcomm_mem g n) hn⟩
    have hle : frattini X ≤ N := by
      refine SectionRank.Ccomm.frattini_le_of_quotient_elementary (p := p) N (fun a b => ?_)
        fun a => ?_
      · induction a using QuotientGroup.induction_on with
        | H a =>
          induction b using QuotientGroup.induction_on with
          | H b =>
            rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
            have e : (a * b)⁻¹ * (b * a) = ⁅b⁻¹, a⁻¹⁆ := by rw [commutatorElement_def]; group
            rw [e]
            exact hcomm_mem _ _
      · induction a using QuotientGroup.induction_on with
        | H a =>
          rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
          exact subset_closure (Or.inr ⟨a, a.2, rfl⟩)
    calc (frattini X).map X.subtype ≤ N.map X.subtype := map_mono hle
      _ ≤ closure (commPowSet p X) := map_comap_le _ _
  · rw [closure_le]
    rintro y (⟨a, ha, b, hb, rfl⟩ | ⟨a, ha, rfl⟩)
    · refine ⟨⁅(⟨a, ha⟩ : X), ⟨b, hb⟩⁆, ?_, rfl⟩
      rw [SetLike.mem_coe, ← QuotientGroup.eq_one_iff, commutatorElement_def, QuotientGroup.mk_mul,
        QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
        hcomm (QuotientGroup.mk ⟨a, ha⟩) (QuotientGroup.mk ⟨b, hb⟩)]
      group
    · refine ⟨(⟨a, ha⟩ : X) ^ p, ?_, rfl⟩
      rw [SetLike.mem_coe, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      exact hpow _

theorem closure_commPowSet_sup_central {p : ℕ} {E R : Subgroup G}
    (hE : E ≤ centralizer ((E ⊔ R : Subgroup G) : Set G)) (hEp : ∀ e ∈ E, e ^ p = 1) :
    closure (commPowSet p (E ⊔ R)) = closure (commPowSet p R) := by
  have hcen : ∀ e ∈ E, ∀ y ∈ E ⊔ R, y * e = e * y := fun e he y hy =>
    mem_centralizer_iff.1 (hE he) y hy
  have hRN : R ≤ normalizer (E : Set G) := fun r hr => by
    rw [mem_normalizer_iff]
    intro e
    constructor
    · intro he
      rw [hcen e he r (mem_sup_right hr), mul_inv_cancel_right]
      exact he
    · intro he
      have h1 := hcen _ he r⁻¹ (inv_mem (mem_sup_right hr))
      have h2 : e = r * e * r⁻¹ := by
        calc e = r⁻¹ * (r * e * r⁻¹) * r := by group
          _ = (r * e * r⁻¹) * r⁻¹ * r := by rw [h1]
          _ = r * e * r⁻¹ := by group
      rw [h2]
      exact he
  have hdecomp : ∀ y ∈ E ⊔ R, ∃ e ∈ E, ∃ r ∈ R, y = e * r := by
    intro y hy
    have hy' : y ∈ (E : Set G) * (R : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left E R hRN]
      exact hy
    obtain ⟨e, he, r, hr, rfl⟩ := hy'
    exact ⟨e, he, r, hr, rfl⟩
  apply le_antisymm
  · rw [closure_le]
    rintro y (⟨a, ha, b, hb, rfl⟩ | ⟨a, ha, rfl⟩)
    · obtain ⟨e, he, r, hr, rfl⟩ := hdecomp a ha
      obtain ⟨e', he', r', hr', rfl⟩ := hdecomp b hb
      have hrR : r ∈ E ⊔ R := mem_sup_right hr
      have hr'R : r' ∈ E ⊔ R := mem_sup_right hr'
      have hc4 := hcen e' he' r hrR
      have hz : e' * r * r' * r⁻¹ ∈ E ⊔ R :=
        mul_mem (mul_mem (mul_mem (mem_sup_left he') hrR) hr'R) (inv_mem hrR)
      have hcz := hcen e he _ hz
      have hcm : r * r' * r⁻¹ * r'⁻¹ ∈ E ⊔ R :=
        mul_mem (mul_mem (mul_mem hrR hr'R) (inv_mem hrR)) (inv_mem hr'R)
      have hcc := hcen e' he' _ hcm
      have e1 : ⁅e * r, e' * r'⁆ = ⁅r, r'⁆ := by
        rw [commutatorElement_def, commutatorElement_def]
        calc e * r * (e' * r') * (e * r)⁻¹ * (e' * r')⁻¹
            = e * (r * e') * r' * r⁻¹ * e⁻¹ * r'⁻¹ * e'⁻¹ := by group
          _ = e * (e' * r) * r' * r⁻¹ * e⁻¹ * r'⁻¹ * e'⁻¹ := by rw [hc4]
          _ = e * (e' * r * r' * r⁻¹) * e⁻¹ * r'⁻¹ * e'⁻¹ := by group
          _ = (e' * r * r' * r⁻¹) * e * e⁻¹ * r'⁻¹ * e'⁻¹ := by rw [← hcz]
          _ = e' * (r * r' * r⁻¹ * r'⁻¹) * e'⁻¹ := by group
          _ = (r * r' * r⁻¹ * r'⁻¹) * e' * e'⁻¹ := by rw [← hcc]
          _ = r * r' * r⁻¹ * r'⁻¹ := by group
      rw [e1]
      exact subset_closure (Or.inl ⟨r, hr, r', hr', rfl⟩)
    · obtain ⟨e, he, r, hr, rfl⟩ := hdecomp a ha
      have hc := hcen e he r (mem_sup_right hr)
      rw [(Commute.mul_pow hc.symm p), hEp e he, one_mul]
      exact subset_closure (Or.inr ⟨r, hr, rfl⟩)
  · rw [closure_le]
    rintro y (⟨a, ha, b, hb, rfl⟩ | ⟨a, ha, rfl⟩)
    · exact subset_closure (Or.inl ⟨a, mem_sup_right ha, b, mem_sup_right hb, rfl⟩)
    · exact subset_closure (Or.inr ⟨a, mem_sup_right ha, rfl⟩)

theorem conjugate_closure_commPowSet (p : ℕ) (X : Subgroup G) (g : G) :
    CFSG.conjugate (closure (commPowSet p X)) g = closure (commPowSet p (CFSG.conjugate X g)) := by
  rw [CFSG.conjugate, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨z, (⟨a, ha, b, hb, rfl⟩ | ⟨a, ha, rfl⟩), rfl⟩
    · exact Or.inl ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, map_commutatorElement _ _ _⟩
    · exact Or.inr ⟨_, ⟨a, ha, rfl⟩, map_pow _ _ _⟩
  · rintro (⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩ | ⟨_, ⟨a, ha, rfl⟩, rfl⟩)
    · exact ⟨⁅a, b⁆, Or.inl ⟨a, ha, b, hb, rfl⟩, map_commutatorElement _ _ _⟩
    · exact ⟨a ^ p, Or.inr ⟨a, ha, rfl⟩, map_pow _ _ _⟩

theorem commutator_sup_eq_of_centralizer {W B N : Subgroup G} (hN : N ≤ centralizer (W : Set G))
    (hBN : B ≤ normalizer (N : Set G)) : ⁅W, B ⊔ N⁆ = ⁅W, B⁆ := by
  refine le_antisymm ?_ (commutator_mono le_rfl le_sup_left)
  rw [commutator_le]
  intro w hw s hs
  have hs' : s ∈ (B : Set G) * (N : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right B N hBN]
    exact hs
  obtain ⟨b, hb, k, hk, rfl⟩ := hs'
  have hkw := mem_centralizer_iff.1 (hN hk) w hw
  have e : ⁅w, b * k⁆ = ⁅w, b⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc w * (b * k) * w⁻¹ * (b * k)⁻¹ = w * b * (k * w⁻¹) * k⁻¹ * b⁻¹ := by group
      _ = w * b * (w⁻¹ * k) * k⁻¹ * b⁻¹ := by
        rw [show k * w⁻¹ = w⁻¹ * k by
          rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hkw, inv_mul_cancel_left]]
      _ = w * b * w⁻¹ * b⁻¹ := by group
  rw [e]
  exact commutator_mem_commutator hw hb

end ConstantRank

open ConstantRank in

theorem constant_rank_conjugates_force_centralizer_factorization [Finite G] {p : ℕ}
    [hp : Fact p.Prime] {S U A Q C : Subgroup G} (hS : IsPGroup p S) {x : G}
    (hx : x ∈ normalizer (S : Set G)) (hUS : U ≤ S) (hUn : S ≤ normalizer (U : Set G))
    (hUel : IsElementaryAbelian p U) (hA : A = CFSG.conjugate U x)
    (hQ : Q = S ⊓ centralizer (U : Set G))
    (hC : C = S ⊓ centralizer ((U ⊔ A : Subgroup G) : Set G)) {n : ℕ} (_hn : 1 ≤ n)
    (hidx : Q.relIndex S = p ^ n)
    (hconst : ∀ s ∈ S, s ∉ Q → (U ⊓ centralizer {s}).relIndex U = p ^ n)
    (hUA : ⁅U, A⁆ ≠ ⊥) :
    A ⊔ Q = S ∧ U ⊔ CFSG.conjugate Q x = S ∧ U ⊔ A ⊔ C = S ∧ U ⊔ C = Q ∧
    A ⊔ C = CFSG.conjugate Q x ∧ C.relIndex S = p ^ (2 * n) ∧
    (U ⊓ centralizer (A : Set G)).relIndex U = p ^ n ∧
    (A ⊓ centralizer (U : Set G)).relIndex A = p ^ n ∧
    CFSG.conjugate ((frattini Q).map Q.subtype) x = (frattini Q).map Q.subtype ∧
    (⁅U, S⁆ = U ⊓ centralizer (S : Set G) →
      ⁅U, A⁆ = U ⊓ A ∧ U ⊓ A = U ⊓ centralizer (A : Set G) ∧
        x ∈ normalizer ((⁅U, A⁆ : Subgroup G) : Set G)) := by
  classical
  subst hA hQ hC
  have hne : ∀ H L : Subgroup G, H.relIndex L ≠ 0 := fun H L => Subgroup.index_ne_zero_of_finite
  have hpn : 0 < p ^ n := pow_pos hp.out.pos n
  have hUcomm : ∀ y ∈ U, ∀ z ∈ U, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hUel.toIsMulCommutative.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hUp : ∀ e ∈ U, e ^ p = 1 := fun e he => by
    have := hUel
    exact elemPow_eq_one_of_isElementaryAbelian e he
  have hxS : CFSG.conjugate S x = S := conjugate_eq_self_of_mem_normalizer hx
  have hAS : CFSG.conjugate U x ≤ S := fun y hy => by
    rw [← hxS, mem_conjugate_iff_conj]
    rw [mem_conjugate_iff_conj] at hy
    exact hUS hy
  have hAn : S ≤ normalizer ((CFSG.conjugate U x : Subgroup G) : Set G) := by
    intro s hs
    rw [mem_normalizer_iff]
    intro y
    rw [mem_conjugate_iff_conj, mem_conjugate_iff_conj]
    have hs' : x * s * x⁻¹ ∈ S := (mem_normalizer_iff.1 hx s).1 hs
    have h1 := mem_normalizer_iff.1 (hUn hs') (x * y * x⁻¹)
    rw [show x * s * x⁻¹ * (x * y * x⁻¹) * (x * s * x⁻¹)⁻¹ = x * (s * y * s⁻¹) * x⁻¹ by
      group] at h1
    exact h1
  have hAcomm : ∀ y ∈ CFSG.conjugate U x, ∀ z ∈ CFSG.conjugate U x, y * z = z * y := by
    intro y hy z hz
    rw [mem_conjugate_iff_conj] at hy hz
    have h1 := hUcomm _ hy _ hz
    calc y * z = x⁻¹ * ((x * y * x⁻¹) * (x * z * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * z * x⁻¹) * (x * y * x⁻¹)) * x := by rw [h1]
      _ = z * y := by group
  have hAp : ∀ e ∈ CFSG.conjugate U x, e ^ p = 1 := by
    intro e he
    rw [mem_conjugate_iff_conj] at he
    have h1 := hUp _ he
    rw [conj_pow] at h1
    have h2 := congrArg (fun z => x⁻¹ * z * x) h1
    simpa [mul_assoc] using h2
  set A := CFSG.conjugate U x with hAdef
  set Q := S ⊓ centralizer (U : Set G) with hQdef
  have hQx : CFSG.conjugate Q x = S ⊓ centralizer (A : Set G) := by
    rw [hQdef, conjugate_inf, hxS, conjugate_centralizer]
  have hQS : Q ≤ S := inf_le_left
  have hQxS : S ⊓ centralizer (A : Set G) ≤ S := inf_le_left
  have hQn : S ≤ normalizer (Q : Set G) := le_normalizer_inf_centralizer hUn
  have hQxn : S ≤ normalizer ((S ⊓ centralizer (A : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf_centralizer hAn
  have hidx' : (S ⊓ centralizer (A : Set G)).relIndex S = p ^ n := by
    rw [← hQx, ← hidx, ← relIndex_conjugate Q S x, hxS]
  have hUQ : U ≤ Q := le_inf hUS fun y hy => mem_centralizer_iff.2 fun z hz => hUcomm z hz y hy
  have hAQx : A ≤ S ⊓ centralizer (A : Set G) :=
    le_inf hAS fun y hy => mem_centralizer_iff.2 fun z hz => hAcomm z hz y hy
  have hconst' : ∀ s ∈ S, s ∉ S ⊓ centralizer (A : Set G) →
      (A ⊓ centralizer {s}).relIndex A = p ^ n := by
    intro s hs hsQ
    have hs' : x * s * x⁻¹ ∈ S := (mem_normalizer_iff.1 hx s).1 hs
    have hs'Q : x * s * x⁻¹ ∉ Q := by
      intro h
      apply hsQ
      rw [← hQx, mem_conjugate_iff_conj]
      exact h
    have h := hconst _ hs' hs'Q
    have e : CFSG.conjugate (U ⊓ centralizer {x * s * x⁻¹}) x = A ⊓ centralizer {s} := by
      rw [conjugate_inf, conjugate_centralizer_singleton,
        show x⁻¹ * (x * s * x⁻¹) * x = s by group]
    rw [← e, relIndex_conjugate]
    exact h
  obtain ⟨u, hu, a, ha, hua⟩ : ∃ u ∈ U, ∃ a ∈ A, a * u ≠ u * a := by
    by_contra hcon
    push Not at hcon
    apply hUA
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro u hu
    rw [mem_centralizer_iff]
    intro a ha
    exact hcon u hu a ha
  have huQx : u ∉ S ⊓ centralizer (A : Set G) := fun h =>
    hua (mem_centralizer_iff.1 (mem_inf.1 h).2 a ha)
  have haQ : a ∉ Q := fun h => hua (mem_centralizer_iff.1 (mem_inf.1 h).2 u hu).symm
  obtain ⟨hAidx, hAQ⟩ := index_sup_of_constant_rank hAS (hAS.trans hQn) hidx hu
    (hconst' u (hUS hu) huQx)
  obtain ⟨hUidx, hUQx⟩ := index_sup_of_constant_rank hUS (hUS.trans hQxn) hidx' ha
    (hconst a (hAS ha) haQ)
  have hCeq : S ⊓ centralizer ((U ⊔ A : Subgroup G) : Set G) =
      Q ⊓ (S ⊓ centralizer (A : Set G)) := by
    rw [centralizer_sup_eq_inf, hQdef]
    ext y
    simp only [mem_inf]
    tauto
  set C := S ⊓ centralizer ((U ⊔ A : Subgroup G) : Set G) with hCdef
  have hCQ : C ≤ Q := hCeq ▸ inf_le_left
  have hCQx : C ≤ S ⊓ centralizer (A : Set G) := hCeq ▸ inf_le_right
  have hCn : S ≤ normalizer (C : Set G) := hCeq ▸ le_normalizer_inf hQn hQxn
  have hCle : C.relIndex S ≤ p ^ n * p ^ n := by
    rw [hCeq]
    have h := Subgroup.relIndex_inf_le (H := Q) (K := S ⊓ centralizer (A : Set G)) (L := S)
    rw [hidx, hidx'] at h
    exact h
  have hUC : C.relIndex U = p ^ n := by
    have e : U ⊓ C = U ⊓ centralizer (A : Set G) := by
      rw [hCeq]
      exact le_antisymm (le_inf inf_le_left (inf_le_right.trans (inf_le_right.trans inf_le_right)))
        (le_inf inf_le_left (le_inf (inf_le_left.trans hUQ)
          (le_inf (inf_le_left.trans hUS) inf_le_right)))
    rw [← Subgroup.inf_relIndex_right C U, inf_comm, e, hUidx]
  have hAC : C.relIndex A = p ^ n := by
    have e : A ⊓ C = A ⊓ centralizer (U : Set G) := by
      rw [hCeq]
      exact le_antisymm (le_inf inf_le_left (inf_le_right.trans (inf_le_left.trans inf_le_right)))
        (le_inf inf_le_left (le_inf (le_inf (inf_le_left.trans hAS) inf_le_right)
          (inf_le_left.trans hAQx)))
    rw [← Subgroup.inf_relIndex_right C A, inf_comm, e, hAidx]
  have hUCQ : U ⊔ C ≤ Q := sup_le hUQ hCQ
  have h1 : C.relIndex (U ⊔ C) = p ^ n := by
    rw [relIndex_sup_of_le_normalizer (hUS.trans hCn), hUC]
  have h2 : p ^ n ≤ C.relIndex Q := h1 ▸ Subgroup.relIndex_le_of_le_right hUCQ (hne _ _)
  have hmulQ := Subgroup.relIndex_mul_relIndex _ _ _ hCQ hQS
  rw [hidx] at hmulQ
  have hCS : C.relIndex S = p ^ n * p ^ n := by
    refine le_antisymm hCle ?_
    rw [← hmulQ]
    exact Nat.mul_le_mul_right _ h2
  have hCQidx : C.relIndex Q = p ^ n := by
    rw [hCS] at hmulQ
    exact Nat.eq_of_mul_eq_mul_right hpn hmulQ
  have hUCeq : U ⊔ C = Q := eq_of_relIndex_le le_sup_right hUCQ (by rw [hCQidx, h1])
  have hACQx : A ⊔ C ≤ S ⊓ centralizer (A : Set G) := sup_le hAQx hCQx
  have h1' : C.relIndex (A ⊔ C) = p ^ n := by
    rw [relIndex_sup_of_le_normalizer (hAS.trans hCn), hAC]
  have hmulQx := Subgroup.relIndex_mul_relIndex _ _ _ hCQx hQxS
  rw [hidx', hCS] at hmulQx
  have hCQxidx : C.relIndex (S ⊓ centralizer (A : Set G)) = p ^ n :=
    Nat.eq_of_mul_eq_mul_right hpn hmulQx
  have hACeq : A ⊔ C = S ⊓ centralizer (A : Set G) :=
    eq_of_relIndex_le le_sup_right hACQx (by rw [hCQxidx, h1'])
  have hΦ := frattini_map_eq_closure (hS.to_le hQS)
  have hUcen : U ≤ centralizer ((U ⊔ C : Subgroup G) : Set G) := by
    rw [hUCeq]
    intro y hy
    rw [mem_centralizer_iff]
    intro z hz
    exact (mem_centralizer_iff.1 (mem_inf.1 hz).2 y hy).symm
  have hAcen : A ≤ centralizer ((A ⊔ C : Subgroup G) : Set G) := by
    rw [hACeq]
    intro y hy
    rw [mem_centralizer_iff]
    intro z hz
    exact (mem_centralizer_iff.1 (mem_inf.1 hz).2 y hy).symm
  have hΨQ : closure (commPowSet p Q) = closure (commPowSet p C) := by
    rw [← hUCeq]
    exact closure_commPowSet_sup_central hUcen hUp
  have hΨQx : closure (commPowSet p (S ⊓ centralizer (A : Set G))) =
      closure (commPowSet p C) := by
    rw [← hACeq]
    exact closure_commPowSet_sup_central hAcen hAp
  have hfrat : CFSG.conjugate ((frattini Q).map Q.subtype) x = (frattini Q).map Q.subtype := by
    rw [hΦ, conjugate_closure_commPowSet, hQx, hΨQx, ← hΨQ]
  refine ⟨hAQ, by rw [hQx]; exact hUQx, by rw [sup_assoc, hACeq]; exact hUQx, hUCeq,
    hACeq.trans hQx.symm, by rw [hCS, ← pow_add, two_mul], hUidx, hAidx, hfrat,
    fun hUS' => ?_⟩
  have hcommUA : ⁅U, S⁆ = ⁅U, A⁆ := by
    conv_lhs => rw [← hAQ]
    exact commutator_sup_eq_of_centralizer inf_le_right (hAS.trans hQn)
  have hCUA : U ⊓ centralizer (A : Set G) = U ⊓ centralizer (S : Set G) := by
    conv_rhs => rw [← hAQ]
    rw [centralizer_sup_eq_inf, ← inf_assoc]
    refine (inf_eq_left.2 (inf_le_left.trans fun y hy => mem_centralizer_iff.2 fun z hz =>
      (mem_centralizer_iff.1 (mem_inf.1 hz).2 y hy).symm)).symm
  have hle1 : ⁅U, A⁆ ≤ U ⊓ A := by
    rw [commutator_le]
    intro u hu a ha
    refine mem_inf.2 ⟨?_, ?_⟩
    · rw [commutatorElement_def, show u * a * u⁻¹ * a⁻¹ = u * (a * u⁻¹ * a⁻¹) by group]
      exact mul_mem hu ((mem_normalizer_iff.1 (hUn (hAS ha)) u⁻¹).1 (inv_mem hu))
    · rw [commutatorElement_def]
      exact mul_mem ((mem_normalizer_iff.1 (hAn (hUS hu)) a).1 ha) (inv_mem ha)
  have hle2 : U ⊓ A ≤ U ⊓ centralizer (A : Set G) := fun y hy =>
    mem_inf.2 ⟨(mem_inf.1 hy).1, mem_centralizer_iff.2 fun z hz => hAcomm z hz y (mem_inf.1 hy).2⟩
  have hkey : ⁅U, A⁆ = U ⊓ centralizer (A : Set G) := by rw [← hcommUA, hUS', hCUA]
  have hUAeq : ⁅U, A⁆ = U ⊓ A := le_antisymm hle1 (hkey ▸ hle2)
  have e1 : CFSG.conjugate ⁅U, S⁆ x = ⁅A, S⁆ := by
    change (⁅U, S⁆).map (MulAut.conj x⁻¹).toMonoidHom = ⁅A, S⁆
    rw [Subgroup.map_commutator]
    change ⁅CFSG.conjugate U x, CFSG.conjugate S x⁆ = ⁅A, S⁆
    rw [hxS]
  have hAS' : ⁅A, S⁆ = ⁅A, U⁆ := by
    conv_lhs => rw [← hUQx]
    exact commutator_sup_eq_of_centralizer inf_le_right (hUS.trans hQxn)
  have hconjc : CFSG.conjugate ⁅U, A⁆ x = ⁅U, A⁆ := by
    rw [← hcommUA, e1, hAS', commutator_comm, hcommUA]
  exact ⟨hUAeq, hUAeq.symm.trans hkey, mem_normalizer_of_conjugate_eq hconjc⟩

end CFSG.LocalAnalysis.SteinbergBV

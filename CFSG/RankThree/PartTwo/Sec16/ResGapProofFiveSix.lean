module

public import CFSG.RankThree.PartTwo.Sec16.ResGapProofFiveMin
public import CFSG.RankThree.PartTwo.Sec16.ResGapProofFivePair
public import CFSG.RankThree.PartTwo.Sec3.TwoGroupPrimeFiveAction
import CFSG.RankThree.PartOne.S10.PlaneHyperplane
import CFSG.Assembly.OrderReductions.FrattiniAutomorphisms
import CFSG.LinearAlgebra.OddSolvableUnitary.CommutatorForm
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.LocalAnalysis.SignalizerFunctor.Maximality
import CFSG.Assembly.OrderReductions.FrattiniElementary

public section

namespace CFSG.RankThree.PartTwo.Sec16.ResGapFive

open Subgroup CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec3
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem eq_of_card_two {H : Subgroup G} (h2 : Nat.card H = 2) {a b : G} (ha : a ∈ H)
    (hb : b ∈ H) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  by_contra hab
  have hsub : ({1, a, b} : Set G) ⊆ H := by
    rintro y (rfl | rfl | rfl)
    · exact one_mem H
    · exact ha
    · exact hb
  have h3 : ({1, a, b} : Set G).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨1, a, b, ha1.symm, hb1.symm, hab, rfl⟩
  have h2' : (H : Set G).ncard = 2 := (Nat.card_coe_set_eq (H : Set G)).symm.trans h2
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [h3, h2'] at hle
  omega

theorem false_of_extraspecial_section {p q : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hq : q.Prime) (hq3 : 3 < q) (hp3 : 3 < p) {P D U Z : Subgroup G} (hP : IsPGroup p P)
    (hDP : D ≤ P) (hDexp : ∀ d ∈ D, d ^ p = 1)
    (hDcl : ∀ a ∈ D, ∀ b ∈ D, ∀ c ∈ D, ⁅a, b⁆ * c = c * ⁅a, b⁆)
    (hUD : U ≤ normalizer (D : Set G)) {x : G} (hxD : x ∈ normalizer (D : Set G))
    (hxU : x ∈ normalizer (U : Set G)) (hxq : x ^ q = 1) (hU2 : IsPGroup 2 U)
    (hZU : Z ≤ U) (hZc : ∀ z ∈ Z, ∀ v ∈ U, z * v = v * z) (hUUZ : ⁅U, U⁆ = Z)
    (hsqZ : ∀ u ∈ U, u ^ 2 ∈ Z) (hUZ : U ≠ Z) (hKZ : U ⊓ centralizer (D : Set G) ≤ Z)
    (hK2 : Nat.card Z = 2 * Nat.card ↥(U ⊓ centralizer (D : Set G)))
    (hcen : ∀ u ∈ U, (∀ v ∈ U, ⁅u, v⁆ ∈ centralizer (D : Set G)) → u ∈ Z)
    (hfpf : ∀ u ∈ U, x * u * x⁻¹ * u⁻¹ ∈ Z → u ∈ Z)
    (hfix : ∀ u ∈ U, u ∉ centralizer (D : Set G) →
      CFSG.Assembly.pRank p (P ⊓ centralizer ({u} : Set G)) ≤ 2)
    (hZ2 : ∀ z ∈ Z, z ^ 2 = 1) {z' : G} (hz'D : z' ∈ centralizer (D : Set G))
    (hz'fix : CFSG.Assembly.pRank p (P ⊓ centralizer ({z'} : Set G)) ≤ 2) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ := conjAction D U hUD with hφ
  set K := φ.ker with hK
  set S := U ⧸ K
  set π := QuotientGroup.mk' K with hπ
  set Z' := Z.subgroupOf U with hZ'
  have hmemK : ∀ u : U, u ∈ K ↔ (u : G) ∈ centralizer (D : Set G) := fun u => mem_ker_conjAction
  have hKZ' : K ≤ Z' := fun u hu => hKZ ⟨u.2, (hmemK u).mp hu⟩
  have hmemZ : ∀ w : U, π w ∈ Z'.map π → w ∈ Z' := by
    intro w ⟨z, hz, hzw⟩
    have h1 : z⁻¹ * w ∈ K := by
      rw [← QuotientGroup.eq]
      exact hzw
    have := Z'.mul_mem hz (hKZ' h1)
    rwa [mul_inv_cancel_left] at this
  have hS2 : IsPGroup 2 S := (hU2.to_quotient K)
  have hZS : Subgroup.center S = Z'.map π := by
    apply le_antisymm
    · intro s hs
      obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective K s
      refine ⟨u, ?_, rfl⟩
      show (u : G) ∈ Z
      apply hcen u u.2
      intro v hv
      have h1 := Subgroup.mem_center_iff.mp hs (π ⟨v, hv⟩)
      rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq, hmemK] at h1
      have : (((⟨v, hv⟩ * u : U)⁻¹ * (u * ⟨v, hv⟩) : U) : G) = ⁅(u : G)⁻¹, v⁻¹⁆ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
        group
      rw [this] at h1
      have h2 := (mem_normalizer_iff.mp
        (mem_normalizer_centralizer (hUD (mul_mem u.2 hv))) _).mp h1
      rwa [show (u : G) * v * ⁅(u : G)⁻¹, v⁻¹⁆ * ((u : G) * v)⁻¹ = ⁅(u : G), v⁆ by
        simp only [commutatorElement_def]; group] at h2
    · rintro _ ⟨z, hz, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro s
      obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective K s
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext ((hZc z hz v v.2).symm)
  have hcomU : commutator U = Z' := by
    apply map_injective U.subtype_injective
    rw [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype, hUUZ,
      subgroupOf_map_subtype, inf_of_le_left hZU]
  have hcomS : commutator S = Z'.map π := by
    rw [← hcomU, _root_.commutator_def, _root_.commutator_def, map_commutator,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective K)]
  have hfrS : frattini S = Z'.map π := by
    have : Fact (IsPGroup 2 S) := ⟨hS2⟩
    apply le_antisymm
    · rw [CFSG.frattini_eq_closure_commutator_union_powers (p := 2), closure_le]
      rintro s (hs | ⟨t, rfl⟩)
      · rw [← hcomS]
        exact hs
      · obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective K t
        refine ⟨u ^ 2, ?_, by rw [map_pow]⟩
        show ((u ^ 2 : U) : G) ∈ Z
        rw [Subgroup.coe_pow]
        exact hsqZ _ u.2
    · rw [← hcomS]
      exact CFSG.OrderReductions.FrattiniElementary.commutator_le_frattini 2 hS2
  have hcardZS : Nat.card (Subgroup.center S) = 2 := by
    rw [hZS, ← relIndex_ker, QuotientGroup.ker_mk']
    have h := relIndex_mul_card (H := K) (K := Z')
    rw [inf_of_le_left hKZ'] at h
    have hZ'c : Nat.card Z' = Nat.card Z := Nat.card_congr (subgroupOfEquivOfLe hZU).toEquiv
    have hKc : Nat.card K = Nat.card ↥(U ⊓ centralizer (D : Set G)) := by
      refine Nat.card_congr ?_
      exact
        { toFun := fun k => ⟨(k : U), (k : U).2, (hmemK k).mp k.2⟩
          invFun := fun g => ⟨⟨g, g.2.1⟩, (hmemK _).mpr g.2.2⟩
          left_inv := fun k => rfl
          right_inv := fun g => rfl }
    rw [hZ'c, hK2, hKc] at h
    have hpos : 0 < Nat.card ↥(U ⊓ centralizer (D : Set G)) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos h
  have hZcom : Subgroup.center S = commutator S := hZS.trans hcomS.symm
  have hSx : IsExtraspecialPGroup 2 S :=
    ⟨hS2, hZcom.symm, hfrS.trans hZS.symm, hcardZS⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Nat.card S = 2 ^ (1 + 2 * n) := by
    obtain ⟨ε⟩ := CFSG.OddSolvableUnitary.nonempty_center_mulEquiv hcardZS
    let _ : Module (ZMod 2) (Additive (Abelianization S)) := AddCommGroup.zmodModule fun v => by
      obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
      change Additive.ofMul ((Abelianization.of t) ^ 2) = Additive.ofMul 1
      congr 1
      rw [← map_pow, ← MonoidHom.mem_ker, Abelianization.ker_of, hcomS]
      obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective K t
      refine ⟨u ^ 2, ?_, by rw [map_pow]⟩
      show ((u ^ 2 : U) : G) ∈ Z
      rw [Subgroup.coe_pow]
      exact hsqZ _ u.2
    obtain ⟨B, hBa, hBn, -⟩ := CFSG.OddSolvableUnitary.exists_commForm hZcom ε
    have : Finite (Additive (Abelianization S)) :=
      Finite.of_surjective (fun x : S => Additive.ofMul (Abelianization.of x))
        fun v => QuotientGroup.mk_surjective (Additive.toMul v)
    have : Module.Finite (ZMod 2) (Additive (Abelianization S)) := Module.Finite.of_finite
    obtain ⟨a, ha⟩ := LinearMap.BilinForm.IsAlt.even_finrank (K := ZMod 2) hBa hBn
    refine ⟨a, ?_⟩
    rw [CFSG.OddSolvableUnitary.card_eq_card_abelianization_mul hZcom hcardZS]
    change Nat.card (Additive (Abelianization S)) * 2 = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, ha, ← two_mul, pow_add,
      pow_one, mul_comm]
  have hn1 : 1 ≤ n := by
    by_contra h
    have hn0 : n = 0 := by omega
    rw [hn0, mul_zero, add_zero, pow_one] at hn
    have htop : Subgroup.center S = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (hcardZS.trans hn.symm)
    apply hUZ
    refine le_antisymm (fun u hu => ?_) hZU
    have h := hmemZ ⟨u, hu⟩ (by rw [← hZS, htop]; exact mem_top _)
    exact h
  let γ : MulAut S := conjQuot hUD hxD hxU
  have hγfix : ∀ s, γ s * s⁻¹ ∈ Subgroup.center S → s ∈ Subgroup.center S := by
    intro s hs
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective s
    obtain ⟨hu, he⟩ := conjQuot_mk hUD hxD hxU u
    change conjQuot hUD hxD hxU (u : U ⧸ φ.ker) * _ ∈ _ at hs
    rw [he, hZS, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul] at hs
    have h1 := hmemZ _ hs
    rw [mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at h1
    have h2 := hfpf u u.2 h1
    rw [hZS]
    exact ⟨u, h2, rfl⟩
  have hDp : IsPGroup p D := hP.to_le hDP
  have hDexp' : ∀ d : D, d ^ p = 1 := fun d =>
    Subtype.ext (by rw [Subgroup.coe_pow, hDexp d d.2, Subgroup.coe_one])
  have hn2 : 2 ≤ n := by
    let ψ := CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (Subgroup.center S)
    have hψ : ∀ s : S, ψ γ (s : S ⧸ Subgroup.center S) = ((γ s : S) : S ⧸ Subgroup.center S) :=
      fun s => CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism_apply _ γ s
    have hγq : γ ^ q = 1 := conjQuot_pow_eq_one hUD hxD hxU hxq
    have : Fact q.Prime := ⟨hq⟩
    let Γ := zpowers (ψ γ)
    have hΓ : IsPGroup q Γ := fun g => ⟨1, by
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp g.2
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← hk, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast, ← map_pow, hγq, map_one, one_zpow, Subgroup.coe_one]⟩
    have h := hΓ.card_modEq_card_fixedPoints (S ⧸ Subgroup.center S)
    have hfp : Nat.card (MulAction.fixedPoints Γ (S ⧸ Subgroup.center S)) = 1 := by
      rw [Nat.card_eq_one_iff_exists]
      refine ⟨⟨1, fun g => map_one (g : MulAut (S ⧸ Subgroup.center S))⟩, fun ⟨w, hw⟩ =>
        Subtype.ext ?_⟩
      obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective w
      have h1 := hw ⟨ψ γ, mem_zpowers _⟩
      change ψ γ (s : S ⧸ Subgroup.center S) = (s : S ⧸ Subgroup.center S) at h1
      rw [hψ, QuotientGroup.eq] at h1
      change (s : S ⧸ Subgroup.center S) = 1
      rw [QuotientGroup.eq_one_iff]
      apply hγfix
      have h2 : γ s * s⁻¹ = s * ((γ s)⁻¹ * s)⁻¹ * s⁻¹ := by group
      rw [h2]
      exact Subgroup.Normal.conj_mem inferInstance _ (inv_mem h1) s
    rw [hfp] at h
    have hquot : Nat.card (S ⧸ Subgroup.center S) = 2 ^ (2 * n) := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center S)
      rw [hn, hcardZS, pow_add, pow_one] at h1
      omega
    rw [hquot] at h
    have hq1 : q ∣ 2 ^ (2 * n) - 1 := (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp h.symm
    by_contra hlt
    have hn1' : n = 1 := by omega
    rw [hn1'] at hq1
    norm_num at hq1
    have := Nat.le_of_dvd (by norm_num) hq1
    omega
  obtain ⟨z₀, hz₀Z, hz₀K⟩ : ∃ z₀ ∈ Z, z₀ ∉ centralizer (D : Set G) := by
    by_contra hcon
    push Not at hcon
    have hle : Z ≤ U ⊓ centralizer (D : Set G) := fun z hz => ⟨hZU hz, hcon z hz⟩
    have h1 := Subgroup.card_le_of_le hle
    have hpos : 0 < Nat.card ↥(U ⊓ centralizer (D : Set G)) := Nat.card_pos
    omega
  set zt : U := ⟨z₀, hZU hz₀Z⟩ with hzt
  have hztc : zt ∈ Subgroup.center U := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hZc z₀ hz₀Z g g.2).symm
  have hztK : zt ∉ K := fun h => hz₀K ((hmemK zt).mp h)
  have hzt2 : (φ zt) ^ 2 = 1 := by
    rw [← map_pow]
    have : zt ^ 2 = 1 := Subtype.ext (by simpa using hZ2 z₀ hz₀Z)
    rw [this, map_one]
  obtain ⟨f, hf⟩ : ∃ f : D, φ zt f ≠ f := by
    by_contra hcon
    push Not at hcon
    exact hztK (MonoidHom.mem_ker.mpr (MulEquiv.ext fun y => by
      rw [MulAut.one_apply]
      exact hcon y))
  set Pz : Subgroup D := CFSG.RankThree.PartOne.PlaneHyperplane.invCommutator (φ zt) ⊤ with hPz
  have hPinv : ∀ t : U, ∀ y ∈ Pz, φ t y ∈ Pz := by
    intro t y hy
    refine CFSG.RankThree.PartOne.PlaneHyperplane.invCommutator_invariant (u := φ zt)
      (τ := φ t) ?_ (fun _ _ => mem_top _) hy
    show φ zt * φ t = φ t * φ zt
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hztc t]
  have hNtriv : ∀ t ∈ K, ∀ y ∈ Pz, φ t y = y := by
    intro t ht y _
    rw [MonoidHom.mem_ker.mp ht, MulAut.one_apply]
  have hzmove : ∃ y ∈ Pz, φ zt y ≠ y :=
    CFSG.RankThree.PartOne.PlaneHyperplane.exists_apply_ne_of_invCommutator hp2 hp.out hDexp'
      hzt2 (mem_top f) hf
  have hPgen : Pz ≤ Subgroup.closure {w : D | ∃ y ∈ Pz, w = y⁻¹ * φ zt y} :=
    CFSG.RankThree.PartOne.PlaneHyperplane.invCommutator_le_invCommutator_self hp2 hp.out hDexp'
      hzt2
  have hEA : ∀ E : Subgroup D, IsElementaryAbelian p E → ∀ {H : Subgroup G},
      (∀ e ∈ E, (e : G) ∈ H) → ∀ k : ℕ, Nat.card E = p ^ k →
        k ≤ CFSG.Assembly.pRank p H := by
    intro E hE H hEH k hk
    have := hE
    have hE' : IsElementaryAbelian p (E.map D.subtype) := IsElementaryAbelian.map_subtype (H := E)
    refine CFSG.SectionRank.le_pRank hp.out.one_lt (E := E.map D.subtype) ?_
      ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).mp hE') ?_
    · rintro _ ⟨e, he, rfl⟩
      exact hEH e he
    · rw [Subgroup.card_map_of_injective D.subtype_injective, hk]
  have hrank : ∀ t : U, t ∉ K → ∀ E : Subgroup D, IsElementaryAbelian p E → E ≤ Pz →
      (∀ e ∈ E, φ t e = e) → ∀ k : ℕ, Nat.card E = p ^ k → k ≤ 3 := by
    intro t htK E hE _ hEfix k hk
    have ht : (t : G) ∉ centralizer (D : Set G) := fun h => htK ((hmemK t).mpr h)
    have h1 := hEA E hE (H := P ⊓ centralizer ({(t : G)} : Set G)) (fun e he => by
      refine ⟨hDP e.2, mem_centralizer_singleton_iff.mpr ?_⟩
      have h2 := congrArg Subtype.val (hEfix e he)
      rw [conjAction_apply_coe] at h2
      calc (e : G) * t = (t * e * (t : G)⁻¹) * t := by rw [h2]
        _ = t * e := by group) k hk
    have h2 := hfix t t.2 ht
    omega
  have hPrank : ∀ E : Subgroup D, IsElementaryAbelian p E → E ≤ Pz → ∀ k : ℕ,
      Nat.card E = p ^ k → k ≤ 2 := by
    intro E hE _ k hk
    have h1 := hEA E hE (H := P ⊓ centralizer ({z'} : Set G)) (fun e _ =>
      ⟨hDP e.2, mem_centralizer_singleton_iff.mpr
        (mem_centralizer_iff.mp hz'D (e : G) e.2)⟩) k hk
    omega
  exact CFSG.RankThree.PartOne.PlaneHyperplane.extraspecial_quotient_contradiction hp.out hp3
    hDp hDexp' (commutator_le_center_of_forall hDcl) φ hn2 hSx hn hztc hztK hPinv hNtriv hzmove
    hPgen hrank hPrank

theorem false_of_c_action {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {P U X : Subgroup G}
    (hP : IsPGroup p P) (hU : IsPGroup 2 U) (hXq : Nat.card X = 5) (hUX : ⁅U, X⁆ = U)
    (hU1 : U ≠ ⊥) (hUP : U ≤ normalizer (P : Set G)) (hXP : X ≤ normalizer (P : Set G))
    (hfaith : U ⊓ centralizer (P : Set G) = ⊥)
    (hfix : ∀ u ∈ U, u ≠ 1 → CFSG.Assembly.pRank p (P ⊓ centralizer ({u} : Set G)) ≤ 2)
    {c : G} (hc3 : c ^ 3 = 1) (hcU : c ∈ normalizer (U : Set G))
    (hcX : ∀ y ∈ X, y * c = c * y)
    (hcfix : ∀ u ∈ U, c * u * c⁻¹ = u → ∀ y ∈ X, y * u * y⁻¹ = u) : False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := by omega
  have hq : Nat.Prime 5 := by norm_num
  have hq2 : (5 : ℕ) ≠ 2 := by norm_num
  have hq3 : 3 < 5 := by norm_num
  have : Fact (Nat.Prime 5) := ⟨hq⟩
  have hX : IsPGroup 5 X := IsPGroup.of_card (n := 1) (by rw [hXq, pow_one])
  obtain ⟨x, hXx⟩ : ∃ x : G, X = zpowers x := by
    have : IsCyclic X := isCyclic_of_prime_card hXq
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := X)
    refine ⟨g, le_antisymm (fun y hy => ?_) (zpowers_le.mpr g.2)⟩
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hg ⟨y, hy⟩)
    exact mem_zpowers_iff.mpr ⟨k, by
      have := congrArg Subtype.val hk
      simpa using this⟩
  have hxX : x ∈ X := hXx ▸ mem_zpowers x
  have hxq : x ^ 5 = 1 := by
    have h := pow_card_eq_one' (G := X) (x := ⟨x, hxX⟩)
    rw [hXq] at h
    have := congrArg Subtype.val h
    simpa using this
  obtain ⟨U₀, ⟨hU₀U, hcU₀, hU₀X, hU₀1⟩, hU₀min⟩ := (wellFounded_lt (α := Subgroup G)).has_min
    {V | V ≤ U ∧ c ∈ normalizer (V : Set G) ∧ ⁅V, X⁆ = V ∧ V ≠ ⊥} ⟨U, le_rfl, hcU, hUX, hU1⟩
  have hU₀2 : IsPGroup 2 U₀ := hU.to_le hU₀U
  have hCM : CMin X U₀ x c :=
    ⟨hXx, hXq, hU₀2, hU₀X, hU₀1, hcU₀, hc3, hcX x hxX,
      fun u hu hcu => hcfix u (hU₀U hu) hcu x hxX,
      fun V hV hcV hVX hV1 => by_contra fun hne =>
        hU₀min V ⟨hV.trans hU₀U, hcV, hVX, hV1⟩ (lt_of_le_of_ne hV hne)⟩
  have hmin : ∀ V ≤ U₀, ⁅V, X⁆ = V → V ≠ ⊥ → V = U₀ := hCM.min
  have hXU₀ : X ≤ normalizer (U₀ : Set G) := hCM.le_normalizer
  obtain ⟨D, hDP, hND, hDexp, hDcl, hDfaith⟩ := exists_critical_subgroup hp2 hP hU hUP hfaith hU1
  have hU₀D : U₀ ≤ normalizer (D : Set G) := (hU₀U.trans hUP).trans hND
  have hxD : x ∈ normalizer (D : Set G) := hND (hXP hxX)
  have hxU₀ : x ∈ normalizer (U₀ : Set G) := hXU₀ hxX
  have hfaith₀ : ∀ u ∈ U₀, u ∈ centralizer (D : Set G) → u = 1 := fun u hu hc => by
    have : u ∈ U ⊓ centralizer (D : Set G) := ⟨hU₀U hu, hc⟩
    rwa [hDfaith, mem_bot] at this
  have hfix₀ : ∀ D₀ : Subgroup G, ∀ u ∈ U₀, u ∉ centralizer (D₀ : Set G) →
      CFSG.Assembly.pRank p (P ⊓ centralizer ({u} : Set G)) ≤ 2 := fun D₀ u hu hc =>
    hfix u (hU₀U hu) (fun h => hc (h ▸ one_mem _))
  have hfpf : ∀ u ∈ U₀, x * u * x⁻¹ * u⁻¹ ∈ squares U₀ → u ∈ squares U₀ := fun u hu h =>
    mem_squares_of_conj_mul_inv_mem hq hq2 hXx hXq hU₀2 hXU₀ hU₀X hu h
  by_cases hab : ∀ a ∈ U₀, ∀ b ∈ U₀, a * b = b * a
  ·
    exfalso
    have hsq1 : ∀ u ∈ U₀, u ^ 2 = 1 := fun u hu =>
      sq_eq_one_of_commute hq hq2 hX hU₀2 hXU₀ hU₀X hU₀1 hmin hab hu
    have hF : squares U₀ = ⊥ := by
      rw [eq_bot_iff, squares, closure_le]
      rintro _ ⟨w, hw, rfl⟩
      rw [hsq1 w hw]
      exact one_mem _
    refine false_of_elemAbelian_section hp2 hq hq3 hP hDP hDexp hDcl hU₀D hxD hxU₀ hxq ?_ ?_ ?_
      ?_ (hfix₀ D)
    · intro a ha b hb
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (hab a ha b hb)]
      exact one_mem _
    · intro a ha
      rw [hsq1 a ha]
      exact one_mem _
    · by_contra h
      push Not at h
      apply hU₀1
      rw [eq_bot_iff]
      intro u hu
      rw [mem_bot]
      exact hfaith₀ u hu (h u hu)
    · intro u hu hc
      have hw : x * u * x⁻¹ * u⁻¹ ∈ U₀ :=
        mul_mem ((mem_normalizer_iff.mp hxU₀ u).mp hu) (inv_mem hu)
      have h2 := hfpf u hu (by rw [hfaith₀ _ hw hc]; exact one_mem _)
      rw [hF, mem_bot] at h2
      rw [h2]
      exact one_mem _
  ·
    set Z := squares U₀ with hZdef
    have hZU₀ : Z ≤ U₀ := squares_le U₀
    have hZc : ∀ z ∈ Z, ∀ v ∈ U₀, z * v = v * z := fun z hz v hv =>
      squares_commute hq hq2 hX hU₀2 hXU₀ hU₀X hU₀1 hmin hz hv
    have hUUZ : ⁅U₀, U₀⁆ = Z := commutator_eq_squares hq hq2 hX hU₀2 hXU₀ hU₀X hU₀1 hmin
    have hZ2 : ∀ z ∈ Z, z ^ 2 = 1 := fun z hz =>
      sq_eq_one_of_mem_squares hq hq2 hX hU₀2 hXU₀ hU₀X hU₀1 hmin hz
    have hZne : Z ≠ U₀ := squares_ne hU₀2 hU₀1
    have hxZ : ∀ z ∈ Z, x * z * x⁻¹ = z := fun z hz =>
      conj_eq_of_mem_squares hq hq2 hX hU₀2 hXU₀ hU₀1 hmin hxX hz
    have hZbot : Z ≠ ⊥ := fun h => hab fun a ha b hb => by
      have : ⁅a, b⁆ ∈ ⁅U₀, U₀⁆ := commutator_mem_commutator ha hb
      rwa [hUUZ, h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    obtain ⟨r, hr⟩ := (hU₀2.to_le hZU₀).exists_card_eq
    have hr1 : 1 ≤ r := by
      rcases Nat.eq_zero_or_pos r with h | h
      · rw [h, pow_zero, card_eq_one] at hr
        exact absurd hr hZbot
      · exact h
    have hZel : CFSG.Open.IsElemAbelian 2 Z :=
      ⟨⟨⟨fun a b => Subtype.ext (hZc a a.2 b (hZU₀ b.2))⟩⟩, hZ2⟩
    have hcopD : Nat.Coprime 2 (Nat.card D) := by
      obtain ⟨k, hk⟩ := (hP.to_le hDP).exists_card_eq
      rw [hk]
      exact Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm)
    have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2
      (r - 1) Nat.prime_two Z D hZel (by rw [hr, show r - 1 + 1 = r by omega])
      (hZU₀.trans hU₀D) hcopD
    obtain ⟨Z₀, ⟨hZ₀Z, hZ₀card⟩, hZ₀act⟩ : ∃ Z₀ ∈ CFSG.Open.signalizerFunctorEk 2 (r - 1) Z,
        ¬ U₀ ≤ centralizer ((D ⊓ centralizer (Z₀ : Set G) : Subgroup G) : Set G) := by
      by_contra h
      push Not at h
      apply hU₀1
      have hle : D ≤ centralizer (U₀ : Set G) := by
        rw [← hgen]
        exact iSup₂_le fun Z₀ hZ₀ => (le_centralizer_iff.mp (h Z₀ hZ₀))
      rw [eq_bot_iff]
      intro u hu
      rw [mem_bot]
      exact hfaith₀ u hu (le_centralizer_iff.mp hle hu)
    set D₀ := D ⊓ centralizer (Z₀ : Set G) with hD₀
    have hD₀P : D₀ ≤ P := inf_le_left.trans hDP
    have hU₀D₀ : U₀ ≤ normalizer (D₀ : Set G) := fun u hu =>
      mem_normalizer_inf (hU₀D hu) (mem_normalizer_centralizer (mem_normalizer_of_forall_commute
        fun z hz => (hZc z (hZ₀Z hz) u hu).symm))
    have hxD₀ : x ∈ normalizer (D₀ : Set G) :=
      mem_normalizer_inf hxD (mem_normalizer_centralizer (mem_normalizer_of_forall_commute
        fun z hz => by
          have := hxZ z (hZ₀Z hz)
          calc x * z = x * z * x⁻¹ * x := by group
            _ = z * x := by rw [this]))
    set K := U₀ ⊓ centralizer (D₀ : Set G) with hKdef
    have hKne : K ≠ U₀ := fun h => hZ₀act (h ▸ inf_le_right)
    have hXK : X ≤ normalizer (K : Set G) := by
      intro y hy
      have hyZ₀ : ∀ z ∈ Z₀, y * z = z * y := fun z hz => by
        have := conj_eq_of_mem_squares hq hq2 hX hU₀2 hXU₀ hU₀1 hmin hy (hZ₀Z hz)
        calc y * z = y * z * y⁻¹ * y := by group
          _ = z * y := by rw [this]
      exact mem_normalizer_inf (hXU₀ hy) (mem_normalizer_centralizer (mem_normalizer_inf
        (hND (hXP hy)) (mem_normalizer_centralizer (mem_normalizer_of_forall_commute hyZ₀))))
    have hKX := commutator_eq_bot_of_ne hq hq2 hX hU₀2 hmin inf_le_left hXK hKne
    have hKZ : K ≤ Z := fun k hk => hfpf k hk.1 (by
      have : ⁅k, x⁆ ∈ ⁅K, X⁆ := commutator_mem_commutator hk hxX
      rw [hKX, mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      rw [← this, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _)
    have hZ₀K : Z₀ ≤ K := fun z hz => ⟨hZU₀ (hZ₀Z hz), mem_centralizer_iff.mpr fun d hd =>
      (mem_centralizer_iff.mp hd.2 z hz).symm⟩
    have hKcard : Nat.card K = 2 ^ (r - 1) ∨ Nat.card K = 2 ^ r := by
      have h1 : Nat.card Z₀ ∣ Nat.card K := card_dvd_of_le hZ₀K
      have h2 : Nat.card K ∣ Nat.card Z := card_dvd_of_le hKZ
      rw [hZ₀card] at h1
      rw [hr] at h2
      obtain ⟨j, hj, hjK⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
      rw [hjK] at h1
      have : r - 1 ≤ j := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h1
      rcases (show j = r - 1 ∨ j = r by omega) with h | h
      · left
        rw [hjK, h]
      · right
        rw [hjK, h]
    rcases hKcard with hK1 | hK2
    ·
      have hKZ₀ : K = Z₀ := (eq_of_le_of_card_ge hZ₀K (by rw [hK1, hZ₀card])).symm
      have hZ₀ne : Z₀ ≠ Z := fun h => by
        have := congrArg (fun H : Subgroup G => Nat.card H) h
        simp only [hZ₀card, hr] at this
        have := Nat.pow_right_injective (le_refl 2) this
        omega
      have hcomm₀ : ∀ a ∈ U₀, ∀ b ∈ U₀, ⁅a, b⁆ ∈ Z := fun a ha b hb =>
        hUUZ ▸ commutator_mem_commutator ha hb
      have hZab : ∀ z ∈ Z, z * z = 1 := fun z hz => by rw [← pow_two]; exact hZ2 z hz
      have hx2Z : ∀ z ∈ Z, x ^ 2 * z * (x ^ 2)⁻¹ = z := fun z hz => by
        have e : x ^ 2 * z * (x ^ 2)⁻¹ = x * (x * z * x⁻¹) * x⁻¹ := by
          rw [sq, mul_inv_rev]
          group
        rw [e, hxZ z hz, hxZ z hz]
      have hcf : ∀ u ∈ U₀, c * u * c⁻¹ * u⁻¹ ∈ Z → u ∈ Z := fun _ hu h =>
        hCM.mem_squares_of_c hu h
      have cfix : ∀ φ ∈ Z, c * φ * c⁻¹ = φ → φ = 1 := by
        intro φ hφ hφc
        have hφ' : φ ∈ ⁅U₀, U₀⁆ := hUUZ ▸ hφ
        rcases hCM.omega_or with hω | hω
        · exact ResGapFive.Pair.eq_one_of_fixed hZU₀ hcomm₀ hZc hZab hxU₀ hcU₀ hxZ hω hc3 hcf
            hφ' hφc
        · exact ResGapFive.Pair.eq_one_of_fixed hZU₀ hcomm₀ hZc hZab (pow_mem hxU₀ 2) hcU₀
            hx2Z hω hc3 hcf hφ' hφc
      have hZ4 : Nat.card Z ≠ 2 := by
        intro hZcard
        obtain ⟨⟨z, hzZ⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZbot
        have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
        have hczZ : c * z * c⁻¹ ∈ Z :=
          (mem_normalizer_iff.mp hCM.c_mem_normalizer_squares z).mp hzZ
        have hcz1 : c * z * c⁻¹ ≠ 1 := fun h => hz1' (by
          have e : z = c⁻¹ * (c * z * c⁻¹) * c := by group
          rw [e, h]
          group)
        exact hz1' (cfix z hzZ (eq_of_card_two hZcard hczZ hzZ hcz1 hz1'))
      obtain ⟨z', hz'Z₀, hz'1⟩ : ∃ z' ∈ Z₀, z' ≠ 1 := by
        have hZ₀bot : Z₀ ≠ ⊥ := by
          intro hbot
          rw [hbot, Subgroup.card_bot] at hZ₀card
          have h0 : r - 1 = 0 := Nat.pow_right_injective (le_refl 2)
            (show 2 ^ (r - 1) = 2 ^ 0 by rw [← hZ₀card, pow_zero])
          exact hZ4 (by rw [hr, show r = 1 by omega, pow_one])
        obtain ⟨⟨z', hz'⟩, hz'1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZ₀bot
        exact ⟨z', hz', fun h => hz'1 (Subtype.ext h)⟩
      have hz'K := hZ₀K hz'Z₀
      refine false_of_extraspecial_section hp2 hq hq3 hp3 hP hD₀P (fun d hd => hDexp d hd.1)
        (fun a ha b hb c hc => hDcl a ha.1 b hb.1 c hc.1) hU₀D₀ hxD₀ hxU₀ hxq hU₀2 hZU₀ hZc hUUZ
        (fun u hu => sq_mem_squares hu) hZne.symm hKZ ?_ ?_ hfpf (hfix₀ D₀) hZ2 hz'K.2
        (hfix z' (hU₀U hz'K.1) hz'1)
      · rw [hr, hK1, ← pow_succ']
        congr 1
        omega
      · intro u hu hc
        apply mem_squares_of_commutator_mem hq hq2 hXx hXq hX hU₀2 hXU₀ hU₀X hU₀1 hmin hZ₀Z hZ₀ne
          hu
        intro v hv
        have : ⁅u, v⁆ ∈ K :=
          ⟨le_normalizer_iff_commutator_le_left.mp le_normalizer
            (commutator_mem_commutator hu hv), hc v hv⟩
        rwa [hKZ₀] at this
    ·
      exfalso
      have hKZeq : K = Z := eq_of_le_of_card_ge hKZ (by rw [hK2, hr])
      refine false_of_elemAbelian_section hp2 hq hq3 hP hD₀P (fun d hd => hDexp d hd.1)
        (fun a ha b hb c hc => hDcl a ha.1 b hb.1 c hc.1) hU₀D₀ hxD₀ hxU₀ hxq ?_ ?_ ?_ ?_
        (hfix₀ D₀)
      · intro a ha b hb
        have : ⁅a, b⁆ ∈ K := by
          rw [hKZeq, ← hUUZ]
          exact commutator_mem_commutator ha hb
        exact this.2
      · intro a ha
        have : a ^ 2 ∈ K := by
          rw [hKZeq]
          exact sq_mem_squares ha
        exact this.2
      · by_contra h
        push Not at h
        exact hZ₀act fun u hu => h u hu
      · intro u hu hc
        have hw : x * u * x⁻¹ * u⁻¹ ∈ K := Subgroup.mem_inf.mpr
          ⟨mul_mem ((mem_normalizer_iff.mp hxU₀ u).mp hu) (inv_mem hu), hc⟩
        rw [hKZeq] at hw
        have := hfpf u hu hw
        rw [← hKZeq] at this
        exact this.2

end CFSG.RankThree.PartTwo.Sec16.ResGapFive

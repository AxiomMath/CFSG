module

public import CFSG.Quasithin.H13.NQBlockCcommSelf
public import CFSG.Quasithin.H13.NQBlockCcomponentQuotient
public import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerBin

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.SectionRank.Ccomm
open scoped commutatorElement

theorem quotient_two_core_setup {L : Type*} [Group L] [Finite L]
    (hSQT : CFSG.IsStronglyQuasithin L) (hLC : CFSG.IsCComponent (⊤ : Subgroup L)) :
    CFSG.IsStronglyQuasithin (L ⧸ CFSG.pCore 2 L) ∧ CFSG.pCore 2 (L ⧸ CFSG.pCore 2 L) = ⊥ ∧
      CFSG.IsCComponent (⊤ : Subgroup (L ⧸ CFSG.pCore 2 L)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : IsPGroup 2 (CFSG.pCore 2 L) := CFSG.pCore_isPGroup
  have hNs : Group.IsSolvable (CFSG.pCore 2 L) := by
    have := hN.isNilpotent
    infer_instance
  refine ⟨fun r hr hr2 => ?_, CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot, ?_⟩
  · have : Fact r.Prime := ⟨hr⟩
    have hndvd : ¬ r ∣ Nat.card (CFSG.pCore 2 L) := by
      intro h
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hN
      rw [hk] at h
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h))
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_quotient_eq _ hndvd,
      ← CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact hSQT r hr hr2
  · have h := Ccomponent_solvable_quotient_image (CFSG.pCore 2 L) hNs hLC
    rwa [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h

theorem map_frattini_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    (frattini G).map (e : G →* H) = frattini H := by
  apply le_antisymm
  · rw [map_le_iff_le_comap]
    exact frattini_le_comap_frattini_of_surjective e.surjective
  · intro x hx
    have h1 := frattini_le_comap_frattini_of_surjective (φ := e.symm.toMonoidHom) e.symm.surjective
      hx
    exact ⟨e.symm x, h1, by simp⟩

@[expose] noncomputable def residualAction {L : Type*} [Group L] (X : Subgroup L)
    [X.Characteristic] :
    L →* MulAut ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) :=
  (autQuotient (frattini (X ⧸ CFSG.pCore 2 X))).comp
    ((autQuotient (CFSG.pCore 2 X)).comp MulAut.conjNormal)

theorem residualAction_mk {L : Type*} [Group L] (X : Subgroup L) [X.Characteristic] (l : L)
    (x : X) :
    residualAction X l (((x : X ⧸ CFSG.pCore 2 X)) : (X ⧸ CFSG.pCore 2 X) ⧸
      frattini (X ⧸ CFSG.pCore 2 X)) =
      ((((MulAut.conjNormal l x : X) : X ⧸ CFSG.pCore 2 X)) : (X ⧸ CFSG.pCore 2 X) ⧸
        frattini (X ⧸ CFSG.pCore 2 X)) :=
  rfl

theorem exists_odd_pow_map_eq {G K : Type*} [Group G] [Finite G] [Group K] (π : G →* K) (e : G)
    (hodd : Odd (orderOf (π e))) : ∃ k : ℕ, Odd (orderOf (e ^ k)) ∧ π (e ^ k) = π e := by
  set a := (orderOf e).factorization 2 with ha
  have hpos : 0 < orderOf e := orderOf_pos e
  have hdvd : 2 ^ a ∣ orderOf e := Nat.ordProj_dvd _ _
  have hcop : Nat.Coprime (2 ^ a) (orderOf (π e)) :=
    Nat.Coprime.pow_left a (Nat.coprime_comm.mp (Odd.coprime_two_right hodd))
  obtain ⟨u, hu⟩ := exists_pow_eq_self_of_coprime hcop
  refine ⟨2 ^ a * u, ?_, ?_⟩
  · have h1 : orderOf (e ^ 2 ^ a) = orderOf e / 2 ^ a :=
      orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) hdvd
    have h2 : Odd (orderOf e / 2 ^ a) := by
      have h3 := Nat.coprime_ordCompl Nat.prime_two hpos.ne'
      rw [← ha] at h3
      exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp ((Nat.Prime.coprime_iff_not_dvd
        Nat.prime_two).mp h3))
    rw [pow_mul]
    exact Odd.of_dvd_nat (h1 ▸ h2) (orderOf_pow_dvd u)
  · rw [map_pow, pow_mul, hu]

theorem nq_characteristic_radical_odd_residual_witness
    {L : Type*} [Group L] [Finite L]
    (hSQT : CFSG.IsStronglyQuasithin L) (hLC : CFSG.IsCComponent (⊤ : Subgroup L))
    (hq : ¬ CFSG.IsQuasisimple (L ⧸ CFSG.pCore 2 L)) :
    ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ ∃ D : Subgroup (L ⧸ CFSG.pCore 2 L), D.Characteristic ∧
      D ≤ CFSG.pCore p (L ⧸ CFSG.pCore 2 L) ∧
      ((IsElementaryAbelian p D ∧ Nat.card D = p ^ 2) ∨
        (¬ IsMulCommutative D ∧ Nat.card D = p ^ 3 ∧ ∀ x ∈ D, x ^ p = 1)) ∧
      ∀ E X : Subgroup L, E = D.comap (QuotientGroup.mk' (CFSG.pCore 2 L)) →
        X = closure {x | x ∈ E ∧ Odd (orderOf x)} →
        E.Characteristic ∧ ∃ _ : X.Characteristic, X ≤ CFSG.solvableRadical L ∧
          CFSG.QuasithinUnique.Setup.Campbell.NoPQuotient 2 X ∧
          X.map (QuotientGroup.mk' (CFSG.pCore 2 L)) = D ∧
          ((QuotientGroup.mk' (CFSG.pCore 2 L)).comp X.subtype).ker = CFSG.pCore 2 X ∧
          Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p ∧ CFSG.pRank p (X ⧸ CFSG.pCore 2 X) = 2 ∧
          Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2 ∧
          residualAction X ≠ 1 ∧
          ∀ U : Subgroup ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)),
            Nat.card U = p → ∃ l : L, ∃ u ∈ U, residualAction X l u ∉ U := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := CFSG.pCore 2 L with hNdef
  set π := QuotientGroup.mk' N with hπ
  obtain ⟨hSQT', hO2', hLC'⟩ := quotient_two_core_setup hSQT hLC
  obtain ⟨-, hFne, hodd, hCF, hcomm, hcores⟩ := odd_Fitting_cores_self hSQT' hO2' hLC' hq
  obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.mpr ((one_lt_card_iff_ne_bot _).mpr hFne)
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have : Fact p.Prime := ⟨hpp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors hp))
  obtain ⟨-, hcrit⟩ := all_prime_critical_actions_core hLC' hCF hodd hcomm hcores
  set Q := CFSG.pCore p (L ⧸ N) with hQ
  obtain ⟨-, A, hAc, hA, -⟩ := hcrit p hp
  set D := A.map Q.subtype with hD
  set eAD : A ≃* D := A.equivMapOfInjective Q.subtype Q.subtype_injective with heAD
  have heAD' : ∀ d : D, (((eAD.symm d : A) : Q) : L ⧸ N) = d := fun d => by
    conv_rhs => rw [← eAD.apply_symm_apply d]
    rfl
  have hDp : IsPGroup p D := (CFSG.pCore_isPGroup : IsPGroup p Q).to_le (map_subtype_le A)
  have hcardD : Nat.card D = Nat.card A := (Nat.card_congr eAD.toEquiv).symm
  have hDshape : (IsElementaryAbelian p D ∧ Nat.card D = p ^ 2) ∨
      (¬ IsMulCommutative D ∧ Nat.card D = p ^ 3 ∧ ∀ x ∈ D, x ^ p = 1) := by
    rcases hA.shape with ⟨hel, hc⟩ | ⟨hnc, hc, -, -⟩
    · left
      have := hel
      exact ⟨CFSG.QuasithinUnique.Setup.Layer.isElementaryAbelian_map Q.subtype A,
        hcardD.trans hc⟩
    · right
      refine ⟨fun hDc => hnc ⟨⟨fun a b => eAD.injective ?_⟩⟩, hcardD.trans hc, ?_⟩
      · rw [map_mul, map_mul]
        exact hDc.is_comm.comm _ _
      · rintro _ ⟨x, hx, rfl⟩
        rw [← map_pow, hA.pow_eq_one x hx, map_one]
  refine ⟨p, hpp, hA.five_le, D, inferInstance, map_subtype_le _, hDshape, ?_⟩
  intro E X hE hX
  have hEmem : ∀ y : L, y ∈ E ↔ π y ∈ D := fun y => by rw [hE, mem_comap]
  have hEchar : E.Characteristic := by
    rw [characteristic_iff_le_comap]
    intro σ x hx
    rw [mem_comap, MulEquiv.coe_toMonoidHom, hEmem]
    have h1 := (characteristic_iff_le_comap.mp (inferInstance : D.Characteristic)
      (autQuotient N σ)) ((hEmem x).mp hx)
    exact h1
  have hNE : N ≤ E := fun n hn => by
    rw [hEmem, hπ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff n).mpr hn]
    exact one_mem _
  have hEsolv : Group.IsSolvable E := by
    have : Group.IsSolvable N := by
      have := (CFSG.pCore_isPGroup : IsPGroup 2 N).isNilpotent
      infer_instance
    have : Group.IsSolvable D := by
      have := hDp.isNilpotent
      infer_instance
    let g : E →* D := (π.comp E.subtype).codRestrict D fun x => (hEmem x).mp x.2
    refine Group.isSolvable_of_ker_le_range (inclusion hNE) g fun x hx => ?_
    have hx' : (x : L) ∈ N := by
      have h1 : g x = 1 := hx
      have h2 : π x = 1 := congrArg Subtype.val h1
      rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    exact ⟨⟨x, hx'⟩, rfl⟩
  obtain ⟨-, -, hRmax, -⟩ :=
    CFSG.QuasithinUnique.Setup.Offender.solvableRadical_characterization L
  have hERad : E ≤ CFSG.solvableRadical L := hRmax E inferInstance hEsolv
  have hXE : X ≤ E := by
    rw [hX, closure_le]
    exact fun x hx => hx.1
  have hXchar : X.Characteristic := by
    rw [characteristic_iff_le_comap]
    intro σ
    rw [hX, closure_le]
    rintro x ⟨hxE, hxo⟩
    rw [SetLike.mem_coe, mem_comap, MulEquiv.coe_toMonoidHom]
    refine subset_closure ⟨(characteristic_iff_le_comap.mp hEchar σ) hxE, ?_⟩
    have h1 : orderOf (σ x) = orderOf x := orderOf_injective σ.toMonoidHom σ.injective x
    rw [h1]
    exact hxo
  refine ⟨hEchar, hXchar, hXE.trans hERad, ?_⟩
  have hgenX : ∀ x : L, x ∈ E → Odd (orderOf x) → x ∈ X := fun x hxE hxo => by
    rw [hX]
    exact subset_closure ⟨hxE, hxo⟩
  have hnoq : CFSG.QuasithinUnique.Setup.Campbell.NoPQuotient 2 X := by
    intro K _ hK2
    have hgen : ∀ x : L, ∀ (hxE : x ∈ E) (hxo : Odd (orderOf x)),
        (⟨x, hgenX x hxE hxo⟩ : X) ∈ K := by
      intro x hxE hxo
      obtain ⟨k, hk⟩ := hK2 ((⟨x, hgenX x hxE hxo⟩ : X) : X ⧸ K)
      have h1 := orderOf_dvd_of_pow_eq_one hk
      have h2 : orderOf ((⟨x, hgenX x hxE hxo⟩ : X) : X ⧸ K) ∣ orderOf x := by
        have := orderOf_map_dvd (QuotientGroup.mk' K) (⟨x, hgenX x hxE hxo⟩ : X)
        rwa [Subgroup.orderOf_mk] at this
      have hcop : Nat.Coprime (orderOf x) (2 ^ k) :=
        Nat.Coprime.pow_right k (Odd.coprime_two_right hxo)
      have h3 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2 hcop) h1
      rwa [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
    rw [eq_top_iff]
    intro y _
    have hy : (y : L) ∈ K.map X.subtype := by
      have hle : X ≤ K.map X.subtype := by
        conv_lhs => rw [hX]
        rw [closure_le]
        rintro x ⟨hxE, hxo⟩
        exact ⟨⟨x, hgenX x hxE hxo⟩, hgen x hxE hxo, rfl⟩
      exact hle y.2
    obtain ⟨k, hk, hky⟩ := hy
    rwa [← Subtype.ext hky]
  refine ⟨hnoq, ?_⟩
  have hπX : X.map π = D := by
    refine le_antisymm ((map_le_iff_le_comap).mpr (hE ▸ hXE)) fun d hd => ?_
    obtain ⟨e, rfl⟩ := QuotientGroup.mk'_surjective N d
    have heE : e ∈ E := by
      rw [hE, mem_comap]
      exact hd
    have hodd' : Odd (orderOf (π e)) := by
      obtain ⟨k, hk⟩ := hDp ⟨π e, hd⟩
      have h1 : orderOf (π e) ∣ p ^ k := by
        rw [← Subgroup.orderOf_mk (π e) hd]
        exact orderOf_dvd_of_pow_eq_one hk
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hpp).mp h1
      rw [hj]
      exact (hpp.odd_of_ne_two hp2).pow
    obtain ⟨k, hko, hkπ⟩ := exists_odd_pow_map_eq π e hodd'
    exact ⟨e ^ k, hgenX _ (pow_mem heE k) hko, hkπ⟩
  refine ⟨hπX, ?_⟩
  have hker2 : (π.comp X.subtype).ker = CFSG.pCore 2 X := by
    apply le_antisymm
    · apply le_sSup
      refine ⟨inferInstance, ?_⟩
      have h1 : IsPGroup 2 ((π.comp X.subtype).ker.map X.subtype) := by
        refine (CFSG.pCore_isPGroup : IsPGroup 2 N).to_le ?_
        rintro _ ⟨x, hx, rfl⟩
        have h2 : π x = 1 := hx
        rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
      exact h1.of_equiv ((π.comp X.subtype).ker.equivMapOfInjective X.subtype
        X.subtype_injective).symm
    · intro y hy
      have h1 : (CFSG.pCore 2 X).map X.subtype ≤ N := by
        apply le_sSup
        refine ⟨inferInstance, CFSG.pCore_isPGroup.map _⟩
      have h2 : (y : L) ∈ N := h1 ⟨y, hy, rfl⟩
      change π y = 1
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact h2
  refine ⟨hker2, ?_⟩
  let ψ : X →* D := (π.comp X.subtype).codRestrict D fun x => by
    rw [← hπX]
    exact ⟨x, x.2, rfl⟩
  have hψs : Function.Surjective ψ := by
    rintro ⟨d, hd⟩
    rw [← hπX] at hd
    obtain ⟨x, hx, rfl⟩ := hd
    exact ⟨⟨x, hx⟩, rfl⟩
  have hψker : ψ.ker = CFSG.pCore 2 X := (MonoidHom.ker_codRestrict _ _ _).trans hker2
  set φ : X ⧸ CFSG.pCore 2 X ≃* A :=
    ((QuotientGroup.quotientMulEquivOfEq hψker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)).trans eAD.symm with hφ
  have hφmk : ∀ x : X, (((φ (x : X ⧸ CFSG.pCore 2 X) : A) : Q) : L ⧸ N) = π x := fun x =>
    heAD' (ψ x)
  have hAnt : Nontrivial A := (nontrivial_iff_ne_bot A).mpr hA.ne_bot
  have : Nontrivial (X ⧸ CFSG.pCore 2 X) := φ.toEquiv.nontrivial
  have hexp : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p := by
    rw [Monoid.exponent_eq_prime_iff hpp]
    intro g hg
    rw [← orderOf_injective φ.toMonoidHom φ.injective g]
    refine orderOf_eq_prime ?_ ?_
    · exact Subtype.ext (by
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
        exact hA.pow_eq_one _ (φ g).2)
    · intro h1
      exact hg (φ.injective (h1.trans (map_one φ).symm))
  have hrankA : CFSG.pRank p A = 2 := by
    apply le_antisymm
    · have h1 : CFSG.pRank p A ≤ CFSG.pRank p Q := by
        rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_open_pRank_top]
        exact CFSG.SectionRank.pRank_top_le_of_injective hpp.one_lt A.subtype A.subtype_injective
      exact h1.trans (hcores p hp).2
    · rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
      rcases hA.shape with ⟨hel, hc⟩ | ⟨hnc, hc, -, -⟩
      · have : CFSG.IsElementaryAbelian p A := hel
        refine CFSG.SectionRank.le_pRank (E := ⊤) hpp.one_lt (le_refl (⊤ : Subgroup A)) ?_ ?_
        · refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x _ => ?_⟩
          · exact hel.toIsMulCommutative.is_comm.comm (a : A) b
          · exact Subtype.ext (by
              rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
              exact hA.pow_eq_one _ x.2)
        · rw [card_top, hc]
      · obtain ⟨T, hT⟩ := Sylow.exists_subgroup_card_pow_prime p (n := 2)
          (show p ^ 2 ∣ Nat.card A by rw [hc]; exact pow_dvd_pow p (by norm_num))
        have hnc' : ∃ a b : A, a * b ≠ b * a := by
          by_contra h
          push Not at h
          exact hnc ⟨⟨h⟩⟩
        obtain ⟨-, -, -, -, -, hTs, -⟩ := nonabelian_prime_cube_central_structure hc hnc'
        obtain ⟨-, -, hTc, -⟩ := hTs T hT
        refine CFSG.SectionRank.le_pRank (E := T) hpp.one_lt le_top
          ⟨⟨⟨fun a b => Subtype.ext (hTc a a.2 b b.2)⟩⟩, fun x _ => Subtype.ext (by
            rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
            exact hA.pow_eq_one _ x.2)⟩ hT
  have hrank : CFSG.pRank p (X ⧸ CFSG.pCore 2 X) = 2 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_top_eq_of_mulEquiv
      hpp.one_lt φ, ← CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact hrankA
  refine ⟨hexp, hrank, ?_⟩
  set θ : (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X) ≃* A ⧸ frattini A :=
    QuotientGroup.congr _ _ φ (map_frattini_mulEquiv φ) with hθ
  have hθeq : ∀ (l : L) (w : (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)),
      θ (residualAction X l w) = criticalAction A (π l) (θ w) := by
    intro l w
    induction w using QuotientGroup.induction_on with
    | H w =>
      induction w using QuotientGroup.induction_on with
      | H x =>
        rw [residualAction_mk, hθ, QuotientGroup.congr_mk, QuotientGroup.congr_mk]
        change ((φ ((MulAut.conjNormal l x : X) : X ⧸ CFSG.pCore 2 X) : A) : A ⧸ frattini A) =
          frattiniAction A (MulAut.conjNormal (π l)) ((φ (x : X ⧸ CFSG.pCore 2 X) : A) :
            A ⧸ frattini A)
        rw [frattiniAction_mk]
        congr 1
        apply Subtype.ext
        apply Subtype.ext
        rw [hφmk]
        change π (l * x * l⁻¹) = π l * (((φ (x : X ⧸ CFSG.pCore 2 X) : A) : Q) : L ⧸ N) *
          (π l)⁻¹
        rw [hφmk, map_mul, map_mul, map_inv]
  have hcardW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2 := by
    rw [Nat.card_congr θ.toEquiv, hA.card_quotient]
  refine ⟨hcardW, ?_, ?_⟩
  ·
    intro h1
    apply hA.range_ne_bot
    rw [eq_bot_iff]
    rintro _ ⟨m, rfl⟩
    rw [mem_bot]
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective N m
    ext w
    obtain ⟨w', rfl⟩ := θ.surjective w
    rw [MulAut.one_apply]
    change criticalAction A (π l) (θ w') = θ w'
    rw [← hθeq, h1, MonoidHom.one_apply, MulAut.one_apply]
  ·
    intro U hU
    by_contra hcon
    push Not at hcon
    obtain ⟨g, ⟨m, rfl⟩, u', hu', hgu⟩ := hA.irreducible (U.map θ.toMonoidHom)
      (by rw [card_map_of_injective (f := θ.toMonoidHom) θ.injective, hU])
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective N m
    obtain ⟨u, hu, rfl⟩ := hu'
    apply hgu
    refine ⟨residualAction X l u, hcon l u hu, ?_⟩
    change θ (residualAction X l u) = criticalAction A (π l) (θ u)
    exact hθeq l u

theorem ker_mk_comp_subtype_eq_pCore {L : Type*} [Group L] [Finite L] (X : Subgroup L)
    [X.Normal] :
    ((QuotientGroup.mk' (CFSG.pCore 2 L)).comp X.subtype).ker = CFSG.pCore 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · apply le_sSup
    refine ⟨inferInstance, ?_⟩
    have h1 : IsPGroup 2
        (((QuotientGroup.mk' (CFSG.pCore 2 L)).comp X.subtype).ker.map X.subtype) := by
      refine (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 L)).to_le ?_
      rintro _ ⟨x, hx, rfl⟩
      have h2 : QuotientGroup.mk' (CFSG.pCore 2 L) (x : L) = 1 := hx
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    exact h1.of_equiv
      ((((QuotientGroup.mk' (CFSG.pCore 2 L)).comp X.subtype).ker).equivMapOfInjective
        X.subtype X.subtype_injective).symm
  · intro y hy
    have h1 : (CFSG.pCore 2 X).map X.subtype ≤ CFSG.pCore 2 L := by
      apply le_sSup
      refine ⟨⟨fun n hn g => ?_⟩, CFSG.pCore_isPGroup.map _⟩
      have h3 := LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (CFSG.pCore 2 X) (show g ∈ normalizer (X : Set L) by
          rw [normalizer_eq_top_iff.mpr inferInstance]
          exact mem_top g)
      exact (mem_normalizer_iff.mp h3 n).mp hn
    change QuotientGroup.mk' (CFSG.pCore 2 L) (y : L) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact h1 ⟨y, hy, rfl⟩

theorem residual_equiv {L : Type*} [Group L] [Finite L] (X : Subgroup L) [X.Characteristic] :
    ∃ (_ : (X.map (QuotientGroup.mk' (CFSG.pCore 2 L))).Normal)
      (φ : X ⧸ CFSG.pCore 2 X ≃* X.map (QuotientGroup.mk' (CFSG.pCore 2 L)))
      (θ : (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X) ≃*
        X.map (QuotientGroup.mk' (CFSG.pCore 2 L)) ⧸
          frattini (X.map (QuotientGroup.mk' (CFSG.pCore 2 L)))),
      (∀ x : X, (φ (x : X ⧸ CFSG.pCore 2 X) : L ⧸ CFSG.pCore 2 L) =
        QuotientGroup.mk' (CFSG.pCore 2 L) (x : L)) ∧
      ∀ (l : L) (w : (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)),
        θ (residualAction X l w) = wholeFrattiniAction (X.map (QuotientGroup.mk' (CFSG.pCore 2 L)))
          (QuotientGroup.mk' (CFSG.pCore 2 L) l) (θ w) := by
  classical
  set π := QuotientGroup.mk' (CFSG.pCore 2 L) with hπ
  have hDn : (X.map π).Normal := (inferInstance : X.Normal).map π (QuotientGroup.mk'_surjective _)
  let ψ : X →* X.map π := (π.comp X.subtype).codRestrict (X.map π) fun x => ⟨x, x.2, rfl⟩
  have hψs : Function.Surjective ψ := by
    rintro ⟨d, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hψker : ψ.ker = CFSG.pCore 2 X :=
    (MonoidHom.ker_codRestrict _ _ _).trans (ker_mk_comp_subtype_eq_pCore X)
  set φ : X ⧸ CFSG.pCore 2 X ≃* X.map π :=
    (QuotientGroup.quotientMulEquivOfEq hψker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs) with hφ
  have hφmk : ∀ x : X, (φ (x : X ⧸ CFSG.pCore 2 X) : L ⧸ CFSG.pCore 2 L) = π x := fun _ => rfl
  set θ := QuotientGroup.congr _ _ φ (map_frattini_mulEquiv φ) with hθ
  refine ⟨hDn, φ, θ, hφmk, fun l w => ?_⟩
  induction w using QuotientGroup.induction_on with
  | H w =>
    induction w using QuotientGroup.induction_on with
    | H x =>
      rw [residualAction_mk, hθ, QuotientGroup.congr_mk, QuotientGroup.congr_mk]
      change ((φ ((MulAut.conjNormal l x : X) : X ⧸ CFSG.pCore 2 X) : X.map π) :
          X.map π ⧸ frattini (X.map π)) =
        autQuotient (frattini (X.map π)) (MulAut.conjNormal (π l))
          ((φ (x : X ⧸ CFSG.pCore 2 X) : X.map π) : X.map π ⧸ frattini (X.map π))
      rw [autQuotient_mk]
      congr 1

end CFSG.Quasithin.H13.NQBlock

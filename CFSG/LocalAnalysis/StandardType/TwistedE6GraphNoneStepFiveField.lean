module

public import CFSG.LocalAnalysis.StandardType.TwistedE6GraphNoneStepFive

public section

namespace CFSG.StandardType.E6GraphNoneSteps

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.HardMathSupport.Lang.AnisoE6 CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.RankThree.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeF4Close
  CFSG.StandardType.E6GraphNoneSteps


private lemma twE6_step5_baseChange_fixed {K L : Type} [Field K] [Field L] [Algebra K L]
    {σ : K →+* K} {θ : L →+* L} (hσθ : ∀ c, algebraMap K L (σ c) = θ (algebraMap K L c))
    (E : Subgroup (ModGL TwistTag.E6.tag K))
    (hEC : E ≤ graphFixedRootGroup TwistTag.E6 K σ)
    (hEP : ∀ x ∈ E, diagramMap TwistTag.E6 K * x = x * diagramMap TwistTag.E6 K)
    {x : ModGL TwistTag.E6.tag K} (hx : x ∈ E) :
    baseChangeGL (algebraMap K L) x ∈ twistedFixedGroup TwistTag.E6 L θ ∧
      diagramMap TwistTag.E6 L * baseChangeGL (algebraMap K L) x =
        baseChangeGL (algebraMap K L) x * diagramMap TwistTag.E6 L ∧
      Units.map (entrywiseHom θ) (baseChangeGL (algebraMap K L) x) =
        baseChangeGL (algebraMap K L) x := by
  have hxR : baseChangeGL (algebraMap K L) x ∈ twistedFixedGroup TwistTag.E6 L θ :=
    CFSG.StandardType.TableBExcSmallRanks.baseChangeGL_mem_twistedFixedGroup TwistTag.E6
      (algebraMap K L) σ θ hσθ (graphFixedRootGroup_le TwistTag.E6 K σ (hEC hx))
  have hxPL : diagramMap TwistTag.E6 L * baseChangeGL (algebraMap K L) x =
      baseChangeGL (algebraMap K L) x * diagramMap TwistTag.E6 L := by
    rw [← baseChangeGL_diagramMap (algebraMap K L) TwistTag.E6, ← map_mul, ← map_mul,
      hEP x hx]
  refine ⟨hxR, hxPL, ?_⟩
  have h := ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 L θ).1 hxR).2
  rw [twistHom_apply] at h
  have h' : diagramMap TwistTag.E6 L *
        Units.map (entrywiseHom θ) (baseChangeGL (algebraMap K L) x) =
      diagramMap TwistTag.E6 L * baseChangeGL (algebraMap K L) x := by
    rw [hxPL]
    exact (eq_mul_inv_iff_mul_eq.1 h.symm).symm
  exact mul_left_cancel h'

private noncomputable def twE6_step5_f4Component {K L : Type} [Field K] [Field L] [Algebra K L]
    (E : Subgroup (ModGL TwistTag.E6.tag K))
    (hΓ : ∀ x ∈ E, baseChangeGL (algebraMap K L) x ∈
      twistedFixedGroup TwistTag.E6 L (RingHom.id L)) : E →* ModGL Tag.F4 L :=
  (adjointGroup Tag.F4 L).subtype.comp ((e6FixedF4EquivAll L).toMonoidHom.comp
    (((baseChangeGL (algebraMap K L)).comp E.subtype).codRestrict
      (twistedFixedGroup TwistTag.E6 L (RingHom.id L)) fun x => hΓ x x.2))

private lemma twE6_step5_f4Component_injective {K L : Type} [Field K] [Field L] [Algebra K L]
    (E : Subgroup (ModGL TwistTag.E6.tag K))
    (hΓ : ∀ x ∈ E, baseChangeGL (algebraMap K L) x ∈
      twistedFixedGroup TwistTag.E6 L (RingHom.id L)) :
    Function.Injective (twE6_step5_f4Component E hΓ) := by
  intro x y h
  have h1 := (e6FixedF4EquivAll L).injective (Subtype.ext h)
  exact Subtype.ext (baseChangeGL_injective (algebraMap K L) (congrArg Subtype.val h1))

private lemma twE6_step5_f4Component_mem {K L : Type} [Field K] [Field L] [Algebra K L]
    (E : Subgroup (ModGL TwistTag.E6.tag K))
    (hΓ : ∀ x ∈ E, baseChangeGL (algebraMap K L) x ∈
      twistedFixedGroup TwistTag.E6 L (RingHom.id L)) (x : E) :
    twE6_step5_f4Component E hΓ x ∈ adjointGroup Tag.F4 L :=
  ((e6FixedF4EquivAll L) ⟨baseChangeGL (algebraMap K L) (x : ModGL TwistTag.E6.tag K),
    hΓ x x.2⟩).2

private lemma twE6_step5_f4Component_fixed {K L : Type} [Field K] [Field L] [Algebra K L]
    (E : Subgroup (ModGL TwistTag.E6.tag K))
    (hΓ : ∀ x ∈ E, baseChangeGL (algebraMap K L) x ∈
      twistedFixedGroup TwistTag.E6 L (RingHom.id L))
    {θ : L →+* L} (hθ : ∀ x ∈ E,
      Units.map (entrywiseHom θ) (baseChangeGL (algebraMap K L) x) =
        baseChangeGL (algebraMap K L) x) :
    ∀ x : E, Units.map (entrywiseHom θ) (twE6_step5_f4Component E hΓ x) =
      twE6_step5_f4Component E hΓ x := by
  intro x
  change Units.map (entrywiseHom θ) (((e6FixedF4EquivAll L)
    ⟨baseChangeGL (algebraMap K L) (x : ModGL TwistTag.E6.tag K), hΓ x x.2⟩ :
      adjointGroup Tag.F4 L) : ModGL Tag.F4 L) = _
  rw [units_map_entrywiseHom_eq_baseChangeGL_self, coe_e6FixedF4EquivAll,
    ← e6FixedToF4_baseChangeGL θ ⟨_, hΓ x x.2⟩]
  have hsub : (⟨baseChangeGL θ (baseChangeGL (algebraMap K L) (x : ModGL TwistTag.E6.tag K)),
      baseChangeGL_mem_twistedFixedGroup θ (hΓ x x.2)⟩ :
        twistedFixedGroup TwistTag.E6 L (RingHom.id L)) = ⟨_, hΓ x x.2⟩ :=
    Subtype.ext (by
      change baseChangeGL θ (baseChangeGL (algebraMap K L) (x : ModGL TwistTag.E6.tag K)) =
        baseChangeGL (algebraMap K L) (x : ModGL TwistTag.E6.tag K)
      rw [← units_map_entrywiseHom_eq_baseChangeGL_self, hθ x x.2])
  rw [hsub]
  rfl

private noncomputable def twE6_step5_primeFieldComponent {L : Type} [Field L]
    [Algebra (ZMod 2) L] : adjointGroup Tag.F4 (ZMod 2) →* ModGL Tag.F4 L :=
  (baseChangeGL (algebraMap (ZMod 2) L)).comp (adjointGroup Tag.F4 (ZMod 2)).subtype

private lemma twE6_step5_descent_to_prime_field {K L : Type} [Field K] [Field L]
    [Algebra (ZMod 2) L] [Algebra.IsAlgebraic (ZMod 2) L]
    (hK₂ : Nat.card (ZMod 2) = 2) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ (2 ^ 1))
    {p : ℕ} (E : Subgroup (ModGL TwistTag.E6.tag K)) (hE : CFSG.Open.IsElemAbelian p E)
    (φ : E →* ModGL Tag.F4 L) (hφ : Function.Injective φ)
    (hφmem : ∀ x : E, φ x ∈ adjointGroup Tag.F4 L)
    (hφfix : ∀ x : E, Units.map (entrywiseHom Fr) (φ x) = φ x) :
    Function.Injective (twE6_step5_primeFieldComponent (L := L)) ∧
      (∀ x : E, ∃ y : adjointGroup Tag.F4 (ZMod 2),
        twE6_step5_primeFieldComponent (L := L) y = φ x) ∧
      CFSG.Open.IsElemAbelian p (φ.range.comap (twE6_step5_primeFieldComponent (L := L))) ∧
      (φ.range.comap (twE6_step5_primeFieldComponent (L := L))).map
          (twE6_step5_primeFieldComponent (L := L)) = φ.range ∧
      Nat.card (φ.range.comap (twE6_step5_primeFieldComponent (L := L))) = Nat.card E := by
  have hι₂' : Function.Injective (twE6_step5_primeFieldComponent (L := L)) := fun x y h =>
    Subtype.ext (baseChangeGL_injective (algebraMap (ZMod 2) L) h)
  have hdesc : ∀ x : E, ∃ y : adjointGroup Tag.F4 (ZMod 2),
      twE6_step5_primeFieldComponent (L := L) y = φ x := by
    intro x
    obtain ⟨a, u, ⟨u0, hu0, rfl⟩, hr⟩ :=
      CFSG.LieType.Chevalley.exists_rootDiagUnit_mul_of_frobenius_fixed Tag.F4 (K := ZMod 2)
        Fr (fun c => by rw [hK₂]; exact hFr c) (hφmem x) (hφfix x)
    have := CFSG.Monster.Existence.Compat.subsingleton_units_of_card_two hK₂
    have ha : a = 1 := Subsingleton.elim _ _
    rw [ha, rootDiagUnit_one, map_one, one_mul] at hr
    exact ⟨⟨u0, hu0⟩, hr.symm⟩
  refine ⟨hι₂', hdesc, (isElemAbelian_range hE φ).comap hι₂', ?_, ?_⟩
  · exact Subgroup.map_comap_eq_self (by
      rintro u ⟨x, rfl⟩
      obtain ⟨y, hy⟩ := hdesc x
      exact ⟨y, hy⟩)
  · have hmap : (φ.range.comap (twE6_step5_primeFieldComponent (L := L))).map
        (twE6_step5_primeFieldComponent (L := L)) = φ.range :=
      Subgroup.map_comap_eq_self (by
        rintro u ⟨x, rfl⟩
        obtain ⟨y, hy⟩ := hdesc x
        exact ⟨y, hy⟩)
    rw [← Subgroup.card_map_of_injective hι₂', hmap]
    exact (Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv).symm

private lemma twE6_step5_prime_eq_three {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (E₂ : Subgroup (adjointGroup Tag.F4 (ZMod 2))) (hE₂ : CFSG.Open.IsElemAbelian p E₂)
    (h4 : p ^ 4 ≤ Nat.card E₂) :
    p = 3 ∧ orderOf (Nat.card (ZMod 2) : ZMod p) = 2 ∧
      CFSG.StandardType.ExcMaxToral.excDegCount Tag.F4
        (orderOf (Nat.card (ZMod 2) : ZMod p)) = 4 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hK₂ : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have hdeg : 4 ≤ CFSG.StandardType.ExcMaxToral.excDegCount Tag.F4
      (orderOf (Nat.card (ZMod 2) : ZMod p)) := by
    by_contra h
    have hle := CFSG.StandardType.ExcMaxToral.excPRankBound (Or.inr (Or.inr rfl)) (ZMod 2)
      hp hp2 (by omega) E₂ hE₂
    have hlt : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    exact (not_le.2 (lt_of_lt_of_le hlt h4)) hle
  have hd2 : orderOf (Nat.card (ZMod 2) : ZMod p) = 2 := by
    rcases CFSG.StandardType.ExcMaxToral.excDegCount_ge_four hdeg with ⟨-, hd, -⟩ | ⟨hE8, -, -⟩
    · rcases hd with hd | hd
      · exfalso
        rw [orderOf_eq_one_iff, hK₂] at hd
        have h1 : ((2 : ℕ) : ZMod p) - 1 = 1 := by push_cast; ring
        rw [hd, sub_self] at h1
        exact zero_ne_one h1
      · exact hd
    · exact absurd hE8 (by decide)
  have hp3 : p = 3 := by
    have h := pow_orderOf_eq_one (Nat.card (ZMod 2) : ZMod p)
    rw [hd2, hK₂] at h
    have h3 : ((3 : ℕ) : ZMod p) = 0 := by
      have : ((3 : ℕ) : ZMod p) = ((2 : ℕ) : ZMod p) ^ 2 - 1 := by push_cast; ring
      rw [this, h, sub_self]
    rw [ZMod.natCast_eq_zero_iff] at h3
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3
  subst hp3
  exact ⟨rfl, hd2, by rw [hd2]; decide⟩

private lemma twE6_step5_lang_torus_element {K : Type} [Field K]
    {E : Subgroup (ModGL TwistTag.E6.tag K)} {Fr : L2 →+* L2}
    (hFr : ∀ c, Fr c = c ^ (2 ^ 1))
    (E₂ : Subgroup (adjointGroup Tag.F4 (ZMod 2))) (hE₂ : CFSG.Open.IsElemAbelian 3 E₂)
    (h4 : 3 ^ 4 ≤ Nat.card E₂)
    (hd2 : orderOf (Nat.card (ZMod 2) : ZMod 3) = 2)
    (φ : E →* ModGL Tag.F4 L2)
    (hE₂def : E₂ = φ.range.comap (twE6_step5_primeFieldComponent (L := L2)))
    (hdesc : ∀ x : E, ∃ y : adjointGroup Tag.F4 (ZMod 2),
      twE6_step5_primeFieldComponent (L := L2) y = φ x)
    {b : ModGL TwistTag.E6.tag K} (hb : b ∈ E) :
    ∃ (D : LangDatum Tag.F4 L2) (w : WeylGroup Tag.F4) (y : adjointGroup Tag.F4 (ZMod 2))
      (c : Fin Tag.F4.rank → L2ˣ),
      D.Φ = Units.map (entrywiseHom Fr) ∧
        D.n = canonicalRep (coxeterSystem Tag.F4) L2 w ∧
        (∀ u : Fin Tag.F4.rank → ℤ, w • u = -u) ∧
        (∀ x ∈ E₂, D.g0⁻¹ * baseChangeGL (algebraMap (ZMod 2) L2)
          (x : ModGL Tag.F4 (ZMod 2)) * D.g0 ∈ D.torus) ∧
        y ∈ E₂ ∧
        twE6_step5_primeFieldComponent (L := L2) y = φ ⟨b, hb⟩ ∧
        rootDiagUnit Tag.F4 c =
          D.g0⁻¹ * baseChangeGL (algebraMap (ZMod 2) L2) (y : ModGL Tag.F4 (ZMod 2)) * D.g0 ∧
        ∀ k, c k ^ 3 = 1 := by
  have hdegE : CFSG.StandardType.ExcMaxToral.excDegCount Tag.F4
      (orderOf (Nat.card (ZMod 2) : ZMod 3)) = 4 := by rw [hd2]; decide
  obtain ⟨Fr', hFr', D, hΦ, -, ⟨w, hDn, hshape⟩, hmemT, -⟩ :=
    CFSG.StandardType.ExcMaxToral.adjointMaxElemToral Tag.F4 (ZMod 2) 3 inferInstance
      inferInstance Nat.prime_three (by norm_num) hdegE.ge _ hE₂ (by rw [hdegE]; exact h4)
  have hFrEq : Fr' = Fr := RingHom.ext fun c => by
    rw [hFr', Nat.card_zmod]; exact (hFr c).symm
  subst hFrEq
  have hw1 : ∀ u : Fin Tag.F4.rank → ℤ, w • u = -u := by
    unfold CFSG.StandardType.ExcMaxToral.ExcLangShape at hshape
    exact hshape.2.1 hd2
  obtain ⟨y, hy⟩ := hdesc ⟨b, hb⟩
  have hyE : y ∈ E₂ := by
    rw [hE₂def, Subgroup.mem_comap, hy]
    exact ⟨_, rfl⟩
  obtain ⟨c, hc⟩ := exists_rootDiagUnit_of_mem_torusGroup
    ((mem_twistedTorusOf.1 (hmemT y hyE)).1)
  have hy3 : ((y : adjointGroup Tag.F4 (ZMod 2)) : ModGL Tag.F4 (ZMod 2)) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hE₂.2 _ hyE, Subgroup.coe_one]
  have hc3 : ∀ k, c k ^ 3 = 1 := by
    have h1 : rootDiagUnit Tag.F4 (c ^ 3) = rootDiagUnit Tag.F4 1 := by
      rw [rootDiagUnit_one]
      change rootDiagUnitHom Tag.F4 L2 (c ^ 3) = 1
      rw [map_pow]
      change rootDiagUnit Tag.F4 c ^ 3 = 1
      rw [hc]
      have e : ∀ (g x : ModGL Tag.F4 L2), (g⁻¹ * x * g) ^ 3 = g⁻¹ * x ^ 3 * g :=
        fun g x => by simp only [pow_succ, pow_zero, one_mul]; group
      rw [e, ← map_pow, hy3, map_one, mul_one, inv_mul_cancel]
    intro k
    exact congrFun (CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_injective h1) k
  exact ⟨D, w, y, c, hΦ, hDn, hw1, hmemT, hyE, hy, hc, hc3⟩

private lemma twE6_step5_component {K : Type} [Field K] {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ (2 ^ 1)) [Algebra K L2]
    (E : Subgroup (ModGL TwistTag.E6.tag K))
    (hEC : E ≤ graphFixedRootGroup TwistTag.E6 K σ)
    (hEP : ∀ x ∈ E, diagramMap TwistTag.E6 K * x = x * diagramMap TwistTag.E6 K) :
    ∃ hΓ : ∀ x ∈ E, baseChangeGL (algebraMap K L2) x ∈
        twistedFixedGroup TwistTag.E6 L2 (RingHom.id L2),
      Function.Injective (twE6_step5_f4Component E hΓ) ∧
      (∀ x : E, twE6_step5_f4Component E hΓ x ∈ adjointGroup Tag.F4 L2) ∧
      (∀ x : E, Units.map (entrywiseHom (iterateFrobenius L2 2 1))
        (twE6_step5_f4Component E hΓ x) = twE6_step5_f4Component E hΓ x) := by
  have hFr₀ : ∀ c, iterateFrobenius L2 2 1 c = c ^ (2 ^ 1) := fun c => rfl
  have hισ : ∀ c, algebraMap K L2 (σ c) = iterateFrobenius L2 2 1 (algebraMap K L2 c) :=
    fun c => by rw [hFr₀, ← map_pow]; congr 1; exact hσ c
  have hxall : ∀ x ∈ E, baseChangeGL (algebraMap K L2) x ∈
      twistedFixedGroup TwistTag.E6 L2 (iterateFrobenius L2 2 1) ∧
      diagramMap TwistTag.E6 L2 * baseChangeGL (algebraMap K L2) x =
        baseChangeGL (algebraMap K L2) x * diagramMap TwistTag.E6 L2 ∧
      Units.map (entrywiseHom (iterateFrobenius L2 2 1)) (baseChangeGL (algebraMap K L2) x) =
        baseChangeGL (algebraMap K L2) x :=
    fun x hx => twE6_step5_baseChange_fixed hισ E hEC hEP hx
  have hxPL : ∀ x ∈ E, diagramMap TwistTag.E6 L2 * baseChangeGL (algebraMap K L2) x =
      baseChangeGL (algebraMap K L2) x * diagramMap TwistTag.E6 L2 :=
    fun x hx => (hxall x hx).2.1
  have hxΓ : ∀ x ∈ E, baseChangeGL (algebraMap K L2) x ∈
      twistedFixedGroup TwistTag.E6 L2 (RingHom.id L2) :=
    fun x hx => mem_twistedFixedGroup_id_iff.2 ⟨(hxall x hx).1.1, hxPL x hx⟩
  have hxFr : ∀ x ∈ E, Units.map (entrywiseHom (iterateFrobenius L2 2 1))
      (baseChangeGL (algebraMap K L2) x) = baseChangeGL (algebraMap K L2) x :=
    fun x hx => (hxall x hx).2.2
  exact ⟨hxΓ, twE6_step5_f4Component_injective E hxΓ,
    twE6_step5_f4Component_mem E hxΓ, twE6_step5_f4Component_fixed E hxΓ hxFr⟩

private lemma twE6_step5_weyl_inverts_torus (D : LangDatum Tag.F4 L2) (w : WeylGroup Tag.F4)
    (ω : List (Fin Tag.F4.rank))
    (hDn : D.n = canonicalRep (coxeterSystem Tag.F4) L2 w)
    (hDnω : D.n = weylWord (τ := Tag.F4) L2 ω)
    (hw1 : ∀ u : Fin Tag.F4.rank → ℤ, w • u = -u)
    (hconjW : ∀ (b : Fin Tag.F4.rank → L2ˣ),
      rootDiagUnit Tag.F4 b ∈ adjointGroup Tag.F4 L2 →
      weylWord (τ := Tag.E6) L2 (unfoldF4 ω) *
          rootDiagUnit Tag.E6 (fun i => b (e6IndexToF4 i)) *
          (weylWord (τ := Tag.E6) L2 (unfoldF4 ω))⁻¹ =
        rootDiagUnit Tag.E6
          (fun i => CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct
            ((coxeterSystem Tag.F4).wordProd ω) b (e6IndexToF4 i))) :
    (∀ b' : Fin Tag.F4.rank → L2ˣ,
      CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct
        ((coxeterSystem Tag.F4).wordProd ω) b' = b'⁻¹) ∧
    (∀ b' : Fin Tag.F4.rank → L2ˣ,
      CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct
        (CFSG.StandardType.E6GraphNoneSteps.wt (unfoldF4 ω)) (fun i => b' (e6IndexToF4 i)) =
        (fun i => b' (e6IndexToF4 i))⁻¹) := by
  have hwF : ∀ b' : Fin Tag.F4.rank → L2ˣ,
      CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct
        ((coxeterSystem Tag.F4).wordProd ω) b' = b'⁻¹ := by
    intro b'
    have h1 := weylWord_conj_rootDiagUnit (τ := Tag.F4) (L := L2) ω b'
    have h2 := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.canonicalRep_conj_rootDiagUnit
      (K := L2) w b'
    rw [← hDn, hDnω] at h2
    rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_injective (h1.symm.trans h2)]
    funext i
    simp only [CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct, Pi.inv_apply]
    have hi : w⁻¹ • (Pi.single i 1 : Fin Tag.F4.rank → ℤ) = -Pi.single i 1 := by
      have := hw1 (-Pi.single i 1)
      rw [neg_neg] at this
      calc w⁻¹ • (Pi.single i 1 : Fin Tag.F4.rank → ℤ) =
            w⁻¹ • (w • -(Pi.single i 1 : Fin Tag.F4.rank → ℤ)) := by rw [this]
        _ = _ := inv_smul_smul w _
    rw [hi, show rootChar b' (-Pi.single i 1) = (rootChar b' (Pi.single i 1))⁻¹ by
      simp only [rootChar, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib],
      CFSG.HardMathSupport.Timmesfeld.Tables.T1b.rootChar_single]
  refine ⟨hwF, ?_⟩
  intro b'
  have hb' := rootDiagUnit_mem_adjointGroup_of_isAlgClosed (τ := Tag.F4) (L := L2) b'
  have h1 := hconjW b' hb'
  have h2 := weylWord_conj_rootDiagUnit (τ := Tag.E6) (L := L2) (unfoldF4 ω)
    (fun i => b' (e6IndexToF4 i))
  rw [h1, hwF] at h2
  exact (CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_injective h2).symm

private lemma twE6_step5_finish {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (2 ^ 1))
    [Algebra K L2] [IsAlgClosure K L2] [CharP L2 2]
    {g : ModGL Tag.E6 L2} (hg : g ∈ adjointGroup Tag.E6 L2)
    (hgP : g ∈ twistedFixedGroup TwistTag.E6 L2 (RingHom.id L2))
    (ω : List (Fin TwistTag.E6.tag.rank))
    (hlang : Units.map (entrywiseHom (iterateFrobenius L2 2 1)) g =
      g * weylWord (τ := Tag.E6) L2 ω)
    (hwE : ∀ b : Fin Tag.F4.rank → L2ˣ,
      CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct
        (CFSG.StandardType.E6GraphNoneSteps.wt ω) (fun i => b (e6IndexToF4 i)) =
        (fun i => b (e6IndexToF4 i))⁻¹)
    {c : Fin Tag.F4.rank → L2ˣ} (hc3 : ∀ k, c k ^ 3 = 1)
    {b : ModGL TwistTag.E6.tag K}
    (hbg : baseChangeGL (algebraMap K L2) b =
      g * rootDiagUnit Tag.E6 (fun i => c (e6IndexToF4 i)) * g⁻¹) :
    ∃ z ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom, Commute z b ∧
      diagramMap TwistTag.E6 K * z * (diagramMap TwistTag.E6 K)⁻¹ ≠ z := by
  have hFr₀ : ∀ c : L2, iterateFrobenius L2 2 1 c = c ^ (2 ^ 1) := fun c => rfl
  obtain ⟨z, hzC, hcomm, hne⟩ := twE6_step5 (n := 1) le_rfl hK hσ (L := L2) hFr₀
    hg hgP ω hlang hwE hc3
  obtain ⟨zK, hzK, rfl⟩ := hzC
  refine ⟨zK, hzK, ?_, fun heq => hne ?_⟩
  · have h2 : Commute (baseChangeGL (algebraMap K L2) zK : ModGL Tag.E6 L2)
        (g * rootDiagUnit Tag.E6 (fun i => c (e6IndexToF4 i)) * g⁻¹) := hcomm
    rw [← hbg] at h2
    apply baseChangeGL_injective (algebraMap K L2)
    rw [map_mul, map_mul]
    exact h2.eq
  · rw [← baseChangeGL_diagramMap (algebraMap K L2) TwistTag.E6, ← map_inv, ← map_mul,
      ← map_mul, heq]

private theorem twE6_step5_core {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (2 ^ 1))
    [Algebra K L2] [IsAlgClosure K L2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (E : Subgroup (ModGL TwistTag.E6.tag K))
    (hEC : E ≤ graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
    (hEP : ∀ x ∈ E, diagramMap TwistTag.E6 K * x = x * diagramMap TwistTag.E6 K)
    (hE : CFSG.Open.IsElemAbelian p E) (h4 : p ^ 4 ≤ Nat.card E)
    {b : ModGL TwistTag.E6.tag K} (hb : b ∈ E) :
    ∃ z ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom, Commute z b ∧
      diagramMap TwistTag.E6 K * z * (diagramMap TwistTag.E6 K)⁻¹ ≠ z := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : CharP L2 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) L2).injective 2
  have hK₂ : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have hFr₀ : ∀ c, iterateFrobenius L2 2 1 c = c ^ (2 ^ 1) := fun c => rfl
  set ι := algebraMap K L2
  obtain ⟨hΓ, hφ, hφmem, hφfix⟩ := twE6_step5_component hσ E hEC hEP
  let φ : E →* ModGL Tag.F4 L2 := twE6_step5_f4Component E hΓ
  obtain ⟨_, hdesc, hE₂, _, hcard⟩ :=
    twE6_step5_descent_to_prime_field (L := L2) hK₂ hFr₀ E hE φ hφ hφmem hφfix
  obtain ⟨hp3, hd2, _⟩ := twE6_step5_prime_eq_three hp hp2
    (φ.range.comap (twE6_step5_primeFieldComponent (L := L2))) hE₂ (by rw [hcard]; exact h4)
  subst hp3
  obtain ⟨D, w, y, c, hΦ, hDn, hw1, _, _, hy, hc, hc3⟩ :=
    twE6_step5_lang_torus_element hFr₀ (φ.range.comap (twE6_step5_primeFieldComponent (L := L2)))
      hE₂ (by rw [hcard]; exact h4) hd2 φ rfl hdesc hb
  obtain ⟨ω, hDnω, hgP, _, hlang, hconj, hconjW⟩ :=
    CFSG.StandardType.E6GraphNoneSteps.f4LangDatum_transport D (iterateFrobenius L2 2 1) hΦ
  obtain ⟨_, hwE⟩ := twE6_step5_weyl_inverts_torus D w ω hDn hDnω hw1 hconjW
  have hcm := rootDiagUnit_mem_adjointGroup_of_isAlgClosed (τ := Tag.F4) (L := L2) c
  have hbg := hconj c hcm
  have hyb : (⟨D.g0, D.g0_mem⟩ * ⟨_, hcm⟩ * ⟨D.g0, D.g0_mem⟩⁻¹ : adjointGroup Tag.F4 L2) =
      e6FixedF4EquivAll L2 ⟨baseChangeGL ι b, hΓ b hb⟩ :=
    Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      change D.g0 * rootDiagUnit Tag.F4 c * D.g0⁻¹ = φ ⟨b, hb⟩
      rw [← hy, hc]
      group
      rfl)
  rw [hyb, CFSG.StandardType.E6GraphNoneSteps.coe_embE6F4, MulEquiv.symm_apply_apply] at hbg
  exact twE6_step5_finish hK hσ ((embE6F4 L2 ⟨D.g0, D.g0_mem⟩ : adjointGroup .E6 L2)).2 hgP
    (unfoldF4 ω) hlang hwE hc3 hbg

theorem twE6_step5_K {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (2 ^ 1)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (E : Subgroup (ModGL TwistTag.E6.tag K))
    (hEC : E ≤ graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
    (hEP : ∀ x ∈ E, diagramMap TwistTag.E6 K * x = x * diagramMap TwistTag.E6 K)
    (hE : CFSG.Open.IsElemAbelian p E) (h4 : p ^ 4 ≤ Nat.card E)
    {b : ModGL TwistTag.E6.tag K} (hb : b ∈ E) :
    ∃ z ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom, Commute z b ∧
      diagramMap TwistTag.E6 K * z * (diagramMap TwistTag.E6 K)⁻¹ ≠ z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 ^ (1 * 2) := by rw [Fintype.card_eq_nat_card, hK]; norm_num
  have : CharP K 2 := charP_of_card_eq_prime_pow hK'
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  let j : K →ₐ[ZMod 2] L2 := IsAlgClosed.lift
  let : Algebra K L2 := j.toRingHom.toAlgebra
  have : IsScalarTower (ZMod 2) K L2 :=
    IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  have : Algebra.IsAlgebraic K L2 := Algebra.IsAlgebraic.tower_top (K := ZMod 2) K
  have : IsAlgClosure K L2 := ⟨inferInstance, inferInstance⟩
  exact twE6_step5_core hK hσ hp hp2 E hEC hEP hE h4 hb

end CFSG.StandardType.E6GraphNoneSteps

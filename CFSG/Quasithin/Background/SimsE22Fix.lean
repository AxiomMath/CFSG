module

public import CFSG.Quasithin.Background.B6Defs
public import CFSG.Open.StatedDefs
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Quasithin.Background.Basic

public section

namespace CFSG.Quasithin.SimsE22

open CFSG.Open

@[expose] def InnerFieldAt {Y : Type} [Group Y] {F : Type} [Field F] (X : Subgroup Y)
    (φ : ↥X ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSL 2 F)) (t : Y) : Prop :=
  ∃ (g : Matrix.GeneralLinearGroup (Fin 2) F) (σ : F ≃+* F),
    IsSquare (Matrix.GeneralLinearGroup.det g) ∧
    ∀ (x : ↥X) (A : ↥(CFSG.Open.StatedSL 2 F)), φ x = QuotientGroup.mk A →
      ∃ (B : ↥(CFSG.Open.StatedSL 2 F)) (y : ↥X),
        (B : Matrix.GeneralLinearGroup (Fin 2) F) =
          g * Matrix.GeneralLinearGroup.map σ.toRingHom (A : Matrix.GeneralLinearGroup (Fin 2) F) *
            g⁻¹ ∧
        (y : Y) = t * (x : Y) * t⁻¹ ∧ φ y = QuotientGroup.mk B

section Conjugates

variable {P : Type*} [Group P]

def cj (h : P) (X : Subgroup P) : Subgroup P := X.map (MulAut.conj h).toMonoidHom

theorem mem_cj {h x : P} {X : Subgroup P} : x ∈ cj h X ↔ h⁻¹ * x * h ∈ X := by
  unfold cj
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem cj_cj (a b : P) (X : Subgroup P) : cj a (cj b X) = cj (a * b) X := by
  ext x
  simp only [mem_cj, mul_inv_rev, mul_assoc]

theorem cj_one (X : Subgroup P) : cj 1 X = X := by
  ext x
  simp [mem_cj]

theorem map_cj (σ : P ≃* P) (h : P) (X : Subgroup P) :
    (cj h X).map σ.toMonoidHom = cj (σ h) (X.map σ.toMonoidHom) := by
  ext x
  rw [Subgroup.mem_map_equiv, mem_cj, mem_cj, Subgroup.mem_map_equiv]
  simp

abbrev Conjs (X0 : Subgroup P) : Type _ := {X : Subgroup P // ∃ h : P, X = cj h X0}

instance conjsMulAction (X0 : Subgroup P) : MulAction P (Conjs X0) where
  smul a X := ⟨cj a X.1, by
    obtain ⟨h, hX⟩ := X.2
    exact ⟨a * h, by rw [hX, cj_cj]⟩⟩
  one_smul X := Subtype.ext (by
    show cj 1 X.1 = X.1
    exact cj_one _)
  mul_smul a b X := Subtype.ext (by
    show cj (a * b) X.1 = cj a (cj b X.1)
    exact (cj_cj a b X.1).symm)

instance finite_conjs [Finite P] (X0 : Subgroup P) : Finite (Conjs X0) :=
  Finite.of_surjective (fun h : P => (⟨cj h X0, h, rfl⟩ : Conjs X0))
    (fun X => by
      obtain ⟨h, hh⟩ := X.2
      exact ⟨h, Subtype.ext hh.symm⟩)

theorem natCard_conjs_dvd_index (X0 : Subgroup P) : Nat.card (Conjs X0) ∣ X0.index := by
  let x0 : Conjs X0 := ⟨X0, 1, (cj_one X0).symm⟩
  haveI : MulAction.IsPretransitive P (Conjs X0) := ⟨fun X Y => by
    obtain ⟨a, ha⟩ := X.2
    obtain ⟨b, hb⟩ := Y.2
    refine ⟨b * a⁻¹, Subtype.ext ?_⟩
    show cj (b * a⁻¹) X.1 = Y.1
    rw [ha, hb, cj_cj, inv_mul_cancel_right]⟩
  rw [← MulAction.index_stabilizer_of_transitive P x0]
  apply Subgroup.index_dvd_of_le
  intro a ha
  rw [MulAction.mem_stabilizer_iff]
  refine Subtype.ext ?_
  show cj a X0 = X0
  ext x
  rw [mem_cj]
  constructor
  · intro hx
    have := X0.mul_mem (X0.mul_mem ha hx) (X0.inv_mem ha)
    simpa [mul_assoc] using this
  · intro hx
    exact X0.mul_mem (X0.mul_mem (X0.inv_mem ha) hx) ha

theorem exists_fixed_conj [Finite P] {T : Type*} [Group T] (hT : IsPGroup 2 T)
    (ψ : T →* MulAut P) (X0 : Subgroup P) (hodd : Odd X0.index)
    (hψ : ∀ t : T, ∃ h : P, X0.map (ψ t).toMonoidHom = cj h X0) :
    ∃ h : P, ∀ t : T, (cj h X0).map (ψ t).toMonoidHom = cj h X0 := by
  have hstab : ∀ (t : T) (X : Conjs X0), ∃ h : P, X.1.map (ψ t).toMonoidHom = cj h X0 := by
    intro t X
    obtain ⟨h, hX⟩ := X.2
    obtain ⟨h', hh'⟩ := hψ t
    exact ⟨ψ t h * h', by rw [hX, map_cj, hh', cj_cj]⟩
  letI : MulAction T (Conjs X0) :=
    { smul := fun t X => ⟨X.1.map (ψ t).toMonoidHom, hstab t X⟩
      one_smul := fun X => Subtype.ext (by
        show X.1.map (ψ 1).toMonoidHom = X.1
        ext x
        rw [Subgroup.mem_map_equiv, map_one]
        rfl)
      mul_smul := fun s t X => Subtype.ext (by
        show X.1.map (ψ (s * t)).toMonoidHom = (X.1.map (ψ t).toMonoidHom).map (ψ s).toMonoidHom
        ext x
        simp only [Subgroup.mem_map_equiv, map_mul]
        rfl) }
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := hT.card_modEq_card_fixedPoints (Conjs X0)
  have hodd' : Odd (Nat.card (Conjs X0)) := hodd.of_dvd_nat (natCard_conjs_dvd_index X0)
  have hne : Nat.card (MulAction.fixedPoints T (Conjs X0)) ≠ 0 := by
    intro h0
    rw [h0] at hmod
    exact (Nat.not_even_iff_odd.2 hodd')
      (even_iff_two_dvd.2 ((Nat.modEq_zero_iff_dvd).1 hmod))
  obtain ⟨⟨⟨X, h, hXh⟩, hx⟩⟩ := (Nat.card_ne_zero.1 hne).1
  refine ⟨h, fun t => ?_⟩
  have := congrArg Subtype.val (MulAction.mem_fixedPoints.1 hx t)
  rw [← hXh]
  exact this

end Conjugates

section Transport

variable {Y : Type*} [Group Y]

@[expose] noncomputable def conjAut {K : Subgroup Y} [K.Normal] {P : Type*} [Group P]
    (φ : ↥K ≃* P) : Y →* MulAut P :=
  (MulAut.congr φ).toMonoidHom.comp MulAut.conjNormal

theorem conjAut_apply {K : Subgroup Y} [K.Normal] {P : Type*} [Group P] (φ : ↥K ≃* P) (t : Y)
    (p : P) : conjAut φ t p = φ (MulAut.conjNormal t (φ.symm p)) := rfl

theorem le_of_invariant {Ks Ts Ms : Subgroup Y} [Finite Y] [Ks.Normal]
    (hmin : MinParabolic (⊤ : Subgroup Y) Ts Ms) (hKs : IsSimpleGroup ↥Ks)
    {P : Type*} [Group P] (φ : ↥Ks ≃* P) (X : Subgroup P)
    (hinv : ∀ t ∈ Ts, ∀ p : P, conjAut φ t p ∈ X ↔ p ∈ X) (hbot : X ≠ ⊥) (htop : X ≠ ⊤)
    (w : P) (hw : w ∈ X) : ((φ.symm w : ↥Ks) : Y) ∈ Ms := by
  haveI := hKs
  let XY : Subgroup Y := (X.comap φ.toMonoidHom).map Ks.subtype
  have hmem : ∀ y : Y, y ∈ XY ↔ ∃ k : Ks, φ k ∈ X ∧ (k : Y) = y := fun y => Iff.rfl
  have hnorm : ∀ t ∈ Ts, t ∈ Subgroup.normalizer (XY : Set Y) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro b
    rw [hmem, hmem]
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine ⟨MulAut.conjNormal t k, ?_, rfl⟩
      have : conjAut φ t (φ k) = φ (MulAut.conjNormal t k) := by
        rw [conjAut_apply, MulEquiv.symm_apply_apply]
      rw [← this]
      exact (hinv t ht _).2 hk
    · rintro ⟨k', hk', hb⟩
      refine ⟨(MulAut.conjNormal t).symm k', ?_, ?_⟩
      · have : conjAut φ t (φ ((MulAut.conjNormal t).symm k')) = φ k' := by
          rw [conjAut_apply, MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]
        refine (hinv t ht _).1 ?_
        rw [this]
        exact hk'
      · rw [MulAut.conjNormal_symm_apply, hb]
        group
  have hQtop : Subgroup.normalizer (XY : Set Y) ≠ ⊤ := by
    intro hQ
    have hnormal : (X.comap φ.toMonoidHom).Normal := by
      refine ⟨fun n hn g => ?_⟩
      have hgQ : (g : Y) ∈ Subgroup.normalizer (XY : Set Y) := by rw [hQ]; trivial
      have hnXY : (n : Y) ∈ XY := ⟨n, hn, rfl⟩
      obtain ⟨k', hk', hk'eq⟩ := (Subgroup.mem_normalizer_iff.1 hgQ (n : Y)).1 hnXY
      have : k' = g * n * g⁻¹ := Subtype.ext (by simpa using hk'eq)
      rw [← this]
      exact hk'
    rcases hnormal.eq_bot_or_eq_top with hb | ht
    · apply hbot
      ext p
      have h1 : p ∈ X ↔ φ.symm p ∈ X.comap φ.toMonoidHom := by
        simp [Subgroup.mem_comap]
      rw [h1, hb]
      simp
    · apply htop
      rw [Subgroup.eq_top_iff']
      intro p
      have : φ.symm p ∈ X.comap φ.toMonoidHom := by rw [ht]; trivial
      simpa [Subgroup.mem_comap] using this
  have hTsQ : Ts ≤ Subgroup.normalizer (XY : Set Y) := fun t ht => hnorm t ht
  obtain ⟨N, hN, hQN⟩ := exists_isMaxSubgroupIn (lt_top_iff_ne_top.2 hQtop)
  have hNM : N = Ms := hmin.eq_of_maximal hN (hTsQ.trans hQN)
  have hwXY : ((φ.symm w : ↥Ks) : Y) ∈ XY :=
    (hmem _).2 ⟨φ.symm w, by rw [MulEquiv.apply_symm_apply]; exact hw, rfl⟩
  exact hNM ▸ hQN (Subgroup.le_normalizer hwXY)

theorem false_of_conjugate_orbits {Ks Ts Ms : Subgroup Y} [Finite Y] [Ks.Normal]
    (hmin : MinParabolic (⊤ : Subgroup Y) Ts Ms) (hKs : IsSimpleGroup ↥Ks)
    {P : Type*} [Group P] (φ : ↥Ks ≃* P) (X0 : Subgroup P) (hodd : Odd X0.index)
    (hX0top : X0 ≠ ⊤)
    (hstab : ∀ t ∈ Ts, ∃ h : P, X0.map (conjAut φ t).toMonoidHom = cj h X0)
    (x0 : P) (hx0 : x0 ∈ X0) (hx01 : x0 ≠ 1)
    (hx0inv : ∀ z : P, z * x0 = x0 * z → z * z = 1 → z = 1)
    (hz : ∃ z ∈ Ks, z ≠ 1 ∧ z * z = 1 ∧ ∀ m ∈ Ms ⊓ Ks, m * z = z * m) : False := by
  haveI : Finite P := Finite.of_equiv ↥Ks φ.toEquiv
  have hTs : IsPGroup 2 ↥Ts := hmin.isSylow.2.1
  obtain ⟨h, hfix⟩ := exists_fixed_conj hTs ((conjAut φ).comp Ts.subtype) X0 hodd
    (fun t => hstab t t.2)
  have hinv : ∀ t ∈ Ts, ∀ p : P, conjAut φ t p ∈ cj h X0 ↔ p ∈ cj h X0 := by
    intro t ht p
    have h1 : (cj h X0).map (conjAut φ t).toMonoidHom = cj h X0 := hfix ⟨t, ht⟩
    have h2 : conjAut φ t p ∈ (cj h X0).map (conjAut φ t).toMonoidHom ↔ p ∈ cj h X0 := by
      rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
    rwa [h1] at h2
  have hwX : h * x0 * h⁻¹ ∈ cj h X0 := by
    rw [mem_cj]
    simpa [mul_assoc] using hx0
  have hw1 : h * x0 * h⁻¹ ≠ 1 := by
    intro h1
    apply hx01
    calc x0 = h⁻¹ * (h * x0 * h⁻¹) * h := by group
      _ = 1 := by rw [h1]; group
  have hbot : cj h X0 ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.mem_bot] at hwX
    exact hw1 hwX
  have htop : cj h X0 ≠ ⊤ := by
    intro ht
    apply hX0top
    rw [Subgroup.eq_top_iff']
    intro x
    have : h * x * h⁻¹ ∈ cj h X0 := by rw [ht]; trivial
    rw [mem_cj] at this
    simpa [mul_assoc] using this
  have hMs := le_of_invariant hmin hKs φ (cj h X0) hinv hbot htop _ hwX
  obtain ⟨z, hzK, hz1, hzz, hzc⟩ := hz
  have hwKs : ((φ.symm (h * x0 * h⁻¹) : ↥Ks) : Y) ∈ Ks := (φ.symm (h * x0 * h⁻¹)).2
  have hcomm := hzc _ (Subgroup.mem_inf.2 ⟨hMs, hwKs⟩)
  have hcomm' : φ.symm (h * x0 * h⁻¹) * ⟨z, hzK⟩ = ⟨z, hzK⟩ * φ.symm (h * x0 * h⁻¹) :=
    Subtype.ext hcomm
  have hcomm'' : (h * x0 * h⁻¹) * φ ⟨z, hzK⟩ = φ ⟨z, hzK⟩ * (h * x0 * h⁻¹) := by
    simpa using congrArg φ hcomm'
  have hc : (h⁻¹ * φ ⟨z, hzK⟩ * h) * x0 = x0 * (h⁻¹ * φ ⟨z, hzK⟩ * h) := by
    calc (h⁻¹ * φ ⟨z, hzK⟩ * h) * x0
        = h⁻¹ * (φ ⟨z, hzK⟩ * (h * x0 * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * x0 * h⁻¹) * φ ⟨z, hzK⟩) * h := by rw [hcomm'']
      _ = x0 * (h⁻¹ * φ ⟨z, hzK⟩ * h) := by group
  have hzz' : φ ⟨z, hzK⟩ * φ ⟨z, hzK⟩ = 1 := by
    rw [← map_mul]
    have : (⟨z, hzK⟩ : ↥Ks) * ⟨z, hzK⟩ = 1 := Subtype.ext hzz
    rw [this, map_one]
  have hcc : (h⁻¹ * φ ⟨z, hzK⟩ * h) * (h⁻¹ * φ ⟨z, hzK⟩ * h) = 1 := by
    calc (h⁻¹ * φ ⟨z, hzK⟩ * h) * (h⁻¹ * φ ⟨z, hzK⟩ * h)
        = h⁻¹ * (φ ⟨z, hzK⟩ * φ ⟨z, hzK⟩) * h := by group
      _ = 1 := by rw [hzz']; group
  have hone := hx0inv _ hc hcc
  have hφz : φ ⟨z, hzK⟩ = 1 := by
    calc φ ⟨z, hzK⟩ = h * (h⁻¹ * φ ⟨z, hzK⟩ * h) * h⁻¹ := by group
      _ = 1 := by rw [hone]; group
  have : (⟨z, hzK⟩ : ↥Ks) = 1 := φ.injective (by rw [hφz, map_one])
  exact hz1 (congrArg Subtype.val this)

end Transport

theorem innerField_stab {Y : Type} [Group Y] [Finite Y] {F : Type} [Field F] {Ks : Subgroup Y}
    [Ks.Normal] (φ : ↥Ks ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSL 2 F))
    (X0 : Subgroup (CFSG.Open.StatedProj (CFSG.Open.StatedSL 2 F)))
    (hinv : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) F) (σ : F ≃+* F),
      IsSquare (Matrix.GeneralLinearGroup.det g) →
      ∃ h : CFSG.Open.StatedProj (CFSG.Open.StatedSL 2 F), ∀ (A B : ↥(CFSG.Open.StatedSL 2 F)),
        (B : Matrix.GeneralLinearGroup (Fin 2) F) =
          g * Matrix.GeneralLinearGroup.map σ.toRingHom (A : Matrix.GeneralLinearGroup (Fin 2) F) *
            g⁻¹ →
        (QuotientGroup.mk A : CFSG.Open.StatedProj (CFSG.Open.StatedSL 2 F)) ∈ X0 →
        (QuotientGroup.mk B : CFSG.Open.StatedProj (CFSG.Open.StatedSL 2 F)) ∈
          X0.map (MulAut.conj h).toMonoidHom)
    (t : Y) (ht : InnerFieldAt Ks φ t) :
    ∃ h : CFSG.Open.StatedProj (CFSG.Open.StatedSL 2 F),
      X0.map (conjAut φ t).toMonoidHom = cj h X0 := by
  haveI : Finite (CFSG.Open.StatedProj (CFSG.Open.StatedSL 2 F)) :=
    Finite.of_equiv ↥Ks φ.toEquiv
  obtain ⟨g, σ, hdet, hg⟩ := ht
  obtain ⟨h, hh⟩ := hinv g σ hdet
  refine ⟨h, Subgroup.eq_of_le_of_card_ge ?_ ?_⟩
  · rintro _ ⟨p0, hp0, rfl⟩
    obtain ⟨A, hA⟩ := QuotientGroup.mk_surjective p0
    obtain ⟨B, y, hB, hy, hφy⟩ := hg (φ.symm p0) A (by rw [MulEquiv.apply_symm_apply, hA])
    have hyeq : y = MulAut.conjNormal t (φ.symm p0) := Subtype.ext (by rw [hy]; rfl)
    have hψ : conjAut φ t p0 = QuotientGroup.mk B := by
      rw [conjAut_apply, ← hyeq, hφy]
    show conjAut φ t p0 ∈ cj h X0
    rw [hψ]
    exact hh A B hB (by rw [hA]; exact hp0)
  · rw [cj, Subgroup.card_map_of_injective (MulAut.conj h).injective,
      Subgroup.card_map_of_injective (conjAut φ t).injective]

theorem false_of_innerField {Y : Type} [Group Y] [Finite Y] {F : Type} [Field F]
    {Ks Ts Ms : Subgroup Y} (hmin : MinParabolic (⊤ : Subgroup Y) Ts Ms) (hKn : Ks.Normal)
    (hKs : IsSimpleGroup ↥Ks)
    (φ : ↥Ks ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSL 2 F))
    (X0 : Subgroup (CFSG.Open.StatedProj (CFSG.Open.StatedSL 2 F)))
    (hodd : Odd X0.index) (hX0top : X0 ≠ ⊤)
    (hinv : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) F) (σ : F ≃+* F),
      IsSquare (Matrix.GeneralLinearGroup.det g) →
      ∃ h : CFSG.Open.StatedProj (CFSG.Open.StatedSL 2 F), ∀ (A B : ↥(CFSG.Open.StatedSL 2 F)),
        (B : Matrix.GeneralLinearGroup (Fin 2) F) =
          g * Matrix.GeneralLinearGroup.map σ.toRingHom (A : Matrix.GeneralLinearGroup (Fin 2) F) *
            g⁻¹ →
        (QuotientGroup.mk A : CFSG.Open.StatedProj (CFSG.Open.StatedSL 2 F)) ∈ X0 →
        (QuotientGroup.mk B : CFSG.Open.StatedProj (CFSG.Open.StatedSL 2 F)) ∈
          X0.map (MulAut.conj h).toMonoidHom)
    (x0 : CFSG.Open.StatedProj (CFSG.Open.StatedSL 2 F)) (hx0 : x0 ∈ X0) (hx01 : x0 ≠ 1)
    (hx0inv : ∀ z : CFSG.Open.StatedProj (CFSG.Open.StatedSL 2 F), z * x0 = x0 * z → z * z = 1 →
      z = 1)
    (hz : ∃ z ∈ Ks, z ≠ 1 ∧ z * z = 1 ∧ ∀ m ∈ Ms ⊓ Ks, m * z = z * m)
    (hall : ∀ t ∈ Ts, InnerFieldAt Ks φ t) : False := by
  haveI := hKn
  exact false_of_conjugate_orbits hmin hKs φ X0 hodd hX0top
    (fun t ht => innerField_stab φ X0 hinv t (hall t ht)) x0 hx0 hx01 hx0inv hz

end CFSG.Quasithin.SimsE22

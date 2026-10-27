module

public import CFSG.Open.LocalVocabulary

public section

open CFSG.Open
open scoped Pointwise

namespace CFSG.RankThree.PartTwo.Sec4.Item434U38

variable {Γ : Type*} [Group Γ]

@[expose] noncomputable def conjAutOn (Y : Subgroup Γ) (e : Γ) (he : e ∈ Subgroup.normalizer (Y : Set Γ)) :
    MulAut Y where
  toFun y := ⟨e * y * e⁻¹, (Subgroup.mem_normalizer_iff.mp he y).mp y.2⟩
  invFun y := ⟨e⁻¹ * y * e, by
    have h := Subgroup.mem_normalizer_iff.mp he (e⁻¹ * (y : Γ) * e)
    have h2 : e * (e⁻¹ * (y : Γ) * e) * e⁻¹ = y := by group
    rw [h2] at h
    exact h.mpr y.2⟩
  left_inv y := by ext; simp [mul_assoc]
  right_inv y := by ext; simp [mul_assoc]
  map_mul' x y := by ext; simp [mul_assoc]

@[expose] noncomputable def conjHom (Y E : Subgroup Γ) (h : E ≤ Subgroup.normalizer (Y : Set Γ)) :
    E →* MulAut Y where
  toFun e := conjAutOn Y e (h e.2)
  map_one' := by ext y; simp [conjAutOn]
  map_mul' a b := by ext y; simp [conjAutOn, mul_assoc]

theorem exists_normalized_sylow [Finite Γ] {Y E : Subgroup Γ} {r : ℕ} [Fact r.Prime]
    (hE3 : IsPGroup 3 E) (hY : ¬ 3 ∣ Nat.card Y) (h : E ≤ Subgroup.normalizer (Y : Set Γ)) :
    ∃ P : Sylow r Y, ∀ e ∈ E, ∀ x : Γ, x ∈ P.map Y.subtype → (e * x * e⁻¹) ∈ P.map Y.subtype := by
  letI : MulDistribMulAction E Y := MulDistribMulAction.compHom Y (conjHom Y E h)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmod := hE3.card_modEq_card_fixedPoints (Sylow r Y)
  have hdvd : Nat.card (Sylow r Y) ∣ Nat.card Y := by
    obtain ⟨P⟩ : Nonempty (Sylow r Y) := inferInstance
    rw [Sylow.card_eq_index_normalizer P]
    exact Subgroup.index_dvd_card _
  have h3 : ¬ 3 ∣ Nat.card (Sylow r Y) := fun h3 => hY (h3.trans hdvd)
  have hne : Nat.card (MulAction.fixedPoints E (Sylow r Y)) ≠ 0 := by
    intro h0
    rw [h0] at hmod
    exact h3 ((Nat.modEq_zero_iff_dvd).mp hmod)
  obtain ⟨⟨P, hP⟩⟩ := (Nat.card_pos_iff.mp (Nat.pos_of_ne_zero hne)).1
  refine ⟨P, fun e he x hx => ?_⟩
  have hPe : (⟨e, he⟩ : E) • P = P := hP ⟨e, he⟩
  obtain ⟨y, hyP, rfl⟩ := Subgroup.mem_map.mp hx
  have hmem : ((⟨e, he⟩ : E) • y : Y) ∈ ((⟨e, he⟩ : E) • (P : Subgroup Y) : Subgroup Y) :=
    Subgroup.smul_mem_pointwise_smul y _ _ hyP
  have h1 : (((⟨e, he⟩ : E) • P : Sylow r Y) : Subgroup Y) =
      (⟨e, he⟩ : E) • (P : Subgroup Y) := rfl
  have h2 : ((⟨e, he⟩ : E) • y : Y) ∈ (((⟨e, he⟩ : E) • P : Sylow r Y) : Subgroup Y) := by
    rw [h1]; exact hmem
  rw [hPe] at h2
  refine Subgroup.mem_map.mpr ⟨(⟨e, he⟩ : E) • y, h2, ?_⟩
  rfl

end CFSG.RankThree.PartTwo.Sec4.Item434U38

namespace CFSG.RankThree.PartTwo.Sec4.Item434U38

variable {Γ : Type*} [Group Γ]

theorem exists_elemAbelian_normalized [Finite Γ] {Y E : Subgroup Γ} (hE3 : ∀ x ∈ E, x ^ 3 = 1)
    (hY : ¬ 3 ∣ Nat.card Y) (hYbot : Y ≠ ⊥) (h : E ≤ Subgroup.normalizer (Y : Set Γ)) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 3 ∧ ∃ V : Subgroup Γ, V ≠ ⊥ ∧ IsElemAbelian r V ∧
      E ≤ Subgroup.normalizer (V : Set Γ) := by
  have hcard1 : Nat.card Y ≠ 1 := fun h1 => hYbot (Subgroup.eq_bot_of_card_eq Y h1)
  obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd hcard1
  have hr3 : r ≠ 3 := fun h3 => hY (h3 ▸ hrdvd)
  haveI : Fact r.Prime := ⟨hr⟩
  have hE3' : IsPGroup 3 E := fun g => ⟨1, by
    apply Subtype.ext
    simpa using hE3 g g.2⟩
  obtain ⟨P, hPnorm⟩ := exists_normalized_sylow (r := r) hE3' hY h
  set R : Subgroup Γ := (P : Subgroup Y).map Y.subtype with hR
  have hRp : IsPGroup r R := P.isPGroup'.map Y.subtype
  have hRcard : Nat.card R = Nat.card (P : Subgroup Y) :=
    Subgroup.card_map_of_injective Y.subtype_injective
  have hRdvd : r ∣ Nat.card R := by
    have h1 : Nat.card (P : Subgroup Y) = r ^ (Nat.card Y).factorization r :=
      P.card_eq_multiplicity
    have h2 : 0 < (Nat.card Y).factorization r :=
      Nat.Prime.factorization_pos_of_dvd hr Nat.card_pos.ne' hrdvd
    rw [hRcard, h1]
    exact dvd_pow_self r h2.ne'
  have hRnorm : ∀ e ∈ E, ∀ x ∈ R, e * x * e⁻¹ ∈ R := hPnorm
  haveI : Nontrivial R := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    exact lt_of_lt_of_le hr.one_lt (Nat.le_of_dvd Nat.card_pos hRdvd)
  haveI : Nontrivial (Subgroup.center R) := hRp.center_nontrivial
  have hZp : IsPGroup r (Subgroup.center R) := hRp.to_subgroup _
  have hZdvd : r ∣ Nat.card (Subgroup.center R) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hZp
    have hn0 : n ≠ 0 := by
      rintro rfl
      have : Nat.card (Subgroup.center R) = 1 := by simpa using hn
      have : Subsingleton (Subgroup.center R) := (Nat.card_eq_one_iff_unique.mp this).1
      exact not_subsingleton (Subgroup.center R) this
    rw [hn]
    exact dvd_pow_self r hn0
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center R) r hZdvd
  set Z' : Subgroup Γ := (Subgroup.center R).map R.subtype with hZ'
  have hZcomm : ∀ x ∈ Z', ∀ y ∈ Z', x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.mp ha b)
    simpa [Subgroup.coe_mul] using h1.symm
  let V : Subgroup Γ :=
    { carrier := {x | x ∈ Z' ∧ x ^ r = 1}
      one_mem' := ⟨Z'.one_mem, one_pow r⟩
      mul_mem' := fun {a b} ha hb => ⟨Z'.mul_mem ha.1 hb.1, by
        rw [Commute.mul_pow (hZcomm a ha.1 b hb.1), ha.2, hb.2, one_mul]⟩
      inv_mem' := fun {a} ha => ⟨Z'.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hVmem : ∀ x, x ∈ V ↔ x ∈ Z' ∧ x ^ r = 1 := fun x => Iff.rfl
  have hzZ : ((z : R) : Γ) ∈ Z' := Subgroup.mem_map.mpr ⟨(z : R), z.2, rfl⟩
  have hzr : ((z : R) : Γ) ^ r = 1 := by
    have h1 : z ^ r = 1 := hz ▸ pow_orderOf_eq_one z
    have := congrArg (fun w : Subgroup.center R => ((w : R) : Γ)) h1
    simpa [Subgroup.coe_pow] using this
  have hVne : V ≠ ⊥ := by
    intro hV
    have hmem : ((z : R) : Γ) ∈ V := (hVmem _).mpr ⟨hzZ, hzr⟩
    rw [hV, Subgroup.mem_bot] at hmem
    have hz1 : z = 1 := Subtype.ext (Subtype.ext hmem)
    rw [hz1, orderOf_one] at hz
    exact hr.one_lt.ne hz
  have hZinv : ∀ e ∈ E, ∀ x ∈ Z', e * x * e⁻¹ ∈ Z' := by
    intro e he x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    have hmemR : e * (a : Γ) * e⁻¹ ∈ R := hRnorm e he a a.2
    refine Subgroup.mem_map.mpr ⟨⟨e * a * e⁻¹, hmemR⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    have hy' : e⁻¹ * (y : Γ) * (e⁻¹)⁻¹ ∈ R := hRnorm e⁻¹ (E.inv_mem he) y y.2
    have hc := congrArg Subtype.val (Subgroup.mem_center_iff.mp ha ⟨e⁻¹ * y * e⁻¹⁻¹, hy'⟩)
    simp only [Subgroup.coe_mul, inv_inv] at hc
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    calc (y : Γ) * (e * a * e⁻¹) = e * ((e⁻¹ * y * e) * a) * e⁻¹ := by group
      _ = e * (a * (e⁻¹ * y * e)) * e⁻¹ := by rw [hc]
      _ = (e * a * e⁻¹) * y := by group
  have hVinv : ∀ e ∈ E, ∀ x ∈ V, e * x * e⁻¹ ∈ V := fun e he x hx =>
    (hVmem _).mpr ⟨hZinv e he x ((hVmem x).mp hx).1, by
      rw [conj_pow, ((hVmem x).mp hx).2]; simp⟩
  have hnorm : E ≤ Subgroup.normalizer (V : Set Γ) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hVinv e he x
    · intro hx
      have := hVinv e⁻¹ (E.inv_mem he) _ hx
      simpa [mul_assoc] using this
  refine ⟨r, hr, hr3, V, hVne, ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ((hVmem x).mp hx).2⟩, hnorm⟩
  exact hZcomm a ((hVmem a).mp a.2).1 b ((hVmem b).mp b.2).1

end CFSG.RankThree.PartTwo.Sec4.Item434U38

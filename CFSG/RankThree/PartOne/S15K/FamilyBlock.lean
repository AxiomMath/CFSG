module

public import CFSG.RankThree.PartOne.S15K.FamilyForms
public import CFSG.RankThree.PartOne.KC.OrthogonalQPlusOnePlanes

public section

namespace CFSG.RankThree.PartOne.S15K

open Polynomial Module CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem not_dvd_sub_one_of_dvd_add_one {q p : ℕ} (hq : 1 ≤ q) (hp3 : 3 ≤ p) (hpq : p ∣ q + 1) :
    ¬ p ∣ q - 1 := by
  intro h
  have h2 : p ∣ (q + 1) - (q - 1) := Nat.dvd_sub hpq h
  have h3 : (q + 1) - (q - 1) = 2 := by omega
  rw [h3] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  omega

omit [CharP K 2] in
theorem exists_hermBlock (hx : OddOrderIsometry Q p x) (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ Nat.card K + 1) {h : K[X]} [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1) :
    ∃ (ℓ f : ℕ) (hU : UnitaryFieldData ℓ f (AdjoinRoot h))
      (B : primaryComponent x.toLinearMap h →ₛₗ[hU.bar] primaryComponent x.toLinearMap h →ₗ[AdjoinRoot h]
        AdjoinRoot h),
      B.IsSymm ∧ B.SeparatingLeft ∧
      (∀ u w c, Algebra.trace K (AdjoinRoot h) (B u w * c) =
        QuadraticMap.polar Q (u : V) ((c • w : primaryComponent x.toLinearMap h) : V)) ∧
      ℓ ^ f = Nat.card K ∧ finrank K (AdjoinRoot h) = 2 := by
  classical
  have hp2 : Odd p := hp.odd_of_ne_two (by omega)
  have hirr := irreducible_of_mem_primaryFactors hh
  have hself : h = reciprocalPolynomial h :=
    (hx.reciprocal_eq_of_dvd_card_succ hp hpq hh hne1).symm
  obtain ⟨d, H, hdeg, hroot, hH, hadd1, hadd2, hleft, hright, hsymm⟩ :=
    hx.exists_selfDual_hermitian hp2 hh hne1 hself
  have hd : finrank K (AdjoinRoot h) = 2 * d := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  obtain ⟨hd2, -⟩ := hx.exists_norm_model hp hp3 hpq hh hne1
  have hd1 : d = 1 := by omega
  subst hd1
  obtain ⟨ℓ, f, hU, hq, hbar⟩ := exists_unitaryFieldData K (AdjoinRoot h) hd
  have hbar' : ∀ z, frobPow K (AdjoinRoot h) 1 z = hU.bar z := fun z => by
    rw [hbar, frobPow_apply]
  let B : primaryComponent x.toLinearMap h →ₛₗ[hU.bar]
      primaryComponent x.toLinearMap h →ₗ[AdjoinRoot h] AdjoinRoot h :=
    LinearMap.mk₂'ₛₗ hU.bar (RingHom.id _) H hadd1
      (fun c u w => by rw [hleft, smul_eq_mul, hbar']) hadd2
      (fun c u w => by rw [hright, smul_eq_mul, RingHom.id_apply])
  have hBH : ∀ u w, B u w = H u w := fun u w => rfl
  refine ⟨ℓ, f * 1, hU, B, ⟨fun u w => by rw [hBH, hBH, hsymm u w, hbar']⟩, ?_,
    fun u w c => by rw [hBH]; exact hH u w c, by rw [mul_one, ← pow_one (ℓ ^ f)]; simpa using hq.symm, hd2⟩
  intro u hu
  refine Subtype.ext (hx.eq_zero_of_polar_selfdual hh hself u.2 fun w hw => ?_)
  have h1 := hH u ⟨w, hw⟩ 1
  rw [mul_one, one_smul] at h1
  have h2 : H u ⟨w, hw⟩ = 0 := by rw [← hBH]; exact hu _
  rw [h2, map_zero] at h1
  exact h1.symm

structure HermData (Q : QuadraticForm K V) (x : V ≃ₗ[K] V) (h : K[X]) [Fact (Irreducible h)] where
  ℓ : ℕ
  f : ℕ
  hU : UnitaryFieldData ℓ f (AdjoinRoot h)
  B : primaryComponent x.toLinearMap h →ₛₗ[hU.bar] primaryComponent x.toLinearMap h →ₗ[AdjoinRoot h]
    AdjoinRoot h
  symm : B.IsSymm
  sep : B.SeparatingLeft
  trace : ∀ u w c, Algebra.trace K (AdjoinRoot h) (B u w * c) =
    QuadraticMap.polar Q (u : V) ((c • w : primaryComponent x.toLinearMap h) : V)
  card : ℓ ^ f = Nat.card K
  finrank_eq : finrank K (AdjoinRoot h) = 2

omit [CharP K 2] in
theorem nonempty_hermData (hx : OddOrderIsometry Q p x) (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ Nat.card K + 1) {h : K[X]} [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1) : Nonempty (HermData Q x h) := by
  obtain ⟨ℓ, f, hU, B, hs, hl, ht, hc, hr⟩ := exists_hermBlock hx hp hp3 hpq hh hne1
  exact ⟨⟨ℓ, f, hU, B, hs, hl, ht, hc, hr⟩⟩

@[expose] noncomputable def normPlane (x : V ≃ₗ[K] V) (h : K[X]) [Fact (Irreducible h)]
    (b : primaryComponent x.toLinearMap h) : Submodule K V :=
  LinearMap.range ((primaryComponent x.toLinearMap h).subtype ∘ₗ
    (LinearMap.toSpanSingleton (AdjoinRoot h) (primaryComponent x.toLinearMap h) b).restrictScalars K)

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem mem_normPlane {h : K[X]} [Fact (Irreducible h)] {b : primaryComponent x.toLinearMap h}
    {v : V} : v ∈ normPlane x h b ↔ ∃ c : AdjoinRoot h, ((c • b : primaryComponent x.toLinearMap h) : V) = v :=
  Iff.rfl

namespace HermData

variable {h : K[X]} [Fact (Irreducible h)] (D : HermData Q x h)

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem polar_norm (c c' : AdjoinRoot h) (b b' : primaryComponent x.toLinearMap h) :
    QuadraticMap.polar Q ((c • b : primaryComponent x.toLinearMap h) : V)
        ((c' • b' : primaryComponent x.toLinearMap h) : V) =
      Algebra.trace K (AdjoinRoot h) (D.hU.bar c * D.B b b' * c') := by
  rw [← D.trace (c • b) b' c', map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem polar_plane_eq_zero {b b' : primaryComponent x.toLinearMap h} (hbb : D.B b b' = 0) :
    ∀ u ∈ normPlane x h b, ∀ w ∈ normPlane x h b', QuadraticMap.polar Q u w = 0 := by
  intro u hu w hw
  obtain ⟨c, rfl⟩ := mem_normPlane.mp hu
  obtain ⟨c', rfl⟩ := mem_normPlane.mp hw
  rw [D.polar_norm, hbb]
  simp

omit [CharP K 2] [FiniteDimensional K V] in
theorem plane_regular {b : primaryComponent x.toLinearMap h} (hb : D.B b b = 1) :
    ∀ v ∈ normPlane x h b, (∀ u ∈ normPlane x h b, QuadraticMap.polar Q v u = 0) → v = 0 := by
  intro v hv hperp
  obtain ⟨c, rfl⟩ := mem_normPlane.mp hv
  have hc : D.hU.bar c = 0 := by
    refine eq_zero_of_trace_mul_eq_zero K (AdjoinRoot h) fun c' => ?_
    have := hperp ((c' • b : primaryComponent x.toLinearMap h) : V) (mem_normPlane.mpr ⟨c', rfl⟩)
    rw [D.polar_norm, hb, mul_one] at this
    exact this
  have hc0 : c = 0 := (map_eq_zero_iff _ D.hU.bar.injective).mp hc
  rw [hc0, zero_smul]
  rfl

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
include D in
theorem finrank_plane {b : primaryComponent x.toLinearMap h} (hb : b ≠ 0) :
    finrank K (normPlane x h b) = 2 := by
  have hinj : Function.Injective ((primaryComponent x.toLinearMap h).subtype ∘ₗ
      (LinearMap.toSpanSingleton (AdjoinRoot h) (primaryComponent x.toLinearMap h) b).restrictScalars
        K) := by
    intro c c' hcc
    have : c • b = c' • b := Subtype.ext hcc
    exact smul_left_injective (AdjoinRoot h) hb this
  rw [normPlane, LinearMap.finrank_range_of_inj hinj, D.finrank_eq]

theorem plane_aniso (hx : OddOrderIsometry Q p x) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ Nat.card K + 1) (hne1 : h ≠ X - 1) (hh : h ∈ primaryFactors x.toLinearMap)
    {b : primaryComponent x.toLinearMap h} (hb1 : D.B b b = 1) (hb0 : b ≠ 0) :
    ∀ v ∈ normPlane x h b, Q v = 0 → v = 0 := by
  have hmon := monic_of_mem_primaryFactors hh
  have hnk : ¬ p ∣ Nat.card K - 1 :=
    not_dvd_sub_one_of_dvd_add_one (Nat.succ_le_of_lt Finite.card_pos) (by omega) hpq
  refine eq_zero_of_singular_of_isometry (P := normPlane x h b) (D.finrank_plane hb0)
    (D.plane_regular hb1) hp (by omega) hnk (y := x)
    (fun v => (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hx.mem) v) ?_ hx.pow_eq_one ?_
  · intro v hv
    obtain ⟨c, rfl⟩ := mem_normPlane.mp hv
    refine mem_normPlane.mpr ⟨AdjoinRoot.root h * c, ?_⟩
    rw [← smul_smul, coe_root_smul_primaryComponent]
    rfl
  · refine ⟨(b : V), mem_normPlane.mpr ⟨1, by rw [one_smul]⟩, fun hxb => ?_⟩
    have h1 : (AdjoinRoot.root h • b : primaryComponent x.toLinearMap h) = b :=
      Subtype.ext (by rw [coe_root_smul_primaryComponent]; exact hxb)
    have h2 : (AdjoinRoot.root h - 1) • b = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact root_ne_one hmon hne1 (sub_eq_zero.mp h3)
    · exact hb0 h3

end HermData

end CFSG.RankThree.PartOne.S15K

module

public import CFSG.RankThree.PartOne.S11d.OrthCyclic
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalarElementary
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived

public section

namespace CFSG.RankThree.PartOne

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.RankThree.OrthogonalInvolutions CFSG.LieType.Universal.Spin

section Dim

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

omit [Finite K] in
theorem KCOrthogonal.OddOrderIsometry.three_le_finrank_fixed (hx : OddOrderIsometry Q p x)
    (hmult : ∀ h ∈ primaryFactors x.toLinearMap, h ≠ X - 1 →
      primaryMultiplicity x.toLinearMap h ≤ 1)
    (hQ : (polarBilin Q).Nondegenerate) {y : V ≃ₗ[K] V} (hy : y ∈ orthDerived Q) (hy2 : y ^ 2 = 1)
    (hy1 : y ≠ 1) (hyx : y * x = x * y) : 3 ≤ finrank K (fixedSpace x) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hyc : y ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hyx
  have hR : ∀ r ∈ othersSpace x.toLinearMap (X - 1), y r = r :=
    hx.apply_eq_of_two_pow hmult hyc (k := 1) (by rw [pow_one]; exact hy2)
  obtain ⟨hc, horth⟩ := hx.fixed_others
  have hyy : ∀ v, y (y v) = v := fun v => by
    have := congrArg (fun f : V ≃ₗ[K] V => f v) hy2
    simpa [pow_two] using this
  have hW : ∀ w ∈ fixedSpace x, y w ∈ fixedSpace x := fun w hw => mem_fixedSpace_of_apply hyc hw
  set c := commSpace y with hcdef
  have hfix : ∀ v, y (y v - v) = y v - v := by
    intro v
    rw [map_sub, hyy v]
    have h0 : y v - v + (y v - v) = 0 := by
      rw [← two_smul K (y v - v), h2, zero_smul]
    calc v - y v = -(y v - v) := by abel
      _ = y v - v := by rw [neg_eq_iff_add_eq_zero]; exact h0
  have hcW : c ≤ fixedSpace x := by
    intro u hu
    obtain ⟨v, rfl⟩ := mem_commSpace.mp hu
    obtain ⟨w, hw, r, hr, rfl⟩ := exists_add_of_isCompl hc v
    rw [map_add, hR r hr]
    have : y w + r - (w + r) = y w - w := by abel
    rw [this]
    exact sub_mem (hW w hw) hw
  have hcker : ∀ u ∈ c, y u = u := by
    intro u hu
    obtain ⟨v, rfl⟩ := mem_commSpace.mp hu
    exact hfix v
  obtain ⟨w₀, hw₀, hmove⟩ : ∃ w₀ ∈ fixedSpace x, y w₀ ≠ w₀ := by
    obtain ⟨v, hv⟩ : ∃ v, y v ≠ v := by
      by_contra hcon
      push Not at hcon
      exact hy1 (LinearEquiv.ext hcon)
    obtain ⟨w, hw, r, hr, rfl⟩ := exists_add_of_isCompl hc v
    refine ⟨w, hw, fun hwe => hv ?_⟩
    rw [map_add, hR r hr, hwe]
  have heven : Even (finrank K c) := by
    have hd := dicksonHom_apply_orthDerived_eq_one hQ hy
    simp only [dicksonHom_apply, ofAdd_eq_one] at hd
    exact (ZMod.natCast_eq_zero_iff_even).mp hd
  have hc1 : 1 ≤ finrank K c := by
    rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    intro hbot
    have : y w₀ - w₀ ∈ c := mem_commSpace.mpr ⟨w₀, rfl⟩
    rw [hbot, Submodule.mem_bot, sub_eq_zero] at this
    exact hmove this
  have hc2 : 2 ≤ finrank K c := by
    obtain ⟨k, hk⟩ := heven
    omega
  have hlt : c < fixedSpace x := by
    refine lt_of_le_of_ne hcW fun heq => hmove ?_
    exact hcker w₀ (heq ▸ hw₀)
  have := Submodule.finrank_lt_finrank_of_lt hlt
  omega

omit [Finite K] in
theorem KCOrthogonal.OddOrderIsometry.even_finrank_fixed (hx : OddOrderIsometry Q p x) :
    Even (finrank K (fixedSpace x)) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  refine LinearMap.BilinForm.IsAlt.even_finrank
    (B := polarBilin (Q.comp (fixedSpace x).subtype)) (fun a => ?_)
    hx.polarBilin_fixed_nondegenerate
  rw [polarBilin_apply_apply, polar_self_eq_two_mul, h2, zero_mul]

omit [Finite K] in
theorem KCOrthogonal.OddOrderIsometry.four_le_finrank_fixed (hx : OddOrderIsometry Q p x)
    (hmult : ∀ h ∈ primaryFactors x.toLinearMap, h ≠ X - 1 →
      primaryMultiplicity x.toLinearMap h ≤ 1)
    (hQ : (polarBilin Q).Nondegenerate) {y : V ≃ₗ[K] V} (hy : y ∈ orthDerived Q) (hy2 : y ^ 2 = 1)
    (hy1 : y ≠ 1) (hyx : y * x = x * y) : 4 ≤ finrank K (fixedSpace x) := by
  have h3 := hx.three_le_finrank_fixed hmult hQ hy hy2 hy1 hyx
  obtain ⟨k, hk⟩ := hx.even_finrank_fixed
  omega

end Dim

section Singular

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

omit [Finite K] in
theorem exists_singular_of_even_regular (Q : QuadraticForm K V)
    (hQ : (polarBilin Q).Nondegenerate) [Finite K] {n : ℕ} (hn : 2 ≤ n)
    (hdim : finrank K V = 2 * n) : ∃ e : V, e ≠ 0 ∧ Q e = 0 := by
  rcases CFSG.GroupTheory.WeirSylow.exists_isometry_quadPlus_or_quadMinus Q hQ (by omega) hdim with
    he | ⟨b, c, -, he⟩
  · obtain ⟨e⟩ := he
    let s : Fin n ⊕ Fin n → K := Pi.single (Sum.inl ⟨0, by omega⟩) 1
    have hs : quadPlus n K s = 0 := by
      rw [quadPlus_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      simp [s, Pi.single_apply]
    have hs0 : s ≠ 0 := fun h => by
      have := congrFun h (Sum.inl ⟨0, by omega⟩)
      simp [s] at this
    refine ⟨e.symm s, fun h => hs0 ?_, ?_⟩
    · simpa using congrArg e h
    · rw [← e.symm.map_app s] at hs
      exact hs
  · obtain ⟨e⟩ := he
    let s : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K := Pi.single (Sum.inl ⟨0, by omega⟩) 1
    have hs : quadMinus n K b c s = 0 := by
      rw [quadMinus_apply]
      simp [s, Pi.single_apply]
    have hs0 : s ≠ 0 := fun h => by
      have := congrFun h (Sum.inl ⟨0, by omega⟩)
      simp [s] at this
    refine ⟨e.symm s, fun h => hs0 ?_, ?_⟩
    · simpa using congrArg e h
    · rw [← e.symm.map_app s] at hs
      exact hs

end Singular

section Supp

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem othersSpace_le_suppPerp (hx : OddOrderIsometry Q p x) :
    othersSpace x.toLinearMap (X - 1) ≤ suppPerp Q (fixedSpace x) := fun r hr =>
  mem_suppPerp.mpr fun w hw => hx.fixed_others.2 w hw r hr

theorem supportedDerived_le_supportedFixedDerived (hx : OddOrderIsometry Q p x) :
    supportedDerived Q (fixedSpace x) ≤ supportedFixedDerived Q x := by
  intro g hg
  have hWnd : PolarNondegOn Q (fixedSpace x) :=
    polarNondegOn_of_nondegenerate hx.polarBilin_fixed_nondegenerate
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    supportedDerived_le_orthogonalGroup hWnd hg
  have hgR : ∀ r ∈ othersSpace x.toLinearMap (X - 1), g r = r := fun r hr =>
    supportedDerived_apply_perp hg (othersSpace_le_suppPerp hx hr)
  have hxc : x ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hcomm : ∀ v, g (x v) = x (g v) := by
    intro v
    obtain ⟨w, hw, r, hr, rfl⟩ := exists_add_of_isCompl hx.fixed_others.1 v
    have hxw : x w = w := mem_fixedSpace.mp hw
    have hxr : x r ∈ othersSpace x.toLinearMap (X - 1) := mem_othersSpace_of_apply hxc hr
    have hgw : g w ∈ fixedSpace x := supportedDerived_apply_mem hg hw
    simp only [map_add, hxw, hgR r hr, hgR (x r) hxr, mem_fixedSpace.mp hgw]
  have hblock : g ∈ supportedBlock Q x (X - 1) :=
    mem_supportedBlock.mpr ⟨mem_isometryCentralizer.mpr
      ⟨fun v => TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hgO v, hcomm⟩, hgR⟩
  refine mem_supportedFixedDerived.mpr ⟨hblock, ?_⟩
  obtain ⟨-, h, hh, e⟩ := hg
  have : restrictFixed Q x ⟨g, hblock⟩ = h :=
    LinearEquiv.ext fun w => Subtype.ext (by rw [coe_restrictFixed]; exact (e w).symm)
  rw [this]
  exact hh

end Supp

section Commute

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem KCOrthogonal.OddOrderIsometry.fixed_scalar_data (hx : OddOrderIsometry Q p x)
    (hK : 4 ≤ Nat.card K) (h4 : 4 ≤ finrank K (fixedSpace x)) :
    (∃ e ∈ fixedSpace x, e ≠ 0 ∧ Q e = 0) ∧ ElementaryMapsMem Q (fixedSpace x) := by
  have hWnd := hx.polarBilin_fixed_nondegenerate
  obtain ⟨k, hk⟩ := hx.even_finrank_fixed
  obtain ⟨e, he0, hQe⟩ := exists_singular_of_even_regular (Q.comp (fixedSpace x).subtype) hWnd
    (n := k) (by omega) (by omega)
  exact ⟨⟨e, e.2, fun h => he0 (Subtype.ext h), hQe⟩,
    elementaryMapsMem_of_regular hWnd (by omega) (fun h => absurd h (by omega))⟩

theorem KCOrthogonal.OddOrderIsometry.fixes_of_commute (hx : OddOrderIsometry Q p x)
    (hQ : (polarBilin Q).Nondegenerate) (hK : 4 ≤ Nat.card K)
    (h4 : 4 ≤ finrank K (fixedSpace x)) {g : V ≃ₗ[K] V} (hg : g ∈ isometryCentralizer Q x)
    (hcomm : ∀ f ∈ supportedFixedDerived Q x, ∀ v, g (f v) = f (g v)) :
    ∀ w ∈ fixedSpace x, g w = w := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hWnd := hx.polarBilin_fixed_nondegenerate
  have h3 : 3 ≤ finrank K (fixedSpace x) := by omega
  obtain ⟨k, hk⟩ := hx.even_finrank_fixed
  obtain ⟨e, he0, hQe⟩ := exists_singular_of_even_regular (Q.comp (fixedSpace x).subtype) hWnd
    (n := k) (by omega) (by omega)
  have hsing : ∃ e ∈ fixedSpace x, e ≠ 0 ∧ Q e = 0 :=
    ⟨e, e.2, fun h => he0 (Subtype.ext h), hQe⟩
  have hM : ElementaryMapsMem Q (fixedSpace x) :=
    elementaryMapsMem_of_regular hWnd h3 (fun h => absurd h (by omega))
  have hgQ : ∀ v, Q (g.toAddEquiv v) = (1 : K) * (RingEquiv.refl K) (Q v) := fun v => by
    rw [one_mul]
    exact (mem_isometryCentralizer.mp hg).1 v
  have hcomm' : ∀ g' ∈ supportedDerived Q (fixedSpace x), ∀ v,
      g.toAddEquiv (g' v) = g' (g.toAddEquiv v) := fun g' hg' v =>
    hcomm g' (supportedDerived_le_supportedFixedDerived hx hg') v
  obtain ⟨-, c, hc0, hc⟩ := scalar_restriction_of_commute g.toAddEquiv (RingEquiv.refl K) 1 hgQ
    hcomm' hQ hWnd h3 hsing hM (fun c v => by simp)
  have : Nontrivial (fixedSpace x) := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨w₁, hw₁⟩ := exists_map_ne_zero hWnd
  have hcc : c * c = 1 := by
    have h1 := (mem_isometryCentralizer.mp hg).1 (w₁ : V)
    have h5 : g (w₁ : V) = c • (w₁ : V) := hc w₁ w₁.2
    rw [h5, QuadraticMap.map_smul, smul_eq_mul] at h1
    have h6 : (Q.comp (fixedSpace x).subtype) w₁ = Q (w₁ : V) := rfl
    rw [h6] at hw₁
    exact mul_right_cancel₀ hw₁ (by rw [one_mul]; exact h1)
  have hc1 : c = 1 := by
    have h8 : (c - 1) ^ 2 = 0 := by
      have : (c - 1) ^ 2 = c * c - 1 - 2 * (c - 1) := by ring
      rw [this, hcc, h2]
      ring
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h8)
  intro w hw
  have h5 : g w = c • w := hc w hw
  rw [h5, hc1, one_smul]

end Commute

end CFSG.RankThree.PartOne

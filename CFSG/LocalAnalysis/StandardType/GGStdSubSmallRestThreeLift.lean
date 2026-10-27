module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestThreeNorm
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestLift
public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSURepairBlock
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeLift

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGStdSubTwoTorusEltNormSmall (p r : ℕ) (R : Type) [Group R] : Prop :=
  ∀ A : Subgroup R, IsElemAbelian p A → p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A →
    (∃ U : Subgroup R, U ≠ ⊥ ∧ IsPGroup 2 U ∧ A ≤ Subgroup.normalizer (U : Set R)) →
    ∀ a ∈ A, a ≠ 1 → ∀ D : Subgroup R, D ≤ Subgroup.centralizer ({a} : Set R) →
      (∀ c ∈ Subgroup.centralizer ({a} : Set R), ∀ d ∈ D, c * d * c⁻¹ ∈ D) →
      CFSG.IsQuasisimple D → (∀ b ∈ A, (∀ d ∈ D, b * d = d * b) → b ∈ Subgroup.zpowers a) →
      (∀ E : Subgroup R, IsElemAbelian p E → E ≤ D → E ≤ A → Nat.card E < p ^ 3) →
      ∃ U : Subgroup R, U ≤ D ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧ (∀ s ∈ A, ∀ u ∈ U, s * u * s⁻¹ ∈ U) ∧
        ∃ t ∈ D, t ^ p = 1 ∧ (∀ s ∈ A, s * t = t * s) ∧ t ∈ Subgroup.normalizer (U : Set R) ∧
          ∃ j ∈ D, t * j ≠ j * t

namespace StdSubRestThree

section LiftElem

variable {L' R : Type} [Group L'] [Group R] {ψ : L' →* R}

@[expose] def liftElem (hker : ψ.ker ≤ Subgroup.center L') {p : ℕ}
    (hnp : ∀ z ∈ ψ.ker, z ^ p = 1 → z = 1) (K : Subgroup L') (E : Subgroup R)
    (hE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) : Subgroup L' where
  carrier := {y | y ∈ K ∧ y ^ p = 1 ∧ ψ y ∈ E}
  mul_mem' := by
    rintro y₁ y₂ ⟨h1K, h1p, h1E⟩ ⟨h2K, h2p, h2E⟩
    have hc : y₂ * y₁ = y₁ * y₂ :=
      StdSubRest.commute_of_noTorsion hker hnp h1p (hE _ h1E _ h2E)
    refine ⟨K.mul_mem h1K h2K, ?_, by rw [map_mul]; exact E.mul_mem h1E h2E⟩
    rw [(Commute.mul_pow hc.symm), h1p, h2p, one_mul]
  one_mem' := ⟨K.one_mem, one_pow _, by rw [map_one]; exact E.one_mem⟩
  inv_mem' := by
    rintro y ⟨hK, hp, hE'⟩
    exact ⟨K.inv_mem hK, by rw [inv_pow, hp, inv_one], by rw [map_inv]; exact E.inv_mem hE'⟩

theorem isElemAbelian_liftElem (hker : ψ.ker ≤ Subgroup.center L') {p : ℕ}
    (hnp : ∀ z ∈ ψ.ker, z ^ p = 1 → z = 1) (K : Subgroup L') (E : Subgroup R)
    (hE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) : IsElemAbelian p (liftElem hker hnp K E hE) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => hy.2.1⟩
  exact (StdSubRest.commute_of_noTorsion hker hnp a.2.2.1 (hE _ a.2.2.2 _ b.2.2.2)).symm

theorem card_le_card_liftElem [Finite L'] (hker : ψ.ker ≤ Subgroup.center L') {p : ℕ}
    (hp : p.Prime) (hnp : ∀ z ∈ ψ.ker, z ^ p = 1 → z = 1) (K : Subgroup L') (E : Subgroup R)
    (hE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hEp : ∀ x ∈ E, x ^ p = 1) (hEK : E ≤ K.map ψ) :
    Nat.card E ≤ Nat.card (liftElem hker hnp K E hE) := by
  let f : liftElem hker hnp K E hE → E := fun y => ⟨ψ y, y.2.2.2⟩
  have hf : Function.Surjective f := by
    rintro ⟨e, he⟩
    obtain ⟨x, hxK, hx⟩ := hEK he
    obtain ⟨k, hk, hkp⟩ := StdSubRest.exists_lift_pow_eq_one_of_noTorsion hp hnp (hEp e he) hx
    exact ⟨⟨x ^ k, K.pow_mem hxK k, hkp, hk ▸ he⟩, Subtype.ext hk⟩
  exact Nat.card_le_card_of_surjective f hf

end LiftElem

theorem conj_mem_largeEvenLayer {L' : Type} [Group L'] {C : Subgroup L'} {g : L'}
    (hg : ∀ y ∈ C, g * y * g⁻¹ ∈ C) (hg' : ∀ y ∈ C, g⁻¹ * y * g ∈ C) {e : L'}
    (he : e ∈ LargeEvenLayer C) : g * e * g⁻¹ ∈ LargeEvenLayer C := by
  have hCmap : C.map (MulAut.conj g).toMonoidHom = C := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact hg y hy
    · intro y hy
      refine ⟨g⁻¹ * y * g, hg' y hy, ?_⟩
      show g * (g⁻¹ * y * g) * g⁻¹ = y
      group
  have h1 := largeEvenLayer_map_of_injective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective C
  rw [hCmap] at h1
  rw [h1]
  exact ⟨e, he, rfl⟩

end StdSubRestThree

open TableBSymp StdSubSp StdSubRest StdSubRestThree in
theorem ggStdSubTwoTorusNormSmall_of_elt {p r : ℕ} (hp : p.Prime) {R : Type} [Group R]
    {I : Set (MulAut R)} (hI : GGOutdiagPrime p R I) (hZ : Subgroup.center R = ⊥)
    (hZp : GGCenterPrime p R) (h : GGStdSubTwoTorusEltNormSmall p r R) :
    GGStdSubTwoTorusNormSmall p r R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hα a haA ha1 hEcomp hcentA hsmall
  have := Fact.mk hp
  have hAI' : ∀ a ∈ A, ∃ φ ∈ {φ : MulAut R | φ ∈ I ∧ φ ^ p = 1}, ∀ l : L',
      φ (ψ l) = ψ (a l) := by
    intro a ha
    obtain ⟨φ, hφI, hφ⟩ := hAI a ha
    refine ⟨φ, ⟨hφI, ?_⟩, hφ⟩
    ext x
    obtain ⟨l, rfl⟩ := hψ x
    rw [pow_apply_comp_eq hφ p l, hA.2 a ha, MulAut.one_apply, MulAut.one_apply]
  obtain ⟨χ, hχinj, hinner⟩ := exists_inducedHom (I := {φ : MulAut R | φ ∈ I ∧ φ ^ p = 1})
    (fun φ hφ => hI φ hφ.1 hφ.2) hZ hψ hker hperf hAI'
  set Ab := χ.range with hAb
  have hAbA : IsElemAbelian p Ab := isElemAbelian_range
    (fun a b => Subtype.ext (TableB.IsElemAbelian.comm hA a.2 b.2))
    (fun a => Subtype.ext (by simpa using hA.2 a a.2)) χ
  have hcardAb : Nat.card Ab = Nat.card A :=
    (Nat.card_congr (MonoidHom.ofInjective hχinj).toEquiv).symm
  have hlift : ∀ a' : A, ∃ s : L', ψ s = χ a' ∧ ∀ l, (a' : MulAut L') l = s * l * s⁻¹ := by
    intro a'
    obtain ⟨s, hs⟩ := hψ (χ a')
    exact ⟨s, hs, hinner a' s hs⟩
  have hUAb : ∃ U : Subgroup R, U ≠ ⊥ ∧ IsPGroup 2 U ∧ Ab ≤ Subgroup.normalizer (U : Set R) := by
    obtain ⟨U, hU1, hU2, hAU⟩ := hα
    refine ⟨U, hU1, hU2, ?_⟩
    rw [Subgroup.le_normalizer_iff]
    rintro _ ⟨b, rfl⟩ u hu
    obtain ⟨l, rfl⟩ := hψ u
    obtain ⟨s, hs, hsb⟩ := hlift b
    have h1 := hAU b b.2 l hu
    rw [hsb, map_mul, map_mul, map_inv, hs] at h1
    exact h1
  set a₀ : A := ⟨a, haA⟩ with ha₀def
  have hnp := noTorsion_of_centerPrime hp hZp hψ hker hperf
  have hχp : (χ a₀) ^ p = 1 := by
    rw [← map_pow]
    have h1 : a₀ ^ p = 1 := Subtype.ext (by simpa using hA.2 a haA)
    rw [h1, map_one]
  obtain ⟨t₁, ht₁⟩ := hψ (χ a₀)
  obtain ⟨k₀, hk₀, htp'⟩ := exists_lift_pow_eq_one_of_noTorsion hp hnp hχp ht₁
  set t' := t₁ ^ k₀ with ht'def
  have ht' : ψ t' = χ a₀ := hk₀
  have ha₀ := hinner a₀ t' ht'
  have hfix : ggFix a = Subgroup.centralizer ({t'} : Set L') := by
    ext l
    rw [mem_ggFix, show a = (a₀ : MulAut L') from rfl, ha₀,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hl
      calc l * t' = t' * l * t'⁻¹ * t' := by rw [hl]
        _ = t' * l := by group
    · intro hl
      rw [← hl]
      group
  set C := Subgroup.centralizer ({t'} : Set L') with hC
  set E := LargeEvenLayer (ggFix a) with hE
  have hEC : E = LargeEvenLayer C := by rw [hE, hfix]
  have hEcomp' : IsComponentOf E C := by
    rw [← hfix]
    exact hEcomp
  have hχa₁ : χ a₀ ≠ 1 := by
    intro h1
    apply ha1
    have h2 : a₀ = 1 := hχinj (by rw [h1, map_one])
    exact congrArg Subtype.val h2
  have hEn : ∀ g : L', (∀ y ∈ C, g * y * g⁻¹ ∈ C) → (∀ y ∈ C, g⁻¹ * y * g ∈ C) →
      ∀ e ∈ E, g * e * g⁻¹ ∈ E := by
    intro g hg hg' e he
    rw [hEC] at he ⊢
    exact conj_mem_largeEvenLayer hg hg' he
  have hEnC : ∀ g ∈ C, ∀ e ∈ E, g * e * g⁻¹ ∈ E := fun g hg =>
    hEn g (fun y hy => C.mul_mem (C.mul_mem hg hy) (C.inv_mem hg))
      (fun y hy => C.mul_mem (C.mul_mem (C.inv_mem hg) hy) hg)
  have hAfixC : ∀ a' ∈ A, ∀ y ∈ C, (a' : MulAut L') y ∈ C := by
    intro a' ha' y hy
    rw [← hfix, mem_ggFix] at hy ⊢
    have hc : a' * a = a * a' := TableB.IsElemAbelian.comm hA ha' haA
    calc a (a' y) = (a * a') y := rfl
      _ = (a' * a) y := by rw [hc]
      _ = a' (a y) := rfl
      _ = a' y := by rw [hy]
  have hsE : ∀ a' : A, ∀ s : L', (∀ l, (a' : MulAut L') l = s * l * s⁻¹) →
      ∀ e ∈ E, s * e * s⁻¹ ∈ E := by
    intro a' s hsa
    refine hEn s (fun y hy => ?_) (fun y hy => ?_)
    · rw [← hsa]
      exact hAfixC a' a'.2 y hy
    · have h1 := hAfixC (a'⁻¹ : A) (a'⁻¹).2 y hy
      have h2 : ((a'⁻¹ : A) : MulAut L') y = s⁻¹ * y * s := by
        have h3 : (a' : MulAut L') (s⁻¹ * y * s) = y := by rw [hsa]; group
        calc ((a'⁻¹ : A) : MulAut L') y
            = ((a' : MulAut L')⁻¹) ((a' : MulAut L') (s⁻¹ * y * s)) := by rw [h3]; rfl
          _ = s⁻¹ * y * s := (a' : MulAut L').symm_apply_apply _
      rwa [h2] at h1
  set D := E.map ψ with hD
  have hEq : CFSG.IsQuasisimple E := (isQuasisimple_iff _).mp hEcomp'.2.2
  have hEperf : ⁅E, E⁆ = E := Subgroup.isPerfect_iff.1 hEq.1
  have hDq : CFSG.IsQuasisimple D :=
    (isQuasisimple_iff _).mp (SURepair.isQuasisimple_map_of_isQuasisimple hker hEq)
  have hDC : D ≤ Subgroup.centralizer ({χ a₀} : Set R) := by
    rintro _ ⟨e, he, rfl⟩
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hEcomp'.1 he)
    rw [Subgroup.mem_centralizer_singleton_iff, ← ht', ← map_mul, ← map_mul, h1]
  have hCR := TableBUE.centralizer_map_eq_of_noTorsion ψ hψ hker hnp htp'
  have hDn : ∀ c ∈ Subgroup.centralizer ({χ a₀} : Set R), ∀ d ∈ D, c * d * c⁻¹ ∈ D := by
    intro c hc d hd
    rw [← ht', hCR] at hc
    obtain ⟨g, hg, rfl⟩ := hc
    obtain ⟨e, he, rfl⟩ := hd
    exact ⟨g * e * g⁻¹, hEnC g hg e he, by simp only [map_mul, map_inv]⟩
  have hprov : ∀ b ∈ Ab, (∀ d ∈ D, b * d = d * b) → b ∈ Subgroup.zpowers (χ a₀) := by
    rintro _ ⟨b₀, rfl⟩ hb
    obtain ⟨s, hs, hsb⟩ := hlift b₀
    have hfixE : ∀ j ∈ E, (b₀ : MulAut L') j = j := by
      intro j hj
      rw [hsb]
      have hjK : j ∈ ⁅E, E⁆ := hEperf.symm ▸ hj
      have hcomm := commute_of_mem_commutator (x := s) (Y := E) (fun y hy => hker (by
        rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hs,
          hb _ ⟨y, hy, rfl⟩]
        group)) hjK
      rw [hcomm]
      group
    have hmem := (hcentA b₀ b₀.2).mp hfixE
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
    have h2 : a₀ ^ n = b₀ := Subtype.ext (by simpa using hn)
    rw [← map_zpow, h2]
  have hDsmall : ∀ E₁ : Subgroup R, IsElemAbelian p E₁ → E₁ ≤ D → E₁ ≤ Ab →
      Nat.card E₁ < p ^ 3 := by
    intro E₁ hE₁ hE₁D hE₁A
    have hcomm : ∀ x ∈ E₁, ∀ y ∈ E₁, x * y = y * x := fun x hx y hy =>
      TableB.IsElemAbelian.comm hE₁ hx hy
    have h1 := card_le_card_liftElem hker hp hnp E E₁ hcomm hE₁.2 hE₁D
    refine h1.trans_lt (hsmall _ (isElemAbelian_liftElem hker hnp E E₁ hcomm)
      (fun y hy => hy.1) ?_ (Or.inl ?_))
    · intro a' ha' e he
      obtain ⟨s, hs, hsa⟩ := hlift ⟨a', ha'⟩
      rw [show a' = ((⟨a', ha'⟩ : A) : MulAut L') from rfl, hsa]
      have hse : s * e = e * s := by
        refine commute_of_noTorsion hker hnp he.2.1 ?_
        rw [hs]
        exact TableB.IsElemAbelian.comm hAbA (hE₁A he.2.2) ⟨_, rfl⟩
      rw [hse]
      group
    · intro e he
      obtain ⟨b₀, hb₀⟩ := hE₁A he.2.2
      have h2 := hinner b₀ e hb₀.symm
      have h3 : MulAut.conj e = (b₀ : MulAut L') := by
        ext l
        rw [MulAut.conj_apply, h2]
      rw [h3]
      exact b₀.2
  obtain ⟨Ub, hUbD, hUb1, hUb2, hAUb, tb, htbD, htbp, htbA, htbU, jb, hjbD, hjb⟩ :=
    h Ab hAbA (hcardAb ▸ hr) (hcardAb ▸ h3) hUAb (χ a₀) ⟨a₀, rfl⟩ hχa₁ D hDC hDn hDq hprov
      hDsmall
  obtain ⟨U, hUE, hU1, hU2, hUn⟩ := exists_twoSubgroup_lift_le hker hUb1 hUb2 hUbD
  obtain ⟨x, hxE, hx⟩ := htbD
  obtain ⟨k, hψt, htp⟩ := exists_lift_pow_eq_one_of_noTorsion hp hnp htbp hx
  have htE : x ^ k ∈ E := Subgroup.pow_mem _ hxE k
  have htcomm : ∀ a' : A, ∀ s : L', ψ s = χ a' → s * x ^ k = x ^ k * s := by
    intro a' s hs
    refine commute_of_noTorsion hker hnp htp ?_
    rw [hψt, hs]
    exact (htbA _ ⟨a', rfl⟩).symm
  have hUA : ∀ a' ∈ A, ∀ u ∈ U, a' u ∈ U := by
    intro a' ha' u hu
    obtain ⟨s, hs, hsa⟩ := hlift ⟨a', ha'⟩
    rw [show a' = ((⟨a', ha'⟩ : A) : MulAut L') from rfl, hsa]
    refine hUn s (hsE ⟨a', ha'⟩ s hsa) (fun v hv => ?_) u hu
    rw [hs]
    exact hAUb _ ⟨_, rfl⟩ v hv
  have hN : ∀ g : L', g ∈ E → ψ g ∈ Subgroup.normalizer (Ub : Set R) →
      ∀ u ∈ U, g * u * g⁻¹ ∈ U := by
    intro g hgE hgN u hu
    refine hUn g (fun k hk => E.mul_mem (E.mul_mem hgE hk) (E.inv_mem hgE)) (fun v hv => ?_) u hu
    exact (Subgroup.mem_normalizer_iff.mp hgN v).mp hv
  obtain ⟨j, hjE, hj⟩ := hjbD
  refine ⟨U, hU1, hU2, hUE, hUA, x ^ k, htE, htp, fun a' ha' => ?_, ?_, j, hjE,
    fun hcomm => hjb ?_⟩
  · obtain ⟨s, hs, hsa⟩ := hlift ⟨a', ha'⟩
    rw [show a' = ((⟨a', ha'⟩ : A) : MulAut L') from rfl, hsa, htcomm _ s hs]
    group
  · rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · exact hN (x ^ k) htE (hψt ▸ htbU) u
    · intro hu
      have := hN (x ^ k)⁻¹ (E.inv_mem htE)
        (by rw [map_inv, hψt]; exact Subgroup.inv_mem _ htbU) _ hu
      simpa [mul_assoc] using this
  · have := congrArg ψ hcomm
    rwa [map_mul, map_mul, hψt, hj] at this

end CFSG.StandardType

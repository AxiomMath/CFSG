module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthDefs
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestThreeLift

public section

namespace CFSG.StandardType

open CFSG.Assembly

open TableBSymp StdSubSp StdSubRest StdSubRestThree in
theorem ggStdSubTwoTorusInnerSmall_of_elt {p r : ℕ} (hp : p.Prime) {R : Type} [Group R]
    {I : Set (MulAut R)} (hI : GGOutdiagPrime p R I) (hZ : Subgroup.center R = ⊥)
    (hZp : GGCenterPrime p R) (h : GGStdSubTwoTorusEltInnerSmall p r R) :
    GGStdSubTwoTorusInnerSmall p r R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 a haA ha1 hEcomp hcentA hsmall
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
  obtain ⟨tb, htbD, htbA, jb, hjbD, hjb⟩ :=
    h Ab hAbA (hcardAb ▸ hr) (hcardAb ▸ h3) (χ a₀) ⟨a₀, rfl⟩ hχa₁ D hDC hDn hDq hprov hDsmall
  have htbp : tb ^ p = 1 := hAbA.2 tb htbA
  obtain ⟨x, hxE, hx⟩ := htbD
  obtain ⟨k, hψt, htp⟩ := exists_lift_pow_eq_one_of_noTorsion hp hnp htbp hx
  have htE : x ^ k ∈ E := Subgroup.pow_mem _ hxE k
  have htcomm : ∀ a' : A, ∀ s : L', ψ s = χ a' → s * x ^ k = x ^ k * s := by
    intro a' s hs
    refine commute_of_noTorsion hker hnp htp ?_
    rw [hψt, hs]
    exact TableB.IsElemAbelian.comm hAbA htbA ⟨a', rfl⟩
  obtain ⟨a'₀, ha'₀⟩ := htbA
  have hconj : MulAut.conj (x ^ k) = (a'₀ : MulAut L') := by
    have h2 := hinner a'₀ (x ^ k) (hψt.trans ha'₀.symm)
    ext l
    rw [MulAut.conj_apply, h2]
  obtain ⟨j, hjE, hj⟩ := hjbD
  refine ⟨x ^ k, htE, htp, fun a' ha' => ?_, ?_, j, hjE, fun hcomm => hjb ?_⟩
  · obtain ⟨s, hs, hsa⟩ := hlift ⟨a', ha'⟩
    rw [show a' = ((⟨a', ha'⟩ : A) : MulAut L') from rfl, hsa, htcomm _ s hs]
    group
  · rw [hconj]
    exact a'₀.2
  · have := congrArg ψ hcomm
    rwa [map_mul, map_mul, hψt, hj] at this

end CFSG.StandardType

end

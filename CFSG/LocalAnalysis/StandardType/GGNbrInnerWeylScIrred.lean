module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylOpenLabels
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUElt
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflInner
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndModel
public import CFSG.LocalAnalysis.StandardType.GGInnLocalDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBTwDThree
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylClauseFive

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB TypeA

theorem ggTorusNoLine_of_card_lt {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hX : ∀ X : Subgroup (MulAut R), (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X →
      Nat.card X < p ^ 3) : GGTorusNoLine p r R I := by
  classical
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hsc
  exfalso
  have hXA : IsElemAbelian p (inducedSub ψ A) := isElemAbelian_inducedSub hψ hA
  have hXI : ((inducedSub ψ A : Subgroup (MulAut R)) : Set (MulAut R)) ⊆ I := by
    rintro x ⟨a, ha, hxa⟩
    obtain ⟨φa, hφaI, hφa⟩ := hAI a ha
    exact induced_unique ψ hψ hφa hxa ▸ hφaI
  have hcardX : Nat.card (inducedSub ψ A) = Nat.card A :=
    card_inducedSub hψ hker hperf (fun a ha => by
      obtain ⟨φa, -, hφa⟩ := hAI a ha
      exact ⟨φa, hφa⟩)
  have hlt := hX _ hXI hXA
  rw [hcardX] at hlt
  omega

@[expose] def GGSCNoLine (p r : ℕ) (R : Type) [Group R] : Prop :=
  ∀ E : Subgroup R, IsElemAbelian p E → p ^ r ≤ Nat.card E → p ^ 3 ≤ Nat.card E →
    (∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) →
      ∀ e ∈ E, e ≠ 1 → ∃ g ∈ Subgroup.normalizer (E : Set R), g * e * g⁻¹ ∉ Subgroup.zpowers e

theorem ggTorusNoLine_of_scNoLine {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hp : p.Prime) (hZ : Subgroup.center R = ⊥)
    (hIp : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hcp : GGCenterPrime p R) (h : GGSCNoLine p r R) : GGTorusNoLine p r R I := by
  classical
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hsc
  have hcpL := hcp L' ψ hψ hker hperf
  obtain ⟨Λ, hΛeq, hΛinj, hΛmap⟩ : ∃ Λ : R →* MulAut L',
      (∀ {e : R} {x : L'}, ψ x = e → Λ e = MulAut.conj x) ∧ Function.Injective Λ ∧
      (∀ e l, ψ (Λ e l) = e * ψ l * e⁻¹) :=
    ⟨ReflInner.liftConj ψ hψ hker, fun hx => ReflInner.liftConj_eq hψ hker hx,
      ReflInner.liftConj_injective hψ hker hZ, ReflInner.map_liftConj_apply hψ hker⟩
  have hΛn : ∀ n : L', Λ (ψ n) = MulAut.conj n := fun n => hΛeq rfl
  have hAΛ : ∀ a ∈ A, ∃ e, Λ e = a := by
    intro a ha
    obtain ⟨φ, hφI, hφ⟩ := hAI a ha
    have hk : ∀ k : ℕ, ∀ l, (φ ^ k) (ψ l) = ψ ((a ^ k) l) := by
      intro k
      induction k with
      | zero => intro l; simp
      | succ k ih =>
        intro l
        rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hφ, ih]
    have hφp : φ ^ p = 1 := by
      refine MulEquiv.ext fun r => ?_
      obtain ⟨l, rfl⟩ := hψ r
      rw [hk, hA.2 a ha]
      rfl
    obtain ⟨e, rfl⟩ := hIp φ hφI hφp
    refine ⟨e, TypeA.mulAut_eq_of_forall ψ hker hperf fun l => ?_⟩
    rw [hΛmap, ← hφ l, MulAut.conj_apply]
  set E : Subgroup R := A.comap Λ with hE
  have hΦbij : Function.Bijective (fun e : E => (⟨Λ e, e.2⟩ : A)) := by
    refine ⟨fun e₁ e₂ h12 => Subtype.ext (hΛinj (congrArg Subtype.val h12)), fun a => ?_⟩
    obtain ⟨e, he⟩ := hAΛ a a.2
    exact ⟨⟨e, show Λ e ∈ A from he ▸ a.2⟩, Subtype.ext he⟩
  have hcardE : Nat.card E = Nat.card A := Nat.card_congr (Equiv.ofBijective _ hΦbij)
  have hEab : IsElemAbelian p E := by
    refine ⟨⟨⟨fun e₁ e₂ => Subtype.ext (hΛinj ?_)⟩⟩, fun e he => hΛinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hA e₁.2 e₂.2
    · rw [map_pow, map_one]
      exact hA.2 _ he
  have hscE : ∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E := by
    intro g hg hgp
    obtain ⟨n, hn, hnp⟩ := exists_lift_pow_eq_one hp hψ hker hcpL hgp
    have hfix : ∀ a ∈ A, a n = n := by
      intro a ha
      obtain ⟨e, rfl⟩ := hAΛ a ha
      have heE : e ∈ E := show Λ e ∈ A from ha
      refine eq_of_lift_pow_eq_one hp hker hcpL ?_ ?_ hnp
      · rw [hΛmap, hn, ← hg e heE, mul_inv_cancel_right]
      · rw [← map_pow, hnp, map_one]
    have h1 := hsc n hfix hnp
    rw [← hΛn, hn] at h1
    exact h1
  have hnorm_of : ∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
      ψ n ∈ Subgroup.normalizer (E : Set R) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff] at hn ⊢
    intro e
    have h1 := hn (Λ e)
    rw [← hΛn, ← map_inv, ← map_mul, ← map_mul] at h1
    exact h1
  have hnorm_to : ∀ n : L', ψ n ∈ Subgroup.normalizer (E : Set R) →
      MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff] at hn ⊢
    intro a
    constructor
    · intro ha
      obtain ⟨e, rfl⟩ := hAΛ a ha
      have h1 := (hn e).mp ha
      rw [← hΛn, ← map_inv, ← map_mul, ← map_mul]
      exact h1
    · intro ha
      obtain ⟨e₁, he₁⟩ := hAΛ _ ha
      have he₁E : e₁ ∈ E := by
        show Λ e₁ ∈ A
        rw [he₁]
        exact ha
      have h2 : (ψ n)⁻¹ * e₁ * ψ n ∈ E := by
        refine (hn _).mpr ?_
        rw [show ψ n * ((ψ n)⁻¹ * e₁ * ψ n) * (ψ n)⁻¹ = e₁ by group]
        exact he₁E
      have h3' : a = Λ ((ψ n)⁻¹ * e₁ * ψ n) := by
        rw [map_mul, map_mul, map_inv, he₁, hΛn]
        group
      rw [h3']
      exact h2
  refine ⟨{n | MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))}, ?_, ?_⟩
  ·
    intro n hn a ha
    obtain ⟨e, rfl⟩ := hAΛ a ha
    have heE : e ∈ E := ha
    have hn' := hnorm_of n hn
    have he'E : ψ n * e * (ψ n)⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hn' e).mp heE
    obtain ⟨x, hx, hxp⟩ := exists_lift_pow_eq_one hp hψ hker hcpL (g := e) (hEab.2 e heE)
    have hlx : Λ e = MulAut.conj x := hΛeq hx
    have hy : ψ (n * x * n⁻¹) = ψ n * e * (ψ n)⁻¹ := by rw [map_mul, map_mul, map_inv, hx]
    have hyp : (n * x * n⁻¹) ^ p = 1 := by rw [conj_pow, hxp, mul_one, mul_inv_cancel]
    have hcomm : x * (n * x * n⁻¹) = (n * x * n⁻¹) * x :=
      commute_of_lift_pow_eq_one hp hker hcpL
        (by rw [hy, hx]; exact TableB.IsElemAbelian.comm hEab heE he'E) hyp
    have hform : n * (Λ e n)⁻¹ = (n * x * n⁻¹) * x⁻¹ := by
      rw [hlx, MulAut.conj_apply]
      group
    refine ⟨?_, fun a' ha' => ?_⟩
    · have hc : Commute (n * x * n⁻¹) x⁻¹ :=
        (show Commute x (n * x * n⁻¹) from hcomm).symm.inv_right
      rw [hform, hc.mul_pow, hyp, inv_pow, hxp, inv_one, mul_one]
    · obtain ⟨e'', rfl⟩ := hAΛ a' ha'
      have he''E : e'' ∈ E := ha'
      obtain ⟨z, hz, hzp⟩ := exists_lift_pow_eq_one hp hψ hker hcpL (g := e'')
        (hEab.2 e'' he''E)
      have hzx : z * x = x * z :=
        commute_of_lift_pow_eq_one hp hker hcpL
          (by rw [hz, hx]; exact TableB.IsElemAbelian.comm hEab he''E heE) hxp
      have hzy : z * (n * x * n⁻¹) = (n * x * n⁻¹) * z :=
        commute_of_lift_pow_eq_one hp hker hcpL
          (by rw [hz, hy]; exact TableB.IsElemAbelian.comm hEab he''E he'E) hyp
      have hcy : Commute z (n * x * n⁻¹) := hzy
      have hcx : Commute z x⁻¹ := (show Commute z x from hzx).inv_right
      rw [hform, hΛeq hz, MulAut.conj_apply, (hcy.mul_right hcx).eq, mul_inv_cancel_right]
  ·
    intro hall a₀ ha₀ ha₁
    obtain ⟨e₀, rfl⟩ := hAΛ a₀ ha₀
    have he₀E : e₀ ∈ E := ha₀
    have he₀1 : e₀ ≠ 1 := fun h1 => ha₁ (by rw [h1, map_one])
    obtain ⟨g, hg, hmv⟩ := h E hEab (by rw [hcardE]; exact hr) (by rw [hcardE]; exact h3) hscE
      e₀ he₀E he₀1
    obtain ⟨n, rfl⟩ := hψ g
    refine ⟨n, hnorm_to n hg, fun hmem => hmv ?_⟩
    have h1 : MulAut.conj n * Λ e₀ * (MulAut.conj n)⁻¹ = Λ (ψ n * e₀ * (ψ n)⁻¹) := by
      rw [← hΛn, ← map_inv, ← map_mul, ← map_mul]
    rw [h1] at hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, hΛinj (by rw [map_zpow]; exact hk)⟩

theorem largeEvenLabelAll_card_lt_twAThree {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hlab : LargeEvenInLambda2 lab) (h : lab.tag = .twA ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, hpq⟩ := h
  dsimp only at ht hl hpq ⊢
  subst ht hl
  have hn : 1 ≤ n := hlab.1
  have hdq : ((4 : ℕ), 2 ^ n) ≠ (3, 2) := by
    intro he
    have h4 : (4 : ℕ) = 3 := congrArg Prod.fst he
    omega
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq'⟩ := hQ
  exact ⟨K, i1, i2, hK, hq', fun X hXI hX =>
    (TwDThree.card_le_of_subset_unitaryConj (TableBU.unitaryFieldData_of_card hK hn) (by norm_num)
      hdq hp hpq hX hXI).trans_lt (Nat.pow_lt_pow_right hp.one_lt (by norm_num))⟩

section Main

theorem ggNbrInnerWeylOn_unitThree : GGNbrInnerWeylOn GGNbrWeylUnitThreeLabel :=
  ggNbrInnerWeylOn_of_labels fun p lab hp hp2 hlab ⟨hpow, ht, hl, hpq⟩ =>
    largeEvenLabelAll_weylInnerKLevel_of_noLine_or
      (largeEvenLabelAll_pow_mem_powMem hp hp2 hlab hpow)
      ((largeEvenLabelAll_card_lt_twAThree hp hlab ⟨ht, hl, hpq⟩).mono
        fun _ _ _ _ hX _ _ => ⟨0, Or.inr rfl, ggTorusNoLine_of_card_lt hX⟩)

end Main

end CFSG.StandardType

end

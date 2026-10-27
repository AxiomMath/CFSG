module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallUnitDvdCount
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallUnitDvdSmall
public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSURepairBlock

public section

namespace CFSG.StandardType.SmallU

open scoped commutatorElement

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.SectionRank.OddCover CFSG.StandardType.LineU CFSG.StandardType.UnitTB CFSG.Assembly
  CFSG.RankThree.Classical CFSG.RankThree.Classical2 CFSG.StandardType.TableBUE

variable {K : Type} [Field K] {n d p : ℕ} {L' : Type} [Group L']
  {φ : ↥(unitarySU 2 n K d) →* L'}

theorem exists_nu_actsU (hM : Model φ) (hd : 3 ≤ d) {A : Subgroup (MulAut L')}
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t) (s₀ : Fin d) :
    ∃ ν : A →* (Fin d → Kˣ), ∀ a : A, ActsU φ (a : MulAut L') (ν a) ∧ ν a s₀ = 1 := by
  obtain ⟨ν, hν⟩ := exists_nu hM hd hdiag s₀
  refine ⟨ν, fun a => ⟨?_, (hν a).2⟩⟩
  obtain ⟨σ, hσ, hact⟩ := ActsU.of_actsDiagU (hν a).1
  have : σ = ν a := funext fun k => Units.ext (hσ k)
  rw [this] at hact
  exact hact

theorem ActsU.ratio_eq' (hM : Model φ) (hd : 3 ≤ d) {a : MulAut L'} {σ τ : Fin d → Kˣ}
    (hσ : ActsU φ a σ) (hτ : ActsU φ a τ) (i j : Fin d) : σ i * (σ j)⁻¹ = τ i * (τ j)⁻¹ := by
  have h := ActsDiagU.ratio_eq hM.field hd hM.ker hσ.actsDiagU hτ.actsDiagU i j
  apply Units.ext
  simpa using h

theorem ActsU.pow_ratio (hM : Model φ) (hd : 3 ≤ d) {a : MulAut L'} {σ : Fin d → Kˣ}
    (hσ : ActsU φ a σ) (hap : a ^ p = 1) (i j : Fin d) : (σ i * (σ j)⁻¹) ^ p = 1 := by
  have h := ActsDiagU.ratio_pow hM.field hd hM.ker hσ.actsDiagU hap i j
  apply Units.ext
  simpa using h

theorem ActsU.eq_one_of_const (hM : Model φ) {a : MulAut L'} {σ : Fin d → Kˣ}
    (hσ : ActsU φ a σ) (i₀ : Fin d) (hc : ∀ i j, σ i = σ j) : a = 1 :=
  ActsDiagU.eq_one_of_const hM.surj hσ.actsDiagU i₀ fun i j => by simp [hc i j]

@[expose] def BigOK (n : ℕ) {d : ℕ} (S : Finset (Fin d)) : Prop :=
  4 ≤ S.card ∨ (2 ≤ n ∧ 2 ≤ S.card)

theorem ker_le_center (hM : Model φ) : φ.ker ≤ Subgroup.center ↥(unitarySU 2 n K d) := by
  intro x hx
  have h := mem_center_of_ker hM (MonoidHom.mem_ker.mp hx)
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext ((Subgroup.mem_center_iff.mp h) g)

theorem isQuasisimple_block [Finite K] (hM : Model φ) {S : Finset (Fin d)} (hbig : BigOK n S) :
    CFSG.Assembly.IsQuasisimple ↥((blockSU S).map φ) := by
  rcases hbig with h4 | ⟨hn2, h2⟩
  · refine SUTorus.isQuasisimple_map_blockSU hM.field (ker_le_center hM) (by omega) fun he => ?_
    have := congrArg Prod.fst he
    simp only at this
    omega
  · exact SURepair.isQuasisimple_map_blockSU_of_two_le hM.field hn2 (ker_le_center hM) h2


theorem card_A_le_of_class [Finite K] [Finite L'] (hM : Model φ) (hd : 3 ≤ d) (hp : p.Prime)
    (hpK : p ∣ Nat.card K - 1) {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian p A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t) {a : MulAut L'} (haA : a ∈ A)
    {σ : Fin d → Kˣ} (hσ : ActsU φ a σ) {S : Finset (Fin d)}
    (hS : ∀ i ∈ S, ∀ j, j ∈ S ↔ σ j = σ i) (hbig : BigOK n S)
    (hEcomp : IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a))
    (hcentA : ∀ a' ∈ A,
      ((∀ j ∈ LargeEvenLayer (ggFix a), a' j = j) ↔ a' ∈ Subgroup.zpowers a))
    {s₀ : Fin d} {T : Finset (Fin d)} (hTS : T ⊆ S)
    (hT : ∀ a' ∈ A, ∀ τ : Fin d → Kˣ, ActsU φ a' τ → ∀ k ∈ T, τ k = τ s₀) :
    Nat.card A ≤ p * p ^ (S.card - T.card) := by
  classical
  haveI : Finite (MulAut L') :=
    Finite.of_injective (fun f : MulAut L' => (f : L' → L')) DFunLike.coe_injective
  obtain ⟨ν, hν⟩ := exists_nu_actsU hM hd hdiag s₀
  have hlayer : LargeEvenLayer (ggFix a) = (blockSU S).map φ :=
    layer_eq_block hM hσ hS (isQuasisimple_block hM hbig) hEcomp
  let a₀ : A := ⟨a, haA⟩
  have hap : ∀ g : A, ((g : MulAut L') ^ p = 1) := fun g => hA.2 g g.2
  have ha₀p : a₀ ^ p = 1 := Subtype.ext (hA.2 a haA)
  refine (card_le_of_restrict (G := A) hp hpK ν (fun g k => ?_) hTS (fun g k hk => ?_)
    (Subgroup.zpowers a₀) (fun g hg => ?_)).trans ?_
  · have := ActsU.pow_ratio hM hd (hν g).1 (hap g) k s₀
    rwa [(hν g).2, inv_one, mul_one] at this
  · rw [hT g g.2 (ν g) (hν g).1 k hk, (hν g).2]
  · have hfix : ∀ j ∈ LargeEvenLayer (ggFix a), (g : MulAut L') j = j := by
      rw [hlayer]
      rintro _ ⟨y, hy, rfl⟩
      refine ActsU.fix_of_const (hν g).1 (fun i hi j hj => ?_) hy
      rw [hg i hi, hg j hj]
    have hmem := (hcentA g g.2).mp hfix
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
    exact Subgroup.mem_zpowers_iff.mpr ⟨m, Subtype.ext hm⟩
  · have h1 : Nat.card (Subgroup.zpowers a₀) ≤ p := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one ha₀p)
    exact Nat.mul_le_mul_right _ h1

theorem exists_bigOK_cls [Finite K] [Finite L'] (hM : Model φ) (hd : 4 ≤ d) (hn : 1 ≤ n)
    {a : MulAut L'} {σ : Fin d → Kˣ} (hσ : ActsU φ a σ)
    (hEcomp : IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a)) :
    ∃ i, BigOK n (cls σ i) := by
  classical
  by_cases hn2 : 2 ≤ n
  · by_cases hinj : Function.Injective σ
    · exact (not_isComponentOf_of_injective hM hσ hinj hEcomp).elim
    · obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hinj
      refine ⟨i, Or.inr ⟨hn2, ?_⟩⟩
      have hsub : ({i, j} : Finset (Fin d)) ⊆ cls σ i := by
        intro k hk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl
        · exact mem_cls.mpr rfl
        · exact mem_cls.mpr hij.symm
      have := Finset.card_le_card hsub
      rwa [Finset.card_pair hne] at this
  · have hn1 : n = 1 := by omega
    subst hn1
    by_contra hno
    push Not at hno
    refine not_isComponentOf_of_small_classes hM hd hσ (fun i => ?_) hEcomp
    have h1 := hno i
    unfold BigOK at h1
    omega

theorem exists_model
    [Finite K] [Finite L'] (hK : Nat.card K = (2 ^ n) ^ 2)
    (hn : 1 ≤ n) (hd : 5 ≤ d) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hpd : p ∣ d)
    (hnd : ¬ (d = 6 ∧ p = 3))
    {ψ : L' →* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ x ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K d))
        (LargeEvenGUSet (Fin d) K (2 ^ n)), ∀ l : L', x (ψ l) = ψ (a l))
    (hr : p ^ (d - 3) ≤ Nat.card A) (h3 : p ^ 3 ≤ Nat.card A) :
    ∃ φ : ↥(unitarySU 2 n K d) →* L', Model φ ∧ ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t := by
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpq
  have hcard : p ^ (d / p + 2) ≤ Nat.card A := card_ge_of_dvd hp hp2 hd hpd hnd hr h3
  have hdnd : (d, n) ≠ (6, 1) := by
    rintro ⟨rfl, rfl⟩
    have h3' : p ∣ 3 := by simpa using hpq
    exact hnd ⟨rfl, (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3'⟩
  obtain ⟨φ, hφs, hφker, hdiag⟩ := exists_diagModel hK hn hd hp hpq hpd
    (unitaryUniversalCover_holds n d K hK hd hdnd) hψ hker hperf hA hAI hcard
  exact ⟨φ, ⟨TableBU.unitaryFieldData_of_card hK hn, hφs, hφker⟩, hdiag⟩

end CFSG.StandardType.SmallU

end

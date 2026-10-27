module

public import CFSG.LocalAnalysis.StandardType.GGRootGenAvoidCoverTorus
public import CFSG.LocalAnalysis.StandardType.GGTorusWeylEltHypCent
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpDefs
import CFSG.LocalAnalysis.StandardType.GGSixStepOneCompDefs
import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicTransfer
import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CBlockAbs
public import CFSG.LocalAnalysis.StandardType.GGLayerChevAdjoint
public import CFSG.LocalAnalysis.StandardType.GGLayerAbelianInd
import CFSG.Assembly.LargeEvenGLABridge
import CFSG.Assembly.OpenBridges
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBaseIso
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FFix
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FSeitzB1
import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
import CFSG.LocalAnalysis.GLTheoremA.S9.Lemma94
import CFSG.LocalAnalysis.GLTheoremA.S9.Lemma95A

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB
open scoped commutatorElement

private theorem commutatorElement_mul_central {G : Type*} [Group G] {z w : G}
    (hz : z ∈ Subgroup.center G) (hw : w ∈ Subgroup.center G) (t s : G) :
    ⁅t * z, s * w⁆ = ⁅t, s⁆ := by
  have hz1 : ∀ x : G, z * x = x * z := fun x => (Subgroup.mem_center_iff.mp hz x).symm
  have hw1 : ∀ x : G, w * x = x * w := fun x => (Subgroup.mem_center_iff.mp hw x).symm
  simp only [commutatorElement_def, mul_inv_rev]
  calc t * z * (s * w) * (z⁻¹ * t⁻¹) * (w⁻¹ * s⁻¹)
      = t * (z * (s * w)) * (z⁻¹ * t⁻¹) * (w⁻¹ * s⁻¹) := by group
    _ = t * ((s * w) * z) * (z⁻¹ * t⁻¹) * (w⁻¹ * s⁻¹) := by rw [hz1 (s * w)]
    _ = t * s * (w * t⁻¹) * (w⁻¹ * s⁻¹) := by group
    _ = t * s * (t⁻¹ * w) * (w⁻¹ * s⁻¹) := by rw [hw1 t⁻¹]
    _ = t * s * t⁻¹ * s⁻¹ := by group

theorem le_largeEvenLayer_ggFix_of_map_le {L' R : Type} [Group L'] [Group R]
    {ψ : L' →* R} (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    {a : MulAut L'} {C : Subgroup R} (hC : ∀ l : L', ψ l ∈ C ↔ ψ (a l) = ψ l)
    {J : Subgroup L'} (hJ : ⁅J, J⁆ = J) (hJC : J.map ψ ≤ LargeEvenLayer C) :
    J ≤ LargeEvenLayer (ggFix a) := by
  set X : Subgroup L' := C.comap ψ with hX
  have hmap : LargeEvenLayer C ≤ (LargeEvenLayer X).map ψ := by
    refine sSup_le fun K hK => ?_
    have hY : X.map ψ ≤ C := by
      rw [hX, Subgroup.map_comap_eq_self_of_surjective hψ]
    have hn : ((X.map ψ).subgroupOf C).Normal := by
      rw [hX, Subgroup.map_comap_eq_self_of_surjective hψ, Subgroup.subgroupOf_self]
      infer_instance
    have hc : ⁅C, C⁆ ≤ X.map ψ := by
      rw [hX, Subgroup.map_comap_eq_self_of_surjective hψ]
      simpa only [sup_idem] using Subgroup.commutator_le_sup C C
    obtain ⟨K', hK', hK'map⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.T123CB.exists_component_lift_of_commutator_le ψ
        (fun g hg => hker hg) hY hn hc (CFSG.Assembly.isComponentOf_iff_open.mp hK)
    rw [← hK'map]
    exact Subgroup.map_mono (le_sSup (CFSG.Assembly.isComponentOf_iff_open.mpr hK'))
  have hJX : J ≤ LargeEvenLayer X := by
    have h := CFSG.RankThree.PartOne.S15K.le_iSup_of_isPerfect_of_map_le (ι := Unit) (Φ := ψ)
      hker (Q := fun _ => LargeEvenLayer X) (F := fun _ => (LargeEvenLayer X).map ψ) (Y := J)
      (fun _ => rfl) hJ (by simpa only [iSup_const] using hJC.trans hmap)
    simpa only [iSup_const] using h
  have hcomm : ⁅X, X⁆ ≤ ggFix a := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hzx : x⁻¹ * a x ∈ Subgroup.center L' := hker (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, ((hC x).1 hx), inv_mul_cancel])
    have hzy : y⁻¹ * a y ∈ Subgroup.center L' := hker (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, ((hC y).1 hy), inv_mul_cancel])
    change a ⁅x, y⁆ = ⁅x, y⁆
    have hax : a x = x * (x⁻¹ * a x) := by group
    have hay : a y = y * (y⁻¹ * a y) := by group
    rw [map_commutatorElement, hax, hay]
    exact commutatorElement_mul_central hzx hzy x y
  have hFX : ggFix a ≤ X := fun l hl => (hC l).2 (congrArg ψ hl)
  refine hJX.trans (sSup_le fun K hK => ?_)
  obtain ⟨hKX, hKsub, hKq⟩ := hK
  have hKperf : ⁅K, K⁆ = K :=
    Subgroup.isPerfect_iff.1 ((TableBSymp.isQuasisimple_iff ↥K).mp hKq).1
  have hKF : K ≤ ggFix a := by
    rw [← hKperf]
    exact (Subgroup.commutator_mono hKX hKX).trans hcomm
  exact le_largeEvenLayer ⟨hKF, LayerCC.isSubnormal_of_le hKsub hKF hFX, hKq⟩

theorem ggTorusRootSL2At_of_coverTorus {p k : ℕ} {L' R G : Type} [Group L'] [Finite L']
    [Group R] [Group G] {ψ : L' →* R} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hZ : Subgroup.center R = ⊥)
    (hkerp : ∀ z ∈ ψ.ker, z ^ p = 1)
    {ι₀ : R →* G} (hι₀ : Function.Injective ι₀)
    {A : Subgroup (MulAut L')} {Φ : A →* Multiplicative (Fin k → ZMod p)}
    (hΦ : Function.Injective Φ) {τ : (Fin k → ZMod p) → G}
    (hτ : ∀ x y, τ (x + y) = τ x * τ y)
    (hconj : ∀ (a : A) (l : L'), ι₀ (ψ ((a : MulAut L') l)) =
      τ (Multiplicative.toAdd (Φ a)) * ι₀ (ψ l) * (τ (Multiplicative.toAdd (Φ a)))⁻¹)
    {T : Subgroup L'} (hTA : ∀ a ∈ A, ∀ x ∈ T, a x = x) (hkerT : ψ.ker ≤ T)
    {ι : Type} {s : ι → (Fin k → ZMod p) → Fin k → ZMod p}
    {r : ι → R} {S : ι → Subgroup R}
    (hr : ∀ i x, ι₀ (r i) * τ x * (ι₀ (r i))⁻¹ = τ (s i x))
    (hinv : ∀ i (a : A),
      s i (s i (Multiplicative.toAdd (Φ a))) = Multiplicative.toAdd (Φ a))
    (hfix : ∀ i, Nat.card {a : A // s i (Multiplicative.toAdd (Φ a)) =
      Multiplicative.toAdd (Φ a)} * p = Nat.card A)
    (hTs : ∀ i (a : A), ∃ x ∈ T, x ^ p = 1 ∧ ∃ b : A, MulAut.conj x = (b : MulAut L') ∧
      Multiplicative.toAdd (Φ b) =
        s i (Multiplicative.toAdd (Φ a)) - Multiplicative.toAdd (Φ a))
    (hrS : ∀ i, r i ∈ S i)
    (hS : ∀ i, IsComponentOf (S i) ((Subgroup.centralizer
      ((fun a : A => τ (Multiplicative.toAdd (Φ a))) ''
        {a | s i (Multiplicative.toAdd (Φ a)) = Multiplicative.toAdd (Φ a)})).comap ι₀))
    (hdvd : ∀ i, p ∣ Nat.card (S i))
    (hall : ∀ φ ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A, GGIsReflection p φ →
      ∃ i, ∀ a : A, Multiplicative.toAdd (Φ (φ a)) = s i (Multiplicative.toAdd (Φ a)))
    (hlay : ∀ i (a : A), s i (Multiplicative.toAdd (Φ a)) = Multiplicative.toAdd (Φ a) →
      S i ≤ LargeEvenLayer
        ((Subgroup.centralizer {τ (Multiplicative.toAdd (Φ a))}).comap ι₀)) :
    ∀ φ ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A, GGIsReflection p φ →
      ∃ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')))
        (J : Subgroup L'), GGTorusWeylElt p A n ∧ ggConjAut A hn = φ ∧ n ∈ J ∧
        IsComponentOf J (ggHypCent A n) ∧ p ∣ Nat.card J ∧
        ∀ (a : MulAut L') (ha : a ∈ A), φ ⟨a, ha⟩ = ⟨a, ha⟩ → n ∈ LargeEvenLayer (ggFix a) := by
  obtain ⟨J, n, hnN, -, hJmap, hnJ, -, hWeyl, -, hΦconj, hcomp, hdvdJ⟩ :=
    exists_lift_of_coverTorus hψ hker hZ hkerp hι₀ hΦ hτ hconj hTA hkerT hr hinv hfix hTs hrS hS
      hdvd
  intro φ hφ hφr
  obtain ⟨i, hi⟩ := hall φ hφ hφr
  have hφeq : ggConjAut A (hnN i) = φ := by
    refine MulEquiv.ext fun a => hΦ (Multiplicative.toAdd.injective ?_)
    rw [hΦconj i a, hi a]
  refine ⟨n i, hnN i, J i, hWeyl i, hφeq, hnJ i, hcomp i, hdvdJ i, ?_⟩
  intro a ha hfixa
  have hsfix : s i (Multiplicative.toAdd (Φ ⟨a, ha⟩)) = Multiplicative.toAdd (Φ ⟨a, ha⟩) := by
    rw [← hi ⟨a, ha⟩, hfixa]
  have hJperf : ⁅J i, J i⁆ = J i :=
    Subgroup.isPerfect_iff.1 ((TableBSymp.isQuasisimple_iff ↥(J i)).mp (hcomp i).2.2).1
  have hC : ∀ l : L', ψ l ∈ (Subgroup.centralizer
      {τ (Multiplicative.toAdd (Φ ⟨a, ha⟩))}).comap ι₀ ↔ ψ (a l) = ψ l := by
    intro l
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    have hc : ι₀ (ψ (a l)) = τ (Multiplicative.toAdd (Φ ⟨a, ha⟩)) * ι₀ (ψ l) *
        (τ (Multiplicative.toAdd (Φ ⟨a, ha⟩)))⁻¹ := hconj ⟨a, ha⟩ l
    constructor
    · intro h
      apply hι₀
      rw [hc, ← h, mul_inv_cancel_right]
    · intro h
      have h' : ι₀ (ψ (a l)) = ι₀ (ψ l) := by rw [h]
      rw [hc] at h'
      calc ι₀ (ψ l) * τ (Multiplicative.toAdd (Φ ⟨a, ha⟩))
          = (τ (Multiplicative.toAdd (Φ ⟨a, ha⟩)) * ι₀ (ψ l) *
              (τ (Multiplicative.toAdd (Φ ⟨a, ha⟩)))⁻¹) *
              τ (Multiplicative.toAdd (Φ ⟨a, ha⟩)) := by rw [h']
        _ = τ (Multiplicative.toAdd (Φ ⟨a, ha⟩)) * ι₀ (ψ l) := by group
  have hJC : (J i).map ψ ≤ LargeEvenLayer ((Subgroup.centralizer
      {τ (Multiplicative.toAdd (Φ ⟨a, ha⟩))}).comap ι₀) := by
    rw [hJmap i]
    exact hlay i ⟨a, ha⟩ hsfix
  exact le_largeEvenLayer_ggFix_of_map_le hψ hker hC hJperf hJC (hnJ i)

theorem ggTorusRootSL2_of_mulEquiv {p r : ℕ} {R R' : Type} [Group R] [Group R']
    (e : R ≃* R') {I : Set (MulAut R)} {I' : Set (MulAut R')}
    (hI : ∀ φ ∈ I, MulAut.congr e φ ∈ I') (h : GGTorusRootSL2 p r R' I') :
    GGTorusRootSL2 p r R I := by
  intro L' _ _ ψ A hTB
  obtain ⟨hψ, hker, hperf, hA, hAI, hr, h3, hsc⟩ := hTB
  have hTB' : GGTorusTBGroup p r R' I' L' (e.toMonoidHom.comp ψ) A := by
    unfold GGTorusTBGroup
    refine ⟨e.surjective.comp hψ, ?_, hperf, hA, ?_, hr, h3, hsc⟩
    · intro l hl
      exact hker (by simpa [MonoidHom.mem_ker] using hl)
    · intro a ha
      obtain ⟨φ, hφ, hφa⟩ := hAI a ha
      exact ⟨MulAut.congr e φ, hI φ hφ, fun l => by simp [MulAut.congr_apply, hφa]⟩
  exact h L' (e.toMonoidHom.comp ψ) A hTB'

section Chev

open CFSG.Yardstones.Md0ec50421ce4


theorem le_largeEvenLayer_ggFix_of_chevSimple {R : Type} [Group R] [Finite R]
    (hS : IsSimpleGroup R) (hnc : ∃ a b : R, a * b ≠ b * a) (hchev : IsChevSimple 2 R)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {α : MulAut R} (hα : α ^ p = 1) {S : Subgroup R}
    (hSperf : ⁅S, S⁆ = S) (hSα : S ≤ ggFix α) : S ≤ LargeEvenLayer (ggFix α) := by
  have hcent : CFSG.LocalAnalysis.GLTheoremA.I142.centFix (Subgroup.zpowers α) = ggFix α := by
    rw [CFSG.LocalAnalysis.GLTheoremA.I142.centFix_zpowers]
    ext x
    rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup]
    rfl
  have hEp : IsPGroup p (Subgroup.zpowers α) := by
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hα) with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  have hEc : ∀ x ∈ Subgroup.zpowers α, ∀ y ∈ Subgroup.zpowers α, x * y = y * x := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [← zpow_add, ← zpow_add, add_comm]
  have hSle : S ≤ CFSG.LocalAnalysis.GLTheoremA.I142.centFix (Subgroup.zpowers α) := by
    rw [hcent]
    exact hSα
  have hmain := LayerAbelian.lieSemisimpleCentAbelian R hS hnc hchev p hp hp2
    (Subgroup.zpowers α) hEp hEc S hSle hSperf
  rw [hcent] at hmain
  rw [CFSG.Assembly.LargeEven.largeEvenLayer_eq_glaLayer]
  exact hmain

theorem ggTorusRootSL2At_of_coverTorus_chev {p k : ℕ} {L' R G : Type} [Group L'] [Finite L']
    [Group R] [Finite R] [Group G] {ψ : L' →* R} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hZ : Subgroup.center R = ⊥)
    (hkerp : ∀ z ∈ ψ.ker, z ^ p = 1)
    {ι₀ : R →* G} (hι₀ : Function.Injective ι₀)
    {A : Subgroup (MulAut L')} {Φ : A →* Multiplicative (Fin k → ZMod p)}
    (hΦ : Function.Injective Φ) {τ : (Fin k → ZMod p) → G}
    (hτ : ∀ x y, τ (x + y) = τ x * τ y)
    (hconj : ∀ (a : A) (l : L'), ι₀ (ψ ((a : MulAut L') l)) =
      τ (Multiplicative.toAdd (Φ a)) * ι₀ (ψ l) * (τ (Multiplicative.toAdd (Φ a)))⁻¹)
    {T : Subgroup L'} (hTA : ∀ a ∈ A, ∀ x ∈ T, a x = x) (hkerT : ψ.ker ≤ T)
    {ι : Type} {s : ι → (Fin k → ZMod p) → Fin k → ZMod p}
    {r : ι → R} {S : ι → Subgroup R}
    (hr : ∀ i x, ι₀ (r i) * τ x * (ι₀ (r i))⁻¹ = τ (s i x))
    (hinv : ∀ i (a : A),
      s i (s i (Multiplicative.toAdd (Φ a))) = Multiplicative.toAdd (Φ a))
    (hfix : ∀ i, Nat.card {a : A // s i (Multiplicative.toAdd (Φ a)) =
      Multiplicative.toAdd (Φ a)} * p = Nat.card A)
    (hTs : ∀ i (a : A), ∃ x ∈ T, x ^ p = 1 ∧ ∃ b : A, MulAut.conj x = (b : MulAut L') ∧
      Multiplicative.toAdd (Φ b) =
        s i (Multiplicative.toAdd (Φ a)) - Multiplicative.toAdd (Φ a))
    (hrS : ∀ i, r i ∈ S i)
    (hS : ∀ i, IsComponentOf (S i) ((Subgroup.centralizer
      ((fun a : A => τ (Multiplicative.toAdd (Φ a))) ''
        {a | s i (Multiplicative.toAdd (Φ a)) = Multiplicative.toAdd (Φ a)})).comap ι₀))
    (hdvd : ∀ i, p ∣ Nat.card (S i))
    (hR : IsSimpleGroup R) (hnc : ∃ a b : R, a * b ≠ b * a) (hchev : IsChevSimple 2 R)
    (hp : p.Prime) (hp2 : p ≠ 2) (hAp : ∀ a ∈ A, a ^ p = 1)
    (hAI : ∀ a ∈ A, ∃ α : MulAut R, ∀ l : L', α (ψ l) = ψ (a l))
    (hall : ∀ φ ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A, GGIsReflection p φ →
      ∃ i, ∀ a : A, Multiplicative.toAdd (Φ (φ a)) = s i (Multiplicative.toAdd (Φ a))) :
    ∀ φ ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A, GGIsReflection p φ →
      ∃ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')))
        (J : Subgroup L'), GGTorusWeylElt p A n ∧ ggConjAut A hn = φ ∧ n ∈ J ∧
        IsComponentOf J (ggHypCent A n) ∧ p ∣ Nat.card J ∧
        ∀ (a : MulAut L') (ha : a ∈ A), φ ⟨a, ha⟩ = ⟨a, ha⟩ → n ∈ LargeEvenLayer (ggFix a) := by
  refine ggTorusRootSL2At_of_coverTorus hψ hker hZ hkerp hι₀ hΦ hτ hconj hTA hkerT hr hinv hfix
    hTs hrS hS hdvd hall ?_
  intro i a hsa
  obtain ⟨α, hα⟩ := hAI a a.2
  have hCeq : (Subgroup.centralizer {τ (Multiplicative.toAdd (Φ a))}).comap ι₀ = ggFix α := by
    ext x
    obtain ⟨l, rfl⟩ := hψ x
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, mem_ggFix, hα]
    have hc := hconj a l
    constructor
    · intro h
      apply hι₀
      rw [hc, ← h, mul_inv_cancel_right]
    · intro h
      have h' : ι₀ (ψ ((a : MulAut L') l)) = ι₀ (ψ l) := by rw [h]
      rw [hc] at h'
      calc ι₀ (ψ l) * τ (Multiplicative.toAdd (Φ a))
          = (τ (Multiplicative.toAdd (Φ a)) * ι₀ (ψ l) * (τ (Multiplicative.toAdd (Φ a)))⁻¹) *
              τ (Multiplicative.toAdd (Φ a)) := by rw [h']
        _ = τ (Multiplicative.toAdd (Φ a)) * ι₀ (ψ l) := by group
  have hαp : α ^ p = 1 := by
    have hk : ∀ m : ℕ, ∀ l, (α ^ m) (ψ l) = ψ (((a : MulAut L') ^ m) l) := by
      intro m
      induction m with
      | zero => intro l; simp
      | succ m ih =>
        intro l
        rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hα, ih]
    refine MulEquiv.ext fun x => ?_
    obtain ⟨l, rfl⟩ := hψ x
    rw [hk, hAp a a.2]
    rfl
  have hSα : S i ≤ ggFix α := by
    rw [← hCeq]
    intro x hx
    have hxc := (hS i).1 hx
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at hxc
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    exact (hxc _ ⟨a, hsa, rfl⟩).symm
  have hSperf : ⁅S i, S i⁆ = S i :=
    Subgroup.isPerfect_iff.1 ((TableBSymp.isQuasisimple_iff ↥(S i)).mp (hS i).2.2).1
  rw [hCeq]
  exact le_largeEvenLayer_ggFix_of_chevSimple hR hnc hchev hp hp2 hαp hSperf hSα

theorem rootSL2_of_two_pow_of_induced_component
    {L' R : Type} [Group L'] [Finite L'] [Group R] [Finite R]
    {ψ : L' →* R} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (hZ : Subgroup.center R = ⊥) (hodd : ∀ z ∈ ψ.ker, Odd (orderOf z))
    (hR : IsSimpleGroup R) (hnc : ∃ a b : R, a * b ≠ b * a)
    (hchev : IsChevSimple 2 R) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ α : MulAut R, ∀ l, α (ψ l) = ψ (a l))
    {n : L'} (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (hrefl : GGIsReflection p (ggConjAut A hn)) {k : ℕ} (hn2 : n ^ (2 ^ k) = 1)
    {JR : Subgroup R} (hJR : IsComponentOf JR (ggHypCent (TypeA.inducedSub ψ A) (ψ n)))
    (hnJR : ψ n ∈ JR) :
    ∃ J : Subgroup L', n ∈ J ∧ IsComponentOf J (ggHypCent A n) ∧ p ∣ Nat.card J ∧
      GGTorusWeylElt p A n ∧
      ∀ (a : MulAut L') (ha : a ∈ A), ggConjAut A hn ⟨a, ha⟩ = ⟨a, ha⟩ →
        n ∈ LargeEvenLayer (ggFix a) := by
  classical
  let AR := TypeA.inducedSub ψ A
  let e := TypeA.inducedSubEquiv hψ hker hperf hAI
  have he : ∀ (a : A) (l : L'), (e a).1 (ψ l) = ψ (a.1 l) :=
    TypeA.inducedSubEquiv_apply hψ hker hperf hAI
  have hm := conj_mem_normalizer_inducedSub ψ hn
  let J := ⁅JR.comap ψ, JR.comap ψ⁆
  have hcomp : IsComponentOf J (ggHypCent A n) ∧ J.map ψ = JR :=
    isComponentOf_commutator_comap_ggHypCent hψ hker
    (fun α hα => TypeA.mem_inducedSub.mp hα) e he hn hm
    (inducedSubEquiv_ggConjAut hψ hker hperf hAI rfl hn hm) hJR
  have hJRperf : ⁅JR, JR⁆ = JR :=
    Subgroup.isPerfect_iff.mp ((TableBSymp.isQuasisimple_iff _).mp hJR.2.2).1
  have hnJ : n ∈ J := mem_commutator_comap_of_pow_two_pow hψ hker hodd hJRperf hnJR hn2
  have hW : GGTorusWeylElt p A n := ggTorusWeylElt_of_mem_ggHypCent hp hp2 hA hn hrefl
    (mem_ggHypCent_of_pow_two_pow A (fun z hz => hodd z (ψ.center_le_ker hψ hZ hz)) hn2)
  refine ⟨J, hnJ, hcomp.1, ?_, hW, ?_⟩
  · exact prime_dvd_card_of_isSubnormal_ggHypCent_of_mem hp hp2 hA hn hrefl
      hcomp.1.2.1 hnJ
  · intro a ha hfix
    obtain ⟨α, hα⟩ := hAI a ha
    have hJRα : JR ≤ ggFix α := by
      intro r hr
      have hcentr : MulAut.conj (ψ n) * α = α * MulAut.conj (ψ n) := by
        have hf := inducedSubEquiv_ggConjAut hψ hker hperf hAI rfl hn hm ⟨a, ha⟩
        rw [hfix] at hf
        have hαe : (e ⟨a, ha⟩).1 = α := TypeA.induced_unique ψ hψ (he ⟨a, ha⟩) hα
        have hx := congrArg Subtype.val hf
        rw [ggConjAut_apply, hαe] at hx
        exact (mul_inv_eq_iff_eq_mul).mp hx.symm
      exact Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp (hJR.1 hr) α) ⟨⟨a, ha, hα⟩, hcentr⟩
    have hlay : JR ≤ LargeEvenLayer (ggFix α) :=
      le_largeEvenLayer_ggFix_of_chevSimple hR hnc hchev hp hp2
        (TypeA.induced_unique ψ hψ (TypeA.induced_pow ψ hα p) (by
          rw [hA.2 a ha]; exact fun _ => rfl)) hJRperf hJRα
    have hC : ∀ l : L', ψ l ∈ ggFix α ↔ ψ (a l) = ψ l := by
      intro l
      rw [mem_ggFix, hα]
    have hJlay : J.map ψ ≤ LargeEvenLayer (ggFix α) := by rw [hcomp.2]; exact hlay
    exact le_largeEvenLayer_ggFix_of_map_le (J := J) hψ hker hC
      (SCFourCover.commutator_eq_self_of_isComponentOf hcomp.1)
      hJlay hnJ

end Chev

end CFSG.StandardType

end

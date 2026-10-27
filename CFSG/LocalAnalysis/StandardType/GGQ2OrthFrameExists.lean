module

public import CFSG.LocalAnalysis.StandardType.GGQ2OrthFrame
import CFSG.LocalAnalysis.StandardType.GGQ2OrthPlaneForm
import CFSG.LocalAnalysis.StandardType.GGQ2OrthTauMemOmega
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorusCore
import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOrthNsConj
import CFSG.LocalAnalysis.StandardType.GGQTwoVACOrth
import CFSG.LocalAnalysis.StandardType.GGQTwoVACOrthNonFull
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataReindexGroups
import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksCentExt
import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksGroup
import CFSG.RankThree.CentralCover.SteinbergBNLinearTorus
import CFSG.LocalAnalysis.StandardType.GGTBJOmModelMap
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitOmChar

public section

namespace CFSG.StandardType.GGQ2Frame.OrthBlocks

open CFSG CFSG.Assembly CFSG.StandardType Matrix
open CFSG.Open (IsElemAbelian)
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ClassicalGroups.Orthogonal
open QuadraticMap

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

private def otc_keyElt (K : Type) [Field K] [CharP K 2] : SpecialLinearGroup (Fin 2) K :=
  ⟨!![0, 1; 1, 1], by simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩

private lemma otc_coe_keyElt (K : Type) [Field K] [CharP K 2] :
    ((otc_keyElt K : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![0, 1; 1, 1] := rfl

private def otc_sqElt (K : Type) [Field K] [CharP K 2] : SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, 1; 1, 0], by simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩

private lemma otc_coe_sqElt (K : Type) [Field K] [CharP K 2] :
    ((otc_sqElt K : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![1, 1; 1, 0] := rfl

private lemma otc_keyElt_mul_self (K : Type) [Field K] [CharP K 2] :
    (otc_keyElt K : SpecialLinearGroup (Fin 2) K) * otc_keyElt K = otc_sqElt K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [otc_coe_keyElt, otc_coe_sqElt, CharTwo.add_self_eq_zero]

private lemma otc_sqElt_mul_keyElt (K : Type) [Field K] [CharP K 2] :
    (otc_sqElt K : SpecialLinearGroup (Fin 2) K) * otc_keyElt K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [otc_coe_keyElt, otc_coe_sqElt, CharTwo.add_self_eq_zero]

private lemma otc_keyElt_pow_three (K : Type) [Field K] [CharP K 2] :
    (otc_keyElt K : SpecialLinearGroup (Fin 2) K) ^ 3 = 1 := by
  rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, pow_two, otc_keyElt_mul_self,
    otc_sqElt_mul_keyElt]

private lemma otc_keyElt_ne_one (K : Type) [Field K] [CharP K 2] :
    (otc_keyElt K : SpecialLinearGroup (Fin 2) K) ≠ 1 := by
  intro h
  have h1 := congrArg (fun g : SpecialLinearGroup (Fin 2) K =>
    ((g : Matrix (Fin 2) (Fin 2) K)) 0 0) h
  simp [otc_coe_keyElt] at h1

private lemma otc_keyElt_orderOf (K : Type) [Field K] [CharP K 2] :
    orderOf (otc_keyElt K) = 3 := by
  exact orderOf_eq_prime (otc_keyElt_pow_three K) (otc_keyElt_ne_one K)

noncomputable def otc_zeta (K : Type) [Field K] [CharP K 2] :
    Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K := by
  exact CFSG.RankThree.CentralCover.zmodPowHom (otc_keyElt K) (otc_keyElt_pow_three K)

lemma otc_zeta_injective (K : Type) [Field K] [CharP K 2] :
    Function.Injective (otc_zeta K) := by
  exact CFSG.RankThree.CentralCover.zmodPowHom_injective (otc_keyElt_orderOf K)
    (otc_keyElt_pow_three K)

private theorem otc_liftV_injective (t : ℕ) (δ : Fin 2) :
    Function.Injective (liftV t δ) := by
  intro u v h
  funext i
  have h1 : Fin.append u (0 : Fin δ.val → ZMod 3) (Fin.castAdd δ.val i) =
      Fin.append v (0 : Fin δ.val → ZMod 3) (Fin.castAdd δ.val i) := congrFun h _
  simpa [liftV, Fin.append_left] using h1

theorem otc_otau_mul {K : Type} [Field K]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (δ : Fin 2)
    (u v : PlaneRaw.V t) :
    otau ζ t δ (u + v) = otau ζ t δ u * otau ζ t δ v := by
  rw [otau, otau, otau, map_add, SpBlocks.tau_add, Subgroup.coe_mul]

theorem otc_otau_zero {K : Type} [Field K]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (δ : Fin 2) :
    otau ζ t δ (0 : PlaneRaw.V t) = 1 := by
  rw [otau, map_zero, SpBlocks.tau_zero, Subgroup.coe_one]

private noncomputable def otc_otauHom {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (δ : Fin 2)
    (hτ : OrthTauMemOmega) (hK : Nat.card K = 2) :
    Multiplicative (PlaneRaw.V t) →* ↥(omegaQ (K := K) t δ) where
  toFun x := ⟨otau ζ t δ (Multiplicative.toAdd x), hτ ζ t δ hK _⟩
  map_one' := by
    apply Subtype.ext
    simpa using otc_otau_zero ζ t δ
  map_mul' x y := by
    apply Subtype.ext
    simp [otc_otau_mul]

private theorem otc_otauHom_apply {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (δ : Fin 2)
    (hτ : OrthTauMemOmega) (hK : Nat.card K = 2) (u : PlaneRaw.V t) :
    ((otc_otauHom ζ t δ hτ hK (Multiplicative.ofAdd u) : ↥(omegaQ (K := K) t δ)) :
      GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) = otau ζ t δ u := rfl

private theorem otc_otauHom_injective {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K)
    (hζ : Function.Injective ζ) (t : ℕ) (δ : Fin 2)
    (hτ : OrthTauMemOmega) (hK : Nat.card K = 2) :
    Function.Injective (otc_otauHom ζ t δ hτ hK) := by
  intro x y h
  apply Multiplicative.toAdd.injective
  apply otc_liftV_injective t δ
  apply SpBlocks.tau_injective (K := K) (ζ := ζ) hζ (t + δ.val)
  have h1 := congrArg (fun g : ↥(omegaQ (K := K) t δ) =>
    (g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K)) h
  exact Subtype.ext (by simpa [otc_otauHom, otau] using h1)

private noncomputable def otc_torus {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (δ : Fin 2)
    (hτ : OrthTauMemOmega) (hK : Nat.card K = 2) :
    Subgroup (GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :=
  (otc_otauHom ζ t δ hτ hK).range.map (omegaQ (K := K) t δ).subtype

private theorem otc_mem_torus {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (δ : Fin 2)
    (hτ : OrthTauMemOmega) (hK : Nat.card K = 2)
    (x : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :
    x ∈ otc_torus ζ t δ hτ hK ↔ ∃ u : PlaneRaw.V t, x = otau ζ t δ u := by
  rw [show otc_torus ζ t δ hτ hK =
    (otc_otauHom ζ t δ hτ hK).range.map (omegaQ (K := K) t δ).subtype from rfl,
    Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, rfl⟩ := MonoidHom.mem_range.mp hy
    exact ⟨Multiplicative.toAdd z, otc_otauHom_apply ζ t δ hτ hK _⟩
  · rintro ⟨u, rfl⟩
    refine ⟨otc_otauHom ζ t δ hτ hK (Multiplicative.ofAdd u), ⟨_, rfl⟩, ?_⟩
    exact otc_otauHom_apply ζ t δ hτ hK u

private theorem otc_torus_le_omega {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (δ : Fin 2)
    (hτ : OrthTauMemOmega) (hK : Nat.card K = 2) :
    otc_torus ζ t δ hτ hK ≤ omegaQ (K := K) t δ := by
  change (otc_otauHom ζ t δ hτ hK).range.map (omegaQ (K := K) t δ).subtype ≤
    omegaQ (K := K) t δ
  exact Subgroup.map_subtype_le _

private theorem otc_zmod_three_nsmul (z : ZMod 3) : (3 : ℕ) • z = 0 := by
  rw [nsmul_eq_mul, show ((3 : ℕ) : ZMod 3) = 0 from ZMod.natCast_self 3, zero_mul]

private theorem otc_isElemAbelian_top_planeRaw (t : ℕ) :
    IsElemAbelian 3 (⊤ : Subgroup (Multiplicative (PlaneRaw.V t))) := by
  refine ⟨isMulCommutative_iff.mpr (fun a b => mul_comm a b), ?_⟩
  intro x _
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  funext i
  exact otc_zmod_three_nsmul _

private theorem otc_torus_isElemAbelian {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (δ : Fin 2)
    (hτ : OrthTauMemOmega) (hK : Nat.card K = 2) :
    IsElemAbelian 3 (otc_torus ζ t δ hτ hK) := by
  have hrange : IsElemAbelian 3 (otc_otauHom ζ t δ hτ hK).range := by
    rw [MonoidHom.range_eq_map]
    exact CFSG.Open.IsElemAbelian.map (otc_isElemAbelian_top_planeRaw t)
      (otc_otauHom ζ t δ hτ hK)
  have hmap := CFSG.Open.IsElemAbelian.map hrange (omegaQ (K := K) t δ).subtype
  simpa [otc_torus] using hmap

private theorem otc_card_planeRawV (t : ℕ) : Nat.card (PlaneRaw.V t) = 3 ^ t := by
  rw [PlaneRaw.V, Nat.card_fun, Nat.card_zmod, Nat.card_fin]

private theorem otc_card_torus {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K)
    (hζ : Function.Injective ζ) (t : ℕ) (δ : Fin 2)
    (hτ : OrthTauMemOmega) (hK : Nat.card K = 2) :
    Nat.card (otc_torus ζ t δ hτ hK) = 3 ^ t := by
  rw [show otc_torus ζ t δ hτ hK =
      (otc_otauHom ζ t δ hτ hK).range.map (omegaQ (K := K) t δ).subtype from rfl,
    Subgroup.card_map_of_injective (omegaQ (K := K) t δ).subtype_injective]
  have h1 : Nat.card ((otc_otauHom ζ t δ hτ hK).range) =
      Nat.card (Multiplicative (PlaneRaw.V t)) :=
    Nat.card_congr (MonoidHom.ofInjective (otc_otauHom_injective ζ hζ t δ hτ hK)).toEquiv.symm
  rw [h1, Nat.card_congr Multiplicative.toAdd, otc_card_planeRawV]

private theorem otc_single_one_ne_zero (t : ℕ) (ht : 1 ≤ t) :
    (Pi.single ⟨0, ht⟩ (1 : ZMod 3) : PlaneRaw.V t) ≠ 0 := by
  intro h
  have h1 : (Pi.single ⟨0, ht⟩ (1 : ZMod 3) : PlaneRaw.V t) ⟨0, ht⟩ = 0 := by rw [h]; rfl
  simp at h1

private theorem otc_exists_ne_one_of_hmax {K : Type} [Field K] [Finite K] [CharP K 2]
    (t : ℕ) (δ : Fin 2)
    (Q : QuadraticForm K (Fin (t + δ.val) ⊕ Fin (t + δ.val) → K))
    (hΩ : LargeEvenOmega ⇑Q = omegaQ (K := K) t δ)
    (hK : Nat.card K = 2) (ht : 4 ≤ t + δ.val)
    (hτ : OrthTauMemOmega) (A : Subgroup ↥(LargeEvenOmega ⇑Q))
    (hmax : ∀ g : ↥(LargeEvenOmega ⇑Q), (∀ a ∈ A, g * a = a * g) → g ^ 3 = 1 → g ∈ A) :
    ∃ b ∈ A, b ≠ 1 := by
  by_contra h
  push Not at h
  have hbot : A = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    exact h
  have ht1 : 1 ≤ t := by omega
  let ζ := otc_zeta K
  have hζ : Function.Injective ζ := otc_zeta_injective K
  let u : PlaneRaw.V t := Pi.single ⟨0, ht1⟩ 1
  have hu : u ≠ 0 := otc_single_one_ne_zero t ht1
  have hgΩ : otau ζ t δ u ∈ LargeEvenOmega ⇑Q := hΩ ▸ hτ ζ t δ hK u
  have hg3 : otau ζ t δ u ^ 3 = 1 := by
    have hmem : otau ζ t δ u ∈ otc_torus ζ t δ hτ hK :=
      (otc_mem_torus ζ t δ hτ hK _).mpr ⟨u, rfl⟩
    exact (otc_torus_isElemAbelian ζ t δ hτ hK).2 _ hmem
  have hg1 : otau ζ t δ u ≠ 1 := by
    intro h1
    have h2 : otc_otauHom ζ t δ hτ hK (Multiplicative.ofAdd u) = 1 := by
      apply Subtype.ext
      rw [otc_otauHom_apply, h1]
      simp
    have h2' : otc_otauHom ζ t δ hτ hK (Multiplicative.ofAdd u) =
        otc_otauHom ζ t δ hτ hK 1 := by
      rw [map_one]
      exact h2
    have h3 := otc_otauHom_injective ζ hζ t δ hτ hK h2'
    have h4 : u = 0 := by simpa using congrArg Multiplicative.toAdd h3
    exact hu h4
  have hg3' : (⟨otau ζ t δ u, hgΩ⟩ : ↥(LargeEvenOmega ⇑Q)) ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hg3, Subgroup.coe_one]
  have hmemA : (⟨otau ζ t δ u, hgΩ⟩ : ↥(LargeEvenOmega ⇑Q)) ∈ A :=
    hmax ⟨_, hgΩ⟩ (fun a ha => by
      have ha1 : a = 1 := Subgroup.mem_bot.mp (hbot ▸ ha)
      rw [ha1]
      simp) hg3'
  rw [hbot] at hmemA
  exact hg1 (by simpa using congrArg Subtype.val (Subgroup.mem_bot.mp hmemA))

theorem otc_exists_max_isElemAbelian_le {G : Type} [Group G] [Finite G]
    {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) :
    ∃ M : Subgroup G, E ≤ M ∧ IsElemAbelian p M ∧
      ∀ M' : Subgroup G, E ≤ M' → IsElemAbelian p M' → Nat.card M' ≤ Nat.card M := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ M : Subgroup G, E ≤ M ∧ IsElemAbelian p M ∧ Nat.card M = n
  have hP : P (Nat.card E) := ⟨E, le_rfl, hE, rfl⟩
  have hcardE : Nat.card E ≤ Nat.card G :=
    Nat.card_le_card_of_injective (f := E.subtype) E.subtype_injective
  obtain ⟨M, hEM, hMelem, hMcard⟩ :=
    Nat.findGreatest_spec (P := P) (n := Nat.card G) hcardE hP
  refine ⟨M, hEM, hMelem, fun M' hEM' hM' => ?_⟩
  have hPn' : P (Nat.card M') := ⟨M', hEM', hM', rfl⟩
  have hcardM' : Nat.card M' ≤ Nat.card G :=
    Nat.card_le_card_of_injective (f := M'.subtype) M'.subtype_injective
  by_contra hle
  exact Nat.findGreatest_is_greatest (P := P) (n := Nat.card G) (k := Nat.card M')
    (by omega) hcardM' hPn'

theorem otc_selfCent_of_max_isElemAbelian {G : Type} [Group G] [Finite G]
    {p : ℕ} {E M : Subgroup G} (hEM : E ≤ M) (hM : IsElemAbelian p M)
    (hmax : ∀ M' : Subgroup G, E ≤ M' → IsElemAbelian p M' → Nat.card M' ≤ Nat.card M) :
    ∀ g : G, (∀ z ∈ M, g * z = z * g) → g ^ p = 1 → g ∈ M := by
  intro g hcomm hgp
  by_contra hgM
  have hsup : IsElemAbelian p (M ⊔ Subgroup.zpowers g) :=
    hM.sup_of_commute (isElemAbelian_zpowers hgp) (fun a ha b hb => by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      have hav : Commute a g := (hcomm a ha).symm
      exact (hav.zpow_right n).eq)
  have hle : M ≤ M ⊔ Subgroup.zpowers g := le_sup_left
  have hcard : Nat.card ↥(M ⊔ Subgroup.zpowers g) ≤ Nat.card M :=
    hmax (M ⊔ Subgroup.zpowers g) (hEM.trans hle) hsup
  have heq : M ⊔ Subgroup.zpowers g = M :=
    (Subgroup.eq_of_le_of_card_ge (H := M) (K := M ⊔ Subgroup.zpowers g) le_sup_left hcard).symm
  exact hgM (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers g))

private theorem otc_nondegenerate_reindexQuadraticForm {ι K : Type} [Field K] {d : ℕ}
    (e : ι ≃ Fin d) {Q₀ : QuadraticForm K (ι → K)}
    (hQ₀ : Q₀.polarBilin.Nondegenerate) :
    (reindexQuadraticForm e Q₀).polarBilin.Nondegenerate := by
  have hpol : ∀ y z, polar (reindexQuadraticForm e Q₀) y z =
      polar Q₀ ((reindexVectorEquiv (K := K) e).symm y)
        ((reindexVectorEquiv (K := K) e).symm z) := by
    intro y z
    simp only [polar, reindexQuadraticForm, QuadraticMap.comp_apply, LinearEquiv.coe_coe,
      map_add]
  have hsep : ∀ x : Fin d → K,
      (∀ y, polar (reindexQuadraticForm e Q₀) x y = 0) → x = 0 := by
    intro x hx
    have h0 : (reindexVectorEquiv (K := K) e).symm x = 0 := by
      apply hQ₀.1
      intro y
      have h := hx (reindexVectorEquiv e y)
      rwa [hpol, LinearEquiv.symm_apply_apply, ← polarBilin_apply_apply] at h
    exact ((reindexVectorEquiv (K := K) e).symm.map_eq_zero_iff).mp h0
  refine ⟨fun x hx => hsep x fun y => ?_, fun x hx => hsep x fun y => ?_⟩
  · rw [← polarBilin_apply_apply]
    exact hx y
  · rw [polar_comm, ← polarBilin_apply_apply]
    exact hx y

private theorem otc_card_le_pair_of_charSum {K : Type} [Field K] [Finite K] [CharP K 2]
    [Fact (Nat.Prime 3)]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hpq : 3 ∣ Nat.card K - 1 ∨ 3 ∣ Nat.card K + 1) {m : ℕ}
    (hV : Module.finrank K V = 2 * m) (hm : 4 ≤ m)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    {E : Subgroup ↥(orthDerived Q)} (hE : IsElemAbelian 3 E) :
    (OrdPNsOm.charSum Q ⊤ ≡ 1 [ZMOD 3] → Nat.card E ≤ 3 ^ m) ∧
      (OrdPNsOm.charSum Q ⊤ ≡ -1 [ZMOD 3] → Nat.card E ≤ 3 ^ (m - 1)) := by
  classical
  obtain ⟨M, hEM, hMelem, hMmax⟩ := otc_exists_max_isElemAbelian_le hE
  have hMsc := otc_selfCent_of_max_isElemAbelian hEM hMelem hMmax
  have hEMcard : Nat.card E ≤ Nat.card M := hMmax E le_rfl hE
  constructor
  · intro hchar
    by_cases h3 : 3 ^ 3 ≤ Nat.card M
    · have hcard := ggQ2Orth_card_of_charSum (m := m) hQ hpq hV hT hchar hMelem h3 hMsc
      rw [hcard] at hEMcard
      exact hEMcard
    · have hMle : Nat.card M ≤ 3 ^ 3 - 1 := by omega
      have hpow : 3 ^ 3 ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  · intro hchar
    by_cases h3 : 3 ^ 3 ≤ Nat.card M
    · have hcard :=
        ggQ2OrthNonFull_card_of_charSum (m := m) hQ hpq hV hT hchar hMelem h3 hMsc
      rw [hcard] at hEMcard
      exact hEMcard
    · have hMle : Nat.card M ≤ 3 ^ 3 - 1 := by omega
      have hpow : 3 ^ 3 ≤ 3 ^ (m - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega

theorem orthTorusConj_of_tauMemOmega (hτ : OrthTauMemOmega) : OrthTorusConj := by
  classical
  intro K _ _ _ t δ hK ht
  let Q : QuadraticForm K (Fin (t + δ.val) ⊕ Fin (t + δ.val) → K) := planeQForm K t δ
  have hQcoe : ⇑Q = planeQ (K := K) t δ := coe_planeQForm K t δ
  rw [show omegaQ (K := K) t δ = LargeEvenOmega ⇑Q from congrArg LargeEvenOmega hQcoe.symm,
    show planeQ (K := K) t δ = ⇑Q from hQcoe.symm]
  intro A hAelem hmax
  let eΩ : ↥(LargeEvenOmega ⇑Q) ≃* ↥(orthDerived Q) := TableBOrth.omegaEquivOrthDerived Q
  let E : Subgroup ↥(orthDerived Q) := A.map eΩ.toMonoidHom
  have hEelem : IsElemAbelian 3 E := TableB.isElemAbelian_map hAelem eΩ.toMonoidHom
  have hneA : ∃ b ∈ A, b ≠ 1 :=
    otc_exists_ne_one_of_hmax t δ Q (congrArg LargeEvenOmega hQcoe) hK ht hτ A hmax
  have hEsc : ∀ g : ↥(orthDerived Q), (∀ z ∈ E, g * z = z * g) → g ^ 3 = 1 → g ∈ E :=
    CFSG.StandardType.selfCent_map_mulEquiv eΩ hmax
  have hneE : ∃ b ∈ E, b ≠ 1 := by
    obtain ⟨b, hb, hb1⟩ := hneA
    exact ⟨eΩ b, ⟨b, hb, rfl⟩, fun h => hb1 (eΩ.injective (by simpa using h))⟩
  obtain ⟨hlinΩ, hlinpow, hlincomm, hlinmax, hlinne⟩ :=
    CFSG.StandardType.map_subtype_hyps E hEelem hneE hEsc
  obtain ⟨r, τ, F, hτF, hdimF, hdimVle, hτinj, hτrange, hperm, hdinv, hnorm, hcharAlt⟩ :=
    OrthTorus.exists_torus_frame_full (p := 3) (hp2 := by norm_num)
      (hpq := Or.inr (by norm_num [hK]))
      (hQ := nondegenerate_planeQForm (K := K) (t := t) (δ := δ))
      (hT := exists_totallySingular_planeQForm (K := K) (t := t) (δ := δ) (by exact ht))
      (A := E.map (orthDerived Q).subtype) hlinΩ hlinpow hlincomm hlinmax hlinne
  have hdimV : Module.finrank K (Fin (t + δ.val) ⊕ Fin (t + δ.val) → K) =
      2 * (t + δ.val) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  have hcharQ : OrdPNsOm.charSum Q ⊤ ≡ (if δ = 0 then 1 else -1) [ZMOD 3] := by
    simpa [Q] using charSum_planeQForm_modEq (K := K) (t := t) (δ := δ) hK
  have hδcases : δ = 0 ∨ δ = 1 := by
    have hlt := δ.isLt
    have h01 : δ.val = 0 ∨ δ.val = 1 := by omega
    rcases h01 with h | h
    · left; exact Fin.ext (by simpa using h)
    · right; exact Fin.ext (by simpa using h)
  have hr : r = t := by
    rcases hcharAlt with ⟨h1, h2⟩ | ⟨h1, h2, -⟩
    · rcases hδcases with hδ | hδ
      · subst hδ
        simp at h2 hdimV
        omega
      · exfalso
        subst hδ
        have hneg : OrdPNsOm.charSum Q ⊤ ≡ -1 [ZMOD 3] := by simpa using hcharQ
        exact OrthTorus.one_not_modEq_neg_one Nat.prime_three (by norm_num)
          (h1.symm.trans hneg)
    · rcases hδcases with hδ | hδ
      · exfalso
        subst hδ
        have hpos : OrdPNsOm.charSum Q ⊤ ≡ 1 [ZMOD 3] := by simpa using hcharQ
        exact OrthTorus.neg_one_not_modEq_one Nat.prime_three (by norm_num)
          (h1.symm.trans hpos)
      · subst hδ
        simp at h2 hdimV
        omega
  have hAEcard : Nat.card E = Nat.card A :=
    Subgroup.card_map_of_injective (f := eΩ.toMonoidHom) eΩ.injective
  have hcardA : Nat.card A = 3 ^ t := by
    have h1 : Nat.card (E.map (orthDerived Q).subtype) = Nat.card E :=
      Subgroup.card_map_of_injective (orthDerived Q).subtype_injective
    have h2 : Nat.card (E.map (orthDerived Q).subtype) = 3 ^ t := by
      calc Nat.card (E.map (orthDerived Q).subtype) = Nat.card τ.range :=
          Nat.card_congr (MulEquiv.subgroupCongr hτrange.symm).toEquiv
        _ = 3 ^ r := ggQ2OrthNonFull_card_range hτinj
        _ = 3 ^ t := by rw [hr]
    calc Nat.card A = Nat.card E := hAEcard.symm
      _ = Nat.card (E.map (orthDerived Q).subtype) := h1.symm
      _ = 3 ^ t := h2
  let T : Subgroup (GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :=
    otc_torus (otc_zeta K) t δ hτ hK
  have hTle : T ≤ omegaQ (K := K) t δ := otc_torus_le_omega _ t δ hτ hK
  have hTelem : IsElemAbelian 3 T := otc_torus_isElemAbelian _ t δ hτ hK
  have hTcard : Nat.card T = 3 ^ t :=
    otc_card_torus (otc_zeta K) (otc_zeta_injective K) t δ hτ hK
  have hTmem : ∀ x : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K,
      x ∈ T ↔ ∃ u : PlaneRaw.V t, x = otau (otc_zeta K) t δ u :=
    fun x => otc_mem_torus (otc_zeta K) t δ hτ hK x
  have hTleQ : T ≤ LargeEvenOmega ⇑Q := by
    rw [show LargeEvenOmega ⇑Q = omegaQ (K := K) t δ from congrArg LargeEvenOmega hQcoe]
    exact hTle
  let A_GL : Subgroup (GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :=
    A.map (LargeEvenOmega ⇑Q).subtype
  have hAGLelem : IsElemAbelian 3 A_GL := TableB.isElemAbelian_map hAelem _
  have hAGLcard : Nat.card A_GL = 3 ^ t := by
    change Nat.card (A.map (LargeEvenOmega ⇑Q).subtype) = 3 ^ t
    rw [Subgroup.card_map_of_injective (LargeEvenOmega ⇑Q).subtype_injective]
    exact hcardA
  let e : Fin (t + δ.val) ⊕ Fin (t + δ.val) ≃ Fin ((t + δ.val) + (t + δ.val)) :=
    finSumFinEquiv
  let Q' : QuadraticForm K (Fin ((t + δ.val) + (t + δ.val)) → K) := reindexQuadraticForm e Q
  let ψ : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K ≃*
      GL (Fin ((t + δ.val) + (t + δ.val))) K := reindexMatrixEquiv e
  let Eψ : Subgroup (GL (Fin ((t + δ.val) + (t + δ.val))) K) := A_GL.map ψ.toMonoidHom
  have hEψelem : IsElemAbelian 3 Eψ := TableB.isElemAbelian_map hAGLelem _
  have hEψder : Eψ ≤ matrixDerived Q' := by
    have hAle : A_GL ≤ LargeEvenOmega ⇑Q := Subgroup.map_subtype_le _
    have h := Subgroup.map_mono (f := ψ.toMonoidHom) hAle
    have hder : (LargeEvenOmega ⇑Q).map ψ.toMonoidHom = matrixDerived Q' :=
      stated_derived_reindex e Q
    rwa [hder] at h
  have hEψcard : Nat.card Eψ = 3 ^ t := by
    change Nat.card (A_GL.map ψ.toMonoidHom) = 3 ^ t
    rw [Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective, hAGLcard]
  let Fψ : Subgroup (GL (Fin ((t + δ.val) + (t + δ.val))) K) := T.map ψ.toMonoidHom
  have hFψelem : IsElemAbelian 3 Fψ := TableB.isElemAbelian_map hTelem _
  have hFψder : Fψ ≤ matrixDerived Q' := by
    have h := Subgroup.map_mono (f := ψ.toMonoidHom) hTleQ
    have hder : (LargeEvenOmega ⇑Q).map ψ.toMonoidHom = matrixDerived Q' :=
      stated_derived_reindex e Q
    rwa [hder] at h
  have hQnd : (QuadraticMap.polarBilin Q).Nondegenerate := by
    simpa [Q] using nondegenerate_planeQForm (K := K) (t := t) (δ := δ)
  have hTsing : ∃ S : Submodule K (Fin (t + δ.val) ⊕ Fin (t + δ.val) → K),
      Module.finrank K S = 3 ∧ ∀ v ∈ S, Q v = 0 := by
    simpa [Q] using exists_totallySingular_planeQForm (K := K) (t := t) (δ := δ) (by exact ht)
  have hEmaxψ : ∀ F' : Subgroup (GL (Fin ((t + δ.val) + (t + δ.val))) K),
      F' ≤ matrixDerived Q' → (∀ a ∈ F', ∀ b ∈ F', a * b = b * a) →
      (∀ a ∈ F', a ^ 3 = 1) → Nat.card F' ≤ Nat.card Eψ := by
    intro F' hF'der hF'c hF'p
    let F : Subgroup (GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :=
      F'.map ψ.symm.toMonoidHom
    have hFder : F ≤ LargeEvenOmega ⇑Q := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      change ψ.symm x ∈ LargeEvenOmega ⇑Q
      have hx1 : x ∈ (LargeEvenOmega ⇑Q).map ψ.toMonoidHom := by
        have h := hF'der hx
        rwa [show matrixDerived Q' = (LargeEvenOmega ⇑Q).map ψ.toMonoidHom from
          (stated_derived_reindex e Q).symm] at h
      obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hx1
      have hsym : ψ.symm x = z := by
        rw [MulEquiv.symm_apply_eq]
        exact hzx.symm
      rw [hsym]
      exact hz
    have hFelem : IsElemAbelian 3 F := by
      have hF'elem : IsElemAbelian 3 F' := by
        refine ⟨isMulCommutative_iff.mpr (fun a b => ?_), hF'p⟩
        exact Subtype.ext (hF'c a.val a.2 b.val b.2)
      have h := TableB.isElemAbelian_map hF'elem ψ.symm.toMonoidHom
      simpa [F] using h
    let FΩ : Subgroup ↥(orthDerived Q) :=
      (F.subgroupOf (LargeEvenOmega ⇑Q)).map eΩ.toMonoidHom
    have hFΩelem : IsElemAbelian 3 FΩ :=
      TableB.isElemAbelian_map (IsElemAbelian.subgroupOf hFelem (LargeEvenOmega ⇑Q)) _
    have hFΩcard : Nat.card FΩ = Nat.card F := by
      change Nat.card ((F.subgroupOf (LargeEvenOmega ⇑Q)).map eΩ.toMonoidHom) = Nat.card F
      rw [Subgroup.card_map_of_injective (f := eΩ.toMonoidHom) eΩ.injective,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFder).toEquiv]
    have hbound :=
      otc_card_le_pair_of_charSum (Q := Q) (m := t + δ.val) hQnd
        (Or.inr (by norm_num [hK])) hdimV (by omega) hTsing hFΩelem
    have hFΩle : Nat.card FΩ ≤ 3 ^ t := by
      rcases hδcases with hδ | hδ
      · have hc : OrdPNsOm.charSum Q ⊤ ≡ 1 [ZMOD 3] := by simpa [hδ] using hcharQ
        have h := hbound.1 hc
        have hpow : 3 ^ (t + δ.val) = 3 ^ t := by rw [hδ]; simp
        rwa [hpow] at h
      · have hc : OrdPNsOm.charSum Q ⊤ ≡ -1 [ZMOD 3] := by simpa [hδ] using hcharQ
        have h := hbound.2 hc
        have hpow : 3 ^ ((t + δ.val) - 1) = 3 ^ t := by rw [hδ]; simp
        rwa [hpow] at h
    have hF'card : Nat.card F' = Nat.card F := by
      change Nat.card F' = Nat.card (F'.map ψ.symm.toMonoidHom)
      rw [Subgroup.card_map_of_injective (f := ψ.symm.toMonoidHom) ψ.symm.injective]
    calc Nat.card F' = Nat.card F := hF'card
      _ = Nat.card FΩ := hFΩcard.symm
      _ ≤ 3 ^ t := hFΩle
      _ = Nat.card Eψ := hEψcard.symm
  have hQ'nd : (QuadraticMap.polarBilin Q').Nondegenerate :=
    otc_nondegenerate_reindexQuadraticForm e hQnd
  have hT' : ∃ S : Submodule K (Fin ((t + δ.val) + (t + δ.val)) → K),
      Module.finrank K S = 3 ∧ ∀ v ∈ S, Q' v = 0 := by
    obtain ⟨S, hSdim, hSsing⟩ := hTsing
    refine ⟨S.map (reindexVectorEquiv e).toLinearMap, ?_, ?_⟩
    · rw [LinearEquiv.finrank_map_eq]
      exact hSdim
    · intro v hv
      obtain ⟨s, hs, rfl⟩ := Submodule.mem_map.mp hv
      change reindexQuadraticForm e Q (reindexVectorEquiv e s) = 0
      rw [reindexQuadraticForm_map]
      exact hSsing s hs
  have hpq3 : 3 ∣ Nat.card K + 1 := by norm_num [hK]
  obtain ⟨g', hg'isom, hconj⟩ :=
    OrthNs.exists_conj_le_of_maxCard (Q := Q') hQ'nd hT' Nat.prime_three hpq3
      hEψder (fun a ha b hb => TableB.IsElemAbelian.comm hEψelem ha hb) hEψelem.2
      hEmaxψ hFψder (fun a ha b hb => TableB.IsElemAbelian.comm hFψelem ha hb) hFψelem.2
  let g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K := ψ.symm g'
  have hψg : ψ g = g' := MulEquiv.apply_symm_apply ψ g'
  have hconjA : ∀ y ∈ T, g * y * g⁻¹ ∈ A_GL := by
    intro y hy
    have hyF : ψ y ∈ Fψ := ⟨y, hy, rfl⟩
    have h1 := hconj (ψ y) hyF
    obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.mp h1
    have h2 : ψ.symm (g' * ψ y * g'⁻¹) = a := by
      rw [MulEquiv.symm_apply_eq]
      exact hae.symm
    have h3 : ψ.symm (g' * ψ y * g'⁻¹) = g * y * g⁻¹ := by
      simp [g]
    have h4 : a = g * y * g⁻¹ := h2.symm.trans h3
    rwa [h4] at ha
  have hTmap_le : T.map (MulAut.conj g).toMonoidHom ≤ A_GL := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    simpa [MulAut.conj_apply] using hconjA y hy
  have hcardTmap : Nat.card (T.map (MulAut.conj g).toMonoidHom) = Nat.card T :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hTeq : T.map (MulAut.conj g).toMonoidHom = A_GL := by
    refine Subgroup.eq_of_le_of_card_ge hTmap_le ?_
    rw [hcardTmap, hTcard, hAGLcard]
  have hPT : A_GL.map (MulAut.conj g⁻¹).toMonoidHom = T := by
    have h1 : (T.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom
        = A_GL.map (MulAut.conj g⁻¹).toMonoidHom := by rw [hTeq]
    rw [Subgroup.map_map] at h1
    have hcomp : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom
        = MonoidHom.id (GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) := by
      ext x
      simp only [MulEquiv.coe_toMonoidHom, MonoidHom.comp_apply, MonoidHom.id_apply,
        MulAut.conj_apply]
      group
    rw [hcomp, Subgroup.map_id] at h1
    exact h1.symm
  have hg_raw : ∀ v : Fin (t + δ.val) ⊕ Fin (t + δ.val) → K,
      Q ((g : Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
        (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) *ᵥ v) = Q v := by
    intro v
    have h1 := reindexQuadraticForm_map e Q (g *ᵥ v)
    have h2 := (mem_matrixIsometries_iff Q' g').mp hg'isom (reindexVectorEquiv e v)
    have h3 := reindexMatrixEquiv_mulVec e g v
    calc Q (g *ᵥ v) = Q' (reindexVectorEquiv e (g *ᵥ v)) := h1.symm
      _ = Q' (matrixLinearEquiv g' (reindexVectorEquiv e v)) := by rw [← h3, hψg]
      _ = Q' (reindexVectorEquiv e v) := h2
      _ = Q v := reindexQuadraticForm_map e Q v
  have hP_raw : ∀ v : Fin (t + δ.val) ⊕ Fin (t + δ.val) → K,
      Q (((g⁻¹ : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :
        Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
          (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) *ᵥ v) = Q v := by
    intro v
    have hstep : (g : Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
          (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) *ᵥ
        (((g⁻¹ : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :
          Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
            (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
    have h := hg_raw (((g⁻¹ : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :
      Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
        (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) *ᵥ v)
    rw [hstep] at h
    exact h.symm
  have hiff : ∀ x : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K,
      (∃ a ∈ A, x = g⁻¹ * (a : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) * (g⁻¹)⁻¹) ↔
        x ∈ A_GL.map (MulAut.conj g⁻¹).toMonoidHom := by
    intro x
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine Subgroup.mem_map.mpr
        ⟨(a : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K), ⟨a, ha, rfl⟩, ?_⟩
      simp
    · intro hx
      obtain ⟨b, hb, hbx⟩ := Subgroup.mem_map.mp hx
      obtain ⟨a, ha, hab⟩ := Subgroup.mem_map.mp hb
      exact ⟨a, ha, by rw [← hbx, ← hab]; simp⟩
  refine ⟨otc_zeta K, g⁻¹, otc_zeta_injective K, hP_raw, fun x => ?_⟩
  rw [hiff x, hPT]
  exact hTmem x

theorem orthTorusConj_holds : OrthTorusConj :=
  orthTorusConj_of_tauMemOmega orthTauMemOmega_holds

end

end CFSG.StandardType.GGQ2Frame.OrthBlocks

namespace CFSG.StandardType.GGQ2Frame.OrthPlacement

theorem existsOrthFrame_holds : ExistsOrthFrame :=
  existsOrthFrame_of_torusConj OrthBlocks.orthTorusConj_holds

end CFSG.StandardType.GGQ2Frame.OrthPlacement

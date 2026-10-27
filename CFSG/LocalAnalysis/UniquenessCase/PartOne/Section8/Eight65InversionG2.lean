module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG2QHeis
public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.AGLEmbedding.KFactProofs.G2Q
open scoped commutatorElement

section Frobenius

variable {L : Type} [Field L]

theorem nw0_sq : (nw0 : ModGL .G2 L) ^ 2 = 1 := by
  have h : (nw0 : ModGL .G2 L) = (n0 * n1) ^ 3 := by
    rw [nw0, yq, pow_succ, pow_two]
    group
  calc (nw0 : ModGL .G2 L) ^ 2 = ((n0 * n1) ^ 3) ^ 2 := by rw [h]
    _ = ((n0 * n1) ^ 2) ^ 3 := by rw [← pow_mul, ← pow_mul]
    _ = (yq : ModGL .G2 L) ^ 3 := by rw [show (n0 * n1) ^ 2 = (yq : ModGL .G2 L) from rfl]
    _ = 1 := yq_pow_three

end Frobenius

variable {L : Type} [Field L]

theorem commutator_tz_yq (ω : Lˣ) (hω : (ω : L) ^ 3 = 1) :
    (⁅tz ω 1, yq⁆ : ModGL .G2 L) = tz 1 ω⁻¹ := by
  have hω3 : (ω ^ 3 : Lˣ) = 1 := Units.ext (by simpa using hω)
  have hy : yq * tz ω 1 * yq⁻¹ = tz ω ω := by
    rw [yq_tz]
    congr 1 <;> simp [hω3]
  calc (⁅tz ω 1, yq⁆ : ModGL .G2 L) = tz ω 1 * (yq * tz ω 1 * yq⁻¹)⁻¹ := by
        rw [commutatorElement_def]
        group
    _ = tz ω 1 * (tz ω ω)⁻¹ := by rw [hy]
    _ = tz ω 1 * tz ω⁻¹ ω⁻¹ := by rw [tz_inv]
    _ = tz (ω * ω⁻¹) (1 * ω⁻¹) := by rw [tz_mul]
    _ = tz 1 ω⁻¹ := by rw [mul_inv_cancel, one_mul]

theorem nw0_tz_center (ω : Lˣ) :
    (nw0 : ModGL .G2 L) * tz 1 ω⁻¹ * nw0⁻¹ = tz 1 ω := by
  rw [nw0_tz]
  simp

variable {L : Type} [Field L]

theorem tz3_eq_closure {ω : Lˣ} (hω3 : ω ^ 3 = 1)
    (hζ : IsPrimitiveRoot (ω : L) 3) :
    (tz3 : Subgroup (ModGL .G2 L)) =
      Subgroup.closure ({tz ω 1, tz 1 ω} : Set (ModGL .G2 L)) := by
  apply le_antisymm
  · rintro g ⟨s, t, hs, ht, rfl⟩
    have hsL : (s : L) ^ 3 = 1 := by simpa using congrArg (Units.val) hs
    have htL : (t : L) ^ 3 = 1 := by simpa using congrArg (Units.val) ht
    obtain ⟨i, -, hsi⟩ := hζ.eq_pow_of_pow_eq_one hsL
    obtain ⟨j, -, htj⟩ := hζ.eq_pow_of_pow_eq_one htL
    have hsi' : ω ^ i = s := Units.ext (by simpa using hsi)
    have htj' : ω ^ j = t := Units.ext (by simpa using htj)
    rw [← hsi', ← htj']
    have hpow : tz (ω ^ i) (ω ^ j) = (tz ω 1) ^ i * (tz 1 ω) ^ j := by
      rw [tz_pow, tz_pow, tz_mul]
      simp
    rw [hpow]
    exact Subgroup.mul_mem _
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) i)
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) j)
  · refine (Subgroup.closure_le _).2 ?_
    rintro g (rfl | rfl)
    · exact ⟨ω, 1, hω3, one_pow 3, rfl⟩
    · exact ⟨1, ω, one_pow 3, hω3, rfl⟩

theorem card_tz3 {ω : Lˣ} (hζ : IsPrimitiveRoot (ω : L) 3) :
    Nat.card (tz3 : Subgroup (ModGL .G2 L)) = 9 := by
  let f : (rootsOfUnity 3 L × rootsOfUnity 3 L) → (tz3 : Subgroup (ModGL .G2 L)) :=
    fun p => ⟨tz p.1 p.2, ⟨p.1, p.2, p.1.2, p.2.2, rfl⟩⟩
  have hf_inj : Function.Injective f := by
    rintro ⟨⟨s, hs⟩, ⟨t, ht⟩⟩ ⟨⟨s', hs'⟩, ⟨t', ht'⟩⟩ h
    have hst : (tz s t : ModGL .G2 L) = tz s' t' := congrArg Subtype.val h
    obtain ⟨h1, h2⟩ := tz_injective hst
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  have hf_surj : Function.Surjective f := by
    rintro ⟨g, s, t, hs, ht, hg⟩
    exact ⟨(⟨s, hs⟩, ⟨t, ht⟩), Subtype.ext hg.symm⟩
  have hcard : Nat.card (tz3 : Subgroup (ModGL .G2 L)) =
      Nat.card (rootsOfUnity 3 L × rootsOfUnity 3 L) :=
    Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩).symm
  rw [Nat.card_prod, IsPrimitiveRoot.card_rootsOfUnity hζ] at hcard
  simpa using hcard

theorem tz_mul_comm (s t s' t' : Lˣ) :
    (tz s t : ModGL .G2 L) * tz s' t' = tz s' t' * tz s t := by
  rw [tz_mul, tz_mul, mul_comm s s', mul_comm t t']

theorem yq_fix_tz_center (ω : Lˣ) (hω3 : ω ^ 3 = 1) :
    (yq : ModGL .G2 L) * tz 1 ω⁻¹ * yq⁻¹ = tz 1 ω⁻¹ := by
  have hω2 : ω ^ 2 = ω⁻¹ :=
    eq_inv_of_mul_eq_one_right (by rw [← pow_succ', show 2 + 1 = 3 by norm_num, hω3])
  have h3 : (ω⁻¹) ^ 3 = 1 := by rw [inv_pow, hω3, inv_one]
  have h2 : ((ω⁻¹) ^ 2)⁻¹ = ω⁻¹ := by
    rw [inv_pow, inv_inv, hω2]
  rw [yq_tz]
  congr 1
  · simp [h3]
  · simpa using h2

theorem extSub_eq_closure {G : Type} [Group G] {T : Subgroup G} {y : G} (hExt : Ext3 T y) :
    extSub hExt = Subgroup.closure (T ∪ {y}) := by
  apply le_antisymm
  · intro g hg
    rw [mem_extSub_iff hExt] at hg
    obtain ⟨t, ht, k, rfl⟩ := hg
    exact Subgroup.mul_mem _
      (Subgroup.subset_closure (Set.mem_union_left _ ht))
      (Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_union_right _ (Set.mem_singleton y))) k)
  · refine (Subgroup.closure_le _).2 ?_
    intro g hg
    rw [Set.mem_union] at hg
    rcases hg with hg | hg
    · exact le_extSub hExt hg
    · rw [Set.mem_singleton_iff] at hg
      subst hg
      exact y_mem_extSub hExt

theorem exists_rational_conj_fixed (K : Type) [Field K] [Finite K] :
    ∃ F : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, F c = c ^ Nat.card K) ∧
      ∀ n ∈ adjointGroup .G2 (AlgebraicClosure K),
        ∃ g ∈ adjointGroup .G2 (AlgebraicClosure K),
          Units.map (entrywiseHom F) g = g * n ∧
          ∀ s ∈ adjointGroup .G2 (AlgebraicClosure K),
            n * Units.map (entrywiseHom F) s * n⁻¹ = s →
            g * s * g⁻¹ ∈ (adjointGroup .G2 K).map
              (baseChangeGL (algebraMap K (AlgebraicClosure K))) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  set q := Nat.card K with hq
  have hℓ : (ringChar K).Prime := CharP.char_is_prime K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  obtain ⟨e, -, hqe⟩ := FiniteField.card K (ringChar K)
  let L := AlgebraicClosure K
  have : CharP L (ringChar K) := charP_of_injective_algebraMap (algebraMap K L).injective _
  have : ExpChar L (ringChar K) := ExpChar.prime hℓ
  set F : L →+* L := iterateFrobenius L (ringChar K) e
  have hF : ∀ c : L, F c = c ^ q := fun c => by
    rw [iterateFrobenius_def, hq, Nat.card_eq_fintype_card, hqe]
  refine ⟨F, hF, fun n hn => ?_⟩
  obtain ⟨S₁, hS, hLang⟩ :=
    (exceptional_all_characteristic_field_Lang_surjectivity (ringChar K) L (e : ℕ) e.pos).1 .G2
  obtain ⟨g₀, hg₀⟩ := hLang ⟨n, hn⟩
  set g : ModGL .G2 L := (g₀ : ModGL .G2 L) with hgdef
  have hFg : Units.map (entrywiseHom F) g = g * n := by
    have h := congrArg Subtype.val hg₀
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
    rw [hS] at h
    rw [h, mul_inv_cancel_left]
  refine ⟨g, g₀.2, hFg, fun s hs hns => ?_⟩
  have hfix := (CFSG.RankThree.Chevalley.G2_F4_exact_finite_field_fixed_root_matrices
    (τ := .G2) (Or.inl rfl) K (AlgebraicClosure K) F hF).1
  rw [← hfix]
  refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem g₀.2 hs) (inv_mem g₀.2), ?_⟩
  change Units.map (entrywiseHom F) (g * s * g⁻¹) = g * s * g⁻¹
  rw [map_mul, map_mul, map_inv, hFg]
  calc g * n * Units.map (entrywiseHom F) s * (g * n)⁻¹
      = g * (n * Units.map (entrywiseHom F) s * n⁻¹) * g⁻¹ := by group
    _ = g * s * g⁻¹ := by rw [hns]

theorem card_center_eq_three_of_card_27_of_noncomm
    {G : Type} [Group G] [Finite G] (hcard : Nat.card G = 27)
    (hnoncomm : ¬ IsMulCommutative G) :
    Nat.card (Subgroup.center G) = 3 := by
  classical
  let Z : Subgroup G := Subgroup.center G
  haveI : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  have hG3 : IsPGroup 3 G := IsPGroup.of_card (n := 3) (by rw [hcard]; norm_num)
  have hZ1 : 1 < Nat.card Z :=
    (Subgroup.one_lt_card_iff_ne_bot Z).mpr (ne_of_gt hG3.bot_lt_center)
  have hdvd : Nat.card Z ∣ 3 ^ 3 := by
    simpa [hcard] using Subgroup.card_subgroup_dvd_card Z
  obtain ⟨k, hk, hkcard⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  interval_cases k
  · rw [hkcard] at hZ1
    exact absurd hZ1 (by norm_num)
  · exact hkcard
  · have hZ9 : Nat.card Z = 9 := hkcard
    have hidx : Z.index = 3 := by
      rw [Subgroup.index_eq_card_div, hcard, hZ9]
    have hquot : Nat.card (G ⧸ Z) = 3 := by
      rw [← Subgroup.index_eq_card, hidx]
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    haveI : IsCyclic (G ⧸ Z) := isCyclic_of_prime_card (p := 3) hquot
    have hcomm : IsMulCommutative G := isMulCommutative_of_isCyclic_quotient_center_self G
    exact absurd hcomm hnoncomm
  · have hZtop : Z = ⊤ := Subgroup.eq_top_of_le_card (H := Z) (by rw [hcard, hkcard]; norm_num)
    have hcomm : IsMulCommutative G := Subgroup.center_eq_top_iff.mp hZtop
    exact absurd hcomm hnoncomm

theorem g2_sylow_three_inversion_transport
    {G : Type} [Group G] [Finite G]
    (S : Subgroup G) (hS27 : Nat.card S = 27)
    (hSsyl : ∃ P : Sylow 3 G, (P : Subgroup G) = S)
    (z : ↥S) (hzcenter : Subgroup.center ↥S = zpowers z)
    (t : G) (ht2 : orderOf t = 2)
    (htinv : t * (z : G) * t⁻¹ = (z : G)⁻¹) :
    ∀ (Q : Sylow 3 G) (w : G),
      w ∈ (Q : Subgroup G) → w ∈ Subgroup.centralizer ((Q : Subgroup G) : Set G) →
      orderOf w = 3 → ∃ u : G, orderOf u = 2 ∧ u * w * u⁻¹ = w⁻¹ := by
  classical
  obtain ⟨SylS, hSylS⟩ := hSsyl
  intro Q w hwQ hwc hw3
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G SylS Q
  have hQ : (Q : Subgroup G) = S.map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, hSylS]
    ext x
    constructor <;> rintro ⟨y, hy, rfl⟩ <;> exact ⟨y, hy, rfl⟩
  let w' : G := g⁻¹ * w * g
  have hwS : w ∈ S.map (MulAut.conj g).toMonoidHom := by
    rw [hQ] at hwQ
    exact hwQ
  obtain ⟨s, hs, hsw⟩ := Subgroup.mem_map.mp hwS
  have hw'S : w' ∈ S := by
    have hw'eq : w' = s := by
      dsimp [w']
      rw [← hsw]
      change g⁻¹ * (g * s * g⁻¹) * g = s
      group
    rwa [hw'eq]
  let wS : ↥S := ⟨w', hw'S⟩
  have hw'center : wS ∈ Subgroup.center ↥S := by
    rw [Subgroup.mem_center_iff]
    intro s
    apply Subtype.ext
    have hgs : g * (s : G) * g⁻¹ ∈ (Q : Subgroup G) := by
      rw [hQ]
      exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom s.2
    have hcomm := Subgroup.mem_centralizer_iff.mp hwc (g * (s : G) * g⁻¹) hgs
    have hconj : g * ((s : G) * w') * g⁻¹ = g * (w' * (s : G)) * g⁻¹ := by
      calc g * ((s : G) * w') * g⁻¹ = (g * (s : G) * g⁻¹) * w := by
            dsimp [w']
            group
        _ = w * (g * (s : G) * g⁻¹) := hcomm
        _ = g * (w' * (s : G)) * g⁻¹ := by
            dsimp [w']
            group
    exact (MulAut.conj g).injective hconj
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (by rw [← hzcenter]; exact hw'center)
  have hwk : w' = (z : G) ^ k := by
    have h := congrArg Subtype.val hk
    simpa [wS] using h.symm
  have hw'inv : t * w' * t⁻¹ = w'⁻¹ := by
    rw [hwk]
    calc t * z ^ k * t⁻¹ = (t * z * t⁻¹) ^ k := by rw [conj_zpow]
      _ = (z⁻¹) ^ k := by rw [htinv]; simp
      _ = (z ^ k)⁻¹ := by simp
  refine ⟨g * t * g⁻¹, ?_, ?_⟩
  · change orderOf ((MulAut.conj g) t) = 2
    exact ((MulAut.conj g).orderOf_eq t).trans ht2
  · calc (g * t * g⁻¹) * w * (g * t * g⁻¹)⁻¹ = g * (t * w' * t⁻¹) * g⁻¹ := by
          dsimp [w']
          group
      _ = g * w'⁻¹ * g⁻¹ := by rw [hw'inv]
      _ = w⁻¹ := by
          dsimp [w']
          group

section Concrete

variable {K : Type} [Field K] [Finite K]

theorem g2_concrete_heisenberg (h3 : ¬ 3 ∣ Nat.card K) :
    ∃ (S : Subgroup (adjointGroup .G2 K)) (z : ↥S) (t : adjointGroup .G2 K),
      Nat.card S = 27 ∧ Subgroup.center ↥S = zpowers z ∧
      orderOf (z : adjointGroup .G2 K) = 3 ∧ orderOf t = 2 ∧
      t * (z : adjointGroup .G2 K) * t⁻¹ = (z : adjointGroup .G2 K)⁻¹ := by
  classical
  have hne : (3 : K) ≠ 0 := by
    intro h
    apply h3
    have hℓ : (ringChar K).Prime := CharP.char_is_prime K (ringChar K)
    have hp : ringChar K = 3 := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1
      ((CharP.cast_eq_zero_iff K (ringChar K) 3).1 (by exact_mod_cast h))
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨e, -, hqe⟩ := FiniteField.card K (ringChar K)
    rw [Nat.card_eq_fintype_card, hqe, hp]
    exact dvd_pow_self 3 e.ne_zero
  have : NeZero ((3 : ℕ) : K) := ⟨by exact_mod_cast hne⟩
  let L := AlgebraicClosure K
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.prim (M := L) (n := 3)
  set ω : Lˣ := (hζ.isUnit (by norm_num)).unit with hωdef
  have hζω : IsPrimitiveRoot (ω : L) 3 := by simpa [hωdef] using hζ
  have hω3 : ω ^ 3 = 1 := Units.ext (by simpa [hωdef] using hζ.pow_eq_one)
  have hω1 : ω ≠ 1 := fun h =>
    hζ.ne_one (by norm_num) (by simpa [hωdef] using congrArg Units.val h)
  obtain ⟨F, hF, hTW⟩ := exists_rational_conj_fixed K
  have hq3 : Nat.card K % 3 = 1 ∨ Nat.card K % 3 = 2 := by omega
  have hFω : Units.map (F : L →* L) ω = ω ^ Nat.card K :=
    Units.ext (by simp [hF])
  obtain ⟨n, hn, hn_case, hnx, hnx2, hny⟩ : ∃ n : ModGL .G2 L,
      n ∈ adjointGroup .G2 L ∧ (n = 1 ∨ n = nw0) ∧
      n * Units.map (entrywiseHom F) (tz ω 1 : ModGL .G2 L) * n⁻¹ = tz ω 1 ∧
      n * Units.map (entrywiseHom F) (tz 1 ω : ModGL .G2 L) * n⁻¹ = tz 1 ω ∧
      n * Units.map (entrywiseHom F) (yq : ModGL .G2 L) * n⁻¹ = yq := by
    rcases hq3 with h1 | h2
    · have hωq : ω ^ Nat.card K = ω := by
        rw [← Nat.div_add_mod (Nat.card K) 3, h1, pow_add, pow_mul, hω3, one_pow, one_mul,
          pow_one]
      refine ⟨1, one_mem _, Or.inl rfl, ?_, ?_, ?_⟩
      · rw [frob_tz, hFω, hωq, map_one]
        group
      · rw [frob_tz, hFω, hωq, map_one]
        group
      · rw [frob_yq]
        group
    · have hωq : ω ^ Nat.card K = ω⁻¹ := by
        rw [← Nat.div_add_mod (Nat.card K) 3, h2, pow_add, pow_mul, hω3, one_pow, one_mul]
        refine eq_inv_of_mul_eq_one_left ?_
        rw [← pow_succ]
        exact hω3
      refine ⟨nw0, nw0_mem_adjointGroup, Or.inr rfl, ?_, ?_, ?_⟩
      · rw [frob_tz, hFω, hωq, map_one, nw0_tz, inv_inv, inv_one]
      · rw [frob_tz, hFω, hωq, map_one, nw0_tz, inv_inv, inv_one]
      · rw [frob_yq, nw0_comm_yq]
        group
  obtain ⟨g, hg, hFg, hrat⟩ := hTW n hn
  obtain ⟨x, hxG, hx⟩ := hrat _ (tz_mem_adjointGroup ω 1) hnx
  obtain ⟨x2, hx2G, hx2⟩ := hrat _ (tz_mem_adjointGroup 1 ω) hnx2
  obtain ⟨y, hyG, hy⟩ := hrat _ yq_mem_adjointGroup hny
  let φ : adjointGroup .G2 K →* ModGL .G2 L :=
    (baseChangeGL (τ := .G2) (algebraMap K L)).comp (adjointGroup .G2 K).subtype
  have hφ_inj : Function.Injective φ :=
    (baseChangeGL_injective (τ := .G2) (algebraMap K L)).comp Subtype.val_injective
  let xK : adjointGroup .G2 K := ⟨x, hxG⟩
  let x2K : adjointGroup .G2 K := ⟨x2, hx2G⟩
  let yK : adjointGroup .G2 K := ⟨y, hyG⟩
  let S : Subgroup (adjointGroup .G2 K) := Subgroup.closure {xK, x2K, yK}
  let z0 : ModGL .G2 L := tz 1 ω⁻¹
  have hxA : (tz ω 1 : ModGL .G2 L) ∈ extSub (ext3_tz3 hω1) := by
    refine le_extSub (ext3_tz3 hω1) ?_
    rw [tz3_eq_closure hω3 hζω]
    exact Subgroup.subset_closure (by simp)
  have hx2A : (tz 1 ω : ModGL .G2 L) ∈ extSub (ext3_tz3 hω1) := by
    refine le_extSub (ext3_tz3 hω1) ?_
    rw [tz3_eq_closure hω3 hζω]
    exact Subgroup.subset_closure (by simp)
  have hyA : (yq : ModGL .G2 L) ∈ extSub (ext3_tz3 hω1) := y_mem_extSub (ext3_tz3 hω1)
  have hz0A : z0 ∈ extSub (ext3_tz3 hω1) := by
    refine le_extSub (ext3_tz3 hω1) ?_
    refine ⟨1, ω⁻¹, one_pow 3, ?_, rfl⟩
    rw [inv_pow, hω3, inv_one]
  have hsub : ({tz ω 1, tz 1 ω} : Set (ModGL .G2 L)) ⊆
      ({tz ω 1, tz 1 ω, yq} : Set (ModGL .G2 L)) := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
    rcases hz with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  have hA_eq : extSub (ext3_tz3 hω1) = Subgroup.closure
      ({tz ω 1, tz 1 ω, yq} : Set (ModGL .G2 L)) := by
    rw [extSub_eq_closure, tz3_eq_closure hω3 hζω]
    apply le_antisymm
    · refine (Subgroup.closure_le _).2 ?_
      intro g hg
      rw [Set.mem_union] at hg
      rcases hg with hg | hg
      · exact Subgroup.closure_mono hsub hg
      · rw [Set.mem_singleton_iff] at hg
        subst hg
        exact Subgroup.subset_closure (by simp)
    · refine (Subgroup.closure_le _).2 ?_
      intro g hg
      rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl
      · exact Subgroup.subset_closure
          (Set.mem_union_left _ (Subgroup.subset_closure (by simp)))
      · exact Subgroup.subset_closure
          (Set.mem_union_left _ (Subgroup.subset_closure (by simp)))
      · exact Subgroup.subset_closure (Set.mem_union_right _ (by simp))
  have hφx : φ xK = g * tz ω 1 * g⁻¹ := hx
  have hφx2 : φ x2K = g * tz 1 ω * g⁻¹ := hx2
  have hφy : φ yK = g * yq * g⁻¹ := hy
  have hSmap : S.map φ = (extSub (ext3_tz3 hω1)).map (MulAut.conj g).toMonoidHom := by
    change (Subgroup.closure ({xK, x2K, yK} : Set (adjointGroup .G2 K))).map φ =
      (extSub (ext3_tz3 hω1)).map (MulAut.conj g).toMonoidHom
    rw [hA_eq, MonoidHom.map_closure, MonoidHom.map_closure]
    congr 1
    ext z
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨w, rfl | rfl | rfl, rfl⟩
      · exact ⟨tz ω 1, by simp, hφx.symm⟩
      · exact ⟨tz 1 ω, by simp, hφx2.symm⟩
      · exact ⟨yq, by simp, hφy.symm⟩
    · rintro ⟨w, rfl | rfl | rfl, rfl⟩
      · exact ⟨xK, by simp, hφx⟩
      · exact ⟨x2K, by simp, hφx2⟩
      · exact ⟨yK, by simp, hφy⟩
  have hScard : Nat.card S = 27 := by
    calc Nat.card S = Nat.card (S.map φ) :=
          (Subgroup.card_map_of_injective hφ_inj).symm
      _ = Nat.card ((extSub (ext3_tz3 hω1)).map (MulAut.conj g).toMonoidHom) := by rw [hSmap]
      _ = Nat.card (extSub (ext3_tz3 hω1)) := Subgroup.card_map_of_injective (MulAut.conj g).injective
      _ = 3 * Nat.card (tz3 : Subgroup (ModGL .G2 L)) := card_extSub (ext3_tz3 hω1)
      _ = 27 := by rw [card_tz3 hζω]
  have hS_exp : ∀ s ∈ S, s ^ 3 = 1 := by
    intro s hs
    apply hφ_inj
    rw [map_pow, map_one]
    have hmem : φ s ∈ (extSub (ext3_tz3 hω1)).map (MulAut.conj g).toMonoidHom := by
      rw [← hSmap]
      exact Subgroup.mem_map_of_mem φ hs
    obtain ⟨a, ha, haeq⟩ := hmem
    rw [← haeq]
    have ha3 : a ^ 3 = 1 := pow_three_of_mem_extSub hω1 ha
    calc ((MulAut.conj g) a) ^ 3 = (MulAut.conj g) (a ^ 3) := by rw [map_pow]
      _ = 1 := by rw [ha3, map_one]
  have hxy_ne : (tz ω 1 : ModGL .G2 L) * yq ≠ yq * tz ω 1 := by
    intro h
    have hyconj : (yq : ModGL .G2 L) * tz ω 1 * yq⁻¹ = tz ω ω := by
      rw [yq_tz]
      congr 1 <;> simp [hω3]
    have hxeq : (tz ω 1 : ModGL .G2 L) = tz ω ω := by
      calc tz ω 1 = (tz ω 1 * yq) * yq⁻¹ := by group
        _ = (yq * tz ω 1) * yq⁻¹ := by rw [h]
        _ = tz ω ω := hyconj
    have := (tz_injective hxeq).2
    exact hω1 (by simpa using this.symm)
  have hxyK_ne : xK * yK ≠ yK * xK := by
    intro h
    apply hxy_ne
    have h' := congrArg φ h
    rw [map_mul, map_mul, hφx, hφy] at h'
    have := congrArg (fun z => g⁻¹ * z * g) h'
    simpa [mul_assoc] using this
  have hzS : ⁅xK, yK⁆ ∈ S := by
    have hxS : xK ∈ S := Subgroup.subset_closure (by simp)
    have hyS : yK ∈ S := Subgroup.subset_closure (by simp)
    simpa using (Subgroup.commutator_le_sup S S) (Subgroup.commutator_mem_commutator hxS hyS)
  let zK : ↥S := ⟨⁅xK, yK⁆, hzS⟩
  have hzK_cube : (zK : adjointGroup .G2 K) ^ 3 = 1 := hS_exp zK.1 zK.2
  have hzK_ne : (zK : adjointGroup .G2 K) ≠ 1 := by
    intro h
    apply hxyK_ne
    exact commutatorElement_eq_one_iff_mul_comm.mp h
  have hzK_order : orderOf (zK : adjointGroup .G2 K) = 3 :=
    orderOf_eq_prime hzK_cube hzK_ne
  have hz0_centerA : (⟨z0, hz0A⟩ : ↥(extSub (ext3_tz3 hω1))) ∈ Subgroup.center ↥(extSub (ext3_tz3 hω1)) := by
    rw [Subgroup.mem_center_iff]
    intro a
    apply Subtype.ext
    have hmem : a.1 ∈ Subgroup.closure ({tz ω 1, tz 1 ω, yq} : Set (ModGL .G2 L)) := by
      rw [← hA_eq]
      exact a.2
    have hC : Subgroup.closure ({tz ω 1, tz 1 ω, yq} : Set (ModGL .G2 L)) ≤
        Subgroup.centralizer ({z0} : Set (ModGL .G2 L)) := by
      refine (Subgroup.closure_le _).2 ?_
      rintro g (rfl | rfl | rfl)
      · change ∀ h ∈ ({z0} : Set (ModGL .G2 L)), h * (tz ω 1) = (tz ω 1) * h
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact (tz_mul_comm ω 1 1 ω⁻¹).symm
      · change ∀ h ∈ ({z0} : Set (ModGL .G2 L)), h * (tz 1 ω) = (tz 1 ω) * h
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact (tz_mul_comm 1 ω 1 ω⁻¹).symm
      · change ∀ h ∈ ({z0} : Set (ModGL .G2 L)), h * (yq : ModGL .G2 L) = yq * h
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        have hyq : (yq : ModGL .G2 L) * z0 = z0 * yq := by
          calc yq * z0 = (yq * z0 * yq⁻¹) * yq := by group
            _ = z0 * yq := by rw [yq_fix_tz_center ω hω3]
        exact hyq.symm
    have hcomm := Subgroup.mem_centralizer_iff.mp (hC hmem) z0 (by simp)
    exact hcomm.symm
  have hzK_center : zK ∈ Subgroup.center ↥S := by
    rw [Subgroup.mem_center_iff]
    intro s
    apply Subtype.ext
    apply hφ_inj
    change φ ((s : adjointGroup .G2 K) * (zK : adjointGroup .G2 K)) =
      φ ((zK : adjointGroup .G2 K) * (s : adjointGroup .G2 K))
    have hmem : φ s ∈ (extSub (ext3_tz3 hω1)).map (MulAut.conj g).toMonoidHom := by
      rw [← hSmap]
      exact Subgroup.mem_map_of_mem φ (show (s : adjointGroup .G2 K) ∈ S from s.2)
    obtain ⟨a, ha, haeq⟩ := hmem
    have hz0a : (⟨z0, hz0A⟩ : ↥(extSub (ext3_tz3 hω1))) ∈ Subgroup.center ↥(extSub (ext3_tz3 hω1)) := hz0_centerA
    have hza : a * z0 = z0 * a := congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz0a) ⟨a, ha⟩)
    have hφz : φ zK = g * z0 * g⁻¹ := by
      have h1 : φ zK = ⁅φ xK, φ yK⁆ := by
        change φ ⁅xK, yK⁆ = ⁅φ xK, φ yK⁆
        rw [map_commutatorElement]
      rw [h1, hφx, hφy]
      have hconj : ⁅g * tz ω 1 * g⁻¹, g * yq * g⁻¹⁆ = (MulAut.conj g) ⁅tz ω 1, yq⁆ := by
        simp only [commutatorElement_def, MulAut.conj_apply]
        group
      rw [hconj]
      rw [commutator_tz_yq ω (by simpa using congrArg Units.val hω3)]
      rfl
    rw [map_mul, map_mul, hφz, ← haeq]
    calc g * a * g⁻¹ * (g * z0 * g⁻¹) = g * (a * z0) * g⁻¹ := by group
      _ = g * (z0 * a) * g⁻¹ := by rw [hza]
      _ = g * z0 * g⁻¹ * (g * a * g⁻¹) := by group
  have hS_noncomm : ¬ IsMulCommutative ↥S := by
    intro hcomm
    apply hxyK_ne
    have hxS : xK ∈ S := Subgroup.subset_closure (by simp)
    have hyS : yK ∈ S := Subgroup.subset_closure (by simp)
    have h := hcomm.is_comm.comm ⟨xK, hxS⟩ ⟨yK, hyS⟩
    exact congrArg Subtype.val h
  have hcenterS : Subgroup.center ↥S = zpowers zK := by
    have hZcard : Nat.card (Subgroup.center ↥S) = 3 :=
      card_center_eq_three_of_card_27_of_noncomm hScard hS_noncomm
    have hzpow_le : zpowers zK ≤ Subgroup.center ↥S := Subgroup.zpowers_le.mpr hzK_center
    have hcard_eq : Nat.card (Subgroup.center ↥S) = Nat.card (zpowers zK) := by
      have hord : orderOf zK = 3 := (Subgroup.orderOf_coe zK).symm.trans hzK_order
      rw [hZcard, Nat.card_zpowers, hord]
    exact (Subgroup.eq_of_le_of_card_ge hzpow_le hcard_eq.le).symm
  let t_alg : ModGL .G2 L := g * nw0 * g⁻¹
  have ht_alg_eq : t_alg = g * nw0 * g⁻¹ := rfl
  have ht_alg_adj : t_alg ∈ adjointGroup .G2 L :=
    mul_mem (mul_mem hg nw0_mem_adjointGroup) (inv_mem hg)
  have ht_alg_sq : t_alg ^ 2 = 1 := by
    rw [ht_alg_eq]
    calc (g * nw0 * g⁻¹) ^ 2 = (g * nw0 * g⁻¹) * (g * nw0 * g⁻¹) := by rw [pow_two]
      _ = g * (nw0 * nw0) * g⁻¹ := by group
      _ = 1 := by rw [← pow_two, nw0_sq]; group
  have ht_alg_fixed : Units.map (entrywiseHom F) t_alg = t_alg := by
    rw [ht_alg_eq]
    rw [map_mul, map_mul, map_inv, hFg]
    rcases hn_case with h1 | h2
    · rw [h1, frob_nw0]
      group
    · rw [h2, frob_nw0]
      group
  have ht_mem_map : t_alg ∈
      (adjointGroup .G2 K).map (baseChangeGL (τ := .G2) (algebraMap K L)) := by
    have hfix := (CFSG.RankThree.Chevalley.G2_F4_exact_finite_field_fixed_root_matrices
      (τ := .G2) (Or.inl rfl) K L F hF).1
    rw [← hfix]
    refine ⟨ht_alg_adj, ?_⟩
    simpa using ht_alg_fixed
  obtain ⟨t, htG, htbase⟩ := ht_mem_map
  let tK : adjointGroup .G2 K := ⟨t, htG⟩
  have hφt : φ tK = t_alg := htbase
  have htK_sq : tK ^ 2 = 1 := by
    apply hφ_inj
    rw [map_pow, hφt, ht_alg_sq, map_one]
  have hφz' : φ zK = g * z0 * g⁻¹ := by
    have h1 : φ zK = ⁅φ xK, φ yK⁆ := by
      change φ ⁅xK, yK⁆ = ⁅φ xK, φ yK⁆
      rw [map_commutatorElement]
    rw [h1, hφx, hφy]
    have hconj : ⁅g * tz ω 1 * g⁻¹, g * yq * g⁻¹⁆ = (MulAut.conj g) ⁅tz ω 1, yq⁆ := by
      simp only [commutatorElement_def, MulAut.conj_apply]
      group
    rw [hconj]
    rw [commutator_tz_yq ω (by simpa using congrArg Units.val hω3)]
    rfl
  have htK_inv : tK * zK * tK⁻¹ = zK⁻¹ := by
    apply hφ_inj
    simp only [map_mul, map_inv, hφt, hφz']
    rw [ht_alg_eq]
    change (g * nw0 * g⁻¹) * (g * z0 * g⁻¹) * (g * nw0 * g⁻¹)⁻¹ = (φ zK)⁻¹
    rw [hφz']
    calc (g * nw0 * g⁻¹) * (g * z0 * g⁻¹) * (g * nw0 * g⁻¹)⁻¹
        = g * (nw0 * z0 * nw0⁻¹) * g⁻¹ := by group
      _ = g * z0⁻¹ * g⁻¹ := by
        have hz0inv : z0⁻¹ = tz 1 ω := by
          rw [show z0 = tz 1 ω⁻¹ from rfl, tz_inv]
          simp
        rw [nw0_tz_center ω, hz0inv]
      _ = (g * z0 * g⁻¹)⁻¹ := by group
  have htK_ne : tK ≠ 1 := by
    intro h1
    have hz_eq : zK = zK⁻¹ := by
      have h := htK_inv
      rw [h1] at h
      apply Subtype.ext
      simpa using h
    have hz2 : zK ^ 2 = 1 := by
      have h := mul_inv_cancel zK
      rw [← hz_eq] at h
      simpa [pow_two] using h
    have hdvd : orderOf zK ∣ 2 := orderOf_dvd_of_pow_eq_one hz2
    have hord : orderOf zK = 3 := (Subgroup.orderOf_coe zK).symm.trans hzK_order
    rw [hord] at hdvd
    norm_num at hdvd
  have htK_order : orderOf tK = 2 := orderOf_eq_prime htK_sq htK_ne
  exact ⟨S, zK, tK, hScard, hcenterS, hzK_order, htK_order, htK_inv⟩

end Concrete

section Specialisations

variable {K : Type} [Field K] [Finite K]

theorem g2_sylow_inversion_of_card_five (hK : Nat.card K = 5) :
    ∀ (Q : Sylow 3 (adjointGroup .G2 K)) (z : adjointGroup .G2 K),
      z ∈ (Q : Subgroup (adjointGroup .G2 K)) →
      z ∈ Subgroup.centralizer ((Q : Subgroup (adjointGroup .G2 K)) : Set (adjointGroup .G2 K)) →
      orderOf z = 3 → ∃ t : adjointGroup .G2 K, orderOf t = 2 ∧
        t * z * t⁻¹ = z⁻¹ := by
  classical
  obtain ⟨S, z0, t, hS27, hcenter, hzord, ht2, htinv⟩ :=
    g2_concrete_heisenberg (K := K) (by rw [hK]; norm_num)
  have hS3 : IsPGroup 3 S := IsPGroup.of_card (n := 3) (by rw [hS27]; norm_num)
  have hidx : ¬ 3 ∣ S.index := by
    rw [Subgroup.index_eq_card_div, hS27,
      CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hK]
    norm_num [CFSG.Open.ordG2]
  exact g2_sylow_three_inversion_transport S hS27 ⟨hS3.toSylow hidx, rfl⟩
    z0 hcenter t ht2 htinv

theorem g2_sylow_inversion_of_card_seven (hK : Nat.card K = 7) :
    ∀ (Q : Sylow 3 (adjointGroup .G2 K)) (z : adjointGroup .G2 K),
      z ∈ (Q : Subgroup (adjointGroup .G2 K)) →
      z ∈ Subgroup.centralizer ((Q : Subgroup (adjointGroup .G2 K)) : Set (adjointGroup .G2 K)) →
      orderOf z = 3 → ∃ t : adjointGroup .G2 K, orderOf t = 2 ∧
        t * z * t⁻¹ = z⁻¹ := by
  classical
  obtain ⟨S, z0, t, hS27, hcenter, hzord, ht2, htinv⟩ :=
    g2_concrete_heisenberg (K := K) (by rw [hK]; norm_num)
  have hS3 : IsPGroup 3 S := IsPGroup.of_card (n := 3) (by rw [hS27]; norm_num)
  have hidx : ¬ 3 ∣ S.index := by
    rw [Subgroup.index_eq_card_div, hS27,
      CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hK]
    norm_num [CFSG.Open.ordG2]
  exact g2_sylow_three_inversion_transport S hS27 ⟨hS3.toSylow hidx, rfl⟩
    z0 hcenter t ht2 htinv

end Specialisations

theorem g2_five_inverting_of_lieModel
    {X : Type} [Group X] [Finite X]
    (hX : CFSG.Blueprint.LieModel X .G2 0 5 1)
    (Q : Sylow 3 X) {z : X}
    (hzQ : z ∈ (Q : Subgroup X))
    (hzc : z ∈ Subgroup.centralizer ((Q : Subgroup X) : Set X))
    (hz3 : orderOf z = 3) :
    ∃ t : X, orderOf t = 2 ∧ t * z * t⁻¹ = z⁻¹ := by
  classical
  have hp : Nat.Prime 5 := by norm_num
  have hc : CFSG.Blueprint.ChevalleyExceptionalModel X .G2 5 1 :=
    CFSG.Blueprint.LieModel.chevalleyExceptionalModel hX (by decide)
  have hm : CFSG.Blueprint.UntwistedChevalleyModel X .G2 (5 ^ 1) := hc.2
  obtain ⟨K, hKfield, hKfinite, hKcard, ⟨eX⟩⟩ :=
    CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup (τ := .G2) hm
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  have hK5 : Nat.card K = 5 := by simpa using hKcard
  let Q' : Sylow 3 (adjointGroup .G2 K) :=
    Sylow.mapSurjective (f := eX.toMonoidHom) eX.surjective Q
  let z' : adjointGroup .G2 K := eX z
  have hQ' : (Q' : Subgroup (adjointGroup .G2 K)) =
      (Q : Subgroup X).map eX.toMonoidHom := by
    simp [Q']
  have hzQ' : z' ∈ (Q' : Subgroup (adjointGroup .G2 K)) := by
    rw [hQ']
    exact Subgroup.mem_map_of_mem eX.toMonoidHom hzQ
  have hzc' : z' ∈ Subgroup.centralizer
      ((Q' : Subgroup (adjointGroup .G2 K)) : Set (adjointGroup .G2 K)) := by
    rw [Subgroup.mem_centralizer_iff] at hzc ⊢
    intro y hy
    rw [hQ'] at hy
    obtain ⟨q, hq, rfl⟩ := hy
    simpa only [map_mul, z', MulEquiv.coe_toMonoidHom] using congrArg eX.toMonoidHom
      (Subgroup.mem_centralizer_iff.mp hzc q hq)
  have hz3' : orderOf z' = 3 := by
    simpa [z'] using (MulEquiv.orderOf_eq eX z).trans hz3
  obtain ⟨t', ht'2, ht'inv⟩ :=
    g2_sylow_inversion_of_card_five hK5 Q' z' hzQ' hzc' hz3'
  refine ⟨eX.symm t', ?_, ?_⟩
  · rw [← (MulEquiv.orderOf_eq eX (eX.symm t')), eX.apply_symm_apply, ht'2]
  · apply eX.injective
    rw [map_mul, map_mul, map_inv, eX.apply_symm_apply, map_inv]
    exact ht'inv

theorem g2_seven_inverting_of_lieModel
    {X : Type} [Group X] [Finite X]
    (hX : CFSG.Blueprint.LieModel X .G2 0 7 1)
    (Q : Sylow 3 X) {z : X}
    (hzQ : z ∈ (Q : Subgroup X))
    (hzc : z ∈ Subgroup.centralizer ((Q : Subgroup X) : Set X))
    (hz3 : orderOf z = 3) :
    ∃ t : X, orderOf t = 2 ∧ t * z * t⁻¹ = z⁻¹ := by
  classical
  have hp : Nat.Prime 7 := by norm_num
  have hc : CFSG.Blueprint.ChevalleyExceptionalModel X .G2 7 1 :=
    CFSG.Blueprint.LieModel.chevalleyExceptionalModel hX (by decide)
  have hm : CFSG.Blueprint.UntwistedChevalleyModel X .G2 (7 ^ 1) := hc.2
  obtain ⟨K, hKfield, hKfinite, hKcard, ⟨eX⟩⟩ :=
    CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup (τ := .G2) hm
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  have hK7 : Nat.card K = 7 := by simpa using hKcard
  let Q' : Sylow 3 (adjointGroup .G2 K) :=
    Sylow.mapSurjective (f := eX.toMonoidHom) eX.surjective Q
  let z' : adjointGroup .G2 K := eX z
  have hQ' : (Q' : Subgroup (adjointGroup .G2 K)) =
      (Q : Subgroup X).map eX.toMonoidHom := by
    simp [Q']
  have hzQ' : z' ∈ (Q' : Subgroup (adjointGroup .G2 K)) := by
    rw [hQ']
    exact Subgroup.mem_map_of_mem eX.toMonoidHom hzQ
  have hzc' : z' ∈ Subgroup.centralizer
      ((Q' : Subgroup (adjointGroup .G2 K)) : Set (adjointGroup .G2 K)) := by
    rw [Subgroup.mem_centralizer_iff] at hzc ⊢
    intro y hy
    rw [hQ'] at hy
    obtain ⟨q, hq, rfl⟩ := hy
    simpa only [map_mul, z', MulEquiv.coe_toMonoidHom] using congrArg eX.toMonoidHom
      (Subgroup.mem_centralizer_iff.mp hzc q hq)
  have hz3' : orderOf z' = 3 := by
    simpa [z'] using (MulEquiv.orderOf_eq eX z).trans hz3
  obtain ⟨t', ht'2, ht'inv⟩ :=
    g2_sylow_inversion_of_card_seven hK7 Q' z' hzQ' hzc' hz3'
  refine ⟨eX.symm t', ?_, ?_⟩
  · rw [← (MulEquiv.orderOf_eq eX (eX.symm t')), eX.apply_symm_apply, ht'2]
  · apply eX.injective
    rw [map_mul, map_mul, map_inv, eX.apply_symm_apply, map_inv]
    exact ht'inv

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

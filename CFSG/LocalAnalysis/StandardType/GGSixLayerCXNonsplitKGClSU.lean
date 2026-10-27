module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGClLift
public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivSUTag
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplit

public section

namespace CFSG.StandardType

namespace ClNonsplit

open CFSG.Assembly Matrix LayerCores LayerFacts CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K] {f n : ℕ} {G : Type*} [Group G]
  {ψ : ↥(unitarySU 2 f K n) →* G}

theorem exists_prime_dvd_two_pow_add_one (f : ℕ) : ∃ q, q.Prime ∧ q ∣ 2 ^ f + 1 :=
  Nat.exists_prime_and_dvd (show 2 ^ f + 1 ≠ 1 by have := Nat.one_le_two_pow (n := f); omega)

theorem exists_mem_suPairs_pow_eq_one [Finite K] (h : UnitaryFieldData 2 f K) (hn : 3 ≤ n)
    (hnq : (n, 2 ^ f) ≠ (3, 2)) (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 f K n)) {p : ℕ}
    (hp : p.Prime) (hpK : ¬ p ∣ Nat.card K - 1) {x : G} (hx : x ^ p = 1) {A : GL (Fin n) K}
    (hA : (x, A) ∈ SUTorus.suPairs ψ) :
    ∃ A' : GL (Fin n) K, (x, A') ∈ SUTorus.suPairs ψ ∧ A' ^ p = 1 := by
  obtain ⟨q, hq, hqd⟩ := exists_prime_dvd_two_pow_add_one f
  have h1 := (SUTorus.suPairs ψ).pow_mem hA p
  rw [Prod.pow_mk, hx] at h1
  obtain ⟨c, hc⟩ := SUTorus.exists_scalar_of_mem_suPairs_one h hn hnq hq hqd hker h1
  obtain ⟨ν, hν⟩ := (Nat.Coprime.pow_left_bijective (LinNonsplit.coprime_card_units hp hpK)).2 c
  refine ⟨GeneralLinearGroup.scalar (Fin n) ν⁻¹ * A, ?_, ?_⟩
  · have h2 := (SUTorus.suPairs ψ).mul_mem (SUTorus.one_scalar_mem_suPairs ψ ν⁻¹) hA
    rwa [Prod.mk_mul_mk, one_mul] at h2
  · rw [(TypeA.PGLTor.commute_scalar ν⁻¹ A).mul_pow, hc, ← map_pow, ← map_mul, inv_pow]
    simp only at hν
    rw [hν, inv_mul_cancel, map_one]

theorem suAdj_pow_mul_pow (h : UnitaryFieldData 2 f K) {A : GL (Fin n) K} {c : K}
    (hc : suAdj h (A : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) =
      c • (1 : Matrix (Fin n) (Fin n) K)) (k : ℕ) :
    suAdj h ((A ^ k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((A ^ k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      c ^ k • (1 : Matrix (Fin n) (Fin n) K) := by
  induction k with
  | zero => simp [(isInvol_suAdj (n := n) h).map_one]
  | succ k ih =>
    rw [pow_succ, Units.val_mul, (isInvol_suAdj h).map_mul]
    calc suAdj h (A : Matrix (Fin n) (Fin n) K) *
          suAdj h ((A ^ k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          (((A ^ k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K))
        = suAdj h (A : Matrix (Fin n) (Fin n) K) *
          (suAdj h ((A ^ k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((A ^ k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
          (A : Matrix (Fin n) (Fin n) K) := by simp only [Matrix.mul_assoc]
      _ = c ^ (k + 1) • (1 : Matrix (Fin n) (Fin n) K) := by
          rw [ih, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hc, smul_smul, pow_succ,
            mul_comm]

theorem mem_unitaryOf_of_pow_eq_one [Finite K] (h : UnitaryFieldData 2 f K) (hn : 1 ≤ n)
    {p : ℕ} (hp : p.Prime) (hpK : ¬ p ∣ Nat.card K - 1) {A : GL (Fin n) K}
    (hAN : A ∈ Subgroup.normalizer (unitarySU 2 f K n : Set (GL (Fin n) K))) (hAp : A ^ p = 1) :
    A ∈ unitaryOf (isInvol_suAdj h) := by
  obtain ⟨c, hc⟩ := exists_suAdj_mul_eq_smul h hAN
  have h1 := suAdj_pow_mul_pow h hc p
  rw [hAp, Units.val_one, (isInvol_suAdj h).map_one, Matrix.one_mul] at h1
  have hcp : c ^ p = 1 := by
    have h2 := congrFun (congrFun h1 ⟨0, hn⟩) ⟨0, hn⟩
    simpa using h2.symm
  have hc0 : c ≠ 0 := fun h0 => by
    rw [h0, zero_pow hp.ne_zero] at hcp
    exact zero_ne_one hcp
  have hc1 : c = 1 := by
    have hu : (Units.mk0 c hc0) ^ p = 1 := Units.ext (by simpa using hcp)
    have ho : orderOf (Units.mk0 c hc0) = 1 :=
      Nat.eq_one_of_dvd_coprimes (LinNonsplit.coprime_card_units hp hpK).symm
        (orderOf_dvd_of_pow_eq_one hu) (orderOf_dvd_natCard _)
    have := congrArg Units.val (orderOf_eq_one_iff.mp ho)
    simpa using this
  rw [mem_unitaryOf, hc, hc1, one_smul]

theorem mul_comm_of_mem_suPairs [Finite K] (h : UnitaryFieldData 2 f K) (hn : 3 ≤ n)
    (hnq : (n, 2 ^ f) ≠ (3, 2)) (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 f K n)) {p : ℕ}
    (hp : p.Prime) (hpK : ¬ p ∣ Nat.card K - 1) {x y : G} (hxy : x * y = y * x)
    {A B : GL (Fin n) K} (hA : (x, A) ∈ SUTorus.suPairs ψ) (hB : (y, B) ∈ SUTorus.suPairs ψ)
    (hAp : A ^ p = 1) : A * B = B * A := by
  obtain ⟨q, hq, hqd⟩ := exists_prime_dvd_two_pow_add_one f
  have h1 := (SUTorus.suPairs ψ).mul_mem ((SUTorus.suPairs ψ).mul_mem hA hB)
    ((SUTorus.suPairs ψ).inv_mem ((SUTorus.suPairs ψ).mul_mem hB hA))
  rw [Prod.mk_mul_mk, Prod.mk_mul_mk, Prod.inv_mk, Prod.mk_mul_mk, hxy, mul_inv_cancel] at h1
  obtain ⟨c, hc⟩ := SUTorus.exists_scalar_of_mem_suPairs_one h hn hnq hq hqd hker h1
  set s := GeneralLinearGroup.scalar (Fin n) c with hs
  have hconj : A * B * A⁻¹ = s * B := by
    calc A * B * A⁻¹ = A * B * (B * A)⁻¹ * B := by group
      _ = s * B := by rw [hc]
  have hiter : ∀ k : ℕ, A ^ k * B * (A ^ k)⁻¹ = s ^ k * B := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc A ^ (k + 1) * B * (A ^ (k + 1))⁻¹ = A * (A ^ k * B * (A ^ k)⁻¹) * A⁻¹ := by group
        _ = A * (s ^ k * B) * A⁻¹ := by rw [ih]
        _ = s ^ k * (A * B * A⁻¹) := by
          rw [hs, ← map_pow, ← mul_assoc A, ← TypeA.PGLTor.scalar_mul_comm]
          group
        _ = s ^ (k + 1) * B := by rw [hconj, pow_succ, mul_assoc]
  have hsp : s ^ p = 1 := by
    have h2 := hiter p
    rw [hAp, one_mul, inv_one, mul_one] at h2
    exact (mul_eq_right.mp h2.symm)
  have hn0 : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hcp : c ^ p = 1 := by
    apply TypeA.PGLTor.scalar_injective (ι := Fin n)
    rw [map_pow, ← hs, hsp, map_one]
  have hc1 : c = 1 := by
    rw [← orderOf_eq_one_iff]
    exact Nat.eq_one_of_dvd_coprimes (LinNonsplit.coprime_card_units hp hpK).symm
      (orderOf_dvd_of_pow_eq_one hcp) (orderOf_dvd_natCard c)
  have hs1 : s = 1 := by rw [hs, hc1, map_one]
  calc A * B = A * B * (B * A)⁻¹ * (B * A) := by group
    _ = B * A := by rw [hc, hs1, one_mul]

theorem centralizer_inducedMatrices_zpowers [Finite K] (h : UnitaryFieldData 2 f K)
    (hn : 3 ≤ n) (hnq : (n, 2 ^ f) ≠ (3, 2))
    (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 f K n)) {x : G} {A : GL (Fin n) K}
    (hA : (x, A) ∈ SUTorus.suPairs ψ) :
    Subgroup.centralizer (SUTorus.inducedMatrices ψ (Subgroup.zpowers x) : Set (GL (Fin n) K)) =
      Subgroup.centralizer (Subgroup.zpowers A : Set (GL (Fin n) K)) := by
  obtain ⟨q, hq, hqd⟩ := exists_prime_dvd_two_pow_add_one f
  apply le_antisymm
  · apply Subgroup.centralizer_le
    intro g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact SUTorus.mem_inducedMatrices.mpr ⟨x ^ k, Subgroup.zpow_mem_zpowers x k,
      (SUTorus.suPairs ψ).zpow_mem hA k⟩
  · intro g hg
    rw [Subgroup.mem_centralizer_iff] at hg ⊢
    intro M hM
    obtain ⟨e, he, heM⟩ := SUTorus.mem_inducedMatrices.mp hM
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    have hk : (x ^ k, A ^ k) ∈ SUTorus.suPairs ψ := (SUTorus.suPairs ψ).zpow_mem hA k
    obtain ⟨c, rfl⟩ := SUTorus.exists_scalar_mul_of_mem_suPairs h hn hnq hq hqd hker hk heM
    have h1 := hg (A ^ k) (Subgroup.zpow_mem_zpowers A k)
    rw [mul_assoc, h1, ← mul_assoc, TypeA.PGLTor.scalar_mul_comm, mul_assoc]

theorem isCoreFamily_su (h : UnitaryFieldData 2 f K) {A : GL (Fin n) K} {β : Type}
    {S : β → Subgroup (GL (Fin n) K)}
    (hS : IsCoreFamily (adjCent (Subgroup.zpowers A) (isInvol_suAdj (n := n) h)) S) :
    IsCoreFamily ((Subgroup.centralizer (Subgroup.zpowers A : Set (GL (Fin n) K))).comap
        (unitarySU 2 f K n).subtype) (fun c => (S c).comap (unitarySU 2 f K n).subtype) ∧
      ∀ c, Nat.card ((S c).comap (unitarySU 2 f K n).subtype) = Nat.card (S c) := by
  classical
  set H₀ : Subgroup (GL (Fin n) K) :=
    adjCent (Subgroup.zpowers A) (isInvol_suAdj (n := n) h) ⊓
      (Matrix.GeneralLinearGroup.det).ker with hH₀
  have hSdet : ∀ c, S c ≤ H₀ := by
    intro c
    refine le_inf (hS.1 c) ?_
    rw [← LayerFacts.ggCommutator_eq_of_isQuasisimple (hS.2.2.1 c)]
    exact (Subgroup.commutator_mono le_top le_top).trans (Abelianization.commutator_subset_ker _)
  have hS0 := hS.mono inf_le_left hSdet
  have hdet : ∀ g : GL (Fin n) K, g ∈ (Matrix.GeneralLinearGroup.det).ker ↔
      (g : Matrix (Fin n) (Fin n) K).det = 1 := fun g => by
    rw [MonoidHom.mem_ker, Units.ext_iff, Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  have hle : H₀ ≤ (unitarySU 2 f K n).subtype.range := by
    intro g hg
    obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.mp hg
    exact ⟨⟨g, (mem_unitarySU_iff_suAdj h).mpr ⟨(Subgroup.mem_inf.mp hg1).2, (hdet g).mp hg2⟩⟩,
      rfl⟩
  have hC : H₀.comap (unitarySU 2 f K n).subtype =
      (Subgroup.centralizer (Subgroup.zpowers A : Set (GL (Fin n) K))).comap
        (unitarySU 2 f K n).subtype := by
    ext x
    rw [Subgroup.mem_comap, Subgroup.mem_comap, hH₀, adjCent, Subgroup.mem_inf, Subgroup.mem_inf]
    have hx := (mem_unitarySU_iff_suAdj h).mp x.2
    exact ⟨fun hx' => hx'.1.1, fun hx' => ⟨⟨hx', hx.1⟩, (hdet _).mpr hx.2⟩⟩
  have h2 := hS0.comap (unitarySU 2 f K n).subtype (Subgroup.subtype_injective _) hle
  rw [hC] at h2
  refine ⟨h2, fun c => ?_⟩
  rw [← Subgroup.card_map_of_injective (Subgroup.subtype_injective (unitarySU 2 f K n)),
    Subgroup.map_comap_eq_self ((hSdet c).trans hle)]

theorem exists_isComponentOf_le_su [Finite G] (h : UnitaryFieldData 2 f K) (hn : 3 ≤ n)
    (hnq : (n, 2 ^ f) ≠ (3, 2)) (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 f K n)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K - 1) {x y : G} (hx : x ^ p = 1)
    (hy : y ^ p = 1) (hxy : x * y = y * x) {A₀ B₀ : GL (Fin n) K}
    (hA₀ : (x, A₀) ∈ SUTorus.suPairs ψ) (hB₀ : (y, B₀) ∈ SUTorus.suPairs ψ) {X : Subgroup G}
    (hX : IsComponentOf X (ψ.range ⊓ Subgroup.centralizer {x})) (hpX : ¬ p ∣ Nat.card X) :
    ∃ X' : Subgroup G, IsComponentOf X' (ψ.range ⊓ Subgroup.centralizer {y}) ∧ X ≤ X' := by
  classical
  have := h.finite
  have : CharP K 2 := h.charP
  obtain ⟨A, hA, hAp⟩ := exists_mem_suPairs_pow_eq_one h hn hnq hker hp hpK hx hA₀
  obtain ⟨B, hB, hBp⟩ := exists_mem_suPairs_pow_eq_one h hn hnq hker hp hpK hy hB₀
  have hAB := mul_comm_of_mem_suPairs h hn hnq hker hp hpK hxy hA hB hAp
  have hAu := mem_unitaryOf_of_pow_eq_one h (by omega) hp hpK hA.1 hAp
  have hBu := mem_unitaryOf_of_pow_eq_one h (by omega) hp hpK hB.1 hBp
  obtain ⟨c, hc⟩ := exists_add_bar_eq_one h
  have hsymd : ∀ C : GL (Fin n) K, ∃ Y : Matrix (Fin n) (Fin n) K,
      Y * (C : Matrix (Fin n) (Fin n) K) = (C : Matrix (Fin n) (Fin n) K) * Y ∧
        Y + suAdj h Y = 1 := fun C =>
    ⟨c • 1, by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one],
      by rw [suAdj_smul_one, ← add_smul, hc, one_smul]⟩
  obtain ⟨β, Sx, hFx, β', Sy, hFy, hlift⟩ := exists_coreFamilies_lift (isInvol_suAdj (n := n) h)
    hAu hBu hp hp2 hAp hBp hAB (hsymd A) (hsymd B)
  obtain ⟨hFx', hcardx⟩ := isCoreFamily_su h hFx
  obtain ⟨hFy', -⟩ := isCoreFamily_su h hFy
  rw [← centralizer_inducedMatrices_zpowers h hn hnq hker hA] at hFx'
  rw [← centralizer_inducedMatrices_zpowers h hn hnq hker hB] at hFy'
  have hEA : ∀ (z : G) (C : GL (Fin n) K), (z, C) ∈ SUTorus.suPairs ψ →
      ∀ e ∈ Subgroup.zpowers z, ∃ B', (e, B') ∈ SUTorus.suPairs ψ := by
    intro z C hzC e he
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    exact ⟨C ^ k, (SUTorus.suPairs ψ).zpow_mem hzC k⟩
  have hcz : ∀ z : G, Subgroup.centralizer (Subgroup.zpowers z : Set G) =
      Subgroup.centralizer {z} := fun z => by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [← hcz] at hX ⊢
  obtain ⟨c₀, rfl⟩ := LayerPDiv.exists_eq_map_of_isComponentOf ψ hker
    (map_ggSUCent_le (hEA x A hA)) (normal_map_ggSUCent hker) (commutator_le_map_ggSUCent hker)
    _ hFx'.1 hFx'.2.1 hFx'.2.2.1 hFx'.2.2.2.1 hX
  have hpc : ¬ p ∣ Nat.card (Sx c₀) := by
    intro hdvd
    apply hpX
    refine LayerPDiv.dvd_card_map_of_perfect ψ hker
      (LayerFacts.ggCommutator_eq_of_isQuasisimple (hFx'.2.2.1 c₀)) hp ?_
    rw [hcardx c₀]
    exact hdvd
  obtain ⟨c', hc'⟩ := hlift c₀ hpc
  exact ⟨((Sy c').comap (unitarySU 2 f K n).subtype).map ψ,
    LinNonsplit.isComponentOf_map_of_le ψ hker (map_ggSUCent_le (hEA y B hB))
      (normal_map_ggSUCent hker) (hFy'.1 c') (hFy'.2.1 c') (hFy'.2.2.1 c'),
    Subgroup.map_mono (Subgroup.comap_mono hc')⟩

end ClNonsplit

section Tag

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.SectionRank.OddCover CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits InnerDiagSU CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel

theorem ClNonsplit.exists_isComponentOf_le_su_antidiag {G : Type} [Group G] [Finite G] {f m : ℕ}
    (hf : 1 ≤ f) (hn : 4 ≤ m + 1)
    {ψ : SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (m + 1) →* G}
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (m + 1)))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq1 : ¬ p ∣ 2 ^ f - 1) (hq2 : ¬ p ∣ 2 ^ f + 1)
    {x y : G} (hx : x ^ p = 1) (hy : y ^ p = 1) (hxy : x * y = y * x)
    (hxD : GGPsiInnerDiag (Unitary.rootDatum (card_galoisField_two_mul 2 f hf) (m + 1)) ψ x)
    (hyD : GGPsiInnerDiag (Unitary.rootDatum (card_galoisField_two_mul 2 f hf) (m + 1)) ψ y)
    {X : Subgroup G} (hX : IsComponentOf X (ψ.range ⊓ Subgroup.centralizer {x}))
    (hpX : ¬ p ∣ Nat.card X) :
    ∃ X' : Subgroup G, IsComponentOf X' (ψ.range ⊓ Subgroup.centralizer {y}) ∧ X ≤ X' := by
  classical
  have hF : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := card_galoisField_two_mul 2 f hf
  have h : UnitaryFieldData 2 f (GaloisField 2 (2 * f)) :=
    ⟨Nat.prime_two, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  have : Finite (GaloisField 2 (2 * f)) := h.finite
  have : CharP (GaloisField 2 (2 * f)) 2 := h.charP
  obtain ⟨P, hP⟩ := exists_wittMatrix hF (m + 1)
  have hSU : SUid (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (m + 1) =
      unitarySU 2 f (GaloisField 2 (2 * f)) (m + 1) := SUid_eq_statedSU hF (m + 1)
  set Φ := (conjEquiv P hP).trans (MulEquiv.subgroupCongr hSU) with hΦ
  set ψ₁ := ψ.comp Φ.symm.toMonoidHom with hψ₁
  have hr₁ : ψ₁.range = ψ.range := SUTorus.range_comp_symm ψ Φ
  have hker₁ : ψ₁.ker ≤ Subgroup.center ↥(unitarySU 2 f (GaloisField 2 (2 * f)) (m + 1)) :=
    SUTorus.ker_comp_symm_le hker Φ
  have hpair : ∀ z : G, GGPsiInnerDiag (Unitary.rootDatum (card_galoisField_two_mul 2 f hf)
      (m + 1)) ψ z → ∃ C, (z, C) ∈ SUTorus.suPairs ψ₁ := by
    intro z hz
    obtain ⟨A, hA, hAc⟩ := suInnerDiagConj hF hn G ψ hker z hz
    have h1 : (z⁻¹, P * A * P⁻¹) ∈ SUTorus.suPairs ψ₁ :=
      SUTorus.mem_suPairs_transfer P hP hSU hA fun u => by
        rw [inv_inv]
        exact hAc u
    refine ⟨(P * A * P⁻¹)⁻¹, ?_⟩
    have h2 := (SUTorus.suPairs ψ₁).inv_mem h1
    rwa [Prod.inv_mk, inv_inv] at h2
  obtain ⟨A₀, hA₀⟩ := hpair x hxD
  obtain ⟨B₀, hB₀⟩ := hpair y hyD
  have hpK : ¬ p ∣ Nat.card (GaloisField 2 (2 * f)) - 1 := by
    rw [hF, show (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) by
      simpa using Nat.sq_sub_sq (2 ^ f) 1]
    intro hd
    rcases (Nat.Prime.dvd_mul hp).mp hd with h1 | h1
    · exact hq2 h1
    · exact hq1 h1
  have hnq : (m + 1, 2 ^ f) ≠ (3, 2) := fun h' => by
    have := congrArg Prod.fst h'
    simp only at this
    omega
  rw [← hr₁] at hX ⊢
  exact ClNonsplit.exists_isComponentOf_le_su h (by omega) hnq hker₁ hp hp2 hpK hx hy hxy hA₀ hB₀
    hX hpX

theorem ggNonsplitCompLiftTag_PSU : GGNonsplitCompLiftTag .PSU := by
  intro G _ _ n f
  by_cases hf : 1 ≤ f
  · have hU : ggU .PSU n f =
        ⟨Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n,
          Unitary.rootDatum (card_galoisField_two_mul 2 f hf) n⟩ := by
      simp only [ggU, lieUniversal, hf, ↓reduceDIte]
    rw [hU]
    intro ψ G₀ hpres p hp hp2 hq1 hq2 x y hx hy hxy _ _ hxD hyD K hK hpK
    obtain ⟨⟨-, hrk⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
    have hn : 4 ≤ n := by
      have : 2 ≤ n / 2 := hrk
      omega
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [← hrange] at hK ⊢
    exact ClNonsplit.exists_isComponentOf_le_su_antidiag hf hn hker hp hp2 hq1 hq2 hx hy hxy hxD
      hyD hK hpK
  · intro ψ G₀ hpres
    exact absurd hpres.1.1.2.1 hf

end Tag

end CFSG.StandardType

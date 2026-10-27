module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Glue4TorusReduction
import CFSG.LocalAnalysis.UniquenessCase.Lie.SU3Cover

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
open scoped Pointwise

private theorem g4u3_pow_mul_mem {Y : Type} [Group Y] {U : Subgroup Y} {y u : Y}
    (hy : y ∈ normalizer (U : Set Y)) (hu : u ∈ U) (m : ℕ) : (y * u) ^ m * (y ^ m)⁻¹ ∈ U := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : y * u * y⁻¹ ∈ U := (mem_normalizer_iff.1 hy u).1 hu
    have h2 : y ^ m * (y * u * y⁻¹) * (y ^ m)⁻¹ ∈ U :=
      (mem_normalizer_iff.1 (pow_mem hy m) _).1 h1
    have e : (y * u) ^ (m + 1) * (y ^ (m + 1))⁻¹ =
        ((y * u) ^ m * (y ^ m)⁻¹) * (y ^ m * (y * u * y⁻¹) * (y ^ m)⁻¹) := by
      rw [pow_succ, pow_succ]
      group
    rw [e]
    exact U.mul_mem ih h2

private theorem g4u3_pow_mul_mem_iff {Y : Type} [Group Y] {U : Subgroup Y} {y u : Y}
    (hy : y ∈ normalizer (U : Set Y)) (hu : u ∈ U) (m : ℕ) : (y * u) ^ m ∈ U ↔ y ^ m ∈ U := by
  have e : (y * u) ^ m = ((y * u) ^ m * (y ^ m)⁻¹) * y ^ m := by group
  rw [e, Subgroup.mul_mem_cancel_left _ (g4u3_pow_mul_mem hy hu m)]

private theorem g4u3_mem_zpowers_pow {Y : Type} [Group Y] {a y : Y} {N M : ℕ}
    (hNM : Nat.Coprime N M) (hy : y ∈ zpowers a) (hyN : y ^ N = 1) : y ∈ zpowers (a ^ M) := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
  obtain ⟨e, he1, he2⟩ := Nat.chineseRemainder hNM 1 0
  obtain ⟨c, hc⟩ := Nat.modEq_zero_iff_dvd.1 he2
  have h1 : (a ^ k) ^ e = a ^ k := by
    have h2 : e ≡ 1 [MOD orderOf (a ^ k)] := he1.of_dvd (orderOf_dvd_of_pow_eq_one hyN)
    exact (pow_eq_pow_iff_modEq.2 h2).trans (pow_one _)
  refine mem_zpowers_iff.2 ⟨k * c, ?_⟩
  rw [← h1, hc, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul]
  congr 1
  push_cast
  ring

private theorem g4u3_mem_normalizer_of_map {S Y : Type} [Group S] [Group Y] [Finite S]
    {α : S →* Y} {M : ℕ} (hM : Odd M) (hker : ∀ x ∈ α.ker, x ^ M = 1)
    (hcent : α.ker ≤ center S) {X : Subgroup S} (hX : IsPGroup 2 X) {s : S}
    (hs : α s ∈ normalizer ((X.map α : Subgroup Y) : Set Y)) : s ∈ normalizer (X : Set S) := by
  have h := uc22pwsu3_lift_preserves hM hker hcent hX (ψ := MulAut.conj (α s))
    (ψ' := MulAut.conj s) (fun x => by simp [MulAut.conj_apply])
    (fun x => mem_normalizer_iff.1 hs x)
  exact mem_normalizer_iff.2 fun x => by simpa [MulAut.conj_apply] using h x

private theorem g4u3_orderOf_map_pow {S Y : Type} [Group S] [Group Y] {α : S →* Y} {N M : ℕ}
    (hNM : Nat.Coprime N M) (hM : 0 < M) (hker : ∀ x ∈ α.ker, x ^ M = 1) {g : S}
    (hg : orderOf g = N * M) : orderOf (α (g ^ M)) = N := by
  apply Nat.dvd_antisymm
  · apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, ← pow_mul, mul_comm, ← hg, pow_orderOf_eq_one, map_one]
  · have h2 : g ^ (M * orderOf (α (g ^ M))) ∈ α.ker := by
      rw [MonoidHom.mem_ker, pow_mul, map_pow]
      exact pow_orderOf_eq_one _
    have h3 : g ^ (M * orderOf (α (g ^ M)) * M) = 1 := by
      rw [pow_mul]
      exact hker _ h2
    have h4 : N * M ∣ M * orderOf (α (g ^ M)) * M := hg ▸ orderOf_dvd_of_pow_eq_one h3
    exact hNM.dvd_of_dvd_mul_left (Nat.dvd_of_mul_dvd_mul_right hM h4)

private theorem g4u3_iff {S Y : Type} [Group S] [Group Y] [Finite S] [Finite Y] {N M : ℕ}
    (hNM : Nat.Coprime N M) (hM : Odd M) {α : S →* Y} (hα : Function.Surjective α)
    (hker : ∀ x ∈ α.ker, x ^ M = 1) (hcent : α.ker ≤ center S) {X : Subgroup S}
    (hX : IsPGroup 2 X) {g : S} (hgN : g ∈ normalizer (X : Set S))
    (hdec : ∀ s ∈ normalizer (X : Set S), ∃ k : ℤ, ∃ u ∈ X, s = g ^ k * u)
    (hodd : Odd (orderOf g)) (hdo : orderOf (α (g ^ M)) = N) :
    ∀ x ∈ normalizer ((X.map α : Subgroup Y) : Set Y),
      x ^ N ∈ X.map α ↔ x ∈ zpowers (α (g ^ M)) ⊔ X.map α := by
  intro x hx
  have hgN' : α g ∈ normalizer ((X.map α : Subgroup Y) : Set Y) :=
    uc22pwsu3_map_normalizer_le α X (mem_map_of_mem α hgN)
  have hDN : zpowers (α (g ^ M)) ≤ normalizer ((X.map α : Subgroup Y) : Set Y) := by
    rw [zpowers_le, map_pow]
    exact pow_mem hgN' M
  constructor
  · intro hxN
    obtain ⟨s, rfl⟩ := hα x
    obtain ⟨k, u, hu, rfl⟩ := hdec s (g4u3_mem_normalizer_of_map hM hker hcent hX hx)
    rw [map_mul, map_zpow] at hxN ⊢
    have h1 : (α g ^ k) ^ N ∈ X.map α :=
      (g4u3_pow_mul_mem_iff (zpow_mem hgN' k) (mem_map_of_mem α hu) N).1 hxN
    have hT : Odd (Nat.card (zpowers (α g))) := by
      rw [Nat.card_zpowers]
      exact hodd.of_dvd_nat (orderOf_map_dvd α g)
    have h2 : (α g ^ k) ^ N = 1 :=
      uc22pwr1_eq_one_of_mem_inf (hX.map α) hT h1 (pow_mem (zpow_mem_zpowers _ _) _)
    have h3 : α g ^ k ∈ zpowers (α (g ^ M)) := by
      rw [map_pow]
      exact g4u3_mem_zpowers_pow hNM (zpow_mem_zpowers _ _) h2
    exact mul_mem_sup h3 (mem_map_of_mem α hu)
  · intro hxD
    have hx' : x ∈ ((zpowers (α (g ^ M)) : Set Y) * ((X.map α : Subgroup Y) : Set Y)) := by
      rw [← coe_mul_of_left_le_normalizer_right _ _ hDN]
      exact hxD
    obtain ⟨y, hy, u, hu, rfl⟩ := hx'
    rw [g4u3_pow_mul_mem_iff (hDN hy) hu N]
    have hyN : y ^ N = 1 := by
      have h := uc22pwr1_pow_card hy
      rwa [Nat.card_zpowers, hdo] at h
    rw [hyN]
    exact one_mem _

private theorem g4u3_cartanAt {S Y : Type} [Group S] [Group Y] [Finite S] [Finite Y] {n : ℕ}
    (hn : 1 ≤ n) {α : S →* Y} (hα : Function.Surjective α)
    (hker : ∀ x ∈ α.ker, x ^ (2 ^ n + 1) = 1) (hcent : α.ker ≤ center S) {X : Subgroup S}
    (hX : IsPGroup 2 X) {g w : S} (hgN : g ∈ normalizer (X : Set S))
    (hdec : ∀ s ∈ normalizer (X : Set S), ∃ k : ℤ, ∃ u ∈ X, s = g ^ k * u)
    (hg : orderOf g = (2 ^ n - 1) * (2 ^ n + 1)) (hw2 : w ^ 2 = 1)
    (hwinv : w * g ^ (2 ^ n + 1) * w⁻¹ = (g ^ (2 ^ n + 1))⁻¹) :
    CartanAt (X.map α) n (Multiplicative (ZMod (2 ^ n - 1))) := by
  have hNM := uc22pwsu3_coprime_two_pow hn
  have hM := uc22pwsu3_odd_two_pow_add_one hn
  have hdo := g4u3_orderOf_map_pow hNM hM.pos hker hg
  have hgN' : α g ∈ normalizer ((X.map α : Subgroup Y) : Set Y) :=
    uc22pwsu3_map_normalizer_le α X (mem_map_of_mem α hgN)
  have hodd : Odd (orderOf g) := by
    rw [hg]
    exact (uc22pwsu3_odd_two_pow_sub_one hn).mul hM
  refine ⟨zpowers (α (g ^ (2 ^ n + 1))), α w, ?_, ⟨mulEquivOfCyclicCardEq ?_⟩,
    g4u3_iff hNM hM hα hker hcent hX hgN hdec hodd hdo, ?_, ?_⟩
  · rw [zpowers_le, map_pow]
    exact pow_mem hgN' _
  · rw [Nat.card_zpowers, hdo]
    exact (Nat.card_zmod _).symm
  · have h1 : orderOf (α w) ∣ 2 ^ 1 :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_one, ← map_pow, hw2, map_one])
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
    exact ⟨k, hk⟩
  · intro a ha
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 ha
    rw [← conj_zpow, ← map_inv, ← map_mul, ← map_mul, hwinv, map_inv, inv_zpow]

section Model

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

private theorem g4u3_exists_cover (hK : Nat.card K = (2 ^ n) ^ 2) {Y : Type} [Group Y]
    (e : Y ≃* StatedProj (StatedSU 3 (2 ^ n) K)) :
    ∃ α : SU (unitaryInvolution K 2 n) 3 →* Y, Function.Surjective α ∧
      α.ker ≤ center (SU (unitaryInvolution K 2 n) 3) ∧ ∀ x ∈ α.ker, x ^ (2 ^ n + 1) = 1 := by
  let α : SU (unitaryInvolution K 2 n) 3 →* Y :=
    e.symm.toMonoidHom.comp ((QuotientGroup.mk' _).comp (equivStatedSU hK 3).toMonoidHom)
  have hZ : ∀ s, α s = 1 → equivStatedSU hK 3 s ∈
      (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (2 ^ n) K) := fun s hs =>
    (QuotientGroup.eq_one_iff _).1 ((map_eq_one_iff _ e.symm.injective).1 hs)
  refine ⟨α, e.symm.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (equivStatedSU hK 3).surjective), ?_, ?_⟩
  · intro s hs
    have hc := uc22pwsu3_scalar_mem_center _ (hZ s hs)
    rw [Subgroup.mem_center_iff]
    intro g
    apply (equivStatedSU hK 3).injective
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.1 hc _
  · intro x hx
    have hcard :=
      (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK (n := 3) (by norm_num)).2.2
    have h3 := uc22pwr1_pow_card (hZ x hx)
    rw [hcard] at h3
    have h4 : (equivStatedSU hK 3 x) ^ (2 ^ n + 1) = 1 := by
      obtain ⟨c, hc⟩ := Nat.gcd_dvd_right 3 (2 ^ n + 1)
      rw [hc, pow_mul, h3, one_pow]
    apply (equivStatedSU hK 3).injective
    rw [map_pow, h4, map_one]

private theorem g4u3_su3_borel (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    ∃ g w : SU (unitaryInvolution K 2 n) 3,
      g ∈ normalizer ((uc22pwsu3X (unitaryInvolution_involutive hK) :
        Subgroup (SU (unitaryInvolution K 2 n) 3)) : Set (SU (unitaryInvolution K 2 n) 3)) ∧
      (∀ s ∈ normalizer ((uc22pwsu3X (unitaryInvolution_involutive hK) :
        Subgroup (SU (unitaryInvolution K 2 n) 3)) : Set (SU (unitaryInvolution K 2 n) 3)),
        ∃ k : ℤ, ∃ u ∈ uc22pwsu3X (unitaryInvolution_involutive hK), s = g ^ k * u) ∧
      orderOf g = (2 ^ n - 1) * (2 ^ n + 1) ∧ w ^ 2 = 1 ∧
      w * g ^ (2 ^ n + 1) * w⁻¹ = (g ^ (2 ^ n + 1))⁻¹ := by
  have hσ := unitaryInvolution_involutive hK
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hK
  have hσn : ∀ c : K, unitaryInvolution K 2 n c = c ^ 2 ^ n := unitaryInvolution_apply K 2 n
  haveI := uc22pwsu3H_cyclic (σ := unitaryInvolution K 2 n)
  obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_generator (α := uc22pwsu3H (unitaryInvolution K 2 n))
  have hg : orderOf (g₀ : SU (unitaryInvolution K 2 n) 3) = (2 ^ n - 1) * (2 ^ n + 1) := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg₀,
      card_levelTorus_three hK, uc22pwsu3_sq_sub_one hn]
  refine ⟨g₀, uc22pwsu3W hσ ζ, uc22pwsu3_levelTorus_le_normalizer hσ g₀.2, ?_, hg,
    uc22pwsu3_levelWeyl_sq hσ hζ, ?_⟩
  · intro s hs
    obtain ⟨h, hh, u, hu, rfl⟩ :=
      uc22pwsu3_normalizer_decomp hσ (uc22pwsu3_hnorm hK) (rankOne_three_eq_top hK) hζ hs
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (hg₀ ⟨h, hh⟩)
    exact ⟨k, u, hu, by rw [← Subgroup.coe_zpow, hk]⟩
  · have ht : (g₀ : SU (unitaryInvolution K 2 n) 3) ^ (2 ^ n + 1) ∈
        uc22pwsu3H (unitaryInvolution K 2 n) := pow_mem g₀.2 _
    have htpow : ((g₀ : SU (unitaryInvolution K 2 n) 3) ^ (2 ^ n + 1)) ^ (2 ^ n - 1) = 1 := by
      rw [← pow_mul, mul_comm, ← hg, pow_orderOf_eq_one]
    obtain ⟨τ, hτ⟩ := exists_mat_eq_diagonal_of_mem_levelTorus_three ht
    have h1 : (τ : K) ^ (2 ^ n - 1) = 1 := uc22pwsu3_entry_pow_eq_one ht (by simp [hτ]) htpow
    exact uc22pwsu3_levelWeyl_conj hσ hζ τ.ne_zero hτ (uc22pwsu3_sigma_eq_of_pow hσ hσn h1)

end Model

theorem cartanAt_of_isU3 {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hn : 2 ≤ n) (h : IsU3 Y n) :
    ∃ U : Subgroup Y, CFSG.ABGLocalTools.IsSylowOf 2 U ⊤ ∧
      CartanAt U n (Multiplicative (ZMod (2 ^ n - 1))) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)
  haveI : CharP K 2 := uc22pwlie_charP_two (n := 2 * n) (by rw [hK, ← pow_mul, mul_comm])
  have hn1 : 1 ≤ n := by omega
  obtain ⟨α, hα, hαc, hαk⟩ := g4u3_exists_cover hK e
  obtain ⟨g, w, hgN, hdec, hg, hw2, hwinv⟩ := g4u3_su3_borel hn1 hK
  have hX := uc22pwsu3X_isPGroup hK
  refine ⟨_, CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨le_top, hX.map α, ?_⟩,
    g4u3_cartanAt hn1 hα hαk hαc hX hgN hdec hg hw2 hwinv⟩
  rw [relIndex_top_right]
  exact fun hd => uc22pwsu3X_index hn1 hK (hd.trans (index_map_dvd _ hα))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

module

public import CFSG.RankThree.PartTwo.Sec4.Statements
public import CFSG.RankThree.PartTwo.Sec4.LThreePiDefs
import CFSG.RankThree.PartTwo.Sec16.Item169StepsProofHess
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.KFacts.KSL3PiOrder3TypeC

public section

namespace CFSG.RankThree.PartTwo.Sec15

namespace Proof15Res9Torus

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 Matrix
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.RankThree.PartTwo.Sec16.ProofHess

variable {K : Type} [Field K]

theorem commute_of_commute_eigen {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {P Q Y : Matrix (Fin 3) (Fin 3) K} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hY : Y * P = P * diagonal ![τ, τ ^ 2, 1]) {M N : Matrix (Fin 3) (Fin 3) K}
    (hM : M * Y = Y * M) (hN : N * Y = Y * N) : M * N = N * M := by
  have hMd := eq_diagonal_of_commute hτ hτ1 (conj_commute hPQ hQP hY hM)
  have hNd := eq_diagonal_of_commute hτ hτ1 (conj_commute hPQ hQP hY hN)
  have hc : (Q * M * P) * (Q * N * P) = (Q * N * P) * (Q * M * P) := by
    rw [hMd, hNd, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    ring
  rw [conj_mul hPQ, conj_mul hPQ] at hc
  calc M * N = P * (Q * (M * N) * P) * Q := (unconj hPQ _).symm
    _ = P * (Q * (N * M) * P) * Q := by rw [hc]
    _ = N * M := unconj hPQ _

theorem conj_diagonal_commute {τ : K} {P Q Y : Matrix (Fin 3) (Fin 3) K} (hPQ : P * Q = 1)
    (hQP : Q * P = 1) (hY : Y * P = P * diagonal ![τ, τ ^ 2, 1]) (d : Fin 3 → K) :
    (P * diagonal d * Q) * Y = Y * (P * diagonal d * Q) := by
  have hQY : Q * Y = diagonal ![τ, τ ^ 2, 1] * Q := inv_mul_eq hPQ hQP hY
  have hdd : diagonal d * diagonal ![τ, τ ^ 2, 1] = diagonal ![τ, τ ^ 2, 1] * diagonal d := by
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    ring
  calc P * diagonal d * Q * Y = P * diagonal d * (Q * Y) := by rw [Matrix.mul_assoc]
    _ = P * (diagonal d * diagonal ![τ, τ ^ 2, 1]) * Q := by
        rw [hQY]
        simp only [Matrix.mul_assoc]
    _ = P * diagonal ![τ, τ ^ 2, 1] * diagonal d * Q := by
        rw [hdd]
        simp only [Matrix.mul_assoc]
    _ = Y * (P * diagonal d * Q) := by
        rw [← hY]
        simp only [Matrix.mul_assoc]

theorem exists_torus_model {r : ℕ} (hK : PiField true r 2 K) (hq : ModThree true (r ^ 2))
    (h9 : ¬ 9 ∣ Nat.card K - 1) {y : ProjGenLinGroup (Fin 3) K}
    (hy : y ∈ projImage (slPi true 3 (r ^ 2) K)) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    ∃ V : Subgroup (ProjGenLinGroup (Fin 3) K), V ≤ projImage (slPi true 3 (r ^ 2) K) ∧
      (∀ v ∈ V, v ^ 2 ^ padicValNat 2 (r ^ 2 - 1) = 1) ∧
      4 ^ padicValNat 2 (r ^ 2 - 1) ≤ Nat.card V ∧
      (∀ v ∈ V, v * y = y * v) ∧
      ∀ z ∈ projImage (slPi true 3 (r ^ 2) K), z * y = y * z → ∀ v ∈ V, z * v * z⁻¹ ∈ V := by
  classical
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) :=
    inferInstanceAs (Finite (GL (Fin 3) K ⧸ Subgroup.center (GL (Fin 3) K)))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨yh, hyhS, rfl⟩ := hy
  have hyh3 : yh ^ 3 = 1 := pow_three_eq_one_of_lift hK h9 hyhS hy3
  have hdet : (yh : Matrix (Fin 3) (Fin 3) K).det = 1 := (mem_slPi_true _).mp hyhS
  have hyhs : ∀ c : K, (yh : Matrix (Fin 3) (Fin 3) K) ≠ c • 1 := by
    intro c hc
    apply hy1
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      rw [hc, det_zero] at hdet
      exact zero_ne_one hdet
    exact KFacts.mk_eq_one_iff_mem_statedScalars'.mpr (mem_statedScalars_of_eq_smul hc hc0)
  have hyh3m : (yh : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hyh3, Units.val_one]
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have h3 : (3 : K) ≠ 0 := hK.three_ne_zero hq
  obtain ⟨hτ0, -, -⟩ := tau_facts hτ hτ1
  obtain ⟨P, j, hP, hPD⟩ := exists_normal_form_det_one hτ hτ1 h3 hyh3m hdet hyhs
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hPQ : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPdet
  have hQP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPdet
  have hτj : τ ^ (j : ℕ) ≠ 0 := pow_ne_zero _ hτ0
  have hcY : ∀ M : Matrix (Fin 3) (Fin 3) K, M * (yh : Matrix (Fin 3) (Fin 3) K) =
      (yh : Matrix (Fin 3) (Fin 3) K) * M →
      M * (τ ^ (j : ℕ) • (yh : Matrix (Fin 3) (Fin 3) K)) =
        (τ ^ (j : ℕ) • (yh : Matrix (Fin 3) (Fin 3) K)) * M := fun M hM => by
    rw [Matrix.mul_smul, Matrix.smul_mul, hM]
  have hcY' : ∀ M : Matrix (Fin 3) (Fin 3) K,
      M * (τ ^ (j : ℕ) • (yh : Matrix (Fin 3) (Fin 3) K)) =
        (τ ^ (j : ℕ) • (yh : Matrix (Fin 3) (Fin 3) K)) * M →
      M * (yh : Matrix (Fin 3) (Fin 3) K) = (yh : Matrix (Fin 3) (Fin 3) K) * M := fun M hM => by
    rw [Matrix.mul_smul, Matrix.smul_mul] at hM
    exact smul_right_injective _ hτj hM
  set m := 2 ^ padicValNat 2 (r ^ 2 - 1) with hm
  have hm3 : Nat.Coprime m 3 := Nat.Coprime.pow_left _ (by norm_num)
  have hcardK : Nat.card K = r ^ 2 := by
    rw [hK.card]
    rfl
  have hmK : m ∣ Nat.card K - 1 := by
    rw [hcardK, hm]
    exact pow_padicValNat_dvd
  let Vh : Subgroup (GL (Fin 3) K) :=
    { carrier := {g | g ∈ slPi true 3 (r ^ 2) K ∧ g * yh = yh * g ∧ g ^ m = 1}
      mul_mem' := by
        rintro g₁ g₂ ⟨h₁S, h₁y, h₁m⟩ ⟨h₂S, h₂y, h₂m⟩
        have hcomm : g₁ * g₂ = g₂ * g₁ := by
          apply Units.ext
          simp only [Units.val_mul]
          refine commute_of_commute_eigen hτ hτ1 hPQ hQP hPD (hcY _ ?_) (hcY _ ?_)
          · have := congrArg Units.val h₁y
            simpa only [Units.val_mul] using this
          · have := congrArg Units.val h₂y
            simpa only [Units.val_mul] using this
        refine ⟨mul_mem h₁S h₂S, ?_, ?_⟩
        · calc g₁ * g₂ * yh = g₁ * (g₂ * yh) := by rw [mul_assoc]
            _ = g₁ * (yh * g₂) := by rw [h₂y]
            _ = (g₁ * yh) * g₂ := by rw [mul_assoc]
            _ = yh * (g₁ * g₂) := by rw [h₁y, mul_assoc]
        · rw [(show Commute g₁ g₂ from hcomm).mul_pow, h₁m, h₂m, one_mul]
      one_mem' := ⟨one_mem _, by rw [one_mul, mul_one], one_pow _⟩
      inv_mem' := by
        rintro g ⟨hS, hgy, hgm⟩
        refine ⟨inv_mem hS, ?_, by rw [inv_pow, hgm, inv_one]⟩
        calc g⁻¹ * yh = g⁻¹ * (yh * g) * g⁻¹ := by group
          _ = g⁻¹ * (g * yh) * g⁻¹ := by rw [hgy]
          _ = yh * g⁻¹ := by group }
  have hmemVh : ∀ g, g ∈ Vh ↔ g ∈ slPi true 3 (r ^ 2) K ∧ g * yh = yh * g ∧ g ^ m = 1 :=
    fun g => Iff.rfl
  have hinj : ∀ g ∈ Vh, ProjGenLinGroup.mk g = 1 → g = 1 := by
    intro g hg hg1
    obtain ⟨hgS, -, hgm⟩ := (hmemVh g).mp hg
    obtain ⟨μ, rfl⟩ := KFacts.mk_eq_one_iff_mem_statedScalars'.mp hg1
    have hdetμ : (μ : K) ^ 3 = 1 := by
      have h1 := (mem_slPi_true _).mp hgS
      simpa only [KFacts.det_scalar_eq] using h1
    have hμm : μ ^ m = 1 := by
      have h1 := congrArg (fun z : GL (Fin 3) K => (z : Matrix (Fin 3) (Fin 3) K) 0 0) hgm
      simp only [← map_pow, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Units.val_one, Matrix.one_apply_eq, diagonal_apply_eq] at h1
      exact Units.ext (by simpa using h1)
    have hμ3 : μ ^ 3 = 1 := Units.ext (by simpa using hdetμ)
    have hμ1 : μ = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hm3
      (orderOf_dvd_of_pow_eq_one hμm) (orderOf_dvd_of_pow_eq_one hμ3))
    rw [hμ1, map_one]
  refine ⟨Vh.map ProjGenLinGroup.mk, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩
    exact ⟨g, hg.1, rfl⟩
  · rintro _ ⟨g, hg, rfl⟩
    rw [← map_pow, hg.2.2, map_one]
  ·
    set R := rootsOfUnity m K with hR
    have hRcard : Nat.card R = m := by
      have : NeZero m := ⟨by positivity⟩
      exact CFSG.LinearGroups.card_rootsOfUnity_of_dvd hmK
    have hRm : ∀ a : R, ((a : Kˣ) : K) ^ m = 1 := fun a => by
      have := congrArg Units.val ((mem_rootsOfUnity _ _).mp a.2)
      simpa using this
    let D : R × R → Matrix (Fin 3) (Fin 3) K := fun ab =>
      diagonal ![((ab.1 : Kˣ) : K), ((ab.2 : Kˣ) : K), (((ab.1 : Kˣ) * (ab.2 : Kˣ))⁻¹ : Kˣ)]
    let Dinv : R × R → Matrix (Fin 3) (Fin 3) K := fun ab =>
      diagonal ![(((ab.1 : Kˣ))⁻¹ : Kˣ), (((ab.2 : Kˣ))⁻¹ : Kˣ),
        (((ab.1 : Kˣ) * (ab.2 : Kˣ)) : Kˣ)]
    have hDD : ∀ ab, D ab * Dinv ab = 1 := fun ab => by
      simp only [D, Dinv, diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      fin_cases i
      · exact Units.mul_inv _
      · exact Units.mul_inv _
      · exact Units.inv_mul _
    have hDD' : ∀ ab, Dinv ab * D ab = 1 := fun ab => by
      simp only [D, Dinv, diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      fin_cases i
      · exact Units.inv_mul _
      · exact Units.inv_mul _
      · exact Units.mul_inv _
    let g : R × R → GL (Fin 3) K := fun ab =>
      ⟨P * D ab * P⁻¹, P * Dinv ab * P⁻¹, by
        rw [conj_mul hQP, hDD, Matrix.mul_one, hPQ], by
        rw [conj_mul hQP, hDD', Matrix.mul_one, hPQ]⟩
    have hgval : ∀ ab, ((g ab : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = P * D ab * P⁻¹ :=
      fun ab => rfl
    have hgVh : ∀ ab, g ab ∈ Vh := by
      intro ab
      refine ⟨?_, ?_, ?_⟩
      · rw [mem_slPi_true, hgval, det_conj hPQ, det_diagonal, Fin.prod_univ_three]
        change ((ab.1 : Kˣ) : K) * ((ab.2 : Kˣ) : K) *
          ((((ab.1 : Kˣ) * (ab.2 : Kˣ))⁻¹ : Kˣ) : K) = 1
        rw [← Units.val_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      · apply Units.ext
        simp only [Units.val_mul, hgval]
        exact hcY' _ (conj_diagonal_commute hPQ hQP hPD _)
      · apply Units.ext
        rw [Units.val_pow_eq_pow_val, hgval, Units.val_one, conj_pow hQP hPQ]
        have hDm : D ab ^ m = 1 := by
          have hu : ∀ u : Kˣ, u ^ m = 1 → (u : K) ^ m = 1 := fun u hu => by
            rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
          have h1 : (ab.1 : Kˣ) ^ m = 1 := (mem_rootsOfUnity _ _).mp ab.1.2
          have h2 : (ab.2 : Kˣ) ^ m = 1 := (mem_rootsOfUnity _ _).mp ab.2.2
          have h3 : ((ab.1 : Kˣ) * (ab.2 : Kˣ))⁻¹ ^ m = 1 := by
            rw [inv_pow, mul_pow, h1, h2, mul_one, inv_one]
          simp only [D]
          rw [diagonal_pow, ← diagonal_one]
          congr 1
          funext i
          fin_cases i
          · exact hu _ h1
          · exact hu _ h2
          · exact hu _ h3
        rw [hDm, Matrix.mul_one, hPQ]
    have hginj : Function.Injective fun ab => (⟨ProjGenLinGroup.mk (g ab),
        ⟨g ab, hgVh ab, rfl⟩⟩ : Vh.map ProjGenLinGroup.mk) := by
      intro ab ab' hab
      have h1 : ProjGenLinGroup.mk (g ab * (g ab')⁻¹) = 1 := by
        rw [map_mul, map_inv]
        have := congrArg Subtype.val hab
        simp only at this
        rw [this, mul_inv_cancel]
      have h2 := hinj _ (mul_mem (hgVh ab) (inv_mem (hgVh ab'))) h1
      have h3 : g ab = g ab' := mul_inv_eq_one.mp h2
      have h4 : D ab = D ab' := by
        have h5 := congrArg (fun z : GL (Fin 3) K => P⁻¹ * (z : Matrix (Fin 3) (Fin 3) K) * P) h3
        simp only [hgval] at h5
        rwa [unconj hQP, unconj hQP] at h5
      have e1 : ((ab.1 : Kˣ) : K) = ((ab'.1 : Kˣ) : K) := by
        have := congrFun (congrFun h4 0) 0
        simpa [D] using this
      have e2 : ((ab.2 : Kˣ) : K) = ((ab'.2 : Kˣ) : K) := by
        have := congrFun (congrFun h4 1) 1
        simpa [D] using this
      exact Prod.ext (Subtype.ext (Units.ext e1)) (Subtype.ext (Units.ext e2))
    have hle := Nat.card_le_card_of_injective _ hginj
    rw [Nat.card_prod, hRcard] at hle
    calc 4 ^ padicValNat 2 (r ^ 2 - 1) = m * m := by
          rw [hm, ← mul_pow]
          norm_num
      _ ≤ _ := hle
  · rintro _ ⟨g, hg, rfl⟩
    rw [← map_mul, ← map_mul, hg.2.1]
  · rintro z ⟨zh, hzhS, rfl⟩ hzy _ ⟨g, hg, rfl⟩
    obtain ⟨hgS, hgy, hgm⟩ := (hmemVh g).mp hg
    have hs : zh * yh * zh⁻¹ * yh⁻¹ ∈ StatedScalars (Fin 3) K := by
      rw [← KFacts.mk_eq_one_iff_mem_statedScalars', map_mul, map_mul, map_mul, map_inv,
        map_inv, hzy]
      group
    have hcen := commute_of_mem_statedScalars hs
    set s := zh * yh * zh⁻¹ * yh⁻¹ with hsdef
    have hzy' : zh * yh * zh⁻¹ = s * yh := by rw [hsdef]; group
    refine ⟨zh * g * zh⁻¹, ⟨mul_mem (mul_mem hzhS hgS) (inv_mem hzhS), ?_, ?_⟩, ?_⟩
    · have hyh : yh = s⁻¹ * (zh * yh * zh⁻¹) := by rw [hzy']; group
      calc zh * g * zh⁻¹ * yh = zh * g * zh⁻¹ * (s⁻¹ * (zh * yh * zh⁻¹)) := by
            rw [← hyh]
        _ = s⁻¹ * (zh * (g * yh) * zh⁻¹) := by
            have h1 : ∀ w, w * s⁻¹ = s⁻¹ * w := fun w => by
              have := hcen w
              calc w * s⁻¹ = s⁻¹ * (s * w) * s⁻¹ := by group
                _ = s⁻¹ * (w * s) * s⁻¹ := by rw [this]
                _ = s⁻¹ * w := by group
            calc zh * g * zh⁻¹ * (s⁻¹ * (zh * yh * zh⁻¹)) =
                (zh * g * zh⁻¹ * s⁻¹) * (zh * yh * zh⁻¹) := by group
              _ = (s⁻¹ * (zh * g * zh⁻¹)) * (zh * yh * zh⁻¹) := by rw [h1]
              _ = s⁻¹ * (zh * (g * yh) * zh⁻¹) := by group
        _ = s⁻¹ * (zh * (yh * g) * zh⁻¹) := by rw [hgy]
        _ = s⁻¹ * (zh * yh * zh⁻¹) * (zh * g * zh⁻¹) := by group
        _ = yh * (zh * g * zh⁻¹) := by rw [hzy']; group
    · rw [_root_.conj_pow, hgm, mul_one, mul_inv_cancel]
    · rw [map_mul, map_mul, map_inv]

end Proof15Res9Torus

open Proof15Res9Torus
open CFSG.RankThree.PartTwo.Sec4 Matrix
open CFSG.Assembly.RankThreeEven (projImage)

theorem ks1518HessTorus :
    ∀ (X : Type) [Group X] [Finite X] (r : ℕ) [Fact r.Prime], r ≠ 2 →
      Sec4.IsoLThreePi X r 2 → ¬ (r ^ 2 % 9 = 1 ∨ r ^ 2 % 9 = 8) →
      ∀ x : X, x ^ 3 = 1 → x ≠ 1 →
        ∃ V : Subgroup X, IsPGroup 2 V ∧ 4 ^ padicValNat 2 (r ^ 2 - 1) ≤ Nat.card V ∧
          V ≤ Subgroup.centralizer {x} ∧
          Subgroup.centralizer {x} ≤ Subgroup.normalizer (V : Set X) := by
  classical
  intro X _ _ r _ hr2 hiso h9 x hx3 hx1
  have hr : r.Prime := Fact.out
  obtain ⟨π, K, _, hK, hq, ⟨φ⟩⟩ := Sec13.exists_projImage_model (by norm_num) hiso
  have hπ : π = true := by
    cases π
    · exfalso
      change r ^ 2 % 3 = 2 at hq
      have : r % 3 < 3 := Nat.mod_lt _ (by norm_num)
      rw [Nat.pow_mod] at hq
      interval_cases h : r % 3 <;> simp_all
    · rfl
  subst hπ
  have h9K : ¬ 9 ∣ Nat.card K - 1 := by
    rw [hK.card]
    change ¬ 9 ∣ r ^ 2 - 1
    intro hd
    apply h9
    left
    have h1 : 1 ≤ r ^ 2 := Nat.one_le_pow _ _ hr.pos
    omega
  set S := projImage (slPi true 3 (r ^ 2) K) with hS
  set ψ : X →* ProjGenLinGroup (Fin 3) K := S.subtype.comp φ.toMonoidHom with hψ
  have hψinj : Function.Injective ψ := Subtype.val_injective.comp φ.injective
  have hψS : ∀ g, ψ g ∈ S := fun g => (φ g).2
  obtain ⟨V, hVS, hV2, hVcard, hVC, hVN⟩ := exists_torus_model hK hq h9K (hψS x)
    (by rw [← map_pow, hx3, map_one]) (fun h => hx1 (hψinj (h.trans (map_one ψ).symm)))
  refine ⟨V.comap ψ, ?_, ?_, ?_, ?_⟩
  · intro v
    exact ⟨padicValNat 2 (r ^ 2 - 1), Subtype.ext (hψinj (by
      rw [Subgroup.coe_pow, map_pow, Subgroup.coe_one, map_one]
      exact hV2 _ v.2))⟩
  · have h1 : (V.comap ψ).map ψ = V := by
      rw [Subgroup.map_comap_eq, inf_eq_right]
      intro v hv
      obtain ⟨u, hu⟩ := (hVS hv : v ∈ S)
      exact ⟨φ.symm ⟨v, hVS hv⟩, by simp [hψ]⟩
    rw [← Subgroup.card_map_of_injective hψinj, h1]
    exact hVcard
  · intro v hv
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply hψinj
    rw [map_mul, map_mul]
    exact hVC _ hv
  · intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff] at hz
    refine Subgroup.mem_normalizer_fintype fun v hv => ?_
    change ψ (z * v * z⁻¹) ∈ V
    rw [map_mul, map_mul, map_inv]
    refine hVN _ (hψS z) ?_ _ hv
    rw [← map_mul, ← map_mul, hz]

end CFSG.RankThree.PartTwo.Sec15

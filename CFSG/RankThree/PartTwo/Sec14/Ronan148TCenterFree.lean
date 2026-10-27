module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148TOddCenter
import CFSG.RankThree.SubgroupLists.CentralThreeLift

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148T

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 Matrix
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.Assembly.LowTwoRank (StatedScalars)

theorem center_eq_bot_of_isoLThreePi {X : Type} [Group X] [Finite X] {p e : ℕ} [Fact p.Prime]
    (he : 1 ≤ e) (hiso : Sec4.IsoLThreePi X p e) {K : Subgroup X} (hKq : IsQuasisimple K)
    (hZ3 : IsPGroup 3 (Subgroup.center K)) : Subgroup.center K = ⊥ := by
  by_contra hZ
  obtain ⟨π, F, _, hF, hq, ⟨φ⟩⟩ := exists_slPi_quotient he hiso
  have := hF.finite
  have hπ : π = false → UnitaryFieldData p e F := fun h => by subst h; exact hF.unitary
  have hq' : π = false → ModThree false (p ^ e) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hF hq
  set H := slPi π 3 (p ^ e) F with hH
  set N := Subgroup.center H with hN
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hz3⟩ : ∃ z : Subgroup.center K, orderOf z = 3 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ3
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hZ (Subgroup.card_eq_one.mp (by rw [hk, pow_zero]))
    exact exists_prime_orderOf_dvd_card' 3 (hk ▸ dvd_pow_self 3 hk0)
  have hzpow : (z : K) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, ← hz3, pow_orderOf_eq_one, Subgroup.coe_one]
  have hz1 : (z : K) ≠ 1 := by
    intro h
    have : z = 1 := Subtype.ext h
    rw [this, orderOf_one] at hz3
    norm_num at hz3
  obtain ⟨a, b, hab⟩ : ∃ a b : K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hKq.2.2
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b =>
        exact ⟨a, b, fun h => hab (by rw [← QuotientGroup.mk_mul, h, QuotientGroup.mk_mul])⟩
  set K₁ : Subgroup (H ⧸ N) := K.map φ.toMonoidHom with hK₁
  haveI : Group.IsPerfect K := hKq.1
  haveI : Group.IsPerfect K₁ := Group.IsPerfect.map φ.toMonoidHom
  set M : Subgroup H := K₁.comap (QuotientGroup.mk' N) with hM
  set D : Subgroup H := ⁅M, M⁆ with hD
  haveI hDp : Group.IsPerfect D := SubgroupLists.isPerfect_commutator_comap le_rfl K₁
  have hDK : D.map (QuotientGroup.mk' N) = K₁ := SubgroupLists.map_commutator_comap K₁
  have hmemK : ∀ d ∈ D, QuotientGroup.mk' N d ∈ K₁ := fun d hd => hDK ▸ ⟨d, hd, rfl⟩
  have hDnc : ¬ ∀ d₁ ∈ D, ∀ d₂ ∈ D, d₁ * d₂ = d₂ * d₁ := by
    intro hc
    obtain ⟨d₁, hd₁, h₁⟩ : φ (a : X) ∈ D.map (QuotientGroup.mk' N) := hDK ▸ ⟨a, a.2, rfl⟩
    obtain ⟨d₂, hd₂, h₂⟩ : φ (b : X) ∈ D.map (QuotientGroup.mk' N) := hDK ▸ ⟨b, b.2, rfl⟩
    apply hab
    apply Subtype.ext
    apply φ.injective
    change φ ((a : X) * b) = φ ((b : X) * a)
    rw [map_mul, map_mul, ← h₁, ← h₂, ← map_mul, ← map_mul, hc d₁ hd₁ d₂ hd₂]
  set z₁ : H ⧸ N := φ ((z : K) : X) with hz₁
  have hz₁K : z₁ ∈ K₁ := ⟨(z : K), (z : K).2, rfl⟩
  have hz₁c : ∀ k ∈ K₁, k * z₁ = z₁ * k := by
    rintro _ ⟨k, hk, rfl⟩
    have h := Subgroup.mem_center_iff.mp z.2 ⟨k, hk⟩
    change φ k * φ ((z : K) : X) = φ ((z : K) : X) * φ k
    rw [← map_mul, ← map_mul]
    exact congrArg (fun t : K => φ (t : X)) h
  have hz₁3 : z₁ ^ 3 = 1 := by
    rw [hz₁, ← map_pow, ← Subgroup.coe_pow, hzpow, Subgroup.coe_one, map_one]
  have hz₁1 : z₁ ≠ 1 := by
    intro h
    apply hz1
    apply Subtype.ext
    apply φ.injective
    rw [← hz₁, h, Subgroup.coe_one, map_one]
  obtain ⟨w, hwD, hwz⟩ : z₁ ∈ D.map (QuotientGroup.mk' N) := hDK ▸ hz₁K
  have hDw : D ≤ Subgroup.centralizer {w} := by
    refine le_centralizer_of_isPerfect fun d hd => ?_
    rw [← QuotientGroup.eq_one_iff (N := N)]
    change QuotientGroup.mk' N (d * w * d⁻¹ * w⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hwz, hz₁c _ (hmemK d hd)]
    group
  set x : GL (Fin 3) F := (w : GL (Fin 3) F) with hx
  have hxH : x ∈ glPi π 3 (p ^ e) F := slPi_le_glPi hπ w.2
  have hzPi := zPi_eq hπ hq' hτ hτ1
  have hxZ : x ∉ zPi π 3 (p ^ e) F := by
    rw [hzPi]
    rintro ⟨-, hxs⟩
    apply hz₁1
    rw [← hwz]
    exact (QuotientGroup.eq_one_iff (N := N) w).mpr ((mem_center_slPi_iff hF hq w).mpr hxs)
  have hx3 : x ^ 3 ∈ zPi π 3 (p ^ e) F := by
    rw [hzPi]
    refine ⟨pow_mem hxH 3, ?_⟩
    have hw3 : w ^ 3 ∈ N := by
      rw [← QuotientGroup.eq_one_iff (N := N)]
      change QuotientGroup.mk' N (w ^ 3) = 1
      rw [map_pow, hwz, hz₁3]
    have := (mem_center_slPi_iff hF hq (w ^ 3)).mp hw3
    rwa [Subgroup.coe_pow] at this
  obtain ⟨y, ⟨s, hs, rfl⟩, hcases⟩ := rank3II_4_10_one hF hq hτ hτ1 hxH hxZ hx3
  have hsc : s ∈ StatedScalars (Fin 3) F := by
    rw [hzPi] at hs
    exact hs.2
  set C := slPi π 3 (p ^ e) F ⊓ Subgroup.centralizer {x * s} with hC
  have hDC : ∀ d ∈ D, (d : GL (Fin 3) F) ∈ C := by
    intro d hd
    refine Subgroup.mem_inf.mpr ⟨d.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : d * w = w * d := Subgroup.mem_centralizer_singleton_iff.mp (hDw hd)
    have h1' : (d : GL (Fin 3) F) * x = x * d := by
      rw [hx]
      exact congrArg Subtype.val h1
    have h2 : (d : GL (Fin 3) F) * s = s * d := commute_of_mem_statedScalars hsc _
    calc (d : GL (Fin 3) F) * (x * s) = x * (d * s) := by rw [← mul_assoc, h1', mul_assoc]
      _ = x * s * d := by rw [h2, mul_assoc]
  let ι : D →* C :=
    { toFun := fun d => ⟨(d : H), hDC d d.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hι : Function.Injective ι := fun d₁ d₂ h => by
    have := congrArg (fun t : C => (t : GL (Fin 3) F)) h
    exact Subtype.ext (Subtype.ext this)
  have hCcomm : (∀ c₁ c₂ : C, c₁ * c₂ = c₂ * c₁) → False := by
    intro hc
    apply hDnc
    intro d₁ hd₁ d₂ hd₂
    have := hc (ι ⟨d₁, hd₁⟩) (ι ⟨d₂, hd₂⟩)
    rw [← map_mul, ← map_mul] at this
    exact congrArg Subtype.val (hι this)
  rcases hcases with ⟨-, ⟨ψ⟩, -⟩ | ⟨-, ⟨ψ⟩, -⟩ | ⟨-, -, -, hcyc, -⟩
  ·
    refine hCcomm fun c₁ c₂ => ψ.injective ?_
    rw [map_mul, map_mul, mul_comm]
  ·
    let θ : D →* GL (Fin 2) F :=
      (glPi π 2 (p ^ e) F).subtype.comp (ψ.toMonoidHom.comp ι)
    have hθ : Function.Injective θ :=
      (glPi π 2 (p ^ e) F).subtype_injective.comp (ψ.injective.comp hι)
    set W : GL (Fin 2) F := θ ⟨w, hwD⟩ with hW
    have hWc : ∀ d : D, θ d * W = W * θ d := by
      intro d
      rw [hW, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hDw d.2))
    by_cases hsW : ∀ c : F, (W : Matrix (Fin 2) (Fin 2) F) ≠ c • (1 : Matrix (Fin 2) (Fin 2) F)
    · apply hDnc
      intro d₁ hd₁ d₂ hd₂
      have hm : ∀ d : D, ((θ d : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * W =
          W * ((θ d : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := fun d => by
        rw [← Units.val_mul, ← Units.val_mul, hWc d]
      have h := commute_of_commute_nonscalar hsW (hm ⟨d₁, hd₁⟩) (hm ⟨d₂, hd₂⟩)
      have h' : θ (⟨d₁, hd₁⟩ * ⟨d₂, hd₂⟩) = θ (⟨d₂, hd₂⟩ * ⟨d₁, hd₁⟩) := by
        rw [map_mul, map_mul]
        exact Units.ext (by rw [Units.val_mul, Units.val_mul, h])
      exact congrArg Subtype.val (hθ h')
    · push Not at hsW
      obtain ⟨c, hcW⟩ := hsW
      have hdet : Matrix.GeneralLinearGroup.det W = 1 := by
        let δ : D →* Fˣ := Matrix.GeneralLinearGroup.det.comp θ
        have hker : δ.ker = ⊤ := by
          rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := D)]
          exact Abelianization.commutator_subset_ker δ
        have h1 : δ ⟨w, hwD⟩ = 1 := (MonoidHom.mem_ker).mp (hker ▸ Subgroup.mem_top _)
        exact h1
      have hc2 : c ^ 2 = 1 := by
        have h1 := congrArg Units.val hdet
        rw [Matrix.GeneralLinearGroup.val_det_apply, hcW, Matrix.det_smul, Matrix.det_one,
          Fintype.card_fin, mul_one, Units.val_one] at h1
        exact h1
      have hW2 : W ^ 2 = 1 := by
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, hcW, smul_pow, one_pow, hc2, one_smul, Units.val_one]
      have hw2 : (⟨w, hwD⟩ : D) ^ 2 = 1 := hθ (by rw [map_pow, ← hW, hW2, map_one])
      apply hz₁1
      have hz₁2 : z₁ ^ 2 = 1 := by
        rw [← hwz, ← map_pow]
        have : w ^ 2 = 1 := by
          have := congrArg Subtype.val hw2
          rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
        rw [this, map_one]
      calc z₁ = z₁ ^ 3 * (z₁ ^ 2)⁻¹ := by group
        _ = 1 := by rw [hz₁3, hz₁2, inv_one, mul_one]
  ·
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    refine hCcomm fun c₁ c₂ => ?_
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg c₁)
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg c₂)
    exact (Commute.zpow_zpow_self g i j).eq

end CFSG.RankThree.PartTwo.Sec14.Ronan148T

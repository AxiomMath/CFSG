module

public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerSUCore
public import CFSG.LocalAnalysis.StandardType.GGLinearFusionCyclic
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeSUDiag

public section

namespace CFSG.StandardType

namespace RootCentSU

open Subgroup Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.BorelTits OTwoGen InnerDiagSU

section Pairs

variable {F : Type} [Field F] {σ : F ≃+* F} {n : ℕ} {G : Type*} [Group G]

theorem isJUnitary_one : IsJUnitary σ (1 : GL (Fin n) F) := by
  unfold IsJUnitary
  rw [Units.val_one, conjTr_one, Matrix.one_mul, Matrix.mul_one]

variable (σ) in
@[expose] def ggSUInducedPairs (ψ : SU σ n →* G) : Subgroup (G × GL (Fin n) F) where
  carrier := {p | IsJUnitary σ p.2 ∧ ∀ u v : SU σ n, (v : GL (Fin n) F) = p.2 * u * p.2⁻¹ →
    p.1 * ψ u * p.1⁻¹ = ψ v}
  one_mem' := ⟨isJUnitary_one, fun u v h => by
    have hv : v = u := Subtype.ext (by rw [h]; simp)
    simp [hv]⟩
  mul_mem' := by
    rintro ⟨a, A⟩ ⟨b, B⟩ ⟨hA, ha⟩ ⟨hB, hb⟩
    refine ⟨IsJUnitary.mul hA hB, fun u v h => ?_⟩
    let w : SU σ n := ⟨B * u * B⁻¹, conj_mem_SU hB u.2⟩
    have hw := hb u w rfl
    have hv := ha w v (by
      change (v : GL (Fin n) F) = A * (B * u * B⁻¹) * A⁻¹
      rw [h]
      change A * B * u * (A * B)⁻¹ = A * (B * u * B⁻¹) * A⁻¹
      group)
    change a * b * ψ u * (a * b)⁻¹ = ψ v
    calc a * b * ψ u * (a * b)⁻¹ = a * (b * ψ u * b⁻¹) * a⁻¹ := by group
      _ = a * ψ w * a⁻¹ := by rw [hw]
      _ = ψ v := hv
  inv_mem' := by
    rintro ⟨a, A⟩ ⟨hA, ha⟩
    refine ⟨IsJUnitary.inv hA, fun u v h => ?_⟩
    have hu := ha v u (by
      change (v : GL (Fin n) F) = A⁻¹ * u * A⁻¹⁻¹ at h
      rw [h]
      group)
    change a⁻¹ * ψ u * a⁻¹⁻¹ = ψ v
    rw [← hu]
    group

theorem mem_ggSUInducedPairs {ψ : SU σ n →* G} {y : G} {A : GL (Fin n) F} :
    (y, A) ∈ ggSUInducedPairs σ ψ ↔ IsJUnitary σ A ∧
      ∀ u v : SU σ n, (v : GL (Fin n) F) = A * u * A⁻¹ → y * ψ u * y⁻¹ = ψ v :=
  Iff.rfl

theorem mem_ggSUInducedPairs_of_conjSU {ψ : SU σ n →* G} {y : G} {A : GL (Fin n) F}
    (hA : IsJUnitary σ A) (h : ∀ u, y * ψ u * y⁻¹ = ψ (conjSU A hA u)) :
    (y, A) ∈ ggSUInducedPairs σ ψ :=
  ⟨hA, fun u v hv => by
    rw [h u]
    congr 1
    exact Subtype.ext hv.symm⟩

theorem mem_ggSUInducedPairs_comp_conj {ψ : SU σ n →* G} {y : G} {A : GL (Fin n) F}
    (hyA : (y, A) ∈ ggSUInducedPairs σ ψ) (h : SU σ n) :
    (y, (h : GL (Fin n) F)⁻¹ * A * h) ∈
      ggSUInducedPairs σ (ψ.comp (MulAut.conj h).toMonoidHom) := by
  obtain ⟨hA, hy⟩ := hyA
  refine ⟨IsJUnitary.mul (IsJUnitary.mul (IsJUnitary.inv (isJUnitary_of_mem_SU h)) hA)
    (isJUnitary_of_mem_SU h), fun u v hv => ?_⟩
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  refine hy _ _ ?_
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hv]
  group

end Pairs

section Kernel

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ} {G : Type*} [Group G]

theorem coe_ggInvSU_eq_ggT0GL [CharP F 2] (hm : 1 ≤ m) :
    ((ggInvSU σ (m + 1) 1 : SU σ (m + 1)) : GL (Fin (m + 1)) F) = LinFusion.ggT0GL m F := by
  apply Units.ext
  rw [coe_ggInvSU σ (by omega), LinFusion.coe_ggT0GL, ggInvMatrix_one m hm,
    ggInvUMatrix_one (by omega)]
  have hL : Fin.rev (⟨0, by omega⟩ : Fin (m + 1)) = Fin.last m := by
    ext
    simp
  rw [hL]
  rfl

theorem mem_centralizer_of_mem_ggSUInducedPairs [CharP F 2] (hm : 1 ≤ m)
    {ψ : SU σ (m + 1) →* G} (hker : ψ.ker ≤ Subgroup.center (SU σ (m + 1))) {y : G}
    {A : GL (Fin (m + 1)) F} (h : (y, A) ∈ ggSUInducedPairs σ ψ)
    (hy : y ∈ Subgroup.centralizer {ψ (ggInvSU σ (m + 1) 1)}) :
    A ∈ Subgroup.centralizer {LinFusion.ggT0GL m F} := by
  obtain ⟨hA, hpair⟩ := h
  have h1 := hpair (ggInvSU σ (m + 1) 1) (conjSU A hA (ggInvSU σ (m + 1) 1))
    (coe_conjSU A hA _)
  rw [Subgroup.mem_centralizer_singleton_iff] at hy
  have hTv : ψ (conjSU A hA (ggInvSU σ (m + 1) 1)) = ψ (ggInvSU σ (m + 1) 1) := by
    rw [← h1, hy, mul_inv_cancel_right]
  have hT2 : ggInvSU σ (m + 1) 1 * ggInvSU σ (m + 1) 1 = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Units.val_mul, coe_ggInvSU σ (by omega), Subgroup.coe_one,
      Units.val_one]
    exact ggInvUMatrix_mul_self _ _
  have hTinv : (ggInvSU σ (m + 1) 1)⁻¹ = ggInvSU σ (m + 1) 1 :=
    (eq_inv_of_mul_eq_one_left hT2).symm
  have hv2 : conjSU A hA (ggInvSU σ (m + 1) 1) * conjSU A hA (ggInvSU σ (m + 1) 1) = 1 := by
    rw [← map_mul, hT2, map_one]
  set v := conjSU A hA (ggInvSU σ (m + 1) 1) with hvdef
  obtain ⟨z, hz⟩ : ∃ z, z = v * (ggInvSU σ (m + 1) 1)⁻¹ := ⟨_, rfl⟩
  have hzc : z ∈ Subgroup.center (SU σ (m + 1)) :=
    hker (by rw [hz, MonoidHom.mem_ker, map_mul, hTv, map_inv, mul_inv_cancel])
  have hz2 : z ^ 2 = 1 := by
    have hcomm : (ggInvSU σ (m + 1) 1)⁻¹ * z = z * (ggInvSU σ (m + 1) 1)⁻¹ :=
      Subgroup.mem_center_iff.mp hzc _
    rw [pow_two]
    calc z * z = v * (ggInvSU σ (m + 1) 1)⁻¹ * z := by rw [← hz]
      _ = v * ((ggInvSU σ (m + 1) 1)⁻¹ * z) := by group
      _ = v * (z * (ggInvSU σ (m + 1) 1)⁻¹) := by rw [hcomm]
      _ = v * v * ((ggInvSU σ (m + 1) 1)⁻¹ * (ggInvSU σ (m + 1) 1)⁻¹) := by
        rw [hz]
        group
      _ = 1 := by rw [hv2, hTinv, hT2, one_mul]
  have hz1 : z = 1 := eq_one_of_mem_center_SU_of_sq_eq_one σ hzc hz2
  have hvT : v = ggInvSU σ (m + 1) 1 := by
    rw [hz, mul_inv_eq_one] at hz1
    exact hz1
  rw [Subgroup.mem_centralizer_singleton_iff, ← coe_ggInvSU_eq_ggT0GL hm]
  have h2 := congrArg (fun w : SU σ (m + 1) => (w : GL (Fin (m + 1)) F)) hvT
  simp only [hvdef, coe_conjSU] at h2
  calc A * ((ggInvSU σ (m + 1) 1 : SU σ (m + 1)) : GL (Fin (m + 1)) F) =
      A * ((ggInvSU σ (m + 1) 1 : SU σ (m + 1)) : GL (Fin (m + 1)) F) * A⁻¹ * A := by group
    _ = _ := by rw [h2]

theorem conj_eq_of_smul {n : ℕ} {A B : GL (Fin n) F} {c : Fˣ}
    (hB : (B : Matrix (Fin n) (Fin n) F) = (c : F) • (A : Matrix (Fin n) (Fin n) F))
    (u : GL (Fin n) F) : B * u * B⁻¹ = A * u * A⁻¹ := by
  set s := Matrix.GeneralLinearGroup.scalar (Fin n) c
  have hs : ∀ X : GL (Fin n) F, s * X = X * s := fun X => Units.ext (by
    rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
    exact Matrix.scalar_commute _ (fun r => Commute.all _ r) _)
  have hB' : B = s * A := Units.ext (by
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, hB, Matrix.smul_eq_diagonal_mul]
    rfl)
  rw [hB']
  calc s * A * u * (s * A)⁻¹ = s * (A * u * A⁻¹) * s⁻¹ := by group
    _ = A * u * A⁻¹ * s * s⁻¹ := by rw [hs]
    _ = A * u * A⁻¹ := by group

theorem corner_norm_eq_one (hm : 1 ≤ m) {A : GL (Fin (m + 1)) F} (hJ : IsJUnitary σ A)
    (hA : A ∈ Subgroup.centralizer {LinFusion.ggT0GL m F}) :
    σ ((A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) (Fin.last m) (Fin.last m)) *
      (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) (Fin.last m) (Fin.last m) = 1 := by
  have hc := LinFusion.commute_of_mem_centralizer hA
  have h := congrFun (congrFun hJ (Fin.last m)) 0
  rw [CFSG.LieType.Steinberg.conjTr_mul_antidiag_mul_apply,
    Finset.sum_eq_single (Fin.last m)] at h
  · rw [Fin.rev_last, ← LinFusion.corner_eq_of_commute hm hc] at h
    rw [h]
    simp [antidiag]
  · intro t _ ht
    rw [LinFusion.col_last_of_commute hm hc t, ite_eq_right ht, map_zero, zero_mul]
  · simp

end Kernel

section Cyclic

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F} {m : ℕ} {G : Type*} [Group G]

variable (σ m) in
@[expose] def SUCoreProperty : Prop :=
  ∀ M : SU σ (m + 1), M ∈ Subgroup.centralizer {ggInvSU σ (m + 1) 1} →
    mat σ (m + 1) M (Fin.last m) (Fin.last m) = 1 →
      M ∈ ggOTwoPrime (Subgroup.centralizer {ggInvSU σ (m + 1) 1})

theorem suCoreProperty_of_card [Finite F] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
    (hm : 3 ≤ m) : SUCoreProperty (unitaryInvolution F 2 f) m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  intro M hM h1
  exact mem_ggOTwoPrime_centralizer_of_corner hF (by omega) hM h1

theorem mem_ggOTwoPrime_of_ggCentChar_eq_one_su (hm : 1 ≤ m) (hcore : SUCoreProperty σ m)
    {ψ : SU σ (m + 1) →* G} (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {z : G}
    {A : GL (Fin (m + 1)) F} (hzA : (z, A) ∈ ggSUInducedPairs σ ψ)
    (hA : A ∈ Subgroup.centralizer {LinFusion.ggT0GL m F})
    (hχ : LinFusion.ggCentChar F hm ⟨A, hA⟩ = 1) :
    z ∈ ggOTwoPrime (ψ.range ⊓ Subgroup.centralizer {ψ (ggInvSU σ (m + 1) 1)}) := by
  set l := LinFusion.ggCentLambda F hm ⟨A, hA⟩ with hl
  have hdet := LinFusion.det_eq_of_ggCentChar_eq_one hm hχ
  obtain ⟨hJ, hpair⟩ := hzA
  have hpair' : ∀ u v : SU σ (m + 1), (v : GL (Fin (m + 1)) F) = A * u * A⁻¹ →
      z * ψ u * z⁻¹ = ψ v := hpair
  have hnorm := corner_norm_eq_one hm hJ hA
  have hlA : ((l : Fˣ) : F) = (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) (Fin.last m)
      (Fin.last m) := LinFusion.coe_ggCentLambda hm ⟨A, hA⟩
  set Mm : Matrix (Fin (m + 1)) (Fin (m + 1)) F :=
    ((l⁻¹ : Fˣ) : F) • (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) with hMm
  have hMdet : Mm.det = 1 := by
    rw [hMm, det_smul, Fintype.card_fin, hdet, ← mul_pow, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, one_pow]
  have hσl : σ ((l⁻¹ : Fˣ) : F) * ((l⁻¹ : Fˣ) : F) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, ← mul_inv, hlA, hnorm, inv_one]
  have hMiso : conjTr σ Mm * antidiag (m + 1) * Mm = antidiag (m + 1) := by
    have hc : conjTr σ Mm = σ ((l⁻¹ : Fˣ) : F) •
        conjTr σ (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) := by
      ext a b
      simp [hMm, conjTr]
    rw [hc, hMm, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hσl, one_smul]
    exact hJ
  have hMu : IsUnit Mm.det := by
    rw [hMdet]
    exact isUnit_one
  let MGL : GL (Fin (m + 1)) F :=
    ⟨Mm, Mm⁻¹, Matrix.mul_nonsing_inv _ hMu, Matrix.nonsing_inv_mul _ hMu⟩
  let Msu : SU σ (m + 1) := ⟨MGL, hMdet, hMiso⟩
  have hAc := LinFusion.commute_of_mem_centralizer hA
  have hMC : Msu ∈ Subgroup.centralizer {ggInvSU σ (m + 1) 1} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul,
      coe_ggInvSU_eq_ggT0GL hm, LinFusion.coe_ggT0GL]
    change Mm * ggInvMatrix (m + 1) 1 F = ggInvMatrix (m + 1) 1 F * Mm
    rw [hMm, Matrix.smul_mul, Matrix.mul_smul, hAc]
  have hM1 : mat σ (m + 1) Msu (Fin.last m) (Fin.last m) = 1 := by
    change (((l⁻¹ : Fˣ) : F) • (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F)) (Fin.last m)
      (Fin.last m) = 1
    rw [Matrix.smul_apply, smul_eq_mul, ← hlA, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hMO := hcore Msu hMC hM1
  have hz : z = ψ Msu := by
    have hw : (ψ Msu)⁻¹ * z ∈ Subgroup.centralizer (ψ.range : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨u, rfl⟩
      have h := hpair' u (Msu * u * Msu⁻¹) (by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact conj_eq_of_smul (c := l⁻¹) rfl (u : GL (Fin (m + 1)) F))
      rw [map_mul, map_mul, map_inv] at h
      calc ψ u * ((ψ Msu)⁻¹ * z) = (ψ Msu)⁻¹ * (ψ Msu * ψ u * (ψ Msu)⁻¹) * z := by group
        _ = (ψ Msu)⁻¹ * (z * ψ u * z⁻¹) * z := by rw [h]
        _ = (ψ Msu)⁻¹ * z * ψ u := by group
    rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hw
    exact hw.symm
  rw [hz]
  refine LinFusion.ggOTwoPrime_mono ?_
    (LinFusion.map_ggOTwoPrime_le ψ _ (Subgroup.mem_map_of_mem ψ hMO))
  intro x hx
  obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hx
  refine Subgroup.mem_inf.mpr ⟨⟨v, rfl⟩, ?_⟩
  have hv' := Subgroup.mem_centralizer_singleton_iff.mp hv
  exact Subgroup.mem_centralizer_singleton_iff.mpr (by rw [← map_mul, hv', map_mul])

theorem exists_zpowers_sup_ggOTwoPrime_su [Finite F] (hm : 1 ≤ m) (hcore : SUCoreProperty σ m)
    (ψ : SU σ (m + 1) →* G) (hker : ψ.ker ≤ Subgroup.center (SU σ (m + 1)))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) (Y : Subgroup G)
    (hYr : Y ≤ Subgroup.centralizer {ψ (ggInvSU σ (m + 1) 1)})
    (hY : ∀ y ∈ Y, ∃ A : GL (Fin (m + 1)) F, (y, A) ∈ ggSUInducedPairs σ ψ) :
    ∃ y₀ ∈ Y, Y ≤ Subgroup.zpowers y₀ ⊔
      ggOTwoPrime (ψ.range ⊓ Subgroup.centralizer {ψ (ggInvSU σ (m + 1) 1)}) := by
  set SY : Subgroup (G × GL (Fin (m + 1)) F) := ggSUInducedPairs σ ψ ⊓ Y.prod ⊤ with hSY
  have hmem : ∀ p : SY, (p : G × GL (Fin (m + 1)) F).2 ∈
      Subgroup.centralizer {LinFusion.ggT0GL m F} :=
    fun p => mem_centralizer_of_mem_ggSUInducedPairs hm hker p.2.1 (hYr p.2.2.1)
  let π : SY →* Subgroup.centralizer {LinFusion.ggT0GL m F} :=
    MonoidHom.codRestrict ((MonoidHom.snd G (GL (Fin (m + 1)) F)).comp SY.subtype) _ hmem
  let φ : SY →* Fˣ := (LinFusion.ggCentChar F hm).comp π
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := φ.range)
  obtain ⟨p₀, hp₀⟩ := g.2
  refine ⟨(p₀ : G × GL (Fin (m + 1)) F).1, p₀.2.2.1, fun y hy => ?_⟩
  obtain ⟨A, hA⟩ := hY y hy
  let p : SY := ⟨(y, A), hA, hy, Subgroup.mem_top A⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨φ p, p, rfl⟩)
  have hk' : φ (p₀ ^ k) = φ p := by
    rw [map_zpow, hp₀]
    exact congrArg Subtype.val hk
  set q : SY := p * (p₀ ^ k)⁻¹ with hq
  have hφq : φ q = 1 := by rw [hq, map_mul, map_inv, hk', mul_inv_cancel]
  have hzq := mem_ggOTwoPrime_of_ggCentChar_eq_one_su hm hcore hC q.2.1 (hmem q) hφq
  have hpow : ((p₀ ^ k : SY) : G × GL (Fin (m + 1)) F).1 =
      (p₀ : G × GL (Fin (m + 1)) F).1 ^ k := by
    rw [Subgroup.coe_zpow]
    exact map_zpow (MonoidHom.fst G (GL (Fin (m + 1)) F)) _ k
  have hy' : y = (q : G × GL (Fin (m + 1)) F).1 * ((p₀ : G × GL (Fin (m + 1)) F).1) ^ k := by
    rw [hq, Subgroup.coe_mul, Subgroup.coe_inv, Prod.fst_mul, Prod.fst_inv, hpow,
      inv_mul_cancel_right]
  rw [hy']
  exact mul_mem (Subgroup.mem_sup_right hzq)
    (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers _ k))

end Cyclic

section LongRoot

open CFSG.Assembly.LowTwoRank

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f m : ℕ} {G : Type} [Group G]

theorem exists_zpowers_sup_ggOTwoPrime_of_longRoot [Fact (Nat.Prime 2)]
    (hF : Nat.card F = (2 ^ f) ^ 2) (hm : 3 ≤ m)
    (ψ : SU (unitaryInvolution F 2 f) (m + 1) →* G)
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) (m + 1)))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {t : StatedLieTag} (ht : GGTwistedTag t)
    {r : G} (hr : GGRootInvolution (rootDatum hF (m + 1)) t ψ r) (Y : Subgroup G)
    (hYr : Y ≤ Subgroup.centralizer {r})
    (hYd : ∀ y ∈ Y, GGPsiInnerDiag (rootDatum hF (m + 1)) ψ y) :
    ∃ y₀ ∈ Y, Y ≤ Subgroup.zpowers y₀ ⊔ ggOTwoPrime (ψ.range ⊓ Subgroup.centralizer {r}) := by
  obtain ⟨hr2, γ, ⟨-, hlong⟩, u₀, hru⟩ := hr
  obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hru
  have hx1 : x ≠ 1 := by
    rintro rfl
    simp at hr2
  obtain ⟨a, ha⟩ := exists_conj_ggInvSU_of_longRoot hF (hlong ht) hx hx1
  set h := u₀ * a with hh
  set ψ' := ψ.comp (MulAut.conj h).toMonoidHom with hψ'
  have hr' : ψ' (ggInvSU (unitaryInvolution F 2 f) (m + 1) 1) =
      ψ ((MulAut.conj u₀).toMonoidHom x) := by
    simp only [hψ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ha, hh]
    congr 1
    group
  have hrange : ψ'.range = ψ.range := by
    rw [hψ', MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulEquiv.surjective _),
      ← MonoidHom.range_eq_map]
  have hker' : ψ'.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) (m + 1)) := by
    intro v hv
    have hz : h * v * h⁻¹ ∈ Subgroup.center (SU (unitaryInvolution F 2 f) (m + 1)) := hker hv
    have h1 := (inferInstance :
      (Subgroup.center (SU (unitaryInvolution F 2 f) (m + 1))).Normal).conj_mem _ hz h⁻¹
    rwa [inv_inv, show h⁻¹ * (h * v * h⁻¹) * h = v by group] at h1
  have hC' : Subgroup.centralizer (ψ'.range : Set G) = ⊥ := by
    rw [hrange]
    exact hC
  have hYr' : Y ≤ Subgroup.centralizer {ψ' (ggInvSU (unitaryInvolution F 2 f) (m + 1) 1)} := by
    rw [hr']
    exact hYr
  have hY' : ∀ y ∈ Y, ∃ A : GL (Fin (m + 1)) F,
      (y, A) ∈ ggSUInducedPairs (unitaryInvolution F 2 f) ψ' := by
    intro y hy
    obtain ⟨A, hA, hconj⟩ :=
      suInnerDiagConj hF (by omega) G ψ hker y⁻¹ (hYd y⁻¹ (Y.inv_mem hy))
    have hpair : (y, A) ∈ ggSUInducedPairs (unitaryInvolution F 2 f) ψ :=
      mem_ggSUInducedPairs_of_conjSU hA (fun u => by rw [← hconj u, inv_inv])
    exact ⟨_, mem_ggSUInducedPairs_comp_conj hpair h⟩
  obtain ⟨y₀, hy₀, hle⟩ := exists_zpowers_sup_ggOTwoPrime_su (by omega)
    (suCoreProperty_of_card hF hm) ψ' hker' hC' Y hYr' hY'
  rw [hrange, hr'] at hle
  exact ⟨y₀, hy₀, hle⟩

end LongRoot

end RootCentSU

section Tags

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits

theorem ggRootCentralizerCyclicTag_PSU : GGRootCentralizerCyclicTag .PSU := by
  intro G _ _ n f
  by_cases hf : 1 ≤ f
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have e : ggU .PSU n f =
        ⟨Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n,
          Unitary.rootDatum (card_galoisField_two_mul 2 f hf) n⟩ := by
      simp only [ggU, lieUniversal, hf, ↓reduceDIte]
    rw [e]
    intro ψ _ hrk hker hC r hr Y hY hYd
    have hn : 4 ≤ n := by
      change 2 ≤ n / 2 at hrk
      omega
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact RootCentSU.exists_zpowers_sup_ggOTwoPrime_of_longRoot
      (card_galoisField_two_mul 2 f hf) (by omega) ψ hker hC (Or.inl rfl) hr Y
      (fun y hy => (hY hy).2) hYd
  · intro ψ hadm
    exact absurd hadm.2.1 hf

end Tags

end CFSG.StandardType

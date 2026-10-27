module

public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitQuaternionWeights
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitProjectiveLift
public import CFSG.ClassicalInvolution.AschTight.Sec7L98H
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.SignalizerFunctorTheorem.NonLocal
open CFSG.RankThree.PartTwo.Sec4

variable {F V G Y : Type*} [Field F] [IsAlgClosed F]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  [Group G] [Group Y]

theorem eight_le_finrank_of_lifted_q8_inverts
    (ρ : G →* (V ≃ₗ[F] V)) (hρ : Function.Injective ρ)
    (e : G ≃* Y)
    {E Q : Subgroup Y} [Finite E]
    (hEne : E ≠ ⊥)
    (hEab : IsMulCommutative E)
    (hEodd : Odd (Nat.card E))
    (hEchar : (Nat.card E : F) ≠ 0)
    (eQ : ↥Q ≃* QuaternionGroup 2)
    (hQE : ∀ q ∈ Q, ∀ x ∈ E, q * x * q⁻¹ ∈ E)
    (zQ : ↥Q) (hzQ : eQ zQ = QuaternionGroup.a 2)
    (hinv : ∀ x ∈ E, (zQ : Y) * x * (zQ : Y)⁻¹ = x⁻¹) :
    8 ≤ Module.finrank F V := by
  classical
  let E' : Subgroup G := E.comap e.toMonoidHom
  let Q' : Subgroup G := Q.comap e.toMonoidHom
  have hE'map : E'.map e.toMonoidHom = E := by
    apply Subgroup.map_comap_eq_self
    rw [MonoidHom.range_eq_top.mpr e.surjective]
    exact le_top
  have hQ'map : Q'.map e.toMonoidHom = Q := by
    apply Subgroup.map_comap_eq_self
    rw [MonoidHom.range_eq_top.mpr e.surjective]
    exact le_top
  let eE : E' ≃* E :=
    (Subgroup.equivMapOfInjective E' e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hE'map)
  let eQ' : Q' ≃* Q :=
    (Subgroup.equivMapOfInjective Q' e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hQ'map)
  have heE_apply : ∀ x : E', ((eE x : E) : Y) = e (x : G) := by
    intro x
    rfl
  have heQ_apply : ∀ x : Q', ((eQ' x : Q) : Y) = e (x : G) := by
    intro x
    rfl
  have hcardE' : Nat.card E' = Nat.card E := Nat.card_congr eE.toEquiv
  have : Finite E' := Finite.of_injective (eE : E' → E) eE.injective
  have hEab' : IsMulCommutative E' := by
    refine isMulCommutative_iff.mpr ?_
    intro x y
    apply eE.injective
    rw [map_mul, map_mul]
    exact isMulCommutative_iff.mp hEab (eE x) (eE y)
  have hEodd' : Odd (Nat.card E') := hcardE' ▸ hEodd
  have hEchar' : (Nat.card E' : F) ≠ 0 := hcardE' ▸ hEchar
  have hEne' : E' ≠ ⊥ := by
    intro hbot
    apply hEne
    have hcard : Nat.card E' = 1 := by rw [hbot, Subgroup.card_bot]
    exact Subgroup.card_eq_one.mp (hcardE'.symm.trans hcard)
  let eQ8 : Q' ≃* QuaternionGroup 2 := eQ'.trans eQ
  let zQ' : Q' := eQ'.symm zQ
  have hzQ8 : eQ8 zQ' = QuaternionGroup.a 2 := by
    simp [eQ8, zQ', hzQ]
  have hQE' : ∀ q ∈ Q', ∀ x ∈ E', q * x * q⁻¹ ∈ E' := by
    intro q hq x hx
    rw [Subgroup.mem_comap]
    have hqQ : e q ∈ Q := hq
    have hxE : e x ∈ E := hx
    simpa [map_mul] using hQE (e q) hqQ (e x) hxE
  have hinv' : ∀ x ∈ E', (zQ' : G) * x * (zQ' : G)⁻¹ = x⁻¹ := by
    intro x hx
    apply e.injective
    have hz : e (zQ' : G) = (zQ : Y) := by
      rw [← heQ_apply zQ']
      exact congrArg Subtype.val (eQ'.apply_symm_apply zQ)
    have hx' : e (x : G) = (eE ⟨x, hx⟩ : E) := by
      rw [← heE_apply ⟨x, hx⟩]
    simp only [map_mul, map_inv, hz, hx']
    exact hinv (eE ⟨x, hx⟩) (eE ⟨x, hx⟩).2
  exact eight_le_finrank_of_q8_inverts (ρ := ρ) (E := E') (Q := Q')
    hEab' hEodd' hEchar' (fun x _ hx => hρ (by simpa using hx)) eQ8 hQE'
    zQ' hzQ8 hinv' hEne'

theorem false_of_odd_abelian_q8_in_projective_sl3
    {K : Type} [Field K] {p f : ℕ} {π : Bool}
    (hK : PiField π p f K)
    {E Q : Subgroup (CFSG.PGLModel.projImage (slPi π 3 (p ^ f) K))}
    (hEne : E ≠ ⊥)
    (hEab : IsMulCommutative E)
    (hEodd : Odd (Nat.card E))
    (hE3 : ¬ 3 ∣ Nat.card E)
    (hEp : ¬ p ∣ Nat.card E)
    (eQ : ↥Q ≃* QuaternionGroup 2)
    (hQE : ∀ q ∈ Q, ∀ x ∈ E, q * x * q⁻¹ ∈ E)
    (zQ : ↥Q) (hzQ : eQ zQ = QuaternionGroup.a 2)
    (hinv : ∀ x ∈ E,
      (zQ : CFSG.PGLModel.projImage (slPi π 3 (p ^ f) K)) * x *
        (zQ : CFSG.PGLModel.projImage (slPi π 3 (p ^ f) K))⁻¹ = x⁻¹) :
    False := by
  classical
  have : Finite K := hK.finite
  let P := CFSG.PGLModel.projImage (slPi π 3 (p ^ f) K)
  let Y : Subgroup P := E ⊔ Q
  have hQcard : Nat.card Q = 8 := by
    rw [Nat.card_congr eQ.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hQ2 : IsPGroup 2 Q := by
    refine IsPGroup.of_card (n := 3) ?_
    rw [hQcard]
    norm_num
  have hQnorm : Q ≤ Subgroup.normalizer (E : Set P) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hQE q hq x hx
    · intro hx
      have h := hQE q⁻¹ (Q.inv_mem hq) (q * x * q⁻¹) hx
      have h' : q⁻¹ * (q * x * q⁻¹) * (q⁻¹)⁻¹ = x := by group
      rwa [h'] at h
  have hEinf : E ⊓ Q = ⊥ :=
    CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7.inf_eq_bot_of_odd_of_isPGroup
      hEodd hQ2
  have hcardY : Nat.card Y = Nat.card Q * Nat.card E := by
    have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := Q) (K := E) hQnorm
    rw [sup_comm, inf_comm, hEinf, Subgroup.card_bot, mul_one] at h
    exact h
  have hY3 : ¬ 3 ∣ Nat.card Y := by
    intro h3
    rw [hcardY, hQcard] at h3
    rcases (Nat.prime_three.dvd_mul).mp h3 with h | h
    · norm_num at h
    · exact hE3 h
  obtain ⟨Ŷ, hŶ, eLift, heLift⟩ :=
    exists_lift_projective_sl3 hK Y hY3
  let EY : Subgroup ↥Y := E.subgroupOf Y
  let QY : Subgroup ↥Y := Q.subgroupOf Y
  let eEY : EY ≃* E := Subgroup.subgroupOfEquivOfLe (le_sup_left : E ≤ Y)
  let eQY0 : QY ≃* Q := Subgroup.subgroupOfEquivOfLe (le_sup_right : Q ≤ Y)
  let eQY : QY ≃* QuaternionGroup 2 := eQY0.trans eQ
  let zQY : QY := eQY0.symm zQ
  have hzQY : eQY zQY = QuaternionGroup.a 2 := by
    simp [eQY, zQY, hzQ]
  have hcardEY : Nat.card EY = Nat.card E := Nat.card_congr eEY.toEquiv
  have hEneY : EY ≠ ⊥ := by
    intro hbot
    apply hEne
    have hcard : Nat.card EY = 1 := by rw [hbot, Subgroup.card_bot]
    exact Subgroup.card_eq_one.mp (hcardEY.symm.trans hcard)
  have hEabY : IsMulCommutative EY := by
    refine isMulCommutative_iff.mpr ?_
    intro x y
    apply eEY.injective
    rw [map_mul, map_mul]
    exact isMulCommutative_iff.mp hEab (eEY x) (eEY y)
  have hEoddY : Odd (Nat.card EY) := hcardEY ▸ hEodd
  have hE3Y : ¬ 3 ∣ Nat.card EY := by
    intro h
    rw [hcardEY] at h
    exact hE3 h
  have hEpY : ¬ p ∣ Nat.card EY := by
    intro h
    rw [hcardEY] at h
    exact hEp h
  have hQEY : ∀ q ∈ QY, ∀ x ∈ EY, q * x * q⁻¹ ∈ EY := by
    intro q hq x hx
    apply Subgroup.mem_subgroupOf.mpr
    have hqQ : (q : P) ∈ Q := hq
    have hxE : (x : P) ∈ E := hx
    simpa using hQE (q : P) hqQ (x : P) hxE
  have hinvY : ∀ x ∈ EY, (zQY : ↥Y) * x * (zQY : ↥Y)⁻¹ = x⁻¹ := by
    intro x hx
    apply Subtype.ext
    have hxE : (x : P) ∈ E := by
      rw [← Subgroup.mem_subgroupOf]
      exact hx
    have hzP : (zQY : P) = (zQ : P) :=
      Subgroup.subgroupOfEquivOfLe_symm_apply_coe_coe (le_sup_right : Q ≤ Y) zQ
    change (zQY : P) * (x : P) * (zQY : P)⁻¹ = (x : P)⁻¹
    rw [hzP]
    exact hinv (x : P) hxE
  let L := AlgebraicClosure K
  have : Fintype K := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hK.prime⟩
  have hcharK : CharP K p := by
    cases π
    · exact charP_of_card_eq_prime_pow (f := 2 * f) (by
        rw [← Nat.card_eq_fintype_card, hK.card]
        simp [piCard, pow_mul, mul_comm])
    · exact charP_of_card_eq_prime_pow (f := f) (by
        rw [← Nat.card_eq_fintype_card, hK.card]
        simp [piCard])
  have : CharP K p := hcharK
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have hEcharY : (Nat.card EY : L) ≠ 0 := by
    intro h
    exact hEpY ((CharP.cast_eq_zero_iff L p (Nat.card EY)).mp h)
  let fGL : GL (Fin 3) K →* GL (Fin 3) L :=
    Matrix.GeneralLinearGroup.map (algebraMap K L)
  have hfGL : Function.Injective fGL :=
    Matrix.GeneralLinearGroup.map_injective (algebraMap K L).injective
  let nat : GL (Fin 3) L →* ((Fin 3 → L) ≃ₗ[L] (Fin 3 → L)) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv L (Fin 3 → L)).toMonoidHom.comp
      (Matrix.GeneralLinearGroup.toLin (n := Fin 3) (R := L)).toMonoidHom
  have hnat : Function.Injective nat := by
    intro x y hxy
    exact (Matrix.GeneralLinearGroup.toLin (n := Fin 3) (R := L)).injective
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv L (Fin 3 → L)).injective hxy)
  let ρ : GL (Fin 3) K →* ((Fin 3 → L) ≃ₗ[L] (Fin 3 → L)) := nat.comp fGL
  have hρ : Function.Injective ρ := hnat.comp hfGL
  let ρŶ : Ŷ →* ((Fin 3 → L) ≃ₗ[L] (Fin 3 → L)) := ρ.comp Ŷ.subtype
  have hρŶ : Function.Injective ρŶ := hρ.comp Ŷ.subtype_injective
  have h8 : 8 ≤ Module.finrank L (Fin 3 → L) :=
    eight_le_finrank_of_lifted_q8_inverts (F := L) (V := Fin 3 → L)
      ρŶ hρŶ eLift hEneY hEabY hEoddY hEcharY eQY hQEY zQY hzQY hinvY
  have hdim : Module.finrank L (Fin 3 → L) = 3 := by
    rw [Module.finrank_fin_fun]
  rw [hdim] at h8
  omega

theorem false_of_odd_abelian_q8_in_projective_sl3_of_mulEquiv
    {K : Type} [Field K] {p f : ℕ} {π : Bool}
    (hK : PiField π p f K)
    {G : Type*} [Group G]
    (eG : G ≃* CFSG.PGLModel.projImage (slPi π 3 (p ^ f) K))
    {E Q : Subgroup G}
    (hEne : E ≠ ⊥)
    (hEab : IsMulCommutative E)
    (hEodd : Odd (Nat.card E))
    (hE3 : ¬ 3 ∣ Nat.card E)
    (hEp : ¬ p ∣ Nat.card E)
    (eQ : ↥Q ≃* QuaternionGroup 2)
    (hQE : ∀ q ∈ Q, ∀ x ∈ E, q * x * q⁻¹ ∈ E)
    (zQ : ↥Q) (hzQ : eQ zQ = QuaternionGroup.a 2)
    (hinv : ∀ x ∈ E, (zQ : G) * x * (zQ : G)⁻¹ = x⁻¹) :
    False := by
  classical
  let P := CFSG.PGLModel.projImage (slPi π 3 (p ^ f) K)
  let E' : Subgroup P := E.map eG.toMonoidHom
  let Q' : Subgroup P := Q.map eG.toMonoidHom
  let eE : E ≃* E' := Subgroup.equivMapOfInjective E eG.toMonoidHom eG.injective
  let eQ' : Q ≃* Q' := Subgroup.equivMapOfInjective Q eG.toMonoidHom eG.injective
  have hQ_apply : ∀ x : Q, (eQ' x : P) = eG (x : G) := fun x => rfl
  have hcardE : Nat.card E' = Nat.card E := (Nat.card_congr eE.toEquiv).symm
  have hEne' : E' ≠ ⊥ := by
    intro hbot
    apply hEne
    have hcard : Nat.card E' = 1 := by rw [hbot, Subgroup.card_bot]
    exact Subgroup.card_eq_one.mp (hcardE.symm.trans hcard)
  have hEab' : IsMulCommutative E' := by
    refine isMulCommutative_iff.mpr ?_
    intro x y
    apply eE.symm.injective
    rw [map_mul, map_mul]
    exact isMulCommutative_iff.mp hEab (eE.symm x) (eE.symm y)
  have hEodd' : Odd (Nat.card E') := hcardE ▸ hEodd
  have hE3' : ¬ 3 ∣ Nat.card E' := by
    intro h
    rw [hcardE] at h
    exact hE3 h
  have hEp' : ¬ p ∣ Nat.card E' := by
    intro h
    rw [hcardE] at h
    exact hEp h
  let eQ'' : Q' ≃* QuaternionGroup 2 := eQ'.symm.trans eQ
  let zQ' : Q' := eQ' zQ
  have hzQ' : eQ'' zQ' = QuaternionGroup.a 2 := by
    simp [eQ'', zQ', hzQ]
  have hQE' : ∀ q' ∈ Q', ∀ x' ∈ E', q' * x' * q'⁻¹ ∈ E' := by
    intro q' hq' x' hx'
    obtain ⟨q, hqQ, rfl⟩ := Subgroup.mem_map.mp hq'
    obtain ⟨x, hxE, rfl⟩ := Subgroup.mem_map.mp hx'
    refine Subgroup.mem_map.mpr ⟨q * x * q⁻¹, hQE q hqQ x hxE, ?_⟩
    simp only [map_mul, map_inv]
  have hinv' : ∀ x' ∈ E', (zQ' : P) * x' * (zQ' : P)⁻¹ = x'⁻¹ := by
    intro x' hx'
    obtain ⟨x, hxE, rfl⟩ := Subgroup.mem_map.mp hx'
    have hz : (zQ' : P) = eG (zQ : G) := hQ_apply zQ
    simpa [hz, map_mul, map_inv] using congrArg eG (hinv x hxE)
  exact false_of_odd_abelian_q8_in_projective_sl3 hK
    hEne' hEab' hEodd' hE3' hEp' eQ'' hQE' zQ' hzQ' hinv'

theorem false_of_odd_abelian_q8_in_lieModel_PSL3_or_PSU3
    {G : Type} [Group G] {p f : ℕ}
    (h : CFSG.Blueprint.LieModel G .PSL 3 p f ∨
      CFSG.Blueprint.LieModel G .PSU 3 p f)
    {E Q : Subgroup G}
    (hEne : E ≠ ⊥)
    (hEab : IsMulCommutative E)
    (hEodd : Odd (Nat.card E))
    (hE3 : ¬ 3 ∣ Nat.card E)
    (hEp : ¬ p ∣ Nat.card E)
    (eQ : ↥Q ≃* QuaternionGroup 2)
    (hQE : ∀ q ∈ Q, ∀ x ∈ E, q * x * q⁻¹ ∈ E)
    (zQ : ↥Q) (hzQ : eQ zQ = QuaternionGroup.a 2)
    (hinv : ∀ x ∈ E, (zQ : G) * x * (zQ : G)⁻¹ = x⁻¹) :
    False := by
  rcases h with hPSL | hPSU
  · rcases hPSL with ⟨-, hSC⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩
    · rcases hSC with ⟨hadm, K, iK, fK, hKcard, ⟨eX⟩⟩
      let : Field K := iK
      let : Finite K := fK
      have hK : PiField true p f K :=
        ⟨hadm.1, hadm.2.1, by simpa [piCard] using hKcard⟩
      let eG : G ≃* CFSG.PGLModel.projImage (slPi true 3 (p ^ f) K) :=
        eX.trans (CFSG.Open.StatedAPI.mapMkEquivStatedProj (CFSG.Open.StatedSL 3 K)).symm
      exact false_of_odd_abelian_q8_in_projective_sl3_of_mulEquiv hK eG
        hEne hEab hEodd hE3 hEp eQ hQE zQ hzQ hinv
    all_goals omega
  · rcases hPSU with ⟨-, hSC⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩
    · rcases hSC with ⟨hadm, K, iK, fK, hKcard, ⟨eX⟩⟩
      let : Field K := iK
      let : Finite K := fK
      have hK : PiField false p f K :=
        ⟨hadm.1, hadm.2.1, by simpa [piCard] using hKcard⟩
      let eG : G ≃* CFSG.PGLModel.projImage (slPi false 3 (p ^ f) K) :=
        eX.trans (CFSG.Open.StatedAPI.mapMkEquivStatedProj (CFSG.Open.StatedSU 3 (p ^ f) K)).symm
      exact false_of_odd_abelian_q8_in_projective_sl3_of_mulEquiv hK eG
        hEne hEab hEodd hE3 hEp eQ hQE zQ hzQ hinv
    all_goals omega

end CFSG.LocalAnalysis.UniquenessCase.UC22

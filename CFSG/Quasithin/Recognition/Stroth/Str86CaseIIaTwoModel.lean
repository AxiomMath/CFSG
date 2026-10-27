module

public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIaBasic
public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIaTwoTransport
public import CFSG.Quasithin.Recognition.Stroth.Str86U3Model3
public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoBound
public import CFSG.Quasithin.Vol2.Ch1Sec3Basic
public import CFSG.Quasithin.Background.AutOnCard

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open scoped Pointwise commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]

noncomputable section

theorem isSylowIn_su3Anti_ujSub {K : Type} [Field K] [Finite K] [CharP K 2] {k : ℕ}
    (hk : 1 ≤ k) (hFc : Nat.card K = (2 ^ k) ^ 2) :
    IsSylowIn 2 (CFSG.Quasithin.H.SU3.ujSub k K) (su3Anti K k) := by
  have hSyl := CFSG.Quasithin.H.SU3.isSylowIn_uiSub (K := K) hk hFc
  let W : GL (Fin 3) K := CFSG.Quasithin.H.SU3.wittGL (K := K)
  let e : GL (Fin 3) K ≃* GL (Fin 3) K := MulAut.conj W⁻¹
  have h1 : IsSylowIn 2 ((CFSG.Quasithin.H.SU3.uiSub k K).map e.toMonoidHom)
      ((StatedSU 3 (2 ^ k) K).map e.toMonoidHom) :=
    (CFSG.Quasithin.E1.isSylowIn_map_mulEquiv e).mpr hSyl
  have hU : (CFSG.Quasithin.H.SU3.uiSub k K).map e.toMonoidHom =
      CFSG.Quasithin.H.SU3.ujSub k K := by
    rw [CFSG.Quasithin.H.SU3.uiSub, Subgroup.map_map]
    have hcomp : (e.toMonoidHom.comp (MulAut.conj W).toMonoidHom) =
        MonoidHom.id (GL (Fin 3) K) := by
      refine MonoidHom.ext fun x => ?_
      dsimp only [e]
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.id_apply]
      change (MulAut.conj W⁻¹) ((MulAut.conj W) x) = x
      rw [MulAut.conj_apply, MulAut.conj_apply]
      group
    rw [hcomp, Subgroup.map_id]
  have hH : (StatedSU 3 (2 ^ k) K).map e.toMonoidHom = su3Anti K k := rfl
  rwa [hU, hH] at h1


theorem binaryNaturalSU3_su3Anti_model {V : Type} [CommGroup V] [Finite V]
    {H : Subgroup (MulAut V)} {k : ℕ} (hk : 2 ≤ k) (h : BinaryNaturalSU3 H ⊤ ⊥ k) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      Nat.card K = (2 ^ k) ^ 2 ∧
      ∃ (Φ : V ≃* Multiplicative (Fin 3 → K)) (ρ : ↥H →* ↥(su3Anti K k)),
        Function.Surjective ρ ∧
        ∀ (x : ↥H) (v : V),
          Φ ((x : MulAut V) v) =
            Multiplicative.ofAdd
              ((((ρ x : ↥(su3Anti K k)) : GL (Fin 3) K) :
                Matrix (Fin 3) (Fin 3) K) *ᵥ (Φ v).toAdd) := by
  classical
  obtain ⟨K, hKf, hKfin, hKcard, π, hπsurj, Φ₀, hΦ₀⟩ :=
    binaryNaturalSU3_realization (V := V) h
  letI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := 2 * k) (by
      rw [← Nat.card_eq_fintype_card, hKcard, ← pow_mul, mul_comm])
  have hπinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    have hnat : ∀ w : Multiplicative (Fin 3 → K),
        natAct (StatedSU 3 (2 ^ k) K) γ w = w := by
      intro w
      obtain ⟨v, rfl⟩ := Φ₀.surjective w
      have h1 : ((π γ : ↥H) : MulAut V) v = v := by rw [hγ]; rfl
      rw [← hΦ₀ γ v, h1]
    exact natAct_faithful (StatedSU 3 (2 ^ k) K) γ
      (fun m => by rw [hnat m, mul_inv_cancel])
  let eπ : ↥(StatedSU 3 (2 ^ k) K) ≃* ↥H :=
    MulEquiv.ofBijective π ⟨hπinj, hπsurj⟩
  obtain ⟨P, -, hPmap⟩ := statedSU3_conj_anti (F := K) (k := k) hk hKcard
  let eΨ₀ : ↥(StatedSU 3 (2 ^ k) K) ≃*
      ↥((StatedSU 3 (2 ^ k) K).map (MulAut.conj P).toMonoidHom) :=
    Subgroup.equivMapOfInjective _ _ (MulAut.conj P).injective
  let eΨ : ↥(StatedSU 3 (2 ^ k) K) ≃* ↥(su3Anti K k) :=
    eΨ₀.trans (MulEquiv.subgroupCongr hPmap)
  have hΨ_apply : ∀ γ : ↥(StatedSU 3 (2 ^ k) K),
      ((eΨ γ : ↥(su3Anti K k)) : GL (Fin 3) K) = P * (γ : GL (Fin 3) K) * P⁻¹ := by
    intro γ
    rfl
  let Padd : (Fin 3 → K) ≃+ (Fin 3 → K) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin 3 → K)
      (Matrix.GeneralLinearGroup.toLin P)).toAddEquiv
  have hPadd : ∀ v : Fin 3 → K, Padd v = (P : Matrix (Fin 3) (Fin 3) K) *ᵥ v := by
    intro v
    change (LinearMap.GeneralLinearGroup.generalLinearEquiv K ((Fin 3 → K))
        (Matrix.GeneralLinearGroup.toLin P) : (Fin 3 → K) →ₗ[K] (Fin 3 → K)) v =
      (P : Matrix (Fin 3) (Fin 3) K) *ᵥ v
    rw [LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap,
      Matrix.GeneralLinearGroup.toLin_apply, Matrix.mulVecLin_apply]
  let Φ₁ : V ≃* Multiplicative (Fin 3 → K) :=
    Φ₀.trans (AddEquiv.toMultiplicative Padd)
  have hΦ₁_apply : ∀ v : V,
      Φ₁ v = Multiplicative.ofAdd ((P : Matrix (Fin 3) (Fin 3) K) *ᵥ (Φ₀ v).toAdd) := by
    intro v
    rfl
  have hΦ₁_action : ∀ (γ : ↥(StatedSU 3 (2 ^ k) K)) (v : V),
      Φ₁ (((π γ : ↥H) : MulAut V) v) =
        Multiplicative.ofAdd
          ((((eΨ γ : ↥(su3Anti K k)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
            ((P : Matrix (Fin 3) (Fin 3) K) *ᵥ (Φ₀ v).toAdd)) := by
    intro γ v
    rw [hΦ₁_apply, hΦ₀ γ v, hΨ_apply γ, natAct]
    congr 1
    have hxP : ((eΨ γ : ↥(su3Anti K k)) : GL (Fin 3) K) * P = P * γ := by
      rw [hΨ_apply γ]
      group
    calc (P : Matrix (Fin 3) (Fin 3) K) *ᵥ
          (((γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ (Φ₀ v).toAdd)
        = (((P * γ : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) *ᵥ (Φ₀ v).toAdd := by
          conv_lhs => rw [Matrix.mulVec_mulVec, ← Units.val_mul]
      _ = (((((eΨ γ : ↥(su3Anti K k)) : GL (Fin 3) K)) * P : GL (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K) *ᵥ (Φ₀ v).toAdd := by rw [hxP]
      _ = (((eΨ γ : ↥(su3Anti K k)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
            ((P : Matrix (Fin 3) (Fin 3) K) *ᵥ (Φ₀ v).toAdd) := by
          conv_rhs => rw [Matrix.mulVec_mulVec, ← Units.val_mul]
  let ρ : ↥H →* ↥(su3Anti K k) := eΨ.toMonoidHom.comp eπ.symm.toMonoidHom
  refine ⟨K, hKf, hKfin, inferInstance, hKcard, Φ₁, ρ, ?_, ?_⟩
  · intro y
    obtain ⟨γ, rfl⟩ := eΨ.surjective y
    exact ⟨eπ γ, by simp [ρ]⟩
  · intro x v
    let γ : ↥(StatedSU 3 (2 ^ k) K) := eπ.symm x
    have hπγ : π γ = x := by
      change π (eπ.symm x) = x
      rw [← MulEquiv.ofBijective_apply π ⟨hπinj, hπsurj⟩]
      exact eπ.apply_symm_apply x
    have h1 := hΦ₁_action γ v
    rw [hπγ] at h1
    rw [h1]
    congr 1

theorem str86_caseIIa_two_model
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (hm : IsL2Quot m (oTwoQuot ↥L2))
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hIIa : L2 ⊔ Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G))
    (hZ : Z1 L1 L2 S ≤ Q2 L1 L2 S)
    (hc : IsChiefSeriesFrom (L2 ⊔ S) (str86U L1 L2 S) (str86U L1 L2 S) 2)
    {N : Subgroup G} (hN : IsElemAbelian 2 N)
    (hNZ : N ≤ Z1 L1 L2 S) (hNne : N ≠ ⊥)
    (hNP1 : P1 L1 L2 S ≤ Subgroup.normalizer (N : Set G))
    (hNS : S ⊓ Subgroup.centralizer (N : Set G) = Q1 L1 L2 S)
    (hNat : @BinaryNaturalSU3 ↥N (commGroupOfElemAbelian hN) (autOn (L1 ⊔ S) N) ⊤ ⊥ k) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = (2 ^ k) ^ 2 ∧
      ∃ Φ : Additive ↥N ≃+ (Fin 3 → K),
        (∀ h ∈ L1 ⊔ S, ∃ x ∈ su3Anti K k, ∀ n n' : ↥N, (n' : G) = h * n * h⁻¹ →
          Φ (Additive.ofMul n') = (x : Matrix (Fin 3) (Fin 3) K).mulVec (Φ (Additive.ofMul n))) ∧
        (∀ x ∈ su3Anti K k, ∃ h ∈ L1 ⊔ S, ∀ n n' : ↥N, (n' : G) = h * n * h⁻¹ →
          Φ (Additive.ofMul n') = (x : Matrix (Fin 3) (Fin 3) K).mulVec (Φ (Additive.ofMul n))) ∧
        (∀ s ∈ S, ∃ x ∈ CFSG.Quasithin.H.SU3.ujSub k K, ∀ n n' : ↥N, (n' : G) = s * n * s⁻¹ →
          Φ (Additive.ofMul n') = (x : Matrix (Fin 3) (Fin 3) K).mulVec (Φ (Additive.ofMul n))) ∧
        (∀ x ∈ CFSG.Quasithin.H.SU3.ujSub k K, ∃ s ∈ S, ∀ n n' : ↥N,
          (n' : G) = s * n * s⁻¹ →
          Φ (Additive.ofMul n') =
            (x : Matrix (Fin 3) (Fin 3) K).mulVec (Φ (Additive.ofMul n))) := by
  classical
  letI : CommGroup ↥N := commGroupOfElemAbelian hN
  obtain ⟨K, hKf, hKfin, hKcard, π, hπsurj, Φ₀, hΦ₀⟩ :=
    binaryNaturalSU3_realization (V := ↥N) hNat
  letI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := 2 * k) (by
      rw [← Nat.card_eq_fintype_card, hKcard, ← pow_mul, mul_comm])
  let H : Subgroup G := L1 ⊔ S
  have hSH : S ≤ H := le_sup_right
  have hSP1 : S ≤ P1 L1 L2 S :=
    (le_sup_right : S ≤ bigB L1 L2 S).trans
      (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S)
  have hSN : S ≤ Subgroup.normalizer (N : Set G) := hSP1.trans hNP1
  have hHN : H ≤ Subgroup.normalizer (N : Set G) :=
    sup_le (le_sup_left.trans hNP1) hSN
  have hπinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    have hnat : ∀ w : Multiplicative (Fin 3 → K),
        natAct (StatedSU 3 (2 ^ k) K) γ w = w := by
      intro w
      obtain ⟨v, rfl⟩ := Φ₀.surjective w
      have h1 : ((π γ : ↥(autOn H N)) : MulAut ↥N) v = v := by rw [hγ]; rfl
      rw [← hΦ₀ γ v, h1]
    exact natAct_faithful (StatedSU 3 (2 ^ k) K) γ
      (fun m => by rw [hnat m, mul_inv_cancel])
  let eπ : ↥(StatedSU 3 (2 ^ k) K) ≃* ↥(autOn H N) :=
    MulEquiv.ofBijective π ⟨hπinj, hπsurj⟩
  obtain ⟨P, -, hPmap⟩ := statedSU3_conj_anti (F := K) hk hKcard
  let eΨ₀ : ↥(StatedSU 3 (2 ^ k) K) ≃*
      ↥((StatedSU 3 (2 ^ k) K).map (MulAut.conj P).toMonoidHom) :=
    Subgroup.equivMapOfInjective _ _ (MulAut.conj P).injective
  let eΨ : ↥(StatedSU 3 (2 ^ k) K) ≃* ↥(su3Anti K k) :=
    eΨ₀.trans (MulEquiv.subgroupCongr hPmap)
  have hΨ_apply : ∀ γ : ↥(StatedSU 3 (2 ^ k) K),
      ((eΨ γ : ↥(su3Anti K k)) : GL (Fin 3) K) = P * (γ : GL (Fin 3) K) * P⁻¹ := by
    intro γ
    rfl
  let Padd : (Fin 3 → K) ≃+ (Fin 3 → K) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin 3 → K)
      (Matrix.GeneralLinearGroup.toLin P)).toAddEquiv
  have hPadd : ∀ v : Fin 3 → K, Padd v = (P : Matrix (Fin 3) (Fin 3) K) *ᵥ v := by
    intro v
    change (LinearMap.GeneralLinearGroup.generalLinearEquiv K ((Fin 3 → K))
        (Matrix.GeneralLinearGroup.toLin P) : (Fin 3 → K) →ₗ[K] (Fin 3 → K)) v =
      (P : Matrix (Fin 3) (Fin 3) K) *ᵥ v
    rw [LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap,
      Matrix.GeneralLinearGroup.toLin_apply, Matrix.mulVecLin_apply]
  let Φ₁ : ↥N ≃* Multiplicative (Fin 3 → K) :=
    Φ₀.trans (AddEquiv.toMultiplicative Padd)
  have hΦ₁_apply : ∀ n : ↥N,
      Φ₁ n = Multiplicative.ofAdd ((P : Matrix (Fin 3) (Fin 3) K) *ᵥ (Φ₀ n).toAdd) := by
    intro n
    rfl
  have hΦ₁_action : ∀ (γ : ↥(StatedSU 3 (2 ^ k) K)) (n : ↥N),
      Φ₁ (((π γ : ↥(autOn H N)) : MulAut ↥N) n) =
        Multiplicative.ofAdd
          ((((eΨ γ : ↥(su3Anti K k)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
            ((P : Matrix (Fin 3) (Fin 3) K) *ᵥ (Φ₀ n).toAdd)) := by
    intro γ n
    rw [hΦ₁_apply, hΦ₀ γ n, hΨ_apply γ, natAct]
    congr 1
    have hxP : ((eΨ γ : ↥(su3Anti K k)) : GL (Fin 3) K) * P = P * γ := by
      rw [hΨ_apply γ]
      group
    calc (P : Matrix (Fin 3) (Fin 3) K) *ᵥ
          (((γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ (Φ₀ n).toAdd)
        = (((P * γ : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) *ᵥ (Φ₀ n).toAdd := by
          conv_lhs => rw [Matrix.mulVec_mulVec, ← Units.val_mul]
      _ = (((((eΨ γ : ↥(su3Anti K k)) : GL (Fin 3) K)) * P : GL (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K) *ᵥ (Φ₀ n).toAdd := by rw [hxP]
      _ = (((eΨ γ : ↥(su3Anti K k)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
            ((P : Matrix (Fin 3) (Fin 3) K) *ᵥ (Φ₀ n).toAdd) := by
          conv_rhs => rw [Matrix.mulVec_mulVec, ← Units.val_mul]
  let R : Subgroup (MulAut ↥N) := autOn S N
  have hRS : R ≤ autOn H N := AutOn.autOn_mono hSH
  let ιR : ↥R →* ↥(autOn H N) := Subgroup.inclusion hRS
  let f : ↥R →* ↥(su3Anti K k) :=
    eΨ.toMonoidHom.comp (eπ.symm.toMonoidHom.comp ιR)
  have hinjf : Function.Injective f := by
    intro x y hxy
    have h1 : eπ.symm (ιR x) = eπ.symm (ιR y) := eΨ.injective hxy
    have h2 : ιR x = ιR y := eπ.symm.injective h1
    exact (Subgroup.inclusion_injective hRS) h2
  let Tsub : Subgroup ↥(su3Anti K k) := f.range
  let T : Subgroup (GL (Fin 3) K) := Tsub.map (su3Anti K k).subtype
  have hTle : T ≤ su3Anti K k := Subgroup.map_subtype_le _
  have hQ1S : Q1 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hcardR : Nat.card R = (2 ^ k) ^ 3 := by
    have hcard := AutOn.card_autOn_mul (K := S) (V := N) hSN
    rw [hNS] at hcard
    have hrel := str86_relIndex_q1_s (F := F) hF hSB hk hFc hU3
    have hrelmul := Subgroup.relIndex_mul_card (H := Q1 L1 L2 S) (K := S)
    rw [inf_eq_left.mpr hQ1S] at hrelmul
    have hmul : Nat.card R * Nat.card ↥(Q1 L1 L2 S) =
        (2 ^ k) ^ 3 * Nat.card ↥(Q1 L1 L2 S) := by
      rw [show Nat.card R = Nat.card (autOn S N) from rfl, hcard]
      rw [← hrelmul, hrel]
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hmul
  have hcardT : Nat.card T = (2 ^ k) ^ 3 := by
    have h1 : Nat.card T = Nat.card R := by
      dsimp only [T, Tsub]
      rw [Subgroup.card_map_of_injective (su3Anti K k).subtype_injective]
      exact Nat.card_congr (MonoidHom.ofInjective hinjf).symm.toEquiv
    rw [h1, hcardR]
  have hfac : (Nat.card (su3Anti K k)).factorization 2 = 3 * k := by
    have hcard : Nat.card (su3Anti K k) = Nat.card (StatedSU 3 (2 ^ k) K) := by
      rw [su3Anti]
      exact Subgroup.card_map_of_injective (MulAut.conj _).injective
    have h2 : 2 ^ (Nat.card (su3Anti K k)).factorization 2 = (2 ^ k) ^ 3 := by
      rw [hcard]
      exact CFSG.Quasithin.H.SU3.card_statedSU_two (K := K) (by omega) hKcard
    rw [show (2 ^ k) ^ 3 = 2 ^ (3 * k) by rw [← pow_mul, mul_comm]] at h2
    exact Nat.pow_right_injective (by norm_num) h2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTsyl : IsSylowIn 2 T (su3Anti K k) := by
    refine isSylowIn_of_card_eq hTle ?_
    rw [hcardT, hfac, ← pow_mul, mul_comm]
  have hujSyl : IsSylowIn 2 (CFSG.Quasithin.H.SU3.ujSub k K) (su3Anti K k) :=
    isSylowIn_su3Anti_ujSub (by omega) hKcard
  obtain ⟨g, hg, hgiff⟩ := CFSG.Quasithin.Ch1Sec3.exists_conj_of_isSylowIn (p := 2) hTsyl hujSyl
  have hTconj : ∀ y : GL (Fin 3) K,
      y ∈ T ↔ g * y * g⁻¹ ∈ CFSG.Quasithin.H.SU3.ujSub k K := by
    intro y
    have h := (hgiff (g * y * g⁻¹)).symm
    simpa [mul_assoc] using h
  have hTmap : T.map (MulAut.conj g).toMonoidHom =
      CFSG.Quasithin.H.SU3.ujSub k K := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [MulAut.conj_apply] using (hTconj y).mp hy
    · intro hx
      refine ⟨g⁻¹ * x * g, ?_, ?_⟩
      · exact (hTconj (g⁻¹ * x * g)).mpr (by simpa [mul_assoc] using hx)
      · simp [MulAut.conj_apply, mul_assoc]
  let gAdd : (Fin 3 → K) ≃+ (Fin 3 → K) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin 3 → K)
      (Matrix.GeneralLinearGroup.toLin g)).toAddEquiv
  have hgAdd : ∀ v : Fin 3 → K, gAdd v = (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v := by
    intro v
    change (LinearMap.GeneralLinearGroup.generalLinearEquiv K ((Fin 3 → K))
        (Matrix.GeneralLinearGroup.toLin g) : (Fin 3 → K) →ₗ[K] (Fin 3 → K)) v =
      (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v
    rw [LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap,
      Matrix.GeneralLinearGroup.toLin_apply, Matrix.mulVecLin_apply]
  let Φ₁a : Additive ↥N ≃+ (Fin 3 → K) :=
    (MulEquiv.toAdditive Φ₁).trans (AddEquiv.additiveMultiplicative (Fin 3 → K))
  have hΦ₁a : ∀ n : ↥N,
      Φ₁a (Additive.ofMul n) =
        (P : Matrix (Fin 3) (Fin 3) K) *ᵥ (Φ₀ n).toAdd := by
    intro n
    rfl
  let Φ : Additive ↥N ≃+ (Fin 3 → K) := Φ₁a.trans gAdd
  have hΦ_apply : ∀ n : ↥N,
      Φ (Additive.ofMul n) =
        (g : Matrix (Fin 3) (Fin 3) K) *ᵥ
          ((P : Matrix (Fin 3) (Fin 3) K) *ᵥ (Φ₀ n).toAdd) := by
    intro n
    rfl
  have hΦ_eq : ∀ n : ↥N,
      Φ (Additive.ofMul n) = ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        (Φ₁ n).toAdd := by
    intro n
    rw [hΦ_apply, hΦ₁_apply]
    rfl
  have hΦ_action : ∀ (γ : ↥(StatedSU 3 (2 ^ k) K)) (n : ↥N),
      Φ (Additive.ofMul (((π γ : ↥(autOn H N)) : MulAut ↥N) n)) =
        ((g * ((eΨ γ : ↥(su3Anti K k)) : GL (Fin 3) K) * g⁻¹ :
            GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ Φ (Additive.ofMul n) := by
    intro γ n
    have h1 : (Φ₁ (((π γ : ↥(autOn H N)) : MulAut ↥N) n)).toAdd =
        (((eΨ γ : ↥(su3Anti K k)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
          (Φ₁ n).toAdd := by
      rw [hΦ₁_action γ n]
      rfl
    rw [hΦ_eq, h1, hΦ_eq]
    have hxP : g * ((eΨ γ : ↥(su3Anti K k)) : GL (Fin 3) K) * g⁻¹ * g =
        g * ((eΨ γ : ↥(su3Anti K k)) : GL (Fin 3) K) := by group
    conv_lhs => rw [Matrix.mulVec_mulVec, ← Units.val_mul]
    conv_rhs => rw [Matrix.mulVec_mulVec, ← Units.val_mul]
    rw [hxP]
  refine ⟨K, hKf, hKfin, inferInstance, hKcard, Φ, ?_, ?_, ?_, ?_⟩
  · intro h hh
    let hH : ↥H := ⟨h, hh⟩
    let a : ↥(autOn H N) :=
      ⟨A4.actionOn N H hHN hH, (A4.mem_autOn_iff hHN).mpr ⟨hH, rfl⟩⟩
    let γ : ↥(StatedSU 3 (2 ^ k) K) := eπ.symm a
    let x : ↥(su3Anti K k) := eΨ γ
    have hxmem : g * (x : GL (Fin 3) K) * g⁻¹ ∈ su3Anti K k :=
      (su3Anti K k).mul_mem ((su3Anti K k).mul_mem hg x.2) ((su3Anti K k).inv_mem hg)
    refine ⟨g * (x : GL (Fin 3) K) * g⁻¹, hxmem, ?_⟩
    intro n n' hn'
    have hπγ : π γ = a := by
      change π (eπ.symm a) = a
      rw [← MulEquiv.ofBijective_apply π ⟨hπinj, hπsurj⟩]
      exact eπ.apply_symm_apply a
    have hact : ((π γ : ↥(autOn H N)) : MulAut ↥N) n = n' := by
      apply Subtype.ext
      rw [hπγ]
      change ((A4.actionOn N H hHN hH) n : G) = (n' : G)
      rw [A4.actionOn_apply_coe]
      exact hn'.symm
    rw [← hact, hΦ_action γ n]
  · intro x hx
    let y : GL (Fin 3) K := g⁻¹ * x * g
    have hymem : y ∈ su3Anti K k :=
      (su3Anti K k).mul_mem ((su3Anti K k).mul_mem ((su3Anti K k).inv_mem hg) hx) hg
    let γ : ↥(StatedSU 3 (2 ^ k) K) := eΨ.symm ⟨y, hymem⟩
    have hπγ : ((π γ : ↥(autOn H N)) : MulAut ↥N) ∈ autOn H N := (π γ).2
    let hH : ↥H := Classical.choose ((A4.mem_autOn_iff hHN).mp hπγ)
    have hact : A4.actionOn N H hHN hH = ((π γ : ↥(autOn H N)) : MulAut ↥N) :=
      Classical.choose_spec ((A4.mem_autOn_iff hHN).mp hπγ)
    refine ⟨(hH : G), hH.2, ?_⟩
    intro n n' hn'
    have hγy : ((eΨ γ : ↥(su3Anti K k)) : GL (Fin 3) K) = y := by
      simp [γ]
    have hnact : ((π γ : ↥(autOn H N)) : MulAut ↥N) n = n' := by
      apply Subtype.ext
      rw [← hact]
      change ((A4.actionOn N H hHN hH) n : G) = (n' : G)
      rw [A4.actionOn_apply_coe]
      exact hn'.symm
    rw [← hnact, hΦ_action γ n, hγy]
    have hyx : g * y * g⁻¹ = x := by
      dsimp [y]
      group
    rw [hyx]
  · intro s hs
    let sS : ↥S := ⟨s, hs⟩
    let aS : ↥(autOn S N) :=
      ⟨A4.actionOn N S hSN sS, (A4.mem_autOn_iff hSN).mpr ⟨sS, rfl⟩⟩
    let a : ↥(autOn H N) := ιR aS
    let γ : ↥(StatedSU 3 (2 ^ k) K) := eπ.symm a
    let x : ↥(su3Anti K k) := eΨ γ
    have hxTsub : x ∈ Tsub := ⟨aS, rfl⟩
    have hxT : (x : GL (Fin 3) K) ∈ T := ⟨x, hxTsub, rfl⟩
    have hxuj : g * (x : GL (Fin 3) K) * g⁻¹ ∈ CFSG.Quasithin.H.SU3.ujSub k K :=
      (hTconj (x : GL (Fin 3) K)).mp hxT
    refine ⟨g * (x : GL (Fin 3) K) * g⁻¹, hxuj, ?_⟩
    intro n n' hn'
    have hπγ : π γ = a := by
      change π (eπ.symm a) = a
      rw [← MulEquiv.ofBijective_apply π ⟨hπinj, hπsurj⟩]
      exact eπ.apply_symm_apply a
    have hact : ((π γ : ↥(autOn H N)) : MulAut ↥N) n = n' := by
      apply Subtype.ext
      rw [hπγ]
      change ((A4.actionOn N S hSN sS) n : G) = (n' : G)
      rw [A4.actionOn_apply_coe]
      exact hn'.symm
    rw [← hact, hΦ_action γ n]
  · intro x hx
    have hgxT : g⁻¹ * x * g ∈ T :=
      (hTconj (g⁻¹ * x * g)).mpr (by simpa [mul_assoc] using hx)
    obtain ⟨z, hzTsub, hzval⟩ := Subgroup.mem_map.mp hgxT
    obtain ⟨aS, haS⟩ := MonoidHom.mem_range.mp hzTsub
    let sS : ↥S := Classical.choose ((A4.mem_autOn_iff hSN).mp aS.2)
    have hsact : A4.actionOn N S hSN sS = (aS : MulAut ↥N) :=
      Classical.choose_spec ((A4.mem_autOn_iff hSN).mp aS.2)
    refine ⟨(sS : G), sS.2, ?_⟩
    let a : ↥(autOn H N) := ιR aS
    let γ : ↥(StatedSU 3 (2 ^ k) K) := eπ.symm a
    have hπγ : π γ = a := by
      change π (eπ.symm a) = a
      rw [← MulEquiv.ofBijective_apply π ⟨hπinj, hπsurj⟩]
      exact eπ.apply_symm_apply a
    have hπγ' : ((π γ : ↥(autOn H N)) : MulAut ↥N) = A4.actionOn N S hSN sS := by
      rw [hπγ]
      change ((ιR aS : ↥(autOn H N)) : MulAut ↥N) = (A4.actionOn N S hSN) sS
      rw [hsact]
      rfl
    have hγx : ((eΨ γ : ↥(su3Anti K k)) : GL (Fin 3) K) = g⁻¹ * x * g := by
      have hfval : (eΨ γ : ↥(su3Anti K k)) = f aS := rfl
      rw [hfval, haS]
      exact hzval
    intro n n' hn'
    have hnact : ((π γ : ↥(autOn H N)) : MulAut ↥N) n = n' := by
      apply Subtype.ext
      rw [hπγ']
      change ((A4.actionOn N S hSN sS) n : G) = (n' : G)
      rw [A4.actionOn_apply_coe]
      exact hn'.symm
    rw [← hnact, hΦ_action γ n, hγx]
    have hconj : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [hconj]

end

end CFSG.Quasithin.Stroth

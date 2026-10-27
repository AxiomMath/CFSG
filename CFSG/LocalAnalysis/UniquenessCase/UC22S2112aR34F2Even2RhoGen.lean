module

public import CFSG.GH74.GLS.IVK.Lifted.SL2Aut
import CFSG.Walter.Cited.PSL2Small
import CFSG.GH74.GLS.LU.Local.SL2Aut2
import CFSG.HardMathSupport.Solomon.Coordinator.L3BAutSL
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Residual

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open CFSG.GorensteinWalter
open CFSG.Semidihedral.MatrixCoverData (slConjugation)
open scoped MatrixGroups

variable {X : Type*} [Group X] (K : Subgroup X) {F : Type} [Field F] [Finite F]

noncomputable def uc22s2112r34_gammaAct (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (eK : K ≃* SL(2, F)) : normalizer (K : Set X) →* PGammaL2 F :=
  (CFSG.GH74.GLS.IVK.Lifted.gammaOf hodd h3).comp
    ((MulAut.congr eK).toMonoidHom.comp K.normalizerMonoidHom)

noncomputable def uc22s2112r34_rhoGen (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (eK : K ≃* SL(2, F)) (hσ : ∀ g, (uc22s2112r34_gammaAct K hodd h3 eK g).right = 1) :
    normalizer (K : Set X) →* PGL(Fin 2, F) where
  toFun g := (uc22s2112r34_gammaAct K hodd h3 eK g).left
  map_one' := by
    show (uc22s2112r34_gammaAct K hodd h3 eK 1).left = 1
    rw [map_one, SemidirectProduct.one_left]
  map_mul' g h := by
    show (uc22s2112r34_gammaAct K hodd h3 eK (g * h)).left =
      (uc22s2112r34_gammaAct K hodd h3 eK g).left *
        (uc22s2112r34_gammaAct K hodd h3 eK h).left
    rw [map_mul, SemidirectProduct.mul_left, hσ g, map_one, MulAut.one_apply]

variable {K}

omit [Finite F] in
private theorem uc22s2112r34_rhoGen_congr_conj {Q : Type*} [Group Q]
    (e : Q ≃* SL(2, F)) (c : Q) :
    MulAut.congr e (MulAut.conj c) = MulAut.conj (e c) := by
  refine MulEquiv.ext fun s => ?_
  obtain ⟨k, rfl⟩ := e.surjective s
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem uc22s2112r34_rhoGen_eq_one_iff (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (eK : K ≃* SL(2, F)) (hσ : ∀ g, (uc22s2112r34_gammaAct K hodd h3 eK g).right = 1)
    (g : normalizer (K : Set X)) :
    uc22s2112r34_rhoGen K hodd h3 eK hσ g = 1 ↔ ∀ k ∈ K, (g : X) * k * (g : X)⁻¹ = k := by
  have hkey : uc22s2112r34_gammaAct K hodd h3 eK g = 1 ↔
      K.normalizerMonoidHom g = 1 := by
    constructor
    · intro hΓ
      have h2 : (CFSG.GH74.GLS.IVK.Lifted.gammaOf hodd h3)
          ((MulAut.congr eK) (K.normalizerMonoidHom g)) =
          (CFSG.GH74.GLS.IVK.Lifted.gammaOf hodd h3) ((MulAut.congr eK) 1) := by
        rw [map_one, map_one]
        exact hΓ
      have h1 : (MulAut.congr eK) (K.normalizerMonoidHom g) = (MulAut.congr eK) 1 :=
        CFSG.GH74.GLS.IVK.Lifted.gammaOf_injective hodd h3 h2
      exact (MulAut.congr eK).injective h1
    · intro hφ
      show (CFSG.GH74.GLS.IVK.Lifted.gammaOf hodd h3)
        ((MulAut.congr eK) (K.normalizerMonoidHom g)) = 1
      rw [hφ, map_one, map_one]
  constructor
  · intro h k hk
    have hΓ : uc22s2112r34_gammaAct K hodd h3 eK g = 1 :=
      SemidirectProduct.ext h (hσ g)
    have hφ := hkey.mp hΓ
    have hk' := congrArg (fun f : MulAut K => f ⟨k, hk⟩) hφ
    rw [MulAut.one_apply] at hk'
    have hval := congrArg Subtype.val hk'
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at hval
    simpa using hval
  · intro h
    have hφ : K.normalizerMonoidHom g = 1 := by
      refine MulEquiv.ext fun k => ?_
      apply Subtype.ext
      rw [MulAut.one_apply, Subgroup.normalizerMonoidHom_apply_apply_coe]
      exact h k k.2
    show (uc22s2112r34_gammaAct K hodd h3 eK g).left = 1
    rw [hkey.mpr hφ, SemidirectProduct.one_left]

theorem uc22s2112r34_rhoGen_not_isCyclic (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (eK : K ≃* SL(2, F)) (hσ : ∀ g, (uc22s2112r34_gammaAct K hodd h3 eK g).right = 1)
    {Q : Subgroup X} (hQ : CFSG.ABGLocalTools.IsSylowOf 2 Q K) :
    ¬ IsCyclic ((Q.subgroupOf (normalizer (K : Set X))).map
      (uc22s2112r34_rhoGen K hodd h3 eK hσ)) := by
  classical
  let S := SL(2, F)
  let P := PSL2 F
  let Z := Subgroup.center S
  let π : S →* P := QuotientGroup.mk' Z
  let N : Subgroup X := normalizer (K : Set X)
  let QN : Subgroup N := Q.subgroupOf N
  let fQ : QN →* K :=
    { toFun := fun q => ⟨(q : N).1, hQ.le q.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl }
  let g : QN →* P := π.comp (eK.toMonoidHom.comp fQ)
  have : Finite K := Finite.of_injective eK.toMonoidHom eK.injective
  obtain ⟨QK, hQK⟩ := hQ.exists_sylow_eq_subgroupOf
  let QS : Sylow 2 S := Sylow.mapSurjective (f := eK.toMonoidHom) eK.surjective QK
  let Qbar : Sylow 2 P := Sylow.mapSurjective (f := π) (QuotientGroup.mk'_surjective Z) QS
  have hQS_coe : (QS : Subgroup S) = (QK : Subgroup K).map eK.toMonoidHom :=
    Sylow.coe_mapSurjective (f := eK.toMonoidHom) eK.surjective QK
  have hQbar_coe : (Qbar : Subgroup P) = (QS : Subgroup S).map π :=
    Sylow.coe_mapSurjective (f := π) (QuotientGroup.mk'_surjective Z) QS
  have hoddF : IsOddPrimePower (Nat.card F) :=
    CFSG.ABGLocalTools.isOddPrimePower_card_of_odd hodd
  have hQbar_nc : ¬ IsCyclic (Qbar : Subgroup P) := by
    obtain ⟨m, hm, ⟨em⟩⟩ := psl2_odd_hasDihedralSylowTwo_model F hoddF Qbar
    refine fun hc => DihedralGroup.not_isCyclic (n := 2 ^ m) ?_
      (isCyclic_of_surjective em.toMonoidHom em.surjective)
    have : 1 < 2 ^ m := Nat.one_lt_pow (by omega) (by norm_num)
    omega
  have hQNmapfQ : fQ.range = (QK : Subgroup K) := by
    apply le_antisymm
    · rintro x ⟨q, rfl⟩
      rw [hQK]
      exact q.2
    · intro x hx
      rw [hQK] at hx
      exact ⟨⟨⟨x.1, Subgroup.le_normalizer x.2⟩, hx⟩, Subtype.ext rfl⟩
  have hQNmapg : g.range = (Qbar : Subgroup P) := by
    change (π.comp (eK.toMonoidHom.comp fQ)).range = (Qbar : Subgroup P)
    rw [MonoidHom.range_comp, MonoidHom.range_comp, hQNmapfQ, hQbar_coe, hQS_coe]
  have hρ : ∀ q : QN, uc22s2112r34_rhoGen K hodd h3 eK hσ q.1 =
      Matrix.ProjectiveSpecialLinearGroup.toPGL (g q) := by
    intro q
    have hconj : K.normalizerMonoidHom q.1 = MulAut.conj (fQ q) := by
      refine MulEquiv.ext fun k => ?_
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply]
      rfl
    show (CFSG.GH74.GLS.IVK.Lifted.gammaOf hodd h3
      ((MulAut.congr eK) (K.normalizerMonoidHom q.1))).left = _
    have hcc := uc22s2112r34_rhoGen_congr_conj eK (fQ q)
    rw [hconj, hcc, CFSG.GH74.GLS.IVK.Lifted.gammaOf_conj]
    rfl
  have hmapρ : QN.map (uc22s2112r34_rhoGen K hodd h3 eK hσ) =
      g.range.map (Matrix.ProjectiveSpecialLinearGroup.toPGL) := by
    apply le_antisymm
    · rintro x ⟨q, hq, rfl⟩
      exact ⟨g ⟨q, hq⟩, ⟨⟨q, hq⟩, rfl⟩, (hρ ⟨q, hq⟩).symm⟩
    · rintro x ⟨y, hy, rfl⟩
      obtain ⟨q, rfl⟩ := hy
      exact ⟨q.1, q.2, hρ q⟩
  change ¬ IsCyclic (QN.map (uc22s2112r34_rhoGen K hodd h3 eK hσ))
  intro hcyc
  rw [hmapρ] at hcyc
  have hgcyc : IsCyclic g.range :=
    (MulEquiv.isCyclic (Subgroup.equivMapOfInjective g.range
      Matrix.ProjectiveSpecialLinearGroup.toPGL
      Matrix.ProjectiveSpecialLinearGroup.toPGL_injective)).mpr hcyc
  exact hQbar_nc (hQNmapg ▸ hgcyc)

theorem uc22s2112r34_gammaAct_right_eq_one {p n : ℕ} (hp : p.Prime) (hn : Odd n)
    (hFn : Nat.card F = p ^ n) (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (eK : K ≃* SL(2, F))
    (hsq : ∀ g : normalizer (K : Set X), ∃ c ∈ K, ∀ k ∈ K,
      (g : X) * (g : X) * k * ((g : X) * (g : X))⁻¹ = c * k * c⁻¹)
    (g : normalizer (K : Set X)) : (uc22s2112r34_gammaAct K hodd h3 eK g).right = 1 := by
  let σ : F ≃+* F := (uc22s2112r34_gammaAct K hodd h3 eK g).right
  have hright : (uc22s2112r34_gammaAct K hodd h3 eK (g * g)).right = 1 := by
    obtain ⟨c, hc, hcK⟩ := hsq g
    have hconj : K.normalizerMonoidHom (g * g) = MulAut.conj (⟨c, hc⟩ : K) := by
      refine MulEquiv.ext fun k => ?_
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply]
      simpa [Subgroup.coe_mul] using hcK k k.2
    change (CFSG.GH74.GLS.IVK.Lifted.gammaOf hodd h3
      ((MulAut.congr eK) (K.normalizerMonoidHom (g * g)))).right = 1
    rw [hconj, uc22s2112r34_rhoGen_congr_conj eK (⟨c, hc⟩ : K),
      CFSG.GH74.GLS.IVK.Lifted.gammaOf_conj_right]
  have hmul : (uc22s2112r34_gammaAct K hodd h3 eK (g * g)).right = σ * σ := by
    rw [map_mul, SemidirectProduct.mul_right]
  have hσ2 : σ * σ = 1 := by rw [← hmul]; exact hright
  have hpow : σ ^ n = 1 :=
    CFSG.HardMathSupport.Solomon.Coordinator.ringEquiv_pow_eq_one hp hFn σ
  obtain ⟨m, hm⟩ := hn
  have h2 : σ ^ (2 * m + 1) = (σ * σ) ^ m * σ := by
    rw [pow_succ, pow_mul, sq]
  rw [hm] at hpow
  rw [h2, hσ2] at hpow
  simpa using hpow

theorem uc22s2112r34_sq_inner_of_partner {K' : Subgroup X} (hKK' : centralizer (K : Set X) ≤ K')
    (hK'K : centralizer (K' : Set X) ≤ K) (hcomm : ⁅K, K'⁆ = ⊥) {F' : Type} [Field F'] [Finite F']
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hF' : Nat.card F' = p) (eK' : K' ≃* SL(2, F'))
    (g : normalizer (K : Set X)) :
    ∃ c ∈ K, ∀ k ∈ K, (g : X) * (g : X) * k * ((g : X) * (g : X))⁻¹ = c * k * c⁻¹ := by
  classical
  have hpOdd : Odd p := hp.odd_of_ne_two (by omega)
  have hodd' : Odd (Nat.card F') := by rw [hF']; exact hpOdd
  have h3' : 3 < Nat.card F' := by rw [hF']; omega
  have : Fact p.Prime := ⟨hp⟩
  have : Subsingleton (F' ≃+* F') :=
    CFSG.Walter.Suzuki.subsingleton_ringEquiv_of_card_prime F' hF'
  have hK'cent : K' ≤ Subgroup.centralizer (K : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (by rw [Subgroup.commutator_comm]; exact hcomm)
  have hcent : Subgroup.centralizer (K : Set X) = K' := le_antisymm hKK' hK'cent
  have hgNorm : (g : X) ∈ Subgroup.normalizer (K' : Set X) := by
    have h := CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer K g.2
    rwa [hcent] at h
  let gN : normalizer (K' : Set X) := ⟨(g : X), hgNorm⟩
  let α' : MulAut (SL(2, F')) := (MulAut.congr eK') (K'.normalizerMonoidHom gN)
  have hright : (CFSG.GH74.GLS.IVK.Lifted.gammaOf hodd' h3' α').right = 1 :=
    Subsingleton.elim _ _
  obtain ⟨G, hG⟩ :=
    CFSG.GH74.GLS.IVK.Lifted.eq_slConjugation_of_right_eq_one hodd' h3' α' hright
  have hsqdet : IsSquare
      (Matrix.det (((G * G : GL (Fin 2) F') : Matrix (Fin 2) (Fin 2) F'))) := by
    rw [Units.val_mul, Matrix.det_mul]
    exact ⟨_, rfl⟩
  obtain ⟨y, hy⟩ :=
    CFSG.GH74.GLS.LU.Local.exists_conj_eq_slConjugation_of_isSquare_det (G * G) hsqdet
  have hα2 : α' * α' = MulAut.conj y := by
    calc α' * α' = slConjugation F' G * slConjugation F' G := by rw [hG]
      _ = slConjugation F' (G * G) := (map_mul _ G G).symm
      _ = MulAut.conj y := hy
  have hinnerK' : K'.normalizerMonoidHom (gN * gN) = MulAut.conj (eK'.symm y) := by
    apply (MulAut.congr eK').injective
    rw [uc22s2112r34_rhoGen_congr_conj eK' (eK'.symm y), MulEquiv.apply_symm_apply,
      map_mul, map_mul]
    exact hα2
  have hinner_apply : ∀ x : K', ((g : X) * (g : X)) * (x : X) * ((g : X) * (g : X))⁻¹ =
      ((eK'.symm y : K') : X) * (x : X) * ((eK'.symm y : K') : X)⁻¹ := by
    intro x
    have h1 := congrArg (fun f : MulAut K' => ((f x : K') : X)) hinnerK'
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply] at h1
    simpa [gN, Subgroup.coe_mul] using h1
  let k' : K' := eK'.symm y
  let c : X := (k' : X)⁻¹ * ((g : X) * (g : X))
  have hcK' : c ∈ Subgroup.centralizer (K' : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' := hinner_apply ⟨x, hx⟩
    simp only [c]
    calc x * ((k' : X)⁻¹ * ((g : X) * (g : X)))
        = (k' : X)⁻¹ * ((k' : X) * x * (k' : X)⁻¹) * ((g : X) * (g : X)) := by group
      _ = (k' : X)⁻¹ * (((g : X) * (g : X)) * x * ((g : X) * (g : X))⁻¹)
            * ((g : X) * (g : X)) := by rw [← hx']
      _ = (k' : X)⁻¹ * ((g : X) * (g : X)) * x := by group
  have hcK : c ∈ K := hK'K hcK'
  refine ⟨c, hcK, fun k hk => ?_⟩
  have hk'comm : ∀ y ∈ K, (k' : X) * y = y * (k' : X) := by
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hK'cent k'.2) y hy).symm
  have hckc : c * k * c⁻¹ ∈ K := K.mul_mem (K.mul_mem hcK hk) (K.inv_mem hcK)
  have hkey : (g : X) * (g : X) = (k' : X) * c := by
    simp only [c]
    group
  calc (g : X) * (g : X) * k * ((g : X) * (g : X))⁻¹
      = (k' : X) * (c * k * c⁻¹) * (k' : X)⁻¹ := by rw [hkey]; group
    _ = c * k * c⁻¹ := by rw [hk'comm _ hckc]; group

theorem uc22s2112r34_exists_rho_of_partner {p n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : Odd n)
    (hFn : Nat.card F = p ^ n) {K' : Subgroup X} (hKK' : centralizer (K : Set X) ≤ K')
    (hK'K : centralizer (K' : Set X) ≤ K) (hcomm : ⁅K, K'⁆ = ⊥) {F' : Type} [Field F'] [Finite F']
    (hF' : Nat.card F' = p) (eK : K ≃* SL(2, F)) (eK' : K' ≃* SL(2, F')) :
    ∃ ρ : normalizer (K : Set X) →* PGL(Fin 2, F),
      (∀ g, ρ g = 1 ↔ ∀ k ∈ K, (g : X) * k * (g : X)⁻¹ = k) ∧
      ∀ {Q : Subgroup X}, CFSG.ABGLocalTools.IsSylowOf 2 Q K →
        ¬ IsCyclic ((Q.subgroupOf (normalizer (K : Set X))).map ρ) := by
  have hpOdd : Odd p := hp.odd_of_ne_two (by omega)
  have hodd : Odd (Nat.card F) := by rw [hFn]; exact hpOdd.pow
  have hn1 : 1 ≤ n := by
    obtain ⟨m, hm⟩ := hn
    omega
  have h3 : 3 < Nat.card F := by
    rw [hFn]
    calc 3 < p := by omega
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ n := Nat.pow_le_pow_right (by omega) hn1
  have hsq : ∀ g : normalizer (K : Set X), ∃ c ∈ K, ∀ k ∈ K,
      (g : X) * (g : X) * k * ((g : X) * (g : X))⁻¹ = c * k * c⁻¹ :=
    fun g => uc22s2112r34_sq_inner_of_partner hKK' hK'K hcomm hp hp5 hF' eK' g
  have hσ : ∀ g, (uc22s2112r34_gammaAct K hodd h3 eK g).right = 1 :=
    uc22s2112r34_gammaAct_right_eq_one hp hn hFn hodd h3 eK hsq
  refine ⟨uc22s2112r34_rhoGen K hodd h3 eK hσ, ?_, ?_⟩
  · intro g
    exact uc22s2112r34_rhoGen_eq_one_iff hodd h3 eK hσ g
  · intro Q hQ
    exact uc22s2112r34_rhoGen_not_isCyclic hodd h3 eK hσ hQ

end CFSG.LocalAnalysis.UniquenessCase.UC22

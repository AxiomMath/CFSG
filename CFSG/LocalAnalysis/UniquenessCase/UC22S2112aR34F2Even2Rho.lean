module

public import CFSG.Walter.Cited.PSL2Small
public import TauCeti.GroupTheory.QuotientGroup.MulAut
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.Adapters.SpecialLinearPerfect

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open CFSG.GorensteinWalter
open scoped MatrixGroups

variable {X : Type*} [Group X] (K : Subgroup X) {F : Type} [Field F] [Finite F] {p : ℕ}
  [Fact p.Prime]

private noncomputable def uc22s2112r34_rho_mulAutEquiv (hp5 : 5 ≤ p) (hF : Nat.card F = p) :
    MulAut (PSL2 F) ≃* PGL2 F :=
  have hodd : IsOddPrimePower (Nat.card F) :=
    ⟨p, 1, (Fact.out : p.Prime), (Fact.out : p.Prime).odd_of_ne_two (by omega), le_rfl,
      by rw [hF, pow_one]⟩
  have h3 : 3 < Nat.card F := by omega
  letI : Subsingleton (F ≃+* F) :=
    CFSG.Walter.Suzuki.subsingleton_ringEquiv_of_card_prime F hF
  (MulEquiv.ofBijective (pGammaL2ToMulAutPSL2 F hodd h3)
      ⟨pGammaL2ToMulAutPSL2_injective F hodd h3,
        pGammaL2ToMulAutPSL2_surjective F (p := p) (f := 1) (by rw [hF, pow_one]) hodd
          h3⟩).symm.trans
    (MulEquiv.ofBijective (SemidirectProduct.inl : PGL2 F →* PGammaL2 F)
      ⟨SemidirectProduct.inl_injective, fun x =>
        ⟨x.left, SemidirectProduct.ext rfl (Subsingleton.elim _ _)⟩⟩).symm

noncomputable def uc22s2112r34_rho (hp5 : 5 ≤ p) (hF : Nat.card F = p) (eK : K ≃* SL(2, F)) :
    normalizer (K : Set X) →* PGL(Fin 2, F) :=
  (uc22s2112r34_rho_mulAutEquiv (F := F) hp5 hF).toMonoidHom.comp <|
    (MulAut.mapQuotient (Subgroup.center (SL(2, F)))).comp <|
      (MulAut.congr eK).toMonoidHom.comp K.normalizerMonoidHom

variable {K}

private theorem uc22s2112r34_rho_mapQuotient_center_eq_one {G : Type*} [Group G]
    (hperf : commutator G = ⊤) (φ : MulAut G)
    (h : MulAut.mapQuotient (Subgroup.center G) φ = 1) : φ = 1 := by
  have hcent : ∀ x : G, x⁻¹ * φ x ∈ Subgroup.center G := by
    intro x
    have h1 := congrArg (fun α : MulAut (G ⧸ Subgroup.center G) =>
      α (QuotientGroup.mk x)) h
    simp only [MulAut.mapQuotient_mk, MulAut.one_apply] at h1
    have h2 : (QuotientGroup.mk (x⁻¹ * φ x) : G ⧸ Subgroup.center G) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, h1]
      exact inv_mul_cancel _
    exact (QuotientGroup.eq_one_iff _).1 h2
  let f : G →* Subgroup.center G :=
    { toFun := fun x => ⟨x⁻¹ * φ x, hcent x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        change (x * y)⁻¹ * φ (x * y) = x⁻¹ * φ x * (y⁻¹ * φ y)
        have h1 := (Subgroup.mem_center_iff.1 (hcent x)) y⁻¹
        rw [map_mul]
        calc (x * y)⁻¹ * (φ x * φ y) = y⁻¹ * (x⁻¹ * φ x) * φ y := by group
          _ = (x⁻¹ * φ x) * y⁻¹ * φ y := by rw [h1]
          _ = x⁻¹ * φ x * (y⁻¹ * φ y) := by group) }
  have hker : commutator G ≤ f.ker := Abelianization.commutator_subset_ker f
  rw [hperf] at hker
  ext x
  have hx := hker (Subgroup.mem_top x)
  rw [MonoidHom.mem_ker] at hx
  have h1 : x⁻¹ * φ x = 1 := congrArg Subtype.val hx
  rw [MulAut.one_apply]
  calc φ x = x * (x⁻¹ * φ x) := by group
    _ = x := by rw [h1, mul_one]

theorem uc22s2112r34_rho_eq_one_iff (hp5 : 5 ≤ p) (hF : Nat.card F = p) (eK : K ≃* SL(2, F))
    (g : normalizer (K : Set X)) :
    uc22s2112r34_rho K hp5 hF eK g = 1 ↔ ∀ k ∈ K, (g : X) * k * (g : X)⁻¹ = k := by
  classical
  let S := SL(2, F)
  let π : S →* (S ⧸ Subgroup.center S) := QuotientGroup.mk' _
  let φ : MulAut K := K.normalizerMonoidHom g
  have hperfS : Group.IsPerfect S := by
    exact CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F (by omega)
  have hstep : uc22s2112r34_rho_mulAutEquiv (F := F) hp5 hF
      (MulAut.mapQuotient (Subgroup.center S) ((MulAut.congr eK) φ)) = 1 ↔ φ = 1 := by
    constructor
    · intro h
      have h1 : MulAut.mapQuotient (Subgroup.center S) ((MulAut.congr eK) φ) = 1 :=
        (MulEquiv.map_eq_one_iff (uc22s2112r34_rho_mulAutEquiv (F := F) hp5 hF)).mp h
      exact (MulEquiv.map_eq_one_iff (MulAut.congr eK)).mp
        (uc22s2112r34_rho_mapQuotient_center_eq_one hperfS.commutator_eq_top
          ((MulAut.congr eK) φ) h1)
    · intro h
      have h1 : (MulAut.congr eK) φ = 1 :=
        (MulEquiv.map_eq_one_iff (MulAut.congr eK)).mpr h
      have h2 : MulAut.mapQuotient (Subgroup.center S) ((MulAut.congr eK) φ) = 1 := by
        simp [h1]
      exact (MulEquiv.map_eq_one_iff (uc22s2112r34_rho_mulAutEquiv (F := F) hp5 hF)).mpr h2
  have hρ : uc22s2112r34_rho K hp5 hF eK g =
      uc22s2112r34_rho_mulAutEquiv (F := F) hp5 hF
        (MulAut.mapQuotient (Subgroup.center S) ((MulAut.congr eK) φ)) := rfl
  rw [hρ, hstep]
  constructor
  · intro h k hk
    have hk' := congrArg (fun f : MulAut K => f ⟨k, hk⟩) h
    rw [MulAut.one_apply] at hk'
    have hval := congrArg Subtype.val hk'
    have hφ : (φ ⟨k, hk⟩ : X) = (g : X) * k * (g : X)⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe K g ⟨k, hk⟩
    rw [hφ] at hval
    simpa using hval
  · intro h
    refine MulEquiv.ext fun k => ?_
    rw [MulAut.one_apply]
    apply Subtype.ext
    have hφ : (φ k : X) = (g : X) * k * (g : X)⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe K g k
    rw [hφ]
    exact h k k.2

private theorem uc22s2112r34_rho_conj_injective_of_center_eq_bot {G : Type*} [Group G]
    (hZ : Subgroup.center G = ⊥) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  intro x y hxy
  have h1 : MulAut.conj (x⁻¹ * y) = 1 := by
    rw [map_mul, map_inv, hxy]
    simp
  have hcomm : ∀ z : G, z * (x⁻¹ * y) = (x⁻¹ * y) * z := by
    intro z
    have hz := congrArg (fun f : MulAut G => f z) h1
    simp only [MulAut.one_apply, MulAut.conj_apply] at hz
    calc z * (x⁻¹ * y) = ((x⁻¹ * y) * z * (x⁻¹ * y)⁻¹) * (x⁻¹ * y) := by rw [hz]
      _ = (x⁻¹ * y) * z := by group
  have hmem : x⁻¹ * y ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr hcomm
  rw [hZ, Subgroup.mem_bot] at hmem
  exact inv_mul_eq_one.mp hmem

theorem uc22s2112r34_rho_not_isCyclic (hp5 : 5 ≤ p) (hF : Nat.card F = p) (eK : K ≃* SL(2, F))
    {Q : Subgroup X} (hQ : CFSG.ABGLocalTools.IsSylowOf 2 Q K) :
    ¬ IsCyclic ((Q.subgroupOf (normalizer (K : Set X))).map (uc22s2112r34_rho K hp5 hF eK)) := by
  classical
  let S := SL(2, F)
  let P := PSL2 F
  let Z := Subgroup.center S
  let π : S →* P := QuotientGroup.mk' Z
  let N : Subgroup X := normalizer (K : Set X)
  let QN : Subgroup N := Q.subgroupOf N
  let iso : MulAut P ≃* PGL(Fin 2, F) := uc22s2112r34_rho_mulAutEquiv (F := F) hp5 hF
  let h : P →* PGL(Fin 2, F) := iso.toMonoidHom.comp (MulAut.conj : P →* MulAut P)
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
    ⟨p, 1, (Fact.out : p.Prime), (Fact.out : p.Prime).odd_of_ne_two (by omega),
      le_rfl, by rw [hF, pow_one]⟩
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
  have hconj_inj : Function.Injective (MulAut.conj : P →* MulAut P) :=
    uc22s2112r34_rho_conj_injective_of_center_eq_bot (psl2_center_eq_bot F)
  have hh_inj : Function.Injective h := by
    intro x y hxy
    exact hconj_inj (iso.injective hxy)
  have hρ : ∀ q : QN, uc22s2112r34_rho K hp5 hF eK q.1 = h (g q) := by
    intro q
    have hconj : (MulAut.congr eK) (K.normalizerMonoidHom q.1) =
        MulAut.conj (eK (fQ q)) := by
      refine MulEquiv.ext fun s => ?_
      obtain ⟨k, rfl⟩ := eK.surjective s
      rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
        MulEquiv.trans_apply, MulAut.conj_apply]
      have hfk : (K.normalizerMonoidHom q.1) k = fQ q * k * (fQ q)⁻¹ := by
        apply Subtype.ext
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
        rfl
      rw [hfk, map_mul, map_mul, map_inv]
    have hmapq : MulAut.mapQuotient Z (MulAut.conj (eK (fQ q))) =
        MulAut.conj (π (eK (fQ q))) := by
      ext x
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
      rw [MulAut.mapQuotient_mk, MulAut.conj_apply, MulAut.conj_apply]
      rfl
    show iso (MulAut.mapQuotient Z ((MulAut.congr eK) (K.normalizerMonoidHom q.1))) =
      iso (MulAut.conj (π (eK (fQ q))))
    rw [hconj, hmapq]
  have hmapρ : QN.map (uc22s2112r34_rho K hp5 hF eK) = g.range.map h := by
    apply le_antisymm
    · rintro x ⟨q, hq, rfl⟩
      exact ⟨g ⟨q, hq⟩, ⟨⟨q, hq⟩, rfl⟩, (hρ ⟨q, hq⟩).symm⟩
    · rintro x ⟨y, hy, rfl⟩
      obtain ⟨q, rfl⟩ := hy
      exact ⟨q.1, q.2, hρ q⟩
  change ¬ IsCyclic (QN.map (uc22s2112r34_rho K hp5 hF eK))
  intro hcyc
  rw [hmapρ] at hcyc
  have hgcyc : IsCyclic g.range :=
    (MulEquiv.isCyclic (Subgroup.equivMapOfInjective g.range h hh_inj)).mpr hcyc
  exact hQbar_nc (hQNmapg ▸ hgcyc)

end CFSG.LocalAnalysis.UniquenessCase.UC22

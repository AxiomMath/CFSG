module

public import CFSG.RankThree.PartTwo.Sec12.Item125Act
import CFSG.RankThree.PartTwo.Sec8.Hering611S3Step4b
public import CFSG.RankThree.PartTwo.Sec6.Item612Local
public import CFSG.RankThree.PartTwo.Sec8.Hering611KFInvMap

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem normalizes_core {C : Subgroup G} {K₀ : Subgroup C} {V : Subgroup G} {x : G}
    (hK₀ : K₀ ∈ thetaComponents 3 C)
    (hZ : Subgroup.center ((K₀.map C.subtype : Subgroup G) ⧸
      aschbacherSolvableCore 3 (K₀.map C.subtype : Subgroup G)) = ⊥)
    (hVK : V ≤ K₀.map C.subtype) (hV1 : imageSub (K₀.map C.subtype : Subgroup G) V ≠ ⊥)
    (hxC : x ∈ C) (hxV : x ∈ Subgroup.normalizer (V : Set G)) :
    x ∈ Subgroup.normalizer ((K₀.map C.subtype : Subgroup G) : Set G) := by
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : C, (x₀ : G) = x := ⟨⟨x, hxC⟩, rfl⟩
  have hK₁ := map_mulEquiv_mem_thetaComponents Nat.prime_three (MulAut.conj x₀) hK₀
  by_contra hxN
  have hne : K₀ ≠ K₀.map (MulAut.conj x₀).toMonoidHom := by
    intro h
    apply hxN
    rw [← hx₀]
    exact (Sec13.coe_mem_normalizer_map_iff C).mpr
      (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm)
  have hcomm := CFSG.RankThree.PartTwo.Sec14.Item148HJ.commutator_le_of_mem_thetaComponents_of_ne
    hK₀ hK₁ hne
  have hVK₁ : ∀ v₀ : C, (v₀ : G) ∈ V → v₀ ∈ K₀.map (MulAut.conj x₀).toMonoidHom := by
    intro v₀ hv
    have hxv : x⁻¹ * (v₀ : G) * x ∈ V := by
      refine (Subgroup.mem_normalizer_iff.mp hxV _).mpr ?_
      rw [show x * (x⁻¹ * (v₀ : G) * x) * x⁻¹ = (v₀ : G) by group]
      exact hv
    obtain ⟨c, hc, hcx⟩ := Subgroup.mem_map.mp (hVK hxv)
    refine Subgroup.mem_map.mpr ⟨c, hc, Subtype.ext ?_⟩
    have hcx' : (c : G) = x⁻¹ * (v₀ : G) * x := hcx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hx₀, hcx']
    group
  have hkey : ∀ v₀ : K₀, ((v₀ : C) : G) ∈ V → (v₀ : K₀ ⧸ aschbacherSolvableCore 3 K₀) = 1 := by
    intro v₀ hv
    have hv₁ := hVK₁ (v₀ : C) hv
    have hcentral : ∀ g : K₀ ⧸ aschbacherSolvableCore 3 K₀,
        g * (v₀ : K₀ ⧸ aschbacherSolvableCore 3 K₀) =
          (v₀ : K₀ ⧸ aschbacherSolvableCore 3 K₀) * g := by
      intro g
      obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective g
      refine Commute.eq
        (CFSG.RankThree.PartTwo.Sec8.Hering611S3Step4bProof.commute_mk_of_commutator_mem _ ?_)
      refine CFSG.RankThree.PartTwo.Sec8.Hering611S3Step4bProof.mem_aschbacherSolvableCore_of_mem ?_
      have hcomm0 : ((⁅g₀, v₀⁆ : K₀) : C) = ⁅(g₀ : C), (v₀ : C)⁆ := by
        simp [commutatorElement_def]
      rw [hcomm0]
      exact hcomm (Subgroup.commutator_mem_commutator g₀.2 hv₁)
    exact CFSG.RankThree.PartTwo.Sec8.Hering611S3Step4bProof.eq_one_of_central_of_center_eq_bot
      (Sec13.thetaQuotEquivSub C K₀) hZ hcentral
  apply hV1
  refine (Subgroup.eq_bot_iff_forall _).mpr ?_
  rintro y ⟨w, hw, rfl⟩
  have hwV : (w : G) ∈ V := Subgroup.mem_subgroupOf.mp hw
  obtain ⟨v₀, hv₀, hv₀G⟩ := Subgroup.mem_map.mp w.2
  have hmem : ((v₀ : C) : G) ∈ V := by
    rw [show ((v₀ : C) : G) = (w : G) from hv₀G]
    exact hwV
  have h1 := hkey ⟨v₀, hv₀⟩ hmem
  have h2 := congrArg (Sec13.thetaQuotEquivSub C K₀) h1
  rw [map_one, Sec13.thetaQuotEquivSub_mk] at h2
  have hw' : K₀.equivMapOfInjective C.subtype C.subtype_injective ⟨v₀, hv₀⟩ = w :=
    Subtype.ext hv₀G
  rw [hw'] at h2
  exact h2

theorem normalizes_of_centralizes {K V : Subgroup G} {d x : G} (hK : K ∈ thetaComponentsAt 3 d)
    (hZ : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥) (hVK : V ≤ K)
    (hV1 : imageSub K V ≠ ⊥) (hxd : x * d = d * x)
    (hxV : x ∈ Subgroup.normalizer (V : Set G)) : x ∈ Subgroup.normalizer (K : Set G) := by
  obtain ⟨K₀, hK₀, rfl⟩ := hK
  exact normalizes_core hK₀ hZ hVK hV1 (Subgroup.mem_centralizer_singleton_iff.mpr hxd) hxV

theorem V_sylow {K V : Subgroup G} {d : G} (hK : K ∈ thetaComponentsAt 3 d)
    (hZ : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥)
    (hodd : ¬ 2 ∣ Nat.card (Sec4.thetaQuotCentralizer K ⊓ Subgroup.centralizer ({d} : Set G) :
      Subgroup G))
    (hVK : V ≤ K) (hV2 : IsPGroup 2 V) (hV1 : imageSub K V ≠ ⊥)
    (hJ5 : ∀ σ : MulAut (K ⧸ aschbacherSolvableCore 3 K), (∀ v ∈ imageSub K V, σ v = v) →
      ∃ v ∈ imageSub K V, σ = MulAut.conj v) :
    ∀ T : Subgroup G, IsPGroup 2 T → T ≤ Subgroup.centralizer (V : Set G) ⊓
      Subgroup.centralizer ({d} : Set G) → V ≤ T → T ≤ V := by
  intro T hT hTC hVT x hx
  obtain ⟨hxCV, hxCd⟩ := Subgroup.mem_inf.mp (hTC hx)
  have hxd : x * d = d * x := Subgroup.mem_centralizer_singleton_iff.mp hxCd
  have hxV : x ∈ Subgroup.normalizer (V : Set G) := Subgroup.centralizer_le_normalizer _ hxCV
  have hxK : x ∈ Subgroup.normalizer (K : Set G) :=
    normalizes_of_centralizes hK hZ hVK hV1 hxd hxV
  have hfix : ∀ u ∈ imageSub K V, Sec12.thetaBarAct K ⟨x, hxK⟩ u = u := by
    intro u hu
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hu
    have hwV : (w : G) ∈ V := Subgroup.mem_subgroupOf.mp hw
    have hwx : (w : G) * x = x * (w : G) := Subgroup.mem_centralizer_iff.mp hxCV _ hwV
    rw [Sec12.thetaBarAct_mk]
    congr 1
    apply Subtype.ext
    rw [Sec4.normalizerMonoidHom_apply_coe, ← hwx, mul_inv_cancel_right]
  obtain ⟨vb, hvb, hσ⟩ := hJ5 (Sec12.thetaBarAct K ⟨x, hxK⟩) hfix
  obtain ⟨vk, hvk, hvkv⟩ := Subgroup.mem_map.mp hvb
  have hvV : (vk : G) ∈ V := Subgroup.mem_subgroupOf.mp hvk
  have hvN : (vk : G) ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer vk.2
  have hvd : (vk : G) ∈ Subgroup.centralizer ({d} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hK vk.2
  have hzT : x * (vk : G)⁻¹ ∈ T := T.mul_mem hx (T.inv_mem (hVT hvV))
  have hzd : x * (vk : G)⁻¹ ∈ Subgroup.centralizer ({d} : Set G) :=
    (Subgroup.centralizer ({d} : Set G)).mul_mem hxCd
      ((Subgroup.centralizer ({d} : Set G)).inv_mem hvd)
  have hzN : x * (vk : G)⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normalizer (K : Set G)).mul_mem hxK ((Subgroup.normalizer (K : Set G)).inv_mem hvN)
  have hact : Sec12.thetaBarAct K ⟨x * (vk : G)⁻¹, hzN⟩ = 1 := by
    have e1 : (⟨x * (vk : G)⁻¹, hzN⟩ : Subgroup.normalizer (K : Set G)) =
        ⟨x, hxK⟩ * (⟨(vk : G), hvN⟩)⁻¹ := rfl
    rw [e1, map_mul, map_inv, Sec12.thetaBarAct_of_mem vk.2, hσ, hvkv, mul_inv_cancel]
  have hz1 : x * (vk : G)⁻¹ ∈ Sec4.thetaQuotCentralizer K :=
    (Sec12.mem_thetaQuotCentralizer_iff_thetaBarAct hzN).mpr hact
  have hD : x * (vk : G)⁻¹ ∈ Sec4.thetaQuotCentralizer K ⊓ Subgroup.centralizer ({d} : Set G) :=
    Subgroup.mem_inf.mpr ⟨hz1, hzd⟩
  have hdvd := Subgroup.orderOf_dvd_natCard _ hD
  have hnd : ¬ 2 ∣ orderOf (x * (vk : G)⁻¹) := fun h => hodd (h.trans hdvd)
  obtain ⟨k, hk⟩ := hT ⟨x * (vk : G)⁻¹, hzT⟩
  have hk' : (x * (vk : G)⁻¹) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime (orderOf (x * (vk : G)⁻¹)) (2 ^ k) :=
    Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hnd).symm
  have hone : orderOf (x * (vk : G)⁻¹) = 1 :=
    Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_of_pow_eq_one hk')
  have hz : x * (vk : G)⁻¹ = 1 := orderOf_eq_one_iff.mp hone
  rw [mul_inv_eq_one.mp hz]
  exact hvV

end CFSG.RankThree.PartTwo.Sec8.Hering611

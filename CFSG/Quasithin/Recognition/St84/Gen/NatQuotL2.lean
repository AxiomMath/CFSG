module

public import CFSG.Quasithin.Recognition.St84.Sec6BaumannS3
import CFSG.Quasithin.Recognition.St84.Gen.NatL2
import CFSG.Quasithin.Recognition.St84.Gen.PushZL2
import CFSG.Quasithin.Recognition.St84.Gen.PerfectGen
import CFSG.Quasithin.Recognition.St84.Gen.NatSecQuot

public section

namespace CFSG.Quasithin.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell CFSG.Quasithin.F53Push CFSG.Quasithin.H13
open scoped MatrixGroups commutatorElement Matrix

section FiniteTop

variable {H : Type} [Group H] [Finite H]

private theorem natQuot_of_isL2Quot_top {P : Subgroup H} {n : ℕ} (hn : 2 ≤ n)
    (hc : CharTwo (⊤ : Subgroup H)) (hq : IsL2Quot n (oTwoQuot ↥(⊤ : Subgroup H)))
    (hP : IsSylowTwoOf P (⊤ : Subgroup H)) (hnc : NoCharNormal P (⊤ : Subgroup H))
    (he : IsElemAbelian 2 (pCoreOf 2 (⊤ : Subgroup H))) :
    NatQuot (⊤ : Subgroup H) (pCoreOf 2 (⊤ : Subgroup H)) (centerOf (⊤ : Subgroup H)) n ∧
      ⁅pCoreOf 2 (⊤ : Subgroup H), oTwoRes (⊤ : Subgroup H)⁆ ≠ ⊥ := by
  classical
  let E : Subgroup H := pCoreOf 2 (⊤ : Subgroup H)
  let F := GaloisField 2 n
  have hCE : Subgroup.centralizer (E : Set H) ≤ E := by
    intro x hx
    exact hc (Subgroup.mem_inf.mpr ⟨Subgroup.mem_top x, hx⟩)
  have hEcent : E ≤ Subgroup.centralizer (E : Set H) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (congrArg Subtype.val (he.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)).symm
  have hcent_eq : (⊤ : Subgroup H) ⊓ Subgroup.centralizer (E : Set H) = E := by
    rw [top_inf_eq]
    exact le_antisymm hCE hEcent
  have hZcE : centerOf (⊤ : Subgroup H) ≤ E := by
    intro z hz
    have hzC : z ∈ Subgroup.centralizer (E : Set H) := by
      rw [centerOf, Subgroup.mem_inf] at hz
      rw [Subgroup.mem_centralizer_iff]
      intro e _
      exact Subgroup.mem_centralizer_iff.mp hz.2 e (Subgroup.mem_top e)
    exact hc (Subgroup.mem_inf.mpr ⟨Subgroup.mem_top z, hzC⟩)
  have hPush : PushHyp (⊤ : Subgroup H) P E :=
    ⟨hP, CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (⊤ : Subgroup H), he, le_rfl, hcent_eq⟩
  have hJ : ¬ thompsonJ P ≤ E := not_thompsonJ_le_pCoreOf_L2 hq hP hnc
  obtain ⟨α, β, hα, hαk, hβ, hβe, hβk⟩ := natCoord_of_isL2Quot hPush hn hq hJ
  have hsup : pResidualOf 2 (⊤ : Subgroup H) ⊔ E = ⊤ := by
    let q : ↥(⊤ : Subgroup H) →* oTwoQuot ↥(⊤ : Subgroup H) :=
      QuotientGroup.mk' (CFSG.pCore 2 ↥(⊤ : Subgroup H))
    have hEsub : E.subgroupOf (⊤ : Subgroup H) = CFSG.pCore 2 ↥(⊤ : Subgroup H) := by
      change (pCoreOf 2 (⊤ : Subgroup H)).subgroupOf (⊤ : Subgroup H) = _
      rw [pCoreOf]
      exact Subgroup.comap_map_eq_self_of_injective (⊤ : Subgroup H).subtype_injective _
    have hperf : Group.IsPerfect (oTwoQuot ↥(⊤ : Subgroup H)) :=
      CFSG.Quasithin.F112R.isPerfect_of_isL2Quot hn hq
    have hp : oTwoUpper (⊤ : Subgroup (oTwoQuot ↥(⊤ : Subgroup H))) = ⊤ := by
      refine le_antisymm le_top ?_
      show (⊤ : Subgroup (oTwoQuot ↥(⊤ : Subgroup H))) ≤
        oTwoUpper (⊤ : Subgroup (oTwoQuot ↥(⊤ : Subgroup H)))
      haveI : Group.IsPerfect (oTwoQuot ↥(⊤ : Subgroup H)) := hperf
      have hperf' : Group.IsPerfect ↥(⊤ : Subgroup (oTwoQuot ↥(⊤ : Subgroup H))) :=
        Group.IsPerfect.ofSurjective (f := (Subgroup.topEquiv).symm.toMonoidHom)
          (by simpa using (Subgroup.topEquiv).symm.surjective)
      exact CFSG.Quasithin.perfect_le_oTwoUpper le_rfl hperf'
    have hmap : (oTwoUpper (⊤ : Subgroup ↥(⊤ : Subgroup H))).map q = ⊤ := by
      rw [← oTwoUpper_map q (⊤ : Subgroup ↥(⊤ : Subgroup H)), Subgroup.map_top,
        MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _), hp]
    have hcomap : Subgroup.comap q ⊤ = oTwoUpper (⊤ : Subgroup ↥(⊤ : Subgroup H)) ⊔ q.ker := by
      rw [← hmap, Subgroup.comap_map_eq]
    rw [Subgroup.comap_top, QuotientGroup.ker_mk', ← hEsub] at hcomap
    have hmap2 := congrArg (Subgroup.map (⊤ : Subgroup H).subtype) hcomap
    rw [Subgroup.map_sup, oTwoUpper_top_subgroupOf,
      Subgroup.map_subgroupOf_eq_of_le (CFSG.LieType.BorelTits.pCoreOf_le 2 (⊤ : Subgroup H)),
      Subgroup.map_top,
      Subgroup.range_subtype] at hmap2
    rw [oTwoUpper_eq_pResidualOf] at hmap2
    have h : pResidualOf 2 (⊤ : Subgroup H) ⊔ E = ⊤ := by
      have h' := hmap2
      rw [show Subgroup.map (⊤ : Subgroup H).subtype
          ((pResidualOf 2 (⊤ : Subgroup H)).subgroupOf ⊤) =
          pResidualOf 2 (⊤ : Subgroup H) from
        Subgroup.map_subgroupOf_eq_of_le (le_top : pResidualOf 2 (⊤ : Subgroup H) ≤ ⊤),
        show pCoreOf 2 (⊤ : Subgroup H) = E from rfl] at h'
      exact h'.symm
    exact h
  have hZ0eq : zZero (⊤ : Subgroup H) E = centerOf (⊤ : Subgroup H) := by
    have hZ0' : zZero (⊤ : Subgroup H) E =
        E ⊓ Subgroup.centralizer (pResidualOf 2 (⊤ : Subgroup H) : Set H) := by
      rw [zZero_eq, pResidualOf_eq_oTwoRes]
    refine le_antisymm ?_ ?_
    · intro x hx
      rw [hZ0', Subgroup.mem_inf] at hx
      obtain ⟨hxE, hxC⟩ := hx
      have hxEcent : x ∈ Subgroup.centralizer (E : Set H) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact congrArg Subtype.val (he.1.is_comm.comm ⟨y, hy⟩ ⟨x, hxE⟩)
      have hO : pResidualOf 2 (⊤ : Subgroup H) ≤ Subgroup.centralizer (Subgroup.zpowers x) :=
        Subgroup.le_centralizer_iff.mp (Subgroup.zpowers_le.mpr hxC)
      have hE' : E ≤ Subgroup.centralizer (Subgroup.zpowers x) :=
        Subgroup.le_centralizer_iff.mpr (Subgroup.zpowers_le.mpr hxEcent)
      have htop : (⊤ : Subgroup H) ≤ Subgroup.centralizer (Subgroup.zpowers x) := by
        rw [← hsup]
        exact sup_le hO hE'
      rw [centerOf, Subgroup.mem_inf]
      refine ⟨Subgroup.mem_top x, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y _
      have hxcent : x ∈ Subgroup.centralizer (⊤ : Set H) :=
        Subgroup.zpowers_le.mp (Subgroup.le_centralizer_iff.mpr htop)
      exact (Subgroup.mem_centralizer_iff.mp hxcent) y (Subgroup.mem_top y)
    · intro x hx
      rw [hZ0', Subgroup.mem_inf]
      refine ⟨hZcE hx, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y _
      rw [centerOf, Subgroup.mem_inf] at hx
      exact Subgroup.mem_centralizer_iff.mp hx.2 y (Subgroup.mem_top y)
  have hβkerZ : β.ker = ((centerOf (⊤ : Subgroup H)).subgroupOf ⊤).subgroupOf (E.subgroupOf ⊤) := by
    rw [beta_ker_eq_zZero β hβk, hZ0eq]
  let E' : Subgroup ↥(⊤ : Subgroup H) := E.subgroupOf ⊤
  have hβkerZ' : β.ker = ((centerOf (⊤ : Subgroup H)).subgroupOf ⊤).subgroupOf E' := hβkerZ
  have hNZ : (⊤ : Subgroup H) ≤ Subgroup.normalizer (centerOf (⊤ : Subgroup H) : Set H) := by
    have h := A4.normalizer_le_normalizer_centerOf (⊤ : Subgroup H)
    rwa [Subgroup.normalizer_eq_top_iff.mpr inferInstance] at h
  have hEZ : E ≤ Subgroup.normalizer (centerOf (⊤ : Subgroup H) : Set H) :=
    fun x _ => hNZ (Subgroup.mem_top x)
  have img_relCent_iff : ∀ (A : Subgroup H), IsSylowTwoOf A (⊤ : Subgroup H) →
      ∀ v : Multiplicative (Fin 2 → F),
      v ∈ (((relCent E (centerOf (⊤ : Subgroup H)) A).subgroupOf ⊤).subgroupOf E').map β ↔
        Multiplicative.toAdd v ∈ SL2Nat.fixedSub ((A.subgroupOf ⊤).map α) := by
    intro A hA v
    constructor
    · rintro ⟨e, he, rfl⟩
      have he1 : ((e : ↥(⊤ : Subgroup H)) : H) ∈ relCent E (centerOf (⊤ : Subgroup H)) A := by
        exact Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp he)
      rw [SL2Nat.mem_fixedSub]
      intro r hr
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hr
      have haA : (a : H) ∈ A := Subgroup.mem_subgroupOf.mp ha
      obtain ⟨-, hcomm⟩ := (mem_relCent hEZ).mp he1
      let e' : ↥E' := ⟨a * e * a⁻¹, Subgroup.mem_subgroupOf.mpr
        ((Subgroup.mem_normalizer_iff.mp (hPush.normal a.2) (e : ↥(⊤ : Subgroup H))).mp
          (Subgroup.mem_subgroupOf.mp e.2))⟩
      have he' : β e' = β e := by
        have hcomm' : ⁅((e : ↥(⊤ : Subgroup H)) : H), (a : H)⁆ ∈ centerOf (⊤ : Subgroup H) :=
          hcomm (a : H) haA
        have hker : (e' * e⁻¹) ∈ β.ker := by
          rw [hβkerZ']
          refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr ?_)
          have h1 : (((e' * e⁻¹ : ↥E') : ↥(⊤ : Subgroup H)) : H) =
              (a : H) * ((e : ↥(⊤ : Subgroup H)) : H) * (a : H)⁻¹ *
                ((e : ↥(⊤ : Subgroup H)) : H)⁻¹ := rfl
          rw [h1]
          have h2 : (a : H) * ((e : ↥(⊤ : Subgroup H)) : H) * (a : H)⁻¹ *
                ((e : ↥(⊤ : Subgroup H)) : H)⁻¹ =
              ⁅((e : ↥(⊤ : Subgroup H)) : H), (a : H)⁆⁻¹ := by
            rw [commutatorElement_def]
            group
          rw [h2]
          exact (centerOf (⊤ : Subgroup H)).inv_mem hcomm'
        have h1 : β (e' * e⁻¹) = 1 := MonoidHom.mem_ker.mp hker
        rw [map_mul, map_inv] at h1
        exact mul_inv_eq_one.mp h1
      rw [SL2Nat.lin_apply, ← hβe a e e' rfl, he']
    · intro hv
      obtain ⟨e, hev⟩ := hβ v
      refine ⟨e, ?_, hev⟩
      have he1 : ((e : ↥(⊤ : Subgroup H)) : H) ∈ relCent E (centerOf (⊤ : Subgroup H)) A := by
        rw [mem_relCent hEZ]
        refine ⟨Subgroup.mem_subgroupOf.mp e.2, ?_⟩
        intro a haA
        have ha : (⟨a, hA.1 haA⟩ : ↥(⊤ : Subgroup H)) ∈ A.subgroupOf ⊤ :=
          Subgroup.mem_subgroupOf.mpr haA
        let a' : ↥(⊤ : Subgroup H) := ⟨a, hA.1 haA⟩
        let e' : ↥E' := ⟨a' * e * a'⁻¹, Subgroup.mem_subgroupOf.mpr
          ((Subgroup.mem_normalizer_iff.mp (hPush.normal a'.2) (e : ↥(⊤ : Subgroup H))).mp
            (Subgroup.mem_subgroupOf.mp e.2))⟩
        have hfix' : (α a' : Matrix (Fin 2) (Fin 2) F).mulVec
            (Multiplicative.toAdd (β e)) = Multiplicative.toAdd (β e) := by
          have hmap : α a' ∈ (A.subgroupOf ⊤).map α := Subgroup.mem_map_of_mem α ha
          have hfix := (SL2Nat.mem_fixedSub).mp hv (α a') hmap
          rw [SL2Nat.lin_apply] at hfix
          simpa [← hev] using hfix
        have heq : Multiplicative.toAdd (β e') = Multiplicative.toAdd (β e) := by
          rw [hβe a' e e' rfl]
          exact hfix'
        have heq' : β e' = β e := Multiplicative.toAdd.injective heq
        have hker : (e' * e⁻¹) ∈ β.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, heq', mul_inv_cancel]
        rw [hβkerZ'] at hker
        have hmem : (((e' * e⁻¹ : ↥E') : ↥(⊤ : Subgroup H)) : H) ∈ centerOf (⊤ : Subgroup H) :=
          Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hker)
        have h1 : (((e' * e⁻¹ : ↥E') : ↥(⊤ : Subgroup H)) : H) =
            (a' : H) * ((e : ↥(⊤ : Subgroup H)) : H) * (a' : H)⁻¹ *
              ((e : ↥(⊤ : Subgroup H)) : H)⁻¹ := rfl
        rw [h1] at hmem
        have h2 : (a' : H) * ((e : ↥(⊤ : Subgroup H)) : H) * (a' : H)⁻¹ *
              ((e : ↥(⊤ : Subgroup H)) : H)⁻¹ =
            ⁅((e : ↥(⊤ : Subgroup H)) : H), (a' : H)⁆⁻¹ := by
          rw [commutatorElement_def]
          group
        rw [h2] at hmem
        simpa [a'] using (centerOf (⊤ : Subgroup H)).inv_mem hmem
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr he1)
  have hZc_relCent : ∀ (A : Subgroup H), centerOf (⊤ : Subgroup H) ≤
      relCent E (centerOf (⊤ : Subgroup H)) A := by
    intro A z hz
    rw [mem_relCent hEZ]
    refine ⟨hZcE hz, fun a _ => ?_⟩
    have hzC : z ∈ Subgroup.centralizer (⊤ : Set H) := by
      rw [centerOf, Subgroup.mem_inf] at hz
      exact hz.2
    have hza : ⁅z, a⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.mp hzC a (Subgroup.mem_top a)).symm
    rw [hza]
    exact (centerOf (⊤ : Subgroup H)).one_mem
  have mem_relCent_iff_beta : ∀ (A : Subgroup H), IsSylowTwoOf A (⊤ : Subgroup H) →
      ∀ x : ↥E', ((x : ↥(⊤ : Subgroup H)) : H) ∈
          relCent E (centerOf (⊤ : Subgroup H)) A ↔
        Multiplicative.toAdd (β x) ∈ SL2Nat.fixedSub ((A.subgroupOf ⊤).map α) := by
    intro A hA x
    constructor
    · intro hx
      have hxK : x ∈ (((relCent E (centerOf (⊤ : Subgroup H)) A).subgroupOf ⊤).subgroupOf E') :=
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hx)
      exact (img_relCent_iff A hA (β x)).mp ⟨x, hxK, rfl⟩
    · intro hfix
      obtain ⟨x', hx'K, hβx'⟩ := (img_relCent_iff A hA (β x)).mpr hfix
      have hx'R : ((x' : ↥(⊤ : Subgroup H)) : H) ∈
          relCent E (centerOf (⊤ : Subgroup H)) A :=
        Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hx'K)
      have hker : x * x'⁻¹ ∈ β.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hβx', mul_inv_cancel]
      have hZ : (((x * x'⁻¹ : ↥E') : ↥(⊤ : Subgroup H)) : H) ∈
          centerOf (⊤ : Subgroup H) := by
        rw [hβkerZ'] at hker
        exact Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hker)
      have hZrel : (((x * x'⁻¹ : ↥E') : ↥(⊤ : Subgroup H)) : H) ∈
          relCent E (centerOf (⊤ : Subgroup H)) A := hZc_relCent A hZ
      have hmul : (((x * x'⁻¹ : ↥E') : ↥(⊤ : Subgroup H)) : H) *
            ((x' : ↥(⊤ : Subgroup H)) : H) ∈
          relCent E (centerOf (⊤ : Subgroup H)) A :=
        (relCent E (centerOf (⊤ : Subgroup H)) A).mul_mem hZrel hx'R
      convert hmul using 1
      symm
      change (((x * x'⁻¹) * x' : ↥E') : H) = (x : H)
      congr 1
      group
  have beta_eq_mul_inv_mem_Z : ∀ x y : ↥E', β x = β y →
      ((x : ↥(⊤ : Subgroup H)) : H) * ((y : ↥(⊤ : Subgroup H)) : H)⁻¹ ∈
        centerOf (⊤ : Subgroup H) := by
    intro x y hxy
    have hker : x * y⁻¹ ∈ β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, mul_inv_cancel]
    rw [hβkerZ'] at hker
    exact Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hker)
  have natCard_img_relCent : ∀ (A : Subgroup H), IsSylowTwoOf A (⊤ : Subgroup H) →
      Nat.card ↥((((relCent E (centerOf (⊤ : Subgroup H)) A).subgroupOf ⊤).subgroupOf E').map β) =
        Nat.card ↥(SL2Nat.fixedSub ((A.subgroupOf ⊤).map α)) := by
    intro A hA
    refine Nat.card_congr ?_
    refine
      { toFun := fun v => ⟨Multiplicative.toAdd v.1,
          (img_relCent_iff A hA v.1).mp v.2⟩
        invFun := fun v => ⟨Multiplicative.ofAdd v.1,
          (img_relCent_iff A hA (Multiplicative.ofAdd v.1)).mpr (by simpa using v.2)⟩
        left_inv := fun v => by apply Subtype.ext; simp
        right_inv := fun v => by apply Subtype.ext; simp }
  have natCard_imgβ_eq_relIndex : ∀ (K : Subgroup H), centerOf (⊤ : Subgroup H) ≤ K → K ≤ E →
      Nat.card ↥((((K.subgroupOf ⊤).subgroupOf E').map β)) =
        (centerOf (⊤ : Subgroup H)).relIndex K := by
    intro K hZK hKE
    let K' : Subgroup ↥E' := (K.subgroupOf ⊤).subgroupOf E'
    have hK' : K.subgroupOf ⊤ ≤ E' := fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hKE (Subgroup.mem_subgroupOf.mp hx))
    let eK : ↥K' ≃* ↥K :=
      (Subgroup.subgroupOfEquivOfLe hK').trans (Subgroup.subgroupOfEquivOfLe le_top)
    let βK : ↥K →* Multiplicative (Fin 2 → F) :=
      β.comp (K'.subtype.comp eK.symm.toMonoidHom)
    have hker : βK.ker = (centerOf (⊤ : Subgroup H)).subgroupOf K := by
      ext x
      constructor
      · intro hx
        have hx' : (eK.symm x : ↥E') ∈ β.ker := hx
        rw [hβkerZ'] at hx'
        exact Subgroup.mem_subgroupOf.mpr
          (Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hx'))
      · intro hx
        have hx' : (x : H) ∈ centerOf (⊤ : Subgroup H) := Subgroup.mem_subgroupOf.mp hx
        have hmem : (eK.symm x : ↥E') ∈
            ((centerOf (⊤ : Subgroup H)).subgroupOf ⊤).subgroupOf E' := by
          refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr ?_)
          exact Subgroup.mem_subgroupOf.mpr hx'
        rw [← hβkerZ'] at hmem
        exact hmem
    have hrange : βK.range = K'.map β := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact Subgroup.mem_map_of_mem β (eK.symm x).2
      · intro hy
        obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hy
        refine ⟨eK ⟨k, hk⟩, ?_⟩
        change β ((eK.symm (eK ⟨k, hk⟩) : ↥K') : ↥E') = β k
        rw [MulEquiv.symm_apply_apply]
    have h1 : βK.ker.index = Nat.card ↥(K'.map β) := by
      rw [Subgroup.index_ker, hrange]
    have h2 : βK.ker.index = (centerOf (⊤ : Subgroup H)).relIndex K := by
      rw [hker]
      rfl
    rw [← h1, h2]
  have hindex : (centerOf (⊤ : Subgroup H)).relIndex E = 2 ^ (2 * n) := by
    let e : ↥(E.subgroupOf ⊤) ≃* ↥E := Subgroup.subgroupOfEquivOfLe le_top
    have hmap : Subgroup.map e.toMonoidHom β.ker =
        (centerOf (⊤ : Subgroup H)).subgroupOf E := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [hβkerZ] at hy
        exact Subgroup.mem_subgroupOf.mpr
          (Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hy))
      · intro hx
        refine ⟨⟨⟨x.1, Subgroup.mem_top x.1⟩, Subgroup.mem_subgroupOf.mpr x.2⟩, ?_, ?_⟩
        · rw [hβkerZ]
          exact Subgroup.mem_subgroupOf.mpr
            (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hx))
        · rfl
    have h1 : β.ker.index = Nat.card (Multiplicative (Fin 2 → F)) := by
      rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hβ, Subgroup.card_top]
    have h2 : (Subgroup.map e.toMonoidHom β.ker).index = β.ker.index := by
      simpa using Subgroup.index_map_equiv β.ker e
    rw [Subgroup.relIndex, ← hmap, h2, h1]
    rw [Nat.card_congr
      (Multiplicative.toAdd : Multiplicative (Fin 2 → F) ≃ (Fin 2 → F)),
      Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin]
    change Nat.card (GaloisField 2 n) ^ 2 = 2 ^ (2 * n)
    rw [GaloisField.card 2 n (by omega)]
    rw [pow_two, ← pow_add, two_mul]
  have beta_comm_gen : ∀ (e : ↥E') (a : ↥(⊤ : Subgroup H)),
      ∃ c : ↥E', (c : ↥(⊤ : Subgroup H)) = (a * (e : ↥(⊤ : Subgroup H)) * a⁻¹) *
          (e : ↥(⊤ : Subgroup H))⁻¹ ∧
        Multiplicative.toAdd (β c) =
          (α a : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β e)) -
            Multiplicative.toAdd (β e) := by
    intro e a
    let e' : ↥E' := ⟨a * (e : ↥(⊤ : Subgroup H)) * a⁻¹, Subgroup.mem_subgroupOf.mpr
      ((Subgroup.mem_normalizer_iff.mp (hPush.normal a.2) (e : ↥(⊤ : Subgroup H))).mp
        (Subgroup.mem_subgroupOf.mp e.2))⟩
    refine ⟨e' * e⁻¹, rfl, ?_⟩
    have h1 : Multiplicative.toAdd (β e') =
        (α a : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β e)) :=
      hβe a e e' rfl
    have h2 : Multiplicative.toAdd (β (e' * e⁻¹)) =
        Multiplicative.toAdd (β e') - Multiplicative.toAdd (β e) := by
      rw [map_mul, map_inv]
      simp [sub_eq_add_neg]
    rw [h2, h1]
  refine ⟨?_, ?_⟩
  · refine ⟨hZcE, le_top, ?_, hindex, ?_, ?_, ?_, ?_, ?_⟩
    · exact le_inf
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (⊤ : Subgroup H))
        (by
          have h := A4.normalizer_le_normalizer_centerOf (⊤ : Subgroup H)
          rwa [Subgroup.normalizer_eq_top_iff.mpr inferInstance] at h)
    · intro A hA
      let R : Subgroup SL(2, F) := (A.subgroupOf ⊤).map α
      have hR : IsPGroup 2 R := by
        have h1 : IsPGroup 2 ↥(A.subgroupOf ⊤) :=
          hA.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe (le_top : A ≤ ⊤)).symm
        exact IsPGroup.map h1 α
      have hRcard : Nat.card R = Nat.card F := card_map_sylow_of_natCoord hA α hα
      have hcardFixed : Nat.card ↥(SL2Nat.fixedSub R) = Nat.card F :=
        SL2Nat.natCard_fixedSub_of_card hR hRcard
      have hrelE : relCent E (centerOf (⊤ : Subgroup H)) A ≤ E := fun x hx => hx.1
      rw [← natCard_imgβ_eq_relIndex (relCent E (centerOf (⊤ : Subgroup H)) A)
          (hZc_relCent A) hrelE, natCard_img_relCent A hA, hcardFixed]
      rw [GaloisField.card 2 n (by omega)]
    · intro A hA
      let R : Subgroup SL(2, F) := (A.subgroupOf ⊤).map α
      have hR : IsPGroup 2 R := by
        have h1 : IsPGroup 2 ↥(A.subgroupOf ⊤) :=
          hA.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe (le_top : A ≤ ⊤)).symm
        exact IsPGroup.map h1 α
      have hRcard : Nat.card R = Nat.card F := card_map_sylow_of_natCoord hA α hα
      have hcomm_eq : SL2Nat.commSub R = SL2Nat.fixedSub R :=
        SL2Nat.commSub_eq_fixedSub_of_card hR hRcard
      let K : Subgroup H := ⁅E, A⁆ ⊔ centerOf (⊤ : Subgroup H)
      have hEA_le_E : ⁅E, A⁆ ≤ E := by
        rw [Subgroup.commutator_le]
        intro e he a ha
        have ha_top : a ∈ (⊤ : Subgroup H) := Subgroup.mem_top a
        have h1 : a * e⁻¹ * a⁻¹ ∈ E := by
          have h := (Subgroup.mem_normalizer_iff.mp (hPush.normal ha_top) (e⁻¹)).mp
            (E.inv_mem he)
          simpa [mul_assoc] using h
        rw [commutatorElement_def]
        have h2 : e * a * e⁻¹ * a⁻¹ = e * (a * e⁻¹ * a⁻¹) := by group
        rw [h2]
        exact E.mul_mem he h1
      have hK_le_E : K ≤ E := by
        change ⁅E, A⁆ ⊔ centerOf (⊤ : Subgroup H) ≤ E
        exact sup_le hEA_le_E hZcE
      have hK_le : K ≤ relCent E (centerOf (⊤ : Subgroup H)) A := by
        change ⁅E, A⁆ ⊔ centerOf (⊤ : Subgroup H) ≤ relCent E (centerOf (⊤ : Subgroup H)) A
        rw [sup_le_iff]
        constructor
        · rw [Subgroup.commutator_le]
          intro e he a ha
          let e' : ↥E' := ⟨⟨e, Subgroup.mem_top e⟩, he⟩
          let a' : ↥(⊤ : Subgroup H) := ⟨a, hA.1 ha⟩
          obtain ⟨c, hc_eq, hcβ⟩ := beta_comm_gen e' a'
          have hx_memE : ⁅e, a⁆ ∈ E := by
            have hmem : ⁅e, a⁆ ∈ ⁅E, A⁆ :=
              Subgroup.commutator_mem_commutator he ha
            exact hEA_le_E hmem
          let x : ↥E' := ⟨⟨⁅e, a⁆, Subgroup.mem_top _⟩,
            Subgroup.mem_subgroupOf.mpr hx_memE⟩
          have hx_eq : x = c⁻¹ := by
            apply Subtype.ext
            rw [Subgroup.coe_inv]
            apply Subtype.ext
            have hcH : ((c : ↥(⊤ : Subgroup H)) : H) = a * e * a⁻¹ * e⁻¹ := by
              simpa using congrArg (fun z : ↥(⊤ : Subgroup H) => (z : H)) hc_eq
            rw [Subgroup.coe_inv, hcH]
            change (e * a * e⁻¹ * a⁻¹ : H) = (a * e * a⁻¹ * e⁻¹ : H)⁻¹
            group
          have hgen : Multiplicative.toAdd (β c) ∈ SL2Nat.commSub R := by
            rw [hcβ, ← SL2Nat.lin_apply]
            exact SL2Nat.sub_mem_commSub
              (Subgroup.mem_map_of_mem α (Subgroup.mem_subgroupOf.mpr ha))
              (Multiplicative.toAdd (β e'))
          have hxβ : Multiplicative.toAdd (β x) ∈ SL2Nat.fixedSub R := by
            rw [hx_eq, map_inv]
            have hgen' : Multiplicative.toAdd (β c) ∈ SL2Nat.fixedSub R := by
              rwa [hcomm_eq] at hgen
            rw [show Multiplicative.toAdd ((β c)⁻¹) = -Multiplicative.toAdd (β c) by
              simp [sub_eq_add_neg]]
            exact (SL2Nat.fixedSub R).neg_mem hgen'
          have hxrel : ((x : ↥(⊤ : Subgroup H)) : H) ∈
              relCent E (centerOf (⊤ : Subgroup H)) A :=
            (mem_relCent_iff_beta A hA x).mpr hxβ
          simpa [x] using hxrel
        · exact hZc_relCent A
      let P : (Fin 2 → F) → Prop := fun w =>
        ∀ c : F, ∃ y : ↥E', ((y : ↥(⊤ : Subgroup H)) : H) ∈ K ∧
          Multiplicative.toAdd (β y) = c • w
      have hP : ∀ w, w ∈ SL2Nat.commSub R → P w := by
        intro w hw
        rw [show SL2Nat.commSub R = Submodule.span F {w | ∃ r ∈ R, ∃ v : Fin 2 → F,
          w = SL2Nat.lin r v - v} from rfl] at hw
        refine Submodule.span_induction ?mem ?zero ?add ?smul hw
        · rintro w ⟨r, hr, v, rfl⟩ c
          obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hr
          have haA : (a : H) ∈ A := Subgroup.mem_subgroupOf.mp ha
          obtain ⟨e, heβ⟩ := hβ (Multiplicative.ofAdd (c • v))
          obtain ⟨y, hy_eq, hyβ⟩ := beta_comm_gen e a
          refine ⟨y, ?_, ?_⟩
          · have hy_comm : ((y : ↥(⊤ : Subgroup H)) : H) =
                ⁅((e : ↥(⊤ : Subgroup H)) : H), (a : H)⁆⁻¹ := by
              rw [hy_eq]
              change (a : H) * ((e : ↥(⊤ : Subgroup H)) : H) * (a : H)⁻¹ *
                ((e : ↥(⊤ : Subgroup H)) : H)⁻¹ =
                ⁅((e : ↥(⊤ : Subgroup H)) : H), (a : H)⁆⁻¹
              rw [commutatorElement_def]
              group
            rw [hy_comm]
            exact K.inv_mem (Subgroup.mem_sup_left
              (Subgroup.commutator_mem_commutator
                (Subgroup.mem_subgroupOf.mp e.2) haA))
          · rw [hyβ, show Multiplicative.toAdd (β e) = c • v by
              rw [heβ]; simp]
            rw [Matrix.mulVec_smul, SL2Nat.lin_apply, smul_sub]
        · intro c
          refine ⟨1, ?_, ?_⟩
          · exact K.one_mem
          · rw [map_one]
            simp
        · intro w₁ w₂ h₁ h₂ ih₁ ih₂ c
          obtain ⟨y₁, hy₁K, hy₁β⟩ := ih₁ c
          obtain ⟨y₂, hy₂K, hy₂β⟩ := ih₂ c
          refine ⟨y₁ * y₂, K.mul_mem hy₁K hy₂K, ?_⟩
          rw [map_mul]
          simp [hy₁β, hy₂β, smul_add]
        · intro a w hw ih c
          obtain ⟨y, hyK, hyβ⟩ := ih (a * c)
          refine ⟨y, hyK, ?_⟩
          rw [hyβ, mul_comm a c, smul_smul]
      have hZ_le_K : centerOf (⊤ : Subgroup H) ≤ K := by
        intro z hz
        exact Subgroup.mem_sup_right hz
      have hrel_le_K : relCent E (centerOf (⊤ : Subgroup H)) A ≤ K := by
        intro x hx
        let xE : ↥E' := ⟨⟨x, Subgroup.mem_top x⟩, hx.1⟩
        have hxβ : Multiplicative.toAdd (β xE) ∈ SL2Nat.fixedSub R :=
          (mem_relCent_iff_beta A hA xE).mp hx
        have hw : Multiplicative.toAdd (β xE) ∈ SL2Nat.commSub R := by
          rwa [hcomm_eq]
        obtain ⟨y, hyK, hyβ⟩ := hP _ hw 1
        have hyβ' : β y = β xE := by
          apply Multiplicative.toAdd.injective
          simpa using hyβ
        have hxyZ : ((xE : ↥(⊤ : Subgroup H)) : H) *
            ((y : ↥(⊤ : Subgroup H)) : H)⁻¹ ∈ centerOf (⊤ : Subgroup H) :=
          beta_eq_mul_inv_mem_Z xE y hyβ'.symm
        have hxyK : (((xE : ↥(⊤ : Subgroup H)) : H) *
            ((y : ↥(⊤ : Subgroup H)) : H)⁻¹) *
            ((y : ↥(⊤ : Subgroup H)) : H) ∈ K :=
          K.mul_mem (hZ_le_K hxyZ) hyK
        have hx_eq : x = (((xE : ↥(⊤ : Subgroup H)) : H) *
            ((y : ↥(⊤ : Subgroup H)) : H)⁻¹) * ((y : ↥(⊤ : Subgroup H)) : H) := by
          have hxE : ((xE : ↥(⊤ : Subgroup H)) : H) = x := rfl
          rw [hxE]
          group
        rw [hx_eq]
        exact hxyK
      have himage_le_fixed : ∀ v ∈ (((K.subgroupOf ⊤).subgroupOf E').map β),
          Multiplicative.toAdd v ∈ SL2Nat.fixedSub R := by
        rintro v ⟨y, hy, rfl⟩
        have hyR : ((y : ↥(⊤ : Subgroup H)) : H) ∈
            relCent E (centerOf (⊤ : Subgroup H)) A :=
          hK_le (Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hy))
        exact (mem_relCent_iff_beta A hA y).mp hyR
      have hfixed_le_image : ∀ w ∈ SL2Nat.fixedSub R, Multiplicative.ofAdd w ∈
          (((K.subgroupOf ⊤).subgroupOf E').map β) := by
        intro w hw
        have hw' : w ∈ SL2Nat.commSub R := by rwa [hcomm_eq]
        obtain ⟨y, hyK, hyβ⟩ := hP w hw' 1
        refine ⟨y, ?_, ?_⟩
        · exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hyK)
        · apply Multiplicative.toAdd.injective
          rw [hyβ]
          simp
      have hcard_image : Nat.card ↥(((K.subgroupOf ⊤).subgroupOf E').map β) =
          Nat.card ↥(SL2Nat.fixedSub R) := by
        refine Nat.card_congr ?_
        refine
          { toFun := fun v => ⟨Multiplicative.toAdd v.1, himage_le_fixed v.1 v.2⟩
            invFun := fun w => ⟨Multiplicative.ofAdd w.1, hfixed_le_image w.1 w.2⟩
            left_inv := fun v => by apply Subtype.ext; simp
            right_inv := fun w => by apply Subtype.ext; simp }
      have hK_index : (centerOf (⊤ : Subgroup H)).relIndex K = Nat.card F := by
        rw [← natCard_imgβ_eq_relIndex K hZ_le_K hK_le_E, hcard_image,
          SL2Nat.natCard_fixedSub_of_card hR hRcard]
      have hR_index : (centerOf (⊤ : Subgroup H)).relIndex
          (relCent E (centerOf (⊤ : Subgroup H)) A) = Nat.card F := by
        rw [← natCard_imgβ_eq_relIndex (relCent E (centerOf (⊤ : Subgroup H)) A)
          (hZc_relCent A) (fun x hx => hx.1), natCard_img_relCent A hA,
          SL2Nat.natCard_fixedSub_of_card hR hRcard]
      have hcardK : Nat.card ↥K = Nat.card ↥(relCent E (centerOf (⊤ : Subgroup H)) A) := by
        have h1 := Subgroup.relIndex_mul_card (centerOf (⊤ : Subgroup H)) K
        have h2 := Subgroup.relIndex_mul_card (centerOf (⊤ : Subgroup H))
          (relCent E (centerOf (⊤ : Subgroup H)) A)
        rw [inf_eq_left.mpr hZ_le_K] at h1
        rw [inf_eq_left.mpr (hZc_relCent A)] at h2
        rw [hK_index] at h1
        rw [hR_index] at h2
        exact h1.symm.trans h2
      have hK_eq : K = relCent E (centerOf (⊤ : Subgroup H)) A := by
        refine Subgroup.eq_of_le_of_card_ge hK_le ?_
        rw [hcardK]
      exact hK_eq
    · intro A A' hA hA' hAA'
      let R : Subgroup SL(2, F) := (A.subgroupOf ⊤).map α
      let R' : Subgroup SL(2, F) := (A'.subgroupOf ⊤).map α
      have hR : IsPGroup 2 R := by
        have h1 : IsPGroup 2 ↥(A.subgroupOf ⊤) :=
          hA.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe (le_top : A ≤ ⊤)).symm
        exact IsPGroup.map h1 α
      have hRcard : Nat.card R = Nat.card F := card_map_sylow_of_natCoord hA α hα
      have hR' : IsPGroup 2 R' := by
        have h1 : IsPGroup 2 ↥(A'.subgroupOf ⊤) :=
          hA'.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe (le_top : A' ≤ ⊤)).symm
        exact IsPGroup.map h1 α
      have hR'card : Nat.card R' = Nat.card F :=
        card_map_sylow_of_natCoord hA' α hα
      obtain ⟨v, hv, hWline⟩ := SL2Nat.fixedSub_eq_span_of_card hR hRcard
      obtain ⟨v', hv', hW'line⟩ := SL2Nat.fixedSub_eq_span_of_card hR' hR'card
      let W : Submodule F (Fin 2 → F) := SL2Nat.fixedSub R
      let W' : Submodule F (Fin 2 → F) := SL2Nat.fixedSub R'
      have hWv : W = Submodule.span F {v} := by
        change SL2Nat.fixedSub R = _; exact hWline
      have hW'v : W' = Submodule.span F {v'} := by
        change SL2Nat.fixedSub R' = _; exact hW'line
      have hfinW : Module.finrank F ↥W = 1 := by
        change Module.finrank F ↥(SL2Nat.fixedSub R) = 1
        exact SL2Nat.finrank_fixedSub_of_card hR hRcard
      have hfinW' : Module.finrank F ↥W' = 1 := by
        change Module.finrank F ↥(SL2Nat.fixedSub R') = 1
        exact SL2Nat.finrank_fixedSub_of_card hR' hR'card
      have hfinV : Module.finrank F (Fin 2 → F) = 2 := by
        simpa using (Module.finrank_fin_fun F (n := 2))
      have hWne : W ≠ W' := by
        intro hEq
        have hvW : v ∈ W := by
          rw [hWv]; exact Submodule.subset_span rfl
        have hvW' : v ∈ W' := by rwa [hEq] at hvW
        have hvWfix : v ∈ SL2Nat.fixedSub R := by
          change v ∈ W
          exact hvW
        have hRsub : R ≤ sl2Stab v := by
          intro r hr
          rw [mem_sl2Stab, ← SL2Nat.lin_apply]
          exact (SL2Nat.mem_fixedSub).mp hvWfix r hr
        have hR'sub : R' ≤ sl2Stab v := by
          intro r hr
          rw [mem_sl2Stab, ← SL2Nat.lin_apply]
          exact (SL2Nat.mem_fixedSub).mp (by change v ∈ W'; exact hvW') r hr
        have hReq : R = sl2Stab v := by
          refine Subgroup.eq_of_le_of_card_ge hRsub ?_
          rw [card_sl2Stab hv, hRcard]
        have hR'eq : R' = sl2Stab v := by
          refine Subgroup.eq_of_le_of_card_ge hR'sub ?_
          rw [card_sl2Stab hv, hR'card]
        have hRR' : R = R' := by rw [hReq, hR'eq]
        apply hAA'
        intro a ha
        let aH : ↥(⊤ : Subgroup H) := ⟨a, hA.1 ha⟩
        have haR : α aH ∈ R :=
          Subgroup.mem_map_of_mem α (Subgroup.mem_subgroupOf.mpr ha)
        have haR' : α aH ∈ R' := by rwa [hRR'] at haR
        obtain ⟨a', ha'mem, ha'eq⟩ := Subgroup.mem_map.mp haR'
        have ha'A : (a' : H) ∈ A' := Subgroup.mem_subgroupOf.mp ha'mem
        have hker : a'⁻¹ * aH ∈ α.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, ha'eq, inv_mul_cancel]
        rw [alpha_ker_eq_pCoreOf hPush α hαk] at hker
        have hE : ((a'⁻¹ * aH : ↥(⊤ : Subgroup H)) : H) ∈ E :=
          Subgroup.mem_subgroupOf.mp hker
        have h1 : (a' : H) ∈ A' ⊔ E := Subgroup.mem_sup_left ha'A
        have h2 : ((a'⁻¹ * aH : ↥(⊤ : Subgroup H)) : H) ∈ A' ⊔ E :=
          Subgroup.mem_sup_right hE
        have heq : a = (a' : H) * ((a'⁻¹ * aH : ↥(⊤ : Subgroup H)) : H) := by
          change a = (a' : H) * ((a' : H)⁻¹ * a)
          group
        rw [heq]
        exact (A' ⊔ E).mul_mem h1 h2
      have hinf : W ⊓ W' = ⊥ := by
        have hlt : W ⊓ W' < W := by
          refine lt_of_le_of_ne inf_le_left ?_
          intro hEq
          have hle : W ≤ W' := by rw [← hEq]; exact inf_le_right
          have hWeq : W = W' :=
            Submodule.eq_of_le_of_finrank_eq hle (by rw [hfinW, hfinW'])
          exact hWne hWeq
        have hlt' := Submodule.finrank_lt_finrank_of_lt hlt
        have hzero : Module.finrank F ↥(W ⊓ W') = 0 := by omega
        exact (Submodule.finrank_eq_zero).mp hzero
      have hsup : W ⊔ W' = ⊤ := by
        have hlt : W < W ⊔ W' := by
          refine lt_of_le_of_ne le_sup_left ?_
          intro hEq
          have hle : W' ≤ W := by
            calc W' ≤ W ⊔ W' := le_sup_right
              _ = W := hEq.symm
          have hWeq : W' = W :=
            Submodule.eq_of_le_of_finrank_eq hle (by rw [hfinW', hfinW])
          exact hWne hWeq.symm
        have hlt' := Submodule.finrank_lt_finrank_of_lt hlt
        have hge : 2 ≤ Module.finrank F ↥(W ⊔ W') := by omega
        have hle : Module.finrank F ↥(W ⊔ W') ≤ 2 := by
          have hmono := Submodule.finrank_mono (le_top : W ⊔ W' ≤ ⊤)
          rw [finrank_top, hfinV] at hmono
          exact hmono
        have heq : Module.finrank F ↥(W ⊔ W') = 2 := le_antisymm hle hge
        exact Submodule.eq_top_of_finrank_eq (by rw [heq, hfinV])
      have hinf_rel : relCent E (centerOf (⊤ : Subgroup H)) A ⊓
          relCent E (centerOf (⊤ : Subgroup H)) A' = centerOf (⊤ : Subgroup H) := by
        refine le_antisymm ?_ (le_inf (hZc_relCent A) (hZc_relCent A'))
        intro x hx
        rw [Subgroup.mem_inf] at hx
        let xE : ↥E' := ⟨⟨x, Subgroup.mem_top x⟩, hx.1.1⟩
        have hxW : Multiplicative.toAdd (β xE) ∈ W := by
          change Multiplicative.toAdd (β xE) ∈ SL2Nat.fixedSub R
          exact (mem_relCent_iff_beta A hA xE).mp hx.1
        have hxW' : Multiplicative.toAdd (β xE) ∈ W' := by
          change Multiplicative.toAdd (β xE) ∈ SL2Nat.fixedSub R'
          exact (mem_relCent_iff_beta A' hA' xE).mp hx.2
        have hbot : Multiplicative.toAdd (β xE) ∈ (⊥ : Submodule F (Fin 2 → F)) := by
          rw [← hinf]
          exact Submodule.mem_inf.mpr ⟨hxW, hxW'⟩
        have hzero : Multiplicative.toAdd (β xE) = 0 := (Submodule.mem_bot F).mp hbot
        have hβ1 : β xE = 1 :=
          Multiplicative.toAdd.injective (by simpa using hzero)
        have hker : xE ∈ β.ker := MonoidHom.mem_ker.mpr hβ1
        rw [hβkerZ'] at hker
        exact Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hker)
      have hsup_rel : relCent E (centerOf (⊤ : Subgroup H)) A ⊔
          relCent E (centerOf (⊤ : Subgroup H)) A' = E := by
        refine le_antisymm ?_ ?_
        · exact sup_le (fun x hx => hx.1) (fun x hx => hx.1)
        · intro x hx
          let xE : ↥E' := ⟨⟨x, Subgroup.mem_top x⟩, hx⟩
          have hxW : Multiplicative.toAdd (β xE) ∈ W ⊔ W' := by
            rw [hsup]
            exact Submodule.mem_top
          obtain ⟨w1, hw1, w2, hw2, hw_eq⟩ := Submodule.mem_sup.mp hxW
          obtain ⟨y1, hy1⟩ := hβ (Multiplicative.ofAdd w1)
          obtain ⟨y2, hy2⟩ := hβ (Multiplicative.ofAdd w2)
          have hy1R : ((y1 : ↥(⊤ : Subgroup H)) : H) ∈
              relCent E (centerOf (⊤ : Subgroup H)) A := by
            refine (mem_relCent_iff_beta A hA y1).mpr ?_
            rw [hy1]
            simpa using hw1
          have hy2R : ((y2 : ↥(⊤ : Subgroup H)) : H) ∈
              relCent E (centerOf (⊤ : Subgroup H)) A' := by
            refine (mem_relCent_iff_beta A' hA' y2).mpr ?_
            rw [hy2]
            simpa using hw2
          have hβxy : β (y1 * y2) = β xE := by
            apply Multiplicative.toAdd.injective
            rw [map_mul]
            simp [hy1, hy2, hw_eq]
          have hZ : ((xE : ↥(⊤ : Subgroup H)) : H) *
              (((y1 * y2 : ↥E') : ↥(⊤ : Subgroup H)) : H)⁻¹ ∈
              centerOf (⊤ : Subgroup H) :=
            beta_eq_mul_inv_mem_Z xE (y1 * y2) hβxy.symm
          have hprod : (((y1 * y2 : ↥E') : ↥(⊤ : Subgroup H)) : H) ∈
              relCent E (centerOf (⊤ : Subgroup H)) A ⊔
                relCent E (centerOf (⊤ : Subgroup H)) A' := by
            have hy1sup : ((y1 : ↥(⊤ : Subgroup H)) : H) ∈
                relCent E (centerOf (⊤ : Subgroup H)) A ⊔
                  relCent E (centerOf (⊤ : Subgroup H)) A' :=
              Subgroup.mem_sup_left hy1R
            have hy2sup : ((y2 : ↥(⊤ : Subgroup H)) : H) ∈
                relCent E (centerOf (⊤ : Subgroup H)) A ⊔
                  relCent E (centerOf (⊤ : Subgroup H)) A' :=
              Subgroup.mem_sup_right hy2R
            have hmul := (relCent E (centerOf (⊤ : Subgroup H)) A ⊔
              relCent E (centerOf (⊤ : Subgroup H)) A').mul_mem hy1sup hy2sup
            convert hmul using 1
          have hmem : (((xE : ↥(⊤ : Subgroup H)) : H) *
              (((y1 * y2 : ↥E') : ↥(⊤ : Subgroup H)) : H)⁻¹) *
              (((y1 * y2 : ↥E') : ↥(⊤ : Subgroup H)) : H) ∈
              relCent E (centerOf (⊤ : Subgroup H)) A ⊔
                relCent E (centerOf (⊤ : Subgroup H)) A' := by
            refine (relCent E (centerOf (⊤ : Subgroup H)) A ⊔
              relCent E (centerOf (⊤ : Subgroup H)) A').mul_mem ?_ hprod
            exact (le_trans (hZc_relCent A) le_sup_left) hZ
          have hx_eq : x = (((xE : ↥(⊤ : Subgroup H)) : H) *
              (((y1 * y2 : ↥E') : ↥(⊤ : Subgroup H)) : H)⁻¹) *
              (((y1 * y2 : ↥E') : ↥(⊤ : Subgroup H)) : H) := by
            have hxE : ((xE : ↥(⊤ : Subgroup H)) : H) = x := rfl
            rw [hxE]
            group
          rw [hx_eq]
          exact hmem
      exact ⟨hinf_rel, hsup_rel⟩
    · intro g hg hodd hgE e heE hcomm
      let g' : ↥(⊤ : Subgroup H) := ⟨g, hg⟩
      let e' : ↥E' := ⟨⟨e, Subgroup.mem_top e⟩, heE⟩
      let e'' : ↥E' := ⟨g' * (e' : ↥(⊤ : Subgroup H)) * g'⁻¹, Subgroup.mem_subgroupOf.mpr
        ((Subgroup.mem_normalizer_iff.mp (hPush.normal g'.2) (e' : ↥(⊤ : Subgroup H))).mp
          (Subgroup.mem_subgroupOf.mp e'.2))⟩
      have hcommZ : ⁅e, g⁆ ∈ centerOf (⊤ : Subgroup H) := hcomm
      have hker : (e'' * e'⁻¹) ∈ β.ker := by
        rw [hβkerZ']
        refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr ?_)
        have h1 : (((e'' * e'⁻¹ : ↥E') : ↥(⊤ : Subgroup H)) : H) =
            g * e * g⁻¹ * e⁻¹ := rfl
        have h2 : g * e * g⁻¹ * e⁻¹ = ⁅e, g⁆⁻¹ := by
          rw [commutatorElement_def]
          group
        rw [h1, h2]
        exact (centerOf (⊤ : Subgroup H)).inv_mem hcommZ
      have heqβ : β e'' = β e' := by
        have h1 : β (e'' * e'⁻¹) = 1 := MonoidHom.mem_ker.mp hker
        rw [map_mul, map_inv] at h1
        exact mul_inv_eq_one.mp h1
      have hfix : (α g' : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β e')) =
          Multiplicative.toAdd (β e') := by
        have h := hβe g' e' e'' rfl
        rw [heqβ] at h
        exact h.symm
      have hodd' : Odd (orderOf g') := by simpa [g', Subgroup.orderOf_mk] using hodd
      have hoddα : Odd (orderOf (α g')) := hodd'.of_dvd_nat (orderOf_map_dvd α g')
      have hαg : α g' ≠ 1 := by
        intro h
        apply hgE
        have hmem : g' ∈ α.ker := MonoidHom.mem_ker.mpr h
        rwa [alpha_ker_eq_pCoreOf hPush α hαk, Subgroup.mem_subgroupOf] at hmem
      have hβe0 : β e' = 1 := by
        by_contra hne
        have hv : Multiplicative.toAdd (β e') ≠ 0 := by
          intro h0
          exact hne (Multiplicative.toAdd.injective h0)
        exact hαg (SL2Nat.eq_one_of_odd_order_of_fixed hv hoddα hfix)
      have hmemZ : e' ∈ β.ker := MonoidHom.mem_ker.mpr hβe0
      rw [hβkerZ'] at hmemZ
      exact Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hmemZ)
    · intro A hZA hAE hnorm
      have h := irr_of_natCoord hPush α β hα hβe hβk hAE hnorm
      rw [hZ0eq] at h
      rcases h with hle | hle
      · left
        exact le_antisymm hle hZA
      · right
        refine le_antisymm hAE ?_
        rwa [sup_eq_left.mpr hZA] at hle
  · intro hbot
    have hbot' : ⁅E, pResidualOf 2 (⊤ : Subgroup H)⁆ = ⊥ := by
      rwa [pResidualOf_eq_oTwoRes]
    have hOle : pResidualOf 2 (⊤ : Subgroup H) ≤ E := by
      change pResidualOf 2 (⊤ : Subgroup H) ≤ pCoreOf 2 (⊤ : Subgroup H)
      rw [← hPush.cent_eq]
      refine le_inf (pResidualOf_le_self (⊤ : Subgroup H)) ?_
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have hcomm : ⁅e, x⁆ = 1 := by
        have hmem : ⁅e, x⁆ ∈ ⁅E, pResidualOf 2 (⊤ : Subgroup H)⁆ :=
          Subgroup.commutator_mem_commutator he hx
        rw [hbot'] at hmem
        exact Subgroup.mem_bot.mp hmem
      exact commutatorElement_eq_one_iff_mul_comm.mp hcomm
    have htopE : (⊤ : Subgroup H) ≤ E := by
      rw [← hsup]
      exact sup_le hOle le_rfl
    have hEtop : E = ⊤ := le_antisymm (CFSG.LieType.BorelTits.pCoreOf_le 2 (⊤ : Subgroup H)) htopE
    have hcore : CFSG.pCore 2 ↥(⊤ : Subgroup H) = ⊤ := by
      have h1 : E.subgroupOf (⊤ : Subgroup H) = CFSG.pCore 2 ↥(⊤ : Subgroup H) := by
        change (pCoreOf 2 (⊤ : Subgroup H)).subgroupOf (⊤ : Subgroup H) = _
        rw [pCoreOf]
        exact Subgroup.comap_map_eq_self_of_injective (⊤ : Subgroup H).subtype_injective _
      rw [← h1, hEtop]
      exact Subgroup.subgroupOf_self ⊤
    haveI : Nontrivial (oTwoQuot ↥(⊤ : Subgroup H)) := by
      obtain ⟨e⟩ := hq
      have hF4 : 4 ≤ Nat.card (GaloisField 2 n) := by
        rw [GaloisField.card 2 n (by omega)]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      haveI : Nontrivial (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
        (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hF4).toNontrivial
      exact e.toEquiv.nontrivial
    haveI : Subsingleton (oTwoQuot ↥(⊤ : Subgroup H)) := by
      show Subsingleton (↥(⊤ : Subgroup H) ⧸ CFSG.pCore 2 ↥(⊤ : Subgroup H))
      rw [hcore]
      exact QuotientGroup.subsingleton_quotient_top
    exact (not_subsingleton (oTwoQuot ↥(⊤ : Subgroup H))) inferInstance

end FiniteTop

theorem natQuot_of_isL2Quot {G : Type} [Group G] {L P : Subgroup G} [Finite ↥L] {n : ℕ}
    (hn : 1 ≤ n) (hc : CharTwo L) (hq : IsL2Quot n (oTwoQuot ↥L))
    (hP : IsSylowTwoOf P L) (hnc : NoCharNormal P L) (he : IsElemAbelian 2 (pCoreOf 2 L)) :
    NatQuot L (pCoreOf 2 L) (centerOf L) n ∧ ⁅pCoreOf 2 L, pResidualOf 2 L⁆ ≠ ⊥ := by
  rcases eq_or_lt_of_le hn with hn1 | hn1
  ·
    subst hn1
    exact natQuot_of_baumann_one hc hq hP hnc he
  ·
    have hn2 : 2 ≤ n := hn1
    let E : Subgroup G := pCoreOf 2 L
    let Z : Subgroup G := centerOf L
    have hEtop : pCoreOf 2 (⊤ : Subgroup ↥L) = E.subgroupOf L := by
      ext x
      rw [CFSG.Quasithin.F53Push.pCoreOf_top_eq, ← CFSG.Quasithin.F53Push.mem_pCoreOf_iff x,
        Subgroup.mem_subgroupOf]
    have hZtop : centerOf (⊤ : Subgroup ↥L) = Z.subgroupOf L := by
      ext x
      change x ∈ (⊤ : Subgroup ↥L) ⊓ Subgroup.centralizer (⊤ : Set ↥L) ↔
        x ∈ (L ⊓ Subgroup.centralizer (L : Set G)).subgroupOf L
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      constructor
      · rintro ⟨-, hx⟩
        refine ⟨x.2, ?_⟩
        change (x : G) ∈ Subgroup.centralizer (L : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        simpa using congrArg Subtype.val (hx ⟨y, hy⟩ (Subgroup.mem_top _))
      · rintro ⟨-, hx⟩
        refine ⟨Subgroup.mem_top x, ?_⟩
        change x ∈ Subgroup.centralizer (⊤ : Set ↥L)
        rw [Subgroup.mem_centralizer_iff]
        intro y _
        apply Subtype.ext
        simpa using hx y y.2
    have hctop : CharTwo (⊤ : Subgroup ↥L) := by
      simpa using CFSG.Quasithin.EmptyFaithfulMultiple.L15422.charTwo_subgroupOf
        (X := L) (L := L) le_rfl hc
    have hqtop : IsL2Quot n (oTwoQuot ↥(⊤ : Subgroup ↥L)) := by
      obtain ⟨eL⟩ := hq
      exact ⟨(CFSG.Quasithin.F112R.oTwoQuotCongr
        (Subgroup.topEquiv (G := ↥L))).trans eL⟩
    have hPtop : IsSylowTwoOf (P.subgroupOf L) (⊤ : Subgroup ↥L) :=
      CFSG.Quasithin.X1512.sylow_subgroupOf_top hP
    have hnctop : NoCharNormal (P.subgroupOf L) (⊤ : Subgroup ↥L) :=
      noCharNormal_subgroupOf hP.1 hnc
    have hetop : IsElemAbelian 2 (pCoreOf 2 (⊤ : Subgroup ↥L)) := by
      have h : IsElemAbelian 2 (E.subgroupOf L) := by
        refine ⟨?_, ?_⟩
        · exact IsMulCommutative.of_comm (fun x y => by
            apply Subtype.ext
            apply Subtype.ext
            simpa using congrArg Subtype.val (he.1.is_comm.comm
              ⟨((x : ↥L) : G), Subgroup.mem_subgroupOf.mp x.2⟩
              ⟨((y : ↥L) : G), Subgroup.mem_subgroupOf.mp y.2⟩))
        · intro x hx
          have hxG : (x : G) ∈ E := Subgroup.mem_subgroupOf.mp hx
          apply Subtype.ext
          simpa using he.2 (x : G) hxG
      simpa [hEtop] using h
    obtain ⟨hntop, hcommtop⟩ :=
      natQuot_of_isL2Quot_top hn2 hctop hqtop hPtop hnctop hetop
    have hinput : NatQuot (⊤ : Subgroup ↥L) (E.subgroupOf L) (Z.subgroupOf L) n := by
      simpa [hEtop, hZtop] using hntop
    have hL : NatQuot L E Z n :=
      natQuot_subgroupOf (CFSG.LieType.BorelTits.pCoreOf_le 2 L)
        (fun x hx => (Subgroup.mem_inf.mp hx).1) hinput
    have hRtop : oTwoRes (⊤ : Subgroup ↥L) = (oTwoUpper L).subgroupOf L := by
      rw [oTwoRes_eq_oTwoUpper, oTwoUpper_top_subgroupOf]
    refine ⟨?_, ?_⟩
    · simpa [E, Z] using hL
    · intro hbot
      have hbotO : ⁅E, oTwoUpper L⁆ = ⊥ := by
        rw [eq_bot_iff]
        calc ⁅E, oTwoUpper L⁆ ≤ ⁅E, pResidualOf 2 L⁆ :=
              Subgroup.commutator_mono le_rfl (oTwoUpper_le_pResidualOf L)
          _ = ⊥ := hbot
      have hcommSub : ⁅pCoreOf 2 (⊤ : Subgroup ↥L), oTwoRes (⊤ : Subgroup ↥L)⁆ =
          (⁅E, oTwoUpper L⁆).subgroupOf L := by
        rw [hEtop, hRtop,
          CFSG.GroupTheory.commutator_subgroupOf_eq (CFSG.LieType.BorelTits.pCoreOf_le 2 L)
            (oTwoUpper_le L)]
      apply hcommtop
      rw [hcommSub, hbotO]
      simp

end CFSG.Quasithin.St84

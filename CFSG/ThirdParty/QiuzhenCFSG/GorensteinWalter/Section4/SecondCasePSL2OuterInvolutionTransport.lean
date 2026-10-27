module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2Action
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.CentralizerLiftOfOddCenter
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Theorem26ComponentTransport
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Outer-involution reflected commutator transport in the second PSL₂ case

This module transports the odd reflected-torus calculation from `PGL₂(K)`
back to the selected ambient component.  No centerless-cover hypothesis is
used: the odd center is removed by a fixed-representative lift and by the
fact that the distinguished involution both fixes and inverts the residual
central kernel.
-/

noncomputable section

open Matrix
open scoped commutatorElement IsMulCommutative

namespace CFSG.GorensteinWalter

universe u

private lemma zpow_eq_one_or_self_of_sq_eq_one_outer
    {H : Type u} [Group H] {t : H}
    (ht : t * t = 1) (k : ℤ) : t ^ k = 1 ∨ t ^ k = t := by
  by_cases ht1 : t = 1
  · left
    simp [ht1]
  · have hord : orderOf t = 2 :=
      (orderOf_eq_prime_iff (x := t)).2 ⟨by simpa [pow_two] using ht, ht1⟩
    rw [← zpow_mod_orderOf, hord]
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · left
      change k % (2 : ℤ) = 0 at hk
      simp [hk]
    · right
      change k % (2 : ℤ) = 1 at hk
      simp [hk]

/-- The canonical component map to `PGL₂(K)` obtained from the selected
central quotient model. -/
public def secondCasePSL2ComponentPGLMap
    {G : Type u} [Group G] [Finite G]
    {c : CentralizerSetup G} {w : SecondCaseWitness c}
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (ad : SecondCasePSL2ActionData w d K) : d.E →* PGL2 K :=
  Matrix.ProjectiveSpecialLinearGroup.toPGL.comp
    (ad.modelEquiv.some.toMonoidHom.comp
      (QuotientGroup.mk' (Subgroup.center d.E)))

/-- Evaluation of the component-to-`PGL₂` map. -/
public theorem secondCase_psl2_componentPGLMap_apply
    {G : Type u} [Group G] [Finite G]
    {c : CentralizerSetup G} {w : SecondCaseWitness c}
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (ad : SecondCasePSL2ActionData w d K) (x : d.E) :
    secondCasePSL2ComponentPGLMap d K ad x =
      Matrix.ProjectiveSpecialLinearGroup.toPGL
        (ad.modelEquiv.some
          (QuotientGroup.mk' (Subgroup.center d.E) x)) := by
  rfl

public theorem secondCase_psl2_action_on_component_eq_inl
    {G : Type u} [Group G] [Finite G]
    {c : CentralizerSetup G} (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (ad : SecondCasePSL2ActionData w d K)
    (x : d.E) :
    ad.f ⟨x, d.E_component.1 x.2⟩ =
      SemidirectProduct.inl (secondCasePSL2ComponentPGLMap d K ad x) := by
  let q : d.E →* d.E ⧸ Subgroup.center d.E :=
    QuotientGroup.mk' (Subgroup.center d.E)
  let x0 : PSL2 K := ad.modelEquiv.some (q x)
  have hact :
      pGammaL2ToMulAutPSL2 K ad.primePower ad.fieldCardGtThree
          (ad.f ⟨x, d.E_component.1 x.2⟩) =
        MulAut.conj x0 := by
    apply MulEquiv.ext
    intro z
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective
      (Subgroup.center d.E) (ad.modelEquiv.some.symm z)
    have hz : z = ad.modelEquiv.some (q y) := by
      calc
        z = ad.modelEquiv.some (ad.modelEquiv.some.symm z) := by simp
        _ = ad.modelEquiv.some (q y) := congrArg ad.modelEquiv.some hy.symm
    rw [hz]
    rw [ad.action_eq ⟨x, d.E_component.1 x.2⟩ y]
    have hq : q ⟨(x : G) * (y : G) * (x : G)⁻¹,
          d.E_normal.2 (x : G) (d.E_component.1 x.2) (y : G) y.2⟩ =
        q x * q y * (q x)⁻¹ := by
      have hsub :
          (⟨(x : G) * (y : G) * (x : G)⁻¹,
            d.E_normal.2 (x : G) (d.E_component.1 x.2) (y : G) y.2⟩ : d.E) =
            x * y * x⁻¹ := by
        apply Subtype.ext
        rfl
      rw [hsub, map_mul, map_mul, map_inv]
    rw [hq]
    simp [x0, MulAut.conj_apply, mul_assoc]
  have hinl :
      pGammaL2ToMulAutPSL2 K ad.primePower ad.fieldCardGtThree
          (SemidirectProduct.inl
            (Matrix.ProjectiveSpecialLinearGroup.toPGL x0)) =
        MulAut.conj x0 := by
    rw [pGammaL2ToMulAutPSL2_inl]
    exact pgl2InnerAutPSL2_toPGL K ad.primePower ad.fieldCardGtThree x0
  have h := pGammaL2ToMulAutPSL2_injective K ad.primePower
    ad.fieldCardGtThree (hact.trans hinl.symm)
  simpa [secondCasePSL2ComponentPGLMap, q, x0] using h

/-- Let `r ∈ M \ E` be an involution commuting with the distinguished
involution `t`, and suppose their images under the second-case action are
simultaneously aligned with the outer/inner pair of a fixed reflected-torus
package in `PGL₂(K)`.  Then

`R = [⟨t⟩, C_E(r)]`

is cyclic, has the odd complementary-half cardinality, and is inverted by
`t`.  The explicit model alignment is the narrow datum not chosen by
`SecondCasePSL2ActionData` itself. -/
public theorem secondCase_psl2_outer_involution_transport
    {G : Type u} [Group G] [Finite G]
    {c : CentralizerSetup G} (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (ad : SecondCasePSL2ActionData w d K)
    (P : Sylow 2 (PGL2 K)) {m : ℕ}
    (eP : P ≃* DihedralGroup (2 ^ m))
    (T : PGL2LowReflectedToriData K P eP)
    (r : w.M) (hrI : IsInvolution (r : G))
    (hrE : (r : G) ∉ d.E) (htr : Commute c.t (r : G))
    (r0 t0 a : PGL2 K)
    (hr0 : ad.f r = SemidirectProduct.inl r0)
    (ht0 : ad.f ⟨c.t, d.E_component.1 d.t_mem_E⟩ =
      SemidirectProduct.inl t0)
    (hrT : r0 = a * T.s * a⁻¹)
    (htT : t0 = a * T.t * a⁻¹) :
    let CE : Subgroup G :=
      Subgroup.centralizer ({(r : G)} : Set G) ⊓ d.E
    let R : Subgroup G := ⁅Subgroup.zpowers c.t, CE⁆
    IsCyclic R ∧ Odd (Nat.card R) ∧
      Nat.card R = Nat.card T.U / 2 ∧
      (∀ x : G, x ∈ R → c.t * x * c.t⁻¹ = x⁻¹) ∧
      (R.subgroupOf d.E).map (secondCasePSL2ComponentPGLMap d K ad) =
        T.R.map (MulAut.conj a).toMonoidHom := by
  classical
  intro CE R
  have _hrE := hrE
  have _htr := htr
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  let q : d.E →* d.E ⧸ Subgroup.center d.E :=
    QuotientGroup.mk' (Subgroup.center d.E)
  let φ : d.E →* PGL2 K := secondCasePSL2ComponentPGLMap d K ad
  have hφf (x : d.E) :
      ad.f ⟨x, d.E_component.1 x.2⟩ = SemidirectProduct.inl (φ x) := by
    simpa [φ] using secondCase_psl2_action_on_component_eq_inl w d K ad x
  have hφrange : φ.range = commutator (PGL2 K) := by
    rw [pgl2_commutator_eq_psl2_range_of_card_gt_three K ad.primePower
      ad.fieldCardGtThree]
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      exact ⟨ad.modelEquiv.some (q x), rfl⟩
    · rintro y ⟨z, rfl⟩
      obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective
        (Subgroup.center d.E) (ad.modelEquiv.some.symm z)
      refine ⟨x, ?_⟩
      change Matrix.ProjectiveSpecialLinearGroup.toPGL
        (ad.modelEquiv.some (q x)) =
          Matrix.ProjectiveSpecialLinearGroup.toPGL z
      rw [hx]
      simp
  have hφker : φ.ker = Subgroup.center d.E := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have hx' : ad.modelEquiv.some (q x) = 1 :=
        Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (by
          change Matrix.ProjectiveSpecialLinearGroup.toPGL
            (ad.modelEquiv.some (q x)) =
              Matrix.ProjectiveSpecialLinearGroup.toPGL 1
          change Matrix.ProjectiveSpecialLinearGroup.toPGL
            (ad.modelEquiv.some
              (QuotientGroup.mk' (Subgroup.center d.E) x)) = 1 at hx
          simpa [q] using hx)
      have hq : q x = 1 := ad.modelEquiv.some.injective (by simpa using hx')
      exact (QuotientGroup.eq_one_iff (N := Subgroup.center d.E) x).mp hq
    · intro hx
      have hq : q x = 1 :=
        (QuotientGroup.eq_one_iff (N := Subgroup.center d.E) x).mpr hx
      change Matrix.ProjectiveSpecialLinearGroup.toPGL
        (ad.modelEquiv.some (q x)) = 1
      rw [hq]
      simp
  let tE : d.E := ⟨c.t, d.t_mem_E⟩
  have hφt : φ tE = t0 := by
    exact SemidirectProduct.inl_injective ((hφf tE).symm.trans ht0)
  have htE : Subgroup.zpowers c.t ≤ d.E :=
    Subgroup.zpowers_le.mpr d.t_mem_E
  have hCEleE : CE ≤ d.E := inf_le_right
  have hRleE : R ≤ d.E :=
    commutator_le_of_le_t26 (Subgroup.zpowers c.t) CE d.E htE hCEleE
  let TE : Subgroup d.E := Subgroup.zpowers tE
  let CEE : Subgroup d.E := CE.subgroupOf d.E
  let RE : Subgroup d.E := R.subgroupOf d.E
  have hTEmap : TE.map d.E.subtype = Subgroup.zpowers c.t := by
    simp [TE, tE, MonoidHom.map_zpowers]
  have hCEEmap : CEE.map d.E.subtype = CE := by
    simpa [CEE] using Subgroup.map_subgroupOf_eq_of_le hCEleE
  have hREmapE : RE.map d.E.subtype = R := by
    simpa [RE] using Subgroup.map_subgroupOf_eq_of_le hRleE
  have hREeq : RE = ⁅TE, CEE⁆ := by
    apply Subgroup.map_subtype_inj.mp
    rw [Subgroup.map_commutator, hTEmap, hCEEmap, hREmapE]
  have hr2 : (r : G) * (r : G) = 1 := by
    simpa [pow_two] using hrI.2
  have hrN : (r : G) ∈ Subgroup.normalizer (d.E : Set G) :=
    le_normalizer_of_isNormalIn d.E_normal r.2
  have hrzpN : Subgroup.zpowers (r : G) ≤
      Subgroup.normalizer (d.E : Set G) := Subgroup.zpowers_le.mpr hrN
  have hZodd : Odd (Nat.card ((Subgroup.center d.E).map d.E.subtype)) := by
    rw [Subgroup.card_map_of_injective d.E.subtype_injective]
    exact d.center_odd
  have hCEEφ : CEE.map φ =
      commutator (PGL2 K) ⊓ Subgroup.centralizer ({r0} : Set (PGL2 K)) := by
    apply le_antisymm
    · rintro y ⟨x, hx, rfl⟩
      have hxCE : (x : G) ∈ CE := Subgroup.mem_subgroupOf.mp hx
      have hxcommG : (x : G) * (r : G) = (r : G) * (x : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp hxCE.1
      let xM : w.M := ⟨x, d.E_component.1 x.2⟩
      have hxcommM : xM * r = r * xM := Subtype.ext hxcommG
      have hfcomm := congrArg ad.f hxcommM
      have hmodelcomm : φ x * r0 = r0 * φ x := by
        have hinlEq :
            (SemidirectProduct.inl : PGL2 K →* PGammaL2 K) (φ x * r0) =
              (SemidirectProduct.inl : PGL2 K →* PGammaL2 K) (r0 * φ x) := by
          have hfx : ad.f xM = SemidirectProduct.inl (φ x) := by
            simpa [xM] using hφf x
          simpa only [map_mul, hfx, hr0] using hfcomm
        exact SemidirectProduct.inl_injective hinlEq
      exact ⟨by rw [← hφrange]; exact ⟨x, rfl⟩,
        Subgroup.mem_centralizer_singleton_iff.mpr hmodelcomm⟩
    · intro y hy
      have hyJ : y ∈ commutator (PGL2 K) := hy.1
      have hyC : y * r0 = r0 * y :=
        Subgroup.mem_centralizer_singleton_iff.mp hy.2
      have hyRange : y ∈ φ.range := by simpa [hφrange] using hyJ
      rcases hyRange with ⟨x, hxy⟩
      let xM : w.M := ⟨x, d.E_component.1 x.2⟩
      have hfcomm : ad.f xM * ad.f r = ad.f r * ad.f xM := by
        have hinlcomm := congrArg
          (SemidirectProduct.inl : PGL2 K →* PGammaL2 K) hyC
        rw [hφf x, hr0]
        simpa only [map_mul, hxy] using hinlcomm
      let defectM : w.M := r * xM * r⁻¹ * xM⁻¹
      have hdefectE : (defectM : G) ∈ d.E := by
        dsimp [defectM, xM]
        exact d.E.mul_mem
          (d.E_normal.2 (r : G) r.2 (x : G) x.2)
          (d.E.inv_mem x.2)
      let defectE : d.E := ⟨(defectM : G), hdefectE⟩
      have hfdefect : ad.f defectM = 1 := by
        dsimp [defectM]
        rw [map_mul, map_mul, map_mul, map_inv, map_inv]
        calc
          ad.f r * ad.f xM * (ad.f r)⁻¹ * (ad.f xM)⁻¹ =
              ad.f xM * ad.f r * (ad.f r)⁻¹ * (ad.f xM)⁻¹ := by
                rw [hfcomm.symm]
          _ = 1 := by group
      have hφdefect : φ defectE = 1 := by
        have hinl :
            (SemidirectProduct.inl : PGL2 K →* PGammaL2 K) (φ defectE) =
              (SemidirectProduct.inl : PGL2 K →* PGammaL2 K) 1 := by
          calc
            SemidirectProduct.inl (φ defectE) =
                ad.f ⟨defectE, d.E_component.1 defectE.2⟩ :=
              (hφf defectE).symm
            _ = ad.f defectM := by congr 1
            _ = 1 := hfdefect
            _ = SemidirectProduct.inl 1 := by simp
        exact SemidirectProduct.inl_injective hinl
      have hdefectZ : defectE ∈ Subgroup.center d.E := by
        rw [← hφker]
        exact hφdefect
      have hfixmod : (r : G) * (x : G) * (r : G)⁻¹ * (x : G)⁻¹ ∈
          (Subgroup.center d.E).map d.E.subtype := by
        refine Subgroup.mem_map.mpr ⟨defectE, hdefectZ, ?_⟩
        rfl
      obtain ⟨z, hzfix⟩ := centralizer_lift_of_odd_center d.E (r : G)
        hrzpN hr2 hZodd hfixmod
      rcases Subgroup.mem_map.mp z.2 with ⟨zE, hzEZ, hzval⟩
      let zxE : d.E := zE * x
      have hzxfix : (r : G) * (zxE : G) * (r : G)⁻¹ = (zxE : G) := by
        change (r : G) * ((zE : G) * (x : G)) * (r : G)⁻¹ =
          (zE : G) * (x : G)
        have hzval' : (zE : G) = (z : G) := hzval
        rw [hzval']
        exact hzfix
      have hzxCE : (zxE : G) ∈ CE := by
        constructor
        · apply Subgroup.mem_centralizer_singleton_iff.mpr
          have hrzx : (r : G) * (zxE : G) = (zxE : G) * (r : G) := by
            calc
              (r : G) * (zxE : G) =
                  ((r : G) * (zxE : G) * (r : G)⁻¹) * (r : G) := by group
              _ = (zxE : G) * (r : G) := by rw [hzxfix]
          exact hrzx.symm
        · exact zxE.2
      have hφz : φ zE = 1 := by
        exact MonoidHom.mem_ker.mp (by rw [hφker]; exact hzEZ)
      refine Subgroup.mem_map.mpr ⟨zxE, Subgroup.mem_subgroupOf.mpr hzxCE, ?_⟩
      calc
        φ zxE = φ zE * φ x := map_mul φ zE x
        _ = y := by rw [hφz, ← hxy, one_mul]
  have hTEφ : TE.map φ = Subgroup.zpowers t0 := by
    simp [TE, hφt, MonoidHom.map_zpowers]
  let C1 : Subgroup (PGL2 K) := ⁅Subgroup.zpowers t0,
    commutator (PGL2 K) ⊓ Subgroup.centralizer ({r0} : Set (PGL2 K))⁆
  have hREφ : RE.map φ = C1 := by
    rw [hREeq, Subgroup.map_commutator, hTEφ, hCEEφ]
  have hmodelCard := pgl2_reflected_outer_commutator_card ad.primePower
    ad.fieldCardGtThree P eP T (s0 := r0) (t0 := t0)
      ⟨a, hrT, htT⟩
  dsimp at hmodelCard
  have hmodelEq := pgl2_reflected_outer_commutator_eq_conj_R ad.primePower
    ad.fieldCardGtThree P eP T (a := a) (s0 := r0) (t0 := t0) hrT htT
  dsimp at hmodelEq
  have hC1cyc : IsCyclic C1 := by simpa [C1] using hmodelCard.1
  have hC1card : Nat.card C1 = Nat.card T.U / 2 := by
    simpa [C1] using hmodelCard.2
  have hC1eq : C1 = T.R.map (MulAut.conj a).toMonoidHom := by
    simpa [C1] using hmodelEq
  let ρ : RE →* C1 :=
    (φ.comp RE.subtype).codRestrict C1 (fun x => by
      have hx : φ (x : d.E) ∈ RE.map φ :=
        Subgroup.mem_map.mpr ⟨(x : d.E), x.2, rfl⟩
      rwa [hREφ] at hx)
  have hρkerCenter : ρ.ker ≤ Subgroup.center RE := by
    intro x hx
    have hφx : φ (x : d.E) = 1 := by
        have hx1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
        change (φ.comp RE.subtype) x = 1 at hx1
        simpa [MonoidHom.comp_apply] using hx1
    have hxCenterE : (x : d.E) ∈ Subgroup.center d.E := by
      rw [← hφker]
      exact hφx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : d.E => (z : G))
      (Subgroup.mem_center_iff.mp hxCenterE (y : d.E))
  let : IsCyclic C1 := hC1cyc
  let : CommGroup RE := commGroupOfCyclicCenterQuotient ρ hρkerCenter
  have hREcomm : ∀ x y : RE, x * y = y * x := fun x y => mul_comm x y
  have htt : c.t * c.t = 1 := by
    simpa [pow_two] using c.t_involution.2
  have htin : c.t⁻¹ = c.t := inv_eq_of_mul_eq_one_right htt
  let CInvRE : Subgroup RE :=
    { carrier := {x : RE | c.t * ((x : d.E) : G) * c.t⁻¹ = ((x : d.E) : G)⁻¹}
      one_mem' := by simp
      mul_mem' := by
        intro x y hx hy
        have hxy := hREcomm x y
        have hxyG : ((x : d.E) : G) * ((y : d.E) : G) =
            ((y : d.E) : G) * ((x : d.E) : G) := by
          exact congrArg (fun z : RE => ((z : d.E) : G)) hxy
        calc
          c.t * (((x : d.E) : G) * ((y : d.E) : G)) * c.t⁻¹ =
              (c.t * ((x : d.E) : G) * c.t⁻¹) *
                (c.t * ((y : d.E) : G) * c.t⁻¹) := by group
          _ = ((x : d.E) : G)⁻¹ * ((y : d.E) : G)⁻¹ := by rw [hx, hy]
          _ = (((x : d.E) : G) * ((y : d.E) : G))⁻¹ := by
            rw [hxyG]
            simp
      inv_mem' := by
        intro x hx
        change c.t * ((x : d.E) : G)⁻¹ * c.t⁻¹ =
          (((x : d.E) : G)⁻¹)⁻¹
        calc
          c.t * ((x : d.E) : G)⁻¹ * c.t⁻¹ =
              (c.t * ((x : d.E) : G) * c.t⁻¹)⁻¹ := by group
          _ = (((x : d.E) : G)⁻¹)⁻¹ := by rw [hx] }
  have hgen : ∀ x : d.E, x ∈ TE → ∀ y : d.E, y ∈ CEE →
      c.t * ((⁅x, y⁆ : d.E) : G) * c.t⁻¹ = ((⁅x, y⁆ : d.E) : G)⁻¹ := by
    intro x hx y hy
    rcases Subgroup.mem_zpowers_iff.mp hx with ⟨k, hk⟩
    have htE2 : tE * tE = 1 := by
      apply Subtype.ext
      exact htt
    rcases zpow_eq_one_or_self_of_sq_eq_one_outer htE2 k with hk1 | hkt
    · have hx1 : x = 1 := by simpa [hk] using hk1
      simp [hx1]
    · have hxt : x = tE := by simpa [hk] using hkt
      rw [hxt]
      rw [htin]
      change c.t * ⁅c.t, (y : G)⁆ * c.t = (⁅c.t, (y : G)⁆)⁻¹
      simp only [commutatorElement_def]
      rw [htin]
      rw [show (c.t * (y : G) * c.t * (y : G)⁻¹)⁻¹ =
          (y : G) * c.t⁻¹ * (y : G)⁻¹ * c.t⁻¹ by group]
      rw [htin]
      calc
        c.t * (c.t * (y : G) * c.t * (y : G)⁻¹) * c.t =
            (c.t * c.t) * (y : G) * c.t * (y : G)⁻¹ * c.t := by group
        _ = (y : G) * c.t * (y : G)⁻¹ * c.t := by rw [htt]; simp
  have hcommMapLe : (⁅TE, CEE⁆ : Subgroup d.E) ≤ CInvRE.map RE.subtype := by
    apply Subgroup.commutator_le.mpr
    intro x hx y hy
    have hmem : ⁅x, y⁆ ∈ RE := by
      rw [hREeq]
      exact Subgroup.commutator_mem_commutator hx hy
    let z : RE := ⟨⁅x, y⁆, hmem⟩
    refine Subgroup.mem_map.mpr ⟨z, ?_, rfl⟩
    exact hgen x hx y hy
  have hInvRE : ∀ x : RE,
      c.t * ((x : d.E) : G) * c.t⁻¹ = ((x : d.E) : G)⁻¹ := by
    intro x
    have hxcomm : (x : d.E) ∈ (⁅TE, CEE⁆ : Subgroup d.E) := by
      rw [← hREeq]
      exact x.2
    have hxmap : (x : d.E) ∈ CInvRE.map RE.subtype := hcommMapLe hxcomm
    rcases Subgroup.mem_map.mp hxmap with ⟨y, hy, hyx⟩
    have hy_eq : y = x := by
      apply Subtype.ext
      exact hyx
    change c.t * ((y : d.E) : G) * c.t⁻¹ = ((y : d.E) : G)⁻¹ at hy
    simpa [hy_eq] using hy
  have hInvR : ∀ x : G, x ∈ R → c.t * x * c.t⁻¹ = x⁻¹ := by
    intro x hx
    let xE : d.E := ⟨x, hRleE hx⟩
    let xRE : RE := ⟨xE, Subgroup.mem_subgroupOf.mpr hx⟩
    simpa [xE, xRE] using hInvRE xRE
  have hρker : ρ.ker = ⊥ := by
    apply le_antisymm
    · intro x hx
      have hφx : φ (x : d.E) = 1 := by
        have hx1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
        change (φ.comp RE.subtype) x = 1 at hx1
        simpa [MonoidHom.comp_apply] using hx1
      have hxCenterE : (x : d.E) ∈ Subgroup.center d.E := by
        rw [← hφker]
        exact hφx
      have hfix : c.t * ((x : d.E) : G) * c.t⁻¹ = ((x : d.E) : G) := by
        have hcommE := Subgroup.mem_center_iff.mp hxCenterE tE
        have hcommG : c.t * ((x : d.E) : G) = ((x : d.E) : G) * c.t :=
          congrArg (fun z : d.E => (z : G)) hcommE
        calc
          c.t * ((x : d.E) : G) * c.t⁻¹ =
              ((x : d.E) : G) * c.t * c.t⁻¹ := by rw [hcommG]
          _ = ((x : d.E) : G) := by group
      have hinv := hInvRE x
      have heqinv : ((x : d.E) : G) = ((x : d.E) : G)⁻¹ := hfix.symm.trans hinv
      let xZ : Subgroup.center d.E := ⟨(x : d.E), hxCenterE⟩
      have hxZsq : xZ ^ 2 = 1 := by
        rw [pow_two]
        apply Subtype.ext
        apply Subtype.ext
        change ((x : d.E) : G) * ((x : d.E) : G) = 1
        calc
          ((x : d.E) : G) * ((x : d.E) : G) =
              ((x : d.E) : G)⁻¹ * ((x : d.E) : G) := by rw [← heqinv]
          _ = 1 := by simp
      have hxZ1 : xZ = 1 :=
        eq_one_of_sq_eq_one_of_coprime_two d.center_odd.coprime_two_left hxZsq
      rw [Subgroup.mem_bot]
      apply Subtype.ext
      exact congrArg (fun z : Subgroup.center d.E => (z : d.E)) hxZ1
    · exact bot_le
  have hρinj : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).mp hρker
  have hρsurj : Function.Surjective ρ := by
    intro y
    have hyMap : (y : PGL2 K) ∈ RE.map φ := by
      rw [hREφ]
      exact y.2
    rcases Subgroup.mem_map.mp hyMap with ⟨x, hx, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact hxy
  let eRE : RE ≃* C1 := MulEquiv.ofBijective ρ ⟨hρinj, hρsurj⟩
  have hREcyc : IsCyclic RE := eRE.isCyclic.mpr hC1cyc
  let eSub : RE ≃* R := Subgroup.subgroupOfEquivOfLe hRleE
  have hRcyc : IsCyclic R := eSub.isCyclic.mp hREcyc
  have hRcard : Nat.card R = Nat.card T.U / 2 := by
    calc
      Nat.card R = Nat.card RE := (Nat.card_congr eSub.toEquiv).symm
      _ = Nat.card C1 := Nat.card_congr eRE.toEquiv
      _ = Nat.card T.U / 2 := hC1card
  have hRodd : Odd (Nat.card R) := by
    rw [hRcard]
    exact T.U_half_odd
  refine ⟨hRcyc, hRodd, hRcard, hInvR, ?_⟩
  simpa [RE, φ] using hREφ.trans hC1eq

end CFSG.GorensteinWalter

module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FittingCentralizes
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearFittingExtraction
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2NonsplitTorusFixed
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseReflectedTorusNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2QuotientTorusReflection
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2ConcreteSplitTorusCentralizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2SplitReflectedTorusPComplementFixed
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2InnerInvolutionFusion
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2TorusInvolutionDerived
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2SemilinearConjugationTransport
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.FStarCommute
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldSquare
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section
namespace CFSG.GorensteinWalter
open Matrix
open scoped MatrixGroups
universe u

/-- The odd Fitting image in the local involution centralizer has trivial
field projection, hence every element of `F` induces an inner action on the
component quotient. -/
public theorem secondCase_psl2_fitting_innerAction_of_actionData
    {G : Type u} [Group G] [Finite G]
    {c : CentralizerSetup G} {w : SecondCaseWitness c}
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (ad : SecondCasePSL2ActionData w d K)
    (torus : SecondCasePSL2QuotientTorusCard d K)
    (F : Subgroup G) (hFleFU : F ≤ c.FU) (hFleM : F ≤ w.M) :
    secondCase_psl2_fitting_innerAction d K ad F hFleM := by
  classical
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  let : Fintype K := Fintype.ofFinite K
  let : Finite (K ≃+* K) :=
    Finite.of_injective (fun e : K ≃+* K => (e : K → K)) (by
      intro e f hef
      ext x
      exact congrFun hef x)
  let : Finite (PGammaL2 K) :=
    Finite.of_injective
      (fun x : PGammaL2 K => (x.left, x.right)) (by
        intro x y hxy
        exact SemidirectProduct.ext
          (congrArg Prod.fst hxy) (congrArg Prod.snd hxy))
  let Q := d.E ⧸ Subgroup.center d.E
  let q : d.E →* Q := QuotientGroup.mk' (Subgroup.center d.E)
  let tE : d.E := ⟨c.t, d.t_mem_E⟩
  let tQ : Q := q tE
  let e : Q ≃* PSL2 K := ad.modelEquiv.some
  let toPGL : PSL2 K →* PGL2 K :=
    Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)
  let i : PGL2 K →* PGammaL2 K := SemidirectProduct.inl
  let hPGL : Q →* PGL2 K := toPGL.comp e.toMonoidHom
  let hPG : Q →* PGammaL2 K := i.comp hPGL
  let tM : w.M := ⟨c.t, d.E_component.1 d.t_mem_E⟩
  let tau : PGammaL2 K := ad.f tM
  let tauPGL : PGL2 K := hPGL tQ
  let C : Subgroup w.M :=
    (Subgroup.centralizer ({c.t} : Set G)).comap w.M.subtype
  let A : Subgroup (PGammaL2 K) := C.map ad.f
  let YG : Subgroup G := c.FU ⊓ w.M
  let YM : Subgroup w.M := YG.subgroupOf w.M
  let N0 : Subgroup (PGammaL2 K) := YM.map ad.f
  have hYleC : YM ≤ C := by
    intro y hy
    have hyG : (y : G) ∈ YG := Subgroup.mem_subgroupOf.mp hy
    have hyH : (y : G) ∈ c.H :=
      (centralizerSetup_FU_isNormalIn_H c).1 hyG.1
    apply Subgroup.mem_comap.mpr
    rw [← c.H_eq_centralizer]
    exact hyH
  have hN0leA : N0 ≤ A := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact Subgroup.mem_map.mpr ⟨y, hYleC hy, rfl⟩
  let N : Subgroup A := N0.subgroupOf A
  have hYnormalC : IsNormalIn YM C := by
    refine ⟨hYleC, ?_⟩
    intro z hz y hy
    apply Subgroup.mem_subgroupOf.mpr
    have hzC : (z : G) ∈ Subgroup.centralizer ({c.t} : Set G) :=
      Subgroup.mem_comap.mp hz
    have hzH : (z : G) ∈ c.H := by
      rw [c.H_eq_centralizer]
      exact hzC
    have hyYG : (y : G) ∈ YG := Subgroup.mem_subgroupOf.mp hy
    exact ⟨(centralizerSetup_FU_isNormalIn_H c).2 (z : G) hzH
        (y : G) hyYG.1,
      w.M.mul_mem (w.M.mul_mem z.2 hyYG.2) (w.M.inv_mem z.2)⟩
  have hNnormal : N.Normal := by
    refine ⟨?_⟩
    intro n hn a
    have hn0 : (n : PGammaL2 K) ∈ N0 := Subgroup.mem_subgroupOf.mp hn
    rcases Subgroup.mem_map.mp hn0 with ⟨y, hyY, hyeq⟩
    have haA : (a : PGammaL2 K) ∈ A := a.2
    rcases Subgroup.mem_map.mp haA with ⟨z, hzC, hzeq⟩
    apply Subgroup.mem_subgroupOf.mpr
    apply Subgroup.mem_map.mpr
    refine ⟨z * y * z⁻¹, hYnormalC.2 z hzC y hyY, ?_⟩
    rw [map_mul, map_mul, map_inv, hzeq, hyeq]
    rfl
  let : N.Normal := hNnormal
  have hNcard : Nat.card N = Nat.card N0 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN0leA).toEquiv
  have hYMcard : Nat.card YM = Nat.card YG :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show YG ≤ w.M from inf_le_right)).toEquiv
  have hYGU : YG ≤ c.U := inf_le_left.trans (fittingSubgroupOf_le c.U)
  have hNodd : Odd (Nat.card N) := by
    have hUodd : Odd (Nat.card c.U) := by
      change Odd (Nat.card (oddCoreOf c.H))
      exact odd_card_oddCoreOf c.H
    apply Odd.of_dvd_nat hUodd
    rw [hNcard]
    exact (Subgroup.card_map_dvd YM ad.f).trans (by
      rw [hYMcard]
      exact Subgroup.card_dvd_of_le hYGU)
  have hNnil : Group.IsNilpotent N := by
    have hYMnil : Group.IsNilpotent YM := by
      let YFU : Subgroup c.FU := YG.subgroupOf c.FU
      have : Group.IsNilpotent c.FU := fittingSubgroupOf_isNilpotent c.U
      have hYFUnil : Group.IsNilpotent YFU := Subgroup.isNilpotent YFU
      let eY : YFU ≃* YM := by
        let e1 : YFU ≃* YG := Subgroup.subgroupOfEquivOfLe inf_le_left
        let e2 : YM ≃* YG := Subgroup.subgroupOfEquivOfLe inf_le_right
        exact e1.trans e2.symm
      exact Group.nilpotent_of_mulEquiv (G := YFU) (G' := YM) eY
    let fN0 : YM →* N0 := (ad.f.comp YM.subtype).codRestrict N0 (fun y =>
      Subgroup.mem_map.mpr ⟨y, y.2, rfl⟩)
    have hfN0surj : Function.Surjective fN0 := by
      intro x
      rcases Subgroup.mem_map.mp x.2 with ⟨y, hy, hxy⟩
      refine ⟨⟨y, hy⟩, ?_⟩
      apply Subtype.ext
      exact hxy
    have hN0nil : Group.IsNilpotent N0 :=
      Group.nilpotent_of_surjective fN0 hfN0surj
    exact Group.nilpotent_of_mulEquiv (G := N0) (G' := N)
      (Subgroup.subgroupOfEquivOfLe hN0leA).symm
  let UPGL : Subgroup (PGL2 K) := torus.T.map hPGL
  let U : Subgroup (PGammaL2 K) := UPGL.map i
  have hhPGLinj : Function.Injective hPGL := by
    intro x y hxy
    apply e.injective
    apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
    exact hxy
  have hiinj : Function.Injective i := SemidirectProduct.inl_injective
  have htQinv : IsInvolution tQ := by
    have htEinv : IsInvolution tE := by
      constructor
      · intro h1
        exact c.t_involution.1 (congrArg Subtype.val h1)
      · apply Subtype.ext
        simpa [pow_two] using c.t_involution.2
    exact quotient_involution_of_involution (Subgroup.center d.E)
      d.center_odd htEinv
  have htauPGLinv : IsInvolution tauPGL := by
    constructor
    · intro h1
      apply htQinv.1
      apply hhPGLinj
      simpa using h1
    · simpa [tauPGL, map_pow] using congrArg hPGL htQinv.2
  have htauEq : tau = i tauPGL := by
    apply pGammaL2ToMulAutPSL2_injective K ad.primePower ad.fieldCardGtThree
    apply MulEquiv.ext
    intro z
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective
      (Subgroup.center d.E) (e.symm z)
    have hz : z = e (q x) := by
      calc
        z = e (e.symm z) := by simp
        _ = e (q x) := congrArg e hx.symm
    rw [hz]
    change pGammaL2ToMulAutPSL2 K ad.primePower ad.fieldCardGtThree
        (ad.f tM) (e (q x)) =
      pGammaL2ToMulAutPSL2 K ad.primePower ad.fieldCardGtThree
        (SemidirectProduct.inl (toPGL (e (q tE)))) (e (q x))
    rw [ad.action_eq tM x]
    rw [pGammaL2ToMulAutPSL2_inl]
    rw [pgl2InnerAutPSL2_toPGL K ad.primePower ad.fieldCardGtThree]
    change e (q ⟨(tM : G) * (x : G) * (tM : G)⁻¹,
        d.E_normal.2 (tM : G) tM.2 (x : G) x.2⟩) =
      e (q tE) * e (q x) * (e (q tE))⁻¹
    have hqeq : q ⟨(tM : G) * (x : G) * (tM : G)⁻¹,
        d.E_normal.2 (tM : G) tM.2 (x : G) x.2⟩ =
        q tE * q x * (q tE)⁻¹ := by
      rw [← map_mul, ← map_inv, ← map_mul]
      apply congrArg q
      apply Subtype.ext
      rfl
    simpa only [map_mul, map_inv] using congrArg e hqeq
  have hUPGLcyc : IsCyclic UPGL := by
    let eU : torus.T ≃* UPGL := Subgroup.equivMapOfInjective
      torus.T hPGL hhPGLinj
    exact (MulEquiv.isCyclic eU).mp torus.T_cyclic
  have hUcyc : IsCyclic U := by
    let eU : UPGL ≃* U := Subgroup.equivMapOfInjective UPGL i hiinj
    exact (MulEquiv.isCyclic eU).mp hUPGLcyc
  have hUPGLcard : Nat.card UPGL = Nat.card torus.T := by
    exact Subgroup.card_map_of_injective (K := torus.T) hhPGLinj
  have hUcard : Nat.card U = Nat.card torus.T := by
    rw [← hUPGLcard]
    exact Subgroup.card_map_of_injective (K := UPGL) hiinj
  have htauU : tau ∈ U := by
    rw [htauEq]
    apply Subgroup.mem_map.mpr
    refine ⟨tauPGL, ?_, rfl⟩
    exact Subgroup.mem_map.mpr ⟨tQ, torus.T_contains_t, rfl⟩
  have hAdata := secondCase_psl2_hAcont w d K ad
  have htauL : tau ∈ pGammaL2PSLRange K := hAdata.1
  have hAcent : A ≤ Subgroup.centralizer ({tau} : Set (PGammaL2 K)) := hAdata.2.1
  have hAcont : (Subgroup.centralizer ({tau} : Set (PGammaL2 K)) ⊓
      pGammaL2PSLRange K) ≤ A := hAdata.2.2
  have hUleC : U ≤ Subgroup.centralizer ({tau} : Set (PGammaL2 K)) ⊓
      pGammaL2PSLRange K := by
    intro x hx
    constructor
    · change x ∈ Subgroup.centralizer ({tau} : Set (PGammaL2 K))
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyEq : y = tau := by simpa using hy
      subst y
      rcases hUcyc with ⟨a, ha⟩
      rcases ha ⟨x, hx⟩ with ⟨m, hm⟩
      rcases ha ⟨tau, htauU⟩ with ⟨n, hn⟩
      have hcomm : (⟨x, hx⟩ : U) * (⟨tau, htauU⟩ : U) =
          (⟨tau, htauU⟩ : U) * (⟨x, hx⟩ : U) := by
        calc
          (⟨x, hx⟩ : U) * (⟨tau, htauU⟩ : U) = a ^ m * a ^ n := by
            simp [hm, hn]
          _ = a ^ (m + n) := by rw [zpow_add]
          _ = a ^ (n + m) := by rw [add_comm]
          _ = a ^ n * a ^ m := by rw [zpow_add]
          _ = (⟨tau, htauU⟩ : U) * (⟨x, hx⟩ : U) := by
            simp [← hm, ← hn]
      exact (congrArg Subtype.val hcomm).symm
    · rcases Subgroup.mem_map.mp hx with ⟨z, hz, rfl⟩
      rcases Subgroup.mem_map.mp hz with ⟨y, hy, rfl⟩
      exact (mem_pGammaL2PSLRange_iff K (i (hPGL y))).mpr ⟨e y, rfl⟩
  have hUnormA : IsNormalIn U A := by
    obtain ⟨sQ, hsQI, hsQnot, hsQinv, hCq⟩ :=
      secondCase_psl2_quotient_torus_reflection c w d K torus
    have htQ : IsInvolution tQ := htQinv
    have hTmax : ∀ X : Subgroup Q,
        IsCyclic X → tQ ∈ X →
          X ≤ Subgroup.centralizer ({tQ} : Set Q) → X ≤ torus.T := by
      intro X hXcyc htX hXcent
      exact cyclic_subgroup_containing_involution_le_reflected_torus
        (G := Q) htQ torus.T sQ torus.T_cyclic torus.T_contains_t
        hsQI hsQnot hsQinv hCq hXcyc hXcent htX
    refine ⟨hUleC.trans hAcont, ?_⟩
    intro a ha x hx
    rcases Subgroup.mem_map.mp ha with ⟨m, hmC, hma⟩
    rcases Subgroup.mem_map.mp hx with ⟨z, hzUPGL, hzx⟩
    rcases Subgroup.mem_map.mp hzUPGL with ⟨u, huT, hzu⟩
    let αhom : d.E →* d.E :=
      { toFun := fun y =>
          ⟨(m : G) * (y : G) * (m : G)⁻¹,
            d.E_normal.2 (m : G) m.2 (y : G) y.2⟩
        map_one' := by apply Subtype.ext; simp
        map_mul' := by intro y z; apply Subtype.ext; simp [mul_assoc] }
    let αinv : d.E →* d.E :=
      { toFun := fun y =>
          ⟨(m : G)⁻¹ * (y : G) * (m : G),
            by simpa using d.E_normal.2 (m : G)⁻¹ (w.M.inv_mem m.2) (y : G) y.2⟩
        map_one' := by apply Subtype.ext; simp
        map_mul' := by intro y z; apply Subtype.ext; simp [mul_assoc] }
    have hleft : ∀ y : d.E, αinv (αhom y) = y := by
      intro y; apply Subtype.ext; simp [αinv, αhom]; group
    have hright : ∀ y : d.E, αhom (αinv y) = y := by
      intro y; apply Subtype.ext; simp [αinv, αhom]; group
    let αE : d.E ≃* d.E := MulEquiv.ofBijective αhom ⟨
      (Function.LeftInverse.injective hleft),
      (fun y => ⟨αinv y, hright y⟩)⟩
    let αQ : Q ≃* Q :=
      quotientCenterAutomorphism d.E αE
    have hαQ_t : αQ tQ = tQ := by
      apply e.injective
      change e (αQ (q tE)) = e (q tE)
      rw [show αQ (q tE) = q (αE tE) by
        rw [quotientCenterAutomorphism_apply_mk]]
      apply congrArg e
      apply congrArg q
      apply Subtype.ext
      change (m : G) * c.t * (m : G)⁻¹ = c.t
      have hmcent : (m : G) ∈ Subgroup.centralizer ({c.t} : Set G) := hmC
      have hmc := hmcent c.t (by simp)
      calc
        (m : G) * c.t * (m : G)⁻¹ = (c.t * (m : G)) * (m : G)⁻¹ := by rw [hmc]
        _ = c.t := by group
    let X : Subgroup Q := torus.T.map αQ.toMonoidHom
    have hXcyc : IsCyclic X := by
      let eX : torus.T ≃* X := Subgroup.equivMapOfInjective torus.T
        αQ.toMonoidHom αQ.injective
      exact (MulEquiv.isCyclic eX).mp torus.T_cyclic
    have htX : tQ ∈ X := by
      apply Subgroup.mem_map.mpr
      refine ⟨tQ, torus.T_contains_t, ?_⟩
      simp [hαQ_t]
    have hXcent : X ≤ Subgroup.centralizer ({tQ} : Set Q) := by
      have hTcent : torus.T ≤ Subgroup.centralizer ({tQ} : Set Q) := by
        intro v hv
        rw [Subgroup.mem_centralizer_singleton_iff]
        rcases torus.T_cyclic with ⟨b, hb⟩
        rcases hb ⟨v, hv⟩ with ⟨r, hr⟩
        rcases hb ⟨tQ, torus.T_contains_t⟩ with ⟨s, hs⟩
        have hc : (⟨v, hv⟩ : torus.T) *
            (⟨tQ, torus.T_contains_t⟩ : torus.T) =
            (⟨tQ, torus.T_contains_t⟩ : torus.T) *
              (⟨v, hv⟩ : torus.T) := by
          calc
            (⟨v, hv⟩ : torus.T) *
                (⟨tQ, torus.T_contains_t⟩ : torus.T) = b ^ r * b ^ s := by
                  simp [hr, hs]
            _ = b ^ (r + s) := by rw [zpow_add]
            _ = b ^ (s + r) := by rw [add_comm]
            _ = b ^ s * b ^ r := by rw [zpow_add]
            _ = (⟨tQ, torus.T_contains_t⟩ : torus.T) *
                (⟨v, hv⟩ : torus.T) := by simp [← hs, ← hr]
        simpa using congrArg Subtype.val hc
      intro y hy
      rcases Subgroup.mem_map.mp hy with ⟨v, hvT, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hvcent : v * tQ = tQ * v :=
        Subgroup.mem_centralizer_singleton_iff.mp (hTcent hvT)
      have := congrArg αQ hvcent
      simpa [hαQ_t, map_mul] using this
    have hXle : X ≤ torus.T := hTmax X hXcyc htX hXcent
    have hαu : αQ u ∈ torus.T := hXle (Subgroup.mem_map.mpr ⟨u, huT, rfl⟩)
    apply Subgroup.mem_map.mpr
    refine ⟨hPGL (αQ u), ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨αQ u, hαu, rfl⟩
    subst hma
    subst hzx
    subst hzu
    apply pGammaL2ToMulAutPSL2_injective K ad.primePower ad.fieldCardGtThree
    have hAct : pGammaL2ToMulAutPSL2 K ad.primePower ad.fieldCardGtThree
        (ad.f m) = MulAut.congr e αQ := by
      apply MulEquiv.ext
      intro y'
      obtain ⟨x', hx'⟩ := QuotientGroup.mk'_surjective
        (Subgroup.center d.E) (e.symm y')
      have hy' : y' = e (q x') := by
        calc y' = e (e.symm y') := by simp
             _ = e (q x') := congrArg e hx'.symm
      rw [hy']
      rw [ad.action_eq m x']
      rw [MulAut.congr_apply]
      simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      change e (q (αhom x')) = e (αQ (q x'))
      rw [show αQ (q x') = q (αE x') by
        rw [quotientCenterAutomorphism_apply_mk]]
      rfl
    have hInl : ∀ v : Q,
        pGammaL2ToMulAutPSL2 K ad.primePower ad.fieldCardGtThree
          (i (hPGL v)) = MulAut.conj (e v) := by
      intro v
      rw [pGammaL2ToMulAutPSL2_inl]
      exact pgl2InnerAutPSL2_toPGL K ad.primePower ad.fieldCardGtThree (e v)
    rw [map_mul, map_mul, map_inv, hAct, hInl, hInl]
    apply MulEquiv.ext
    intro y
    simp [MulAut.congr_apply, MulAut.conj_apply]
  have hUnilp : Group.IsNilpotent U := by
    let : IsCyclic U := hUcyc
    let : CommGroup U := IsCyclic.commGroup
    infer_instance
  have hNker : N ≤ pGammaL2LinearKernel K A := by
    by_contra hnle
    have hproj : ∃ n : N, SemidirectProduct.rightHom (n : PGammaL2 K) ≠ 1 := by
      rcases SetLike.not_le_iff_exists.mp hnle with ⟨n, hnN, hnker⟩
      refine ⟨⟨n, hnN⟩, ?_⟩
      intro hright
      apply hnker
      rw [mem_pGammaL2LinearKernel_iff]
      simpa [pGammaL2FieldProjection] using hright
    obtain ⟨p, hp, hpodd, sigma, hsigord, P, hPleF, hPnormF, hPp,
      a0, ha0P, ha0sigma, ha0pow⟩ :=
      secondCase_fitting_fieldProjection_pElement A N hNodd hNnil hproj
    let : Fact p.Prime := ⟨hp⟩
    let U0U : Subgroup U := pPrimeCore p U
    let U0 : Subgroup (PGammaL2 K) := U0U.map U.subtype
    have hU0leU : U0 ≤ U := Subgroup.map_subtype_le U0U
    have hU0normU : IsNormalIn U0 U := by
      exact fstar_characteristic_subgroupOf_map_normal_in
        (pPrimeCore_characteristic (p := p) (G := U)) ⟨le_rfl, by
          intro a ha x hx
          exact U.mul_mem (U.mul_mem ha hx) (U.inv_mem ha)⟩
    have hU0normA : IsNormalIn U0 A := by
      exact fstar_characteristic_subgroupOf_map_normal_in
        (pPrimeCore_characteristic (p := p) (G := U)) hUnormA
    have hU0card : Nat.card U0 = Nat.card U0U := by
      exact Subgroup.card_map_of_injective U.subtype_injective
    have hU0cop : Nat.Coprime p (Nat.card U0) := by
      rw [hU0card]
      exact pPrimeCore_coprime_card (p := p) (G := U)
    have hU0sub : U0.subgroupOf U = U0U := by
      ext x
      constructor
      · intro hx
        rcases Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hx) with
          ⟨y, hy, hxy⟩
        have : y = x := by
          apply U.subtype_injective
          exact hxy
        simpa [this] using hy
      · intro hx
        apply Subgroup.mem_subgroupOf.mpr
        exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    have hU0quot : IsPGroup p (↥U ⧸ U0.subgroupOf U) := by
      rw [hU0sub]
      have : Group.IsNilpotent U := hUnilp
      have hQnil : Group.IsNilpotent (U ⧸ pPrimeCore p U) :=
        Group.nilpotent_of_surjective (QuotientGroup.mk' (pPrimeCore p U))
          (QuotientGroup.mk'_surjective (pPrimeCore p U))
      have htopnil : Group.IsNilpotent
          (⊤ : Subgroup (U ⧸ pPrimeCore p U)) := by
        let : Group.IsNilpotent (U ⧸ pPrimeCore p U) := hQnil
        infer_instance
      have htopP : IsPGroup p (⊤ : Subgroup (U ⧸ pPrimeCore p U)) :=
        isPGroup_of_nilpotent_normal (⊤ : Subgroup (U ⧸ pPrimeCore p U))
          inferInstance htopnil (pPrimeCore_quotient_pPrimeCore_eq_bot p)
      exact htopP.of_equiv Subgroup.topEquiv
    let R := FixedPoints.subfield (Subgroup.zpowers sigma) K
    obtain ⟨hr, _hp3, hq⟩ := finiteField_primeOrder_fixedSubfield_data
      K ad.primePower sigma p hp hpodd hsigord
    have hKodd : Odd (Nat.card K) := by
      rcases ad.primePower with ⟨ell, n, hell, hellodd, hn, hKcard⟩
      rw [hKcard]
      exact hellodd.pow
    have hrOdd : Odd (Nat.card R) := by
      rcases Nat.even_or_odd (Nat.card R) with hrEven | hrOdd
      · exfalso
        have h2r : 2 ∣ Nat.card R := even_iff_two_dvd.mp hrEven
        have h2pow : 2 ∣ Nat.card R ^ p := dvd_pow h2r hp.ne_zero
        rw [← hq] at h2pow
        exact hKodd.not_two_dvd_nat h2pow
      · exact hrOdd
    have hU0fixed : ∀ b0 : PGammaL2 K, b0 ∈ P →
        SemidirectProduct.rightHom b0 = sigma →
        (∃ k : ℕ, b0 ^ p ^ k = 1) →
        (∀ u : PGammaL2 K, u ∈ U0 → b0 * u * b0⁻¹ = u) →
        (Nat.card U = (Nat.card K - 1) / 2 ∧
            Nat.card U0 ∣ (Nat.card R - 1) / 2) ∨
          (Nat.card U = (Nat.card K + 1) / 2 ∧
            Nat.card U0 ∣ (Nat.card R + 1) / 2) := by
      intro b0 hb0P hb0sigma _hb0pow hb0fix
      let U0P : Subgroup (PGL2 K) := U0.comap i
      have hU0Pmap : U0P.map i = U0 := by
        apply le_antisymm
        · exact Subgroup.map_comap_le i U0
        · intro x hx
          have hxU : x ∈ U := hU0leU hx
          rcases Subgroup.mem_map.mp hxU with ⟨y, hy, hxy⟩
          exact Subgroup.mem_map.mpr ⟨y, by
            apply Subgroup.mem_comap.mpr
            simpa [hxy] using hx, hxy⟩
      have hU0Pcard : Nat.card U0P = Nat.card U0 := by
        rw [← hU0Pmap]
        exact (Subgroup.card_map_of_injective (K := U0P) hiinj).symm
      have hU0Ple : U0P ≤ UPGL := by
        intro x hx
        have hinlU0 : i x ∈ U0 := Subgroup.mem_comap.mp hx
        have hinlU : i x ∈ U := hU0leU hinlU0
        rcases Subgroup.mem_map.mp hinlU with ⟨y, hy, hxy⟩
        have hyx : y = x := hiinj hxy
        simpa [hyx] using hy
      have hUPGLinner : UPGL ≤ commutator (PGL2 K) := by
        intro x hx
        rcases Subgroup.mem_map.mp hx with ⟨v, hv, rfl⟩
        rw [pgl2_commutator_eq_psl2_range_of_card_gt_three
          K ad.primePower ad.fieldCardGtThree]
        exact ⟨e v, rfl⟩
      have hU0Pinner : U0P ≤ commutator (PGL2 K) := hU0Ple.trans hUPGLinner
      have hsemiconj : ∀ x : PGL2 K, x ∈ U0P →
          b0.left * pgl2FieldAut K sigma x * b0.left⁻¹ = x := by
        intro x hx
        have hfix := hb0fix (i x) (Subgroup.mem_comap.mp hx)
        have hleft := congrArg SemidirectProduct.left hfix
        simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
          SemidirectProduct.inv_left, map_inv] at hleft
        have hb0right : b0.right = sigma := by simpa using hb0sigma
        rw [hb0right] at hleft
        simpa [i] using hleft
      have htauUPGL : tauPGL ∈ UPGL :=
        Subgroup.mem_map.mpr ⟨tQ, torus.T_contains_t, rfl⟩
      have htauJ : tauPGL ∈ commutator (PGL2 K) := hUPGLinner htauUPGL
      have hJindex : (commutator (PGL2 K)).index = 2 := by
        rw [pgl2_commutator_eq_psl2_range_of_card_gt_three
          K ad.primePower ad.fieldCardGtThree]
        exact pgl2_psl2Range_index_eq_two K ad.primePower
      have cyclic_le_centralizer : ∀ (V : Subgroup (PGL2 K)) (s : PGL2 K),
          IsCyclic V → s ∈ V →
            V ≤ Subgroup.centralizer ({s} : Set (PGL2 K)) := by
        intro V s hVcyc hsV x hx
        rw [Subgroup.mem_centralizer_singleton_iff]
        rcases hVcyc with ⟨a, ha⟩
        rcases ha ⟨x, hx⟩ with ⟨m, hm⟩
        rcases ha ⟨s, hsV⟩ with ⟨n, hn⟩
        have hc : (⟨x, hx⟩ : V) * (⟨s, hsV⟩ : V) =
            (⟨s, hsV⟩ : V) * (⟨x, hx⟩ : V) := by
          calc
            (⟨x, hx⟩ : V) * (⟨s, hsV⟩ : V) = a ^ m * a ^ n := by
              simp [hm, hn]
            _ = a ^ (m + n) := by rw [zpow_add]
            _ = a ^ (n + m) := by rw [add_comm]
            _ = a ^ n * a ^ m := by rw [zpow_add]
            _ = (⟨s, hsV⟩ : V) * (⟨x, hx⟩ : V) := by
              simp [← hn, ← hm]
        simpa using congrArg Subtype.val hc
      rcases torus.T_card with hTminus | hTplus
      · left
        refine ⟨hUcard.trans hTminus, ?_⟩
        obtain ⟨wS, hScyc, hScard, hsS, hsI, hwSnot, hwS2,
          hwSinv, hCS, _hDcard, hSnotJ⟩ :=
          pgl2_fullSplitTorus_centralizer_data K ad.primePower
        let S : Subgroup (PGL2 K) := (pGammaL2FullSplitTorus K).range
        let sS : PGL2 K := pGammaL2FullSplitTorus K (-1 : Kˣ)
        have hhalfEven : Even ((Nat.card K - 1) / 2) := by
          rw [← hTminus]
          exact torus.T_even
        have hqsubtwo : Nat.card K - 1 =
            2 * ((Nat.card K - 1) / 2) := by
          have htwo : 2 ∣ Nat.card K - 1 := by
            rcases hKodd with ⟨k, hk⟩
            use k
            omega
          rw [mul_comm]
          exact (Nat.div_mul_cancel htwo).symm
        have hsJ : sS ∈ commutator (PGL2 K) := by
          apply pgl2_torus_involution_mem_commutator hJindex S hScyc hsS
            (by simpa [pow_two] using hsI.2) hsI.1
            (m := (Nat.card K - 1) / 2)
          · change Nat.card (pGammaL2FullSplitTorus K).range =
              2 * ((Nat.card K - 1) / 2)
            exact hScard.trans hqsubtwo
          · exact hhalfEven
          · exact hSnotJ
        obtain ⟨g, hgJ, hg⟩ := pgl2_inner_involutions_conjugate
          ad.primePower ad.fieldCardGtThree htauJ htauPGLinv hsJ hsI
        let X : Subgroup (PGL2 K) := UPGL.map (MulAut.conj g).toMonoidHom
        have hXcyc : IsCyclic X := by
          let ex : UPGL ≃* X := Subgroup.equivMapOfInjective UPGL
            (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
          exact (MulEquiv.isCyclic ex).mp hUPGLcyc
        have hsX : sS ∈ X := by
          exact Subgroup.mem_map.mpr ⟨tauPGL, htauUPGL, by
            simpa [sS, MulAut.conj_apply] using hg⟩
        have hXleS : X ≤ S :=
          cyclic_subgroup_containing_involution_le_reflected_torus
            hsI S wS hScyc hsS
            (by constructor
                · intro h1
                  apply hwSnot
                  rw [h1]
                  exact S.one_mem
                · simpa [pow_two] using hwS2)
            hwSnot hwSinv hCS hXcyc
            (cyclic_le_centralizer X sS hXcyc hsX) hsX
        let Astd : Subgroup (PGL2 K) :=
          U0P.map (MulAut.conj g).toMonoidHom
        have hAstdleX : Astd ≤ X :=
          Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hU0Ple
        have hAstdleS : Astd ≤ S := hAstdleX.trans hXleS
        have hXinner : X ≤ commutator (PGL2 K) := by
          intro x hx
          rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
          exact (inferInstance : (commutator (PGL2 K)).Normal).conj_mem
            y (hUPGLinner hy) g
        have hAstdinner : Astd ≤ commutator (PGL2 K) :=
          hAstdleX.trans hXinner
        let zS : PGL2 K :=
          g * b0.left * (pgl2FieldAut K sigma g)⁻¹
        have hAstdconj : ∀ x : PGL2 K, x ∈ Astd →
            zS * pgl2FieldAut K sigma x * zS⁻¹ = x := by
          intro x hx
          rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
          exact pgl2_semilinear_conjugate_transport sigma g b0.left y
            (hsemiconj y hy)
        let Tsplit : Kˣ →* PGL2 K := pGammaL2FullSplitTorus K
        let B : Subgroup Kˣ := Astd.comap Tsplit
        have hBmap : B.map Tsplit = Astd := by
          apply le_antisymm
          · exact Subgroup.map_comap_le Tsplit Astd
          · intro x hx
            rcases hAstdleS hx with ⟨b, hb⟩
            exact Subgroup.mem_map.mpr ⟨b, by
              apply Subgroup.mem_comap.mpr
              simpa [Tsplit, hb] using hx, hb⟩
        have hBcard : Nat.card B = Nat.card Astd := by
          rw [← hBmap]
          exact (Subgroup.card_map_of_injective
            (K := B) (pGammaL2FullSplitTorus_injective K)).symm
        have hAstdcard : Nat.card Astd = Nat.card U0P := by
          exact Subgroup.card_map_of_injective (MulAut.conj g).injective
        have hdvd := pGammaL2_splitTorus_semilinearConjugate_fixedSubfield
          ad.primePower ad.fieldCardGtThree sigma p hp hpodd hsigord
          hhalfEven zS B
          (by intro b hb
              apply hAstdinner
              have : Tsplit b ∈ Astd := Subgroup.mem_comap.mp hb
              simpa [Tsplit] using this)
          (by intro b hb
              rw [← pGammaL2FullSplitTorus_map_field]
              apply hAstdconj
              have : Tsplit b ∈ Astd := Subgroup.mem_comap.mp hb
              simpa [Tsplit] using this)
        rw [hBcard, hAstdcard, hU0Pcard] at hdvd
        exact hdvd
      · right
        refine ⟨hUcard.trans hTplus, ?_⟩
        let : Fintype R := Fintype.ofFinite R
        have hcharR : ringChar R ≠ 2 := by
          intro hchar
          let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
          have hdvd : 2 ∣ Fintype.card R :=
            (prime_dvd_char_iff_dvd_card (R := R) (p := 2)).mp (by
              simp [hchar])
          apply hrOdd.not_two_dvd_nat
          simpa [Nat.card_eq_fintype_card] using hdvd
        obtain ⟨lamR, hlamNS⟩ := FiniteField.exists_nonsquare hcharR
        let lam : K := (lamR : R)
        obtain ⟨sN, wN, hNcyc, hNcard, hsN, hsNI, hwN2, hwNnot,
          hwNinv, hCN, _hDNcard, _hNnotRange, hNnotJ⟩ :=
          pgl2_concrete_nonsplit_torus_centralizer_data K ad.primePower
            lam (fun hsquare => hlamNS
              ((fixedSubfield_isSquare_iff K sigma p hp hpodd hsigord lamR).mp
                hsquare))
        let SN : Subgroup (PGL2 K) := pgl2ConcreteNonsplitTorus K lam
        have hhalfEven : Even ((Nat.card K + 1) / 2) := by
          rw [← hTplus]
          exact torus.T_even
        have hqaddtwo : Nat.card K + 1 =
            2 * ((Nat.card K + 1) / 2) := by
          have htwo : 2 ∣ Nat.card K + 1 := by
            rcases hKodd with ⟨k, hk⟩
            use k + 1
            omega
          rw [mul_comm]
          exact (Nat.div_mul_cancel htwo).symm
        have hsNJ : sN ∈ commutator (PGL2 K) := by
          apply pgl2_torus_involution_mem_commutator hJindex SN hNcyc hsN
            (by simpa [pow_two] using hsNI.2) hsNI.1
            (m := (Nat.card K + 1) / 2)
          · change Nat.card (pgl2ConcreteNonsplitTorus K lam) =
              2 * ((Nat.card K + 1) / 2)
            exact hNcard.trans hqaddtwo
          · exact hhalfEven
          · exact hNnotJ
        obtain ⟨g, hgJ, hg⟩ := pgl2_inner_involutions_conjugate
          ad.primePower ad.fieldCardGtThree htauJ htauPGLinv hsNJ hsNI
        let X : Subgroup (PGL2 K) := UPGL.map (MulAut.conj g).toMonoidHom
        have hXcyc : IsCyclic X := by
          let ex : UPGL ≃* X := Subgroup.equivMapOfInjective UPGL
            (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
          exact (MulEquiv.isCyclic ex).mp hUPGLcyc
        have hsX : sN ∈ X := by
          exact Subgroup.mem_map.mpr ⟨tauPGL, htauUPGL, by
            simpa [MulAut.conj_apply] using hg⟩
        have hXleN : X ≤ SN :=
          cyclic_subgroup_containing_involution_le_reflected_torus
            hsNI SN wN hNcyc hsN
            (by constructor
                · intro h1
                  apply hwNnot
                  rw [h1]
                  exact SN.one_mem
                · simpa [pow_two] using hwN2)
            hwNnot hwNinv hCN hXcyc
            (cyclic_le_centralizer X sN hXcyc hsX) hsX
        let Astd : Subgroup (PGL2 K) :=
          U0P.map (MulAut.conj g).toMonoidHom
        have hAstdleX : Astd ≤ X :=
          Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hU0Ple
        have hAstdleN : Astd ≤ SN := hAstdleX.trans hXleN
        have hXinner : X ≤ commutator (PGL2 K) := by
          intro x hx
          rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
          exact (inferInstance : (commutator (PGL2 K)).Normal).conj_mem
            y (hUPGLinner hy) g
        have hAstdinner : Astd ≤ commutator (PGL2 K) :=
          hAstdleX.trans hXinner
        let zN : PGL2 K :=
          g * b0.left * (pgl2FieldAut K sigma g)⁻¹
        have hAstdconj : ∀ x : PGL2 K, x ∈ Astd →
            zN * pgl2FieldAut K sigma x * zN⁻¹ = x := by
          intro x hx
          rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
          exact pgl2_semilinear_conjugate_transport sigma g b0.left y
            (hsemiconj y hy)
        have hAstdcard : Nat.card Astd = Nat.card U0P := by
          exact Subgroup.card_map_of_injective (MulAut.conj g).injective
        have hdvd :=
          pGammaL2_nonsplitTorus_semilinearConjugate_fixedSubfield
            ad.primePower ad.fieldCardGtThree sigma p hp hpodd hsigord
            lam lamR.2 hlamNS zN Astd hAstdleN hAstdinner hAstdconj
        rw [hAstdcard, hU0Pcard] at hdvd
        exact hdvd
    apply hnle
    exact pGammaL2_weak_normal_nilpotent_odd_fieldProjection_trivial
      K ad.primePower ad.fieldCardGtThree A tau htauL
      (by
        rw [htauEq]
        constructor
        · intro h1
          exact htauPGLinv.1 (hiinj (by simpa using h1))
        · simpa [map_pow] using congrArg i htauPGLinv.2)
      hAcent hAcont N hNodd hNnil p hpodd sigma hsigord P hPleF
      hPnormF hPp ⟨a0, ha0P, ha0sigma⟩ U hUleC hUnormA hUcyc
      hUnilp U0 hU0leU hU0normU hU0normA hU0cop hU0quot
      (Nat.card R) hr hrOdd hq hU0fixed
  have himageN : N0 ≤ pGammaL2PSLRange K := by
    intro x hx
    have hxA : x ∈ A := hN0leA hx
    have hxker : (⟨x, hxA⟩ : A) ∈ pGammaL2LinearKernel K A := by
      exact hNker (Subgroup.mem_subgroupOf.mpr hx)
    have hN0odd : Odd (Nat.card N0) := by
      rw [← hNcard]
      exact hNodd
    have hxodd : Odd (orderOf x) :=
      Odd.of_dvd_nat hN0odd (Subgroup.orderOf_dvd_natCard N0 hx)
    exact pGammaL2_linearKernel_odd_order_mem_pslRange
      K ad.primePower A hxA hxker hxodd
  apply secondCase_psl2_innerAction_of_image_in_pslRange d K ad F hFleM
  intro f hf
  apply himageN
  exact Subgroup.mem_map.mpr
    ⟨⟨f, hFleM hf⟩, Subgroup.mem_subgroupOf.mpr ⟨hFleFU hf, hFleM hf⟩, rfl⟩

end CFSG.GorensteinWalter

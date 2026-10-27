module

public import CFSG.Quasithin.Recognition.Stroth.BenderNoFF
public import CFSG.Quasithin.Background.SmithC27Setup
public import CFSG.Quasithin.Background.InternalSecB56
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.RouteBGlue
public import CFSG.GroupTheory.PerfectCentralExtensionUnique
public import CFSG.Quasithin.Vol2.Ch3Sec3InspF618Tools
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIGroup
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
open CFSG.HardMathSupport.Cooperstein.Coordinator
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem map_mk'_eq_top_iff {H : Type} [Group H] {R : Subgroup H} [R.Normal]
    {C : Subgroup H} (hRC : R ≤ C) :
    C.map (QuotientGroup.mk' R) = ⊤ ↔ C = ⊤ := by
  constructor
  · intro htop
    rw [eq_top_iff]
    intro x hx
    have hxM : QuotientGroup.mk' R x ∈ C.map (QuotientGroup.mk' R) := by
      rw [htop]; exact Subgroup.mem_top _
    obtain ⟨c, hc, hcx⟩ := hxM
    have hmem : c⁻¹ * x ∈ R := by
      refine (QuotientGroup.eq_one_iff (N := R) (x := c⁻¹ * x)).mp ?_
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      have hcx' : (↑c : H ⧸ R) = ↑x := by simpa [QuotientGroup.mk'_apply] using hcx
      rw [hcx', inv_mul_cancel]
    have hx' : x = c * (c⁻¹ * x) := by group
    rw [hx']
    exact C.mul_mem hc (hRC hmem)
  · rintro rfl
    exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective R)

private theorem pCore_eq_bot_of_quasisimple_of_center_pow_three {Q : Type} [Group Q] [Finite Q]
    (hQ : CFSG.IsQuasisimple Q) (h3 : ∀ z ∈ Subgroup.center Q, z ^ 3 = 1) :
    CFSG.pCore 2 Q = ⊥ := by
  have hP : (CFSG.pCore 2 Q).Normal := CFSG.pCore_normal
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ hP with htop | hcenter
  · exfalso
    have htopP : IsPGroup 2 (⊤ : Subgroup Q) :=
      htop ▸ CFSG.LieType.BorelTits.pCore_isPGroup (G := Q) 2
    have hPQ : IsPGroup 2 Q := IsPGroup.of_equiv htopP Subgroup.topEquiv
    have hsub : Subsingleton Q :=
      CFSG.Quasithin.H13.C1294.subsingleton_of_perfect_isPGroup hPQ hQ.1.commutator_eq_top
    haveI : Nontrivial Q := CFSG.LocalCores.isQuasisimple_nontrivial hQ
    obtain ⟨a, b, hab⟩ := (inferInstance : Nontrivial Q).exists_pair_ne
    exact hab (Subsingleton.elim a b)
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := Q) 2) ⟨x, hx⟩
    have hk' : x ^ 2 ^ k = 1 := by
      have := congrArg (fun y : ↥(CFSG.pCore 2 Q) => (y : Q)) hk
      simpa using this
    have hdvd2 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hdvd3 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one (h3 x (hcenter hx))
    have hprime : Nat.Prime 3 := by norm_num
    rcases hprime.eq_one_or_self_of_dvd (orderOf x) hdvd3 with h1 | h3'
    · exact orderOf_eq_one_iff.mp h1
    · exfalso
      rw [h3'] at hdvd2
      have : 3 ∣ 2 := hprime.dvd_of_dvd_pow hdvd2
      omega

private theorem omegaOneCenter_pCore_facts (H : Subgroup G) :
    IsElemAbelian 2 (CFSG.Quasithin.omegaOneCenterOf (CFSG.Open.pCoreOf 2 H)) ∧
      CFSG.Quasithin.omegaOneCenterOf (CFSG.Open.pCoreOf 2 H) ≤ H ∧
      H ≤ Subgroup.normalizer
        (CFSG.Quasithin.omegaOneCenterOf (CFSG.Open.pCoreOf 2 H) : Set G) ∧
      CFSG.Open.pCoreOf 2 H ≤ Subgroup.centralizer
        (CFSG.Quasithin.omegaOneCenterOf (CFSG.Open.pCoreOf 2 H) : Set G) :=
  ⟨CFSG.Quasithin.SmithC27.isElemAbelian_omegaOneCenterOf _,
   CFSG.Quasithin.SmithC27.omegaOneCenterOf_pCoreOf_le H,
   CFSG.Quasithin.SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf H,
   CFSG.Quasithin.SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf H⟩

private theorem Csub_facts {H V : Subgroup G}
    (hHN : H ≤ Subgroup.normalizer (V : Set G))
    (hRV : CFSG.Open.pCoreOf 2 H ≤ Subgroup.centralizer (V : Set G))
    (hHC : ¬ H ≤ Subgroup.centralizer (V : Set G)) :
    CFSG.pCore 2 ↥H ≤ (H ⊓ Subgroup.centralizer (V : Set G)).subgroupOf H ∧
      ((H ⊓ Subgroup.centralizer (V : Set G)).subgroupOf H).Normal ∧
      ((H ⊓ Subgroup.centralizer (V : Set G)).subgroupOf H) ≠ ⊤ := by
  have hRsub_coe : ∀ x ∈ CFSG.pCore 2 ↥H,
      (x : G) ∈ CFSG.Open.pCoreOf 2 H := fun x hx =>
    Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have hRC : CFSG.pCore 2 ↥H ≤ (H ⊓ Subgroup.centralizer (V : Set G)).subgroupOf H := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr ⟨x.2, hRV (hRsub_coe x hx)⟩
  have hCsub_normal : ((H ⊓ Subgroup.centralizer (V : Set G)).subgroupOf H).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer
      (H := H ⊓ Subgroup.centralizer (V : Set G)) (K := H) inf_le_left).2 ?_
    exact B2F.le_normalizer_inf Subgroup.le_normalizer (B2F.le_normalizer_centralizer hHN)
  have hCsub_ne_top : ((H ⊓ Subgroup.centralizer (V : Set G)).subgroupOf H) ≠ ⊤ := by
    intro htop
    apply hHC
    intro x hx
    have hmem : (⟨x, hx⟩ : ↥H) ∈ (H ⊓ Subgroup.centralizer (V : Set G)).subgroupOf H := by
      rw [htop]; exact Subgroup.mem_top _
    simpa [Subgroup.mem_subgroupOf] using hmem
  exact ⟨hRC, hCsub_normal, hCsub_ne_top⟩

private theorem centralFactor_center {H : Subgroup G} {Rsub Csub : Subgroup ↥H}
    [Rsub.Normal] (hCsub_normal : Csub.Normal) (hRC : Rsub ≤ Csub)
    {Q : Type} [Group Q] (eQ : (↥H ⧸ Rsub) ≃* Q) (hQ : CFSG.IsQuasisimple Q)
    (hCsub_ne_top : Csub ≠ ⊤) :
    (Csub.map (QuotientGroup.mk' Rsub)).map eQ.toMonoidHom ≤ Subgroup.center Q ∧
      Csub.map (QuotientGroup.mk' Rsub) ≤ Subgroup.center (↥H ⧸ Rsub) := by
  let D : Subgroup (↥H ⧸ Rsub) := Csub.map (QuotientGroup.mk' Rsub)
  let D' : Subgroup Q := D.map eQ.toMonoidHom
  have hD_normal : D.Normal :=
    hCsub_normal.map _ (QuotientGroup.mk'_surjective Rsub)
  have hD'_normal : D'.Normal := hD_normal.map _ eQ.surjective
  have hD'_center : D' ≤ Subgroup.center Q := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ hD'_normal with htop | hle
    · exfalso
      have hDtop : D = ⊤ := (CFSG.Quasithin.E1.map_eq_top_iff_mulEquiv eQ D).1 htop
      exact hCsub_ne_top ((map_mk'_eq_top_iff hRC).1 hDtop)
    · exact hle
  have hD_center : D ≤ Subgroup.center (↥H ⧸ Rsub) := by
    intro d hd
    rw [Subgroup.mem_center_iff]
    intro a
    apply eQ.injective
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.mp
      (hD'_center (Subgroup.mem_map_of_mem eQ.toMonoidHom hd)) (eQ a)
  exact ⟨hD'_center, hD_center⟩

private theorem autI_isQuasisimple {V : Subgroup G} (hV : IsElemAbelian 2 V)
    {H : Subgroup G} {Q : Type} [Group Q]
    (hQ : CFSG.IsQuasisimple Q) (hCent3 : ∀ z ∈ Subgroup.center Q, z ^ 3 = 1)
    {Csub : Subgroup ↥H} [Csub.Normal] {D' : Subgroup Q} [D'.Normal]
    (hD'_center : D' ≤ Subgroup.center Q)
    (hquot : Nonempty (↥H ⧸ Csub ≃* Q ⧸ D'))
    (eHstar : ↥H ⧸ Csub ≃* CFSG.Quasithin.autI hV H) :
    CFSG.IsQuasisimple ↥(CFSG.Quasithin.autI hV H) ∧
      (∀ z ∈ Subgroup.center ↥(CFSG.Quasithin.autI hV H), z ^ 3 = 1) ∧
      CFSG.pCore 2 ↥(CFSG.Quasithin.autI hV H) = ⊥ ∧
      CFSG.Quasithin.autI hV H = quasithinGenFitting (CFSG.Quasithin.autI hV H) := by
  obtain ⟨eHC⟩ := hquot
  let eQbar : ↥(CFSG.Quasithin.autI hV H) ≃* Q ⧸ D' := eHstar.symm.trans eHC
  have hHq : CFSG.IsQuasisimple ↥(CFSG.Quasithin.autI hV H) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eQbar.symm
      (CFSG.LocalCores.quasisimple_central_quotient hQ D' hD'_center).1
  have hCent3star : ∀ z ∈ Subgroup.center ↥(CFSG.Quasithin.autI hV H), z ^ 3 = 1 := by
    have hZQ : Subgroup.center (Q ⧸ D') =
        (Subgroup.center Q).map (QuotientGroup.mk' D') :=
      (CFSG.LocalCores.quasisimple_central_quotient hQ D' hD'_center).2.2
    intro z hz
    have hz' : eQbar z ∈ Subgroup.center (Q ⧸ D') := by
      rw [Subgroup.mem_center_iff]
      intro a
      obtain ⟨b, rfl⟩ := eQbar.surjective a
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz b]
    rw [hZQ] at hz'
    obtain ⟨w, hw, hwz⟩ := hz'
    have h3w : w ^ 3 = 1 := hCent3 w hw
    apply eQbar.injective
    rw [map_pow, ← hwz, ← map_pow, h3w]
    simp
  have hO2 : CFSG.pCore 2 ↥(CFSG.Quasithin.autI hV H) = ⊥ :=
    pCore_eq_bot_of_quasisimple_of_center_pow_three hHq hCent3star
  have hLF : CFSG.Quasithin.autI hV H =
      quasithinGenFitting (CFSG.Quasithin.autI hV H) := by
    refine le_antisymm ?_ (quasithinGenFitting_le _)
    exact CFSG.Quasithin.InternalSec.le_quasithinGenFitting_of_normal le_rfl
      (fun x hx k hk => Subgroup.mul_mem _
        (Subgroup.mul_mem _ hx hk) (Subgroup.inv_mem _ hx)) hHq
  exact ⟨hHq, hCent3star, hO2, hLF⟩

private theorem autI_centerQuot {V : Subgroup G} (hV : IsElemAbelian 2 V)
    {H : Subgroup G} {Q : Type} [Group Q] (hQ : CFSG.IsQuasisimple Q)
    {Csub : Subgroup ↥H} [Csub.Normal] {D' : Subgroup Q} [D'.Normal]
    (hD'_center : D' ≤ Subgroup.center Q)
    (hquot : Nonempty (↥H ⧸ Csub ≃* Q ⧸ D'))
    (eHstar : ↥H ⧸ Csub ≃* CFSG.Quasithin.autI hV H) :
    Nonempty (↥(CFSG.Quasithin.autI hV H) ⧸
        Subgroup.center ↥(CFSG.Quasithin.autI hV H) ≃*
      Q ⧸ Subgroup.center Q) := by
  obtain ⟨eHC⟩ := hquot
  let eQbar : ↥(CFSG.Quasithin.autI hV H) ≃* Q ⧸ D' := eHstar.symm.trans eHC
  have hZQ : Subgroup.center (Q ⧸ D') =
      (Subgroup.center Q).map (QuotientGroup.mk' D') :=
    (CFSG.LocalCores.quasisimple_central_quotient hQ D' hD'_center).2.2
  let eZ : ↥(CFSG.Quasithin.autI hV H) ⧸
      Subgroup.center ↥(CFSG.Quasithin.autI hV H) ≃*
      (Q ⧸ D') ⧸ Subgroup.center (Q ⧸ D') :=
    QuotientGroup.congr _ _ eQbar (Subgroup.map_center_eq eQbar)
  let eZQ : (Q ⧸ D') ⧸ Subgroup.center (Q ⧸ D') ≃*
      Q ⧸ Subgroup.center Q :=
    (QuotientGroup.quotientMulEquivOfEq hZQ).trans
      (QuotientGroup.quotientQuotientEquivQuotient D' (Subgroup.center Q) hD'_center)
  exact ⟨eZ.trans eZQ⟩

private theorem not_isFFModule_autI {V : Subgroup G} (hV : IsElemAbelian 2 V)
    {H : Subgroup G} {Q : Type} [Group Q]
    (hLF : CFSG.Quasithin.autI hV H = quasithinGenFitting (CFSG.Quasithin.autI hV H))
    (hHq : CFSG.IsQuasisimple ↥(CFSG.Quasithin.autI hV H))
    (hO2 : CFSG.pCore 2 ↥(CFSG.Quasithin.autI hV H) = ⊥)
    (hNoFF : NoIrrFFOffender (Q ⧸ Subgroup.center Q))
    (hcenterQuot : Nonempty
      (↥(CFSG.Quasithin.autI hV H) ⧸ Subgroup.center ↥(CFSG.Quasithin.autI hV H) ≃*
        Q ⧸ Subgroup.center Q)) :
    ¬ IsFFModule (CFSG.Quasithin.autI hV H) := by
  intro hFF
  obtain ⟨eY⟩ := hcenterQuot
  exact (not_isFFModule_of_noIrrFFOffender (W := CFSG.Quasithin.IntMod V hV)
    (fun w => by rw [← pow_two]; exact CFSG.Quasithin.IntMod.sq_eq_one w)
    hLF hHq hO2 hNoFF ⟨eY⟩) hFF

private theorem eq_top_subgroupOf_of_central_factor {H : Subgroup G}
    {Rsub Csub Nsub : Subgroup ↥H} [Rsub.Normal]
    (hQbar : CFSG.IsQuasisimple (↥H ⧸ Rsub))
    (hD_center : Csub.map (QuotientGroup.mk' Rsub) ≤
      Subgroup.center (↥H ⧸ Rsub))
    (hfac : (⊤ : Subgroup ↥H) = Nsub ⊔ Csub) (hRN : Rsub ≤ Nsub) :
    Nsub = ⊤ := by
  let mkR : ↥H →* ↥H ⧸ Rsub := QuotientGroup.mk' Rsub
  let D : Subgroup (↥H ⧸ Rsub) := Csub.map mkR
  let Nbar : Subgroup (↥H ⧸ Rsub) := Nsub.map mkR
  haveI : Group.IsPerfect (↥H ⧸ Rsub) := hQbar.1
  have htopD : (⊤ : Subgroup (↥H ⧸ Rsub)) = Nbar ⊔ D := by
    calc (⊤ : Subgroup (↥H ⧸ Rsub)) = (⊤ : Subgroup ↥H).map mkR :=
          (Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Rsub)).symm
      _ = (Nsub ⊔ Csub).map mkR := by rw [hfac]
      _ = Nbar ⊔ D := by rw [Subgroup.map_sup]
  have hNbar_top : Nbar = ⊤ :=
    CFSG.GroupTheory.eq_top_of_sup_le_center_of_isPerfect hD_center htopD.symm
  exact (map_mk'_eq_top_iff hRN).1 hNbar_top

private theorem le_normalizer_thompsonJ_of_subgroupOf_eq_top {H T : Subgroup G}
    (hNtop : (H ⊓ Subgroup.normalizer (thompsonJ T : Set G)).subgroupOf H = ⊤) :
    H ≤ Subgroup.normalizer (thompsonJ T : Set G) := by
  intro x hx
  have hmem : (⟨x, hx⟩ : ↥H) ∈
      (H ⊓ Subgroup.normalizer (thompsonJ T : Set G)).subgroupOf H := by
    rw [hNtop]; exact Subgroup.mem_top _
  exact (Subgroup.mem_subgroupOf.1 hmem).2

private theorem le_centralizer_or_le_normalizer_of_quasisimple
    {H T : Subgroup G} (hT : CFSG.QuasithinUnique.IsSylowTwoOf T H)
    {Q : Type} [Group Q] [Finite Q] (eQ : CFSG.Quasithin.oTwoQuot ↥H ≃* Q)
    (hQ : CFSG.IsQuasisimple Q) (hCent3 : ∀ z ∈ Subgroup.center Q, z ^ 3 = 1)
    (hNoFF : NoIrrFFOffender (Q ⧸ Subgroup.center Q)) :
    H ≤ Subgroup.centralizer
        (CFSG.Quasithin.omegaOneCenterOf (CFSG.Open.pCoreOf 2 H) : Set G) ∨
      H ≤ Subgroup.normalizer (CFSG.Quasithin.thompsonJ T : Set G) := by
  classical
  let R : Subgroup G := CFSG.Open.pCoreOf 2 H
  let V : Subgroup G := CFSG.Quasithin.omegaOneCenterOf R
  obtain ⟨hV0, hVH0, hHN0, hRV0⟩ := omegaOneCenter_pCore_facts H
  have hV : IsElemAbelian 2 V := by simpa [V, R] using hV0
  have hVH : V ≤ H := by simpa [V, R] using hVH0
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := by simpa [V, R] using hHN0
  have hRV : CFSG.Open.pCoreOf 2 H ≤ Subgroup.centralizer (V : Set G) :=
    by simpa [V, R] using hRV0
  by_cases hHC : H ≤ Subgroup.centralizer (V : Set G)
  · exact Or.inl hHC
  · right
    let N : Subgroup G := H ⊓ Subgroup.normalizer (thompsonJ T : Set G)
    let C : Subgroup G := H ⊓ Subgroup.centralizer (V : Set G)
    let Rsub : Subgroup ↥H := CFSG.pCore 2 ↥H
    let Csub : Subgroup ↥H := C.subgroupOf H
    obtain ⟨hRC0, hCsub_normal0, hCsub_ne_top0⟩ := Csub_facts (V := V) hHN hRV hHC
    have hRC : Rsub ≤ Csub := by simpa [Rsub, Csub, C] using hRC0
    have hCsub_normal : Csub.Normal := by simpa [Csub, C] using hCsub_normal0
    have hCsub_ne_top : Csub ≠ ⊤ := by simpa [Csub, C] using hCsub_ne_top0
    let mkR : ↥H →* ↥H ⧸ Rsub := QuotientGroup.mk' Rsub
    let D : Subgroup (↥H ⧸ Rsub) := Csub.map mkR
    let D' : Subgroup Q := D.map eQ.toMonoidHom
    have hD_center : D ≤ Subgroup.center (↥H ⧸ Rsub) := by
      simpa [D, mkR] using (centralFactor_center hCsub_normal hRC eQ hQ hCsub_ne_top).2
    have hD'_center : D' ≤ Subgroup.center Q := by
      simpa [D', D, mkR] using (centralFactor_center hCsub_normal hRC eQ hQ hCsub_ne_top).1
    have hD_normal : D.Normal := hCsub_normal.map _ (QuotientGroup.mk'_surjective Rsub)
    have hD'_normal : D'.Normal := hD_normal.map _ eQ.surjective
    haveI : Csub.Normal := hCsub_normal
    haveI : D'.Normal := hD'_normal
    have hquot : Nonempty (↥H ⧸ Csub ≃* Q ⧸ D') :=
      ⟨(QuotientGroup.quotientQuotientEquivQuotient Rsub Csub hRC).symm.trans
        (QuotientGroup.congr D D' eQ rfl)⟩
    let φ : ↥H →* MulAut (CFSG.Quasithin.IntMod V hV) :=
      CFSG.Quasithin.convHom hV H hHN
    have hφker : φ.ker = Csub := by
      rw [CFSG.Quasithin.ker_convHom]
    let eHstar : ↥H ⧸ Csub ≃* CFSG.Quasithin.autI hV H := by
      have hker : φ.rangeRestrict.ker = Csub := by
        rw [MonoidHom.ker_rangeRestrict, hφker]
      exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        ((QuotientGroup.quotientKerEquivOfSurjective φ.rangeRestrict
          φ.rangeRestrict_surjective).trans
          (MulEquiv.subgroupCongr (CFSG.Quasithin.range_convHom hV H hHN)))
    obtain ⟨hHq, hCent3star, hO2, hLF⟩ :=
      autI_isQuasisimple (V := V) hV hQ hCent3 hD'_center hquot eHstar
    have hcenterQuot := autI_centerQuot (V := V) hV hQ hD'_center hquot eHstar
    have hnotFF : ¬ IsFFModule (CFSG.Quasithin.autI hV H) :=
      not_isFFModule_autI (V := V) hV hLF hHq hO2 hNoFF hcenterQuot
    rcases B2_7 hV hVH hHN hT with ⟨-, hfac⟩ | ⟨-, hFF, -⟩
    · have hQbar : CFSG.IsQuasisimple (↥H ⧸ Rsub) :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv eQ.symm hQ
      have hfacH : (⊤ : Subgroup ↥H) = N.subgroupOf H ⊔ Csub := by
        have h1 : H.subgroupOf H = (N ⊔ C).subgroupOf H :=
          congrArg (fun K => K.subgroupOf H) hfac
        rw [Subgroup.subgroupOf_self] at h1
        rw [h1, Subgroup.subgroupOf_sup inf_le_left inf_le_left]
      have hRN : Rsub ≤ N.subgroupOf H := by
        intro x hx
        rw [Subgroup.mem_subgroupOf]
        have hxR : (x : G) ∈ R := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
        exact ⟨hT.1 (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hT hxR),
          (CFSG.Quasithin.B6.le_normalizer_thompsonJ T)
            (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hT hxR)⟩
      have hNtop : N.subgroupOf H = ⊤ :=
        eq_top_subgroupOf_of_central_factor hQbar hD_center hfacH hRN
      exact le_normalizer_thompsonJ_of_subgroupOf_eq_top hNtop
    · exact (hnotFF hFF).elim

theorem center_statedSU_pow_three {n : ℕ} {F : Type} [Field F] [Finite F]
    [Fact (Nat.Prime 2)] [CharP F 2] (hn : 2 ≤ n) (hF : Nat.card F = (2 ^ n) ^ 2) :
    ∀ z ∈ Subgroup.center (StatedSU 3 (2 ^ n) F), z ^ 3 = 1 := by
  have hnq : ((3 : ℕ), 2 ^ n) ≠ (3, 2) := by
    intro h
    have h2 : 2 ^ n = 2 := congrArg Prod.snd h
    have hle : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    rw [h2] at hle
    norm_num at hle
  intro z hz
  have hZ := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (p := 2) (f := n) (F := F) hF (by norm_num) hnq).2
  rw [hZ] at hz
  obtain ⟨u, hu⟩ := Subgroup.mem_subgroupOf.mp hz
  have hdet := CFSG.LieType.Universal.Unitary.det_eq_one_of_mem_statedSU z.2
  rw [← hu] at hdet
  have hu3 : u ^ 3 = 1 := by
    apply Units.ext
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal]
      using hdet
  apply Subtype.ext
  change (((z : StatedSU 3 (2 ^ n) F) : GL (Fin 3) F) ^ 3) = 1
  rw [← hu, ← map_pow, hu3, map_one]

theorem le_centralizer_or_le_normalizer_thompsonJ
    {G : Type} [Group G] [Finite G] {H T : Subgroup G}
    (hX : (∃ a : ℕ, 1 ≤ a ∧ Nonempty (CFSG.Quasithin.oTwoQuot ↥H ≃* CFSG.Open.Sz a)) ∨
      (∃ n : ℕ, 2 ≤ n ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (2 ^ n) ^ 2 ∧
        (Nonempty (CFSG.Quasithin.oTwoQuot ↥H ≃* CFSG.Open.StatedSU 3 (2 ^ n) F) ∨
          Nonempty (CFSG.Quasithin.oTwoQuot ↥H ≃*
            CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ n) F)))))
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T H) :
    H ≤ Subgroup.centralizer
        (CFSG.Quasithin.omegaOneCenterOf (CFSG.Open.pCoreOf 2 H) : Set G) ∨
      H ≤ Subgroup.normalizer (CFSG.Quasithin.thompsonJ T : Set G) := by
  rcases hX with ⟨a, ha, ⟨e⟩⟩ | ⟨n, hn, F, hFld, hFin, hcard, he⟩
  ·
    refine le_centralizer_or_le_normalizer_of_quasisimple hT e ?_ ?_ ?_
    · exact isQuasisimple_sz a ha
    · intro z hz
      have hz1 : z = 1 := by
        have : z ∈ (⊥ : Subgroup ↥(Sz a)) := by rwa [center_sz a ha] at hz
        exact Subgroup.mem_bot.mp this
      rw [hz1, one_pow]
    · exact CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.noIrrFFOffender_transfer
        (noIrrFFOffender_sz a ha)
        ⟨QuotientGroup.quotientBot.symm.trans
          (QuotientGroup.quotientMulEquivOfEq (center_sz a ha)).symm⟩
  ·
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    letI : Fintype F := Fintype.ofFinite F
    have hcard' : Nat.card F = 2 ^ (2 * n) := by
      rw [hcard, ← pow_mul, Nat.mul_comm n 2]
    have hcard'' : Fintype.card F = 2 ^ (2 * n) := by
      rw [← Nat.card_eq_fintype_card]; exact hcard'
    haveI : CharP F 2 := charP_of_card_eq_prime_pow (f := 2 * n) hcard''
    have hnq : ((3 : ℕ), 2 ^ n) ≠ (3, 2) := by
      intro h
      have h2 : 2 ^ n = 2 := congrArg Prod.snd h
      have hle : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      omega
    have hSUq : CFSG.IsQuasisimple ↥(StatedSU 3 (2 ^ n) F) :=
      (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
        (p := 2) (f := n) (F := F) hcard (by norm_num) hnq).1
    rcases he with ⟨eSU⟩ | ⟨ePSU⟩
    ·
      refine le_centralizer_or_le_normalizer_of_quasisimple hT eSU.some hSUq
        (center_statedSU_pow_three hn hcard) ?_
      have hZ := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
        (p := 2) (f := n) (F := F) hcard (by norm_num) hnq).2
      exact CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.noIrrFFOffender_transfer
        (noIrrFFOffender_statedProjSU3 hn hcard)
        ⟨(QuotientGroup.quotientMulEquivOfEq hZ).symm⟩
    ·
      have hSimple : IsSimpleGroup (StatedProj (StatedSU 3 (2 ^ n) F)) :=
        CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F 2 n hcard 3
          (by norm_num) hnq
      haveI := hSimple
      have hnc := CFSG.Quasithin.F6.InspRest.exists_noncomm_statedProj
        (H := StatedSU 3 (2 ^ n) F) hSUq hSimple
      have hQ : CFSG.IsQuasisimple (StatedProj (StatedSU 3 (2 ^ n) F)) :=
        (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1
      have hZ : Subgroup.center (StatedProj (StatedSU 3 (2 ^ n) F)) = ⊥ :=
        (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).2
      refine le_centralizer_or_le_normalizer_of_quasisimple hT ePSU.some hQ ?_ ?_
      · intro z hz
        have hz1 : z = 1 := by
          have : z ∈ (⊥ : Subgroup (StatedProj (StatedSU 3 (2 ^ n) F))) := by rwa [hZ] at hz
          exact Subgroup.mem_bot.mp this
        rw [hz1, one_pow]
      · exact CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.noIrrFFOffender_transfer
          (noIrrFFOffender_statedProjSU3 hn hcard)
          ⟨QuotientGroup.quotientBot.symm.trans
            (QuotientGroup.quotientMulEquivOfEq hZ).symm⟩


end CFSG.Quasithin.Stroth

end

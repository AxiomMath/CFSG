module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2ComponentLeNormalizerLayer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseFactorization
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PreambleHSU
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27Infra
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalizerEqOfNontrivialNormalInCoatom
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ComponentLayerPerfect
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Equality of controlled normalizer layers in the PSL₂ branch

The forward containment `d.E ≤ componentLayerOf (N_G(X))` is
`secondCase_psl2_component_le_normalizer_layer`.  For the reverse
containment the source (`refs/bender-dihedral-sylow.tex`, L682–687) uses
Fact 1.10(ii): the elements of `F` that normalize `X` induce inner
automorphisms on `E(N_G(X))`, so the layer centralizes them.  That Fact
1.10(ii) centralization step is isolated here as the exported statement
`secondCase_psl2_fact_1_10_ii_centralization` (the exact source-level
implication `componentLayerOf (N_G(X)) ≤ C_G(N_F(X))`, kept separate as the
remaining blocker); the equality theorem below takes it as an explicit
input.

Given that centralization, the reverse containment is model-independent.
`Z(F)` is characteristic in the normal nontrivial subgroup `F ◁ M`, it
centralizes `X`, hence `Z(F) ≤ N_F(X)`, so the layer centralizes `Z(F)`,
and the maximal-normalizer infrastructure
(`normalizer_eq_of_nontrivial_normal_in_coatom`) places
`C_G(Z(F)) ≤ N_G(Z(F)) = M`.  The layer `L ≤ M` is perfect, while
`M / E` is a solvable image of `C_M(t) ≤ H`: `M = E·C_M(t)` by
`secondCase_M_eq_component_sup_centralizer`, and `H = S ⊔ O(H)` is
solvable by `fact_2_preamble_H_eq_SU_proved` (dihedral `2`-group `S` and
odd solvable `O(H)`).  A perfect subgroup of `M` therefore maps trivially
to the solvable quotient `M / E`, giving `L ≤ E`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private local instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-! ## The paper's `N_F(X)`: the elements of `F` normalizing `X` -/

/-- The elements of `F` that normalize `X`, the paper's `N_F(X)`. -/
@[expose] public def normalizerInF {G : Type*} [Group G]
    (F X : Subgroup G) : Subgroup G :=
  F ⊓ Subgroup.normalizer (X : Set G)

/-- The ambient center of `F` lies in `N_F(X)`: it centralizes every
subgroup of `F`. -/
private theorem center_le_normalizerInF {G : Type*} [Group G]
    (F X : Subgroup G) (hXleF : X ≤ F) :
    (Subgroup.center F).map F.subtype ≤ normalizerInF F X := by
  intro z hz
  rcases Subgroup.mem_map.mp hz with ⟨z0, hz0, rfl⟩
  have hzCentF : (z0 : G) ∈ Subgroup.centralizer (F : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have hcomm : (z0 : G) * f = f * (z0 : G) := by
      have hz0c : z0 ∈ Subgroup.center F := hz0
      exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz0c ⟨f, hf⟩)).symm
    exact hcomm.symm
  have hzCentX : (z0 : G) ∈ Subgroup.centralizer (X : Set G) :=
    (Subgroup.centralizer_le (SetLike.coe_mono hXleF)) hzCentF
  have hzNormX : (z0 : G) ∈ Subgroup.normalizer (X : Set G) :=
    Subgroup.centralizer_le_normalizer (X : Set G) hzCentX
  exact ⟨z0.2, hzNormX⟩

/-! ## The Fact 1.10(ii) centralization statement (the remaining blocker) -/

/-- The paper's Fact 1.10(ii) centralization statement, exported separately
as the remaining blocker: in the D-group `N_G(X)` the elements of `F` that
normalize `X` induce inner automorphisms on the layer (Fact 1.10(ii) of
Bender, "Finite groups with dihedral Sylow 2-subgroups"), so the layer
centralizes `N_F(X)`.  This is the exact source-level implication of
L682–687.  The equality theorem below consumes this statement as an
explicit input. -/
@[expose] public def secondCase_psl2_fact_1_10_ii_centralization
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (F X : Subgroup G)
    (_hFleFU : F ≤ c.FU) (_hFleM : F ≤ w.M)
    (_hFcentE : F ≤ Subgroup.centralizer (d.E : Set G))
    (_hXne : X ≠ ⊥) (_hXleF : X ≤ F) : Prop :=
  componentLayerOf (Subgroup.normalizer (X : Set G)) ≤
    Subgroup.centralizer (normalizerInF F X : Set G)

/-! ## Solvability of the involution centralizer `H = C_G(t)` -/

/-- The involution centralizer `H = S ⊔ O(H)` is solvable: `O(H)` is an odd
(hence solvable) normal subgroup and the quotient `H / O(H)` is an image of
the dihedral `2`-group `S`. -/
private theorem secondCase_H_solvable
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) :
    Group.IsSolvable c.H := by
  classical
  let U : Subgroup G := c.U
  let S : Subgroup G := c.S
  have hH : S ⊔ U = c.H := fact_2_preamble_H_eq_SU_proved hmin c
  have hUleH : U ≤ c.H := by
    change oddCoreOf c.H ≤ c.H
    exact Subgroup.map_subtype_le (pPrimeCore 2 c.H)
  have hUnormalH : IsNormalIn U c.H := by
    refine ⟨hUleH, ?_⟩
    intro h hh u hu
    rcases Subgroup.mem_map.mp hu with ⟨u0, hu0, rfl⟩
    refine Subgroup.mem_map.mpr
      ⟨(⟨h, hh⟩ : c.H) * u0 * (⟨h, hh⟩ : c.H)⁻¹, ?_, rfl⟩
    exact (pPrimeCore_normal (p := 2) (G := c.H)).conj_mem u0 hu0 ⟨h, hh⟩
  have hUodd : Odd (Nat.card U) := by
    change Odd (Nat.card (oddCoreOf c.H))
    exact odd_card_oddCoreOf c.H
  have hUsolv : Group.IsSolvable U := odd_order_theorem U hUodd
  have hSleH : S ≤ c.H := centralizerSetup_S_le_H c
  have hS2 : IsPGroup 2 S := c.S.isPGroup'
  let US : Subgroup c.H := U.subgroupOf c.H
  have : US.Normal :=
    (Subgroup.normal_subgroupOf_iff hUleH).2 (fun h k hh hk => hUnormalH.2 k hk h hh)
  have hUsolvH : Group.IsSolvable US := by
    let e : US ≃* U := Subgroup.subgroupOfEquivOfLe hUleH
    let : Group.IsSolvable U := hUsolv
    exact isSolvable_of_mulEquiv e.symm
  let S' : Subgroup c.H := S.subgroupOf c.H
  have hS2' : IsPGroup 2 S' := hS2.comap_subtype
  let q : c.H →* c.H ⧸ US := QuotientGroup.mk' US
  let f : S' →* c.H ⧸ US := q.comp S'.subtype
  have hsup_top : US ⊔ S' = ⊤ := by
    apply le_antisymm
    · intro x hx
      trivial
    · intro x hx
      have hxG : (x : G) ∈ S ⊔ U := by
        rw [hH]
        exact x.2
      have hmap : (US ⊔ S').map c.H.subtype = S ⊔ U := by
        calc
          (US ⊔ S').map c.H.subtype =
              US.map c.H.subtype ⊔ S'.map c.H.subtype := by rw [Subgroup.map_sup]
          _ = U ⊔ S := by
            rw [Subgroup.map_subgroupOf_eq_of_le hUleH,
              Subgroup.map_subgroupOf_eq_of_le hSleH]
          _ = S ⊔ U := sup_comm U S
      have hxmap : (x : G) ∈ (US ⊔ S').map c.H.subtype := by
        rwa [hmap]
      rcases Subgroup.mem_map.mp hxmap with ⟨y, hySup, hyx⟩
      have hyx' : y = x := Subtype.ext hyx
      simpa [hyx'] using hySup
  have hf_surj : Function.Surjective f := by
    intro a
    refine QuotientGroup.induction_on a ?_
    intro h
    have hhSup : h ∈ US ⊔ S' := by
      rw [hsup_top]
      trivial
    rcases (Subgroup.mem_sup_of_normal_left (s := US) (t := S')).mp hhSup with
      ⟨z, hz, e, he, hze⟩
    have hqz : q z = 1 := (QuotientGroup.eq_one_iff (N := US) z).2 hz
    have hqh : q h = q e := by
      calc
        q h = q (z * e) := congrArg q hze.symm
        _ = q z * q e := map_mul q z e
        _ = 1 * q e := by rw [hqz]
        _ = q e := one_mul _
    refine ⟨⟨e, he⟩, ?_⟩
    convert hqh.symm using 1
    · simp [f]
    · exact (QuotientGroup.mk'_apply (N := US) h).symm
  have hQ2 : IsPGroup 2 (c.H ⧸ US) := IsPGroup.of_surjective hS2' f hf_surj
  have hQsolv : Group.IsSolvable (c.H ⧸ US) := isSolvable_of_isPGroup hQ2
  exact isSolvable_of_normal_solvable_quotient_solvable US hUsolvH hQsolv

/-! ## Reverse layer containment for the source-faithful fixed part -/

/-- The layer of the normalizer of a nontrivial `X ≤ F` lies in the
selected PSL₂ component, given the Fact 1.10(ii) centralization of the
layer.  `F` is the source-faithful fixed part: normal in `M` and
nontrivial (whence `Z(F) ≠ 1` characteristic in `F`). -/
public theorem secondCase_psl2_normalizer_layer_eq_component
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (e : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃* PSL2 K))
    (F X : Subgroup G)
    (hFleFU : F ≤ c.FU) (hFleM : F ≤ w.M)
    (hFcentE : F ≤ Subgroup.centralizer (d.E : Set G))
    (hFnormalM : IsNormalIn F w.M)
    (hFne : F ≠ ⊥)
    (hXne : X ≠ ⊥) (hXleF : X ≤ F)
    (hLcentNF : secondCase_psl2_fact_1_10_ii_centralization
      c w d F X hFleFU hFleM hFcentE hXne hXleF) :
    componentLayerOf (Subgroup.normalizer (X : Set G)) = d.E := by
  classical
  let N : Subgroup G := Subgroup.normalizer (X : Set G)
  let L : Subgroup G := componentLayerOf N
  have hforward : d.E ≤ L := by
    simpa [N, L] using secondCase_psl2_component_le_normalizer_layer
      hmin c w d K hK e F X hFleFU hFleM hFcentE hXne hXleF
  let ZF : Subgroup G := (Subgroup.center F).map F.subtype
  have hZFleF : ZF ≤ F := Subgroup.map_subtype_le (Subgroup.center F)
  have hZFleNF : ZF ≤ normalizerInF F X := center_le_normalizerInF F X hXleF
  have hLcentZ : L ≤ Subgroup.centralizer (ZF : Set G) :=
    hLcentNF.trans (Subgroup.centralizer_le (SetLike.coe_mono hZFleNF))
  have hZFnormalM : IsNormalIn ZF w.M :=
    map_characteristic_isNormalIn_of_isNormalIn
      (K := Subgroup.center (↥F)) (hKchar := by infer_instance)
      (hHnormal := hFnormalM)
  have hZFne : ZF ≠ ⊥ := by
    have hFnil : Group.IsNilpotent (↥F) := by
      let e : F.subgroupOf c.FU ≃* F := Subgroup.subgroupOfEquivOfLe hFleFU
      have : Group.IsNilpotent (↥c.FU) := fittingSubgroupOf_isNilpotent c.U
      have : Group.IsNilpotent (F.subgroupOf c.FU) := inferInstance
      exact Group.nilpotent_of_mulEquiv e
    have : Group.IsNilpotent (↥F) := hFnil
    have : Nontrivial F := (Subgroup.nontrivial_iff_ne_bot F).2 hFne
    have hcenter_ne : Subgroup.center F ≠ ⊥ :=
      Group.IsNilpotent.center_ne_bot (G := ↥F)
    intro hbot
    apply hcenter_ne
    exact (Subgroup.map_eq_bot_iff_of_injective
      (H := Subgroup.center F) (f := F.subtype) F.subtype_injective).mp hbot
  have hZFsubnormalM : (ZF.subgroupOf w.M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff (hZFleF.trans hFleM)]
    intro z m hz hm
    exact hZFnormalM.2 m hm z hz
  have hNZF : Subgroup.normalizer (ZF : Set G) = w.M :=
    normalizer_eq_of_nontrivial_normal_in_coatom
      (minimalCounterexample_isSimple hmin) w.M_maximal
      (hZFleF.trans hFleM) hZFne hZFsubnormalM
  have hLleM : L ≤ w.M := by
    intro l hl
    have hlC : l ∈ Subgroup.centralizer (ZF : Set G) := hLcentZ hl
    have hlN : l ∈ Subgroup.normalizer (ZF : Set G) :=
      Subgroup.centralizer_le_normalizer (ZF : Set G) hlC
    rwa [hNZF] at hlN
  -- `M / E` is a solvable image of `C_M(t) ≤ H`, and `H` is solvable.
  let E : Subgroup G := d.E
  let M : Subgroup G := w.M
  let C : Subgroup G := Subgroup.centralizer ({c.t} : Set G) ⊓ w.M
  have hME : M = E ⊔ C := secondCase_M_eq_component_sup_centralizer w d
  have hEnormalM : IsNormalIn E M := d.E_normal
  have hEleM : E ≤ M := hEnormalM.1
  have hCE : C ≤ M := inf_le_right
  have hC : C ≤ c.H := by
    intro c' hc'
    rw [c.H_eq_centralizer]
    exact hc'.1
  have hCsolv : Group.IsSolvable C := by
    let : Group.IsSolvable c.H := secondCase_H_solvable hmin c
    let : Group.IsSolvable (C.subgroupOf c.H) := inferInstance
    exact isSolvable_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hC)
  let EN : Subgroup M := E.subgroupOf M
  have hENnormal : EN.Normal := by
    rw [Subgroup.normal_subgroupOf_iff hEleM]
    intro e m he hm
    exact hEnormalM.2 m hm e he
  let : EN.Normal := hENnormal
  let q : M →* M ⧸ EN := QuotientGroup.mk' EN
  let CM : Subgroup M := C.subgroupOf M
  have hCsolvM : Group.IsSolvable CM := by
    let e : CM ≃* C := Subgroup.subgroupOfEquivOfLe hCE
    let : Group.IsSolvable C := hCsolv
    exact isSolvable_of_mulEquiv e.symm
  have hCMsurj : Function.Surjective (q.comp CM.subtype) := by
    intro a
    refine QuotientGroup.induction_on a ?_
    intro m
    have hmsup : m ∈ EN ⊔ CM := by
      have hmap : (EN ⊔ CM).map M.subtype = E ⊔ C := by
        rw [Subgroup.map_sup]
        simp [EN, CM, Subgroup.map_subgroupOf_eq_of_le hEleM,
          Subgroup.map_subgroupOf_eq_of_le hCE]
      have hmG : (m : G) ∈ E ⊔ C := by
        rw [← hME]
        exact m.2
      have hmx : (m : G) ∈ (EN ⊔ CM).map M.subtype := by
        rwa [hmap]
      rcases Subgroup.mem_map.mp hmx with ⟨y, hySup, hyx⟩
      have hyx' : y = m := Subtype.ext hyx
      simpa [hyx'] using hySup
    rcases (Subgroup.mem_sup_of_normal_left (s := EN) (t := CM)).mp hmsup with
      ⟨e0, he0, c0, hc0, hec0⟩
    have hqe0 : q e0 = 1 := (QuotientGroup.eq_one_iff (N := EN) e0).2 he0
    have hqm : q m = q c0 := by
      calc
        q m = q (e0 * c0) := congrArg q hec0.symm
        _ = q e0 * q c0 := map_mul q e0 c0
        _ = 1 * q c0 := by rw [hqe0]
        _ = q c0 := one_mul _
    refine ⟨⟨c0, hc0⟩, ?_⟩
    convert hqm.symm using 1
    · rfl
    · exact (QuotientGroup.mk'_apply (N := EN) m).symm
  have hMsolvQuot : Group.IsSolvable (M ⧸ EN) :=
    Group.isSolvable_of_surjective (f := q.comp CM.subtype) hCMsurj
  -- A perfect subgroup of `M` maps trivially to the solvable quotient.
  have hLperfect : Group.IsPerfect (L.subgroupOf M) := by
    let e : L.subgroupOf M ≃* L := Subgroup.subgroupOfEquivOfLe hLleM
    let : Group.IsPerfect L := componentLayerOf_isPerfect N
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hLmap_bot : (L.subgroupOf M).map q = ⊥ := by
    by_contra hne
    have : Nontrivial ((L.subgroupOf M).map q) :=
      (Subgroup.nontrivial_iff_ne_bot ((L.subgroupOf M).map q)).2 hne
    let : Group.IsSolvable ((L.subgroupOf M).map q) := by
      let : Group.IsSolvable (M ⧸ EN) := hMsolvQuot
      infer_instance
    have hperf : Group.IsPerfect ((L.subgroupOf M).map q) := by
      let : Group.IsPerfect (L.subgroupOf M) := hLperfect
      exact Group.IsPerfect.map q
    exact Group.IsPerfect.not_isSolvable ((L.subgroupOf M).map q) inferInstance
  have hLleE : L ≤ E := by
    intro l hl
    have hlL : (⟨l, hLleM hl⟩ : M) ∈ L.subgroupOf M :=
      Subgroup.mem_subgroupOf.mpr hl
    have hq1 : q (⟨l, hLleM hl⟩ : M) = 1 := by
      have hmap : q (⟨l, hLleM hl⟩ : M) ∈ (L.subgroupOf M).map q :=
        Subgroup.mem_map.mpr ⟨⟨l, hLleM hl⟩, hlL, rfl⟩
      rw [hLmap_bot] at hmap
      exact Subgroup.mem_bot.mp hmap
    have hlEN : (⟨l, hLleM hl⟩ : M) ∈ EN :=
      (QuotientGroup.eq_one_iff (N := EN) (⟨l, hLleM hl⟩ : M)).mp hq1
    have hlmap : (l : G) ∈ EN.map M.subtype :=
      Subgroup.mem_map.mpr ⟨⟨l, hLleM hl⟩, hlEN, rfl⟩
    have hmap : EN.map M.subtype = E := Subgroup.map_subgroupOf_eq_of_le hEleM
    simpa [E, hmap] using hlmap
  simpa [N, L, E] using le_antisymm hLleE hforward

end CFSG.GorensteinWalter

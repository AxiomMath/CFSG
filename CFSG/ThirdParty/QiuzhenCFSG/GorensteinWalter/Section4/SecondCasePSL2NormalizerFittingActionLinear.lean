module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2NormalizerFittingActionCommon
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2ComponentLeNormalizerLayer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PerfectImageNormalOddIndex
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ComponentLayerPerfect
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PreambleHSU
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Reflection
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Theorem26Core
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseComponentData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Center
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2KleinFourCentralizerEqSelf
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2KleinFourSelfCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourOfCommutingInvolutions
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourMapInjective
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The linear model case of the Fact 1.10(ii) normalizer centralization

For `N = N_G(X)` a D-group whose quotient `N / O₂'(N)` has the
`quotientHasLinearNormalSubgroup` shape (a normal odd-index subgroup
modeled by `PSL₂(K')` or `PGL₂(K')`), every element of `P = N_F(X)`
centralizes the component layer `L = E(N)`.

Given the semilinear Fact 1.10(ii) transport `hInner` (the action of `P` on
`L` is inner by elements of `L`, supplied by the field-projection killing),
the argument is:

1. `f ∈ P` acts on `L` as `inn(ℓ)` for some `ℓ ∈ L` (`hInner`).
2. `f` centralizes the selected component `E` (`hFcentE`), hence so does
   `ℓ`; so the image `ℓ̄` of `ℓ` in `N̄ = N / O₂'(N)` centralizes the image
   `Ebar` of `E`.
3. `Lbar ≤ Lq` and `Ebar ≤ Lq` (`perfect_image_le_normal_odd_index_of_solvable_kernel`).
4. `Ebar` is a central quotient of `E` with the centerless quotient
   `E / Z(E) ≅ PSL₂(K)`; the distinguished involution `t = c.t`, the
   reflection `s`, and their product have non-central images in `Ebar`
   (an element whose image is central in `Ebar` has all its commutators
   with `E` in `E ∩ O₂'(N) ⊆ Z(E)`, hence is central in `E`, contradicting
   that `Z(E)` is odd and the element is an involution).
5. The images `t̄, s̄` of `t` and `s` are distinct commuting involutions in
   `Lq`, generating a Klein four `V'` inside `eL(Ebar)`; `V'` is
   self-centralizing in the `PSL₂(K')` / `PGL₂(K')` model, and no element of
   `V'` is central in `eL(Ebar)` (step 4), so `V' ∩ Z(eL(Ebar)) = 1`.
6. `a := eL(ℓ̄)` centralizes `eL(Ebar)` (step 2), so `a ∈ C(V') = V'` and
   `a ∈ Z(eL(Ebar))`; hence `a = 1`, `ℓ̄ = 1`, and `inn(f̄)` is trivial on
   the image of `L`.  The perfect-layer tail
   (`centralizes_layer_of_quotient_action_trivial`) then gives
   `f ∈ C_G(L)`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- An involution does not lie in an odd-order subgroup. -/
private theorem involution_not_mem_of_odd_card
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (hHodd : Odd (Nat.card H)) {t : G}
    (ht : IsInvolution t) : t ∉ H := by
  intro htH
  have hdvd : orderOf t ∣ Nat.card H := Subgroup.orderOf_dvd_natCard H htH
  have hord2 : orderOf t = 2 := orderOf_eq_prime ht.2 ht.1
  exact hHodd.not_two_dvd_nat (by simpa [hord2] using hdvd)

/-- An element of a group with centerless central quotient is central as
soon as all its commutators with the group are central. -/
private theorem mem_center_of_commutators_central
    {A : Type u} [Group A]
    (hZ : Subgroup.center (A ⧸ Subgroup.center A) = ⊥)
    {x : A} (hx : ∀ z : A, x * z * x⁻¹ * z⁻¹ ∈ Subgroup.center A) :
    x ∈ Subgroup.center A := by
  classical
  let q : A →* A ⧸ Subgroup.center A := QuotientGroup.mk' (Subgroup.center A)
  have hqcent : q x ∈ Subgroup.center (A ⧸ Subgroup.center A) := by
    rw [Subgroup.mem_center_iff]
    intro y
    refine QuotientGroup.induction_on y ?_
    intro z
    have h1 : q (x * z * (z * x)⁻¹) = 1 := by
      apply (QuotientGroup.eq_one_iff (N := Subgroup.center A) (x * z * (z * x)⁻¹)).2
      have hxz : x * z * (z * x)⁻¹ = x * z * x⁻¹ * z⁻¹ := by group
      rw [hxz]
      exact hx z
    calc
      q z * q x = q (z * x) := (map_mul q z x).symm
      _ = q (x * z) := by
        have hq1 : q (x * z * (z * x)⁻¹) = 1 := h1
        calc
          q (z * x) = 1 * q (z * x) := (one_mul _).symm
          _ = q (x * z * (z * x)⁻¹) * q (z * x) := by rw [hq1]
          _ = q ((x * z * (z * x)⁻¹) * (z * x)) := (map_mul q _ _).symm
          _ = q (x * z) := by
            congr 1
            group
      _ = q x * q z := map_mul q x z
  have hqbot : q x ∈ (⊥ : Subgroup (A ⧸ Subgroup.center A)) := by
    rw [← hZ]
    exact hqcent
  have hq1 : q x = 1 := Subgroup.mem_bot.mp hqbot
  exact (QuotientGroup.eq_one_iff (N := Subgroup.center A) x).mp hq1

/-- The elements of a Klein four generated by two commuting involutions. -/
private theorem kleinFour_mem_cases
    {G : Type u} [Group G] [Finite G]
    {a b : G} (V : Subgroup G) (hV : IsKleinFour V)
    (haV : a ∈ V) (hbV : b ∈ V)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b)
    {w : G} (hwV : w ∈ V) :
    w = a * b ∨ w = a ∨ w = b ∨ w = 1 := by
  let : IsKleinFour V := hV
  let : Fintype (↥V) := Fintype.ofFinite (↥V)
  let : DecidableEq (↥V) := Classical.decEq _
  let aV : V := ⟨a, haV⟩
  let bV : V := ⟨b, hbV⟩
  let wV : V := ⟨w, hwV⟩
  have haVne : aV ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
  have hbVne : bV ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  have habVne : aV ≠ bV := fun h => hab (congrArg Subtype.val h)
  have huniv : ({aV * bV, aV, bV, (1 : V)} : Finset V) = Finset.univ :=
    IsKleinFour.eq_finset_univ haVne hbVne habVne
  have hwmem : wV ∈ ({aV * bV, aV, bV, (1 : V)} : Finset V) := by
    rw [huniv]
    exact Finset.mem_univ wV
  simp only [Finset.mem_insert, Finset.mem_singleton] at hwmem
  rcases hwmem with h1 | h2 | h3 | h4
  · exact Or.inl (congrArg Subtype.val h1)
  · exact Or.inr (Or.inl (congrArg Subtype.val h2))
  · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val h3)))
  · exact Or.inr (Or.inr (Or.inr (congrArg Subtype.val h4)))

/-- If the image of an element of `E` in the quotient is central in the
image of `E`, then the element is central in `E`: its commutators with `E`
lie in `E ∩ O₂'(N) ⊆ Z(E)`, and `E / Z(E)` is centerless. -/
private theorem mem_center_of_quotient_center_mem
    {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) (O : Subgroup N) [O.Normal]
    (E : Subgroup G) (hEleN : E ≤ N)
    (hEO : ∀ e : E, (e : G) ∈ O.map N.subtype → e ∈ Subgroup.center E)
    (hZq : Subgroup.center (E ⧸ Subgroup.center E) = ⊥)
    (x : E)
    (hxEbar : QuotientGroup.mk' O ⟨(x : G), hEleN x.2⟩ ∈
      (E.subgroupOf N).map (QuotientGroup.mk' O))
    (hxZbar : (⟨QuotientGroup.mk' O ⟨(x : G), hEleN x.2⟩, hxEbar⟩ :
        (E.subgroupOf N).map (QuotientGroup.mk' O)) ∈
      Subgroup.center ((E.subgroupOf N).map (QuotientGroup.mk' O))) :
  x ∈ Subgroup.center E := by
  classical
  let q : N →* N ⧸ O := QuotientGroup.mk' O
  let Ebar : Subgroup (N ⧸ O) := (E.subgroupOf N).map q
  have hcommO : ∀ z : E,
      (x : G) * (z : G) * (x : G)⁻¹ * (z : G)⁻¹ ∈ O.map N.subtype := by
    intro z
    let zN : N := ⟨(z : G), hEleN z.2⟩
    have hzEbar : q zN ∈ Ebar := by
      dsimp [Ebar]
      exact Subgroup.mem_map.mpr ⟨zN, Subgroup.mem_subgroupOf.mpr z.2, rfl⟩
    have hqeq : q ⟨(x : G), hEleN x.2⟩ * q zN =
        q zN * q ⟨(x : G), hEleN x.2⟩ := by
      have hc := (Subgroup.mem_center_iff.mp hxZbar) ⟨q zN, hzEbar⟩
      change q ⟨(x : G), hEleN x.2⟩ * q zN =
        q zN * q ⟨(x : G), hEleN x.2⟩
      exact congrArg Subtype.val hc.symm
    have hmemO : ⟨(x : G), hEleN x.2⟩ * zN * (zN * ⟨(x : G), hEleN x.2⟩)⁻¹ ∈ O := by
      have hqeq' : q (⟨(x : G), hEleN x.2⟩ * zN) =
          q (zN * ⟨(x : G), hEleN x.2⟩) := by
        rwa [← map_mul, ← map_mul] at hqeq
      have h1 : q (⟨(x : G), hEleN x.2⟩ * zN * (zN * ⟨(x : G), hEleN x.2⟩)⁻¹) = 1 := by
        calc
          q (⟨(x : G), hEleN x.2⟩ * zN * (zN * ⟨(x : G), hEleN x.2⟩)⁻¹) =
              q (⟨(x : G), hEleN x.2⟩ * zN) * (q (zN * ⟨(x : G), hEleN x.2⟩))⁻¹ := by
                rw [map_mul, map_inv]
          _ = 1 := by
            rw [hqeq']
            simp
      change (QuotientGroup.mk' O)
        (⟨(x : G), hEleN x.2⟩ * zN * (zN * ⟨(x : G), hEleN x.2⟩)⁻¹) = 1 at h1
      let v : N :=
        ⟨(x : G), hEleN x.2⟩ * zN * (zN * ⟨(x : G), hEleN x.2⟩)⁻¹
      have h1v : (QuotientGroup.mk' O) v = 1 := by
        simpa only [v] using h1
      exact (QuotientGroup.eq_one_iff (N := O) v).mp h1v
    refine Subgroup.mem_map.mpr
      ⟨⟨(x : G), hEleN x.2⟩ * zN * (zN * ⟨(x : G), hEleN x.2⟩)⁻¹, hmemO, ?_⟩
    change (x : G) * (z : G) * (z * (x : G))⁻¹ =
      (x : G) * (z : G) * (x : G)⁻¹ * (z : G)⁻¹
    group
  have hcommZ : ∀ z : E, x * z * x⁻¹ * z⁻¹ ∈ Subgroup.center E := by
    intro z
    have hmemE : (x : G) * (z : G) * (x : G)⁻¹ * (z : G)⁻¹ ∈ E :=
      E.mul_mem (E.mul_mem (E.mul_mem x.2 z.2) (E.inv_mem x.2)) (E.inv_mem z.2)
    have hz : (⟨(x : G) * (z : G) * (x : G)⁻¹ * (z : G)⁻¹, hmemE⟩ : E) ∈
        Subgroup.center E :=
      hEO ⟨(x : G) * (z : G) * (x : G)⁻¹ * (z : G)⁻¹, hmemE⟩ (hcommO z)
    change (⟨(x : G) * (z : G) * (x : G)⁻¹ * (z : G)⁻¹, hmemE⟩ : E) ∈
      Subgroup.center E
    exact hz
  exact mem_center_of_commutators_central hZq hcommZ

/-- The linear-model Fact 1.10(ii) centralization for a single abstract
model: given the semilinear inner-action transport and a normal odd-index
`Lq` modeled by `M` whose Klein fours are self-centralizing, the layer of
`N_G(X)` centralizes `N_F(X)`. -/
private theorem secondCase_psl2_linear_quotient_centralization_of_model
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (e : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃* PSL2 K))
    (F X : Subgroup G)
    (s : d.E)
    (_hF_eq : F = centralizerIn (c.FU ⊓ w.M) (s : G))
    (hrefl : c.IsReflection (s : G))
    (hFleFU : F ≤ c.FU) (hFleM : F ≤ w.M)
    (hFcentE : F ≤ Subgroup.centralizer (d.E : Set G))
    (hXne : X ≠ ⊥) (hXleF : X ≤ F)
    (Lq : Subgroup (Subgroup.normalizer (X : Set G) ⧸
      pPrimeCore 2 (Subgroup.normalizer (X : Set G))))
    (hLqnormal : Lq.Normal) (hLqindex : Odd Lq.index)
    (M : Type u) [Group M] [Finite M]
    (eL : Lq ≃* M)
    (hself : ∀ (V : Subgroup M), IsKleinFour V →
      Subgroup.centralizer (V : Set M) = V)
    (hInner : secondCase_psl2_normalizer_innerAction c X) :
    secondCase_psl2_fact_1_10_ii_centralization c w d F X
      hFleFU hFleM hFcentE hXne hXleF := by
  classical
  let N : Subgroup G := Subgroup.normalizer (X : Set G)
  let L : Subgroup G := componentLayerOf N
  let O : Subgroup N := pPrimeCore 2 N
  let : O.Normal := by
    dsimp [O]
    infer_instance
  let q : N →* N ⧸ O := QuotientGroup.mk' O
  let Oamb : Subgroup G := O.map N.subtype
  let EN : Subgroup N := d.E.subgroupOf N
  let Ebar : Subgroup (N ⧸ O) := EN.map q
  let LN : Subgroup N := L.subgroupOf N
  let Lbar : Subgroup (N ⧸ O) := LN.map q
  have hLleN : L ≤ N := (componentLayerOf_isNormalIn N).1
  have hLnorm : IsNormalIn L N := componentLayerOf_isNormalIn N
  have hforward : d.E ≤ L := by
    simpa [N, L] using secondCase_psl2_component_le_normalizer_layer
      hmin c w d K hK e F X hFleFU hFleM hFcentE hXne hXleF
  have hEleN : d.E ≤ N := hforward.trans hLleN
  have hOodd : Odd (Nat.card O) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := N))
  have hOsolv : IsSolvable O := odd_order_theorem O hOodd
  have hOamb_odd : Odd (Nat.card Oamb) := by
    have hcard : Nat.card Oamb = Nat.card O :=
      Subgroup.card_map_of_injective (f := N.subtype) N.subtype_injective
    exact hcard ▸ hOodd
  have hOamb_normal_N : IsNormalIn Oamb N := by
    refine ⟨Subgroup.map_subtype_le O, ?_⟩
    intro n hn o ho
    rcases Subgroup.mem_map.mp ho with ⟨o0, ho0, rfl⟩
    exact Subgroup.mem_map.mpr
      ⟨(⟨n, hn⟩ : N) * o0 * (⟨n, hn⟩ : N)⁻¹,
        (pPrimeCore_normal (p := 2) (G := N)).conj_mem o0 ho0 ⟨n, hn⟩, rfl⟩
  have hLperf : Group.IsPerfect L := componentLayerOf_isPerfect N
  have hLperfLN : Group.IsPerfect LN := by
    let eLN : LN ≃* L := Subgroup.subgroupOfEquivOfLe hLleN
    let : Group.IsPerfect L := hLperf
    exact Group.IsPerfect.ofSurjective
      (f := eLN.symm.toMonoidHom) eLN.symm.surjective
  have hL_ne_bot : L ≠ ⊥ := by
    intro hbot
    have htL : c.t ∈ L := hforward d.t_mem_E
    have ht1 : c.t = 1 := by simpa [hbot] using htL
    exact c.t_involution.1 ht1
  have hLne : LN ≠ ⊥ := by
    intro hbot
    have hmap : LN.map N.subtype = L := Subgroup.map_subgroupOf_eq_of_le hLleN
    rw [hbot, Subgroup.map_bot] at hmap
    exact hL_ne_bot hmap.symm
  have hENperf : Group.IsPerfect EN := by
    let eEN : EN ≃* d.E := Subgroup.subgroupOfEquivOfLe hEleN
    let : Group.IsPerfect d.E := (Group.isPerfect_def).2 d.E_component.2.2.2.1
    exact Group.IsPerfect.ofSurjective
      (f := eEN.symm.toMonoidHom) eEN.symm.surjective
  have hENne : EN ≠ ⊥ := by
    intro hbot
    apply (Subgroup.nontrivial_iff_ne_bot d.E).mp d.E_component.2.2.1
    have hmap : EN.map N.subtype = d.E := Subgroup.map_subgroupOf_eq_of_le hEleN
    rw [hbot, Subgroup.map_bot] at hmap
    exact hmap.symm
  -- the images of the layer and the component lie in the model `Lq`
  have hLbarData := @perfect_image_le_normal_odd_index_of_solvable_kernel
    N _ _ LN hLperfLN hLne O (inferInstance : O.Normal) hOsolv Lq hLqnormal hLqindex
  have hLbarLq : Lbar ≤ Lq := by simpa [Lbar, q] using hLbarData.2.2
  have hEbarData := @perfect_image_le_normal_odd_index_of_solvable_kernel
    N _ _ EN hENperf hENne O (inferInstance : O.Normal) hOsolv Lq hLqnormal hLqindex
  have hEbarLq : Ebar ≤ Lq := by simpa [Ebar, q] using hEbarData.2.2
  -- `E ∩ O₂'(N) ≤ Z(E)`: an odd normal subgroup of the quasisimple `E`.
  have hEO_normal_E : IsNormalIn (d.E ⊓ Oamb) d.E := by
    refine ⟨inf_le_left, ?_⟩
    intro e he x hx
    exact ⟨d.E.mul_mem (d.E.mul_mem he hx.1) (d.E.inv_mem he),
      hOamb_normal_N.2 e (hEleN he) x hx.2⟩
  have hEO_normal : ((d.E ⊓ Oamb).subgroupOf d.E).Normal := by
    rw [Subgroup.normal_subgroupOf_iff (show d.E ⊓ Oamb ≤ d.E from inf_le_left)]
    intro a b ha hb
    exact hEO_normal_E.2 b hb a ha
  have hEO_ne_top : (d.E ⊓ Oamb).subgroupOf d.E ≠ ⊤ := by
    intro htop
    have htEO : (⟨c.t, d.t_mem_E⟩ : d.E) ∈ (d.E ⊓ Oamb).subgroupOf d.E := by
      rw [htop]
      trivial
    have htO : c.t ∈ Oamb := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp htEO)).2
    exact involution_not_mem_of_odd_card Oamb hOamb_odd c.t_involution htO
  have hEO_le_Z : (d.E ⊓ Oamb).subgroupOf d.E ≤ Subgroup.center d.E := by
    rcases normal_subgroup_le_center_or_eq_top d.E_component.2.2
        ((d.E ⊓ Oamb).subgroupOf d.E) hEO_normal with hle | htop
    · exact hle
    · exact False.elim (hEO_ne_top htop)
  -- the centerless central quotient of the component
  have hZq : Subgroup.center (d.E ⧸ Subgroup.center d.E) = ⊥ :=
    center_eq_bot_of_mulEquiv e.some (psl2_center_eq_bot K)
  have hZamb_odd : Odd (Nat.card ((Subgroup.center d.E).map d.E.subtype)) := by
    have hcard : Nat.card ((Subgroup.center d.E).map d.E.subtype) =
        Nat.card (Subgroup.center d.E) :=
      Subgroup.card_map_of_injective (f := d.E.subtype) d.E.subtype_injective
    rw [hcard]
    exact d.center_odd
  have hEO : ∀ e : d.E, (e : G) ∈ Oamb → e ∈ Subgroup.center d.E := by
    intro e he
    exact hEO_le_Z (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨e.2, he⟩))
  -- the distinguished involution and the reflection in `N`, and their
  -- images in `N̄`
  have hts : Commute c.t (s : G) := by
    have hsH : (s : G) ∈ c.H := centralizerSetup_S_le_H c hrefl.1
    rw [c.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff] at hsH
    exact hsH.symm
  have htsGne : c.t ≠ (s : G) := by
    intro h
    apply hrefl.2
    exact h ▸ c.t_mem_S0
  have hsI : IsInvolution (s : G) := centralizerSetup_reflection_isInvolution c hrefl
  let tN : N := ⟨c.t, hLleN (hforward d.t_mem_E)⟩
  let sN : N := ⟨(s : G), hLleN (hforward s.2)⟩
  let tbar : N ⧸ O := q tN
  let sbar : N ⧸ O := q sN
  have htN_sq : tN * tN = 1 := by
    apply Subtype.ext
    change c.t * c.t = (1 : G)
    simpa [pow_two] using c.t_involution.2
  have hsN_sq : sN * sN = 1 := by
    apply Subtype.ext
    change (s : G) * (s : G) = (1 : G)
    simpa [pow_two] using hsI.2
  have htbar_ne1 : tbar ≠ 1 := by
    intro h
    have htN_O : tN ∈ O := (QuotientGroup.eq_one_iff (N := O) tN).mp h
    exact involution_not_mem_of_odd_card Oamb hOamb_odd c.t_involution
      (Subgroup.mem_map.mpr ⟨tN, htN_O, rfl⟩)
  have hsbar_ne1 : sbar ≠ 1 := by
    intro h
    have hsN_O : sN ∈ O := (QuotientGroup.eq_one_iff (N := O) sN).mp h
    exact involution_not_mem_of_odd_card Oamb hOamb_odd hsI
      (Subgroup.mem_map.mpr ⟨sN, hsN_O, rfl⟩)
  have htbar_sq : tbar * tbar = 1 := by
    change q tN * q tN = 1
    rw [← map_mul, htN_sq, map_one]
  have hsbar_sq : sbar * sbar = 1 := by
    change q sN * q sN = 1
    rw [← map_mul, hsN_sq, map_one]
  have htbarI : IsInvolution tbar := ⟨htbar_ne1, by simpa [pow_two] using htbar_sq⟩
  have hsbarI : IsInvolution sbar := ⟨hsbar_ne1, by simpa [pow_two] using hsbar_sq⟩
  have hcomm_tN_sN : Commute tN sN := by
    apply Subtype.ext
    change c.t * (s : G) = (s : G) * c.t
    exact hts
  have hcomm_tbar_sbar : Commute tbar sbar := by
    change q tN * q sN = q sN * q tN
    rw [← map_mul, ← map_mul]
    exact congrArg q hcomm_tN_sN
  have htsI : IsInvolution (c.t * (s : G)) := by
    constructor
    · intro h1
      apply htsGne
      have hsG_inv : (s : G)⁻¹ = (s : G) :=
        inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hsI.2)
      calc
        c.t = (c.t * (s : G)) * (s : G)⁻¹ := by group
        _ = (1 : G) * (s : G)⁻¹ := by rw [h1]
        _ = (s : G) := by simp [hsG_inv]
    · have ht2 : c.t * c.t = 1 := by simpa [pow_two] using c.t_involution.2
      have hs2 : (s : G) * (s : G) = 1 := by simpa [pow_two] using hsI.2
      rw [pow_two]
      calc
        (c.t * (s : G)) * (c.t * (s : G)) = c.t * ((s : G) * c.t) * (s : G) := by group
        _ = c.t * (c.t * (s : G)) * (s : G) := by rw [hts]
        _ = (c.t * c.t) * ((s : G) * (s : G)) := by group
        _ = 1 := by rw [ht2, hs2]; simp
  have hts_div_notO : tN * sN⁻¹ ∉ O := by
    intro h
    apply involution_not_mem_of_odd_card Oamb hOamb_odd htsI
    refine Subgroup.mem_map.mpr ⟨tN * sN⁻¹, h, ?_⟩
    change (c.t) * (s : G)⁻¹ = (c.t) * (s : G)
    congr 1
    exact inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hsI.2)
  have htsbar : tbar ≠ sbar := by
    intro h
    apply hts_div_notO
    have hdiv := (QuotientGroup.eq_iff_div_mem.mp h)
    rwa [div_eq_mul_inv] at hdiv
  -- the images lie in `Lbar ≤ Lq` and in `Ebar`
  have htbar_mem_Lbar : tbar ∈ Lbar :=
    Subgroup.mem_map.mpr ⟨tN, Subgroup.mem_subgroupOf.mpr (hforward d.t_mem_E), rfl⟩
  have hsbar_mem_Lbar : sbar ∈ Lbar :=
    Subgroup.mem_map.mpr ⟨sN, Subgroup.mem_subgroupOf.mpr (hforward s.2), rfl⟩
  have htbar_mem_Ebar : tbar ∈ Ebar :=
    Subgroup.mem_map.mpr ⟨tN, Subgroup.mem_subgroupOf.mpr d.t_mem_E, rfl⟩
  have hsbar_mem_Ebar : sbar ∈ Ebar :=
    Subgroup.mem_map.mpr ⟨sN, Subgroup.mem_subgroupOf.mpr s.2, rfl⟩
  have htbar_Lq : tbar ∈ Lq := hLbarLq htbar_mem_Lbar
  have hsbar_Lq : sbar ∈ Lq := hLbarLq hsbar_mem_Lbar
  let tbarL : Lq := ⟨tbar, htbar_Lq⟩
  let sbarL : Lq := ⟨sbar, hsbar_Lq⟩
  have htbarL_ne1 : tbarL ≠ 1 := fun h => htbar_ne1 (congrArg Subtype.val h)
  have hsbarL_ne1 : sbarL ≠ 1 := fun h => hsbar_ne1 (congrArg Subtype.val h)
  have htbarL_sq : tbarL * tbarL = 1 := by
    apply Subtype.ext
    simpa using htbar_sq
  have hsbarL_sq : sbarL * sbarL = 1 := by
    apply Subtype.ext
    simpa using hsbar_sq
  have htbarLI : IsInvolution tbarL := ⟨htbarL_ne1, by simpa [pow_two] using htbarL_sq⟩
  have hsbarLI : IsInvolution sbarL := ⟨hsbarL_ne1, by simpa [pow_two] using hsbarL_sq⟩
  have htsbarL : tbarL ≠ sbarL := fun h => htsbar (congrArg Subtype.val h)
  have hcomm_tbarL_sbarL : Commute tbarL sbarL := by
    apply Subtype.ext
    change tbar * sbar = sbar * tbar
    exact hcomm_tbar_sbar
  -- the Klein four generated by `tbarL` and `sbarL`
  obtain ⟨V0, hV0, htbarV0, hsbarV0⟩ :=
    exists_kleinFour_of_commuting_involutions tbarL sbarL htbarLI hsbarLI
      htsbarL hcomm_tbarL_sbarL
  let V0N : Subgroup (N ⧸ O) := V0.map Lq.subtype
  have hV0N : IsKleinFour V0N :=
    isKleinFour_map_of_injective V0 hV0 Lq.subtype Lq.subtype_injective
  have hV0N_le_Ebar : V0N ≤ Ebar := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨w, hwV0, rfl⟩
    rcases kleinFour_mem_cases V0 hV0 htbarV0 hsbarV0 htbarL_ne1 hsbarL_ne1
        htsbarL hwV0 with
      hw | hw | hw | hw
    · rw [hw]
      change (tbar * sbar : N ⧸ O) ∈ Ebar
      exact Ebar.mul_mem htbar_mem_Ebar hsbar_mem_Ebar
    · rw [hw]
      change (tbar : N ⧸ O) ∈ Ebar
      exact htbar_mem_Ebar
    · rw [hw]
      change (sbar : N ⧸ O) ∈ Ebar
      exact hsbar_mem_Ebar
    · rw [hw]
      change (1 : N ⧸ O) ∈ Ebar
      exact Ebar.one_mem
  -- the images of `t`, `s`, and `t·s` are not central in `Ebar`
  have htsE : (c.t * (s : G)) ∈ d.E :=
    d.E.mul_mem d.t_mem_E s.2
  have htbar_not_cent : ∀ hv : tbar ∈ Ebar,
      ¬ (⟨tbar, hv⟩ : Ebar) ∈ Subgroup.center Ebar := by
    intro hv hz
    have htZ : (⟨c.t, d.t_mem_E⟩ : d.E) ∈ Subgroup.center d.E :=
      mem_center_of_quotient_center_mem N O d.E hEleN hEO hZq
        ⟨c.t, d.t_mem_E⟩ hv hz
    exact involution_not_mem_of_odd_card
      ((Subgroup.center d.E).map d.E.subtype) hZamb_odd c.t_involution
      (Subgroup.mem_map.mpr ⟨⟨c.t, d.t_mem_E⟩, htZ, rfl⟩)
  have hsbar_not_cent : ∀ hv : sbar ∈ Ebar,
      ¬ (⟨sbar, hv⟩ : Ebar) ∈ Subgroup.center Ebar := by
    intro hv hz
    have hsZ : (⟨(s : G), s.2⟩ : d.E) ∈ Subgroup.center d.E :=
      mem_center_of_quotient_center_mem N O d.E hEleN hEO hZq
        ⟨(s : G), s.2⟩ hv hz
    exact involution_not_mem_of_odd_card
      ((Subgroup.center d.E).map d.E.subtype) hZamb_odd hsI
      (Subgroup.mem_map.mpr ⟨⟨(s : G), s.2⟩, hsZ, rfl⟩)
  have htsbar_mem_Ebar : (tbar * sbar) ∈ Ebar :=
    Ebar.mul_mem htbar_mem_Ebar hsbar_mem_Ebar
  have htsbar_not_cent : ∀ hv : (tbar * sbar) ∈ Ebar,
      ¬ (⟨tbar * sbar, hv⟩ : Ebar) ∈ Subgroup.center Ebar := by
    intro hv hz
    have htsbar_mem_Ebar' : q ⟨(c.t * (s : G)), hEleN htsE⟩ ∈ Ebar := by
      have hN : ⟨(c.t * (s : G)), hEleN htsE⟩ = tN * sN := by
        apply Subtype.ext
        change (c.t * (s : G)) = (c.t) * (s : G)
        rfl
      rw [hN, map_mul]
      exact Ebar.mul_mem htbar_mem_Ebar hsbar_mem_Ebar
    have htsZ : (⟨c.t * (s : G), htsE⟩ : d.E) ∈ Subgroup.center d.E :=
      mem_center_of_quotient_center_mem N O d.E hEleN hEO hZq
        ⟨c.t * (s : G), htsE⟩ htsbar_mem_Ebar' hz
    exact involution_not_mem_of_odd_card
      ((Subgroup.center d.E).map d.E.subtype) hZamb_odd htsI
      (Subgroup.mem_map.mpr ⟨⟨c.t * (s : G), htsE⟩, htsZ, rfl⟩)
  have hV0N_cent_inter :
      ∀ z : Ebar, (z : N ⧸ O) ∈ V0N → z ∈ Subgroup.center Ebar →
        (z : N ⧸ O) = 1 := by
    intro z hzV hzZ
    rcases Subgroup.mem_map.mp hzV with ⟨w, hwV0, hwz⟩
    rcases kleinFour_mem_cases V0 hV0 htbarV0 hsbarV0 htbarL_ne1 hsbarL_ne1
        htsbarL hwV0 with
      hw | hw | hw | hw
    · exfalso
      have hz : z = (⟨tbar * sbar, htsbar_mem_Ebar⟩ : Ebar) := by
        apply Subtype.ext
        calc
          z.1 = (z : N ⧸ O) := rfl
          _ = (w : N ⧸ O) := hwz.symm
          _ = ((tbarL * sbarL : Lq) : N ⧸ O) :=
            congrArg (fun zz : Lq => (zz : N ⧸ O)) hw
          _ = tbar * sbar := rfl
      have hzZ' : (⟨tbar * sbar, htsbar_mem_Ebar⟩ : Ebar) ∈
          Subgroup.center Ebar := by
        rwa [← hz]
      exact htsbar_not_cent htsbar_mem_Ebar hzZ'
    · exfalso
      have hz : z = (⟨tbar, htbar_mem_Ebar⟩ : Ebar) := by
        apply Subtype.ext
        calc
          z.1 = (z : N ⧸ O) := rfl
          _ = (w : N ⧸ O) := hwz.symm
          _ = ((tbarL : Lq) : N ⧸ O) :=
            congrArg (fun zz : Lq => (zz : N ⧸ O)) hw
          _ = tbar := rfl
      have hzZ' : (⟨tbar, htbar_mem_Ebar⟩ : Ebar) ∈ Subgroup.center Ebar := by
        rwa [← hz]
      exact htbar_not_cent htbar_mem_Ebar hzZ'
    · exfalso
      have hz : z = (⟨sbar, hsbar_mem_Ebar⟩ : Ebar) := by
        apply Subtype.ext
        calc
          z.1 = (z : N ⧸ O) := rfl
          _ = (w : N ⧸ O) := hwz.symm
          _ = ((sbarL : Lq) : N ⧸ O) :=
            congrArg (fun zz : Lq => (zz : N ⧸ O)) hw
          _ = sbar := rfl
      have hzZ' : (⟨sbar, hsbar_mem_Ebar⟩ : Ebar) ∈ Subgroup.center Ebar := by
        rwa [← hz]
      exact hsbar_not_cent hsbar_mem_Ebar hzZ'
    · have hz1 : (z : N ⧸ O) = (w : N ⧸ O) := hwz.symm
      simpa [hz1, hw]
  -- the layer centralizes the odd core
  have hLcentO : L ≤ Subgroup.centralizer (Oamb : Set G) :=
    layer_centralizes_oddCore N
  let ELq : Subgroup Lq := Ebar.subgroupOf Lq
  let EM : Subgroup M := ELq.map eL.toMonoidHom
  change componentLayerOf (Subgroup.normalizer (X : Set G)) ≤
    Subgroup.centralizer (normalizerInF F X : Set G)
  rw [Subgroup.le_centralizer_iff]
  intro f hfP
  have hfF : f ∈ F := (Subgroup.mem_inf.mp hfP).1
  have hfN : f ∈ N := (Subgroup.mem_inf.mp hfP).2
  obtain ⟨ℓ, hℓL, hℓconj⟩ := hInner f ⟨hFleFU hfF, hfN⟩
  -- `ℓ` centralizes the selected component: `f` does (`hFcentE`), and the
  -- actions of `f` and `ℓ` agree on the layer
  have hℓcentE : ℓ ∈ Subgroup.centralizer (d.E : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hfx : f * x * f⁻¹ = x := by
      have hc : f * x = x * f := ((Subgroup.mem_centralizer_iff.mp (hFcentE hfF)) x hx).symm
      calc
        f * x * f⁻¹ = (x * f) * f⁻¹ := by rw [hc]
        _ = x := by group
    have hℓx : ℓ * x * ℓ⁻¹ = x :=
      (hℓconj x (hforward hx)).symm.trans hfx
    exact (mul_inv_eq_iff_eq_mul.mp hℓx).symm
  let ℓN : N := ⟨ℓ, hLleN hℓL⟩
  let ℓbar : N ⧸ O := q ℓN
  have hℓbar_mem_Lbar : ℓbar ∈ Lbar :=
    Subgroup.mem_map.mpr ⟨ℓN, Subgroup.mem_subgroupOf.mpr hℓL, rfl⟩
  have hℓbar_Lq : ℓbar ∈ Lq := hLbarLq hℓbar_mem_Lbar
  let ℓbarL : Lq := ⟨ℓbar, hℓbar_Lq⟩
  have hℓbarC : ℓbar ∈ Subgroup.centralizer (Ebar : Set (N ⧸ O)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨x, hxEN, rfl⟩
    have hxE : (x : G) ∈ d.E := Subgroup.mem_subgroupOf.mp hxEN
    have hℓx : ℓ * (x : G) * ℓ⁻¹ = (x : G) := by
      have hc := Subgroup.mem_centralizer_iff.mp hℓcentE (x : G) hxE
      calc
        ℓ * (x : G) * ℓ⁻¹ = ((x : G) * ℓ) * ℓ⁻¹ := by rw [← hc]
        _ = (x : G) := by group
    change q x * q ℓN = q ℓN * q x
    rw [← map_mul, ← map_mul]
    apply congrArg q
    apply Subtype.ext
    exact (mul_inv_eq_iff_eq_mul.mp hℓx).symm
  -- `a := eL(ℓ̄)` centralizes `eL(Ebar)`, and the Klein four pulls `a` into
  -- the self-centralizer, so `a = 1`
  let a : M := eL ℓbarL
  let V' : Subgroup M := V0.map eL.toMonoidHom
  have hV' : IsKleinFour V' :=
    isKleinFour_map_of_injective V0 hV0 eL.toMonoidHom eL.injective
  have hselfV : Subgroup.centralizer (V' : Set M) = V' := hself V' hV'
  have hV0N_le_Ebar' : ∀ w : Lq, w ∈ V0 → (w : N ⧸ O) ∈ Ebar := by
    intro w hw
    exact hV0N_le_Ebar (Subgroup.mem_map.mpr ⟨w, hw, rfl⟩)
  have hacentV' : a ∈ Subgroup.centralizer (V' : Set M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨w, hwV0, rfl⟩
    have hwE : (w : N ⧸ O) ∈ Ebar := hV0N_le_Ebar' w hwV0
    have hℓw : ℓbar * (w : N ⧸ O) * ℓbar⁻¹ = (w : N ⧸ O) := by
      have hc := (Subgroup.mem_centralizer_iff.mp hℓbarC) (w : N ⧸ O) hwE
      calc
        ℓbar * (w : N ⧸ O) * ℓbar⁻¹ = ((w : N ⧸ O) * ℓbar) * ℓbar⁻¹ := by rw [hc]
        _ = (w : N ⧸ O) := by group
    have hℓLw : ℓbarL * w * (ℓbarL)⁻¹ = w := by
      apply Subtype.ext
      change ℓbar * (w : N ⧸ O) * ℓbar⁻¹ = (w : N ⧸ O)
      exact hℓw
    have h : eL ℓbarL * (eL w) * (eL ℓbarL)⁻¹ = eL w := by
      rw [← map_mul, ← map_inv, ← map_mul]
      exact congrArg eL hℓLw
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  have haV' : a ∈ V' := by
    rw [← hselfV]
    exact hacentV'
  have ha_EM : a ∈ EM := by
    rcases Subgroup.mem_map.mp haV' with ⟨w₀, hw₀V0, hw₀eq⟩
    refine Subgroup.mem_map.mpr ⟨w₀, ?_, ?_⟩
    · apply Subgroup.mem_subgroupOf.mpr
      exact hV0N_le_Ebar' w₀ hw₀V0
    · exact hw₀eq
  have ha_cent_EM : ∀ y : EM, a * (y : M) * a⁻¹ = (y : M) := by
    intro y
    rcases Subgroup.mem_map.mp y.2 with ⟨x, hxELq, hxy⟩
    have hxE : (x : N ⧸ O) ∈ Ebar := Subgroup.mem_subgroupOf.mp hxELq
    have hℓx : ℓbar * (x : N ⧸ O) * ℓbar⁻¹ = (x : N ⧸ O) := by
      have hc := (Subgroup.mem_centralizer_iff.mp hℓbarC) (x : N ⧸ O) hxE
      calc
        ℓbar * (x : N ⧸ O) * ℓbar⁻¹ = ((x : N ⧸ O) * ℓbar) * ℓbar⁻¹ := by rw [hc]
        _ = (x : N ⧸ O) := by group
    have hℓLx : ℓbarL * x * (ℓbarL)⁻¹ = x := by
      apply Subtype.ext
      change ℓbar * (x : N ⧸ O) * ℓbar⁻¹ = (x : N ⧸ O)
      exact hℓx
    change a * (y : M) * a⁻¹ = (y : M)
    rw [← hxy]
    change eL ℓbarL * (eL x) * (eL ℓbarL)⁻¹ = eL x
    rw [← map_mul, ← map_inv, ← map_mul]
    exact congrArg eL hℓLx
  rcases Subgroup.mem_map.mp haV' with ⟨w₀, hw₀V0, hw₀eq⟩
  change eL w₀ = a at hw₀eq
  have hw₀E : (w₀ : N ⧸ O) ∈ Ebar := hV0N_le_Ebar' w₀ hw₀V0
  have hw₀_cent : (⟨(w₀ : N ⧸ O), hw₀E⟩ : Ebar) ∈
      Subgroup.center Ebar := by
    rw [Subgroup.mem_center_iff]
    intro y
    let yL : Lq := ⟨(y : N ⧸ O), hEbarLq y.2⟩
    have hyELq : yL ∈ ELq := Subgroup.mem_subgroupOf.mpr y.2
    have hyEM : eL yL ∈ EM := Subgroup.mem_map.mpr ⟨yL, hyELq, rfl⟩
    have hcommM : eL yL * a = a * eL yL :=
      (mul_inv_eq_iff_eq_mul.mp (ha_cent_EM ⟨eL yL, hyEM⟩)).symm
    have hcommL : yL * w₀ = w₀ * yL := by
      apply eL.injective
      calc
        eL (yL * w₀) = eL yL * eL w₀ := map_mul eL yL w₀
        _ = eL yL * a := by rw [hw₀eq]
        _ = a * eL yL := hcommM
        _ = eL w₀ * eL yL := by rw [hw₀eq]
        _ = eL (w₀ * yL) := (map_mul eL w₀ yL).symm
    apply Subtype.ext
    change (y : N ⧸ O) * (w₀ : N ⧸ O) = (w₀ : N ⧸ O) * (y : N ⧸ O)
    exact congrArg Subtype.val hcommL
  have hw₀_V0 : (w₀ : N ⧸ O) ∈ V0N :=
    Subgroup.mem_map.mpr ⟨w₀, hw₀V0, rfl⟩
  have hw₀N : (w₀ : N ⧸ O) = 1 :=
    hV0N_cent_inter ⟨(w₀ : N ⧸ O), hw₀E⟩ hw₀_V0 hw₀_cent
  have hw₀L : w₀ = 1 := Subtype.ext hw₀N
  have ha_one : a = 1 := by
    calc
      a = eL w₀ := hw₀eq.symm
      _ = eL 1 := by rw [hw₀L]
      _ = 1 := by simp
  have hℓbarL_one : ℓbarL = 1 := eL.injective (by simpa [a] using ha_one)
  have hℓbar_one : ℓbar = 1 := congrArg Subtype.val hℓbarL_one
  -- the induced action of `f` on the image of the layer is trivial
  have hquot : ∀ x : L,
      QuotientGroup.mk' (pPrimeCore 2 N)
          (⟨f * (x : G) * f⁻¹, hLnorm.1 (hLnorm.2 f hfN (x : G) x.2)⟩ : N) =
        QuotientGroup.mk' (pPrimeCore 2 N) (⟨(x : G), hLleN x.2⟩ : N) := by
    intro x
    let a0 : N := ⟨f * (x : G) * f⁻¹, hLnorm.1 (hLnorm.2 f hfN (x : G) x.2)⟩
    let b0 : N := ⟨(x : G), hLleN x.2⟩
    let c0 : N := ⟨ℓ * (x : G) * ℓ⁻¹,
      hLleN (L.mul_mem (L.mul_mem hℓL x.2) (L.inv_mem hℓL))⟩
    change QuotientGroup.mk' O a0 = QuotientGroup.mk' O b0
    calc
      QuotientGroup.mk' O a0 = QuotientGroup.mk' O c0 := by
        apply congrArg (QuotientGroup.mk' O)
        apply Subtype.ext
        exact hℓconj (x : G) x.2
      _ = QuotientGroup.mk' O b0 := by
        have hc : c0 = ℓN * b0 * ℓN⁻¹ := by
          apply Subtype.ext
          change ℓ * (x : G) * ℓ⁻¹ = ℓ * (x : G) * ℓ⁻¹
          rfl
        rw [hc, map_mul, map_mul, map_inv]
        change q ℓN * q b0 * (q ℓN)⁻¹ = q b0
        have hqℓ : q ℓN = 1 := hℓbar_one
        rw [hqℓ]
        simp
  exact centralizes_layer_of_quotient_action_trivial N L f hLleN hLnorm hfN
    hLperf hLcentO hquot

/-- The linear model case of the Fact 1.10(ii) normalizer centralization:
`N = N_G(X)` is a D-group whose quotient by `O₂'(N)` has a normal odd-index
subgroup modeled by `PSL₂(K')` or `PGL₂(K')`.  Given the semilinear
inner-action transport `hInner`, the layer of `N` centralizes `N_F(X)`. -/
public theorem secondCase_psl2_normalizer_fitting_action_of_linear_quotient
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (e : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃* PSL2 K))
    (F X : Subgroup G)
    (s : d.E)
    (hF_eq : F = centralizerIn (c.FU ⊓ w.M) (s : G))
    (hrefl : c.IsReflection (s : G))
    (hFleFU : F ≤ c.FU) (hFleM : F ≤ w.M)
    (hFcentE : F ≤ Subgroup.centralizer (d.E : Set G))
    (hXne : X ≠ ⊥) (hXleF : X ≤ F)
    (K' : Type u) [Field K'] [Finite K']
    (hK' : IsOddPrimePower (Nat.card K'))
    (Lq : Subgroup (Subgroup.normalizer (X : Set G) ⧸
      pPrimeCore 2 (Subgroup.normalizer (X : Set G))))
    (hLqnormal : Lq.Normal) (hLqindex : Odd Lq.index)
    (hLqmodel : Nonempty (Lq ≃* PSL2 K') ∨ Nonempty (Lq ≃* PGL2 K'))
    (hInner : secondCase_psl2_normalizer_innerAction c X) :
    secondCase_psl2_fact_1_10_ii_centralization c w d F X
      hFleFU hFleM hFcentE hXne hXleF := by
  classical
  rcases hLqmodel with eL | eL
  · rcases eL with ⟨eL⟩
    exact secondCase_psl2_linear_quotient_centralization_of_model
      hmin c w d K hK e F X s hF_eq hrefl hFleFU hFleM hFcentE hXne hXleF
      Lq hLqnormal hLqindex (PSL2 K') eL
      (fun V hV => psl2_kleinFour_centralizer_eq_self K' hK' V hV) hInner
  · rcases eL with ⟨eL⟩
    let : Finite (PGL2 K') :=
      Finite.of_surjective Matrix.ProjGenLinGroup.mk
        Matrix.ProjGenLinGroup.mk_surjective
    exact secondCase_psl2_linear_quotient_centralization_of_model
      hmin c w d K hK e F X s hF_eq hrefl hFleFU hFleM hFcentE hXne hXleF
      Lq hLqnormal hLqindex (PGL2 K') eL
      (fun V hV => pgl2_kleinFour_centralizer_eq_self K' hK' V hV) hInner

end CFSG.GorensteinWalter

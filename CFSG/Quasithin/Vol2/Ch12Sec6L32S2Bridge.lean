module

public import CFSG.Quasithin.Vol2.Ch12Sec6L32S2Defs

public section

namespace CFSG.Quasithin.H13.L1232S2

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique S126

attribute [local instance] commGroupOfFact

theorem conjSub_le_of_mem_normalizer_L32S2 {G : Type} [Group G] {X I : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (X : Set G)) (hIX : I ≤ X) :
    CFSG.Quasithin.conjSub x I ≤ X := by
  intro y hy
  rw [CFSG.Quasithin.mem_conjSub] at hy
  have h1 := (Subgroup.mem_normalizer_iff.mp hx _).mp (hIX hy)
  simpa [mul_assoc] using h1

theorem binaryNaturalSL_transport_L32S2 {G : Type} [Group G] (V₁ K J IH IH' : Subgroup G)
    (e : IH = IH') (E : IsElemAbelian 2 (tildeOf V₁ IH))
    (E' : IsElemAbelian 2 (tildeOf V₁ IH')) :
    @BinaryNaturalSL _ (commGroupOfElemAbelian E) (autOn (tildeOf V₁ K) (tildeOf V₁ IH))
        (subM V₁ IH J) ⊥ 3 2 →
      @BinaryNaturalSL _ (commGroupOfElemAbelian E') (autOn (tildeOf V₁ K) (tildeOf V₁ IH'))
        (subM V₁ IH' J) ⊥ 3 2 := by
  subst e
  exact id

theorem subM_map_actH_L32S2 {G : Type} [Group G] {V₁ IH H I : Subgroup G}
    [Fact (IsElemAbelian 2 (tildeOf V₁ IH))]
    (hV₁ : H ≤ Subgroup.normalizer (V₁ : Set G)) (hIHN : IH ≤ Subgroup.normalizer (V₁ : Set G))
    (hIHH : H ≤ Subgroup.normalizer (IH : Set G)) (hV₁I : V₁ ≤ I) (hIIH : I ≤ IH) (x : ↥H) :
    (subM V₁ IH I).map (actH hV₁ hIHH x).toMonoidHom =
      subM V₁ IH (CFSG.Quasithin.conjSub (x : G) I) := by
  have hxN : (x : G) ∈ Subgroup.normalizer (IH : Set G) := hIHH x.2
  have hxN' : (x : G)⁻¹ ∈ Subgroup.normalizer (IH : Set G) := hIHH (H.inv_mem x.2)
  have hconjIH : ∀ a ∈ IH, (x : G) * a * (x : G)⁻¹ ∈ IH := fun a ha =>
    (Subgroup.mem_normalizer_iff.mp hxN a).mp ha
  have hconjIH' : ∀ a ∈ IH, (x : G)⁻¹ * a * (x : G) ∈ IH := fun a ha => by
    have h1 := (Subgroup.mem_normalizer_iff.mp hxN' a).mp ha
    simpa using h1
  have hV₁conj : V₁ ≤ CFSG.Quasithin.conjSub (x : G) I := by
    intro y hy
    rw [CFSG.Quasithin.mem_conjSub]
    apply hV₁I
    have h1 := (Subgroup.mem_normalizer_iff.mp (hV₁ (H.inv_mem x.2)) y).mp hy
    simpa using h1
  have hmodeq : ∀ {a b : G} (ha : a ∈ IH) (hb : b ∈ IH), a = b →
      modMk hIHN a ha = modMk hIHN b hb := by
    rintro a b ha hb rfl
    rfl
  ext w
  constructor
  · intro hw
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hw
    obtain ⟨a, haIH, hau⟩ := exists_mk_of_mem_tilde u
    have hu' : u = modMk hIHN (a : G) haIH := Subtype.ext hau.symm
    rw [hu', modMk_mem_subM_iff hIHN hV₁I haIH] at hu
    rw [hu', MulEquiv.coe_toMonoidHom, actH_modMk hV₁ hIHN hIHH x haIH]
    refine (modMk_mem_subM_iff hIHN hV₁conj (hconjIH _ haIH)).mpr ?_
    rw [CFSG.Quasithin.mem_conjSub]
    simpa [mul_assoc] using hu
  · intro hw
    obtain ⟨b, hbIH, hbw⟩ := exists_mk_of_mem_tilde w
    have hw' : w = modMk hIHN (b : G) hbIH := Subtype.ext hbw.symm
    rw [hw', modMk_mem_subM_iff hIHN hV₁conj hbIH, CFSG.Quasithin.mem_conjSub] at hw
    refine Subgroup.mem_map.mpr ⟨modMk hIHN _ (hconjIH' _ hbIH),
      (modMk_mem_subM_iff hIHN hV₁I (hconjIH' _ hbIH)).mpr hw, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, actH_modMk hV₁ hIHN hIHH x (hconjIH' _ hbIH), hw']
    apply hmodeq
    group

theorem tildeOf_inf_eq_bot_of_subM_L32S2 {G : Type} [Group G] {V₁ IH I J : Subgroup G}
    (hI : I ≤ IH) (hinf : subM V₁ IH I ⊓ subM V₁ IH J = ⊥) :
    tildeOf V₁ I ⊓ tildeOf V₁ J = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨hyI, hyJ⟩ := Subgroup.mem_inf.mp hy
  have hyIH : y ∈ tildeOf V₁ IH := (secImg_mono hI : tildeOf V₁ I ≤ tildeOf V₁ IH) hyI
  have hw : (⟨y, hyIH⟩ : ↥(tildeOf V₁ IH)) ∈ subM V₁ IH I ⊓ subM V₁ IH J :=
    Subgroup.mem_inf.mpr ⟨hyI, hyJ⟩
  rw [hinf, Subgroup.mem_bot] at hw
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val hw

theorem tildeOf_sup_eq_of_subM_L32S2 {G : Type} [Group G] {V₁ IH I J : Subgroup G}
    (hI : I ≤ IH) (hJ : J ≤ IH) (hsup : subM V₁ IH I ⊔ subM V₁ IH J = ⊤) :
    tildeOf V₁ I ⊔ tildeOf V₁ J = tildeOf V₁ IH := by
  have h1 : tildeOf V₁ I ≤ tildeOf V₁ IH := secImg_mono hI
  have h2 : tildeOf V₁ J ≤ tildeOf V₁ IH := secImg_mono hJ
  refine le_antisymm (sup_le h1 h2) ?_
  have htop : (tildeOf V₁ I ⊔ tildeOf V₁ J).subgroupOf (tildeOf V₁ IH) = ⊤ := by
    rw [Subgroup.subgroupOf_sup h1 h2]
    exact hsup
  exact Subgroup.subgroupOf_eq_top.mp htop

theorem leafBridge_holds : LeafBridge := by
  intro G _ _ T L V _ F H K h I hV₁I hIU hIH hyp
  haveI := factElem h hIU
  obtain ⟨t, ht, hnat, hinf, hsup⟩ := hyp
  rw [autIH_eq_map h h.T_le_H] at ht
  obtain ⟨x, hxT, rfl⟩ := Subgroup.mem_map.mp ht
  have hIIH : I ≤ conjClosure I H := CFSG.Quasithin.le_conjClosure I H
  have hkey := subM_map_actH_L32S2 h.H_le_normalizer_V₁ (h.conjClosure_le_normalizer_V₁ hIU)
    (CFSG.Quasithin.le_normalizer_conjClosure I H) hV₁I hIIH x
  rw [hkey] at hinf hsup
  have hJ : CFSG.Quasithin.conjSub (x : G) I ≤ conjClosure I H :=
    conjSub_le_of_mem_normalizer_L32S2 (CFSG.Quasithin.le_normalizer_conjClosure I H x.2) hIIH
  refine ⟨(x : G), Subgroup.mem_subgroupOf.mp hxT,
    tildeOf_inf_eq_bot_of_subM_L32S2 hIIH hinf, ?_, ?_⟩
  · have hsupU := tildeOf_sup_eq_of_subM_L32S2 hIIH hJ hsup
    rw [hIH] at hsupU
    exact hsupU
  · exact binaryNaturalSL_transport_L32S2 F.V1 K I (conjClosure I H) (conjClosure F.V5 H) hIH
      (factElem h hIU).out h.toHypF98.toHypF91.isElemAbelian_tilde hnat

end CFSG.Quasithin.H13.L1232S2

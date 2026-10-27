module

public import CFSG.Quasithin.Vol2.Ch3Sec2Prop3210Six
public import CFSG.Quasithin.Recognition.M12AmalAutIso
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def Sp62InvolutionsIntoCJ : Prop :=
  ∀ (X : Type) [Group X] [Finite X], LieModel X .PSp 3 2 1 → ∀ P : Sylow 2 X, ∀ x : X,
    orderOf x = 2 → ∃ g : X, g * x * g⁻¹ ∈ centralizer (thompsonJ (P : Subgroup X) : Set X)

@[expose] def Sp62TransvectionProduct : Prop :=
  ∀ (X : Type) [Group X] [Finite X], LieModel X .PSp 3 2 1 → ∀ d e : X, orderOf d = 2 →
    5 ∣ Nat.card ↥(centralizer ({d} : Set X)) → IsConj d e → d * e = e * d → e ≠ d →
    ∃ P : Sylow 2 X, (P : Subgroup X) ≤ centralizer ({d * e} : Set X)

variable {G : Type} [Group G] [Finite G]

theorem le_of_conj_mem_of_pGroup (T : Sylow 2 G) {E : Subgroup G} (hTE : (T : Subgroup G) ≤ E)
    {d : G} (hCd : centralizer ({d} : Set G) ≤ E)
    (hfus : ∀ g : G, g * d * g⁻¹ ∈ E → ∃ e ∈ E, e * d * e⁻¹ = g * d * g⁻¹)
    {X P : Subgroup G} (hP2 : IsPGroup 2 P) (hXP : X ≤ normalizer (P : Set G)) (hdP : d ∈ P) :
    X ≤ E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : ∀ g : G, g * d * g⁻¹ ∈ E → g ∈ E := by
    intro g hg
    obtain ⟨e, he, hed⟩ := hfus g hg
    have hc : e⁻¹ * g ∈ centralizer ({d} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      have h1 : (e⁻¹ * g) * d * (e⁻¹ * g)⁻¹ = d := by
        calc (e⁻¹ * g) * d * (e⁻¹ * g)⁻¹ = e⁻¹ * (g * d * g⁻¹) * e := by group
          _ = e⁻¹ * (e * d * e⁻¹) * e := by rw [hed]
          _ = d := by group
      calc e⁻¹ * g * d = (e⁻¹ * g) * d * (e⁻¹ * g)⁻¹ * (e⁻¹ * g) := by group
        _ = d * (e⁻¹ * g) := by rw [h1]
    have : g = e * (e⁻¹ * g) := by group
    rw [this]
    exact mul_mem he (hCd hc)
  obtain ⟨Q, hPQ⟩ := hP2.exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G T Q
  have hdg : g⁻¹ * d * g⁻¹⁻¹ ∈ E := by
    have hd' := hPQ hdP
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hd'
    rw [inv_inv]
    exact hTE hd'
  have hgE : g ∈ E := by
    have := key g⁻¹ hdg
    simpa using this
  have hPE : P ≤ E := by
    intro p hp
    have hp' := hPQ hp
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hp'
    have h1 : g⁻¹ * p * g ∈ E := hTE hp'
    have : p = g * (g⁻¹ * p * g) * g⁻¹ := by group
    rw [this]
    exact mul_mem (mul_mem hgE h1) (inv_mem hgE)
  intro x hx
  exact key x (hPE ((mem_normalizer_iff.mp (hXP hx) d).mp hdP))

theorem fusion_of_sp62 (hX1 : Sp62InvolutionsIntoCJ) (hX2 : Sp62TransvectionProduct)
    (hEven : quasithinEvenCharacteristic G) (T : Sylow 2 G) {E : Subgroup G}
    (hE : LieModel ↥E .PSp 3 2 1) (hTE : (T : Subgroup G) ≤ E)
    (hNJ : normalizer (thompsonJ (T : Subgroup G) : Set G) ≤ E) {d : G} (hd2 : orderOf d = 2)
    (hdT : d ∈ (T : Subgroup G)) (hdZ : d ∈ centralizer ((T : Subgroup G) : Set G))
    (hCd : centralizer ({d} : Set G) ≤ E) (h5 : 5 ∣ Nat.card ↥(centralizer ({d} : Set G))) :
    (∀ a ∈ E, ∀ b ∈ E, orderOf a = 2 → IsConj a b → ∃ e ∈ E, e * a * e⁻¹ = b) ∧
    ∀ e : G, IsConj d e → d * e = e * d → e ≠ d → centralizer ({d * e} : Set G) ≤ E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set TE : Sylow 2 ↥E := T.subtype hTE with hTEdef
  have hTEcoe : ((TE : Subgroup ↥E)).map E.subtype = (T : Subgroup G) := by
    rw [hTEdef, Sylow.coe_subtype, map_subgroupOf_eq_of_le hTE]
  have hJE : (thompsonJ (TE : Subgroup ↥E)).map E.subtype = thompsonJ (T : Subgroup G) := by
    rw [hTEdef, Sylow.coe_subtype,
      ← AmalTransport.thompsonJ_map_of_injective E.subtype E.subtype_injective,
      map_subgroupOf_eq_of_le hTE]
  have hinto : ∀ a ∈ E, orderOf a = 2 → ∃ g ∈ E,
      g * a * g⁻¹ ∈ centralizer (thompsonJ (T : Subgroup G) : Set G) := by
    intro a ha ha2
    have ha2' : orderOf (⟨a, ha⟩ : ↥E) = 2 := by
      rw [← ha2]
      exact Subgroup.orderOf_mk a ha
    obtain ⟨g, hg⟩ := hX1 ↥E hE TE ⟨a, ha⟩ ha2'
    refine ⟨g, g.2, ?_⟩
    rw [mem_centralizer_iff]
    intro w hw
    rw [← hJE] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    have := (mem_centralizer_iff.mp hg) w' hw'
    exact congrArg Subtype.val this
  have hJT : thompsonJ (T : Subgroup G) ≤ T := iSup₂_le fun _ hA => hA.1
  have hwc : IsWeaklyClosedIn (thompsonJ (T : Subgroup G)) T :=
    Prop3210.thompsonJ_isWeaklyClosedIn
  have hA : ∀ a ∈ E, ∀ b ∈ E, orderOf a = 2 → IsConj a b → ∃ e ∈ E, e * a * e⁻¹ = b := by
    intro a ha b hb ha2 hab
    have hb2 : orderOf b = 2 := by
      obtain ⟨c, hc⟩ := isConj_iff.mp hab
      have h := MulEquiv.orderOf_eq (MulAut.conj c) a
      rw [MulAut.conj_apply, hc] at h
      rw [h, ha2]
    obtain ⟨g₁, hg₁E, hg₁⟩ := hinto a ha ha2
    obtain ⟨g₂, hg₂E, hg₂⟩ := hinto b hb hb2
    obtain ⟨c, hc⟩ := isConj_iff.mp hab
    obtain ⟨n, hnN, hn⟩ := burnside_fusion_lemma_centralizer T hJT hwc hg₁ hg₂
      (g := g₁ * c⁻¹ * g₂⁻¹) (by rw [← hc]; group)
    refine ⟨g₂⁻¹ * n⁻¹ * g₁, mul_mem (mul_mem (inv_mem hg₂E) (inv_mem (hNJ hnN))) hg₁E, ?_⟩
    calc g₂⁻¹ * n⁻¹ * g₁ * a * (g₂⁻¹ * n⁻¹ * g₁)⁻¹ =
        g₂⁻¹ * (n⁻¹ * (g₁ * a * g₁⁻¹) * n) * g₂ := by group
      _ = g₂⁻¹ * (g₂ * b * g₂⁻¹) * g₂ := by rw [hn]
      _ = b := by group
  refine ⟨hA, ?_⟩
  intro e hde hcomm hne
  have hdE : d ∈ E := hTE hdT
  have heE : e ∈ E := hCd (mem_centralizer_singleton_iff.mpr hcomm.symm)
  obtain ⟨c, hcE, hcd⟩ := hA d hdE e heE hd2 hde
  have hdE2 : orderOf (⟨d, hdE⟩ : ↥E) = 2 := by rw [← hd2]; exact Subgroup.orderOf_mk d hdE
  have hcard : Nat.card ↥(centralizer ({(⟨d, hdE⟩ : ↥E)} : Set ↥E)) =
      Nat.card ↥(centralizer ({d} : Set G)) := by
    have hmap : (centralizer ({(⟨d, hdE⟩ : ↥E)} : Set ↥E)).map E.subtype =
        centralizer ({d} : Set G) := by
      apply le_antisymm
      · rintro _ ⟨x, hx, rfl⟩
        rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hx
        rw [mem_centralizer_singleton_iff]
        exact congrArg Subtype.val hx
      · intro x hx
        refine ⟨⟨x, hCd hx⟩, ?_, rfl⟩
        rw [mem_centralizer_singleton_iff] at hx
        rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
        exact Subtype.ext hx
    rw [← hmap, card_map_of_injective E.subtype_injective]
  have hconjE : IsConj (⟨d, hdE⟩ : ↥E) ⟨e, heE⟩ :=
    isConj_iff.mpr ⟨⟨c, hcE⟩, Subtype.ext hcd⟩
  have hcommE : (⟨d, hdE⟩ : ↥E) * ⟨e, heE⟩ = ⟨e, heE⟩ * ⟨d, hdE⟩ := Subtype.ext hcomm
  have hneE : (⟨e, heE⟩ : ↥E) ≠ ⟨d, hdE⟩ := fun h => hne (congrArg Subtype.val h)
  obtain ⟨P, hP⟩ := hX2 ↥E hE ⟨d, hdE⟩ ⟨e, heE⟩ hdE2 (hcard ▸ h5) hconjE hcommE hneE
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq ↥E TE P
  set j : G := (x : G)⁻¹ * (d * e) * x with hj
  have hTj : (T : Subgroup G) ≤ centralizer ({j} : Set G) := by
    intro t ht
    have htE : t ∈ E := hTE ht
    have h1 : (⟨t, htE⟩ : ↥E) ∈ (TE : Subgroup ↥E) := by
      rw [hTEdef, Sylow.coe_subtype]
      exact ht
    have h2 : MulAut.conj x • (⟨t, htE⟩ : ↥E) ∈ (P : Subgroup ↥E) := by
      rw [← hx, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ h1
    have h3 := mem_centralizer_singleton_iff.mp (hP h2)
    have h4 : ((x : G) * t * (x : G)⁻¹) * (d * e) = (d * e) * ((x : G) * t * (x : G)⁻¹) := by
      have := congrArg Subtype.val h3
      simpa [MulAut.smul_def, MulAut.conj_apply] using this
    rw [mem_centralizer_singleton_iff, hj]
    set y : G := (x : G) with hy
    calc t * (y⁻¹ * (d * e) * y) = y⁻¹ * ((y * t * y⁻¹) * (d * e)) * y := by group
      _ = y⁻¹ * ((d * e) * (y * t * y⁻¹)) * y := by rw [h4]
      _ = y⁻¹ * (d * e) * y * t := by group
  have hj1 : j ≠ 1 := by
    intro h
    apply hne
    have h1 : d * e = 1 := by
      have : d * e = (x : G) * j * (x : G)⁻¹ := by rw [hj]; group
      rw [this, h, mul_one, mul_inv_cancel]
    have hd1 : d * d = 1 := by rw [← pow_two, ← hd2, pow_orderOf_eq_one]
    calc e = d * (d * e) := by rw [← mul_assoc, hd1, one_mul]
      _ = d := by rw [h1, mul_one]
  have hjmem : j ∈ centralizer ({j} : Set G) := mem_centralizer_singleton_iff.mpr rfl
  have hO2 : pCoreOf 2 (centralizer ({j} : Set G)) ≠ ⊥ := by
    have he2 : orderOf e = 2 := by
      obtain ⟨y, hy⟩ := isConj_iff.mp hde
      have h := MulEquiv.orderOf_eq (MulAut.conj y) d
      rw [MulAut.conj_apply, hy] at h
      rw [h, hd2]
    have hj2 : j ^ 2 = 1 := by
      have hdd : d ^ 2 = 1 := by rw [← hd2]; exact pow_orderOf_eq_one d
      have hee : e ^ 2 = 1 := by rw [← he2]; exact pow_orderOf_eq_one e
      have hde2 : (d * e) ^ 2 = 1 := by
        rw [pow_two, show d * e * (d * e) = d * (e * d) * e by group, ← hcomm,
          show d * (d * e) * e = d ^ 2 * e ^ 2 by rw [pow_two, pow_two]; group, hdd, hee,
          one_mul]
      have hjp : j = (x : G)⁻¹ * (d * e) * ((x : G)⁻¹)⁻¹ := by rw [hj, inv_inv]
      rw [hjp, conj_pow, hde2]
      group
    intro hbot
    have hzle : zpowers j ≤ pCoreOf 2 (centralizer ({j} : Set G)) := by
      refine CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 _ _
        (zpowers_le.mpr hjmem) ?_ ?_
      · refine (normal_subgroupOf_iff_le_normalizer (zpowers_le.mpr hjmem)).2 fun y hy => ?_
        refine Subgroup.centralizer_le_normalizer _ ?_
        rw [mem_centralizer_iff]
        intro w hw
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
        exact ((Commute.zpow_left (mem_centralizer_singleton_iff.mp hy).symm k).symm).eq.symm
      · exact IsPGroup.of_card (n := 1) (by
          rw [Nat.card_zpowers, pow_one]
          exact orderOf_eq_prime hj2 hj1)
    rw [hbot, le_bot_iff, zpowers_eq_bot] at hzle
    exact hj1 hzle
  have hchar : CharTwo (centralizer ({j} : Set G)) :=
    CFSG.Quasithin.charTwo_of_inH hEven T ⟨hTj, hO2⟩
  have hO2T : pCoreOf 2 (centralizer ({j} : Set G)) ≤ (T : Subgroup G) :=
    pCoreOf_two_le_sylow _ T hTj
  have hdO2 : d ∈ pCoreOf 2 (centralizer ({j} : Set G)) := by
    refine hchar (mem_inf.mpr ⟨hTj hdT, ?_⟩)
    rw [mem_centralizer_iff]
    intro y hy
    exact mem_centralizer_iff.mp hdZ y (hO2T hy)
  have hfus : ∀ g : G, g * d * g⁻¹ ∈ E → ∃ f ∈ E, f * d * f⁻¹ = g * d * g⁻¹ := fun g hg =>
    hA d hdE _ hg hd2 (isConj_iff.mpr ⟨g, rfl⟩)
  have hCj : centralizer ({j} : Set G) ≤ E :=
    le_of_conj_mem_of_pGroup T hTE hCd hfus (LieType.BorelTits.pCoreOf_isPGroup 2 _)
      (LieType.BorelTits.le_normalizer_pCoreOf 2 _) hdO2
  intro y hy
  have hy' : (x : G)⁻¹ * y * x ∈ centralizer ({j} : Set G) := by
    rw [mem_centralizer_singleton_iff] at hy ⊢
    rw [hj]
    calc (x : G)⁻¹ * y * x * ((x : G)⁻¹ * (d * e) * x) = (x : G)⁻¹ * (y * (d * e)) * x := by
          group
      _ = (x : G)⁻¹ * ((d * e) * y) * x := by rw [hy]
      _ = (x : G)⁻¹ * (d * e) * x * ((x : G)⁻¹ * y * x) := by group
  have : y = x * ((x : G)⁻¹ * y * x) * (x : G)⁻¹ := by group
  rw [this]
  exact mul_mem (mul_mem x.2 (hCj hy')) (inv_mem x.2)

end CFSG.Quasithin.H13.U3

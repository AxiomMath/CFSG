module

public import CFSG.Timmesfeld.Bridge.OddRootSzMainBlock
public import CFSG.Timmesfeld.Bridge.OddLocalMain
import CFSG.Timmesfeld.Bridge.OddRootBasic
import CFSG.Timmesfeld.Bridge.RootClosureThree
public import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.Timmesfeld.Bridge.OddRoot

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
  CFSG.Timmesfeld.Bridge.OddTransp CFSG.Timmesfeld.Bridge.OddLocal
  CFSG.Timmesfeld.Bridge.Asc72 CFSG.BenderSuzuki

variable {G : Type} [Group G] [Finite G] {D : Set G} {d e : G} {E : Set G} {n : ℕ}

theorem Hyp.le_center_of_disjoint (h : Hyp G D) {K : Subgroup G} (hK : K.Normal)
    (hKD : ∀ x ∈ D, x ∉ K) : K ≤ Subgroup.center G := by
  have hO2 : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N = ⊥ := by
    intro N hN hN2
    have hle : N ≤ CFSG.pCore 2 G := CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hN hN2
    rw [h.o2] at hle
    exact le_bot_iff.mp hle
  have hzc : zStar G = Subgroup.center G := OddLocal.zStar_eq_center hO2
  have hsimple : IsSimpleGroup (G ⧸ Subgroup.center G) := by
    have h1 := OddTransp.isSimpleGroup_quotient_zStar h.setup h.sq
    exact (MulEquiv.isSimpleGroup_congr (QuotientGroup.quotientMulEquivOfEq hzc)).mp h1
  let π : G →* G ⧸ Subgroup.center G := QuotientGroup.mk' (Subgroup.center G)
  let L : Subgroup (G ⧸ Subgroup.center G) := K.map π
  have hL : L.Normal := hK.map π (QuotientGroup.mk'_surjective _)
  rcases Subgroup.Normal.eq_bot_or_eq_top L with hbot | htop
  · intro k hk
    have hkL : π k ∈ L := Subgroup.mem_map_of_mem π hk
    rw [hbot] at hkL
    have hk1 : π k = 1 := by simpa using hkL
    exact (QuotientGroup.eq_one_iff (N := Subgroup.center G) k).mp (by simpa [π] using hk1)
  · exfalso
    have hsup : K ⊔ Subgroup.center G = ⊤ := by
      rw [eq_top_iff]
      intro g _
      have hgL : π g ∈ L := by rw [htop]; exact Subgroup.mem_top _
      obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.mp hgL
      have hmem : k⁻¹ * g ∈ Subgroup.center G := by
        rw [← QuotientGroup.eq_one_iff (N := Subgroup.center G)]
        change π (k⁻¹ * g) = 1
        rw [map_mul, map_inv, hkg]
        group
      have hg_eq : g = k * (k⁻¹ * g) := by group
      rw [hg_eq]
      exact Subgroup.mul_mem_sup hk hmem
    haveI : K.Normal := hK
    have hcomm : commutator G ≤ K :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top
        (H := Subgroup.center G) hsup inferInstance
    haveI : IsMulCommutative (G ⧸ K) :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcomm
    let πK : G →* G ⧸ K := QuotientGroup.mk' K
    obtain ⟨u, hu, v, hv, -, -, huv⟩ := h.sq
    have himg : ∀ g x : G, πK (g * x * g⁻¹) = πK x := by
      intro g x
      rw [map_mul, map_mul, map_inv, mul_comm' (πK g) (πK x)]
      group
    have heq : ∀ x ∈ D, πK x = πK u := by
      intro x hx
      obtain ⟨g, hg⟩ := isConj_iff.mp (h.setup.isConj hx hu)
      rw [← hg, himg]
    have huv_eq : πK u = πK (u * v) := by
      obtain ⟨g, hg⟩ := isConj_iff.mp (h.setup.isConj hu huv)
      rw [← hg, himg]
    rw [map_mul] at huv_eq
    have hv1 : πK v = 1 := by
      have h1 : πK u * πK v = πK u * 1 := by rw [mul_one]; exact huv_eq.symm
      exact mul_left_cancel h1
    have hu1 : πK u = 1 := (heq v hv).symm.trans hv1
    exact hKD u hu ((QuotientGroup.eq_one_iff (N := K) u).mp hu1)


private theorem mem_normalizer_rootSet_conj_image_iff (D : Set G) {x : G} {g h : G} :
    h ∈ Subgroup.normalizer ((fun y => g * y * g⁻¹) '' rootSet D x) ↔
      g⁻¹ * h * g ∈ Subgroup.normalizer (rootSet D x) := by
  rw [Subgroup.mem_set_normalizer_iff'', Subgroup.mem_set_normalizer_iff'']
  have hmem : ∀ y : G, (y ∈ (fun z => g * z * g⁻¹) '' rootSet D x ↔ g⁻¹ * y * g ∈ rootSet D x) := by
    intro y
    constructor
    · rintro ⟨z, hz, hzy⟩
      have hzy' : g⁻¹ * y * g = z := by
        have := congrArg (fun w => g⁻¹ * w * g) hzy
        simpa [mul_assoc] using this.symm
      rwa [hzy']
    · intro hy
      exact ⟨g⁻¹ * y * g, hy, by group⟩
  constructor
  · intro H z
    have hz := H (g * z * g⁻¹)
    rw [hmem, hmem] at hz
    rw [show g⁻¹ * (g * z * g⁻¹) * g = z from by group,
      show g⁻¹ * (h⁻¹ * (g * z * g⁻¹) * h) * g =
        (g⁻¹ * h * g)⁻¹ * z * (g⁻¹ * h * g) from by group] at hz
    exact hz
  · intro H z
    have hz := H (g⁻¹ * z * g)
    constructor
    · intro hzmem
      have h1 : g⁻¹ * z * g ∈ rootSet D x := (hmem z).mp hzmem
      have h2 : (g⁻¹ * h * g)⁻¹ * (g⁻¹ * z * g) * (g⁻¹ * h * g) ∈ rootSet D x := hz.mp h1
      exact (hmem (h⁻¹ * z * h)).mpr (by
        rw [show g⁻¹ * (h⁻¹ * z * h) * g =
          (g⁻¹ * h * g)⁻¹ * (g⁻¹ * z * g) * (g⁻¹ * h * g) from by group]
        exact h2)
    · intro hzmem
      have h1 : g⁻¹ * (h⁻¹ * z * h) * g ∈ rootSet D x := (hmem (h⁻¹ * z * h)).mp hzmem
      have h2 : (g⁻¹ * h * g)⁻¹ * (g⁻¹ * z * g) * (g⁻¹ * h * g) ∈ rootSet D x := by
        rw [show (g⁻¹ * h * g)⁻¹ * (g⁻¹ * z * g) * (g⁻¹ * h * g) =
          g⁻¹ * (h⁻¹ * z * h) * g from by group]
        exact h1
      have h3 : g⁻¹ * z * g ∈ rootSet D x := hz.mpr h2
      exact (hmem z).mpr h3

private theorem secondKindStructure_of_mem_rootSet (c : SzCfg G D d E e n) {a b x : G}
    (ha : a ∈ E) (hb : b ∈ rootSet D a) (hne : b ≠ a) (hab : a⁻¹ * b ∈ szQ E)
    (hxE : x ∈ E) (hxa : ¬ Commute x a) :
    SecondKindStructure a x b := by
  have haD : a ∈ D := (c.subset_commSet ha).1
  have hbD : b ∈ D := hb.1
  have hxD : x ∈ D := (c.subset_commSet hxE).1
  have hcomm_ab : Commute a b :=
    commute_of_mem_rootSet haD (mem_rootSet_self haD) hb
  have hax : ¬ Commute a x := fun h => hxa h.symm
  have hbx : ¬ Commute b x := fun h => hax ((hb.2 x hxD).mp h)
  have htri : Asc72.IsTriangle D a x b :=
    ⟨haD, hbD, hxD, fun h => hne h.symm, hcomm_ab, hax, hbx⟩
  have hab' : a * b ∈ szQ E := by
    simpa [c.hyp.setup.oddT.inv_eq haD] using hab
  have horder4 : orderOf (a * b * x) = 4 := by
    have hxH : x ∈ Subgroup.closure E := Subgroup.subset_closure hxE
    have hx2 : x * x = 1 := c.hyp.setup.oddT.mul_self_eq_one hxD
    have hP : IsPGroup 2 ↥(Subgroup.zpowers x ⊔ szQ E) :=
      isPGroup_zpowers_sup_szQ hxH hx2
    have hmem : a * b * x ∈ (Subgroup.zpowers x ⊔ szQ E : Subgroup G) := by
      have h1 : a * b ∈ (szQ E : Subgroup G) := hab'
      have h2 : x ∈ (Subgroup.zpowers x : Subgroup G) := Subgroup.mem_zpowers x
      have := Subgroup.mul_mem_sup h1 h2
      simpa [sup_comm] using this
    obtain ⟨k, hk⟩ := hP ⟨a * b * x, hmem⟩
    have hdvd : orderOf (a * b * x) ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    rcases Asc72.IsTriangle.orderOf_cases c.hyp.setup.oddT c.hyp.setup.normal htri with
      ⟨hodd, hgt⟩ | h4 | ⟨m, hm, hm1, hord⟩
    · exfalso
      have h1 : orderOf (a * b * x) = 1 :=
        CFSG.Timmesfeld.Special.eq_one_of_odd_of_dvd_two_pow hodd hdvd
      omega
    · exact h4
    · exfalso
      rw [hord] at hdvd
      have h1 : m = 1 :=
        CFSG.Timmesfeld.Special.eq_one_of_odd_of_dvd_two_pow hm
          ((dvd_mul_left m 2).trans hdvd)
      omega
  have hnoThird : ∀ y ∈ D, y ∈ Subgroup.closure ({a, x} : Set G) →
      Asc72.IsTriangle D a y b → ¬ Asc72.IsThirdKind a y b := by
    intro y hyD hyCl htriY hthird
    have hsub : ({a, x} : Set G) ⊆ E := by
      intro z hz
      rcases hz with rfl | rfl
      · exact ha
      · exact hxE
    have hyH : y ∈ Subgroup.closure E := Subgroup.closure_mono hsub hyCl
    have hy2 : y * y = 1 := c.hyp.setup.oddT.mul_self_eq_one hyD
    have hP : IsPGroup 2 ↥(Subgroup.zpowers y ⊔ szQ E) :=
      isPGroup_zpowers_sup_szQ hyH hy2
    have hmem : a * b * y ∈ (Subgroup.zpowers y ⊔ szQ E : Subgroup G) := by
      have h1 : a * b ∈ (szQ E : Subgroup G) := hab'
      have h2 : y ∈ (Subgroup.zpowers y : Subgroup G) := Subgroup.mem_zpowers y
      have := Subgroup.mul_mem_sup h1 h2
      simpa [sup_comm] using this
    obtain ⟨k, hk⟩ := hP ⟨a * b * y, hmem⟩
    have hdvd : orderOf (a * b * y) ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    obtain ⟨m, hm, hm1, hord⟩ := hthird
    rw [hord] at hdvd
    have h1 : m = 1 :=
      CFSG.Timmesfeld.Special.eq_one_of_odd_of_dvd_two_pow hm
        ((dvd_mul_left m 2).trans hdvd)
    omega
  exact oddTranspSecondKind (G := G) (D := D) c.hyp.setup.oddT c.hyp.setup.normal a x b
    htri horder4 hnoThird



private theorem mem_normalizer_rootSet_of_mem_rootSet (c : SzCfg G D d E e n) {a b x : G}
    (ha : a ∈ E) (hb : b ∈ rootSet D a) (hne : b ≠ a) (hab : a⁻¹ * b ∈ szQ E)
    (hxE : x ∈ E) (hxa : ¬ Commute x a) :
    a * b ∈ Subgroup.normalizer (rootSet D x) := by
  have haD : a ∈ D := (c.subset_commSet ha).1
  have hxD : x ∈ D := (c.subset_commSet hxE).1
  have hax : ¬ Commute a x := fun h => hxa h.symm
  have S := secondKindStructure_of_mem_rootSet c ha hb hne hab hxE hxa
  let N : Subgroup G := conjClosure (Subgroup.closure ({a, x} : Set G)) (a * b)
  have hmemN : a * b ∈ N :=
    Subgroup.subset_closure ⟨1, Subgroup.one_mem _, by group⟩
  have hNcomm : N ≤ Subgroup.centralizer ({a * b} : Set G) := by
    intro n hn
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact S.comm n hn (a * b) hmemN
  have hCnorm : Subgroup.centralizer ({a * b} : Set G) ≤
      Subgroup.normalizer (rootSet D a) :=
    centralizer_mul_le_normalizer c.hyp.setup.oddT c.hyp.setup.normal haD
      (mem_rootSet_self haD) hb (fun h => hne h.symm)
  have hNnorm : N ≤ Subgroup.normalizer (rootSet D a) := hNcomm.trans hCnorm
  obtain ⟨w, hwCl, hwa⟩ :=
    Asc72.IsOddTransp.exists_conj c.hyp.setup.oddT haD hxD hax
  have hsub : ({a, x} : Set G) ⊆ ({a, x, b} : Set G) := by
    intro z hz
    rcases hz with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  have hwCl' : w ∈ Subgroup.closure ({a, x, b} : Set G) :=
    Subgroup.closure_mono hsub hwCl
  have hroot : (fun x => w * x * w⁻¹) '' rootSet D a = rootSet D x := by
    have h1 := CFSG.Timmesfeld.rootSet_conj c.hyp.setup.isClass w a
    rw [hwa] at h1
    exact h1.symm
  have hwN : w⁻¹ * (a * b) * w ∈ N := by
    simpa [MulAut.conj_apply] using S.normal w⁻¹ (Subgroup.inv_mem _ hwCl') (a * b) hmemN
  rw [← hroot]
  exact (mem_normalizer_rootSet_conj_image_iff D (x := a) (g := w) (h := a * b)).mpr
    (hNnorm hwN)



private theorem mem_normalizer_rootSet_of_commute {a y : G}
    (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (h : Commute a y) :
    a ∈ Subgroup.normalizer (rootSet D y) := by
  have hy : a * y * a⁻¹ = y := by rw [h.eq]; group
  have h1 := CFSG.Timmesfeld.rootSet_conj hclass a y
  rw [hy] at h1
  rw [Subgroup.mem_set_normalizer_iff'']
  intro z
  constructor
  · intro hmem
    rw [h1] at hmem ⊢
    rcases hmem with ⟨w, hw, hwz⟩
    rw [show a⁻¹ * z * a = w from by rw [← hwz]; group]
    exact h1 ▸ hw
  · intro hmem
    rw [h1]
    exact ⟨a⁻¹ * z * a, hmem, by group⟩

private theorem mem_normalizer_rootSet_of_mem_E_or_rootSet (c : SzCfg G D d E e n) {a b y : G}
    (ha : a ∈ E) (hb : b ∈ rootSet D a) (hne : b ≠ a) (hab : a⁻¹ * b ∈ szQ E)
    (hy : y ∈ E ∪ rootSet D d) : a * b ∈ Subgroup.normalizer (rootSet D y) := by
  have haD : a ∈ D := (c.subset_commSet ha).1
  have hclass : ∃ d₀ : G, D = {g | IsConj d₀ g} := c.hyp.setup.isClass
  rcases hy with hyE | hyF
  · have hyD : y ∈ D := (c.subset_commSet hyE).1
    by_cases hcomm : Commute a y
    · have hby : Commute b y := (hb.2 y hyD).mpr hcomm
      exact mem_normalizer_rootSet_of_commute hclass (Commute.mul_left hcomm hby)
    · exact mem_normalizer_rootSet_of_mem_rootSet c ha hb hne hab hyE
        (fun h => hcomm h.symm)
  · have hyF' : y ∈ normSet D E \ E := by
      rw [c.normSet_diff_eq]
      exact hyF
    have hay : Commute a y := (OddLocal.commute_of_mem_F c.hyp.setup c.maxOrbit hyF' ha).symm
    have hby : Commute b y :=
      (OddLocal.commute_of_mem_F c.hyp.setup c.maxOrbit hyF' (c.rootSet_subset_of_mem ha hb)).symm
    exact mem_normalizer_rootSet_of_commute hclass (Commute.mul_left hay hby)


private theorem closure_conj_E_le_centralizer (c : SzCfg G D d E e n) {a g : G}
    (hgda : g * d * g⁻¹ = a) :
    Subgroup.closure ((fun x => g * x * g⁻¹) '' E) ≤
      Subgroup.centralizer (rootSet D a) := by
  have hroot_g : (fun x => g * x * g⁻¹) '' rootSet D d = rootSet D a := by
    have h1 := CFSG.Timmesfeld.rootSet_conj c.hyp.setup.isClass g d
    rw [hgda] at h1
    exact h1.symm
  rw [Subgroup.closure_le]
  rintro z ⟨e, heE, rfl⟩
  change (fun x => g * x * g⁻¹) e ∈ Subgroup.centralizer (rootSet D a)
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  rw [← hroot_g] at hf
  obtain ⟨f₀, hf₀, hf₀eq⟩ := hf
  have hf₀F : f₀ ∈ normSet D E \ E := by
    rw [c.normSet_diff_eq]
    exact hf₀
  have hcomm_fe : Commute f₀ e :=
    OddLocal.commute_of_mem_F c.hyp.setup c.maxOrbit hf₀F heE
  rw [← hf₀eq]
  exact (Commute.conj_iff g).mpr hcomm_fe

private theorem exists_conj_commonNeighbour_commute (c : SzCfg G D d E e n) {a b cc : G}
    (ha : a ∈ E) (hb : b ∈ rootSet D a)
    (hccD : cc ∈ D) (hcc_a : Commute cc a) (hcc_notroot : cc ∉ rootSet D a) :
    ∃ w : G, w * cc * w⁻¹ = d ∧ Commute w (a * b) := by
  have haD : a ∈ D := (c.subset_commSet ha).1
  obtain ⟨g, hgda⟩ := isConj_iff.mp (c.hyp.setup.isConj c.d_mem haD)
  have hview : viewE D a = (fun x => g * x * g⁻¹) '' E := by
    have h1 := viewE_conj c.hyp.setup.normal g d
    rw [hgda, c.viewE_eq] at h1
    exact h1
  have hc_view : cc ∈ viewE D a := ⟨hccD, hcc_a, hcc_notroot⟩
  have hd_view : d ∈ viewE D a :=
    ⟨c.d_mem, ((c.subset_commSet ha).2.1).symm,
      fun h => c.d_not_mem (c.rootSet_subset_of_mem ha h)⟩
  rw [hview] at hc_view hd_view
  obtain ⟨c₀, hc₀E, hc₀eq⟩ := hc_view
  obtain ⟨d₀, hd₀E, hd₀eq⟩ := hd_view
  have hc₀eq' : g * c₀ * g⁻¹ = cc := hc₀eq
  have hd₀eq' : g * d₀ * g⁻¹ = d := hd₀eq
  obtain ⟨h, hhCl, hhconj⟩ := c.exists_conj hc₀E hd₀E
  let w : G := g * h * g⁻¹
  have hwc : w * cc * w⁻¹ = d := by
    have h1 : w * cc * w⁻¹ = g * (h * c₀ * h⁻¹) * g⁻¹ := by
      dsimp [w]
      rw [← hc₀eq']
      group
    rw [h1, hhconj, hd₀eq']
  refine ⟨w, hwc, ?_⟩
  have hwCl : w ∈ Subgroup.closure ((fun x => g * x * g⁻¹) '' E) := by
    have hhmap : g * h * g⁻¹ ∈
        Subgroup.map (MulAut.conj g).toMonoidHom (Subgroup.closure E) :=
      Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hhCl
    have hmap : Subgroup.map (MulAut.conj g).toMonoidHom (Subgroup.closure E) =
        Subgroup.closure ((fun x => g * x * g⁻¹) '' E) := by
      rw [MonoidHom.map_closure]
      rfl
    rwa [hmap] at hhmap
  have hcent := closure_conj_E_le_centralizer c hgda
  have hwcent : w ∈ Subgroup.centralizer (rootSet D a) := hcent hwCl
  have hwa : Commute w a :=
    (Subgroup.mem_centralizer_iff.mp hwcent a (mem_rootSet_self haD)).symm
  have hwb : Commute w b :=
    (Subgroup.mem_centralizer_iff.mp hwcent b hb).symm
  exact hwa.mul_right hwb

private theorem mem_normalizer_rootSet_of_mem (c : SzCfg G D d E e n) {a b : G}
    (ha : a ∈ E) (hb : b ∈ rootSet D a) (hne : b ≠ a) (hab : a⁻¹ * b ∈ szQ E)
    {y : G} (hyD : y ∈ D) : a * b ∈ Subgroup.normalizer (rootSet D y) := by
  by_cases hcomm : Commute a y
  · have hby : Commute b y := (hb.2 y hyD).mpr hcomm
    exact mem_normalizer_rootSet_of_commute c.hyp.setup.isClass (Commute.mul_left hcomm hby)
  · have haD : a ∈ D := (c.subset_commSet ha).1
    have hconn : ∀ x ∈ D, ∀ z ∈ D, Reach D x z := by
      intro x hx z hz
      by_contra h
      exact c.hyp.conn ⟨x, hx, z, hz, h⟩
    obtain ⟨cc, hccD, hcc_a, hcc_y⟩ :=
      commonNeighbour (G := G) (D := D) c.hyp.setup hconn c.hyp.sq a haD y hyD hcomm
    have hcc_notroot : cc ∉ rootSet D a := by
      intro hccroot
      exact hcomm ((hccroot.2 y hyD).mp hcc_y)
    obtain ⟨w, hwc, hwab⟩ :=
      exists_conj_commonNeighbour_commute c ha hb hccD hcc_a hcc_notroot
    have hywD : w * y * w⁻¹ ∈ D := c.hyp.setup.conj_mem w hyD
    have hyw_comm : Commute (w * y * w⁻¹) d := by
      have h1 : Commute (w * cc * w⁻¹) (w * y * w⁻¹) :=
        (Commute.conj_iff w).mpr hcc_y
      rw [hwc] at h1
      exact h1.symm
    have hyw_EF : w * y * w⁻¹ ∈ E ∪ rootSet D d := by
      rw [Set.union_comm]
      exact (c.commute_d_iff hywD).mp hyw_comm
    have hiv : a * b ∈ Subgroup.normalizer (rootSet D (w * y * w⁻¹)) :=
      mem_normalizer_rootSet_of_mem_E_or_rootSet c ha hb hne hab hyw_EF
    have hroot_w : (fun x => w * x * w⁻¹) '' rootSet D y = rootSet D (w * y * w⁻¹) :=
      (CFSG.Timmesfeld.rootSet_conj c.hyp.setup.isClass w y).symm
    rw [← hroot_w] at hiv
    have hfin := (mem_normalizer_rootSet_conj_image_iff D (x := y) (g := w) (h := a * b)).mp hiv
    rwa [show w⁻¹ * (a * b) * w = a * b from by
      calc w⁻¹ * (a * b) * w = w⁻¹ * ((a * b) * w) := by group
        _ = w⁻¹ * (w * (a * b)) := by rw [← hwab.eq]
        _ = a * b := by group] at hfin


private def rootSetKernel (D : Set G) : Subgroup G :=
  ⨅ x : D, Subgroup.normalizer (rootSet D x)

private theorem rootSetKernel_normal (c : SzCfg G D d E e n) :
    (rootSetKernel D).Normal := by
  refine ⟨fun g hg h => ?_⟩
  rw [rootSetKernel, Subgroup.mem_iInf] at hg ⊢
  intro x
  have hx' : h⁻¹ * (x : G) * h ∈ D := by
    simpa using c.hyp.setup.conj_mem h⁻¹ x.2
  have hg' : g ∈ Subgroup.normalizer (rootSet D (h⁻¹ * (x : G) * h)) := hg ⟨_, hx'⟩
  have hs : rootSet D (h⁻¹ * (x : G) * h) =
      (fun y => h⁻¹ * y * h) '' rootSet D x := by
    have h1 := CFSG.Timmesfeld.rootSet_conj c.hyp.setup.isClass h⁻¹ (x : G)
    simpa [mul_assoc] using h1
  rw [hs] at hg'
  have hfin := (mem_normalizer_rootSet_conj_image_iff D (x := x) (g := h⁻¹) (h := g)).mp
    (by simpa using hg')
  simpa using hfin

private theorem rootSetKernel_disjoint (c : SzCfg G D d E e n) :
    ∀ x ∈ D, x ∉ rootSetKernel D := by
  intro y hyD hyK
  have hK : (rootSetKernel D).Normal := rootSetKernel_normal c
  have hDsub : D ⊆ rootSetKernel D := by
    intro z hzD
    obtain ⟨g, hg⟩ := isConj_iff.mp (c.hyp.setup.isConj hyD hzD)
    rw [← hg]
    exact hK.conj_mem y hyK g
  have hgen : Subgroup.closure D ≤ Subgroup.normalizer (rootSet D d) := by
    rw [Subgroup.closure_le]
    intro z hzD
    exact (Subgroup.mem_iInf.mp (hDsub hzD)) ⟨d, c.d_mem⟩
  rw [c.hyp.setup.gen] at hgen
  have htop : Subgroup.normalizer (rootSet D d) = ⊤ := eq_top_iff.mpr hgen
  have hEd : rootSet D d = D := by
    refine Set.Subset.antisymm (rootSet_subset D d) ?_
    intro z hzD
    obtain ⟨g, hg⟩ := isConj_iff.mp (c.hyp.setup.isConj c.d_mem hzD)
    have hgN : g ∈ Subgroup.normalizer (rootSet D d) := by
      rw [htop]
      exact Subgroup.mem_top g
    have hmem : g * d * g⁻¹ ∈ rootSet D d :=
      (Subgroup.mem_set_normalizer_iff.mp hgN d).mp (mem_rootSet_self c.d_mem)
    exact hg ▸ hmem
  have he : e ∈ rootSet D d := by
    rw [hEd]
    exact (c.subset_commSet c.e_mem).1
  exact (Set.disjoint_left.mp c.disjoint) he c.e_mem


theorem SzCfg.eq_of_mem_rootSet (c : SzCfg G D d E e n) {a b : G} (ha : a ∈ E)
    (hb : b ∈ rootSet D a) (hab : a⁻¹ * b ∈ szQ E) : b = a := by
  by_contra hne
  have haD : a ∈ D := (c.subset_commSet ha).1
  have hab' : a * b ∈ szQ E := by
    simpa [c.hyp.setup.oddT.inv_eq haD] using hab
  have hmemK : a * b ∈ rootSetKernel D := by
    rw [rootSetKernel, Subgroup.mem_iInf]
    intro y
    exact mem_normalizer_rootSet_of_mem c ha hb hne hab y.2
  have hK : (rootSetKernel D).Normal := rootSetKernel_normal c
  have hKD : ∀ x ∈ D, x ∉ rootSetKernel D := rootSetKernel_disjoint c
  have hcenter : a * b ∈ Subgroup.center G := (Hyp.le_center_of_disjoint c.hyp hK hKD) hmemK
  have hcomm_ab : Commute a b :=
    commute_of_mem_rootSet haD (mem_rootSet_self haD) hb
  have ha2 : a * a = 1 := c.hyp.setup.oddT.mul_self_eq_one haD
  have hb2 : b * b = 1 := c.hyp.setup.oddT.mul_self_eq_one hb.1
  have hab2 : (a * b) * (a * b) = 1 := by
    calc (a * b) * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hcomm_ab.eq]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2, one_mul]
  have hnorm : (Subgroup.zpowers (a * b)).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hcenter)
  have hP : IsPGroup 2 ↥(Subgroup.zpowers (a * b)) :=
    CFSG.Timmesfeld.Bridge.RootClosure.isPGroup_zpowers_of_mul_self_eq_one hab2
  have hle : Subgroup.zpowers (a * b) ≤ CFSG.pCore 2 G :=
    CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hnorm hP
  rw [c.hyp.o2] at hle
  have hab1 : a * b = 1 := by
    have hmem : a * b ∈ (⊥ : Subgroup G) := hle (Subgroup.mem_zpowers (a * b))
    simpa using hmem
  have hba : b = a := by
    calc b = 1 * b := (one_mul b).symm
      _ = (a * a) * b := by rw [ha2]
      _ = a * (a * b) := by group
      _ = a * 1 := by rw [hab1]
      _ = a := mul_one a
  exact hne hba




end CFSG.Timmesfeld.Bridge.OddRoot

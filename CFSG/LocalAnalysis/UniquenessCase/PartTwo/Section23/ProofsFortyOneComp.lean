module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsFortyOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsFortyOneSteps
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.QuotInfBar2
public import CFSG.LocalAnalysis.RankThreeUC.Section5.OpenPCoreEq
public import CFSG.GroupTheory.InvOddSimple
public import CFSG.Quasithin.Background.F918Z4bPrime
public import CFSG.Adapters.WholeGroupLayer
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinRad
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.ThreeConstrained
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22l
public import CFSG.Quasithin.Background.C2PushLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx23L.S2341Frame

private theorem Wstar_isElemAbelian {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h1930 : H1930 D) :
    IsElemAbelian 2 (imageOTwoQuot D.M X.W) := by
  have h := (X.isElemAbelian_W h4 h1930).subgroupOf D.M
  exact h.map (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M))

private theorem Wstar_mk_eq_one_iff {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h39 : S23_39 D Ch)
    (h40 : S23_40 D Ch) (h1930 : H1930 D) (hneq : ⁅X.W, X.F⁆ ≠ ⊥) {w : G}
    (hw : w ∈ X.W) :
    (QuotientGroup.mk ⟨w, s2341_W_le_M X h4 h23 h39 h40 h1930 hw⟩ : Bar2 D.M) = 1 ↔
      w ∈ X.Zh := by
  have hinf := (s2341_W_inf_O2 X h4 h23 h39 h40 h1930 hneq).2
  rw [mk_eq_one_iff_mem_pCoreOf]
  constructor
  · intro h
    exact hinf ▸ (show w ∈ X.W ⊓ CFSG.Open.pCoreOf 2 D.M from ⟨hw, h⟩)
  · intro h
    exact (hinf.symm ▸ h).2

private theorem Wstar_card {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h39 : S23_39 D Ch)
    (h40 : S23_40 D Ch) (h1930 : H1930 D) (hneq : ⁅X.W, X.F⁆ ≠ ⊥) :
    Nat.card (imageOTwoQuot D.M X.W) = 2 ^ CFSG.Open.pRank 2 D.Z := by
  classical
  have hWM : X.W ≤ D.M := s2341_W_le_M X h4 h23 h39 h40 h1930
  have hinf := (s2341_W_inf_O2 X h4 h23 h39 h40 h1930 hneq).2
  let A : Subgroup ↥D.M := X.W.subgroupOf D.M
  let π : ↥D.M →* Bar2 D.M := QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)
  have hker : (A ⊓ π.ker : Subgroup ↥D.M) =
      (X.W ⊓ CFSG.Open.pCoreOf 2 D.M).subgroupOf D.M := by
    ext m
    refine ⟨fun hm => ⟨hm.1, ?_⟩, fun hm => ⟨hm.1, ?_⟩⟩
    · exact (mk_eq_one_iff_mem_pCoreOf m).mp (MonoidHom.mem_ker.mp hm.2)
    · exact MonoidHom.mem_ker.mpr ((mk_eq_one_iff_mem_pCoreOf m).mpr hm.2)
  have hkerCard : Nat.card (A ⊓ π.ker : Subgroup ↥D.M) = Nat.card X.Zh := by
    rw [hker, hinf]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (X.Zh_le_W.trans hWM)).toEquiv
  have hcardA : Nat.card A = Nat.card X.W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWM).toEquiv
  have hmul := CFSG.Quasithin.SteinbergBS.card_inf_ker_mul_card_map π A
  have hmap : A.map π = imageOTwoQuot D.M X.W := rfl
  rw [hmap, hkerCard, hcardA, X.card_W h4 h23 h1930, X.card_Zh h4 h1930, pow_two] at hmul
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (pow_ne_zero _ (by norm_num))) hmul

private theorem mem_Wstar_of_mem {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h39 : S23_39 D Ch)
    (h40 : S23_40 D Ch) (h1930 : H1930 D) {v : D.M} (hv : (v : G) ∈ X.W) :
    (QuotientGroup.mk v : Bar2 D.M) ∈ imageOTwoQuot D.M X.W := by
  have hWM : X.W ≤ D.M := s2341_W_le_M X h4 h23 h39 h40 h1930
  exact Subgroup.mem_map.mpr ⟨v, hv, rfl⟩

private theorem image_isSimple {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (h1930 : H1930 D) (h37 : S23_37 D Ch) {K : Subgroup G} (hK : K ∈ calC D.M) :
    IsSimpleGroup (imageOTwoQuot D.M K) := by
  obtain ⟨q, hq, hq2, hL2⟩ := (h37 h1930 c K hK).1
  obtain ⟨e⟩ := CFSG.Quasithin.C2Push.nonempty_mulEquiv_pCore_quotient_imageOTwoQuot hK.1
  haveI : IsSimpleGroup (Bar2 K) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2
  exact MulEquiv.isSimpleGroup e.symm

private theorem image_center_eq_bot {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (h1930 : H1930 D) (h37 : S23_37 D Ch) {K : Subgroup G} (hK : K ∈ calC D.M) :
    Subgroup.center (imageOTwoQuot D.M K) = ⊥ := by
  obtain ⟨q, hq, hq2, hL2⟩ := (h37 h1930 c K hK).1
  obtain ⟨e⟩ := CFSG.Quasithin.C2Push.nonempty_mulEquiv_pCore_quotient_imageOTwoQuot hK.1
  have hc : Subgroup.center (Bar2 K) = ⊥ := center_eq_bot_of_isL2Odd hK.2.2 hL2
  have hmap := Subgroup.map_center_eq e
  rw [hc, Subgroup.map_bot] at hmap
  exact hmap.symm

private theorem image_not_isPGroup_two {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (h1930 : H1930 D) (h37 : S23_37 D Ch) {K : Subgroup G} (hK : K ∈ calC D.M) :
    ¬ IsPGroup 2 (imageOTwoQuot D.M K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsSimpleGroup (imageOTwoQuot D.M K) := image_isSimple (c := c) h1930 h37 hK
  have hcen := image_center_eq_bot (c := c) h1930 h37 hK
  intro hp
  have hc : Nontrivial ↥(Subgroup.center (imageOTwoQuot D.M K)) := hp.center_nontrivial
  rw [hcen] at hc
  exact not_nontrivial_iff_subsingleton.mpr inferInstance hc

private theorem mul_ne_one_of_center_eq_bot {Q : Type*} [Group Q] {K : Subgroup Q}
    (hZ : Subgroup.center K = ⊥) {y z : Q} (hyK : y ∈ K) (hy1 : y ≠ 1)
    (hz : ∀ k ∈ K, Commute z k) : y * z ≠ 1 := by
  intro h
  have hyz : y = z⁻¹ := eq_inv_of_mul_eq_one_left h
  have hyC : (⟨y, hyK⟩ : K) ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    show (k : Q) * y = y * (k : Q)
    rw [hyz]
    exact (Commute.inv_left (hz (k : Q) k.2)).eq.symm
  rw [hZ] at hyC
  exact hy1 (congrArg Subtype.val (Subgroup.mem_bot.mp hyC))

private theorem comp_cent_pow_normalizer {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (X : S2341Frame D Ch c) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h39 : S23_39 D Ch) (h40 : S23_40 D Ch)
    (h1930 : H1930 D) {K : Subgroup G} (hK : K ∈ calC D.M)
    (hN : ∀ v : D.M, (v : G) ∈ X.W → ∀ x : Bar2 D.M,
      x ∈ imageOTwoQuot D.M K →
      (QuotientGroup.mk v) * x * (QuotientGroup.mk v)⁻¹ ∈ imageOTwoQuot D.M K)
    {v : D.M} (hvW : (v : G) ∈ X.W) :
    (QuotientGroup.mk v : Bar2 D.M) * (QuotientGroup.mk v) = 1 ∧
      (QuotientGroup.mk v : Bar2 D.M) ∈
        Subgroup.normalizer ((imageOTwoQuot D.M K) : Set (Bar2 D.M)) := by
  have hE := Wstar_isElemAbelian X h4 h1930
  have htv := mem_Wstar_of_mem X h4 h23 h39 h40 h1930 hvW
  have ht2 : (QuotientGroup.mk v : Bar2 D.M) * (QuotientGroup.mk v) = 1 := by
    simpa [pow_two] using hE.2 (QuotientGroup.mk v) htv
  have htN : (QuotientGroup.mk v : Bar2 D.M) ∈
      Subgroup.normalizer ((imageOTwoQuot D.M K) : Set (Bar2 D.M)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact hN v hvW y hy
    · intro hy
      have h := hN v⁻¹ (X.W.inv_mem hvW)
        ((QuotientGroup.mk v) * y * (QuotientGroup.mk v)⁻¹) hy
      simpa [map_inv, mul_assoc] using h
  exact ⟨ht2, htN⟩

private theorem comp_cent {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h39 : S23_39 D Ch)
    (h40 : S23_40 D Ch) (h1930 : H1930 D) (h37 : S23_37 D Ch) {K : Subgroup G}
    (hK : K ∈ calC D.M)
    (hN : ∀ v : D.M, (v : G) ∈ X.W → ∀ x : Bar2 D.M,
      x ∈ imageOTwoQuot D.M K →
      (QuotientGroup.mk v) * x * (QuotientGroup.mk v)⁻¹ ∈ imageOTwoQuot D.M K)
    {w : D.M} (hwW : (w : G) ∈ X.W) (hwZh : (w : G) ∉ X.Zh)
    (hwc : ∀ x : Bar2 D.M, x ∈ imageOTwoQuot D.M K →
      Commute (QuotientGroup.mk w) x) (h7 : X.NoOddInverted) :
    ∀ v : D.M, (v : G) ∈ X.W → ∀ x : Bar2 D.M, x ∈ imageOTwoQuot D.M K →
      Commute (QuotientGroup.mk v) x := by
  intro v hvW
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hxK, hxnc⟩ := hcon
  haveI : IsSimpleGroup (imageOTwoQuot D.M K) := image_isSimple (c := c) h1930 h37 hK
  obtain ⟨ht2, htN⟩ := comp_cent_pow_normalizer X h4 h23 h39 h40 h1930 hK hN hvW
  have htC : (QuotientGroup.mk v : Bar2 D.M) ∉
      Subgroup.centralizer ((imageOTwoQuot D.M K) : Set (Bar2 D.M)) := by
    intro hc
    exact hxnc ((Subgroup.mem_centralizer_iff.mp hc x hxK).symm)
  obtain ⟨y, hyK, hy1, hyodd, hyinv⟩ :=
    CFSG.GroupTheory.inv_odd_of_simple (K := imageOTwoQuot D.M K)
      (image_not_isPGroup_two (c := c) h1930 h37 hK) ht2 htN htC
  exact h7 y hy1 hyodd v w hvW hwW hwZh hyinv (hwc y hyK)

private theorem map_conj_map_conj {Q : Type*} [Group Q] (K : Subgroup Q) (g h : Q) :
    (K.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h).toMonoidHom =
      K.map (MulAut.conj (h * g)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem map_conj_ne_of_not_mem_normalizer {Q : Type*} [Group Q] {K : Subgroup Q}
    {g : Q} (hg : g ∉ Subgroup.normalizer (K : Set Q)) :
    K.map (MulAut.conj g).toMonoidHom ≠ K := by
  intro h
  exact hg ((Subgroup.mem_normalizer_iff_map_conj_eq (H := K) (g := g)).mpr h)

private theorem map_conj_one {Q : Type*} [Group Q] (K : Subgroup Q) :
    K.map (1 : MulAut Q).toMonoidHom = K := by
  ext x
  simp

private theorem map_conj_four_ne {Q : Type*} [Group Q] {K : Subgroup Q} {a b : Q}
    (ha2 : a * a = 1) (hb2 : b * b = 1) (hab : a * b = b * a)
    (haN : a ∉ Subgroup.normalizer (K : Set Q))
    (hbN : b ∉ Subgroup.normalizer (K : Set Q))
    (habN : a * b ∉ Subgroup.normalizer (K : Set Q)) :
    K.map (MulAut.conj a).toMonoidHom ≠ K ∧
      K.map (MulAut.conj b).toMonoidHom ≠ K ∧
      K.map (MulAut.conj (a * b)).toMonoidHom ≠ K ∧
      K.map (MulAut.conj a).toMonoidHom ≠ K.map (MulAut.conj b).toMonoidHom ∧
      K.map (MulAut.conj a).toMonoidHom ≠
        K.map (MulAut.conj (a * b)).toMonoidHom ∧
      K.map (MulAut.conj b).toMonoidHom ≠
        K.map (MulAut.conj (a * b)).toMonoidHom := by
  have hab' : a * (a * b) = b := by rw [← mul_assoc, ha2, one_mul]
  have hba' : b * (a * b) = a := by
    calc b * (a * b) = b * (b * a) := by rw [hab]
      _ = (b * b) * a := by rw [mul_assoc]
      _ = a := by rw [hb2, one_mul]
  refine ⟨map_conj_ne_of_not_mem_normalizer haN,
    map_conj_ne_of_not_mem_normalizer hbN,
    map_conj_ne_of_not_mem_normalizer habN, ?_, ?_, ?_⟩
  · intro h
    have h' := congrArg (fun L => L.map (MulAut.conj a).toMonoidHom) h
    rw [map_conj_map_conj K a a, map_conj_map_conj K b a, ha2,
      map_one (MulAut.conj), map_conj_one] at h'
    exact map_conj_ne_of_not_mem_normalizer habN h'.symm
  · intro h
    have h' := congrArg (fun L => L.map (MulAut.conj a).toMonoidHom) h
    rw [map_conj_map_conj K a a, map_conj_map_conj K (a * b) a, hab', ha2,
      map_one (MulAut.conj), map_conj_one] at h'
    exact map_conj_ne_of_not_mem_normalizer hbN h'.symm
  · intro h
    have h' := congrArg (fun L => L.map (MulAut.conj b).toMonoidHom) h
    rw [map_conj_map_conj K b b, map_conj_map_conj K (a * b) b, hba', hb2,
      map_one (MulAut.conj), map_conj_one] at h'
    exact map_conj_ne_of_not_mem_normalizer haN h'.symm

private structure CompNormData {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) (K : Subgroup G) (v : D.M) where
  a : Bar2 D.M
  A : Subgroup (Bar2 D.M)
  W1 : Subgroup (Bar2 D.M)
  Kstar : Subgroup (Bar2 D.M)
  ha : a = QuotientGroup.mk v
  hA : A = imageOTwoQuot D.M X.W
  hW1 : W1 = A ⊓ Subgroup.normalizer (Kstar : Set (Bar2 D.M))
  hKstar : Kstar = imageOTwoQuot D.M K
  haA : a ∈ A
  ha2 : a * a = 1
  haN : a ∉ Subgroup.normalizer (Kstar : Set (Bar2 D.M))
  hE : IsElemAbelian 2 A
  hAcard : Nat.card A = 2 ^ CFSG.Open.pRank 2 D.Z
  hKcomp : CFSG.IsComponent Kstar
  hKnot2 : ¬ IsPGroup 2 ↥Kstar
  hKcenter : Subgroup.center Kstar = ⊥
  hKsimple : IsSimpleGroup ↥Kstar
  haW1 : a ∉ W1

private structure FourConjData {Q : Type*} [Group Q] (K : Subgroup Q) (a b y : Q) where
  y2 : Q
  y3 : Q
  y4 : Q
  h2eq : y2 = (MulAut.conj a) y
  h3eq : y3 = (MulAut.conj b) y
  h4eq : y4 = (MulAut.conj (a * b)) y
  hy2 : y2 ∈ K.map (MulAut.conj a).toMonoidHom
  hy3 : y3 ∈ K.map (MulAut.conj b).toMonoidHom
  hy4 : y4 ∈ K.map (MulAut.conj (a * b)).toMonoidHom
  hy2odd : Odd (orderOf y2)
  hy3odd : Odd (orderOf y3)
  hy4odd : Odd (orderOf y4)
  hyodd : Odd (orderOf y)
  hyy2 : Commute y y2
  hyy3 : Commute y y3
  hyy4 : Commute y y4
  hy2y4 : Commute y2 y4
  hy3y4 : Commute y3 y4
  hy3y2 : Commute y3 y2
  hy2C : ∀ k ∈ K, Commute y2 k
  hy3C : ∀ k ∈ K, Commute y3 k
  hy4C : ∀ k ∈ K, Commute y4 k

private structure FourConjX {Q : Type*} [Group Q] (K : Subgroup Q) (a b y : Q)
    extends FourConjData K a b y where
  z : Q
  x : Q
  hz : z = y3 * (y2 * y4)⁻¹
  hx : x = y * z
  hzodd : Odd (orderOf z)
  hyz : Commute y z
  hzC : ∀ k ∈ K, Commute z k
  hx1 : x ≠ 1
  hxodd : Odd (orderOf x)

private structure FourConjCase {Q : Type*} [Group Q] (A W1 K : Subgroup Q) (a : Q) where
  b : Q
  hbA : b ∈ A
  hbNot : b ∉ W1 ⊔ Subgroup.zpowers a
  hbNotW1 : b ∉ W1
  hbN : b ∉ Subgroup.normalizer (K : Set Q)
  hb2 : b * b = 1
  habc : a * b = b * a
  habNot : a * b ∉ W1 ⊔ Subgroup.zpowers a
  habA : a * b ∈ A
  habN : a * b ∉ Subgroup.normalizer (K : Set Q)

private theorem four_conj_component_data {Q : Type*} [Group Q]
    {K : Subgroup Q} {a b : Q} (hK : CFSG.IsComponent K) :
    CFSG.IsComponent (K.map (MulAut.conj a).toMonoidHom) ∧
      CFSG.IsComponent (K.map (MulAut.conj b).toMonoidHom) ∧
      CFSG.IsComponent (K.map (MulAut.conj (a * b)).toMonoidHom) := by
  exact ⟨CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj a) hK,
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj b) hK,
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj (a * b)) hK⟩

private noncomputable def comp_norm_data {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h39 : S23_39 D Ch) (h40 : S23_40 D Ch) (h1930 : H1930 D)
    (hneq : ⁅X.W, X.F⁆ ≠ ⊥) (h37 : S23_37 D Ch)
    {K : Subgroup G} (hK : K ∈ calC D.M) {v : D.M} (hvW : (v : G) ∈ X.W)
    (hcon : (QuotientGroup.mk v : Bar2 D.M) ∉
      Subgroup.normalizer (imageOTwoQuot D.M K : Set (Bar2 D.M))) :
    CompNormData X K v := by
  have hE := Wstar_isElemAbelian X h4 h1930
  have hAcard := Wstar_card X h4 h23 h39 h40 h1930 hneq
  set a : Bar2 D.M := QuotientGroup.mk v with ha
  set A : Subgroup (Bar2 D.M) := imageOTwoQuot D.M X.W with hA
  set Kstar : Subgroup (Bar2 D.M) := imageOTwoQuot D.M K with hKstar
  have haA : a ∈ A := by
    rw [ha, hA]
    exact mem_Wstar_of_mem X h4 h23 h39 h40 h1930 hvW
  have ha2 : a * a = 1 := by
    have h := hE.2 a haA
    simpa [pow_two] using h
  have haN : a ∉ Subgroup.normalizer (Kstar : Set (Bar2 D.M)) := by
    intro h
    exact hcon (by rw [ha, hKstar]; exact h)
  have hKcomp : CFSG.IsComponent Kstar := by
    rw [hKstar]; exact uc22p22l_barImage_isComponent hK
  have hKnot2 : ¬ IsPGroup 2 ↥Kstar := by
    rw [hKstar]
    exact image_not_isPGroup_two (c := c) h1930 h37 hK
  have hKcenter : Subgroup.center Kstar = ⊥ := by
    rw [hKstar]
    exact image_center_eq_bot (c := c) h1930 h37 hK
  have hKsimple : IsSimpleGroup ↥Kstar := by
    rw [hKstar]; exact image_isSimple (c := c) h1930 h37 hK
  set W1 : Subgroup (Bar2 D.M) :=
    A ⊓ Subgroup.normalizer (Kstar : Set (Bar2 D.M)) with hW1
  have haW1 : a ∉ W1 := fun h => haN h.2
  exact ⟨a, A, W1, Kstar, ha, hA, hW1, hKstar, haA, ha2, haN, hA ▸ hE,
    by rw [hA]; exact hAcard, hKcomp, hKnot2, hKcenter, hKsimple, haW1⟩

private noncomputable def four_conj_case_data {Q : Type*} [Group Q] {A W1 K : Subgroup Q} {a : Q}
    (hE : IsElemAbelian 2 A) (haA : a ∈ A)
    (hW1 : W1 = A ⊓ Subgroup.normalizer (K : Set Q))
    (hcase : ∃ b ∈ A, b ∉ W1 ⊔ Subgroup.zpowers a) :
    FourConjCase A W1 K a := by
  let b : Q := Classical.choose hcase
  have hb_spec := Classical.choose_spec hcase
  have hbA : b ∈ A := hb_spec.1
  have hbNot : b ∉ W1 ⊔ Subgroup.zpowers a := hb_spec.2
  have hbNotW1 : b ∉ W1 := fun h => hbNot (Subgroup.mem_sup_left h)
  have hbN : b ∉ Subgroup.normalizer (K : Set Q) := by
    intro h
    exact hbNotW1 (by rw [hW1]; exact ⟨hbA, h⟩)
  have hb2 : b * b = 1 := by
    have h := hE.2 b hbA
    simpa [pow_two] using h
  have habc : a * b = b * a :=
    congrArg (fun x : A => (x : Q)) (hE.1.is_comm.comm ⟨a, haA⟩ ⟨b, hbA⟩)
  have ha2 : a * a = 1 := by
    simpa [pow_two] using hE.2 a haA
  have habNot : a * b ∉ W1 ⊔ Subgroup.zpowers a := by
    intro h
    apply hbNot
    have hb_eq : b = a * (a * b) := by rw [← mul_assoc, ha2, one_mul]
    rw [hb_eq]
    exact (W1 ⊔ Subgroup.zpowers a).mul_mem
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers a)) h
  have habA : a * b ∈ A := A.mul_mem haA hbA
  have habN : a * b ∉ Subgroup.normalizer (K : Set Q) := by
    intro h
    exact habNot (Subgroup.mem_sup_left (by rw [hW1]; exact ⟨habA, h⟩))
  exact ⟨b, hbA, hbNot, hbNotW1, hbN, hb2, habc, habNot, habA, habN⟩

private theorem four_conj_comm_outer {Q : Type*} [Group Q] [Finite Q]
    {K : Subgroup Q} {a b : Q} (hK : CFSG.IsComponent K)
    (h2 : CFSG.IsComponent (K.map (MulAut.conj a).toMonoidHom))
    (h3 : CFSG.IsComponent (K.map (MulAut.conj b).toMonoidHom))
    (h4 : CFSG.IsComponent (K.map (MulAut.conj (a * b)).toMonoidHom))
    (ha2 : a * a = 1) (hb2 : b * b = 1) (hab : a * b = b * a)
    (haN : a ∉ Subgroup.normalizer (K : Set Q))
    (hbN : b ∉ Subgroup.normalizer (K : Set Q))
    (habN : a * b ∉ Subgroup.normalizer (K : Set Q)) :
    (∀ x ∈ K, ∀ y ∈ K.map (MulAut.conj a).toMonoidHom, Commute x y) ∧
      (∀ x ∈ K, ∀ y ∈ K.map (MulAut.conj b).toMonoidHom, Commute x y) ∧
      (∀ x ∈ K, ∀ y ∈ K.map (MulAut.conj (a * b)).toMonoidHom, Commute x y) := by
  have hfour := map_conj_four_ne ha2 hb2 hab haN hbN habN
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy
    exact CFSG.QuasithinUnique.BenderBranch.commute_of_commutator_eq_bot
      (CFSG.ComponentClassification.LocalComponents.commute_of_ne K
        (K.map (MulAut.conj a).toMonoidHom) ((CFSG.isComponent_iff_open K).mp hK)
        ((CFSG.isComponent_iff_open _).mp h2) hfour.1.symm) hx hy
  · intro x hx y hy
    exact CFSG.QuasithinUnique.BenderBranch.commute_of_commutator_eq_bot
      (CFSG.ComponentClassification.LocalComponents.commute_of_ne K
        (K.map (MulAut.conj b).toMonoidHom) ((CFSG.isComponent_iff_open K).mp hK)
        ((CFSG.isComponent_iff_open _).mp h3) hfour.2.1.symm) hx hy
  · intro x hx y hy
    exact CFSG.QuasithinUnique.BenderBranch.commute_of_commutator_eq_bot
      (CFSG.ComponentClassification.LocalComponents.commute_of_ne K
        (K.map (MulAut.conj (a * b)).toMonoidHom) ((CFSG.isComponent_iff_open K).mp hK)
        ((CFSG.isComponent_iff_open _).mp h4) hfour.2.2.1.symm) hx hy

private theorem four_conj_comm_inner {Q : Type*} [Group Q] [Finite Q]
    {K : Subgroup Q} {a b : Q} (hK : CFSG.IsComponent K)
    (h2 : CFSG.IsComponent (K.map (MulAut.conj a).toMonoidHom))
    (h3 : CFSG.IsComponent (K.map (MulAut.conj b).toMonoidHom))
    (h4 : CFSG.IsComponent (K.map (MulAut.conj (a * b)).toMonoidHom))
    (ha2 : a * a = 1) (hb2 : b * b = 1) (hab : a * b = b * a)
    (haN : a ∉ Subgroup.normalizer (K : Set Q))
    (hbN : b ∉ Subgroup.normalizer (K : Set Q))
    (habN : a * b ∉ Subgroup.normalizer (K : Set Q)) :
    (∀ x ∈ K.map (MulAut.conj a).toMonoidHom,
      ∀ y ∈ K.map (MulAut.conj b).toMonoidHom, Commute x y) ∧
      (∀ x ∈ K.map (MulAut.conj a).toMonoidHom,
        ∀ y ∈ K.map (MulAut.conj (a * b)).toMonoidHom, Commute x y) ∧
      (∀ x ∈ K.map (MulAut.conj b).toMonoidHom,
        ∀ y ∈ K.map (MulAut.conj (a * b)).toMonoidHom, Commute x y) := by
  have hfour := map_conj_four_ne ha2 hb2 hab haN hbN habN
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy
    exact CFSG.QuasithinUnique.BenderBranch.commute_of_commutator_eq_bot
      (CFSG.ComponentClassification.LocalComponents.commute_of_ne
        (K.map (MulAut.conj a).toMonoidHom) (K.map (MulAut.conj b).toMonoidHom)
        ((CFSG.isComponent_iff_open _).mp h2) ((CFSG.isComponent_iff_open _).mp h3)
        hfour.2.2.2.1) hx hy
  · intro x hx y hy
    exact CFSG.QuasithinUnique.BenderBranch.commute_of_commutator_eq_bot
      (CFSG.ComponentClassification.LocalComponents.commute_of_ne
        (K.map (MulAut.conj a).toMonoidHom) (K.map (MulAut.conj (a * b)).toMonoidHom)
        ((CFSG.isComponent_iff_open _).mp h2) ((CFSG.isComponent_iff_open _).mp h4)
        hfour.2.2.2.2.1) hx hy
  · intro x hx y hy
    exact CFSG.QuasithinUnique.BenderBranch.commute_of_commutator_eq_bot
      (CFSG.ComponentClassification.LocalComponents.commute_of_ne
        (K.map (MulAut.conj b).toMonoidHom) (K.map (MulAut.conj (a * b)).toMonoidHom)
        ((CFSG.isComponent_iff_open _).mp h3) ((CFSG.isComponent_iff_open _).mp h4)
        hfour.2.2.2.2.2) hx hy

private noncomputable def four_conj_y {Q : Type*} [Group Q] [Finite Q]
    {K : Subgroup Q} {a b y : Q} (hK : CFSG.IsComponent K)
    (ha2 : a * a = 1) (hb2 : b * b = 1) (hab : a * b = b * a)
    (haN : a ∉ Subgroup.normalizer (K : Set Q))
    (hbN : b ∉ Subgroup.normalizer (K : Set Q))
    (habN : a * b ∉ Subgroup.normalizer (K : Set Q))
    (hyK : y ∈ K) (hyodd : Odd (orderOf y)) :
    FourConjData K a b y := by
  obtain ⟨h2, h3, h4⟩ := four_conj_component_data (a := a) (b := b) hK
  obtain ⟨h12, h13, h14⟩ :=
    four_conj_comm_outer hK h2 h3 h4 ha2 hb2 hab haN hbN habN
  obtain ⟨h23, h24, h34⟩ :=
    four_conj_comm_inner hK h2 h3 h4 ha2 hb2 hab haN hbN habN
  have hy2 : (MulAut.conj a) y ∈ K.map (MulAut.conj a).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨y, hyK, rfl⟩
  have hy3 : (MulAut.conj b) y ∈ K.map (MulAut.conj b).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨y, hyK, rfl⟩
  have hy4 : (MulAut.conj (a * b)) y ∈ K.map (MulAut.conj (a * b)).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨y, hyK, rfl⟩
  have hy2odd : Odd (orderOf ((MulAut.conj a) y)) := by
    rw [(MulAut.conj a).orderOf_eq y]
    exact hyodd
  have hy3odd : Odd (orderOf ((MulAut.conj b) y)) := by
    rw [(MulAut.conj b).orderOf_eq y]
    exact hyodd
  have hy4odd : Odd (orderOf ((MulAut.conj (a * b)) y)) := by
    rw [(MulAut.conj (a * b)).orderOf_eq y]
    exact hyodd
  exact ⟨(MulAut.conj a) y, (MulAut.conj b) y, (MulAut.conj (a * b)) y, rfl, rfl, rfl,
    hy2, hy3, hy4, hy2odd, hy3odd, hy4odd, hyodd,
    h12 y hyK _ hy2, h13 y hyK _ hy3, h14 y hyK _ hy4,
    h24 _ hy2 _ hy4, h34 _ hy3 _ hy4, (h23 _ hy2 _ hy3).symm,
    fun k hk => (h12 k hk _ hy2).symm, fun k hk => (h13 k hk _ hy3).symm,
    fun k hk => (h14 k hk _ hy4).symm⟩

private noncomputable def four_conj_z {Q : Type*} [Group Q] {K : Subgroup Q} {a b y : Q}
    (Y : FourConjData K a b y) (hKcenter : Subgroup.center K = ⊥)
    (hyK : y ∈ K) (hy1 : y ≠ 1) :
    FourConjX K a b y := by
  let z : Q := Y.y3 * (Y.y2 * Y.y4)⁻¹
  let x : Q := y * z
  have hzodd : Odd (orderOf z) := by
    change Odd (orderOf (Y.y3 * (Y.y2 * Y.y4)⁻¹))
    have h24 : Odd (orderOf (Y.y2 * Y.y4)) :=
      (Y.hy2odd.mul Y.hy4odd).of_dvd_nat
        (Y.hy2y4.orderOf_mul_dvd_lcm.trans (Nat.lcm_dvd_mul _ _))
    have h24i : Odd (orderOf (Y.y2 * Y.y4)⁻¹) := by rwa [orderOf_inv]
    have h3 : Commute Y.y3 (Y.y2 * Y.y4)⁻¹ := (Y.hy3y2.mul_right Y.hy3y4).inv_right
    exact (Y.hy3odd.mul h24i).of_dvd_nat
      (h3.orderOf_mul_dvd_lcm.trans (Nat.lcm_dvd_mul _ _))
  have hyz : Commute y z := by
    change Commute y (Y.y3 * (Y.y2 * Y.y4)⁻¹)
    exact Y.hyy3.mul_right ((Y.hyy2.mul_right Y.hyy4).inv_right)
  have hzC : ∀ k ∈ K, Commute z k := by
    intro k hk
    have h3 : Commute Y.y3 k := Y.hy3C k hk
    have h2 : Commute Y.y2 k := Y.hy2C k hk
    have h4 : Commute Y.y4 k := Y.hy4C k hk
    change Commute (Y.y3 * (Y.y2 * Y.y4)⁻¹) k
    exact h3.mul_left ((h2.mul_left h4).inv_left)
  have hx1 : x ≠ 1 := by
    change y * z ≠ 1
    exact mul_ne_one_of_center_eq_bot hKcenter hyK hy1 hzC
  have hxodd : Odd (orderOf x) := by
    change Odd (orderOf (y * z))
    exact (Y.hyodd.mul hzodd).of_dvd_nat
      (hyz.orderOf_mul_dvd_lcm.trans (Nat.lcm_dvd_mul _ _))
  exact FourConjX.mk Y z x rfl rfl hzodd hyz hzC hx1 hxodd

private theorem four_conj_inv {Q : Type*} [Group Q] {K : Subgroup Q} {a b y : Q}
    (Z : FourConjX K a b y) (ha2 : a * a = 1) (hb2 : b * b = 1)
    (hab : a * b = b * a) : a * Z.x * a⁻¹ = Z.x⁻¹ := by
  have hconj2a : (MulAut.conj a) * (MulAut.conj a) = 1 := by
    rw [← map_mul (MulAut.conj) a a, ha2, map_one (MulAut.conj)]
  have ha_y : (MulAut.conj a) y = Z.y2 := Z.h2eq.symm
  have ha_y2 : (MulAut.conj a) Z.y2 = y := by
    rw [Z.h2eq]
    change ((MulAut.conj a) * (MulAut.conj a)) y = y
    rw [hconj2a]
    rfl
  have hab_conj : (MulAut.conj a) * (MulAut.conj b) = MulAut.conj (a * b) := by
    rw [← map_mul (MulAut.conj) a b]
  have ha_ab : (MulAut.conj a) * (MulAut.conj (a * b)) = MulAut.conj b := by
    rw [← map_mul (MulAut.conj) a (a * b), show a * (a * b) = b by
      rw [← mul_assoc, ha2, one_mul]]
  have ha_y3 : (MulAut.conj a) Z.y3 = Z.y4 := by
    rw [Z.h3eq, Z.h4eq]
    change ((MulAut.conj a) * (MulAut.conj b)) y = (MulAut.conj (a * b)) y
    rw [hab_conj]
  have ha_y4 : (MulAut.conj a) Z.y4 = Z.y3 := by
    rw [Z.h4eq, Z.h3eq]
    change ((MulAut.conj a) * (MulAut.conj (a * b))) y = (MulAut.conj b) y
    rw [ha_ab]
  change (MulAut.conj a) Z.x = Z.x⁻¹
  rw [Z.hx, Z.hz]
  simp only [map_mul, map_inv, ha_y, ha_y2, ha_y3, ha_y4]
  group

private theorem four_conj_cent {Q : Type*} [Group Q] {K : Subgroup Q} {a b y : Q}
    (Z : FourConjX K a b y) (hb2 : b * b = 1) (hab : a * b = b * a) :
    Commute b Z.x := by
  have hconj2b : (MulAut.conj b) * (MulAut.conj b) = 1 := by
    rw [← map_mul (MulAut.conj) b b, hb2, map_one (MulAut.conj)]
  have hb_y : (MulAut.conj b) y = Z.y3 := Z.h3eq.symm
  have hb_y3 : (MulAut.conj b) Z.y3 = y := by
    rw [Z.h3eq]
    change ((MulAut.conj b) * (MulAut.conj b)) y = y
    rw [hconj2b]
    rfl
  have hba_conj : (MulAut.conj b) * (MulAut.conj a) = MulAut.conj (a * b) := by
    rw [← map_mul (MulAut.conj) b a, ← hab]
  have hb_ab : (MulAut.conj b) * (MulAut.conj (a * b)) = MulAut.conj a := by
    rw [← map_mul (MulAut.conj) b (a * b), show b * (a * b) = a by
      calc b * (a * b) = b * (b * a) := by rw [hab]
        _ = (b * b) * a := by rw [mul_assoc]
        _ = a := by rw [hb2, one_mul]]
  have hb_y2 : (MulAut.conj b) Z.y2 = Z.y4 := by
    rw [Z.h2eq, Z.h4eq]
    change ((MulAut.conj b) * (MulAut.conj a)) y = (MulAut.conj (a * b)) y
    rw [hba_conj]
  have hb_y4 : (MulAut.conj b) Z.y4 = Z.y2 := by
    rw [Z.h4eq, Z.h2eq]
    change ((MulAut.conj b) * (MulAut.conj (a * b))) y = (MulAut.conj a) y
    rw [hb_ab]
  have hbconj : b * Z.x * b⁻¹ = Z.x := by
    change (MulAut.conj b) Z.x = Z.x
    rw [Z.hx, Z.hz]
    simp only [map_mul, map_inv, hb_y, hb_y2, hb_y3, hb_y4]
    rw [← Z.hy2y4.eq]
    calc Z.y3 * (y * (Z.y2 * Z.y4)⁻¹) = (Z.y3 * y) * (Z.y2 * Z.y4)⁻¹ := by group
      _ = (y * Z.y3) * (Z.y2 * Z.y4)⁻¹ := by rw [← Z.hyy3.eq]
      _ = y * (Z.y3 * (Z.y2 * Z.y4)⁻¹) := by group
  rw [commute_iff_eq]
  calc b * Z.x = (b * Z.x * b⁻¹) * b := by group
    _ = Z.x * b := by rw [hbconj]

private theorem comp_norm_case_four_apply {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (X : S2341Frame D Ch c) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h39 : S23_39 D Ch) (h40 : S23_40 D Ch)
    (h1930 : H1930 D) (hneq : ⁅X.W, X.F⁆ ≠ ⊥) {K : Subgroup G} (hK : K ∈ calC D.M)
    {v : D.M} (hvW : (v : G) ∈ X.W) (P : CompNormData X K v)
    (C : FourConjCase P.A P.W1 P.Kstar P.a) (h7 : X.NoOddInverted)
    {y : Bar2 D.M} (Z : FourConjX P.Kstar P.a C.b y) : False := by
  have hbA' : C.b ∈ (X.W.subgroupOf D.M).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) := by
    simpa [P.hA, imageOTwoQuot] using C.hbA
  obtain ⟨bM : ↥D.M, hbMW, hbMeq⟩ := Subgroup.mem_map.mp hbA'
  have hb1 : C.b ≠ 1 := fun h => C.hbNotW1 (h ▸ P.W1.one_mem)
  have hbMZh : (bM : G) ∉ X.Zh := by
    intro hz
    have h1 : (QuotientGroup.mk bM : Bar2 D.M) = 1 :=
      (Wstar_mk_eq_one_iff X h4 h23 h39 h40 h1930 hneq hbMW).mpr hz
    exact hb1 (hbMeq.symm.trans h1)
  have hvZh : (v : G) ∉ X.Zh := by
    intro hz
    have h1 : P.a = 1 := by
      rw [P.ha]
      exact (Wstar_mk_eq_one_iff X h4 h23 h39 h40 h1930 hneq hvW).mpr hz
    exact P.haW1 (h1 ▸ P.W1.one_mem)
  have hinv : (QuotientGroup.mk v) * Z.x * (QuotientGroup.mk v)⁻¹ = Z.x⁻¹ := by
    rw [← P.ha]
    exact four_conj_inv Z P.ha2 C.hb2 C.habc
  have hcent : Commute (QuotientGroup.mk bM) Z.x := by
    have hb : (QuotientGroup.mk bM : Bar2 D.M) = C.b := hbMeq
    rw [hb]
    exact four_conj_cent Z C.hb2 C.habc
  exact h7 Z.x Z.hx1 Z.hxodd v bM hvW hbMW hbMZh hinv hcent

private theorem comp_norm_case_four {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h39 : S23_39 D Ch) (h40 : S23_40 D Ch) (h1930 : H1930 D)
    (hneq : ⁅X.W, X.F⁆ ≠ ⊥) {K : Subgroup G} (hK : K ∈ calC D.M)
    {v : D.M} (hvW : (v : G) ∈ X.W) (P : CompNormData X K v)
    (hcase : ∃ b ∈ P.A, b ∉ P.W1 ⊔ Subgroup.zpowers P.a)
    (h7 : X.NoOddInverted) : False := by
  let C : FourConjCase P.A P.W1 P.Kstar P.a :=
    four_conj_case_data P.hE P.haA P.hW1 hcase
  let y : Bar2 D.M := Classical.choose
    (CFSG.QuasithinUnique.Fin253.exists_odd_orderOf_of_not_isPGroup P.hKnot2)
  have hy_spec := Classical.choose_spec
    (CFSG.QuasithinUnique.Fin253.exists_odd_orderOf_of_not_isPGroup P.hKnot2)
  have hyK : y ∈ P.Kstar := hy_spec.1
  have hy1 : y ≠ 1 := hy_spec.2.1
  have hyodd : Odd (orderOf y) := hy_spec.2.2
  let Y : FourConjData P.Kstar P.a C.b y :=
    four_conj_y P.hKcomp P.ha2 C.hb2 C.habc P.haN C.hbN C.habN hyK hyodd
  let Z : FourConjX P.Kstar P.a C.b y := four_conj_z Y P.hKcenter hyK hy1
  exact comp_norm_case_four_apply X h4 h23 h39 h40 h1930 hneq hK hvW P C h7 Z

private structure CompNormSupW {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) {K : Subgroup G} {v : D.M}
    (P : CompNormData X K v) where
  w : Bar2 D.M
  hwW1 : w ∈ P.W1
  hwA : w ∈ P.A
  hwN : w ∈ Subgroup.normalizer (P.Kstar : Set (Bar2 D.M))
  hw1 : w ≠ 1
  hw2 : w * w = 1
  wM : D.M
  hwMW : (wM : G) ∈ X.W
  hwMeq : (QuotientGroup.mk wM : Bar2 D.M) = w

private theorem comp_norm_case_sup_eq {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (X : S2341Frame D Ch c) {K : Subgroup G} {v : D.M}
    (P : CompNormData X K v) (hn3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hcase : ¬ ∃ b ∈ P.A, b ∉ P.W1 ⊔ Subgroup.zpowers P.a) :
    P.A = P.W1 ⊔ Subgroup.zpowers P.a ∧ P.W1 ≠ ⊥ := by
  have hAsup : P.A = P.W1 ⊔ Subgroup.zpowers P.a := by
    refine le_antisymm (fun x hx => ?_) ?_
    · push Not at hcase
      exact hcase x hx
    · rw [P.hW1]
      exact sup_le inf_le_left (Subgroup.zpowers_le.mpr P.haA)
  have hW1ne : P.W1 ≠ ⊥ := by
    intro hbot
    have hAle : P.A ≤ Subgroup.zpowers P.a := by rw [hAsup, hbot, bot_sup_eq]
    have hA8 : 8 ≤ Nat.card P.A := by
      rw [P.hAcard]
      exact (by norm_num : 8 ≤ 2 ^ 3).trans (pow_le_pow_right₀ (by norm_num) hn3)
    have hle2 : Nat.card P.A ≤ 2 := by
      calc Nat.card P.A ≤ Nat.card (Subgroup.zpowers P.a) := Subgroup.card_le_of_le hAle
        _ = orderOf P.a := Nat.card_zpowers P.a
        _ ≤ 2 := Nat.le_of_dvd (by norm_num)
          (orderOf_dvd_iff_pow_eq_one.mpr (by simpa [pow_two] using P.ha2))
    omega
  exact ⟨hAsup, hW1ne⟩

private noncomputable def comp_norm_case_sup_w {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (X : S2341Frame D Ch c) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h39 : S23_39 D Ch) (h40 : S23_40 D Ch)
    (h1930 : H1930 D) (hneq : ⁅X.W, X.F⁆ ≠ ⊥) {K : Subgroup G} {v : D.M}
    (hvW : (v : G) ∈ X.W) (P : CompNormData X K v) (hW1ne : P.W1 ≠ ⊥) :
    CompNormSupW X P := by
  have hnt : Nontrivial ↥P.W1 := (Subgroup.nontrivial_iff_ne_bot P.W1).mpr hW1ne
  let wstar : ↥P.W1 := Classical.choose (exists_ne (1 : ↥P.W1))
  have hwstar1 : wstar ≠ 1 := Classical.choose_spec (exists_ne (1 : ↥P.W1))
  let w : Bar2 D.M := (wstar : Bar2 D.M)
  have hwW1 : w ∈ P.W1 := wstar.2
  have hwW1' : w ∈ P.A ⊓ Subgroup.normalizer (P.Kstar : Set (Bar2 D.M)) := by
    simpa [P.hW1] using hwW1
  have hwA : w ∈ P.A := hwW1'.1
  have hwN : w ∈ Subgroup.normalizer (P.Kstar : Set (Bar2 D.M)) := hwW1'.2
  have hw1 : w ≠ 1 := fun h => hwstar1 (Subtype.ext h)
  have hw2 : w * w = 1 := by
    have h := P.hE.2 w hwA
    simpa [pow_two] using h
  have hwA' : w ∈ (X.W.subgroupOf D.M).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) := by
    simpa [P.hA, imageOTwoQuot] using hwA
  let wM : ↥D.M := Classical.choose (Subgroup.mem_map.mp hwA')
  have hwM_spec := Classical.choose_spec (Subgroup.mem_map.mp hwA')
  have hwMW : (wM : G) ∈ X.W := hwM_spec.1
  have hwMeq : (QuotientGroup.mk wM : Bar2 D.M) = w := hwM_spec.2
  exact ⟨w, hwW1, hwA, hwN, hw1, hw2, wM, hwMW, hwMeq⟩

private theorem comp_norm_sup_not_mem_Zh {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (X : S2341Frame D Ch c) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h39 : S23_39 D Ch) (h40 : S23_40 D Ch)
    (h1930 : H1930 D) (hneq : ⁅X.W, X.F⁆ ≠ ⊥) {K : Subgroup G} {v : D.M}
    (hvW : (v : G) ∈ X.W) {P : CompNormData X K v}
    (S : CompNormSupW X P) :
    (S.wM : G) ∉ X.Zh ∧ (v : G) ∉ X.Zh := by
  constructor
  · intro hz
    have h1 : (QuotientGroup.mk S.wM : Bar2 D.M) = 1 :=
      (Wstar_mk_eq_one_iff X h4 h23 h39 h40 h1930 hneq S.hwMW).mpr hz
    exact S.hw1 (S.hwMeq.symm.trans h1)
  · intro hz
    have h1 : P.a = 1 := by
      rw [P.ha]
      exact (Wstar_mk_eq_one_iff X h4 h23 h39 h40 h1930 hneq hvW).mpr hz
    exact P.haW1 (h1 ▸ P.W1.one_mem)

private structure SupCentY {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) {K : Subgroup G} {v : D.M}
    (P : CompNormData X K v) where
  y : Bar2 D.M
  y2 : Bar2 D.M
  hyK : y ∈ P.Kstar
  hy1 : y ≠ 1
  hyodd : Odd (orderOf y)
  hy2eq : y2 = (MulAut.conj P.a) y
  hy2 : y2 ∈ P.Kstar.map (MulAut.conj P.a).toMonoidHom
  hy2odd : Odd (orderOf y2)
  hyy2 : Commute y y2
  hK2comm : ∀ k ∈ P.Kstar, Commute k y2

private structure SupCentBasic {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) {K : Subgroup G} {v : D.M}
    (P : CompNormData X K v) extends SupCentY X P where
  x : Bar2 D.M
  hx : x = y * y2⁻¹
  hx1 : x ≠ 1
  hxodd : Odd (orderOf x)

private noncomputable def comp_norm_sup_cent_y {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (X : S2341Frame D Ch c) {K : Subgroup G} {v : D.M}
    (P : CompNormData X K v) : SupCentY X P := by
  have hK2 : CFSG.IsComponent (P.Kstar.map (MulAut.conj P.a).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj P.a) P.hKcomp
  let y : Bar2 D.M := Classical.choose
    (CFSG.QuasithinUnique.Fin253.exists_odd_orderOf_of_not_isPGroup P.hKnot2)
  have hy_spec := Classical.choose_spec
    (CFSG.QuasithinUnique.Fin253.exists_odd_orderOf_of_not_isPGroup P.hKnot2)
  have hyK : y ∈ P.Kstar := hy_spec.1
  have hy1 : y ≠ 1 := hy_spec.2.1
  have hyodd : Odd (orderOf y) := hy_spec.2.2
  let y2 : Bar2 D.M := (MulAut.conj P.a) y
  have hy2 : y2 ∈ P.Kstar.map (MulAut.conj P.a).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨y, hyK, rfl⟩
  have hy2odd : Odd (orderOf y2) := by
    change Odd (orderOf ((MulAut.conj P.a) y))
    rw [(MulAut.conj P.a).orderOf_eq y]
    exact hyodd
  have hne : P.Kstar ≠ P.Kstar.map (MulAut.conj P.a).toMonoidHom :=
    (map_conj_ne_of_not_mem_normalizer P.haN).symm
  have hcomm : ⁅P.Kstar, P.Kstar.map (MulAut.conj P.a).toMonoidHom⁆ = ⊥ :=
    CFSG.ComponentClassification.LocalComponents.commute_of_ne P.Kstar _
      ((CFSG.isComponent_iff_open _).mp P.hKcomp)
      ((CFSG.isComponent_iff_open _).mp hK2) hne
  exact SupCentY.mk y y2 hyK hy1 hyodd rfl hy2 hy2odd
    (CFSG.QuasithinUnique.BenderBranch.commute_of_commutator_eq_bot hcomm hyK hy2)
    (fun k hk =>
      CFSG.QuasithinUnique.BenderBranch.commute_of_commutator_eq_bot hcomm hk hy2)

private noncomputable def comp_norm_sup_cent_basic {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (X : S2341Frame D Ch c) {K : Subgroup G} {v : D.M}
    (P : CompNormData X K v) (Y : SupCentY X P) : SupCentBasic X P := by
  let z : Bar2 D.M := Y.y2⁻¹
  let x : Bar2 D.M := Y.y * z
  have hzcent : ∀ k ∈ P.Kstar, Commute z k := by
    intro k hk
    change Commute Y.y2⁻¹ k
    exact (Y.hK2comm k hk).symm.inv_left
  have hx1 : x ≠ 1 := by
    change Y.y * z ≠ 1
    exact mul_ne_one_of_center_eq_bot P.hKcenter Y.hyK Y.hy1 hzcent
  have hxodd : Odd (orderOf x) := by
    change Odd (orderOf (Y.y * Y.y2⁻¹))
    have hy2i : Odd (orderOf Y.y2⁻¹) := by
      rw [orderOf_inv]
      exact Y.hy2odd
    exact (Y.hyodd.mul hy2i).of_dvd_nat
      (Y.hyy2.inv_right.orderOf_mul_dvd_lcm.trans (Nat.lcm_dvd_mul _ _))
  exact SupCentBasic.mk Y x rfl hx1 hxodd

private theorem comp_norm_sup_cent_inv {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (X : S2341Frame D Ch c) {K : Subgroup G} {v : D.M}
    (P : CompNormData X K v) (B : SupCentBasic X P) :
    P.a * B.x * P.a⁻¹ = B.x⁻¹ := by
  have hconj2a : (MulAut.conj P.a) * (MulAut.conj P.a) = 1 := by
    rw [← map_mul (MulAut.conj) P.a P.a, P.ha2, map_one (MulAut.conj)]
  have ha_y : (MulAut.conj P.a) B.y = B.y2 := B.hy2eq.symm
  have ha_y2 : (MulAut.conj P.a) B.y2 = B.y := by
    rw [B.hy2eq]
    change ((MulAut.conj P.a) * (MulAut.conj P.a)) B.y = B.y
    rw [hconj2a]
    rfl
  change (MulAut.conj P.a) B.x = B.x⁻¹
  rw [B.hx]
  simp only [map_mul, map_inv, ha_y, ha_y2]
  group

private theorem comp_norm_sup_cent_comm {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (X : S2341Frame D Ch c) {K : Subgroup G} {v : D.M}
    (P : CompNormData X K v) (B : SupCentBasic X P) (S : CompNormSupW X P)
    (hwc : ∀ k ∈ P.Kstar, Commute S.w k) : Commute S.w B.x := by
  have hwaw : S.w * P.a = P.a * S.w :=
    congrArg (fun x : P.A => (x : Bar2 D.M))
      (P.hE.1.is_comm.comm ⟨S.w, S.hwA⟩ ⟨P.a, P.haA⟩)
  have hwc2 : (MulAut.conj S.w) B.y2 = B.y2 := by
    rw [B.hy2eq]
    change S.w * ((MulAut.conj P.a) B.y) * S.w⁻¹ = (MulAut.conj P.a) B.y
    rw [MulAut.conj_apply]
    have hwaw' : P.a⁻¹ * S.w⁻¹ = S.w⁻¹ * P.a⁻¹ := by
      have h := congrArg Inv.inv hwaw
      rwa [mul_inv_rev, mul_inv_rev] at h
    calc S.w * (P.a * B.y * P.a⁻¹) * S.w⁻¹ =
        (S.w * P.a) * B.y * (P.a⁻¹ * S.w⁻¹) := by group
      _ = (P.a * S.w) * B.y * (S.w⁻¹ * P.a⁻¹) := by rw [hwaw, hwaw']
      _ = P.a * (S.w * B.y * S.w⁻¹) * P.a⁻¹ := by group
      _ = P.a * B.y * P.a⁻¹ := by rw [(hwc B.y B.hyK).eq]; group
  have hwconj : S.w * B.x * S.w⁻¹ = B.x := by
    change (MulAut.conj S.w) B.x = B.x
    rw [B.hx]
    simp only [map_mul, map_inv, MulAut.conj_apply, hwc2, (hwc B.y B.hyK).eq]
    group
  rw [commute_iff_eq]
  calc S.w * B.x = (S.w * B.x * S.w⁻¹) * S.w := by group
    _ = B.x * S.w := by rw [hwconj]

private theorem comp_norm_sup_cent_finish {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (X : S2341Frame D Ch c) {K : Subgroup G} {v : D.M}
    (P : CompNormData X K v) (B : SupCentBasic X P) (S : CompNormSupW X P)
    (hvW : (v : G) ∈ X.W) (hnZ : (S.wM : G) ∉ X.Zh ∧ (v : G) ∉ X.Zh)
    (h7 : X.NoOddInverted) (hinv : P.a * B.x * P.a⁻¹ = B.x⁻¹)
    (hcent : Commute S.w B.x) : False := by
  have hinv' : (QuotientGroup.mk v) * B.x * (QuotientGroup.mk v)⁻¹ = B.x⁻¹ := by
    rw [← P.ha]
    exact hinv
  have hcent' : Commute (QuotientGroup.mk S.wM) B.x := by
    rw [S.hwMeq]
    exact hcent
  exact h7 B.x B.hx1 B.hxodd v S.wM hvW S.hwMW hnZ.1 hinv' hcent'

private structure SupNoncentY {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) {K : Subgroup G} {v : D.M}
    (P : CompNormData X K v) (S : CompNormSupW X P) where
  y : Bar2 D.M
  y2 : Bar2 D.M
  hyK : y ∈ P.Kstar
  hy1 : y ≠ 1
  hyodd : Odd (orderOf y)
  hy2eq : y2 = (MulAut.conj P.a) y
  hy2 : y2 ∈ P.Kstar.map (MulAut.conj P.a).toMonoidHom
  hy2odd : Odd (orderOf y2)
  hyy2 : Commute y y2
  hK2comm : ∀ k ∈ P.Kstar, Commute k y2
  hyinv : S.w * y * S.w⁻¹ = y⁻¹

private structure SupNoncentBasic {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) {K : Subgroup G} {v : D.M}
    (P : CompNormData X K v) (S : CompNormSupW X P) extends SupNoncentY X P S where
  x : Bar2 D.M
  hx : x = y * y2
  hx1 : x ≠ 1
  hxodd : Odd (orderOf x)
  hcent : Commute P.a x

private noncomputable def comp_norm_sup_noncent_y {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (X : S2341Frame D Ch c) {K : Subgroup G} {v : D.M}
    (P : CompNormData X K v) (S : CompNormSupW X P)
    (hwc : ¬ ∀ k ∈ P.Kstar, Commute S.w k) : SupNoncentY X P S := by
  push Not at hwc
  let k : Bar2 D.M := Classical.choose hwc
  have hk_spec := Classical.choose_spec hwc
  have hkK : k ∈ P.Kstar := hk_spec.1; have hkw : ¬ Commute S.w k := hk_spec.2
  have hwC : S.w ∉ Subgroup.centralizer (P.Kstar : Set (Bar2 D.M)) := by
    intro h
    exact hkw (Subgroup.mem_centralizer_iff.mp h k hkK).symm
  haveI : IsSimpleGroup ↥P.Kstar := P.hKsimple
  let y : Bar2 D.M := Classical.choose
    (CFSG.GroupTheory.inv_odd_of_simple (K := P.Kstar) P.hKnot2 S.hw2 S.hwN hwC)
  have hy_spec := Classical.choose_spec
    (CFSG.GroupTheory.inv_odd_of_simple (K := P.Kstar) P.hKnot2 S.hw2 S.hwN hwC)
  have hyK : y ∈ P.Kstar := hy_spec.1
  have hy1 : y ≠ 1 := hy_spec.2.1
  have hyodd : Odd (orderOf y) := hy_spec.2.2.1
  have hyinv : S.w * y * S.w⁻¹ = y⁻¹ := hy_spec.2.2.2
  have hK2 := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj P.a) P.hKcomp
  let y2 : Bar2 D.M := (MulAut.conj P.a) y
  have hy2 : y2 ∈ P.Kstar.map (MulAut.conj P.a).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨y, hyK, rfl⟩
  have hy2odd : Odd (orderOf y2) := by
    simpa [y2] using (show Odd (orderOf ((MulAut.conj P.a) y)) by
      rwa [(MulAut.conj P.a).orderOf_eq y])
  have hne := (map_conj_ne_of_not_mem_normalizer P.haN).symm
  have hcomm : ⁅P.Kstar, P.Kstar.map (MulAut.conj P.a).toMonoidHom⁆ = ⊥ :=
    CFSG.ComponentClassification.LocalComponents.commute_of_ne P.Kstar _
      ((CFSG.isComponent_iff_open _).mp P.hKcomp)
      ((CFSG.isComponent_iff_open _).mp hK2) hne
  exact SupNoncentY.mk y y2 hyK hy1 hyodd rfl hy2 hy2odd
    (CFSG.QuasithinUnique.BenderBranch.commute_of_commutator_eq_bot hcomm hyK hy2)
    (fun k hk =>
      CFSG.QuasithinUnique.BenderBranch.commute_of_commutator_eq_bot hcomm hk hy2)
    hyinv

private noncomputable def comp_norm_sup_noncent_basic {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (X : S2341Frame D Ch c) {K : Subgroup G} {v : D.M}
    (P : CompNormData X K v) (S : CompNormSupW X P) (Y : SupNoncentY X P S) :
    SupNoncentBasic X P S := by
  let x : Bar2 D.M := Y.y * Y.y2
  have hx1 : x ≠ 1 := by
    change Y.y * Y.y2 ≠ 1
    exact mul_ne_one_of_center_eq_bot P.hKcenter Y.hyK Y.hy1
      (fun k hk => (Y.hK2comm k hk).symm)
  have hxodd : Odd (orderOf x) := by
    change Odd (orderOf (Y.y * Y.y2))
    exact (Y.hyodd.mul Y.hy2odd).of_dvd_nat
      (Y.hyy2.orderOf_mul_dvd_lcm.trans (Nat.lcm_dvd_mul _ _))
  have hconj2a : (MulAut.conj P.a) * (MulAut.conj P.a) = 1 := by
    rw [← map_mul (MulAut.conj) P.a P.a, P.ha2, map_one (MulAut.conj)]
  have ha_y : (MulAut.conj P.a) Y.y = Y.y2 := Y.hy2eq.symm
  have ha_y2 : (MulAut.conj P.a) Y.y2 = Y.y := by
    rw [Y.hy2eq]
    change ((MulAut.conj P.a) * (MulAut.conj P.a)) Y.y = Y.y
    rw [hconj2a]
    rfl
  have hac : P.a * x * P.a⁻¹ = x := by
    change (MulAut.conj P.a) x = x
    rw [show x = Y.y * Y.y2 from rfl]
    simp only [map_mul, ha_y, ha_y2]
    exact Y.hyy2.eq.symm
  have hcent : Commute P.a x := by
    rw [commute_iff_eq]
    calc P.a * x = (P.a * x * P.a⁻¹) * P.a := by group
      _ = x * P.a := by rw [hac]
  exact SupNoncentBasic.mk Y x rfl hx1 hxodd hcent

private theorem comp_norm_sup_noncent_inv {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (X : S2341Frame D Ch c) {K : Subgroup G} {v : D.M}
    (P : CompNormData X K v) (S : CompNormSupW X P) (B : SupNoncentBasic X P S) :
    S.w * B.x * S.w⁻¹ = B.x⁻¹ := by
  have hwaw : S.w * P.a = P.a * S.w :=
    congrArg (fun x : P.A => (x : Bar2 D.M))
      (P.hE.1.is_comm.comm ⟨S.w, S.hwA⟩ ⟨P.a, P.haA⟩)
  have hwy2 : S.w * B.y2 * S.w⁻¹ = B.y2⁻¹ := by
    rw [B.hy2eq]
    change S.w * ((MulAut.conj P.a) B.y) * S.w⁻¹ = ((MulAut.conj P.a) B.y)⁻¹
    rw [MulAut.conj_apply]
    have hwaw' : P.a⁻¹ * S.w⁻¹ = S.w⁻¹ * P.a⁻¹ := by
      have h := congrArg Inv.inv hwaw
      rwa [mul_inv_rev, mul_inv_rev] at h
    calc S.w * (P.a * B.y * P.a⁻¹) * S.w⁻¹ =
        (S.w * P.a) * B.y * (P.a⁻¹ * S.w⁻¹) := by group
      _ = (P.a * S.w) * B.y * (S.w⁻¹ * P.a⁻¹) := by rw [hwaw, hwaw']
      _ = P.a * (S.w * B.y * S.w⁻¹) * P.a⁻¹ := by group
      _ = P.a * B.y⁻¹ * P.a⁻¹ := by rw [B.hyinv]
      _ = (P.a * B.y * P.a⁻¹)⁻¹ := by group
  change (MulAut.conj S.w) B.x = B.x⁻¹
  rw [B.hx]
  simp only [map_mul, MulAut.conj_apply, B.hyinv, hwy2]
  simpa only [mul_inv_rev] using (B.hyy2.inv_left.inv_right).eq

private theorem comp_norm_sup_noncent_finish {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (X : S2341Frame D Ch c) {K : Subgroup G} {v : D.M}
    (P : CompNormData X K v) (S : CompNormSupW X P) (B : SupNoncentBasic X P S)
    (hvW : (v : G) ∈ X.W) (hnZ : (S.wM : G) ∉ X.Zh ∧ (v : G) ∉ X.Zh)
    (h7 : X.NoOddInverted) (hinv : S.w * B.x * S.w⁻¹ = B.x⁻¹) : False := by
  have hinv' : (QuotientGroup.mk S.wM) * B.x * (QuotientGroup.mk S.wM)⁻¹ = B.x⁻¹ := by
    rw [S.hwMeq]
    exact hinv
  have hcent' : Commute (QuotientGroup.mk v) B.x := by
    rw [← P.ha]
    exact B.hcent
  exact h7 B.x B.hx1 B.hxodd S.wM v S.hwMW hvW hnZ.2 hinv' hcent'

private theorem comp_norm_case_sup {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h39 : S23_39 D Ch) (h40 : S23_40 D Ch) (h1930 : H1930 D)
    (hneq : ⁅X.W, X.F⁆ ≠ ⊥) (hn3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    {K : Subgroup G} {v : D.M} (hvW : (v : G) ∈ X.W)
    (P : CompNormData X K v)
    (hcase : ¬ ∃ b ∈ P.A, b ∉ P.W1 ⊔ Subgroup.zpowers P.a)
    (h7 : X.NoOddInverted) : False := by
  obtain ⟨hAsup, hW1ne⟩ := comp_norm_case_sup_eq X P hn3 hcase
  let S : CompNormSupW X P :=
    comp_norm_case_sup_w X h4 h23 h39 h40 h1930 hneq hvW P hW1ne
  have hnZ := comp_norm_sup_not_mem_Zh X h4 h23 h39 h40 h1930 hneq hvW S
  by_cases hwc : ∀ k ∈ P.Kstar, Commute S.w k
  · let Y : SupCentY X P := comp_norm_sup_cent_y X P
    let B : SupCentBasic X P := comp_norm_sup_cent_basic X P Y
    exact comp_norm_sup_cent_finish X P B S hvW hnZ h7
      (comp_norm_sup_cent_inv X P B) (comp_norm_sup_cent_comm X P B S hwc)
  · let Y : SupNoncentY X P S := comp_norm_sup_noncent_y X P S hwc
    let B : SupNoncentBasic X P S := comp_norm_sup_noncent_basic X P S Y
    exact comp_norm_sup_noncent_finish X P S B hvW hnZ h7
      (comp_norm_sup_noncent_inv X P S B)

private theorem comp_norm {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h39 : S23_39 D Ch)
    (h40 : S23_40 D Ch) (h1930 : H1930 D) (hneq : ⁅X.W, X.F⁆ ≠ ⊥)
    (hn3 : 3 ≤ CFSG.Open.pRank 2 D.Z) (h37 : S23_37 D Ch) (h7 : X.NoOddInverted)
    {K : Subgroup G} (hK : K ∈ calC D.M) :
    ∀ v : D.M, (v : G) ∈ X.W →
      (QuotientGroup.mk v : Bar2 D.M) ∈
        Subgroup.normalizer (imageOTwoQuot D.M K : Set (Bar2 D.M)) := by
  intro v hvW
  by_contra hcon
  let P : CompNormData X K v :=
    comp_norm_data X h4 h23 h39 h40 h1930 hneq h37 hK hvW hcon
  by_cases hcase : ∃ b ∈ P.A, b ∉ P.W1 ⊔ Subgroup.zpowers P.a
  · exact comp_norm_case_four X h4 h23 h39 h40 h1930 hneq hK hvW P hcase h7
  · exact comp_norm_case_sup X h4 h23 h39 h40 h1930 hneq hn3 hvW P hcase h7

private theorem fittingSubgroup_odd {D : Data G} :
    Odd (Nat.card (CFSG.fittingSubgroup (Bar2 D.M))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LocalAnalysis.RankThreeUC.Section5.OddActorSylowFactorization.odd_of_pCore_bot
    (pCore_two_quot_eq_bot D.M) (CFSG.fittingSubgroup (Bar2 D.M))

private theorem fitting_exists_fixed_moved {Q : Type*} [Group Q] [Finite Q]
    {F A : Subgroup Q} [F.Normal] [MulDistribMulAction A F]
    (hnotfix : ∃ a : A, ∃ p : F, a • p ≠ p)
    (hgen : (⨆ (w : A) (_ : w ≠ 1), fixedPointSubgroup (Subgroup.zpowers w) F) = ⊤) :
    ∃ w : A, w ≠ 1 ∧ ∃ a : A, ∃ p : F,
      p ∈ fixedPointSubgroup (Subgroup.zpowers w) F ∧ a • p ≠ p := by
  by_contra h
  push Not at h
  have hfix : ∀ a : A, ∀ p : F, a • p = p := by
    intro a p
    have hle : (⨆ (w : A) (_ : w ≠ 1), fixedPointSubgroup (Subgroup.zpowers w) F) ≤
        fixedPointSubgroup (Subgroup.zpowers a) F := by
      refine iSup₂_le fun w hw => ?_
      intro x hx
      exact (CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff a x).mpr
        (h w hw a x hx)
    rw [hgen] at hle
    exact (CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff a p).mp
      (hle (Subgroup.mem_top p))
  obtain ⟨a, p, hap⟩ := hnotfix
  exact hap (hfix a p)

section FittingCentralizedAux

variable {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch} {X : S2341Frame D Ch c}

private theorem fitting_centralized_hnotfix (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h39 : S23_39 D Ch) (h40 : S23_40 D Ch) (h1930 : H1930 D)
    (hneq : ⁅X.W, X.F⁆ ≠ ⊥) (hn3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hnot : ⁅CFSG.fittingSubgroup (Bar2 D.M), imageOTwoQuot D.M X.W⁆ ≠ ⊥) :
    ∃ a : imageOTwoQuot D.M X.W, ∃ p : CFSG.fittingSubgroup (Bar2 D.M),
      a • p ≠ p := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : MulDistribMulAction (imageOTwoQuot D.M X.W) (CFSG.fittingSubgroup (Bar2 D.M)) :=
    MulDistribMulAction.compHom (CFSG.fittingSubgroup (Bar2 D.M))
      ((MulAut.conjNormal (H := CFSG.fittingSubgroup (Bar2 D.M))).comp
        (imageOTwoQuot D.M X.W).subtype)
  have hE := Wstar_isElemAbelian X h4 h1930
  have hA4 : 4 ≤ Nat.card (imageOTwoQuot D.M X.W) := by
    rw [Wstar_card X h4 h23 h39 h40 h1930 hneq]
    exact (by norm_num : 4 ≤ 2 ^ 3).trans (pow_le_pow_right₀ (by norm_num) hn3)
  haveI : CFSG.IsElementaryAbelian 2 ↥(imageOTwoQuot D.M X.W) :=
    (CFSG.Open.isElemAbelian_iff_isElementaryAbelian (p := 2)
      (E := imageOTwoQuot D.M X.W)).mp hE
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := 2)
    (A := imageOTwoQuot D.M X.W) (H := CFSG.fittingSubgroup (Bar2 D.M))
    (by simpa using hA4) (fun h =>
      (Nat.not_even_iff_odd.mpr (fittingSubgroup_odd (D := D))) (even_iff_two_dvd.mpr h))
  by_contra h
  push Not at h
  apply hnot
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro p hp
  rw [Subgroup.mem_centralizer_iff]; intro a ha
  have h' := congrArg (fun y : CFSG.fittingSubgroup (Bar2 D.M) => (y : Bar2 D.M))
    (h ⟨a, ha⟩ ⟨p, hp⟩)
  have ha' : (a : Bar2 D.M) * (p : Bar2 D.M) * (a : Bar2 D.M)⁻¹ = (p : Bar2 D.M) := by
    change (MulAut.conjNormal (a : Bar2 D.M))
      (⟨p, hp⟩ : CFSG.fittingSubgroup (Bar2 D.M)) = (p : Bar2 D.M) at h' ⊢
    simpa [MulAut.conjNormal_apply] using h'
  calc (a : Bar2 D.M) * (p : Bar2 D.M) =
      ((a : Bar2 D.M) * (p : Bar2 D.M) * (a : Bar2 D.M)⁻¹) * (a : Bar2 D.M) := by group
    _ = (p : Bar2 D.M) * (a : Bar2 D.M) := by rw [ha']

private theorem fitting_centralized_hex (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h39 : S23_39 D Ch) (h40 : S23_40 D Ch) (h1930 : H1930 D)
    (hneq : ⁅X.W, X.F⁆ ≠ ⊥) (hn3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hnot : ⁅CFSG.fittingSubgroup (Bar2 D.M), imageOTwoQuot D.M X.W⁆ ≠ ⊥) :
    ∃ w : imageOTwoQuot D.M X.W, w ≠ 1 ∧
      ∃ a : imageOTwoQuot D.M X.W, ∃ p : CFSG.fittingSubgroup (Bar2 D.M),
        (a : Bar2 D.M) * (p : Bar2 D.M) * (a : Bar2 D.M)⁻¹ ≠ (p : Bar2 D.M) ∧
        (w : Bar2 D.M) * (p : Bar2 D.M) * (w : Bar2 D.M)⁻¹ = (p : Bar2 D.M) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : MulDistribMulAction (imageOTwoQuot D.M X.W) (CFSG.fittingSubgroup (Bar2 D.M)) :=
    MulDistribMulAction.compHom (CFSG.fittingSubgroup (Bar2 D.M))
      ((MulAut.conjNormal (H := CFSG.fittingSubgroup (Bar2 D.M))).comp
        (imageOTwoQuot D.M X.W).subtype)
  have hA4 : 4 ≤ Nat.card (imageOTwoQuot D.M X.W) := by
    rw [Wstar_card X h4 h23 h39 h40 h1930 hneq]
    exact (by norm_num : 4 ≤ 2 ^ 3).trans (pow_le_pow_right₀ (by norm_num) hn3)
  haveI := (CFSG.Open.isElemAbelian_iff_isElementaryAbelian (p := 2)
    (E := imageOTwoQuot D.M X.W)).mp (Wstar_isElemAbelian X h4 h1930)
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := 2)
    (A := imageOTwoQuot D.M X.W) (H := CFSG.fittingSubgroup (Bar2 D.M))
    (by simpa using hA4) (fun h =>
      (Nat.not_even_iff_odd.mpr (fittingSubgroup_odd (D := D))) (even_iff_two_dvd.mpr h))
  obtain ⟨w, hw1, a, p, hpC, hap⟩ :=
    fitting_exists_fixed_moved (fitting_centralized_hnotfix h4 h23 h39 h40 h1930 hneq hn3 hnot)
      hgen
  have hwp := (CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff w p).mp hpC
  have hap' : (a : Bar2 D.M) * (p : Bar2 D.M) * (a : Bar2 D.M)⁻¹ ≠ (p : Bar2 D.M) := by
    intro h
    apply hap; change (MulAut.conjNormal (a : Bar2 D.M)) p = p
    exact Subtype.ext (by simpa [MulAut.conjNormal_apply] using h)
  have hwp' : (w : Bar2 D.M) * (p : Bar2 D.M) * (w : Bar2 D.M)⁻¹ = (p : Bar2 D.M) := by
    change (MulAut.conjNormal (w : Bar2 D.M)) p = p at hwp
    simpa [MulAut.conjNormal_apply] using
      congrArg (fun y : CFSG.fittingSubgroup (Bar2 D.M) => (y : Bar2 D.M)) hwp
  exact ⟨w, hw1, a, p, hap', hwp'⟩

end FittingCentralizedAux

private theorem fitting_centralized_x_basic {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (X : S2341Frame D Ch c)
    (hFodd : Odd (Nat.card (CFSG.fittingSubgroup (Bar2 D.M))))
    {a : imageOTwoQuot D.M X.W} {p : CFSG.fittingSubgroup (Bar2 D.M)}
    (ha2 : (a : Bar2 D.M) * (a : Bar2 D.M) = 1)
    (hap' : (a : Bar2 D.M) * (p : Bar2 D.M) * (a : Bar2 D.M)⁻¹ ≠ (p : Bar2 D.M)) :
    ∃ x : Bar2 D.M,
      x = (p : Bar2 D.M)⁻¹ * ((a : Bar2 D.M) * (p : Bar2 D.M) * (a : Bar2 D.M)⁻¹) ∧
        x ≠ 1 ∧ Odd (orderOf x) ∧ x ∈ CFSG.fittingSubgroup (Bar2 D.M) := by
  let x : Bar2 D.M := (p : Bar2 D.M)⁻¹ * ((a : Bar2 D.M) * (p : Bar2 D.M) * (a : Bar2 D.M)⁻¹)
  have hx1 : x ≠ 1 := by
    intro hx
    apply hap'
    have h := congrArg (fun y => (p : Bar2 D.M) * y) hx
    simpa [x, mul_assoc] using h
  haveI hFn : (CFSG.fittingSubgroup (Bar2 D.M)).Normal := CFSG.fittingSubgroup_normal
  have hxmem : x ∈ CFSG.fittingSubgroup (Bar2 D.M) := by
    have hconjF : (a : Bar2 D.M) * (p : Bar2 D.M) * (a : Bar2 D.M)⁻¹ ∈
        CFSG.fittingSubgroup (Bar2 D.M) :=
      hFn.conj_mem (p : Bar2 D.M) p.2 (a : Bar2 D.M)
    exact (CFSG.fittingSubgroup (Bar2 D.M)).mul_mem
      ((CFSG.fittingSubgroup (Bar2 D.M)).inv_mem p.2) hconjF
  have hxodd : Odd (orderOf x) :=
    Odd.of_dvd_nat hFodd
      (Subgroup.orderOf_dvd_natCard (CFSG.fittingSubgroup (Bar2 D.M)) hxmem)
  exact ⟨x, rfl, hx1, hxodd, hxmem⟩

private theorem fitting_centralized_x_inv {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (X : S2341Frame D Ch c) {a : imageOTwoQuot D.M X.W}
    {p : CFSG.fittingSubgroup (Bar2 D.M)} {aM : D.M}
    (haMeq : (QuotientGroup.mk aM : Bar2 D.M) = a)
    (ha2 : (a : Bar2 D.M) * (a : Bar2 D.M) = 1) {x : Bar2 D.M}
    (hxdef : x = (p : Bar2 D.M)⁻¹ *
      ((a : Bar2 D.M) * (p : Bar2 D.M) * (a : Bar2 D.M)⁻¹)) :
    (QuotientGroup.mk aM) * x * (QuotientGroup.mk aM)⁻¹ = x⁻¹ := by
  change (↑aM : Bar2 D.M) * x * (↑aM)⁻¹ = x⁻¹
  have haMco : (↑aM : Bar2 D.M) = (a : Bar2 D.M) := haMeq
  rw [haMco]
  have hainv : (a : Bar2 D.M)⁻¹ = (a : Bar2 D.M) := inv_eq_of_mul_eq_one_right ha2
  have hR : ((p : Bar2 D.M)⁻¹ * ((a : Bar2 D.M) * (p : Bar2 D.M) * (a : Bar2 D.M)))⁻¹ =
      (a : Bar2 D.M) * (p : Bar2 D.M)⁻¹ * (a : Bar2 D.M) * (p : Bar2 D.M) := by
    simp [hainv, mul_inv_rev]
    group
  rw [hxdef]
  calc (a : Bar2 D.M) *
      ((p : Bar2 D.M)⁻¹ * ((a : Bar2 D.M) * (p : Bar2 D.M) * (a : Bar2 D.M)⁻¹)) *
        (a : Bar2 D.M)⁻¹
      = ((a : Bar2 D.M) * (p : Bar2 D.M)⁻¹ * (a : Bar2 D.M) * (p : Bar2 D.M)) *
          ((a : Bar2 D.M) * (a : Bar2 D.M)) := by
        rw [hainv]
        group
    _ = (a : Bar2 D.M) * (p : Bar2 D.M)⁻¹ * (a : Bar2 D.M) * (p : Bar2 D.M) := by
      rw [ha2, mul_one]
    _ = ((p : Bar2 D.M)⁻¹ * ((a : Bar2 D.M) * (p : Bar2 D.M) * (a : Bar2 D.M)⁻¹))⁻¹ := by
      rw [hainv, hR]

private theorem fitting_centralized_x_comm {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (X : S2341Frame D Ch c)
    (hE : IsElemAbelian 2 (imageOTwoQuot D.M X.W))
    {w a : imageOTwoQuot D.M X.W} {p : CFSG.fittingSubgroup (Bar2 D.M)} {wM : D.M}
    (hwMeq : (QuotientGroup.mk wM : Bar2 D.M) = w)
    (hwp' : (w : Bar2 D.M) * (p : Bar2 D.M) * (w : Bar2 D.M)⁻¹ = (p : Bar2 D.M))
    {x : Bar2 D.M}
    (hxdef : x = (p : Bar2 D.M)⁻¹ *
      ((a : Bar2 D.M) * (p : Bar2 D.M) * (a : Bar2 D.M)⁻¹)) :
    Commute (QuotientGroup.mk wM) x := by
  change Commute (↑wM : Bar2 D.M) x
  have hwMco : (↑wM : Bar2 D.M) = (w : Bar2 D.M) := hwMeq
  rw [hwMco]
  have hcommA : (w : Bar2 D.M) * (a : Bar2 D.M) = (a : Bar2 D.M) * (w : Bar2 D.M) :=
    congrArg (fun y : imageOTwoQuot D.M X.W => (y : Bar2 D.M))
      (hE.1.is_comm.comm w a)
  have hcommp : (w : Bar2 D.M) * (p : Bar2 D.M) = (p : Bar2 D.M) * (w : Bar2 D.M) := by
    calc (w : Bar2 D.M) * (p : Bar2 D.M) =
        ((w : Bar2 D.M) * (p : Bar2 D.M) * (w : Bar2 D.M)⁻¹) * (w : Bar2 D.M) := by group
      _ = (p : Bar2 D.M) * (w : Bar2 D.M) := by rw [hwp']
  rw [hxdef]
  exact (show Commute (w : Bar2 D.M) (p : Bar2 D.M) from hcommp).inv_right.mul_right
    (((show Commute (w : Bar2 D.M) (a : Bar2 D.M) from hcommA).mul_right
      (show Commute (w : Bar2 D.M) (p : Bar2 D.M) from hcommp)).mul_right
        (show Commute (w : Bar2 D.M) (a : Bar2 D.M) from hcommA).inv_right)

private theorem fitting_centralized {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h39 : S23_39 D Ch)
    (h40 : S23_40 D Ch) (h1930 : H1930 D) (hneq : ⁅X.W, X.F⁆ ≠ ⊥)
    (hn3 : 3 ≤ CFSG.Open.pRank 2 D.Z) (h7 : X.NoOddInverted) :
    ⁅CFSG.fittingSubgroup (Bar2 D.M), imageOTwoQuot D.M X.W⁆ = ⊥ := by
  classical
  classical
  let Q := Bar2 D.M
  let F : Subgroup Q := CFSG.fittingSubgroup Q
  let A : Subgroup Q := imageOTwoQuot D.M X.W
  haveI hFn : F.Normal := CFSG.fittingSubgroup_normal
  letI : MulDistribMulAction A F :=
    MulDistribMulAction.compHom F ((MulAut.conjNormal (H := F)).comp A.subtype)
  by_contra hnot
  obtain ⟨w, hw1, a, p, hap', hwp'⟩ :=
    fitting_centralized_hex (X := X) h4 h23 h39 h40 h1930 hneq hn3 hnot
  have hE := Wstar_isElemAbelian X h4 h1930
  have hFodd : Odd (Nat.card F) := fittingSubgroup_odd
  obtain ⟨wM, hwMW, hwMeq⟩ := Subgroup.mem_map.mp w.2
  obtain ⟨aM, haMW, haMeq⟩ := Subgroup.mem_map.mp a.2
  have hwZh : (wM : G) ∉ X.Zh := by
    intro hz
    have h1 : (QuotientGroup.mk wM : Q) = 1 :=
      (Wstar_mk_eq_one_iff X h4 h23 h39 h40 h1930 hneq hwMW).mpr hz
    exact hw1 (Subtype.ext (hwMeq.symm.trans h1))
  have ha2 : (a : Q) * (a : Q) = 1 := by
    have h := hE.2 (a : Q) a.2
    simpa [pow_two] using h
  obtain ⟨x, hxdef, hx1, hxodd, hxmem⟩ :=
    fitting_centralized_x_basic X hFodd ha2 hap'
  have hinv := fitting_centralized_x_inv X haMeq ha2 hxdef
  have hcomm := fitting_centralized_x_comm X hE hwMeq hwp' hxdef
  exact h7 x hx1 hxodd aM wM haMW hwMW hwZh hinv hcomm

private theorem exists_faithful_comp_layer {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (X : S2341Frame D Ch c)
    (hcon : ∀ K ∈ calC D.M, ∀ w : D.M, (w : G) ∈ X.W →
      ∀ x : Bar2 D.M, x ∈ imageOTwoQuot D.M K →
        Commute (QuotientGroup.mk w) x) :
    imageOTwoQuot D.M X.W ≤
      Subgroup.centralizer (CFSG.layer (Bar2 D.M) : Set (Bar2 D.M)) := by
  have hcentcomp : ∀ C : Subgroup (Bar2 D.M), CFSG.IsComponent C →
      ∀ s ∈ imageOTwoQuot D.M X.W, ∀ k ∈ C, k * s = s * k := by
    intro C hC s hs k hk
    obtain ⟨K, hK, hKC⟩ := uc22p21c_exists_calC_of_component D.M hC
    have hs' : s ∈ (X.W.subgroupOf D.M).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) := by
      simpa [imageOTwoQuot] using hs
    obtain ⟨w : ↥D.M, hwW, hweq⟩ := Subgroup.mem_map.mp hs'
    have hx : k ∈ imageOTwoQuot D.M K := by
      have hkb : k ∈ barImage D.M K := hKC ▸ hk
      simpa [barImage, imageOTwoQuot] using hkb
    have hcw : Commute (QuotientGroup.mk w) k := hcon K hK w hwW k hx
    rw [← hweq]
    exact hcw.eq.symm
  exact CFSG.HardMathSupport.Meierfrankenfeld.AGL81.le_centralizer_layer_of_forall_component
    hcentcomp

private theorem exists_faithful_comp_false {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (X : S2341Frame D Ch c) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h39 : S23_39 D Ch) (h40 : S23_40 D Ch)
    (h1930 : H1930 D) (hneq : ⁅X.W, X.F⁆ ≠ ⊥)
    (hn3 : 3 ≤ CFSG.Open.pRank 2 D.Z) (h7 : X.NoOddInverted)
    (hcon : ∀ K ∈ calC D.M, ∀ w : D.M, (w : G) ∈ X.W →
      ∀ x : Bar2 D.M, x ∈ imageOTwoQuot D.M K →
        Commute (QuotientGroup.mk w) x) : False := by
  have hAle := exists_faithful_comp_layer X hcon
  have hFit : ⁅CFSG.fittingSubgroup (Bar2 D.M), imageOTwoQuot D.M X.W⁆ = ⊥ :=
    fitting_centralized X h4 h23 h39 h40 h1930 hneq hn3 h7
  have hFit' : ⁅imageOTwoQuot D.M X.W, CFSG.fittingSubgroup (Bar2 D.M)⁆ = ⊥ := by
    rwa [Subgroup.commutator_comm] at hFit
  have hAleF : imageOTwoQuot D.M X.W ≤
      Subgroup.centralizer (CFSG.fittingSubgroup (Bar2 D.M) : Set (Bar2 D.M)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hFit'
  have hAleFstar : imageOTwoQuot D.M X.W ≤
      Subgroup.centralizer (CFSG.generalizedFitting (Bar2 D.M) : Set (Bar2 D.M)) := by
    rw [CFSG.generalizedFitting.eq_sup, Subgroup.le_centralizer_iff]
    exact sup_le (Subgroup.le_centralizer_iff.mp hAleF)
      (Subgroup.le_centralizer_iff.mp hAle)
  have hAleFit : imageOTwoQuot D.M X.W ≤ CFSG.fittingSubgroup (Bar2 D.M) := fun x hx =>
    CFSG.Adapters.centralizer_generalizedFitting_le_fittingSubgroup (G := Bar2 D.M)
      (hAleFstar hx)
  have h2A : 2 ∣ Nat.card (imageOTwoQuot D.M X.W) := by
    rw [Wstar_card X h4 h23 h39 h40 h1930 hneq]
    exact dvd_pow_self 2 (by omega : CFSG.Open.pRank 2 D.Z ≠ 0)
  have h2F : 2 ∣ Nat.card (CFSG.fittingSubgroup (Bar2 D.M)) :=
    h2A.trans (Subgroup.card_dvd_of_le hAleFit)
  exact (Nat.not_even_iff_odd.mpr (fittingSubgroup_odd (D := D)))
    (even_iff_two_dvd.mpr h2F)

private theorem exists_faithful_comp {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h37 : S23_37 D Ch)
    (h39 : S23_39 D Ch) (h40 : S23_40 D Ch) (h1930 : H1930 D)
    (hneq : ⁅X.W, X.F⁆ ≠ ⊥) (hn3 : 3 ≤ CFSG.Open.pRank 2 D.Z) (h7 : X.NoOddInverted) :
    ∃ K ∈ calC D.M, ∃ w : D.M, (w : G) ∈ X.W ∧
      ¬ ∀ x : Bar2 D.M, x ∈ imageOTwoQuot D.M K →
        Commute (QuotientGroup.mk w) x := by
  classical
  by_contra hcon
  push Not at hcon
  exact exists_faithful_comp_false X h4 h23 h39 h40 h1930 hneq hn3 h7 hcon

private theorem autRankLe_imageOTwoQuot {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (h1930 : H1930 D) (h37 : S23_37 D Ch) {K : Subgroup G} (hK : K ∈ calC D.M) :
    CFSG.Quasithin.AutRankLe (imageOTwoQuot D.M K) 2 := by
  obtain ⟨q, hq, hq2, hL2⟩ := (h37 h1930 c K hK).1
  rw [IsL2Odd, CFSG.Blueprint.LieModel] at hL2
  rcases hL2 with ⟨-, hclass⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · rw [CFSG.Open.StatedClassicalModel] at hclass
    obtain ⟨Kf, hKf, hKfin, hcard, ⟨eK⟩⟩ := hclass.2
    letI : Field Kf := hKf
    letI : Finite Kf := hKfin
    let ePSL : Bar2 K ≃* CFSG.GorensteinWalter.PSL2 Kf :=
      eK.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj
        2 Kf).symm
    have hpsl : CFSG.Quasithin.AutRankLe (CFSG.GorensteinWalter.PSL2 Kf) 2 :=
      autRankLe_psl2_of_card_prime hq hq2 (by simpa using hcard)
    have hbar : CFSG.Quasithin.AutRankLe (Bar2 K) 2 :=
      CFSG.Quasithin.AutRankLe.of_mulEquiv ePSL hpsl
    obtain ⟨e1⟩ := uc22p22l_barImage_equiv hK
    exact CFSG.Quasithin.AutRankLe.of_mulEquiv e1.symm hbar
  · exact absurd h0 (by norm_num)
  · exact absurd h0 (by norm_num)
  · exact absurd h0 (by norm_num)

private structure NoOddBase {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) where
  K : Subgroup G
  hK : K ∈ calC D.M
  w : D.M
  hwW : (w : G) ∈ X.W
  hw_notcent : ¬ ∀ x : Bar2 D.M, x ∈ imageOTwoQuot D.M K →
    Commute (QuotientGroup.mk w) x
  hwZh : (w : G) ∉ X.Zh
  hN : ∀ v : D.M, (v : G) ∈ X.W → ∀ x : Bar2 D.M, x ∈ imageOTwoQuot D.M K →
    (QuotientGroup.mk v) * x * (QuotientGroup.mk v)⁻¹ ∈ imageOTwoQuot D.M K

private structure NoOddAction {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) extends NoOddBase X where
  hAleN : imageOTwoQuot D.M X.W ≤
    Subgroup.normalizer (imageOTwoQuot D.M K : Set (Bar2 D.M))
  iota : imageOTwoQuot D.M X.W →*
    Subgroup.normalizer (imageOTwoQuot D.M K : Set (Bar2 D.M))
  phi : imageOTwoQuot D.M X.W →* MulAut (imageOTwoQuot D.M K)
  phi_apply : ∀ (a : imageOTwoQuot D.M X.W) (x : Bar2 D.M)
    (hx : x ∈ imageOTwoQuot D.M K),
    ((phi a) ⟨x, hx⟩ : Bar2 D.M) = (a : Bar2 D.M) * x * (a : Bar2 D.M)⁻¹

private noncomputable def noOddInverted_base {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (X : S2341Frame D Ch c) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h37 : S23_37 D Ch) (h39 : S23_39 D Ch)
    (h40 : S23_40 D Ch) (h1930 : H1930 D) (hneq : ⁅X.W, X.F⁆ ≠ ⊥)
    (hn3 : 3 ≤ CFSG.Open.pRank 2 D.Z) (h7 : X.NoOddInverted) :
    NoOddBase X := by
  classical
  let K : Subgroup G := Classical.choose
    (exists_faithful_comp X h4 h23 h37 h39 h40 h1930 hneq hn3 h7)
  have hK_spec := Classical.choose_spec
    (exists_faithful_comp X h4 h23 h37 h39 h40 h1930 hneq hn3 h7)
  have hK : K ∈ calC D.M := hK_spec.1
  let w : D.M := Classical.choose hK_spec.2
  have hw_spec := Classical.choose_spec hK_spec.2
  have hwW : (w : G) ∈ X.W := hw_spec.1
  have hw_notcent := hw_spec.2
  have hwZh : (w : G) ∉ X.Zh := by
    intro hz
    apply hw_notcent
    intro x hx
    have h1 : (QuotientGroup.mk w : Bar2 D.M) = 1 :=
      (Wstar_mk_eq_one_iff X h4 h23 h39 h40 h1930 hneq hwW).mpr hz
    rw [h1]
    exact Commute.one_left x
  have hN : ∀ v : D.M, (v : G) ∈ X.W → ∀ x : Bar2 D.M,
      x ∈ imageOTwoQuot D.M K →
      (QuotientGroup.mk v) * x * (QuotientGroup.mk v)⁻¹ ∈ imageOTwoQuot D.M K := by
    intro v hvW x hx
    exact ((Subgroup.mem_normalizer_iff.mp
      (comp_norm X h4 h23 h39 h40 h1930 hneq hn3 h37 h7 hK v hvW)) x).mp hx
  exact NoOddBase.mk K hK w hwW hw_notcent hwZh hN

private noncomputable def noOddInverted_action {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (X : S2341Frame D Ch c) (B : NoOddBase X) : NoOddAction X := by
  have hAleN : imageOTwoQuot D.M X.W ≤
      Subgroup.normalizer (imageOTwoQuot D.M B.K : Set (Bar2 D.M)) := by
    intro a ha
    have ha' : a ∈ (X.W.subgroupOf D.M).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) := by
      have haim : a ∈ imageOTwoQuot D.M X.W := ha
      simpa [imageOTwoQuot] using haim
    let v : ↥D.M := Classical.choose (Subgroup.mem_map.mp ha')
    have hv_spec := Classical.choose_spec (Subgroup.mem_map.mp ha')
    have hvW : (v : G) ∈ X.W := hv_spec.1
    have hveq : (QuotientGroup.mk v : Bar2 D.M) = a := hv_spec.2
    rw [← hveq]
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact B.hN v hvW x
    · intro hx
      have h := B.hN v⁻¹ (X.W.inv_mem hvW)
        ((QuotientGroup.mk v) * x * (QuotientGroup.mk v)⁻¹) hx
      simpa [map_inv, mul_assoc] using h
  let iota : imageOTwoQuot D.M X.W →*
      Subgroup.normalizer (imageOTwoQuot D.M B.K : Set (Bar2 D.M)) :=
    (imageOTwoQuot D.M X.W).subtype.codRestrict _ (fun a => hAleN a.2)
  let phi : imageOTwoQuot D.M X.W →* MulAut (imageOTwoQuot D.M B.K) :=
    (imageOTwoQuot D.M B.K).normalizerMonoidHom.comp iota
  have hphi_apply : ∀ (a : imageOTwoQuot D.M X.W) (x : Bar2 D.M)
      (hx : x ∈ imageOTwoQuot D.M B.K),
      ((phi a) ⟨x, hx⟩ : Bar2 D.M) = (a : Bar2 D.M) * x * (a : Bar2 D.M)⁻¹ := by
    intro a x hx
    simp [phi, iota, Subgroup.normalizerMonoidHom_apply_apply_coe]
  exact NoOddAction.mk B hAleN iota phi hphi_apply

private theorem noOddInverted_ker {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (X : S2341Frame D Ch c) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h37 : S23_37 D Ch) (h39 : S23_39 D Ch)
    (h40 : S23_40 D Ch) (h1930 : H1930 D) (hneq : ⁅X.W, X.F⁆ ≠ ⊥)
    (h7 : X.NoOddInverted) (S : NoOddAction X) :
    Function.Injective S.phi := by
  rw [injective_iff_map_eq_one]; intro a ha
  have hacent : ∀ x : Bar2 D.M, x ∈ imageOTwoQuot D.M S.K →
      Commute (a : Bar2 D.M) x := by
    intro x hx
    have h := congrArg (fun e : MulAut (imageOTwoQuot D.M S.K) =>
      (e ⟨x, hx⟩ : Bar2 D.M)) ha
    have h' : (a : Bar2 D.M) * x * (a : Bar2 D.M)⁻¹ = x := by
      rw [← S.phi_apply a x hx]
      simpa using h
    rw [Commute]
    calc (a : Bar2 D.M) * x =
        ((a : Bar2 D.M) * x * (a : Bar2 D.M)⁻¹) * (a : Bar2 D.M) := by group
      _ = x * (a : Bar2 D.M) := by rw [h']
  have haA : (a : Bar2 D.M) ∈ (X.W.subgroupOf D.M).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) := by
    simpa [imageOTwoQuot] using a.2
  obtain ⟨v : ↥D.M, hvW, hveq⟩ := Subgroup.mem_map.mp haA
  by_cases hvZh : (v : G) ∈ X.Zh
  · apply Subtype.ext
    have h1 : (QuotientGroup.mk v : Bar2 D.M) = 1 :=
      (Wstar_mk_eq_one_iff X h4 h23 h39 h40 h1930 hneq hvW).mpr hvZh
    exact hveq.symm.trans h1
  · exfalso
    have hwc : ∀ x : Bar2 D.M, x ∈ imageOTwoQuot D.M S.K →
        Commute (QuotientGroup.mk v) x := by
      intro x hx
      change Commute ((QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) v) x
      rw [hveq]
      exact hacent x hx
    exact S.hw_notcent (comp_cent X h4 h23 h39 h40 h1930 h37 S.hK S.hN hvW hvZh hwc
      h7 S.w S.hwW)

private theorem noOddInverted_rank {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (X : S2341Frame D Ch c) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h37 : S23_37 D Ch) (h39 : S23_39 D Ch)
    (h40 : S23_40 D Ch) (h1930 : H1930 D) (hneq : ⁅X.W, X.F⁆ ≠ ⊥)
    (hn3 : 3 ≤ CFSG.Open.pRank 2 D.Z) (S : NoOddAction X)
    (hinj : Function.Injective S.phi) : False := by
  have hE := Wstar_isElemAbelian X h4 h1930
  have hEab : CFSG.Quasithin.IsElemAb2 (imageOTwoQuot D.M X.W) := by
    refine ⟨?_, ?_⟩
    · intro a ha b hb
      exact congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    · intro a ha
      exact hE.2 a ha
  have hAcard := Wstar_card X h4 h23 h39 h40 h1930 hneq
  have hrank : CFSG.Quasithin.rk (imageOTwoQuot D.M X.W) ≤ 2 := by
    have htop : CFSG.Quasithin.IsElemAb2 (⊤ : Subgroup (imageOTwoQuot D.M X.W)) := by
      refine ⟨?_, ?_⟩
      · intro a _ b _
        exact Subtype.ext (hEab.1 a.1 a.2 b.1 b.2)
      · intro a _
        exact Subtype.ext (hEab.2 a.1 a.2)
    have hle := autRankLe_imageOTwoQuot (c := c) h1930 h37 S.hK
      ((⊤ : Subgroup (imageOTwoQuot D.M X.W)).map S.phi) (htop.map S.phi)
    rw [CFSG.Quasithin.rk_map_eq_of_injective S.phi hinj] at hle
    rw [CFSG.Quasithin.rk_top (G := imageOTwoQuot D.M X.W)] at hle
    exact hle
  have hcardrank : Nat.card (imageOTwoQuot D.M X.W) =
      2 ^ CFSG.Quasithin.rk (imageOTwoQuot D.M X.W) := hEab.card_eq_two_pow
  have hrk : CFSG.Quasithin.rk (imageOTwoQuot D.M X.W) = CFSG.Open.pRank 2 D.Z := by
    apply Nat.pow_right_injective (by norm_num : 2 ≤ 2)
    change 2 ^ CFSG.Quasithin.rk (imageOTwoQuot D.M X.W) =
      2 ^ CFSG.Open.pRank 2 D.Z
    rw [← hcardrank, hAcard]
  omega

theorem false_of_noOddInverted {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h37 : S23_37 D Ch)
    (h39 : S23_39 D Ch) (h40 : S23_40 D Ch) (h1930 : H1930 D)
    (hneq : ⁅X.W, X.F⁆ ≠ ⊥) (hn3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (h7 : X.NoOddInverted) : False := by
  let B : NoOddBase X :=
    noOddInverted_base X h4 h23 h37 h39 h40 h1930 hneq hn3 h7
  let S : NoOddAction X := noOddInverted_action X B
  exact noOddInverted_rank X h4 h23 h37 h39 h40 h1930 hneq hn3 S
    (noOddInverted_ker X h4 h23 h37 h39 h40 h1930 hneq h7 S)

end Ctx23L.S2341Frame

end CFSG.LocalAnalysis.UniquenessCase.UC22

module

public import CFSG.RankThree.PartTwo.Sec21.Item2119End4ProofTools
public import CFSG.RankThree.PartTwo.Sec21.Item2119EndProof2125
import CFSG.RankThree.PartTwo.Sec21.Item2119End3Proof2125Unique
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec14.Item14J2
public import CFSG.RankThree.PartTwo.Sec21.Item2119End4ProofKF
public import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)

structure Gen2125 (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G)
    (d : G) (U₀ : Subgroup G) (a : G) (X : Subgroup G) (e : G) (Y : Subgroup G) : Prop where
  cfg : Config2119End G A E U c L d U₀ a X
  concl23 : Concl2123 L X c d
  concl24 : Concl2124 A L X d
  mem_e : e ∈ A
  not_mem_cd : e ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d
  not_mem_ad : e ∉ Subgroup.zpowers a ⊔ Subgroup.zpowers d
  not_mem_ac : e ∉ Subgroup.zpowers a ⊔ Subgroup.zpowers c
  type_L : Sec4.InducesTypeOn L e 2
  type_X : Sec4.InducesTypeOn X e 2
  iso : ∃ n : ℕ, 0 < n ∧ Even n ∧ Nonempty (lBar L ≃* projSL 3 (GaloisField 2 n)) ∧
    Nonempty (lBar (Sec11.sec11K L e) ≃* projSL 2 (GaloisField 2 n))
  mem_Y : Y ∈ thetaComponentsAt 3 e
  le_I : Sec11.sec11K L e ≤ Y
  le_J : Sec11.sec11K X e ≤ Y
  cent : A ⊓ Sec4.thetaQuotCentralizer Y = Subgroup.zpowers e
  inf_I : A ⊓ Sec11.sec11K L e = Subgroup.zpowers d
  mem_lStar : Y ∈ lStar A

namespace Item2119End4Proof

open Item2119EndProof Item2119End3Proof

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_eq_of_mem_sup {g x y : G} (hx : g * x * g⁻¹ = x) (hy : g * y * g⁻¹ = y) {z : G}
    (hz : z ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y) : g * z * g⁻¹ = z := by
  have hxC : x ∈ Subgroup.centralizer ({g} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * g = g * x * g⁻¹ * g := by rw [hx]
      _ = g * x := by group
  have hyC : y ∈ Subgroup.centralizer ({g} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc y * g = g * y * g⁻¹ * g := by rw [hy]
      _ = g * y := by group
  have hle : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤ Subgroup.centralizer ({g} : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hxC) (Subgroup.zpowers_le.mpr hyC)
  have h := Subgroup.mem_centralizer_singleton_iff.mp (hle hz)
  rw [← h]
  group

theorem not_mem_sup_swap {x y z : G} (hxy : x * y = y * x) (hxz : x * z = z * x)
    (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hz3 : z ^ 3 = 1) (hx1 : x ≠ 1)
    (hy : y ∉ Subgroup.zpowers x) (hz : z ∉ Subgroup.zpowers x ⊔ Subgroup.zpowers y) :
    y ∉ Subgroup.zpowers x ⊔ Subgroup.zpowers z := by
  intro h
  have hzx : z ∉ Subgroup.zpowers x := fun h' => hz (Subgroup.mem_sup_left h')
  have h9y := Item21LateProof.card_zpowers_sup_zpowers hxy hx3 hy3 hx1 hy
  have h9z := Item21LateProof.card_zpowers_sup_zpowers hxz hx3 hz3 hx1 hzx
  have hle : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤ Subgroup.zpowers x ⊔ Subgroup.zpowers z :=
    sup_le le_sup_left (Subgroup.zpowers_le.mpr h)
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [h9y, h9z])
  apply hz
  rw [heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)

theorem not_mem_zpowers_symm {x y : G} (hx3 : x ^ 3 = 1) (hy1 : y ≠ 1)
    (hxy : x ∉ Subgroup.zpowers y) : y ∉ Subgroup.zpowers x := fun h =>
  hxy (Item21Late2Proof.mem_zpowers_of_mem hx3 h hy1 (Subgroup.mem_zpowers x))

theorem exists_gen2125
    (h211 : Item211) (h2116 : Item2116) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (h66 : Sec6.Item6_6) {A E U L U₀ X : Subgroup G} {c d a : G}
    (hE : Config2119End G A E U c L d U₀ a X) (h23 : Concl2123 L X c d)
    (h24 : Concl2124 A L X d) {e : G} (he : e ∈ A)
    (hecd : e ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d)
    (head : e ∉ Subgroup.zpowers a ⊔ Subgroup.zpowers d)
    (heac : e ∉ Subgroup.zpowers a ⊔ Subgroup.zpowers c) :
    ∃ Y : Subgroup G, Gen2125 G A E U c L d U₀ a X e Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h23' := h23
  obtain ⟨⟨eXL⟩, hdX, hdTX, -⟩ := h23
  have hcfg := hE.cfg
  have hpair := hcfg.pair
  obtain ⟨n, hn0, hne, ⟨eL⟩⟩ := hcfg.lthree
  have hpair' : Sec21Pair G A E U₀ a X :=
    { toSec21Std := hpair.toSec21Std
      mem_E := hpair.mem_E
      mem_U := hE.mem_U₀.1
      mem_pair := hE.mem_pair }
  obtain ⟨hn', he', hC', h27', hS3'⟩ :=
    Item21LateProof.case7_of_lBar_L3 h211 h2116 hpair' (eXL.trans eL)
  have hcfgX : Config2119 G A E U₀ a X :=
    ⟨hpair', ⟨n, hn', he', ⟨eXL.trans eL⟩⟩, hC', h27', hS3'⟩
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hpairs' := mem_lThreeStarPairs_iff.mp hE.mem_pair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h3 : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have h27 : Nat.card A = 27 := by rw [hcfg.card]; norm_num
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have haA : a ∈ A := hpair.mem_E.2 hpairs'.1.1
  have hc1 : c ≠ 1 := hpairs.2.1
  have ha1 : a ≠ 1 := hpairs'.2.1
  have hdA : d ∈ A := hE.mem_d.1
  have hdL : d ∈ L := hE.mem_d.2
  have hd1 := hE.ne_one_d
  have hd3 : d ^ 3 = 1 := h3 d hdA
  have he3 : e ^ 3 = 1 := h3 e he
  have hed : e ∉ Subgroup.zpowers d := fun h => hecd (Subgroup.mem_sup_right h)
  have he1 : e ≠ 1 := fun h => hed (h ▸ Subgroup.one_mem _)
  have hLc : L ∈ thetaComponentsAt 3 c := lZeroStarAt_subset A c hpairs.2.2.1
  have hXa : X ∈ thetaComponentsAt 3 a := lZeroStarAt_subset A a hpairs'.2.2.1
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  have hXC : X ≤ Subgroup.centralizer ({a} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hXa
  have hcL : c ∉ L := (Item21Late2Proof.frame_of h45 h66 hcfg).1
  have hcd : c ∉ Subgroup.zpowers d := fun h => hcL ((Subgroup.zpowers_le.mpr hdL) h)
  have haCD : a ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d := not_mem_sup_of_config2119End hE
  have had : a ∉ Subgroup.zpowers d := fun h => haCD (Subgroup.mem_sup_right h)
  have hac : a ∉ Subgroup.zpowers c := fun h => haCD (Subgroup.mem_sup_left h)
  have hdc : d ∉ Subgroup.zpowers c := not_mem_zpowers_symm (h3 c hcA) hd1 hcd
  have hda : d ∉ Subgroup.zpowers a := not_mem_zpowers_symm (h3 a haA) hd1 had
  have hec : e ∉ Subgroup.zpowers c := fun h => hecd (Subgroup.mem_sup_left h)
  have hea : e ∉ Subgroup.zpowers a := fun h => head (Subgroup.mem_sup_left h)
  have hce : c ∉ Subgroup.zpowers e := not_mem_zpowers_symm he3 hc1 hec
  have hae : a ∉ Subgroup.zpowers e := not_mem_zpowers_symm he3 ha1 hea
  have hcED : c ∉ Subgroup.zpowers e ⊔ Subgroup.zpowers d := by
    rw [sup_comm]
    exact not_mem_sup_swap (hcomm d hdA c hcA) (hcomm d hdA e he) hd3 (h3 c hcA) he3 hd1 hcd
      (by rw [sup_comm]; exact hecd)
  have haED : a ∉ Subgroup.zpowers e ⊔ Subgroup.zpowers d := by
    rw [sup_comm]
    exact not_mem_sup_swap (hcomm d hdA a haA) (hcomm d hdA e he) hd3 (h3 a haA) he3 hd1 had
      (by rw [sup_comm]; exact head)
  have hdCE : d ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers e :=
    not_mem_sup_swap (hcomm c hcA d hdA) (hcomm c hcA e he) (h3 c hcA) hd3 he3 hc1 hdc hecd
  have hdAE : d ∉ Subgroup.zpowers a ⊔ Subgroup.zpowers e :=
    not_mem_sup_swap (hcomm a haA d hdA) (hcomm a haA e he) (h3 a haA) hd3 he3 ha1 hda head
  have haCE : a ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers e :=
    not_mem_sup_swap (hcomm c hcA a haA) (hcomm c hcA e he) (h3 c hcA) (h3 a haA) he3 hc1 hac
      (by rw [sup_comm]; exact heac)
  have h9ce : Nat.card (Subgroup.zpowers c ⊔ Subgroup.zpowers e : Subgroup G) = 9 :=
    Item21LateProof.card_zpowers_sup_zpowers (hcomm c hcA e he) (h3 c hcA) he3 hc1 hec
  have h9ae : Nat.card (Subgroup.zpowers a ⊔ Subgroup.zpowers e : Subgroup G) = 9 :=
    Item21LateProof.card_zpowers_sup_zpowers (hcomm a haA e he) (h3 a haA) he3 ha1 hea
  have heTL : Sec4.InducesTypeOn L e 2 :=
    inducesTypeOn_two_gen h45 h66 he he1 hdA hd1 hed hcfg hdL hE.type_d hcED
  have heTX : Sec4.InducesTypeOn X e 2 :=
    inducesTypeOn_two_gen h45 h66 he he1 hdA hd1 hed hcfgX hdX hdTX haED
  obtain ⟨hdI, hIq, -⟩ :=
    kf2123TypeTwo G L n hn0 hne ⟨eL⟩ e he3 heTL d hdL hd3 hE.type_d (hcomm e he d hdA)
  obtain ⟨-, ⟨eI⟩⟩ :=
    kf2123TypeTwoSL L n hn0 hne ⟨eL⟩ e he3 heTL d hdL hd3 hE.type_d (hcomm e he d hdA)
  obtain ⟨hdJ, hJq, -⟩ :=
    kf2123TypeTwo G X n hn0 hne ⟨eXL.trans eL⟩ e he3 heTX d hdX hd3 hdTX (hcomm e he d hdA)
  have hZI := center_lBar_eq_bot_of_typeTwo hn0 hne ⟨eL⟩ he3 heTL hdL hd3 hE.type_d
    (hcomm e he d hdA)
  have hZJ := center_lBar_eq_bot_of_typeTwo hn0 hne ⟨eXL.trans eL⟩ he3 heTX hdX hd3 hdTX
    (hcomm e he d hdA)
  have hG4 := hpair.standing.toTheoremFourHyp
  have hC4 := hG4.sectionFourHyp (Sec6.centralizer_ne_top_of_ne_one hG4 he1)
  have hE27 : Late.IsE27 A := ⟨hAe, h27⟩
  obtain ⟨Y, hY, hIY⟩ :=
    Sec14.exists_mem_thetaComponentsAt_le_residual h48 hC4 hE27 hcA he hc1 hLc hIq
  obtain ⟨Y', hY', hJY'⟩ :=
    Sec14.exists_mem_thetaComponentsAt_le_residual h48 hC4 hE27 haA he ha1 hXa hJq
  have hYY' : Y = Y' := eq_of_mem_thetaComponentsAt_of_mem hY hY' hJY' hZJ hdJ (hIY hdI) hd3 hd1
  subst hYY'
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG4 hAe he he1 Y hY
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG4 hAe hcA hc1 L hLc
  have hAX : A ≤ Subgroup.normalizer (X : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG4 hAe haA ha1 X hXa
  have hAres : ∀ {W : Subgroup G}, A ≤ Subgroup.normalizer (W : Set G) →
      A ≤ Subgroup.normalizer
        (inSubgroup perfectResidual (W ⊓ Subgroup.centralizer ({e} : Set G)) : Set G) := by
    intro W hAW x hx
    have h1 : x ∈ Subgroup.normalizer
        ((W ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hAW hx, Subgroup.le_normalizer
        (Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hx e he))⟩
    exact GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual _ h1
  have hAI := hAres hAL
  have hAJ := hAres hAX
  have hIc : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({e} : Set G)) ≤
      Subgroup.centralizer ({c} : Set G) :=
    ((Subgroup.map_subtype_le _).trans inf_le_left).trans hLC
  have hIe : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({e} : Set G)) ≤
      Subgroup.centralizer ({e} : Set G) := (Subgroup.map_subtype_le _).trans inf_le_right
  have hJa : inSubgroup perfectResidual (X ⊓ Subgroup.centralizer ({e} : Set G)) ≤
      Subgroup.centralizer ({a} : Set G) :=
    ((Subgroup.map_subtype_le _).trans inf_le_left).trans hXC
  have hJe : inSubgroup perfectResidual (X ⊓ Subgroup.centralizer ({e} : Set G)) ≤
      Subgroup.centralizer ({e} : Set G) := (Subgroup.map_subtype_le _).trans inf_le_right
  have hCA : A ⊓ Sec4.thetaQuotCentralizer Y = Subgroup.zpowers e := by
    apply le_antisymm
    · rintro x ⟨hxA, hxY⟩
      have hxI := mem_thetaQuotCentralizer_of_le' hIY hxY (hAI hxA)
      have hxJ := mem_thetaQuotCentralizer_of_le' hJY' hxY (hAJ hxA)
      have h1 := mem_sup_of_mem_thetaQuotCentralizer hcomm h3 h27 hcA he hdA hdI hZI hIc hIe
        h9ce hdCE hxA hxI
      have h2 := mem_sup_of_mem_thetaQuotCentralizer hcomm h3 h27 haA he hdA hdJ hZJ hJa hJe
        h9ae hdAE hxA hxJ
      exact mem_zpowers_of_mem_sup_of_mem_sup (hcomm c hcA e he) (hcomm a haA e he) (h3 c hcA)
        (h3 a haA) he3 he1 hce hae haCE h1 h2
    · rw [Subgroup.zpowers_le]
      exact ⟨he, Item2119End3Proof.mem_thetaQuotCentralizer_of_mem_thetaComponentsAt hY⟩
  have hAI' : A ⊓ inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({e} : Set G)) =
      Subgroup.zpowers d :=
    inf_eq_zpowers_of_center_eq_bot hcomm h3 h27 hcA he hdA hdI hZI hIc hIe h9ce hdCE
  have hYs : Y ∈ lStar A := Sec6.mem_lStar_of_inf_le_zpowers hAe he he1 hY hAY (le_of_eq hCA)
  exact ⟨Y, ⟨hE, h23', h24, he, hecd, head, heac, heTL, heTX, ⟨n, hn0, hne, ⟨eL⟩, ⟨eI⟩⟩, hY, hIY,
    hJY', hCA, hAI', hYs⟩⟩

theorem exists_onPlane_of_offPlane (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6)
    {A E U L U₀ X : Subgroup G} {c d a : G} (hE : Config2119End G A E U c L d U₀ a X)
    (hoff : ∀ e' ∈ A, e' ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d →
      e' ∉ Subgroup.zpowers a ⊔ Subgroup.zpowers d →
      e' ∉ Subgroup.zpowers a ⊔ Subgroup.zpowers c →
      ∃ Le ∈ thetaComponentsAt 3 e', 3 ∣ Nat.card Le ∧ Nonempty (lBar Le ≃* lBar L) ∧
        d ∈ Le ∧ Sec4.InducesTypeOn Le d 1 ∧ Sec4.InducesTypeOn Le c 2)
    {e : G} (he : e ∈ A) (hecd : e ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d)
    (head : e ∉ Subgroup.zpowers a ⊔ Subgroup.zpowers d)
    (heac : e ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers c) :
    ∃ Le ∈ thetaComponentsAt 3 e, 3 ∣ Nat.card Le ∧ Nonempty (lBar Le ≃* lBar L) ∧
      d ∈ Le ∧ Sec4.InducesTypeOn Le d 1 ∧ Sec4.InducesTypeOn Le c 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcfg := hE.cfg
  have hpair := hcfg.pair
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hpairs' := mem_lThreeStarPairs_iff.mp hE.mem_pair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h3 : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have h27 : Nat.card A = 27 := by rw [hcfg.card]; norm_num
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have haA : a ∈ A := hpair.mem_E.2 hpairs'.1.1
  have hc1 : c ≠ 1 := hpairs.2.1
  have hdA : d ∈ A := hE.mem_d.1
  have hdL : d ∈ L := hE.mem_d.2
  have hd1 := hE.ne_one_d
  have hd3 : d ^ 3 = 1 := h3 d hdA
  have hec : e ∉ Subgroup.zpowers c := fun h => hecd (Subgroup.mem_sup_left h)
  have hLc : L ∈ thetaComponentsAt 3 c := lZeroStarAt_subset A c hpairs.2.2.1
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  obtain ⟨hcL, d₀, -, -, -, hTU, -, -, -, ⟨w, ⟨hwL, hwN⟩, -, hwd₀, hwA, hwmove⟩, -⟩ :=
    Item21Late2Proof.frame_of h45 h66 hcfg
  have hZ₀ : Subgroup.zpowers d₀ = Subgroup.zpowers d :=
    zpowers_eq_of_eq_or_eq_inv (hTU d hE.mem_d hd1 hE.type_d)
  have hwd : w * d * w⁻¹ = d :=
    Item21LateProof.conj_eq_of_mem_zpowers hwd₀ (by rw [hZ₀]; exact Subgroup.mem_zpowers d)
  rw [hZ₀] at hwA
  have hwc : w * c * w⁻¹ = c := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hLC hwL), mul_inv_cancel_right]
  have hcd : c ∉ Subgroup.zpowers d := fun h => hcL ((Subgroup.zpowers_le.mpr hdL) h)
  have hdc : d ∉ Subgroup.zpowers c := not_mem_zpowers_symm (h3 c hcA) hd1 hcd
  have haCD : a ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d := not_mem_sup_of_config2119End hE
  have hB9 := Item21LateProof.card_zpowers_sup_zpowers (hcomm d hdA c hcA) hd3 (h3 c hcA) hd1 hcd
  have haB : a ∉ Subgroup.zpowers d ⊔ Subgroup.zpowers c := by
    rw [sup_comm]
    exact haCD
  set e' := w * e * w⁻¹ with he'def
  have he'A : e' ∈ A := (Subgroup.mem_normalizer_iff.mp hwN e).mp he
  have hδ : e⁻¹ * e' ∈ Subgroup.zpowers d := hwA e he
  have hee' : e = e' * (e⁻¹ * e')⁻¹ := by group
  have hecd' : e' ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
    intro h
    apply hecd
    rw [hee']
    exact Subgroup.mul_mem _ h (Subgroup.inv_mem _ (Subgroup.mem_sup_right hδ))
  have head' : e' ∉ Subgroup.zpowers a ⊔ Subgroup.zpowers d := by
    intro h
    apply head
    rw [hee']
    exact Subgroup.mul_mem _ h (Subgroup.inv_mem _ (Subgroup.mem_sup_right hδ))
  have heac' : e' ∉ Subgroup.zpowers a ⊔ Subgroup.zpowers c := by
    intro h
    have hδac : e⁻¹ * e' ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers c :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ heac) h
    have hδ1 : e⁻¹ * e' = 1 := by
      by_contra hne
      have hdδ : d ∈ Subgroup.zpowers (e⁻¹ * e') :=
        Item21Late2Proof.mem_zpowers_of_mem hd3 hδ hne (Subgroup.mem_zpowers d)
      have hdac : d ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers c :=
        (Subgroup.zpowers_le.mpr hδac) hdδ
      apply haCD
      by_contra haCD'
      exact not_mem_sup_swap (hcomm c hcA d hdA) (hcomm c hcA a haA) (h3 c hcA) hd3 (h3 a haA)
        hc1 hdc haCD' (by rw [sup_comm]; exact hdac)
    have hwe : w * e * w⁻¹ = e := by
      calc w * e * w⁻¹ = e' := rfl
        _ = e * (e⁻¹ * e') := by group
        _ = e := by rw [hδ1, mul_one]
    have hace : a ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers e := by
      by_contra hn
      exact not_mem_sup_swap (hcomm c hcA e he) (hcomm c hcA a haA) (h3 c hcA) (h3 e he)
        (h3 a haA) hc1 hec hn (by rw [sup_comm]; exact heac)
    have hwa : w * a * w⁻¹ = a := conj_eq_of_mem_sup hwc hwe hace
    obtain ⟨y, hyA, hy⟩ := hwmove
    exact hy (conj_eq_of_fix_basis hcomm h3 h27 hcA hdA haA hB9 haB hwa hwd hwc y hyA)
  obtain ⟨Le', hLe', hLe'3, ⟨eLe'⟩, hdLe', hdTLe', hcTLe'⟩ := hoff e' he'A hecd' head' heac'
  have hw'e : (MulAut.conj w⁻¹) e' = e := by
    rw [MulAut.conj_apply, he'def]
    group
  have hw'd : w⁻¹ * d * w⁻¹⁻¹ = d := by
    conv_lhs => rw [← hwd]
    group
  have hw'c : w⁻¹ * c * w⁻¹⁻¹ = c := by
    conv_lhs => rw [← hwc]
    group
  refine ⟨Le'.map (MulAut.conj w⁻¹).toMonoidHom, ?_, ?_,
    ⟨(lBarMapConj w⁻¹ Le').symm.trans eLe'⟩, ?_, ?_, ?_⟩
  · have h1 := map_mem_thetaComponentsAt (MulAut.conj w⁻¹) hLe'
    rwa [hw'e] at h1
  · rw [Subgroup.card_map_of_injective (MulAut.conj w⁻¹).injective]
    exact hLe'3
  · refine ⟨d, hdLe', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact hw'd
  · have h1 := inducesTypeOn_map_conj w⁻¹ hdTLe'
    rwa [hw'd] at h1
  · have h1 := inducesTypeOn_map_conj w⁻¹ hcTLe'
    rwa [hw'c] at h1

end Item2119End4Proof

open Item2119End4Proof

end CFSG.RankThree.PartTwo.Sec21

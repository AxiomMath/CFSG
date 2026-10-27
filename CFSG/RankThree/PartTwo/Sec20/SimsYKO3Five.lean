module

public import CFSG.RankThree.PartTwo.Sec20.SimsYKO3
public import CFSG.RankThree.PartTwo.Sec20.SimsYKO3FiveOffender
import CFSG.RankThree.PartTwo.Sec20.SimsYKO3Bridge
import CFSG.RankThree.PartTwo.Sec20.Item20Res11ProofPGroup
import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofTools
import CFSG.RankThree.PartTwo.Late.Item2010
import CFSG.RankThree.PartOne.S9.MinTwoAction.FixedRankBridge

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)

namespace SimsYKO3

open CFSG.HardMathSupport.Solomon.UniquenessMaximal (jOf jOneOf omegaOneZ)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem mem_pCoreOf_of_pow_two_pow {O : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {z : G} (hz : z ∈ oTwoPCore p O) {a : ℕ} (hza : z ^ (2 ^ a) = 1) :
    z ∈ CFSG.Open.pCoreOf 2 O := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨w, hw, rfl⟩ := hz
  obtain ⟨b, hb⟩ := CFSG.pCore_isPGroup (p := p) (G := O ⧸ CFSG.pCore 2 O)
    ⟨QuotientGroup.mk' (CFSG.pCore 2 O) w, hw⟩
  have hw2 : w ^ (2 ^ a) = 1 := Subtype.ext (by simpa using hza)
  have h2 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 O) w) ∣ 2 ^ a :=
    (orderOf_map_dvd _ w).trans (orderOf_dvd_of_pow_eq_one hw2)
  have hpb : orderOf (QuotientGroup.mk' (CFSG.pCore 2 O) w) ∣ p ^ b :=
    orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hb)
  have hcop : Nat.Coprime (2 ^ a) (p ^ b) :=
    Nat.Coprime.pow a b ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  have h1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h2 hpb)
  exact ⟨w, (QuotientGroup.eq_one_iff w).mp h1, rfl⟩

private noncomputable def preD (O : Subgroup G)
    (D : Subgroup ↥(CFSG.pCore 5 (↥O ⧸ CFSG.pCore 2 ↥O))) : Subgroup G :=
  ((D.map (CFSG.pCore 5 (↥O ⧸ CFSG.pCore 2 ↥O)).subtype).comap
    (QuotientGroup.mk' (CFSG.pCore 2 ↥O))).map O.subtype

omit [Finite G] in
private theorem preD_le (O : Subgroup G) (D : Subgroup ↥(CFSG.pCore 5 (↥O ⧸ CFSG.pCore 2 ↥O))) :
    preD O D ≤ O :=
  Subgroup.map_subtype_le _

omit [Finite G] in
private theorem mem_preD {O : Subgroup G} {D : Subgroup ↥(CFSG.pCore 5 (↥O ⧸ CFSG.pCore 2 ↥O))}
    (x : O) : (x : G) ∈ preD O D ↔
      QuotientGroup.mk' (CFSG.pCore 2 ↥O) x ∈
        D.map (CFSG.pCore 5 (↥O ⧸ CFSG.pCore 2 ↥O)).subtype := by
  constructor
  · rintro ⟨x', hx', hxx'⟩
    have : x' = x := Subtype.ext hxx'
    rw [← this]
    exact hx'
  · intro hx
    exact ⟨x, hx, rfl⟩

omit [Finite G] in
private theorem exists_of_mem_preD {O : Subgroup G}
    {D : Subgroup ↥(CFSG.pCore 5 (↥O ⧸ CFSG.pCore 2 ↥O))} (w : preD O D) :
    ∃ d ∈ D, ((d : CFSG.pCore 5 (↥O ⧸ CFSG.pCore 2 ↥O)) : ↥O ⧸ CFSG.pCore 2 ↥O) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥O) (Subgroup.inclusion (preD_le O D) w) :=
  (mem_preD (Subgroup.inclusion (preD_le O D) w)).mp w.2

private noncomputable def preDHom₀ (O : Subgroup G)
    (D : Subgroup ↥(CFSG.pCore 5 (↥O ⧸ CFSG.pCore 2 ↥O))) :
    ↥(preD O D) →* ↥(CFSG.pCore 5 (↥O ⧸ CFSG.pCore 2 ↥O)) :=
  MonoidHom.codRestrict ((QuotientGroup.mk' (CFSG.pCore 2 ↥O)).comp
    (Subgroup.inclusion (preD_le O D))) _ fun w => by
      obtain ⟨d, -, hd⟩ := exists_of_mem_preD w
      rw [MonoidHom.comp_apply, ← hd]
      exact d.2

omit [Finite G] in
private theorem preDHom₀_mem (O : Subgroup G)
    (D : Subgroup ↥(CFSG.pCore 5 (↥O ⧸ CFSG.pCore 2 ↥O))) (w : preD O D) : preDHom₀ O D w ∈ D := by
  obtain ⟨d, hdD, hd⟩ := exists_of_mem_preD w
  have : preDHom₀ O D w = d := Subtype.ext hd.symm
  rw [this]
  exact hdD

private noncomputable def preDHom (O : Subgroup G)
    (D : Subgroup ↥(CFSG.pCore 5 (↥O ⧸ CFSG.pCore 2 ↥O))) : ↥(preD O D) →* ↥D :=
  MonoidHom.codRestrict (preDHom₀ O D) D (preDHom₀_mem O D)

private noncomputable def actP (O : Subgroup G) :
    ↥(Subgroup.normalizer (O : Set G)) →* MulAut ↥(CFSG.pCore 5 (↥O ⧸ CFSG.pCore 2 ↥O)) :=
  (MulAut.characteristic (CFSG.pCore 5 (↥O ⧸ CFSG.pCore 2 ↥O))).comp
    (Res11.quotAction (le_refl (Subgroup.normalizer (O : Set G))))

omit [Finite G] in
private theorem actP_coe (O : Subgroup G) (g : Subgroup.normalizer (O : Set G))
    (z : CFSG.pCore 5 (↥O ⧸ CFSG.pCore 2 ↥O)) :
    ((actP O g z : CFSG.pCore 5 (↥O ⧸ CFSG.pCore 2 ↥O)) : ↥O ⧸ CFSG.pCore 2 ↥O) =
      Res11.quotAction (le_refl _) g z :=
  rfl

omit [Finite G] in
private theorem conj_mem_preD {O : Subgroup G}
    {D : Subgroup ↥(CFSG.pCore 5 (↥O ⧸ CFSG.pCore 2 ↥O))} [hDc : D.Characteristic]
    (g : Subgroup.normalizer (O : Set G)) (w : preD O D) : (g : G) * w * (g : G)⁻¹ ∈ preD O D := by
  have hgO : (g : G) * w * (g : G)⁻¹ ∈ O :=
    (Subgroup.mem_normalizer_iff.mp g.2 w).mp (preD_le O D w.2)
  refine (mem_preD ⟨_, hgO⟩).mpr ⟨actP O g (preDHom₀ O D w), ?_, ?_⟩
  · exact Subgroup.characteristic_iff_le_comap.mp hDc (actP O g) (preDHom₀_mem O D w)
  · rw [Subgroup.coe_subtype, actP_coe]
    exact Res11.quotAction_mk (le_refl _) g (Subgroup.inclusion (preD_le O D) w)

omit [Finite G] in
private theorem preDHom_conj {O : Subgroup G}
    {D : Subgroup ↥(CFSG.pCore 5 (↥O ⧸ CFSG.pCore 2 ↥O))} [D.Characteristic]
    (g : Subgroup.normalizer (O : Set G)) (w : preD O D) (h : (g : G) * w * (g : G)⁻¹ ∈ preD O D) :
    SectionRank.Ccomm.frattiniAction D (actP O g)
        (QuotientGroup.mk' (frattini ↥D) (preDHom O D w)) =
      QuotientGroup.mk' (frattini ↥D) (preDHom O D ⟨_, h⟩) := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, SectionRank.Ccomm.frattiniAction_mk]
  congr 1

private noncomputable def thetaD (O : Subgroup G)
    (D : Subgroup ↥(CFSG.pCore 5 (↥O ⧸ CFSG.pCore 2 ↥O))) [D.Characteristic] :
    ↥(Subgroup.normalizer (O : Set G)) →* MulAut (↥D ⧸ frattini ↥D) :=
  (SectionRank.Ccomm.frattiniAction D).comp (actP O)

private noncomputable def piD (O : Subgroup G)
    (D : Subgroup ↥(CFSG.pCore 5 (↥O ⧸ CFSG.pCore 2 ↥O))) : ↥(preD O D) →* (↥D ⧸ frattini ↥D) :=
  (QuotientGroup.mk' (frattini ↥D)).comp (preDHom O D)

omit [Finite G] in
private theorem thetaD_piD {O : Subgroup G}
    {D : Subgroup ↥(CFSG.pCore 5 (↥O ⧸ CFSG.pCore 2 ↥O))} [D.Characteristic]
    (g : Subgroup.normalizer (O : Set G)) (w : preD O D) (h : (g : G) * w * (g : G)⁻¹ ∈ preD O D) :
    thetaD O D g (piD O D w) = piD O D ⟨_, h⟩ :=
  preDHom_conj g w h

omit [Finite G] in
private theorem preDHom_surjective (O : Subgroup G)
    (D : Subgroup ↥(CFSG.pCore 5 (↥O ⧸ CFSG.pCore 2 ↥O))) :
    Function.Surjective ((QuotientGroup.mk' (frattini ↥D)).comp (preDHom O D)) := by
  intro v
  obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective (frattini ↥D) v
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥O)
    ((d : CFSG.pCore 5 (↥O ⧸ CFSG.pCore 2 ↥O)) : ↥O ⧸ CFSG.pCore 2 ↥O)
  have hxW : (x : G) ∈ preD O D := (mem_preD x).mpr (by rw [hx]; exact ⟨d, d.2, rfl⟩)
  refine ⟨⟨x, hxW⟩, ?_⟩
  exact congrArg (QuotientGroup.mk' (frattini ↥D)) (Subtype.ext (Subtype.ext hx))

omit [Finite G] in
private theorem pCoreOf_le_preD (O : Subgroup G)
    (D : Subgroup ↥(CFSG.pCore 5 (↥O ⧸ CFSG.pCore 2 ↥O))) :
    CFSG.Open.pCoreOf 2 O ≤ preD O D := by
  rintro _ ⟨x, hx, rfl⟩
  refine (mem_preD x).mpr ?_
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥O) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
  rw [h1]
  exact Subgroup.one_mem _

omit [Finite G] in
private theorem piD_surjective (O : Subgroup G)
    (D : Subgroup ↥(CFSG.pCore 5 (↥O ⧸ CFSG.pCore 2 ↥O))) : Function.Surjective (piD O D) :=
  preDHom_surjective O D

omit [Finite G] in
private theorem preDHom_eq_one (O : Subgroup G)
    (D : Subgroup ↥(CFSG.pCore 5 (↥O ⧸ CFSG.pCore 2 ↥O))) (w : preD O D)
    (hw : (w : G) ∈ CFSG.Open.pCoreOf 2 O) : preDHom O D w = 1 := by
  obtain ⟨x, hx, hxw⟩ := hw
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥O) (Subgroup.inclusion (preD_le O D) w) = 1 := by
    have : Subgroup.inclusion (preD_le O D) w = x := Subtype.ext hxw.symm
    rw [this]
    exact (QuotientGroup.eq_one_iff x).mpr hx
  exact Subtype.ext (Subtype.ext h1)

omit [Finite G] in
private theorem preD_le_oTwoPCore (O : Subgroup G)
    (D : Subgroup ↥(CFSG.pCore 5 (↥O ⧸ CFSG.pCore 2 ↥O))) : preD O D ≤ oTwoPCore 5 O := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨d, -, hd⟩ := hx
  refine ⟨x, ?_, rfl⟩
  show QuotientGroup.mk' (CFSG.pCore 2 ↥O) x ∈ CFSG.pCore 5 (↥O ⧸ CFSG.pCore 2 ↥O)
  rw [← hd]
  exact d.2

omit [Finite G] in
private theorem exists_pow_mem_of_mem_preD (O : Subgroup G)
    (D : Subgroup ↥(CFSG.pCore 5 (↥O ⧸ CFSG.pCore 2 ↥O))) :
    ∀ w ∈ preD O D, ∃ a : ℕ, w ^ (5 ^ a) ∈ CFSG.Open.pCoreOf 2 O := by
  have hp5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro w hw
  obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := 5) (G := ↥O ⧸ CFSG.pCore 2 ↥O))
    (preDHom₀ O D ⟨w, hw⟩)
  refine ⟨a, ⟨Subgroup.inclusion (preD_le O D) ⟨w, hw⟩ ^ (5 ^ a), ?_, by simp⟩⟩
  have : QuotientGroup.mk' (CFSG.pCore 2 ↥O)
      (Subgroup.inclusion (preD_le O D) ⟨w, hw⟩ ^ (5 ^ a)) = 1 := by
    rw [map_pow]
    exact congrArg Subtype.val ha
  exact (QuotientGroup.eq_one_iff _).mp this

private theorem preD_le_of_map_eq (O : Subgroup G)
    (D : Subgroup ↥(CFSG.pCore 5 (↥O ⧸ CFSG.pCore 2 ↥O))) (X : Subgroup G)
    (hQX : CFSG.Open.pCoreOf 2 O ≤ X)
    (hXv : ∀ v : ↥D ⧸ frattini ↥D, ∃ x : preD O D, (x : G) ∈ X ∧
      QuotientGroup.mk' (frattini ↥D) (preDHom O D x) = v) : preD O D ≤ X := by
  have htop : (X.subgroupOf (preD O D)).map (preDHom O D) ⊔ frattini ↥D = ⊤ := by
    rw [eq_top_iff]
    intro d _
    obtain ⟨x, hxX, hxv⟩ := hXv (QuotientGroup.mk' (frattini ↥D) d)
    obtain ⟨c, hc, hcd⟩ := (QuotientGroup.mk'_eq_mk' _).mp hxv
    rw [← hcd]
    exact Subgroup.mul_mem_sup ⟨x, Subgroup.mem_subgroupOf.mpr hxX, rfl⟩ hc
  have hDXt := frattini_nongenerating htop
  intro w hw
  have h1 : preDHom O D ⟨w, hw⟩ ∈ (X.subgroupOf (preD O D)).map (preDHom O D) :=
    hDXt ▸ Subgroup.mem_top _
  obtain ⟨x, hxX, hxw⟩ := h1
  have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥O) (Subgroup.inclusion (preD_le O D) x) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥O) (Subgroup.inclusion (preD_le O D) ⟨w, hw⟩) :=
    congrArg (fun d : D =>
      ((d : CFSG.pCore 5 (↥O ⧸ CFSG.pCore 2 ↥O)) : ↥O ⧸ CFSG.pCore 2 ↥O)) hxw
  obtain ⟨c, hc, hcw⟩ := (QuotientGroup.mk'_eq_mk' _).mp h2
  have h3 : (c : G) ∈ X := hQX ⟨c, hc, rfl⟩
  have h4 := X.mul_mem (Subgroup.mem_subgroupOf.mp hxX) h3
  have h5 : (x : G) * c = w := congrArg Subtype.val hcw
  rwa [h5] at h4

omit [Finite G] in
private theorem comm_mem_of_frattiniAction_eq_one (O : Subgroup G)
    (D : Subgroup ↥(CFSG.pCore 5 (↥O ⧸ CFSG.pCore 2 ↥O))) [D.Characteristic]
    (hker : IsPGroup 5 (SectionRank.Ccomm.frattiniAction D).ker)
    (g : Subgroup.normalizer (O : Set G)) {b : ℕ} (hgb : g ^ (2 ^ b) = 1)
    (h1 : SectionRank.Ccomm.frattiniAction D (actP O g) = 1) :
    ∀ w ∈ preD O D, (g : G) * w * (g : G)⁻¹ * w⁻¹ ∈ CFSG.Open.pCoreOf 2 O := by
  intro w hw
  obtain ⟨a, ha⟩ := hker ⟨_, MonoidHom.mem_ker.mpr h1⟩
  have h5 : orderOf (actP O g) ∣ 5 ^ a :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val ha)
  have h2 : orderOf (actP O g) ∣ 2 ^ b :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hgb, map_one])
  have hcop : Nat.Coprime (5 ^ a) (2 ^ b) := Nat.Coprime.pow _ _ (by norm_num)
  have hρ1 : actP O g = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h5 h2)
  have hfix : Res11.quotAction (le_refl _) g
      (QuotientGroup.mk' (CFSG.pCore 2 ↥O) (Subgroup.inclusion (preD_le O D) ⟨w, hw⟩)) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥O) (Subgroup.inclusion (preD_le O D) ⟨w, hw⟩) :=
    congrArg (fun σ : MulAut (CFSG.pCore 5 (↥O ⧸ CFSG.pCore 2 ↥O)) =>
      ((σ (preDHom₀ O D ⟨w, hw⟩) : CFSG.pCore 5 (↥O ⧸ CFSG.pCore 2 ↥O)) :
        ↥O ⧸ CFSG.pCore 2 ↥O)) hρ1
  exact Res11.comm_mem_of_quotAction_fix (le_refl _) g
    (Subgroup.inclusion (preD_le O D) ⟨w, hw⟩) hfix

private theorem frattiniQuot_facts {P : Type*} [Group P] [Finite P] (hP : IsPGroup 5 P)
    (hrank : CFSG.pRank 5 P ≤ 2) {D : Subgroup P} (hDexp : ∀ x ∈ D, x ^ 5 = 1)
    (hDcomm : ⁅D, (⊤ : Subgroup P)⁆ ≤ D ⊓ Subgroup.centralizer (D : Set P))
    {K : Type*} [Group K] [Group.IsPerfect K] (κ : K →* MulAut (↥D ⧸ frattini ↥D)) (hκ : κ ≠ 1) :
    (∀ a b : ↥D ⧸ frattini ↥D, a * b = b * a) ∧ (∀ a : ↥D ⧸ frattini ↥D, a ^ 5 = 1) ∧
      Nat.card (↥D ⧸ frattini ↥D) = 25 := by
  have hp5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hDp : IsPGroup 5 D := hP.to_subgroup D
  have hDexp' : ∀ x : D, x ^ 5 = 1 := fun x => Subtype.ext (by
    rw [Subgroup.coe_pow, hDexp x x.2, Subgroup.coe_one])
  have hDclass : commutator D ≤ Subgroup.center D :=
    Res11.commutator_le_center_of_le_centralizer hDcomm
  have hDrank : CFSG.pRank 5 D ≤ 2 :=
    (RankThree.PartOne.FixedRank36.pRank_le_of_injective D.subtype D.subtype_injective).trans
      hrank
  have hQrank : CFSG.pRank 5 (D ⧸ commutator D) ≤ 2 :=
    (class_two_small_rank_order_bounds hDp hDexp' hDclass).1 hDrank
  have hΦ : frattini D = commutator D := frattini_eq_commutator hDp hDexp'
  have : Fact (IsPGroup 5 D) := ⟨hDp⟩
  have hWel : IsElementaryAbelian 5 (D ⧸ frattini D) :=
    CFSG.isElementaryAbelian_quotient_frattini (R := D) (p := 5)
  have hWrank : CFSG.pRank 5 (D ⧸ frattini D) ≤ 2 :=
    (RankThree.PartOne.FixedRank36.pRank_le_of_injective
      (QuotientGroup.quotientMulEquivOfEq hΦ).toMonoidHom
      (QuotientGroup.quotientMulEquivOfEq hΦ).injective).trans hQrank
  have hE5 : ∀ x : D ⧸ frattini D, x ^ 5 = 1 := fun x =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hWel.exponent_dvd_p x
  have hEc : ∀ a b : D ⧸ frattini D, a * b = b * a := fun a b =>
    hWel.toIsMulCommutative.is_comm.comm a b
  obtain ⟨n, hn⟩ := (hDp.to_quotient (frattini D)).exists_card_eq
  have hn2 : n ≤ 2 := by
    rw [← pRank_eq_of_isMulCommutative hp5.out hE5 hWel.toIsMulCommutative hn]
    exact hWrank
  refine ⟨hEc, hE5, ?_⟩
  rcases (show n = 0 ∨ n = 1 ∨ n = 2 by omega) with h | h | h
  · exfalso
    rw [h, pow_zero] at hn
    have : Subsingleton (D ⧸ frattini D) := (Nat.card_eq_one_iff_unique.mp hn).1
    exact hκ (MonoidHom.ext fun _ => MulEquiv.ext fun _ => Subsingleton.elim _ _)
  · exfalso
    rw [h, pow_one] at hn
    have : IsCyclic (D ⧸ frattini D) := isCyclic_of_prime_card hn
    exact hκ (eq_one_of_isCyclic _)
  · rw [hn, h]; norm_num

private theorem actP_comp_eq_one {O K R M : Subgroup G} [Group.IsPerfect K]
    (hK : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* projSL 2 (GaloisField 2 2)))
    (hKO : K ≤ Subgroup.normalizer (O : Set G)) (hRO : R ≤ Subgroup.normalizer (O : Set G))
    (h3 : Nat.Coprime 3 (Nat.card O)) (hQR : CFSG.Open.pCoreOf 2 O ≤ R)
    (hHyp : HypThree (oTwoPCore 5 O ⊔ R) R)
    (hKR : K ≤ Subgroup.normalizer (R : Set G)) (hRK : R ≤ Subgroup.normalizer (K : Set G))
    (hrank : CFSG.Open.pRank 5 O ≤ 2)
    (hM0 : Subgroup.normalizer (omegaOneZ R : Set G) ≤ M)
    (hM2 : Subgroup.normalizer (omegaOneZ (jOneOf R) : Set G) ≤ M)
    (hMK : M ≤ Subgroup.normalizer (K : Set G)) :
    (actP O).comp (Subgroup.inclusion hKO) = 1 := by
  classical
  have hp5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  by_cases hnt : Nontrivial ↥(CFSG.pCore 5 (↥O ⧸ CFSG.pCore 2 ↥O))
  swap
  · rw [not_nontrivial_iff_subsingleton] at hnt
    exact MonoidHom.ext fun _ => MulEquiv.ext fun _ => Subsingleton.elim _ _
  obtain ⟨D, hDc, -, hDexp, hDcomm, -, hker⟩ :=
    SectionRank.Ccomm.supercritical_witness (p := 5) (by norm_num)
      (CFSG.pCore_isPGroup (p := 5) (G := ↥O ⧸ CFSG.pCore 2 ↥O))
  by_cases hθK : (thetaD O D).comp (Subgroup.inclusion hKO) = 1
  ·
    apply Res11.eq_one_of_isPGroup_range ((actP O).comp (Subgroup.inclusion hKO)) (p := 5)
    refine hker.to_le ?_
    rintro _ ⟨k', rfl⟩
    rw [MonoidHom.mem_ker]
    exact DFunLike.congr_fun hθK k'
  exfalso
  have hrankP : CFSG.pRank 5 (CFSG.pCore 5 (↥O ⧸ CFSG.pCore 2 ↥O)) ≤ 2 :=
    ((RankThree.PartOne.FixedRank36.pRank_le_of_injective _ (Subgroup.subtype_injective _)).trans
      (Res11.pRank_quotient_le O (by norm_num) (by norm_num))).trans hrank
  obtain ⟨hEc, hE5, hE25⟩ := frattiniQuot_facts CFSG.pCore_isPGroup hrankP hDexp hDcomm _ hθK
  have hWN : Subgroup.normalizer (O : Set G) ≤ Subgroup.normalizer (preD O D : Set G) := by
    intro g hg
    refine CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7.mem_normalizer_of_conj_mem
      (fun x hx => conj_mem_preD ⟨g, hg⟩ ⟨x, hx⟩) (fun x hx => ?_)
    have := conj_mem_preD (D := D) ⟨g, hg⟩⁻¹ ⟨x, hx⟩
    simpa using this
  have hHyp' : HypThree (preD O D ⊔ R) R :=
    hHyp.mono le_sup_right (sup_le_sup_right (preD_le_oTwoPCore O D) R)
  have hQπ : ∀ w : ↥(preD O D), (w : G) ∈ CFSG.Open.pCoreOf 2 O → piD O D w = 1 := by
    intro w hw
    show QuotientGroup.mk' (frattini ↥D) (preDHom O D w) = 1
    rw [preDHom_eq_one O D w hw, map_one]
  have hRθ : ∀ r (hr : r ∈ R), thetaD O D ⟨r, hRO hr⟩ = 1 →
      ∀ w ∈ preD O D, r * w * r⁻¹ * w⁻¹ ∈ CFSG.Open.pCoreOf 2 O := by
    intro r hr h1
    obtain ⟨b, hb⟩ := hHyp.two ⟨r, hr⟩
    exact comm_mem_of_frattiniAction_eq_one O D hker ⟨r, hRO hr⟩
      (Subtype.ext (by simpa using congrArg Subtype.val hb)) h1
  have hJ : jOneOf R ≤ Subgroup.centralizer (reducedClosure (preD O D ⊔ R) R : Set G) :=
    jOneOf_le_centralizer_of_E25 hEc hE5 hE25 (thetaD O D) (piD O D) (piD_surjective O D) hWN
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 O)
      ((preD_le O D).trans Subgroup.le_normalizer) hRO hKO thetaD_piD (pCoreOf_le_preD O D) hQπ
      (fun X hQX _ hXv => preD_le_of_map_eq O D X hQX hXv) (exists_pow_mem_of_mem_preD O D)
      hRθ hQR hHyp' hK hKR hRK hθK
  obtain ⟨U, hUR, -, hUn, -, hUc⟩ := hHyp'.exists_O2
  obtain ⟨-, hVn, -, hZV, -, -, -⟩ :=
    reducedClosure_spec hHyp'.le hHyp'.two hHyp'.syl hUR hUn hUc
  have hWDM : preD O D ⊔ R ≤ M :=
    le_of_fac hM0 hM2 (fac_two_one_of_le_centralizer hHyp'.le hHyp'.two hHyp'.syl hVn hZV hJ)
  obtain ⟨hs, h3K⟩ := simple_three_dvd_small (Or.inr hK)
  suffices hθ1 : ∀ k' : K, thetaD O D (Subgroup.inclusion hKO k') = 1 from
    hθK (MonoidHom.ext fun k' => hθ1 k')
  intro k'
  refine MulEquiv.ext fun v => ?_
  rw [MulAut.one_apply]
  obtain ⟨w, rfl⟩ := piD_surjective O D v
  have hkw : (k' : G) * w * (k' : G)⁻¹ ∈ preD O D := conj_mem_preD (Subgroup.inclusion hKO k') w
  rw [thetaD_piD (Subgroup.inclusion hKO k') w hkw]
  have hwK : (w : G) ∈ Subgroup.normalizer (K : Set G) := hMK (hWDM (Subgroup.mem_sup_left w.2))
  have hcK : (k' : G) * w * (k' : G)⁻¹ * (w : G)⁻¹ ∈ K := by
    have h1 : (w : G) * (k' : G)⁻¹ * (w : G)⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp hwK _).mp (K.inv_mem k'.2)
    have := K.mul_mem k'.2 h1
    simpa [mul_assoc] using this
  have hcW : (k' : G) * w * (k' : G)⁻¹ * (w : G)⁻¹ ∈ preD O D :=
    (preD O D).mul_mem hkw ((preD O D).inv_mem w.2)
  have hc2 : (k' : G) * w * (k' : G)⁻¹ * (w : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 K :=
    inf_le_pCoreOf_two hKO h3 hs h3K ⟨hcK, preD_le O D hcW⟩
  obtain ⟨a, ha⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K ⟨_, hc2⟩
  have hc2' : ((k' : G) * w * (k' : G)⁻¹ * (w : G)⁻¹) ^ (2 ^ a) = 1 := by
    simpa using congrArg Subtype.val ha
  have hcQ : (k' : G) * w * (k' : G)⁻¹ * (w : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 O :=
    mem_pCoreOf_of_pow_two_pow (by norm_num) (by norm_num) (preD_le_oTwoPCore O D hcW) hc2'
  have h1 : (⟨_, hkw⟩ : preD O D) = ⟨_, hcW⟩ * w := Subtype.ext (by simp)
  have h2 : piD O D ⟨_, hkw⟩ = piD O D w := by rw [h1, map_mul, hQπ _ hcQ, one_mul]
  exact h2

theorem fix_pCore_five_of_pair02 {O K R M : Subgroup G} [Group.IsPerfect K]
    (hK : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* projSL 2 (GaloisField 2 2)))
    (hKO : K ≤ Subgroup.normalizer (O : Set G)) (hRO : R ≤ Subgroup.normalizer (O : Set G))
    (h3 : Nat.Coprime 3 (Nat.card O)) (hQR : CFSG.Open.pCoreOf 2 O ≤ R)
    (hHyp : HypThree (oTwoPCore 5 O ⊔ R) R)
    (hKR : K ≤ Subgroup.normalizer (R : Set G)) (hRK : R ≤ Subgroup.normalizer (K : Set G))
    (hrank : CFSG.Open.pRank 5 O ≤ 2)
    (hM0 : Subgroup.normalizer (omegaOneZ R : Set G) ≤ M)
    (hM2 : Subgroup.normalizer (omegaOneZ (jOneOf R) : Set G) ≤ M)
    (hMK : M ≤ Subgroup.normalizer (K : Set G)) (k : K) {y : ↥O ⧸ CFSG.pCore 2 ↥O}
    (hy : y ∈ CFSG.pCore 5 (↥O ⧸ CFSG.pCore 2 ↥O)) : Res11.quotAction hKO k y = y :=
  congrArg (fun σ : MulAut (CFSG.pCore 5 (↥O ⧸ CFSG.pCore 2 ↥O)) =>
    ((σ ⟨y, hy⟩ : CFSG.pCore 5 (↥O ⧸ CFSG.pCore 2 ↥O)) : ↥O ⧸ CFSG.pCore 2 ↥O))
    (DFunLike.congr_fun (actP_comp_eq_one hK hKO hRO h3 hQR hHyp hKR hRK hrank hM0 hM2 hMK) k)

end SimsYKO3

theorem step204YKO3CommFive_holds : Step204YKO3CommFive := by
  intro G _ _ A M L N c T i j P hset X hX hXM hm hle he hij2 k hk o ho
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsSimpleGroup G := hset.isSimpleGroup
  set K := kTwenty M c with hKdef
  set Y := yTwenty X c with hYdef
  set O := inSubgroup (CFSG.pPrimeCore 3) Y with hOdef
  set R := CFSG.Open.pCoreOf 2 (K ⊔ T) with hRdef
  have hKX : K ≤ X := fun x hx => hX.2 (Subgroup.mem_sup_left hx)
  have hKY : K ≤ Y := Res6.kTwenty_le_yTwenty hset hKX
  have hYX : Y ≤ X := Res6.normalClosureIn_le_self (hKX (self_mem_normalClosureIn M c))
  have hOX : O ≤ X := (Res6.inSubgroup_pPrimeCore_le 3 Y).trans hYX
  have hperf : Group.IsPerfect K := isPerfect_of_mem_oTwoComponentsIn hset.mem_oTwoComponentsIn
  haveI := hperf
  have hKO : K ≤ Subgroup.normalizer (O : Set G) :=
    hKY.trans (Res6.le_normalizer_inSubgroup_pPrimeCore 3 Y)
  have hXO : X ≤ Subgroup.normalizer (O : Set G) :=
    (le_normalizer_normalClosureIn X c).trans
      (Res6.normalizer_le_normalizer_inSubgroup_pPrimeCore 3 Y)
  have hO3 : Nat.Coprime 3 (Nat.card O) := Res6.coprime_card_inSubgroup_pPrimeCore 3 Y
  have hrank := SimsYKO3.rank_le_two hset hX hOX
  have hMK : M ≤ Subgroup.normalizer (K : Set G) := le_normalizer_normalClosureIn M c
  obtain ⟨hs, h3K⟩ := SimsYKO3.simple_three_dvd_small (Or.inr he)
  have hKTX : K ⊔ T ≤ X := fun x hx => hX.2 hx
  have hRX : R ≤ X := (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hKTX
  have hQR : CFSG.Open.pCoreOf 2 O ≤ R :=
    SimsYKO3.le_of_mem_max hset.maxInvariant (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 O)
      ((hKTX.trans hXO).trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 O))
      ((hRX.trans hXO).trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 O))
  have hX2R : CFSG.Open.pCoreOf 2 X ≤ R :=
    SimsYKO3.le_of_mem_max hset.maxInvariant (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)
      (hKTX.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X))
      (hRX.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X))
  have hM : M ≠ ⊤ := ne_top_of_pCoreOf_ne_bot hset.nonabelian
    (pCoreOf_ne_bot_of_isMaximalTwoLocal hset.mem_scriptM.1)
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  obtain ⟨hsol, h3', -, hO', hidx⟩ := SimsYKO3.oTwoPCore_sup_package (p := 5) (by norm_num)
    le_rfl hOX hXO hO3 hR2 hRX hQR hX2R (hset.charTwoType X hX.1.1)
  have hHyp : SimsYKO3.HypThree (SimsYKO3.oTwoPCore 5 O ⊔ R) R :=
    ⟨hsol, h3', hO', le_sup_right, hR2, hidx⟩
  have hKR : K ≤ Subgroup.normalizer (R : Set G) :=
    le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (K ⊔ T))
  have hRK : R ≤ Subgroup.normalizer (K : Set G) :=
    Subgroup.le_normalizer.trans hset.normalizer_le
  have hne2 : Subgroup.normalizer (Sec18.fourChar R 2 : Set G) ≤ M → Sec18.fourChar R 2 ≠ ⊥ := by
    intro hN hbot
    apply hM
    rw [hbot, Subgroup.normalizer_eq_top] at hN
    exact top_le_iff.mp hN
  have h02 : Subgroup.normalizer (Sec18.fourChar R 0 : Set G) ≤ M →
      Subgroup.normalizer (Sec18.fourChar R 2 : Set G) ≤ M →
        k * o * k⁻¹ * o⁻¹ ∈ CFSG.Open.pCoreOf 2 O := by
    intro h0 h2
    have hM0 : Subgroup.normalizer
        (CFSG.HardMathSupport.Solomon.UniquenessMaximal.omegaOneZ R : Set G) ≤ M := by
      rwa [SimsYKO3.fourChar_zero_eq R] at h0
    have hM2 : Subgroup.normalizer (CFSG.HardMathSupport.Solomon.UniquenessMaximal.omegaOneZ
        (CFSG.HardMathSupport.Solomon.UniquenessMaximal.jOneOf R) : Set G) ≤ M := by
      rwa [SimsYKO3.fourChar_two_eq R hR2 (hne2 h2)] at h2
    obtain ⟨x, hx, rfl⟩ := ho
    exact Res11.comm_mem_of_quotAction_fix hKO ⟨k, hk⟩ x
      (SimsYKO3.fix_pCore_five_of_pair02 he hKO (hRX.trans hXO) hO3 hQR hHyp hKR hRK
        (hrank 5 (by norm_num) le_rfl) hM0 hM2 hMK ⟨k, hk⟩ hx)
  have h12 : Subgroup.normalizer (Sec18.fourChar R 1 : Set G) ≤ M →
      Subgroup.normalizer (Sec18.fourChar R 2 : Set G) ≤ M →
        k * o * k⁻¹ * o⁻¹ ∈ CFSG.Open.pCoreOf 2 O := by
    intro h1 h2
    have hW : SimsYKO3.oTwoPCore 5 O ⊔ R ≤ M :=
      SimsYKO3.le_of_fac (A := Subgroup.normalizer
          (CFSG.HardMathSupport.Solomon.UniquenessMaximal.jOf R : Set G))
        (by rwa [SimsYKO3.fourChar_one_eq R] at h1)
        (by rwa [SimsYKO3.fourChar_two_eq R hR2 (hne2 h2)] at h2)
        (SimsYKO3.fac_zero_one_three hsol h3' hO' le_sup_right hR2 hidx)
    exact SimsYKO3.comm_mem_oTwoPCore hKO hO3 hs h3K (p := 5) (by norm_num) (by norm_num)
      ((le_sup_left.trans hW).trans hMK) hk ho
  have hcases : ∀ i : Fin 4, i ≠ 3 → i = 0 ∨ i = 1 ∨ i = 2 := by decide
  have hNi := hset.normalizer_left
  have hNj := hset.normalizer_right
  rcases hcases i hset.ne_three_left with rfl | rfl | rfl <;>
    rcases hcases j hset.ne_three_right with rfl | rfl | rfl
  · exact absurd rfl hset.ne
  · exact absurd hij2 (by decide)
  · exact h02 hNi hNj
  · exact absurd hij2 (by decide)
  · exact absurd rfl hset.ne
  · exact h12 hNi hNj
  · exact h02 hNj hNi
  · exact h12 hNj hNi
  · exact absurd rfl hset.ne

theorem step204YKO3CommSmall_holds :
    Step204YKO3CommSmall :=
  step204YKO3CommSmall_of_five step204YKO3CommFive_holds

end CFSG.RankThree.PartTwo.Sec20

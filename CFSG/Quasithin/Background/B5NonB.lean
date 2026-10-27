module

public import CFSG.Quasithin.Background.B5IrrA
public import CFSG.Quasithin.Background.B5NonInputs
import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.Quasithin.Background.A3StructureKGroup
public import CFSG.Quasithin.Background.B6Offenders

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B5

section Abstract

variable {Ω : Type*} [Group Ω] [Finite Ω]

omit [Finite Ω] in
theorem commute_of_comm_central {L : Subgroup Ω} (hperf : ⁅L, L⁆ = L) {m : Ω}
    (hmn : ∀ l ∈ L, m * l * m⁻¹ ∈ L) {Z : Subgroup Ω} (hZ : ∀ z ∈ Z, ∀ l ∈ L, z * l = l * z)
    (hmZ : ∀ l ∈ L, ⁅m, l⁆ ∈ Z) : ∀ l ∈ L, m * l = l * m := by
  have hle : ⁅L, L⁆ ≤ Subgroup.centralizer ({m} : Set Ω) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hz₁ : ⁅m, a⁆ ∈ L := by
      have := L.mul_mem (hmn a ha) (L.inv_mem ha)
      simpa [commutatorElement_def] using this
    have hz₂ : ⁅m, b⁆ ∈ L := by
      have := L.mul_mem (hmn b hb) (L.inv_mem hb)
      simpa [commutatorElement_def] using this
    have e₁ : m * a * m⁻¹ = a * ⁅m, a⁆ := by
      rw [← hZ _ (hmZ a ha) a ha]; simp [commutatorElement_def]
    have e₂ : m * b * m⁻¹ = b * ⁅m, b⁆ := by
      rw [← hZ _ (hmZ b hb) b hb]; simp [commutatorElement_def]
    have hc : m * ⁅a, b⁆ * m⁻¹ = ⁅a, b⁆ := by
      have e : m * ⁅a, b⁆ * m⁻¹ = ⁅m * a * m⁻¹, m * b * m⁻¹⁆ := by
        simp only [commutatorElement_def]; group
      rw [e, e₁, e₂]
      exact comm_mul_central (hZ _ (hmZ a ha) b hb) (hZ _ (hmZ a ha) _ hz₂)
        (hZ _ (hmZ b hb) a ha)
    have := mul_inv_eq_iff_eq_mul.1 hc
    exact this.symm
  rw [hperf] at hle
  intro l hl
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hl)).symm

omit [Finite Ω] in
theorem eq_one_of_pgroup_of_odd_orderOf {R : Subgroup Ω} (hR : IsPGroup 2 R) {x : Ω} (hx : x ∈ R)
    (hodd : Odd (orderOf x)) : x = 1 := by
  obtain ⟨i, hi⟩ := IsPGroup.iff_orderOf.1 hR ⟨x, hx⟩
  rw [Subgroup.orderOf_mk] at hi
  rw [hi] at hodd
  have : i = 0 := by
    by_contra hne
    exact (Nat.not_even_iff_odd.2 hodd) ((Nat.even_pow.2 ⟨even_two, hne⟩))
  rw [this, pow_zero] at hi
  exact orderOf_eq_one_iff.1 hi

theorem section_group_facts {L Y : Subgroup Ω} (hLY : L ≤ Y) (hq : CFSG.Open.IsQuasisimple ↥L)
    (hn : ∀ y ∈ Y, ∀ l ∈ L, y * l * y⁻¹ ∈ L) (h2 : ∀ y ∈ Y, y ^ 2 ∈ L)
    (hd : ∀ x ∈ Y, (∀ l ∈ L, x * l = l * x) → x ∈ L ∧ Odd (orderOf x)) :
    pCoreOf 2 Y = ⊥ ∧ quasithinGenFitting Y = L ∧ centerOf Y ≤ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO2 : pCoreOf 2 Y = ⊥ := by
    set N := pCoreOf 2 Y with hNdef
    have hN2 : IsPGroup 2 ↥N := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
    have hNY : N ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
    have hNn : ∀ y ∈ Y, ∀ n ∈ N, y * n * y⁻¹ ∈ N := fun y hy n hn =>
      B1Red.conj_mem_pCoreOf_prime 2 hy hn
    have hLn : ∀ l ∈ L, ∀ n ∈ N, l * n * l⁻¹ ∈ N := fun l hl n hn => hNn l (hLY hl) n hn
    have hNL : N ⊓ L = ⊥ := by
      have hDnorm : ((N ⊓ L).subgroupOf L).Normal := by
        refine ⟨fun x hx g => ?_⟩
        rw [Subgroup.mem_subgroupOf] at hx ⊢
        exact ⟨by simpa using hLn (g : Ω) g.2 x hx.1,
          by simpa using L.mul_mem (L.mul_mem g.2 hx.2) (L.inv_mem g.2)⟩
      rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq
        ((N ⊓ L).subgroupOf L) with hc | htop
      · rw [eq_bot_iff]
        intro d hd'
        have hcomm : ∀ l ∈ L, d * l = l * d := by
          intro l hl
          have hmem : (⟨d, hd'.2⟩ : ↥L) ∈ (N ⊓ L).subgroupOf L := hd'
          have := Subgroup.mem_center_iff.mp (hc hmem) ⟨l, hl⟩
          exact (congrArg Subtype.val this).symm
        obtain ⟨-, hodd⟩ := hd d (hNY hd'.1) hcomm
        exact Subgroup.mem_bot.2 (eq_one_of_pgroup_of_odd_orderOf hN2 hd'.1 hodd)
      · exfalso
        have hLN : L ≤ N := by
          intro l hl
          have : (⟨l, hl⟩ : ↥L) ∈ (N ⊓ L).subgroupOf L := by rw [htop]; trivial
          exact (Subgroup.mem_subgroupOf.1 this).1
        have hperf : Group.IsPerfect ↥L := ⟨hq.1⟩
        have hnt : Nontrivial ↥L := CFSG.ComponentClassification.Quasisimple.nontrivial hq
        exact Group.IsPerfect.not_isNilpotent ↥L (hN2.to_le hLN).isNilpotent
    have hcomm : ⁅N, L⁆ ≤ N ⊓ L :=
      B1Red.commutator_le_inf_of_normalizes (fun n hn' l hl => hn n (hNY hn') l hl) hLn
    rw [hNL] at hcomm
    have hNc : N ≤ Subgroup.centralizer (L : Set Ω) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 (le_bot_iff.1 hcomm)
    rw [eq_bot_iff]
    intro n hnN
    have hcn : ∀ l ∈ L, n * l = l * n := fun l hl =>
      (Subgroup.mem_centralizer_iff.1 (hNc hnN) l hl).symm
    obtain ⟨-, hodd⟩ := hd n (hNY hnN) hcn
    exact Subgroup.mem_bot.2 (eq_one_of_pgroup_of_odd_orderOf hN2 hnN hodd)
  refine ⟨hO2, B1Red.quasithinGenFitting_eq_of_two_quot hLY hn hq h2 hO2, ?_⟩
  intro z hz
  have hcomm : ∀ l ∈ L, z * l = l * z := fun l hl =>
    (Subgroup.mem_centralizer_iff.1 hz.2 l (hLY hl)).symm
  exact (hd z hz.1 hcomm).1

omit [Finite Ω] in
theorem commutator_L_perfect' {L : Subgroup Ω} (hLq : CFSG.IsQuasisimple ↥L) : ⁅L, L⁆ = L := by
  have : Group.IsPerfect ↥L := hLq.1
  exact Subgroup.commutator_eq_self

end Abstract

section SQTKTransport

variable {Ω : Type} [Group Ω]

theorem sqtk_of_mulEquiv {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y] (e : X ≃* Y)
    (hY : SQTKGroup Y) : SQTKGroup X :=
  ⟨fun p hp hp2 => by
    show CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
    exact hY.1 p hp hp2, hY.2.of_mulEquiv e⟩

theorem sqtk_of_le [Finite Ω] {X Y : Subgroup Ω} (hX : SQTKGroup ↥X) (hYX : Y ≤ X) : SQTKGroup ↥Y :=
  sqtk_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hYX).symm
    ⟨sqt_subgroup hX.1 (Y.subgroupOf X), kGroup_subgroup hX.2 (Y.subgroupOf X)⟩

end SQTKTransport

section SecCtx

variable {V : Type} [CommGroup V] [Finite V] {G L A : Subgroup (MulAut V)} {W U : Subgroup V}

structure SecCtx (G L A : Subgroup (MulAut V)) (W U : Subgroup V) : Prop where
  hAG : A ≤ G
  hAel : IsElemAbelian2 A
  hAne : A ≠ ⊥
  hUW : U ≤ W
  hMW : L ⊔ A ≤ stabSub W
  hMU : L ⊔ A ≤ stabSub U
  hnc : ¬ commSub W L ≤ U

omit [Finite V] in
theorem SecCtx.hA2 (c : SecCtx G L A W U) : IsPGroup 2 A := c.hAel.isPGroup

omit [Finite V] in
theorem layer_eq_top_of_quasisimple {M : Type*} [Group M] (hM : CFSG.IsQuasisimple M) :
    CFSG.layer M = ⊤ :=
  CFSG.WholeGroup.layer_eq_top_of_isQuasisimple hM

omit [Finite V] in
theorem commutator_L_perfect (hLq : CFSG.IsQuasisimple ↥L) : ⁅L, L⁆ = L := by
  have : Group.IsPerfect ↥L := hLq.1
  exact Subgroup.commutator_eq_self

variable (h : B51Hyp G L) (c : SecCtx G L A W U)
include h c

theorem secKernel_le : (L ⊔ A) ⊓ centSec W U ≤ L ∧
    (L ⊔ A) ⊓ centSec W U ≤ Subgroup.centralizer (L : Set (MulAut V)) := by
  refine normal_le_of_not_ge h (le_sup_left : L ≤ L ⊔ A) (sup_normal_L h c.hAG)
    (sup_inf_centralizer_le h c.hAG c.hA2) inf_le_left ?_ ?_
  · intro m hm n hn
    exact ⟨(L ⊔ A).mul_mem ((L ⊔ A).mul_mem hm hn.1) ((L ⊔ A).inv_mem hm),
      conj_mem_centSec (c.hMW hm) (c.hMU hm) hn.2⟩
  · intro hLN
    apply c.hnc
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, hw, rfl⟩
    exact (hLN hx).2.2 w hw

theorem sec_A_inf_centSec : A ⊓ centSec W U = ⊥ := by
  have h1 := two_inf_centralizer_eq_bot h c.hAG c.hA2
  rw [eq_bot_iff, ← h1]
  exact fun x hx => ⟨hx.1, (secKernel_le h c).2 ⟨Subgroup.mem_sup_right hx.1, hx.2⟩⟩

theorem sec_lift_centralizer {x : MulAut (Sec W U)} (hx : x ∈ autSec (L ⊔ A) W U)
    (hc' : ∀ l ∈ autSec L W U, x * l = l * x) :
    ∃ m : ↥(L ⊔ A), (m : MulAut V) ∈ L ∧
      (m : MulAut V) ∈ Subgroup.centralizer (L : Set (MulAut V)) ∧
      secHom (L ⊔ A) c.hMW c.hMU m = x := by
  rw [← range_secHom (L ⊔ A) c.hMW c.hMU] at hx
  obtain ⟨m, rfl⟩ := hx
  have hcomm : ∀ l ∈ L, (m : MulAut V) * l = l * (m : MulAut V) := by
    refine commute_of_comm_central (commutator_L_perfect (quasi_L h))
      (sup_normal_L h c.hAG (m : MulAut V) m.2) (Z := (L ⊔ A) ⊓ centSec W U) ?_ ?_
    · intro z hz l hl
      exact (Subgroup.mem_centralizer_iff.1 ((secKernel_le h c).2 hz) l hl).symm
    · intro l hl
      have hlM : l ∈ L ⊔ A := Subgroup.mem_sup_left hl
      set lm : ↥(L ⊔ A) := ⟨l, hlM⟩ with hlm
      have hρl : secHom (L ⊔ A) c.hMW c.hMU lm ∈ autSec L W U := by
        rw [← map_secHom_eq_autSec (L ⊔ A) c.hMW c.hMU (le_sup_left : L ≤ L ⊔ A)]
        exact Subgroup.mem_map.2 ⟨lm, Subgroup.mem_subgroupOf.2 hl, rfl⟩
      have h1 := hc' _ hρl
      have hker : m * lm * m⁻¹ * lm⁻¹ ∈ (secHom (L ⊔ A) c.hMW c.hMU).ker := by
        rw [MonoidHom.mem_ker]
        simp only [map_mul, map_inv]
        rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
        exact h1
      have := (mem_ker_secHom (L ⊔ A) c.hMW c.hMU _).1 hker
      refine ⟨(L ⊔ A).mul_mem ((L ⊔ A).mul_mem ((L ⊔ A).mul_mem m.2 hlM) ((L ⊔ A).inv_mem m.2))
        ((L ⊔ A).inv_mem hlM), ?_⟩
      exact this
  have hcent : (m : MulAut V) ∈ Subgroup.centralizer (L : Set (MulAut V)) :=
    Subgroup.mem_centralizer_iff.2 fun l hl => (hcomm l hl).symm
  exact ⟨m, sup_inf_centralizer_le h c.hAG c.hA2 ⟨m.2, hcent⟩, hcent, rfl⟩

theorem isQuasisimple_secL : CFSG.IsQuasisimple ↥(autSec L W U) := by
  have hLM : L ≤ L ⊔ A := le_sup_left
  have hq := B1Red.isQuasisimple_to_open (quasi_L h)
  set ρ := secHom (L ⊔ A) c.hMW c.hMU with hρ
  have e : autSec L W U = (ρ.comp (Subgroup.inclusion hLM)).range := by
    rw [← map_secHom_eq_autSec (L ⊔ A) c.hMW c.hMU hLM]
    ext φ
    simp only [Subgroup.mem_map, MonoidHom.mem_range, MonoidHom.comp_apply, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
    · rintro ⟨l, rfl⟩
      exact ⟨Subgroup.inclusion hLM l, l.2, rfl⟩
  rw [e]
  refine B1Red.isQuasisimple_of_open
    (CFSG.ComponentClassification.Quasisimple.range_quasisimple_of_ker_ne_top hq _ ?_)
  intro htop
  apply c.hnc
  rw [commSub, Subgroup.closure_le]
  rintro _ ⟨x, hx, w, hw, rfl⟩
  have hx' : (⟨x, hx⟩ : ↥L) ∈ (ρ.comp (Subgroup.inclusion hLM)).ker := by rw [htop]; trivial
  rw [MonoidHom.mem_ker] at hx'
  have h1 : (Subgroup.inclusion hLM ⟨x, hx⟩) ∈ ρ.ker := hx'
  exact ((mem_ker_secHom (L ⊔ A) c.hMW c.hMU _).1 h1).2 w hw

theorem secX_conj {y l : MulAut (Sec W U)} (hy : y ∈ autSec (L ⊔ A) W U)
    (hl : l ∈ autSec L W U) : y * l * y⁻¹ ∈ autSec L W U := by
  have hmapL := map_secHom_eq_autSec (L ⊔ A) c.hMW c.hMU (le_sup_left : L ≤ L ⊔ A)
  rw [← range_secHom (L ⊔ A) c.hMW c.hMU] at hy
  obtain ⟨m, rfl⟩ := hy
  rw [← hmapL] at hl ⊢
  obtain ⟨l₀, hl₀, rfl⟩ := Subgroup.mem_map.1 hl
  refine Subgroup.mem_map.2 ⟨m * l₀ * m⁻¹, ?_, by simp only [map_mul, map_inv]⟩
  rw [Subgroup.mem_subgroupOf] at hl₀ ⊢
  exact sup_normal_L h c.hAG (m : MulAut V) m.2 _ hl₀

theorem secX_sq {y : MulAut (Sec W U)} (hy : y ∈ autSec (L ⊔ A) W U) :
    y ^ 2 ∈ autSec L W U := by
  have hmapL := map_secHom_eq_autSec (L ⊔ A) c.hMW c.hMU (le_sup_left : L ≤ L ⊔ A)
  rw [← range_secHom (L ⊔ A) c.hMW c.hMU] at hy
  obtain ⟨m, rfl⟩ := hy
  rw [← hmapL]
  refine Subgroup.mem_map.2 ⟨m ^ 2, ?_, by simp only [map_pow]⟩
  rw [Subgroup.mem_subgroupOf]
  have hAnL : A ≤ Subgroup.normalizer (L : Set (MulAut V)) := hTn_of h c.hAG
  exact B1Red.sq_mem_of_mem_sup hAnL c.hAel.2 (m : MulAut V) m.2

theorem secY_facts {Y : Subgroup (MulAut (Sec W U))} (hLY : autSec L W U ≤ Y)
    (hYX : Y ≤ autSec (L ⊔ A) W U) :
    pCoreOf 2 Y = ⊥ ∧ quasithinGenFitting Y = autSec L W U ∧ centerOf Y ≤ autSec L W U ∧
      (∀ x ∈ Y, (∀ l ∈ autSec L W U, x * l = l * x) → x ∈ autSec L W U ∧ Odd (orderOf x)) := by
  have hmapL := map_secHom_eq_autSec (L ⊔ A) c.hMW c.hMU (le_sup_left : L ≤ L ⊔ A)
  have hn : ∀ y ∈ Y, ∀ l ∈ autSec L W U, y * l * y⁻¹ ∈ autSec L W U := fun y hy l hl =>
    secX_conj h c (hYX hy) hl
  have h2 : ∀ y ∈ Y, y ^ 2 ∈ autSec L W U := fun y hy => secX_sq h c (hYX hy)
  have hd : ∀ x ∈ Y, (∀ l ∈ autSec L W U, x * l = l * x) →
      x ∈ autSec L W U ∧ Odd (orderOf x) := by
    intro x hx hcomm
    obtain ⟨m, hmL, hmc, rfl⟩ := sec_lift_centralizer h c (hYX hx) hcomm
    refine ⟨?_, ?_⟩
    · rw [← hmapL]
      exact Subgroup.mem_map.2 ⟨m, Subgroup.mem_subgroupOf.2 hmL, rfl⟩
    · have hmG : (m : MulAut V) ∈ G := (sup_le (le_G h) c.hAG) m.2
      have hodd : Odd (orderOf (m : MulAut V)) := odd_orderOf_of_mem_centralizer h hmG hmc
      rw [Subgroup.orderOf_coe] at hodd
      exact Odd.of_dvd_nat hodd (orderOf_map_dvd _ m)
  obtain ⟨h1, h2', h3⟩ := section_group_facts hLY
    (B1Red.isQuasisimple_to_open (isQuasisimple_secL h c)) hn h2 hd
  exact ⟨h1, h2', h3, hd⟩

theorem sqtk_secX (hA21 : AsA21SQTKSection) : SQTKGroup ↥(autSec (L ⊔ A) W U) := by
  have hM := sqtk_sup h c.hAG c.hA2
  set X := autSec (L ⊔ A) W U with hXdef
  have hmem : ∀ g : ↥(L ⊔ A), secHom (L ⊔ A) c.hMW c.hMU g ∈ X := fun g => by
    rw [hXdef, ← range_secHom (L ⊔ A) c.hMW c.hMU]; exact ⟨g, rfl⟩
  let π : ↥(⊤ : Subgroup ↥(L ⊔ A)) →* ↥X :=
    ((secHom (L ⊔ A) c.hMW c.hMU).codRestrict X hmem).comp (⊤ : Subgroup ↥(L ⊔ A)).subtype
  have hπ : Function.Surjective π := by
    intro y
    have hy : (y : MulAut (Sec W U)) ∈ (secHom (L ⊔ A) c.hMW c.hMU).range := by
      rw [range_secHom]; exact y.2
    obtain ⟨g, hg⟩ := hy
    exact ⟨⟨g, trivial⟩, Subtype.ext hg⟩
  have hLX : autSec L W U ≤ X := autSec_mono le_sup_left W U
  let Lb : Subgroup ↥X := (autSec L W U).subgroupOf X
  have hLbn : Lb.Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using secX_conj h c g.2 hx⟩
  have hLq : CFSG.IsQuasisimple ↥Lb :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLX).symm
      (isQuasisimple_secL h c)
  have hlayer : CFSG.layer ↥Lb = ⊤ := layer_eq_top_of_quasisimple hLq
  have h2 : IsPGroup 2 (↥X ⧸ Lb) := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨1, ?_⟩
    show (QuotientGroup.mk y : ↥X ⧸ Lb) ^ (2 ^ 1) = 1
    rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact secX_sq h c y.2
  exact hA21 ↥(L ⊔ A) hM ⊤ ↥X π hπ Lb hlayer h2

theorem sqtk_secL (hA21 : AsA21SQTKSection) : SQTKGroup ↥(autSec L W U) :=
  sqtk_of_le (sqtk_secX h c hA21) (autSec_mono le_sup_left W U)

theorem isA2_secA : IsA2 (autSec (L ⊔ A) W U) (autSec A W U) := by
  have hmapA := map_secHom_eq_autSec (L ⊔ A) c.hMW c.hMU (le_sup_right : A ≤ L ⊔ A)
  refine ⟨autSec_mono le_sup_right W U, ?_, ?_, ?_⟩
  · intro hbot
    have hcard := card_autSec_mul (A := A) (le_sup_right.trans c.hMW) (le_sup_right.trans c.hMU)
    rw [sec_A_inf_centSec h c, Subgroup.card_bot, mul_one, hbot, Subgroup.card_bot] at hcard
    exact c.hAne (Subgroup.card_eq_one.1 hcard.symm)
  · intro φ hφ ψ hψ
    rw [← hmapA] at hφ hψ
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hφ
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hψ
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (c.hAel.1 _ (Subgroup.mem_subgroupOf.1 ha) _ (Subgroup.mem_subgroupOf.1 hb))
  · intro φ hφ
    rw [← hmapA] at hφ
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hφ
    rw [← map_pow]
    have : a ^ 2 = 1 := Subtype.ext (c.hAel.2 _ (Subgroup.mem_subgroupOf.1 ha))
    rw [this, map_one]

omit [Finite V] h in
theorem isQuadratic_secA (hq : IsQuadratic A) : IsQuadratic (autSec A W U) := by
  have hmapA := map_secHom_eq_autSec (L ⊔ A) c.hMW c.hMU (le_sup_right : A ≤ L ⊔ A)
  rw [IsQuadratic, commV, Subgroup.closure_le]
  rintro _ ⟨φ, hφ, s, rfl⟩
  rw [← hmapA] at hφ
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hφ
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective s
  intro ψ hψ
  rw [← hmapA] at hψ
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hψ
  have ha' : (a : MulAut V) ∈ A := Subgroup.mem_subgroupOf.1 ha
  have hb' : (b : MulAut V) ∈ A := Subgroup.mem_subgroupOf.1 hb
  have hfix : (b : MulAut V) ((a : MulAut V) (w : V) * (w : V)⁻¹) =
      (a : MulAut V) (w : V) * (w : V)⁻¹ := hq (Subgroup.subset_closure ⟨a, ha', w, rfl⟩) b hb'
  have hW' : ∀ g : ↥(L ⊔ A), ∀ w : ↥W, (g : MulAut V) (w : V) ∈ W := fun g w => (c.hMW g.2 w).2 w.2
  set x : ↥W := ⟨(a : MulAut V) (w : V), hW' a w⟩ * w⁻¹ with hx
  have hxV : ((x : ↥W) : V) = (a : MulAut V) (w : V) * (w : V)⁻¹ := rfl
  have hLHS : (secHom (L ⊔ A) c.hMW c.hMU a) (QuotientGroup.mk w) * (QuotientGroup.mk w)⁻¹ =
      (QuotientGroup.mk x : Sec W U) := by
    rw [secHom_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
  show (secHom (L ⊔ A) c.hMW c.hMU b)
      ((secHom (L ⊔ A) c.hMW c.hMU a) (QuotientGroup.mk w) * (QuotientGroup.mk w)⁻¹) =
    (secHom (L ⊔ A) c.hMW c.hMU a) (QuotientGroup.mk w) * (QuotientGroup.mk w)⁻¹
  rw [hLHS, secHom_mk]
  congr 1
  apply Subtype.ext
  show (b : MulAut V) ((x : ↥W) : V) = ((x : ↥W) : V)
  rw [hxV]
  exact hfix

theorem qOf_secX_le (hq : IsQuadratic A) :
    qOf (autSec (L ⊔ A) W U) ≤ ((rAV (autSec A W U) : ℚ) : WithTop ℚ) :=
  qOf_le_iff.2 ⟨autSec A W U, isA2_secA h c, isQuadratic_secA c hq, le_rfl⟩

theorem b4Hyp_sec' (hA21 : AsA21SQTKSection)
    (hirr : XMod.IsIrrSec ↥(autSec L W U) (⊥ : Subgroup (Sec W U)) ⊤) :
    B4Hyp (autSec (L ⊔ A) W U) (autSec L W U) := by
  have hLX : autSec L W U ≤ autSec (L ⊔ A) W U := autSec_mono le_sup_left W U
  exact ⟨sqtk_secX h c hA21, ((secY_facts h c hLX le_rfl).2.1).symm, isQuasisimple_secL h c, hirr⟩

theorem b4Hyp_sec (hA21 : AsA21SQTKSection) (hlt : U < W)
    (hirr : ∀ J : Subgroup V, (∀ x ∈ L, ∀ w ∈ J, x w ∈ J) → U ≤ J → J ≤ W → J = U ∨ J = W) :
    B4Hyp (autSec (L ⊔ A) W U) (autSec L W U) :=
  b4Hyp_sec' h c hA21 (isIrrSec_autSec hlt hirr (le_sup_left.trans c.hMW) (le_sup_left.trans c.hMU))

omit [Finite V] h in
theorem isIrrSec_secX (hlt : U < W)
    (hch : ∀ X : Subgroup V, L ⊔ A ≤ stabSub X → U ≤ X → X ≤ W → X = U ∨ X = W) :
    XMod.IsIrrSec ↥(autSec (L ⊔ A) W U) (⊥ : Subgroup (Sec W U)) ⊤ :=
  isIrrSec_autSec hlt (fun J hJ hUJ hJW => hch J (fun x hx => mem_stabSub_of_inv (hJ x hx)
    (hJ x⁻¹ ((L ⊔ A).inv_mem hx))) hUJ hJW) c.hMW c.hMU

theorem isIrrSec_secL_of_irrPlus
    (hM : XMod.IsIrrSec ↥(autSec (L ⊔ A) W U) (⊥ : Subgroup (Sec W U)) ⊤)
    (hI : commV (autSec L W U) ∈ IrrPlus (autSec L W U) (⊤ : Subgroup (Sec W U))) :
    XMod.IsIrrSec ↥(autSec L W U) (⊥ : Subgroup (Sec W U)) ⊤ := by
  obtain ⟨hinv, hcomm, hlt, hirr⟩ := irr_data hI
  obtain ⟨hbt, hM2⟩ := hM
  have hcom : commV (autSec L W U) = ⊤ := by
    have h1 := hM2 (commV (autSec L W U)) (fun g w hw => commV_inv (fun l hl => secX_conj h c g.2 hl) w hw)
      bot_le le_top
    rcases h1 with h1 | h1
    · exfalso
      have : commV (autSec L W U) ⊓ fixV (autSec L W U) < commV (autSec L W U) := hlt
      rw [h1, bot_inf_eq] at this
      exact lt_irrefl _ this
    · exact h1
  have hfix : fixV (autSec L W U) = ⊥ := by
    have h1 := hM2 (fixV (autSec L W U)) (fun g w hw => by
      refine fixV_inv (fun l hl => ?_) w hw
      have := secX_conj h c ((autSec (L ⊔ A) W U).inv_mem g.2) hl
      simpa using this) bot_le le_top
    rcases h1 with h1 | h1
    · exact h1
    · exfalso
      have : commV (autSec L W U) ⊓ fixV (autSec L W U) < commV (autSec L W U) := hlt
      rw [h1, inf_top_eq] at this
      exact lt_irrefl _ this
  rw [hcom, hfix, inf_bot_eq] at hirr
  exact ⟨hbt, fun J' hJ' _ _ => hirr J' (fun x hx w hw => hJ' ⟨x, hx⟩ w hw) bot_le le_top⟩

theorem b51Hyp_secY (hA21 : AsA21SQTKSection) {B : Subgroup (MulAut (Sec W U))}
    (hB : IsFFStarOffender (autSec (L ⊔ A) W U) B) :
    B51Hyp (autSec L W U ⊔ B) (autSec L W U) := by
  have hLX : autSec L W U ≤ autSec (L ⊔ A) W U := autSec_mono le_sup_left W U
  set Lb := autSec L W U with hLb
  set Y := Lb ⊔ B with hY
  have hYX : Y ≤ autSec (L ⊔ A) W U := sup_le hLX hB.1
  obtain ⟨hO2, hF, hZ, hd⟩ := secY_facts h c (le_sup_left : Lb ≤ Y) hYX
  have hLq := isQuasisimple_secL h c
  have hBY : IsFFStarOffender Y B := ⟨le_sup_right, hB.2.1, hB.2.2.1, hB.2.2.2⟩
  have hJle : ffJ Y ≤ Y := iSup₂_le fun A' hA' => hA'.1
  have hBJ : B ≤ ffJ Y := B6.le_ffJ hBY
  have hJn : ∀ y ∈ Y, ∀ j ∈ ffJ Y, y * j * y⁻¹ ∈ ffJ Y := fun y hy j hj =>
    (Subgroup.mem_normalizer_iff.1 (B6.le_normalizer_ffJ Y hy) j).1 hj
  have hBn : ∀ b ∈ B, ∀ l ∈ Lb, b * l * b⁻¹ ∈ Lb := fun b hb l hl =>
    secX_conj h c (hYX (Subgroup.mem_sup_right hb)) hl
  have hLJ : Lb ≤ ffJ Y := by
    have hq' := B1Red.isQuasisimple_to_open hLq
    have hDnorm : ((ffJ Y ⊓ Lb).subgroupOf Lb).Normal := by
      refine ⟨fun x hx g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact ⟨by simpa using hJn (g : MulAut (Sec W U)) (Subgroup.mem_sup_left g.2) x hx.1,
        by simpa using Lb.mul_mem (Lb.mul_mem g.2 hx.2) (Lb.inv_mem g.2)⟩
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq'
      ((ffJ Y ⊓ Lb).subgroupOf Lb) with hc' | htop
    · exfalso
      have hcen : ∀ z ∈ ffJ Y ⊓ Lb, ∀ l ∈ Lb, z * l = l * z := by
        intro z hz l hl
        have hmem : (⟨z, hz.2⟩ : ↥Lb) ∈ (ffJ Y ⊓ Lb).subgroupOf Lb := hz
        have := Subgroup.mem_center_iff.mp (hc' hmem) ⟨l, hl⟩
        exact (congrArg Subtype.val this).symm
      have hBc : ∀ b ∈ B, ∀ l ∈ Lb, b * l = l * b := by
        intro b hb
        refine commute_of_comm_central (commutator_L_perfect' hLq) (hBn b hb) hcen ?_
        intro l hl
        have h1 : ⁅b, l⁆ ∈ Lb := by
          rw [commutatorElement_def]
          exact Lb.mul_mem (hBn b hb l hl) (Lb.inv_mem hl)
        have h2 : ⁅b, l⁆ ∈ ffJ Y := by
          have e : ⁅b, l⁆ = (l * b * l⁻¹ * b⁻¹)⁻¹ := by rw [commutatorElement_def]; group
          rw [e]
          exact (ffJ Y).inv_mem ((ffJ Y).mul_mem (hJn l (Subgroup.mem_sup_left hl) b (hBJ hb))
            ((ffJ Y).inv_mem (hBJ hb)))
        exact ⟨h2, h1⟩
      apply hB.2.1
      rw [eq_bot_iff]
      intro b hb
      obtain ⟨-, hodd⟩ := hd b (Subgroup.mem_sup_right hb) (hBc b hb)
      exact Subgroup.mem_bot.2 (eq_one_of_pgroup_of_odd_orderOf hB.2.2.1.isPGroup hb hodd)
    · intro l hl
      have : (⟨l, hl⟩ : ↥Lb) ∈ (ffJ Y ⊓ Lb).subgroupOf Lb := by rw [htop]; trivial
      exact (Subgroup.mem_subgroupOf.1 this).1
  refine ⟨?_, hLq, sqtk_secL h c hA21, le_sup_left, hO2, le_antisymm (sup_le hLJ hBJ) hJle⟩
  rw [hF]
  exact (sup_eq_left.2 hZ).symm

end SecCtx



end B5

end CFSG.Quasithin

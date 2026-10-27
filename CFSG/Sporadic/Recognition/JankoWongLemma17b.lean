module

public import CFSG.Sporadic.Recognition.JankoWongLemma17
public import CFSG.Sporadic.Recognition.JankoWongMStructure
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Equiv Equiv.Perm Subgroup CFSG.GH74 CFSG.GH74.GLS CFSG.Open

section Abstract

theorem card_le_three_mul_card_inf {K : Type*} [Group K] [Finite K] {M R : Subgroup K}
    [M.Normal] (hR : IsPGroup 3 R) (hK : Nat.card K = 120 * Nat.card M) :
    Nat.card R ≤ 3 * Nat.card ↥(R ⊓ M) := by
  have hpos : 0 < Nat.card M := Nat.card_pos
  have hidx : M.index = 120 := by
    have h1 : Nat.card M * M.index = Nat.card M * 120 := by
      rw [Subgroup.card_mul_index, hK]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos h1
  have hrel : M.relIndex (R ⊔ M) = M.relIndex R := Subgroup.relIndex_sup_right R M
  have hdvd : M.relIndex (R ⊔ M) ∣ M.index := Subgroup.relIndex_dvd_index_of_le le_sup_right
  rw [hrel, hidx] at hdvd
  have e : M.relIndex R * Nat.card ↥(M ⊓ R) = Nat.card R := Subgroup.relIndex_mul_card M R
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR
  have hd3 : M.relIndex R ∣ 3 ^ k := Dvd.intro _ (e.trans hk)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd3
  have hj1 : j ≤ 1 := by
    by_contra h
    have h2 : 3 ^ 2 ∣ 3 ^ j := pow_dvd_pow 3 (by omega)
    rw [← hj] at h2
    have := h2.trans hdvd
    norm_num at this
  have hle : M.relIndex R ≤ 3 := by
    rw [hj]
    calc 3 ^ j ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hj1
      _ = 3 := by norm_num
  rw [inf_comm] at e
  calc Nat.card R = M.relIndex R * Nat.card ↥(R ⊓ M) := e.symm
    _ ≤ 3 * Nat.card ↥(R ⊓ M) := Nat.mul_le_mul_right _ hle

end Abstract

theorem factorization_three_120 : (120 : ℕ).factorization 3 = 1 := by
  have : (120 : ℕ) = 3 ^ 1 * 40 := by norm_num
  rw [this, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three]
  have h : (40 : ℕ).factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  simp [h]

namespace Setup

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {S : Setup G} (c : Ctx S)

theorem aK_cube : c.aK ^ 3 = 1 := Subtype.ext (by
  have := congrArg Subtype.val c.ha3
  simpa [Ctx.aK] using this)

theorem aK_ne_one : c.aK ≠ 1 := fun e => by
  have h1 : c.a = 1 := Subtype.ext (congrArg (fun y : ↥c.Kg => (y : G)) e)
  exact permA3_ne_one (by rw [← c.ha, h1, map_one])

theorem aK_central : ∀ k : ↥c.Kg, k * c.aK = c.aK * k := fun k =>
  Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp k.2)

theorem zK_sq : c.zK ^ 2 = 1 := by
  have := c.orderOf_zK
  rw [← this]; exact pow_orderOf_eq_one c.zK

theorem mem_zpowers_aK_comm {m : ↥c.Kg} (hm : m ∈ zpowers c.aK) (k : ↥c.Kg) :
    k * m = m * k := by
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hm
  exact (Commute.zpow_right (show Commute k c.aK from c.aK_central k) j).eq

theorem mem_zpowers_aK_cube {m : ↥c.Kg} (hm : m ∈ zpowers c.aK) : m ^ 3 = 1 := by
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hm
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, c.aK_cube, one_zpow]

theorem exists_five_Kg :
    ∃ r₁ r₂ : ↥c.Kg, orderOf r₁ = 5 ∧ orderOf r₂ = 5 ∧ (r₁ * r₂) ^ 2 = c.zK := by
  obtain ⟨r₁, r₂, hr₁, hr₂, hr₁a, hr₂a, hr₁₂⟩ := c.exists_five_elements
  have hr₁K : (r₁ : G) ∈ c.Kg :=
    Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hr₁a)
  have hr₂K : (r₂ : G) ∈ c.Kg :=
    Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hr₂a)
  have hord : ∀ r : S.H, orderOf r = 5 → ∀ hr : (r : G) ∈ c.Kg,
      orderOf (⟨(r : G), hr⟩ : ↥c.Kg) = 5 := fun r h5 hr => by
    rw [← Subgroup.orderOf_coe (⟨(r : G), hr⟩ : ↥c.Kg)]
    show orderOf ((r : S.H) : G) = 5
    rw [Subgroup.orderOf_coe]; exact h5
  refine ⟨⟨(r₁ : G), hr₁K⟩, ⟨(r₂ : G), hr₂K⟩, hord r₁ hr₁ hr₁K, hord r₂ hr₂ hr₂K, ?_⟩
  exact Subtype.ext (by
    have := congrArg Subtype.val hr₁₂
    simp only [pow_two, Subgroup.coe_mul] at this ⊢
    exact this)

theorem bsStructure :
    Nat.card ↥c.Kg * 3 = Nat.card (CFSG.oddCore ↥c.Kg) * 360 ∧
    zpowers c.aK ≤ CFSG.oddCore ↥c.Kg ∧
    CFSG.oddCore ↥c.Kg ⊓ centralizer ({c.zK} : Set ↥c.Kg) = zpowers c.aK ∧
    (∀ m ∈ CFSG.oddCore ↥c.Kg, ∀ n ∈ CFSG.oddCore ↥c.Kg, m * n * m⁻¹ * n⁻¹ ∈ zpowers c.aK) ∧
    (∀ m ∈ CFSG.oddCore ↥c.Kg, c.zK * m * c.zK⁻¹ * m ∈ zpowers c.aK) := by
  obtain ⟨r₁, r₂, hr₁, hr₂, hr₁₂⟩ := c.exists_five_Kg
  exact brauerSuzuki_structure c.aK_cube c.aK_ne_one c.aK_central c.zK_sq c.hBS_Kg
    c.card_centralizer_zK (fun W hW hn hodd => c.odd_normal_le_zpowers_aK hW hn hodd)
    hr₁ hr₂ hr₁₂

theorem card_Kg_eq : Nat.card ↥c.Kg = 120 * Nat.card (CFSG.oddCore ↥c.Kg) := by
  have := c.bsStructure.1
  omega

theorem aK_mem_oddCore : c.aK ∈ CFSG.oddCore ↥c.Kg :=
  c.bsStructure.2.1 (Subgroup.mem_zpowers _)

theorem OG_le_Kg
    : c.OG ≤ c.Kg := fun y hy =>
  Subgroup.mem_centralizer_singleton_iff.mpr (c.OG_comm y hy _ c.aG_mem_OG)

theorem factorization_three_oddCore
    {W : Subgroup G} (hW : c.IsW W) :
    (Nat.card (CFSG.oddCore ↥c.Kg)).factorization 3 = 5 := by
  have h := c.card_Kg_eq
  have hMne : Nat.card (CFSG.oddCore ↥c.Kg) ≠ 0 := Nat.card_pos.ne'
  have h3 : (Nat.card ↥c.Kg).factorization 3 = 6 := hW.factorization_three_Kg
  rw [h, Nat.factorization_mul (by norm_num) hMne, Finsupp.add_apply,
    factorization_three_120] at h3
  omega

theorem card_MG_inf_OG
    : 27 ≤ Nat.card ↥(c.MG ⊓ c.OG) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hMn := CFSG.oddCore_normal ↥c.Kg
  set NK : Subgroup ↥c.Kg := c.OG.subgroupOf c.Kg with hNK
  have hNKp : IsPGroup 3 NK :=
    c.isPGroup_three_OG.of_equiv (Subgroup.subgroupOfEquivOfLe c.OG_le_Kg).symm
  have hNKcard : Nat.card NK = 81 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe c.OG_le_Kg).toEquiv, c.card_OG_eq_81]
  have h1 := card_le_three_mul_card_inf (M := CFSG.oddCore ↥c.Kg) (R := NK) hNKp c.card_Kg_eq
  set R₀ : Subgroup G := (NK ⊓ CFSG.oddCore ↥c.Kg).map c.Kg.subtype with hR₀
  have hR₀card : Nat.card R₀ = Nat.card ↥(NK ⊓ CFSG.oddCore ↥c.Kg) :=
    Subgroup.card_map_of_injective c.Kg.subtype_injective
  have hR₀le : R₀ ≤ c.MG ⊓ c.OG := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy.2, rfl⟩, hy.1⟩
  have := Subgroup.card_le_of_le hR₀le
  omega

theorem exists_mem_MG_OG_ocl_s
    : ∃ y ∈ c.MG, y ∈ c.OG ∧ y ∈ c.ocl c.s := by
  obtain ⟨y, hy, hys⟩ := c.exists_mem_ocl_s_of_card (R := c.MG ⊓ c.OG) inf_le_right
    (by have := c.card_MG_inf_OG; omega)
  exact ⟨y, hy.1, hy.2, hys⟩

theorem MG_comm_mem_zpowers {m n : G} (hm : m ∈ c.MG) (hn : n ∈ c.MG) :
    m * n * m⁻¹ * n⁻¹ ∈ zpowers (c.a : G) := by
  obtain ⟨hmK, hm'⟩ := c.mem_MG_iff.mp hm
  obtain ⟨hnK, hn'⟩ := c.mem_MG_iff.mp hn
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (c.bsStructure.2.2.2.1 _ hm' _ hn')
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  have := congrArg Subtype.val hk
  simpa [Ctx.aK] using this

theorem isPGroup_three_oddCore
    {W : Subgroup G} (hW : c.IsW W) :
    IsPGroup 3 (CFSG.oddCore ↥c.Kg) ∧ Nat.card (CFSG.oddCore ↥c.Kg) = 3 ^ 5 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hMne : Nat.card (CFSG.oddCore ↥c.Kg) ≠ 0 := Nat.card_pos.ne'
  have hModd : Odd (Nat.card (CFSG.oddCore ↥c.Kg)) :=
    CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd
  obtain ⟨s', hs'MG, -, hs'ocl⟩ := c.exists_mem_MG_OG_ocl_s
  have hall : ∀ {r : ℕ}, r.Prime → r ∣ Nat.card (CFSG.oddCore ↥c.Kg) → r = 3 := by
    intro r hr hrdvd
    by_contra hr3
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(CFSG.oddCore ↥c.Kg)) r hrdvd
    have hyMG : ((y : ↥c.Kg) : G) ∈ c.MG := ⟨(y : ↥c.Kg), y.2, rfl⟩
    have hyr : ((y : ↥c.Kg) : G) ^ r = 1 := by
      have h1 : y ^ r = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
      have := congrArg (fun t : ↥(CFSG.oddCore ↥c.Kg) => ((t : ↥c.Kg) : G)) h1
      simpa using this
    have hyorder : orderOf ((y : ↥c.Kg) : G) = r := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hy]
    have hr3' : ¬ 3 ∣ r := fun h => hr3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).mp h).symm
    have hcomm : s' * ((y : ↥c.Kg) : G) = ((y : ↥c.Kg) : G) * s' :=
      commute_of_coprime_of_commutator_mem_zpowers c.aG_cube
        (Subgroup.mem_centralizer_singleton_iff.mp (c.MG_le_Kg hs'MG))
        (Subgroup.mem_centralizer_singleton_iff.mp (c.MG_le_Kg hyMG))
        (c.MG_comm_mem_zpowers hs'MG hyMG) hyr hr3'
    obtain ⟨g, -, hgs⟩ := hs'ocl
    have hcentcard : Nat.card (centralizer ({s'} : Set G)) = 972 := by
      have hconj : IsConj c.s s' := isConj_iff.mpr ⟨g, hgs.symm⟩
      rw [← card_centralizer_eq_of_isConj hconj]
      exact c.lemma14.2.1
    have hyc : ((y : ↥c.Kg) : G) ∈ centralizer ({s'} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm
    have hdvd : r ∣ 972 := by
      have h1 := orderOf_dvd_natCard (⟨((y : ↥c.Kg) : G), hyc⟩ : ↥(centralizer ({s'} : Set G)))
      rw [Subgroup.orderOf_mk, hyorder, hcentcard] at h1
      exact h1
    have hdvd' : r ∣ 2 ^ 2 * 3 ^ 5 := by norm_num; exact hdvd
    have hr2 : r ≠ 2 := fun h => by
      have := Odd.of_dvd_nat hModd hrdvd
      rw [h] at this
      exact absurd this (by decide)
    rcases (Nat.Prime.dvd_mul hr).mp hdvd' with h | h
    · exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h))
    · exact hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp (hr.dvd_of_dvd_pow h))
  have hcardpow : Nat.card (CFSG.oddCore ↥c.Kg) = 3 ^ 5 := by
    have h := Nat.eq_prime_pow_of_unique_prime_dvd hMne (fun {d} hd hdvd => hall hd hdvd)
    obtain ⟨L, hL⟩ : ∃ L : ℕ, Nat.card (CFSG.oddCore ↥c.Kg) = 3 ^ L := ⟨_, h⟩
    have h5 := c.factorization_three_oddCore hW
    rw [hL, Nat.Prime.factorization_pow Nat.prime_three] at h5
    simp at h5
    rw [hL, h5]
  exact ⟨IsPGroup.of_card hcardpow, hcardpow⟩

theorem MG_le_W
    {W : Subgroup G} (hW : c.IsW W) : c.MG ≤ W := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hMp, -⟩ := c.isPGroup_three_oddCore hW
  have hWK : W ≤ c.Kg := hW.le_Kg
  have hWKcard : Nat.card (W.subgroupOf c.Kg) = 3 ^ (Nat.card ↥c.Kg).factorization 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWK).toEquiv, hW.card,
      hW.factorization_three_Kg]
  let SW : Sylow 3 ↥c.Kg := Sylow.ofCard (W.subgroupOf c.Kg) hWKcard
  have := CFSG.oddCore_normal ↥c.Kg
  have h1 : CFSG.oddCore ↥c.Kg ≤ (SW : Subgroup ↥c.Kg) := hMp.le_sylow_of_normal SW
  intro m hm
  obtain ⟨hmK, hmq⟩ := c.mem_MG_iff.mp hm
  have h2 : (⟨m, hmK⟩ : ↥c.Kg) ∈ (SW : Subgroup ↥c.Kg) := h1 hmq
  have h3 : (⟨m, hmK⟩ : ↥c.Kg) ∈ W.subgroupOf c.Kg := by
    simpa [SW, Sylow.coe_ofCard] using h2
  exact Subgroup.mem_subgroupOf.mp h3

theorem MG_not_abelian
    {W : Subgroup G} (hW : c.IsW W) : ¬ ∀ m ∈ c.MG, ∀ n ∈ c.MG, m * n = n * m := fun h =>
  hW.not_abelian_of_card (A := c.MG) (c.MG_le_W hW)
    (by rw [c.card_MG, (c.isPGroup_three_oddCore hW).2]) h

theorem normal_between
    {W : Subgroup G} (hW : c.IsW W) {D : Subgroup ↥c.Kg} (hDn : D.Normal) (haD : c.aK ∈ D)
    (hDM : D ≤ CFSG.oddCore ↥c.Kg) : D = zpowers c.aK ∨ D = CFSG.oddCore ↥c.Kg := by
  obtain ⟨hMp, hMcard⟩ := c.isPGroup_three_oddCore hW
  obtain ⟨r₁, r₂, hr₁, hr₂, hr₁₂⟩ := c.exists_five_Kg
  exact eq_zpowers_or_eq_oddCore_of_normal c.aK_cube c.aK_ne_one c.aK_central c.zK_sq
    c.hBS_Kg c.card_centralizer_zK
    (fun W hW hn hodd => c.odd_normal_le_zpowers_aK hW hn hodd) hr₁ hr₂ hr₁₂ hMp hMcard hDn haD
    hDM

theorem center_MG
    {W : Subgroup G} (hW : c.IsW W) :
    ∀ m ∈ c.MG, (∀ n ∈ c.MG, m * n = n * m) ↔ m ∈ zpowers (c.a : G) := by
  have hMn := CFSG.oddCore_normal ↥c.Kg
  set Zq : Subgroup ↥c.Kg :=
    CFSG.oddCore ↥c.Kg ⊓ centralizer (CFSG.oddCore ↥c.Kg : Set ↥c.Kg) with hZq
  have hZn : Zq.Normal := ⟨fun x hx k => by
    obtain ⟨hxM, hxc⟩ := hx
    refine ⟨hMn.conj_mem x hxM k, Subgroup.mem_centralizer_iff.mpr (fun m hm => ?_)⟩
    have hm' : k⁻¹ * m * k ∈ CFSG.oddCore ↥c.Kg := by
      have := hMn.conj_mem m hm k⁻¹
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp hxc _ hm'
    calc m * (k * x * k⁻¹) = k * ((k⁻¹ * m * k) * x) * k⁻¹ := by group
      _ = k * (x * (k⁻¹ * m * k)) * k⁻¹ := by rw [h1]
      _ = k * x * k⁻¹ * m := by group⟩
  have haZ : c.aK ∈ Zq := ⟨c.aK_mem_oddCore,
    Subgroup.mem_centralizer_iff.mpr fun m _ => c.aK_central m⟩
  rcases c.normal_between hW hZn haZ inf_le_left with h | h
  · intro m hm
    obtain ⟨hmK, hmq⟩ := c.mem_MG_iff.mp hm
    constructor
    · intro hmc
      have hmZ : (⟨m, hmK⟩ : ↥c.Kg) ∈ Zq := by
        refine ⟨hmq, Subgroup.mem_centralizer_iff.mpr (fun n hn => ?_)⟩
        have hnMG : (n : G) ∈ c.MG := c.mem_MG_iff.mpr ⟨n.2, hn⟩
        exact Subtype.ext (hmc _ hnMG).symm
      rw [h] at hmZ
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmZ
      refine Subgroup.mem_zpowers_iff.mpr ⟨j, ?_⟩
      have := congrArg Subtype.val hj
      simpa [Ctx.aK] using this
    · intro hma n hn
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hma
      exact (Commute.zpow_left (show Commute (c.a : G) n from
        (Subgroup.mem_centralizer_singleton_iff.mp (c.MG_le_Kg hn)).symm) j).eq
  · exfalso
    refine c.MG_not_abelian hW (fun m hm n hn => ?_)
    obtain ⟨hmK, hmq⟩ := c.mem_MG_iff.mp hm
    obtain ⟨hnK, hnq⟩ := c.mem_MG_iff.mp hn
    have hmZ : (⟨m, hmK⟩ : ↥c.Kg) ∈ Zq := by rw [h]; exact hmq
    have := Subgroup.mem_centralizer_iff.mp hmZ.2 _ hnq
    exact (congrArg Subtype.val this).symm

@[expose] def OmegaM : Subgroup ↥c.Kg where
  carrier := {x | x ∈ CFSG.oddCore ↥c.Kg ∧ x ^ 3 = 1}
  mul_mem' := by
    rintro x y ⟨hx, hx3⟩ ⟨hy, hy3⟩
    refine ⟨(CFSG.oddCore ↥c.Kg).mul_mem hx hy, ?_⟩
    have hc := c.bsStructure.2.2.2.1 y hy x hx
    have hyx : y * x = (y * x * y⁻¹ * x⁻¹) * (x * y) := by group
    rw [mul_pow_three_of_central_commutator hyx (c.mem_zpowers_aK_comm hc x)
      (c.mem_zpowers_aK_comm hc y) (c.mem_zpowers_aK_cube hc), hx3, hy3, one_mul]
  one_mem' := ⟨(CFSG.oddCore ↥c.Kg).one_mem, one_pow 3⟩
  inv_mem' := by
    rintro x ⟨hx, hx3⟩
    exact ⟨(CFSG.oddCore ↥c.Kg).inv_mem hx, by rw [inv_pow, hx3, inv_one]⟩

theorem OmegaM_normal : (c.OmegaM).Normal :=
  ⟨fun x hx k => ⟨(CFSG.oddCore_normal ↥c.Kg).conj_mem x hx.1 k, by
    have h : (k * x * k⁻¹) ^ 3 = k * x ^ 3 * k⁻¹ := conj_pow
    rw [h, hx.2]; group⟩⟩

theorem exponent_MG
    {W : Subgroup G} (hW : c.IsW W) : ∀ m ∈ c.MG, m ^ 3 = 1 := by
  have haO : c.aK ∈ c.OmegaM := ⟨c.aK_mem_oddCore, c.aK_cube⟩
  rcases c.normal_between hW c.OmegaM_normal haO (fun x hx => hx.1) with h | h
  · exfalso
    have hle : c.MG ⊓ c.OG ≤ zpowers (c.a : G) := by
      intro y hy
      obtain ⟨hyK, hyq⟩ := c.mem_MG_iff.mp hy.1
      have hy3 : (⟨y, hyK⟩ : ↥c.Kg) ∈ c.OmegaM := ⟨hyq, Subtype.ext (by
        simpa using c.OG_pow_three y hy.2)⟩
      rw [h] at hy3
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hy3
      refine Subgroup.mem_zpowers_iff.mpr ⟨j, ?_⟩
      have := congrArg Subtype.val hj
      simpa [Ctx.aK] using this
    have h3 := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, orderOf_aG] at h3
    have := c.card_MG_inf_OG
    omega
  · intro m hm
    obtain ⟨hmK, hmq⟩ := c.mem_MG_iff.mp hm
    have hmΩ : (⟨m, hmK⟩ : ↥c.Kg) ∈ c.OmegaM := by rw [h]; exact hmq
    simpa using congrArg Subtype.val hmΩ.2

structure IsExtraspecialThree (M : Subgroup G) (a : G) : Prop where
  card : Nat.card M = 3 ^ 5
  exponent : ∀ m ∈ M, m ^ 3 = 1
  center : ∀ m ∈ M, (∀ n ∈ M, m * n = n * m) ↔ m ∈ zpowers a
  commutator : ∀ m ∈ M, ∀ n ∈ M, m * n * m⁻¹ * n⁻¹ ∈ zpowers a
  nonabelian : ∃ m ∈ M, ∃ n ∈ M, m * n ≠ n * m

theorem isExtraspecialThree_MG
    {W : Subgroup G} (hW : c.IsW W) : IsExtraspecialThree c.MG (c.a : G) where
  card := by rw [c.card_MG, (c.isPGroup_three_oddCore hW).2]
  exponent := c.exponent_MG hW
  center := c.center_MG hW
  commutator := fun _ hm _ hn => c.MG_comm_mem_zpowers hm hn
  nonabelian := by
    by_contra h
    push Not at h
    exact c.MG_not_abelian hW h

end Ctx

end Setup

end CFSG.Sporadic.Recognition.JankoWong

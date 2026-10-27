module

public import CFSG.Sporadic.Recognition.JankoWongLemma14Sylow
public import CFSG.Sporadic.Recognition.JankoWongSDKernel

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Equiv Equiv.Perm Subgroup CFSG.GH74 CFSG.GH74.GLS CFSG.Open

section Orbit

theorem card_modEq_card_inf_centralizer_of_pow_prime {G : Type*} [Group G] {Q : Subgroup G}
    [Finite Q] {r : G} {p : ℕ} [Fact p.Prime] (hr : r ^ p = 1) (hQ : ∀ q ∈ Q, r * q * r⁻¹ ∈ Q) :
    Nat.card Q ≡ Nat.card ↥(Q ⊓ centralizer ({r} : Set G)) [MOD p] := by
  classical
  have : Fintype Q := Fintype.ofFinite Q
  let f : Function.End Q := fun q => ⟨r * q * r⁻¹, hQ q q.2⟩
  have hpow : ∀ (n : ℕ) (q : Q), (((f ^ n) q : Q) : G) = r ^ n * q * (r ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro q; simp; rfl
    | succ n ih =>
      intro q
      rw [pow_succ']
      change r * (((f ^ n) q : Q) : G) * r⁻¹ = _
      rw [ih]
      simp only [pow_succ']
      group
  have hf : f ^ p ^ 1 = 1 := by
    funext q
    apply Subtype.ext
    rw [pow_one, hpow]
    show _ = (q : G)
    rw [hr]
    group
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := p) (n := 1) hf
  have hfix : Fintype.card ↑(Function.fixedPoints f) =
      Nat.card ↥(Q ⊓ centralizer ({r} : Set G)) := by
    rw [← Nat.card_eq_fintype_card]
    refine Nat.card_congr
      { toFun := fun q => ⟨(q.1 : G), q.1.2, ?_⟩
        invFun := fun q => ⟨⟨(q : G), q.2.1⟩, ?_⟩
        left_inv := fun q => by apply Subtype.ext; apply Subtype.ext; rfl
        right_inv := fun q => by apply Subtype.ext; rfl }
    · have h := congrArg Subtype.val q.2
      change r * (q.1 : G) * r⁻¹ = q.1 at h
      show (q.1 : G) ∈ centralizer ({r} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (q.1 : G) * r = (r * (q.1 : G) * r⁻¹) * r := by rw [h]
        _ = r * (q.1 : G) := by group
    · have h := Subgroup.mem_centralizer_singleton_iff.mp q.2.2
      apply Subtype.ext
      change r * (q : G) * r⁻¹ = q
      calc r * (q : G) * r⁻¹ = ((q : G) * r) * r⁻¹ := by rw [h]
        _ = q := by group
  rw [hfix, ← Nat.card_eq_fintype_card] at hmod
  exact hmod

end Orbit

namespace Setup

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {S : Setup G} (c : Ctx S)

abbrev Kbar : Type := ↥c.NG ⧸ CFSG.oddCore ↥c.NG

@[expose] def Kπ : ↥c.NG →* c.Kbar := QuotientGroup.mk' (CFSG.oddCore ↥c.NG)

theorem Kπ_surjective : Function.Surjective c.Kπ := QuotientGroup.mk'_surjective _

theorem ker_Kπ : c.Kπ.ker = CFSG.oddCore ↥c.NG := QuotientGroup.ker_mk' _

theorem odd_card_ker_Kπ : Odd (Nat.card c.Kπ.ker) := by
  rw [c.ker_Kπ]; exact CFSG.ABGDGroups.odd_card_oddCore _

theorem mem_oddCore_iff_mem_OG
    (y : ↥c.NG) : y ∈ CFSG.oddCore ↥c.NG ↔ (y : G) ∈ c.OG := by
  rw [← c.oddCore_NG_map]
  constructor
  · intro h; exact ⟨y, h, rfl⟩
  · rintro ⟨o, ho, hoy⟩
    have : o = y := Subtype.ext hoy
    rwa [this] at ho

theorem exists_three_element_NG :
    ∃ g ∈ c.NG, g ∉ c.OG ∧ ∃ n : ℕ, g ^ (3 ^ n) = 1 := by
  have h81 := c.card_OG_eq_81
  obtain ⟨Q, hQ, hOQ, g, hgQ, hgO, hgN⟩ := exists_three_element_normalizing c.isPGroup_three_OG
    (m := 6) S.three_pow_six_dvd_card (by rw [h81]; norm_num)
  refine ⟨g, hgN, hgO, ?_⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp hQ ⟨g, hgQ⟩
  refine ⟨n, ?_⟩
  have h1 : (⟨g, hgQ⟩ : Q) ^ (3 ^ n) = 1 := by rw [← hn]; exact pow_orderOf_eq_one _
  simpa using congrArg (fun w : Q => (w : G)) h1

theorem not_hasNormalPComplement_NG :
    ¬ CFSG.HasNormalPComplement 2 ↥c.NG := by
  rintro ⟨X, hXn, hXcop, hXq⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hgNG, hgO, n, hgn⟩ := c.exists_three_element_NG
  have hXodd : Odd (Nat.card X) := Nat.coprime_two_left.mp hXcop
  have hXle : X ≤ CFSG.oddCore ↥c.NG := le_oddCore_of_normal_odd X hXn hXodd
  have hodd : Odd (Nat.card (Subgroup.zpowers (⟨g, hgNG⟩ : ↥c.NG))) := by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk]
    have hd : orderOf g ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one hgn
    exact Odd.of_dvd_nat (Odd.pow (by decide)) hd
  have hle := CFSG.QuasiDihedralFusion.le_of_odd_of_isPGroup_quotient X hXq _ hodd
  have hg : (⟨g, hgNG⟩ : ↥c.NG) ∈ X := hle (Subgroup.mem_zpowers _)
  exact hgO ((c.mem_oddCore_iff_mem_OG _).mp (hXle hg))

@[expose] noncomputable def BnG : Subgroup ↥c.NG := c.Bg.subgroupOf c.NG

theorem card_BnG :
    Nat.card c.BnG = 16 := by
  rw [BnG, Nat.card_congr (Subgroup.subgroupOfEquivOfLe c.Bg_le_NG).toEquiv, c.card_Bg]

@[expose] noncomputable def SylBn
    : Sylow 2 ↥c.NG :=
  Sylow.ofCard c.BnG (by rw [c.card_BnG, c.factorization_two_NG]; norm_num)

theorem SylBn_coe :
    (c.SylBn : Subgroup ↥c.NG) = c.BnG := Sylow.coe_ofCard _ _

@[expose] noncomputable def SBar
    : Sylow 2 c.Kbar :=
  c.SylBn.mapSurjective c.Kπ_surjective

theorem SBar_eq_map :
    (c.SBar : Subgroup c.Kbar) = c.BnG.map c.Kπ := by
  rw [SBar, Sylow.coe_mapSurjective, SylBn_coe]

theorem nonempty_SD_equiv_SBar :
    Nonempty (SemidihedralGroup 4 ≃* ↥(c.SBar : Subgroup c.Kbar)) := by
  obtain ⟨e⟩ := CFSG.QuasiDihedralFusion.nonempty_sylow_equiv_map c.Kπ c.Kπ_surjective
    c.odd_card_ker_Kπ c.SylBn
  exact ⟨c.BgEquiv.trans ((Subgroup.subgroupOfEquivOfLe c.Bg_le_NG).symm.trans
    ((MulEquiv.subgroupCongr (c.SylBn_coe).symm).trans e))⟩

@[expose] def zNG : ↥c.NG := ⟨S.z, c.z_mem_NG⟩

@[expose] def zbar : c.Kbar := c.Kπ c.zNG

theorem zNG_sq : c.zNG ^ 2 = 1 := Subtype.ext (by simpa [zNG] using z_sq (S := S))

theorem zbar_sq : c.zbar ^ 2 = 1 := by rw [zbar, ← map_pow, c.zNG_sq, map_one]

theorem zbar_ne_one
    : c.zbar ≠ 1 := by
  intro e
  have hmem : c.zNG ∈ CFSG.oddCore ↥c.NG := by rw [← c.ker_Kπ]; exact e
  have h1 : orderOf c.zNG ∣ Nat.card (CFSG.oddCore ↥c.NG) := by
    have := orderOf_dvd_natCard (⟨c.zNG, hmem⟩ : CFSG.oddCore ↥c.NG)
    rwa [Subgroup.orderOf_mk] at this
  have hord : orderOf c.zNG = 2 :=
    orderOf_eq_prime c.zNG_sq (fun e => z_ne_one' (S := S) (congrArg Subtype.val e))
  rw [hord] at h1
  exact (Nat.not_even_iff_odd.mpr (CFSG.ABGDGroups.odd_card_oddCore _))
    (even_iff_two_dvd.mpr h1)

theorem zbar_mem_SBar :
    c.zbar ∈ (c.SBar : Subgroup c.Kbar) := by
  rw [c.SBar_eq_map]
  exact ⟨c.zNG, Subgroup.mem_subgroupOf.mpr c.z_mem_Bg, rfl⟩

theorem SBar_comm_zbar :
    ∀ y ∈ (c.SBar : Subgroup c.Kbar), y * c.zbar = c.zbar * y := by
  intro y hy
  rw [c.SBar_eq_map] at hy
  obtain ⟨b, hb, rfl⟩ := hy
  show c.Kπ b * c.Kπ c.zNG = c.Kπ c.zNG * c.Kπ b
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact Subgroup.mem_centralizer_singleton_iff.mp (c.Bg_le_H (Subgroup.mem_subgroupOf.mp hb))

theorem centralizer_zbar_le :
    ∀ g : c.Kbar, g * c.zbar = c.zbar * g → g ∈ (c.SBar : Subgroup c.Kbar) := by
  intro g hg
  have hcent : g ∈ centralizer ({c.zbar} : Set c.Kbar) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hg
  have hmk : centralizer ({c.zbar} : Set c.Kbar) =
      (centralizer ({c.zNG} : Set ↥c.NG)).map (QuotientGroup.mk' (CFSG.oddCore ↥c.NG)) :=
    centralizer_mk_oddCore_of_sq c.zNG_sq
  rw [hmk] at hcent
  obtain ⟨y, hy, rfl⟩ := hcent
  have hyz : (y : G) * S.z = S.z * (y : G) :=
    congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy)
  have hyH : (y : G) ∈ S.H := Subgroup.mem_centralizer_singleton_iff.mpr hyz
  have hyNH : (y : G) ∈ c.NH := c.NG_inf_H_le_NH ⟨y.2, hyH⟩
  obtain ⟨p, hp, b, hb, hpb⟩ := c.NH_eq_mul _ hyNH
  have hpNG : p ∈ c.NG := c.OG_le_NG (c.PG_le_OG c.card_OG_eq_81 hp)
  have hbNG : b ∈ c.NG := c.Bg_le_NG hb
  have hyeq : y = ⟨p, hpNG⟩ * ⟨b, hbNG⟩ := Subtype.ext hpb
  have hp1 : (⟨p, hpNG⟩ : ↥c.NG) ∈ CFSG.oddCore ↥c.NG :=
    (c.mem_oddCore_iff_mem_OG _).mpr (c.PG_le_OG c.card_OG_eq_81 hp)
  have hkp : c.Kπ ⟨p, hpNG⟩ = 1 := by
    rw [← MonoidHom.mem_ker, c.ker_Kπ]; exact hp1
  show (QuotientGroup.mk' (CFSG.oddCore ↥c.NG)) y ∈ (c.SBar : Subgroup c.Kbar)
  have : (QuotientGroup.mk' (CFSG.oddCore ↥c.NG)) y = c.Kπ ⟨b, hbNG⟩ := by
    show c.Kπ y = _
    rw [hyeq, map_mul, hkp, one_mul]
  rw [this, c.SBar_eq_map]
  exact ⟨⟨b, hbNG⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩

theorem not_hasNormalPComplement_Kbar :
    ¬ CFSG.HasNormalPComplement 2 c.Kbar := fun h =>
  c.not_hasNormalPComplement_NG
    ((CFSG.QuasiDihedralFusion.hasNormalPComplement_iff_of_oddKernel c.Kπ c.Kπ_surjective
      c.odd_card_ker_Kπ).mp h)

theorem exists_dihedral_kernel :
    ∃ L : Subgroup c.Kbar, L.Normal ∧ L.index = 2 ∧ (∀ M : Subgroup L, M.index ≠ 2) ∧
      CFSG.GorensteinWalter.HasDihedralSylowTwo L ∧ c.zbar ∈ L ∧
      (∀ u : c.Kbar, u ^ 2 = 1 → u ≠ 1 → IsConj u c.zbar) :=
  exists_dihedral_kernel_of_semidihedral_selfcentralizing c.SBar c.nonempty_SD_equiv_SBar
    c.zbar_mem_SBar c.zbar_sq c.zbar_ne_one c.SBar_comm_zbar c.centralizer_zbar_le
    c.not_hasNormalPComplement_Kbar

theorem card_oddCore_NG :
    Nat.card (CFSG.oddCore ↥c.NG) = 81 := by
  rw [← c.card_OG_eq_81, ← c.oddCore_NG_map,
    Subgroup.card_map_of_injective c.NG.subtype_injective]

theorem Cg_le_NG : c.Cg ≤ c.NG := c.cg_le_ng.trans c.Ng_le_NG

theorem card_NG_le_mul_card_Cg :
    Nat.card c.NG ≤ Nat.card c.Cg * 80 := by
  classical
  set K : Subgroup ↥c.NG := c.Cg.subgroupOf c.NG with hK
  have hOGs : c.s ∈ c.OG := c.zpowers_le_OG (Subgroup.mem_zpowers c.s)
  let f : ↥c.NG ⧸ K → ↥((c.OG : Set G) \ {1}) := Quotient.lift
    (fun g => ⟨(g : G) * c.s * (g : G)⁻¹, c.conj_mem_OG_of_mem_NG g.2 hOGs, fun e => c.s_ne_one (by
      have h0 : (g : G) * c.s * (g : G)⁻¹ = 1 := e
      have h1 : (g : G)⁻¹ * ((g : G) * c.s * (g : G)⁻¹) * (g : G) = c.s := by group
      rw [h0] at h1
      simpa using h1.symm)⟩)
    (fun g g' h => by
      have h1 : (g : G)⁻¹ * (g' : G) ∈ c.Cg := Subgroup.mem_subgroupOf.mp
        (QuotientGroup.leftRel_apply.mp h)
      have h2 := c.mem_cg_iff.mp h1
      apply Subtype.ext
      show (g : G) * c.s * (g : G)⁻¹ = (g' : G) * c.s * (g' : G)⁻¹
      calc (g : G) * c.s * (g : G)⁻¹
          = (g : G) * ((g : G)⁻¹ * (g' : G) * c.s * ((g : G)⁻¹ * (g' : G))⁻¹) * (g : G)⁻¹ := by
            rw [h2]
        _ = (g' : G) * c.s * (g' : G)⁻¹ := by group)
  have hf : Function.Injective f := by
    intro x y hxy
    induction x using Quotient.inductionOn
    induction y using Quotient.inductionOn
    rename_i g g'
    have h1 : (g : G) * c.s * (g : G)⁻¹ = (g' : G) * c.s * (g' : G)⁻¹ := congrArg Subtype.val hxy
    refine Quotient.sound (QuotientGroup.leftRel_apply.mpr ?_)
    rw [Subgroup.mem_subgroupOf, c.mem_cg_iff]
    show (g : G)⁻¹ * (g' : G) * c.s * ((g : G)⁻¹ * (g' : G))⁻¹ = c.s
    calc (g : G)⁻¹ * (g' : G) * c.s * ((g : G)⁻¹ * (g' : G))⁻¹
        = (g : G)⁻¹ * ((g' : G) * c.s * (g' : G)⁻¹) * (g : G) := by group
      _ = (g : G)⁻¹ * ((g : G) * c.s * (g : G)⁻¹) * (g : G) := by rw [h1]
      _ = c.s := by group
  have hcard : Nat.card (↥c.NG ⧸ K) ≤ 80 := by
    have h1 := Nat.card_le_card_of_injective f hf
    have h2 : Nat.card ↥((c.OG : Set G) \ {1}) = 80 := by
      rw [Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem c.OG.one_mem]
      have h81 := c.card_OG_eq_81
      have : (c.OG : Set G).ncard = 81 := by rw [← Nat.card_coe_set_eq]; exact h81
      omega
    omega
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup K
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe c.Cg_le_NG).toEquiv] at hmul
  rw [hmul]
  nlinarith

end Ctx

end Setup

end CFSG.Sporadic.Recognition.JankoWong

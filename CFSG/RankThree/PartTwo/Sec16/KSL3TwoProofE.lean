module

public import CFSG.RankThree.PartTwo.Sec16.KSL3TwoProofTypeC
public import CFSG.RankThree.PartTwo.Sec16.KSL3TwoProofFusX
import CFSG.RankThree.PartTwo.Sec16.Item16Tail
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
public import CFSG.RankThree.PartTwo.Sec16.Item16Tail17

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix (ProjGenLinGroup)
open scoped Pointwise
open Proof1617

variable {G : Type} [Group G] [Finite G]

theorem ks1617E_of_steps_two (h1614 : Step1614) (h1616 : Step1616) (h138 : Item138N) :
    KS1617E := by
  intro G _ _ A c L h hx
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hxW, hx3, hxA⟩ := hx
  obtain ⟨n, hz⟩ := h1616 G A c L h
  have hn3 := not_three_dvd_of_isZ3 h h138 hz
  have hn2 : 2 ≤ n := by
    have hqs := Sec6.isQuasisimple_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
    have : Group.IsPerfect (↥L ⧸ aschbacherSolvableCore 3 ↥L) := hqs.1
    have hne := (Sec19.Step1914TriProof.isSimpleGroup_of_isoLThreePi hz.1 hz.2.1).2
    by_contra hlt
    have : n = 1 := by omega
    subst this
    exact hne (by norm_num)
  obtain ⟨hcL, h9, hAle⟩ := facts_of_isZ3 h hz
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) := h.le_centralizer
  have hAeq := eq_zpowers_sup_inf h.mem_A hAle hLc
  have hCN := centralizer_le_normalizer_L h hz
  refine ⟨⟨2, n, inferInstance, hz.1, hz.2.1⟩, ?_⟩
  set D := A ⊓ L with hDdef
  have hDab : CFSG.Assembly.IsElemAbelian 3 D :=
    Proof169.isElemAbelian_of_le h.isElemAbelian inf_le_left
  have hDc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb => h.commute ha.1 hb.1
  have hDe : ∀ a ∈ D, a ^ 3 = 1 := fun a ha => h.isElemAbelian.2 a ha.1
  have hc3 : c ^ 3 = 1 := h.isElemAbelian.2 c h.mem_A
  have hxH : x ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    normalizer_le_of_omegaA_eq (h1614 G A c L h) hxW
  have hxc : x * c = c * x := mul_eq_mul_of_mem_normalizer_zpowers h.card_zpowers hx3 hxH
  have hxC : x ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hxc
  have hxL : x ∈ Subgroup.normalizer (L : Set G) := hCN hxC
  have hxD : x ∈ Subgroup.normalizer (D : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun d hd => ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hxW d).mp hd.1
    · exact (Subgroup.mem_normalizer_iff.mp hxL d).mp hd.2
  set Y := A ⊔ Subgroup.zpowers x with hY
  have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer (A : Set G) := Subgroup.zpowers_le.mpr hxW
  have hYN : Y ≤ Subgroup.normalizer (L : Set G) :=
    sup_le h.le_normalizer (Subgroup.zpowers_le.mpr hxL)
  have hYC : Y ≤ Subgroup.centralizer ({c} : Set G) :=
    sup_le h.A_le_centralizer (Subgroup.zpowers_le.mpr hxC)
  have hYA : Y ≤ Subgroup.normalizer (A : Set G) := sup_le Subgroup.le_normalizer hxN
  have hdecY : ∀ y ∈ Y, ∃ a ∈ A, ∃ k : ℤ, y = a * x ^ k := by
    intro y hy
    have hy' : y ∈ (A : Set G) * (Subgroup.zpowers x : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left A _ hxN]
      exact hy
    obtain ⟨a, ha, _, hw, rfl⟩ := hy'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact ⟨a, ha, k, rfl⟩
  have hxk3 : ∀ k : ℤ, (x ^ k) ^ 3 = 1 := fun k => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
  have hxkD : ∀ k : ℤ, x ^ k ∈ Subgroup.normalizer (D : Set G) := fun k => zpow_mem hxD k
  have hxkc : ∀ k : ℤ, x ^ k * c = c * x ^ k := fun k => (Commute.zpow_left hxc k).eq
  have hY3 : ∀ y ∈ Y, y ^ 3 = 1 := by
    intro y hy
    obtain ⟨a, ha, k, rfl⟩ := hdecY y hy
    rw [hAeq] at ha
    obtain ⟨j, d, hd, rfl⟩ := exists_eq_zpow_mul (inf_le_right.trans hLc) ha
    set s := x ^ k with hs
    have hcd : c ^ j * (d * s) = d * s * c ^ j := by
      have h1 : c ^ j * d = d * c ^ j :=
        (Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp (hLc hd.2)).symm j).eq
      have h2 : c ^ j * s = s * c ^ j := (Commute.zpow_left (hxkc k).symm j).eq
      rw [← mul_assoc, h1, mul_assoc, h2, ← mul_assoc]
    have hcj : (c ^ j) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc3, one_zpow]
    have hnorm := mul_conj_mul_conj_eq_one hDc hDe h9 (hxkD k) (hxk3 k) hd
    have hds : (d * s) ^ 3 = d * (s * d * s⁻¹) * (s * (s * d * s⁻¹) * s⁻¹) * s ^ 3 := by
      rw [pow_three, pow_three]; group
    rw [mul_assoc, (Commute.mul_pow hcd 3), hcj, one_mul, hds, hnorm, hxk3 k, one_mul]
  set θG := (aschbacherSolvableCore 3 ↥L).map L.subtype with hθG
  have hθ3 : ¬ 3 ∣ Nat.card θG := by
    rw [hθG, Subgroup.card_map_of_injective L.subtype_injective]
    exact (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.2.1
  have hDθ : ∀ g ∈ D, g ∈ θG → g = 1 := by
    intro g hgD hgθ
    have h1 : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one (hDe g hgD)
    have h2 : orderOf g ∣ Nat.card θG := by
      have := orderOf_dvd_natCard (⟨g, hgθ⟩ : θG)
      rwa [Subgroup.orderOf_mk] at this
    have h3 : orderOf g = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
      · exact h
      · exact absurd (h ▸ h2) hθ3
    exact orderOf_eq_one_iff.mp h3
  have hsec : Late.sectionCentralizer A L θG = (Subgroup.zpowers c : Set G) :=
    h.sectionCentralizer_eq
  have hker : ∀ y ∈ Y, (∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ θG) → y ∈ Subgroup.zpowers c := by
    intro y hy htriv
    obtain ⟨a, ha, k, rfl⟩ := hdecY y hy
    have hxkA : x ^ k ∈ A := by
      refine mem_of_mem_partTwoF h.mem_partTwoF (hxk3 k) ?_
      rw [hAeq]
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (fun d hd => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hxkc k).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have hd' := htriv d hd.2
        set s := x ^ k with hs
        have had : a * d = d * a := h.commute ha hd.1
        have hsd : s * d * s⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp (hxkD k) d).mp hd
        have heq : a * s * d * (a * s)⁻¹ * d⁻¹ = s * d * s⁻¹ * d⁻¹ := by
          have hasd : a * (s * d * s⁻¹) = (s * d * s⁻¹) * a := h.commute ha hsd.1
          calc a * s * d * (a * s)⁻¹ * d⁻¹ = (a * (s * d * s⁻¹)) * a⁻¹ * d⁻¹ := by group
            _ = s * d * s⁻¹ * d⁻¹ := by rw [hasd]; group
        rw [heq] at hd'
        have hmem : s * d * s⁻¹ * d⁻¹ ∈ D := D.mul_mem hsd (D.inv_mem hd)
        have h1 := hDθ _ hmem hd'
        have h2 : s * d * s⁻¹ = d := mul_inv_eq_one.mp h1
        calc d * s = s * d * s⁻¹ * s := by rw [h2]
          _ = s * d := by group
    have hayA : a * x ^ k ∈ A := A.mul_mem ha hxkA
    have hmem : a * x ^ k ∈ Late.sectionCentralizer A L θG := ⟨hayA, htriv⟩
    rw [hsec] at hmem
    exact hmem
  set ρY : ↥Y →* MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    ((Sec4.thetaQuotMulAut ↥L).comp L.normalizerMonoidHom).comp (Subgroup.inclusion hYN)
    with hρY
  have hρYapp : ∀ y : ↥Y, ρY y =
      Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨y, hYN y.2⟩) := fun y => rfl
  have hcY : c ∈ Y := Subgroup.mem_sup_left h.mem_A
  have hctriv : ∀ g ∈ Subgroup.zpowers c, ∀ l ∈ L, g * l * g⁻¹ * l⁻¹ ∈ θG := by
    intro g hg l hl
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hcl : c ^ k * l = l * c ^ k :=
      (Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp (hLc hl)).symm k).eq
    rw [hcl, mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _
  have hkerY : ∀ y : ↥Y, ρY y = 1 ↔ (y : G) ∈ Subgroup.zpowers c := by
    intro y
    rw [hρYapp, thetaQuotMulAut_eq_one_iff]
    exact ⟨hker y y.2, fun hyc => hctriv _ hyc⟩
  have hkercard : Nat.card ρY.ker = 3 := by
    have : ρY.ker = (Subgroup.zpowers c).subgroupOf Y := by
      ext y
      rw [MonoidHom.mem_ker, hkerY, Subgroup.mem_subgroupOf]
    rw [this, card_subgroupOf_of_le (Subgroup.zpowers_le.mpr hcY), h.card_zpowers]
  have hx1 : x ≠ 1 := fun h1 => hxA (h1 ▸ A.one_mem)
  have hxord : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hx3 hx1
  have hAx : A ⊓ Subgroup.zpowers x = ⊥ := by
    have hdvd : Nat.card (A ⊓ Subgroup.zpowers x : Subgroup G) ∣ 3 :=
      hxord ▸ Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3'
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : A ⊓ Subgroup.zpowers x = Subgroup.zpowers x :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3', hxord])
      apply hxA
      have : x ∈ A ⊓ Subgroup.zpowers x := by
        rw [heq]
        exact Subgroup.mem_zpowers x
      exact this.1
  have hY81 : Nat.card Y = 81 := by
    have h1 := card_sup_mul_card_inf_of_le_normalizer hxN
    rw [hAx, Subgroup.card_bot, mul_one, h.card_eq, hxord, sup_comm] at h1
    exact h1
  set P := Sec4.autThetaQuot Y L with hP
  have hPrange : P = ρY.range := by
    ext τ
    rw [Sec4.mem_autThetaQuot_iff]
    constructor
    · rintro ⟨g, hgN, hgY, rfl⟩
      exact ⟨⟨g, hgY⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, hYN y.2, y.2, rfl⟩
  have hP27 : Nat.card P = 27 := by
    have h1 := card_eq_card_range_mul_card_ker ρY
    rw [hY81, hkercard, ← hPrange] at h1
    omega
  have hP3 : IsPGroup 3 P := IsPGroup.of_card (n := 3) (by rw [hP27]; norm_num)
  obtain ⟨P₀, hP₀P, hP₀9, π, p, f, K, _, hKf, hq, e, Dt, hDt, hτD, hDτ⟩ :=
    kS1617TypeC_two _ n hn2 hn3 hz.2.1 P hP3 hP27
  have hP₀R : P₀ ≤ ρY.range := hPrange ▸ hP₀P
  set E₀ : Subgroup ↥Y := P₀.comap ρY with hE₀
  set E : Subgroup G := E₀.map Y.subtype with hE
  have hEY : E ≤ Y := Subgroup.map_subtype_le E₀
  have hmemE : ∀ g (hg : g ∈ Y), g ∈ E ↔ ρY ⟨g, hg⟩ ∈ P₀ := by
    intro g hg
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hρ
      exact ⟨⟨g, hg⟩, hρ, rfl⟩
  have hcE : c ∈ E := (hmemE c hcY).mpr (by
    rw [(hkerY ⟨c, hcY⟩).mpr (Subgroup.mem_zpowers c)]
    exact P₀.one_mem)
  have hautE : Sec4.autThetaQuot E L = P₀ := by
    ext τ
    rw [Sec4.mem_autThetaQuot_iff]
    constructor
    · rintro ⟨g, hgN, hgE, rfl⟩
      exact (hmemE g (hEY hgE)).mp hgE
    · intro hτ
      obtain ⟨y, rfl⟩ := hP₀R hτ
      exact ⟨y, hYN y.2, (hmemE y y.2).mpr hτ, rfl⟩
  have hE27 : Nat.card E = 27 := by
    rw [hE, Subgroup.card_map_of_injective Y.subtype_injective,
      card_comap_of_le_range ρY hP₀R, hP₀9, hkercard]
  have hP₀n : (P₀.subgroupOf P).Normal := by
    refine Subgroup.normal_of_index_eq_minFac_card ?_
    have hidx := Subgroup.index_mul_card (P₀.subgroupOf P)
    rw [card_subgroupOf_of_le hP₀P, hP₀9, hP27] at hidx
    rw [hP27, show Nat.minFac 27 = 3 by norm_num]
    omega
  have hAE : A ≤ Subgroup.normalizer (E : Set G) := by
    intro a ha
    have haY : a ∈ Y := Subgroup.mem_sup_left ha
    refine Subgroup.mem_normalizer_fintype fun g hg => ?_
    have hgY := hEY hg
    have hagY : a * g * a⁻¹ ∈ Y := Y.mul_mem (Y.mul_mem haY hgY) (Y.inv_mem haY)
    refine (hmemE _ hagY).mpr ?_
    have h1 : ρY ⟨a * g * a⁻¹, hagY⟩ = ρY ⟨a, haY⟩ * ρY ⟨g, hgY⟩ * (ρY ⟨a, haY⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    have hρa : ρY ⟨a, haY⟩ ∈ P := hPrange ▸ ⟨⟨a, haY⟩, rfl⟩
    have hρg : ρY ⟨g, hgY⟩ ∈ P₀ := (hmemE g hgY).mp hg
    have h2 := hP₀n.conj_mem ⟨ρY ⟨g, hgY⟩, hP₀P hρg⟩ (Subgroup.mem_subgroupOf.mpr hρg)
      ⟨ρY ⟨a, haY⟩, hρa⟩
    rw [Subgroup.mem_subgroupOf] at h2
    rw [h1]
    exact h2
  have hP₀c : IsMulCommutative P₀ :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := P₀) (by rw [hP₀9]; norm_num)
  have hcD : ∀ g ∈ Subgroup.zpowers c, g ∈ D → g = 1 := by
    intro g hgc hgD
    by_contra hg1
    have heq := Proof169.zpowers_eq_of_mem_of_ne_one h.card_zpowers hgc hg1
    apply hcL
    have hcg : c ∈ Subgroup.zpowers g := heq ▸ Subgroup.mem_zpowers c
    exact (Subgroup.zpowers_le.mpr hgD.2) hcg
  have hcentral : ∀ g ∈ E, ∀ a ∈ E ⊓ A, g * a = a * g := by
    intro g hg a ha
    have hgY := hEY hg
    have haY := hEY ha.1
    set t := g * a * g⁻¹ * a⁻¹ with ht
    have htY : t ∈ Y := Y.mul_mem (Y.mul_mem (Y.mul_mem hgY haY) (Y.inv_mem hgY)) (Y.inv_mem haY)
    have htc : t ∈ Subgroup.zpowers c := by
      refine (hkerY ⟨t, htY⟩).mp ?_
      have hρg : ρY ⟨g, hgY⟩ ∈ P₀ := (hmemE g hgY).mp hg
      have hρa : ρY ⟨a, haY⟩ ∈ P₀ := (hmemE a haY).mp ha.1
      have hcomm : ρY ⟨g, hgY⟩ * ρY ⟨a, haY⟩ = ρY ⟨a, haY⟩ * ρY ⟨g, hgY⟩ :=
        congrArg Subtype.val (hP₀c.is_comm.comm ⟨_, hρg⟩ ⟨_, hρa⟩)
      have h1 : ρY ⟨t, htY⟩ = ρY ⟨g, hgY⟩ * ρY ⟨a, haY⟩ * (ρY ⟨g, hgY⟩)⁻¹ *
          (ρY ⟨a, haY⟩)⁻¹ := by
        rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
        rfl
      rw [h1, hcomm]
      group
    have htD : t ∈ D := by
      have haA : a ∈ A := ha.2
      rw [hAeq] at haA
      obtain ⟨j, d, hd, hadj⟩ := exists_eq_zpow_mul (inf_le_right.trans hLc) haA
      have hgc : g * c ^ j = c ^ j * g := by
        have := Subgroup.mem_centralizer_singleton_iff.mp (hYC hgY)
        exact (Commute.zpow_right this j).eq
      have hgdg : g * d * g⁻¹ * d⁻¹ ∈ L := by
        refine L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hYN hgY) d).mp hd.2) (L.inv_mem hd.2)
      have hcjt : c ^ j * (g * d * g⁻¹ * d⁻¹) = (g * d * g⁻¹ * d⁻¹) * c ^ j :=
        (Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp (hLc hgdg)).symm j).eq
      have hteq : t = g * d * g⁻¹ * d⁻¹ := by
        rw [ht, hadj]
        calc g * (c ^ j * d) * g⁻¹ * (c ^ j * d)⁻¹
            = (g * c ^ j) * d * g⁻¹ * d⁻¹ * (c ^ j)⁻¹ := by group
          _ = c ^ j * (g * d * g⁻¹ * d⁻¹) * (c ^ j)⁻¹ := by rw [hgc]; group
          _ = g * d * g⁻¹ * d⁻¹ := by rw [hcjt]; group
      refine ⟨?_, hteq ▸ hgdg⟩
      have h1 := (Subgroup.mem_normalizer_iff.mp (hYA hgY) a).mp ha.2
      rw [ht]
      exact A.mul_mem h1 (A.inv_mem ha.2)
    have ht1 : t = 1 := hcD t htc htD
    have : g * a * g⁻¹ = a := mul_inv_eq_one.mp ht1
    calc g * a = g * a * g⁻¹ * g := by group
      _ = a * g := by rw [this]
  have hEA9 : 9 ≤ Nat.card (A ⊓ E : Subgroup G) := by
    have h1 := card_sup_mul_card_inf_of_le_normalizer (hEY.trans hYA)
    rw [h.card_eq, hE27] at h1
    have h2 : Nat.card (E ⊔ A : Subgroup G) ≤ 81 :=
      hY81 ▸ Subgroup.card_le_of_le (sup_le hEY le_sup_left)
    have h3 : 0 < Nat.card (A ⊓ E : Subgroup G) := Nat.card_pos
    nlinarith
  have hEcomm : IsMulCommutative E := by
    set Z := Subgroup.center ↥E with hZdef
    have hZ : (A ⊓ E).subgroupOf E ≤ Z := by
      intro a ha
      rw [Subgroup.mem_center_iff]
      intro g
      have ha' := Subgroup.mem_subgroupOf.mp ha
      exact Subtype.ext (hcentral g g.2 a ⟨ha'.2, ha'.1⟩)
    have hZ9 : 9 ≤ Nat.card Z := by
      have h1 := Subgroup.card_le_of_le hZ
      rw [card_subgroupOf_of_le inf_le_right] at h1
      omega
    have hZdvd : Nat.card Z ∣ 27 := hE27 ▸ Subgroup.card_subgroup_dvd_card Z
    have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
    rw [hE27] at hq
    have hcyc : IsCyclic (↥E ⧸ Z) := by
      obtain ⟨i, hi, hiZ⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
        (show Nat.card Z ∣ 3 ^ 3 from hZdvd)
      interval_cases i
      · rw [hiZ] at hZ9; norm_num at hZ9
      · rw [hiZ] at hZ9; norm_num at hZ9
      · rw [hiZ] at hq
        exact isCyclic_of_prime_card (p := 3) (by omega)
      · rw [hiZ] at hq
        have h1 : Nat.card (↥E ⧸ Z) = 1 := by omega
        have : Subsingleton (↥E ⧸ Z) := (Nat.card_eq_one_iff_unique.mp h1).1
        infer_instance
    exact (QuotientGroup.mk' Z).isMulCommutative_of_isCyclic_of_ker_le_center
      (by rw [QuotientGroup.ker_mk'])
  obtain ⟨f₀, hf₀, hf₀1⟩ : ∃ f₀ ∈ (A ⊓ E) ⊓ D, f₀ ≠ 1 := by
    have hne := Proof169.inf_ne_bot_of_nine_le (A := A) (B := A ⊓ E) (E := D) inf_le_left
      inf_le_left h.card_eq hEA9 h9.ge
    obtain ⟨⟨f₀, hf₀⟩, hf₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    exact ⟨f₀, hf₀, fun h1 => hf₀1 (Subtype.ext h1)⟩
  have hf₀E : f₀ ∈ E := hf₀.1.2
  have hf₀D : f₀ ∈ D := hf₀.2
  refine ⟨E, hcE, ⟨hEcomm, fun g hg => hY3 g (hEY hg)⟩, hE27, hEY.trans hYN, ?_, ?_,
    hAle.trans (sup_le_sup_right (Subgroup.zpowers_le.mpr hcE) L), h9, ?_, hAE, ?_⟩
  ·
    ext g
    constructor
    · rintro ⟨hgE, htriv⟩
      exact hker g (hEY hgE) htriv
    · intro hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      exact ⟨E.zpow_mem hcE k, hctriv _ hg⟩
  ·
    refine ⟨π, p, f, K, inferInstance, hKf, hq, e, Dt, hDt, fun τ hτ => ?_, fun y hy => ?_⟩
    · rw [hautE] at hτ
      exact hτD τ hτ
    · obtain ⟨τ, hτ, heq⟩ := hDτ y hy
      refine ⟨τ, ?_, heq⟩
      rw [hautE]
      exact hτ
  ·
    intro y hy hy1 z hzD hz1
    obtain ⟨w, hw, hwyz⟩ := ks1617Fus_proved G L D n hz.1 hn3 hz.2.1 inf_le_right hDab h9 y hy hy1
      z hzD hz1
    exact ⟨w, hw.1, hwyz⟩
  ·
    intro a ha
    rw [hAeq] at ha
    obtain ⟨j, d, hd, rfl⟩ := exists_eq_zpow_mul (inf_le_right.trans hLc) ha
    by_cases hd1 : d = 1
    · refine ⟨1, Subgroup.one_mem _, ?_⟩
      rw [hd1, mul_one, one_mul, inv_one, mul_one]
      exact E.zpow_mem hcE j
    · obtain ⟨w, hw, hwd⟩ := ks1617Fus_proved G L D n hz.1 hn3 hz.2.1 inf_le_right hDab h9 d hd
        hd1 f₀ hf₀D hf₀1
      refine ⟨w, ⟨mem_normalizer_of_mem_normalizer_inf hAeq hLc hw, hw.1⟩, ?_⟩
      have hwc : w * c ^ j = c ^ j * w :=
        (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp (hLc hw.1)) j).eq
      have heq : w * (c ^ j * d) * w⁻¹ = c ^ j * (w * d * w⁻¹) := by
        calc w * (c ^ j * d) * w⁻¹ = (w * c ^ j) * d * w⁻¹ := by group
          _ = c ^ j * (w * d * w⁻¹) := by rw [hwc]; group
      rw [heq, hwd]
      exact E.mul_mem (E.zpow_mem hcE j) hf₀E

end CFSG.RankThree.PartTwo.Sec16

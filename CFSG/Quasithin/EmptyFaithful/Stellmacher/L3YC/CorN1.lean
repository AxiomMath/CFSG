module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.CorN1Aux
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.NPrimeSetting
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCLemmaUBar

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417 CFSG.Quasithin.SBd7
  CFSG.Quasithin.S153D
open scoped commutatorElement Pointwise

namespace Stellmacher.L3YC

section Bar

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_mk_mem {H S L : Subgroup G} (hS : IsSylowTwoOf S H)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) (hperf : ⁅L, L⁆ = L) (hLH : L ≤ H) {x : G}
    (hxH : x ∈ H)
    (hx : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, hxH⟩ ∈
      Subgroup.normalizer (modO2Image H L : Set (↥H ⧸ CFSG.pCore 2 ↥H))) :
    x ∈ Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Subgroup G := (CFSG.pCore 2 ↥H).map H.subtype
  have hPS : P ≤ S := by
    rintro _ ⟨y, hy, rfl⟩
    exact pCore_two_le_subgroupOf hS hy
  have hPN : P ≤ Subgroup.normalizer (L : Set G) := hPS.trans hSL
  have hP2 : IsPGroup 2 ↥P := hS.2.1.to_le hPS
  let M : Subgroup G := L.map (MulAut.conj x).toMonoidHom
  have hMle : M ≤ L ⊔ P := by
    rintro _ ⟨y, hy, rfl⟩
    have hyH : y ∈ H := hLH hy
    have hxyH : x * y * x⁻¹ ∈ H := H.mul_mem (H.mul_mem hxH hyH) (H.inv_mem hxH)
    have hyb : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, hyH⟩ ∈ modO2Image H L :=
      ⟨⟨y, hyH⟩, hy, rfl⟩
    obtain ⟨⟨l, hlH⟩, hl, hlx⟩ := (Subgroup.mem_normalizer_iff.mp hx _).mp hyb
    have hlx' : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨l, hlH⟩ =
        QuotientGroup.mk' (CFSG.pCore 2 ↥H) (⟨x, hxH⟩ * ⟨y, hyH⟩ * ⟨x, hxH⟩⁻¹) := by
      rw [hlx]
      simp only [map_mul, map_inv]
    have hk : (⟨l, hlH⟩ : H)⁻¹ * (⟨x, hxH⟩ * ⟨y, hyH⟩ * ⟨x, hxH⟩⁻¹) ∈ CFSG.pCore 2 ↥H :=
      QuotientGroup.eq.mp hlx'
    have hk' : l⁻¹ * (x * y * x⁻¹) ∈ P :=
      Subgroup.mem_map.mpr ⟨_, hk, rfl⟩
    have hl' : l ∈ L := hl
    have : x * y * x⁻¹ = l * (l⁻¹ * (x * y * x⁻¹)) := by group
    show x * y * x⁻¹ ∈ L ⊔ P
    rw [this]
    exact Subgroup.mul_mem_sup hl' hk'
  have hMperf : ⁅M, M⁆ = M := by
    show ⁅L.map (MulAut.conj x).toMonoidHom, L.map (MulAut.conj x).toMonoidHom⁆ = _
    rw [← Subgroup.map_commutator, hperf]
  have hLnorm : (L.subgroupOf (L ⊔ P)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le (fun x hx => Subgroup.le_normalizer hx) hPN)
  have hnil : Group.IsNilpotent ↥P := hP2.isNilpotent
  have hsolv : Group.IsSolvable ↥P := @IsNilpotent.to_isSolvable _ _ hnil
  have hcore : perfectCore (L ⊔ P) ≤ L :=
    perfectCore_le_of_sup_solvable le_sup_left hLnorm rfl hsolv
  have hML : M ≤ L := (le_perfectCore_of_perfect hMle hMperf).trans hcore
  refine Subgroup.mem_normalizer_fintype fun a ha => ?_
  exact hML ⟨a, ha, rfl⟩

omit [Finite G] in
theorem exists_three_lift {H : Subgroup G} {xb : ↥H ⧸ CFSG.pCore 2 ↥H} {m : ℕ}
    (hxb : xb ^ 3 ^ m = 1) :
    ∃ (x : G) (hxH : x ∈ H), x ^ 3 ^ m = 1 ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, hxH⟩ = xb := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective xb
  have hmem : h ^ 3 ^ m ∈ CFSG.pCore 2 ↥H := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hxb
  obtain ⟨h₂, hh₂, h₃, -, hsplit, h₃pow⟩ :=
    exists_two_three_split (CFSG.pCore_isPGroup (G := ↥H) (p := 2)) hmem
  refine ⟨(h₃ : G), h₃.2, ?_, ?_⟩
  · have := congrArg Subtype.val h₃pow
    simpa using this
  · have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥H) h₂ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hh₂
    rw [QuotientGroup.mk'_apply]
    conv_rhs => rw [hsplit]
    rw [QuotientGroup.mk_mul]
    have : (QuotientGroup.mk h₂ : ↥H ⧸ CFSG.pCore 2 ↥H) = 1 := h2
    rw [this, one_mul]

end Bar

section Main

variable {G : Type} [Group G] [Finite G]

theorem corN1_G (h113 : StageLemma14113) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : Ctx15316 T Mc M V₁ V₂ Yp I L t) (hq : IsLnTwoQuot L 3) (c12 : Concl15312Two Yp L)
    (hV : ⁅VZ T M, YL153 Yp L⁆ ≠ ⊥) (hYY : Yp = Y153 Mc M)
    (hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G))
    {t' : G} (ht'T : t' ∈ T) (ht'S : t' ∉ Sgp153 T V₁)
    (hswap : B6.conjSub t' (YL153 Yp L) = YC153 Yp L)
    (h4 : MS93.IsC134Case4Corr (L ⊔ Sgp153 T V₁) (Sgp153 T V₁) L)
    {c₀ : G} (hc₀ : c₀ ∈ c134CQ (L ⊔ Sgp153 T V₁) L) (hc₀1 : c₀ ≠ 1)
    {x : G} (hxN : x ∈ Subgroup.normalizer (L : Set G)) (hxc : x * c₀ = c₀ * x)
    {m : ℕ} (hxm : x ^ 3 ^ m = 1) :
    ∃ b ∈ L, ∀ q ∈ c134Q (L ⊔ Sgp153 T V₁) L, x * q * x⁻¹ = b * q * b⁻¹ := by
  obtain ⟨l, hl, n, hn, hxln, hnm⟩ := exists_decomp_of_three_power hq hxN hxm
  obtain ⟨hC4, hCsq⟩ := c134CQ_card_four hq h4
  have hxV : x ∈ Subgroup.normalizer ((c134CQ (L ⊔ Sgp153 T V₁) L : Subgroup G) : Set G) :=
    Stellmacher.CD.L3YC.normalizer_le_normalizer_c134CQ_of_case4 hSL h4 hxN
  have hxc' : x * c₀ * x⁻¹ = c₀ := by rw [hxc]; group
  have hfix := centralizes_of_fixes hC4 hCsq hxV hxm hc₀ hc₀1 hxc'
  have hnx : n = l⁻¹ * x := by rw [hxln]; group
  have hnV : ∀ v ∈ c134CQ (L ⊔ Sgp153 T V₁) L, n * v * n⁻¹ = v := by
    intro v hv
    have hvl : l * v = v * l := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hv).2 l hl
    calc n * v * n⁻¹ = l⁻¹ * (x * v * x⁻¹) * l := by rw [hnx]; group
      _ = l⁻¹ * v * l := by rw [hfix v hv]
      _ = v := by rw [mul_assoc, ← hvl]; group
  have hQ := centralizes_c134Q_of_N0 h113 h37 h38 c hq c12 hV hYY hSL ht'T ht'S hswap h4 n hn
    ⟨m, hnm⟩ hnV
  refine ⟨l, hl, fun q hqm => ?_⟩
  calc x * q * x⁻¹ = l * (n * q * n⁻¹) * l⁻¹ := by rw [hxln]; group
    _ = l * q * l⁻¹ := by rw [hQ q hqm]

theorem corN1 (h113 : StageLemma14113) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : Ctx15316 T Mc M V₁ V₂ Yp I L t) (hq : IsLnTwoQuot L 3) (c12 : Concl15312Two Yp L)
    (hV : ⁅VZ T M, YL153 Yp L⁆ ≠ ⊥) (hYY : Yp = Y153 Mc M)
    (hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G))
    {t' : G} (ht'T : t' ∈ T) (ht'S : t' ∉ Sgp153 T V₁)
    (hswap : B6.conjSub t' (YL153 Yp L) = YC153 Yp L)
    (h4 : MS93.IsC134Case4Corr (L ⊔ Sgp153 T V₁) (Sgp153 T V₁) L)
    {c₀ : G} (hc₀ : c₀ ∈ c134CQ (L ⊔ Sgp153 T V₁) L) (hc₀1 : c₀ ≠ 1)
    {H : Subgroup G} (hH : H = Subgroup.centralizer ({c₀} : Set G)) (hS : IsSylowTwoOf (Sgp153 T V₁) H)
    {xb : ↥H ⧸ CFSG.pCore 2 ↥H} {m : ℕ} (hxb : xb ^ 3 ^ m = 1)
    (hn : xb ∈ Subgroup.normalizer (modO2Image H L : Set (↥H ⧸ CFSG.pCore 2 ↥H))) :
    ∃ b ∈ modO2Image H L, ∀ q ∈ Stellmacher.PU.L3YC.Qbar H (L ⊔ Sgp153 T V₁) L,
      xb * q * xb⁻¹ = b * q * b⁻¹ := by
  have hperf : ⁅L, L⁆ = L := by
    obtain ⟨h, -⟩ := c.conc
    exact perfect_of_mem_cComp h
  have hLH : L ≤ H := by
    rw [hH]
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc₀).2 l hl
  obtain ⟨x, hxH, hxm, rfl⟩ := exists_three_lift hxb
  have hxN : x ∈ Subgroup.normalizer (L : Set G) :=
    mem_normalizer_of_mk_mem hS hSL hperf hLH hxH hn
  have hxc : x * c₀ = c₀ * x := by
    have := hH ▸ hxH
    exact Subgroup.mem_centralizer_singleton_iff.mp this
  obtain ⟨b, hb, hbq⟩ := corN1_G h113 h37 h38 c hq c12 hV hYY hSL ht'T ht'S hswap h4 hc₀ hc₀1 hxN
    hxc hxm
  refine ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨b, hLH hb⟩, ⟨⟨b, hLH hb⟩, hb, rfl⟩, ?_⟩
  rintro _ ⟨q, hq', rfl⟩
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hbq q hq')

end Main

end Stellmacher.L3YC

end CFSG.Quasithin

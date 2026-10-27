module

public import CFSG.Quasithin.EmptyFaithful.S151S8BSplit
public import CFSG.Quasithin.EmptyFaithful.S151ZH
public import CFSG.Quasithin.EmptyFaithful.A38cOrders
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239Covers
public import CFSG.Sporadic.Schreier.MathieuOddCoreM11

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Timmesfeld.Orders
  CFSG.Quasithin.H13.VolI CFSG.Quasithin.Vol2.Ch10.SecA CFSG.Quasithin.S151S8
open scoped commutatorElement

theorem not_a38Order_7920 : ¬ A38Order 7920 :=
  not_a38Order_of (a := 4) (b := 495) rfl (by decide) (by decide) (by decide) (by decide)
    (by decide)
    (ordA_one_ne_of_lt (b := 7920) (B := 30) (by norm_num) (by
      intro p hpB hp hp3
      interval_cases p <;> decide))

theorem m11_not_a38Types
    {X : Type} [Group X]
    (h : IsSporadic .M11 X) : ¬ A38Types X := by
  intro hA
  obtain ⟨e⟩ := h
  have hc := a38Order_card hA
  rw [Nat.card_congr e.toEquiv,
    show Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M11) = 7920 from
      CFSG.Sporadic.Mathieu.card_M11] at hc
  exact not_a38Order_7920 hc

theorem isQuasisimple_of_open' {Q : Type*} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨⟨h1⟩, h2, ?_⟩
  by_contra hc
  have hc' : ∀ a b : Q ⧸ Subgroup.center Q, a * b = b * a := fun a b => by
    by_contra hab
    exact hc ⟨a, b, hab⟩
  have hZ : commutator Q ≤ Subgroup.center Q := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' (Subgroup.center Q) ⁅x, y⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hc' _ _
  rw [h1] at hZ
  have hall : ∀ q : Q ⧸ Subgroup.center Q, q = 1 := fun q => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact (QuotientGroup.eq_one_iff x).mpr (hZ (Subgroup.mem_top x))
  obtain ⟨a, b, hab⟩ := exists_pair_ne (Q ⧸ Subgroup.center Q)
  exact hab ((hall a).trans (hall b).symm)

theorem m11_center_eq_bot {G : Type}
    [Group G] [Finite G] {L : Subgroup G} (hL : CFSG.Open.IsQuasisimple ↥L)
    (hM : IsSporadic .M11 (↥L ⧸ CFSG.pCore 2 ↥L)) : Subgroup.center ↥L = ⊥ := by
  obtain ⟨e⟩ := hM
  have hs : IsSimpleGroup ↥CFSG.Blueprint.NativeSporadic.M11 :=
    CFSG.Sporadic.Mathieu.fam_m11_simplicity.2.2
  exact CFSG.QuasithinUnique.Vol2Native.L239.center_eq_bot_of_exp2 (isQuasisimple_of_open' hL) e hs
    (CFSG.QuasithinUnique.Vol2Native.L239.exists_noncomm_of_simple_card hs
      CFSG.Sporadic.Mathieu.card_M11 (by norm_num) (by norm_num))
    (fun E' _ _ π' h1 h2 h3 h4 =>
      CFSG.QuasithinUnique.Vol2Native.L239.Covers.m11_cover_exp2 π' h1 h2 h3 h4)

theorem isSporadic_m11_of_quot
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (hL : CFSG.Open.IsQuasisimple ↥L)
    (hM : IsSporadic .M11 (↥L ⧸ CFSG.pCore 2 ↥L)) : IsSporadic .M11 ↥L := by
  have hZ := m11_center_eq_bot hL hM
  have hb : CFSG.pCore 2 ↥L = ⊥ := le_bot_iff.mp ((zb_pCore_le_center hL).trans hZ.le)
  obtain ⟨e⟩ := hM
  exact ⟨(((QuotientGroup.quotientMulEquivOfEq hb).trans QuotientGroup.quotientBot).symm).trans e⟩

theorem exists_conj_of_m11
    {Y : Type} [Group Y]
    (hY : IsSporadic .M11 Y) (α : MulAut Y) : ∃ y : Y, MulAut.conj y = α := by
  obtain ⟨e⟩ := hY
  have htop : CFSG.ComponentClassification.OuterAutomorphisms.inner
      CFSG.Blueprint.NativeSporadic.M11 = ⊤ :=
    CFSG.Sporadic.Schreier.inner_eq_top_of_card_le CFSG.Sporadic.Schreier.m11_center_eq_bot'
      CFSG.Sporadic.Schreier.m11_mulAut_card
  have hβ : MulAut.congr e α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (CFSG.Blueprint.NativeSporadic.Carrier .M11) := by
    have h : MulAut.congr e α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
        CFSG.Blueprint.NativeSporadic.M11 := by
      rw [htop]
      exact Subgroup.mem_top _
    exact h
  rw [← CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e] at hβ
  obtain ⟨γ, hγ, hγα⟩ := hβ
  have hγα' : γ = α := (MulAut.congr e).injective hγα
  obtain ⟨y, hy⟩ := hγ
  exact ⟨y, hy.trans hγα'⟩

theorem le_sup_centralizer_of_m11
    {G : Type} [Group G]
    {H L : Subgroup G} (hLH : L ≤ H) (hN : H ≤ Subgroup.normalizer (L : Set G))
    (hL : IsSporadic .M11 ↥L) : H ≤ L ⊔ (H ⊓ Subgroup.centralizer (L : Set G)) := by
  intro g hg
  obtain ⟨l₀, hl₀⟩ := exists_conj_of_m11 hL (L.normalizerMonoidHom ⟨g, hN hg⟩)
  have key : ∀ x : ↥L, (l₀ : G) * x * (l₀ : G)⁻¹ = g * x * g⁻¹ := by
    intro x
    have := congrArg (fun α : MulAut ↥L => ((α x : ↥L) : G)) hl₀
    simpa using this
  have hc : (l₀ : G)⁻¹ * g ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := key ⟨x, hx⟩
    calc x * ((l₀ : G)⁻¹ * g) = (l₀ : G)⁻¹ * ((l₀ : G) * x * (l₀ : G)⁻¹) * g := by group
      _ = (l₀ : G)⁻¹ * (g * x * g⁻¹) * g := by rw [h1]
      _ = ((l₀ : G)⁻¹ * g) * x := by group
  have hmem : (l₀ : G)⁻¹ * g ∈ H ⊓ Subgroup.centralizer (L : Set G) :=
    ⟨H.mul_mem (H.inv_mem (hLH l₀.2)) hg, hc⟩
  have := Subgroup.mul_mem_sup l₀.2 hmem
  simpa using this

@[expose] def Input15122M11Normalizer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L S : Subgroup G), IsSporadic .M11 ↥L → IsSylowTwoOf S L →
    IsPGroup 2 ↥(L ⊓ Subgroup.normalizer (thompsonJ S : Set G))

theorem input15122ThreeDM11_of_simple
    (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (hN : Input15122M11Normalizer) : Input15122ThreeDM11 := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp h3D hM
  have hq := hc.ctx.qtfe
  have hMf := hc.ctx.mf
  have hSet := hc.ctx.setting
  have hLG : L ≤ g1_1516 Z₁ := le_of_mem_cComp hc.hL.comp
  have hLM : IsSporadic .M11 ↥L := isSporadic_m11_of_quot hcomp.2.2 hM
  have hZ : Subgroup.center ↥L = ⊥ := m11_center_eq_bot hcomp.2.2 hM
  have hG1N : g1_1516 Z₁ ≤ Subgroup.normalizer (L : Set G) := by
    rcases lemma_1_2_1_three hq.qtke hq.simple hq.nonabelian h37 h38
        (hSet.pCore_g1_ne_bot hq hMf) hc.hL.comp with hn | ⟨-, h2⟩
    · exact (Subgroup.normal_subgroupOf_iff_le_normalizer hLG).mp hn
    · exact absurd h2 (m11_not_a38Types hM)
  have hcomm : ∀ l ∈ L, ∀ c ∈ g1_1516 Z₁ ⊓ Subgroup.centralizer (L : Set G), l * c = c * l :=
    fun l hl c hcC => Subgroup.mem_centralizer_iff.mp hcC.2 l hl
  have hbot : L ⊓ (g1_1516 Z₁ ⊓ Subgroup.centralizer (L : Set G)) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxL, hxC⟩
    have hx : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC.2 y y.2)
    rw [hZ, Subgroup.mem_bot] at hx
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx)
  have hHLC : g1_1516 Z₁ ≤ L ⊔ (g1_1516 Z₁ ⊓ Subgroup.centralizer (L : Set G)) :=
    le_sup_centralizer_of_m11 hLG hG1N hLM
  have hSsyl : IsSylowTwoOf (s1516 T Z₁) (g1_1516 Z₁) := hc.h18.four
  have hSL : IsSylowTwoOf (s1516 T Z₁ ⊓ L) L := hc.h20.sylow
  have hSLC : s1516 T Z₁ ≤ L ⊔ (g1_1516 Z₁ ⊓ Subgroup.centralizer (L : Set G)) :=
    (s1516_le_g1 T Z₁).trans hHLC
  have hsplit := sylow_split hcomm hbot hLG inf_le_left hSsyl hSL hSLC
  have hNL : IsPGroup 2 ↥(L ⊓ Subgroup.normalizer (thompsonJ (s1516 T Z₁ ⊓ L) : Set G)) :=
    hN G L (s1516 T Z₁ ⊓ L) hLM hSL
  exact ⟨hLM, h3D.2, oTwoUpper_normalizer_le_centralizer hcomm hbot hHLC hsplit hNL⟩

end CFSG.Quasithin

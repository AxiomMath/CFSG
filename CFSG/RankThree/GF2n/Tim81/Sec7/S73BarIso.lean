module

public import CFSG.RankThree.GF2n.Tim81.Sec7.S73Bar
import CFSG.GroupTheory.SubgroupOfLattice
import CFSG.GroupTheory.SubgroupOfPPrimeCore
import CFSG.GroupTheory.Commutator.SubgroupOf
import CFSG.RankThree.GF2n.Tim81.Sec7.Transport

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open CFSG.RankThree.GF2n.Tim81.Sec7 (yOf rOf oOf)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M V A B : Subgroup G} {h : G} {n f : ℕ}

abbrev barRoots (h : G) (V : Subgroup G) : Set (Subgroup (YBar h)) :=
  {U | ∃ g : YBar h, U = conjSubgroup g (barY h V)}

abbrev preimY (h : G) (N : Subgroup (YBar h)) : Subgroup G :=
  (N.comap (QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h)))).map (yOf h).subtype

theorem mem_preimY_iff (h : G) {N : Subgroup (YBar h)} {x : G} :
    x ∈ preimY h N ↔
      ∃ hx : x ∈ yOf h, QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h)) ⟨x, hx⟩ ∈ N := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hN⟩
    exact ⟨⟨x, hx⟩, hN, rfl⟩

theorem barY_le_iff_le_preimY (h : G) {K : Subgroup G} (hK : K ≤ yOf h)
    {N : Subgroup (YBar h)} : barY h K ≤ N ↔ K ≤ preimY h N :=
  Subgroup.map_le_iff_le_comap.trans (CFSG.subgroupOf_le_iff_le_map_subtype hK)

theorem mem_normalizer_preimY (h : G) {N : Subgroup (YBar h)} {y : G} (hy : y ∈ yOf h)
    (hN : QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h)) ⟨y, hy⟩ ∈
      Subgroup.normalizer (N : Set (YBar h))) :
    y ∈ Subgroup.normalizer (preimY h N : Set G) :=
  Subgroup.le_normalizer_map (yOf h).subtype
    ⟨⟨y, hy⟩, Subgroup.le_normalizer_comap (QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h)))
      (Subgroup.mem_comap.mpr hN), rfl⟩

theorem ker_barMap (h : G) {K : Subgroup G} (hK : K ≤ yOf h) :
    (barMap h hK).ker = (inSubgroup (pPrimeCore 2) (yOf h)).subgroupOf K := by
  ext k
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  change (QuotientGroup.mk (Subgroup.inclusion hK k) : YBar h) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  constructor
  · intro hk
    exact ⟨_, hk, rfl⟩
  · rintro ⟨y, hy, hyk⟩
    have : y = Subgroup.inclusion hK k := Subtype.ext hyk
    rwa [this] at hy

theorem exists_barQuotEquiv (h : G) {K : Subgroup G} (hK : K ≤ yOf h)
    (hker : (inSubgroup (pPrimeCore 2) (yOf h)).subgroupOf K = pPrimeCore 2 ↥K) :
    ∃ e : (↥K ⧸ pPrimeCore 2 ↥K) ≃* ↥(barY h K),
      ∀ k : ↥K, (e (QuotientGroup.mk k) : YBar h) = barMap h hK k := by
  have hk : (barMap h hK).ker = pPrimeCore 2 ↥K := (ker_barMap h hK).trans hker
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    ((QuotientGroup.quotientKerEquivRange (barMap h hK)).trans
      (MulEquiv.subgroupCongr (barY_eq_range_barMap h hK).symm)), fun k => rfl⟩

theorem barY_eq_map_barMap (h : G) {K L : Subgroup G} (hKL : K ≤ L) (hL : L ≤ yOf h) :
    barY h K = (K.subgroupOf L).map (barMap h hL) := by
  ext x
  constructor
  · rintro ⟨⟨y, hyY⟩, hyK, rfl⟩
    exact ⟨⟨y, hKL (Subgroup.mem_subgroupOf.mp hyK)⟩,
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hyK), rfl⟩
  · rintro ⟨⟨y, hyL⟩, hyK, rfl⟩
    exact ⟨⟨y, hL hyL⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hyK), rfl⟩

theorem barY_le_normalizer (h : G) {K L : Subgroup G}
    (hKL : K ≤ Subgroup.normalizer (L : Set G)) :
    barY h K ≤ Subgroup.normalizer (barY h L : Set (YBar h)) :=
  CFSG.GroupTheory.map_subgroupOf_le_normalizer
    (QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h))) hKL

theorem normal_barY (h : G) {K : Subgroup G}
    (hK : yOf h ≤ Subgroup.normalizer (K : Set G)) : (barY h K).Normal :=
  (Subgroup.normal_subgroupOf_of_le_normalizer hK).map
    (QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h))) (QuotientGroup.mk'_surjective _)

theorem isPGroup_barY (h : G) {K : Subgroup G} (hK : IsPGroup 2 K) :
    IsPGroup 2 (barY h K) :=
  IsPGroup.map (hK.comap_subtype (K := yOf h)) (QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h)))

theorem isElemAbelian_barY (h : G) {K : Subgroup G} (hK : Assembly.IsElemAbelian 2 K) :
    Assembly.IsElemAbelian 2 (barY h K) :=
  (hK.subgroupOf (yOf h)).map (QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h)))

theorem barY_le_centralizer (h : G) {K L : Subgroup G} (hKL : K ≤ cenOf L) :
    barY h K ≤ Subgroup.centralizer (barY h L : Set (YBar h)) := by
  refine (Subgroup.map_mono (f := QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h))) fun k hk => ?_).trans
    (Subgroup.map_centralizer_le_centralizer_image
      ((L.subgroupOf (yOf h) : Subgroup (yOf h)) : Set (yOf h))
      (QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h))))
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp
    (hKL (Subgroup.mem_subgroupOf.mp hk)) (z : G) (Subgroup.mem_subgroupOf.mp hz))

theorem subgroupOf_rOf_of_oddCore_eq (hOY : inSubgroup (pPrimeCore 2) (yOf h) = oOf M h) :
    (inSubgroup (pPrimeCore 2) (yOf h)).subgroupOf (rOf M h) = pPrimeCore 2 ↥(rOf M h) := by
  rw [hOY]
  change ((pPrimeCore 2 ↥(rOf M h)).map (rOf M h).subtype).subgroupOf (rOf M h) = _
  rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective (rOf M h).subtype_injective]

namespace EpsIn

theorem y0Of_le_yOf (hE : EpsIn M V h) : y0Of V (Subgroup.zpowers h) ≤ yOf h := by
  unfold y0Of
  exact iSup₂_le fun x hx => hE.conjSubgroup_le_yOf hx

theorem subgroupOf_y0Of (hE : EpsIn M V h) :
    (inSubgroup (pPrimeCore 2) (yOf h)).subgroupOf (y0Of V (Subgroup.zpowers h)) =
      pPrimeCore 2 ↥(y0Of V (Subgroup.zpowers h)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.GroupTheory.subgroupOf_inSubgroup_pPrimeCore hE.y0Of_le_yOf
    (cenOf_le_normalizer_y0Of V _)

theorem disjoint_oddCore_of_isPGroup (hE : EpsIn M V h) {K : Subgroup G} (hK : IsPGroup 2 K) :
    Disjoint K (inSubgroup (pPrimeCore 2) (yOf h)) := by
  rw [disjoint_iff]
  refine le_bot_iff.mp fun x hx => ?_
  obtain ⟨hxK, hxO⟩ := Subgroup.mem_inf.mp hx
  have hodd : Odd (orderOf x) :=
    hE.odd_oddCore_yOf.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hxO)
  exact Subgroup.mem_bot.mpr (eq_one_of_odd_of_isPGroup hK hxK hodd)

theorem card_barY_of_disjoint (hE : EpsIn M V h) {K : Subgroup G} (hK : K ≤ yOf h)
    (hdisj : Disjoint K (inSubgroup (pPrimeCore 2) (yOf h))) :
    Nat.card (barY h K) = Nat.card K := by
  have hinj := hE.barMap_injective_of_disjoint hK hdisj
  have hbij : Function.Bijective (barMap h hK).rangeRestrict :=
    ⟨fun a b hab => hinj (congrArg Subtype.val hab), MonoidHom.rangeRestrict_surjective _⟩
  rw [barY_eq_range_barMap h hK]
  exact (Nat.card_congr (MulEquiv.ofBijective _ hbij).toEquiv).symm

theorem card_barY_self (hE : EpsIn M V h) : Nat.card (barY h V) = Nat.card V := by
  have := hE.card_barY (y := 1) (Subgroup.one_mem _)
  rwa [conjSubgroup_one] at this

theorem pCore_yBar_eq_bot (hE : EpsIn M V h) : pCore 2 (YBar h) = ⊥ := by
  by_contra hne
  have htop : pCore 2 ↥(⊤ : Subgroup (YBar h)) ≠ ⊥ := by
    intro hbot
    apply hne
    rw [← pCore_map_iso 2 (Subgroup.topEquiv : (⊤ : Subgroup (YBar h)) ≃* YBar h), hbot,
      Subgroup.map_bot]
  have hle := hE.le_of_pCore_ne_bot le_top htop
  obtain ⟨c, hcY, hcV, -⟩ := hE.moved
  have hcbar : (QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h))) ⟨c, hcY⟩ ∈ barY h (rOf M h) :=
    hle (Subgroup.mem_top _)
  have hcR := hE.mem_rOf_of_bar_mem hcY hcbar
  exact hcV (conjSubgroup_eq_self_iff.mpr (hE.root.le_normalizer hcR.1))

end EpsIn

theorem Sec7Hyp.epsIn (hS : Sec7Hyp M V n f) (h72 : Sec7.Stmt72 M V n f)
    (h73a : Sec7.Stmt73alpha M V) (h73g : Sec7.Stmt73gamma M V)
    (h73d : Sec7.Stmt73delta M V) (hD : L2Datum M V A B h) : EpsIn M V h := by
  have h72' := h72 A B h hD
  have hO_le : V ≤ p0Of M V (A ⊔ B) := by
    calc V = ⁅p0Of M V (A ⊔ B), p0Of M V (A ⊔ B)⁆ := h72'.2.2.1.symm
      _ ≤ p0Of M V (A ⊔ B) := Subgroup.commutator_le_self _
  exact
    { root := hS.sec5.toRootHyp
      le_p0 := by rw [h72'.1]; exact hO_le
      cen := by rw [h72'.1]; exact (h73a A B h hD).2.2.2.1
      maxEA := (h73g A B h hD).2
      moved := by
        obtain ⟨H₀, hH₀Y, -, -, -, c, hcH, hcVne, hcVM⟩ := h73d A B h hD
        exact ⟨c, hH₀Y hcH, hcVne, hcVM.trans inf_le_left⟩ }

end CFSG.RankThree.GF2n.Tim81

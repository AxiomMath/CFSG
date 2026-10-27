module

public import CFSG.Quasithin.EmptyFaithful.R3c11Cl
public import CFSG.Quasithin.EmptyFaithful.R3c12Cfg

public section

namespace CFSG.Quasithin.R3c12

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Blueprint
open CFSG.Quasithin.R3c10
open scoped commutatorElement

section Red

variable {G : Type} [Group G] [Finite G]

theorem clConfig_of_ctx2 {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G} (h113 : StageLemma14113)
    (c : CtxComp2 T Mc M V₁ V₂ Yp I L t) (hN : I ≤ Subgroup.normalizer (L : Set G))
    (hYL : Yp ≤ L) : ClConfig (↥L ⧸ Subgroup.center ↥L) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.hyp
  have hLc : L ∈ cComp I := c.c33.mem
  have hLI : L ≤ I := le_of_mem_cComp hLc
  have hV2S : V₂ ≤ Sgp153 T V₁ := R3c8.V₂_le_Sgp153 hh.hyp hh.decomp
  have hSM : Sgp153 T V₁ ≤ M := inf_le_left.trans hh.hyp.T_le
  have hSI : Sgp153 T V₁ ≤ I := le_sup_right.trans c.inH.1.1
  have hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) := fun s hs => hN (hSI hs)
  have hZ : centerOf L = CFSG.Open.pCoreOf 2 L := c.c33.center_eq
  have hSyl : IsSylowTwoOf (Sgp153 T V₁) I := c.facts.sylow
  have hQ : IsSylowTwoOf (Sgp153 T V₁ ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal (A4.isSylowTwoOf_mono hSyl (le_inf hSyl.1 hSL) inf_le_left)
      (le_inf hLI Subgroup.le_normalizer) inf_le_right
  set Q : Subgroup G := Sgp153 T V₁ ⊓ L with hQdef
  obtain ⟨hYN, hfix, hV2Y, hMIV⟩ := ctx2_facts h113 c
  have hV4 : Nat.card V₂ = 4 := hh.decomp.card₂
  have hV2L : V₂ ≤ L := hV2Y.trans hYL
  have hVQ : V₂ ≤ Q := le_inf hV2S hV2L
  have hQS : Q ≤ Sgp153 T V₁ := inf_le_left
  have hQV : Q ≤ Subgroup.normalizer (V₂ : Set G) := fun q hq => hMIV ⟨hSM (hQS hq), hSI (hQS hq)⟩
  have hVz : ∀ x ∈ V₂, x ∈ centerOf L → x = 1 := fun x hx hxc =>
    hfix x hx fun a ha => Subgroup.mem_centralizer_iff.mp hxc.2 a (hYL ha)
  have hV2sq : ∀ x ∈ V₂, x * x = 1 := fun x hx => by
    have := hh.hyp.elemAbelian.2 x (hh.decomp.le₂ hx)
    rw [← sq]
    exact this
  obtain ⟨E, hEY, hE, hE9⟩ := exists_nine_of_pRank_two c.rank
  obtain ⟨e, heE, he1, hec⟩ := exists_ne_one_centralizes (hEY.trans hYN) hE9 hV4
  have he3 : e ^ 3 = 1 := hE.2 e heE
  have heL : e ∈ L := hYL (hEY heE)
  have hZP : ∀ z ∈ Subgroup.center ↥L, (z : G) ∈ Q := center_le_of_isSylowTwoOf hZ hQ
  obtain ⟨Tsyl, hT, hTcomap, hNcomap⟩ := exists_quotSylow hZ hQ
  set Z : Subgroup ↥L := Subgroup.center ↥L with hZdef
  set π : ↥L →* ↥L ⧸ Z := QuotientGroup.mk' Z with hπ
  have hker : π.ker = Z := QuotientGroup.ker_mk' Z
  set T' : Subgroup (↥L ⧸ Z) := (Tsyl : Subgroup (↥L ⧸ Z)) with hTdef
  have hTsyl : IsSylowTwoOf T' ⊤ :=
    K1.isSylowTwoOf_top_iff.mpr ⟨Tsyl.isPGroup', Tsyl.not_dvd_index⟩
  have hPL : Q ≤ L := hQ.1
  have hVL : V₂ ≤ L := hV2L
  set Vbar : Subgroup (↥L ⧸ Z) := (V₂.subgroupOf L).map π with hVbar
  have hVT : Vbar ≤ T' := by
    rw [hT]
    refine Subgroup.map_mono fun x hx => ?_
    exact Subgroup.mem_subgroupOf.mpr (hVQ (Subgroup.mem_subgroupOf.mp hx))
  have hKcard : Nat.card (V₂.subgroupOf L) = 4 := by
    rw [← hV4]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVL).toEquiv
  have hinj : Function.Injective (π.comp (V₂.subgroupOf L).subtype) := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have hk' : π (k : ↥L) = 1 := hk
    have hkZ : (k : ↥L) ∈ Z := by
      rw [← hker]
      exact hk'
    have hkc : ((k : ↥L) : G) ∈ centerOf L := SBc2.mem_centerOf_iff_center.mpr hkZ
    have hkV : ((k : ↥L) : G) ∈ V₂ := Subgroup.mem_subgroupOf.mp k.2
    exact Subtype.ext (Subtype.ext (hVz _ hkV hkc))
  have hVbar4 : Nat.card Vbar = 4 := by
    have h1 : (π.comp (V₂.subgroupOf L).subtype).range = Vbar := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← h1]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm.trans hKcard
  refine ⟨T', Vbar, π ⟨e, heL⟩, hTsyl, hVT, hVbar4, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x₀, hx₀, rfl⟩
    rw [← map_mul]
    have hxV : (x₀ : G) ∈ V₂ := Subgroup.mem_subgroupOf.mp hx₀
    have : x₀ * x₀ = 1 := Subtype.ext (hV2sq _ hxV)
    rw [this, map_one]
  ·
    intro t' ht'
    rw [hT] at ht'
    obtain ⟨l, hl, rfl⟩ := ht'
    have hlQ : (l : G) ∈ Q := Subgroup.mem_subgroupOf.mp hl
    have hlV : (l : G) ∈ Subgroup.normalizer (V₂ : Set G) := hQV hlQ
    have hlV' : l ∈ Subgroup.normalizer ((V₂.subgroupOf L : Subgroup ↥L) : Set ↥L) :=
      (SBc2.mem_normalizer_subgroupOf_iff hVL l).mpr hlV
    refine A4.mem_normalizer_of_conj_mem fun vbar hvbar => ?_
    obtain ⟨a, ha, rfl⟩ := hvbar
    refine ⟨l * a * l⁻¹, (Subgroup.mem_normalizer_iff.mp hlV' a).mp ha, ?_⟩
    simp [map_mul, map_inv]
  ·
    intro h1
    have heZ : (⟨e, heL⟩ : ↥L) ∈ Z := by
      rw [← hker]
      exact h1
    have heQ : e ∈ Q := hZP _ heZ
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hQ.2.1) (⟨e, heQ⟩ : ↥Q)
    have hj' : orderOf e = 2 ^ j := by
      rw [← hj]
      exact Subgroup.orderOf_coe (⟨e, heQ⟩ : ↥Q)
    have hdvd : 2 ^ j ∣ 3 := by
      rw [← hj']
      exact orderOf_dvd_of_pow_eq_one he3
    have hj0 : 2 ^ j = 1 :=
      (Nat.Coprime.pow_left j (by norm_num : Nat.Coprime 2 3)).eq_one_of_dvd hdvd
    rw [hj0, orderOf_eq_one_iff] at hj'
    exact he1 hj'
  · rw [← map_pow]
    have : (⟨e, heL⟩ : ↥L) ^ 3 = 1 := Subtype.ext he3
    rw [this, map_one]
  · rintro _ ⟨x₀, hx₀, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hec _ (Subgroup.mem_subgroupOf.mp hx₀))

end Red

end CFSG.Quasithin.R3c12

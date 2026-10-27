module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Bot47Base
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Forty7aCommon
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Kernel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResultsB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c1_card_starImg_mul_card_uOne {V : Subgroup G} {z : G} (hV : IsElemAbelian 2 V)
    (hz : z ∈ V) :
    Nat.card ↥(starImg (centralizer ({z} : Set G)) V) * Nat.card ↥(uOne V z) =
      Nat.card ↥V := by
  let H := centralizer ({z} : Set G)
  let V' : Subgroup ↥H := V.subgroupOf H
  let π : ↥H →* Bar2 H := QuotientGroup.mk' (CFSG.pCore 2 ↥H)
  let ψ : ↥V' →* Bar2 H := π.comp V'.subtype
  have hVH : V ≤ H := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    letI : IsMulCommutative ↥V := hV.1
    exact congrArg Subtype.val (mul_comm' (⟨z, hz⟩ : ↥V) (⟨v, hv⟩ : ↥V))
  have hrange : ψ.range = starImg H V := by
    show (π.comp V'.subtype).range = (V.subgroupOf H).map π
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : Nat.card ↥ψ.ker = Nat.card ↥(uOne V z) := by
    have hker_eq : ψ.ker = ((uOne V z).subgroupOf H).subgroupOf V' := by
      ext y
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      constructor
      · intro hy
        have hψ : ψ y = 1 := (MonoidHom.mem_ker).mpr hy
        have hπ : π (y : ↥H) = 1 := by
          change (π.comp V'.subtype) y = 1
          simpa only [ψ] using hψ
        have hpcore : (y : ↥H) ∈ CFSG.pCore 2 ↥H := by
          have hmem : (y : ↥H) ∈ (QuotientGroup.mk' (CFSG.pCore 2 ↥H)).ker := by
            rw [MonoidHom.mem_ker]
            simpa only [π] using hπ
          rwa [QuotientGroup.ker_mk' (CFSG.pCore 2 ↥H)] at hmem
        exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp y.2,
          Subgroup.mem_map.mpr ⟨(y : ↥H), hpcore, rfl⟩⟩
      · intro hy
        obtain ⟨-, hpcore⟩ := Subgroup.mem_inf.mp hy
        obtain ⟨o, ho, hoo⟩ := Subgroup.mem_map.mp hpcore
        have hoy : o = (y : ↥H) := Subtype.ext hoo
        have hπo : π o = 1 := by
          have hmem : o ∈ CFSG.pCore 2 ↥H := ho
          rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥H)] at hmem
          simpa only [π] using (MonoidHom.mem_ker).mp hmem
        have hπ : π (y : ↥H) = 1 := by rw [← hoy]; exact hπo
        rw [MonoidHom.mem_ker]
        change (π.comp V'.subtype) y = 1
        simpa using hπ
    rw [hker_eq]
    have hle1 : (uOne V z).subgroupOf H ≤ V' := by
      intro w hw
      rw [Subgroup.mem_subgroupOf] at hw ⊢
      change (w : G) ∈ V ⊓ pCoreOf 2 (centralizer ({z} : Set G)) at hw
      exact hw.1
    calc Nat.card ↥(((uOne V z).subgroupOf H).subgroupOf V')
        = Nat.card ↥((uOne V z).subgroupOf H) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle1).toEquiv
      _ = Nat.card ↥(uOne V z) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe
            ((inf_le_left : uOne V z ≤ V).trans hVH)).toEquiv
  have hcardV' : Nat.card ↥V' = Nat.card ↥V :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVH).toEquiv
  have hmain := Subgroup.card_ker_mul_card_range ψ
  rw [hrange, hker, hcardV'] at hmain
  rw [mul_comm] at hmain
  exact hmain

theorem s16c1_card_uOne {V : Subgroup G} {z : G} (hV : IsElemAbelian 2 V) (hz : z ∈ V)
    (hV64 : Nat.card ↥V = 64) (h47 : Concl1647 V z) : Nat.card ↥(uOne V z) = 32 := by
  have h := s16c1_card_starImg_mul_card_uOne hV hz
  rw [h47.1, hV64] at h
  omega

theorem s16c1_card_ptCent_zTil (D : Data G) {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D ⊥ V L hV) (hc : Case167_1 D ⊥ V hV L) (h41 : R16_41 D)
    {x : IntMod V hV} (hx1 : x.val ≠ 1)
    (hsing : ∀ Q : Vtil (⊥ : Subgroup G) V hV → ZMod 2, IsMinusQuadF2 Q →
      QuadInvariant Q (lBar ⊥ V hV L) → Q (mkTil ⊥ V hV x) = 0) :
    Nat.card ↥(ptCent (lBar ⊥ V hV L) (mkTil ⊥ V hV x)) = 960 := by
  obtain ⟨⟨Q, hQ, hQi⟩, hall⟩ := h41 (⊥ : Subgroup G) V L hV hS hc
  have hne : mkTil (⊥ : Subgroup G) V hV x ≠ 1 := by
    intro h
    have h1 : (TwelveShort.mkTilEquiv V hV) x = (TwelveShort.mkTilEquiv V hV) 1 := by
      rw [TwelveShort.mkTilEquiv_apply, TwelveShort.mkTilEquiv_apply, h, map_one]
    have hx : x = 1 := (TwelveShort.mkTilEquiv V hV).injective h1
    exact hx1 (by rw [hx]; rfl)
  exact s16c1_card_of_isE16A5 ((hall Q hQ hQi).1 (mkTil ⊥ V hV x) hne (hsing Q hQ hQi))

theorem s16c1_card_imgTil_bot {V U : Subgroup G} (hV : IsElemAbelian 2 V) (hU : U ≤ V) :
    Nat.card ↥(imgTil ⊥ V hV U) = Nat.card ↥U := by
  have hinj : Function.Injective (mkTil (⊥ : Subgroup G) V hV) := by
    intro a b h
    exact (TwelveShort.mkTilEquiv V hV).injective (by
      rw [TwelveShort.mkTilEquiv_apply, TwelveShort.mkTilEquiv_apply]; exact h)
  unfold imgTil
  rw [Subgroup.card_map_of_injective hinj]
  change Nat.card ↥(U.subgroupOf V) = Nat.card ↥U
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU).toEquiv

theorem s16c1_stable_N (D : Data G) {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D ⊥ V L hV) (x : IntMod V hV) :
    StableUnder (ptCent (lBar ⊥ V hV L) (mkTil ⊥ V hV x))
      (imgTil ⊥ V hV (⁅V, eOne V x.val⁆ ⊔ Subgroup.zpowers x.val)) := by
  intro φ hφ q hq
  rw [ptCent, Subgroup.mem_inf] at hφ
  obtain ⟨hφL, hφstab⟩ := hφ
  have hφfix : φ (mkTil (⊥ : Subgroup G) V hV x) = mkTil (⊥ : Subgroup G) V hV x := by
    simpa [MulAut.smul_def] using (MulAction.mem_stabilizer_iff.mp hφstab)
  have hφL' : φ ∈ barSub (⊥ : Subgroup G) V hV L := by simpa only [lBar] using hφL
  obtain ⟨g, hgL, hgφ⟩ := (mem_barSub (⊥ : Subgroup G) V hV L φ).1 hφL'
  obtain ⟨y, hyN, rfl⟩ := (mem_imgTil (⊥ : Subgroup G) V hV _ q).1 hq
  rw [← hgφ, actTil_mk]
  refine (mem_imgTil (⊥ : Subgroup G) V hV _ _).2
    ⟨actStab (⊥ : Subgroup G) V hV g y, ?_, rfl⟩
  rw [actStab_apply_val]
  have hgz : (g : G) * x.val * (g : G)⁻¹ = x.val := by
    have hfix : actTil (⊥ : Subgroup G) V hV g (mkTil (⊥ : Subgroup G) V hV x)
        = mkTil (⊥ : Subgroup G) V hV x := by
      rw [hgφ]
      exact hφfix
    have h1 : mkTil (⊥ : Subgroup G) V hV (actStab (⊥ : Subgroup G) V hV g x)
        = mkTil (⊥ : Subgroup G) V hV x := by
      rw [← actTil_mk]
      exact hfix
    have h2 : (actStab (⊥ : Subgroup G) V hV g x).val = x.val := by
      have hmem := (mkTil_eq_iff (⊥ : Subgroup G) V hV _ _).1 h1
      rwa [Subgroup.mem_bot, mul_inv_eq_one] at hmem
    simpa only [actStab_apply_val] using h2
  have hcomm : x.val * (g : G) = (g : G) * x.val := by
    calc x.val * (g : G) = ((g : G) * x.val * (g : G)⁻¹) * (g : G) := by rw [hgz]
      _ = (g : G) * x.val := by group
  have hgH : (g : G) ∈ centralizer ({x.val} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    exact hcomm
  have hconjV : conjSubgroup V (g : G) = V :=
    (conjSubgroup_eq_iff_mem_normalizer).2
      (hS.setting.hyp151.hyp125.pairFacts.le_normalizer (hS.setting.hyp151.le hgL))
  have hconjE : conjSubgroup (eOne V x.val) (g : G) = eOne V x.val := by
    simpa only [eOne] using
      s16c1_conjSubgroup_hConjClosure (z := x.val) (uOne V x.val) hgH
  have hzg : (g : G)⁻¹ * x.val * (g : G) = x.val := by
    calc (g : G)⁻¹ * x.val * (g : G) = (g : G)⁻¹ * (x.val * (g : G)) := by group
      _ = (g : G)⁻¹ * ((g : G) * x.val) := by rw [hcomm]
      _ = x.val := by group
  have hconjz : conjSubgroup (Subgroup.zpowers x.val) (g : G) = Subgroup.zpowers x.val := by
    rw [conjSubgroup, MonoidHom.map_zpowers]
    change Subgroup.zpowers (MulAut.conj (g : G)⁻¹ x.val) = Subgroup.zpowers x.val
    rw [MulAut.conj_apply, inv_inv, hzg]
  have hconjVE : conjSubgroup ⁅V, eOne V x.val⁆ (g : G) = ⁅V, eOne V x.val⁆ := by
    rw [conjSubgroup, Subgroup.map_commutator]
    change ⁅conjSubgroup V (g : G), conjSubgroup (eOne V x.val) (g : G)⁆
      = ⁅V, eOne V x.val⁆
    rw [hconjV, hconjE]
  have hN : conjSubgroup (⁅V, eOne V x.val⁆ ⊔ Subgroup.zpowers x.val) (g : G)
      = ⁅V, eOne V x.val⁆ ⊔ Subgroup.zpowers x.val := by
    rw [conjSubgroup, Subgroup.map_sup]
    change conjSubgroup ⁅V, eOne V x.val⁆ (g : G)
      ⊔ conjSubgroup (Subgroup.zpowers x.val) (g : G) = ⁅V, eOne V x.val⁆ ⊔ Subgroup.zpowers x.val
    rw [hconjVE, hconjz]
  have hnorm : ∀ n ∈ ⁅V, eOne V x.val⁆ ⊔ Subgroup.zpowers x.val,
      (g : G) * n * (g : G)⁻¹ ∈ ⁅V, eOne V x.val⁆ ⊔ Subgroup.zpowers x.val := by
    intro n hn
    have hn' : n ∈ conjSubgroup (⁅V, eOne V x.val⁆ ⊔ Subgroup.zpowers x.val) (g : G) := by
      rw [hN]; exact hn
    exact (mem_conjSubgroup_iff).mp hn'
  exact hnorm y.val hyN

theorem s16c1_card_N_cases (D : Data G) (hkit : OmegaKit) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D ⊥ V L hV) (hc : Case167_1 D ⊥ V hV L)
    (h41 : R16_41 D) {x : IntMod V hV} (hx1 : x.val ≠ 1)
    (hsing : ∀ Q : Vtil (⊥ : Subgroup G) V hV → ZMod 2, IsMinusQuadF2 Q →
      QuadInvariant Q (lBar ⊥ V hV L) → Q (mkTil ⊥ V hV x) = 0)
    (hSyl : IsSylowIn 2 (D.T ⊓ centralizer ({x.val} : Set G)) (centralizer ({x.val} : Set G)))
    (hV64 : Nat.card ↥V = 64) (h47 : Concl1647 V x.val) :
    Nat.card ↥(⁅V, eOne V x.val⁆ ⊔ Subgroup.zpowers x.val) = 2 ∨
      Nat.card ↥(⁅V, eOne V x.val⁆ ⊔ Subgroup.zpowers x.val) = 32 := by
  set N : Subgroup G := ⁅V, eOne V x.val⁆ ⊔ Subgroup.zpowers x.val with hNdef
  have hMV : D.M ≤ normalizer (V : Set G) :=
    hS.setting.hyp151.hyp125.pairFacts.le_normalizer
  have hP : pCoreOf 2 (centralizer ({x.val} : Set G)) ≤ normalizer (V : Set G) :=
    (s16c1_pCoreOf_le_M D hSyl).trans hMV
  have hz : x.val ∈ V := x.val_mem
  have hNU : N ≤ uOne V x.val := s16c1_comm_V_eOne_sup_le hV hz hP
  have hU32 : Nat.card ↥(uOne V x.val) = 32 := s16c1_card_uOne hV hz hV64 h47
  have hNle : Nat.card ↥N ≤ 32 := by
    have hcard := Subgroup.card_le_of_le hNU
    rwa [hU32] at hcard
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardz : Nat.card ↥(Subgroup.zpowers x.val) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hV.2 x.val hz) hx1
  have hNge : 2 ≤ Nat.card ↥N := by
    have hcard := Subgroup.card_le_of_le (le_sup_right : Subgroup.zpowers x.val ≤ N)
    rwa [hcardz] at hcard
  have hScard : Nat.card ↥(imgTil (⊥ : Subgroup G) V hV N) = Nat.card ↥N :=
    s16c1_card_imgTil_bot hV (hNU.trans inf_le_left)
  have hstable : StableUnder
      (ptCent (lBar (⊥ : Subgroup G) V hV L) (mkTil (⊥ : Subgroup G) V hV x))
      (imgTil (⊥ : Subgroup G) V hV N) := by
    simpa only [hNdef] using s16c1_stable_N D hS x
  have h960 : Nat.card ↥(ptCent (lBar (⊥ : Subgroup G) V hV L)
      (mkTil (⊥ : Subgroup G) V hV x)) = 960 :=
    s16c1_card_ptCent_zTil D hS hc h41 hx1 hsing
  have hne : mkTil (⊥ : Subgroup G) V hV x ≠ 1 := by
    intro h
    have h1 : (TwelveShort.mkTilEquiv V hV) x = (TwelveShort.mkTilEquiv V hV) 1 := by
      rw [TwelveShort.mkTilEquiv_apply, TwelveShort.mkTilEquiv_apply, h, map_one]
    have hx : x = 1 := (TwelveShort.mkTilEquiv V hV).injective h1
    exact hx1 (by rw [hx]; rfl)
  have hIrr : OmegaIrr (lBar (⊥ : Subgroup G) V hV L) :=
    (hkit _ (lBar (⊥ : Subgroup G) V hV L) hc.2.1).2.1
  have hcases := hIrr (mkTil (⊥ : Subgroup G) V hV x) hne h960
    (imgTil (⊥ : Subgroup G) V hV N) hstable
  rw [hScard] at hcases
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
